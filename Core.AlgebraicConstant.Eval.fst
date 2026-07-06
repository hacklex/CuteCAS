module Core.AlgebraicConstant.Eval

(*
   §E splitting-field bridge.

   Embed a base polynomial  p : polynomial t  into the extension's
   polynomial ring  polynomial (algebraic r)  (coefficient-wise via
   ac_const), then connect  poly_eval  OVER the extension at theta to the
   ac_eval Horner map.  The payoff:

       theta_root_ext :  r | d  ==>  theta is a root of (ext_embed_poly d)
                                     AS A POLYNOMIAL OVER algebraic r

   which is exactly the precondition the factor theorem needs to peel
   (X - theta) from the embedded d.

   Deliverables:
     - ext_embed_poly p    : coefficient-wise embedding  t[X] -> (algebraic r)[X]
     - ext_embed_eval p    : poly_eval (ext_embed_poly p) theta ~ ac_eval p theta
     - theta_root_ext d    : r | d  ==>  poly_eval (ext_embed_poly d) theta ~ 0
*)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Eval
open Core.Polynomial.Irreducible
open Core.FinSum
open Core.AlgebraicConstant
open Core.AlgebraicConstant.Root

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* The commutative-ring instance on the extension carrier: the canonical
   TC-resolved one, i.e. the algebraic field's commutative-ring projection. *)
unfold let acr (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
  : commutative_ring (algebraic r)
  = algebraic_commutative_ring r

(* ================================================================ *)
(*  0.  Generic eval facts over an arbitrary commutative ring.      *)
(*      (Bucket-B poly_eval facts; reused at the extension ring.)   *)
(* ================================================================ *)

(* poly_eval of a constant polynomial is the constant. *)
let eval_poly_const (#s:Type) {| cr: commutative_ring s |} (c: s) (x: s)
  : Lemma (poly_eval (poly_const c) x = c)
  = H.elim_equatable_laws s ();
    H.trans_for_calc s ();
    let p = poly_const c in
    let f = eval_term p x in
    (* len (poly_const c) <= 1, so summing to 1 is the whole value *)
    monomial_deg c 0;                       (* deg = -1 or 0 ; len <= 1 *)
    eval_extend p x 1;                      (* sum f 0 1 = poly_eval p x *)
    sum_range_unfold_left f 0 1;
    sum_range_empty f 1 1;                   (* sum f 1 1 = zero *)
    H.x_plus_zero (f 0);                           (* f 0 + zero ~ f 0 *)
    add_congruence (f 0) (sum_range f 1 1) (f 0) (zero <: s);
    (* f 0 = coeff p 0 * cpow x 0 = c * one ~ c *)
    poly_const_coeff0 c;                    (* coeff p 0 = c *)
    mul_congruence (coeff p 0) (cpow x 0) c (one <: s);  (* cpow x 0 == one *)
    (* assemble: poly_eval p x ~ sum f 0 1 ~ f 0 + zero ~ f 0 ~ c *)
    H.x_mul_one c // omitted explicit transitivity calls

(* poly_eval of X = monomial one 1 is the evaluation point. *)
let eval_X (#s:Type) {| cr: commutative_ring s |} (x: s)
  : Lemma (poly_eval (monomial one 1) x = x)
  = H.elim_equatable_laws s ();
    H.trans_for_calc s ();
    let m = monomial one 1 in
    let f = eval_term m x in
    monomial_deg #s one 1;              (* deg -1 or 1 ; len <= 2 *)
    eval_extend m x 2;                      (* sum f 0 2 = poly_eval m x *)
    sum_range_unfold_left f 0 2;            (* sum 0 2 = f 0 + sum 1 2 *)
    sum_range_unfold_left f 1 2;            (* sum 1 2 = f 1 + sum 2 2 *)
    sum_range_empty f 2 2;                  (* sum 2 2 = zero *)
    (* f 0 = coeff m 0 * cpow x 0 = zero * one ~ zero *)
    monomial_coeff #s one 1 0;          (* coeff m 0 = zero *)
    mul_congruence (coeff m 0) (cpow x 0) zero (cpow x 0);
    H.zero_mul_x (cpow x 0);                (* zero * cpow x 0 ~ zero *)
    transitivity (f 0) (zero * cpow x 0) zero;  (* f 0 ~ zero *)
    (* f 1 = coeff m 1 * cpow x 1 = one * (x * cpow x 0) = one * (x * one) ~ x *)
    monomial_coeff #s one 1 1;          (* coeff m 1 = one *)
    (* cpow x 1 = x * cpow x 0 = x * one ~ x *)
    H.x_mul_one x;                                 (* x * one ~ x *)
    (* cpow x 1 == x * cpow x 0, and cpow x 0 == one *)    
    H.x_mul_one (coeff m 1);                (* but better: one * (x*one) *)
    mul_congruence (coeff m 1) (cpow x 1) (one <: s) (x * (one <: s));
    H.one_mul_x (x * (one <: s));                  (* one * (x*one) ~ (x*one) *)
    (* sum 1 2 = f 1 + zero ~ f 1 ~ x *)
    H.x_plus_zero (f 1);
    add_congruence (f 1) (sum_range f 2 2) (f 1) (zero <: s);
    (* sum 0 2 = f 0 + sum 1 2 ~ zero + x ~ x *)
    add_congruence (f 0) (sum_range f 1 2) (zero <: s) x;
    H.zero_plus_x x

(* Horner cons step for poly_eval (over any ring):
     poly_eval (c :: tl) x  ~  c + x * poly_eval tl x. *)
let eval_horner_cons (#s:Type) {| cr: commutative_ring s |}
                     (c: s) (tl: polynomial s)
                     (p: polynomial s {p == (c :: tl)}) (x: s)
  : Lemma (poly_eval p x = c + x * poly_eval tl x)
  = H.elim_equatable_laws s ();
    H.trans_for_calc s ();
    let m  : polynomial s = monomial one 1 in
    let xtl : polynomial s = m * tl in
    let lhs : polynomial s = (poly_const c) + xtl in
    (* horner_cons : poly_eq lhs p  =>  poly_eval p x = poly_eval lhs x *)
    horner_cons c tl p;                            (* poly_eq lhs p *)
    symmetry lhs p;                                (* poly_eq p lhs *)
    eval_congruence p lhs x;                       (* poly_eval p x = poly_eval lhs x *)
    (* poly_eval lhs x = poly_eval (poly_const c) x + poly_eval xtl x *)
    eval_add (poly_const c) xtl x;
    (* poly_eval (poly_const c) x = c *)
    eval_poly_const c x;
    (* poly_eval xtl x = poly_eval m x * poly_eval tl x ~ x * poly_eval tl x *)
    eval_mul m tl x;
    eval_X x;                                      (* poly_eval m x = x *)
    mul_congruence (poly_eval m x) (poly_eval tl x)
                   x (poly_eval tl x);             (* poly_eval m x * .. ~ x * .. *)    
    (* combine the two summands *)
    add_congruence (poly_eval (poly_const c) x) (poly_eval xtl x)
                   c (x * poly_eval tl x)

(* ================================================================ *)
(*  1.  ext_embed_poly : coefficient-wise embedding.                *)
(* ================================================================ *)

let ext_embed_poly (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                   (p: polynomial t)
  : polynomial (algebraic r)
  = trim (L.map ac_const p)

(* index of a mapped list. *)
private let rec index_map_lemma (#a:Type) (#b:Type) (g: a -> b) (l: list a) (i:nat{i < L.length l})
  : Lemma (ensures L.index (L.map g l) i == g (L.index l i)) (decreases l)
  = if i = 0 then ()
    else index_map_lemma g (L.tl l) (i - 1)

(* coeff of the embedded polynomial = ac_const of the base coeff.
   In range it's a genuine == (list index); out of range both sides are
   the ring zero / ac_const zero, related by =eq (poly_const zero ~ poly_zero). *)
let embed_coeff (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                (p: polynomial t) (i: nat)
  : Lemma ((coeff (ext_embed_poly p) i) =
             (ac_const #_ #_ #r (coeff p i)))
  = let ac_const = ac_const #_ #_ #r in
    let mapped : list (algebraic r) = L.map ac_const p in
    H.elim_equatable_laws (polynomial t) ();
    ac_elim_equatable_laws r;
    L.map_lemma ac_const p;                               (* length (map g p) == length p *)
    coeff_trim mapped i;
    if i < L.length p then
      index_map_lemma ac_const p i                        (* index mapped i == g (coeff p i) *)
    else begin  
      divides_zero r;                               (* r | poly_zero *)
      divides_congruence_right r poly_zero (poly_const zero);  (* r | poly_const zero *)
      ac_eq_zero_iff_divides (ac_const zero)
    end

(* The base list and the embedded list have equal length (trim is a no-op
   because ac_const never produces the carrier-zero unless... it can; but we
   only ever index, so we use coeff via embed_coeff and never length). *)

(* ================================================================ *)
(*  2.  The eval bridge:  poly_eval (ext_embed_poly p) theta         *)
(*                        ~  ac_eval p theta.                        *)
(* ================================================================ *)

(* Cons shape of ext_embed_poly: as a list,
     ext_embed_poly (c::tl)  =  trim (g c :: map g tl).
   We avoid reasoning about trim directly and instead drive the induction
   through eval_horner_cons + embed_coeff at the extension ring. *)

(* The cons Horner step at the extension ring, with coeff-embedding folded in.
   poly_eval (ext_embed_poly (c::tl)) theta ~ ac_add (ac_const c) (ac_mul theta (poly_eval (ext_embed_poly tl) theta)). *)
(* Coefficient-wise: the embedded cons equals  poly_const (g c) + X * (embed tl)
   over the extension ring (poly_eq).  This is the Horner decomposition lifted
   through the coefficient embedding; mirrors Root.horner_cons but with
   embed_coeff replacing the literal coefficient reads. *)
(* --- decomposition of embed_cons_poly_eq into per-index private lemmas --- *)

#push-options "--z3rlimit 20"
private let embed_cons_coeff_zero (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
                                  (c: t) (tl: polynomial t)
                                  (p: polynomial t {p == (c :: tl)})
  : Lemma (coeff (ext_embed_poly p) 0 =
             coeff (poly_const (ac_const c) +
                    (monomial one 1) * (ext_embed_poly #_ #_ #r tl)) 0)
  = H.elim_equatable_laws (algebraic r) ();
    H.trans_for_calc (algebraic r) ();
    let embed = ext_embed_poly #_ #_ #r in
    let ep  : polynomial (algebraic r) = embed p in
    let etl : polynomial (algebraic r) = embed tl in
    let m   : polynomial (algebraic r) = monomial one 1 in
    let xtl : polynomial (algebraic r) = m * etl in
    let cnst: polynomial (algebraic r) = poly_const (ac_const c) in
    let rhs : polynomial (algebraic r) = cnst + xtl in
    poly_add_coeff cnst xtl 0;   (* coeff rhs 0 = coeff cnst 0 + coeff xtl 0 *)
    embed_coeff #_ #_ #r p 0;    (* coeff ep 0 ~ ac_const (coeff p 0) *)
    (* coeff cnst 0 = ac_const c ; coeff xtl 0 = zero ; sum ~ ac_const c. *)
    poly_const_coeff0 (ac_const #_ #_ #r c);   (* coeff cnst 0 = g c *)
    x_mul_coeff_zero etl;                       (* coeff xtl 0 = zero *)
    add_congruence
      (coeff cnst 0) (coeff xtl 0)
      (ac_const c) (zero);
    H.x_plus_zero (ac_const #_ #_ #r c);
    (* coeff p 0 = c (list head) ⇒ ac_const (coeff p 0) == ac_const c *)
    assert (coeff p 0 == c);
    transitivity
      (coeff ep 0)
      (ac_const c)
      (coeff rhs 0)
#pop-options

#push-options "--z3rlimit 20"
private let embed_cons_coeff_succ (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
                                  (c: t) (tl: polynomial t)
                                  (p: polynomial t {p == (c :: tl)})
                                  (j: nat {j >= 1})
  : Lemma (coeff (ext_embed_poly p) j =
             coeff ((poly_const (ac_const c))
                    + ((monomial (one #(algebraic r)) 1) * (ext_embed_poly tl))) j)
  = H.elim_equatable_laws (algebraic r) ();
    H.trans_for_calc (algebraic r) ();
    let ep  : polynomial (algebraic r) = ext_embed_poly p in
    let etl : polynomial (algebraic r) = ext_embed_poly tl in
    let m   : polynomial (algebraic r) = monomial one 1 in
    let xtl : polynomial (algebraic r) = m * etl in
    let cnst: polynomial (algebraic r) = poly_const (ac_const c) in
    let rhs : polynomial (algebraic r) = cnst + xtl in
    poly_add_coeff cnst xtl j;   (* coeff rhs j = coeff cnst j + coeff xtl j *)
    embed_coeff #_ #_ #r p j;    (* coeff ep j ~ ac_const (coeff p j) *)
    let i = j - 1 in
    (* coeff cnst j = zero ; coeff xtl j = coeff etl i ; sum ~ coeff etl i. *)
    poly_const_coeff_high (ac_const #_ #_ #r c) j;  (* coeff cnst j = zero *)
    x_mul_coeff_succ etl i;                         (* coeff xtl j = coeff etl i *)
    add_congruence
      (coeff cnst j) (coeff xtl j)
      (zero <: algebraic r) (coeff etl i);
    H.zero_plus_x (coeff etl i);
    (* coeff etl i ~ ac_const (coeff tl i) *)
    embed_coeff #_ #_ #r tl i;
    (* coeff p j = coeff (c::tl) j = coeff tl (j-1) = coeff tl i (list index) *)
    assert (coeff p j == coeff tl i);
    transitivity
      (coeff ep j)
      (ac_const (coeff tl i))
      (coeff etl i);
    transitivity
      (coeff ep j)
      (coeff etl i)
      (coeff rhs j)
#pop-options

#push-options "--z3rlimit 20"
let embed_cons_poly_eq (#t:Type) {| f: field t |} (r: polynomial t {proper_extension r})
                       (c: t) (tl: polynomial t)
                       (p: polynomial t {p == (c :: tl)})
  : Lemma ((ext_embed_poly p) =
             (
                (poly_const (ac_const c)) +
                ((monomial (one #(algebraic r)) 1) *
                   (ext_embed_poly  tl))))
  = let ep  : polynomial (algebraic r) = ext_embed_poly p in
    let etl : polynomial (algebraic r) = ext_embed_poly tl in
    let m   : polynomial (algebraic r) = monomial one 1 in
    let xtl : polynomial (algebraic r) = m * etl in
    let cnst: polynomial (algebraic r) = poly_const (ac_const c) in
    let rhs : polynomial (algebraic r) = cnst + xtl in
    let aux (j:nat) : Lemma (coeff ep j = coeff rhs j) =
      if j = 0 then embed_cons_coeff_zero r c tl p
      else embed_cons_coeff_succ r c tl p j
    in
    poly_eq_by_coeff ep rhs aux
#pop-options

let embed_cons_eval (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                    (c: t) (tl: polynomial t)
                    (p: polynomial t {p == (c :: tl)})
  : Lemma (ensures
      ac_eq (poly_eval (ext_embed_poly p) (theta #_ #_ #r))
            ((ac_const c)
               + ((theta #_ #_ #r)
                  * (poly_eval (ext_embed_poly tl) (theta #_ #_ #r)))))
  = ac_elim_equatable_laws r;
    H.elim_equatable_laws (algebraic r) ();
    H.trans_for_calc (algebraic r) ();
    let th  : algebraic r = theta in
    let ep  : polynomial (algebraic r) = ext_embed_poly p in
    let etl : polynomial (algebraic r) = ext_embed_poly tl in
    let m   : polynomial (algebraic r) = monomial one 1 in
    let xtl : polynomial (algebraic r) = m * etl in
    let cnst: polynomial (algebraic r) = poly_const (ac_const c) in
    let rhs : polynomial (algebraic r) = cnst + xtl in
    (* theta IS the polynomial point; note theta.ac_rep = monomial one 1, but here
       `th` is the *evaluation point* of type (algebraic r). *)
    (* Step 1: poly_eval ep th = poly_eval rhs th (eval_congruence, via embed_cons_poly_eq) *)
    embed_cons_poly_eq r c tl p;             (* poly_eq ep rhs *)
    eval_congruence ep rhs th;  (* poly_eval ep th = poly_eval rhs th *)
    (* Step 2: poly_eval rhs th = poly_eval cnst th + poly_eval xtl th *)
    eval_add cnst xtl th;
    (* poly_eval cnst th = ac_const c *)
    eval_poly_const (ac_const c) th;
    (* poly_eval xtl th = poly_eval m th * poly_eval etl th ~ th * poly_eval etl th *)
    eval_mul m etl th;
    eval_X th;                  (* poly_eval m th = th *)
    mul_congruence
      (poly_eval m th) (poly_eval etl th)
      th (poly_eval etl th);    (* poly_eval m th * .. ~ th * .. *)
    (* combine summands: cnst-eval + xtl-eval ~ ac_const c + th * eval etl *)
    add_congruence
      (poly_eval cnst th) (poly_eval xtl th)
      (ac_const c)
      (th * (poly_eval etl th));
    transitivity
      (poly_eval rhs th)
      ((poly_eval cnst th) + (poly_eval xtl th))
      ((ac_const c) + (th * (poly_eval etl th)));
    transitivity
      (poly_eval ep th)
      (poly_eval rhs th)
      ((ac_const c) + (th * (poly_eval etl th)))

(* The embedded polynomial of a cons, viewed coefficient-wise, lets us run
   the generic Horner cons.  We prove the bridge by induction on the raw
   coefficient list of p. *)
let rec ext_embed_eval_aux (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                           (p: polynomial t)
  : Lemma (ensures ac_eq (poly_eval
                            (ext_embed_poly p) (theta #_ #_ #r))
                         (ac_eval p (theta #_ #_ #r)))
          (decreases (p <: list t))
  = ac_elim_equatable_laws r;
    H.elim_equatable_laws (algebraic r) ();
    H.trans_for_calc (algebraic r) ();
    let th : algebraic r = theta in
    let ep : polynomial (algebraic r) = ext_embed_poly p in
    match (p <: list t) with
    | [] ->
        (* ext_embed_poly [] = trim (map g []) = trim [] = [] = poly_zero;
           poly_eval poly_zero theta = zero(acr) = ac_zero ;
           ac_eval [] theta = ac_zero. *)
        (* ext_embed_poly [] = trim (map g []) = trim [] = [] = poly_zero. *)
        assert (L.map (ac_const #_ #_ #r) (p <: list t) == ([] <: list (algebraic r)));
        assert (ep == (poly_zero #(algebraic r)));
        eval_zero th     (* poly_eval poly_zero theta = zero(acr) *)
        (* zero(acr) == ac_zero by reveal ; ac_eval [] theta == ac_zero,
           closed by ac_elim_equatable_laws reflexivity. *)
    | c :: tl ->
        tail_trimmed c tl;                       (* tl is a trimmed polynomial *)
        let tlp : polynomial t = tl in
        (* IH: poly_eval (ext_embed_poly tl) theta ~ ac_eval tl theta *)
        ext_embed_eval_aux #_ #_ #r tlp;
        let evtl_e : algebraic r =
          poly_eval (ext_embed_poly #_ #_ #r tlp) th in
        let evtl_a : algebraic r = ac_eval_aux (tlp <: list t) th in
        (* The embedded polynomial ep, as a list, IS  (g c) :: (ext_embed_poly tl)
           up to trim ; we prove poly_eval ep theta ~ g c + theta * evtl_e
           by the generic Horner cons applied to the embedded list. *)
        embed_cons_eval #_ #_ #r c tlp p;
        (* embed_cons_eval gives:
             poly_eval ep theta ~ ac_const c + theta * poly_eval (ext_embed_poly tl) theta
           (the `+`,`*` being ac_add, ac_mul via reveal). *)
        (* ac_eval (c::tl) theta = ac_add (ac_const c) (ac_mul theta evtl_a) *)
        (* Combine: by IH evtl_e ~ evtl_a, so
             ac_const c + theta*evtl_e ~ ac_const c + theta*evtl_a = ac_eval p theta. *)
        mul_congruence th evtl_e th evtl_a;     (* theta*evtl_e ~ theta*evtl_a *)
        add_congruence
          (ac_const c) (th * evtl_e)
          (ac_const c) (th * evtl_a);
        (* RHS (ac_const c) + (th * evtl_a) == ac_eval p theta (defeq) *)
        transitivity
          (poly_eval ep th)
          ((ac_const c) + (th * evtl_e))
          ((ac_const c) + (th * evtl_a))

let ext_embed_eval (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                   (p: polynomial t)
  : Lemma (ac_eq (poly_eval
                    (ext_embed_poly p) (theta #_ #_ #r))
                 (ac_eval p (theta #_ #_ #r)))
  = ext_embed_eval_aux #_ #_ #r p

(* ================================================================ *)
(*  3.  theta is a root of the embedded multiple OVER the extension. *)
(* ================================================================ *)

let theta_root_ext (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                   (d: polynomial t)
  : Lemma (requires divides r d)
          (ensures ac_eq (poly_eval
                            (ext_embed_poly d) (theta #_ #_ #r))
                         (ac_zero #_ #_ #r))
  = H.elim_equatable_laws (algebraic r) ();
    ext_embed_eval #_ #_ #r d;                      (* poly_eval (embed d) theta ~ ac_eval d theta *)
    theta_root_of_multiple r d;                     (* ac_eval d theta ~ ac_zero *)
    transitivity
      (poly_eval (ext_embed_poly d) (theta #_ #_ #r))
      (ac_eval d (theta #_ #_ #r))
      (ac_zero #_ #_ #r)
