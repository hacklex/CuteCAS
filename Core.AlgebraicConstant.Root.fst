module Core.AlgebraicConstant.Root

(*
   §E foundation: evaluation map on the algebraic extension
       algebraic r = t[X] / (r)
   and the fact that the class of X (= theta) is a ROOT of the modulus r.

   Deliverables:
     - ac_const c       : the class of the constant polynomial [c]
     - theta            : the class of X = monomial one 1
     - ac_eval p a      : Horner evaluation of p at a
     - modulus_vanishes : [r] = 0 in the quotient
     - ac_eval_is_class : ac_eval p theta = [p]
     - theta_root_of_modulus : ac_eval r theta = 0
*)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Algebra.CongruenceMod
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Irreducible
open Core.FinSum
open Core.AlgebraicConstant

(* ================================================================ *)
(*  1.  Constructions                                               *)
(* ================================================================ *)

(* The class of the constant polynomial [c].  Reduced already: deg (poly_const c)
   is -1 or 0, both < deg r (deg r >= 2). *)
let ac_const (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
             (c: t)
  : algebraic r
  = poly_const_deg c;
    (poly_const c)

(* to avoid unneeded ac_const #t #f #r x in favor of ac_embed r x*)
unfold let ac_embed #t #f r x = ac_const #t #f #r x 

(* The class of X = monomial one 1.  Reduced: deg (monomial one 1) = 1 < deg r. *)
let theta (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  : algebraic r
  = monomial_deg (one <: t) 1;
    (monomial one 1)

(* Horner evaluation over the coefficient list (raw list recursion). *)
let rec ac_eval_aux (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                    (p: list t) (a: algebraic r)
  : Tot (algebraic r) (decreases p)
  = match p with
    | []      -> zero
    | c :: tl -> (ac_const c) + (a * (ac_eval_aux tl a))

let ac_eval (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
            (p: polynomial t) (a: algebraic r)
  : algebraic r
  = ac_eval_aux p a

(* ================================================================ *)
(*  Bridge: poly_eq of reps  =>  ac_eq  (reconstructed; the         *)
(*  originals in Core.AlgebraicConstant are private).               *)
(* ================================================================ *)

let sub_zero_of_poly_eq
    (#t:Type) {| cr: commutative_ring t |} (a b: polynomial t)
  : Lemma (requires a = b)
          (ensures  (a -- b) = poly_zero)
  = H.elim_equatable_laws (polynomial t) ();
    poly_add_congruence a (- b) b (- b);
    poly_add_negation b;       (* b + (- b) ~ poly_zero *)
    transitivity (a + (- b))
                 (b + (- b))
                 poly_zero

let poly_eq_implies_ac_eq
    (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
    (a b: algebraic r)
  : Lemma (requires poly_eq a b)
          (ensures  ac_eq a b)
  = let x = a in
    let y = (b <: polynomial t) in
    sub_zero_of_poly_eq x y;
    divides_zero r;
    symmetry (x -- y) poly_zero;
    divides_congruence_right r poly_zero (x -- y);
    ac_eq_divides a b

(* ================================================================ *)
(*  Local CanonRing identities used by class_of_divides_iff_pub below.      *)
(*  The congruence-modulo toolkit (cong / cong_trans / cong_mul /     *)
(*  cong_add / cong_of_eq) is the generic one from                    *)
(*  Core.Algebra.CongruenceMod; the class_of bridges                  *)
(*  (class_of_cong / class_of_cong_sym / ac_eq_of_cong) come from     *)
(*  Core.AlgebraicConstant.                                           *)
(* ================================================================ *)

private let cr_add_sub_cancel_pub
    (#u:Type) {| cr: commutative_ring u |} (a m: u)
  : Lemma (eq (a + (m + (- a))) m)
  = assert (eq (a + (m + (- a))) m)
      by Core.Tactics.CanonRing.canon_ring ()

private let cr_sub_sub_self_pub
    (#u:Type) {| cr: commutative_ring u |} (m a: u)
  : Lemma (eq (m + (- (m + (- a)))) a)
  = assert (eq (m + (- (m + (- a)))) a)
      by Core.Tactics.CanonRing.canon_ring ()

(* ================================================================ *)
(*  4.  modulus_vanishes:  [r] = 0  in the quotient.                *)
(* ================================================================ *)

(* class_of p is divisible by r iff p is (class_of p ~ p mod r).  Local downstream
   reconstruction using the exposed keystone class_of_mod. *)
let class_of_divides_iff_pub (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  (p: polynomial t)
  : Lemma (divides r (class_of r p) <==> divides r p)
  = let m = (class_of r p) in
    class_of_mod #_ #_ #r p;                                  (* r | (m -- p) *)
    let fwd () : Lemma (requires divides r p) (ensures divides r m)
      = divides_add r p (m -- p);                       (* r | (p + (m--p)) *)
        cr_add_sub_cancel_pub p m;      (* p + (m--p) ~ m *)
        divides_congruence_right r (p + (m -- p)) m in
    let bwd () : Lemma (requires divides r m) (ensures divides r p)
      = divides_sub r m (m -- p);                        (* r | (m -- (m--p)) *)
        cr_sub_sub_self_pub m p;         (* m -- (m--p) ~ p *)
        divides_congruence_right r (m -- (m -- p)) p in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

let modulus_vanishes (#t:Type) {| f: field t |}
                     (r: polynomial t {proper_extension r})
  : Lemma (ac_eq (class_of r r) (ac_zero #_ #_ #r))
  = divides_refl r;
    class_of_divides_iff_pub #_ #_ #r r;            (* divides r (class_of r r) <==> divides r r *)
    ac_eq_zero_iff_divides (class_of r r)

(* ================================================================ *)
(*  5.  ac_eval_is_class.                                            *)
(* ================================================================ *)

(* coeff of X*tl at index 0 is zero (X has zero constant term).  *)
let x_mul_coeff_zero (#t:Type) {| cr: commutative_ring t |} (q: polynomial t)
  : Lemma (coeff ((monomial one 1) * q) 0 = zero)
  = H.elim_equatable_laws t ();
    let m : polynomial t = monomial one 1 in
    let g (i:nat) : t = zero in
    let h (i:nat)
      : Lemma (g i = coeff m i * coeff q (0 - i))
      = if i = 0 then begin
          (* coeff m 0 = zero, so zero * coeff q 0 = zero *)
          monomial_coeff (one <: t) 1 0;     (* coeff m 0 = zero *)
          mul_congruence (coeff m 0) (coeff q (0 - 0))
                         zero (coeff q (0 - 0));
          H.zero_mul_x (coeff q (0 - 0));
          (* coeff m 0 * coeff q 0 = zero * coeff q 0 = zero ; want g 0 = that *)
          transitivity (coeff m 0 * coeff q (0 - 0))
                       (zero * coeff q (0 - 0))
                       zero
        end
        else begin
          (* coeff q (0 - i) = coeff q (negative) = zero, so _ * zero = zero *)
          mul_congruence (coeff m i) (coeff q (0 - i))
                         (coeff m i) zero;
          H.x_mul_zero (coeff m i);
          transitivity (coeff m i * coeff q (0 - i))
                       (coeff m i * zero)
                       zero
        end
    in
    coeff_poly_mul_named m q 0 g h;
    sum_range_all_zero g 0 (L.length m) H.obvious;
    transitivity (coeff (m * q) 0)
                 (sum_range g 0 (L.length m))
                 zero

(* coeff of X*tl at index i+1 equals coeff tl i. *)
let x_mul_coeff_succ (#t:Type) {| cr: commutative_ring t |} (q: polynomial t) (i: nat)
  : Lemma (coeff ((monomial one 1) * q) (i ++ 1)
           = coeff q i)
  = H.elim_equatable_laws t ();
    (* monomial_mul_coeff one 1 q i : coeff (m * q) (1+i) = one * coeff q i *)
    monomial_mul_coeff one 1 q i;
    H.one_mul_x (coeff q i);
    transitivity (coeff ((monomial one 1) * q) (1 ++ i))
                 (one * coeff q i)
                 (coeff q i)

(* Tail of a trimmed list is trimmed (public reconstruction). *)
let tail_trimmed (#t:Type) {| cr: commutative_ring t |} (c: t) (tl: list t)
  : Lemma (requires is_trimmed (c :: tl))
          (ensures  is_trimmed tl)
  = match tl with
    | []      -> ()
    | x :: xs -> ()   (* L.last (c::tl) == L.last tl, and length>0 *)

(* The Horner cons reconstruction:
     poly_const c + X * tl  ~  (c :: tl)   when (c :: tl) is trimmed. *)
let horner_cons (#t:Type) {| cr: commutative_ring t |}
                (c: t) (tl: polynomial t)
                (p: polynomial t {p == (c :: tl)})
  : Lemma (((poly_const c)
            + ((monomial one 1) * tl))
           = p)
  = H.elim_equatable_laws t ();
    let xtl : polynomial t = (monomial one 1) * tl in
    let lhs : polynomial t = (poly_const c) + xtl in
    let aux (j:nat) : Lemma (coeff lhs j = coeff p j) =
      poly_add_coeff (poly_const c) xtl j;
      if j = 0 then begin
        (* coeff lhs 0 = coeff(poly_const c) 0 + coeff(X*tl) 0 = c + 0 = c *)
        let cc0 : t = coeff (poly_const c) 0 in
        let cx0 : t = coeff xtl 0 in
        poly_const_coeff0 c;                         (* coeff (poly_const c) 0 = c *)
        x_mul_coeff_zero tl;                         (* coeff (X*tl) 0 = zero *)
        add_congruence cc0 cx0 c zero;
        H.x_plus_zero c;
        transitivity (cc0 + cx0) (c + zero) c;
        (* coeff p 0 = c since p = c :: tl *)
        assert (coeff p 0 == c);
        transitivity (coeff lhs 0) (cc0 + cx0) c
      end
      else begin
        let i = j - 1 in
        let ctli : t = coeff tl i in
        let ccj  : t = coeff (poly_const c) j in
        let cxj  : t = coeff xtl j in
        poly_const_coeff_high c j;                   (* coeff (poly_const c) j = zero *)
        x_mul_coeff_succ tl i;                       (* coeff (X*tl) j = coeff tl i *)
        add_congruence ccj cxj zero ctli;
        H.zero_plus_x ctli;
        transitivity (ccj + cxj)
                     (zero + ctli)
                     ctli;
        (* coeff p j = coeff (c :: tl) j = coeff tl (j-1) = coeff tl i *)
        assert (coeff p j == ctli);
        transitivity (coeff lhs j) (ccj + cxj) ctli
      end
    in
    poly_eq_by_coeff lhs p aux

(* ac_eval_aux p theta  ~  [p]  for any list p that is a polynomial. *)
let rec ac_eval_is_class_aux (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                             (p: polynomial t)
  : Lemma (ensures ac_eq (ac_eval_aux p (theta #_ #_ #r))
                         (class_of r p))
          (decreases p)
  = H.elim_equatable_laws (polynomial t) ();
    H.elim_equatable_laws (algebraic r) ();
    match p with
    | [] ->
        (* ac_eval_aux [] theta = ac_zero ; goal: ac_eq ac_zero (class_of []).
           class_of [] ~ [] (mod r), r | [], so [class_of []] = 0 = ac_zero. *)
        divides_zero r;                                       (* r | poly_zero = [] *)
        class_of_divides_iff_pub #_ #_ #r poly_zero;           (* r | class_of [] <==> r | [] *)
        ac_eq_zero_iff_divides (class_of r poly_zero);
        (* ac_eq (class_of []) ac_zero ; symmetrize to ac_eq ac_zero (class_of []) *)
        symmetry (class_of r poly_zero)
                 (ac_zero #_ #_ #r)
    | c :: tl ->
        (* tl is a trimmed polynomial (tail of a trimmed list). *)
        tail_trimmed c tl;
        let tlp : polynomial t = tl in
        (* IH: ac_eval_aux tl theta ~ class_of tl *)
        ac_eval_is_class_aux #_ #_ #r tlp;
        let evtl : algebraic r = ac_eval_aux tlp theta in
        let th   : algebraic r = theta in
        let mtl  : algebraic r = class_of r tlp in
        (* By IH + congruence:  ac_mul theta evtl ~ ac_mul theta (class_of tl) *)
        mul_congruence th evtl th mtl;
        add_congruence (ac_const c) (th * evtl)
                          (ac_const c) (th * mtl);
        let stepc : algebraic r = (ac_const c) + (th * mtl) in
        (* stepc <: polynomial t  ==  poly_add (poly_const c) (class_of (X * class_of tl)). *)
        ac_add_rep (ac_const c) (th * mtl);          (* stepc == poly_add (ac_const c) (th * mtl) *)
        ac_mul_rep th mtl;                                 (* th * mtl == class_of (X * class_of tl) *)
        let xc : polynomial t = monomial one 1 in
        let pc : polynomial t = poly_const c in
        let mtlp : polynomial t = mtl in
        let xmtl : polynomial t = xc * mtlp in
        (* cong chain: stepc ~ class_of p  (mod r). *)
        (* (1) poly_add pc (class_of xmtl) ~ poly_add pc xmtl    [class_of on 2nd summand] *)
        class_of_cong r xmtl;                              (* class_of xmtl ~ xmtl *)
        cong_of_eq r pc pc;                                (* pc ~ pc (mod r) *)
        cong_add r pc pc (class_of r xmtl) xmtl;
        (* (2) pc + xmtl = pc + (X * tl)     [class_of tl ~ tl, mul_l] *)
        class_of_cong r tlp;                               (* class_of tl ~ tl *)
        cong_refl r xc;
        cong_mul r xc xc mtlp tlp;          (* X*(class_of tl) ~ X*tl *)
        cong_add r pc pc xmtl (xc * tlp);
        cong_trans r
          (pc + (class_of r xmtl)) (pc + xmtl) (pc + (xc * tlp));
        (* (3) pc + (X*tl) = p                      [horner_cons, exact] *)
        horner_cons c tlp p;          (* (pc + X*tl) = p *)
        cong_of_eq r (pc + (xc * tlp)) p;
        cong_trans r
          (pc + (class_of r xmtl)) (pc + (xc * tlp)) p;
        (* (4) p ~ class_of p *)
        class_of_cong_sym r p;
        cong_trans r
          (pc + (class_of r xmtl)) p (class_of r p);
        (* stepc == poly_add pc (class_of xmtl) (defeq via reps), so cong stepc (class_of r p). *)
        ac_eq_of_cong r stepc (class_of r p);
        (* chain: ac_eval_aux p theta == stepterm ~ stepc ~ class_of p *)
        transitivity (ac_const c + th * evtl) stepc (class_of r p)

let ac_eval_is_class (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                     (p: polynomial t)
  : Lemma (ac_eq (ac_eval p (theta #_ #_ #r))
                 (class_of r p))
  = ac_eval_is_class_aux #_ #_ #r p

(* ================================================================ *)
(*  6.  theta is a root of the modulus.                             *)
(* ================================================================ *)

let theta_root_of_modulus (#t:Type) {| f: field t |}
                          (r: polynomial t {proper_extension r})
  : Lemma (ac_eq (ac_eval r theta) (ac_zero #_ #_ #r))
  = ac_eval_is_class #_ #_ #r r;            (* ac_eval r theta ~ class_of r *)
    modulus_vanishes r;               (* class_of r ~ 0 *)
    transitivity (ac_eval r theta) (class_of r r) (ac_zero #_ #_ #r)

(* ================================================================ *)
(*  7.  theta is a root of ANY multiple of the modulus.             *)
(*      In particular, if r is an irreducible factor of d (r | d),  *)
(*      then theta = [X] in t[X]/(r) is a root of d — the seed of    *)
(*      the splitting-field construction (peel (X - theta) from d).  *)
(* ================================================================ *)

let theta_root_of_multiple (#t:Type) {| f: field t |}
                           (r: polynomial t {proper_extension r}) (d: polynomial t)
  : Lemma (requires divides r d)
          (ensures ac_eval d theta = ac_zero #_ #_ #r)
  = ac_eval_is_class #_ #_ #r d;            (* ac_eval d theta ~ class_of d *)
    (* [class_of d] = 0  <==>  r | class_of d  <==>  r | d  (given). *)
    class_of_divides_iff_pub #_ #_ #r d;
    ac_eq_zero_iff_divides (class_of r d);
    transitivity (ac_eval d theta) (class_of r d) (ac_zero #_ #_ #r)
