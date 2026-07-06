module Core.AlgebraicConstant.EmbedTransport

(*
   §E splitting-field: EMBED-TRANSPORT pack.

   Small lemmas that push the coefficient-wise embedding

       ext_embed_poly : polynomial t -> polynomial (algebraic r)     (via ac_const)

   through the linear-factor / product-of-linears machinery of
   Core.Polynomial.Roots, plus the associated ac_const transport facts
   (nonzero / one / neg / sub / injectivity).

   Deliverables:
     - embed_deg          : deg (ext_embed_poly p) == deg p
     - embed_one          : ext_embed_poly poly_one = poly_one
     - embed_linear       : ext_embed_poly (poly_linear a) = poly_linear (ac_const a)
     - embed_const        : ext_embed_poly (poly_const c) = poly_const (ac_const c)
     - embed_const_mul    : ext_embed_poly (poly_const c * p)
                              = poly_const (ac_const c) * ext_embed_poly p
     - embed_prod_linears : ext_embed_poly (poly_prod_linears roots)
                              = poly_prod_linears (L.map ac_const roots)
     - embed_all_distinct : all_distinct roots ==> all_distinct (L.map ac_const roots)
*)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Irreducible
open Core.Polynomial.Roots
open Core.AlgebraicConstant
open Core.AlgebraicConstant.Root
open Core.AlgebraicConstant.Eval
open Core.AlgebraicConstant.EmbedHom
open Core.AlgebraicConstant.EmbedEval    (* ac_const_one *)

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  0.  ac_const transport facts.                                   *)
(* ================================================================ *)

(* ac_const of a NONZERO base element is nonzero in the extension:
   if [ac_const x] = 0 then r | poly_const x, but deg r >= 2 > 0 = deg(poly_const x). *)
let ac_const_nonzero (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                     (x: t)
  : Lemma (requires not (x = (zero <: t)))
          (ensures  not (ac_eq (ac_const #_ #_ #r x) (ac_zero #_ #_ #r)))
  = assert ((ac_const #_ #_ #r x <: polynomial t) == poly_const x)
      by (FStar.Tactics.norm [delta_only [`%ac_const]; iota; zeta]; FStar.Tactics.trefl ());
    poly_const_deg x;                       (* deg (poly_const x) == 0  (x <> zero) *)
    let aux () : Lemma (requires ac_eq (ac_const #_ #_ #r x) (ac_zero #_ #_ #r)) (ensures False)
      = ac_eq_zero_iff_divides (ac_const #_ #_ #r x);   (* r divides (ac_const x) == poly_const x *)
        divides_degree_le r (poly_const x)  (* deg r <= 0, contradicting deg r >= 2 *)
    in
    Classical.move_requires aux ()

(* ac_const one = ac_one is EmbedEval.ac_const_one. *)

(* ac_const (- x)  =  - (ac_const x)  (negation is a homomorphism, by uniqueness
   of the additive inverse). *)
let ac_const_neg (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                 (x: t)
  : Lemma (ac_eq (ac_const #_ #_ #r (- x)) (- (ac_const #_ #_ #r x)))
  = ac_elim_equatable_laws r;
    let ex  : algebraic r = ac_const #_ #_ #r x in
    let enx : algebraic r = ac_const #_ #_ #r (- x) in
    let nex : algebraic r = - ex in
    (* (1)  ex + enx  =  ac_zero *)
    ac_const_add #_ #_ #r x (- x);          (* ac_const (x + (-x)) = ex + enx *)
    H.x_plus_neg_x x;                       (* x + (-x) = zero  (base) *)
    ac_const_congr #_ #_ #r (x + (- x)) (zero <: t);   (* ac_const (x+(-x)) = ac_const zero *)
    ac_const_zero #_ #_ #r ();              (* ac_const zero = ac_zero *)
    (* (2)  ex + nex  =  zero(acr) == ac_zero *)
    H.x_plus_neg_x ex;                      (* ex + nex = zero(acr) *)
    algebraic_eq_zero_pointwise r;          (* zero(acr) == ac_zero *)
    (* (3)  cancel:  ex + enx = ex + nex  ==>  enx = nex *)
    H.group_cancel_left ex enx nex

(* ac_const (x -- y)  =  ac_const x -- ac_const y. *)
let ac_const_sub (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                 (x y: t)
  : Lemma (ac_eq (ac_const #_ #_ #r (x -- y))
                 ((ac_const #_ #_ #r x) -- (ac_const #_ #_ #r y)))
  = ac_elim_equatable_laws r;
    ac_const_add #_ #_ #r x (- y);          (* ac_const (x + (-y)) = ac_const x + ac_const (-y) *)
    ac_const_neg #_ #_ #r y;                (* ac_const (-y) = - (ac_const y) *)
    add_congruence (ac_const #_ #_ #r x) (ac_const #_ #_ #r (- y))
                   (ac_const #_ #_ #r x) (- (ac_const #_ #_ #r y));
    transitivity (ac_const #_ #_ #r (x -- y))
                 ((ac_const #_ #_ #r x) + (ac_const #_ #_ #r (- y)))
                 ((ac_const #_ #_ #r x) -- (ac_const #_ #_ #r y))

(* ac_const is INJECTIVE (on the field equality): x <> y ==> ac_const x <> ac_const y. *)
let ac_const_inj (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                 (x y: t)
  : Lemma (requires not (x = y))
          (ensures  not (ac_eq (ac_const #_ #_ #r x) (ac_const #_ #_ #r y)))
  = ac_elim_equatable_laws r;
    let aux () : Lemma (requires ac_eq (ac_const #_ #_ #r x) (ac_const #_ #_ #r y))
                       (ensures False)
      = ac_elim_equatable_laws r;
        H.sub_nonzero x y;                  (* (x -- y) <> zero *)
        (* ac_eq (ac_const x) (ac_const y) ==> ac_const x -- ac_const y = ac_zero *)
        H.sub_self_zero (ac_const #_ #_ #r x) (ac_const #_ #_ #r y);
        algebraic_eq_zero_pointwise r;      (* zero(acr) == ac_zero *)
        ac_const_sub #_ #_ #r x y;
                (* ac_const (x--y) = ac_const x -- ac_const y *)
        ac_eq_transitivity (ac_const #_ #_ #r (x -- y))
                     ((ac_const #_ #_ #r x) -- (ac_const #_ #_ #r y))
                     (ac_zero #_ #_ #r);
                (* ac_eq (ac_const (x--y)) ac_zero *)
        ac_const_nonzero #_ #_ #r (x -- y)  (* but (x--y) <> zero ==> NOT ac_eq ... : contradiction *)
    in
    Classical.move_requires aux ()

(* ================================================================ *)
(*  1.  embed_deg:  deg (ext_embed_poly p) == deg p.                *)
(* ================================================================ *)

(* last of a mapped list.  Generic list fact; a twin (last_map_lemma) lives in
   Core.Polynomial.EmbedQ — that module sits in the Polynomial layer and cannot
   import the AlgebraicConstant tower, and no shared list-helpers module exists,
   so both copies stay (cross-referenced). *)
#push-options "--fuel 2 --ifuel 2"
private let rec last_map (#a:Type) (#b:Type) (gm: a -> b) (l: list a {Cons? l})
  : Lemma (ensures L.last (L.map gm l) == gm (L.last l)) (decreases l)
  = match l with
    | [_]          -> ()
    | _ :: y :: tl -> last_map gm (y :: tl)
#pop-options

(* the coefficient-wise embedding of a (trimmed) polynomial is already trimmed:
   its leading coefficient ac_const (poly_lc p) is nonzero. *)
private let map_ac_const_trimmed (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                                 (p: polynomial t)
  : Lemma (is_trimmed (L.map (ac_const #_ #_ #r) p))
  = match p with
    | []      -> ()
    | _ :: _  ->
        let gm = ac_const #_ #_ #r in
        last_map gm p;                      (* L.last (map gm p) == gm (L.last p) *)
        assert (not ((L.last p) = (zero <: t)));   (* p trimmed, nonempty *)
        ac_const_nonzero #_ #_ #r (L.last p);      (* not (ac_eq (gm (L.last p)) ac_zero) *)
        algebraic_eq_zero_pointwise r              (* zero(acr) == ac_zero ; eq == ac_eq *)

let embed_deg (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
              (p: polynomial t)
  : Lemma (deg (ext_embed_poly #_ #_ #r p) == deg p)
  = let gm = ac_const #_ #_ #r in
    let m : list (algebraic r) = L.map gm p in
    L.map_lemma gm p;                       (* L.length m == L.length p *)
    map_ac_const_trimmed #_ #_ #r p;        (* is_trimmed m *)
    trim_poly_does_nothing m                (* trim m == m ; ext_embed_poly p == trim m *)

(* ================================================================ *)
(*  2.  embed_one:  ext_embed_poly poly_one = poly_one.             *)
(* ================================================================ *)

#push-options "--fuel 4 --ifuel 2"
private let one_coeff0 (#u:Type) {| f: field u |} ()
  : Lemma (coeff (poly_one #u) 0 = (one <: u))
  = H.elim_equatable_laws u ();
    let _ : squash (not (one #u = zero)) = f.f_one_ne_zero in
    last_eq_index #u (poly_one #u) 0;
    poly_lc_reveal (poly_one #u)

private let one_coeffH (#u:Type) {| f: field u |} (j:nat{j >= 1})
  : Lemma (coeff (poly_one #u) j == (zero <: u))
  = H.elim_equatable_laws u ();
    let _ : squash (not (one #u = zero)) = f.f_one_ne_zero in
    poly_lc_reveal (poly_one #u);
    coeff_above_degree (poly_one #u) j
#pop-options

let embed_one (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r}) ()
  : Lemma (ext_embed_poly #_ #_ #r (poly_one #t) = (poly_one #(algebraic r)))
  = ac_elim_equatable_laws r;
    let lhs : polynomial (algebraic r) = ext_embed_poly #_ #_ #r (poly_one #t) in
    let rhs : polynomial (algebraic r) = poly_one in
    let aux (j:nat) : Lemma (coeff lhs j = coeff rhs j) =
      H.elim_equatable_laws t ();
      ac_elim_equatable_laws r;
      embed_coeff #_ #_ #r (poly_one #t) j;    (* coeff lhs j = ac_const (coeff (poly_one) j) *)
      if j = 0 then begin
        one_coeff0 #t ();                       (* coeff (poly_one #t) 0 = one *)
        one_coeff0 #(algebraic r) ();           (* coeff rhs 0 = ac_one *)
        ac_const_congr #_ #_ #r (coeff (poly_one #t) 0) (one <: t);
        ac_const_one #_ #_ #r ();               (* ac_const one = ac_one *)
        transitivity (coeff lhs 0) (ac_const #_ #_ #r (coeff (poly_one #t) 0))
                     (ac_const #_ #_ #r (one <: t));
        transitivity (coeff lhs 0) (ac_const #_ #_ #r (one <: t)) (ac_one #_ #_ #r)
      end else begin
        one_coeffH #t j;                        (* coeff (poly_one #t) j == zero *)
        one_coeffH #(algebraic r) j;            (* coeff rhs j == zero(acr) *)
        ac_const_congr #_ #_ #r (coeff (poly_one #t) j) (zero <: t);
        ac_const_zero #_ #_ #r ();              (* ac_const zero = ac_zero *)
        algebraic_eq_zero_pointwise r;          (* zero(acr) == ac_zero *)
        transitivity (coeff lhs j) (ac_const #_ #_ #r (coeff (poly_one #t) j))
                     (ac_const #_ #_ #r (zero <: t));
        transitivity (coeff lhs j) (ac_const #_ #_ #r (zero <: t)) (ac_zero #_ #_ #r)
      end
    in
    poly_eq_by_coeff lhs rhs aux

(* ================================================================ *)
(*  3.  embed_linear:  ext_embed_poly (poly_linear a)               *)
(*                       = poly_linear (ac_const a).                *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 2"
let embed_linear (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                 (a: t)
  : Lemma (ext_embed_poly #_ #_ #r (poly_linear a) = poly_linear (ac_const #_ #_ #r a))
  = ac_elim_equatable_laws r;
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    let lhs : polynomial (algebraic r) = ext_embed_poly #_ #_ #r (poly_linear a) in
    let rhs : polynomial (algebraic r) = poly_linear (ac_const #_ #_ #r a) in
    let aux (j:nat) : Lemma (coeff lhs j = coeff rhs j) =
      H.elim_equatable_laws t ();
      ac_elim_equatable_laws r;
      embed_coeff #_ #_ #r (poly_linear a) j;   (* coeff lhs j = ac_const (coeff (poly_linear a) j) *)
      if j = 0 then begin
        (* coeff (poly_linear a) 0 == (-a) ; coeff rhs 0 == - (ac_const a) *)
        ac_const_neg #_ #_ #r a;                (* ac_const (-a) = - (ac_const a) *)
        transitivity (coeff lhs 0) (ac_const #_ #_ #r (- a)) (- (ac_const #_ #_ #r a))
      end else if j = 1 then begin
        (* coeff (poly_linear a) 1 == one ; coeff rhs 1 == ac_one *)
        ac_const_one #_ #_ #r ();               (* ac_const one = ac_one *)
        transitivity (coeff lhs 1) (ac_const #_ #_ #r (one <: t)) (ac_one #_ #_ #r)
      end else begin
        (* both out of range: coeff (poly_linear a) j == zero ; coeff rhs j == zero(acr) *)
        ac_const_zero #_ #_ #r ();              (* ac_const zero = ac_zero *)
        algebraic_eq_zero_pointwise r;          (* zero(acr) == ac_zero *)
        transitivity (coeff lhs j) (ac_const #_ #_ #r (zero <: t)) (ac_zero #_ #_ #r)
      end
    in
    poly_eq_by_coeff lhs rhs aux
#pop-options

(* ================================================================ *)
(*  4.  embed_const:  ext_embed_poly (poly_const c)                 *)
(*                      = poly_const (ac_const c).                  *)
(* ================================================================ *)

let embed_const (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                (c: t)
  : Lemma (ext_embed_poly #_ #_ #r (poly_const c) = poly_const (ac_const #_ #_ #r c))
  = ac_elim_equatable_laws r;
    let gc : algebraic r = ac_const #_ #_ #r c in
    let lhs : polynomial (algebraic r) = ext_embed_poly #_ #_ #r (poly_const c) in
    let rhs : polynomial (algebraic r) = poly_const gc in
    let aux (j:nat) : Lemma (coeff lhs j = coeff rhs j) =
      H.elim_equatable_laws t ();
      ac_elim_equatable_laws r;
      embed_coeff #_ #_ #r (poly_const c) j;    (* coeff lhs j = ac_const (coeff (poly_const c) j) *)
      if j = 0 then begin
        poly_const_coeff0 c;                    (* coeff (poly_const c) 0 = c *)
        poly_const_coeff0 gc;                   (* coeff rhs 0 = gc = ac_const c *)
        ac_const_congr #_ #_ #r (coeff (poly_const c) 0) c;
        transitivity (coeff lhs 0) (ac_const #_ #_ #r (coeff (poly_const c) 0)) gc
      end else begin
        poly_const_coeff_high c j;              (* coeff (poly_const c) j = zero *)
        poly_const_coeff_high gc j;             (* coeff rhs j = zero(acr) *)
        ac_const_congr #_ #_ #r (coeff (poly_const c) j) (zero <: t);
        ac_const_zero #_ #_ #r ();              (* ac_const zero = ac_zero *)
        algebraic_eq_zero_pointwise r;          (* zero(acr) == ac_zero *)
        transitivity (coeff lhs j) (ac_const #_ #_ #r (coeff (poly_const c) j))
                     (ac_const #_ #_ #r (zero <: t));
        transitivity (coeff lhs j) (ac_const #_ #_ #r (zero <: t)) (ac_zero #_ #_ #r)
      end
    in
    poly_eq_by_coeff lhs rhs aux

(* ================================================================ *)
(*  5.  embed_const_mul:  scaling by a base constant transports.    *)
(* ================================================================ *)

let embed_const_mul (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                    (c: t) (p: polynomial t)
  : Lemma (ext_embed_poly #_ #_ #r ((poly_const c) * p)
           = (poly_const (ac_const #_ #_ #r c)) * (ext_embed_poly #_ #_ #r p))
  = H.elim_equatable_laws (polynomial (algebraic r)) ();
    ext_embed_poly_mul #_ #_ #r (poly_const c) p;   (* embed(pc*p) = embed(pc) * embed p *)
    embed_const #_ #_ #r c;                         (* embed(pc) = poly_const (ac_const c) *)
    mul_congruence
      (ext_embed_poly #_ #_ #r (poly_const c)) (ext_embed_poly #_ #_ #r p)
      (poly_const (ac_const #_ #_ #r c))       (ext_embed_poly #_ #_ #r p);
    transitivity
      (ext_embed_poly #_ #_ #r ((poly_const c) * p))
      ((ext_embed_poly #_ #_ #r (poly_const c)) * (ext_embed_poly #_ #_ #r p))
      ((poly_const (ac_const #_ #_ #r c)) * (ext_embed_poly #_ #_ #r p))

(* ================================================================ *)
(*  6.  embed_prod_linears:  push through a product of linears.     *)
(* ================================================================ *)

let rec embed_prod_linears (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                           (roots: list t)
  : Lemma (ensures (ext_embed_poly #_ #_ #r (poly_prod_linears roots))
                   = (poly_prod_linears (L.map (ac_const #_ #_ #r) roots)))
          (decreases roots)
  = H.elim_equatable_laws (polynomial (algebraic r)) ();
    match roots with
    | []        -> embed_one #_ #_ #r ()
    | a :: rest ->
        let gm = ac_const #_ #_ #r in
        ext_embed_poly_mul #_ #_ #r (poly_linear a) (poly_prod_linears rest);
        embed_linear #_ #_ #r a;                    (* embed(pl a) = poly_linear (gm a) *)
        embed_prod_linears #_ #_ #r rest;           (* IH *)
        mul_congruence
          (ext_embed_poly #_ #_ #r (poly_linear a))
          (ext_embed_poly #_ #_ #r (poly_prod_linears rest))
          (poly_linear (gm a))
          (poly_prod_linears (L.map gm rest));
        transitivity
          (ext_embed_poly #_ #_ #r (poly_prod_linears (a :: rest)))
          ((ext_embed_poly #_ #_ #r (poly_linear a))
             * (ext_embed_poly #_ #_ #r (poly_prod_linears rest)))
          ((poly_linear (gm a)) * (poly_prod_linears (L.map gm rest)))

(* ================================================================ *)
(*  7.  embed_all_distinct:  ac_const preserves pairwise distinctness. *)
(* ================================================================ *)

let rec embed_all_distinct (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                           (roots: list t)
  : Lemma (requires all_distinct roots)
          (ensures  all_distinct (L.map (ac_const #_ #_ #r) roots))
          (decreases roots)
  = match roots with
    | []        -> ()
    | c :: cs   ->
        let gm = ac_const #_ #_ #r in
        embed_all_distinct #_ #_ #r cs;             (* all_distinct (map gm cs) *)
        introduce forall (d': algebraic r). L.memP d' (L.map gm cs) ==> not ((gm c) = d')
        with begin
          introduce L.memP d' (L.map gm cs) ==> not ((gm c) = d')
          with _memp. begin
            L.memP_map_elim gm d' cs;               (* exists d. memP d cs /\ gm d == d' *)
            eliminate exists (d: t). L.memP d cs /\ gm d == d'
            returns not ((gm c) = d')
            with _pf. begin
              assert (not (c = d));                 (* from all_distinct (c::cs) *)
              ac_const_inj #_ #_ #r c d             (* not (gm c = gm d) ; gm d == d' *)
            end
          end
        end

(* ================================================================ *)
(*  8.  embed_lc:  the leading coefficient transports.               *)
(* ================================================================ *)

let embed_lc (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
             (p: polynomial t)
  : Lemma (requires deg p >= 0)
          (ensures  ac_eq (poly_lc (ext_embed_poly #_ #_ #r p))
                          (ac_const #_ #_ #r (poly_lc p)))
  = ac_elim_equatable_laws r;
    let gm = ac_const #_ #_ #r in
    let m : list (algebraic r) = L.map gm p in
    L.map_lemma gm p;                       (* L.length m == L.length p *)
    map_ac_const_trimmed #_ #_ #r p;        (* is_trimmed m *)
    trim_poly_does_nothing m;               (* trim m == m ; ext_embed_poly p == m *)
    last_map gm p;                          (* L.last m == gm (L.last p) *)
    poly_lc_reveal (ext_embed_poly #_ #_ #r p);   (* lc (embed p) == L.last m *)
    poly_lc_reveal p                        (* poly_lc p == L.last p *)
