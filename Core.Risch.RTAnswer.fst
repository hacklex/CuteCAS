module Core.Risch.RTAnswer

(* ================================================================ *)
(*  ALGORITHM-LEVEL Rothstein-Trager answer theory.                  *)
(*                                                                   *)
(*  Connects the proven (abstract, partition-relative) RT soundness  *)
(*  capstone `Core.Risch.RTSoundness.rt_soundness_partition`         *)
(*  (Σ group_contribution = p/q) to the LRT ALGORITHM's actual       *)
(*  log-arguments  v_c = gcd(p - c.q', q).                            *)
(*                                                                   *)
(*  `group_contribution_is_vc_term` (the bridge): for g = the         *)
(*  COMPLETE residue-c class of roots,                                *)
(*    group_contribution p roots g  =  c · (v_c'/v_c)   (as fractions)*)
(*  i.e. the abstract per-group term IS the algorithm's term.         *)
(*                                                                   *)
(*  Math:  vc_factorization gives v_c = poly_scale (lc v_c) (∏g);     *)
(*  the log-derivative fraction is scale-invariant                    *)
(*    Fraction (c·D v_c) v_c = Fraction (c·D(∏g)) (∏g)                 *)
(*  (cross-multiply; D(poly_scale s u)=poly_scale s (D u); s cancels).*)
(*                                                                   *)
(*  NEXT (future, in this module): build the residue-class partition  *)
(*  of `roots`, discharge `rt_soundness_partition`'s hypotheses, and  *)
(*  assemble the end-to-end  d/dx[Σ_c c·log(gcd(p-c.q',q))] = p/q.     *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.Roots
open Core.Fractions
open Core.Risch.RTSoundness

#set-options "--fuel 2 --ifuel 1 --z3rlimit 10"

(* ---------------------------------------------------------------- *)
(*  poly_scale helpers (poly_scale a x == poly_mul (a@poly_zero) x). *)
(* ---------------------------------------------------------------- *)

(* poly_scale respects equality of the polynomial argument. *)
private let poly_scale_poly_congr (#t:Type) {| cr: commutative_ring t |}
  (a: t) (x y: polynomial t)
  : Lemma (requires (x = y)) (ensures (poly_scale a x = poly_scale a y))
  = H.elim_equatable_laws (polynomial t) ();
    poly_mul_congruence (a @ poly_zero) x (a @ poly_zero) y

(* poly_scale a x * y = poly_scale a (x * y)   (associativity). *)
private let poly_scale_mul_l (#t:Type) {| cr: commutative_ring t |}
  (a: t) (x y: polynomial t)
  : Lemma (((poly_scale a x) * y) = (poly_scale a (x * y)))
  = H.elim_equatable_laws (polynomial t) ();
    (* poly_scale a x * y = ((a@0)*x)*y = (a@0)*(x*y) = poly_scale a (x*y) *)
    poly_mul_associativity (a @ poly_zero) x y

(* x * poly_scale a y = poly_scale a (x * y)   (commute + assoc). *)
private let poly_scale_mul_r (#t:Type) {| cr: commutative_ring t |}
  (a: t) (x y: polynomial t)
  : Lemma ((x * (poly_scale a y)) = (poly_scale a (x * y)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* x*(scale a y) = x*((a@0)*y) = ((a@0)*y)*x = (a@0)*(y*x) = (a@0)*(x*y) *)
    poly_mul_commutativity x (poly_scale a y);          (* x*(scale a y) = (scale a y)*x *)
    poly_scale_mul_l a y x;                              (* (scale a y)*x = scale a (y*x) *)
    transitivity (x * (poly_scale a y))
                 ((poly_scale a y) * x)
                 (poly_scale a (y * x));
    poly_mul_commutativity y x;                                 (* y*x = x*y *)
    poly_scale_poly_congr a (y * x) (x * y);
    transitivity (x * (poly_scale a y))
                 (poly_scale a (y * x))
                 (poly_scale a (x * y))

(* ---------------------------------------------------------------- *)
(*  The residue-class hypothesis as an OPAQUE proposition (Q1):       *)
(*  `g` is exactly the residue-c class of roots, where c = residue at *)
(*  hd g.  Packages the three pointwise quantifiers (subset,          *)
(*  homogeneity, completeness) so no raw `forall` lands in a          *)
(*  consumer's SMT context.  Template: CRT.coprime_with_all.          *)
(* ---------------------------------------------------------------- *)
(* The homogeneity (all roots in `g` share the residue of `hd g`) and        *)
(* completeness (every root with that residue is in `g`) hypotheses, hidden   *)
(* behind an opaque proposition so neither `forall` lands in a consumer's SMT *)
(* context.  Both residue calls are guarded by `L.memP b roots` so the        *)
(* proposition is well-typed without the subset hypothesis (which is kept     *)
(* explicit on the lemma, since `group_contribution`/`residue` in the ensures *)
(* need it for well-definedness).  Template: CRT.coprime_with_all.            *)
[@@"opaque_to_smt"]
let residue_homog_complete (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t{all_distinct roots})
  (g: list t{Cons? g /\ L.memP (L.hd g) roots})
  : prop =
    forall (b:t). L.memP b roots ==>
      ((L.memP b g ==> residue p roots b = residue p roots (L.hd g)) /\
       (residue p roots b = residue p roots (L.hd g) ==> L.memP b g))

let residue_homog_complete_elim (#t:Type) {| f: field t |}
  (p: polynomial t) (roots: list t{all_distinct roots})
  (g: list t{Cons? g /\ L.memP (L.hd g) roots /\ residue_homog_complete p roots g})
  : Lemma (forall (b:t). L.memP b roots ==>
             ((L.memP b g ==> residue p roots b = residue p roots (L.hd g)) /\
              (residue p roots b = residue p roots (L.hd g) ==> L.memP b g)))
  = reveal_opaque (`%residue_homog_complete) (residue_homog_complete p roots g)

(* ---------------------------------------------------------------- *)
(*  (C)  vc = poly_gcd pp q is nonzero (deg vc >= 0, so vc != 0).     *)
(* ---------------------------------------------------------------- *)
private let vc_is_nonzero (#t:Type) {| f: field t |}
  (pp q: polynomial t)
  : Lemma (requires deg q >= 0)
          (ensures is_nonzero (poly_gcd pp q))
  = let vc = poly_gcd pp q in
    Core.Matrix.Resultant.gcd_pos pp q;           (* deg vc >= 0 *)
    Classical.move_requires
      (fun () -> Core.Polynomial.Unique.degree_well_defined vc (poly_zero #t)
                 <: Lemma (requires (vc = (poly_zero #t))) (ensures False))
      ()

(* ---------------------------------------------------------------- *)
(*  (E)  the cross-product equality                                  *)
(*    (c * D u) * vc  =  u * (c * D vc)                               *)
(*  given vc = poly_scale s u  (s = poly_lc vc).                      *)
(*  Uses D vc = poly_scale s (D u) (section D, derived inline).       *)
(* ---------------------------------------------------------------- *)
private let cross_product_eq (#t:Type) {| f: field t |}
  (c s: t) (u vc: polynomial t)
  : Lemma (requires (vc = poly_scale s u))
          (ensures ((poly_scale c (poly_deriv u)) * vc
                    = u * (poly_scale c (poly_deriv vc))))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();

    (* --- (D)  D vc = poly_scale s (D u) ------------------------------- *)
    poly_deriv_congruence vc (poly_scale s u);     (* D vc = D (scale s u) *)
    poly_deriv_scalar_mul s u;                     (* D ((s@0)*u) = (s@0)*(D u) *)
    poly_eq_transitivity (poly_deriv vc)
                         (poly_deriv (poly_scale s u))
                         (poly_scale s (poly_deriv u));

    let du : polynomial t = poly_deriv u in
    let lnum : polynomial t = poly_scale c du in
    let rnum : polynomial t = poly_scale c (poly_deriv vc) in

    (* lnum * vc = scale c (du * vc) = scale c (scale s (du*u)) *)
    poly_scale_mul_l c du vc;                      (* lnum*vc = scale c (du*vc) *)
    poly_mul_congruence du vc du (poly_scale s u); (* du*vc = du*(scale s u) *)
    poly_scale_mul_r s du u;                        (* du*(scale s u) = scale s (du*u) *)
    poly_eq_transitivity (du * vc)
                         (du * (poly_scale s u))
                         (poly_scale s (du * u));
    poly_scale_poly_congr c (du * vc) (poly_scale s (du * u));
    poly_eq_transitivity (lnum * vc)
                         (poly_scale c (du * vc))
                         (poly_scale c (poly_scale s (du * u)));

    (* RHS: u * rnum = scale c (scale s (du*u)) *)
    poly_scale_poly_congr c (poly_deriv vc) (poly_scale s du);  (* rnum = scale c (scale s du) *)
    poly_mul_congruence u rnum u (poly_scale c (poly_scale s du));
    poly_scale_mul_r c u (poly_scale s du);        (* u*(scale c X) = scale c (u*X) *)
    poly_eq_transitivity (u * rnum)
                         (u * (poly_scale c (poly_scale s du)))
                         (poly_scale c (u * (poly_scale s du)));
    poly_scale_mul_r s u du;                        (* u*(scale s du) = scale s (u*du) *)
    poly_mul_commutativity u du;                    (* u*du = du*u *)
    poly_scale_poly_congr s (u * du) (du * u);
    poly_eq_transitivity (u * (poly_scale s du))
                         (poly_scale s (u * du))
                         (poly_scale s (du * u));
    poly_scale_poly_congr c (u * (poly_scale s du)) (poly_scale s (du * u));
    poly_eq_transitivity (u * rnum)
                         (poly_scale c (u * (poly_scale s du)))
                         (poly_scale c (poly_scale s (du * u)));

    (* lnum*vc = scale c (scale s (du*u)) = u*rnum *)
    poly_eq_symmetry (u * rnum) (poly_scale c (poly_scale s (du * u)));
    poly_eq_transitivity (lnum * vc)
                         (poly_scale c (poly_scale s (du * u)))
                         (u * rnum)

let group_contribution_is_vc_term (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (g: list t)
  : Lemma (requires Cons? g /\ all_distinct g /\ all_distinct roots /\
                    (forall (b:t). L.memP b g ==> L.memP b roots) /\
                    L.memP (L.hd g) roots /\
                    residue_homog_complete p roots g)
          (ensures
            is_nonzero
              (poly_gcd
                 ((p -- (poly_scale (residue p roots (L.hd g))
                           (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                 (poly_prod_linears roots)) /\
            (group_contribution p roots g)
            = (Fraction #(polynomial t) #(polynomial_id #t)
                 (poly_scale (residue p roots (L.hd g))
                    (poly_deriv
                       (poly_gcd
                          ((p -- (poly_scale (residue p roots (L.hd g))
                                    (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                          (poly_prod_linears roots))))
                 (poly_gcd
                    ((p -- (poly_scale (residue p roots (L.hd g))
                              (poly_deriv (poly_prod_linears roots)))) <: polynomial t)
                    (poly_prod_linears roots))))
  = let id_p = polynomial_id #t in
    let c : t = residue p roots (L.hd g) in
    let u : polynomial t = poly_prod_linears g in
    let q : polynomial t = poly_prod_linears roots in
    let pp : polynomial t = (p -- (poly_scale c (poly_deriv q))) <: polynomial t in
    let vc : polynomial t = poly_gcd pp q in

    H.elim_equatable_laws (polynomial t) ();

    (* --- (A)  membership <==> for vc_factorization --------------------- *)
    residue_homog_complete_elim p roots g;
    assert (forall (b:t). L.memP b g <==>
                          (L.memP b roots /\ residue p roots b = c));

    (* --- (B)  vc = poly_scale (lc vc) u  ------------------------------- *)
    vc_factorization p roots c g;
    let s : t = poly_lc vc in
    (* vc_factorization gives:  vc = poly_scale s u   (equatable =) *)

    (* --- (C)  is_nonzero vc -------------------------------------------- *)
    poly_prod_linears_deg roots;                  (* deg q == length roots *)
    vc_is_nonzero pp q;
    let vcnz : (vv:polynomial t{is_nonzero vv}) = vc in

    (* --- (D+E)  the cross-product equality:  lnum*vc = u*rnum ---------- *)
    cross_product_eq c s u vc;
    let rnum : polynomial t = poly_scale c (poly_deriv vc) in
    assert (((poly_scale c (poly_deriv u)) * vc) = (u * rnum));

    (* --- (F)  conclude the fraction equality --------------------------- *)
    (* Mirror group_contribution's body so SMT sees it == Fraction pd v.   *)
    prod_linears_nonzero g;
    let v : (vv:polynomial t{is_nonzero vv}) = poly_prod_linears g in
    let pd : polynomial t =
      poly_scale c (poly_deriv (poly_prod_linears g)) in
    (* note: pd == lnum and v == u (definitionally). *)
    let xf : fraction id_p = Fraction pd v in
    let yf : fraction id_p = Fraction rnum vcnz in
    H.elim_equatable_laws (fraction id_p) ();
    (* cross product (fraction_eq_reveal):  pd * vc  =  v * rnum  i.e. lnum*vc = u*rnum *)
    fraction_eq_reveal xf yf;
    (* SMT:  group_contribution p roots g == xf  (definitional),  xf = yf. *)
    transitivity (group_contribution p roots g) xf yf
