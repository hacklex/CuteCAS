(* ================================================================ *)
(*  UFD factorization-EXISTENCE for polynomials over a field.        *)
(*                                                                   *)
(*  Every polynomial p of degree >= 1 over ANY field factors as a    *)
(*  product of irreducible polynomials, with the product EQUAL to    *)
(*  p (hence in particular an associate of p — mutual divisibility). *)
(*  Proved GENERICALLY over {| field t |} by strong induction on     *)
(*  degree.                                                          *)
(*                                                                   *)
(*  This is the non-square-free companion of                         *)
(*  Core.Modular.PrimeField.BerlekampComplete.complete_factorization_*)
(*  exists: it DROPS the square_free hypothesis (and, correspondingly*)
(*  the pairwise-coprime / distinctness conclusion), keeping only    *)
(*  "product of irreducibles = p".  Used to factor the RT resultant  *)
(*  R into its Q-irreducible factors for the vc-explicit rendering.  *)
(*                                                                   *)
(*  NO admit / assume / sorry.  Lemma / ghost / Tot only.            *)
(* ================================================================ *)

module Core.Polynomial.FactorizationExists

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module IR = Core.Polynomial.Irreducible
module PR = Core.Polynomial.Roots
module ID = FStar.IndefiniteDescription
module BC = Core.Modular.PrimeField.BerlekampComplete

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.GCD
open Core.Polynomial.SquareFree
open Core.Polynomial.Div

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  Auxiliary: exact-product factorization (strong induction).       *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec poly_factorization_exists_aux (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires deg p >= 1)
          (ensures exists (facs: list (polynomial t)).
             Cons? facs /\
             (PR.poly_prod facs = p) /\
             (forall (g: polynomial t). L.memP g facs ==> IR.poly_irreducible g))
          (decreases (if deg p >= 0 then deg p else 0))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* 1. an irreducible factor q | p *)
    IR.irreducible_factor_exists p;
    let q : polynomial t =
      ID.indefinite_description_ghost (polynomial t)
        (fun q -> IR.poly_irreducible q /\ divides q p) in
    assert (IR.poly_irreducible q /\ divides q p);
    assert (deg q >= 1);                                 (* from poly_irreducible q *)
    (* 2. cofactor:  q * cof = p *)
    let cof = poly_div p q in
    poly_div_correct p q;                                (* (q * cof) = p *)
    IR.poly_div_degree p q;                              (* deg cof == deg p - deg q *)
    if deg cof = 0 then begin
      (* BASE: p is an associate of the irreducible q, hence irreducible. *)
      poly_eq_symmetry (q * cof) p;                      (* p = q * cof *)
      BC.irreducible_associate q cof p;                  (* poly_irreducible p *)
      let facs : list (polynomial t) = [p] in
      poly_mul_one p;                                    (* (p * poly_one) = p *)
      assert (PR.poly_prod facs = p);
      introduce exists (facs: list (polynomial t)).
                  Cons? facs /\ (PR.poly_prod facs = p) /\
                  (forall (g: polynomial t). L.memP g facs ==> IR.poly_irreducible g)
      with facs and ()
    end else begin
      (* RECURSE on cof (deg cof >= 1 and strictly below deg p). *)
      assert (deg cof >= 1);
      assert (deg cof < deg p);                          (* deg q >= 1 *)
      poly_factorization_exists_aux cof;
      eliminate exists (fcof: list (polynomial t)).
                  Cons? fcof /\ (PR.poly_prod fcof = cof) /\
                  (forall (g: polynomial t). L.memP g fcof ==> IR.poly_irreducible g)
      returns (exists (facs: list (polynomial t)).
                  Cons? facs /\ (PR.poly_prod facs = p) /\
                  (forall (g: polynomial t). L.memP g facs ==> IR.poly_irreducible g))
      with _.
      begin
        let facs : list (polynomial t) = q :: fcof in
        (* poly_prod (q::fcof) = q * poly_prod fcof = q * cof = p *)
        assert (PR.poly_prod facs == (q * (PR.poly_prod fcof)));
        poly_mul_right_congruence q (PR.poly_prod fcof) cof;
        poly_eq_transitivity (q * (PR.poly_prod fcof)) (q * cof) p;
        assert (PR.poly_prod facs = p);
        introduce exists (facs: list (polynomial t)).
                    Cons? facs /\ (PR.poly_prod facs = p) /\
                    (forall (g: polynomial t). L.memP g facs ==> IR.poly_irreducible g)
        with facs and ()
      end
    end
#pop-options

(* ================================================================ *)
(*  PUBLIC: UFD factorization existence (associate form).            *)
(*                                                                   *)
(*  There is a non-empty list of irreducible polynomials whose       *)
(*  product is an associate of p (mutual divisibility).              *)
(* ================================================================ *)

let poly_factorization_exists (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires deg p >= 1)
          (ensures exists (facs: list (polynomial t)).
             Cons? facs /\
             (divides (PR.poly_prod facs) p /\ divides p (PR.poly_prod facs)) /\
             (forall (g: polynomial t). L.memP g facs ==> IR.poly_irreducible g))
  = H.elim_equatable_laws (polynomial t) ();
    poly_factorization_exists_aux p;
    eliminate exists (facs: list (polynomial t)).
                Cons? facs /\ (PR.poly_prod facs = p) /\
                (forall (g: polynomial t). L.memP g facs ==> IR.poly_irreducible g)
    returns (exists (facs: list (polynomial t)).
                Cons? facs /\
                (divides (PR.poly_prod facs) p /\ divides p (PR.poly_prod facs)) /\
                (forall (g: polynomial t). L.memP g facs ==> IR.poly_irreducible g))
    with _.
    begin
      let pr = PR.poly_prod facs in
      assert (pr = p);
      (* pr = p  ==>  pr | p  and  p | pr *)
      H.trans_for_calc (polynomial t) ();
      poly_mul_one pr;                                   (* (pr * poly_one) = pr *)
      poly_eq_transitivity (pr * (poly_one #t)) pr p;   (* (pr * poly_one) = p *)
      poly_eq_symmetry (pr * (poly_one #t)) p;          (* p = pr * poly_one *)
      divides_intro pr p (poly_one #t);                 (* divides pr p *)
      poly_mul_one p;                                    (* (p * poly_one) = p *)
      poly_eq_symmetry pr p;                            (* p = pr *)
      poly_eq_transitivity (p * (poly_one #t)) p pr;    (* (p * poly_one) = pr *)
      poly_eq_symmetry (p * (poly_one #t)) pr;          (* pr = p * poly_one *)
      divides_intro p pr (poly_one #t);                 (* divides p pr *)
      introduce exists (facs: list (polynomial t)).
                  Cons? facs /\
                  (divides (PR.poly_prod facs) p /\ divides p (PR.poly_prod facs)) /\
                  (forall (g: polynomial t). L.memP g facs ==> IR.poly_irreducible g)
      with facs and ()
    end
