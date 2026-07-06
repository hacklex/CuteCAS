module Core.Polynomial.DerivPower

(*
   Power rule for the formal derivative of univariate polynomials over a
   commutative ring:

     D(d^m) ≈ m · ( d^(m-1) · D(d) )

   where `m · (-)` is `nat_scale` at the POLYNOMIAL add_comm_group level
   (repeated poly_add), NOT a scalar multiplication.

   Proof: induction on m, modelled on `deriv_power_divisibility` in
   Core.Polynomial.Irreducible.
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* The add_comm_group of the polynomial commutative_ring instance.
   Its `.add`/`.zero` are `poly_add`/`poly_zero`. *)
unfold
let pacg (#t:Type) (cr: commutative_ring t) : add_comm_group (polynomial t #cr)
  = (polynomial_cr #t #cr).cr_r.r_add

#push-options "--fuel 2 --z3rlimit 80"
let rec poly_deriv_power (#t:Type) {| cr: commutative_ring t |}
  (d: polynomial t) (m: pos)
  : Lemma (ensures
      (poly_deriv (poly_power d m))
      = (nat_scale #(polynomial t) #(pacg cr) m
                 ((poly_power d (m - 1)) * (poly_deriv d))))
    (decreases m)
  =
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let dd  = poly_deriv d in
    if m = 1 then begin
      (* LHS: poly_power d 1 == poly_mul d (poly_power d 0) == poly_mul d poly_one.
         poly_mul_one : poly_eq (poly_mul d poly_one) d, so
         poly_power d 1 = d, hence D(d^1) = D(d). *)
      poly_mul_one d;                                   (* poly_eq (poly_mul d poly_one) d *)
      (* poly_power d 1 == poly_mul d (poly_power d 0) == poly_mul d poly_one [defeq] *)
      poly_deriv_congruence (poly_power d 1) d;
      (* poly_eq (poly_deriv (poly_power d 1)) (poly_deriv d) *)

      (* RHS: nat_scale 1 (poly_mul (poly_power d 0) (poly_deriv d))
              = nat_scale 1 (poly_mul poly_one dd).
         poly_mul_one : poly_eq (poly_mul poly_one dd) dd
         nat_scale_congruence : nat_scale 1 (poly_mul poly_one dd) = nat_scale 1 dd
         nat_scale_one : nat_scale 1 dd = dd *)
      let x1 = (poly_power d 0) * dd in   (* == poly_one * dd *)
      poly_mul_one dd;                                  (* poly_eq (poly_mul poly_one dd) dd *)
      nat_scale_congruence 1 x1 dd;
      nat_scale_one dd;
      (* nat_scale 1 x1 = dd ; both sides ≈ dd, so combine by trans+sym
         (universally available from the (polynomial t) elim/trans helpers). *)
      ()
    end
    else begin
      (* m >= 2. poly_power d m == poly_mul d (poly_power d (m-1)) [defeq]. *)
      let dm1 = poly_power d (m - 1) in          (* d^(m-1) *)
      let dm2 = poly_power d (m - 2) in          (* d^(m-2) *)
      let ddm1 = poly_deriv dm1 in               (* D(d^(m-1)) *)
      let xX = dm1 * dd in                       (* X = d^(m-1)·D(d) *)

      (* --- Product rule on d · d^(m-1) --- *)
      poly_deriv_mul d dm1;
      (* poly_eq (poly_deriv (poly_mul d dm1))
                 (poly_add (poly_mul dd dm1) (poly_mul d ddm1)) *)
      (* poly_power d m == poly_mul d dm1 [defeq], so LHS == poly_deriv (poly_power d m) *)
      let t1 = dd * dm1 in                       (* D(d)·d^(m-1) *)
      let t2 = d * ddm1 in                       (* d·D(d^(m-1)) *)

      (* ============ Term t2 = d·D(d^(m-1)) ≈ nat_scale (m-1) X ============ *)
      (* IH: D(d^(m-1)) ≈ nat_scale (m-1) (d^(m-2)·D(d)) *)
      poly_deriv_power d (m - 1);
      let xY = dm2 * dd in                       (* Y = d^(m-2)·D(d) *)
      (* ddm1 ≈ nat_scale (m-1) xY *)

      (* t2 = poly_mul d ddm1 ≈ poly_mul d (nat_scale (m-1) xY) [right congruence] *)
      poly_mul_right_congruence d ddm1 (nat_scale (m - 1) xY);
      (* poly_eq (poly_mul d ddm1) (poly_mul d (nat_scale (m-1) xY)) *)

      (* poly_mul d (nat_scale (m-1) xY) ≈ nat_scale (m-1) (poly_mul d xY) [nat_scale_mul_right] *)
      nat_scale_mul_right (m - 1) d xY;
      (* poly_eq (poly_mul d (nat_scale (m-1) xY)) (nat_scale (m-1) (poly_mul d xY)) ;
         t2 ≈ nat_scale (m-1) (poly_mul d xY) by transitivity (laws in scope) *)

      (* poly_mul d xY = poly_mul d (poly_mul dm2 dd) ≈ poly_mul (poly_mul d dm2) dd [assoc rev] *)
      mul_associativity d dm2 dd;
      (* poly_eq (poly_mul (poly_mul d dm2) dd) (poly_mul d (poly_mul dm2 dd)) ;
         symmetric direction available from the equatable laws in scope. *)
      (* poly_mul d dm2 == poly_power d (m-1) == dm1 [defeq] since (m-1) >= 1 *)
      (* so poly_mul (poly_mul d dm2) dd == poly_mul dm1 dd == xX [defeq] *)
      nat_scale_congruence (m - 1)
        (d * xY) ((d * dm2) * dd);
      (* nat_scale (m-1) (poly_mul d xY) = nat_scale (m-1) xX [defeq target] ;
         t2 ≈ nat_scale (m-1) xX by transitivity (laws in scope) *)

      (* ============ Term t1 = D(d)·d^(m-1) ≈ nat_scale 1 X ============ *)
      mul_commutativity dd dm1;
      (* poly_eq (poly_mul dd dm1) (poly_mul dm1 dd) = poly_eq t1 xX *)
      nat_scale_one xX;
      (* nat_scale 1 xX = xX ; t1 ≈ nat_scale 1 xX by sym+trans (laws in scope) *)

      (* ============ Sum: t1 + t2 ≈ nat_scale m xX ============ *)
      poly_add_congruence
        t1 t2
        (nat_scale 1 xX)
        (nat_scale (m - 1) xX);
      (* poly_eq (poly_add t1 t2)
                 (poly_add (nat_scale 1 xX) (nat_scale (m-1) xX)) *)
      nat_scale_add 1 (m - 1) xX;
      (* nat_scale (1 + (m-1)) xX = poly_add (nat_scale 1 xX) (nat_scale (m-1) xX)
         and 1 + (m-1) == m *)
      assert ((1 ++ (m - 1)) == m)
    end
#pop-options
