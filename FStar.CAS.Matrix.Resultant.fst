module FStar.CAS.Matrix.Resultant

(*
  The resultant of two univariate polynomials, defined as the determinant
  of their Sylvester matrix.

  Given p, q in polynomial t with formal degree bounds m_deg, n_deg, the
  Sylvester matrix is (m_deg + n_deg) x (m_deg + n_deg) and the resultant
  is its determinant. The resultant lives in the coefficient ring t.

  This module provides:
    - the `resultant` definition,
    - lookup-driven structural lemmas connecting `resultant` to
      `sylvester_matrix` (so downstream callers don't have to peek
      inside the definition),
    - basic degenerate cases (one polynomial has degree zero, e.g.
      n_deg = 0 makes the Sylvester matrix lower-triangular when p has
      its top coefficient picked out).
*)

module TC = FStar.Tactics.Typeclasses

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Multiplicative
open FStar.CAS.Ringlikes
open FStar.CAS.Polynomial
open FStar.CAS.Matrix
open FStar.CAS.Permutation
open FStar.CAS.Matrix.Determinant
open FStar.CAS.Matrix.Sylvester

unfold let nat_add (a b: nat) : nat = Prims.op_Addition a b
unfold let nat_sub (a: nat) (b: nat{b <= a}) : nat = Prims.op_Subtraction a b
unfold let nat_mul (a b: nat) : nat = Prims.op_Star a b

(* ------------------------------------------------------------------------ *)
(*  Definition.                                                             *)
(* ------------------------------------------------------------------------ *)

let resultant (#t: Type) {| cr: commutative_ring t |}
              (m_deg n_deg: nat) (p q: polynomial t) : t
  = det (sylvester_matrix #t #cr.ring.semiring m_deg n_deg p q)

let resultant_unfold (#t: Type) {| cr: commutative_ring t |}
                     (m_deg n_deg: nat) (p q: polynomial t)
  : Lemma (resultant #t #cr m_deg n_deg p q
           == det (sylvester_matrix #t #cr.ring.semiring m_deg n_deg p q))
  = ()

(* ------------------------------------------------------------------------ *)
(*  Trivial case: m_deg = n_deg = 0 produces a 0x0 matrix whose             *)
(*  determinant is one.                                                     *)
(* ------------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let resultant_zero_zero
  (#t: Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma (resultant #t #cr 0 0 p q = cr.ring.semiring.mul_monoid.has_one.one)
  = let r : ring t = cr.ring in
    let h1 = r.semiring.mul_monoid.has_one in
    det_identity #t #r 0;
    let m1 : square_matrix t 0 = sylvester_matrix #t #r.semiring 0 0 p q in
    let m2 : square_matrix t 0 = id_matrix #t 0 in
    let pw (a b: fin 0) : Lemma (m1 a b = m2 a b)
      = false_elim () in
    Classical.forall_intro_2 pw;
    det_pointwise_eq #t #r #0 m1 m2;
    reflexivity h1.one;
    transitivity (resultant #t #cr 0 0 p q) (det m2) h1.one
#pop-options

(* ------------------------------------------------------------------------ *)
(*  If the Sylvester matrix has an all-zero row or column, resultant = 0.   *)
(* ------------------------------------------------------------------------ *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let resultant_zero_of_zero_row
  (#t: Type) {| cr: commutative_ring t |} (m_deg n_deg: nat)
  (p q: polynomial t) (k: fin (nat_add m_deg n_deg))
  : Lemma (requires forall (j: fin (nat_add m_deg n_deg)).
                      sylvester_matrix #t #cr.ring.semiring m_deg n_deg p q k j
                      = cr.ring.semiring.add_comm_monoid.add_monoid.has_zero.zero)
          (ensures resultant #t #cr m_deg n_deg p q
                   = cr.ring.semiring.add_comm_monoid.add_monoid.has_zero.zero)
  = let r : ring t = cr.ring in
    det_zero_row #t #r #(nat_add m_deg n_deg)
                 (sylvester_matrix #t #r.semiring m_deg n_deg p q) k

let resultant_zero_of_zero_col
  (#t: Type) {| cr: commutative_ring t |} (m_deg n_deg: nat)
  (p q: polynomial t) (j: fin (nat_add m_deg n_deg))
  : Lemma (requires forall (k: fin (nat_add m_deg n_deg)).
                      sylvester_matrix #t #cr.ring.semiring m_deg n_deg p q k j
                      = cr.ring.semiring.add_comm_monoid.add_monoid.has_zero.zero)
          (ensures resultant #t #cr m_deg n_deg p q
                   = cr.ring.semiring.add_comm_monoid.add_monoid.has_zero.zero)
  = det_zero_column #t #cr #(nat_add m_deg n_deg)
                    (sylvester_matrix #t #cr.ring.semiring m_deg n_deg p q) j
#pop-options

(* ====================================================================== *)
(*  L3: Resultant skew-symmetry                                            *)
(*       res(p, q, m, n) = (-1)^(m*n) * res(q, p, n, m)                    *)
(*                                                                         *)
(*  Strategy: the Sylvester matrix for (q, p, n, m) is obtained from the   *)
(*  one for (p, q, m, n) by a block-swap permutation of rows. Determinant  *)
(*  picks up the sign of that permutation, which is (-1)^(m*n).            *)
(* ====================================================================== *)

(* Pointwise: applying block_swap_perm to rows of sylvester m n p q yields
   sylvester n m q p (modulo nat-add commutativity in the index type). *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let sylvester_block_swap_pointwise
  (#t: Type) {| sr: semiring t |}
  (m_deg n_deg: nat) (p q: polynomial t)
  (i: fin (nat_add m_deg n_deg))
  (j: fin (nat_add m_deg n_deg))
  : Lemma (let src = sylvester_matrix #t #sr m_deg n_deg p q in
           let dst = sylvester_matrix #t #sr n_deg m_deg q p in
           let sigma = block_swap_perm m_deg n_deg in
           let i' : fin (nat_add n_deg m_deg) = (i <: nat) in
           let j' : fin (nat_add n_deg m_deg) = (j <: nat) in
           permute_rows src sigma i j == dst i' j')
  = block_swap_perm_fwd m_deg n_deg i
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 120"
let resultant_skew_symmetry
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat) (p q: polynomial t)
  : Lemma (resultant #t #cr n_deg m_deg q p =
           (if (nat_mul m_deg n_deg) % 2 = 0
            then resultant #t #cr m_deg n_deg p q
            else -(resultant #t #cr m_deg n_deg p q)))
  = let r : ring t = cr.ring in
    let sr : semiring t = r.semiring in
    let nn : nat = nat_add m_deg n_deg in
    assert (nn == nat_add n_deg m_deg);
    let src : square_matrix t nn = sylvester_matrix #t #sr m_deg n_deg p q in
    let dst : square_matrix t nn = sylvester_matrix #t #sr n_deg m_deg q p in
    let sigma : permutation nn = block_swap_perm m_deg n_deg in
    let pr : square_matrix t nn = permute_rows src sigma in
    let pw (a b: fin nn) : Lemma (pr a b = dst a b)
      = sylvester_block_swap_pointwise #t #sr m_deg n_deg p q a b;
        reflexivity (pr a b) in
    Classical.forall_intro_2 pw;
    det_pointwise_eq #t #r #nn pr dst;
    (* det pr = det dst *)
    det_permute_rows #t #cr #nn src sigma;
    (* det pr = (if parity sigma then det src else -det src) *)
    parity_block_swap m_deg n_deg;
    (* parity sigma == ((m * n) % 2 = 0) *)
    resultant_unfold #t #cr m_deg n_deg p q;
    resultant_unfold #t #cr n_deg m_deg q p;
    let lhs = resultant #t #cr n_deg m_deg q p in
    let rhs_pos = resultant #t #cr m_deg n_deg p q in
    assert (lhs == det dst);
    assert (rhs_pos == det src);
    reflexivity (det dst);
    reflexivity (det src);
    assert (lhs = det dst);
    assert (rhs_pos = det src);
    symmetry (det pr) (det dst);
    assert (det dst = det pr);
    if (nat_mul m_deg n_deg) % 2 = 0 then begin
      assert (parity sigma == true);
      assert (det pr = det src);
      transitivity lhs (det dst) (det pr);
      transitivity lhs (det pr) (det src);
      symmetry rhs_pos (det src);
      transitivity lhs (det src) rhs_pos;
      assert (lhs = rhs_pos)
    end else begin
      assert (parity sigma == false);
      assert (det pr = -(det src));
      transitivity lhs (det dst) (det pr);
      transitivity lhs (det pr) (-(det src));
      reflexivity (-(det src));
      assert (-(det src) == -(rhs_pos));
      assert (-(det src) = -(rhs_pos));
      transitivity lhs (-(det src)) (-(rhs_pos));
      assert (lhs = -(rhs_pos))
    end
#pop-options
