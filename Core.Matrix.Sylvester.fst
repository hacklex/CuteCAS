module Core.Matrix.Sylvester

(*
   Sylvester matrix construction.

   Given two univariate polynomials over a commutative ring,
       p = p_0 + p_1*x + ... + p_m * x^m,
       q = q_0 + q_1*x + ... + q_n * x^n,
   the Sylvester matrix S(p, q) is the (m+n) x (m+n) square matrix
   built by stacking n shifted copies of p atop m shifted copies of q.

   This module establishes the construction and lookup lemmas only.
   Its determinant — the resultant — is studied in a downstream module.

   All nat-arithmetic uses `Prims.op_Addition` / `Prims.op_Subtraction`
   explicitly to avoid clashing with the typeclass `+` brought in by
   `Core.Algebra.Notation`.

   The polynomial convention here is "coefficient at index i is the
   coefficient of x^i", which matches `Core.Polynomial.coeff`.
*)

module TC = FStar.Tactics.Typeclasses
module L = FStar.List.Tot

open Core.Algebra
open Core.Permutation
open Core.Matrix
open Core.Polynomial

unfold let nat_add (a b: nat) : nat = Prims.op_Addition a b
unfold let nat_sub (a: nat) (b: nat{b <= a}) : nat = Prims.op_Subtraction a b
unfold let int_add (a b: int) : int = Prims.op_Addition a b
unfold let int_sub (a b: int) : int = Prims.op_Subtraction a b

(* ------------------------------------------------------------------ *)
(*  Sylvester matrix                                                  *)
(*                                                                    *)
(*  Parameterized by formal degree bounds (m_deg, n_deg) for p, q.    *)
(*  The caller is expected to ensure p has degree <= m_deg and q has  *)
(*  degree <= n_deg (i.e. coefficients above those bounds vanish).    *)
(*                                                                    *)
(*  Layout:                                                           *)
(*    - rows 0 .. n_deg - 1     : shifted copies of p                 *)
(*    - rows n_deg .. m+n - 1   : shifted copies of q                 *)
(*                                                                    *)
(*  Entry formula (matches the standard textbook Sylvester layout     *)
(*  with descending column degrees):                                  *)
(*    S[i][j] = p_{m_deg + i - j}   for 0 <= i < n_deg                *)
(*    S[i][j] = q_{i - j}           for n_deg <= i                    *)
(*  (with `coeff` returning zero outside [0, deg] and for i < 0).    *)
(* ------------------------------------------------------------------ *)

let sylvester_matrix
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  : square_matrix t (nat_add m_deg n_deg)
  = fun (i: fin (nat_add m_deg n_deg)) (j: fin (nat_add m_deg n_deg)) ->
      let i_nat : nat = i in
      let j_nat : nat = j in
      if i_nat < n_deg then
        coeff p (int_sub (int_add m_deg i_nat) j_nat)
      else
        coeff q (int_sub i_nat j_nat)

(* ------------------------------------------------------------------ *)
(*  Lookup lemmas                                                     *)
(* ------------------------------------------------------------------ *)

let sylvester_p_block_lookup
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) < n_deg)
          (ensures sylvester_matrix m_deg n_deg p q i j
                == coeff p (int_sub (int_add m_deg i) j))
  = ()

let sylvester_q_block_lookup
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) >= n_deg)
          (ensures sylvester_matrix m_deg n_deg p q i j
                == coeff q (int_sub i j))
  = ()

let sylvester_p_block_in_range
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) < n_deg /\
                    (j <: nat) <= (i <: nat) + m_deg /\
                    (j <: nat) >= i)
          (ensures sylvester_matrix m_deg n_deg p q i j
                == coeff p (nat_sub (nat_add m_deg i) j))
  = ()

let sylvester_p_block_right_zero
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) < n_deg /\
                    (j <: nat) > (i <: nat) + m_deg)
          (ensures sylvester_matrix m_deg n_deg p q i j == (zero <: t))
  = ()

let sylvester_p_block_left_zero
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) < n_deg /\
                    (j <: nat) < i /\
                    L.length p <= nat_add m_deg 1)
          (ensures sylvester_matrix m_deg n_deg p q i j == (zero <: t))
  = let i_nat : nat = i in
    let j_nat : nat = j in
    let idx_int : int = int_sub (int_add m_deg i_nat) j_nat in
    assert (idx_int > m_deg);
    let idx : nat = idx_int in
    assert (idx >= L.length p);
    assert (coeff p idx == (zero <: t))

let sylvester_q_block_in_range
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) >= n_deg /\
                    (j <: nat) <= (i <: nat) - n_deg + n_deg /\
                    (j <: nat) <= (i <: nat))
          (ensures sylvester_matrix m_deg n_deg p q i j
                == coeff q (nat_sub i j))
  = ()

let sylvester_q_block_right_zero
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) >= n_deg /\
                    (j <: nat) > (i <: nat))
          (ensures sylvester_matrix m_deg n_deg p q i j == (zero <: t))
  = ()

let sylvester_q_block_left_zero
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{nat_add m_deg n_deg > 0}) (p q: polynomial t)
  (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) >= n_deg /\
                    (j <: nat) + n_deg < (i <: nat) /\
                    L.length q <= nat_add n_deg 1)
          (ensures sylvester_matrix m_deg n_deg p q i j == (zero <: t))
  = ()
