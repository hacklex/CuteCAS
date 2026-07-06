module Core.Matrix.Sylvester

(* INTERNAL — do not import directly; helper bridged into Core.Matrix.Resultant (Sylvester matrix construction). No .fsti by design. *)

(*
   Sylvester matrix construction.

   Given two univariate polynomials over a commutative ring,
       p = p_0 + p_1*x + ... + p_m * x^m,
       q = q_0 + q_1*x + ... + q_n * x^n,
   the Sylvester matrix S(p, q) is the (m+n) x (m+n) square matrix
   built by stacking n shifted copies of p atop m shifted copies of q.

   This module establishes the construction and lookup lemmas only.
   Its determinant — the resultant — is studied in a downstream module.

   All nat/int index arithmetic uses `( ++ )` (= `Prims.op_Addition`,
   from `Core.Algebra.Notation`) for addition and plain `( - )` for
   subtraction, to avoid clashing with the typeclass `+` overload.

   The polynomial convention here is "coefficient at index i is the
   coefficient of x^i", which matches `Core.Polynomial.coeff`.
*)

module TC = FStar.Tactics.Typeclasses
module L = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Permutation
open Core.Matrix
open Core.Polynomial

(* These nat/int wrappers are re-exported (via `open`) into the downstream
   `Core.Matrix.Resultant`, which uses them in its own signatures; they are
   kept here for that consumer. Inside this module we write `( ++ )` / `( - )`. *)
unfold let nat_add (a b: nat) : nat = a ++ b
unfold let nat_sub (a: nat) (b: nat{b <= a}) : nat = a - b
unfold let int_add (a b: int) : int = a ++ b
unfold let int_sub (a b: int) : int = a - b

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
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0}) (p q: polynomial t)
  : square_matrix t (m_deg ++ n_deg)
  = fun (i: fin (m_deg ++ n_deg)) (j: fin (m_deg ++ n_deg)) ->
      let i_nat : nat = i in
      let j_nat : nat = j in
      if i_nat < n_deg then
        coeff p ((m_deg ++ i_nat) - j_nat)
      else
        coeff q (i_nat - j_nat)

(* ------------------------------------------------------------------ *)
(*  Lookup lemmas                                                     *)
(* ------------------------------------------------------------------ *)

let sylvester_p_block_lookup
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0}) (p q: polynomial t)
  (i j: fin (m_deg ++ n_deg))
  : Lemma (requires i < n_deg)
          (ensures sylvester_matrix m_deg n_deg p q i j
                == coeff p ((m_deg ++ i) - j))
  = ()

let sylvester_q_block_lookup
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0}) (p q: polynomial t)
  (i j: fin (m_deg ++ n_deg))
  : Lemma (requires i >= n_deg)
          (ensures sylvester_matrix m_deg n_deg p q i j
                == coeff q (i - j))
  = ()

let sylvester_p_block_in_range
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0}) (p q: polynomial t)
  (i j: fin (m_deg ++ n_deg))
  : Lemma (requires i < n_deg /\
                    j <= (i ++ m_deg) /\
                    j >= i)
          (ensures sylvester_matrix m_deg n_deg p q i j
                == coeff p ((m_deg ++ i) - j))
  = ()

let sylvester_p_block_right_zero
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0}) (p q: polynomial t)
  (i j: fin (m_deg ++ n_deg))
  : Lemma (requires i < n_deg /\
                    j > (i ++ m_deg))
          (ensures sylvester_matrix m_deg n_deg p q i j == (zero <: t))
  = ()

let sylvester_p_block_left_zero
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0}) (p q: polynomial t)
  (i j: fin (m_deg ++ n_deg))
  : Lemma (requires i < n_deg /\
                    j < i /\
                    L.length p <= (m_deg ++ 1))
          (ensures sylvester_matrix m_deg n_deg p q i j == (zero <: t))
  = let i_nat : nat = i in
    let j_nat : nat = j in
    let idx_int : int = (m_deg ++ i_nat) - j_nat in
    assert (idx_int > m_deg);
    let idx : nat = idx_int in
    assert (idx >= L.length p);
    assert (coeff p idx == (zero <: t))

let sylvester_q_block_in_range
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0}) (p q: polynomial t)
  (i j: fin (m_deg ++ n_deg))
  : Lemma (requires i >= n_deg /\
                    j <= ((i - n_deg) ++ n_deg) /\
                    j <= i)
          (ensures sylvester_matrix m_deg n_deg p q i j
                == coeff q (i - j))
  = ()

let sylvester_q_block_right_zero
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0}) (p q: polynomial t)
  (i j: fin (m_deg ++ n_deg))
  : Lemma (requires i >= n_deg /\
                    j > i)
          (ensures sylvester_matrix m_deg n_deg p q i j == (zero <: t))
  = ()

let sylvester_q_block_left_zero
  (#t: Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0}) (p q: polynomial t)
  (i j: fin (m_deg ++ n_deg))
  : Lemma (requires i >= n_deg /\
                    (j ++ n_deg) < i /\
                    L.length q <= (n_deg ++ 1))
          (ensures sylvester_matrix m_deg n_deg p q i j == (zero <: t))
  = ()
