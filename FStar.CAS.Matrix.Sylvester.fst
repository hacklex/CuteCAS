module FStar.CAS.Matrix.Sylvester

(*
  Sylvester matrix construction.

  Given two univariate polynomials
      p = p_m x^m + p_{m-1} x^{m-1} + ... + p_0,
      q = q_n x^n + q_{n-1} x^{n-1} + ... + q_0,
  the Sylvester matrix S(p, q) has dimension (m + n) x (m + n) and is the
  block stack of n shifted copies of p atop m shifted copies of q.  The
  first n rows shift p; the next m rows shift q.

  This module establishes the construction and lookup lemmas only.  Its
  determinant (the resultant) is studied in a downstream module.

  All nat-arithmetic uses `Prims.op_Addition` / `Prims.op_Subtraction`
  explicitly to avoid clashing with the typeclass `+`/`-` operators that
  the algebra tower brings into scope.
*)

module TC = FStar.Tactics.Typeclasses

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Multiplicative
open FStar.CAS.Ringlikes
open FStar.CAS.Polynomial
open FStar.CAS.Permutation
open FStar.CAS.Matrix

unfold let nat_add (a b: nat) : nat = Prims.op_Addition a b
unfold let nat_sub (a: nat) (b: nat{b <= a}) : nat = Prims.op_Subtraction a b
unfold let int_add (a b: int) : int = Prims.op_Addition a b
unfold let int_sub (a b: int) : int = Prims.op_Subtraction a b

(* ------------------------------------------------------------------------ *)
(*  Safe coefficient lookup with integer index.                             *)
(* ------------------------------------------------------------------------ *)

let safe_coeff (#t: Type) {| h: has_zero t |}
               (p: polynomial t) (i: int) : t
  = if i >= 0 then coeff p i else zero

let safe_coeff_neg (#t: Type) {| h: has_zero t |}
                   (p: polynomial t) (i: int)
  : Lemma (requires i < 0)
          (ensures safe_coeff p i == zero #t) = ()

let safe_coeff_nonneg (#t: Type) {| h: has_zero t |}
                      (p: polynomial t) (i: nat)
  : Lemma (safe_coeff p i == coeff p i) = ()

(* ------------------------------------------------------------------------ *)
(*  Sylvester matrix                                                        *)
(*                                                                          *)
(*  Parameterized by formal degree bounds (m_deg, n_deg) for p, q. The      *)
(*  caller asserts that p has degree <= m_deg and q has degree <= n_deg.    *)
(* ------------------------------------------------------------------------ *)

let sylvester_matrix (#t: Type) {| sr: semiring t |}
                     (m_deg n_deg: nat) (p q: polynomial t)
                     : square_matrix t (nat_add m_deg n_deg)
  = fun (i: fin (nat_add m_deg n_deg)) (j: fin (nat_add m_deg n_deg)) ->
      let i_nat : nat = i in
      let j_nat : nat = j in
      if i_nat < n_deg then
        (* p-block: row i shifts p by i columns. Entry index = m_deg + i - j. *)
        safe_coeff p (int_sub (int_add m_deg i_nat) j_nat)
      else
        (* q-block: row n_deg + s shifts q by s columns; entry index = s + n_deg - j = i - j. *)
        safe_coeff q (int_sub i_nat j_nat)

(* ------------------------------------------------------------------------ *)
(*  Lookup lemmas: identify the entries of the Sylvester matrix.            *)
(* ------------------------------------------------------------------------ *)

let sylvester_p_block_in_range
  (#t: Type) {| sr: semiring t |} (m_deg n_deg: nat)
  (p q: polynomial t) (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) < n_deg
                  /\ (i <: nat) <= (j <: nat)
                  /\ (j <: nat) <= nat_add (i <: nat) m_deg)
          (ensures sylvester_matrix m_deg n_deg p q i j
                   == coeff p (nat_sub (nat_add m_deg (i <: nat)) (j <: nat))) = ()

(* p-block, j > i + m_deg: column is past the shifted copy of p.
   The Sylvester entry is unconditionally zero. *)
let sylvester_p_block_right_zero
  (#t: Type) {| sr: semiring t |} (m_deg n_deg: nat)
  (p q: polynomial t) (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) < n_deg /\ (j <: nat) > nat_add (i <: nat) m_deg)
          (ensures sylvester_matrix m_deg n_deg p q i j == zero #t) = ()

(* p-block, j < i: requires `coeff p (m_deg + i - j) = zero`, i.e., a degree
   bound on p. We state it as an explicit hypothesis. *)
let sylvester_p_block_left_zero
  (#t: Type) {| sr: semiring t |} (m_deg n_deg: nat)
  (p q: polynomial t) (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) < n_deg /\ (j <: nat) < (i <: nat)
                  /\ coeff p (nat_sub (nat_add m_deg (i <: nat)) (j <: nat))
                       == zero #t)
          (ensures sylvester_matrix m_deg n_deg p q i j == zero #t) = ()

let sylvester_q_block_in_range
  (#t: Type) {| sr: semiring t |} (m_deg n_deg: nat)
  (p q: polynomial t) (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) >= n_deg
                  /\ nat_sub (i <: nat) n_deg <= (j <: nat)
                  /\ (j <: nat) <= (i <: nat))
          (ensures sylvester_matrix m_deg n_deg p q i j
                   == coeff q (nat_sub (i <: nat) (j <: nat))) = ()

(* q-block, j > i: column is past the shifted copy of q. Unconditionally zero. *)
let sylvester_q_block_right_zero
  (#t: Type) {| sr: semiring t |} (m_deg n_deg: nat)
  (p q: polynomial t) (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) >= n_deg /\ (j <: nat) > (i <: nat))
          (ensures sylvester_matrix m_deg n_deg p q i j == zero #t) = ()

(* q-block, j < i - n_deg: requires degree bound on q
   (coeff q (i - j) = zero when i - j > n_deg). *)
let sylvester_q_block_left_zero
  (#t: Type) {| sr: semiring t |} (m_deg n_deg: nat)
  (p q: polynomial t) (i j: fin (nat_add m_deg n_deg))
  : Lemma (requires (i <: nat) >= n_deg
                  /\ (j <: nat) < nat_sub (i <: nat) n_deg
                  /\ coeff q (nat_sub (i <: nat) (j <: nat)) == zero #t)
          (ensures sylvester_matrix m_deg n_deg p q i j == zero #t) = ()

(* ------------------------------------------------------------------------ *)
(*  Top-left and bottom-right corner anchors.                               *)
(* ------------------------------------------------------------------------ *)

let sylvester_top_left
  (#t: Type) {| sr: semiring t |} (m_deg n_deg: nat)
  (p q: polynomial t)
  : Lemma (requires n_deg > 0)
          (ensures sylvester_matrix m_deg n_deg p q
                     ((0 <: nat) <: fin (nat_add m_deg n_deg))
                     ((0 <: nat) <: fin (nat_add m_deg n_deg))
                   == coeff p m_deg) = ()

let sylvester_bottom_right
  (#t: Type) {| sr: semiring t |} (m_deg n_deg: nat)
  (p q: polynomial t)
  : Lemma (requires m_deg > 0)
          (ensures
            (let last : fin (nat_add m_deg n_deg) =
               (nat_sub (nat_add m_deg n_deg) 1 <: nat) <: fin (nat_add m_deg n_deg) in
             sylvester_matrix m_deg n_deg p q last last
             == coeff q 0)) = ()
