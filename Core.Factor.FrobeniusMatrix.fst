module Core.Factor.FrobeniusMatrix

(* ================================================================ *)
(*  C5c — the matrix <-> Frobenius BRIDGE.                          *)
(*                                                                   *)
(*  Establishes the correspondence between the concrete list-matrix *)
(*  fed to Core.LinearAlgebra.FpNullSpace and the Frobenius(-id)     *)
(*  endomorphism  h |-> (h^p mod fbar) - h  on  (fp p)[x]/(fbar).    *)
(*                                                                   *)
(*  poly_of_vec / vec_of_poly are the coordinate <-> polynomial      *)
(*  dictionary;  berlekamp_matrix_T is the TRANSPOSE of              *)
(*  BerlekampFactor.berlekamp_matrix (see the CONVENTION note).      *)
(* ================================================================ *)

module L   = FStar.List.Tot
module NS  = Core.LinearAlgebra.FpNullSpace
module BF  = Core.Factor.BerlekampFactor
module EU  = Core.NumberTheory

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Modular.PrimeField

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  1.  poly_of_vec / vec_of_poly                                    *)
(* ================================================================ *)

let poly_of_vec (#p:int{EU.is_prime p}) (v: NS.vector p) : polynomial (fp p)
  = trim v

(* [coeff h 0; ...; coeff h (n-1)] : the length-n coordinate vector of h. *)
let vec_of_poly (#p:int{EU.is_prime p}) (n:nat) (h: polynomial (fp p)) : NS.vector p
  = BF.vec_of h 0 n

(* ---------------- vec_of : length and entries ---------------- *)

let rec vec_of_length (#p:int{EU.is_prime p}) (g: polynomial (fp p)) (i n:nat)
  : Lemma (ensures L.length (BF.vec_of g i n) == n) (decreases n)
  = if n = 0 then () else vec_of_length g (i ++ 1) (n - 1)

let rec vec_of_index (#p:int{EU.is_prime p}) (g: polynomial (fp p)) (i n j:nat)
  : Lemma (requires j < n)
          (ensures  (vec_of_length g i n;
                     L.index (BF.vec_of g i n) j == coeff g (i + j)))
          (decreases n)
  = vec_of_length g i n;
    if j = 0 then ()
    else begin
      vec_of_length g (i ++ 1) (n - 1);
      vec_of_index g (i ++ 1) (n - 1) (j - 1)
    end

let vec_of_poly_length (#p:int{EU.is_prime p}) (n:nat) (h: polynomial (fp p))
  : Lemma (L.length (vec_of_poly n h) == n)
  = vec_of_length h 0 n

let vec_of_poly_get (#p:int{EU.is_prime p}) (n:nat) (h: polynomial (fp p)) (j:nat)
  : Lemma (requires j < n)
          (ensures  NS.get (vec_of_poly n h) j == coeff h j)
  = vec_of_length h 0 n;
    vec_of_index h 0 n j

(* ---------------- poly_of_vec : coefficients ---------------- *)

(* trim never changes the coordinate function. *)
let poly_of_vec_coeff (#p:int{EU.is_prime p}) (v: NS.vector p) (j:nat)
  : Lemma (coeff (poly_of_vec v) j == NS.get v j)
  = coeff_trim v j

(* ================================================================ *)
(*  2.  Round-trip  poly_of_vec (vec_of_poly n h) = h   (deg h < n). *)
(* ================================================================ *)

let round_trip_coeff (#p:int{EU.is_prime p}) (n:nat) (h: polynomial (fp p)) (j:nat)
  : Lemma (requires deg h < n)
          (ensures  coeff (poly_of_vec (vec_of_poly n h)) j == coeff h j)
  = poly_of_vec_coeff (vec_of_poly n h) j;    (* coeff pov j == get (vec_of_poly n h) j *)
    vec_of_poly_length n h;
    if j < n then vec_of_poly_get n h j
    else begin
      (* both zero: get (vec) j = 0 since j >= length; coeff h j = 0 since deg h < n <= j *)
      reflexivity (coeff h j)
    end

let round_trip (#p:int{EU.is_prime p}) (n:nat) (h: polynomial (fp p))
  : Lemma (requires deg h < n)
          (ensures  poly_eq (poly_of_vec (vec_of_poly n h)) h)
  = let pov = poly_of_vec (vec_of_poly n h) in
    Classical.forall_intro (Classical.move_requires (round_trip_coeff #p n h));
    equal_coeffs_means_poly_eq pov h

(* ================================================================ *)
(*  3.  The Frobenius(-id) endomorphism as a polynomial.            *)
(*                                                                   *)
(*  frob p fbar h  :=  (h^p mod fbar) - h                           *)
(*  and the per-monomial image  frob_x p fbar i  =  frob applied to *)
(*  the basis monomial x^i.  (berlekamp_row i is exactly the length *)
(*  n coefficient vector of frob_x i.)                             *)
(* ================================================================ *)

let frob (p:int{EU.is_prime p}) (fbar h: polynomial (fp p)) : polynomial (fp p)
  = (poly_rem (poly_power h (p <: nat)) fbar) -- h

let frob_x (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (i:nat) : polynomial (fp p)
  = frob p fbar (BF.mono_x p i)

(* berlekamp_row i is the coefficient vector of frob_x i. *)
let berlekamp_row_is_frob_x (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (i:nat)
  : Lemma (BF.berlekamp_row p fbar i == BF.vec_of (frob_x p fbar i) 0 (BF.pdeg fbar))
  = ()

(* ================================================================ *)
(*  4.  berlekamp_matrix_T  — the TRANSPOSE (build by columns).      *)
(*                                                                   *)
(*  The transpose construction now LIVES in BerlekampFactor (it      *)
(*  drives berlekamp_kernel), so berlekamp_kernel's null space is    *)
(*  genuinely the Berlekamp subalgebra.  We re-export the names here *)
(*  for the bridge lemmas below.  Row k of berlekamp_matrix_T is     *)
(*     [ coeff (frob_x 0) k ; ... ; coeff (frob_x (n-1)) k ].        *)
(* ================================================================ *)

(* The transpose def + its structural lemmas (mT_entry / mT_row / mT_rows /
   berlekamp_matrix_T + mT_row_length / mT_row_index / mT_rows_length /
   mT_rows_index / mT_rows_all_len / berlekamp_matrix_T_all_len /
   berlekamp_matrix_T_length) now live in BerlekampFactor (they drive
   berlekamp_kernel).  We reference them as  BF.*  below. *)

let berlekamp_matrix_T (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  : list (NS.vector p)
  = BF.berlekamp_matrix_T p fbar

(* ---------------- rows of BerlekampFactor.berlekamp_matrix ---------------- *)

let rec rows_from_length (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (i cnt:nat)
  : Lemma (ensures L.length (BF.rows_from p fbar i cnt) == cnt) (decreases cnt)
  = if cnt = 0 then () else rows_from_length p fbar (i ++ 1) (cnt - 1)

let berlekamp_matrix_length (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  : Lemma (L.length (BF.berlekamp_matrix p fbar) == BF.pdeg fbar)
          [SMTPat (BF.berlekamp_matrix p fbar)]
  = rows_from_length p fbar 0 (BF.pdeg fbar)

let rec rows_from_index (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (i cnt a:nat)
  : Lemma (requires a < cnt)
          (ensures  (rows_from_length p fbar i cnt;
                     L.index (BF.rows_from p fbar i cnt) a == BF.berlekamp_row p fbar (i ++ a)))
          (decreases cnt)
  = rows_from_length p fbar i cnt;
    if a = 0 then ()
    else (rows_from_length p fbar (i ++ 1) (cnt - 1);
          rows_from_index p fbar (i ++ 1) (cnt - 1) (a - 1))

(* ================================================================ *)
(*  5.  THE TRANSPOSE IDENTITY  (formal convention resolution).      *)
(*                                                                   *)
(*  For i,k < n :   (M^T)[k][i]  ==  M[i][k].                        *)
(* ================================================================ *)

let transpose_entry (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (i k:nat)
  : Lemma (requires i < BF.pdeg fbar /\ k < BF.pdeg fbar)
          (ensures  NS.get (L.index (berlekamp_matrix_T p fbar) k) i
                    == NS.get (L.index (BF.berlekamp_matrix p fbar) i) k)
  = let n = BF.pdeg fbar in
    (* LHS *)
    BF.mT_rows_length p fbar 0 n;
    BF.mT_rows_index p fbar 0 n k;              (* index mT k == mT_row p fbar k 0 n *)
    BF.mT_row_length p fbar k 0 n;
    BF.mT_row_index p fbar k 0 n i;             (* index (mT_row k 0 n) i == mT_entry i k *)
    (* RHS *)
    rows_from_index p fbar 0 n i                (* index M i == berlekamp_row p fbar i *)
