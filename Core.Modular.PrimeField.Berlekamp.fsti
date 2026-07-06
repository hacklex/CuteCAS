module Core.Modular.PrimeField.Berlekamp

(* ================================================================ *)
(*  PUBLIC INTERFACE — Berlekamp factorization theory over F_p.     *)
(*                                                                   *)
(*  This is the published face of the whole finite-field cluster     *)
(*  (Fp + Frobenius are implementation modules consumed only here).  *)
(*  It exposes the splitting vocabulary and the headline theorems;   *)
(*  the ~80 helper lemmas in the .fst stay private.                  *)
(*                                                                   *)
(*  Vocabulary defs are abstract (`val`) with a `*_reveal` lemma     *)
(*  (or a recursive characterization) so consumers can unfold on     *)
(*  demand without the impl details leaking by default.              *)
(* ================================================================ *)

module L  = FStar.List.Tot
module PR = Core.Polynomial.Roots
module IR = Core.Polynomial.Irreducible
module SF = Core.Polynomial.SquareFree
module EU = FStar.Math.Euclid

open Core.Algebra
open Core.Algebra.Divisibility
open Core.Algebra.CongruenceMod
open Core.Tactics.CanonRing
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Permutation
open Core.Vector
open Core.Matrix
open Core.Matrix.Determinant
open Core.Modular.PrimeField
open Core.FinSum
open Core.Algebra.Notation

(* ---------------------------------------------------------------- *)
(*  Ring-instance vocabulary                                         *)
(*                                                                   *)
(*  The polynomial commutative_ring is the canonical `polynomial_cr` *)
(*  instance (resolved by TC, or written explicitly over fp p where  *)
(*  fp_field/fp_comm_ring are not registered instances).             *)
(*  Ordinary power g^k in t[X] is Core.Polynomial.SquareFree.poly_power. *)
(* ---------------------------------------------------------------- *)

(* ---------------------------------------------------------------- *)
(*  Congruence modulo m:   cong m x y  :=  m | (x - y)               *)
(* ---------------------------------------------------------------- *)

(* cong / cong_reveal now come from Core.Algebra.CongruenceMod (opened above). *)

(* ---------------------------------------------------------------- *)
(*  The splitting step  berlekamp_split f h c = gcd(f, h - c)        *)
(* ---------------------------------------------------------------- *)

val berlekamp_split (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (c: t) : polynomial t

(* each candidate factor divides f. *)
val berlekamp_split_divides_f (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (c: t)
  : Lemma (divides #(polynomial t)
                   (berlekamp_split #t #f fpoly h c) fpoly)

(* each candidate factor divides h - c (the residue condition). *)
val berlekamp_split_divides_shift (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (c: t)
  : Lemma (divides #(polynomial t)
                   (berlekamp_split #t #f fpoly h c)
                   (h -- (poly_const #t c)))

(* distinct residues give coprime split factors. *)
val berlekamp_split_pairwise_coprime (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (c c': t)
  : Lemma (requires not (c' = c))
          (ensures  coprime #t #f (berlekamp_split #t #f fpoly h c)
                                  (berlekamp_split #t #f fpoly h c'))

(* ---------------------------------------------------------------- *)
(*  The factor list  berlekamp_factors f h cs = map (split f h) cs   *)
(* ---------------------------------------------------------------- *)

val berlekamp_factors (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t) : list (polynomial t)

val berlekamp_factors_reveal (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t)
  : Lemma (berlekamp_factors #t #f fpoly h cs
           == L.map (fun c -> berlekamp_split #t #f fpoly h c) cs)

val berlekamp_factors_length (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t)
  : Lemma (L.length (berlekamp_factors #t #f fpoly h cs) == L.length cs)
          [SMTPat (berlekamp_factors #t #f fpoly h cs)]

(* each factor is nonzero when f is. *)
val berlekamp_factors_have_degree (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t) (k:nat)
  : Lemma (requires k < L.length cs /\ deg fpoly >= 0)
          (ensures  deg (L.index (berlekamp_factors #t #f fpoly h cs) k) >= 0)

(* forward split:  the product of the F_p factors divides f. *)
val berlekamp_factors_product_divides_f (p:int{EU.is_prime p})
  (fpoly h: polynomial (fp p))
  : Lemma (requires deg #(fp p) fpoly >= 0)
          (ensures  divides #(polynomial (fp p))
                       (Core.Polynomial.Roots.poly_prod #(fp p)
                          (berlekamp_factors #(fp p) fpoly h (fp_enum p)))
                       fpoly)

(* ---------------------------------------------------------------- *)
(*  Reverse split + the irreducibility criterion (the headline)      *)
(* ---------------------------------------------------------------- *)

(* for a kernel element h,  prod_c gcd(f, h - c)  and  f  are associates. *)
val berlekamp_reverse_associates (p:int{EU.is_prime p}) (fpoly h: polynomial (fp p))
  : Lemma (requires deg #(fp p) fpoly >= 0 /\
                    cong #(polynomial (fp p))
                            fpoly (poly_power #(fp p) h (p <: nat)) h)
          (ensures  (let prod = PR.poly_prod #(fp p)
                                   (berlekamp_factors #(fp p) fpoly h (fp_enum p)) in
                     divides #(polynomial (fp p)) fpoly prod /\
                     divides #(polynomial (fp p)) prod fpoly))

(* Opaque "h is congruent to SOME global constant modulo q"
   (q | (h - [c]) for some c in F_p); _elim restores the raw exists. *)
[@@"opaque_to_smt"]
val kernel_is_const_shifted (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : prop

val kernel_is_const_shifted_elim (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : Lemma (requires kernel_is_const_shifted p q h)
          (ensures (exists (c:fp p).
                      divides #(polynomial (fp p))
                        q (h -- (poly_const #(fp p) c))))

(* kernel membership <=> a constant shift is divided out, for irreducible q. *)
val kernel_factor_iff (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : Lemma (requires IR.poly_irreducible #(fp p) q)
          (ensures  (cong #(polynomial (fp p))
                             q (poly_power #(fp p) h (p <: nat)) h
                     <==> kernel_is_const_shifted p q h))

(* Opaque "there is a nontrivial Berlekamp splitter for q1*m"
   (a kernel element congruent to no global constant); _elim restores
   the raw existential (with the inner ~exists). *)
[@@"opaque_to_smt"]
val splitter_witness_exists (p:int{EU.is_prime p}) (q1 m: polynomial (fp p))
  : prop

val splitter_witness_exists_elim (p:int{EU.is_prime p}) (q1 m: polynomial (fp p))
  : Lemma (requires splitter_witness_exists p q1 m)
          (ensures (exists (w: polynomial (fp p)).
                      cong #(polynomial (fp p))
                        (q1 * m) (poly_power #(fp p) w (p <: nat)) w /\
                      ~(exists (d:fp p).
                          divides #(polynomial (fp p))
                            (q1 * m)
                            (w -- (poly_const #(fp p) d)))))

(* a reducible coprime product has a nontrivial Berlekamp splitter. *)
val berlekamp_splitter_exists (p:int{EU.is_prime p}) (q1 m: polynomial (fp p))
  : Lemma (requires coprime #(fp p) q1 m /\
                    deg #(fp p) q1 >= 1 /\
                    deg #(fp p) m >= 1)
          (ensures  splitter_witness_exists p q1 m)

(* if f is irreducible, every kernel element is congruent to a constant. *)
val irreducible_kernel_is_constant (p:int{EU.is_prime p}) (f h: polynomial (fp p))
  : Lemma (requires IR.poly_irreducible #(fp p) f /\
                    cong #(polynomial (fp p))
                            f (poly_power #(fp p) h (p <: nat)) h)
          (ensures  kernel_is_const_shifted p f h)
