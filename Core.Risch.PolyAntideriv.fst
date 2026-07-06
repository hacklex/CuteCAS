module Core.Risch.PolyAntideriv

(* ================================================================ *)
(*  §F — polynomial-part integration soundness:  D(∫p) = p.          *)
(*                                                                   *)
(*  `antideriv p` is the char-0 antiderivative  ∫(Σ aₖ xᵏ) =          *)
(*  Σ aₖ/(k+1) xᵏ⁺¹  (zero constant term).  This is the top-level,    *)
(*  provable version of `Core.Risch.Rational.poly_antideriv`'s        *)
(*  local `build_coeffs`.  With this + the proven Hermite reduction   *)
(*  soundness + the §A LRT log-part soundness, the rational           *)
(*  integrator's `D(integrate p q) = p/q` assembles.                 *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Derivative
open Core.Risch.Hermite

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  Top-level antiderivative coefficient list (lift of Rational's    *)
(*  local `build_coeffs`).  Produces [a_k·inv(k+1), …, a_{k+fuel-1}·… ]*)
(* ---------------------------------------------------------------- *)

let rec antideriv_coeffs (#t:Type) {| f: field t |} (p: polynomial t)
  (k: nat) (fuel: nat)
  : Pure (list t)
         (requires char_zero f /\ (k ++ fuel) == L.length p)
         (ensures fun r -> L.length r == fuel)
         (decreases fuel)
  = if fuel = 0 then []
    else
      let ck = coeff p k in
      let kp1_nat : pos = k ++ 1 in
      let kp1 : t = nat_scale kp1_nat (one #t) in
      (* char_zero ensures nat_scale (k+1) one ≠ zero *)
      assert (is_nonzero kp1);
      let kp1_inv : t = inv kp1 in
      let new_coeff : t = ck * kp1_inv in
      new_coeff :: antideriv_coeffs p (k ++ 1) (fuel - 1)

(* the polynomial antiderivative  (zero constant term, aₖ ↦ aₖ/(k+1) at k+1). *)
let antideriv (#t:Type) {| f: field t |} (p: polynomial t)
  : Pure (polynomial t) (requires char_zero f) (ensures fun _ -> True)
  = if L.length p = 0 then poly_zero #t
    else trim (zero :: antideriv_coeffs p 0 (L.length p))

(* ---------------------------------------------------------------- *)
(*  Index of the coefficient list:                                   *)
(*    L.index (antideriv_coeffs p k fuel) i                          *)
(*      == coeff p (k+i) · inv(nat_scale (k+i+1) one)                *)
(* ---------------------------------------------------------------- *)

let rec antideriv_coeffs_index (#t:Type) {| f: field t |} (p: polynomial t)
  (k: nat) (fuel: nat) (i: nat)
  : Lemma
      (requires char_zero f /\ (k ++ fuel) == L.length p /\ i < fuel)
      (ensures
        is_nonzero (nat_scale ((k ++ i) ++ 1) (one #t)) /\
        L.length (antideriv_coeffs p k fuel) == fuel /\
        L.index (antideriv_coeffs p k fuel) i
          == coeff p (k ++ i)
             * inv (nat_scale ((k ++ i) ++ 1) (one #t)))
      (decreases fuel)
  = let kp1k : t = nat_scale (k ++ 1) (one #t) in
    assert (is_nonzero kp1k);
    if i = 0 then ()
    else
      antideriv_coeffs_index p (k ++ 1) (fuel - 1) (i - 1)

(* ---------------------------------------------------------------- *)
(*  Coefficient at index k+1 of antideriv:                           *)
(*    coeff (antideriv p) (k+1) == coeff p k · inv(nat_scale (k+1) one)*)
(* ---------------------------------------------------------------- *)

let antideriv_coeff_succ (#t:Type) {| f: field t |} (p: polynomial t) (k: nat)
  : Lemma
      (requires char_zero f /\ k < L.length p)
      (ensures
        is_nonzero (nat_scale (k ++ 1) (one #t)) /\
        coeff (antideriv p) (k ++ 1)
          = coeff p k * inv (nat_scale (k ++ 1) (one #t)))
  = H.elim_equatable_laws t ();
    let n = L.length p in
    let cs : list t = antideriv_coeffs p 0 n in
    let full : list t = zero :: cs in
    (* antideriv p = trim full *)
    assert (antideriv p == trim full);
    antideriv_coeffs_index p 0 n k;
    (* L.index cs k == coeff p k · inv(nat_scale (k+1) one) *)
    assert (L.index full (k ++ 1) == L.index cs k);
    coeff_trim full (k ++ 1);
    (* coeff (trim full) (k+1) = L.index full (k+1) = L.index cs k *)
    ()

(* ---------------------------------------------------------------- *)
(*  Scalar/inverse identity:                                         *)
(*    nat_scale n (x · inv(nat_scale n one)) = x   (n:pos, nz scale)  *)
(* ---------------------------------------------------------------- *)

let scale_mul_inv (#t:Type) {| f: field t |} (n: pos) (x: t)
  : Lemma
      (requires is_nonzero (nat_scale n (one #t)))
      (ensures nat_scale n (x * inv (nat_scale n (one #t))) = x)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let kn : t = nat_scale n (one #t) in
    let iv : t = inv kn in
    (* nat_scale n (x·iv) = nat_scale n (one · (x·iv)) — one·(x·iv) = x·iv *)
    H.one_mul_x (x * iv);                                   (* one * (x*iv) = x*iv *)
    nat_scale_congruence n (one * (x * iv)) (x * iv);
    (* nat_scale n (one * (x*iv)) = nat_scale n one * (x*iv) = kn * (x*iv) *)
    nat_scale_mul_left n (one #t) (x * iv);
    (* so: nat_scale n (x*iv) = kn * (x*iv) *)
    (* kn * (x*iv) = x * (kn * iv)  via comm/assoc *)
    mul_commutativity kn (x * iv);                          (* kn*(x*iv) = (x*iv)*kn *)
    mul_associativity x iv kn;                              (* (x*iv)*kn = x*(iv*kn) *)
    inversion_lemma kn;                                    (* iv*kn = one *)
    mul_congruence x (iv * kn) x (one #t);                  (* x*(iv*kn) = x*one *)
    H.x_mul_one x                                           (* x*one = x *)

(* ---------------------------------------------------------------- *)
(*  nat_scale (k+1) zero = zero  (degenerate index case)             *)
(* ---------------------------------------------------------------- *)

let scale_zero_succ (#t:Type) {| f: field t |} (k: nat)
  : Lemma (nat_scale (k ++ 1) (zero <: t) = zero)
  = nat_scale_zero_element #t (k ++ 1)

(* trim never lengthens its argument *)
let rec trim_length_bound (#t:Type) {| cr: commutative_ring t |} (l: list t)
  : Lemma (ensures L.length (trim l) <= L.length l) (decreases l)
  = match l with
    | [] -> ()
    | _ :: l' -> trim_length_bound l'

(* helper: antideriv p has length <= length p + 1, so coeff g (k+1) = zero
   for k >= length p. *)
let antideriv_length_bound (#t:Type) {| f: field t |} (p: polynomial t)
  : Lemma (requires char_zero f)
          (ensures L.length (antideriv p) <= (L.length p) ++ 1)
  = if L.length p = 0 then ()
    else (
      let cs : list t = antideriv_coeffs p 0 (L.length p) in
      trim_length_bound (zero :: cs)
    )

(* ---------------------------------------------------------------- *)
(*  Per-index coefficient soundness:                                 *)
(*    coeff (poly_deriv (antideriv p)) k = coeff p k                 *)
(* ---------------------------------------------------------------- *)

let antideriv_deriv_coeff (#t:Type) {| f: field t |} (p: polynomial t) (k: nat)
  : Lemma
      (requires char_zero f)
      (ensures coeff (poly_deriv (antideriv p)) k = coeff p k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let g : polynomial t = antideriv p in
    (* coeff (poly_deriv g) k = nat_scale (k+1) (coeff g (k+1)) *)
    poly_deriv_coeff g k;
    let kp1nat : pos = k ++ 1 in
    let kn : t = nat_scale kp1nat (one #t) in
    if k < L.length p then (
      (* coeff g (k+1) == coeff p k · inv kn  *)
      antideriv_coeff_succ p k;
      (* nat_scale (k+1) (coeff p k · inv kn) == coeff p k *)
      scale_mul_inv kp1nat (coeff p k);
      (* chain: coeff(deriv g) k = nat_scale (k+1) (coeff g (k+1))
                                 = nat_scale (k+1) (coeff p k · inv kn)  [congr]
                                 = coeff p k *)
      nat_scale_congruence kp1nat
        (coeff g (k ++ 1)) (coeff p k * inv kn)
    ) else (
      (* coeff p k = zero, coeff g (k+1) = zero, nat_scale (k+1) zero = zero *)
      (* g = antideriv p has length <= length p + 1; coeff g (k+1) = zero when
         k >= length p, since k+1 >= length p + 1 > length of antideriv p list. *)
      assert (coeff p k == (zero <: t));
      antideriv_length_bound p;
      assert (coeff g (k ++ 1) == (zero <: t));
      scale_zero_succ #t k;
      nat_scale_congruence kp1nat
        (coeff g (k ++ 1)) zero
    )

(* SOUNDNESS:  D(antideriv p) = p. *)
let antideriv_correct (#t:Type) {| f: field t |} (p: polynomial t)
  : Lemma (requires char_zero f)
          (ensures (poly_deriv (antideriv p)) = p)
  = let g : polynomial t = poly_deriv (antideriv p) in
    let aux (j:nat) : Lemma (coeff g j = coeff p j)
      = antideriv_deriv_coeff p j in
    Classical.forall_intro aux;
    (* extend to all integer indices: negative indices give zero on both sides *)
    let aux2 (j:int) : Lemma (coeff g j = coeff p j)
      = H.elim_equatable_laws t ();
        if j < 0 then ()
        else aux j in
    Classical.forall_intro aux2;
    equal_coeffs_means_poly_eq g p
