module Core.Risch.LRT
(*
   Lazard-Rioboo-Trager algorithm for the logarithmic part of
   rational integration.

   Given p/q with q square-free and deg(p) < deg(q) (output of Hermite
   reduction), the integral has the form:
     ∫ p/q dx = Σᵢ cᵢ · log(vᵢ(x))

   Algorithm:
     1. Compute R(z) = res_x(p - z·q', q) — a polynomial in z.
        R(z) ∈ k[z] has degree ≤ deg(q).
     2. For each root cᵢ of R(z):
        vᵢ(x) = gcd(p - cᵢ·q', q)
     3. Output: RootSum(R, z ↦ z · log(gcd(p - z·q', q)))

   Implementation note:
     To compute res_x(p - z·q', q), we work in k[z][x]:
     - Coefficients of x-polynomials are polynomials in z.
     - `q` is embedded as constant (in z) coefficients.
     - `p - z·q'` has coefficients [coeff(p,i) - z·coeff(q',i)] in k[z].
     - We then compute the Sylvester-matrix determinant over k[z].
     - The result is a polynomial in z.

   For the soundness proof, we only need:
     d/dx[Σ cᵢ·log(vᵢ)] = Σ cᵢ·vᵢ'/vᵢ = p/q
   which reduces to a polynomial identity at each root cᵢ.
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Matrix.Resultant

(* ================================================================ *)
(*  Embedding k into k[z] : scalar → constant polynomial            *)
(* ================================================================ *)

let embed_const (#t:Type) {| cr: commutative_ring t |} (c: t) : polynomial t
  = if c = zero then poly_zero #t else [c]

(* ================================================================ *)
(*  Build p - z·q' as a polynomial in x with k[z] coefficients      *)
(*                                                                  *)
(*  Each x-coefficient is a polynomial in z:                        *)
(*    coeff_x(p - z·q', i) = [coeff(p,i)] + [-coeff(q',i)] · z     *)
(*                          = [coeff(p,i); -coeff(q',i)]            *)
(*  (after trimming in k[z])                                        *)
(* ================================================================ *)

let p_minus_z_qprime_coeff (#t:Type) {| cr: commutative_ring t |}
  (p q': polynomial t) (i: nat) : polynomial t
  = let pi : t = coeff p i in
    let qi : t = coeff q' i in
    let neg_qi : t = neg qi in
    (* This is pi + neg_qi * z in k[z], i.e., the polynomial [pi; neg_qi] *)
    if neg_qi = zero then embed_const pi
    else if pi = zero then (zero <: t) @ (embed_const neg_qi)
    else [pi; neg_qi]

(* Build the full polynomial (in x) whose coefficients are in k[z].
   The result is a `list (polynomial t)` representing the coefficients
   of x^0, x^1, ..., x^(n-1) where n = max(deg p, deg q') + 1.
   We then trim it to get a proper `polynomial (polynomial t)`. *)

let build_p_minus_z_qprime (#t:Type) {| cr: commutative_ring t |}
  (p q': polynomial t) (n: nat)
  : list (polynomial t)
  = let rec aux (i: nat) (fuel: nat)
      : Tot (list (polynomial t)) (decreases fuel)
      = if fuel = 0 then []
        else p_minus_z_qprime_coeff p q' i :: aux (Prims.op_Addition i 1) (Prims.op_Subtraction fuel 1)
    in aux 0 n

(* Embed q into k[z][x]: each coefficient c of q becomes [c] in k[z] *)
let embed_poly (#t:Type) {| cr: commutative_ring t |}
  (q: polynomial t)
  : list (polynomial t)
  = L.map (fun c -> embed_const #t #cr c) q

(* ================================================================ *)
(*  LRT resultant polynomial computation                            *)
(*                                                                  *)
(*  Computes R(z) = res_x(p - z·q', q) as a polynomial in k[z].    *)
(*  Uses the Sylvester matrix over k[z] (= polynomial (polynomial t)).*)
(* ================================================================ *)

(* We need `commutative_ring (polynomial t)` for the Sylvester/det    *)
(* computation. This comes from `polynomial_commutative_ring_instance`.*)

let lrt_resultant_raw (#t:Type) {| f: field t |}
  (p q: polynomial t)
  : Pure (polynomial t)
         (requires Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1)
         (ensures fun _ -> True)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let id_p = (polynomial_integral_domain_instance #t #(id_of_f t)).pid in
    (* commutative_ring (polynomial t) — needed to form polynomial (polynomial t) *)
    let cr_poly : commutative_ring (polynomial t) = cr_of_id (polynomial t) #id_p in
    let q' = poly_deriv #t #cr q in
    let dq = Some?.v (poly_deg q) in
    let dp = (match poly_deg p with | None -> 0 | Some d -> d) in
    let dq' = (match poly_deg q' with | None -> 0 | Some d -> d) in
    let n = (if dp > dq' then dp else dq') in
    (* Build the coefficient lists in k[z][x] *)
    let _pzq_raw = build_p_minus_z_qprime #t #cr p q' (Prims.op_Addition n 1) in
    let _q_raw = embed_poly #t #cr q in
    (* Trim them to get proper polynomials in (polynomial t)[x] *)
    let pzq : polynomial (polynomial t) = trim #(polynomial t) #cr_poly _pzq_raw in
    let q_emb : polynomial (polynomial t) = trim #(polynomial t) #cr_poly _q_raw in
    (* res_x(p - z*q', q) = det of the Sylvester matrix whose entries are
       polynomials in z.  This is exactly `resultant` instantiated at the
       coefficient ring (polynomial t) = k[z]; the fin-indexed Sylvester
       matrix is built internally by `resultant` from `coeff`. *)
    resultant #(polynomial t) #cr_poly n dq pzq q_emb

(* ================================================================ *)
(*  Log-integral output type: a "root sum"                          *)
(*                                                                  *)
(*  RootSum(R, z ↦ z · log(gcd_z(x))) represents:                  *)
(*    Σ_{cᵢ : R(cᵢ)=0} cᵢ · log(gcd(p - cᵢ·q', q))              *)
(*                                                                  *)
(*  We store this symbolically as (R, p, q, q') — the gcd can be   *)
(*  recomputed for any specific root.                               *)
(* ================================================================ *)

noeq type root_sum (#t:Type) (f: field t) = {
  rs_resultant: polynomial t;  (* R(z) — roots give the constants cᵢ *)
  rs_p: polynomial t;          (* original numerator p *)
  rs_q: polynomial t;          (* original square-free denominator q *)
  rs_qprime: polynomial t;     (* q' = poly_deriv q *)
}

(* ================================================================ *)
(*  Top-level LRT function                                          *)
(*                                                                  *)
(*  Given p/q with q square-free, produce the root_sum that         *)
(*  represents ∫ p/q dx as a sum of logarithms.                    *)
(*                                                                  *)
(*  NOTE: The actual resultant computation (lrt_resultant_raw)      *)
(*  requires the determinant over polynomial coefficients, which    *)
(*  our current infrastructure supports in principle. However,      *)
(*  the Sylvester matrix + det machinery takes `fin n → fin n → t`  *)
(*  matrix format. Building the bridge from our list-based polys    *)
(*  to that matrix format is mechanical but requires careful typing. *)
(*  For now, we provide the data type and the placeholder.          *)
(* ================================================================ *)

let lrt (#t:Type) {| f: field t |}
  (p q: polynomial t)
  : Pure (root_sum f)
         (requires Some? (poly_deg q) /\ Some?.v (poly_deg q) >= 1 /\
                  square_free #t #f q)
         (ensures fun _ -> True)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let q' = poly_deriv #t #cr q in
    (* In a full implementation, we would compute:
       let r = lrt_resultant_computed p q in ...
       For now we return the symbolic representation.
       The actual resultant computation requires bridging the
       Sylvester matrix infrastructure (fin-indexed) with our
       polynomial representation (list-based). This bridge is
       mechanical but verbose — see Core.Matrix.Resultant for the
       pattern. *)
    let r = lrt_resultant_raw #t #f p q in
    { rs_resultant = r;          (* R(z) = res_x(p - z*q', q) *)
      rs_p = p;
      rs_q = q;
      rs_qprime = q'; }

(* ================================================================ *)
(*  Evaluate the root sum at a specific constant c                  *)
(*                                                                  *)
(*  For a given root c of R(z), the log-argument is:                *)
(*    v_c(x) = gcd(p - c·q', q)                                    *)
(* ================================================================ *)

let lrt_log_argument (#t:Type) {| f: field t |}
  (p q q': polynomial t)
  (c: t)
  : Pure (polynomial t)
         (requires Some? (poly_deg q))
         (ensures fun _ -> True)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    (* Compute p - c·q' *)
    let c_times_qprime = poly_mul (embed_const #t #cr c) q' in
    let p_minus_c_qprime = poly_sub p c_times_qprime in
    (* gcd(p - c·q', q) *)
    poly_gcd #t #f p_minus_c_qprime q

(* ================================================================ *)
(*  Structural soundness of the LRT log-argument (Rothstein-Trager   *)
(*  residue property, base-field version).                           *)
(*                                                                   *)
(*  Each log-argument v_c = gcd(p - c*q', q) is a genuine factor of  *)
(*  the square-free denominator q, and on that factor the residue    *)
(*  condition p ≡ c*q' holds (v_c | (p - c*q')).  These are the two  *)
(*  defining properties of an LRT logarithmic term; they follow      *)
(*  directly from the proven GCD divisibility axioms.                *)
(*                                                                   *)
(*  NOTE: the *full* LRT soundness — d/dx[Σ cᵢ·log vᵢ] = p/q summed  *)
(*  over the roots cᵢ of R(z) — additionally requires the splitting  *)
(*  field of R (sum over roots / residue theorem) and resultant      *)
(*  specialization (R(c) = res_x(p - c*q', q)); neither is available *)
(*  yet (Core.AlgebraicConstant is commutative-ring-only; there is   *)
(*  no eval-as-ring-hom nor a determinant-specialization lemma).     *)
(* ================================================================ *)

(* v_c divides q : each logarithm is taken of a factor of q. *)
let lrt_log_argument_divides_q (#t:Type) {| f: field t |}
  (p q q': polynomial t) (c: t)
  : Lemma (requires Some? (poly_deg q))
          (ensures divides (lrt_log_argument #t #f p q q' c) q)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let resid = poly_sub p (poly_mul (embed_const #t #cr c) q') in
    gcd_divides_right #t #f resid q

(* v_c divides (p - c*q') : the residue condition p ≡ c*q' on v_c. *)
let lrt_log_argument_divides_residue (#t:Type) {| f: field t |}
  (p q q': polynomial t) (c: t)
  : Lemma (requires Some? (poly_deg q))
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    divides (lrt_log_argument #t #f p q q' c)
                            (poly_sub p (poly_mul (embed_const #t #cr c) q'))))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let resid = poly_sub p (poly_mul (embed_const #t #cr c) q') in
    gcd_divides_left #t #f resid q
