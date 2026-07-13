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
module RT  = Core.Polynomial.Roots
module SP  = Core.Polynomial.Roots
module SYL = Core.Polynomial.Sylvester
module DET = Core.Matrix.Determinant
module RES = Core.Polynomial.Resultant
module DE  = Core.Matrix.DetEval

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.Resultant
open Core.Polynomial.Eval
open Core.FinSum

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
    let neg_qi : t = (- qi) in
    (* This is pi + neg_qi * z in k[z], i.e., the polynomial [pi; neg_qi] *)
    if neg_qi = zero then embed_const pi
    else if pi = zero then (zero) @ (embed_const neg_qi)
    else [pi; neg_qi]

(* Build the full polynomial (in x) whose coefficients are in k[z].
   The result is a `list (polynomial t)` representing the coefficients
   of x^0, x^1, ..., x^(n-1) where n = max(deg p, deg q') + 1.
   We then trim it to get a proper `polynomial (polynomial t)`. *)

(* top-level recursive builder (lifted from a local `aux` so its index/length
   are characterizable externally — needed by the RT-specialization proof). *)
let rec build_aux (#t:Type) {| cr: commutative_ring t |}
  (p q': polynomial t) (i: nat) (fuel: nat)
  : Tot (list (polynomial t)) (decreases fuel)
  = if fuel = 0 then []
    else p_minus_z_qprime_coeff p q' i
         :: build_aux p q' (i ++ 1) (fuel - 1)

let build_p_minus_z_qprime (#t:Type) {| cr: commutative_ring t |}
  (p q': polynomial t) (n: nat)
  : list (polynomial t)
  = build_aux p q' 0 n

(* build_aux has exactly `fuel` entries *)
let rec build_aux_length (#t:Type) {| cr: commutative_ring t |}
  (p q': polynomial t) (i: nat) (fuel: nat)
  : Lemma (ensures L.length (build_aux p q' i fuel) == fuel) (decreases fuel)
  = if fuel = 0 then ()
    else build_aux_length p q' (i ++ 1) (fuel - 1)

(* the k-th entry of build_aux is the (i+k)-th z-coefficient *)
let rec build_aux_index (#t:Type) {| cr: commutative_ring t |}
  (p q': polynomial t) (i: nat) (fuel: nat) (k: nat)
  : Lemma (requires k < L.length (build_aux p q' i fuel))
          (ensures L.index (build_aux p q' i fuel) k
                   == p_minus_z_qprime_coeff p q' (i ++ k))
          (decreases fuel)
  = if fuel = 0 then ()
    else if k = 0 then ()
    else build_aux_index p q' (i ++ 1)
                              (fuel - 1) (k - 1)

(* Embed q into k[z][x]: each coefficient c of q becomes [c] in k[z] *)
let embed_poly (#t:Type) {| cr: commutative_ring t |}
  (q: polynomial t)
  : list (polynomial t)
  = L.map (fun (c:t) -> embed_const c) q

(* ================================================================ *)
(*  LRT resultant polynomial computation                            *)
(*                                                                  *)
(*  Computes R(z) = res_x(p - z·q', q) as a polynomial in k[z].    *)
(*  Uses the Sylvester matrix over k[z] (= polynomial (polynomial t)).*)
(* ================================================================ *)

(* We need `commutative_ring (polynomial t)` for the Sylvester/det    *)
(* computation. This comes from the registered `polynomial_cr` instance.*)

let lrt_resultant_raw (#t:Type) {| f: field t |}
  (p q: polynomial t)
  : Pure (polynomial t)
         (requires deg q >= 1)
         (ensures fun _ -> True)
  = let q' = poly_deriv q in
    let dq = deg q in
    let dp = (if deg p < 0 then 0 else deg p) in
    let dq' = (if deg q' < 0 then 0 else deg q') in
    let n = (if dp > dq' then dp else dq') in
    (* Build the coefficient lists in k[z][x] *)
    let _pzq_raw = build_p_minus_z_qprime p q' (n ++ 1) in
    let _q_raw = embed_poly q in
    (* Trim them to get proper polynomials in (polynomial t)[x] *)
    let pzq : polynomial (polynomial t) = trim _pzq_raw in
    let q_emb : polynomial (polynomial t) = trim _q_raw in
    (* res_x(p - z*q', q) = det of the Sylvester matrix whose entries are
       polynomials in z.  This is exactly `resultant` instantiated at the
       coefficient ring (polynomial t) = k[z]; the fin-indexed Sylvester
       matrix is built internally by `resultant` from `coeff`. *)
    resultant n dq pzq q_emb

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
         (requires deg q >= 1 /\
                  square_free q)
         (ensures fun _ -> True)
  = let q' = poly_deriv q in
    (* `lrt_resultant_raw` COMPUTES R(z) = res_x(p - z*q', q) executably, as
       the Sylvester determinant over the coefficient ring k[z] (= polynomial t)
       — see `resultant` in Core.Polynomial.Resultant.  The root_sum records this
       computed R together with p, q, q'; its roots are the RT residues, and its
       ℚ-irreducible factors drive the vc-explicit rendering (LogPartFactored /
       LogPartSound).  Soundness of the *rendering* is Core.Risch.LogPartSound;
       soundness of the *producer* (that this determinant equals the true
       resultant, so its roots are exactly the residues) is resultant_specializes
       (Core.Polynomial.Resultant, §A.5). *)
    let r = lrt_resultant_raw p q in
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
         (requires deg q >= 0)
         (ensures fun _ -> True)
  = (* Compute p - c·q' *)
    let c_times_qprime = ((embed_const c) * q') in
    let p_minus_c_qprime = (p -- c_times_qprime) in
    (* gcd(p - c·q', q) *)
    poly_gcd p_minus_c_qprime q

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
  : Lemma (requires deg q >= 0)
          (ensures divides (lrt_log_argument p q q' c) q)
  = let resid = (p -- ((embed_const c) * q')) in
    gcd_divides_right resid q

(* v_c divides (p - c*q') : the residue condition p ≡ c*q' on v_c. *)
let lrt_log_argument_divides_residue (#t:Type) {| f: field t |}
  (p q q': polynomial t) (c: t)
  : Lemma (requires deg q >= 0)
          (ensures divides (lrt_log_argument p q q' c)
                            (p -- ((embed_const c) * q')))
  = let resid = (p -- ((embed_const c) * q')) in
    gcd_divides_left resid q

(* ===== merged from Core.Risch.LRTResultant - resultant specialization of the LRT step ===== *)

#set-options "--fuel 2 --ifuel 2 --z3rlimit 30"

(* Evaluating the constant embedding gives the constant back. *)
let embed_const_eval (#t:Type) {| f: field t |} (c0 c: t)
  : Lemma (poly_eval (embed_const c0) c = c0)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    assert (embed_const c0
            == (if c0 = (zero) then (poly_zero #t) else ([c0])))
      by (FStar.Tactics.norm [delta_only [`%embed_const]; primops]; FStar.Tactics.trefl ());
    if c0 = (zero) then
      eval_zero c                    (* eval poly_zero c = zero; c0 = zero closes *)
    else
      RT.eval_singleton c0 c          (* poly_eval [c0] c = c0 *)

(* deg-1 evaluation:  poly_eval [a; b] c = a + b*c   (b<>0 so [a;b] is trimmed).
   Mirrors Core.Polynomial.Roots.eval_linear (which is this with a=neg a0, b=one). *)
let eval_deg1 (#t:Type) {| f: field t |} (a b c: t)
  : Lemma (requires not (b = (zero)))
          (ensures  poly_eval ([a; b]) c = (a + b * c))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let la : polynomial t = [a; b] in
    let g = eval_term la c in
    sum_range_unfold_left g 0 2;                 (* sum02 = g0 + sum12 *)
    sum_range_unfold_left g 1 2;                 (* sum12 = g1 + sum22 *)
    sum_range_empty g 2 2;                        (* sum22 = zero *)
    H.x_mul_one a;
    H.x_mul_one c;                               (* c * one = c *)

    mul_congruence b (c * one) b c;              (* b*(c*one) = b*c  (== g1 = b*c) *)
    assert (cpow c 1 == c * one);
    assert (g 0 == a * one);
    assert (g 1 == b * (c * one));
    assert (g 1 = b * c);
    assert (g 0 = a);
    H.x_plus_zero (g 1);
    add_congruence (g 1) (sum_range g 2 2) (g 1) (zero);
    add_congruence (g 0) (sum_range g 1 2) a (b * c)

(* Evaluating the i-th k[z]-coefficient of (p - z*q') at z=c:
   poly_eval (p_minus_z_qprime_coeff p q' i) c = coeff p i + neg (c * coeff q' i). *)
#push-options "--z3rlimit 30"
let pzq_coeff_eval (#t:Type) {| f: field t |} (p q' : polynomial t) (i: nat) (c: t)
  : Lemma (poly_eval (p_minus_z_qprime_coeff p q' i) c
           = coeff p i + (- (c * coeff q' i)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pi : t = coeff p i in
    let qi : t = coeff q' i in
    let neg_qi : t = (- qi) in
    let m : polynomial t = p_minus_z_qprime_coeff p q' i in
    if neg_qi = (zero) then begin
      (* Case A: m == embed_const pi; poly_eval m c = pi *)
      assert (m == embed_const pi);
      embed_const_eval pi c;
      assert (poly_eval m c = pi);
      H.zero_of_neg qi;                        (* qi = zero *)
      H.x_mul_zero c;                          (* c * zero = zero *)
      mul_congruence c qi c (zero);       (* c*qi = c*zero *)
      neg_congruence (c * qi) (zero);     (* neg(c*qi) = neg zero *)
      H.neg_zero #t ();                        (* zero = neg zero *)
      H.x_plus_zero pi;                        (* pi + zero = pi *)
      add_congruence pi ((- (c * qi))) pi (zero)   (* pi+neg(c*qi) = pi+zero *)
    end else begin
      (* common conversion:  neg_qi * c = neg (c * qi) *)
      H.neg_mul_l qi c;                        (* (neg qi)*c = neg(qi*c) *)
      mul_commutativity qi c;                  (* qi*c = c*qi *)
      neg_congruence (qi * c) (c * qi);        (* neg(qi*c) = neg(c*qi); neg_qi*c = neg(c*qi) *)
      if pi = (zero) then begin
        (* Case B: m == zero @ (embed_const neg_qi) == [zero; neg_qi] *)
        assert (embed_const neg_qi
                == (if neg_qi = (zero) then (poly_zero #t) else ([neg_qi])))
          by (FStar.Tactics.norm [delta_only [`%embed_const]; primops];
              FStar.Tactics.trefl ());
        assert (embed_const neg_qi == ([neg_qi]));
        assert (m == ((zero) @ (embed_const neg_qi)));
        assert (((zero) @ ([neg_qi])) == ([(zero); neg_qi]));
        assert (m == ([(zero); neg_qi]));
        eval_deg1 (zero) neg_qi c;        (* poly_eval [zero;neg_qi] c = zero + neg_qi*c *)
        assert (poly_eval m c = (zero) + neg_qi * c);
        add_congruence (zero) (neg_qi * c) pi ((- (c * qi)))  (* zero+neg_qi*c = pi+neg(c*qi) *)
      end else begin
        (* Case C: m == [pi; neg_qi] *)
        assert (m == ([pi; neg_qi]));
        eval_deg1 pi neg_qi c;                 (* poly_eval [pi;neg_qi] c = pi + neg_qi*c *)
        assert (poly_eval m c = pi + neg_qi * c);
        add_congruence pi (neg_qi * c) pi ((- (c * qi)))  (* pi+neg_qi*c = pi+neg(c*qi) *)
      end
    end
#pop-options

(* coeff of (p - c*q') at i, with c*q' = poly_scale c q'.  Matches pzq_coeff_eval's RHS. *)
let sub_scale_coeff (#t:Type) {| f: field t |} (p q' : polynomial t) (c: t) (i: nat)
  : Lemma (coeff ((p -- (SP.poly_scale c q'))) i = coeff p i + (- (c * coeff q' i)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    poly_sub_coeff p (SP.poly_scale c q') i;     (* coeff(p - s) i = coeff p i + neg(coeff s i) *)
    poly_mul_singleton_coeff c q' i;             (* coeff(poly_scale c q') i = c * coeff q' i *)
    neg_congruence (coeff (SP.poly_scale c q') i) (c * coeff q' i);
    add_congruence (coeff p i) ((- (coeff (SP.poly_scale c q') i)))
                   (coeff p i) ((- (c * coeff q' i)))

(* ================================================================ *)
(*  Per-entry evaluation of the Sylvester inputs (q_emb / pzq).      *)
(* ================================================================ *)

(* generic map index/length helpers *)
let rec index_map (#a #b:Type) (g: a -> b) (l: list a) (k:nat)
  : Lemma (requires k < L.length l)
          (ensures L.length (L.map g l) == L.length l /\
                   L.index (L.map g l) k == g (L.index l k))
          (decreases l)
  = match l with
    | [] -> ()
    | x :: xs -> if k = 0 then () else index_map g xs (k - 1)

let rec map_length (#a #b:Type) (g: a -> b) (l: list a)
  : Lemma (ensures L.length (L.map g l) == L.length l) (decreases l)
  = match l with
    | [] -> ()
    | _ :: xs -> map_length g xs

let embed_const_zero_eq (#t:Type) {| cr: commutative_ring t |} (c: t)
  : Lemma (requires c = (zero)) (ensures embed_const c == (poly_zero #t))
  = ()

(* coeff of the embedded denominator q_emb = trim (embed_poly q)  (= is poly_eq). *)
let coeff_qemb_eq (#t:Type) {| f: field t |} (q: polynomial t) (k: nat)
  : Lemma (eq
             (coeff
                (trim (embed_poly q)) k)
             (embed_const (coeff q k)))
  = H.elim_equatable_laws (polynomial t) ();
    coeff_trim (embed_poly q) k;
    assert (embed_poly q == L.map (fun (c:t) -> embed_const c) q)
      by (FStar.Tactics.norm [delta_only [`%embed_poly]]; FStar.Tactics.trefl ());
    map_length (fun (c:t) -> embed_const c) q;
    if k < L.length q then begin
      index_map (fun (c:t) -> embed_const c) q k;
      assert (coeff q k == L.index q k)
    end else begin
      assert (coeff q k == (zero <: t));
      reflexivity (zero <: t);
      embed_const_zero_eq (coeff q k)
    end

(* eval of the q-block entry: poly_eval (coeff q_emb k) c = coeff q k. *)
let qemb_entry_eval (#t:Type) {| f: field t |} (q: polynomial t) (k: nat) (c: t)
  : Lemma (poly_eval (coeff
                        (trim (embed_poly q)) k) c
           = coeff q k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let qe = coeff (trim (embed_poly q)) k in
    coeff_qemb_eq q k;
    eval_congruence qe (embed_const (coeff q k)) c;
    embed_const_eval (coeff q k) c

(* coeff of the trimmed (p - z*q') builder = the k-th z-coefficient, for k <= n. *)
let coeff_pzq_eq (#t:Type) {| f: field t |} (p q': polynomial t) (n: nat) (k: nat)
  : Lemma (requires k <= n)
          (ensures eq
                     (coeff
                        (trim
                           (build_p_minus_z_qprime p q' (n ++ 1))) k)
                     (p_minus_z_qprime_coeff p q' k))
  = H.elim_equatable_laws (polynomial t) ();
    build_aux_length p q' 0 (n ++ 1);
    build_aux_index  p q' 0 (n ++ 1) k;
    coeff_trim
      (build_p_minus_z_qprime p q' (n ++ 1)) k

(* eval of the p-block entry: poly_eval (coeff pzq k) c = coeff (p - c*q') k, for k <= n. *)
let pzq_entry_eval (#t:Type) {| f: field t |} (p q': polynomial t) (n: nat) (k: nat) (c: t)
  : Lemma (requires k <= n)
          (ensures poly_eval (coeff
                     (trim
                        (build_p_minus_z_qprime p q' (n ++ 1))) k) c
                   = coeff ((p -- (SP.poly_scale c q'))) k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pz = coeff
               (trim
                  (build_p_minus_z_qprime p q' (n ++ 1))) k in
    coeff_pzq_eq p q' n k;
    eval_congruence pz (p_minus_z_qprime_coeff p q' k) c;
    pzq_coeff_eval p q' k c;
    sub_scale_coeff p q' c k

(* ================================================================ *)
(*  Sylvester-entry specialization + the RT resultant specialization. *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let eval_sylvester_entry (#t:Type) {| f: field t |} (p q' q: polynomial t) (n dq: nat) (c: t)
  (i j: Core.Permutation.fin (n ++ dq))
  : Lemma (requires dq >= 1 /\
                    L.length (trim
                       (build_p_minus_z_qprime p q' (n ++ 1))) <= (n ++ 1) /\
                    L.length ((p -- (SP.poly_scale c q')) <: polynomial t) <= (n ++ 1) /\
                    L.length (trim (embed_poly q)) <= (dq ++ 1) /\
                    L.length q <= (dq ++ 1))
          (ensures
             poly_eval
               (SYL.sylvester_matrix n dq
                  (trim (build_p_minus_z_qprime p q' (n ++ 1)))
                  (trim (embed_poly q)) i j) c
             = SYL.sylvester_matrix n dq
                  ((p -- (SP.poly_scale c q'))) q i j)
  = H.elim_equatable_laws t ();
    let pzq : polynomial (polynomial t) =
      trim (build_p_minus_z_qprime p q' (n ++ 1)) in
    let qe  : polynomial (polynomial t) = trim (embed_poly q) in
    let pp  : polynomial t = (p -- (SP.poly_scale c q')) in
    let mi : nat = i in
    let mj : nat = j in
    (* LHS matrix entry (polynomial t) and RHS matrix entry (t) *)
    let lhs_e : polynomial t = SYL.sylvester_matrix n dq pzq qe i j in
    let rhs_e : t            = SYL.sylvester_matrix n dq pp q i j in
    if mi < dq then begin
      (* p-block *)
      if mj >= mi && mj <= mi + n then begin
        (* in range *)
        SYL.sylvester_p_block_in_range n dq pzq qe i j;
        SYL.sylvester_p_block_in_range n dq pp q i j;
        let idx : nat = SYL.nat_sub (SYL.nat_add n mi) mj in
        (* lhs_e == coeff pzq idx, rhs_e == coeff pp idx *)
        assert (lhs_e == coeff pzq idx);
        assert (rhs_e == coeff pp idx);
        pzq_entry_eval p q' n idx c;
        (* poly_eval (coeff pzq idx) c = coeff pp idx = rhs_e *)
        assert (poly_eval lhs_e c = rhs_e)
      end else if mj > mi + n then begin
        (* right zero *)
        SYL.sylvester_p_block_right_zero n dq pzq qe i j;
        SYL.sylvester_p_block_right_zero n dq pp q i j;
        assert (lhs_e == (poly_zero #t));
        eval_zero c;
        assert (poly_eval lhs_e c = (zero));
        assert (rhs_e == (zero))
      end else begin
        (* left zero: mj < mi *)
        SYL.sylvester_p_block_left_zero n dq pzq qe i j;
        SYL.sylvester_p_block_left_zero n dq pp q i j;
        assert (lhs_e == (poly_zero #t));
        eval_zero c;
        assert (poly_eval lhs_e c = (zero));
        assert (rhs_e == (zero))
      end
    end else begin
      (* q-block: mi >= dq *)
      if mj <= mi then begin
        (* in range *)
        SYL.sylvester_q_block_in_range n dq pzq qe i j;
        SYL.sylvester_q_block_in_range n dq pp q i j;
        let idx : nat = SYL.nat_sub mi mj in
        assert (lhs_e == coeff qe idx);
        assert (rhs_e == coeff q idx);
        qemb_entry_eval q idx c;
        assert (poly_eval lhs_e c = rhs_e)
      end else begin
        (* right zero: mj > mi *)
        SYL.sylvester_q_block_right_zero n dq pzq qe i j;
        SYL.sylvester_q_block_right_zero n dq pp q i j;
        assert (lhs_e == (poly_zero #t));
        eval_zero c;
        assert (poly_eval lhs_e c = (zero));
        assert (rhs_e == (zero))
      end
    end
#pop-options

(* THE RT SPECIALIZATION (generic n,dq form):
   poly_eval (resultant pzq q_emb) c = resultant (p - c*q') q. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let resultant_eval_specialized (#t:Type) {| f: field t |} (p q' q: polynomial t) (n dq: nat) (c: t)
  : Lemma (requires dq >= 1 /\
                    L.length (trim
                       (build_p_minus_z_qprime p q' (n ++ 1))) <= (n ++ 1) /\
                    L.length ((p -- (SP.poly_scale c q')) <: polynomial t) <= (n ++ 1) /\
                    L.length (trim (embed_poly q)) <= (dq ++ 1) /\
                    L.length q <= (dq ++ 1))
          (ensures poly_eval
                     (RES.resultant n dq
                        (trim (build_p_minus_z_qprime p q' (n ++ 1)))
                        (trim (embed_poly q))) c
                   = RES.resultant n dq ((p -- (SP.poly_scale c q'))) q)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pzq = trim (build_p_minus_z_qprime p q' (n ++ 1)) in
    let qe  = trim (embed_poly q) in
    let pp  : polynomial t = (p -- (SP.poly_scale c q')) in
    let m1 = DE.eval_matrix (SYL.sylvester_matrix n dq pzq qe) c in
    let m2 = SYL.sylvester_matrix n dq pp q in
    let aux (i j: Core.Permutation.fin (n ++ dq)) : Lemma (m1 i j = m2 i j)
      = eval_sylvester_entry p q' q n dq c i j in
    FStar.Classical.forall_intro_2 aux;
    DET.det_pointwise_eq m1 m2;
    DE.resultant_eval n dq pzq qe c;
    RES.resultant_unfold n dq pp q
#pop-options

(* ================================================================ *)
(*  Literal lrt_resultant_raw specialization (degree bounds + corollary). *)
(* ================================================================ *)
(* high coeffs of a scaled poly vanish *)
let coeff_zero_above_k_of_scale (#t:Type) {| f: field t |} (c: t) (qq: polynomial t) (k:nat) (i:nat)
  : Lemma (requires i >= k /\ deg qq < k)
          (ensures coeff (SP.poly_scale c qq) i = (zero))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    coeff_above_degree qq i;                       (* coeff qq i = zero *)
    poly_mul_singleton_coeff c qq i;               (* coeff (poly_scale c qq) i = c * coeff qq i *)
    H.x_mul_zero c;                                (* c * zero = zero *)
    mul_congruence c (coeff qq i) c (zero)     (* c*coeff qq i = c*zero *)

(* deg(poly_scale c qq) < k  when deg qq < k  (mirrors poly_add_degree_bound) *)
let poly_scale_deg_le (#t:Type) {| f: field t |} (c: t) (qq: polynomial t) (k:nat)
  : Lemma (requires deg qq < k)
          (ensures deg (SP.poly_scale c qq) < k)
  = if deg (SP.poly_scale c qq) < 0 then ()
    else begin
        let d = deg (SP.poly_scale c qq) in
        if d < k then ()
        else begin
          coeff_zero_above_k_of_scale c qq k d;   (* coeff (scale) d = zero *)
          leading_coeff_nonzero (SP.poly_scale c qq)    (* coeff (scale) d <> zero — contradiction *)
        end
    end

(* the literal lrt_resultant_raw specialization *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let lrt_resultant_specializes (#t:Type) {| f: field t |} (p q: polynomial t) (c: t)
  : Lemma (requires deg q >= 1)
          (ensures (let q'  = poly_deriv q in
                    let dq  = deg q in
                    let dp  = (if deg p < 0 then 0 else deg p) in
                    let dq' = (if deg q' < 0 then 0 else deg q') in
                    let n   = (if dp > dq' then dp else dq') in
                    poly_eval (lrt_resultant_raw p q) c
                    = RES.resultant n dq
                        ((p -- (SP.poly_scale c q'))) q))
  = let q'  = poly_deriv q in
    let dq  = deg q in
    let dp  = (if deg p < 0 then 0 else deg p) in
    let dq' = (if deg q' < 0 then 0 else deg q') in
    let n   = (if dp > dq' then dp else dq') in
    build_aux_length p q' 0 (n ++ 1);
    trim_length_le
      (build_p_minus_z_qprime p q' (n ++ 1));      (* bound 1 *)
    map_length (fun (cc:t) -> embed_const cc) q;
    trim_length_le (embed_poly q);       (* bounds 3,4 *)
    poly_scale_deg_le c q' (n ++ 1);            (* deg(scale) < n+1 *)
    poly_sub_degree_bound p (SP.poly_scale c q') (n ++ 1);  (* bound 2 *)
    resultant_eval_specialized p q' q n dq c
#pop-options
