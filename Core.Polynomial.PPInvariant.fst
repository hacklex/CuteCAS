module Core.Polynomial.PPInvariant

(*
   Powered-product loop invariant for Yun's algorithm.

   Establishes the identity:
     PP(yun_loop b d [] fuel) ≈ b · b_product(b, d, fuel)

   where b_product(b, d, fuel) = b₁ · b₂ · ... · bₙ is the ghost
   product of intermediate square-free factors.

   Key exports:
     - poly_power_congruence: a ≈ b → a^n ≈ b^n
     - yun_loop_b_product: ghost product of intermediate b's
     - yun_loop_pp_invariant: the PP loop invariant
     - yun_loop_pp_b_product: PP(yun_loop b d [] fuel) ≈ b · b_product
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.GCD
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.Irreducible

(* ================================================================ *)
(*  poly_power_congruence: a ≈ b → a^n ≈ b^n                       *)
(* ================================================================ *)

let rec poly_power_congruence (#t:Type) {| cr: commutative_ring t |}
  (a b: polynomial t) (n: nat)
  : Lemma (requires poly_eq a b)
          (ensures  poly_eq (poly_power a n) (poly_power b n))
          (decreases n)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if n = 0 then
      poly_eq_reflexivity (poly_one #t)
    else begin
      poly_power_congruence a b (n - 1);
      poly_mul_congruence a (poly_power a (n - 1)) b (poly_power b (n - 1))
    end

(* ================================================================ *)
(*  Ghost b-product: tracks product of intermediate b values        *)
(*                                                                  *)
(*  yun_loop_b_product(b, d, fuel) = b₁ · b₂ · ... · bₙ           *)
(*  where bₖ = bₖ₋₁ / gcd(bₖ₋₁, dₖ₋₁).                          *)
(* ================================================================ *)

let rec yun_loop_b_product (#t:Type) {| f: field t |}
  (b d: polynomial t) (fuel: nat)
  : Tot (polynomial t) (decreases fuel)
  = if fuel = 0 then poly_one #t
    else if None? (poly_deg b) then poly_one #t
    else if Some?.v (poly_deg b) = 0 then poly_one #t
    else
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      poly_mul b' (yun_loop_b_product #t #f b' d' (fuel - 1))

(* ================================================================ *)
(*  PP loop invariant:                                               *)
(*                                                                  *)
(*  PP(output) ≈ PP(acc) · b^(|acc|+1) · b_product(b, d, fuel)     *)
(*                                                                  *)
(*  At the top level (acc = []):                                    *)
(*  PP(yun(p)) ≈ 1 · b₀ · b_product = b₀ · b_product              *)
(*                                                                  *)
(*  Key algebraic step in the inductive case:                       *)
(*  We need: PP(acc) · b^n · (b' · R)                              *)
(*         ≈ PP(acc') · b'^(n+1) · R                               *)
(*  Using b ≈ a · b' and PP(acc') ≈ PP(acc) · a^n.                 *)
(* ================================================================ *)

(* Helper: five-factor rearrangement
   (P · (A · B)) · (b' · R) ≈ ((P · A) · (b' · B)) · R
   This swaps B and b' in a product of five factors. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
private let five_factor_rearrange (#t:Type) {| cr: commutative_ring t |}
  (p_ a_ b_ b'_ r_: polynomial t)
  : Lemma (ensures poly_eq
      (poly_mul (poly_mul p_ (poly_mul a_ b_)) (poly_mul b'_ r_))
      (poly_mul (poly_mul (poly_mul p_ a_) (poly_mul b'_ b_)) r_))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* Step 1: P · (A · B) ≈ (P · A) · B  [assoc] *)
    poly_mul_associativity p_ a_ b_;
    poly_eq_symmetry (poly_mul (poly_mul p_ a_) b_) (poly_mul p_ (poly_mul a_ b_));
    let pa = poly_mul p_ a_ in
    (* Step 2: ((P·A) · B) · (b' · R)  [lift step 1] *)
    poly_mul_left_congruence (poly_mul p_ (poly_mul a_ b_)) (poly_mul pa b_)
                             (poly_mul b'_ r_);
    (* Step 3: ((P·A) · B) · (b' · R) ≈ (P·A) · (B · (b' · R))  [assoc] *)
    poly_mul_associativity pa b_ (poly_mul b'_ r_);
    (* Step 4: B · (b' · R) ≈ (B · b') · R  [assoc] *)
    poly_mul_associativity b_ b'_ r_;
    poly_eq_symmetry (poly_mul (poly_mul b_ b'_) r_) (poly_mul b_ (poly_mul b'_ r_));
    (* Step 5: B · b' ≈ b' · B  [comm] *)
    poly_mul_commutativity b_ b'_;
    poly_mul_left_congruence (poly_mul b_ b'_) (poly_mul b'_ b_) r_;
    (* Step 6: (P·A) · ((b' · B) · R) ≈ ((P·A) · (b' · B)) · R  [assoc] *)
    poly_mul_associativity pa (poly_mul b'_ b_) r_;
    poly_eq_symmetry (poly_mul (poly_mul pa (poly_mul b'_ b_)) r_)
                     (poly_mul pa (poly_mul (poly_mul b'_ b_) r_));
    (* Chain everything *)
    let t1 = poly_mul (poly_mul p_ (poly_mul a_ b_)) (poly_mul b'_ r_) in
    let t2 = poly_mul (poly_mul pa b_) (poly_mul b'_ r_) in
    let t3 = poly_mul pa (poly_mul b_ (poly_mul b'_ r_)) in
    let t4 = poly_mul pa (poly_mul (poly_mul b_ b'_) r_) in
    let t5 = poly_mul pa (poly_mul (poly_mul b'_ b_) r_) in
    let t6 = poly_mul (poly_mul pa (poly_mul b'_ b_)) r_ in
    poly_eq_transitivity t1 t2 t3;
    poly_mul_right_congruence pa (poly_mul b_ (poly_mul b'_ r_))
                                 (poly_mul (poly_mul b_ b'_) r_);
    poly_eq_transitivity t1 t3 t4;
    poly_mul_right_congruence pa (poly_mul (poly_mul b_ b'_) r_)
                                 (poly_mul (poly_mul b'_ b_) r_);
    poly_eq_transitivity t1 t4 t5;
    poly_eq_transitivity t1 t5 t6
#pop-options

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let rec yun_loop_pp_invariant (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  : Lemma (ensures poly_eq
      (powered_product_aux (yun_loop #t #f b d acc fuel) 1)
      (poly_mul (poly_mul (powered_product_aux acc 1)
                          (poly_power b (Prims.op_Addition (L.length acc) 1)))
                (yun_loop_b_product #t #f b d fuel)))
    (decreases fuel)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let n : pos = Prims.op_Addition (L.length acc) 1 in
    let pp_acc = powered_product_aux acc 1 in
    let bp = poly_power b n in
    if fuel = 0 || None? (poly_deg b) || Some?.v (poly_deg b) = 0 then begin
      (* Base case: output = acc ++ [b], b_product = poly_one *)
      powered_product_aux_snoc acc b 1;
      let lhs = poly_mul pp_acc bp in
      H.x_mul_one #(polynomial t) lhs;
      poly_eq_symmetry (poly_mul lhs (poly_one #t)) lhs;
      poly_eq_transitivity (powered_product_aux (L.append acc [b]) 1)
                           lhs
                           (poly_mul lhs (poly_one #t))
    end
    else begin
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      let acc' = L.append acc [a] in
      L.append_length acc [a];
      let n' : pos = Prims.op_Addition (L.length acc) 2 in
      assert (L.length acc' == Prims.op_Addition (L.length acc) 1);
      assert (Prims.op_Addition (L.length acc') 1 == n');

      (* IH *)
      yun_loop_pp_invariant #t #f b' d' acc' (fuel - 1);
      let pp_acc' = powered_product_aux acc' 1 in
      let bpn = poly_power b' n in   (* b'^n, NOT b'^n' *)
      let bp' = poly_power b' n' in  (* b'^n' *)
      let bp'_prod = yun_loop_b_product #t #f b' d' (fuel - 1) in
      let output = yun_loop #t #f b d acc fuel in

      (* From IH: PP(output) ≈ (pp_acc' · bp') · bp'_prod *)
      (* We want: PP(output) ≈ (pp_acc · bp) · (b' · bp'_prod) *)

      (* Fact 1: pp_acc' ≈ pp_acc · a^n *)
      powered_product_aux_snoc acc a 1;
      let apn = poly_power a n in

      (* Fact 2: b ≈ a · b' *)
      gcd_has_degree #t #f b d;
      gcd_divides_left #t #f b d;
      poly_div_correct #t #f b a;
      poly_eq_symmetry (poly_mul a b') b;

      (* Fact 3: b^n ≈ a^n · b'^n *)
      poly_power_congruence b (poly_mul a b') n;
      poly_power_mul a b' n;
      poly_eq_transitivity bp (poly_power (poly_mul a b') n) (poly_mul apn bpn);

      (* Fact 4: bp' = poly_mul b' bpn  [definitional, since n' = n+1] *)
      assert (bp' == poly_mul b' (poly_power b' (n' - 1)));
      assert (n' - 1 == n);

      (* Now build the chain:
         (pp_acc · bp) · (b' · bp'_prod)
         ≈ (pp_acc · (apn · bpn)) · (b' · bp'_prod)  [Fact 3, congruence]
         ≈ ((pp_acc · apn) · (b' · bpn)) · bp'_prod  [five_factor_rearrange]
         ≈ (pp_acc' · bp') · bp'_prod                 [Fact 1 + Fact 4, congruence]
         ≈ PP(output)                                  [IH, symmetry]
      *)

      (* Step A: lift Fact 3 into the product *)
      poly_mul_right_congruence pp_acc bp (poly_mul apn bpn);
      poly_mul_left_congruence (poly_mul pp_acc bp)
                               (poly_mul pp_acc (poly_mul apn bpn))
                               (poly_mul b' bp'_prod);
      let s1 = poly_mul (poly_mul pp_acc bp) (poly_mul b' bp'_prod) in
      let s2 = poly_mul (poly_mul pp_acc (poly_mul apn bpn)) (poly_mul b' bp'_prod) in

      (* Step B: five-factor rearrange *)
      five_factor_rearrange pp_acc apn bpn b' bp'_prod;
      let s3 = poly_mul (poly_mul (poly_mul pp_acc apn) (poly_mul b' bpn)) bp'_prod in
      poly_eq_transitivity s1 s2 s3;

      (* Step C: substitute pp_acc' for pp_acc · apn *)
      poly_eq_symmetry pp_acc' (poly_mul pp_acc apn);
      poly_mul_left_congruence (poly_mul pp_acc apn) pp_acc' (poly_mul b' bpn);
      poly_mul_left_congruence (poly_mul (poly_mul pp_acc apn) (poly_mul b' bpn))
                               (poly_mul pp_acc' (poly_mul b' bpn))
                               bp'_prod;
      let s4 = poly_mul (poly_mul pp_acc' (poly_mul b' bpn)) bp'_prod in
      poly_eq_transitivity s1 s3 s4;

      (* Step D: b'·b'^n == b'^(n+1), so s4 == ih_rhs propositionally *)
      let ih_rhs = poly_mul (poly_mul pp_acc' bp') bp'_prod in

      (* Step E: from IH (with symmetry) *)
      poly_eq_symmetry (powered_product_aux output 1) ih_rhs;
      poly_eq_transitivity s1 ih_rhs (powered_product_aux output 1);
      poly_eq_symmetry s1 (powered_product_aux output 1)
    end
#pop-options

(* ================================================================ *)
(*  Top-level corollary: PP(yun_loop b d [] fuel) ≈ b · b_product   *)
(*                                                                  *)
(*  Specializes the loop invariant to acc = []:                     *)
(*    PP_aux([] , 1) = poly_one                                     *)
(*    poly_power b 1 = b · poly_one ≈ b                            *)
(*  So: PP(output) ≈ poly_one · b^1 · b_product ≈ b · b_product   *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let yun_loop_pp_b_product (#t:Type) {| f: field t |}
  (b d: polynomial t) (fuel: nat)
  : Lemma (ensures poly_eq
      (powered_product (yun_loop #t #f b d [] fuel))
      (poly_mul b (yun_loop_b_product #t #f b d fuel)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let bp = yun_loop_b_product #t #f b d fuel in
    let one_p = poly_one #t in
    (* Invoke the loop invariant with acc = [] *)
    yun_loop_pp_invariant #t #f b d [] fuel;
    (* PP(output) ≈ (poly_one · poly_power b 1) · bp *)
    (* Simplify poly_power b 1 ≈ b *)
    H.x_mul_one #(polynomial t) b;
    (* poly_mul b poly_one ≈ b *)
    (* poly_power b 1 == poly_mul b poly_one  [definitional with fuel 2] *)
    (* Simplify poly_mul poly_one (poly_mul b poly_one) ≈ b *)
    poly_mul_right_congruence one_p (poly_mul b one_p) b;
    (* poly_mul one_p (poly_mul b one_p) ≈ poly_mul one_p b *)
    H.one_mul_x #(polynomial t) b;
    (* poly_mul one_p b ≈ b *)
    poly_eq_transitivity (poly_mul one_p (poly_mul b one_p))
                         (poly_mul one_p b)
                         b;
    (* poly_mul one_p (poly_mul b one_p) ≈ b *)
    poly_mul_left_congruence (poly_mul one_p (poly_mul b one_p)) b bp;
    (* (one · (b · one)) · bp ≈ b · bp *)
    let rhs_raw = poly_mul (poly_mul one_p (poly_power b 1)) bp in
    let rhs_clean = poly_mul b bp in
    poly_eq_transitivity (powered_product (yun_loop #t #f b d [] fuel))
                         rhs_raw
                         rhs_clean
#pop-options
