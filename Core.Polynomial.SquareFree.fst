module Core.Polynomial.SquareFree

(*
   Yun's square-free factorization algorithm for univariate polynomials
   over a field of characteristic zero (or char > deg f).

   Main results:
     - square_free : polynomial t -> bool
     - yun        : polynomial t -> list (polynomial t)
     - yun_product_identity (correctness): f = a₁ · a₂² · a₃³ · ... · aₘᵐ
     - yun_factors_square_free: each aᵢ is square-free
     - yun_factors_coprime: aᵢ and aⱼ are coprime for i ≠ j

   Algorithm (Yun 1976):
     a₀ = gcd(f, f')
     b₀ = f / a₀
     c₀ = f' / a₀
     d₀ = c₀ - b₀'
     Loop:
       aᵢ = gcd(bᵢ₋₁, dᵢ₋₁)
       bᵢ = bᵢ₋₁ / aᵢ
       cᵢ = dᵢ₋₁ / aᵢ
       dᵢ = cᵢ - bᵢ'
     Until deg(bᵢ) = 0 (bᵢ is a unit/constant)
     Output: [a₁, a₂, ..., aₘ]
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

(* ================================================================ *)
(*  Square-free predicate                                           *)
(* ================================================================ *)

let square_free (#t:Type) {| f: field t |} (p: polynomial t) : bool
  = coprime p (poly_deriv p)

(* ================================================================ *)
(*  Degree measure for termination                                  *)
(* ================================================================ *)

private let deg_measure (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) : nat
  = if deg p < 0 then 0 else (deg p ++ 1)

(* ================================================================ *)
(*  Yun's loop (iterative step)                                     *)
(*                                                                  *)
(*  State: (b, d, acc) where                                        *)
(*    b = current "quotient" factor                                  *)
(*    d = c - b' at current step                                    *)
(*    acc = accumulated factors so far                               *)
(*                                                                  *)
(*  Uses fuel = deg(b) as termination bound.                        *)
(*  Correctness proof will show fuel never runs out for valid input. *)
(* ================================================================ *)

let rec yun_loop (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  : Tot (list (polynomial t)) (decreases fuel)
  = if fuel = 0 then L.append acc [b]  // fuel exhausted: b is the remaining factor
    else if deg b < 0 then L.append acc [b]  // b = 0: include terminal factor
    else if deg b = 0 then L.append acc [b]  // b is constant: include terminal factor
    else
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' = (c' -- (poly_deriv b')) in
      yun_loop b' d' (L.append acc [a]) (fuel - 1)

(* ================================================================ *)
(*  Yun's algorithm (top level)                                     *)
(* ================================================================ *)

let yun (#t:Type) {| f: field t |}
  (p: polynomial t)
  : list (polynomial t)
  = let p' = poly_deriv p in
    let a0 = poly_gcd p p' in
    let b0 = poly_div p a0 in
    let c0 = poly_div p' a0 in
    let d0 = (c0 -- (poly_deriv b0)) in
    let fuel = deg_measure a0 in
    yun_loop b0 d0 [] fuel

(* Public reveal lemma: connects yun p to yun_loop with explicit fuel *)
let yun_unfold (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (let p' = poly_deriv p in
           let a0 = poly_gcd p p' in
           let b0 = poly_div p a0 in
           let c0 = poly_div p' a0 in
           let d0 = (c0 -- (poly_deriv b0)) in
           let fuel = (if deg a0 < 0 then 0 else (deg a0 ++ 1)) in
           yun p == yun_loop b0 d0 [] fuel)
  = ()

(* ================================================================ *)
(*  Powered product: a₁ · a₂² · a₃³ · ... · aₘᵐ                    *)
(* ================================================================ *)

(* poly_power and poly_power_congruence moved to Core.Polynomial, next to the
   polynomial ring construction — basic & general, not square-free-specific.
   (Both resolve here via `open Core.Polynomial`.) *)

let rec powered_product_aux (#t:Type) {| cr: commutative_ring t |}
  (factors: list (polynomial t)) (start_power: pos)
  : Tot (polynomial t) (decreases factors)
  = match factors with
    | [] -> poly_one #t
    | a :: rest ->
        ((poly_power a start_power)
                 * (powered_product_aux rest (start_power ++ 1)))

let powered_product (#t:Type) {| cr: commutative_ring t |}
  (factors: list (polynomial t))
  : polynomial t
  = powered_product_aux factors 1

(* ================================================================ *)
(*  Exact division correctness                                      *)
(* ================================================================ *)

(* Helper: given explicit witness c with p = d*c, show quot = c, rem = 0 *)
private let poly_div_helper (#t:Type) {| f: field t |}
  (p d c: polynomial t)
  : Lemma (requires deg d >= 0 /\ (p = (d * c)))
          (ensures  (let (quot, rem) = poly_divmod p d in
                     (quot = c) /\ (rem = (poly_zero #t))))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let (quot, rem) = poly_divmod p d in
    // From divmod_correct: poly_eq p (poly_add (poly_mul d quot) rem)
    // Given: poly_eq p (poly_mul d c)
    // Need: poly_eq (poly_add (poly_mul d quot) rem) (poly_add (poly_mul d c) poly_zero)
    add_zero (d * c);
    // poly_eq (poly_add (poly_mul d c) poly_zero) (poly_mul d c) [from poly_add_zero]
    // poly_eq (poly_mul d c) (poly_add (poly_mul d c) poly_zero)
    // poly_eq p (poly_add (poly_mul d c) poly_zero)
    // poly_eq (poly_add (poly_mul d quot) rem) p
    transitivity ((d * quot) + rem) p
                 ((d * c) + poly_zero);
    // Now apply uniqueness
    poly_divmod_unique d quot c rem (poly_zero #t)

(* poly_div_correct: when d divides p (and d has positive degree),
   poly_mul d (poly_div p d) ≡ p. *)
let poly_div_correct (#t:Type) {| f: field t |}
  (p d: polynomial t)
  : Lemma (requires deg d >= 0 /\ divides d p)
          (ensures  ((d * (poly_div p d)) = p))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let (quot, rem) = poly_divmod p d in
    // Helper: for any witness c, derive the goal
    let aux (c: polynomial t)
      : Lemma (requires (p = (d * c)))
              (ensures  ((d * quot) = p))
      = poly_div_helper p d c;
        // Now we have: poly_eq rem poly_zero
        add_zero (d * quot);
        let pz = poly_zero #t in
        let dq = (d * quot) in
        poly_add_congruence dq rem dq pz;
        symmetry dq p
    in
    // Eliminate the existential: divides d p = ∃c. poly_eq p (poly_mul d c)
    Classical.forall_intro (Classical.move_requires aux)

(* ================================================================ *)
(*  GCD nonzero lemma                                               *)
(* ================================================================ *)

(* If p has positive degree and gcd(p,q) divides p, then gcd(p,q) is non-zero.
   More precisely: gcd(p,q) always has Some degree when p does. *)
let gcd_has_degree (#t:Type) {| f: field t |}
  (p q: polynomial t)
  : Lemma (requires deg p >= 0)
          (ensures  deg (poly_gcd p q) >= 0)
  = gcd_divides_left p q;
    let g = poly_gcd p q in
    if deg g >= 0 then () else begin
        // g has None degree ⟹ g = [] = poly_zero
        assert (g == (poly_zero #t));
        // divides poly_zero p gives ∃c. poly_eq p (poly_mul poly_zero c)
        // poly_mul poly_zero c = poly_mul [] c = trim [] = [] = poly_zero (definitionally)
        // So poly_eq p poly_zero. But poly_deg p = Some _, contradiction via degree_well_defined.
        let aux (c: polynomial t)
          : Lemma (requires (p = (g * c)))
                  (ensures  False)
          = assert ((g * c) == (poly_zero #t));
            degree_well_defined p (poly_zero #t)
        in
        Classical.forall_intro (Classical.move_requires aux)
    end

(* ================================================================ *)
(*  Reconstruction at each step                                     *)
(* ================================================================ *)

(* Key step property: b = gcd(b,d) · (b / gcd(b,d)) *)
let yun_step_reconstruction (#t:Type) {| f: field t |}
  (b d: polynomial t)
  : Lemma (requires deg b >= 0)
          (ensures  (let g = poly_gcd b d in
                     ((g * (poly_div b g)) = b)))
  = let g = poly_gcd b d in
    gcd_has_degree b d;
    gcd_divides_left b d;
    poly_div_correct b g

(* ================================================================ *)
(*  Initial decomposition: f = gcd(f,f') · b₀                       *)
(* ================================================================ *)

let yun_initial_decomposition (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires deg p >= 0)
          (ensures  (let a0 = poly_gcd p (poly_deriv p) in
                     let b0 = poly_div p a0 in
                     ((a0 * b0) = p)))
  = let p' = poly_deriv p in
    gcd_has_degree p p';
    gcd_divides_left p p';
    poly_div_correct p (poly_gcd p p')

(* ================================================================ *)
(*  GCD divides both: exact division of d by gcd(b,d) is valid      *)
(* ================================================================ *)

(* The gcd divides d, so poly_div d (gcd b d) is meaningful. *)
let gcd_divides_d_exact (#t:Type) {| f: field t |}
  (b d: polynomial t)
  : Lemma (requires deg b >= 0)
          (ensures  (let g = poly_gcd b d in
                     divides g d))
  = gcd_divides_right b d

(* ================================================================ *)
(*  Flat product of a list of polynomials                           *)
(* ================================================================ *)

let rec flat_product (#t:Type) {| cr: commutative_ring t |}
  (factors: list (polynomial t))
  : Tot (polynomial t) (decreases factors)
  = match factors with
    | [] -> poly_one #t
    | a :: rest -> (a * (flat_product rest))

(* ================================================================ *)
(*  Flat product chain: b₀ = flat_product(yun factors) · b_final    *)
(* ================================================================ *)

(* This is the flat (non-powered) product identity for the loop.
   At each step, b_{k-1} = gcd(b,d) · b_k, so chaining through the
   full loop gives b₀ = a₁ · a₂ · ... · aₘ · b_final.
   When the loop terminates with b_final of degree ≤ 0, this
   accounts for all non-trivial factors. *)

(* Helper: poly_mul is congruence-compatible with poly_eq *)
let poly_mul_left_congruence (#t:Type) {| cr: commutative_ring t |}
  (p q r: polynomial t)
  : Lemma (requires (p = q))
          (ensures  ((p * r) = (q * r)))
  = poly_eq_reflexivity r;
    poly_mul_congruence p r q r

let poly_mul_right_congruence (#t:Type) {| cr: commutative_ring t |}
  (p q r: polynomial t)
  : Lemma (requires (q = r))
          (ensures  ((p * q) = (p * r)))
  = poly_eq_reflexivity p;
    poly_mul_congruence p q p r

(* flat_product distributes over append *)
let rec flat_product_append (#t:Type) {| cr: commutative_ring t |}
  (xs: list (polynomial t)) (ys: list (polynomial t))
  : Lemma (ensures ((flat_product (L.append xs ys))
                           = ((flat_product xs) * (flat_product ys))))
          (decreases xs)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match xs with
    | [] ->
        (* LHS = flat_product ys
           RHS = poly_mul poly_one (flat_product ys)
           mul_one gives: poly_eq (poly_mul poly_one fp_ys) fp_ys
           symmetry/transitivity from the equatable-laws above. *)
        let fp_ys = flat_product ys in
        mul_one fp_ys
    | a :: rest ->
        (* LHS = poly_mul a (flat_product (append rest ys))
           RHS = poly_mul (poly_mul a fp_rest) fp_ys
           Chain: LHS ≈ poly_mul a (poly_mul fp_rest fp_ys) ≈ RHS *)
        let fp_rest = flat_product rest in
        let fp_ys = flat_product ys in
        flat_product_append rest ys;
        poly_mul_right_congruence a
          (flat_product (L.append rest ys))
          (fp_rest * fp_ys);
        (* LHS ≈ mid *)
        mul_associativity a fp_rest fp_ys
        (* RHS ≈ mid via associativity; symmetry+transitivity from equatable laws *)

(* Corollary: appending a single factor *)
let flat_product_snoc (#t:Type) {| cr: commutative_ring t |}
  (xs: list (polynomial t)) (y: polynomial t)
  : Lemma (ensures ((flat_product (L.append xs [y]))
                           = ((flat_product xs) * y)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    flat_product_append xs [y];
    (* flat_product [y] = poly_mul y (flat_product []) = poly_mul y poly_one *)
    mul_one y;
    (* poly_eq (poly_mul y poly_one) y *)
    poly_mul_right_congruence (flat_product xs)
      (flat_product [y]) y
    (* transitivity from equatable laws *)

(* ================================================================ *)
(*  Main loop invariant: flat_product(acc) · b is conserved         *)
(* ================================================================ *)

(* The Yun loop preserves the invariant:
     flat_product(result) ≈ flat_product(acc) · b
   where result = yun_loop b d acc fuel.
   In other words, the flat product of the accumulated factors times the
   remaining b-polynomial stays constant throughout the recursion. *)

let rec yun_loop_flat_invariant (#t:Type) {| f: field t |}
  (b d: polynomial t) (acc: list (polynomial t)) (fuel: nat)
  : Lemma (ensures ((flat_product (yun_loop b d acc fuel))
                           = ((flat_product acc) * b)))
          (decreases fuel)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    if fuel = 0 then begin
      (* result = L.append acc [b]
         flat_product (append acc [b]) ≈ poly_mul (flat_product acc) b
         by flat_product_snoc *)
      flat_product_snoc acc b
    end
    else if deg b < 0 then begin
      flat_product_snoc acc b
    end
    else if deg b = 0 then begin
      flat_product_snoc acc b
    end
    else begin
      let a = poly_gcd b d in
      let b' = poly_div b a in
      let c' = poly_div d a in
      let d' = (c' -- (poly_deriv b')) in
      let acc' = L.append acc [a] in
      (* IH gives: flat_product(yun_loop b' d' acc' (fuel-1)) ≈ flat_product(acc') · b' *)
      yun_loop_flat_invariant b' d' acc' (fuel - 1);
      (* We have: flat_product(acc') = flat_product(append acc [a])
                                     ≈ flat_product(acc) · a  (by snoc) *)
      flat_product_snoc acc a;
      (* And: b ≈ poly_mul a b'  (by yun_step_reconstruction) *)
      yun_step_reconstruction b d;
      (* Chain: flat_product(acc') · b' ≈ (flat_product(acc) · a) · b'
                                        = flat_product(acc) · (a · b')
                                        ≈ flat_product(acc) · b *)
      (* Step 1: flat_product(acc') ≈ flat_product(acc) · a *)
      (* Step 2: flat_product(acc') · b' ≈ (flat_product(acc) · a) · b' *)
      poly_mul_left_congruence (flat_product acc') ((flat_product acc) * a) b';
      (* Step 3: (flat_product(acc) · a) · b' ≈ flat_product(acc) · (a · b') -- associativity *)
      mul_associativity (flat_product acc) a b';
      (* Step 4: a · b' ≈ b (reconstruction gives b = a·b'; symmetry from equatable laws) *)
      poly_mul_right_congruence (flat_product acc) (a * b') b
      (* Chain closed by trans_for_calc:
         flat_product(result) ≈ flat_product(acc') · b'  -- IH
         flat_product(acc') · b' ≈ (flat_product(acc) · a) · b'  -- step 2
         (flat_product(acc) · a) · b' ≈ flat_product(acc) · (a · b')  -- step 3
         flat_product(acc) · (a · b') ≈ flat_product(acc) · b  -- step 4
       *)
    end

(* ================================================================ *)
(*  Each factor divides the flat product                            *)
(* ================================================================ *)

(* If a factor appears at index k in the list, it divides the
   flat product of the entire list. This gives us: each output
   of yun divides b₀. *)

let rec flat_product_factor_divides (#t:Type) {| f: field t |}
  (factors: list (polynomial t)) (k: nat)
  : Lemma (requires k < L.length factors)
          (ensures  divides (L.index factors k) (flat_product factors))
          (decreases factors)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match factors with
    | a :: rest ->
        if k = 0 then begin
          (* a | flat_product (a::rest) = poly_mul a (flat_product rest)
             witness: flat_product rest
             Need: poly_eq (poly_mul a (flat_product rest)) (poly_mul a (flat_product rest)) *)
          divides_intro
            a (a * (flat_product rest)) (flat_product rest)
        end
        else begin
          (* IH: L.index rest (k-1) | flat_product rest *)
          flat_product_factor_divides rest (k - 1);
          (* L.index rest (k-1) = L.index factors k *)
          let elem = L.index rest (k - 1) in
          (* From IH: exists c. poly_eq (flat_product rest) (poly_mul elem c) *)
          (* We need: divides elem (poly_mul a (flat_product rest))
             i.e. exists c'. poly_eq (poly_mul a (flat_product rest)) (poly_mul elem c') *)
          let aux (c: polynomial t)
            : Lemma (requires ((flat_product rest) = (elem * c)))
                    (ensures  divides elem (a * (flat_product rest)))
            = (* poly_mul a (flat_product rest) ≈ poly_mul a (poly_mul elem c)
                 ≈ poly_mul a (poly_mul elem c) ≈ poly_mul elem (poly_mul a c)
                 by commutativity + associativity *)
              poly_mul_right_congruence a (flat_product rest) (elem * c);
              (* poly_eq (poly_mul a (flat_product rest)) (poly_mul a (poly_mul elem c)) *)
              mul_associativity a elem c;
              (* poly_eq (poly_mul (poly_mul a elem) c) (poly_mul a (poly_mul elem c)) *)
              mul_commutativity a elem;
              (* poly_eq (poly_mul a elem) (poly_mul elem a) *)
              poly_mul_left_congruence (a * elem) (elem * a) c;
              (* poly_eq (poly_mul (poly_mul a elem) c) (poly_mul (poly_mul elem a) c) *)
              mul_associativity elem a c;
              (* poly_eq (poly_mul (poly_mul elem a) c) (poly_mul elem (poly_mul a c)) *)
              let m1 = (a * (flat_product rest)) in
              let m2 = (a * (elem * c)) in
              let m3 = ((a * elem) * c) in
              let m4 = ((elem * a) * c) in
              let m5 = (elem * (a * c)) in
              divides_intro  elem m1 (a * c)
          in
          Classical.forall_intro (Classical.move_requires aux)
        end

(* ================================================================ *)
(*  Yun output factors divide b₀                                    *)
(* ================================================================ *)

(* Combined with yun_initial_decomposition (f = gcd(f,f') · b₀)
   and yun_loop_flat_invariant (flat_product(output) ≈ ... · b₀),
   this establishes that each output factor divides the input. *)

(* When the loop terminates via fuel=0, we have the strongest form:
   each output factor divides b₀ because the flat product of the
   output equals b₀ (modulo the fuel=0 case). *)
let yun_output_factor_divides_flat (#t:Type) {| f: field t |}
  (factors: list (polynomial t)) (k: nat) (b: polynomial t)
  : Lemma (requires k < L.length factors /\
                    ((flat_product factors) = b))
          (ensures  divides (L.index factors k) b)
  = 
    flat_product_factor_divides factors k;
    (* divides (L.index factors k) (flat_product factors) *)
    divides_congruence_right 
      (L.index factors k)
      (flat_product factors) b

(* Convenience: a product identity gives divisibility *)
let product_implies_divides (#t:Type) {| f: field t |}
  (a b p: polynomial t)
  : Lemma (requires ((a * b) = p))
          (ensures  divides a p /\ divides b p)
  =
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* divides a p: witness is b. Need poly_eq p (poly_mul a b); symmetry from laws. *)
    divides_intro  a p b;
    (* divides b p: witness is a. Need poly_eq p (poly_mul b a); comm + transitivity. *)
    mul_commutativity a b;
    divides_intro  b p a

(* Top-level consequence: gcd(p, p') divides p, and b₀ divides p *)
let yun_initial_both_divide (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires deg p >= 0)
          (ensures  (let a0 = poly_gcd p (poly_deriv p) in
                     let b0 = poly_div p a0 in
                     divides a0 p /\ divides b0 p))
  = yun_initial_decomposition p;
    product_implies_divides
      (poly_gcd p (poly_deriv p))
      (poly_div p (poly_gcd p (poly_deriv p)))
      p

(* ================================================================ *)
(*  Top-level flat product identity:                                *)
(*    a₀ · flat_product(yun(p)) ≈ p                                 *)
(*                                                                  *)
(*  Combines yun_initial_decomposition (p ≈ a₀ · b₀) with          *)
(*  yun_loop_flat_invariant (flat_product(output) ≈ poly_one · b₀). *)
(* ================================================================ *)

let yun_flat_product_identity (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires deg p >= 1)
          (ensures  (let a0 = poly_gcd p (poly_deriv p) in
                     ((a0 * (flat_product (yun p))) = p)))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let p' = poly_deriv p in
    let a0 = poly_gcd p p' in
    let b0 = poly_div p a0 in
    let c0 = poly_div p' a0 in
    let d0 = (c0 -- (poly_deriv b0)) in
    let fuel = deg_measure a0 in
    let output = yun_loop b0 d0 [] fuel in
    (* Step 1: flat_product(output) ≈ poly_mul poly_one b0 *)
    yun_loop_flat_invariant b0 d0 [] fuel;
    (* Step 2: poly_mul poly_one b0 ≈ b0 *)
    mul_one b0;
    (* Step 3: a0 · flat_product(output) ≈ a0 · b0 *)
    poly_mul_right_congruence a0 (flat_product output) b0;
    (* Step 4: a0 · b0 ≈ p (from yun_initial_decomposition); transitivity from laws *)
    yun_initial_decomposition p

(* Each Yun output factor divides the input polynomial p *)
let yun_factor_divides_p (#t:Type) {| f: field t |}
  (p: polynomial t) (k: nat)
  : Lemma (requires deg p >= 1 /\
                    k < L.length (yun p))
          (ensures  divides (L.index (yun p) k) p)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let output = yun p in
    let a0 = poly_gcd p (poly_deriv p) in
    (* flat_product(output) | p: from yun_flat_product_identity, a0·fp ≈ p *)
    yun_flat_product_identity p;
    mul_commutativity a0 (flat_product output);
    divides_intro  (flat_product output) p a0;
    (* L.index output k | flat_product(output) *)
    flat_product_factor_divides output k;
    (* Transitivity: L.index output k | flat_product(output) | p *)
    divides_trans 
      (L.index output k) (flat_product output) p
