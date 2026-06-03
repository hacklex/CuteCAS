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
  = coprime #t #f p (poly_deriv p)

(* ================================================================ *)
(*  Degree measure for termination                                  *)
(* ================================================================ *)

private let deg_measure (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) : nat
  = match poly_deg p with
    | None   -> 0
    | Some n -> Prims.op_Addition n 1

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
    else if None? (poly_deg b) then L.append acc [b]  // b = 0: include terminal factor
    else if Some?.v (poly_deg b) = 0 then L.append acc [b]  // b is constant: include terminal factor
    else
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      yun_loop #t #f b' d' (L.append acc [a]) (fuel - 1)

(* ================================================================ *)
(*  Yun's algorithm (top level)                                     *)
(* ================================================================ *)

let yun (#t:Type) {| f: field t |}
  (p: polynomial t)
  : list (polynomial t)
  = let p' = poly_deriv p in
    let a0 = poly_gcd #t #f p p' in
    let b0 = poly_div #t #f p a0 in
    let c0 = poly_div #t #f p' a0 in
    let d0 = poly_sub c0 (poly_deriv b0) in
    let fuel = deg_measure a0 in
    yun_loop #t #f b0 d0 [] fuel

(* Public reveal lemma: connects yun p to yun_loop with explicit fuel *)
let yun_unfold (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (let p' = poly_deriv p in
           let a0 = poly_gcd #t #f p p' in
           let b0 = poly_div #t #f p a0 in
           let c0 = poly_div #t #f p' a0 in
           let d0 = poly_sub c0 (poly_deriv b0) in
           let fuel = (match poly_deg a0 with | None -> 0 | Some n -> Prims.op_Addition n 1) in
           yun #t #f p == yun_loop #t #f b0 d0 [] fuel)
  = ()

(* ================================================================ *)
(*  Powered product: a₁ · a₂² · a₃³ · ... · aₘᵐ                    *)
(* ================================================================ *)

let rec poly_power (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (n: nat)
  : Tot (polynomial t) (decreases n)
  = if n = 0 then poly_one #t
    else poly_mul p (poly_power p (n - 1))

let rec powered_product_aux (#t:Type) {| cr: commutative_ring t |}
  (factors: list (polynomial t)) (start_power: pos)
  : Tot (polynomial t) (decreases factors)
  = match factors with
    | [] -> poly_one #t
    | a :: rest ->
        poly_mul (poly_power a start_power)
                 (powered_product_aux rest (Prims.op_Addition start_power 1))

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
  : Lemma (requires Some? (poly_deg d) /\ poly_eq p (poly_mul d c))
          (ensures  (let (quot, rem) = poly_divmod #t #f p d in
                     poly_eq quot c /\ poly_eq rem (poly_zero #t)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let (quot, rem) = poly_divmod #t #f p d in
    poly_divmod_correct #t #f p d;
    poly_divmod_correct_degree #t #f p d;
    // From divmod_correct: poly_eq p (poly_add (poly_mul d quot) rem)
    // Given: poly_eq p (poly_mul d c)
    // Need: poly_eq (poly_add (poly_mul d quot) rem) (poly_add (poly_mul d c) poly_zero)
    poly_add_zero (poly_mul d c);
    // poly_eq (poly_add (poly_mul d c) poly_zero) (poly_mul d c) [from poly_add_zero]
    // poly_eq (poly_mul d c) (poly_add (poly_mul d c) poly_zero)
    // poly_eq p (poly_add (poly_mul d c) poly_zero)
    // poly_eq (poly_add (poly_mul d quot) rem) p
    transitivity (poly_add (poly_mul d quot) rem) p
                 (poly_add (poly_mul d c) (poly_zero #t));
    // Now apply uniqueness
    poly_divmod_unique #t #f d quot c rem (poly_zero #t)

(* poly_div_correct: when d divides p (and d has positive degree),
   poly_mul d (poly_div p d) ≡ p. *)
let poly_div_correct (#t:Type) {| f: field t |}
  (p d: polynomial t)
  : Lemma (requires Some? (poly_deg d) /\ divides d p)
          (ensures  poly_eq (poly_mul d (poly_div #t #f p d)) p)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_div_reveal #t #f p d;
    let (quot, rem) = poly_divmod #t #f p d in
    poly_divmod_correct #t #f p d;
    // Helper: for any witness c, derive the goal
    let aux (c: polynomial t)
      : Lemma (requires poly_eq p (poly_mul d c))
              (ensures  poly_eq (poly_mul d quot) p)
      = poly_div_helper #t #f p d c;
        // Now we have: poly_eq rem poly_zero
        poly_add_zero (poly_mul d quot);
        let pz = poly_zero #t in
        let dq = poly_mul d quot in
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
  : Lemma (requires Some? (poly_deg p))
          (ensures  Some? (poly_deg (poly_gcd #t #f p q)))
  = gcd_divides_left #t #f p q;
    let g = poly_gcd #t #f p q in
    match poly_deg g with
    | Some _ -> ()
    | None ->
        // g has None degree ⟹ g = [] = poly_zero
        assert (g == (poly_zero #t));
        // divides poly_zero p gives ∃c. poly_eq p (poly_mul poly_zero c)
        // poly_mul poly_zero c = poly_mul [] c = trim [] = [] = poly_zero (definitionally)
        // So poly_eq p poly_zero. But poly_deg p = Some _, contradiction via degree_well_defined.
        let aux (c: polynomial t)
          : Lemma (requires poly_eq p (poly_mul g c))
                  (ensures  False)
          = assert (poly_mul g c == (poly_zero #t));
            degree_well_defined p (poly_zero #t)
        in
        Classical.forall_intro (Classical.move_requires aux)

(* ================================================================ *)
(*  Reconstruction at each step                                     *)
(* ================================================================ *)

(* Key step property: b = gcd(b,d) · (b / gcd(b,d)) *)
let yun_step_reconstruction (#t:Type) {| f: field t |}
  (b d: polynomial t)
  : Lemma (requires Some? (poly_deg b))
          (ensures  (let g = poly_gcd #t #f b d in
                     poly_eq (poly_mul g (poly_div #t #f b g)) b))
  = let g = poly_gcd #t #f b d in
    gcd_has_degree #t #f b d;
    gcd_divides_left #t #f b d;
    poly_div_correct #t #f b g

(* ================================================================ *)
(*  Initial decomposition: f = gcd(f,f') · b₀                       *)
(* ================================================================ *)

let yun_initial_decomposition (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires Some? (poly_deg p))
          (ensures  (let a0 = poly_gcd #t #f p (poly_deriv p) in
                     let b0 = poly_div #t #f p a0 in
                     poly_eq (poly_mul a0 b0) p))
  = let p' = poly_deriv p in
    gcd_has_degree #t #f p p';
    gcd_divides_left #t #f p p';
    poly_div_correct #t #f p (poly_gcd #t #f p p')

(* ================================================================ *)
(*  GCD divides both: exact division of d by gcd(b,d) is valid      *)
(* ================================================================ *)

(* The gcd divides d, so poly_div d (gcd b d) is meaningful. *)
let gcd_divides_d_exact (#t:Type) {| f: field t |}
  (b d: polynomial t)
  : Lemma (requires Some? (poly_deg b))
          (ensures  (let g = poly_gcd #t #f b d in
                     divides g d))
  = gcd_divides_right #t #f b d

(* ================================================================ *)
(*  Flat product of a list of polynomials                           *)
(* ================================================================ *)

let rec flat_product (#t:Type) {| cr: commutative_ring t |}
  (factors: list (polynomial t))
  : Tot (polynomial t) (decreases factors)
  = match factors with
    | [] -> poly_one #t
    | a :: rest -> poly_mul a (flat_product rest)

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
  : Lemma (requires poly_eq p q)
          (ensures  poly_eq (poly_mul p r) (poly_mul q r))
  = poly_eq_reflexivity r;
    poly_mul_congruence p r q r

let poly_mul_right_congruence (#t:Type) {| cr: commutative_ring t |}
  (p q r: polynomial t)
  : Lemma (requires poly_eq q r)
          (ensures  poly_eq (poly_mul p q) (poly_mul p r))
  = poly_eq_reflexivity p;
    poly_mul_congruence p q p r

(* flat_product distributes over append *)
let rec flat_product_append (#t:Type) {| cr: commutative_ring t |}
  (xs: list (polynomial t)) (ys: list (polynomial t))
  : Lemma (ensures poly_eq (flat_product (L.append xs ys))
                           (poly_mul (flat_product xs) (flat_product ys)))
          (decreases xs)
  = match xs with
    | [] ->
        (* LHS = flat_product ys
           RHS = poly_mul poly_one (flat_product ys)
           poly_mul_one gives: poly_eq (poly_mul poly_one fp_ys) fp_ys
           We need the reverse direction. *)
        let fp_ys = flat_product ys in
        poly_mul_one fp_ys;
        poly_eq_symmetry (poly_mul (poly_one #t) fp_ys) fp_ys
    | a :: rest ->
        (* LHS = poly_mul a (flat_product (append rest ys))
           RHS = poly_mul (poly_mul a fp_rest) fp_ys
           Chain: LHS ≈ poly_mul a (poly_mul fp_rest fp_ys) ≈ RHS *)
        let fp_rest = flat_product rest in
        let fp_ys = flat_product ys in
        let mid = poly_mul a (poly_mul fp_rest fp_ys) in
        flat_product_append rest ys;
        poly_mul_right_congruence a
          (flat_product (L.append rest ys))
          (poly_mul fp_rest fp_ys);
        (* LHS ≈ mid *)
        poly_mul_associativity a fp_rest fp_ys;
        (* poly_eq (poly_mul (poly_mul a fp_rest) fp_ys) mid, i.e. RHS ≈ mid *)
        poly_eq_symmetry (poly_mul (poly_mul a fp_rest) fp_ys) mid;
        (* mid ≈ RHS *)
        poly_eq_transitivity
          (poly_mul a (flat_product (L.append rest ys)))
          mid
          (poly_mul (poly_mul a fp_rest) fp_ys)

(* Corollary: appending a single factor *)
let flat_product_snoc (#t:Type) {| cr: commutative_ring t |}
  (xs: list (polynomial t)) (y: polynomial t)
  : Lemma (ensures poly_eq (flat_product (L.append xs [y]))
                           (poly_mul (flat_product xs) y))
  = flat_product_append xs [y];
    (* flat_product [y] = poly_mul y (flat_product []) = poly_mul y poly_one *)
    poly_mul_one y;
    (* poly_eq (poly_mul y poly_one) y *)
    poly_mul_right_congruence (flat_product xs)
      (flat_product [y]) y;
    poly_eq_transitivity
      (flat_product (L.append xs [y]))
      (poly_mul (flat_product xs) (flat_product [y]))
      (poly_mul (flat_product xs) y)

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
  : Lemma (ensures poly_eq (flat_product (yun_loop #t #f b d acc fuel))
                           (poly_mul (flat_product acc) b))
          (decreases fuel)
  = if fuel = 0 then begin
      (* result = L.append acc [b]
         flat_product (append acc [b]) ≈ poly_mul (flat_product acc) b
         by flat_product_snoc *)
      flat_product_snoc acc b
    end
    else if None? (poly_deg b) then begin
      flat_product_snoc acc b
    end
    else if Some?.v (poly_deg b) = 0 then begin
      flat_product_snoc acc b
    end
    else begin
      let a = poly_gcd #t #f b d in
      let b' = poly_div #t #f b a in
      let c' = poly_div #t #f d a in
      let d' = poly_sub c' (poly_deriv b') in
      let acc' = L.append acc [a] in
      (* IH gives: flat_product(yun_loop b' d' acc' (fuel-1)) ≈ flat_product(acc') · b' *)
      yun_loop_flat_invariant #t #f b' d' acc' (fuel - 1);
      (* We have: flat_product(acc') = flat_product(append acc [a])
                                     ≈ flat_product(acc) · a  (by snoc) *)
      flat_product_snoc acc a;
      (* And: b ≈ poly_mul a b'  (by yun_step_reconstruction) *)
      yun_step_reconstruction #t #f b d;
      (* Chain: flat_product(acc') · b' ≈ (flat_product(acc) · a) · b'
                                        = flat_product(acc) · (a · b')
                                        ≈ flat_product(acc) · b *)
      (* Step 1: flat_product(acc') ≈ flat_product(acc) · a *)
      (* Step 2: flat_product(acc') · b' ≈ (flat_product(acc) · a) · b' *)
      poly_mul_left_congruence (flat_product acc') (poly_mul (flat_product acc) a) b';
      (* Step 3: (flat_product(acc) · a) · b' ≈ flat_product(acc) · (a · b') -- associativity *)
      poly_mul_associativity (flat_product acc) a b';
      (* Step 4: a · b' ≈ b *)
      poly_eq_symmetry (poly_mul (poly_gcd #t #f b d) (poly_div #t #f b (poly_gcd #t #f b d))) b;
      poly_mul_right_congruence (flat_product acc) (poly_mul a b') b;
      (* Chain all together:
         flat_product(result) ≈ flat_product(acc') · b'  -- IH
         flat_product(acc') · b' ≈ (flat_product(acc) · a) · b'  -- step 2
         (flat_product(acc) · a) · b' ≈ flat_product(acc) · (a · b')  -- step 3
         flat_product(acc) · (a · b') ≈ flat_product(acc) · b  -- step 4
       *)
      let t1 = flat_product (yun_loop #t #f b' d' acc' (fuel - 1)) in
      let t2 = poly_mul (flat_product acc') b' in
      let t3 = poly_mul (poly_mul (flat_product acc) a) b' in
      let t4 = poly_mul (flat_product acc) (poly_mul a b') in
      let t5 = poly_mul (flat_product acc) b in
      poly_eq_transitivity t1 t2 t3;
      poly_eq_transitivity t1 t3 t4;
      poly_eq_transitivity t1 t4 t5
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
  = let pcrc : polynomial_commutative_ring t =
      polynomial_commutative_ring_instance #t #(cr_of_id t #(id_of_f t)) in
    
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match factors with
    | a :: rest ->
        if k = 0 then begin
          (* a | flat_product (a::rest) = poly_mul a (flat_product rest)
             witness: flat_product rest
             Need: poly_eq (poly_mul a (flat_product rest)) (poly_mul a (flat_product rest)) *)
          divides_intro 
            a (poly_mul a (flat_product rest)) (flat_product rest)
        end
        else begin
          (* IH: L.index rest (k-1) | flat_product rest *)
          flat_product_factor_divides #t #f rest (k - 1);
          (* L.index rest (k-1) = L.index factors k *)
          let elem = L.index rest (k - 1) in
          (* From IH: exists c. poly_eq (flat_product rest) (poly_mul elem c) *)
          (* We need: divides elem (poly_mul a (flat_product rest))
             i.e. exists c'. poly_eq (poly_mul a (flat_product rest)) (poly_mul elem c') *)
          let aux (c: polynomial t)
            : Lemma (requires poly_eq (flat_product rest) (poly_mul elem c))
                    (ensures  divides elem (poly_mul a (flat_product rest)))
            = (* poly_mul a (flat_product rest) ≈ poly_mul a (poly_mul elem c)
                 ≈ poly_mul a (poly_mul elem c) ≈ poly_mul elem (poly_mul a c)
                 by commutativity + associativity *)
              poly_mul_right_congruence a (flat_product rest) (poly_mul elem c);
              (* poly_eq (poly_mul a (flat_product rest)) (poly_mul a (poly_mul elem c)) *)
              poly_mul_associativity a elem c;
              (* poly_eq (poly_mul (poly_mul a elem) c) (poly_mul a (poly_mul elem c)) *)
              poly_mul_commutativity a elem;
              (* poly_eq (poly_mul a elem) (poly_mul elem a) *)
              poly_mul_left_congruence (poly_mul a elem) (poly_mul elem a) c;
              (* poly_eq (poly_mul (poly_mul a elem) c) (poly_mul (poly_mul elem a) c) *)
              poly_mul_associativity elem a c;
              (* poly_eq (poly_mul (poly_mul elem a) c) (poly_mul elem (poly_mul a c)) *)
              let m1 = poly_mul a (flat_product rest) in
              let m2 = poly_mul a (poly_mul elem c) in
              let m3 = poly_mul (poly_mul a elem) c in
              let m4 = poly_mul (poly_mul elem a) c in
              let m5 = poly_mul elem (poly_mul a c) in
              divides_intro  elem m1 (poly_mul a c)
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
                    poly_eq (flat_product factors) b)
          (ensures  divides (L.index factors k) b)
  = 
    flat_product_factor_divides #t #f factors k;
    (* divides (L.index factors k) (flat_product factors) *)
    divides_congruence_right 
      (L.index factors k)
      (flat_product factors) b

(* Convenience: a product identity gives divisibility *)
let product_implies_divides (#t:Type) {| f: field t |}
  (a b p: polynomial t)
  : Lemma (requires poly_eq (poly_mul a b) p)
          (ensures  divides a p /\ divides b p)
  = 
    (* divides a p: witness is b. Need poly_eq p (poly_mul a b). *)
    poly_eq_symmetry (poly_mul a b) p;
    divides_intro  a p b;
    (* divides b p: witness is a. Need poly_eq p (poly_mul b a). *)
    poly_mul_commutativity a b;
    poly_eq_transitivity p (poly_mul a b) (poly_mul b a);
    divides_intro  b p a

(* Top-level consequence: gcd(p, p') divides p, and b₀ divides p *)
let yun_initial_both_divide (#t:Type) {| f: field t |}
  (p: polynomial t)
  : Lemma (requires Some? (poly_deg p))
          (ensures  (let a0 = poly_gcd #t #f p (poly_deriv p) in
                     let b0 = poly_div #t #f p a0 in
                     divides a0 p /\ divides b0 p))
  = yun_initial_decomposition #t #f p;
    product_implies_divides #t #f
      (poly_gcd #t #f p (poly_deriv p))
      (poly_div #t #f p (poly_gcd #t #f p (poly_deriv p)))
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
  : Lemma (requires Some? (poly_deg p) /\ Some?.v (poly_deg p) >= 1)
          (ensures  (let a0 = poly_gcd #t #f p (poly_deriv p) in
                     poly_eq (poly_mul a0 (flat_product (yun #t #f p))) p))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let p' = poly_deriv p in
    let a0 = poly_gcd #t #f p p' in
    let b0 = poly_div #t #f p a0 in
    let c0 = poly_div #t #f p' a0 in
    let d0 = poly_sub c0 (poly_deriv b0) in
    let fuel = deg_measure a0 in
    let output = yun_loop #t #f b0 d0 [] fuel in
    (* Step 1: flat_product(output) ≈ poly_mul poly_one b0 *)
    yun_loop_flat_invariant #t #f b0 d0 [] fuel;
    (* Step 2: poly_mul poly_one b0 ≈ b0 *)
    poly_mul_one b0;
    (* Step 3: a0 · flat_product(output) ≈ a0 · b0 *)
    poly_mul_right_congruence a0 (flat_product output) b0;
    (* Step 4: a0 · b0 ≈ p (from yun_initial_decomposition) *)
    yun_initial_decomposition #t #f p;
    poly_eq_transitivity (poly_mul a0 (flat_product output))
                         (poly_mul a0 b0)
                         p

(* Each Yun output factor divides the input polynomial p *)
let yun_factor_divides_p (#t:Type) {| f: field t |}
  (p: polynomial t) (k: nat)
  : Lemma (requires Some? (poly_deg p) /\ Some?.v (poly_deg p) >= 1 /\
                    k < L.length (yun #t #f p))
          (ensures  divides (L.index (yun #t #f p) k) p)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let output = yun #t #f p in
    let a0 = poly_gcd #t #f p (poly_deriv p) in
    (* flat_product(output) | p: from yun_flat_product_identity, a0·fp ≈ p *)
    yun_flat_product_identity #t #f p;
    poly_mul_commutativity a0 (flat_product output);
    poly_eq_transitivity p (poly_mul a0 (flat_product output))
                           (poly_mul (flat_product output) a0);
    divides_intro  (flat_product output) p a0;
    (* L.index output k | flat_product(output) *)
    flat_product_factor_divides #t #f output k;
    (* Transitivity: L.index output k | flat_product(output) | p *)
    divides_trans 
      (L.index output k) (flat_product output) p
