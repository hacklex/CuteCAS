module Core.Matrix.Determinant.Mul

(*
   Cauchy-Binet: det (matrix_mul a b) = det a * det b.

   Strategy (Leibniz):
     det (AB)
       = sum_σ sign σ * perm_product (AB) σ                      [Leibniz]
       = sum_σ sign σ * prod_i (sum_k a(i,k) b(k, σ i))           [matrix_mul]
       = sum_σ sign σ * sum_φ prod_i a(i, φ i) * b(φ i, σ i)      [multi-distrib]
       = sum_φ (prod_i a(i, φ i)) *
              (sum_σ sign σ * prod_i b(φ i, σ i))                 [factor, swap]
       = sum_φ (prod_i a(i, φ i)) * det (phi_matrix b φ)          [Leibniz]
       = sum_{φ injective} (prod_i a(i, φ i)) * sign(perm φ) * det b
                                                                  [vanishing]
       = (sum_π sign π * prod_i a(i, π i)) * det b                [reindex]
       = det a * det b.

   No lambdas in postconditions: every shape used in a lemma statement is
   a top-level (or `private let`) named function whose TC instances are
   captured at definition site, so all callers refer to the same SMT term.
*)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.FinSum
open Core.Permutation
open Core.Permutation.Enum
open Core.Permutation.Sum
open Core.Matrix
open Core.Matrix.Ring
open Core.Matrix.MultiDistrib
open Core.Matrix.Determinant
open Core.Tactics.CanonRing

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ============================================================ *)
(*  Section A: Named term builders.                              *)
(*  Every function used in a lemma statement is named here so    *)
(*  SMT sees a stable symbol across sites.                       *)
(* ============================================================ *)

(* Inner expansion term: a(i,k) * b(k, sigma i).
   Used inside `fin_sum` for matrix_mul_eq_at expansion. *)
let ab_k (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (i: fin n) (k: fin n) : t
  = a i k * b k (sigma.fwd i)

(* Outer Leibniz term, expanded via matrix_mul:
   if i<n then (AB)(i, sigma i) else one. *)
let ab_perm_body (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (i: nat) : t
  = if i < n then (matrix_mul a b) (i <: fin n) (sigma.fwd (i <: fin n))
    else one

(* Same outer term but expanded as fin_sum:
   if i<n then sum_k a(i,k) b(k, sigma i) else one. *)
let finsum_perm_body (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (i: nat) : t
  = if i < n then fin_sum (ab_k a b sigma (i <: fin n))
    else one

(* Multi-distrib expansion: pick a representative φ for each factor.
   if i<n then a(i, φ i) * b(φ i, sigma i) else one. *)
let phi_inner_body (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n) (i: nat) : t
  = if i < n then ab_k a b sigma (i <: fin n) (phi (i <: fin n))
    else one

(* prod_range of phi_inner_body — one summand of the multi-distrib sum
   over fin_map n n. *)
let phi_outer (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n) : t
  = prod_range (phi_inner_body a b sigma phi) 0 n

(* ============================================================ *)
(*  Section B: perm_product expanded as a sum over fin_map n n.    *)
(* ============================================================ *)

(* Step B.1: perm_product (matrix_mul a b) sigma
            = prod_range (finsum_perm_body a b sigma) 0 n.

   Pointwise, ab_perm_body i = finsum_perm_body i (for i < n) by
   matrix_mul_eq_at.  Then prod_range_congruence. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let perm_product_as_finsum_prod
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (perm_product (matrix_mul a b) sigma
           = prod_range (finsum_perm_body a b sigma) 0 n)
  = H.elim_equatable_laws t ();
    let pointwise (i: nat)
      : Lemma (requires 0 <= i /\ i < n)
              (ensures ab_perm_body a b sigma i = finsum_perm_body a b sigma i)
      = let ii : fin n = i in
        assert (matrix_mul a b ii (sigma.fwd ii) ==
                fin_sum (ab_k a b sigma ii))
          by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
        H.leibniz_to_eq (matrix_mul a b ii (sigma.fwd ii))
                        (fin_sum (ab_k a b sigma ii))
    in
    Classical.forall_intro (Classical.move_requires pointwise);
    prod_range_congruence (ab_perm_body a b sigma) (finsum_perm_body a b sigma) 0 n (fun _ -> ());
    assert (perm_product (matrix_mul a b) sigma ==
            prod_range (ab_perm_body a b sigma) 0 n)
      by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
    H.leibniz_then_eq (perm_product (matrix_mul a b) sigma)
                      (prod_range (ab_perm_body a b sigma) 0 n)
                      (prod_range (finsum_perm_body a b sigma) 0 n)
#pop-options

(* Step B.2: Apply multi-distrib expansion.
   prod_range (finsum_perm_body a b sigma) 0 n
     = sum_over_fns_to n n (phi_outer a b sigma).                         *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let prod_range_finsum_to_sum_over_fns
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (prod_range (finsum_perm_body a b sigma) 0 n
           = sum_over_fns_to n n (phi_outer a b sigma))
  = H.elim_equatable_laws t ();
    prod_range_of_fin_sum #t #(cr.cr_r) n n (ab_k a b sigma);
    (* That gives:
         prod_range (fun i -> if i<n then fin_sum (ab_k a b sigma i) else one) 0 n
         = sum_over_fns_to n n (fun phi -> prod_range (fun i -> if i<n then ab_k a b sigma i (phi i) else one) 0 n)
       Both sides definitionally match our named functions.            *)
    assert (prod_range (finsum_perm_body a b sigma) 0 n ==
            prod_range (fun (i: nat) ->
              if i < n then fin_sum (ab_k a b sigma (i <: fin n)) else one) 0 n)
      by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
    assert (sum_over_fns_to n n (phi_outer a b sigma) ==
            sum_over_fns_to #t #(acg_of_r t #(cr.cr_r)) n n
              (fun (phi: fin_map n n) ->
                prod_range (fun (i: nat) ->
                  if i < n then ab_k a b sigma (i <: fin n) (phi (i <: fin n))
                  else one) 0 n))
      by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
    ()
#pop-options
(* Step B.3: Compose B.1 + B.2.
   perm_product (matrix_mul a b) sigma = sum_over_fns_to n n (phi_outer a b sigma).  *)
let perm_product_to_sum_over_fns
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (perm_product (matrix_mul a b) sigma
           = sum_over_fns_to n n (phi_outer a b sigma))
  = perm_product_as_finsum_prod a b sigma;
    prod_range_finsum_to_sum_over_fns a b sigma;
    transitivity (perm_product (matrix_mul a b) sigma)
                 (prod_range (finsum_perm_body a b sigma) 0 n)
                 (sum_over_fns_to n n (phi_outer a b sigma))

(* ============================================================ *)
(* Section C: Factor phi_outer = phi_prod * perm_product(phi_mat) *)
(* ============================================================ *)

(* Named: prod_i a(i, phi i), via fin_prod over apply_along.   *)
let phi_prod (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a: square_matrix t n) (phi: fin_map n n) : t
  = fin_prod (apply_along a phi)

(* Named: matrix whose row i is row (phi i) of b.               *)
let phi_matrix (#t: Type) (#n: pos)
  (b: square_matrix t n) (phi: fin_map n n) : square_matrix t n
  = fun i j -> b (phi i) j

(* Named: ab_perm_body for the phi_matrix:                       *)
let phi_matrix_perm_body (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (b: square_matrix t n) (phi: fin_map n n) (sigma: permutation n) (i: nat) : t
  = if i < n then (phi_matrix b phi) (i <: fin n) (sigma.fwd (i <: fin n))
    else one
(* ============================================================ *)
(*  Section C-pre: Helper lemma — pointwise product factors.    *)
(* ============================================================ *)

(* Named pairwise product. *)
let pw_mul (#t: Type) {| cr: commutative_ring t |} (f g: nat -> t) (i: nat) : t
  = f i * g i

(* Helper: (a*b) * (c*d) = (a*c) * (b*d). *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let four_swap_cr
  (#t: Type) {| cr: commutative_ring t |} (a b c d: t)
  : Lemma ((a * b) * (c * d) = (a * c) * (b * d))
  = assert ((a * b) * (c * d) = (a * c) * (b * d)) by canon_ring ()
#pop-options
(* prod_range_factor: pointwise multiplicative factoring of prod_range over
   commutative ring.  Uses the named pw_mul to avoid lambda-in-postcondition. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec prod_range_factor
  (#t: Type) {| cr: commutative_ring t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma
    (ensures prod_range (pw_mul f g) lo hi
           = prod_range f lo hi * prod_range g lo hi)
    (decreases (hi - lo))
  = H.elim_equatable_laws t ();
    if lo >= hi then begin
      prod_range_empty (pw_mul f g) lo hi;
      prod_range_empty f lo hi;
      prod_range_empty g lo hi;
      reflexivity (one #t);
      mul_congruence (prod_range f lo hi) (prod_range g lo hi) (one #t) (one #t);
      H.one_mul_x (one #t);
      transitivity (prod_range f lo hi * prod_range g lo hi)
                   (one #t * one #t) (one #t);
      symmetry (prod_range f lo hi * prod_range g lo hi) (one #t);
      transitivity (prod_range (pw_mul f g) lo hi)
                   (one #t)
                   (prod_range f lo hi * prod_range g lo hi)
    end else begin
      prod_range_unfold_left (pw_mul f g) lo hi;
      prod_range_unfold_left f lo hi;
      prod_range_unfold_left g lo hi;
      prod_range_factor f g (Prims.op_Addition lo 1) hi;
      let pf = prod_range f (Prims.op_Addition lo 1) hi in
      let pg = prod_range g (Prims.op_Addition lo 1) hi in
      let pfg = prod_range (pw_mul f g) (Prims.op_Addition lo 1) hi in
      (* pfg = pf * pg by IH *)
      reflexivity (f lo * g lo);
      mul_congruence (f lo * g lo) pfg (f lo * g lo) (pf * pg);
      four_swap_cr (f lo) (g lo) pf pg;
      (* now: (f lo * g lo) * pfg = (f lo * g lo) * (pf*pg) = (f lo * pf) * (g lo * pg) *)
      transitivity ((f lo * g lo) * pfg)
                   ((f lo * g lo) * (pf * pg))
                   ((f lo * pf) * (g lo * pg));
      reflexivity (prod_range f lo hi);
      reflexivity (prod_range g lo hi);
      mul_congruence (f lo * pf) (g lo * pg)
                     (prod_range f lo hi) (prod_range g lo hi);
      transitivity ((f lo * g lo) * pfg)
                   ((f lo * pf) * (g lo * pg))
                   (prod_range f lo hi * prod_range g lo hi);
      (* finally: prod_range (pw_mul f g) lo hi = (f lo * g lo) * pfg = ... *)
      reflexivity (prod_range (pw_mul f g) lo hi);
      H.leibniz_to_eq (prod_range (pw_mul f g) lo hi) ((f lo * g lo) * pfg);
      transitivity (prod_range (pw_mul f g) lo hi)
                   ((f lo * g lo) * pfg)
                   (prod_range f lo hi * prod_range g lo hi)
    end
#pop-options
(* The two named factors of phi_inner_body: the a-side and the b-side. *)
let phi_a_part (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a: square_matrix t n) (phi: fin_map n n) (i: nat) : t
  = if i < n then a (i <: fin n) (phi (i <: fin n)) else one

let phi_b_part (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (b: square_matrix t n) (phi: fin_map n n) (sigma: permutation n) (i: nat) : t
  = if i < n then b (phi (i <: fin n)) (sigma.fwd (i <: fin n)) else one

(* phi_inner_body = pw_mul (phi_a_part a phi) (phi_b_part b phi sigma). *)
let phi_inner_body_def
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n)
  : Lemma (forall (i: nat). phi_inner_body a b sigma phi i =
                            pw_mul (phi_a_part a phi) (phi_b_part b phi sigma) i)
  = H.elim_equatable_laws t ();
    let aux (i: nat) : Lemma (phi_inner_body a b sigma phi i =
                              pw_mul (phi_a_part a phi) (phi_b_part b phi sigma) i)
      = if i < n then
          reflexivity (a (i <: fin n) (phi (i <: fin n))
                         * b (phi (i <: fin n)) (sigma.fwd (i <: fin n)))
        else begin
          H.one_mul_x (one #t);
          symmetry (one #t * one #t) (one #t)
        end
    in
    Classical.forall_intro aux

(* Factor lemma: prod_range phi_inner_body = prod a-part * prod b-part. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let phi_outer_factored
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n)
  : Lemma (phi_outer a b sigma phi =
           prod_range (phi_a_part a phi) 0 n
           * prod_range (phi_b_part b phi sigma) 0 n)
  = H.elim_equatable_laws t ();
    phi_inner_body_def a b sigma phi;
    prod_range_congruence (phi_inner_body a b sigma phi)
                          (pw_mul (phi_a_part a phi) (phi_b_part b phi sigma))
                          0 n (fun _ -> ());
    prod_range_factor (phi_a_part a phi) (phi_b_part b phi sigma) 0 n;
    transitivity (phi_outer a b sigma phi)
                 (prod_range (pw_mul (phi_a_part a phi) (phi_b_part b phi sigma)) 0 n)
                 (prod_range (phi_a_part a phi) 0 n * prod_range (phi_b_part b phi sigma) 0 n)
#pop-options
(* Compose: phi_outer = phi_prod * perm_product (phi_matrix b phi).        *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let phi_outer_eq_a_prod_perm_product
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n)
  : Lemma (phi_outer a b sigma phi =
           phi_prod a phi * perm_product (phi_matrix b phi) sigma)
  = H.elim_equatable_laws t ();
    phi_outer_factored a b sigma phi;
    (* prod_range (phi_a_part a phi) 0 n == phi_prod a phi by eta. *)
    assert (prod_range (phi_a_part a phi) 0 n == phi_prod a phi)
      by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
    (* prod_range (phi_b_part b phi sigma) 0 n == perm_product (phi_matrix b phi) sigma. *)
    assert (prod_range (phi_b_part b phi sigma) 0 n ==
            perm_product (phi_matrix b phi) sigma)
      by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
    H.leibniz_to_eq (prod_range (phi_a_part a phi) 0 n) (phi_prod a phi);
    H.leibniz_to_eq (prod_range (phi_b_part b phi sigma) 0 n)
                    (perm_product (phi_matrix b phi) sigma);
    mul_congruence (prod_range (phi_a_part a phi) 0 n)
                   (prod_range (phi_b_part b phi sigma) 0 n)
                   (phi_prod a phi)
                   (perm_product (phi_matrix b phi) sigma);
    transitivity (phi_outer a b sigma phi)
                 (prod_range (phi_a_part a phi) 0 n
                  * prod_range (phi_b_part b phi sigma) 0 n)
                 (phi_prod a phi * perm_product (phi_matrix b phi) sigma)
#pop-options
(* ============================================================ *)
(*  Section E.1: Non-injective phi forces det(phi_matrix b phi) = 0. *)
(* ============================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let det_phi_matrix_non_inj
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (b: square_matrix t n) (phi: fin_map n n) (i j: fin n)
  : Lemma (requires ~(i == j) /\ phi i == phi j)
          (ensures  det (phi_matrix b phi) = zero)
  = H.elim_equatable_laws t ();
    let m = phi_matrix b phi in
    let aux (k: fin n) : Lemma (m i k = m j k)
      = assert (m i k == b (phi i) k);
        assert (m j k == b (phi j) k);
        assert (phi i == phi j);
        reflexivity (b (phi i) k)
    in
    Classical.forall_intro aux;
    det_two_equal_rows_cr #t #cr #n m i j
#pop-options
(* ============================================================ *)
(*  Section D: Combinatorial machinery on fin_map n n.            *)
(*  search_preimage, compress_val, injective_surjective,        *)
(*  inverse_fn, perm_of_injective_fn, is_injective_b.           *)
(* ============================================================ *)

private let rec search_preimage (#n: pos) (f: fin_map n n) (target: fin n) (k: nat)
  : Tot (option (fin n)) (decreases (n - k))
  = if k >= n then None
    else if f (k <: fin n) = target then Some (k <: fin n)
    else search_preimage f target (Prims.op_Addition k 1)

private let rec search_preimage_spec (#n: pos) (f: fin_map n n) (target: fin n) (k: nat)
  : Lemma (ensures (match search_preimage f target k with
                    | Some j -> f j == target
                    | None -> forall (j: fin n). (j <: nat) >= k ==> ~(f j == target)))
          (decreases (n - k))
  = if k >= n then ()
    else if f (k <: fin n) = target then ()
    else search_preimage_spec f target (Prims.op_Addition k 1)

private let compress_val (n: nat{n >= 2}) (gap: fin n) (v: fin n) : fin (Prims.op_Subtraction n 1)
  = if (v <: nat) < (gap <: nat) then (v <: nat)
    else if (v <: nat) = (gap <: nat) then 0
    else Prims.op_Subtraction (v <: nat) 1

private let compress_val_injective (n: nat{n >= 2}) (gap: fin n) (v1 v2: fin n)
  : Lemma (requires ~(v1 == gap) /\ ~(v2 == gap) /\ compress_val n gap v1 == compress_val n gap v2)
          (ensures v1 == v2)
  = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
private let rec injective_surjective (#n: pos) (f: fin_map n n) (target: fin n)
  : Lemma (requires forall (i j: fin n). f i == f j ==> i == j)
          (ensures Some? (search_preimage f target 0))
          (decreases n)
  = if n = 0 then ()
    else if n = 1 then
      search_preimage_spec f target 0
    else begin
      search_preimage_spec f target 0;
      if Some? (search_preimage f target 0) then ()
      else begin
        let n1 : nat = Prims.op_Subtraction n 1 in
        let last : fin n = n1 in
        let g : fin_map n1 n1 = fun (i: fin n1) -> compress_val n target (f (i <: fin n)) in
        let g_inj (i1 i2: fin n1)
          : Lemma (requires g i1 == g i2) (ensures i1 == i2) =
            compress_val_injective n target (f (i1 <: fin n)) (f (i2 <: fin n))
        in
        Classical.forall_intro_2 (fun i1 -> Classical.move_requires (g_inj i1));
        let target' : fin n1 = compress_val n target (f last) in
        injective_surjective #n1 g target';
        search_preimage_spec #n1 g target' 0;
        let j' = Some?.v (search_preimage #n1 g target' 0) in
        compress_val_injective n target (f (j' <: fin n)) (f last);
        assert False
      end
    end
#pop-options

private let inverse_fn (#n: pos) (f: fin_map n n)
  (f_inj: squash (forall (i j: fin n). f i == f j ==> i == j))
  (target: fin n) : fin n
  = injective_surjective f target;
    search_preimage_spec f target 0;
    Some?.v (search_preimage f target 0)

private let inverse_fn_spec (#n: pos) (f: fin_map n n)
  (f_inj: squash (forall (i j: fin n). f i == f j ==> i == j))
  (target: fin n) : Lemma (f (inverse_fn f f_inj target) == target)
  = injective_surjective f target;
    search_preimage_spec f target 0

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let perm_of_injective_fn (#n: pos) (f: fin_map n n)
  (f_inj: squash (forall (i j: fin n). f i == f j ==> i == j))
  : (p: permutation n { forall (i: fin n). p.fwd i == f i })
  = let bwd = inverse_fn f f_inj in
    let fwd_bwd (i: fin n) : Lemma (f (bwd i) == i)
      = inverse_fn_spec f f_inj i in
    let bwd_fwd (i: fin n) : Lemma (bwd (f i) == i)
      = inverse_fn_spec f f_inj (f i)
    in
    { fwd = f; bwd = bwd; fwd_bwd_id = fwd_bwd; bwd_fwd_id = bwd_fwd }
#pop-options

private let rec is_injective_from (#n: pos) (f: fin_map n n) (k: nat)
  : Tot bool (decreases (n - k))
  = if k >= n then true
    else
      let _ = search_preimage_spec f (f (k <: fin n)) 0 in
      match search_preimage f (f (k <: fin n)) 0 with
      | None -> false
      | Some j -> if (j <: nat) = k then is_injective_from f (Prims.op_Addition k 1)
                  else false

let is_injective_b (#n: pos) (f: fin_map n n) : bool
  = is_injective_from f 0

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let rec is_injective_from_true (#n: pos) (f: fin_map n n) (k: nat)
  : Lemma (requires is_injective_from f k)
          (ensures forall (i: fin n). (i <: nat) >= k ==>
                   search_preimage f (f i) 0 == Some i)
          (decreases (n - k))
  = if k >= n then ()
    else begin
      search_preimage_spec f (f (k <: fin n)) 0;
      is_injective_from_true f (Prims.op_Addition k 1)
    end
#pop-options

let is_injective_true (#n: pos) (f: fin_map n n)
  : Lemma (requires is_injective_b f)
          (ensures forall (i j: fin n). f i == f j ==> i == j)
  = is_injective_from_true f 0

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let rec is_injective_from_false (#n: pos) (f: fin_map n n) (k: nat)
  : Lemma (requires not (is_injective_from f k) /\ k < n)
          (ensures exists (a b: fin n). ~(a == b) /\ f a == f b)
          (decreases (n - k))
  = search_preimage_spec f (f (k <: fin n)) 0;
    match search_preimage f (f (k <: fin n)) 0 with
    | None -> ()
    | Some j ->
        if (j <: nat) = k then begin
          if Prims.op_Addition k 1 >= n then ()
          else is_injective_from_false f (Prims.op_Addition k 1)
        end
        else ()
#pop-options

let is_injective_false (#n: pos) (f: fin_map n n)
  : Lemma (requires not (is_injective_b f) /\ n > 0)
          (ensures exists (a b: fin n). ~(a == b) /\ f a == f b)
  = is_injective_from_false f 0
(* ============================================================ *)
(*  Section E.2: Injective phi → det(phi_matrix) = sign * det b *)
(* ============================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let det_phi_matrix_inj
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (b: square_matrix t n) (phi: fin_map n n)
  (phi_inj: squash (forall (i j: fin n). phi i == phi j ==> i == j))
  : Lemma (det (phi_matrix b phi) =
           (if parity (perm_of_injective_fn phi phi_inj) then det b
            else -(det b)))
  = H.elim_equatable_laws t ();
    let p = perm_of_injective_fn phi phi_inj in
    let m1 = phi_matrix b phi in
    let m2 = permute_rows b p in
    let cell_eq (i j: fin n) : Lemma (m1 i j = m2 i j)
      = assert (m1 i j == b (phi i) j);
        assert (m2 i j == b (p.fwd i) j);
        assert (p.fwd i == phi i);
        reflexivity (b (phi i) j)
    in
    Classical.forall_intro_2 cell_eq;
    det_pointwise_eq #t #cr #n m1 m2;
    det_permute_rows #t #cr #n b p;
    transitivity (det m1) (det m2)
                 (if parity p then det b else -(det b))
#pop-options
(* ============================================================ *)
(*  Section F: sum_list_fubini.                                 *)
(* ============================================================ *)

private let inner_sum_x_branch
  (#a #b #t: Type) {| acg: add_comm_group t |}
  (f: a -> b -> t) (ys: list b) (x: a)
  : t
  = sum_list (L.map (f x) ys)

private let inner_sum_y_branch
  (#a #b #t: Type) {| acg: add_comm_group t |}
  (f: a -> b -> t) (xs: list a) (y: b)
  : t
  = sum_list (L.map (swap_args f y) xs)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec sum_list_zeros
  (#a #t: Type) {| acg: add_comm_group t |}
  (xs: list a)
  : Lemma (ensures sum_list (L.map (const (zero #t)) xs) = zero #t)
          (decreases xs)
  = H.elim_equatable_laws t ();
    match xs with
    | [] -> sum_list_nil #t #acg
    | _ :: rest ->
      let tl = L.map (const (zero #t)) rest in
      sum_list_cons (zero #t) tl;
      sum_list_zeros #a #t #acg rest;
      add_congruence (zero #t) (sum_list tl) (zero #t) (zero #t);
      H.zero_plus_x (zero #t);
      transitivity (zero #t + sum_list tl) (zero #t + zero #t) (zero #t);
      transitivity (sum_list ((zero #t) :: tl)) (zero #t + sum_list tl) (zero #t)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let sum_list_fubini_step
  (#a #b #t: Type) {| acg: add_comm_group t |}
  (f: a -> b -> t) (xs: list a {Cons? xs}) (ys: list b)
  : Lemma
    (requires sum_list (L.map (inner_sum_x_branch f ys) (Cons?.tl xs))
            = sum_list (L.map (inner_sum_y_branch f (Cons?.tl xs)) ys))
    (ensures  sum_list (L.map (inner_sum_x_branch f ys) xs)
            = sum_list (L.map (inner_sum_y_branch f xs) ys))
  = H.elim_equatable_laws t ();
    let x = Cons?.hd xs in
    let xs' = Cons?.tl xs in
    assert (xs == x :: xs');
    let f_x_ys = inner_sum_x_branch f ys x in
    let inner_xs' = sum_list (L.map (inner_sum_x_branch f ys) xs') in
    let inner_xs'_swapped = sum_list (L.map (inner_sum_y_branch f xs') ys) in
    let lhs = sum_list (L.map (inner_sum_x_branch f ys) xs) in
    let rhs = sum_list (L.map (inner_sum_y_branch f xs) ys) in
    sum_list_cons f_x_ys (L.map (inner_sum_x_branch f ys) xs');
    assert (lhs == f_x_ys + inner_xs');
    reflexivity f_x_ys;
    assert (inner_xs' = inner_xs'_swapped);
    add_congruence f_x_ys inner_xs' f_x_ys inner_xs'_swapped;
    assert (lhs = f_x_ys + inner_xs'_swapped);
    let g_x : b -> t = f x in
    let g_xs' : b -> t = inner_sum_y_branch f xs' in
    let map_xy_combined = L.map (pointwise_add g_x g_xs') ys in
    sum_list_map_add g_x g_xs' ys;
    assert (sum_list map_xy_combined = sum_list (L.map g_x ys) + sum_list (L.map g_xs' ys));
    assert (sum_list (L.map g_x ys) == f_x_ys);
    assert (sum_list (L.map g_xs' ys) == inner_xs'_swapped);
    assert (sum_list map_xy_combined = f_x_ys + inner_xs'_swapped);
    symmetry (sum_list map_xy_combined) (f_x_ys + inner_xs'_swapped);
    transitivity lhs (f_x_ys + inner_xs'_swapped) (sum_list map_xy_combined);
    let pw (y: b) : Lemma (L.memP y ys ==>
      pointwise_add g_x g_xs' y = inner_sum_y_branch f xs y)
      = if L.memP y ys then begin
          pointwise_add_unfold g_x g_xs' y;
          assert (inner_sum_y_branch f xs y
                  == sum_list (L.map (swap_args f y) xs));
          assert (L.map (swap_args f y) xs
                  == (swap_args f y x) :: L.map (swap_args f y) xs');
          swap_args_unfold f y x;
          sum_list_cons (swap_args f y x) (L.map (swap_args f y) xs');
          assert (sum_list ((swap_args f y x) :: L.map (swap_args f y) xs')
                  = swap_args f y x + sum_list (L.map (swap_args f y) xs'));
          assert (sum_list (L.map (swap_args f y) xs') == g_xs' y);
          symmetry (inner_sum_y_branch f xs y) (g_x y + g_xs' y)
        end
    in
    Classical.forall_intro pw;
    sum_list_map_congruence
      (pointwise_add g_x g_xs')
      (inner_sum_y_branch f xs)
      ys (fun _ -> ());
    transitivity lhs (sum_list map_xy_combined) rhs
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec sum_list_fubini
  (#a #b #t: Type) {| acg: add_comm_group t |}
  (f: a -> b -> t) (xs: list a) (ys: list b)
  : Lemma
    (ensures sum_list (L.map (inner_sum_x_branch f ys) xs)
           = sum_list (L.map (inner_sum_y_branch f xs) ys))
    (decreases xs)
  = H.elim_equatable_laws t ();
    if Nil? xs then begin
      sum_list_nil #t #acg;
      let aux (y: b) : Lemma (L.memP y ys ==>
        inner_sum_y_branch f xs y = (zero #t))
        = if L.memP y ys then
            sum_list_nil #t #acg
      in
      Classical.forall_intro aux;
      sum_list_map_congruence
        (inner_sum_y_branch f xs)
        (const (zero #t))
        ys (fun _ -> ());
      sum_list_zeros #b #t #acg ys;
      transitivity
        (sum_list (L.map (inner_sum_y_branch f xs) ys))
        (sum_list (L.map (const (zero #t)) ys))
        (zero #t);
      symmetry
        (sum_list (L.map (inner_sum_y_branch f xs) ys))
        (zero #t);
      assert (sum_list (L.map (inner_sum_x_branch f ys) xs) = (zero #t));
      transitivity
        (sum_list (L.map (inner_sum_x_branch f ys) xs))
        (zero #t)
        (sum_list (L.map (inner_sum_y_branch f xs) ys))
    end else begin
      sum_list_fubini #a #b #t #acg f (Cons?.tl xs) ys;
      sum_list_fubini_step #a #b #t #acg f xs ys
    end
#pop-options

(* ============================================================ *)
(*  Section F.2: sum_over_fns_to_pointwise                      *)
(* ============================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let sum_over_fns_to_pointwise
  (#t: Type) {| acg: add_comm_group t |}
  (n m: nat) (f g: fin_map n m -> t)
  : Lemma (requires (forall (phi: fin_map n m). f phi = g phi))
          (ensures sum_over_fns_to n m f = sum_over_fns_to n m g)
  = sum_list_map_congruence f g (all_fns_to n m) (fun _ -> ())
#pop-options
(* ============================================================ *)
(*  Section G: perm_product_expand                              *)
(* ============================================================ *)

let phi_pp_term (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n) : t
  = phi_prod a phi * perm_product (phi_matrix b phi) sigma

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let perm_product_expand
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (perm_product (matrix_mul a b) sigma
           = sum_over_fns_to n n (phi_pp_term a b sigma))
  = H.elim_equatable_laws t ();
    perm_product_to_sum_over_fns a b sigma;
    let pw (phi: fin_map n n)
      : Lemma (phi_outer a b sigma phi = phi_pp_term a b sigma phi)
      = phi_outer_eq_a_prod_perm_product a b sigma phi
    in
    Classical.forall_intro pw;
    sum_over_fns_to_pointwise n n (phi_outer a b sigma) (phi_pp_term a b sigma);
    transitivity
      (perm_product (matrix_mul a b) sigma)
      (sum_over_fns_to n n (phi_outer a b sigma))
      (sum_over_fns_to n n (phi_pp_term a b sigma))
#pop-options

(* ============================================================ *)
(*  Section H: leibniz_expand                                   *)
(* ============================================================ *)

let phi_lt_term (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n) : t
  = phi_prod a phi * leibniz_term (phi_matrix b phi) sigma

let neg_phi_pp_term (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n) : t
  = -(phi_pp_term a b sigma phi)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let leibniz_expand
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (leibniz_term (matrix_mul a b) sigma
           = sum_over_fns_to n n (phi_lt_term a b sigma))
  = H.elim_equatable_laws t ();
    perm_product_expand a b sigma;
    if parity sigma then begin
      let pw (phi: fin_map n n)
        : Lemma (phi_pp_term a b sigma phi = phi_lt_term a b sigma phi)
        = reflexivity (phi_pp_term a b sigma phi)
      in
      Classical.forall_intro pw;
      sum_over_fns_to_pointwise n n (phi_pp_term a b sigma) (phi_lt_term a b sigma);
      transitivity
        (leibniz_term (matrix_mul a b) sigma)
        (sum_over_fns_to n n (phi_pp_term a b sigma))
        (sum_over_fns_to n n (phi_lt_term a b sigma))
    end else begin
      neg_congruence
        (perm_product (matrix_mul a b) sigma)
        (sum_over_fns_to n n (phi_pp_term a b sigma));
      sum_list_map_neg
        (phi_pp_term a b sigma)
        (all_fns_to n n);
      let pw (phi: fin_map n n)
        : Lemma (neg_phi_pp_term a b sigma phi = phi_lt_term a b sigma phi)
        = ring_neg_xy_is_x_times_neg_y (phi_prod a phi) (perm_product (phi_matrix b phi) sigma)
      in
      Classical.forall_intro pw;
      sum_list_map_congruence
        (neg_phi_pp_term a b sigma)
        (phi_lt_term a b sigma)
        (all_fns_to n n) (fun _ -> ());
      let pp_fn = phi_pp_term a b sigma in
      sum_list_map_neg pp_fn (all_fns_to n n);
      (* gives: sum_list (L.map (pointwise_neg pp_fn) xs) = neg (sum_list (L.map pp_fn xs)) *)
      let lambda_eq (phi: fin_map n n)
        : Lemma (pointwise_neg pp_fn phi = neg_phi_pp_term a b sigma phi)
        = pointwise_neg_unfold pp_fn phi;
          reflexivity (neg (pp_fn phi))
      in
      Classical.forall_intro lambda_eq;
      sum_list_map_congruence
        (pointwise_neg pp_fn)
        (neg_phi_pp_term a b sigma)
        (all_fns_to n n) (fun _ -> ());
      symmetry
        (sum_list (L.map (pointwise_neg pp_fn) (all_fns_to n n)))
        (sum_list (L.map (neg_phi_pp_term a b sigma) (all_fns_to n n)));
      transitivity
        (sum_list (L.map (neg_phi_pp_term a b sigma) (all_fns_to n n)))
        (sum_list (L.map (pointwise_neg pp_fn) (all_fns_to n n)))
        (neg (sum_list (L.map pp_fn (all_fns_to n n))));
      assert (sum_list (L.map (neg_phi_pp_term a b sigma) (all_fns_to n n))
              = neg (sum_over_fns_to n n (phi_pp_term a b sigma)));
      symmetry
        (sum_list (L.map (neg_phi_pp_term a b sigma) (all_fns_to n n)))
        (neg (sum_over_fns_to n n (phi_pp_term a b sigma)));
      transitivity
        (neg (sum_over_fns_to n n (phi_pp_term a b sigma)))
        (sum_list (L.map (neg_phi_pp_term a b sigma) (all_fns_to n n)))
        (sum_over_fns_to n n (phi_lt_term a b sigma));
      assert (leibniz_term (matrix_mul a b) sigma
              = neg (sum_over_fns_to n n (phi_pp_term a b sigma)));
      transitivity
        (leibniz_term (matrix_mul a b) sigma)
        (neg (sum_over_fns_to n n (phi_pp_term a b sigma)))
        (sum_over_fns_to n n (phi_lt_term a b sigma))
    end
#pop-options

(* ============================================================ *)
(*  Section I: factor_inner_perm_sum + det_expand               *)
(* ============================================================ *)

let phi_det_term (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n) : t
  = phi_prod a phi * det (phi_matrix b phi)

(* Helper: for fixed phi, summing phi_lt_term over sigma in all_permutations n
   equals phi_det_term. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let factor_inner_perm_sum
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n)
  : Lemma (sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n))
           = phi_det_term a b phi)
  = H.elim_equatable_laws t ();
    let c = phi_prod a phi in
    let lt = leibniz_term (phi_matrix b phi) in
    sum_list_map_mul_left c lt (all_permutations n);
    (* c * sum_list (map lt ps) = sum_list (map (pointwise_mul (const c) lt) ps) *)
    let pw (sigma: permutation n)
      : Lemma (pointwise_mul (const c) lt sigma = swap_args (phi_lt_term a b) phi sigma)
      = pointwise_mul_unfold (const c) lt sigma;
        const_unfold c sigma;
        swap_args_unfold (phi_lt_term a b) phi sigma;
        reflexivity (c * lt sigma)
    in
    Classical.forall_intro pw;
    sum_list_map_congruence
      (pointwise_mul (const c) lt)
      (swap_args (phi_lt_term a b) phi)
      (all_permutations n) (fun _ -> ());
    symmetry
      (sum_list (L.map (pointwise_mul (const c) lt) (all_permutations n)))
      (sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n)));
    symmetry (c * sum_list (L.map lt (all_permutations n)))
             (sum_list (L.map (pointwise_mul (const c) lt) (all_permutations n)));
    transitivity
      (sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n)))
      (sum_list (L.map (pointwise_mul (const c) lt) (all_permutations n)))
      (c * sum_list (L.map lt (all_permutations n)));
    leibniz_term_respects_perm_eq (phi_matrix b phi);
    Classical.forall_intro (all_permutations_count_one n);
    sum_over_perms_via_count_one_list lt (all_permutations n) (fun _ -> ());
    symmetry (sum_over_perms n lt) (sum_list (L.map lt (all_permutations n)));
    reflexivity c;
    mul_congruence c (sum_list (L.map lt (all_permutations n)))
                   c (sum_over_perms n lt);
    transitivity
      (sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n)))
      (c * sum_list (L.map lt (all_permutations n)))
      (c * sum_over_perms n lt);
    det_unfold (phi_matrix b phi);
    H.leibniz_to_eq (det (phi_matrix b phi)) (sum_over_perms n lt);
    symmetry (det (phi_matrix b phi)) (sum_over_perms n lt);
    mul_congruence c (sum_over_perms n lt) c (det (phi_matrix b phi));
    transitivity
      (sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n)))
      (c * sum_over_perms n lt)
      (c * det (phi_matrix b phi))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let det_expand
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n)
  : Lemma (det (matrix_mul a b) = sum_over_fns_to n n (phi_det_term a b))
  = H.elim_equatable_laws t ();
    det_unfold (matrix_mul a b);
    H.leibniz_to_eq (det (matrix_mul a b))
                    (sum_over_perms n (leibniz_term (matrix_mul a b)));
    leibniz_term_respects_perm_eq (matrix_mul a b);
    Classical.forall_intro (all_permutations_count_one n);
    sum_over_perms_via_count_one_list
      (leibniz_term (matrix_mul a b)) (all_permutations n) (fun _ -> ());
    transitivity
      (det (matrix_mul a b))
      (sum_over_perms n (leibniz_term (matrix_mul a b)))
      (sum_list (L.map (leibniz_term (matrix_mul a b)) (all_permutations n)));
    let pw_sigma (sigma: permutation n)
      : Lemma (leibniz_term (matrix_mul a b) sigma
               = inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n) sigma)
      = leibniz_expand a b sigma;
        assert (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n) sigma
                == sum_over_fns_to n n (phi_lt_term a b sigma))
          by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
        H.leibniz_to_eq
          (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n) sigma)
          (sum_over_fns_to n n (phi_lt_term a b sigma));
        symmetry
          (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n) sigma)
          (sum_over_fns_to n n (phi_lt_term a b sigma));
        transitivity
          (leibniz_term (matrix_mul a b) sigma)
          (sum_over_fns_to n n (phi_lt_term a b sigma))
          (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n) sigma)
    in
    Classical.forall_intro pw_sigma;
    sum_list_map_congruence
      (leibniz_term (matrix_mul a b))
      (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n))
      (all_permutations n) (fun _ -> ());
    transitivity
      (det (matrix_mul a b))
      (sum_list (L.map (leibniz_term (matrix_mul a b)) (all_permutations n)))
      (sum_list (L.map (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n))
                       (all_permutations n)));
    sum_list_fubini #(permutation n) #(fin_map n n)
      (phi_lt_term a b) (all_permutations n) (all_fns_to n n);
    transitivity
      (det (matrix_mul a b))
      (sum_list (L.map (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n))
                       (all_permutations n)))
      (sum_list (L.map (inner_sum_y_branch (phi_lt_term a b) (all_permutations n))
                       (all_fns_to n n)));
    let pw_phi (phi: fin_map n n)
      : Lemma (inner_sum_y_branch (phi_lt_term a b) (all_permutations n) phi
               = phi_det_term a b phi)
      = factor_inner_perm_sum a b phi;
        (* factor_inner_perm_sum gives:
           sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n))
             = phi_det_term a b phi.
           inner_sum_y_branch unfolds to the same shape. *)
        reflexivity (inner_sum_y_branch (phi_lt_term a b) (all_permutations n) phi)
    in
    Classical.forall_intro pw_phi;
    sum_list_map_congruence
      (inner_sum_y_branch (phi_lt_term a b) (all_permutations n))
      (phi_det_term a b)
      (all_fns_to n n) (fun _ -> ());
    transitivity
      (det (matrix_mul a b))
      (sum_list (L.map (inner_sum_y_branch (phi_lt_term a b) (all_permutations n))
                       (all_fns_to n n)))
      (sum_over_fns_to n n (phi_det_term a b))
#pop-options

(* ============================================================ *)
(*  Section J: Combinatorial machinery — fin_map <-> permutation. *)
(* ============================================================ *)

private let rec fn_to_eq_from (#n #m: nat) (f g: fin_map n m) (k: nat)
  : Tot bool (decreases (n - k))
  = if k >= n then true
    else if f (k <: fin n) = g (k <: fin n)
         then fn_to_eq_from f g (Prims.op_Addition k 1)
         else false

private let fn_to_eq_b (#n #m: nat) (f g: fin_map n m) : bool = fn_to_eq_from f g 0

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
private let rec fn_to_eq_b_spec (#n #m: nat) (f g: fin_map n m) (k: nat)
  : Lemma (ensures (if fn_to_eq_from f g k
                    then forall (i: fin n). (i <: nat) >= k ==> f i == g i
                    else exists (i: fin n). (i <: nat) >= k /\ ~(f i == g i)))
          (decreases (n - k))
  = if k >= n then ()
    else if f (k <: fin n) = g (k <: fin n)
         then fn_to_eq_b_spec f g (Prims.op_Addition k 1)
         else ()
#pop-options

private let rec fn_eq_count (#n #m: nat) (f: fin_map n m) (xs: list (fin_map n m))
  : Tot nat (decreases xs)
  = match xs with
    | [] -> 0
    | h :: tl -> Prims.op_Addition (if fn_to_eq_b f h then 1 else 0) (fn_eq_count f tl)

private let all_funs (n: pos) : list (fin_map n n) = all_fns_to n n

private let sum_over_funs (#t: Type) {| g: add_comm_group t |} (n: pos)
  (h: fin_map n n -> t) : t
  = sum_over_fns_to n n h

private let rec fn_eq_count_append (#n #m: nat) (f: fin_map n m) (xs ys: list (fin_map n m))
  : Lemma (ensures fn_eq_count f (L.append xs ys) ==
           Prims.op_Addition (fn_eq_count f xs) (fn_eq_count f ys))
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: tl -> fn_eq_count_append f tl ys

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let fn_to_eq_b_extend (#k #m: nat) (f: fin_map (Prims.op_Addition k 1) m)
  (phi: fin_map k m) (j: fin m)
  : Lemma (fn_to_eq_b f (extend_fn #k #m phi j) ==
           (f k = j && fn_to_eq_b (restrict_fn #k #m f) phi))
  = fn_to_eq_b_spec f (extend_fn #k #m phi j) 0;
    fn_to_eq_b_spec (restrict_fn #k #m f) phi 0
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let rec all_fins_from_mem (m: nat) (k: nat{k <= m}) (x: fin m)
  : Lemma (ensures L.mem x (all_fins_from m k) == (x >= k))
          (decreases (Prims.op_Subtraction m k))
  = if k = m then ()
    else all_fins_from_mem m (Prims.op_Addition k 1) x

private let rec all_fins_from_noRepeats (m: nat) (k: nat{k <= m})
  : Lemma (ensures L.noRepeats (all_fins_from m k))
          (decreases (Prims.op_Subtraction m k))
  = if k = m then ()
    else begin
      all_fins_from_noRepeats m (Prims.op_Addition k 1);
      all_fins_from_mem m (Prims.op_Addition k 1) (k <: fin m)
    end
#pop-options

private let all_fins_noRepeats (m: nat) : Lemma (L.noRepeats (all_fins m))
  = all_fins_from_noRepeats m 0

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec fn_eq_count_map_extend (#k #m: nat)
  (f: fin_map (Prims.op_Addition k 1) m) (phi: fin_map k m) (js: list (fin m))
  : Lemma (requires L.noRepeats js)
          (ensures fn_eq_count f
             (L.map (extend_fn #k #m phi) js) ==
           (if fn_to_eq_b (restrict_fn #k #m f) phi
               && L.mem (f k) js
            then 1 else 0))
          (decreases js)
  = match js with
    | [] -> ()
    | j :: rest ->
      fn_to_eq_b_extend f phi j;
      fn_eq_count_map_extend f phi rest
#pop-options

#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
private let all_fns_to_succ_list_cons (#k m: nat)
  (phi: fin_map k m) (tl: list (fin_map k m))
  : Lemma (all_fns_to_succ_list #k m (phi :: tl) ==
           L.append (extend_to_all #k #m phi)
                    (all_fns_to_succ_list #k m tl))
  = ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec fn_eq_count_succ (#k #m: nat)
  (f: fin_map (Prims.op_Addition k 1) m) (xs: list (fin_map k m))
  : Lemma (ensures fn_eq_count f (all_fns_to_succ_list #k m xs) ==
                   fn_eq_count (restrict_fn #k #m f) xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | phi :: tl ->
        all_fns_to_succ_list_cons #k m phi tl;
        fn_eq_count_append f
          (extend_to_all #k #m phi)
          (all_fns_to_succ_list #k m tl);
        all_fins_noRepeats m;
        all_fins_from_mem m 0 (f k);
        fn_eq_count_map_extend f phi (all_fins m);
        fn_eq_count_succ f tl
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let rec all_fns_to_count_one (n m: nat) (f: fin_map n m)
  : Lemma (ensures fn_eq_count f (all_fns_to n m) == 1)
          (decreases n)
  = if n = 0 then
      fn_to_eq_b_spec f (nullary m) 0
    else begin
      let k = Prims.op_Subtraction n 1 in
      all_fns_to_count_one k m (restrict_fn #k #m f);
      all_fns_to_succ_eq k m;
      fn_eq_count_succ f (all_fns_to k m)
    end
#pop-options

private let is_injective_b_of_injective (#n: pos) (phi: fin_map n n)
  : Lemma (requires forall (i j: fin n). phi i == phi j ==> i == j)
          (ensures is_injective_b phi == true)
  = if n = 0 then ()
    else if is_injective_b phi then ()
    else begin is_injective_false phi; assert False end

private let perm_of_inj_fn (#n: pos) (phi: fin_map n n{is_injective_b phi})
  : (q: permutation n{forall (i: fin n). q.fwd i == phi i})
  = is_injective_true phi;
    perm_of_injective_fn phi ()

private let rec perm_list_from_funs (#n: pos) (xs: list (fin_map n n))
  : Tot (list (permutation n)) (decreases xs)
  = match xs with
    | [] -> []
    | phi :: tl ->
      if is_injective_b phi
      then perm_of_inj_fn phi :: perm_list_from_funs tl
      else perm_list_from_funs tl

private let perm_list_from_funs_cons_inj (#n: pos) (phi: fin_map n n)
  (tl: list (fin_map n n))
  : Lemma (requires is_injective_b phi)
          (ensures perm_list_from_funs (phi :: tl) ==
                   perm_of_inj_fn phi :: perm_list_from_funs tl)
  = ()

private let perm_list_from_funs_cons_non (#n: pos) (phi: fin_map n n)
  (tl: list (fin_map n n))
  : Lemma (requires not (is_injective_b phi))
          (ensures perm_list_from_funs (phi :: tl) == perm_list_from_funs tl)
  = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let fn_eq_perm_eq_bridge (#n: pos) (p: permutation n)
  (phi: fin_map n n) (q: permutation n{forall (i: fin n). q.fwd i == phi i})
  : Lemma (fn_to_eq_b p.fwd phi == perm_eq p q)
  = fn_to_eq_b_spec p.fwd phi 0;
    if fn_to_eq_b p.fwd phi then begin
      let aux (i: fin n) : Lemma (p.fwd i == q.fwd i) = () in
      Classical.forall_intro aux;
      perm_eq_intro p q aux
    end
    else if perm_eq p q then begin
      let aux (i: fin n) : Lemma (p.fwd i == phi i) =
        perm_eq_elim p q i in
      Classical.forall_intro aux
    end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
private let fn_eq_implies_injective (#n: pos) (p: permutation n)
  (phi: fin_map n n)
  : Lemma (requires forall (i: fin n). p.fwd i == phi i)
          (ensures forall (i j: fin n). phi i == phi j ==> i == j)
  = let aux (i j: fin n) : Lemma (requires phi i == phi j) (ensures i == j) =
      p.bwd_fwd_id i; p.bwd_fwd_id j
    in
    let aux2 (i j: fin n) : Lemma (phi i == phi j ==> i == j) =
      Classical.move_requires (aux i) j
    in
    Classical.forall_intro_2 aux2
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec perm_count_from_funs (#n: pos) (p: permutation n)
  (xs: list (fin_map n n))
  : Lemma (ensures perm_eq_count p (perm_list_from_funs xs) ==
                   fn_eq_count p.fwd xs)
          (decreases xs)
  = match xs with
    | [] ->
      perm_eq_count_nil p
    | phi :: tl ->
      perm_count_from_funs p tl;
      if is_injective_b phi
      then begin
        let q = perm_of_inj_fn phi in
        perm_list_from_funs_cons_inj phi tl;
        perm_eq_count_cons p q (perm_list_from_funs tl);
        fn_eq_perm_eq_bridge p phi q
      end
      else begin
        perm_list_from_funs_cons_non phi tl;
        fn_to_eq_b_spec p.fwd phi 0;
        if fn_to_eq_b p.fwd phi then begin
          fn_eq_implies_injective p phi;
          is_injective_b_of_injective phi
        end
      end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec sum_filter_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (f: permutation n -> t) (g: fin_map n n -> t) (xs: list (fin_map n n))
  : Lemma
      (requires forall (phi: fin_map n n).
        g phi == (if is_injective_b phi then f (perm_of_inj_fn phi) else zero))
      (ensures sum_list (L.map g xs) = sum_list (L.map f (perm_list_from_funs xs)))
      (decreases xs)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match xs with
    | [] ->
      sum_list_nil #t #(cr.cr_r.r_add);
      reflexivity (zero #t)
    | phi :: tl ->
      sum_filter_eq #t #cr #n f g tl;
      sum_list_cons (g phi) (L.map g tl);
      if is_injective_b phi
      then begin
        perm_list_from_funs_cons_inj phi tl;
        sum_list_cons (f (perm_of_inj_fn phi)) (L.map f (perm_list_from_funs tl));
        reflexivity (g phi);
        add_congruence (g phi) (sum_list (L.map g tl))
                       (g phi) (sum_list (L.map f (perm_list_from_funs tl)))
      end
      else begin
        perm_list_from_funs_cons_non phi tl;
        let s = sum_list (L.map g tl) in
        add_zero s;
        transitivity (g phi + s) (zero + s) s;
        transitivity (g phi + s) s (sum_list (L.map f (perm_list_from_funs tl)))
      end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let sum_funs_eq_perms
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (f: permutation n -> t) (g: fin_map n n -> t)
  : Lemma
      (requires respects_perm_eq #t f /\
               (forall (phi: fin_map n n).
                 g phi == (if is_injective_b phi then f (perm_of_inj_fn phi) else zero)))
      (ensures sum_over_funs n g = sum_over_perms n f)
  = let perm_list = perm_list_from_funs (all_funs n) in
    sum_filter_eq #t #cr #n f g (all_funs n);
    let count_one (p: permutation n) : Lemma (perm_eq_count p perm_list == 1)
      = perm_count_from_funs p (all_funs n);
        all_fns_to_count_one n n p.fwd
    in
    Classical.forall_intro count_one;
    sum_over_perms_via_count_one_list #t #(cr.cr_r.r_add) #n f perm_list (fun _ -> ());
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    symmetry (sum_over_perms n f) (sum_list (L.map f perm_list));
    transitivity (sum_over_funs n g) (sum_list (L.map f perm_list)) (sum_over_perms n f)
#pop-options
(* ============================================================ *)
(*  Section K: phi_term split — injective vs non-injective.    *)
(* ============================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let phi_term_non_inj
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n)
  : Lemma (requires is_injective_b phi = false)
          (ensures phi_det_term a b phi = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if n = 0 then
      assert (is_injective_b phi = true)
    else begin
      is_injective_false phi;
      let wit (i j: fin n)
        : Lemma (requires ~(i == j) /\ phi i == phi j)
                (ensures det (phi_matrix b phi) = zero)
        = det_phi_matrix_non_inj b phi i j
      in
      let wit2 (i: fin n) : (j: fin n) -> Lemma ((~(i == j) /\ phi i == phi j) ==> det (phi_matrix b phi) = zero) =
        Classical.move_requires (wit i)
      in
      Classical.forall_intro_2 wit2;
      H.x_mul_zero (phi_prod a phi);
      reflexivity (phi_prod a phi);
      mul_congruence (phi_prod a phi) (det (phi_matrix b phi))
                     (phi_prod a phi) (zero <: t);
      symmetry (phi_prod a phi * zero) (zero <: t);
      transitivity (phi_det_term a b phi)
                   (phi_prod a phi * zero)
                   (zero <: t)
    end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let pa_eq_perm_product
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a: square_matrix t n) (phi: fin_map n n)
  : Lemma (requires is_injective_b phi = true)
          (ensures phi_prod a phi = perm_product a (perm_of_inj_fn phi))
  = H.elim_equatable_laws t ();
    is_injective_true phi;
    let p = perm_of_inj_fn phi in
    perm_product_unfold a p;
    let pwd (i: fin n) : Lemma (apply_along a phi i = apply_along a p.fwd i)
      = apply_along_unfold a phi i;
        apply_along_unfold a p.fwd i;
        reflexivity (a i (phi i)) in
    fin_prod_congruence (apply_along a phi) (apply_along a p.fwd) pwd
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let phi_term_inj
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n)
  : Lemma (requires is_injective_b phi = true)
          (ensures phi_det_term a b phi =
                   leibniz_term a (perm_of_inj_fn phi) * det b)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    is_injective_true phi;
    let p = perm_of_inj_fn phi in
    pa_eq_perm_product a phi;
    det_phi_matrix_inj b phi ();
    if parity p then begin
      mul_congruence (phi_prod a phi) (det (phi_matrix b phi))
                     (perm_product a p) (det b)
    end else begin
      mul_congruence (phi_prod a phi) (det (phi_matrix b phi))
                     (perm_product a p) (-(det b));
      ring_neg_xy_is_x_times_neg_y (perm_product a p) (det b);
      symmetry (-(perm_product a p * det b))
               (perm_product a p * (-(det b)));
      transitivity (phi_det_term a b phi)
                   (perm_product a p * (-(det b)))
                   (-(perm_product a p * det b));
      ring_neg_xy_is_neg_x_times_y (perm_product a p) (det b);
      transitivity (phi_det_term a b phi)
                   (-(perm_product a p * det b))
                   ((-(perm_product a p)) * det b)
    end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let phi_term_value
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n)
  : Lemma (phi_det_term a b phi =
           (if is_injective_b phi
            then leibniz_term a (perm_of_inj_fn phi) * det b
            else zero))
  = if is_injective_b phi
    then phi_term_inj a b phi
    else phi_term_non_inj a b phi
#pop-options

(* ============================================================ *)
(*  Section L: det_expand_to_perms                              *)
(* ============================================================ *)

private let lt_det_b
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) : t
  = leibniz_term a sigma * det b

private let lt_det_b_filtered
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n) : t
  = if is_injective_b phi
    then lt_det_b a b (perm_of_inj_fn phi)
    else zero

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let det_expand_to_perms
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n)
  : Lemma (sum_over_fns_to n n (phi_det_term a b)
           = sum_over_perms n (lt_det_b a b))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let f = lt_det_b a b in
    let h = lt_det_b_filtered a b in
    let pw (phi: fin_map n n)
      : Lemma (phi_det_term a b phi = h phi)
      = phi_term_value a b phi
    in
    Classical.forall_intro pw;
    sum_list_map_congruence
      (phi_det_term a b)
      h (all_fns_to n n) (fun _ -> ());
    leibniz_term_respects_perm_eq a;
    let rpe_prod (p q: permutation n)
      : Lemma (requires perm_eq p q)
              (ensures f p = f q)
      = respects_perm_eq_elim (leibniz_term a) p q;
        reflexivity (det b);
        mul_congruence (leibniz_term a p) (det b) (leibniz_term a q) (det b)
    in
    let rpe_prod2 (p: permutation n) : (q: permutation n) -> Lemma (perm_eq p q ==> f p = f q) =
      Classical.move_requires (rpe_prod p)
    in
    Classical.forall_intro_2 rpe_prod2;
    respects_perm_eq_intro f (fun _ _ -> ());
    sum_funs_eq_perms #t #cr #n f h;
    transitivity
      (sum_over_fns_to n n (phi_det_term a b))
      (sum_over_funs n h)
      (sum_over_perms n f)
#pop-options

(* ============================================================ *)
(*  Section M: det_mul — the headline theorem.                  *)
(* ============================================================ *)

private let db_lt_a
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) : t
  = det b * leibniz_term a sigma

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let det_mul
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n)
  : Lemma (det (matrix_mul a b) = det a * det b)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    det_expand a b;
    det_expand_to_perms a b;
    transitivity (det (matrix_mul a b))
                 (sum_over_fns_to n n (phi_det_term a b))
                 (sum_over_perms n (lt_det_b a b));
    let comm_step (sigma: permutation n)
      : Lemma (lt_det_b a b sigma = db_lt_a a b sigma)
      = mul_commutativity #t #cr.cr_r (leibniz_term a sigma) (det b)
    in
    Classical.forall_intro comm_step;
    sum_over_perms_congruence n (lt_det_b a b) (db_lt_a a b) (fun _ -> ());
    transitivity (det (matrix_mul a b))
                 (sum_over_perms n (lt_det_b a b))
                 (sum_over_perms n (db_lt_a a b));
    sum_over_perms_mul_left_named #t #(cr.cr_r) n (det b) (db_lt_a a b) (leibniz_term a) (fun _ -> ());
    transitivity (det (matrix_mul a b))
                 (sum_over_perms n (db_lt_a a b))
                 (det b * sum_over_perms n (leibniz_term a));
    det_unfold a;
    reflexivity (det b);
    mul_congruence (det b) (sum_over_perms n (leibniz_term a))
                   (det b) (det a);
    transitivity (det (matrix_mul a b))
                 (det b * sum_over_perms n (leibniz_term a))
                 (det b * det a);
    mul_commutativity #t #cr.cr_r (det b) (det a);
    transitivity (det (matrix_mul a b))
                 (det b * det a)
                 (det a * det b)
#pop-options
