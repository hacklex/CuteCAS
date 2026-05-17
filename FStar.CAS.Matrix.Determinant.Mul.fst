module FStar.CAS.Matrix.Determinant.Mul
(*
   det(A·B) = det(A) · det(B) for square matrices over a commutative ring.

   Proof method: Cauchy-Binet expansion via multi-distributivity
   (prod_range_of_fin_sum from MultiDistrib), product factoring,
   Fubini swap of sums, and the fn_to / permutation correspondence.

   Author: A. Rozanov (CuteCAS).
*)

open FStar.CAS.Permutation
open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes
open FStar.CAS.FinSum
open FStar.CAS.Permutation.Enum
open FStar.CAS.Permutation.Sum
open FStar.CAS.Matrix
open FStar.CAS.Matrix.Determinant
open FStar.CAS.Matrix.MultiDistrib
open FStar.CAS.Function.Enum

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses

(* ====================================================================== *)
(*  Section 1: four_swap and prod_range_factor                            *)
(*  Π_i (f i · g i) = (Π_i f i) · (Π_i g i)  for a commutative ring.    *)
(* ====================================================================== *)

(* (a·b)·(c·d) = (a·c)·(b·d) in a ring with given commutativity. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let four_swap
  (#t: Type) {| r: ring t |}
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b c d: t)
  : Lemma ((a * b) * (c * d) = (a * c) * (b * d))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    mul_associativity a b (c * d);
    symmetry (a * b * (c * d)) (a * (b * (c * d)));
    mul_associativity b c d;
    symmetry ((b * c) * d) (b * (c * d));
    reflexivity a;
    mul_congruence a (b * (c * d)) a ((b * c) * d);
    mul_comm b c;
    reflexivity d;
    mul_congruence (b * c) d (c * b) d;
    reflexivity a;
    mul_congruence a ((b * c) * d) a ((c * b) * d);
    mul_associativity c b d;
    reflexivity a;
    mul_congruence a ((c * b) * d) a (c * (b * d));
    mul_associativity a c (b * d);
    symmetry ((a * c) * (b * d)) (a * (c * (b * d)));
    transitivity ((a * b) * (c * d)) (a * (b * (c * d))) (a * ((b * c) * d));
    transitivity ((a * b) * (c * d)) (a * ((b * c) * d)) (a * ((c * b) * d));
    transitivity ((a * b) * (c * d)) (a * ((c * b) * d)) (a * (c * (b * d)));
    transitivity ((a * b) * (c * d)) (a * (c * (b * d))) ((a * c) * (b * d))
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec prod_range_factor
  (#t: Type) {| r: ring t |}
  (mul_comm: (a:t -> b:t -> Lemma (a * b = b * a)))
  (f g: nat -> t) (lo hi: nat)
  : Lemma
    (ensures prod_range (fun i -> f i * g i) lo hi
           = prod_range f lo hi * prod_range g lo hi)
    (decreases (if hi > lo then nat_minus hi lo else 0))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if lo >= hi then begin
      prod_range_empty (fun i -> f i * g i) lo hi;
      prod_range_empty f lo hi;
      prod_range_empty g lo hi;
      reflexivity (one #t);
      mul_congruence (prod_range f lo hi) (prod_range g lo hi) (one #t) (one #t);
      left_mul_identity (one #t);
      trans_lemma [ prod_range f lo hi * prod_range g lo hi;
                    one #t * one #t;
                    one #t ];
      reflexivity (prod_range (fun i -> f i * g i) lo hi);
      symmetry (prod_range f lo hi * prod_range g lo hi) (one #t);
      transitivity (prod_range (fun i -> f i * g i) lo hi)
                   (one #t) (prod_range f lo hi * prod_range g lo hi)
    end else begin
      prod_range_unfold_left (fun i -> f i * g i) lo hi;
      prod_range_unfold_left f lo hi;
      prod_range_unfold_left g lo hi;
      prod_range_factor mul_comm f g (nat_succ lo) hi;
      (* IH: prod_range fg (lo+1) hi = prod_range f (lo+1) hi * prod_range g (lo+1) hi *)
      let pf = prod_range f (nat_succ lo) hi in
      let pg = prod_range g (nat_succ lo) hi in
      (* Step 1: congruence with IH *)
      reflexivity (f lo * g lo);
      mul_congruence (f lo * g lo) (prod_range (fun i -> f i * g i) (nat_succ lo) hi)
                     (f lo * g lo) (pf * pg);
      (* Step 2: four_swap *)
      four_swap mul_comm (f lo) (g lo) pf pg;
      (* Chain *)
      trans_lemma [
        (f lo * g lo) * prod_range (fun i -> f i * g i) (nat_succ lo) hi;
        (f lo * g lo) * (pf * pg);
        (f lo * pf) * (g lo * pg)
      ];
      (* Chain from LHS to RHS *)
      reflexivity (prod_range (fun i -> f i * g i) lo hi);
      transitivity (prod_range (fun i -> f i * g i) lo hi)
                   ((f lo * g lo) * prod_range (fun i -> f i * g i) (nat_succ lo) hi)
                   ((f lo * g lo) * (pf * pg));
      transitivity (prod_range (fun i -> f i * g i) lo hi)
                   ((f lo * g lo) * (pf * pg))
                   ((f lo * pf) * (g lo * pg));
      reflexivity (prod_range f lo hi);
      reflexivity (prod_range g lo hi);
      mul_congruence (f lo * pf) (g lo * pg)
                     (prod_range f lo hi) (prod_range g lo hi);
      transitivity (prod_range (fun i -> f i * g i) lo hi)
                   ((f lo * pf) * (g lo * pg))
                   (prod_range f lo hi * prod_range g lo hi)
    end
#pop-options

(* ====================================================================== *)
(*  Section 2: sum_list_fubini                                            *)
(*  Swap nested sum_list (map ...) over two concrete lists.               *)
(* ====================================================================== *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let sum_list_fubini_step
  (#a #b #t: Type) {| acm: add_comm_monoid t |}
  (f: a -> b -> t) (x: a) (xs': list a) (ys: list b)
  : Lemma
    (requires sum_list (L.map (fun (x':a) -> sum_list (L.map (fun (y:b) -> f x' y) ys)) xs')
            = sum_list (L.map (fun (y:b) -> sum_list (L.map (fun (x':a) -> f x' y) xs')) ys))
    (ensures  sum_list (L.map (fun (x0:a) -> sum_list (L.map (fun (y:b) -> f x0 y) ys)) (x :: xs'))
            = sum_list (L.map (fun (y:b) -> sum_list (L.map (fun (x0:a) -> f x0 y) (x :: xs'))) ys))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    reflexivity (sum_list (L.map (fun (y:b) -> f x y) ys));
    add_congruence
      (sum_list (L.map (fun (y:b) -> f x y) ys))
      (sum_list (L.map (fun (x':a) -> sum_list (L.map (fun (y:b) -> f x' y) ys)) xs'))
      (sum_list (L.map (fun (y:b) -> f x y) ys))
      (sum_list (L.map (fun (y:b) -> sum_list (L.map (fun (x':a) -> f x' y) xs')) ys));
    sum_list_map_add (fun (y:b) -> f x y)
                     (fun (y:b) -> sum_list (L.map (fun (x':a) -> f x' y) xs'))
                     ys;
    let pw (y: b) : Lemma (L.memP y ys ==>
      f x y + sum_list (L.map (fun (x':a) -> f x' y) xs')
      = sum_list (L.map (fun (x':a) -> f x' y) (x :: xs')))
      = if L.memP y ys then
          reflexivity (f x y + sum_list (L.map (fun (x':a) -> f x' y) xs'))
    in
    Classical.forall_intro pw;
    sum_list_map_congruence
      (fun (y:b) -> f x y + sum_list (L.map (fun (x':a) -> f x' y) xs'))
      (fun (y:b) -> sum_list (L.map (fun (x':a) -> f x' y) (x :: xs')))
      ys
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec sum_list_fubini
  (#a #b #t: Type) {| acm: add_comm_monoid t |}
  (f: a -> b -> t) (xs: list a) (ys: list b)
  : Lemma
    (ensures sum_list (L.map (fun (x0:a) -> sum_list (L.map (fun (y:b) -> f x0 y) ys)) xs)
           = sum_list (L.map (fun (y:b) -> sum_list (L.map (fun (x0:a) -> f x0 y) xs)) ys))
    (decreases xs)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    match xs with
    | [] ->
      sum_list_nil #t #acm;
      let g_empty : b -> t = fun y -> sum_list (L.map (fun (x0:a) -> f x0 y) []) in
      let aux (y: b) : Lemma (L.memP y ys ==> g_empty y = zero)
        = if L.memP y ys then begin
            sum_list_nil #t #acm;
            reflexivity (sum_list #t #acm [])
          end
      in
      Classical.forall_intro aux;
      sum_list_map_all_zero g_empty ys;
      symmetry (sum_list (L.map g_empty ys)) (zero #t);
      reflexivity (sum_list #t #acm []);
      transitivity (sum_list #t #acm [])
                   (zero #t)
                   (sum_list (L.map g_empty ys));
      (* Bridge: postcondition RHS captures xs, proof uses [].
         Use sum_list_map_congruence to go from [] to xs. *)
      let br (y: b) : Lemma (L.memP y ys ==>
        sum_list (L.map (fun (x0:a) -> f x0 y) [])
        = sum_list (L.map (fun (x0:a) -> f x0 y) xs))
        = if L.memP y ys then
            reflexivity (sum_list (L.map (fun (x0:a) -> f x0 y) []))
      in
      Classical.forall_intro br;
      sum_list_map_congruence g_empty
        (fun (y:b) -> sum_list (L.map (fun (x0:a) -> f x0 y) xs))
        ys
    | x :: xs' ->
      sum_list_fubini #a #b #t #acm f xs' ys;
      sum_list_fubini_step #a #b #t #acm f x xs' ys;
      (* Bridge: postcondition RHS captures xs, step uses (x :: xs').
         Use sum_list_map_congruence to go from (x :: xs') to xs. *)
      let br (y: b) : Lemma (L.memP y ys ==>
        sum_list (L.map (fun (x0:a) -> f x0 y) (x :: xs'))
        = sum_list (L.map (fun (x0:a) -> f x0 y) xs))
        = if L.memP y ys then
            reflexivity (sum_list (L.map (fun (x0:a) -> f x0 y) (x :: xs')))
      in
      Classical.forall_intro br;
      sum_list_map_congruence
        (fun (y:b) -> sum_list (L.map (fun (x0:a) -> f x0 y) (x :: xs')))
        (fun (y:b) -> sum_list (L.map (fun (x0:a) -> f x0 y) xs))
        ys
#pop-options

(* ====================================================================== *)
(*  Section 3: Pigeonhole for fn_endo — injective implies surjective.     *)
(*  Constructive proof that search_preimage always succeeds when f is      *)
(*  injective, via compression of the codomain.                           *)
(* ====================================================================== *)

(* Search for a preimage of target in f, scanning indices [k, n). *)
private let rec search_preimage (#n: nat) (f: fn_endo n) (target: fin n) (k: nat)
  : Tot (option (fin n)) (decreases (if k < n then nat_minus n k else 0))
  = if k >= n then None
    else if f (k <: fin n) = target then Some (k <: fin n)
    else search_preimage f target (nat_succ k)

private let rec search_preimage_spec (#n: nat) (f: fn_endo n) (target: fin n) (k: nat)
  : Lemma (ensures (match search_preimage f target k with
                    | Some j -> f j == target
                    | None -> forall (j: fin n). (j <: nat) >= k ==> ~(f j == target)))
          (decreases (if k < n then nat_minus n k else 0))
  = if k >= n then ()
    else if f (k <: fin n) = target then ()
    else search_preimage_spec f target (nat_succ k)

(* Compress: remove one value from fin n, mapping to fin (n-1). n >= 2 required. *)
private let compress_val (n: nat{n >= 2}) (gap: fin n) (v: fin n) : fin (Prims.op_Subtraction n 1)
  = if (v <: nat) < (gap <: nat) then (v <: nat)
    else if (v <: nat) = (gap <: nat) then 0
    else Prims.op_Subtraction (v <: nat) 1

(* compress_val is injective on fin n \ {gap}. *)
private let compress_val_injective (n: nat{n >= 2}) (gap: fin n) (v1 v2: fin n)
  : Lemma (requires ~(v1 == gap) /\ ~(v2 == gap) /\ compress_val n gap v1 == compress_val n gap v2)
          (ensures v1 == v2)
  = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
private let rec injective_surjective (#n: nat) (f: fn_endo n) (target: fin n)
  : Lemma (requires forall (i j: fin n). f i == f j ==> i == j)
          (ensures Some? (search_preimage f target 0))
          (decreases n)
  = if n = 0 then ()
    else if n = 1 then
      (* Only one element: f 0 must equal target = 0 *)
      search_preimage_spec f target 0
    else begin
      search_preimage_spec f target 0;
      if Some? (search_preimage f target 0) then ()
      else begin
        let n1 : nat = Prims.op_Subtraction n 1 in
        let last : fin n = n1 in
        let g : fn_endo n1 = fun (i: fin n1) -> compress_val n target (f (i <: fin n)) in
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

(* Build the inverse of an injective fn_endo using search_preimage. *)
private let inverse_fn (#n: nat) (f: fn_endo n)
  (f_inj: squash (forall (i j: fin n). f i == f j ==> i == j))
  (target: fin n) : fin n
  = injective_surjective f target;
    search_preimage_spec f target 0;
    Some?.v (search_preimage f target 0)

private let inverse_fn_spec (#n: nat) (f: fn_endo n)
  (f_inj: squash (forall (i j: fin n). f i == f j ==> i == j))
  (target: fin n) : Lemma (f (inverse_fn f f_inj target) == target)
  = injective_surjective f target;
    search_preimage_spec f target 0

(* Construct a permutation from an injective fn_endo. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
private let perm_of_injective_fn (#n: nat) (f: fn_endo n)
  (f_inj: squash (forall (i j: fin n). f i == f j ==> i == j))
  : (p: permutation n { forall (i: fin n). p.fwd i == f i })
  = let bwd = inverse_fn f f_inj in
    let fwd_bwd (i: fin n) : Lemma (f (bwd i) == i)
      = inverse_fn_spec f f_inj i in
    let bwd_fwd (i: fin n) : Lemma (bwd (f i) == i)
      = inverse_fn_spec f f_inj (f i)
      (* f(bwd(f(i))) == f(i), so by injectivity bwd(f(i)) == i *)
    in
    { fwd = f; bwd = bwd; fwd_bwd_id = fwd_bwd; bwd_fwd_id = bwd_fwd }
#pop-options

(* ====================================================================== *)
(*  Section 4: Decidable injectivity for fn_endo.                         *)
(* ====================================================================== *)

(* For each k, check that the first preimage of f(k) is k itself. *)
private let rec is_injective_from (#n: nat) (f: fn_endo n) (k: nat)
  : Tot bool (decreases nat_minus n k)
  = if k >= n then true
    else
      let _ = search_preimage_spec f (f (k <: fin n)) 0 in
      match search_preimage f (f (k <: fin n)) 0 with
      | None -> false
      | Some j -> if (j <: nat) = k then is_injective_from f (nat_succ k)
                  else false

private let is_injective_b (#n: nat) (f: fn_endo n) : bool
  = is_injective_from f 0

(* True -> for every i >= k, first preimage of f(i) is i itself. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let rec is_injective_from_true (#n: nat) (f: fn_endo n) (k: nat)
  : Lemma (requires is_injective_from f k)
          (ensures forall (i: fin n). (i <: nat) >= k ==>
                   search_preimage f (f i) 0 == Some i)
          (decreases nat_minus n k)
  = if k >= n then ()
    else begin
      search_preimage_spec f (f (k <: fin n)) 0;
      is_injective_from_true f (nat_succ k)
    end
#pop-options

(* is_injective_b true -> f is injective. *)
private let is_injective_true (#n: nat) (f: fn_endo n)
  : Lemma (requires is_injective_b f)
          (ensures forall (i j: fin n). f i == f j ==> i == j)
  = is_injective_from_true f 0

(* is_injective_b false -> f has a collision. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let rec is_injective_from_false (#n: nat) (f: fn_endo n) (k: nat)
  : Lemma (requires not (is_injective_from f k) /\ k < n)
          (ensures exists (a b: fin n). ~(a == b) /\ f a == f b)
          (decreases nat_minus n k)
  = search_preimage_spec f (f (k <: fin n)) 0;
    match search_preimage f (f (k <: fin n)) 0 with
    | None -> ()
    | Some j ->
        if (j <: nat) = k then begin
          if nat_succ k >= n then ()
          else is_injective_from_false f (nat_succ k)
        end
        else ()
#pop-options

private let is_injective_false (#n: nat) (f: fn_endo n)
  : Lemma (requires not (is_injective_b f) /\ n > 0)
          (ensures exists (a b: fin n). ~(a == b) /\ f a == f b)
  = is_injective_from_false f 0

(* ====================================================================== *)
(*  Section 5: phi_matrix and its determinant in the injective /           *)
(*  non-injective cases.                                                   *)
(* ====================================================================== *)

(* phi_matrix B phi: rows of B reindexed by phi. *)
private let phi_matrix (#t: Type) (#n: nat)
  (b: square_matrix t n) (phi: fn_endo n) : square_matrix t n
  = fun i j -> b (phi i) j

(* If phi has a collision, phi_matrix b phi has two equal rows. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
private let det_phi_matrix_non_inj
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (b: square_matrix t n) (phi: fn_endo n)
  (i j: fin n)
  : Lemma (requires ~(i == j) /\ phi i == phi j)
          (ensures det (phi_matrix b phi) = zero)
  = let r : ring t = cr.ring in
    let m = phi_matrix b phi in
    let aux (k: fin n) : Lemma (m i k = m j k)
      = reflexivity (b (phi i) k)
    in
    Classical.forall_intro aux;
    det_two_equal_rows_cr m i j
#pop-options

(* a = b implies -a = -b. Uses: -x = (-1)*x and mul_congruence. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
private let neg_congruence (#t: Type) {| r: ring t |} (a b: t)
  : Lemma (requires a = b) (ensures (-a) = (-b))
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    ring_neg_x_is_minus_one_times_x a;
    ring_neg_x_is_minus_one_times_x b;
    reflexivity ((-one) <: t);
    mul_congruence (-one) a (-one) b;
    transitivity ((-a) <: t) ((-one) * a) ((-one) * b);
    symmetry ((-one) * b) ((-b) <: t);
    transitivity ((-a) <: t) ((-one) * b) ((-b) <: t)
#pop-options

(* If phi is injective, phi_matrix b phi = permute_rows b (perm_of phi). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let det_phi_matrix_inj
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (b: square_matrix t n) (phi: fn_endo n)
  (phi_inj: squash (forall (i j: fin n). phi i == phi j ==> i == j))
  : Lemma (det (phi_matrix b phi) =
           (if parity (perm_of_injective_fn phi phi_inj) then det b
            else -(det b)))
  = let r : ring t = cr.ring in
    let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    let p = perm_of_injective_fn phi phi_inj in
    let m1 = phi_matrix b phi in
    let m2 = permute_rows b p in
    (* perm_product m1 sigma == perm_product m2 sigma for every sigma. *)
    let perm_prod_eq (sigma: permutation n)
      : Lemma (perm_product m1 sigma = perm_product m2 sigma)
      = let f1 (k: nat) = if k < n then m1 (k <: fin n) (sigma.fwd (k <: fin n)) else one in
        let f2 (k: nat) = if k < n then m2 (k <: fin n) (sigma.fwd (k <: fin n)) else one in
        let aux (k: nat)
          : Lemma (requires 0 <= k /\ k < n) (ensures f1 k = f2 k)
          = reflexivity (b (phi (k <: fin n)) (sigma.fwd (k <: fin n)))
        in
        Classical.forall_intro (Classical.move_requires aux);
        prod_range_congruence f1 f2 0 n
    in
    Classical.forall_intro perm_prod_eq;
    (* leibniz_term m1 sigma = leibniz_term m2 sigma for every sigma. *)
    let leib_eq (sigma: permutation n)
      : Lemma (leibniz_term m1 sigma = leibniz_term m2 sigma)
      = perm_prod_eq sigma;
        if parity sigma then ()
        else begin
          neg_congruence (perm_product m1 sigma) (perm_product m2 sigma)
        end
    in
    Classical.forall_intro leib_eq;
    sum_over_perms_congruence n (leibniz_term m1) (leibniz_term m2);
    det_permute_rows b p;
    transitivity (det m1) (det m2)
                 (if parity p then det b else -(det b))
#pop-options

(* ====================================================================== *)
(*  Section 6: fn_to / permutation sum correspondence.                     *)
(*  sum_over_funs n g = sum_over_perms n f  when                           *)
(*  g(phi) = if is_inj(phi) then f(perm_of phi) else zero.               *)
(* ====================================================================== *)

(* If phi is injective, is_injective_b phi must be true. *)
private let is_injective_b_of_injective (#n: nat) (phi: fn_endo n)
  : Lemma (requires forall (i j: fin n). phi i == phi j ==> i == j)
          (ensures is_injective_b phi == true)
  = if n = 0 then ()
    else if is_injective_b phi then ()
    else begin is_injective_false phi; assert False end

(* Filter injective fn_endos, converting each to a permutation. *)
private let perm_of_inj_fn (#n: nat) (phi: fn_endo n{is_injective_b phi})
  : (q: permutation n{forall (i: fin n). q.fwd i == phi i})
  = is_injective_true phi;
    perm_of_injective_fn phi ()

private let rec perm_list_from_funs (#n: nat) (xs: list (fn_endo n))
  : Tot (list (permutation n)) (decreases xs)
  = match xs with
    | [] -> []
    | phi :: tl ->
      if is_injective_b phi
      then perm_of_inj_fn phi :: perm_list_from_funs tl
      else perm_list_from_funs tl

(* Unfold lemmas for perm_list_from_funs. *)
private let perm_list_from_funs_nil (#n: nat)
  : Lemma (perm_list_from_funs #n [] == []) = ()

private let perm_list_from_funs_cons_inj (#n: nat) (phi: fn_endo n)
  (tl: list (fn_endo n))
  : Lemma (requires is_injective_b phi)
          (ensures perm_list_from_funs (phi :: tl) ==
                   perm_of_inj_fn phi :: perm_list_from_funs tl)
  = ()

private let perm_list_from_funs_cons_non (#n: nat) (phi: fn_endo n)
  (tl: list (fn_endo n))
  : Lemma (requires not (is_injective_b phi))
          (ensures perm_list_from_funs (phi :: tl) == perm_list_from_funs tl)
  = ()

(* Bridge: fn_to_eq_b p.fwd phi == perm_eq p q when q.fwd == phi. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let fn_eq_perm_eq_bridge (#n: nat) (p: permutation n)
  (phi: fn_endo n) (q: permutation n{forall (i: fin n). q.fwd i == phi i})
  : Lemma (fn_to_eq_b p.fwd phi == perm_eq p q)
  = fn_to_eq_b_spec p.fwd phi 0;
    if fn_to_eq_b p.fwd phi then begin
      (* fn_to_eq_b_spec gives: forall i. (i:nat) >= 0 ==> p.fwd i == phi i *)
      (* Since q.fwd i == phi i, we need: forall i. p.fwd i == q.fwd i *)
      let aux (i: fin n) : Lemma (p.fwd i == q.fwd i) = () in
      Classical.forall_intro aux;
      perm_eq_intro p q
    end
    else if perm_eq p q then begin
      let aux (i: fin n) : Lemma (p.fwd i == phi i) =
        perm_eq_elim p q i in
      Classical.forall_intro aux
    end
#pop-options

(* If p.fwd agrees with phi pointwise, phi must be injective. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
private let fn_eq_implies_injective (#n: nat) (p: permutation n)
  (phi: fn_endo n)
  : Lemma (requires forall (i: fin n). p.fwd i == phi i)
          (ensures forall (i j: fin n). phi i == phi j ==> i == j)
  = let aux (i j: fin n) : Lemma (requires phi i == phi j) (ensures i == j) =
      p.bwd_fwd_id i; p.bwd_fwd_id j
    in
    Classical.forall_intro_2 (fun i j -> Classical.move_requires (aux i) j)
#pop-options


(* Count bridge: perm_eq_count in perm_list_from_funs == fn_eq_count of p.fwd. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec perm_count_from_funs (#n: nat) (p: permutation n)
  (xs: list (fn_endo n))
  : Lemma (ensures perm_eq_count p (perm_list_from_funs xs) ==
                   fn_eq_count p.fwd xs)
          (decreases xs)
  = match xs with
    | [] ->
      perm_list_from_funs_nil #n;
      perm_eq_count_nil p
    | phi :: tl ->
      perm_count_from_funs p tl;
      if is_injective_b phi
      then begin
        let q = perm_of_inj_fn phi in
        perm_list_from_funs_cons_inj phi tl;
        (* perm_list_from_funs (phi :: tl) == q :: perm_list_from_funs tl *)
        perm_eq_count_cons p q (perm_list_from_funs tl);
        (* perm_eq_count p (q :: ...) == (if perm_eq p q ...) + perm_eq_count p (...) *)
        fn_eq_perm_eq_bridge p phi q
        (* fn_to_eq_b p.fwd phi == perm_eq p q *)
      end
      else begin
        perm_list_from_funs_cons_non phi tl;
        (* perm_list_from_funs (phi :: tl) == perm_list_from_funs tl *)
        (* Need: fn_to_eq_b p.fwd phi == false, else phi would be injective *)
        fn_to_eq_b_spec p.fwd phi 0;
        if fn_to_eq_b p.fwd phi then begin
          fn_eq_implies_injective p phi;
          is_injective_b_of_injective phi
          (* contradiction: is_injective_b phi would be true *)
        end
      end
#pop-options

(* Sum of g over all fn_endos = sum of f over perm_list_from_funs. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec sum_filter_eq
  (#t: Type) {| r: ring t |} (#n: nat)
  (f: permutation n -> t) (g: fn_endo n -> t) (xs: list (fn_endo n))
  : Lemma
      (requires forall (phi: fn_endo n).
        g phi == (if is_injective_b phi then f (perm_of_inj_fn phi) else zero))
      (ensures sum_list (L.map g xs) = sum_list (L.map f (perm_list_from_funs xs)))
      (decreases xs)
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    match xs with
    | [] -> reflexivity (sum_list #t [])
    | phi :: tl ->
      sum_filter_eq #t #r #n f g tl;
      if is_injective_b phi
      then begin
        reflexivity (g phi);
        add_congruence (g phi) (sum_list (L.map g tl))
                       (g phi) (sum_list (L.map f (perm_list_from_funs tl)))
      end
      else begin
        let s = sum_list (L.map g tl) in
        let acm : add_comm_monoid t = TC.solve in
        acm.add_monoid.left_add_identity s;
        transitivity (g phi + s) (zero + s) s;
        transitivity (g phi + s) s (sum_list (L.map f (perm_list_from_funs tl)))
      end
#pop-options

(* Headline: sum_over_funs n g = sum_over_perms n f. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let sum_funs_eq_perms
  (#t: Type) {| r: ring t |} (#n: nat)
  (f: permutation n -> t) (g: fn_endo n -> t)
  : Lemma
      (requires respects_perm_eq #t f /\
               (forall (phi: fn_endo n).
                 g phi == (if is_injective_b phi then f (perm_of_inj_fn phi) else zero)))
      (ensures sum_over_funs n g = sum_over_perms n f)
  = let perm_list = perm_list_from_funs (all_funs n) in
    sum_filter_eq #t #r #n f g (all_funs n);
    let count_one (p: permutation n) : Lemma (perm_eq_count p perm_list == 1)
      = perm_count_from_funs p (all_funs n);
        all_fns_to_count_one n n p.fwd
    in
    Classical.forall_intro count_one;
    sum_over_perms_via_count_one_list f perm_list;
    let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    symmetry (sum_over_perms n f) (sum_list (L.map f perm_list));
    transitivity (sum_over_funs n g) (sum_list (L.map f perm_list)) (sum_over_perms n f)
#pop-options

(* ====================================================================== *)
(*  Section 7: The main equational chain  det(AB) = det(A) · det(B).      *)
(* ====================================================================== *)

(* Product of A-entries along phi: Π_i a(i, phi(i)). *)
private let pa (#t: Type) {| r: ring t |} (#n: nat)
  (a: square_matrix t n) (phi: fn_endo n) : t
  = prod_range (fun (i: nat) ->
      if i < n then a (i <: fin n) (phi (i <: fin n)) else one) 0 n

(* Each summand in multi-distrib factors as pa * perm_product(phi_matrix). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let inner_factor
  (#t: Type) {| r: ring t |} (#n: nat)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b: square_matrix t n) (sigma: permutation n) (phi: fn_endo n)
  : Lemma
    (prod_range (fun (i: nat) ->
       if i < n then
         a (i <: fin n) (phi (i <: fin n)) * b (phi (i <: fin n)) (sigma.fwd (i <: fin n))
       else one) 0 n
     = pa a phi * perm_product (phi_matrix b phi) sigma)
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    let fi (i: nat) : t = if i < n then a (i <: fin n) (phi (i <: fin n)) else one in
    let gi (i: nat) : t = if i < n then b (phi (i <: fin n)) (sigma.fwd (i <: fin n)) else one in
    (* Factor: Π(fi·gi) = (Π fi)·(Π gi). *)
    prod_range_factor mul_comm fi gi 0 n;
    (* Bridge Π gi = perm_product (phi_matrix b phi) sigma. *)
    perm_product_unfold (phi_matrix b phi) sigma;
    let hi (k: nat) : t =
      if k < n then (phi_matrix b phi) (k <: fin n) (sigma.fwd (k <: fin n)) else one in
    let br (k: nat) : Lemma (requires 0 <= k /\ k < n) (ensures gi k = hi k)
      = reflexivity (b (phi (k <: fin n)) (sigma.fwd (k <: fin n)))
    in
    Classical.forall_intro (Classical.move_requires br);
    prod_range_congruence gi hi 0 n;
    reflexivity (pa a phi);
    mul_congruence (pa a phi) (prod_range gi 0 n)
                   (pa a phi) (perm_product (phi_matrix b phi) sigma);
    (* Chain: Π(abk) = Π(fi·gi) = (Π fi)·(Π gi) = pa · perm_product *)
    let abk_exp (i: nat) : t =
      if i < n then
        a (i <: fin n) (phi (i <: fin n)) * b (phi (i <: fin n)) (sigma.fwd (i <: fin n))
      else one in
    let fgi (i: nat) : t = fi i * gi i in
    let br2 (i: nat) : Lemma (requires 0 <= i /\ i < n) (ensures abk_exp i = fgi i)
      = reflexivity (a (i <: fin n) (phi (i <: fin n)) * b (phi (i <: fin n)) (sigma.fwd (i <: fin n)))
    in
    Classical.forall_intro (Classical.move_requires br2);
    prod_range_congruence abk_exp fgi 0 n;
    transitivity (prod_range abk_exp 0 n) (prod_range fgi 0 n) (pa a phi * prod_range gi 0 n);
    transitivity (prod_range abk_exp 0 n) (pa a phi * prod_range gi 0 n)
                 (pa a phi * perm_product (phi_matrix b phi) sigma)
#pop-options

(* Diagnostic tests removed — root cause found: any `semiring t` binding in scope
   changes TC resolution for `one` and `*` in closure lambdas, breaking lambda
   identity across function boundaries. Fix: keep inner_factor calls at top level. *)

(* Top-level relay that calls inner_factor without any semiring in scope. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let inner_factor_relay
  (#t: Type) {| r: ring t |} (#n: nat)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b: square_matrix t n) (sigma: permutation n) (phi: fn_endo n)
  : Lemma
    (prod_range (fun (i: nat) ->
       if i < n then
         a (i <: fin n) (phi (i <: fin n)) * b (phi (i <: fin n)) (sigma.fwd (i <: fin n))
       else one) 0 n
     = pa a phi * perm_product (phi_matrix b phi) sigma)
  = inner_factor mul_comm a b sigma phi
#pop-options

(* Step A: perm_product to sum_over_fns_to via multi-distrib *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let perm_product_to_multidistrib
  (#t: Type) {| r: ring t |} (#n: nat)
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (perm_product (matrix_mul a b) sigma =
           sum_over_fns_to n n
             (fun (phi: fn_to n n) ->
               prod_range (fun (i: nat) ->
                 if i < n then
                   a (i <: fin n) (phi (i <: fin n)) * b (phi (i <: fin n)) (sigma.fwd (i <: fin n))
                 else one) 0 n))
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    let pp_fn (i: nat) : t =
      if i < n then (matrix_mul a b) (i <: fin n) (sigma.fwd (i <: fin n)) else one in
    let md_fn (i: nat) : t =
      if i < n then fin_sum (fun (k: fin n) -> a (i <: fin n) k * b k (sigma.fwd (i <: fin n))) else one in
    let br_pp_md (i: nat) : Lemma (requires 0 <= i /\ i < n) (ensures pp_fn i = md_fn i)
      = matrix_mul_eq_at a b (i <: fin n) (sigma.fwd (i <: fin n));
        reflexivity ((matrix_mul a b) (i <: fin n) (sigma.fwd (i <: fin n)))
    in
    Classical.forall_intro (Classical.move_requires br_pp_md);
    prod_range_congruence pp_fn md_fn 0 n;
    perm_product_unfold (matrix_mul a b) sigma;
    reflexivity (perm_product (matrix_mul a b) sigma);
    prod_range_of_fin_sum n n (fun (i: fin n) (k: fin n) -> a i k * b k (sigma.fwd i));
    trans_lemma [ perm_product (matrix_mul a b) sigma;
                  prod_range pp_fn 0 n;
                  prod_range md_fn 0 n;
                  sum_over_fns_to n n
                    (fun (phi: fn_to n n) ->
                      prod_range (fun (i: nat) ->
                        if i < n then
                          a (i <: fin n) (phi (i <: fin n)) * b (phi (i <: fin n)) (sigma.fwd (i <: fin n))
                        else one) 0 n) ]
#pop-options

(* Step B: factor per-phi prod_range to pa * perm_product *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let sum_fns_to_factor
  (#t: Type) {| r: ring t |} (#n: nat)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (sum_over_fns_to n n
             (fun (phi: fn_to n n) ->
               prod_range (fun (i: nat) ->
                 if i < n then
                   a (i <: fin n) (phi (i <: fin n)) * b (phi (i <: fin n)) (sigma.fwd (i <: fin n))
                 else one) 0 n)
           = sum_over_fns_to n n (fun (phi: fn_to n n) ->
               pa a phi * perm_product (phi_matrix b phi) sigma))
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    let bridge (phi: fn_to n n)
      : Lemma (requires L.memP phi (all_fns_to n n))
              (ensures prod_range (fun (i: nat) ->
                         if i < n then
                           a (i <: fin n) (phi (i <: fin n)) * b (phi (i <: fin n)) (sigma.fwd (i <: fin n))
                         else one) 0 n
                       = pa a phi * perm_product (phi_matrix b phi) sigma)
      = inner_factor_relay mul_comm a b sigma phi
    in
    Classical.forall_intro (Classical.move_requires bridge);
    sum_list_map_congruence
      (fun (phi: fn_to n n) ->
        prod_range (fun (i: nat) ->
          if i < n then
            a (i <: fin n) (phi (i <: fin n)) * b (phi (i <: fin n)) (sigma.fwd (i <: fin n))
          else one) 0 n)
      (fun (phi: fn_to n n) ->
        pa a phi * perm_product (phi_matrix b phi) sigma)
      (all_fns_to n n)
#pop-options

(* Combine steps A and B: perm_product(AB, σ) = Σ_φ pa(φ) · pp(φ_matrix,σ). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let perm_product_expand
  (#t: Type) {| r: ring t |} (#n: nat)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (perm_product (matrix_mul a b) sigma =
           sum_over_fns_to n n (fun (phi: fn_to n n) ->
             pa a phi * perm_product (phi_matrix b phi) sigma))
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    perm_product_to_multidistrib a b sigma;
    sum_fns_to_factor mul_comm a b sigma;
    transitivity (perm_product (matrix_mul a b) sigma)
                 (sum_over_fns_to n n
                    (fun (phi: fn_to n n) ->
                      prod_range (fun (i: nat) ->
                        if i < n then
                          a (i <: fin n) (phi (i <: fin n)) * b (phi (i <: fin n)) (sigma.fwd (i <: fin n))
                        else one) 0 n))
                 (sum_over_fns_to n n (fun (phi: fn_to n n) ->
                   pa a phi * perm_product (phi_matrix b phi) sigma))
#pop-options

(* ====================================================================== *)
(*  Section 7: leibniz_expand — lift to leibniz_term level                *)
(* ====================================================================== *)

(* leibniz_term(AB,σ) = Σ_φ pa(φ) · leibniz_term(φ_matrix b φ, σ). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let leibniz_expand
  (#t: Type) {| r: ring t |} (#n: nat)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (leibniz_term (matrix_mul a b) sigma =
           sum_over_fns_to n n (fun (phi: fn_to n n) ->
             pa a phi * leibniz_term (phi_matrix b phi) sigma))
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    perm_product_expand mul_comm a b sigma;
    if parity sigma then begin
      (* pp == leibniz_term propositionally when parity true *)
      let pw (phi: fn_to n n)
        : Lemma (pa a phi * perm_product (phi_matrix b phi) sigma =
                 pa a phi * leibniz_term (phi_matrix b phi) sigma)
        = reflexivity (pa a phi * perm_product (phi_matrix b phi) sigma)
      in
      Classical.forall_intro pw;
      sum_list_map_congruence
        (fun (phi: fn_to n n) -> pa a phi * perm_product (phi_matrix b phi) sigma)
        (fun (phi: fn_to n n) -> pa a phi * leibniz_term (phi_matrix b phi) sigma)
        (all_fns_to n n)
    end else begin
      (* -(pp(AB)) = -(Σ pa·pp) *)
      neg_congruence
        (perm_product (matrix_mul a b) sigma)
        (sum_over_fns_to n n (fun (phi: fn_to n n) ->
          pa a phi * perm_product (phi_matrix b phi) sigma));
      (* -(Σ f) = Σ(-f) *)
      sum_list_map_neg
        (fun (phi: fn_to n n) -> pa a phi * perm_product (phi_matrix b phi) sigma)
        (all_fns_to n n);
      (* -(pa·pp) = pa·(-pp) == pa·leibniz_term when parity false *)
      let pw (phi: fn_to n n)
        : Lemma (-(pa a phi * perm_product (phi_matrix b phi) sigma) =
                 pa a phi * leibniz_term (phi_matrix b phi) sigma)
        = ring_neg_xy_is_x_times_neg_y (pa a phi) (perm_product (phi_matrix b phi) sigma)
      in
      Classical.forall_intro pw;
      sum_list_map_congruence
        (fun (phi: fn_to n n) -> -(pa a phi * perm_product (phi_matrix b phi) sigma))
        (fun (phi: fn_to n n) -> pa a phi * leibniz_term (phi_matrix b phi) sigma)
        (all_fns_to n n)
    end
#pop-options

(* ====================================================================== *)
(*  Section 8: det_expand — det(AB) = Σ_φ pa(φ) · det(φ_matrix b φ)     *)
(* ====================================================================== *)

(* Sum factoring proved locally to avoid TC diamond issues at module boundaries. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let rec sum_list_factor_ring
  (#t: Type) {| r: ring t |} (#a: Type)
  (c: t) (f: a -> t) (xs: list a)
  : Lemma (ensures sum_list (L.map (fun x -> c * f x) xs) = c * sum_list (L.map f xs))
          (decreases xs)
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    match xs with
    | [] ->
      r.semiring.right_absorption c;
      symmetry (c * zero) (zero <: t)
    | x :: rest ->
      sum_list_factor_ring c f rest;
      (* IH: Σ(c*f, rest) = c * Σ(f, rest) *)
      (* Goal: c*f(x) + Σ(c*f, rest) = c * (f(x) + Σ(f, rest)) *)
      (* Use: c*(a+b) = c*a + c*b [left_distrib] *)
      let a = f x in
      let b = sum_list (L.map f rest) in
      r.semiring.left_distributivity c a b;
      (* c*(a+b) = c*a + c*b *)
      (* IH: Σ(c*f, rest) = c*b *)
      (* So: c*a + Σ(c*f, rest) = c*a + c*b = c*(a+b) *)
      reflexivity (c * a);
      add_congruence (c * a) (sum_list (L.map (fun x -> c * f x) rest))
                     (c * a) (c * b);
      symmetry (c * a + c * b) (c * (a + b))
#pop-options

(* Diagnostic: can we prove det = sum_list in ring equatable? *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let det_as_sum_list_ring
  (#t: Type) {| r: ring t |} (#n: nat) (m: square_matrix t n)
  : Lemma (det m = sum_list (L.map (leibniz_term m) (all_permutations n)))
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    leibniz_term_respects_perm_eq m;
    Classical.forall_intro (all_permutations_count_one n);
    sum_over_perms_via_count_one_list (leibniz_term m) (all_permutations n);
    reflexivity (det m)
#pop-options

(* Relay: a*b = c*d from a=c and b=d, in a small context for TC bridge. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
private let mul_cong_relay (#t: Type) {| r: ring t |} (a b c d: t)
  : Lemma (requires a = c /\ b = d) (ensures a * b = c * d)
  = mul_congruence a b c d
#pop-options

(* Helper: Σ_σ (pa(φ) · lt(φ_mat,σ)) = pa(φ) · det(φ_mat(b,φ)).
   Uses mul_cong_relay to avoid equatable mismatch in large context. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let factor_inner_perm_sum
  (#t: Type) {| r: ring t |} (#n: nat)
  (a b: square_matrix t n) (phi: fn_to n n)
  : Lemma (sum_list (L.map (fun (sigma: permutation n) ->
               pa a phi * leibniz_term (phi_matrix b phi) sigma)
             (all_permutations n))
           = pa a phi * det (phi_matrix b phi))
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    sum_list_factor_ring (pa a phi) (leibniz_term (phi_matrix b phi)) (all_permutations n);
    det_as_sum_list_ring (phi_matrix b phi);
    symmetry (det (phi_matrix b phi))
             (sum_list (L.map (leibniz_term (phi_matrix b phi)) (all_permutations n)));
    reflexivity (pa a phi);
    mul_cong_relay (pa a phi)
                   (sum_list (L.map (leibniz_term (phi_matrix b phi)) (all_permutations n)))
                   (pa a phi)
                   (det (phi_matrix b phi))
#pop-options

(* The main det_expand lemma. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let det_expand
  (#t: Type) {| r: ring t |} (#n: nat)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b: square_matrix t n)
  : Lemma (det (matrix_mul a b) =
           sum_over_fns_to n n (fun (phi: fn_to n n) ->
             pa a phi * det (phi_matrix b phi)))
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    (* Step 1: det(AB) == sum_over_perms n (lt_ab) *)
    det_unfold (matrix_mul a b);
    (* Step 2: bridge sum_over_perms → sum_list *)
    leibniz_term_respects_perm_eq (matrix_mul a b);
    let count_one_aux (p: permutation n)
      : Lemma (perm_eq_count p (all_permutations n) == 1)
      = all_permutations_count_one n p
    in
    Classical.forall_intro count_one_aux;
    sum_over_perms_via_count_one_list
      (leibniz_term (matrix_mul a b)) (all_permutations n);
    (* Step 3: pointwise replace lt_ab sigma with sum_list(map...) *)
    let per_sigma (sigma: permutation n)
      : Lemma (L.memP sigma (all_permutations n) ==>
               leibniz_term (matrix_mul a b) sigma =
               sum_list (L.map (fun (phi: fn_to n n) ->
                  pa a phi * leibniz_term (phi_matrix b phi) sigma)
                 (all_fns_to n n)))
      = if L.memP sigma (all_permutations n) then
          leibniz_expand mul_comm a b sigma
    in
    Classical.forall_intro per_sigma;
    sum_list_map_congruence
      (leibniz_term (matrix_mul a b))
      (fun (sigma: permutation n) ->
        sum_list (L.map (fun (phi: fn_to n n) ->
           pa a phi * leibniz_term (phi_matrix b phi) sigma)
          (all_fns_to n n)))
      (all_permutations n);
    (* Step 4: fubini — swap sums *)
    sum_list_fubini
      (fun (sigma: permutation n) (phi: fn_to n n) ->
         pa a phi * leibniz_term (phi_matrix b phi) sigma)
      (all_permutations n) (all_fns_to n n);
    (* Step 5: factor each inner sum: Σ_σ pa·lt(φ_mat,σ) = pa·det(φ_mat) *)
    let per_phi (phi: fn_to n n)
      : Lemma (L.memP phi (all_fns_to n n) ==>
               sum_list (L.map (fun (sigma: permutation n) ->
                   pa a phi * leibniz_term (phi_matrix b phi) sigma)
                 (all_permutations n))
               = pa a phi * det (phi_matrix b phi))
      = if L.memP phi (all_fns_to n n) then
          factor_inner_perm_sum a b phi
    in
    Classical.forall_intro per_phi;
    sum_list_map_congruence
      (fun (phi: fn_to n n) ->
        sum_list (L.map (fun (sigma: permutation n) ->
            pa a phi * leibniz_term (phi_matrix b phi) sigma)
          (all_permutations n)))
      (fun (phi: fn_to n n) -> pa a phi * det (phi_matrix b phi))
      (all_fns_to n n)
#pop-options

(* ====================================================================== *)
(*  Section 9: Non-inj → 0, inj → leibniz_term · det(b) pointwise       *)
(* ====================================================================== *)

(* Construct commutative_ring from ring + mul_comm for calling lemmas
   that require commutative_ring (e.g. det_two_equal_rows_cr). *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
private let mk_comm_ring (#t: Type) (r: ring t)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  : commutative_ring t
  = let mm = r.semiring.mul_monoid in
    let ms = mm.mul_semigroup in
    let hm = ms.has_mul in
    let mcm : mul_comm_magma t = {
      has_mul = hm;
      mul_commutativity = mul_comm
    } in
    let mcs : mul_comm_semigroup t = {
      mul_semigroup = ms;
      mul_comm_magma = mcm
    } in
    let mcmn : mul_comm_monoid t = {
      mul_monoid = mm;
      mul_comm_semigroup = mcs
    } in
    { ring = r; mul_comm_monoid = mcmn }
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let phi_term_non_inj
  (#t: Type) {| r: ring t |} (#n: nat)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b: square_matrix t n) (phi: fn_to n n)
  : Lemma (requires is_injective_b phi = false)
          (ensures pa a phi * det (phi_matrix b phi) = zero)
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    let cr = mk_comm_ring r mul_comm in
    (* When phi is not injective (and n > 0), get collision witnesses *)
    if n = 0 then begin
      (* n=0: det is one, pa is one, one * one = one. But is_injective_b
         for a fn_endo 0 should be true (vacuously). Contradiction. *)
      assert (is_injective_b phi = true)
    end else begin
      is_injective_false phi;
      (* Now have: exists (i j: fin n). ~(i==j) /\ phi i == phi j *)
      let wit (i j: fin n)
        : Lemma (requires ~(i == j) /\ phi i == phi j)
                (ensures det (phi_matrix b phi) = zero)
        = det_phi_matrix_non_inj #t #cr b phi i j
      in
      Classical.forall_intro_2 (fun i -> Classical.move_requires (wit i));
      (* SMT: exists i j. P i j /\ forall i j. P i j ==> Q ==> Q *)
      assert (det (phi_matrix b phi) = zero);
      right_absorption (pa a phi);
      reflexivity (pa a phi);
      mul_cong_relay (pa a phi) (det (phi_matrix b phi))
                     (pa a phi) (zero <: t);
      symmetry ((pa a phi) * zero) (zero <: t)
    end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let pa_eq_perm_product
  (#t: Type) {| r: ring t |} (#n: nat)
  (a: square_matrix t n) (phi: fn_to n n)
  : Lemma (requires is_injective_b phi = true)
          (ensures pa a phi = perm_product a (perm_of_inj_fn phi))
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    is_injective_true phi;
    let p = perm_of_inj_fn phi in
    perm_product_unfold a p;
    prod_range_congruence
      (fun (i: nat) -> if i < n then a (i <: fin n) (phi (i <: fin n)) else one)
      (fun (i: nat) -> if i < n then a (i <: fin n) (p.fwd (i <: fin n)) else one)
      0 n
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let phi_term_inj
  (#t: Type) {| r: ring t |} (#n: nat)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b: square_matrix t n) (phi: fn_to n n)
  : Lemma (requires is_injective_b phi = true)
          (ensures pa a phi * det (phi_matrix b phi) =
                   leibniz_term a (perm_of_inj_fn phi) * det b)
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    is_injective_true phi;
    let p = perm_of_inj_fn phi in
    pa_eq_perm_product a phi;
    let cr = mk_comm_ring r mul_comm in
    det_phi_matrix_inj #t #cr b phi ();
    if parity p then begin
      mul_cong_relay (pa a phi) (det (phi_matrix b phi))
                     (perm_product a p) (det b)
    end else begin
      mul_cong_relay (pa a phi) (det (phi_matrix b phi))
                     (perm_product a p) (-(det b));
      symmetry (-(perm_product a p * det b))
               (perm_product a p * (-(det b)));
      ring_neg_xy_is_x_times_neg_y (perm_product a p) (det b);
      transitivity (pa a phi * det (phi_matrix b phi))
                   (perm_product a p * (-(det b)))
                   (-(perm_product a p * det b));
      ring_neg_xy_is_neg_x_times_y (perm_product a p) (det b);
      transitivity (pa a phi * det (phi_matrix b phi))
                   (-(perm_product a p * det b))
                   ((-(perm_product a p)) * det b)
    end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let phi_term_value
  (#t: Type) {| r: ring t |} (#n: nat)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b: square_matrix t n) (phi: fn_to n n)
  : Lemma (pa a phi * det (phi_matrix b phi) =
           (if is_injective_b phi
            then leibniz_term a (perm_of_inj_fn phi) * det b
            else zero))
  = if is_injective_b phi
    then phi_term_inj mul_comm a b phi
    else phi_term_non_inj mul_comm a b phi
#pop-options

(* ====================================================================== *)
(*  Section 10: Correspondence — Σ_φ pa·det(φ_mat) = det(a)·det(b)      *)
(* ====================================================================== *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
private let fns_to_eq_funs
  (#t: Type) {| m: add_comm_monoid t |} (#n: nat)
  (f: fn_to n n -> t)
  : Lemma (sum_over_fns_to n n f = sum_over_funs n f)
  = let eq : equatable t = TC.solve in
    reflexivity (sum_list (L.map f (all_fns_to n n)))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let det_expand_to_perms
  (#t: Type) {| r: ring t |} (#n: nat)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b: square_matrix t n)
  : Lemma (sum_over_fns_to n n (fun (phi: fn_to n n) ->
             pa a phi * det (phi_matrix b phi))
           = sum_over_perms n (fun sigma -> leibniz_term a sigma * det b))
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    let f : permutation n -> t = fun sigma -> leibniz_term a sigma * det b in
    let h : fn_to n n -> t =
      fun (phi: fn_to n n) ->
        if is_injective_b phi then f (perm_of_inj_fn phi)
        else zero in
    let pw (phi: fn_to n n)
      : Lemma (L.memP phi (all_fns_to n n) ==>
               pa a phi * det (phi_matrix b phi) = h phi)
      = if L.memP phi (all_fns_to n n) then
          phi_term_value mul_comm a b phi
    in
    Classical.forall_intro pw;
    sum_list_map_congruence
      (fun (phi: fn_to n n) -> pa a phi * det (phi_matrix b phi))
      h (all_fns_to n n);
    fns_to_eq_funs #t h;
    leibniz_term_respects_perm_eq a;
    let rpe_prod (p q: permutation n)
      : Lemma (requires perm_eq p q)
              (ensures f p = f q)
      = respects_perm_eq_elim (leibniz_term a) p q;
        reflexivity (det b);
        mul_cong_relay (leibniz_term a p) (det b) (leibniz_term a q) (det b)
    in
    Classical.forall_intro_2 (fun p -> Classical.move_requires (rpe_prod p));
    respects_perm_eq_intro f;
    sum_funs_eq_perms f h;
    transitivity
      (sum_over_fns_to n n (fun (phi: fn_to n n) -> pa a phi * det (phi_matrix b phi)))
      (sum_over_funs n h)
      (sum_over_perms n f)
#pop-options

(* ====================================================================== *)
(*  Section 11: det_mul — the final theorem                               *)
(* ====================================================================== *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let det_mul
  (#t: Type) {| r: ring t |} (#n: nat)
  (mul_comm: (x:t -> y:t -> Lemma (x * y = y * x)))
  (a b: square_matrix t n)
  : Lemma (det (matrix_mul a b) = det a * det b)
  = let eq : equatable t = TC.solve in
    elim_equatable_laws t #eq;
    transitivity_for_calc_proofs t #eq;
    det_expand mul_comm a b;
    det_expand_to_perms mul_comm a b;
    (* sum_over_perms n (fun sigma -> lt a sigma * det b)
       = sum_over_perms n (fun sigma -> det b * lt a sigma) via comm *)
    let comm_step (sigma: permutation n)
      : Lemma (leibniz_term a sigma * det b = det b * leibniz_term a sigma)
      = mul_comm (leibniz_term a sigma) (det b)
    in
    Classical.forall_intro comm_step;
    sum_over_perms_congruence n
      (fun sigma -> leibniz_term a sigma * det b)
      (fun sigma -> det b * leibniz_term a sigma);
    (* sum_over_perms_mul_left: det b * sum_over_perms n (lt a) =
       sum_over_perms n (fun s -> det b * lt a s) *)
    sum_over_perms_mul_left n (det b) (leibniz_term a);
    symmetry (det b * sum_over_perms n (leibniz_term a))
             (sum_over_perms n (fun s -> det b * leibniz_term a s));
    (* det a == sum_over_perms n (lt a) propositionally, so
       det b * sum_over_perms n (lt a) == det b * det a *)
    det_unfold a;
    reflexivity (det b * det a);
    mul_comm (det b) (det a)
#pop-options