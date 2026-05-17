module FStar.CAS.FinSum

(*
  Finite sums and products over integer ranges and lists — proofs.

  Public interface lives in `FStar.CAS.FinSum.fsti`.

  Author: A. Rozanov (CuteCAS).
*)

module TC = FStar.Tactics.Typeclasses

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes

(* ----------------------------------------------------------------- *)
(*  Sum over an integer range  [lo, hi)                              *)
(* ----------------------------------------------------------------- *)

let sum_range_empty (#t:Type) {| m: add_comm_monoid t |}
                    (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures sum_range f lo hi == zero)
  = ()

let sum_range_unfold_left (#t:Type) {| m: add_comm_monoid t |}
                          (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi == f lo + sum_range f (nat_succ lo) hi)
  = ()

let sum_range_singleton (#t:Type) {| m: add_comm_monoid t |}
                        (f: nat -> t) (k: nat)
  : Lemma (sum_range f k (nat_succ k) = f k)
  = sum_range_unfold_left f k (nat_succ k);
    sum_range_empty f (nat_succ k) (nat_succ k);
    right_add_identity (f k)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec sum_range_congruence
  (#t:Type) {| m: add_comm_monoid t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires (forall (k:nat). lo <= k /\ k < hi ==> f k = g k))
          (ensures sum_range f lo hi = sum_range g lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = if lo >= hi then reflexivity (sum_range f lo hi)
    else begin
      sum_range_congruence f g (nat_succ lo) hi;
      reflexivity (f lo);
      add_congruence (f lo) (sum_range f (nat_succ lo) hi)
                     (g lo) (sum_range g (nat_succ lo) hi)
    end
#pop-options

(* Unfold from the right: sum_range f lo hi = sum_range f lo (hi-1) + f (hi-1). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_range_unfold_right
  (#t:Type) {| m: add_comm_monoid t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi = sum_range f lo (nat_pred hi) + f (nat_pred hi))
          (decreases nat_minus hi lo)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if nat_succ lo = hi then begin
      sum_range_unfold_left f lo hi;
      sum_range_empty f (nat_succ lo) hi;
      right_add_identity (f lo);
      sum_range_empty f lo (nat_pred hi);
      left_add_identity (f (nat_pred hi));
      symmetry (zero + f (nat_pred hi)) (f (nat_pred hi));
      add_congruence (sum_range f lo (nat_pred hi)) (f (nat_pred hi))
                     zero (f (nat_pred hi))
    end else begin
      sum_range_unfold_left f lo hi;
      sum_range_unfold_right f (nat_succ lo) hi;
      reflexivity (f lo);
      add_congruence (f lo) (sum_range f (nat_succ lo) hi)
                     (f lo) (sum_range f (nat_succ lo) (nat_pred hi) + f (nat_pred hi));
      add_associativity (f lo) (sum_range f (nat_succ lo) (nat_pred hi)) (f (nat_pred hi));
      sum_range_unfold_left f lo (nat_pred hi);
      symmetry (sum_range f lo (nat_pred hi))
               (f lo + sum_range f (nat_succ lo) (nat_pred hi));
      reflexivity (f (nat_pred hi));
      add_congruence (f lo + sum_range f (nat_succ lo) (nat_pred hi)) (f (nat_pred hi))
                     (sum_range f lo (nat_pred hi)) (f (nat_pred hi))
    end
#pop-options

(* ----------------------------------------------------------------- *)
(*  Product over an integer range  [lo, hi)                          *)
(* ----------------------------------------------------------------- *)

let prod_range_empty (#t:Type) {| m: mul_monoid t |}
                     (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures prod_range f lo hi == one)
  = ()

let prod_range_unfold_left (#t:Type) {| m: mul_monoid t |}
                           (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi == f lo * prod_range f (nat_succ lo) hi)
  = ()

let prod_range_singleton (#t:Type) {| m: mul_monoid t |}
                         (f: nat -> t) (k: nat)
  : Lemma (prod_range f k (nat_succ k) = f k)
  = prod_range_unfold_left f k (nat_succ k);
    prod_range_empty f (nat_succ k) (nat_succ k);
    right_mul_identity (f k)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec prod_range_congruence
  (#t:Type) {| m: mul_monoid t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires (forall (k:nat). lo <= k /\ k < hi ==> f k = g k))
          (ensures prod_range f lo hi = prod_range g lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = if lo >= hi then reflexivity (prod_range f lo hi)
    else begin
      prod_range_congruence f g (nat_succ lo) hi;
      reflexivity (f lo);
      mul_congruence (f lo) (prod_range f (nat_succ lo) hi)
                     (g lo) (prod_range g (nat_succ lo) hi)
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec prod_range_unfold_right
  (#t:Type) {| m: mul_monoid t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi = prod_range f lo (nat_pred hi) * f (nat_pred hi))
          (decreases nat_minus hi lo)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if nat_succ lo = hi then begin
      prod_range_unfold_left f lo hi;
      prod_range_empty f (nat_succ lo) hi;
      right_mul_identity (f lo);
      prod_range_empty f lo (nat_pred hi);
      left_mul_identity (f (nat_pred hi));
      symmetry (one * f (nat_pred hi)) (f (nat_pred hi));
      mul_congruence (prod_range f lo (nat_pred hi)) (f (nat_pred hi))
                     one (f (nat_pred hi))
    end else begin
      prod_range_unfold_left f lo hi;
      prod_range_unfold_right f (nat_succ lo) hi;
      reflexivity (f lo);
      mul_congruence (f lo) (prod_range f (nat_succ lo) hi)
                     (f lo) (prod_range f (nat_succ lo) (nat_pred hi) * f (nat_pred hi));
      mul_associativity (f lo) (prod_range f (nat_succ lo) (nat_pred hi)) (f (nat_pred hi));
      prod_range_unfold_left f lo (nat_pred hi);
      symmetry (prod_range f lo (nat_pred hi))
               (f lo * prod_range f (nat_succ lo) (nat_pred hi));
      reflexivity (f (nat_pred hi));
      mul_congruence (f lo * prod_range f (nat_succ lo) (nat_pred hi)) (f (nat_pred hi))
                     (prod_range f lo (nat_pred hi)) (f (nat_pred hi))
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec prod_range_split
  (#t:Type) {| m: mul_monoid t |}
  (f: nat -> t) (lo mid hi: nat)
  : Lemma (requires lo <= mid /\ mid <= hi)
          (ensures prod_range f lo hi =
                   prod_range f lo mid * prod_range f mid hi)
          (decreases (if mid > lo then nat_minus mid lo else 0))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if lo = mid then begin
      prod_range_empty f lo mid;
      reflexivity (prod_range f mid hi);
      mul_congruence (prod_range f lo mid) (prod_range f mid hi)
                     (one #t) (prod_range f mid hi);
      left_mul_identity (prod_range f mid hi);
      symmetry (one #t * prod_range f mid hi) (prod_range f mid hi);
      reflexivity (prod_range f lo hi);
      trans_lemma [ prod_range f lo hi;
                    prod_range f mid hi;
                    one #t * prod_range f mid hi;
                    prod_range f lo mid * prod_range f mid hi ]
    end else begin
      prod_range_unfold_left f lo hi;
      prod_range_unfold_left f lo mid;
      prod_range_split f (nat_succ lo) mid hi;
      reflexivity (f lo);
      mul_congruence (f lo) (prod_range f (nat_succ lo) hi)
                     (f lo) (prod_range f (nat_succ lo) mid * prod_range f mid hi);
      mul_associativity (f lo) (prod_range f (nat_succ lo) mid) (prod_range f mid hi);
      reflexivity (prod_range f mid hi);
      mul_congruence (f lo * prod_range f (nat_succ lo) mid) (prod_range f mid hi)
                     (prod_range f lo mid) (prod_range f mid hi);
      trans_lemma [ prod_range f lo hi;
                    f lo * prod_range f (nat_succ lo) hi;
                    f lo * (prod_range f (nat_succ lo) mid * prod_range f mid hi);
                    (f lo * prod_range f (nat_succ lo) mid) * prod_range f mid hi;
                    prod_range f lo mid * prod_range f mid hi ]
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let prod_range_two_step
  (#t:Type) {| m: mul_monoid t |}
  (f: nat -> t) (i: nat)
  : Lemma (prod_range f i (nat_succ (nat_succ i)) = f i * f (nat_succ i))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    prod_range_unfold_left f i (nat_succ (nat_succ i));
    prod_range_singleton f (nat_succ i);
    reflexivity (f i);
    mul_congruence (f i) (prod_range f (nat_succ i) (nat_succ (nat_succ i)))
                   (f i) (f (nat_succ i))
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let prod_range_swap_adjacent
  (#t:Type) {| m: mul_comm_monoid t |}
  (f g: nat -> t) (lo hi: nat) (i: nat)
  : Lemma (requires lo <= i /\ nat_succ i < hi /\
                    g i = f (nat_succ i) /\ g (nat_succ i) = f i /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i /\ k <> nat_succ i ==> g k = f k))
          (ensures prod_range f lo hi = prod_range g lo hi)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    let i2 = nat_succ (nat_succ i) in
    prod_range_split f lo i hi;
    prod_range_split f i i2 hi;
    prod_range_split g lo i hi;
    prod_range_split g i i2 hi;
    let left_cong_aux (k: nat) : Lemma (lo <= k /\ k < i ==> f k = g k)
      = if lo <= k && k < i then begin
          assert (k <> i /\ k <> nat_succ i);
          symmetry (g k) (f k)
        end
    in Classical.forall_intro left_cong_aux;
    prod_range_congruence f g lo i;
    let right_cong_aux (k: nat) : Lemma (i2 <= k /\ k < hi ==> f k = g k)
      = if i2 <= k && k < hi then begin
          assert (k <> i /\ k <> nat_succ i);
          symmetry (g k) (f k)
        end
    in Classical.forall_intro right_cong_aux;
    prod_range_congruence f g i2 hi;
    prod_range_two_step f i;
    prod_range_two_step g i;
    let mcm : mul_comm_magma t = TC.solve in
    mcm.mul_commutativity (f (nat_succ i)) (f i);
    let lp = prod_range f lo i in
    let rp = prod_range f i2 hi in
    let lp_g = prod_range g lo i in
    let rp_g = prod_range g i2 hi in
    reflexivity rp;
    mul_congruence (prod_range f i i2) rp (f i * f (nat_succ i)) rp;
    trans_lemma [ prod_range f i hi;
                  prod_range f i i2 * rp;
                  (f i * f (nat_succ i)) * rp ];
    reflexivity rp_g;
    mul_congruence (prod_range g i i2) rp_g (g i * g (nat_succ i)) rp_g;
    trans_lemma [ prod_range g i hi;
                  prod_range g i i2 * rp_g;
                  (g i * g (nat_succ i)) * rp_g ];
    mul_congruence (g i) (g (nat_succ i)) (f (nat_succ i)) (f i);
    mul_congruence (g i * g (nat_succ i)) rp_g (f (nat_succ i) * f i) rp_g;
    trans_lemma [ prod_range g i hi;
                  (g i * g (nat_succ i)) * rp_g;
                  (f (nat_succ i) * f i) * rp_g ];
    reflexivity lp;
    reflexivity lp_g;
    mul_congruence lp (prod_range f i hi) lp ((f i * f (nat_succ i)) * rp);
    mul_congruence lp_g (prod_range g i hi) lp_g ((f (nat_succ i) * f i) * rp_g);
    assert (f i * f (nat_succ i) = f (nat_succ i) * f i);
    assert (lp = lp_g);
    mul_congruence (f i * f (nat_succ i)) rp (f (nat_succ i) * f i) rp_g;
    mul_congruence lp ((f i * f (nat_succ i)) * rp) lp_g ((f (nat_succ i) * f i) * rp_g);
    trans_lemma [ prod_range f lo hi;
                  lp * prod_range f i hi;
                  lp * ((f i * f (nat_succ i)) * rp);
                  lp_g * ((f (nat_succ i) * f i) * rp_g) ];
    symmetry (prod_range g i hi) ((f (nat_succ i) * f i) * rp_g);
    reflexivity lp_g;
    mul_congruence lp_g ((f (nat_succ i) * f i) * rp_g) lp_g (prod_range g i hi);
    symmetry (prod_range g lo hi) (lp_g * prod_range g i hi);
    trans_lemma [ prod_range f lo hi;
                  lp_g * ((f (nat_succ i) * f i) * rp_g);
                  lp_g * prod_range g i hi;
                  prod_range g lo hi ]
#pop-options

open FStar.CAS.Permutation

#push-options "--fuel 4 --ifuel 2 --z3rlimit 100"
let rec prod_range_perm_invariance
  (#t:Type) {| m: mul_comm_monoid t |}
  (#n: nat) (f: nat -> t) (p: permutation n)
  : Lemma (ensures
            prod_range (fun (k: nat) ->
              if k < n then f (p.fwd (k <: fin n)) else one) 0 n
          = prod_range (fun (k: nat) ->
              if k < n then f k else one) 0 n)
          (decreases inversion_count p)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    let body_p : nat -> t =
      fun (k: nat) -> if k < n then f (p.fwd (k <: fin n)) else one in
    let body_id : nat -> t =
      fun (k: nat) -> if k < n then f k else one in
    perm_descent_exists_or_inv_zero p;
    eliminate (inversion_count p == 0) \/
              (exists (i: nat{i+1 < n}).
                 inversion_count (right_swap p i) < inversion_count p)
    returns prod_range body_p 0 n = prod_range body_id 0 n
    with _.
      begin
        (* Base case: p is extensionally the identity, so body_p ≡ body_id. *)
        let body_eq_aux (k: nat) : Lemma (0 <= k /\ k < n ==> body_p k = body_id k)
          = if 0 <= k && k < n then begin
              inv_zero_implies_identity_fwd p (k <: fin n);
              reflexivity (f k)
            end
        in Classical.forall_intro body_eq_aux;
        prod_range_congruence body_p body_id 0 n
      end
    and _.
      begin
        eliminate exists (i: nat{i+1 < n}).
                    inversion_count (right_swap p i) < inversion_count p
        returns prod_range body_p 0 n = prod_range body_id 0 n
        with _.
          begin
            let q = right_swap p i in
            let body_q : nat -> t =
              fun (k: nat) -> if k < n then f (q.fwd (k <: fin n)) else one in
            (* Swap-adjacent relation: body_p and body_q differ only at i, i+1.
               body_p k = f (p.fwd k); body_q k = f (q.fwd k) = f (p.fwd k')
               where k' is the swap. *)
            let swap_aux_i () : Lemma (body_p i = body_q (nat_succ i))
              = right_swap_fwd_at_k p i (nat_succ i <: fin n);
                reflexivity (f (p.fwd (i <: fin n))) in
            let swap_aux_ip1 () : Lemma (body_p (nat_succ i) = body_q i)
              = right_swap_fwd_at_k p i (i <: fin n);
                reflexivity (f (p.fwd (nat_succ i <: fin n))) in
            let swap_aux_off (k: nat)
              : Lemma (0 <= k /\ k < n /\ k <> i /\ k <> nat_succ i ==> body_q k = body_p k)
              = if 0 <= k && k < n && k <> i && k <> nat_succ i then begin
                  right_swap_fwd_at_k p i (k <: fin n);
                  reflexivity (f (p.fwd (k <: fin n)))
                end
            in
            swap_aux_i ();
            swap_aux_ip1 ();
            Classical.forall_intro swap_aux_off;
            symmetry (body_p i) (body_q (nat_succ i));
            symmetry (body_p (nat_succ i)) (body_q i);
            (* prod_range body_p 0 n = prod_range body_q 0 n via swap. *)
            prod_range_swap_adjacent body_q body_p 0 n i;
            symmetry (prod_range body_q 0 n) (prod_range body_p 0 n);
            (* Recurse on q = right_swap p i: prod_range body_q = prod_range body_id. *)
            prod_range_perm_invariance #t #m #n f q;
            trans_lemma [ prod_range body_p 0 n;
                          prod_range body_q 0 n;
                          prod_range body_id 0 n ]
          end
      end
#pop-options


#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let prod_range_perm_invariance_fn
  (#t:Type) {| m: mul_comm_monoid t |}
  (#n: nat) (f body_p body_id: nat -> t) (p: permutation n)
  : Lemma (requires
            (forall (k: nat). 0 <= k /\ k < n ==> body_p k = f (p.fwd (k <: fin n))) /\
            (forall (k: nat). 0 <= k /\ k < n ==> body_id k = f k))
          (ensures prod_range body_p 0 n = prod_range body_id 0 n)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    prod_range_perm_invariance f p;
    let bp_eq_lp (k: nat) : Lemma
      (requires 0 <= k /\ k < n)
      (ensures body_p k = (if k < n then f (p.fwd (k <: fin n)) else one))
      = reflexivity (f (p.fwd (k <: fin n))) in
    Classical.forall_intro (Classical.move_requires bp_eq_lp);
    prod_range_congruence body_p
      (fun (k: nat) -> if k < n then f (p.fwd (k <: fin n)) else one) 0 n;
    let li_eq_bi (k: nat) : Lemma
      (requires 0 <= k /\ k < n)
      (ensures (if k < n then f k else one) = body_id k)
      = reflexivity (f k) in
    Classical.forall_intro (Classical.move_requires li_eq_bi);
    prod_range_congruence
      (fun (k: nat) -> if k < n then f k else one) body_id 0 n;
    trans_lemma [ prod_range body_p 0 n;
                  prod_range (fun (k: nat) -> if k < n then f (p.fwd (k <: fin n)) else one) 0 n;
                  prod_range (fun (k: nat) -> if k < n then f k else one) 0 n;
                  prod_range body_id 0 n ]
#pop-options

(* ----------------------------------------------------------------- *)
(*  Sum over a list                                                  *)
(*  ----------------------------------------------------------------- *)

open FStar.List.Tot.Base

let sum_list_nil (#t:Type) {| m: add_comm_monoid t |}
  : Lemma (sum_list #t #m [] == zero) = ()

let sum_list_cons (#t:Type) {| m: add_comm_monoid t |} (x: t) (rest: list t)
  : Lemma (sum_list (x :: rest) == x + sum_list rest) = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec sum_list_map_congruence
  (#a:Type) (#t:Type) {| m: add_comm_monoid t |}
  (f g: a -> t) (xs: list a)
  : Lemma (requires (forall (x:a). memP x xs ==> f x = g x))
          (ensures sum_list (map f xs) = sum_list (map g xs))
          (decreases xs)
  = match xs with
    | [] -> reflexivity (sum_list #t #m [])
    | x :: rest ->
      sum_list_map_congruence f g rest;
      add_congruence (f x) (sum_list (map f rest))
                     (g x) (sum_list (map g rest))
#pop-options

(* Negation distributes pointwise over sum_list of a mapped function. *)
private let neg_cong_local (#t:Type) {| g: add_comm_group t |} (a b: t)
  : Lemma (requires a = b) (ensures (-a) = (-b))
  = let ha = g.add_group.add_monoid.has_zero in
    let neg_a : t = -a in
    let neg_b : t = -b in
    ha.eq.reflexivity neg_b;
    add_congruence a neg_b b neg_b;
    g.add_group.negation b;
    ha.eq.transitivity (a + neg_b) (b + neg_b) zero;
    add_commutativity neg_b a;
    ha.eq.transitivity (neg_b + a) (a + neg_b) zero;
    g.add_group.negation a;
    ha.eq.reflexivity neg_a;
    add_congruence neg_b (a + (-a)) neg_b zero;
    ha.eq.symmetry (neg_b + (a + (-a))) (neg_b + zero);
    right_add_identity neg_b;
    ha.eq.symmetry (neg_b + zero) neg_b;
    ha.eq.transitivity neg_b (neg_b + zero) (neg_b + (a + (-a)));
    add_associativity neg_b a (-a);
    ha.eq.symmetry ((neg_b + a) + (-a)) (neg_b + (a + (-a)));
    ha.eq.transitivity neg_b (neg_b + (a + (-a))) ((neg_b + a) + (-a));
    add_congruence (neg_b + a) (-a) zero (-a);
    ha.eq.transitivity neg_b ((neg_b + a) + (-a)) (zero + (-a));
    left_add_identity neg_a;
    ha.eq.transitivity neg_b (zero + neg_a) neg_a;
    ha.eq.symmetry neg_b neg_a

#push-options "--fuel 6 --ifuel 4 --z3rlimit 120"
let rec sum_list_map_neg
  (#a:Type) (#t:Type) {| g: add_comm_group t |}
  (f: a -> t) (xs: list a)
  : Lemma (ensures sum_list (map (fun x -> -(f x)) xs) = -(sum_list (map f xs)))
          (decreases xs)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    match xs with
    | [] ->
      g.add_group.negation (zero #t);
      left_add_identity (-(zero #t));
      symmetry (zero + (-(zero #t))) (-(zero #t));
      transitivity (-(zero #t)) (zero + (-(zero #t))) (zero #t);
      symmetry (-(zero #t)) (zero #t)
    | hx :: rest ->
      sum_list_map_neg #a #t #g f rest;
      assert (sum_list (map (fun x -> -(f x)) rest) = -(sum_list (map f rest)));
      let h = f hx in
      let trest = sum_list (map f rest) in
      let nrest = sum_list (map (fun x -> -(f x)) rest) in
      assert (nrest = (-trest));
      reflexivity (-h);
      add_congruence (-h) nrest (-h) (-trest);
      g.add_comm_monoid.add_comm_semigroup.add_comm_magma.add_commutativity (-h) (-trest);
      neg_of_sum #t #(g.add_group) h trest;
      symmetry (-(h + trest)) ((-trest) + (-h));
      neg_cong_local #t #g (h + trest) (sum_list (map f (hx :: rest)));
      trans_lemma [ sum_list (map (fun x -> -(f x)) (hx :: rest));
                    (-h) + nrest;
                    (-h) + (-trest);
                    (-trest) + (-h);
                    -(h + trest);
                    -(sum_list (map f (hx :: rest))) ]
#pop-options

(* sum_list_map_add: Σ (map (fun x -> f x + g x) xs) = Σ (map f xs) + Σ (map g xs). *)
#push-options "--fuel 6 --ifuel 4 --z3rlimit 80"
let rec sum_list_map_add
  (#a:Type) (#t:Type) {| m: add_comm_monoid t |}
  (f g: a -> t) (xs: list a)
  : Lemma (ensures sum_list (map (fun x -> f x + g x) xs)
                 = sum_list (map f xs) + sum_list (map g xs))
          (decreases xs)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    match xs with
    | [] ->
      (* both sides equal zero. *)
      left_add_identity (zero #t);
      symmetry (zero + zero #t) zero
    | hx :: rest ->
      sum_list_map_add #a #t #m f g rest;
      let a1 = f hx in
      let b1 = g hx in
      let sf = sum_list (map f rest) in
      let sg = sum_list (map g rest) in
      let sh = sum_list (map (fun x -> f x + g x) rest) in
      assert (sh = sf + sg);
      (* head:  (a1 + b1) + sh                                    *)
      (* want:  (a1 + sf) + (b1 + sg)                             *)
      reflexivity (a1 + b1);
      add_congruence (a1 + b1) sh (a1 + b1) (sf + sg);
      (* (a1 + b1) + (sf + sg) = (a1 + sf) + (b1 + sg) by comm/assoc rearrange *)
      let acm = m.add_comm_semigroup.add_comm_magma in
      let asg : add_semigroup t = m.add_monoid.add_semigroup in
      (* Step: ((a1 + b1) + sf) + sg = (a1 + (b1 + sf)) + sg
                                     = (a1 + (sf + b1)) + sg
                                     = ((a1 + sf) + b1) + sg
                                     = (a1 + sf) + (b1 + sg) *)
      asg.associativity a1 b1 sf;
      symmetry ((a1 + b1) + sf) (a1 + (b1 + sf));
      acm.add_commutativity b1 sf;
      add_congruence a1 (b1 + sf) a1 (sf + b1);
      asg.associativity a1 sf b1;
      transitivity (a1 + (b1 + sf)) (a1 + (sf + b1)) ((a1 + sf) + b1);
      transitivity ((a1 + b1) + sf) (a1 + (b1 + sf)) ((a1 + sf) + b1);
      reflexivity sg;
      add_congruence ((a1 + b1) + sf) sg ((a1 + sf) + b1) sg;
      asg.associativity (a1 + b1) sf sg;
      symmetry ((a1 + b1) + sf + sg) ((a1 + b1) + (sf + sg));
      asg.associativity (a1 + sf) b1 sg;
      symmetry ((a1 + sf) + b1 + sg) ((a1 + sf) + (b1 + sg));
      trans_lemma [ (a1 + b1) + sh;
                    (a1 + b1) + (sf + sg);
                    ((a1 + b1) + sf) + sg;
                    ((a1 + sf) + b1) + sg;
                    (a1 + sf) + (b1 + sg) ]
#pop-options

(* ----------------------------------------------------------------- *)
(*  Algebraic identities involving sums                              *)
(*                                                                   *)
(*  Require a ring/semiring structure to talk about scaling sums.    *)
(* ----------------------------------------------------------------- *)

open FStar.CAS.Ringlikes

(* sum_list_map_mul_left: c * Σ (map f xs) = Σ (map (c * f) xs). *)
#push-options "--fuel 6 --ifuel 4 --z3rlimit 80"
let rec sum_list_map_mul_left
  (#a:Type) (#t:Type) {| r: semiring t |}
  (c: t) (f: a -> t) (xs: list a)
  : Lemma (ensures c * sum_list (map f xs) = sum_list (map (fun x -> c * f x) xs))
          (decreases xs)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    match xs with
    | [] ->
      right_absorption c;
      symmetry (c * (zero #t)) (zero #t)
    | hx :: rest ->
      sum_list_map_mul_left #a #t #r c f rest;
      let h = f hx in
      let trest = sum_list (map f rest) in
      let crest = sum_list (map (fun x -> c * f x) rest) in
      assert (c * trest = crest);
      left_distributivity c h trest;
      reflexivity (c * h);
      add_congruence (c * h) (c * trest) (c * h) crest;
      let s_lhs  = c * sum_list (map f (hx :: rest)) in
      let s_mid1 = c * (h + trest) in
      let s_mid2 = c * h + c * trest in
      let s_mid3 = c * h + crest in
      let s_rhs  = sum_list (map (fun x -> c * f x) (hx :: rest)) in
      reflexivity s_lhs;
      reflexivity s_rhs;
      symmetry s_rhs s_mid3;
      trans_lemma [ s_lhs; s_mid1; s_mid2; s_mid3; s_rhs ]
#pop-options

(* sum_range_const_zero: a sum of the zero function is zero. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 30"
let rec sum_range_const_zero
  (#t:Type) {| m: add_comm_monoid t |}
  (lo hi: nat)
  : Lemma (ensures sum_range #t (fun _ -> zero) lo hi = zero)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = if lo >= hi then reflexivity (zero #t)
    else begin
      sum_range_const_zero #t #m (nat_succ lo) hi;
      sum_range_unfold_left #t (fun _ -> zero) lo hi;
      reflexivity (zero #t);
      add_congruence (zero #t) (sum_range #t (fun _ -> zero) (nat_succ lo) hi)
                     (zero #t) (zero #t);
      left_add_identity (zero #t);
      reflexivity (sum_range #t (fun _ -> zero) lo hi);
      trans_lemma [ sum_range #t (fun _ -> zero) lo hi;
                    zero + sum_range #t (fun _ -> zero) (nat_succ lo) hi;
                    zero + zero #t;
                    zero #t ]
    end
#pop-options

(* Sum of left-scaled function: c * Σ f = Σ (c * f). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_range_mul_left
  (#t:Type) {| r: semiring t |}
  (c: t) (f: nat -> t) (lo hi: nat)
  : Lemma (ensures c * sum_range f lo hi = sum_range (fun k -> c * f k) lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if lo >= hi then begin
      sum_range_empty f lo hi;
      sum_range_empty (fun k -> c * f k) lo hi;
      reflexivity c;
      mul_congruence c (sum_range f lo hi) c zero;
      right_absorption c;
      symmetry (sum_range (fun k -> c * f k) lo hi) zero;
      transitivity (c * sum_range f lo hi) (c * zero) zero;
      transitivity (c * sum_range f lo hi) zero (sum_range (fun k -> c * f k) lo hi)
    end else begin
      sum_range_unfold_left f lo hi;
      sum_range_unfold_left (fun k -> c * f k) lo hi;
      (* Step 1: c*sum = c*(f lo + tail) — propositional from unfold_left + reflexivity *)
      let s1 = c * sum_range f lo hi in
      let s2 = c * (f lo + sum_range f (nat_succ lo) hi) in
      reflexivity s1;  (* s1 == s2 by definitional equality of sum_range *)
      (* Step 2: distributivity *)
      left_distributivity c (f lo) (sum_range f (nat_succ lo) hi);
      (* Step 3: inductive hypothesis *)
      sum_range_mul_left c f (nat_succ lo) hi;
      reflexivity (c * f lo);
      add_congruence (c * f lo) (c * sum_range f (nat_succ lo) hi)
                     (c * f lo) (sum_range (fun k -> c * f k) (nat_succ lo) hi);
      (* Step 4: reverse unfold *)
      let s5 = sum_range (fun k -> c * f k) lo hi in
      let s4 = c * f lo + sum_range (fun k -> c * f k) (nat_succ lo) hi in
      reflexivity s5;  (* s5 == s4 by definitional equality *)
      symmetry s5 s4;
      trans_lemma [ s1; s2;
                    c * f lo + c * sum_range f (nat_succ lo) hi;
                    s4; s5 ]
    end
#pop-options

(* Sum of right-scaled function: (Σ f) * c = Σ (f * c). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_range_mul_right
  (#t:Type) {| r: semiring t |}
  (f: nat -> t) (c: t) (lo hi: nat)
  : Lemma (ensures sum_range f lo hi * c = sum_range (fun k -> f k * c) lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if lo >= hi then begin
      sum_range_empty f lo hi;
      sum_range_empty (fun k -> f k * c) lo hi;
      reflexivity c;
      mul_congruence (sum_range f lo hi) c zero c;
      left_absorption c;
      symmetry (sum_range (fun k -> f k * c) lo hi) zero;
      transitivity (sum_range f lo hi * c) (zero * c) zero;
      transitivity (sum_range f lo hi * c) zero (sum_range (fun k -> f k * c) lo hi)
    end else begin
      sum_range_unfold_left f lo hi;
      sum_range_unfold_left (fun k -> f k * c) lo hi;
      let s1 = sum_range f lo hi * c in
      let s2 = (f lo + sum_range f (nat_succ lo) hi) * c in
      reflexivity s1;  (* s1 == s2 by definitional equality *)
      right_distributivity (f lo) (sum_range f (nat_succ lo) hi) c;
      sum_range_mul_right f c (nat_succ lo) hi;
      reflexivity (f lo * c);
      add_congruence (f lo * c) (sum_range f (nat_succ lo) hi * c)
                     (f lo * c) (sum_range (fun k -> f k * c) (nat_succ lo) hi);
      let s5 = sum_range (fun k -> f k * c) lo hi in
      let s4 = f lo * c + sum_range (fun k -> f k * c) (nat_succ lo) hi in
      reflexivity s5;  (* s5 == s4 by definitional equality *)
      symmetry s5 s4;
      trans_lemma [ s1; s2;
                    f lo * c + sum_range f (nat_succ lo) hi * c;
                    s4; s5 ]
    end
#pop-options


(* Sum is additive in the summand: Σ (f + g) = Σ f + Σ g. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_range_add
  (#t:Type) {| m: add_comm_monoid t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (fun k -> f k + g k) lo hi
                  = sum_range f lo hi + sum_range g lo hi)
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if lo >= hi then begin
      sum_range_empty (fun k -> f k + g k) lo hi;
      sum_range_empty f lo hi;
      sum_range_empty g lo hi;
      reflexivity (zero #t);
      add_congruence (sum_range f lo hi) (sum_range g lo hi) zero zero;
      left_add_identity (zero #t);
      symmetry (zero + zero #t) zero;
      trans_lemma [ sum_range (fun k -> f k + g k) lo hi;
                    zero #t;
                    zero + zero #t;
                    sum_range f lo hi + sum_range g lo hi ]
    end else begin
      sum_range_unfold_left (fun k -> f k + g k) lo hi;
      sum_range_unfold_left f lo hi;
      sum_range_unfold_left g lo hi;
      let fl = f lo in let gl = g lo in
      let fa = sum_range f (nat_succ lo) hi in
      let ga = sum_range g (nat_succ lo) hi in
      (* IH *)
      sum_range_add f g (nat_succ lo) hi;
      reflexivity (fl + gl);
      add_congruence (fl + gl) (sum_range (fun k -> f k + g k) (nat_succ lo) hi)
                     (fl + gl) (fa + ga);
      (* Reflexivity bridges definitional equalities to the typeclass `=`. *)
      let head = sum_range (fun k -> f k + g k) lo hi in
      let target = sum_range f lo hi + sum_range g lo hi in
      reflexivity head;       (* head == (fl + gl) + sum_range (fun k -> f k + g k) (succ lo) hi *)
      reflexivity target;     (* target == (fl + fa) + (gl + ga) by definitional unfolding *)
      (* (fl + gl) + (fa + ga) = fl + (gl + (fa + ga))   assoc *)
      add_associativity fl gl (fa + ga);
      (* gl + (fa + ga) = (gl + fa) + ga                 assoc reversed *)
      add_associativity gl fa ga;
      symmetry ((gl + fa) + ga) (gl + (fa + ga));
      (* gl + fa = fa + gl                              comm *)
      add_commutativity gl fa;
      reflexivity ga;
      add_congruence (gl + fa) ga (fa + gl) ga;
      (* (fa + gl) + ga = fa + (gl + ga)                assoc *)
      add_associativity fa gl ga;
      trans_lemma [ gl + (fa + ga);
                    (gl + fa) + ga;
                    (fa + gl) + ga;
                    fa + (gl + ga) ];
      reflexivity fl;
      add_congruence fl (gl + (fa + ga)) fl (fa + (gl + ga));
      (* fl + (fa + (gl + ga)) = (fl + fa) + (gl + ga)  assoc reversed *)
      add_associativity fl fa (gl + ga);
      symmetry ((fl + fa) + (gl + ga)) (fl + (fa + (gl + ga)));
      trans_lemma [ head;
                    (fl + gl) + (fa + ga);
                    fl + (gl + (fa + ga));
                    fl + (fa + (gl + ga));
                    (fl + fa) + (gl + ga) ];
      (* Now bridge (fl + fa) + (gl + ga) = target via reflexivity. *)
      reflexivity ((fl + fa) + (gl + ga));
      transitivity head ((fl + fa) + (gl + ga)) target
    end
#pop-options

(* Double sum swap: Σ_i Σ_j f(i,j) = Σ_j Σ_i f(i,j) over rectangular ranges.

   Strategy: induct on the outer range; use sum_range_add to push the new
   row through the inner sum. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec sum_swap_aux
  (#t:Type) {| m: add_comm_monoid t |}
  (f: nat -> nat -> t)
  (i_lo i_hi j_lo j_hi: nat)
  : Lemma (ensures sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi
                  = sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
          (decreases (if i_hi > i_lo then nat_minus i_hi i_lo else 0))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if i_lo >= i_hi then begin
      (* LHS: empty outer sum = zero. *)
      sum_range_empty #t (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi;
      (* RHS: inner sums are all empty, so RHS = sum of zeros = zero. *)
      let inner_fn (j: nat) : t = sum_range (fun i -> f i j) i_lo i_hi in
      let pf (j: nat) : Lemma (j_lo <= j /\ j < j_hi ==> inner_fn j = zero)
        = if j_lo <= j && j < j_hi then begin
            sum_range_empty #t (fun i -> f i j) i_lo i_hi;
            reflexivity (zero #t)
          end
      in
      Classical.forall_intro pf;
      sum_range_congruence #t inner_fn (fun _ -> zero) j_lo j_hi;
      sum_range_const_zero #t #m j_lo j_hi;
      transitivity (sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
                   (sum_range #t (fun _ -> zero) j_lo j_hi)
                   zero;
      symmetry (sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi) zero;
      transitivity (sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi)
                   zero
                   (sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
    end else begin
      (* Outer step. Outer = f(i_lo) + outer'.  Push f(i_lo) inside. *)
      sum_range_unfold_left #t (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi;
      (* IH on outer' *)
      sum_swap_aux f (nat_succ i_lo) i_hi j_lo j_hi;
      reflexivity (sum_range (f i_lo) j_lo j_hi);
      add_congruence (sum_range (f i_lo) j_lo j_hi)
                     (sum_range (fun i -> sum_range (f i) j_lo j_hi) (nat_succ i_lo) i_hi)
                     (sum_range (f i_lo) j_lo j_hi)
                     (sum_range (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi);
      (* sum_range (f i_lo) j_lo j_hi  +  Σ_j Σ_{i>=i_lo+1} f i j
         = Σ_j ( f i_lo j  +  Σ_{i>=i_lo+1} f i j )   by sum_range_add reversed
         = Σ_j Σ_{i>=i_lo}  f i j                     by unfolding the inner sum
      *)
      sum_range_add #t (f i_lo)
                       (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi)
                       j_lo j_hi;
      symmetry (sum_range (fun j -> f i_lo j + sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi)
               (sum_range (f i_lo) j_lo j_hi
                + sum_range (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi);
      (* Pointwise: f i_lo j + Σ_{i>=i_lo+1} f i j  =  Σ_{i>=i_lo} f i j  (unfold-left). *)
      let lhs_inner (j: nat) : t
        = f i_lo j + sum_range (fun i -> f i j) (nat_succ i_lo) i_hi in
      let rhs_inner (j: nat) : t = sum_range (fun i -> f i j) i_lo i_hi in
      let pf (j: nat) : Lemma (j_lo <= j /\ j < j_hi ==> lhs_inner j = rhs_inner j)
        = if j_lo <= j && j < j_hi then begin
            sum_range_unfold_left #t (fun i -> f i j) i_lo i_hi;
            symmetry (rhs_inner j) (lhs_inner j)
          end
      in
      Classical.forall_intro pf;
      sum_range_congruence #t lhs_inner rhs_inner j_lo j_hi;
      trans_lemma [ sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi;
                    sum_range (f i_lo) j_lo j_hi
                    + sum_range (fun i -> sum_range (f i) j_lo j_hi) (nat_succ i_lo) i_hi;
                    sum_range (f i_lo) j_lo j_hi
                    + sum_range (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi;
                    sum_range lhs_inner j_lo j_hi;
                    sum_range rhs_inner j_lo j_hi ]
    end
#pop-options

let sum_swap
  (#t:Type) {| m: add_comm_monoid t |}
  (f: nat -> nat -> t)
  (i_lo i_hi j_lo j_hi: nat)
  : Lemma (sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi
         = sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
  = sum_swap_aux f i_lo i_hi j_lo j_hi

(* ----------------------------------------------------------------- *)
(*  Sum over `fin n`                                                 *)
(*                                                                   *)
(*  Convenience layer for functions already typed on the refined     *)
(*  index type.  Internally defined via `sum_range` with a guard so  *)
(*  the bridging lemmas reduce to `sum_range_congruence`.            *)
(* ----------------------------------------------------------------- *)

open FStar.CAS.Permutation  // for `fin n`

let fin_sum_congruence
  (#t:Type) {| m: add_comm_monoid t |}
  (#n: nat) (f g: fin n -> t)
  : Lemma (requires (forall (k: fin n). f k = g k))
          (ensures fin_sum f = fin_sum g)
  = sum_range_congruence
      (fun (k: nat) -> if k < n then f (k <: fin n) else zero)
      (fun (k: nat) -> if k < n then g (k <: fin n) else zero)
      0 n

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let fin_sum_mul_left
  (#t:Type) {| r: semiring t |}
  (#n: nat) (c: t) (f: fin n -> t)
  : Lemma (c * fin_sum f = fin_sum (fun (k: fin n) -> c * f k))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    sum_range_mul_left c
      (fun (k: nat) -> if k < n then f (k <: fin n) else zero) 0 n;
    let pf (k: nat) : Lemma (0 <= k /\ k < n ==>
              c * (if k < n then f (k <: fin n) else zero)
              = (if k < n then c * f (k <: fin n) else zero))
      = if 0 <= k && k < n then reflexivity (c * f (k <: fin n))
    in
    Classical.forall_intro pf;
    sum_range_congruence
      (fun (k: nat) -> c * (if k < n then f (k <: fin n) else zero))
      (fun (k: nat) -> if k < n then c * f (k <: fin n) else zero)
      0 n;
    transitivity
      (c * fin_sum f)
      (sum_range (fun (k: nat) -> c * (if k < n then f (k <: fin n) else zero)) 0 n)
      (fin_sum (fun (k: fin n) -> c * f k))
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let fin_sum_mul_right
  (#t:Type) {| r: semiring t |}
  (#n: nat) (f: fin n -> t) (c: t)
  : Lemma (fin_sum f * c = fin_sum (fun (k: fin n) -> f k * c))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    sum_range_mul_right
      (fun (k: nat) -> if k < n then f (k <: fin n) else zero) c 0 n;
    let pf (k: nat) : Lemma (0 <= k /\ k < n ==>
              (if k < n then f (k <: fin n) else zero) * c
              = (if k < n then f (k <: fin n) * c else zero))
      = if 0 <= k && k < n then reflexivity (f (k <: fin n) * c)
    in
    Classical.forall_intro pf;
    sum_range_congruence
      (fun (k: nat) -> (if k < n then f (k <: fin n) else zero) * c)
      (fun (k: nat) -> if k < n then f (k <: fin n) * c else zero)
      0 n;
    transitivity
      (fin_sum f * c)
      (sum_range (fun (k: nat) -> (if k < n then f (k <: fin n) else zero) * c) 0 n)
      (fin_sum (fun (k: fin n) -> f k * c))
#pop-options

(* Sum-swap for `fin n` doubled: Σ_i Σ_j f i j = Σ_j Σ_i f i j. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 200"
let fin_sum_swap
  (#t:Type) {| m: add_comm_monoid t |}
  (#n: nat) (f: fin n -> fin n -> t)
  : Lemma (fin_sum (fun (i: fin n) -> fin_sum (f i))
         = fin_sum (fun (j: fin n) -> fin_sum (fun (i: fin n) -> f i j)))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    let outer_lhs (i: nat) : t
      = if i < n then fin_sum (f (i <: fin n)) else zero in
    let outer_lhs_open (i: nat) : t
      = sum_range (fun (j: nat) -> if i < n && j < n then f (i <: fin n) (j <: fin n) else zero) 0 n in
    let pf1 (i: nat) : Lemma (0 <= i /\ i < n ==> outer_lhs i = outer_lhs_open i)
      = if 0 <= i && i < n then begin
          let inner_a (j: nat) : t = if j < n then f (i <: fin n) (j <: fin n) else zero in
          let inner_b (j: nat) : t = if i < n && j < n then f (i <: fin n) (j <: fin n) else zero in
          let pp (j: nat) : Lemma (0 <= j /\ j < n ==> inner_a j = inner_b j)
            = if 0 <= j && j < n then reflexivity (inner_a j)
          in
          Classical.forall_intro pp;
          sum_range_congruence inner_a inner_b 0 n
        end
    in
    Classical.forall_intro pf1;
    sum_range_congruence outer_lhs outer_lhs_open 0 n;
    let outer_rhs (j: nat) : t
      = if j < n then fin_sum (fun (i: fin n) -> f i (j <: fin n)) else zero in
    let outer_rhs_open (j: nat) : t
      = sum_range (fun (i: nat) -> if i < n && j < n then f (i <: fin n) (j <: fin n) else zero) 0 n in
    let pf2 (j: nat) : Lemma (0 <= j /\ j < n ==> outer_rhs j = outer_rhs_open j)
      = if 0 <= j && j < n then begin
          let inner_a (i: nat) : t = if i < n then f (i <: fin n) (j <: fin n) else zero in
          let inner_b (i: nat) : t = if i < n && j < n then f (i <: fin n) (j <: fin n) else zero in
          let pp (i: nat) : Lemma (0 <= i /\ i < n ==> inner_a i = inner_b i)
            = if 0 <= i && i < n then reflexivity (inner_a i)
          in
          Classical.forall_intro pp;
          sum_range_congruence inner_a inner_b 0 n
        end
    in
    Classical.forall_intro pf2;
    sum_range_congruence outer_rhs outer_rhs_open 0 n;
    (* Apply sum_swap with the unfold-let top-level body so partial applications inline. *)
    sum_swap (fin_swap_body f) 0 n 0 n;
    (* After unfolding `fin_swap_body f i j`, both sides match outer_lhs_open / outer_rhs_open
       definitionally; sum_range_congruence at the outer level can confirm. *)
    let pf3 (i: nat) : Lemma (0 <= i /\ i < n ==>
              sum_range (fin_swap_body f i) 0 n = outer_lhs_open i)
      = if 0 <= i && i < n then reflexivity (sum_range (fin_swap_body f i) 0 n)
    in
    Classical.forall_intro pf3;
    sum_range_congruence
      (fun (i: nat) -> sum_range (fin_swap_body f i) 0 n) outer_lhs_open 0 n;
    let pf4 (j: nat) : Lemma (0 <= j /\ j < n
                          ==> sum_range (fun (i: nat) -> fin_swap_body f i j) 0 n = outer_rhs_open j)
      = if 0 <= j && j < n then
          reflexivity (sum_range (fun (i: nat) -> fin_swap_body f i j) 0 n)
    in
    Classical.forall_intro pf4;
    sum_range_congruence
      (fun (j: nat) -> sum_range (fun (i: nat) -> fin_swap_body f i j) 0 n)
      outer_rhs_open 0 n;
    reflexivity (fin_sum (fun (i: fin n) -> fin_sum (f i)));
    reflexivity (fin_sum (fun (j: fin n) -> fin_sum (fun (i: fin n) -> f i j)));
    symmetry (sum_range (fun (i: nat) -> sum_range (fin_swap_body f i) 0 n) 0 n)
             (sum_range outer_lhs_open 0 n);
    symmetry (sum_range outer_rhs 0 n) (sum_range outer_rhs_open 0 n);
    symmetry (fin_sum (fun (j: fin n) -> fin_sum (fun (i: fin n) -> f i j)))
             (sum_range outer_rhs 0 n);
    transitivity
      (fin_sum (fun (i: fin n) -> fin_sum (f i)))
      (sum_range outer_lhs 0 n)
      (sum_range outer_lhs_open 0 n);
    transitivity
      (fin_sum (fun (i: fin n) -> fin_sum (f i)))
      (sum_range outer_lhs_open 0 n)
      (sum_range (fun (i: nat) -> sum_range (fin_swap_body f i) 0 n) 0 n);
    transitivity
      (fin_sum (fun (i: fin n) -> fin_sum (f i)))
      (sum_range (fun (i: nat) -> sum_range (fin_swap_body f i) 0 n) 0 n)
      (sum_range (fun (j: nat) -> sum_range (fun (i: nat) -> fin_swap_body f i j) 0 n) 0 n);
    transitivity
      (fin_sum (fun (i: fin n) -> fin_sum (f i)))
      (sum_range (fun (j: nat) -> sum_range (fun (i: nat) -> fin_swap_body f i j) 0 n) 0 n)
      (sum_range outer_rhs_open 0 n);
    transitivity
      (fin_sum (fun (i: fin n) -> fin_sum (f i)))
      (sum_range outer_rhs_open 0 n)
      (sum_range outer_rhs 0 n);
    transitivity
      (fin_sum (fun (i: fin n) -> fin_sum (f i)))
      (sum_range outer_rhs 0 n)
      (fin_sum (fun (j: fin n) -> fin_sum (fun (i: fin n) -> f i j)))
#pop-options



(* ----------------------------------------------------------------- *)
(*  Additional helpers needed by the matrix ring + determinant       *)
(* ----------------------------------------------------------------- *)

(* fin_sum of the identically-zero function. *)
let fin_sum_const_zero
  (#t:Type) {| m: add_comm_monoid t |} (#n: nat)
  : Lemma (fin_sum #t #m #n (fun (_: fin n) -> zero #t) = zero #t)
  = elim_equatable_laws t;
    let lhs_open (k: nat) : t
      = if k < n then (fun (_: fin n) -> zero #t) (k <: fin n) else zero in
    let zfn (_: nat) : t = zero in
    let pf (k: nat) : Lemma (0 <= k /\ k < n ==> lhs_open k = zfn k)
      = if k < n then reflexivity (zero #t)
    in
    Classical.forall_intro pf;
    sum_range_congruence lhs_open zfn 0 n;
    sum_range_const_zero #t #m 0 n;
    transitivity
      (fin_sum #t #m #n (fun (_: fin n) -> zero #t))
      (sum_range zfn 0 n)
      (zero #t)

(* Variant: any function pointwise-equal to the zero constant has fin_sum = zero. *)
let fin_sum_zero_ext
  (#t:Type) {| m: add_comm_monoid t |} (#n: nat) (f: fin n -> t)
  : Lemma (requires (forall (k: fin n). f k = zero #t))
          (ensures fin_sum f = zero #t)
  = elim_equatable_laws t;
    let pf (k: fin n) : Lemma (f k = (fun (_: fin n) -> zero #t) k)
      = ()
    in
    Classical.forall_intro pf;
    fin_sum_congruence f (fun (_: fin n) -> zero #t);
    fin_sum_const_zero #t #m #n;
    transitivity (fin_sum f)
                 (fin_sum #t #m #n (fun (_: fin n) -> zero #t))
                 (zero #t)

(* (Semiring-parameterized variant intentionally omitted; the typeclass
   equatable-record paths do not unify across semiring vs add_comm_monoid
   even though their underlying `eq` fields are propositionally equal.
   Callers inline fin_sum_congruence + fin_sum_const_zero instead.) *)

(* fin_sum is additive in the summand. *)
let fin_sum_add
  (#t:Type) {| m: add_comm_monoid t |} (#n: nat) (f g: fin n -> t)
  : Lemma (fin_sum (fun (k: fin n) -> f k + g k)
        = fin_sum f + fin_sum g)
  = elim_equatable_laws t;
    let fopen (k: nat) : t = if k < n then f (k <: fin n) else zero in
    let gopen (k: nat) : t = if k < n then g (k <: fin n) else zero in
    let sopen (k: nat) : t = if k < n then f (k <: fin n) + g (k <: fin n) else zero in
    let addopen (k: nat) : t = fopen k + gopen k in
    let pf (k: nat) : Lemma (0 <= k /\ k < n ==> sopen k = addopen k)
      = if k < n then reflexivity (f (k <: fin n) + g (k <: fin n))
        else begin
          left_add_identity (zero #t);
          symmetry (zero + zero #t) zero
        end
    in
    Classical.forall_intro pf;
    sum_range_congruence sopen addopen 0 n;
    sum_range_add fopen gopen 0 n;
    transitivity
      (fin_sum (fun (k: fin n) -> f k + g k))
      (sum_range addopen 0 n)
      (sum_range fopen 0 n + sum_range gopen 0 n)

(* Variant that takes a third function h with a pointwise-equality hypothesis.
   This dodges the beta-redex matching issue at call sites where users
   write [fin_sum_add (fun k -> ...) (fun k -> ...)] and then want to relate
   the result to [fin_sum (fun k -> ... + ...)] in clean (beta-reduced) form. *)
let fin_sum_add_ext
  (#t:Type) {| m: add_comm_monoid t |} (#n: nat) (f g h: fin n -> t)
  : Lemma (requires (forall (k: fin n). h k = f k + g k))
          (ensures fin_sum h = fin_sum f + fin_sum g)
  = elim_equatable_laws t;
    fin_sum_add f g;
    let pf (k: fin n) : Lemma (h k = (fun (k: fin n) -> f k + g k) k)
      = ()
    in
    Classical.forall_intro pf;
    fin_sum_congruence h (fun (k: fin n) -> f k + g k);
    transitivity (fin_sum h)
                 (fin_sum (fun (k: fin n) -> f k + g k))
                 (fin_sum f + fin_sum g)

(* Kronecker-delta sum lemma over nat range.

   Σ_{k=lo}^{hi-1} (if i0=k then one else zero) * g k
   = g(i0) if lo <= i0 < hi, else zero.
*)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec sum_range_kronecker
  (#t:Type) {| r: semiring t |}
  (i0: nat) (g: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (fun (k:nat) -> (if i0 = k then one else zero #t) * g k) lo hi
                 = (if lo <= i0 && i0 < hi then g i0 else zero #t))
          (decreases (if hi > lo then nat_minus hi lo else 0))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if lo >= hi then begin
      sum_range_empty #t (fun (k:nat) -> (if i0 = k then one else zero #t) * g k) lo hi;
      reflexivity (zero #t)
    end else begin
      sum_range_unfold_left #t (fun (k:nat) -> (if i0 = k then one else zero #t) * g k) lo hi;
      sum_range_kronecker i0 g (nat_succ lo) hi;
      let body : nat -> t
        = fun (k:nat) -> (if i0 = k then one else zero #t) * g k in
      let tail = sum_range body (nat_succ lo) hi in
      let head = body lo in
      let lhs = sum_range body lo hi in
      reflexivity lhs;
      if i0 = lo then begin
        left_mul_identity (g lo);
        right_add_identity (g lo);
        add_congruence head tail (g lo) (zero #t);
        transitivity lhs (head + tail) (g lo + zero);
        transitivity lhs (g lo + zero) (g lo)
      end else begin
        left_absorption (g lo);
        left_add_identity tail;
        add_congruence head tail (zero #t) tail;
        transitivity lhs (head + tail) (zero + tail);
        transitivity lhs (zero + tail) tail
      end
    end
#pop-options

(* The fin_sum version of the Kronecker delta lemma. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let fin_sum_kronecker
  (#t:Type) {| r: semiring t |}
  (#n: nat) (i0: fin n) (g: fin n -> t)
  : Lemma (fin_sum (fun (k: fin n) -> (if (i0 <: nat) = (k <: nat) then one else zero #t) * g k)
        = g i0)
  = elim_equatable_laws t;
    let g_open (k: nat) : t = if k < n then g (k <: fin n) else zero #t in
    let body_open (k: nat) : t
      = if k < n
        then (if (i0 <: nat) = k then one else zero #t) * g (k <: fin n)
        else zero #t in
    let kron_body (k: nat) : t
      = (if (i0 <: nat) = k then one else zero #t) * g_open k in
    let pf (k: nat) : Lemma (0 <= k /\ k < n ==> body_open k = kron_body k)
      = if k < n then reflexivity
            ((if (i0 <: nat) = k then one else zero #t) * g (k <: fin n))
    in
    Classical.forall_intro pf;
    sum_range_congruence body_open kron_body 0 n;
    sum_range_kronecker (i0 <: nat) g_open 0 n;
    assert (sum_range kron_body 0 n = g_open (i0 <: nat));
    assert (g_open (i0 <: nat) == g i0);
    reflexivity (g i0);
    transitivity (sum_range body_open 0 n) (sum_range kron_body 0 n) (g i0);
    reflexivity (fin_sum (fun (k: fin n) ->
       (if (i0 <: nat) = (k <: nat) then one else zero #t) * g k));
    transitivity
      (fin_sum (fun (k: fin n) ->
         (if (i0 <: nat) = (k <: nat) then one else zero #t) * g k))
      (sum_range body_open 0 n)
      (g i0)
#pop-options
