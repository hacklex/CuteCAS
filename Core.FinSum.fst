module Core.FinSum

(*
  Port of FinSum to the new fine-grained TC tower.

  Public interface lives in `Core.FinSum.fsti`.
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Permutation
open Core.Algebra.Helpers
open FStar.List.Tot.Base

(* nat_succ / nat_pred / nat_minus are defined in the fsti. *)

(* ----------------------------------------------------------------- *)
(*  Private helpers                                                  *)
(* ----------------------------------------------------------------- *)

private let rec trans_condition (#t: Type) {| equatable t |}
                                (l: list t{length l > 1}) : bool
  = match l with
    | h1 :: tail ->
      match tail with
      | [h2] -> h1 = h2
      | h2 :: _ -> h1 = h2 && trans_condition tail

private let rec trans_lemma (#t: Type) {| equatable t |}
                            (xs: list t{length xs > 1})
  : Lemma (requires trans_condition xs)
          (ensures hd xs = last xs)
          (decreases xs)
  = match xs with
    | [_; _] -> ()
    | h1 :: h2 :: rest ->
      trans_lemma (h2 :: rest);
      transitivity h1 h2 (last rest)

private let trans2 (#t: Type) {| equatable t |} (a b c: t)
  : Lemma (requires a = b /\ b = c) (ensures a = c)
  = transitivity a b c

private let trans3 (#t: Type) {| equatable t |} (a b c d: t)
  : Lemma (requires a = b /\ b = c /\ c = d) (ensures a = d)
  = transitivity a b c;
    transitivity a c d

private let trans4 (#t: Type) {| equatable t |} (a b c d e: t)
  : Lemma (requires a = b /\ b = c /\ c = d /\ d = e) (ensures a = e)
  = transitivity a b c;
    transitivity a c d;
    transitivity a d e

private let trans5 (#t: Type) {| equatable t |} (a b c d e f: t)
  : Lemma (requires a = b /\ b = c /\ c = d /\ d = e /\ e = f) (ensures a = f)
  = transitivity a b c;
    transitivity a c d;
    transitivity a d e;
    transitivity a e f

private let group_cancel_left (#t: Type) {| g: add_comm_group t |} (a b c: t)
  : Lemma (requires a + b = a + c) (ensures b = c)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    neg_x_plus_x a;
    add_associativity (neg a) a b;
    add_associativity (neg a) a c;
    zero_plus_x b;
    zero_plus_x c;
    reflexivity (neg a);
    add_congruence (neg a) (a + b) (neg a) (a + c);
    add_congruence (neg a + a) b zero b;
    add_congruence (neg a + a) c zero c

(* neg_of_sum now lives in Core.Algebra.Helpers. *)

(* ----------------------------------------------------------------- *)
(*  Sum over an integer range  [lo, hi)                              *)
(* ----------------------------------------------------------------- *)

let rec sum_range (#t:Type) {| m: add_comm_group t |}
                  (f: nat -> t) (lo hi: nat)
  : Tot t
  = if lo >= hi then zero
    else f lo + sum_range f (nat_succ lo) hi

let sum_range_empty (#t:Type) {| m: add_comm_group t |}
                    (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures sum_range f lo hi == zero)
  = ()

let sum_range_unfold_left (#t:Type) {| m: add_comm_group t |}
                          (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi == f lo + sum_range f (nat_succ lo) hi)
  = ()

let sum_range_singleton (#t:Type) {| m: add_comm_group t |}
                        (f: nat -> t) (k: nat)
  : Lemma (sum_range f k (nat_succ k) = f k)
  = sum_range_unfold_left f k (nat_succ k);
    sum_range_empty f (nat_succ k) (nat_succ k);
    x_plus_zero (f k)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec sum_range_congruence_forall
  (#t:Type) {| m: add_comm_group t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires (forall (k:nat). lo <= k /\ k < hi ==> f k = g k))
          (ensures sum_range f lo hi = sum_range g lo hi)
          (decreases (hi - lo))
  = if lo >= hi then reflexivity (sum_range f lo hi)
    else begin
      sum_range_congruence_forall f g (nat_succ lo) hi;
      reflexivity (f lo);
      add_congruence (f lo) (sum_range f (nat_succ lo) hi)
                     (g lo) (sum_range g (nat_succ lo) hi)
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_range_unfold_right
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi = sum_range f lo (nat_pred hi) + f (nat_pred hi))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if nat_succ lo = hi then begin
      sum_range_unfold_left f lo hi;
      sum_range_empty f (nat_succ lo) hi;
      x_plus_zero (f lo);
      sum_range_empty f lo (nat_pred hi);
      zero_plus_x (f (nat_pred hi));
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

let rec prod_range (#t:Type) {| m: ring t |}
                   (f: nat -> t) (lo hi: nat)
  : Tot t
  = if lo >= hi then one
    else f lo * prod_range f (nat_succ lo) hi

let prod_range_empty (#t:Type) {| m: ring t |}
                     (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures prod_range f lo hi == one)
  = ()

let prod_range_unfold_left (#t:Type) {| m: ring t |}
                           (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi == f lo * prod_range f (nat_succ lo) hi)
  = ()

let prod_range_singleton (#t:Type) {| m: ring t |}
                         (f: nat -> t) (k: nat)
  : Lemma (prod_range f k (nat_succ k) = f k)
  = prod_range_unfold_left f k (nat_succ k);
    prod_range_empty f (nat_succ k) (nat_succ k);
    x_mul_one (f k)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec prod_range_congruence_forall
  (#t:Type) {| m: ring t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires (forall (k:nat). lo <= k /\ k < hi ==> f k = g k))
          (ensures prod_range f lo hi = prod_range g lo hi)
          (decreases (hi - lo))
  = if lo >= hi then reflexivity (prod_range f lo hi)
    else begin
      prod_range_congruence_forall f g (nat_succ lo) hi;
      reflexivity (f lo);
      mul_congruence (f lo) (prod_range f (nat_succ lo) hi)
                     (g lo) (prod_range g (nat_succ lo) hi)
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec prod_range_unfold_right
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi = prod_range f lo (nat_pred hi) * f (nat_pred hi))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if nat_succ lo = hi then begin
      prod_range_unfold_left f lo hi;
      prod_range_empty f (nat_succ lo) hi;
      x_mul_one (f lo);
      prod_range_empty f lo (nat_pred hi);
      one_mul_x (f (nat_pred hi));
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

#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
let rec prod_range_split
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (lo mid hi: nat)
  : Lemma (requires lo <= mid /\ mid <= hi)
          (ensures prod_range f lo hi =
                   prod_range f lo mid * prod_range f mid hi)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo = mid then begin
      prod_range_empty f lo mid;
      reflexivity (prod_range f mid hi);
      mul_congruence (prod_range f lo mid) (prod_range f mid hi)
                     (one) (prod_range f mid hi);
      one_mul_x (prod_range f mid hi);
      symmetry (one * prod_range f mid hi) (prod_range f mid hi);
      reflexivity (prod_range f lo hi);
      transitivity (prod_range f lo hi)
                   (prod_range f mid hi)
                   (one * prod_range f mid hi);
      transitivity (prod_range f lo hi)
                   (one * prod_range f mid hi)
                   (prod_range f lo mid * prod_range f mid hi)
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
      trans4 (prod_range f lo hi) (f lo * prod_range f (nat_succ lo) hi) (f lo * (prod_range f (nat_succ lo) mid * prod_range f mid hi)) ((f lo * prod_range f (nat_succ lo) mid) * prod_range f mid hi) (prod_range f lo mid * prod_range f mid hi)
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let prod_range_two_step
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (i: nat)
  : Lemma (prod_range f i (nat_succ (nat_succ i)) = f i * f (nat_succ i))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    prod_range_unfold_left f i (nat_succ (nat_succ i));
    prod_range_singleton f (nat_succ i);
    reflexivity (f i);
    mul_congruence (f i) (prod_range f (nat_succ i) (nat_succ (nat_succ i)))
                   (f i) (f (nat_succ i))
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let prod_range_swap_adjacent_forall
  (#t:Type) {| m: commutative_ring t |}
  (f g: nat -> t) (lo hi: nat) (i: nat)
  : Lemma (requires lo <= i /\ nat_succ i < hi /\
                    g i = f (nat_succ i) /\ g (nat_succ i) = f i /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i /\ k <> nat_succ i ==> g k = f k))
          (ensures prod_range f lo hi = prod_range g lo hi)
  = elim_equatable_laws t ();
    trans_for_calc t ();
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
    prod_range_congruence_forall f g lo i;
    let right_cong_aux (k: nat) : Lemma (i2 <= k /\ k < hi ==> f k = g k)
      = if i2 <= k && k < hi then begin
          assert (k <> i /\ k <> nat_succ i);
          symmetry (g k) (f k)
        end
    in Classical.forall_intro right_cong_aux;
    prod_range_congruence_forall f g i2 hi;
    prod_range_two_step f i;
    prod_range_two_step g i;
    mul_commutativity (f (nat_succ i)) (f i);
    let lp = prod_range f lo i in
    let rp = prod_range f i2 hi in
    let lp_g = prod_range g lo i in
    let rp_g = prod_range g i2 hi in
    reflexivity rp;
    mul_congruence (prod_range f i i2) rp (f i * f (nat_succ i)) rp;
    trans2 (prod_range f i hi) (prod_range f i i2 * rp) ((f i * f (nat_succ i)) * rp);
    reflexivity rp_g;
    mul_congruence (prod_range g i i2) rp_g (g i * g (nat_succ i)) rp_g;
    trans2 (prod_range g i hi) (prod_range g i i2 * rp_g) ((g i * g (nat_succ i)) * rp_g);
    mul_congruence (g i) (g (nat_succ i)) (f (nat_succ i)) (f i);
    mul_congruence (g i * g (nat_succ i)) rp_g (f (nat_succ i) * f i) rp_g;
    trans2 (prod_range g i hi) ((g i * g (nat_succ i)) * rp_g) ((f (nat_succ i) * f i) * rp_g);
    reflexivity lp;
    reflexivity lp_g;
    mul_congruence lp (prod_range f i hi) lp ((f i * f (nat_succ i)) * rp);
    mul_congruence lp_g (prod_range g i hi) lp_g ((f (nat_succ i) * f i) * rp_g);
    assert (f i * f (nat_succ i) = f (nat_succ i) * f i);
    assert (lp = lp_g);
    mul_congruence (f i * f (nat_succ i)) rp (f (nat_succ i) * f i) rp_g;
    mul_congruence lp ((f i * f (nat_succ i)) * rp) lp_g ((f (nat_succ i) * f i) * rp_g);
    trans3 (prod_range f lo hi) (lp * prod_range f i hi) (lp * ((f i * f (nat_succ i)) * rp)) (lp_g * ((f (nat_succ i) * f i) * rp_g));
    symmetry (prod_range g i hi) ((f (nat_succ i) * f i) * rp_g);
    reflexivity lp_g;
    mul_congruence lp_g ((f (nat_succ i) * f i) * rp_g) lp_g (prod_range g i hi);
    symmetry (prod_range g lo hi) (lp_g * prod_range g i hi);
    trans3 (prod_range f lo hi) (lp_g * ((f (nat_succ i) * f i) * rp_g)) (lp_g * prod_range g i hi) (prod_range g lo hi)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec prod_range_perm_invariance
  (#t:Type) {| m: commutative_ring t |}
  (#n: nat) (f: nat -> t) (p: permutation n)
  : Lemma (ensures
            prod_range (fun (k: nat) ->
              if k < n then f (p.fwd (k <: fin n)) else one) 0 n
          = prod_range (fun (k: nat) ->
              if k < n then f k else one) 0 n)
          (decreases (inversion_count p))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let body_p : nat -> t =
      fun (k: nat) -> if k < n then f (p.fwd (k <: fin n)) else one in
    let body_id : nat -> t =
      fun (k: nat) -> if k < n then f k else one in
    perm_descent_exists_or_inv_zero p;
    eliminate (inversion_count p == 0) \/
              (exists (i: nat{nat_succ i < n}).
                 inversion_count (right_swap p i) < inversion_count p)
    returns prod_range body_p 0 n = prod_range body_id 0 n
    with _.
      begin
        let body_eq_aux (k: nat) : Lemma (0 <= k /\ k < n ==> body_p k = body_id k)
          = if 0 <= k && k < n then begin
              inv_zero_implies_identity_fwd p (k <: fin n);
              reflexivity (f k)
            end
        in Classical.forall_intro body_eq_aux;
        prod_range_congruence_forall body_p body_id 0 n
      end
    and _.
      begin
        eliminate exists (i: nat{nat_succ i < n}).
                    inversion_count (right_swap p i) < inversion_count p
        returns prod_range body_p 0 n = prod_range body_id 0 n
        with _.
          begin
            let q = right_swap p i in
            let body_q : nat -> t =
              fun (k: nat) -> if k < n then f (q.fwd (k <: fin n)) else one in
            let swap_aux_i () : Lemma (body_p i = body_q (nat_succ i))
              = right_swap_fwd_at_i_plus_1 p i;
                reflexivity (f (p.fwd (i <: fin n))) in
            let swap_aux_ip1 () : Lemma (body_p (nat_succ i) = body_q i)
              = right_swap_fwd_at_i p i;
                reflexivity (f (p.fwd (nat_succ i <: fin n))) in
            let swap_aux_off (k: nat)
              : Lemma (0 <= k /\ k < n /\ k <> i /\ k <> nat_succ i ==> body_q k = body_p k)
              = if 0 <= k && k < n && k <> i && k <> nat_succ i then begin
                  right_swap_fwd_at_other p i (k <: fin n);
                  reflexivity (f (p.fwd (k <: fin n)))
                end
            in
            swap_aux_i ();
            swap_aux_ip1 ();
            Classical.forall_intro swap_aux_off;
            symmetry (body_p i) (body_q (nat_succ i));
            symmetry (body_p (nat_succ i)) (body_q i);
            prod_range_swap_adjacent_forall body_q body_p 0 n i;
            symmetry (prod_range body_q 0 n) (prod_range body_p 0 n);
            prod_range_perm_invariance #t #m #n f q;
            trans2 (prod_range body_p 0 n) (prod_range body_q 0 n) (prod_range body_id 0 n)
          end
      end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let prod_range_perm_invariance_fn_forall
  (#t:Type) {| m: commutative_ring t |}
  (#n: nat) (f body_p body_id: nat -> t) (p: permutation n)
  : Lemma (requires
            (forall (k: nat). 0 <= k /\ k < n ==> body_p k = f (p.fwd (k <: fin n))) /\
            (forall (k: nat). 0 <= k /\ k < n ==> body_id k = f k))
          (ensures prod_range body_p 0 n = prod_range body_id 0 n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    prod_range_perm_invariance f p;
    let bp_eq_lp (k: nat) : Lemma
      (requires 0 <= k /\ k < n)
      (ensures body_p k = (if k < n then f (p.fwd (k <: fin n)) else one))
      = reflexivity (f (p.fwd (k <: fin n))) in
    Classical.forall_intro (Classical.move_requires bp_eq_lp);
    prod_range_congruence_forall body_p
      (fun (k: nat) -> if k < n then f (p.fwd (k <: fin n)) else one) 0 n;
    let li_eq_bi (k: nat) : Lemma
      (requires 0 <= k /\ k < n)
      (ensures (if k < n then f k else one) = body_id k)
      = reflexivity (f k) in
    Classical.forall_intro (Classical.move_requires li_eq_bi);
    prod_range_congruence_forall
      (fun (k: nat) -> if k < n then f k else one) body_id 0 n;
    trans3 (prod_range body_p 0 n) (prod_range (fun (k: nat) -> if k < n then f (p.fwd (k <: fin n)) else one) 0 n) (prod_range (fun (k: nat) -> if k < n then f k else one) 0 n) (prod_range body_id 0 n)
#pop-options

(* ----------------------------------------------------------------- *)
(*  Sum over a list                                                  *)
(* ----------------------------------------------------------------- *)

let rec sum_list (#t:Type) {| m: add_comm_group t |} (xs: list t) : Tot t
  = match xs with
    | [] -> zero
    | x :: rest -> x + sum_list rest

let sum_list_nil (#t:Type) {| m: add_comm_group t |}
  : Lemma (sum_list [] == zero #t) = ()

let sum_list_cons (#t:Type) {| m: add_comm_group t |} (x: t) (rest: list t)
  : Lemma (sum_list (x :: rest) == x + sum_list rest) = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 20"
let rec sum_list_map_congruence_forall
  (#a:Type) (#t:Type) {| m: add_comm_group t |}
  (f g: a -> t) (xs: list a)
  : Lemma (requires (forall (x:a). memP x xs ==> f x = g x))
          (ensures sum_list (map f xs) = sum_list (map g xs))
  = match xs with
    | [] -> reflexivity (sum_list #t #m [])
    | x :: rest ->
      sum_list_map_congruence_forall f g rest;
      add_congruence (f x) (sum_list (map f rest))
                     (g x) (sum_list (map g rest))
#pop-options

private let rec sum_list_map_neg_lambda
  (#a:Type) (#t:Type) {| g: add_comm_group t |}
  (f: a -> t) (xs: list a)
  : Lemma (ensures sum_list (map (fun x -> neg (f x)) xs) = neg (sum_list (map f xs)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] -> sum_list_nil #t #g;
            assert (sum_list #t #g (map (fun x -> neg (f x)) []) == zero);
            assert (sum_list #t #g (map f []) == zero);
            neg_zero #t ()
    | hx :: rest ->
      sum_list_map_neg_lambda f rest;
      let h = f hx in
      let trest = sum_list (map f rest) in
      let nrest = sum_list (map (fun x -> neg (f x)) rest) in
      assert (nrest = neg trest);
      reflexivity (neg h);
      add_congruence (neg h) nrest (neg h) (neg trest);
      neg_of_sum h trest;
      symmetry (neg (h + trest)) (neg trest + neg h);
      (* But we want `neg h + neg trest = neg (h + trest)`; flip via comm. *)
      add_commutativity (neg h) (neg trest);
      transitivity (neg h + nrest) (neg h + neg trest) (neg trest + neg h);
      transitivity (neg h + nrest) (neg trest + neg h) (neg (h + trest))


#push-options "--fuel 6 --ifuel 4 --z3rlimit 80"
private let rec sum_list_map_add_lambda
  (#a:Type) (#t:Type) {| m: add_comm_group t |}
  (f g: a -> t) (xs: list a)
  : Lemma (ensures sum_list (map (fun x -> f x + g x) xs)
                 = sum_list (map f xs) + sum_list (map g xs))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] ->
      zero_plus_x (zero #t);
      symmetry (zero + zero #t) zero
    | hx :: rest ->
      sum_list_map_add_lambda #a #t #m f g rest;
      let a1 = f hx in
      let b1 = g hx in
      let sf = sum_list (map f rest) in
      let sg = sum_list (map g rest) in
      let sh = sum_list (map (fun x -> f x + g x) rest) in
      assert (sh = sf + sg);
      reflexivity (a1 + b1);
      add_congruence (a1 + b1) sh (a1 + b1) (sf + sg);
      add_associativity a1 b1 sf;
      symmetry ((a1 + b1) + sf) (a1 + (b1 + sf));
      add_commutativity b1 sf;
      reflexivity a1;
      add_congruence a1 (b1 + sf) a1 (sf + b1);
      add_associativity a1 sf b1;
      transitivity (a1 + (b1 + sf)) (a1 + (sf + b1)) ((a1 + sf) + b1);
      transitivity ((a1 + b1) + sf) (a1 + (b1 + sf)) ((a1 + sf) + b1);
      reflexivity sg;
      add_congruence ((a1 + b1) + sf) sg ((a1 + sf) + b1) sg;
      add_associativity (a1 + b1) sf sg;
      symmetry ((a1 + b1) + sf + sg) ((a1 + b1) + (sf + sg));
      add_associativity (a1 + sf) b1 sg;
      symmetry ((a1 + sf) + b1 + sg) ((a1 + sf) + (b1 + sg));
      trans4 ((a1 + b1) + sh) ((a1 + b1) + (sf + sg)) (((a1 + b1) + sf) + sg) (((a1 + sf) + b1) + sg) ((a1 + sf) + (b1 + sg))
#pop-options

(* ----------------------------------------------------------------- *)
(*  Algebraic identities involving sums (ring)                   *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 6 --ifuel 4 --z3rlimit 80"
private let rec sum_list_map_mul_left_lambda
  (#a:Type) (#t:Type) {| r: ring t |}
  (c: t) (f: a -> t) (xs: list a)
  : Lemma (ensures c * sum_list (map f xs) = sum_list (map (fun x -> c * f x) xs))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] ->
      x_mul_zero c;
      symmetry (c * (zero #t)) (zero #t)
    | hx :: rest ->
      sum_list_map_mul_left_lambda #a #t #r c f rest;
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
      trans4 (s_lhs) (s_mid1) (s_mid2) (s_mid3) (s_rhs)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let rec sum_range_const_zero_lambda
  (#t:Type) {| m: add_comm_group t |}
  (lo hi: nat)
  : Lemma (ensures sum_range #t (fun _ -> zero) lo hi = zero)
          (decreases (hi - lo))
  = if lo >= hi then reflexivity (zero #t)
    else begin
      sum_range_const_zero_lambda #t #m (nat_succ lo) hi;
      sum_range_unfold_left #t (fun _ -> zero) lo hi;
      reflexivity (zero #t);
      add_congruence (zero #t) (sum_range #t (fun _ -> zero) (nat_succ lo) hi)
                     (zero #t) (zero #t);
      zero_plus_x (zero #t);
      reflexivity (sum_range #t (fun _ -> zero) lo hi);
      trans3 (sum_range #t (fun _ -> zero) lo hi) (zero + sum_range #t (fun _ -> zero) (nat_succ lo) hi) (zero + zero #t) (zero #t)
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let rec sum_range_mul_left_lambda
  (#t:Type) {| r: ring t |}
  (c: t) (f: nat -> t) (lo hi: nat)
  : Lemma (ensures c * sum_range f lo hi = sum_range (fun k -> c * f k) lo hi)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo >= hi then begin
      sum_range_empty f lo hi;
      sum_range_empty (fun k -> c * f k) lo hi;
      reflexivity c;
      mul_congruence c (sum_range f lo hi) c zero;
      x_mul_zero c;
      symmetry (sum_range (fun k -> c * f k) lo hi) zero;
      transitivity (c * sum_range f lo hi) (c * zero) zero;
      transitivity (c * sum_range f lo hi) zero (sum_range (fun k -> c * f k) lo hi)
    end else begin
      sum_range_unfold_left f lo hi;
      sum_range_unfold_left (fun k -> c * f k) lo hi;
      let s1 = c * sum_range f lo hi in
      let s2 = c * (f lo + sum_range f (nat_succ lo) hi) in
      reflexivity s1;
      left_distributivity c (f lo) (sum_range f (nat_succ lo) hi);
      sum_range_mul_left_lambda c f (nat_succ lo) hi;
      reflexivity (c * f lo);
      add_congruence (c * f lo) (c * sum_range f (nat_succ lo) hi)
                     (c * f lo) (sum_range (fun k -> c * f k) (nat_succ lo) hi);
      let s5 = sum_range (fun k -> c * f k) lo hi in
      let s4 = c * f lo + sum_range (fun k -> c * f k) (nat_succ lo) hi in
      reflexivity s5;
      symmetry s5 s4;
      trans4 (s1) (s2) (c * f lo + c * sum_range f (nat_succ lo) hi) (s4) (s5)
    end
#pop-options


#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let rec sum_range_mul_right_lambda
  (#t:Type) {| r: ring t |}
  (f: nat -> t) (c: t) (lo hi: nat)
  : Lemma (ensures sum_range f lo hi * c = sum_range (fun k -> f k * c) lo hi)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo >= hi then begin
      sum_range_empty f lo hi;
      sum_range_empty (fun k -> f k * c) lo hi;
      reflexivity c;
      mul_congruence (sum_range f lo hi) c zero c;
      zero_mul_x c;
      symmetry (sum_range (fun k -> f k * c) lo hi) zero;
      transitivity (sum_range f lo hi * c) (zero * c) zero;
      transitivity (sum_range f lo hi * c) zero (sum_range (fun k -> f k * c) lo hi)
    end else begin
      sum_range_unfold_left f lo hi;
      sum_range_unfold_left (fun k -> f k * c) lo hi;
      let s1 = sum_range f lo hi * c in
      let s2 = (f lo + sum_range f (nat_succ lo) hi) * c in
      reflexivity s1;
      right_distributivity c (f lo) (sum_range f (nat_succ lo) hi);
      sum_range_mul_right_lambda f c (nat_succ lo) hi;
      reflexivity (f lo * c);
      add_congruence (f lo * c) (sum_range f (nat_succ lo) hi * c)
                     (f lo * c) (sum_range (fun k -> f k * c) (nat_succ lo) hi);
      let s5 = sum_range (fun k -> f k * c) lo hi in
      let s4 = f lo * c + sum_range (fun k -> f k * c) (nat_succ lo) hi in
      reflexivity s5;
      symmetry s5 s4;
      trans4 (s1) (s2) (f lo * c + sum_range f (nat_succ lo) hi * c) (s4) (s5)
    end
#pop-options


#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let rec sum_range_add_lambda
  (#t:Type) {| m: add_comm_group t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (fun k -> f k + g k) lo hi
                  = sum_range f lo hi + sum_range g lo hi)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo >= hi then begin
      sum_range_empty (fun k -> f k + g k) lo hi;
      sum_range_empty f lo hi;
      sum_range_empty g lo hi;
      reflexivity (zero #t);
      add_congruence (sum_range f lo hi) (sum_range g lo hi) zero zero;
      zero_plus_x (zero #t);
      symmetry (zero + zero #t) zero;
      trans3 (sum_range (fun k -> f k + g k) lo hi) (zero #t) (zero + zero #t) (sum_range f lo hi + sum_range g lo hi)
    end else begin
      sum_range_unfold_left (fun k -> f k + g k) lo hi;
      sum_range_unfold_left f lo hi;
      sum_range_unfold_left g lo hi;
      let fl = f lo in let gl = g lo in
      let fa = sum_range f (nat_succ lo) hi in
      let ga = sum_range g (nat_succ lo) hi in
      sum_range_add_lambda f g (nat_succ lo) hi;
      reflexivity (fl + gl);
      add_congruence (fl + gl) (sum_range (fun k -> f k + g k) (nat_succ lo) hi)
                     (fl + gl) (fa + ga);
      let head = sum_range (fun k -> f k + g k) lo hi in
      let target = sum_range f lo hi + sum_range g lo hi in
      reflexivity head;
      reflexivity target;
      add_associativity fl gl (fa + ga);
      add_associativity gl fa ga;
      symmetry ((gl + fa) + ga) (gl + (fa + ga));
      add_commutativity gl fa;
      reflexivity ga;
      add_congruence (gl + fa) ga (fa + gl) ga;
      add_associativity fa gl ga;
      trans3 (gl + (fa + ga)) ((gl + fa) + ga) ((fa + gl) + ga) (fa + (gl + ga));
      reflexivity fl;
      add_congruence fl (gl + (fa + ga)) fl (fa + (gl + ga));
      add_associativity fl fa (gl + ga);
      symmetry ((fl + fa) + (gl + ga)) (fl + (fa + (gl + ga)));
      trans4 (head) ((fl + gl) + (fa + ga)) (fl + (gl + (fa + ga))) (fl + (fa + (gl + ga))) ((fl + fa) + (gl + ga));
      reflexivity ((fl + fa) + (gl + ga));
      transitivity head ((fl + fa) + (gl + ga)) target
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec sum_swap_aux_lambda
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> nat -> t)
  (i_lo i_hi j_lo j_hi: nat)
  : Lemma (ensures sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi
                  = sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
          (decreases (i_hi - i_lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if i_lo >= i_hi then begin
      sum_range_empty #t (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi;
      let inner_fn (j: nat) : t = sum_range (fun i -> f i j) i_lo i_hi in
      let pf (j: nat) : Lemma (j_lo <= j /\ j < j_hi ==> inner_fn j = zero)
        = if j_lo <= j && j < j_hi then begin
            sum_range_empty #t (fun i -> f i j) i_lo i_hi;
            reflexivity (zero #t)
          end
      in
      Classical.forall_intro pf;
      sum_range_congruence_forall #t inner_fn (fun _ -> zero) j_lo j_hi;
      sum_range_const_zero_lambda #t #m j_lo j_hi;
      transitivity (sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
                   (sum_range #t (fun _ -> zero) j_lo j_hi)
                   zero;
      symmetry (sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi) zero;
      transitivity (sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi)
                   zero
                   (sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
    end else begin
      sum_range_unfold_left #t (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi;
      sum_swap_aux_lambda f (nat_succ i_lo) i_hi j_lo j_hi;
      reflexivity (sum_range (f i_lo) j_lo j_hi);
      add_congruence (sum_range (f i_lo) j_lo j_hi)
                     (sum_range (fun i -> sum_range (f i) j_lo j_hi) (nat_succ i_lo) i_hi)
                     (sum_range (f i_lo) j_lo j_hi)
                     (sum_range (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi);
      sum_range_add_lambda #t (f i_lo)
                       (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi)
                       j_lo j_hi;
      symmetry (sum_range (fun j -> f i_lo j + sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi)
               (sum_range (f i_lo) j_lo j_hi
                + sum_range (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi);
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
      sum_range_congruence_forall #t lhs_inner rhs_inner j_lo j_hi;
      trans4 (sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi) (sum_range (f i_lo) j_lo j_hi + sum_range (fun i -> sum_range (f i) j_lo j_hi) (nat_succ i_lo) i_hi) (sum_range (f i_lo) j_lo j_hi + sum_range (fun j -> sum_range (fun i -> f i j) (nat_succ i_lo) i_hi) j_lo j_hi) (sum_range lhs_inner j_lo j_hi) (sum_range rhs_inner j_lo j_hi)
    end
#pop-options

private let sum_swap_lambda
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> nat -> t)
  (i_lo i_hi j_lo j_hi: nat)
  : Lemma (sum_range (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi
         = sum_range (fun j -> sum_range (fun i -> f i j) i_lo i_hi) j_lo j_hi)
  = sum_swap_aux_lambda f i_lo i_hi j_lo j_hi

(* ----------------------------------------------------------------- *)
(*  Sum over `fin n`                                                 *)
(* ----------------------------------------------------------------- *)

(* fin_sum is defined in the fsti as `unfold let`. *)

let fin_sum_congruence_forall
  (#t:Type) {| m: add_comm_group t |}
  (#n: nat) (f g: fin n -> t)
  : Lemma (requires (forall (k: fin n). f k = g k))
          (ensures fin_sum f = fin_sum g)
  = sum_range_congruence_forall
      (fun (k: nat) -> if k < n then f (k <: fin n) else zero)
      (fun (k: nat) -> if k < n then g (k <: fin n) else zero)
      0 n

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let fin_sum_mul_left_lambda
  (#t:Type) {| r: ring t |}
  (#n: nat) (c: t) (f: fin n -> t)
  : Lemma (c * fin_sum f = fin_sum (fun (k: fin n) -> c * f k))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_range_mul_left_lambda c
      (fun (k: nat) -> if k < n then f (k <: fin n) else zero) 0 n;
    let pf (k: nat) : Lemma (0 <= k /\ k < n ==>
              c * (if k < n then f (k <: fin n) else zero)
              = (if k < n then c * f (k <: fin n) else zero))
      = if 0 <= k && k < n then reflexivity (c * f (k <: fin n))
    in
    Classical.forall_intro pf;
    sum_range_congruence_forall
      (fun (k: nat) -> c * (if k < n then f (k <: fin n) else zero))
      (fun (k: nat) -> if k < n then c * f (k <: fin n) else zero)
      0 n;
    transitivity
      (c * fin_sum f)
      (sum_range (fun (k: nat) -> c * (if k < n then f (k <: fin n) else zero)) 0 n)
      (fin_sum (fun (k: fin n) -> c * f k))
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let fin_sum_mul_right_lambda
  (#t:Type) {| r: ring t |}
  (#n: nat) (f: fin n -> t) (c: t)
  : Lemma (fin_sum f * c = fin_sum (fun (k: fin n) -> f k * c))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_range_mul_right_lambda
      (fun (k: nat) -> if k < n then f (k <: fin n) else zero) c 0 n;
    let pf (k: nat) : Lemma (0 <= k /\ k < n ==>
              (if k < n then f (k <: fin n) else zero) * c
              = (if k < n then f (k <: fin n) * c else zero))
      = if 0 <= k && k < n then reflexivity (f (k <: fin n) * c)
    in
    Classical.forall_intro pf;
    sum_range_congruence_forall
      (fun (k: nat) -> (if k < n then f (k <: fin n) else zero) * c)
      (fun (k: nat) -> if k < n then f (k <: fin n) * c else zero)
      0 n;
    transitivity
      (fin_sum f * c)
      (sum_range (fun (k: nat) -> (if k < n then f (k <: fin n) else zero) * c) 0 n)
      (fin_sum (fun (k: fin n) -> f k * c))
#pop-options

(* fin_swap_body is a private helper used by fin_sum_swap_lambda. *)
unfold
private let fin_swap_body (#t:Type) {| m: add_comm_group t |}
    (#n: nat) (f: fin n -> fin n -> t) (i j: nat) : t
  = if i < n && j < n then f (i <: fin n) (j <: fin n) else zero

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let fin_sum_swap_lambda
  (#t:Type) {| m: add_comm_group t |}
  (#n: nat) (f: fin n -> fin n -> t)
  : Lemma (fin_sum (fun (i: fin n) -> fin_sum (f i))
         = fin_sum (fun (j: fin n) -> fin_sum (fun (i: fin n) -> f i j)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
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
          sum_range_congruence_forall inner_a inner_b 0 n
        end
    in
    Classical.forall_intro pf1;
    sum_range_congruence_forall outer_lhs outer_lhs_open 0 n;
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
          sum_range_congruence_forall inner_a inner_b 0 n
        end
    in
    Classical.forall_intro pf2;
    sum_range_congruence_forall outer_rhs outer_rhs_open 0 n;
    sum_swap_lambda (fin_swap_body f) 0 n 0 n;
    let pf3 (i: nat) : Lemma (0 <= i /\ i < n ==>
              sum_range (fin_swap_body f i) 0 n = outer_lhs_open i)
      = if 0 <= i && i < n then reflexivity (sum_range (fin_swap_body f i) 0 n)
    in
    Classical.forall_intro pf3;
    sum_range_congruence_forall
      (fun (i: nat) -> sum_range (fin_swap_body f i) 0 n) outer_lhs_open 0 n;
    let pf4 (j: nat) : Lemma (0 <= j /\ j < n
                          ==> sum_range (fun (i: nat) -> fin_swap_body f i j) 0 n = outer_rhs_open j)
      = if 0 <= j && j < n then
          reflexivity (sum_range (fun (i: nat) -> fin_swap_body f i j) 0 n)
    in
    Classical.forall_intro pf4;
    sum_range_congruence_forall
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

private let fin_sum_const_zero_lambda
  (#t:Type) {| m: add_comm_group t |} (#n: nat)
  : Lemma (fin_sum #t #m #n (fun (_: fin n) -> zero #t) = zero #t)
  = elim_equatable_laws t ();
    let lhs_open (k: nat) : t
      = if k < n then (fun (_: fin n) -> zero #t) (k <: fin n) else zero in
    let zfn (_: nat) : t = zero in
    let pf (k: nat) : Lemma (0 <= k /\ k < n ==> lhs_open k = zfn k)
      = if k < n then reflexivity (zero #t)
    in
    Classical.forall_intro pf;
    sum_range_congruence_forall lhs_open zfn 0 n;
    sum_range_const_zero_lambda #t #m 0 n;
    transitivity
      (fin_sum #t #m #n (fun (_: fin n) -> zero #t))
      (sum_range zfn 0 n)
      (zero #t)

let fin_sum_zero_ext_forall
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f: fin n -> t)
  : Lemma (requires (forall (k: fin n). f k = zero #t))
          (ensures fin_sum f = zero #t)
  = elim_equatable_laws t ();
    let pf (k: fin n) : Lemma (f k = (fun (_: fin n) -> zero #t) k)
      = ()
    in
    Classical.forall_intro pf;
    fin_sum_congruence_forall f (fun (_: fin n) -> zero #t);
    fin_sum_const_zero_lambda #t #m #n;
    transitivity (fin_sum f)
                 (fin_sum #t #m #n (fun (_: fin n) -> zero #t))
                 (zero #t)

private let fin_sum_add_lambda
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f g: fin n -> t)
  : Lemma (fin_sum (fun (k: fin n) -> f k + g k)
        = fin_sum f + fin_sum g)
  = elim_equatable_laws t ();
    let fopen (k: nat) : t = if k < n then f (k <: fin n) else zero in
    let gopen (k: nat) : t = if k < n then g (k <: fin n) else zero in
    let sopen (k: nat) : t = if k < n then f (k <: fin n) + g (k <: fin n) else zero in
    let addopen (k: nat) : t = fopen k + gopen k in
    let pf (k: nat) : Lemma (0 <= k /\ k < n ==> sopen k = addopen k)
      = if k < n then reflexivity (f (k <: fin n) + g (k <: fin n))
        else begin
          zero_plus_x (zero #t);
          symmetry (zero + zero #t) zero
        end
    in
    Classical.forall_intro pf;
    sum_range_congruence_forall sopen addopen 0 n;
    sum_range_add_lambda fopen gopen 0 n;
    transitivity
      (fin_sum (fun (k: fin n) -> f k + g k))
      (sum_range addopen 0 n)
      (sum_range fopen 0 n + sum_range gopen 0 n)

let fin_sum_add_ext_forall
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f g h: fin n -> t)
  : Lemma (requires (forall (k: fin n). h k = f k + g k))
          (ensures fin_sum h = fin_sum f + fin_sum g)
  = elim_equatable_laws t ();
    fin_sum_add_lambda f g;
    let pf (k: fin n) : Lemma (h k = (fun (k: fin n) -> f k + g k) k)
      = ()
    in
    Classical.forall_intro pf;
    fin_sum_congruence_forall h (fun (k: fin n) -> f k + g k);
    transitivity (fin_sum h)
                 (fin_sum (fun (k: fin n) -> f k + g k))
                 (fin_sum f + fin_sum g)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec sum_range_kronecker_lambda
  (#t:Type) {| r: ring t |}
  (i0: nat) (g: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (fun (k:nat) -> (if i0 = k then one else zero #t) * g k) lo hi
                 = (if lo <= i0 && i0 < hi then g i0 else zero #t))
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo >= hi then begin
      sum_range_empty #t (fun (k:nat) -> (if i0 = k then one else zero #t) * g k) lo hi;
      reflexivity (zero #t)
    end else begin
      sum_range_unfold_left #t (fun (k:nat) -> (if i0 = k then one else zero #t) * g k) lo hi;
      sum_range_kronecker_lambda i0 g (nat_succ lo) hi;
      let body : nat -> t
        = fun (k:nat) -> (if i0 = k then one else zero #t) * g k in
      let tail = sum_range body (nat_succ lo) hi in
      let head = body lo in
      let lhs = sum_range body lo hi in
      reflexivity lhs;
      if i0 = lo then begin
        one_mul_x (g lo);
        x_plus_zero (g lo);
        add_congruence head tail (g lo) (zero #t);
        transitivity lhs (head + tail) (g lo + zero);
        transitivity lhs (g lo + zero) (g lo)
      end else begin
        zero_mul_x (g lo);
        zero_plus_x tail;
        add_congruence head tail (zero #t) tail;
        transitivity lhs (head + tail) (zero + tail);
        transitivity lhs (zero + tail) tail
      end
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let fin_sum_kronecker_lambda
  (#t:Type) {| r: ring t |}
  (#n: nat) (i0: fin n) (g: fin n -> t)
  : Lemma (fin_sum (fun (k: fin n) -> (if (i0 <: nat) = (k <: nat) then one else zero #t) * g k)
        = g i0)
  = elim_equatable_laws t ();
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
    sum_range_congruence_forall body_open kron_body 0 n;
    sum_range_kronecker_lambda (i0 <: nat) g_open 0 n;
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

(* =================================================================  *)
(*  New combinator-shape public API (Path A refactor).                *)
(*                                                                    *)
(*  These wrappers bridge the lambda-shape proofs above to the        *)
(*  combinator-shape postconditions declared in the .fsti.            *)
(* =================================================================  *)

let rec sum_list_map_congruence
  (#a:Type) (#t:Type) {| m: add_comm_group t |}
  (f g: a -> t) (xs: list a)
  (h: (x:a) -> Lemma (requires memP x xs) (ensures f x = g x))
  : Lemma (ensures sum_list (map f xs) = sum_list (map g xs))
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] -> reflexivity (sum_list #t #m [])
    | x :: rest ->
        h x;
        let h' (y:a) : Lemma (requires memP y rest) (ensures f y = g y)
          = h y in
        sum_list_map_congruence f g rest h';
        sum_list_cons (f x) (map f rest);
        sum_list_cons (g x) (map g rest);
        add_congruence (f x) (sum_list (map f rest)) (g x) (sum_list (map g rest));
        symmetry (sum_list (map g (x :: rest))) (g x + sum_list (map g rest));
        trans3 (sum_list (map f (x :: rest)))
               (f x + sum_list (map f rest))
               (g x + sum_list (map g rest))
               (sum_list (map g (x :: rest)))

let sum_range_congruence
  (#t:Type) {| m: add_comm_group t |}
  (f g: nat -> t) (lo hi: nat)
  (h: (k:nat{lo <= k /\ k < hi}) -> Lemma (f k = g k))
  : Lemma (sum_range f lo hi = sum_range g lo hi)
  = elim_equatable_laws t ();
    let prf (k: nat) : Lemma (lo <= k /\ k < hi ==> f k = g k)
      = if lo <= k && k < hi then h k
    in
    Classical.forall_intro prf;
    sum_range_congruence_forall f g lo hi

let fin_sum_congruence
  (#t:Type) {| m: add_comm_group t |}
  (#n: nat) (f g: fin n -> t)
  (h: (k:fin n) -> Lemma (f k = g k))
  : Lemma (fin_sum f = fin_sum g)
  = elim_equatable_laws t ();
    let prf (k: fin n) : Lemma (f k = g k) = h k in
    Classical.forall_intro prf;
    fin_sum_congruence_forall f g

let fin_prod_congruence_forall
  (#t:Type) {| r: ring t |}
  (#n: nat) (f g: fin n -> t)
  : Lemma (requires (forall (k: fin n). f k = g k))
          (ensures fin_prod f = fin_prod g)
  = prod_range_congruence_forall
      (fun (k: nat) -> if k < n then f (k <: fin n) else one)
      (fun (k: nat) -> if k < n then g (k <: fin n) else one)
      0 n

let fin_prod_congruence
  (#t:Type) {| r: ring t |}
  (#n: nat) (f g: fin n -> t)
  (h: (k:fin n) -> Lemma (f k = g k))
  : Lemma (fin_prod f = fin_prod g)
  = elim_equatable_laws t ();
    let prf (k: fin n) : Lemma (f k = g k) = h k in
    Classical.forall_intro prf;
    fin_prod_congruence_forall f g

(* ---------------- sum_list / map ---------------- *)

let sum_list_map_neg
  (#a:Type) (#t:Type) {| g: add_comm_group t |}
  (f: a -> t) (xs: list a)
  : Lemma (sum_list (map (pointwise_neg f) xs) = neg (sum_list (map f xs)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_list_map_neg_lambda f xs;
    let lam (x: a) : t = neg (f x) in
    let cm : a -> t = pointwise_neg f in
    let prf (x: a) : Lemma (cm x = lam x)
      = pointwise_neg_unfold f x;
        reflexivity (neg (f x))
    in
    sum_list_map_congruence cm lam xs prf;
    transitivity (sum_list (map cm xs))
                 (sum_list (map lam xs))
                 (neg (sum_list (map f xs)))

let sum_list_map_add
  (#a:Type) (#t:Type) {| m: add_comm_group t |}
  (f g: a -> t) (xs: list a)
  : Lemma (sum_list (map (pointwise_add f g) xs)
         = sum_list (map f xs) + sum_list (map g xs))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_list_map_add_lambda f g xs;
    let lam (x: a) : t = f x + g x in
    let cm : a -> t = pointwise_add f g in
    let prf (x: a) : Lemma (cm x = lam x)
      = pointwise_add_unfold f g x;
        reflexivity (f x + g x)
    in
    sum_list_map_congruence cm lam xs prf;
    transitivity (sum_list (map cm xs))
                 (sum_list (map lam xs))
                 (sum_list (map f xs) + sum_list (map g xs))

let sum_list_map_mul_left
  (#a:Type) (#t:Type) {| r: ring t |}
  (c: t) (f: a -> t) (xs: list a)
  : Lemma (c * sum_list (map f xs)
         = sum_list (map (pointwise_mul (const c) f) xs))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_list_map_mul_left_lambda c f xs;
    let lam (x: a) : t = c * f x in
    let cm : a -> t = pointwise_mul (const c) f in
    let prf (x: a) : Lemma (lam x = cm x)
      = pointwise_mul_unfold (const c) f x;
        const_unfold c x;
        reflexivity (c * f x);
        symmetry (cm x) (c * f x)
    in
    sum_list_map_congruence lam cm xs prf;
    transitivity (c * sum_list (map f xs))
                 (sum_list (map lam xs))
                 (sum_list (map cm xs))

#push-options "--fuel 6 --ifuel 4 --z3rlimit 80"
private let rec sum_list_map_mul_right_lambda
  (#a:Type) (#t:Type) {| r: ring t |}
  (f: a -> t) (c: t) (xs: list a)
  : Lemma (ensures sum_list (map f xs) * c = sum_list (map (fun x -> f x * c) xs))
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] ->
        zero_mul_x c;
        symmetry (zero #t * c) zero;
        reflexivity (sum_list #t #r.r_add (map (fun x -> f x * c) ([] <: list a)))
    | hx :: rest ->
        sum_list_map_mul_right_lambda f c rest;
        let h = f hx in
        let trest = sum_list (map f rest) in
        let crest = sum_list (map (fun x -> f x * c) rest) in
        right_distributivity c h trest;
        reflexivity (h * c);
        add_congruence (h * c) (trest * c) (h * c) crest;
        let s_lhs  = sum_list (map f (hx :: rest)) * c in
        let s_mid1 = (h + trest) * c in
        let s_mid2 = h * c + trest * c in
        let s_mid3 = h * c + crest in
        let s_rhs  = sum_list (map (fun x -> f x * c) (hx :: rest)) in
        reflexivity s_lhs;
        reflexivity s_rhs;
        symmetry s_rhs s_mid3;
        trans4 (s_lhs) (s_mid1) (s_mid2) (s_mid3) (s_rhs)
#pop-options

let sum_list_map_mul_right
  (#a:Type) (#t:Type) {| r: ring t |}
  (f: a -> t) (c: t) (xs: list a)
  : Lemma (sum_list (map f xs) * c
         = sum_list (map (pointwise_mul f (const c)) xs))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_list_map_mul_right_lambda f c xs;
    let lam (x: a) : t = f x * c in
    let cm : a -> t = pointwise_mul f (const c) in
    let prf (x: a) : Lemma (lam x = cm x)
      = pointwise_mul_unfold f (const c) x;
        const_unfold c x;
        reflexivity (f x * c);
        symmetry (cm x) (f x * c)
    in
    sum_list_map_congruence lam cm xs prf;
    transitivity (sum_list (map f xs) * c)
                 (sum_list (map lam xs))
                 (sum_list (map cm xs))

(* ---------------- sum_range ---------------- *)

let sum_range_const_zero
  (#t:Type) {| m: add_comm_group t |}
  (lo hi: nat)
  : Lemma (sum_range #t (const zero) lo hi = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_range_const_zero_lambda #t #m lo hi;
    let prf (k: nat{lo <= k /\ k < hi}) : Lemma ((const #nat #t (zero #t)) k = (fun (_: nat) -> zero #t) k)
      = const_unfold (zero #t) k;
        reflexivity (zero #t)
    in
    sum_range_congruence (const zero) (fun _ -> zero #t) lo hi prf;
    transitivity (sum_range #t (const zero) lo hi)
                 (sum_range #t (fun _ -> zero) lo hi)
                 (zero #t)

let sum_range_mul_left
  (#t:Type) {| r: ring t |}
  (c: t) (f: nat -> t) (lo hi: nat)
  : Lemma (c * sum_range f lo hi
         = sum_range (pointwise_mul (const c) f) lo hi)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_range_mul_left_lambda c f lo hi;
    let lam (k: nat) : t = c * f k in
    let cm : nat -> t = pointwise_mul (const c) f in
    let prf (k: nat{lo <= k /\ k < hi}) : Lemma (lam k = cm k)
      = pointwise_mul_unfold (const c) f k;
        const_unfold c k;
        reflexivity (c * f k);
        symmetry (cm k) (c * f k)
    in
    sum_range_congruence lam cm lo hi prf;
    transitivity (c * sum_range f lo hi)
                 (sum_range lam lo hi)
                 (sum_range cm lo hi)

let sum_range_mul_right
  (#t:Type) {| r: ring t |}
  (f: nat -> t) (c: t) (lo hi: nat)
  : Lemma (sum_range f lo hi * c
         = sum_range (pointwise_mul f (const c)) lo hi)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_range_mul_right_lambda f c lo hi;
    let lam (k: nat) : t = f k * c in
    let cm : nat -> t = pointwise_mul f (const c) in
    let prf (k: nat{lo <= k /\ k < hi}) : Lemma (lam k = cm k)
      = pointwise_mul_unfold f (const c) k;
        const_unfold c k;
        reflexivity (f k * c);
        symmetry (cm k) (f k * c)
    in
    sum_range_congruence lam cm lo hi prf;
    transitivity (sum_range f lo hi * c)
                 (sum_range lam lo hi)
                 (sum_range cm lo hi)

let sum_range_add
  (#t:Type) {| m: add_comm_group t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (sum_range (pointwise_add f g) lo hi
         = sum_range f lo hi + sum_range g lo hi)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_range_add_lambda f g lo hi;
    let lam (k: nat) : t = f k + g k in
    let cm : nat -> t = pointwise_add f g in
    let prf (k: nat{lo <= k /\ k < hi}) : Lemma (cm k = lam k)
      = pointwise_add_unfold f g k;
        reflexivity (f k + g k)
    in
    sum_range_congruence cm lam lo hi prf;
    transitivity (sum_range cm lo hi)
                 (sum_range lam lo hi)
                 (sum_range f lo hi + sum_range g lo hi)

let sum_swap
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> nat -> t)
  (i_lo i_hi j_lo j_hi: nat)
  : Lemma (sum_range (sum_range_on f j_lo j_hi) i_lo i_hi
         = sum_range (sum_range_on (swap_args f) i_lo i_hi) j_lo j_hi)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_swap_lambda f i_lo i_hi j_lo j_hi;
    let lam_i (i: nat) : t = sum_range (f i) j_lo j_hi in
    let cm_i  (i: nat) : t = sum_range_on f j_lo j_hi i in
    let prf_i (i: nat{i_lo <= i /\ i < i_hi}) : Lemma (cm_i i = lam_i i)
      = reflexivity (sum_range (f i) j_lo j_hi)
    in
    sum_range_congruence cm_i lam_i i_lo i_hi prf_i;
    let lam_j (j: nat) : t = sum_range (fun i -> f i j) i_lo i_hi in
    let cm_j  (j: nat) : t = sum_range_on (swap_args f) i_lo i_hi j in
    let prf_j (j: nat{j_lo <= j /\ j < j_hi}) : Lemma (lam_j j = cm_j j)
      = let inner_lam (i: nat) : t = f i j in
        let inner_cm : nat -> t = swap_args f j in
        let inner_prf (i: nat{i_lo <= i /\ i < i_hi}) : Lemma (inner_lam i = inner_cm i)
          = swap_args_unfold f j i;
            reflexivity (f i j);
            symmetry (inner_cm i) (f i j)
        in
        sum_range_congruence inner_lam inner_cm i_lo i_hi inner_prf;
        assert (lam_j j == sum_range inner_lam i_lo i_hi);
        assert (cm_j j == sum_range inner_cm i_lo i_hi)
    in
    sum_range_congruence lam_j cm_j j_lo j_hi prf_j;
    trans3 (sum_range cm_i i_lo i_hi)
           (sum_range lam_i i_lo i_hi)
           (sum_range lam_j j_lo j_hi)
           (sum_range cm_j j_lo j_hi)

(* ---------------- fin_sum ---------------- *)

let fin_sum_mul_left
  (#t:Type) {| r: ring t |}
  (#n: nat) (c: t) (f: fin n -> t)
  : Lemma (c * fin_sum f = fin_sum (pointwise_mul (const c) f))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_mul_left_lambda c f;
    let prf (k: fin n) : Lemma ((fun (k: fin n) -> c * f k) k = pointwise_mul (const c) f k)
      = pointwise_mul_unfold (const c) f k;
        const_unfold c k;
        reflexivity (c * f k);
        symmetry (pointwise_mul (const c) f k) (c * f k)
    in
    fin_sum_congruence (fun (k: fin n) -> c * f k) (pointwise_mul (const c) f) prf;
    transitivity (c * fin_sum f)
                 (fin_sum (fun (k: fin n) -> c * f k))
                 (fin_sum (pointwise_mul (const c) f))

let fin_sum_mul_right
  (#t:Type) {| r: ring t |}
  (#n: nat) (f: fin n -> t) (c: t)
  : Lemma (fin_sum f * c = fin_sum (pointwise_mul f (const c)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_mul_right_lambda f c;
    let prf (k: fin n) : Lemma ((fun (k: fin n) -> f k * c) k = pointwise_mul f (const c) k)
      = pointwise_mul_unfold f (const c) k;
        const_unfold c k;
        reflexivity (f k * c);
        symmetry (pointwise_mul f (const c) k) (f k * c)
    in
    fin_sum_congruence (fun (k: fin n) -> f k * c) (pointwise_mul f (const c)) prf;
    transitivity (fin_sum f * c)
                 (fin_sum (fun (k: fin n) -> f k * c))
                 (fin_sum (pointwise_mul f (const c)))

let fin_sum_swap
  (#t:Type) {| m: add_comm_group t |}
  (#n: nat) (f: fin n -> fin n -> t)
  : Lemma (fin_sum (fin_sum_curry f)
         = fin_sum (fin_sum_curry (swap_args f)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_swap_lambda f;
    (* lambda post:
       fin_sum (fun i -> fin_sum (f i))
         = fin_sum (fun j -> fin_sum (fun i -> f i j))                       *)
    let prf_i (i: fin n) : Lemma (fin_sum_curry f i = (fun (i: fin n) -> fin_sum (f i)) i)
      = reflexivity (fin_sum (f i))
    in
    fin_sum_congruence (fin_sum_curry f) (fun (i: fin n) -> fin_sum (f i)) prf_i;
    let prf_j (j: fin n) : Lemma ((fun (j: fin n) -> fin_sum (fun i -> f i j)) j
                                 = fin_sum_curry (swap_args f) j)
      = let inner_prf (i: fin n) : Lemma ((fun (i: fin n) -> f i j) i = swap_args f j i)
          = swap_args_unfold f j i;
            reflexivity (f i j);
            symmetry (swap_args f j i) (f i j)
        in
        fin_sum_congruence (fun (i: fin n) -> f i j) (swap_args f j) inner_prf;
        (* gives: fin_sum (fun i -> f i j) = fin_sum (swap_args f j)         *)
        assert (fin_sum_curry (swap_args f) j == fin_sum (swap_args f j))
    in
    fin_sum_congruence (fun (j: fin n) -> fin_sum (fun i -> f i j))
                  (fin_sum_curry (swap_args f)) prf_j;
    trans3 (fin_sum (fin_sum_curry f))
           (fin_sum (fun (i: fin n) -> fin_sum (f i)))
           (fin_sum (fun (j: fin n) -> fin_sum (fun i -> f i j)))
           (fin_sum (fin_sum_curry (swap_args f)))

let fin_sum_const_zero
  (#t:Type) {| m: add_comm_group t |} (#n: nat)
  : Lemma (fin_sum #t #m #n (const zero) = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_const_zero_lambda #t #m #n;
    let prf (k: fin n) : Lemma (const #(fin n) #t (zero #t) k
                              = (fun (_: fin n) -> zero #t) k)
      = const_unfold (zero #t) k;
        reflexivity (zero #t)
    in
    fin_sum_congruence (const #(fin n) #t (zero #t))
                  (fun (_: fin n) -> zero #t) prf;
    transitivity (fin_sum #t #m #n (const zero))
                 (fin_sum #t #m #n (fun (_: fin n) -> zero #t))
                 (zero #t)

let fin_sum_add
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f g: fin n -> t)
  : Lemma (fin_sum (pointwise_add f g) = fin_sum f + fin_sum g)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_add_lambda f g;
    let prf (k: fin n) : Lemma (pointwise_add f g k = (fun (k: fin n) -> f k + g k) k)
      = pointwise_add_unfold f g k;
        reflexivity (f k + g k)
    in
    fin_sum_congruence (pointwise_add f g) (fun (k: fin n) -> f k + g k) prf;
    transitivity (fin_sum (pointwise_add f g))
                 (fin_sum (fun (k: fin n) -> f k + g k))
                 (fin_sum f + fin_sum g)

let sum_range_kronecker_legacy
  (#t:Type) {| r: ring t |}
  (i0: nat) (g: nat -> t) (lo hi: nat)
  : Lemma (sum_range (pointwise_mul (kronecker_delta i0) g) lo hi
         = (if lo <= i0 && i0 < hi then g i0 else zero #t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_range_kronecker_lambda i0 g lo hi;
    let lam (k: nat) : t = (if i0 = k then one else zero #t) * g k in
    let cm : nat -> t = pointwise_mul (kronecker_delta i0) g in
    let prf (k: nat{lo <= k /\ k < hi}) : Lemma (cm k = lam k)
      = pointwise_mul_unfold (kronecker_delta i0) g k;
        assert (kronecker_delta #t i0 k == (if i0 = k then one else zero #t));
        reflexivity ((if i0 = k then one else zero #t) * g k)
    in
    sum_range_congruence cm lam lo hi prf;
    transitivity (sum_range cm lo hi)
                 (sum_range lam lo hi)
                 (if lo <= i0 && i0 < hi then g i0 else zero #t)

let fin_sum_kronecker
  (#t:Type) {| r: ring t |}
  (#n: nat) (i0: fin n) (g: fin n -> t)
  : Lemma (fin_sum (pointwise_mul (fin_kronecker_delta i0) g) = g i0)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_kronecker_lambda i0 g;
    let prf (k: fin n) : Lemma
      (pointwise_mul (fin_kronecker_delta i0) g k
       = (fun (k: fin n) -> (if (i0 <: nat) = (k <: nat) then one else zero #t) * g k) k)
      = pointwise_mul_unfold #(fin n) #t (fin_kronecker_delta i0) g k;
        fin_kronecker_delta_unfold #t i0 k;
        assert (kronecker_delta #t (i0 <: nat) (k <: nat)
              == (if (i0 <: nat) = (k <: nat) then one else zero #t));
        reflexivity ((if (i0 <: nat) = (k <: nat) then one else zero #t) * g k);
        symmetry (pointwise_mul (fin_kronecker_delta i0) g k)
                 ((if (i0 <: nat) = (k <: nat) then one else zero #t) * g k)
    in
    fin_sum_congruence (pointwise_mul (fin_kronecker_delta i0) g)
                  (fun (k: fin n) -> (if (i0 <: nat) = (k <: nat) then one else zero #t) * g k)
                  prf;
    transitivity (fin_sum (pointwise_mul (fin_kronecker_delta i0) g))
                 (fin_sum (fun (k: fin n) -> (if (i0 <: nat) = (k <: nat) then one else zero #t) * g k))
                 (g i0)


(* ================================================================= *)
(*  H3 hygiene wrappers: callback-form public API mapping to the     *)
(*  legacy forall-form _forall impls above. Public fsti uses these.*)
(* ================================================================= *)

let prod_range_congruence
  (#t:Type) {| m: ring t |}
  (f g: nat -> t) (lo hi: nat)
  (h: (k:nat{lo <= k /\ k < hi}) -> Lemma (f k = g k))
  : Lemma (ensures prod_range f lo hi = prod_range g lo hi)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    let prf (k: nat) : Lemma (lo <= k /\ k < hi ==> f k = g k)
      = if lo <= k && k < hi then h k
    in
    Classical.forall_intro prf;
    prod_range_congruence_forall f g lo hi

let prod_range_swap_adjacent
  (#t:Type) {| m: commutative_ring t |}
  (f g: nat -> t) (lo hi: nat) (i: nat)
  (h: (k:nat{lo <= k /\ k < hi /\ k <> i /\ k <> nat_succ i}) -> Lemma (g k = f k))
  : Lemma (requires lo <= i /\ nat_succ i < hi /\
                    g i = f (nat_succ i) /\ g (nat_succ i) = f i)
          (ensures prod_range f lo hi = prod_range g lo hi)
  = elim_equatable_laws t ();
    let prf (k: nat) : Lemma (lo <= k /\ k < hi /\ k <> i /\ k <> nat_succ i ==> g k = f k)
      = if lo <= k && k < hi && k <> i && k <> nat_succ i then h k
    in
    Classical.forall_intro prf;
    prod_range_swap_adjacent_forall f g lo hi i

let prod_range_perm_invariance_fn
  (#t:Type) {| m: commutative_ring t |}
  (#n: nat) (f body_p body_id: nat -> t) (p: permutation n)
  (h_p: (k: nat{0 <= k /\ k < n}) -> Lemma (body_p k = f (p.fwd (k <: fin n))))
  (h_id: (k: nat{0 <= k /\ k < n}) -> Lemma (body_id k = f k))
  : Lemma (ensures prod_range body_p 0 n = prod_range body_id 0 n)
  = elim_equatable_laws t ();
    let prf_p (k: nat) : Lemma (0 <= k /\ k < n ==> body_p k = f (p.fwd (k <: fin n)))
      = if 0 <= k && k < n then h_p k
    in
    let prf_id (k: nat) : Lemma (0 <= k /\ k < n ==> body_id k = f k)
      = if 0 <= k && k < n then h_id k
    in
    Classical.forall_intro prf_p;
    Classical.forall_intro prf_id;
    prod_range_perm_invariance_fn_forall f body_p body_id p

let fin_sum_zero_ext
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f: fin n -> t)
  (h: (k: fin n) -> Lemma (f k = zero #t))
  : Lemma (ensures fin_sum f = zero #t)
  = elim_equatable_laws t ();
    let prf (k: fin n) : Lemma (f k = zero #t) = h k in
    Classical.forall_intro prf;
    fin_sum_zero_ext_forall f

let fin_sum_add_ext
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f g h: fin n -> t)
  (pf: (k: fin n) -> Lemma (h k = f k + g k))
  : Lemma (ensures fin_sum h = fin_sum f + fin_sum g)
  = elim_equatable_laws t ();
    let prf (k: fin n) : Lemma (h k = f k + g k) = pf k in
    Classical.forall_intro prf;
    fin_sum_add_ext_forall f g h

let sum_range_kronecker_in_range
  (#t:Type) {| r: ring t |}
  (i0: nat) (g: nat -> t) (lo hi: nat)
  : Lemma (requires lo <= i0 /\ i0 < hi)
          (ensures sum_range (pointwise_mul (kronecker_delta i0) g) lo hi = g i0)
  = sum_range_kronecker_legacy i0 g lo hi

let sum_range_kronecker_out_of_range
  (#t:Type) {| r: ring t |}
  (i0: nat) (g: nat -> t) (lo hi: nat)
  : Lemma (requires i0 < lo \/ i0 >= hi)
          (ensures sum_range (pointwise_mul (kronecker_delta i0) g) lo hi = zero #t)
  = sum_range_kronecker_legacy i0 g lo hi
