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

(* The `( ++ )` integer-addition operator lives in Core.Algebra.Notation;
   plain nat arithmetic is written `++` / `-` directly. *)

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
    add_associativity (- a) a b;
    add_associativity (- a) a c;
    zero_plus_x b;
    zero_plus_x c;
    add_congruence (- a) (a + b) (- a) (a + c);
    add_congruence ((- a) + a) b zero b;
    add_congruence ((- a) + a) c zero c

(* neg_of_sum now lives in Core.Algebra.Helpers. *)

(* ----------------------------------------------------------------- *)
(*  Sum over an integer range  [lo, hi)                              *)
(* ----------------------------------------------------------------- *)

let rec sum_range (#t:Type) {| m: add_comm_group t |}
                  (f: nat -> t) (lo hi: nat)
  : Tot t (decreases hi - lo)
  = if lo >= hi then zero
    else f lo + sum_range f (lo ++ 1) hi

let sum_range_empty (#t:Type) {| m: add_comm_group t |}
                    (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures sum_range f lo hi == zero)
  = ()

let sum_range_unfold_left (#t:Type) {| m: add_comm_group t |}
                          (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi == f lo + sum_range f (lo ++ 1) hi)
  = ()

let sum_range_singleton (#t:Type) {| m: add_comm_group t |}
                        (f: nat -> t) k
  : Lemma (sum_range f k (k ++ 1) = f k)
  = sum_range_unfold_left f k (k ++ 1);
    x_plus_zero (f k)

let rec sum_range_congruence_forall
  (#t:Type) {| m: add_comm_group t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires (forall k. lo <= k /\ k < hi ==> f k = g k))
          (ensures sum_range f lo hi = sum_range g lo hi)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    if lo >= hi then ()
    else begin
      sum_range_congruence_forall f g (lo ++ 1) hi;
      add_congruence (f lo) (sum_range f (lo ++ 1) hi)
                     (g lo) (sum_range g (lo ++ 1) hi)
    end

let rec sum_range_unfold_right
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures sum_range f lo hi = sum_range f lo (hi - 1) + f (hi - 1))
          (decreases hi - lo)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo ++ 1 = hi then begin
      sum_range_unfold_left f lo hi;
      x_plus_zero (f lo);
      zero_plus_x (f (hi - 1));
      symmetry (zero + f (hi - 1)) (f (hi - 1));
      add_congruence (sum_range f lo (hi - 1)) (f (hi - 1))
                     zero (f (hi - 1))
    end else begin
      sum_range_unfold_left f lo hi;
      sum_range_unfold_right f (lo ++ 1) hi;
      reflexivity (f lo);
      add_congruence (f lo) (sum_range f (lo ++ 1) hi)
                     (f lo) (sum_range f (lo ++ 1) (hi - 1) + f (hi - 1));
      add_associativity (f lo) (sum_range f (lo ++ 1) (hi - 1)) (f (hi - 1));
      sum_range_unfold_left f lo (hi - 1);
      symmetry (sum_range f lo (hi - 1))
               (f lo + sum_range f (lo ++ 1) (hi - 1));
      reflexivity (f (hi - 1));
      add_congruence (f lo + sum_range f (lo ++ 1) (hi - 1)) (f (hi - 1))
                     (sum_range f lo (hi - 1)) (f (hi - 1))
    end

let rec sum_range_split (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo mid hi: nat)
  : Lemma (requires lo <= mid /\ mid <= hi)
          (ensures sum_range f lo hi = sum_range f lo mid + sum_range f mid hi)
          (decreases (mid - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo = mid then begin
      add_congruence (sum_range f lo mid) (sum_range f mid hi)
                     zero (sum_range f mid hi);
      zero_plus_x (sum_range f mid hi)
    end else begin
      sum_range_split f (lo ++ 1) mid hi;
      add_congruence (f lo) (sum_range f (lo ++ 1) hi)
                     (f lo) (sum_range f (lo ++ 1) mid + sum_range f mid hi);
      add_associativity (f lo) (sum_range f (lo ++ 1) mid) (sum_range f mid hi);
      add_congruence (f lo + sum_range f (lo ++ 1) mid) (sum_range f mid hi)
                     (sum_range f lo mid) (sum_range f mid hi)      
    end

let rec sum_range_shift (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (offset lo hi: nat)
  : Lemma (ensures sum_range (fun j -> f (j ++ offset)) lo hi
                 = sum_range f (lo ++ offset) (hi ++ offset))
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo < hi then begin
      sum_range_shift f offset (lo ++ 1) hi;
      add_congruence (f (lo ++ offset))
                     (sum_range (fun j -> f (j ++ offset)) (lo ++ 1) hi)
                     (f (lo ++ offset))
                     (sum_range f (lo ++ 1 ++ offset) (hi ++ offset))
    end

let rec sum_range_reverse (#t:Type) {| m: add_comm_group t |}
  (f: int -> t) (n: nat)
  : Lemma (ensures sum_range (fun j -> f (n - 1 - j)) 0 n
                 = sum_range f 0 n)
          (decreases n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let g : nat -> t = fun j -> f (n - 1 - j) in
    if n = 0 then begin
      sum_range_empty g 0 0;
      sum_range_empty f 0 0
    end else begin
      let n1 = n - 1 in
      sum_range_unfold_left g 0 n;
      sum_range_shift g 1 0 n1;
      let h : nat -> t = fun j -> f (n1 - 1 - j) in
      sum_range_congruence_forall
        (fun j -> g (j ++ 1)) h 0 n1;
      sum_range_reverse f n1;
      trans3 (sum_range g 1 n)
             (sum_range (fun j -> g (j ++ 1)) 0 n1)
             (sum_range h 0 n1)
             (sum_range f 0 n1);
      add_congruence (f n1) (sum_range g 1 n)
                     (f n1) (sum_range f 0 n1);
      add_commutativity (f n1) (sum_range f 0 n1);
      sum_range_unfold_right f 0 n
    end

let rec sum_range_all_zero (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  (h: (k: nat{lo <= k /\ k < hi}) -> Lemma (f k = zero))
  : Lemma (ensures sum_range f lo hi = zero)
          (decreases (hi - lo))
  = elim_equatable_laws t();
    trans_for_calc t ();
    if lo < hi then begin      
      sum_range_unfold_left f lo hi;
      h lo;
      sum_range_all_zero f (lo ++ 1) hi h;
      add_congruence (f lo) (sum_range f (lo ++ 1) hi)
                     zero zero;
      zero_plus_x #t zero
    end

(* ----------------------------------------------------------------- *)
(*  Product over an integer range  [lo, hi)                          *)
(* ----------------------------------------------------------------- *)

let rec prod_range (#t:Type) {| m: ring t |}
                   (f: nat -> t) (lo hi: nat)
  : Tot t (decreases hi - lo)
  = if lo >= hi then one
    else f lo * prod_range f (lo ++ 1) hi

let prod_range_empty (#t:Type) {| m: ring t |}
                     (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo >= hi)
          (ensures prod_range f lo hi == one)
  = ()

let prod_range_unfold_left (#t:Type) {| m: ring t |}
                           (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi == f lo * prod_range f (lo ++ 1) hi)
  = ()

let prod_range_singleton (#t:Type) {| m: ring t |}
                         (f: nat -> t) k
  : Lemma (prod_range f k (k ++ 1) = f k)
  = x_mul_one (f k)

let rec prod_range_congruence_forall
  (#t:Type) {| m: ring t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires (forall (k:nat). lo <= k /\ k < hi ==> f k = g k))
          (ensures prod_range f lo hi = prod_range g lo hi)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    if lo < hi then begin
      prod_range_congruence_forall f g (lo ++ 1) hi;
      mul_congruence (f lo) (prod_range f (lo ++ 1) hi)
                     (g lo) (prod_range g (lo ++ 1) hi)
    end

let rec prod_range_unfold_right
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (requires lo < hi)
          (ensures prod_range f lo hi = prod_range f lo (hi - 1) * f (hi - 1))
          (decreases hi - lo)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    mul_one (f lo);
    if lo ++ 1 < hi then begin
      prod_range_unfold_right f (lo ++ 1) hi;
      mul_congruence (f lo) (prod_range f (lo ++ 1) hi)
                     (f lo) (prod_range f (lo ++ 1) (hi - 1) * f (hi - 1));
      mul_associativity (f lo) (prod_range f (lo ++ 1) (hi - 1)) (f (hi - 1));
      mul_congruence (f lo * prod_range f (lo ++ 1) (hi - 1)) (f (hi - 1))
                     (prod_range f lo (hi - 1)) (f (hi - 1))
    end

let rec prod_range_split
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (lo mid hi: nat)
  : Lemma (requires lo <= mid /\ mid <= hi)
          (ensures prod_range f lo hi =
                   prod_range f lo mid * prod_range f mid hi)
          (decreases hi - lo)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    mul_one (prod_range f mid hi);
    if lo < mid then begin
      prod_range_unfold_left f lo hi;
      prod_range_unfold_left f lo mid;
      prod_range_split f (lo ++ 1) mid hi;
      mul_congruence (f lo) (prod_range f (lo ++ 1) hi)
                     (f lo) (prod_range f (lo ++ 1) mid * prod_range f mid hi);
      mul_associativity (f lo) (prod_range f (lo ++ 1) mid) (prod_range f mid hi);
      mul_congruence (f lo * prod_range f (lo ++ 1) mid) (prod_range f mid hi)
                     (prod_range f lo mid) (prod_range f mid hi)
    end

let prod_range_two_step
  (#t:Type) {| m: ring t |}
  (f: nat -> t) (i: nat)
  : Lemma (prod_range f i (i ++ 1 ++ 1) = f i * f (i ++ 1))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    prod_range_unfold_left f i (i ++ 1 ++ 1);
    prod_range_singleton f (i ++ 1);
    mul_congruence (f i) (prod_range f (i ++ 1) (i ++ 2))
                   (f i) (f (i ++ 1))

let prod_range_swap_adjacent_forall
  (#t:Type) {| m: commutative_ring t |}
  (f g: nat -> t) (lo hi: nat) (i: nat)
  : Lemma (requires lo <= i /\ i ++ 1 < hi /\
                    g i = f (i ++ 1) /\ g (i ++ 1) = f i /\
                    (forall k. lo <= k /\ k < hi /\ k <> i /\ k <> i ++ 1 ==> g k = f k))
          (ensures prod_range f lo hi = prod_range g lo hi)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let i2 = i ++ 2 in
    prod_range_split f lo i hi;
    prod_range_split f i i2 hi;
    prod_range_split g lo i hi;
    prod_range_split g i i2 hi;
    prod_range_congruence_forall f g lo i;
    prod_range_congruence_forall f g i2 hi;
    prod_range_two_step f i;
    prod_range_two_step g i;
    mul_commutativity (f (i ++ 1)) (f i);
    let lp = prod_range f lo i in
    let rp = prod_range f i2 hi in
    let lp_g = prod_range g lo i in
    let rp_g = prod_range g i2 hi in
    mul_congruence (prod_range f i i2) rp (f i * f (i ++ 1)) rp;
    mul_congruence (prod_range g i i2) rp_g (g i * g (i ++ 1)) rp_g;
    mul_congruence (g i) (g (i ++ 1)) (f (i ++ 1)) (f i);
    mul_congruence (g i * g (i ++ 1)) rp_g (f (i ++ 1) * f i) rp_g;
    mul_congruence lp (prod_range f i hi) lp ((f i * f (i ++ 1)) * rp);
    mul_congruence (f i * f (i ++ 1)) rp (f (i ++ 1) * f i) rp_g;
    mul_congruence lp ((f i * f (i ++ 1)) * rp) lp_g ((f (i ++ 1) * f i) * rp_g);
    mul_congruence lp_g ((f (i ++ 1) * f i) * rp_g) lp_g (prod_range g i hi)
  

let rec prod_range_perm_invariance
  (#t:Type) {| m: commutative_ring t |}
  (#n: nat) (f: nat -> t) (p: permutation n)
  : Lemma (ensures
            prod_range (fun k ->
              if k < n then f (p.fwd k) else one) 0 n
          = prod_range (fun k ->
              if k < n then f k else one) 0 n)
          (decreases (inversion_count p))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let body_p : nat -> t =
      fun k -> if k < n then f (p.fwd k) else one in
    let body_id : nat -> t =
      fun k -> if k < n then f k else one in
    perm_descent_exists_or_inv_zero p;
    eliminate (inversion_count p == 0) \/
              (exists (i: nat{i ++ 1 < n}).
                 inversion_count (right_swap p i) < inversion_count p)
    returns prod_range body_p 0 n = prod_range body_id 0 n
    with _.
      begin
        let body_eq_aux k : Lemma (0 <= k /\ k < n ==> body_p k = body_id k)
          = if 0 <= k && k < n then begin
              inv_zero_implies_identity_fwd p k
            end
        in Classical.forall_intro body_eq_aux;
        prod_range_congruence_forall body_p body_id 0 n
      end
    and _.
      begin
        eliminate exists i. inversion_count (right_swap p i) < inversion_count p
        returns prod_range body_p 0 n = prod_range body_id 0 n
        with _.
          begin
            let q = right_swap p i in 
            let body_q : nat -> t =
              fun k -> if k < n then f (q.fwd k) else one in
            right_swap_fwd_at_i_plus_1 p i;
            right_swap_fwd_at_i p i;                       
            let swap_aux_off k
              : Lemma (0 <= k /\ k < n /\ k <> i /\ k <> i ++ 1 ==> body_q k = body_p k)
              = if 0 <= k && k < n && k <> i && k <> i ++ 1 
                then right_swap_fwd_at_other p i k
            in
            Classical.forall_intro swap_aux_off;
            prod_range_swap_adjacent_forall body_q body_p 0 n i;
            prod_range_perm_invariance f q
          end
      end

let prod_range_perm_invariance_fn_forall
  (#t:Type) {| m: commutative_ring t |}
  (#n: nat) (f body_p body_id: nat -> t) (p: permutation n)
  : Lemma (requires
            (forall k. 0 <= k /\ k < n ==> body_p k = f (p.fwd k)) /\
            (forall k. 0 <= k /\ k < n ==> body_id k = f k))
          (ensures prod_range body_p 0 n = prod_range body_id 0 n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    prod_range_perm_invariance f p;    
    prod_range_congruence_forall body_p
      (fun k -> if k < n then f (p.fwd k) else one) 0 n;    
    prod_range_congruence_forall
      (fun k -> if k < n then f k else one) body_id 0 n

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

let rec sum_list_map_congruence_forall
  (#a:Type) (#t:Type) {| m: add_comm_group t |}
  (f g: a -> t) (xs: list a)
  : Lemma (requires (forall (x:a). memP x xs ==> f x = g x))
          (ensures sum_list (map f xs) = sum_list (map g xs))
  = elim_equatable_laws t ();
    match xs with
    | [] -> ()
    | x :: rest ->
      sum_list_map_congruence_forall f g rest;
      add_congruence (f x) (sum_list (map f rest))
                     (g x) (sum_list (map g rest))

private let rec sum_list_map_neg_lambda
  (#a:Type) (#t:Type) {| g: add_comm_group t |}
  (f: a -> t) (xs: list a)
  : Lemma (ensures sum_list (map (pointwise_neg f) xs) = neg (sum_list (map f xs)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] -> neg_zero #t ()
    | hx :: rest ->
      sum_list_map_neg_lambda f rest;
      let h = f hx in
      let trest = sum_list (map f rest) in
      let nrest = sum_list (map (pointwise_neg f) rest) in
      add_congruence (neg h) nrest (neg h) (neg trest);
      add_commutativity (neg h) (neg trest);
      neg_of_sum h trest


private let rec sum_list_map_add_lambda
  (#a:Type) (#t:Type) {| m: add_comm_group t |}
  (f g: a -> t) (xs: list a)
  : Lemma (ensures sum_list (map (pointwise_add f g) xs)
                 = sum_list (map f xs) + sum_list (map g xs))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    Classical.forall_intro_3 #t add_associativity;
    match xs with
    | [] -> add_zero #t zero    
    | hx :: rest ->
      sum_list_map_add_lambda f g rest;      
      let a1 = f hx in
      let b1 = g hx in
      let sf = sum_list (map f rest) in
      let sg = sum_list (map g rest) in
      let sh = sum_list (map (pointwise_add f g) rest) in      
      add_commutativity b1 sf;
      add_congruence (a1 + b1) sh (a1 + b1) (sf + sg);     
      add_congruence a1 (b1 + sf) a1 (sf + b1);
      add_congruence ((a1 + b1) + sf) sg ((a1 + sf) + b1) sg
      

(* ----------------------------------------------------------------- *)
(*  Algebraic identities involving sums (ring)                   *)
(* ----------------------------------------------------------------- *)

private let rec sum_list_map_mul_left_lambda
  (#a:Type) (#t:Type) {| r: ring t |}
  (c: t) (f: a -> t) (xs: list a)
  : Lemma (ensures c * sum_list (map f xs) = sum_list (map (pointwise_mul (const c) f) xs))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] -> x_mul_zero c
    | hx :: rest ->
      sum_list_map_mul_left_lambda c f rest;      
      let h = f hx in
      let trest = sum_list (map f rest) in
      let crest = sum_list (map (pointwise_mul (const c) f) rest) in
      left_distributivity c h trest;
      add_congruence (c * h) (c * trest) (c * h) crest

private let rec sum_range_const_zero_lambda
  (t:Type) {| m: add_comm_group t |}
  (lo hi: nat)
  : Lemma (ensures sum_range #t (const zero) lo hi = zero)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo < hi then begin
      sum_range_const_zero_lambda t (lo ++ 1) hi;
      add_congruence zero (sum_range #t (const zero) (lo ++ 1) hi)
                     zero zero;
      zero_plus_x #t zero
    end

private let rec sum_range_mul_left_lambda
  (#t:Type) {| r: ring t |}
  (c: t) (f: nat -> t) (lo hi: nat)
  : Lemma (ensures c * sum_range f lo hi = sum_range (pointwise_mul (const c) f) lo hi)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    x_mul_zero c;
    if lo < hi then begin
      let s1 = c * sum_range f lo hi in
      let s2 = c * (f lo + sum_range f (lo ++ 1) hi) in
      left_distributivity c (f lo) (sum_range f (lo ++ 1) hi);
      sum_range_mul_left_lambda c f (lo ++ 1) hi;
      add_congruence (c * f lo) (c * sum_range f (lo ++ 1) hi)
                     (c * f lo) (sum_range (pointwise_mul (const c) f) (lo ++ 1) hi)      
    end


private let rec sum_range_mul_right_lambda
  (#t:Type) {| r: ring t |}
  (f: nat -> t) (c: t) (lo hi: nat)
  : Lemma (ensures sum_range f lo hi * c = sum_range (pointwise_mul f (const c)) lo hi)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    zero_mul_x c;
    if lo < hi then begin
      let s1 = sum_range f lo hi * c in
      let s2 = (f lo + sum_range f (lo ++ 1) hi) * c in
      right_distributivity c (f lo) (sum_range f (lo ++ 1) hi);
      sum_range_mul_right_lambda f c (lo ++ 1) hi;
      add_congruence (f lo * c) (sum_range f (lo ++ 1) hi * c)
                     (f lo * c) (sum_range (pointwise_mul f (const c)) (lo ++ 1) hi)
    end


private let rec sum_range_add_lambda
  (#t:Type) {| m: add_comm_group t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (pointwise_add f g) lo hi
                  = sum_range f lo hi + sum_range g lo hi)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    Classical.forall_intro_3 m.add_associativity;
    zero_plus_x #t zero;
    if lo < hi then begin
      let fl = f lo in 
      let gl = g lo in
      let fa = sum_range f (lo ++ 1) hi in
      let ga = sum_range g (lo ++ 1) hi in
      sum_range_add_lambda f g (lo ++ 1) hi;
      add_congruence (fl + gl) (sum_range (pointwise_add f g) (lo ++ 1) hi)
                     (fl + gl) (fa + ga);
      add_commutativity gl fa;
      add_congruence (gl + fa) ga (fa + gl) ga;
      add_congruence fl (gl + (fa + ga)) fl (fa + (gl + ga))
    end

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
      sum_range_empty (fun i -> sum_range (f i) j_lo j_hi) i_lo i_hi;
      let inner_fn j : t = sum_range (fun i -> f i j) i_lo i_hi in     
      sum_range_congruence_forall inner_fn (const zero) j_lo j_hi;
      sum_range_const_zero_lambda t j_lo j_hi      
    end else begin
      sum_swap_aux_lambda f (i_lo ++ 1) i_hi j_lo j_hi;
      let gfn j : t = sum_range (fun i -> f i j) (i_lo ++ 1) i_hi in
      add_congruence (sum_range (f i_lo) j_lo j_hi)
                     (sum_range (fun i -> sum_range (f i) j_lo j_hi) (i_lo ++ 1) i_hi)
                     (sum_range (f i_lo) j_lo j_hi)
                     (sum_range gfn j_lo j_hi);
      sum_range_add_lambda (f i_lo) gfn j_lo j_hi;
      let rhs_inner (j: nat) : t = sum_range (fun i -> f i j) i_lo i_hi in      
      sum_range_congruence_forall (pointwise_add (f i_lo) gfn) rhs_inner j_lo j_hi
    end

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

(* Bridge: fin_sum f is sum_range over the zero-padded lift fin_lift f.
   fin_sum unfolds to sum_range over the inline if-then-else lambda; this
   lemma relates that to the named combinator fin_lift, so downstream
   lemmas can state/manipulate things in terms of fin_lift. *)
private let fin_sum_as_fin_lift
  (#t:Type) {| m: add_comm_group t |}
  (#n: nat) (f: fin n -> t)
  : Lemma (fin_sum f = sum_range (fin_lift f) 0 n)
  = elim_equatable_laws t ();
    let lam (k:nat) : t = if k < n then f k else zero in
    let pf k : Lemma (0 <= k /\ k < n ==> lam k = fin_lift f k)
      = if 0 <= k && k < n then fin_lift_in_range f k
    in Classical.forall_intro pf;
    sum_range_congruence_forall lam (fin_lift f) 0 n

let fin_sum_congruence_forall
  (#t:Type) {| m: add_comm_group t |}
  (#n: nat) (f g: fin n -> t)
  : Lemma (requires (forall k. f k = g k))
          (ensures fin_sum f = fin_sum g)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_as_fin_lift f;
    fin_sum_as_fin_lift g;
    let pf k : Lemma (0 <= k /\ k < n ==> fin_lift f k = fin_lift g k)
      = if 0 <= k && k < n then begin
          fin_lift_in_range f k;
          fin_lift_in_range g k
        end
    in
    Classical.forall_intro pf;
    sum_range_congruence_forall (fin_lift f) (fin_lift g) 0 n

private let fin_sum_mul_left_lambda
  (#t:Type) {| r: ring t |}
  (#n: nat) (c: t) (f: fin n -> t)
  : Lemma (c * fin_sum f = fin_sum (fun (k: fin n) -> c * f k))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_as_fin_lift f;
    mul_congruence c (fin_sum f) c (sum_range (fin_lift f) 0 n);
    sum_range_mul_left_lambda c (fin_lift f) 0 n;    
    sum_range_congruence_forall
      (pointwise_mul (const c) (fin_lift f))
      (fun k -> if k < n then c * f k else zero)
      0 n

private let fin_sum_mul_right_lambda
  (#t:Type) {| r: ring t |}
  (#n: nat) (f: fin n -> t) (c: t)
  : Lemma (fin_sum f * c = fin_sum (fun (k: fin n) -> f k * c))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_as_fin_lift f;
    mul_congruence (fin_sum f) c (sum_range (fin_lift f) 0 n) c;
    sum_range_mul_right_lambda (fin_lift f) c 0 n;
    sum_range_congruence_forall
      (pointwise_mul (fin_lift f) (const c))
      (fun k -> if k < n then f k * c else zero)
      0 n

(* fin_swap_body is a private helper used by fin_sum_swap_lambda. *)
unfold
private let fin_swap_body (#t:Type) {| m: add_comm_group t |}
    (#n: nat) (f: fin n -> fin n -> t) (i j: nat) : t
  = if i < n && j < n then f i j else zero

private let fin_sum_swap_lambda
  (#t:Type) {| m: add_comm_group t |}
  (#n: nat) (f: fin n -> fin n -> t)
  : Lemma (fin_sum (fun i -> fin_sum (f i))
         = fin_sum (fun j -> fin_sum (fun i -> f i j)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let outer_lhs (i: nat) : t
      = if i < n then fin_sum (f i) else zero in
    let outer_lhs_open (i: nat) : t
      = sum_range (fun (j: nat) -> if i < n && j < n then f i j else zero) 0 n in
    let pf1 i : Lemma (0 <= i /\ i < n ==> outer_lhs i = outer_lhs_open i)
      = if 0 <= i && i < n then begin
          let inner_a (j: nat) : t = if j < n then f i j else zero in
          let inner_b (j: nat) : t = if i < n && j < n then f i j else zero in         
          sum_range_congruence_forall inner_a inner_b 0 n
        end
    in
    Classical.forall_intro pf1;
    sum_range_congruence_forall outer_lhs outer_lhs_open 0 n;
    let outer_rhs (j: nat) : t
      = if j < n then fin_sum (fun i -> f i j) else zero in
    let outer_rhs_open (j: nat) : t
      = sum_range (fun i -> if i < n && j < n then f i j else zero) 0 n in
    let pf2 j : Lemma (0 <= j /\ j < n ==> outer_rhs j = outer_rhs_open j)
      = if 0 <= j && j < n then begin
          let inner_a (i: nat) : t = if i < n then f i j else zero in
          let inner_b (i: nat) : t = if i < n && j < n then f i j else zero in         
          sum_range_congruence_forall inner_a inner_b 0 n
        end
    in
    Classical.forall_intro pf2;
    sum_range_congruence_forall outer_rhs outer_rhs_open 0 n;
    sum_swap_lambda (fin_swap_body f) 0 n 0 n;    
    sum_range_congruence_forall
      (fun (i: nat) -> sum_range (fin_swap_body f i) 0 n) outer_lhs_open 0 n;
    sum_range_congruence_forall
      (fun (j: nat) -> sum_range (fun (i: nat) -> fin_swap_body f i j) 0 n)
      outer_rhs_open 0 n

(* ----------------------------------------------------------------- *)
(*  Additional helpers needed by the matrix ring + determinant       *)
(* ----------------------------------------------------------------- *)

private let fin_sum_const_zero_lambda
  (#t:Type) {| m: add_comm_group t |} (#n: nat)
  : Lemma (fin_sum #t #m #n (fun (_: fin n) -> zero) = zero)
  = elim_equatable_laws t ();
    trans_for_calc t();
    let lhs_open (k:nat) : t = if k < n then (fun _ -> zero) k else zero in    
    sum_range_congruence_forall lhs_open (const zero) 0 n;
    sum_range_const_zero_lambda t 0 n
    
let fin_sum_zero_ext_forall
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f: fin n -> t)
  : Lemma (requires (forall (k: fin n). f k = zero))
          (ensures fin_sum f = zero)
  = elim_equatable_laws t ();    
    trans_for_calc t();
    fin_sum_congruence_forall f (fun (_: fin n) -> zero);
    fin_sum_const_zero_lambda #t #m #n

private let fin_sum_add_lambda
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f g: fin n -> t)
  : Lemma (fin_sum (fun (k: fin n) -> f k + g k)
        = fin_sum f + fin_sum g)
  = elim_equatable_laws t ();
    trans_for_calc t();
    fin_sum_as_fin_lift f;
    fin_sum_as_fin_lift g;
    let sopen (k:nat) : t = if k < n then f k + g k else zero in
    let pf k : Lemma (0 <= k /\ k < n ==> sopen k = pointwise_add (fin_lift f) (fin_lift g) k)
      = pointwise_add_unfold (fin_lift f) (fin_lift g) k;
        if k < n then begin
          fin_lift_in_range f k;
          fin_lift_in_range g k
        end
        else zero_plus_x (zero #t)
    in
    Classical.forall_intro pf;
    sum_range_congruence_forall sopen (pointwise_add (fin_lift f) (fin_lift g)) 0 n;
    sum_range_add_lambda (fin_lift f) (fin_lift g) 0 n;
    add_congruence (sum_range (fin_lift f) 0 n) (sum_range (fin_lift g) 0 n)
                   (fin_sum f) (fin_sum g)

let fin_sum_add_ext_forall
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f g h: fin n -> t)
  : Lemma (requires (forall (k: fin n). h k = f k + g k))
          (ensures fin_sum h = fin_sum f + fin_sum g)
  = elim_equatable_laws t ();
    trans_for_calc t();
    fin_sum_add_lambda f g;
    fin_sum_congruence_forall h (fun (k: fin n) -> f k + g k)

private let rec sum_range_kronecker_lambda
  (#t:Type) {| r: ring t |}
  (i0: nat) (g: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (pointwise_mul (kronecker_delta i0) g) lo hi
                 = (if lo <= i0 && i0 < hi then g i0 else zero))
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let body : nat -> t = pointwise_mul (kronecker_delta i0) g in
    if lo < hi then begin      
      sum_range_kronecker_lambda i0 g (lo ++ 1) hi;
      let tail = sum_range body (lo ++ 1) hi in
      let head = body lo in
      let lhs = sum_range body lo hi in
      if i0 = lo then begin
        kronecker_delta_eq #t i0 lo;
        one_mul_x (g lo);
        x_plus_zero (g lo);
        add_congruence head tail (g lo) zero
      end else begin
        kronecker_delta_neq #t i0 lo;
        zero_mul_x (g lo);
        zero_plus_x tail;
        add_congruence head tail zero tail
      end
    end

private let fin_sum_kronecker_lambda
  (#t:Type) {| r: ring t |}
  (#n: nat) (i0: fin n) (g: fin n -> t)
  : Lemma (fin_sum (pointwise_mul (fin_kronecker_delta i0) g) = g i0)
  = elim_equatable_laws t ();
    trans_for_calc t();
    let g_open (k:nat) : t = if k < n then g k else zero in
    let body_open (k:nat) : t
      = if k < n
        then pointwise_mul (fin_kronecker_delta i0) g k
        else zero in
    let kron_body : nat -> t = pointwise_mul (kronecker_delta i0) g_open in    
    sum_range_congruence_forall body_open kron_body 0 n;
    sum_range_kronecker_lambda i0 g_open 0 n

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
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] -> ()
    | x :: rest ->
        h x;
        sum_list_map_congruence f g rest h;
        sum_list_cons (f x) (map f rest);
        sum_list_cons (g x) (map g rest);
        add_congruence (f x) (sum_list (map f rest)) (g x) (sum_list (map g rest))

let sum_range_congruence
  (#t:Type) {| m: add_comm_group t |}
  (f g: nat -> t) (lo hi: nat)
  (h: (k: nat{lo <= k /\ k < hi}) -> Lemma (f k = g k))
  : Lemma (sum_range f lo hi = sum_range g lo hi)
  = Classical.forall_intro h;    
    sum_range_congruence_forall f g lo hi

let fin_sum_congruence
  (#t:Type) {| m: add_comm_group t |}
  (#n: nat) (f g: fin n -> t)
  (h: (k:fin n) -> Lemma (f k = g k))
  : Lemma (fin_sum f = fin_sum g)
  = Classical.forall_intro h;
    fin_sum_congruence_forall f g

let fin_prod_congruence_forall
  (#t:Type) {| r: ring t |}
  (#n: nat) (f g: fin n -> t)
  : Lemma (requires (forall (k: fin n). f k = g k))
          (ensures fin_prod f = fin_prod g)
  = prod_range_congruence_forall
      (fun k -> if k < n then f k else one)
      (fun k -> if k < n then g k else one)
      0 n

let fin_prod_congruence
  (#t:Type) {| r: ring t |}
  (#n: nat) (f g: fin n -> t)
  (h: (k:fin n) -> Lemma (f k = g k))
  : Lemma (fin_prod f = fin_prod g)
  = Classical.forall_intro h;
    fin_prod_congruence_forall f g

(* ---------- Propositional-equality congruences ---------- *)

let rec sum_range_eq_pointwise #t {| acg:add_comm_group t |} (f g: nat -> t) (from: nat) (to: nat{from < to})
  : Lemma (requires (forall (k: nat{k >= from /\ k < to}). f k == g k))
          (ensures sum_range f from to == sum_range g from to)
          (decreases (to - from)) =
  if (from < to - 1) then sum_range_eq_pointwise f g (from ++ 1) to
  

let fin_sum_eq_pointwise #t {| acg:add_comm_group t |} (#n:pos) (f g: fin n -> t)
  : Lemma (requires (forall (k: fin n). f k == g k))
          (ensures fin_sum f == fin_sum g) =
  let inl_f (k:nat) = if k < n then f k else zero in
  let inl_g (k:nat) = if k < n then g k else zero in
  (* fin_sum f == sum_range (fin_lift f) 0 n, propositionally, via the
     fin_lift_in_range reveal (which is stated with ==). *)
  let pf_f (k:nat{k >= 0 /\ k < n}) : Lemma (inl_f k == fin_lift f k)
    = fin_lift_in_range f k in
  Classical.forall_intro pf_f;
  sum_range_eq_pointwise inl_f (fin_lift f) 0 n;
  let pf_g (k:nat{k >= 0 /\ k < n}) : Lemma (inl_g k == fin_lift g k)
    = fin_lift_in_range g k in
  Classical.forall_intro pf_g;
  sum_range_eq_pointwise inl_g (fin_lift g) 0 n;
  let pf_fg (k:nat{k >= 0 /\ k < n}) : Lemma (fin_lift f k == fin_lift g k)
    = fin_lift_in_range f k; fin_lift_in_range g k in
  Classical.forall_intro pf_fg;
  sum_range_eq_pointwise (fin_lift f) (fin_lift g) 0 n

(* ---------------- sum_list / map ---------------- *)

let sum_list_map_neg
  (#a:Type) (#t:Type) {| g: add_comm_group t |}
  (f: a -> t) (xs: list a)
  : Lemma (sum_list (map (pointwise_neg f) xs) = neg (sum_list (map f xs)))
  = sum_list_map_neg_lambda f xs

let sum_list_map_add
  (#a:Type) (#t:Type) {| m: add_comm_group t |}
  (f g: a -> t) (xs: list a)
  : Lemma (sum_list (map (pointwise_add f g) xs)
         = sum_list (map f xs) + sum_list (map g xs))
  = sum_list_map_add_lambda f g xs

let sum_list_map_mul_left
  (#a:Type) (#t:Type) {| r: ring t |}
  (c: t) (f: a -> t) (xs: list a)
  : Lemma (c * sum_list (map f xs)
         = sum_list (map (pointwise_mul (const c) f) xs))
  = sum_list_map_mul_left_lambda c f xs

private let rec sum_list_map_mul_right_lambda
  (#a:Type) (#t:Type) {| r: ring t |}
  (f: a -> t) (c: t) (xs: list a)
  : Lemma (ensures sum_list (map f xs) * c = sum_list (map (pointwise_mul f (const c)) xs))
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    zero_mul_x c;
    match xs with
    | [] -> ()
    | hx :: rest ->
        sum_list_map_mul_right_lambda f c rest;
        let h = f hx in
        let trest = sum_list (map f rest) in
        let crest = sum_list (map (pointwise_mul f (const c)) rest) in
        right_distributivity c h trest;
        add_congruence (h * c) (trest * c) (h * c) crest

let sum_list_map_mul_right
  (#a:Type) (#t:Type) {| r: ring t |}
  (f: a -> t) (c: t) (xs: list a)
  : Lemma (sum_list (map f xs) * c
         = sum_list (map (pointwise_mul f (const c)) xs))
  = sum_list_map_mul_right_lambda f c xs

(* ---------------- sum_range ---------------- *)

let sum_range_const_zero
  (#t:Type) {| m: add_comm_group t |}
  (lo hi: nat)
  : Lemma (sum_range (const zero) lo hi = zero #t)
  = sum_range_const_zero_lambda t lo hi

let sum_range_mul_left
  (#t:Type) {| r: ring t |}
  (c: t) (f: nat -> t) (lo hi: nat)
  : Lemma (c * sum_range f lo hi
         = sum_range (pointwise_mul (const c) f) lo hi)
  = sum_range_mul_left_lambda c f lo hi

let sum_range_mul_right
  (#t:Type) {| r: ring t |}
  (f: nat -> t) (c: t) (lo hi: nat)
  : Lemma (sum_range f lo hi * c
         = sum_range (pointwise_mul f (const c)) lo hi)
  = sum_range_mul_right_lambda f c lo hi

let sum_range_add
  (#t:Type) {| m: add_comm_group t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (sum_range (pointwise_add f g) lo hi
         = sum_range f lo hi + sum_range g lo hi)
  = sum_range_add_lambda f g lo hi

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
    sum_range_congruence cm_i lam_i i_lo i_hi obvious;
    let lam_j (j: nat) : t = sum_range (fun i -> f i j) i_lo i_hi in
    let cm_j  (j: nat) : t = sum_range_on (swap_args f) i_lo i_hi j in
    let prf_j (j: nat{j_lo <= j /\ j < j_hi}) : Lemma (lam_j j = cm_j j)
      = let inner_lam (i: nat) : t = f i j in
        let inner_cm : nat -> t = swap_args f j in        
        sum_range_congruence inner_lam inner_cm i_lo i_hi obvious
    in
    sum_range_congruence lam_j cm_j j_lo j_hi prf_j

(* ---------------- fin_sum ---------------- *)

let fin_sum_mul_left
  (#t:Type) {| r: ring t |}
  (#n: nat) (c: t) (f: fin n -> t)
  : Lemma (c * fin_sum f = fin_sum (pointwise_mul (const c) f))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_mul_left_lambda c f;
    fin_sum_congruence (fun (k: fin n) -> c * f k) (pointwise_mul (const c) f) obvious

let fin_sum_mul_right
  (#t:Type) {| r: ring t |}
  (#n: nat) (f: fin n -> t) (c: t)
  : Lemma (fin_sum f * c = fin_sum (pointwise_mul f (const c)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_mul_right_lambda f c;    
    fin_sum_congruence (fun (k: fin n) -> f k * c) (pointwise_mul f (const c)) obvious

let fin_sum_swap
  (#t:Type) {| m: add_comm_group t |}
  (#n: nat) (f: fin n -> fin n -> t)
  : Lemma (fin_sum (fin_sum_curry f)
         = fin_sum (fin_sum_curry (swap_args f)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_swap_lambda f;
    let prf_j (j: fin n) : Lemma ((fun (j: fin n) -> fin_sum (fun i -> f i j)) j
                                 = fin_sum_curry (swap_args f) j)
      = fin_sum_congruence (fun (i: fin n) -> f i j) (swap_args f j) obvious
     in fin_sum_congruence (fun (j: fin n) -> fin_sum (fun i -> f i j))
                           (fin_sum_curry (swap_args f)) 
                           prf_j
                  
let fin_sum_const_zero
  (#t:Type) {| m: add_comm_group t |} (#n: nat)
  : Lemma (fin_sum #t #m #n (const zero) = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_const_zero_lambda #t #m #n;    
    fin_sum_congruence #t (const zero)
                          (fun (_: fin n) -> zero) obvious

let fin_sum_add
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f g: fin n -> t)
  : Lemma (fin_sum (pointwise_add f g) = fin_sum f + fin_sum g)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_add_lambda f g;   
    fin_sum_congruence (pointwise_add f g) (fun (k: fin n) -> f k + g k) obvious

let sum_range_kronecker_legacy
  (#t:Type) {| r: ring t |}
  (i0: nat) (g: nat -> t) (lo hi: nat)
  : Lemma (sum_range (pointwise_mul (kronecker_delta i0) g) lo hi
         = (if lo <= i0 && i0 < hi then g i0 else zero #t))
  = sum_range_kronecker_lambda i0 g lo hi

let fin_sum_kronecker
  (#t:Type) {| r: ring t |}
  (#n: nat) (i0: fin n) (g: fin n -> t)
  : Lemma (fin_sum (pointwise_mul (fin_kronecker_delta i0) g) = g i0)
  = fin_sum_kronecker_lambda i0 g

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
  = Classical.forall_intro h;
    prod_range_congruence_forall f g lo hi

let prod_range_swap_adjacent
  (#t:Type) {| m: commutative_ring t |}
  (f g: nat -> t) (lo hi: nat) (i: nat)
  (h: (k:nat{lo <= k /\ k < hi /\ k <> i /\ k <> i ++ 1}) -> Lemma (g k = f k))
  : Lemma (requires lo <= i /\ i ++ 1 < hi /\
                    g i = f (i ++ 1) /\ g (i ++ 1) = f i)
          (ensures prod_range f lo hi = prod_range g lo hi)
  = Classical.forall_intro h;
    prod_range_swap_adjacent_forall f g lo hi i

let prod_range_perm_invariance_fn
  (#t:Type) {| m: commutative_ring t |}
  (#n: nat) (f body_p body_id: nat -> t) (p: permutation n)
  (h_p: (k: nat{0 <= k /\ k < n}) -> Lemma (body_p k = f (p.fwd k)))
  (h_id: (k: nat{0 <= k /\ k < n}) -> Lemma (body_id k = f k))
  : Lemma (ensures prod_range body_p 0 n = prod_range body_id 0 n)
  = Classical.forall_intro h_p;
    Classical.forall_intro h_id;
    prod_range_perm_invariance_fn_forall f body_p body_id p

let fin_sum_zero_ext
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f: fin n -> t)
  (h: (k: fin n) -> Lemma (f k = zero))
  : Lemma (ensures fin_sum f = zero)
  = Classical.forall_intro h;
    fin_sum_zero_ext_forall f

let fin_sum_add_ext
  (#t:Type) {| m: add_comm_group t |} (#n: nat) (f g h: fin n -> t)
  (pf: (k: fin n) -> Lemma (h k = f k + g k))
  : Lemma (ensures fin_sum h = fin_sum f + fin_sum g)
  = Classical.forall_intro pf;
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

(* ================================================================= *)
(*  sum_range_neg: neg distributes over sum_range                     *)
(* ================================================================= *)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 0"
let rec sum_range_neg (#t:Type) {| g: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  : Lemma (ensures sum_range (pointwise_neg f) lo hi
                 = neg (sum_range f lo hi))
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    neg_zero #t ();
    if lo < hi then begin
      let lo1 : nat = lo ++ 1 in
      sum_range_neg f lo1 hi;
      let rest = sum_range f lo1 hi in
      neg_of_sum (f lo) rest;
      add_commutativity (neg rest) (neg (f lo));
      add_congruence (neg (f lo)) (sum_range (pointwise_neg f) lo1 hi)
                     (neg (f lo)) (neg rest)
    end

(* ================================================================= *)
(*  fin_sum_eq_sum_range: bridge fin_sum to sum_range                  *)
(* ================================================================= *)

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let fin_sum_eq_sum_range (#t:Type) {| acg: add_comm_group t |} (#n: pos)
  (f: fin n -> t) (g: nat -> t)
  : Lemma (requires (forall (k: nat{k < n}). g k = f k))
          (ensures fin_sum f = sum_range g 0 n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    fin_sum_as_fin_lift f;    
    sum_range_congruence (fin_lift f) g 0 n 
                         (fun k -> fin_lift_in_range f k)

(* ================================================================= *)
(*  sum_range_reverse_named: reversal for named functions              *)
(* ================================================================= *)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 0"
let rec sum_range_reverse_named (#t:Type) {| acg: add_comm_group t |}
  (f g: nat -> t) (n: nat)
  (h: (j: nat{j < n}) -> Lemma (f j = g (n - 1 - j)))
  : Lemma (ensures sum_range f 0 n = sum_range g 0 n)
          (decreases n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if n > 0 then begin
      let n1 : nat = n - 1 in
      sum_range_unfold_right g 0 n;
      h 0; 
      let f_sh (j:nat) = f (j ++ 1) in
      sum_range_reverse_named f_sh g n1
                              (fun j -> h (j ++ 1));
      sum_range_shift f 1 0 n1;
      add_congruence (f 0) (sum_range f 1 n) (g n1) (sum_range g 0 n1);
      add_commutativity (sum_range g 0 n1) (g n1)
    end

(* ===== merged from Core.FinSum.Convolution - helper lemmas (private) + sum_range_convolution ===== *)
let conv_term (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k i: nat) : t
  = if i <= k then f i * g (k - i) else zero

let conv_sum (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) k : t
  = sum_range (conv_term f g k) 0 (k ++ 1)

let conv_term_reveal (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k i: nat)
  : Lemma (conv_term f g k i == (if i <= k then f i * g (k - i) else zero)) = ()

let conv_sum_reveal (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) k
  : Lemma (conv_sum f g k == sum_range (conv_term f g k) 0 (k ++ 1)) = ()

(* beyond i=k the term vanishes *)
private let conv_term_zero_high (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k i: nat)
  : Lemma (requires i > k) (ensures conv_term f g k i = zero)
  = elim_equatable_laws t ()

(* padding: summing conv_term up to any N >= k+1 gives the same conv_sum *)
private let conv_extend (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k n: nat)
  : Lemma (requires n >= k ++ 1)
          (ensures sum_range (conv_term f g k) 0 n = conv_sum f g k)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let cf = conv_term f g k in
    sum_range_split cf 0 (k ++ 1) n;
    sum_range_all_zero cf (k ++ 1) n
                       (fun i -> conv_term_zero_high f g k i);
    x_plus_zero (sum_range cf 0 (k ++ 1));
    add_congruence (sum_range cf 0 (k ++ 1)) (sum_range cf (k ++ 1) n)
                   (sum_range cf 0 (k ++ 1)) zero

(* inner collapse: Σ_{k<n} conv_term f g k i = f i * Σ_{j<n-i} g j   (i <= n) *)
private let inner_collapse (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (i n: nat)
  : Lemma (requires i <= n)
          (ensures sum_range (fun k -> conv_term f g k i) 0 n
                 = f i * sum_range g 0 (n - i))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let ni : nat = n - i in
    let cfun : nat -> t = fun k -> conv_term f g k i in
    let gshift : nat -> t = fun k -> if i <= k then g (k - i) else zero in
    let pm : nat -> t = pointwise_mul (const (f i)) gshift in
    let gsh2 : nat -> t = fun j -> gshift (j ++ i) in
    (* split; lower part vanishes *)
    sum_range_split cfun 0 i n;
    sum_range_all_zero cfun 0 i (fun (k:nat{0 <= k /\ k < i}) -> conv_term_zero_high f g k i);
    (* upper part: cfun = pm on [i,n);  Σ pm = f i * Σ gshift *)
    sum_range_congruence cfun pm i n
      (fun (k:nat{i <= k /\ k < n}) -> reflexivity (f i * g (k - i)));
    sum_range_mul_left (f i) gshift i n;
    (* Σ_in gshift = Σ_0^ni g *)
    sum_range_shift gshift i 0 ni;
    sum_range_congruence gsh2 g 0 ni
      (fun (j:nat{0 <= j /\ j < ni}) -> reflexivity (g j));
    mul_congruence (f i) (sum_range gshift i n) (f i) (sum_range g 0 ni);
    (* assemble *)
    add_congruence (sum_range cfun 0 i) (sum_range cfun i n) zero (sum_range cfun i n);
    zero_plus_x (sum_range cfun i n)

(* THE LEMMA: (Σ_{i<m} f)·(Σ_{j<n} g) = Σ_{k<m+n} conv_sum f g k *)
let sum_range_convolution (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (m n: nat)
  (hf: (i:nat{i >= m}) -> Lemma (f i = zero))
  (hg: (j:nat{j >= n}) -> Lemma (g j = zero))
  : Lemma (sum_range f 0 m * sum_range g 0 n
         = sum_range (conv_sum f g) 0 (m ++ n))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let nn : nat = m ++ n in
    let ct2 : nat -> nat -> t = conv_term f g in
    let cg : t = sum_range g 0 n in
    let h : nat -> t = fun (i:nat) -> if i < nn then f i * sum_range g 0 (nn - i) else zero in
    (* g support extension: for i<m, Σ g 0 (nn-i) = Σ g 0 n *)
    let gsupp (i:nat{i < m}) : Lemma (sum_range g 0 (nn - i) = cg) =
      sum_range_split g 0 n (nn - i);
      sum_range_all_zero g n (nn - i) hg;
      x_plus_zero cg;
      add_congruence cg (sum_range g n (nn - i)) cg zero
    in
    (* each outer term collapses: sum_range_on (swap_args ct2) 0 nn i = h i *)
    let outer_cb (i:nat{0 <= i /\ i < nn}) : Lemma (sum_range_on (swap_args ct2) 0 nn i = h i) =
      sum_range_congruence (swap_args ct2 i) (fun (k:nat) -> conv_term f g k i) 0 nn
        (fun (k:nat{0 <= k /\ k < nn}) -> reflexivity (conv_term f g k i));
      inner_collapse f g i nn
    in
    (* Step 1: RHS = Σ_k Σ_i ct2 k i  (square) *)
    sum_range_congruence (conv_sum f g) (sum_range_on ct2 0 nn) 0 nn
      (fun (k:nat{0 <= k /\ k < nn}) -> conv_extend f g k nn);
    (* Step 2: swap *)
    sum_swap ct2 0 nn 0 nn;
    (* Step 3: collapse outer terms to h *)
    sum_range_congruence (sum_range_on (swap_args ct2) 0 nn) h 0 nn outer_cb;
    (* Σ_{i<nn} h = Σ_{i<m} h + Σ_{m<=i<nn} h ; second is 0 *)
    sum_range_split h 0 m nn;
    sum_range_all_zero h m nn
      (fun (i:nat{m <= i /\ i < nn}) ->
         hf i;
         reflexivity (sum_range g 0 (nn - i));
         mul_congruence (f i) (sum_range g 0 (nn - i))
                        zero (sum_range g 0 (nn - i));
         zero_mul_x (sum_range g 0 (nn - i));
         transitivity (f i * sum_range g 0 (nn - i))
                      (zero * sum_range g 0 (nn - i)) zero);
    (* Σ_{i<m} h = (Σ_{i<m} f)·cg *)
    sum_range_congruence h (pointwise_mul f (const cg)) 0 m
      (fun i ->
         gsupp i;
         //reflexivity (f i);
         mul_congruence (f i) (sum_range g 0 (nn - i)) (f i) cg);
    sum_range_mul_right f cg 0 m;
    (* assemble *)
    x_plus_zero (sum_range h 0 m);
    add_congruence (sum_range h 0 m) (sum_range h m nn) (sum_range h 0 m) zero
    
    // Pure AI slop: it's ok to write proofs like that, but always try removing 
    // transitivity chain calls when f* finally accepts your lemma.
    // In most cases, the proof will still succeed with just trans_for_calc t()

    // transitivity (sum_range h 0 nn) (sum_range h 0 m + sum_range h m nn) (sum_range h 0 m + zero);
    // transitivity (sum_range h 0 nn) (sum_range h 0 m + zero) (sum_range h 0 m);
    // transitivity (sum_range h 0 nn) (sum_range h 0 m) (sum_range f 0 m * cg);
    // (* chain RHS(square)=swap=Σh=LHS ; then symmetry *)
    // transitivity (sum_range (conv_sum f g) 0 nn)
    //              (sum_range (sum_range_on ct2 0 nn) 0 nn)
    //              (sum_range (sum_range_on (swap_args ct2) 0 nn) 0 nn);
    // transitivity (sum_range (conv_sum f g) 0 nn)
    //              (sum_range (sum_range_on (swap_args ct2) 0 nn) 0 nn)
    //              (sum_range h 0 nn);
    // transitivity (sum_range (conv_sum f g) 0 nn) (sum_range h 0 nn) (sum_range f 0 m * cg)
