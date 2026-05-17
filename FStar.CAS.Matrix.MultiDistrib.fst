module FStar.CAS.Matrix.MultiDistrib

(*
  Multi-distributivity: n-fold distribution of `prod_range` over `fin_sum`.

  Headline identity (Cauchy-Binet kernel):

      Π_{i in [0,n)} (Σ_{k in fin m} a i k)
        =
      Σ_{phi: fin n -> fin m} Π_{i in [0,n)} a i (phi i)

  This file builds the necessary list-level infrastructure
  (sum_list over append/concatMap, bridge between list-sums on
  all_fins and fin_sum) and the split-head lemma for
  `sum_over_fns_to`, then proves the main lemma by induction on n.
*)

open FStar.CAS.Permutation
open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes
open FStar.CAS.FinSum
open FStar.CAS.Function.Enum

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses

(* -------------------------------------------------------------------- *)
(*  Generalised sum over all functions fin n -> fin m.                  *)
(* -------------------------------------------------------------------- *)

let sum_over_fns_to
  (#t: Type) {| acm: add_comm_monoid t |}
  (n m: nat) (g: fn_to n m -> t) : t
  = sum_list (L.map g (all_fns_to n m))

(* -------------------------------------------------------------------- *)
(*  sum_list over list append.                                          *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_list_append
  (#t: Type) {| acm: add_comm_monoid t |}
  (xs ys: list t)
  : Lemma (ensures sum_list (L.append xs ys) = sum_list xs + sum_list ys)
          (decreases xs)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    match xs with
    | [] ->
        L.append_l_nil ys;
        left_add_identity (sum_list ys);
        symmetry (zero + sum_list ys) (sum_list ys)
    | x :: tl ->
        sum_list_append tl ys;
        reflexivity x;
        add_congruence x (sum_list (L.append tl ys)) x (sum_list tl + sum_list ys);
        let asg = acm.add_monoid.add_semigroup in
        asg.associativity x (sum_list tl) (sum_list ys);
        transitivity
          (x + sum_list (L.append tl ys))
          (x + (sum_list tl + sum_list ys))
          ((x + sum_list tl) + sum_list ys)
#pop-options

(* -------------------------------------------------------------------- *)
(*  sum_list over concatMap.                                            *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_list_concatMap
  (#a #t: Type) {| acm: add_comm_monoid t |}
  (f: a -> list t) (xs: list a)
  : Lemma (ensures sum_list (L.concatMap f xs)
                 = sum_list (L.map (fun (x:a) -> sum_list (f x)) xs))
          (decreases xs)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    match xs with
    | [] -> reflexivity (sum_list #t #acm [])
    | x :: tl ->
        sum_list_concatMap f tl;
        sum_list_append (f x) (L.concatMap f tl);
        reflexivity (sum_list (f x));
        add_congruence
          (sum_list (f x)) (sum_list (L.concatMap f tl))
          (sum_list (f x)) (sum_list (L.map (fun (y:a) -> sum_list (f y)) tl));
        transitivity
          (sum_list (L.concatMap f (x :: tl)))
          (sum_list (f x) + sum_list (L.concatMap f tl))
          (sum_list (f x) + sum_list (L.map (fun (y:a) -> sum_list (f y)) tl))
#pop-options

(* -------------------------------------------------------------------- *)
(*  map distributes over concatMap.                                     *)
(* -------------------------------------------------------------------- *)

let rec map_concatMap
  (#a #b #c: Type) (g: b -> c) (f: a -> list b) (xs: list a)
  : Lemma (ensures L.map g (L.concatMap f xs)
                 == L.concatMap (fun (x:a) -> L.map g (f x)) xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: tl ->
        map_concatMap g f tl;
        L.map_append g (f x) (L.concatMap f tl)

(* -------------------------------------------------------------------- *)
(*  Bridge: sum_list (map f (all_fins m)) = fin_sum m f.                *)
(* -------------------------------------------------------------------- *)

(* sum_list (map f (all_fins_from m k)) = sum_range guarded over [k, m). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec sum_list_map_all_fins_from_eq_sum_range
  (#t: Type) {| acm: add_comm_monoid t |}
  (m: nat) (k: nat{k <= m}) (f: fin m -> t)
  : Lemma (ensures
            sum_list (L.map f (all_fins_from m k))
          = sum_range (fun (j: nat) -> if j < m then f (j <: fin m) else zero) k m)
          (decreases (Prims.op_Subtraction m k))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if k = m then begin
      sum_range_empty
        (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k m;
      symmetry
        (sum_range (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k m)
        (zero #t)
    end else begin
      let k1 = Prims.op_Addition k 1 in
      sum_list_map_all_fins_from_eq_sum_range m k1 f;
      sum_range_unfold_left
        (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k m;
      reflexivity (f (k <: fin m));
      add_congruence
        (f (k <: fin m))
        (sum_list (L.map f (all_fins_from m k1)))
        (f (k <: fin m))
        (sum_range (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k1 m);
      trans_lemma [
        sum_list (L.map f (all_fins_from m k));
        f (k <: fin m) + sum_list (L.map f (all_fins_from m k1));
        f (k <: fin m)
          + sum_range (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k1 m;
        sum_range (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k m
      ]
    end
#pop-options

let sum_list_map_all_fins_eq_fin_sum
  (#t: Type) {| acm: add_comm_monoid t |}
  (m: nat) (f: fin m -> t)
  : Lemma (sum_list (L.map f (all_fins m)) = fin_sum f)
  = sum_list_map_all_fins_from_eq_sum_range m 0 f

(* sum_list (map g (map h xs)) = sum_list (map (g . h) xs). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let rec sum_list_map_compose
  (#a #b #t: Type) {| acm: add_comm_monoid t |}
  (g: b -> t) (h: a -> b) (xs: list a)
  : Lemma (ensures sum_list (L.map g (L.map h xs))
                 = sum_list (L.map (fun (x:a) -> g (h x)) xs))
          (decreases xs)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    match xs with
    | [] -> reflexivity (sum_list #t #acm [])
    | x :: tl ->
        sum_list_map_compose g h tl;
        reflexivity (g (h x));
        add_congruence
          (g (h x)) (sum_list (L.map g (L.map h tl)))
          (g (h x)) (sum_list (L.map (fun (y:a) -> g (h y)) tl))
#pop-options

(* -------------------------------------------------------------------- *)
(*  Split-head for sum_over_fns_to.                                     *)
(* -------------------------------------------------------------------- *)

unfold let extend_fin_sum
  (#t: Type) {| acm: add_comm_monoid t |}
  (n m: nat) (g: fn_to (Prims.op_Addition n 1) m -> t) (phi: fn_to n m) : t =
  fin_sum (fun (k: fin m) -> g (extend_fn #n #m phi k))

let extend_fin_sum_def
  (#t: Type) {| acm: add_comm_monoid t |}
  (n m: nat) (g: fn_to (Prims.op_Addition n 1) m -> t) (phi: fn_to n m)
  : Lemma (extend_fin_sum n m g phi
           == fin_sum (fun (k: fin m) -> g (extend_fn #n #m phi k))) = ()

(*
   sum_over_fns_to (n+1) m g
   = Σ_{phi: fn_to n m} Σ_{k: fin m} g (extend_fn phi k)
*)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let sum_over_fns_to_split_head
  (#t: Type) {| acm: add_comm_monoid t |}
  (n m: nat) (g: fn_to (Prims.op_Addition n 1) m -> t)
  : Lemma (sum_over_fns_to (Prims.op_Addition n 1) m g
         = sum_over_fns_to n m (extend_fin_sum #t #acm n m g))
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    let n1 = Prims.op_Addition n 1 in
    all_fns_to_succ_eq n m;
    map_concatMap g
      (fun (phi: fn_to n m) ->
         L.map (fun (j: fin m) -> extend_fn #n #m phi j) (all_fins m))
      (all_fns_to n m);
    sum_list_concatMap
      (fun (phi: fn_to n m) ->
         L.map g (L.map (fun (j: fin m) -> extend_fn #n #m phi j) (all_fins m)))
      (all_fns_to n m);
    let h' (phi: fn_to n m) : t =
      fin_sum (fun (k: fin m) -> g (extend_fn #n #m phi k))
    in
    let pf (phi: fn_to n m)
      : Lemma
        (sum_list (L.map g (L.map (fun (j: fin m) -> extend_fn #n #m phi j) (all_fins m)))
         = h' phi)
      = sum_list_map_compose g (fun (j: fin m) -> extend_fn #n #m phi j) (all_fins m);
        sum_list_map_all_fins_eq_fin_sum m (fun (j: fin m) -> g (extend_fn #n #m phi j));
        transitivity
          (sum_list (L.map g (L.map (fun (j: fin m) -> extend_fn #n #m phi j) (all_fins m))))
          (sum_list (L.map (fun (j: fin m) -> g (extend_fn #n #m phi j)) (all_fins m)))
          (h' phi)
    in
    Classical.forall_intro pf;
    sum_list_map_congruence
      (fun (phi: fn_to n m) ->
         sum_list (L.map g (L.map (fun (j: fin m) -> extend_fn #n #m phi j) (all_fins m))))
      h'
      (all_fns_to n m);
    reflexivity (sum_over_fns_to n1 m g);
    reflexivity (sum_over_fns_to n m h');
    transitivity
      (sum_over_fns_to n1 m g)
      (sum_list (L.concatMap (fun (phi: fn_to n m) ->
                                L.map g (L.map (fun (j: fin m) -> extend_fn #n #m phi j) (all_fins m)))
                             (all_fns_to n m)))
      (sum_list (L.map
                  (fun (phi: fn_to n m) ->
                     sum_list (L.map g (L.map (fun (j: fin m) -> extend_fn #n #m phi j) (all_fins m))))
                  (all_fns_to n m)));
    transitivity
      (sum_over_fns_to n1 m g)
      (sum_list (L.map
                  (fun (phi: fn_to n m) ->
                     sum_list (L.map g (L.map (fun (j: fin m) -> extend_fn #n #m phi j) (all_fins m))))
                  (all_fns_to n m)))
      (sum_list (L.map h' (all_fns_to n m)));
    transitivity
      (sum_over_fns_to n1 m g)
      (sum_list (L.map h' (all_fns_to n m)))
      (sum_over_fns_to n m h');
    (* Bridge h' to extend_fin_sum: pointwise equal by definition. *)
    let cong_h_ext (phi: fn_to n m) : Lemma (h' phi = extend_fin_sum #t #acm n m g phi)
      = extend_fin_sum_def #t #acm n m g phi;
        reflexivity (h' phi) in
    Classical.forall_intro cong_h_ext;
    sum_list_map_congruence h' (extend_fin_sum #t #acm n m g) (all_fns_to n m);
    transitivity
      (sum_over_fns_to n1 m g)
      (sum_over_fns_to n m h')
      (sum_over_fns_to n m (extend_fin_sum #t #acm n m g))
#pop-options

(* -------------------------------------------------------------------- *)
(*  sum_list scalar multiplication on the right.                        *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 6 --ifuel 4 --z3rlimit 80"
let rec sum_list_map_mul_right
  (#a:Type) (#t:Type) {| r: semiring t |}
  (f: a -> t) (c: t) (xs: list a)
  : Lemma (ensures sum_list (L.map f xs) * c = sum_list (L.map (fun x -> f x * c) xs))
          (decreases xs)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    match xs with
    | [] ->
        left_absorption c;
        symmetry ((zero #t) * c) (zero #t)
    | hx :: rest ->
        sum_list_map_mul_right #a #t #r f c rest;
        let h = f hx in
        let trest = sum_list (L.map f rest) in
        let crest = sum_list (L.map (fun x -> f x * c) rest) in
        right_distributivity h trest c;
        reflexivity (h * c);
        add_congruence (h * c) (trest * c) (h * c) crest;
        trans_lemma [ sum_list (L.map f (hx :: rest)) * c;
                      (h + trest) * c;
                      h * c + trest * c;
                      h * c + crest;
                      sum_list (L.map (fun x -> f x * c) (hx :: rest)) ]
#pop-options

(* -------------------------------------------------------------------- *)
(*  sum_over_fns_to scalar mul right.                                   *)
(* -------------------------------------------------------------------- *)

let sum_over_fns_to_mul_right
  (#t: Type) {| r: semiring t |}
  (n m: nat) (f: fn_to n m -> t) (c: t)
  : Lemma (sum_over_fns_to n m f * c
         = sum_over_fns_to n m (fun (phi: fn_to n m) -> f phi * c))
  = sum_list_map_mul_right f c (all_fns_to n m)

(* -------------------------------------------------------------------- *)
(*  Pointwise inductive step: at fixed (phi, k), the (n+1)-fold product *)
(*  over the extended function decomposes as the n-fold product times   *)
(*  the (n+1)-th coordinate.                                            *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let prod_range_extend_pointwise
  (#t: Type) {| mm: mul_monoid t |}
  (n m: nat) (a: fin (Prims.op_Addition n 1) -> fin m -> t)
  (phi: fn_to n m) (k: fin m)
  : Lemma
    (prod_range (fun (i: nat) ->
       if i < Prims.op_Addition n 1
       then a (i <: fin (Prims.op_Addition n 1))
              ((extend_fn #n #m phi k) (i <: fin (Prims.op_Addition n 1)))
       else one) 0 (Prims.op_Addition n 1)
     = prod_range (fun (i: nat) ->
         if i < n
         then a (i <: fin (Prims.op_Addition n 1)) (phi (i <: fin n))
         else one) 0 n
       * a (n <: fin (Prims.op_Addition n 1)) k)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    prod_range_unfold_right
      (fun (i: nat) ->
         if i < Prims.op_Addition n 1
         then a (i <: fin (Prims.op_Addition n 1))
                ((extend_fn #n #m phi k) (i <: fin (Prims.op_Addition n 1)))
         else one)
      0 (Prims.op_Addition n 1);
    let cong (i: nat)
      : Lemma (0 <= i /\ i < n ==>
               (if i < Prims.op_Addition n 1
                then a (i <: fin (Prims.op_Addition n 1))
                       ((extend_fn #n #m phi k) (i <: fin (Prims.op_Addition n 1)))
                else one)
               = (if i < n
                  then a (i <: fin (Prims.op_Addition n 1)) (phi (i <: fin n))
                  else one))
      = if 0 <= i && i < n then
          reflexivity (a (i <: fin (Prims.op_Addition n 1)) (phi (i <: fin n)))
    in
    Classical.forall_intro cong;
    prod_range_congruence
      (fun (i: nat) ->
         if i < Prims.op_Addition n 1
         then a (i <: fin (Prims.op_Addition n 1))
                ((extend_fn #n #m phi k) (i <: fin (Prims.op_Addition n 1)))
         else one)
      (fun (i: nat) ->
         if i < n
         then a (i <: fin (Prims.op_Addition n 1)) (phi (i <: fin n))
         else one)
      0 n;
    reflexivity (a (n <: fin (Prims.op_Addition n 1)) k);
    mul_congruence
      (prod_range
         (fun (i: nat) ->
            if i < Prims.op_Addition n 1
            then a (i <: fin (Prims.op_Addition n 1))
                   ((extend_fn #n #m phi k) (i <: fin (Prims.op_Addition n 1)))
            else one)
         0 n)
      (if n < Prims.op_Addition n 1
       then a (n <: fin (Prims.op_Addition n 1))
              ((extend_fn #n #m phi k) (n <: fin (Prims.op_Addition n 1)))
       else one)
      (prod_range
         (fun (i: nat) ->
            if i < n
            then a (i <: fin (Prims.op_Addition n 1)) (phi (i <: fin n))
            else one)
         0 n)
      (a (n <: fin (Prims.op_Addition n 1)) k);
    transitivity
      (prod_range
         (fun (i: nat) ->
            if i < Prims.op_Addition n 1
            then a (i <: fin (Prims.op_Addition n 1))
                   ((extend_fn #n #m phi k) (i <: fin (Prims.op_Addition n 1)))
            else one)
         0 (Prims.op_Addition n 1))
      (prod_range
         (fun (i: nat) ->
            if i < Prims.op_Addition n 1
            then a (i <: fin (Prims.op_Addition n 1))
                   ((extend_fn #n #m phi k) (i <: fin (Prims.op_Addition n 1)))
            else one)
         0 n
       * (if n < Prims.op_Addition n 1
          then a (n <: fin (Prims.op_Addition n 1))
                 ((extend_fn #n #m phi k) (n <: fin (Prims.op_Addition n 1)))
          else one))
      (prod_range
         (fun (i: nat) ->
            if i < n
            then a (i <: fin (Prims.op_Addition n 1)) (phi (i <: fin n))
            else one)
         0 n
       * a (n <: fin (Prims.op_Addition n 1)) k)
#pop-options

(* -------------------------------------------------------------------- *)
(*  Main theorem: prod_range_of_fin_sum.                                *)
(*                                                                       *)
(*    prod_range_i (Sigma_k a i k) = Sigma_phi prod_range_i (a i (phi i)) *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let rec prod_range_of_fin_sum
  (#t: Type) {| r: semiring t |}
  (n m: nat) (a: fin n -> fin m -> t)
  : Lemma
    (ensures
       prod_range (fun (i: nat) ->
         if i < n then fin_sum (a (i <: fin n)) else one) 0 n
     = sum_over_fns_to n m
         (fun (phi: fn_to n m) ->
           prod_range (fun (i: nat) ->
             if i < n then a (i <: fin n) (phi (i <: fin n)) else one) 0 n))
    (decreases n)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    if n = 0 then begin
      (* LHS: prod_range _ 0 0 = one. *)
      prod_range_empty
        (fun (i: nat) -> if i < n then fin_sum (a (i <: fin n)) else one) 0 0;
      (* RHS: sum_over_fns_to 0 m g = sum_list [g (nullary m)] = g (nullary m) + zero,
              with g (nullary m) = prod_range _ 0 0 = one. *)
      prod_range_empty
        (fun (i: nat) ->
          if i < n then a (i <: fin n) ((nullary m) (i <: fin n)) else one) 0 0;
      assert (all_fns_to 0 m == [nullary m]);
      (* sum_list (L.map g [nullary m]) = g (nullary m) + sum_list [] = one + zero *)
      right_add_identity (one #t);
      transitivity
        (sum_over_fns_to n m
          (fun (phi: fn_to n m) ->
            prod_range (fun (i: nat) ->
              if i < n then a (i <: fin n) (phi (i <: fin n)) else one) 0 n))
        (one #t + zero #t)
        (one #t);
      symmetry
        (sum_over_fns_to n m
          (fun (phi: fn_to n m) ->
            prod_range (fun (i: nat) ->
              if i < n then a (i <: fin n) (phi (i <: fin n)) else one) 0 n))
        (one #t);
      transitivity
        (prod_range
          (fun (i: nat) -> if i < n then fin_sum (a (i <: fin n)) else one) 0 n)
        (one #t)
        (sum_over_fns_to n m
          (fun (phi: fn_to n m) ->
            prod_range (fun (i: nat) ->
              if i < n then a (i <: fin n) (phi (i <: fin n)) else one) 0 n))
    end else begin
      let n_m1 : nat = Prims.op_Subtraction n 1 in
      assert (Prims.op_Addition n_m1 1 == n);
      elim_equatable_laws t;
      transitivity_for_calc_proofs t;
      let a' : fin n_m1 -> fin m -> t =
        fun (i: fin n_m1) (k: fin m) -> a (i <: fin n) k
      in
      prod_range_of_fin_sum #t #r n_m1 m a';
      [@@inline_let] let body_lhs (i: nat) : t =
        if i < n then fin_sum (a (i <: fin n)) else one #t in
      [@@inline_let] let body_ih_lhs (i: nat) : t =
        if i < n_m1 then fin_sum (a' (i <: fin n_m1)) else one #t in
      [@@inline_let] let g_rhs (phi: fn_to n m) : t =
        prod_range (fun (i: nat) ->
          if i < n then a (i <: fin n) (phi (i <: fin n)) else one #t) 0 n in
      [@@inline_let] let g_ih (phi: fn_to n_m1 m) : t =
        prod_range (fun (i: nat) ->
          if i < n_m1 then a' (i <: fin n_m1) (phi (i <: fin n_m1)) else one #t) 0 n_m1 in
      prod_range_unfold_right body_lhs 0 n;
      let s_n : t = fin_sum (a (n_m1 <: fin n)) in
      let s_n_def () : Lemma (s_n == fin_sum (a (n_m1 <: fin n))) = () in
      s_n_def ();
      assert (body_lhs n_m1 == s_n);
      let body_lhs_def (i: nat) : Lemma (body_lhs i == (if i < n then fin_sum (a (i <: fin n)) else one #t)) = () in
      let body_ih_lhs_def (i: nat) : Lemma (body_ih_lhs i == (if i < n_m1 then fin_sum (a' (i <: fin n_m1)) else one #t)) = () in
      let a'_def (i: fin n_m1) (k: fin m) : Lemma (a' i k == a (i <: fin n) k) = () in
      let g_rhs_def (phi: fn_to n m) : Lemma (g_rhs phi ==
         prod_range (fun (i: nat) ->
           if i < n then a (i <: fin n) (phi (i <: fin n)) else one #t) 0 n) = () in
      let g_ih_def (phi: fn_to n_m1 m) : Lemma (g_ih phi ==
         prod_range (fun (i: nat) ->
           if i < n_m1 then a' (i <: fin n_m1) (phi (i <: fin n_m1)) else one #t) 0 n_m1) = () in
      Classical.forall_intro body_lhs_def;
      Classical.forall_intro body_ih_lhs_def;
      Classical.forall_intro_2 a'_def;
      Classical.forall_intro g_rhs_def;
      Classical.forall_intro g_ih_def;
      let cong_lhs (i: nat)
        : Lemma (0 <= i /\ i < n_m1 ==> body_lhs i = body_ih_lhs i)
        = if 0 <= i && i < n_m1 then begin
            let aux (k: fin m) : Lemma (a (i <: fin n) k = a' (i <: fin n_m1) k)
              = reflexivity (a (i <: fin n) k) in
            Classical.forall_intro aux;
            fin_sum_congruence (a (i <: fin n)) (a' (i <: fin n_m1));
            body_lhs_def i;
            body_ih_lhs_def i
          end
      in
      Classical.forall_intro cong_lhs;
      prod_range_congruence body_lhs body_ih_lhs 0 n_m1;
      let sum_ih : t = sum_over_fns_to n_m1 m g_ih in
      let pr_n_m1 : t = prod_range body_lhs 0 n_m1 in
      let pr_ih   : t = prod_range body_ih_lhs 0 n_m1 in
      transitivity pr_n_m1 pr_ih sum_ih;
      reflexivity s_n;
      mul_congruence pr_n_m1 s_n sum_ih s_n;
      sum_over_fns_to_mul_right #t #r n_m1 m g_ih s_n;
      let h1 (phi: fn_to n_m1 m) : t = g_ih phi * s_n in
      let g_step (phi: fn_to n_m1 m) : t =
        fin_sum (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k)) in
      let per_phi (phi: fn_to n_m1 m)
        : Lemma (h1 phi = g_step phi)
        = let h1_def () : Lemma (h1 phi == g_ih phi * s_n) = () in
          h1_def ();
          fin_sum_mul_left #t #r #m (g_ih phi) (a (n_m1 <: fin n));
          let body_mul : fin m -> t =
            fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k in
          let body_ext : fin m -> t =
            fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k) in
          let body_mul_def (k: fin m) : Lemma (body_mul k == g_ih phi * a (n_m1 <: fin n) k) = () in
          let body_ext_def (k: fin m) : Lemma (body_ext k == g_rhs (extend_fn #n_m1 #m phi k)) = () in
          let g_step_def () : Lemma (g_step phi ==
            fin_sum (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k))) = () in
          Classical.forall_intro body_mul_def;
          Classical.forall_intro body_ext_def;
          g_step_def ();
          let per_k (k: fin m) : Lemma (body_mul k = body_ext k)
            = let phi_ext : fn_to n m = extend_fn #n_m1 #m phi k in
              let gd_body (i: nat) : t =
                if i < n then a (i <: fin n) (phi_ext (i <: fin n)) else one #t in
              let gd_body_def (i: nat) : Lemma (gd_body i ==
                (if i < n then a (i <: fin n) (phi_ext (i <: fin n)) else one #t)) = () in
              let phi_ext_def (i: fin n) : Lemma (phi_ext i ==
                (if i = n_m1 then k else phi (i <: fin n_m1))) = () in
              let body_ih_inner (i: nat) : t =
                if i < n_m1 then a' (i <: fin n_m1) (phi (i <: fin n_m1)) else one #t in
              let body_ih_inner_def (i: nat) : Lemma (body_ih_inner i ==
                (if i < n_m1 then a' (i <: fin n_m1) (phi (i <: fin n_m1)) else one #t)) = () in
              Classical.forall_intro gd_body_def;
              Classical.forall_intro phi_ext_def;
              Classical.forall_intro body_ih_inner_def;
              prod_range_unfold_right gd_body 0 n;
              assert (gd_body n_m1 == a (n_m1 <: fin n) k);
              let cong3 (i: nat)
                : Lemma (0 <= i /\ i < n_m1 ==> gd_body i = body_ih_inner i)
                = if 0 <= i && i < n_m1 then
                    reflexivity (a (i <: fin n) (phi (i <: fin n_m1)))
              in
              Classical.forall_intro cong3;
              prod_range_congruence gd_body body_ih_inner 0 n_m1;
              reflexivity (a (n_m1 <: fin n) k);
              mul_congruence
                (prod_range gd_body 0 n_m1) (a (n_m1 <: fin n) k)
                (prod_range body_ih_inner 0 n_m1) (a (n_m1 <: fin n) k);
              (* prod_range gd_body 0 n = prod_range gd_body 0 n_m1 * gd_body n_m1
                                        = prod_range gd_body 0 n_m1 * a (n_m1 <: fin n) k
                                        = prod_range body_ih_inner 0 n_m1 * a (n_m1 <: fin n) k
                                        = g_ih phi * a (n_m1 <: fin n) k
                                        = body_mul k *)
              transitivity
                (prod_range gd_body 0 n)
                (prod_range gd_body 0 n_m1 * a (n_m1 <: fin n) k)
                (prod_range body_ih_inner 0 n_m1 * a (n_m1 <: fin n) k);
              (* g_rhs phi_ext = prod_range gd_body 0 n,
                 g_ih phi = prod_range body_ih_inner 0 n_m1. *)
              symmetry
                (prod_range gd_body 0 n)
                (prod_range body_ih_inner 0 n_m1 * a (n_m1 <: fin n) k)
          in
          Classical.forall_intro per_k;
          let cong_bm (k: fin m) : Lemma
            ((fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k) k = body_mul k)
            = reflexivity (g_ih phi * a (n_m1 <: fin n) k) in
          Classical.forall_intro cong_bm;
          fin_sum_congruence
            (fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k)
            body_mul;
          fin_sum_congruence body_mul body_ext;
          let cong_be (k: fin m) : Lemma
            (body_ext k = (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k)) k)
            = reflexivity (g_rhs (extend_fn #n_m1 #m phi k)) in
          Classical.forall_intro cong_be;
          fin_sum_congruence body_ext
            (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k));
          let s1 : t = g_ih phi * s_n in
          let s2 : t = fin_sum (fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k) in
          let s3 : t = fin_sum body_mul in
          let s4 : t = fin_sum body_ext in
          let s5 : t = fin_sum (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k)) in
          assert (h1 phi == s1);
          assert (g_step phi == s5);
          reflexivity (h1 phi);
          reflexivity (g_step phi);
          assert (h1 phi = s1);
          assert (g_step phi = s5);
          assert (s1 = s2);
          assert (s2 = s3);
          assert (s3 = s4);
          assert (s4 = s5);
          transitivity (h1 phi) s1 s2;
          transitivity (h1 phi) s2 s3;
          transitivity (h1 phi) s3 s4;
          transitivity (h1 phi) s4 s5;
          transitivity (h1 phi) s5 (g_step phi)
      in
      Classical.forall_intro per_phi;
      sum_list_map_congruence h1 g_step (all_fns_to n_m1 m);
      sum_over_fns_to_split_head #t #(r.add_comm_monoid) n_m1 m g_rhs;
      (* split_head gives: lhs = sum_over_fns_to n_m1 m (extend_fin_sum n_m1 m g_rhs) *)
      let cong_ext_step_rev (phi: fn_to n_m1 m) : Lemma
        (extend_fin_sum #t #(r.add_comm_monoid) n_m1 m g_rhs phi = g_step phi)
        = assert (extend_fin_sum #t #(r.add_comm_monoid) n_m1 m g_rhs phi ==
                  fin_sum (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k)))
            by (FStar.Tactics.norm [delta_only [`%extend_fin_sum]]; FStar.Tactics.trefl ());
          assert (g_step phi ==
                  fin_sum (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k)));
          reflexivity (g_step phi) in
      Classical.forall_intro cong_ext_step_rev;
      sum_list_map_congruence
        (extend_fin_sum #t #(r.add_comm_monoid) n_m1 m g_rhs)
        g_step
        (all_fns_to n_m1 m);
      transitivity
        (sum_over_fns_to (Prims.op_Addition n_m1 1) m g_rhs)
        (sum_over_fns_to n_m1 m (extend_fin_sum #t #(r.add_comm_monoid) n_m1 m g_rhs))
        (sum_over_fns_to n_m1 m g_step);
      assert (Prims.op_Addition n_m1 1 == n);
      let rhs_alt : t = sum_over_fns_to (Prims.op_Addition n_m1 1) m g_rhs in
      let lhs_n = prod_range body_lhs 0 n in
      let rhs_n = sum_over_fns_to n m g_rhs in
      let t1 : t = pr_n_m1 * s_n in
      let t2 : t = sum_ih * s_n in
      let t3 : t = sum_over_fns_to n_m1 m h1 in
      let t4 : t = sum_over_fns_to n_m1 m g_step in
      let t5 : t = sum_over_fns_to n_m1 m
                     (fun (phi: fn_to n_m1 m) -> g_ih phi * s_n) in
      reflexivity lhs_n; reflexivity rhs_n;
      reflexivity t1; reflexivity t2; reflexivity t3; reflexivity t4; reflexivity t5;
      assert (lhs_n = t1);
      assert (t1 = t2);
      let cong_h1 (phi: fn_to n_m1 m) : Lemma
        ((fun (phi: fn_to n_m1 m) -> g_ih phi * s_n) phi = h1 phi)
        = reflexivity (g_ih phi * s_n) in
      Classical.forall_intro cong_h1;
      sum_list_map_congruence
        (fun (phi: fn_to n_m1 m) -> g_ih phi * s_n) h1 (all_fns_to n_m1 m);
      assert (t5 = t3);
      assert (t2 = t5);
      assert (t3 = t4);
      assert (rhs_n == rhs_alt);
      reflexivity rhs_n;
      assert (rhs_n = rhs_alt);
      assert (rhs_alt = t4);
      transitivity rhs_n rhs_alt t4;
      assert (rhs_n = t4);
      symmetry rhs_n t4;
      transitivity lhs_n t1 t2;
      transitivity lhs_n t2 t5;
      transitivity lhs_n t5 t3;
      transitivity lhs_n t3 t4;
      transitivity lhs_n t4 rhs_n
    end
#pop-options
