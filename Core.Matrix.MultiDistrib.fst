module Core.Matrix.MultiDistrib

(*
  Multi-distributivity: n-fold distribution of prod_range over fin_sum.

  Headline identity (Cauchy-Binet kernel):

      Pi_{i in [0,n)} (Sigma_{k in fin m} a i k)
        =
      Sigma_{phi: fin n -> fin m} Pi_{i in [0,n)} a i (phi i)

  Ported into the diamond-free `core/` tower.

  Differences from the old version:
  - Old code threaded an extra `mm: mul_monoid t{mm == mm_of_semiring r}`
    parameter through every lemma. The new tower has no mul_monoid /
    semiring distinction — `ring t` covers both. We drop the parameter.
  - `add_comm_monoid` → `add_comm_group`.
  - `transitivity_for_calc_proofs` → `trans_for_calc`.
*)

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Algebra.Helpers
open Core.FinSum
open Core.Permutation
open FStar.List.Tot.Base

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses

(* -------------------------------------------------------------------- *)
(*  Types: fin_map, nullary, extend_fn, all_fins_from/all_fins,           *)
(*  all_fns_to  -- inlined from legacy Function.Enum.                   *)
(* -------------------------------------------------------------------- *)

let fin_map (n m: nat) = fin n -> fin m

let nullary (m: nat) : fin_map 0 m =
  fun (i: fin 0) -> false_elim #(fin m) ()

let rec all_fins_from (m: nat) (k: nat{k <= m})
  : Tot (list (fin m)) (decreases (Prims.op_Subtraction m k))
  = if k = m then []
    else (k <: fin m) :: all_fins_from m (Prims.op_Addition k 1)

let all_fins (m: nat) : list (fin m) = all_fins_from m 0

let extend_fn (#n #m: nat) (phi: fin_map n m) (j: fin m)
  : fin_map (Prims.op_Addition n 1) m
  = fun (i: fin (Prims.op_Addition n 1)) ->
      if i = n then j
      else phi (i <: fin n)

let extend_to_all (#k #m: nat) (phi: fin_map k m)
  : list (fin_map (Prims.op_Addition k 1) m)
  = map (extend_fn #k #m phi) (all_fins m)

let all_fns_to_succ_list (#k m: nat) (xs: list (fin_map k m))
  : list (fin_map (Prims.op_Addition k 1) m)
  = concatMap (extend_to_all #k #m) xs

let rec all_fns_to (n m: nat) : Tot (list (fin_map n m)) (decreases n)
  = match n with
    | 0 -> [nullary m]
    | _ ->
        all_fns_to_succ_list #(Prims.op_Subtraction n 1) m
          (all_fns_to (Prims.op_Subtraction n 1) m)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let all_fns_to_succ_eq (k m: nat)
  : Lemma (all_fns_to (Prims.op_Addition k 1) m ==
           all_fns_to_succ_list #k m (all_fns_to k m))
  = ()
#pop-options

(* -------------------------------------------------------------------- *)
(*  sum_over_fns_to                                                     *)
(* -------------------------------------------------------------------- *)

let sum_over_fns_to
  (#t: Type) {| g: add_comm_group t |}
  (n m: nat) (f: fin_map n m -> t) : t
  = sum_list (map f (all_fns_to n m))

(* -------------------------------------------------------------------- *)
(*  sum_list over list append.                                          *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
let rec sum_list_append
  (#t: Type) {| g: add_comm_group t |}
  (xs ys: list t)
  : Lemma (ensures sum_list (append xs ys) = sum_list xs + sum_list ys)
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] ->
        sum_list_nil #t #g;
        zero_plus_x (sum_list #t #g ys);
        reflexivity (sum_list #t #g ys)
    | x :: tl ->
        sum_list_append #t #g tl ys;
        sum_list_cons x (append tl ys);
        sum_list_cons x tl;
        reflexivity x;
        g.add_congruence x (sum_list (append tl ys)) x (sum_list tl + sum_list ys);
        g.add_associativity x (sum_list tl) (sum_list ys)
#pop-options

(* -------------------------------------------------------------------- *)
(*  sum_list over concatMap.                                            *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
let rec sum_list_concatMap
  (#a #t: Type) {| g: add_comm_group t |}
  (f: a -> list t) (xs: list a)
  : Lemma (ensures sum_list (concatMap f xs)
                 = sum_list (map (fun (x:a) -> sum_list (f x)) xs))
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] ->
        sum_list_nil #t #g;
        reflexivity (zero #t)
    | x :: tl ->
        sum_list_concatMap #a #t #g f tl;
        sum_list_append (f x) (concatMap f tl);
        sum_list_cons (sum_list (f x)) (map (fun (y:a) -> sum_list (f y)) tl);
        reflexivity (sum_list (f x));
        g.add_congruence
          (sum_list (f x)) (sum_list (concatMap f tl))
          (sum_list (f x)) (sum_list (map (fun (y:a) -> sum_list (f y)) tl));
        transitivity
          (sum_list (concatMap f (x :: tl)))
          (sum_list (f x) + sum_list (concatMap f tl))
          (sum_list (f x) + sum_list (map (fun (y:a) -> sum_list (f y)) tl))
#pop-options

(* -------------------------------------------------------------------- *)
(*  map distributes over concatMap.                                     *)
(* -------------------------------------------------------------------- *)

let rec map_concatMap
  (#a #b #c: Type) (g: b -> c) (f: a -> list b) (xs: list a)
  : Lemma (ensures map g (concatMap f xs)
                 == concatMap (fun (x:a) -> map g (f x)) xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: tl ->
        map_concatMap g f tl;
        L.map_append g (f x) (concatMap f tl)

(* -------------------------------------------------------------------- *)
(*  sum_list (map g (map h xs)) = sum_list (map (g . h) xs).            *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
let rec sum_list_map_compose
  (#a #b #t: Type) {| g: add_comm_group t |}
  (gf: b -> t) (h: a -> b) (xs: list a)
  : Lemma (ensures sum_list (map gf (map h xs))
                 = sum_list (map (fun (x:a) -> gf (h x)) xs))
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] -> sum_list_nil #t #g; reflexivity (zero #t)
    | x :: tl ->
        sum_list_map_compose gf h tl;
        sum_list_cons (gf (h x)) (map gf (map h tl));
        sum_list_cons (gf (h x)) (map (fun (y:a) -> gf (h y)) tl);
        reflexivity (gf (h x));
        g.add_congruence
          (gf (h x)) (sum_list (map gf (map h tl)))
          (gf (h x)) (sum_list (map (fun (y:a) -> gf (h y)) tl))
#pop-options

(* -------------------------------------------------------------------- *)
(*  Bridge: sum_list (map f (all_fins m)) = fin_sum f.                  *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec sum_list_map_all_fins_from_eq_sum_range
  (#t: Type) {| g: add_comm_group t |}
  (m: nat) (k: nat{k <= m}) (f: fin m -> t)
  : Lemma (ensures
            sum_list (map f (all_fins_from m k))
          = sum_range (fun (j: nat) -> if j < m then f (j <: fin m) else zero) k m)
          (decreases (Prims.op_Subtraction m k))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if k = m then begin
      sum_list_nil #t #g;
      sum_range_empty
        (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k m
    end else begin
      let k1 = Prims.op_Addition k 1 in
      sum_list_map_all_fins_from_eq_sum_range m k1 f;
      sum_list_cons (f (k <: fin m)) (map f (all_fins_from m k1));
      sum_range_unfold_left
        (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k m;
      reflexivity (f (k <: fin m));
      g.add_congruence
        (f (k <: fin m))
        (sum_list (map f (all_fins_from m k1)))
        (f (k <: fin m))
        (sum_range (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k1 m)
    end
#pop-options

let sum_list_map_all_fins_eq_fin_sum
  (#t: Type) {| g: add_comm_group t |}
  (m: nat) (f: fin m -> t)
  : Lemma (sum_list (map f (all_fins m)) = fin_sum f)
  = sum_list_map_all_fins_from_eq_sum_range m 0 f

(* -------------------------------------------------------------------- *)
(*  Split-head for sum_over_fns_to.                                     *)
(* -------------------------------------------------------------------- *)

unfold let extend_fin_sum
  (#t: Type) {| g: add_comm_group t |}
  (n m: nat) (gg: fin_map (Prims.op_Addition n 1) m -> t) (phi: fin_map n m) : t =
  fin_sum (fun (k: fin m) -> gg (extend_fn #n #m phi k))

let extend_fin_sum_def
  (#t: Type) {| g: add_comm_group t |}
  (n m: nat) (gg: fin_map (Prims.op_Addition n 1) m -> t) (phi: fin_map n m)
  : Lemma (extend_fin_sum n m gg phi
           == fin_sum (fun (k: fin m) -> gg (extend_fn #n #m phi k))) = ()

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let sum_over_fns_to_split_head
  (#t: Type) {| g: add_comm_group t |}
  (n m: nat) (gg: fin_map (Prims.op_Addition n 1) m -> t)
  : Lemma (sum_over_fns_to (Prims.op_Addition n 1) m gg
         = sum_over_fns_to n m (extend_fin_sum #t #g n m gg))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let n1 = Prims.op_Addition n 1 in
    all_fns_to_succ_eq n m;
    map_concatMap gg
      (extend_to_all #n #m)
      (all_fns_to n m);
    sum_list_concatMap
      (fun (phi: fin_map n m) ->
         map gg (extend_to_all #n #m phi))
      (all_fns_to n m);
    let h' (phi: fin_map n m) : t =
      fin_sum (fun (k: fin m) -> gg (extend_fn #n #m phi k))
    in
    let pf (phi: fin_map n m)
      : Lemma
        (sum_list (map gg (extend_to_all #n #m phi))
         = h' phi)
      = assert (extend_to_all #n #m phi ==
                map (extend_fn #n #m phi) (all_fins m))
          by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
        sum_list_map_compose gg (extend_fn #n #m phi) (all_fins m);
        sum_list_map_all_fins_eq_fin_sum m (fun (j: fin m) -> gg (extend_fn #n #m phi j));
        transitivity
          (sum_list (map gg (extend_to_all #n #m phi)))
          (sum_list (map (fun (j: fin m) -> gg (extend_fn #n #m phi j)) (all_fins m)))
          (h' phi)
    in
    Classical.forall_intro pf;
    sum_list_map_congruence
      (fun (phi: fin_map n m) ->
         sum_list (map gg (extend_to_all #n #m phi)))
      h'
      (all_fns_to n m) (fun _ -> ());
    let cong_h_ext (phi: fin_map n m) : Lemma (h' phi = extend_fin_sum #t #g n m gg phi)
      = extend_fin_sum_def #t #g n m gg phi;
        reflexivity (h' phi) in
    Classical.forall_intro cong_h_ext;
    sum_list_map_congruence h' (extend_fin_sum #t #g n m gg) (all_fns_to n m) (fun _ -> ());
    transitivity
      (sum_over_fns_to n1 m gg)
      (sum_list (map h' (all_fns_to n m)))
      (sum_over_fns_to n m (extend_fin_sum #t #g n m gg))
#pop-options

(* -------------------------------------------------------------------- *)
(*  sum_list scalar multiplication on the right.                        *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
let rec sum_list_map_mul_right
  (#a:Type) (#t:Type) {| r: ring t |}
  (f: a -> t) (c: t) (xs: list a)
  : Lemma (ensures sum_list (map f xs) * c = sum_list (map (fun x -> f x * c) xs))
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] ->
        sum_list_nil #t #(acg_of_r t #r);
        zero_mul_x c
    | hx :: rest ->
        sum_list_map_mul_right #a #t #r f c rest;
        sum_list_cons (f hx) (map f rest);
        sum_list_cons (f hx * c) (map (fun x -> f x * c) rest);
        let h = f hx in
        let trest = sum_list (map f rest) in
        let crest = sum_list (map (fun x -> f x * c) rest) in
        r.right_distributivity c h trest;
        reflexivity (h * c);
        r.r_add.add_congruence (h * c) (trest * c) (h * c) crest;
        transitivity (sum_list (map f (hx :: rest)) * c)
                     ((h + trest) * c)
                     (h * c + trest * c);
        transitivity (sum_list (map f (hx :: rest)) * c)
                     (h * c + trest * c)
                     (h * c + crest)
#pop-options

(* -------------------------------------------------------------------- *)
(*  sum_over_fns_to scalar mul right.                                   *)
(* -------------------------------------------------------------------- *)

let sum_over_fns_to_mul_right
  (#t: Type) {| r: ring t |}
  (n m: nat) (f: fin_map n m -> t) (c: t)
  : Lemma (sum_over_fns_to n m f * c
         = sum_over_fns_to n m (fun (phi: fin_map n m) -> f phi * c))
  = sum_list_map_mul_right f c (all_fns_to n m)

(* -------------------------------------------------------------------- *)
(*  Pointwise inductive step: prod_range over extended function.        *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let prod_range_extend_pointwise
  (#t: Type) {| r: ring t |}
  (n m: nat) (a: fin (Prims.op_Addition n 1) -> fin m -> t)
  (phi: fin_map n m) (k: fin m)
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
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let body_full (i: nat) : t =
      if i < Prims.op_Addition n 1
      then a (i <: fin (Prims.op_Addition n 1))
             ((extend_fn #n #m phi k) (i <: fin (Prims.op_Addition n 1)))
      else one in
    let body_short (i: nat) : t =
      if i < n
      then a (i <: fin (Prims.op_Addition n 1)) (phi (i <: fin n))
      else one in
    prod_range_unfold_right body_full 0 (Prims.op_Addition n 1);
    let cong (i: nat)
      : Lemma (0 <= i /\ i < n ==> body_full i = body_short i)
      = if 0 <= i && i < n then
          reflexivity (a (i <: fin (Prims.op_Addition n 1)) (phi (i <: fin n)))
    in
    Classical.forall_intro cong;
    prod_range_congruence body_full body_short 0 n (fun _ -> ());
    reflexivity (a (n <: fin (Prims.op_Addition n 1)) k);
    r.mul_congruence
      (prod_range body_full 0 n)
      (body_full n)
      (prod_range body_short 0 n)
      (a (n <: fin (Prims.op_Addition n 1)) k);
    transitivity
      (prod_range body_full 0 (Prims.op_Addition n 1))
      (prod_range body_full 0 n * body_full n)
      (prod_range body_short 0 n * a (n <: fin (Prims.op_Addition n 1)) k)
#pop-options

(* Helper: each phi maps to the sum over k of g_rhs(extend phi k). *)
#restart-solver
#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let per_phi_lemma
  (#t: Type) {| r: ring t |}
  (n_m1 m: nat) (a: fin (Prims.op_Addition n_m1 1) -> fin m -> t)
  (phi: fin_map n_m1 m)
  : Lemma (
    prod_range (fun (i: nat) ->
        if i < n_m1 then a (i <: fin (Prims.op_Addition n_m1 1)) (phi (i <: fin n_m1)) else one) 0 n_m1
    * fin_sum (a (n_m1 <: fin (Prims.op_Addition n_m1 1)))
    = fin_sum (fun (k: fin m) ->
        prod_range (fun (i: nat) ->
          if i < Prims.op_Addition n_m1 1
          then a (i <: fin (Prims.op_Addition n_m1 1))
                 ((extend_fn #n_m1 #m phi k) (i <: fin (Prims.op_Addition n_m1 1)))
          else one) 0 (Prims.op_Addition n_m1 1)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let g_ih = prod_range (fun (i: nat) ->
        if i < n_m1 then a (i <: fin (Prims.op_Addition n_m1 1)) (phi (i <: fin n_m1)) else one) 0 n_m1 in
    fin_sum_mul_left #t #r #m g_ih (a (n_m1 <: fin (Prims.op_Addition n_m1 1)));
    (* g_ih * fin_sum (a n_m1) = fin_sum (pointwise_mul (const g_ih) (a n_m1)) *)
    let pw_bridge (k: fin m) : Lemma
      (pointwise_mul (const g_ih) (a (n_m1 <: fin (Prims.op_Addition n_m1 1))) k
       = g_ih * a (n_m1 <: fin (Prims.op_Addition n_m1 1)) k)
      = pointwise_mul_unfold (const g_ih) (a (n_m1 <: fin (Prims.op_Addition n_m1 1))) k;
        const_unfold g_ih k;
        reflexivity (g_ih * a (n_m1 <: fin (Prims.op_Addition n_m1 1)) k) in
    fin_sum_congruence (pointwise_mul (const g_ih) (a (n_m1 <: fin (Prims.op_Addition n_m1 1))))
                  (fun (k: fin m) -> g_ih * a (n_m1 <: fin (Prims.op_Addition n_m1 1)) k) pw_bridge;
    let pk (k: fin m) : Lemma (
        g_ih * a (n_m1 <: fin (Prims.op_Addition n_m1 1)) k =
        prod_range (fun (i: nat) ->
          if i < Prims.op_Addition n_m1 1
          then a (i <: fin (Prims.op_Addition n_m1 1))
                 ((extend_fn #n_m1 #m phi k) (i <: fin (Prims.op_Addition n_m1 1)))
          else one) 0 (Prims.op_Addition n_m1 1))
      = prod_range_extend_pointwise #t #r n_m1 m a phi k
    in
    Classical.forall_intro pk;
    fin_sum_congruence #t #(acg_of_r t #r) #m
      (fun (k: fin m) -> g_ih * a (n_m1 <: fin (Prims.op_Addition n_m1 1)) k)
      (fun (k: fin m) -> prod_range (fun (i: nat) ->
          if i < Prims.op_Addition n_m1 1
          then a (i <: fin (Prims.op_Addition n_m1 1))
                 ((extend_fn #n_m1 #m phi k) (i <: fin (Prims.op_Addition n_m1 1)))
          else one) 0 (Prims.op_Addition n_m1 1)) (fun _ -> ());
    trans3
      (g_ih * fin_sum (a (n_m1 <: fin (Prims.op_Addition n_m1 1))))
      (fin_sum (pointwise_mul (const g_ih) (a (n_m1 <: fin (Prims.op_Addition n_m1 1)))))
      (fin_sum (fun (k: fin m) -> g_ih * a (n_m1 <: fin (Prims.op_Addition n_m1 1)) k))
      (fin_sum (fun (k: fin m) -> prod_range (fun (i: nat) ->
          if i < Prims.op_Addition n_m1 1
          then a (i <: fin (Prims.op_Addition n_m1 1))
                 ((extend_fn #n_m1 #m phi k) (i <: fin (Prims.op_Addition n_m1 1)))
          else one) 0 (Prims.op_Addition n_m1 1)))
#pop-options

(* -------------------------------------------------------------------- *)
(*  Main theorem: prod_range_of_fin_sum.                                *)
(*                                                                       *)
(*    Pi_i (Sigma_k a i k) = Sigma_phi Pi_i (a i (phi i))                *)
(* -------------------------------------------------------------------- *)

#restart-solver
#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
let rec prod_range_of_fin_sum
  (#t: Type) {| r: ring t |}
  (n m: nat) (a: fin n -> fin m -> t)
  : Lemma
    (ensures
      prod_range (fun (i: nat) ->
        if i < n then fin_sum (a (i <: fin n)) else one) 0 n
    = sum_over_fns_to #t #(acg_of_r t #r) n m
        (fun (phi: fin_map n m) ->
          prod_range (fun (i: nat) ->
            if i < n then a (i <: fin n) (phi (i <: fin n)) else one) 0 n))
    (decreases n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if n = 0 then begin
     let inner_body (phi: fin_map n m) (i: nat) : t =
       if i < n then a (i <: fin n) (phi (i <: fin n)) else one in
     let inner_body_def (phi: fin_map n m) (i: nat) : Lemma (inner_body phi i ==
       (if i < n then a (i <: fin n) (phi (i <: fin n)) else one #t)) = () in
     Classical.forall_intro_2 inner_body_def;
     let g_rhs (phi: fin_map n m) : t =
       prod_range (inner_body phi) 0 n in
     let g_rhs_def (phi: fin_map n m) : Lemma (g_rhs phi ==
       prod_range (inner_body phi) 0 n) = () in
     Classical.forall_intro g_rhs_def;
     assert (all_fns_to 0 m == [nullary m]);
     sum_list_cons #t #(acg_of_r t #r) (g_rhs (nullary m)) [];
     sum_list_nil #t #(acg_of_r t #r);
     x_plus_zero (g_rhs (nullary m));
     assert (sum_over_fns_to #t #(acg_of_r t #r) n m g_rhs = g_rhs (nullary m));
     prod_range_empty (inner_body (nullary m)) 0 0;
     assert (g_rhs (nullary m) = one #t);
     prod_range_empty
       (fun (i: nat) -> if i < n then fin_sum (a (i <: fin n)) else one) 0 0;
     let lhs = prod_range (fun (i: nat) ->
       if i < n then fin_sum (a (i <: fin n)) else one) 0 n in
     assert (lhs = one #t);
     symmetry lhs (one #t);
     symmetry (sum_over_fns_to #t #(acg_of_r t #r) n m g_rhs) (g_rhs (nullary m));
     symmetry (g_rhs (nullary m)) (one #t);
     transitivity lhs (one #t) (sum_over_fns_to #t #(acg_of_r t #r) n m g_rhs);
     let pc_lambda (phi: fin_map n m) : t =
       prod_range (fun (i: nat) ->
         if i < n then a (i <: fin n) (phi (i <: fin n)) else one) 0 n in
     let pc_lambda_def (phi: fin_map n m) : Lemma (pc_lambda phi ==
       prod_range (fun (i: nat) ->
         if i < n then a (i <: fin n) (phi (i <: fin n)) else one) 0 n) = () in
     Classical.forall_intro pc_lambda_def;
     let cong_prod (phi: fin_map n m) : Lemma (g_rhs phi = pc_lambda phi)
       = let body2 (i: nat) : t =
           if i < n then a (i <: fin n) (phi (i <: fin n)) else one in
         let cong_i (i: nat) : Lemma (0 <= i /\ i < n ==> inner_body phi i = body2 i)
           = if 0 <= i && i < n then
               reflexivity (a (i <: fin n) (phi (i <: fin n)))
         in
         Classical.forall_intro cong_i;
         prod_range_congruence (inner_body phi) body2 0 n (fun _ -> ())
     in
     Classical.forall_intro cong_prod;
     sum_list_map_congruence g_rhs pc_lambda (all_fns_to n m) (fun _ -> ());
     transitivity lhs
       (sum_over_fns_to #t #(acg_of_r t #r) n m g_rhs)
       (sum_over_fns_to #t #(acg_of_r t #r) n m pc_lambda)
    end else begin
      let n_m1 : nat = Prims.op_Subtraction n 1 in
      assert (Prims.op_Addition n_m1 1 == n);
      [@@inline_let] let a' : fin n_m1 -> fin m -> t =
        fun (i: fin n_m1) (k: fin m) -> a (i <: fin n) k in
      prod_range_of_fin_sum #t #r n_m1 m a';
      [@@inline_let] let body_lhs (i: nat) : t =
        if i < n then fin_sum (a (i <: fin n)) else one #t in
      [@@inline_let] let body_ih_lhs (i: nat) : t =
        if i < n_m1 then fin_sum (a' (i <: fin n_m1)) else one #t in
      [@@inline_let] let g_rhs (phi: fin_map n m) : t =
        prod_range (fun (i: nat) ->
          if i < n then a (i <: fin n) (phi (i <: fin n)) else one #t) 0 n in
      [@@inline_let] let g_ih (phi: fin_map n_m1 m) : t =
        prod_range (fun (i: nat) ->
          if i < n_m1 then a' (i <: fin n_m1) (phi (i <: fin n_m1)) else one #t) 0 n_m1 in
      prod_range_unfold_right body_lhs 0 n;
      let s_n : t = fin_sum (a (n_m1 <: fin n)) in
      assert (body_lhs n_m1 == s_n);
      let cong_lhs (i: nat)
        : Lemma (0 <= i /\ i < n_m1 ==> body_lhs i = body_ih_lhs i)
        = if 0 <= i && i < n_m1 then begin
            let aux (k: fin m) : Lemma (a (i <: fin n) k = a' (i <: fin n_m1) k)
              = reflexivity (a (i <: fin n) k) in
            Classical.forall_intro aux;
            fin_sum_congruence (a (i <: fin n)) (a' (i <: fin n_m1)) (fun _ -> ())
          end
      in
      Classical.forall_intro cong_lhs;
      prod_range_congruence body_lhs body_ih_lhs 0 n_m1 (fun _ -> ());
      let sum_ih : t = sum_over_fns_to #t #(acg_of_r t #r) n_m1 m g_ih in
      let pr_n_m1 : t = prod_range body_lhs 0 n_m1 in
      let pr_ih   : t = prod_range body_ih_lhs 0 n_m1 in
      transitivity pr_n_m1 pr_ih sum_ih;
      reflexivity s_n;
      r.mul_congruence pr_n_m1 s_n sum_ih s_n;
      sum_over_fns_to_mul_right #t #r n_m1 m g_ih s_n;
      let h1 (pp: fin_map n_m1 m) : t = g_ih pp * s_n in
      let g_step (pp: fin_map n_m1 m) : t =
        fin_sum (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m pp k)) in
      let per_phi (phi: fin_map n_m1 m)
        : Lemma (h1 phi = g_step phi)
        = let h1_def () : Lemma (h1 phi == g_ih phi * s_n) = () in
          h1_def ();
          fin_sum_mul_left #t #r #m (g_ih phi) (a (n_m1 <: fin n));
          (* g_ih phi * fin_sum (a (n_m1 ...)) = fin_sum (pointwise_mul (const (g_ih phi)) (a (n_m1 ...))) *)
          let pw_b (k: fin m) : Lemma
            (pointwise_mul (const (g_ih phi)) (a (n_m1 <: fin n)) k
             = g_ih phi * a (n_m1 <: fin n) k)
            = pointwise_mul_unfold (const (g_ih phi)) (a (n_m1 <: fin n)) k;
              const_unfold (g_ih phi) k;
              reflexivity (g_ih phi * a (n_m1 <: fin n) k) in
          fin_sum_congruence
            (pointwise_mul (const (g_ih phi)) (a (n_m1 <: fin n)))
            (fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k) pw_b;
          transitivity
            (g_ih phi * fin_sum (a (n_m1 <: fin n)))
            (fin_sum (pointwise_mul (const (g_ih phi)) (a (n_m1 <: fin n))))
            (fin_sum (fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k));
          let body_mul (k: fin m) : t = g_ih phi * a (n_m1 <: fin n) k in
          let body_ext (k: fin m) : t = g_rhs (extend_fn #n_m1 #m phi k) in
          let body_mul_def (k: fin m) : Lemma (body_mul k == g_ih phi * a (n_m1 <: fin n) k) = () in
          let body_ext_def (k: fin m) : Lemma (body_ext k == g_rhs (extend_fn #n_m1 #m phi k)) = () in
          let g_step_def () : Lemma (g_step phi ==
            fin_sum (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k))) = () in
          Classical.forall_intro body_mul_def;
          Classical.forall_intro body_ext_def;
          g_step_def ();
          let per_k (k: fin m) : Lemma (body_mul k = body_ext k)
            = let phi_ext : fin_map n m = extend_fn #n_m1 #m phi k in
              let gd_body (i: nat) : t =
                if i < n then a (i <: fin n) (phi_ext (i <: fin n)) else one #t in
              let body_ih_inner (i: nat) : t =
                if i < n_m1 then a' (i <: fin n_m1) (phi (i <: fin n_m1)) else one #t in
              let gd_body_def (i: nat) : Lemma (gd_body i ==
                (if i < n then a (i <: fin n) (phi_ext (i <: fin n)) else one #t)) = () in
              let phi_ext_def (i: fin n) : Lemma (phi_ext i ==
                (if i = n_m1 then k else phi (i <: fin n_m1))) = () in
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
              prod_range_congruence gd_body body_ih_inner 0 n_m1 (fun _ -> ());
              reflexivity (a (n_m1 <: fin n) k);
              r.mul_congruence
                (prod_range gd_body 0 n_m1) (a (n_m1 <: fin n) k)
                (prod_range body_ih_inner 0 n_m1) (a (n_m1 <: fin n) k);
              transitivity
                (prod_range gd_body 0 n)
                (prod_range gd_body 0 n_m1 * a (n_m1 <: fin n) k)
                (prod_range body_ih_inner 0 n_m1 * a (n_m1 <: fin n) k);
              symmetry
                (prod_range gd_body 0 n)
                (prod_range body_ih_inner 0 n_m1 * a (n_m1 <: fin n) k)
          in
          Classical.forall_intro per_k;
          let cong_bm (k: fin m) : Lemma
            ((fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k) k = body_mul k)
            = reflexivity (g_ih phi * a (n_m1 <: fin n) k) in
          Classical.forall_intro cong_bm;
          fin_sum_congruence #t #(acg_of_r t #r) #m
            (fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k)
            body_mul (fun _ -> ());
          fin_sum_congruence #t #(acg_of_r t #r) #m body_mul body_ext (fun _ -> ());
          let cong_be (k: fin m) : Lemma
            (body_ext k = (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k)) k)
            = reflexivity (g_rhs (extend_fn #n_m1 #m phi k)) in
          Classical.forall_intro cong_be;
          fin_sum_congruence #t #(acg_of_r t #r) #m body_ext
            (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k)) (fun _ -> ());
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
      sum_list_map_congruence h1 g_step (all_fns_to n_m1 m) (fun _ -> ());
      sum_over_fns_to_split_head #t #(acg_of_r t #r) n_m1 m g_rhs;
      let cong_ext (phi: fin_map n_m1 m) : Lemma
        (extend_fin_sum #t #(acg_of_r t #r) n_m1 m g_rhs phi = g_step phi)
        = assert (extend_fin_sum #t #(acg_of_r t #r) n_m1 m g_rhs phi ==
                  fin_sum (fun (k: fin m) -> g_rhs (extend_fn #n_m1 #m phi k)))
            by (FStar.Tactics.norm [delta_only [`%extend_fin_sum]]; FStar.Tactics.trefl ());
          reflexivity (g_step phi) in
      Classical.forall_intro cong_ext;
      sum_list_map_congruence
        (extend_fin_sum #t #(acg_of_r t #r) n_m1 m g_rhs)
        g_step (all_fns_to n_m1 m) (fun _ -> ());
      transitivity
        (sum_over_fns_to #t #(acg_of_r t #r) (Prims.op_Addition n_m1 1) m g_rhs)
        (sum_over_fns_to #t #(acg_of_r t #r) n_m1 m (extend_fin_sum #t #(acg_of_r t #r) n_m1 m g_rhs))
        (sum_over_fns_to #t #(acg_of_r t #r) n_m1 m g_step);
      let lhs_n = prod_range body_lhs 0 n in
      let rhs_n = sum_over_fns_to #t #(acg_of_r t #r) n m g_rhs in
      let t1 : t = pr_n_m1 * s_n in
      let t2 : t = sum_ih * s_n in
      let t3 : t = sum_over_fns_to #t #(acg_of_r t #r) n_m1 m h1 in
      let t4 : t = sum_over_fns_to #t #(acg_of_r t #r) n_m1 m g_step in
      let t5 : t = sum_over_fns_to #t #(acg_of_r t #r) n_m1 m (fun (phi: fin_map n_m1 m) -> g_ih phi * s_n) in
      reflexivity lhs_n; reflexivity rhs_n;
      reflexivity t1; reflexivity t2; reflexivity t3; reflexivity t4; reflexivity t5;
      assert (lhs_n = t1);
      assert (t1 = t2);
      let cong_h1 (phi: fin_map n_m1 m) : Lemma
        ((fun (phi: fin_map n_m1 m) -> g_ih phi * s_n) phi = h1 phi)
        = reflexivity (g_ih phi * s_n) in
      Classical.forall_intro cong_h1;
      sum_list_map_congruence
        (fun (phi: fin_map n_m1 m) -> g_ih phi * s_n) h1 (all_fns_to n_m1 m) (fun _ -> ());
      assert (t5 = t3);
      assert (t2 = t5);
      assert (t3 = t4);
      assert (rhs_n == sum_over_fns_to #t #(acg_of_r t #r) (Prims.op_Addition n_m1 1) m g_rhs);
      reflexivity rhs_n;
      assert (rhs_n = sum_over_fns_to #t #(acg_of_r t #r) (Prims.op_Addition n_m1 1) m g_rhs);
      assert (sum_over_fns_to #t #(acg_of_r t #r) (Prims.op_Addition n_m1 1) m g_rhs = t4);
      transitivity rhs_n (sum_over_fns_to #t #(acg_of_r t #r) (Prims.op_Addition n_m1 1) m g_rhs) t4;
      symmetry rhs_n t4;
      transitivity lhs_n t1 t2;
      transitivity lhs_n t2 t5;
      transitivity lhs_n t5 t3;
      transitivity lhs_n t3 t4;
      transitivity lhs_n t4 rhs_n
    end
#pop-options
