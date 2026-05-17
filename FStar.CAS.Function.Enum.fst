module FStar.CAS.Function.Enum

(*
   Enumeration of all functions `fin n -> fin n`.

   Modeled on `FStar.CAS.Permutation.Enum`: we build a list
   `all_funs n` of length `n^n` containing (up to pointwise
   equality) every total function `fin n -> fin n`, and we
   define `sum_over_funs` along that list together with the
   basic congruence / distributivity lemmas needed by
   downstream Cauchy-Binet-style reasoning.
*)

open FStar.CAS.Permutation       (* for the [fin n] type *)
open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes
open FStar.CAS.FinSum

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses

(* -------------------------------------------------------------------- *)
(*  Types                                                                *)
(* -------------------------------------------------------------------- *)

(*  Total functions `fin n -> fin m`. The intermediate enumeration is
    parameterised by both arities; the user-facing `fn_endo` and
    `all_funs` then set m = n. *)
let fn_to (n m: nat) = fin n -> fin m

let fn_endo (n: nat) = fn_to n n

let fn_eq (#n: nat) (f g: fn_endo n) : prop = forall (i: fin n). f i == g i

(* -------------------------------------------------------------------- *)
(*  Empty domain: there is exactly one function fin 0 -> fin m.          *)
(* -------------------------------------------------------------------- *)

let nullary (m: nat) : fn_to 0 m =
  fun (i: fin 0) -> false_elim #(fin m) ()

(* -------------------------------------------------------------------- *)
(*  Listing fin m.                                                       *)
(* -------------------------------------------------------------------- *)

let rec all_fins_from (m: nat) (k: nat{k <= m})
  : Tot (list (fin m)) (decreases (Prims.op_Subtraction m k))
  = if k = m then []
    else (k <: fin m) :: all_fins_from m (Prims.op_Addition k 1)

let all_fins (m: nat) : list (fin m) = all_fins_from m 0

let rec all_fins_from_length (m: nat) (k: nat{k <= m})
  : Lemma (ensures L.length (all_fins_from m k) == Prims.op_Subtraction m k)
          (decreases (Prims.op_Subtraction m k))
  = if k = m then ()
    else all_fins_from_length m (Prims.op_Addition k 1)

let all_fins_length (m: nat)
  : Lemma (L.length (all_fins m) == m)
  = all_fins_from_length m 0

let rec all_fins_from_mem (m: nat) (k: nat{k <= m}) (j: fin m)
  : Lemma (requires k <= j)
          (ensures  L.memP j (all_fins_from m k))
          (decreases (Prims.op_Subtraction m k))
  = if k = j then ()
    else all_fins_from_mem m (Prims.op_Addition k 1) j

let all_fins_mem (m: nat) (j: fin m)
  : Lemma (L.memP j (all_fins m))
  = all_fins_from_mem m 0 j

(* -------------------------------------------------------------------- *)
(*  Extending a function: given phi : fin n -> fin m and j: fin m,       *)
(*  produce a function fin (n+1) -> fin m by appending j on the new      *)
(*  top index.                                                           *)
(* -------------------------------------------------------------------- *)

let extend_fn (#n #m: nat) (phi: fn_to n m) (j: fin m) : fn_to (Prims.op_Addition n 1) m
  = fun (i: fin (Prims.op_Addition n 1)) ->
      if i = n then j
      else
        let i' : fin n = i in
        phi i'

(* -------------------------------------------------------------------- *)
(*  Recursive enumeration of fn_to n m.                                  *)
(* -------------------------------------------------------------------- *)

let all_fns_to_succ (#k m: nat) (xs: list (fn_to k m)) : list (fn_to (Prims.op_Addition k 1) m)
  = L.concatMap
      (fun (phi: fn_to k m) ->
          L.map (fun (j: fin m) -> extend_fn #k #m phi j) (all_fins m))
      xs

let rec all_fns_to (n m: nat) : Tot (list (fn_to n m)) (decreases n)
  = match n with
    | 0 -> [nullary m]
    | _ ->
        all_fns_to_succ #(Prims.op_Subtraction n 1) m
          (all_fns_to (Prims.op_Subtraction n 1) m)

let all_funs (n: nat) : list (fn_endo n) = all_fns_to n n

(* -------------------------------------------------------------------- *)
(*  Basic: all_funs is non-empty (so the enumeration is well-formed).    *)
(* -------------------------------------------------------------------- *)

let rec all_fns_to_nonempty (n m: nat)
  : Lemma (ensures L.length (all_fns_to n m) > 0 \/ m = 0)
          (decreases n)
  = if n = 0 then ()
    else all_fns_to_nonempty (Prims.op_Subtraction n 1) m

(* -------------------------------------------------------------------- *)
(*  Length: |all_fns_to n m| = m^n.                                      *)
(* -------------------------------------------------------------------- *)

let rec pow_nat (m: nat) (n: nat) : Tot nat
  = if n = 0 then 1 else Prims.op_Star m (pow_nat m (Prims.op_Subtraction n 1))

(* Length of concatMap over a constant-length-mapped function. *)
let rec length_concatMap_const_fn
  (#a #b: Type)
  (f: a -> list b)
  (xs: list a)
  (c: nat)
  : Lemma (requires forall (x: a). L.memP x xs ==> L.length (f x) == c)
          (ensures L.length (L.concatMap f xs) == Prims.op_Star c (L.length xs))
  = match xs with
    | [] -> ()
    | x :: tl ->
        length_concatMap_const_fn f tl c;
        L.append_length (f x) (L.concatMap f tl)

let rec map_length (#a #b: Type) (f: a -> b) (xs: list a)
  : Lemma (ensures L.length (L.map f xs) == L.length xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: tl -> map_length f tl

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let all_fns_to_succ_eq (k m: nat)
  : Lemma (all_fns_to (Prims.op_Addition k 1) m ==
           all_fns_to_succ #k m (all_fns_to k m))
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let all_fns_to_succ_length (k m: nat) (xs: list (fn_to k m))
  : Lemma (ensures L.length (all_fns_to_succ #k m xs)
                   == Prims.op_Star m (L.length xs))
  = all_fins_length m;
    let f : (fn_to k m -> list (fn_to (Prims.op_Addition k 1) m)) =
      fun phi -> L.map (fun (j: fin m) -> extend_fn #k #m phi j) (all_fins m) in
    let aux (phi: fn_to k m) : Lemma (L.length (f phi) == m) =
      map_length (fun (j: fin m) -> extend_fn #k #m phi j) (all_fins m)
    in
    Classical.forall_intro aux;
    length_concatMap_const_fn f xs m
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec all_fns_to_length (n m: nat)
  : Lemma (ensures L.length (all_fns_to n m) == pow_nat m n)
          (decreases n)
  = if n = 0 then ()
    else begin
      let k : nat = Prims.op_Subtraction n 1 in
      all_fns_to_length k m;
      all_fns_to_succ_length k m (all_fns_to k m);
      all_fns_to_succ_eq k m
    end
#pop-options

let all_funs_length (n: nat)
  : Lemma (L.length (all_funs n) == pow_nat n n)
  = all_fns_to_length n n

(* -------------------------------------------------------------------- *)
(*  Membership lemmas: concatMap and map.                                *)
(* -------------------------------------------------------------------- *)

let rec mem_concatMap_fn
  (#a #b: Type)
  (f: a -> list b)
  (y: a)
  (xs: list a)
  (x: b)
  : Lemma (requires L.memP y xs /\ L.memP x (f y))
          (ensures L.memP x (L.concatMap f xs))
  = match xs with
    | [] -> ()
    | h :: tl ->
        L.append_memP (f h) (L.concatMap f tl) x;
        let aux () : Lemma (requires L.memP y tl) (ensures L.memP x (L.concatMap f tl))
          = mem_concatMap_fn f y tl x in
        Classical.move_requires aux ()

let rec mem_map_fn
  (#a #b: Type)
  (f: a -> b)
  (y: a)
  (xs: list a)
  : Lemma (requires L.memP y xs)
          (ensures L.memP (f y) (L.map f xs))
  = match xs with
    | [] -> ()
    | h :: tl ->
        let aux () : Lemma (requires L.memP y tl) (ensures L.memP (f y) (L.map f tl))
          = mem_map_fn f y tl in
        Classical.move_requires aux ()

(* -------------------------------------------------------------------- *)
(*  Pointwise equality of fn_to.                                         *)
(* -------------------------------------------------------------------- *)

let fn_to_eq (#n #m: nat) (f g: fn_to n m) : prop =
  forall (i: fin n). f i == g i

unfold let fn_to_in_list (#n #m: nat) (f: fn_to n m) (xs: list (fn_to n m)) : prop =
  exists (g: fn_to n m). L.memP g xs /\ fn_to_eq f g

(* -------------------------------------------------------------------- *)
(*  Completeness of all_fns_to.                                          *)
(* -------------------------------------------------------------------- *)

(*  For n = 0, every function fin 0 -> fin m is trivially fn_to_eq to
    nullary m (vacuous forall). *)
let completeness_base_fn (m: nat) (f: fn_to 0 m)
  : Lemma (fn_to_in_list f (all_fns_to 0 m))
  = assert (fn_to_eq f (nullary m));
    assert (L.memP (nullary m) (all_fns_to 0 m))

(*  Helper: given phi : fn_to n m and j : fin m, extend_fn phi j is
    pointwise equal to any f : fn_to (n+1) m such that f n = j and
    f i = phi i for i < n. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let extend_fn_matches
  (#n #m: nat) (phi: fn_to n m) (j: fin m)
  (f: fn_to (Prims.op_Addition n 1) m)
  (i: fin (Prims.op_Addition n 1))
  : Lemma (requires f (n <: fin (Prims.op_Addition n 1)) == j /\
                    (forall (k: fin n). f (k <: fin (Prims.op_Addition n 1)) == phi k))
          (ensures  extend_fn #n #m phi j i == f i)
  = if i = n then ()
    else ()
#pop-options

(*  The truncation of f to fin n: phi (i: fin n) = f i. *)
let truncate_fn (#n #m: nat) (f: fn_to (Prims.op_Addition n 1) m) : fn_to n m
  = fun (i: fin n) -> f (i <: fin (Prims.op_Addition n 1))

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let completeness_step_fn (n m: nat) (f: fn_to (Prims.op_Addition n 1) m)
  (ih: (phi: fn_to n m -> Lemma (fn_to_in_list phi (all_fns_to n m))))
  : Lemma (fn_to_in_list f (all_fns_to (Prims.op_Addition n 1) m))
  = let phi0 : fn_to n m = truncate_fn #n #m f in
    let j    : fin m     = f (n <: fin (Prims.op_Addition n 1)) in
    ih phi0;
    let aux (phi: fn_to n m)
      : Lemma (requires L.memP phi (all_fns_to n m) /\ fn_to_eq phi0 phi)
              (ensures fn_to_in_list f (all_fns_to (Prims.op_Addition n 1) m))
      = let g : fn_to (Prims.op_Addition n 1) m = extend_fn #n #m phi j in
        (* membership of g *)
        all_fins_mem m j;
        mem_map_fn (fun (jj: fin m) -> extend_fn #n #m phi jj) j (all_fins m);
        mem_concatMap_fn
          (fun (psi: fn_to n m) ->
             L.map (fun (jj: fin m) -> extend_fn #n #m psi jj) (all_fins m))
          phi
          (all_fns_to n m)
          g;
        (* fn_to_eq f g *)
        let pf (i: fin (Prims.op_Addition n 1))
          : Lemma (f i == g i)
          = if i = n then ()
            else begin
              let i' : fin n = i in
              assert (phi0 i' == f i);
              assert (phi i' == phi0 i');
              assert (g i == phi i')
            end
        in
        Classical.forall_intro pf
    in
    Classical.exists_elim
      (fn_to_in_list f (all_fns_to (Prims.op_Addition n 1) m))
      #(fn_to n m)
      #(fun phi -> L.memP phi (all_fns_to n m) /\ fn_to_eq phi0 phi)
      ()
      (fun phi -> aux phi)
#pop-options

let rec all_fns_to_complete (n m: nat) (f: fn_to n m)
  : Lemma (ensures fn_to_in_list f (all_fns_to n m))
          (decreases n)
  = if n = 0 then completeness_base_fn m f
    else
      let k : nat = Prims.op_Subtraction n 1 in
      completeness_step_fn k m f (fun phi -> all_fns_to_complete k m phi)

let all_funs_complete (#n: nat) (f: fn_endo n)
  : Lemma (exists (g: fn_endo n). L.memP g (all_funs n) /\ fn_eq f g)
  = all_fns_to_complete n n f

(* -------------------------------------------------------------------- *)
(*  Sum over all functions.                                              *)
(* -------------------------------------------------------------------- *)

let sum_over_funs
  (#t: Type) {| acm: add_comm_monoid t |}
  (n: nat) (f: fn_endo n -> t) : t
  = sum_list (L.map f (all_funs n))

let sum_over_funs_congruence
  (#t: Type) {| acm: add_comm_monoid t |}
  (n: nat) (f g: fn_endo n -> t)
  : Lemma (requires forall (phi: fn_endo n).
                      L.memP phi (all_funs n) ==> f phi = g phi)
          (ensures sum_over_funs n f = sum_over_funs n g)
  = sum_list_map_congruence f g (all_funs n)

let sum_over_funs_add
  (#t: Type) {| acm: add_comm_monoid t |}
  (n: nat) (f g: fn_endo n -> t)
  : Lemma (sum_over_funs n (fun phi -> f phi + g phi)
         = sum_over_funs n f + sum_over_funs n g)
  = sum_list_map_add f g (all_funs n)

let sum_over_funs_neg
  (#t: Type) {| grp: add_comm_group t |}
  (n: nat) (f: fn_endo n -> t)
  : Lemma (sum_over_funs n (fun phi -> -(f phi)) = -(sum_over_funs n f))
  = sum_list_map_neg f (all_funs n)

let sum_over_funs_mul_left
  (#t: Type) {| r: semiring t |}
  (n: nat) (c: t) (f: fn_endo n -> t)
  : Lemma (c * sum_over_funs n f = sum_over_funs n (fun phi -> c * f phi))
  = sum_list_map_mul_left c f (all_funs n)

(* Sum of all-zero summands is zero. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec sum_list_all_zero
  (#t: Type) {| acm: add_comm_monoid t |}
  (xs: list t)
  : Lemma (requires forall (x: t). L.memP x xs ==> x = zero)
          (ensures sum_list xs = zero)
          (decreases xs)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    match xs with
    | [] -> ()
    | x :: tl ->
        sum_list_all_zero tl;
        assert (x = zero);
        assert (sum_list tl = zero);
        add_congruence x (sum_list tl) zero zero;
        left_add_identity (zero <: t);
        assert (sum_list (x :: tl) = x + sum_list tl);
        assert (x + sum_list tl = zero + zero);
        assert (zero + zero = (zero <: t));
        transitivity (sum_list (x :: tl)) (x + sum_list tl) (zero + zero);
        transitivity (sum_list (x :: tl)) (zero + zero) (zero <: t)
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let rec sum_list_map_all_zero
  (#a #t: Type) {| acm: add_comm_monoid t |}
  (f: a -> t) (xs: list a)
  : Lemma (requires forall (x: a). L.memP x xs ==> f x = zero)
          (ensures sum_list (L.map f xs) = zero)
          (decreases xs)
  = elim_equatable_laws t;
    transitivity_for_calc_proofs t;
    match xs with
    | [] -> sum_list_nil #t #acm
    | x :: tl ->
        sum_list_map_all_zero f tl;
        sum_list_cons (f x) (L.map f tl);
        add_congruence (f x) (sum_list (L.map f tl)) zero zero;
        left_add_identity (zero <: t);
        transitivity (sum_list (L.map f (x :: tl)))
                     (f x + sum_list (L.map f tl))
                     (zero + zero);
        transitivity (sum_list (L.map f (x :: tl)))
                     (zero + zero)
                     (zero <: t)
#pop-options

let sum_over_funs_all_zero
  (#t: Type) {| acm: add_comm_monoid t |}
  (n: nat) (f: fn_endo n -> t)
  : Lemma (requires forall (phi: fn_endo n). f phi = zero)
          (ensures sum_over_funs n f = zero)
  = sum_list_map_all_zero f (all_funs n)
(* -------------------------------------------------------------------- *)
(*  Decidable pointwise equality and counting.                            *)
(* -------------------------------------------------------------------- *)

let rec fn_to_eq_from (#n #m: nat) (f g: fn_to n m) (k: nat)
  : Tot bool (decreases nat_minus n k)
  = if k >= n then true
    else if f (k <: fin n) = g (k <: fin n) then fn_to_eq_from f g (nat_succ k)
    else false

let fn_to_eq_b (#n #m: nat) (f g: fn_to n m) : bool = fn_to_eq_from f g 0

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let rec fn_to_eq_b_spec (#n #m: nat) (f g: fn_to n m) (k: nat)
  : Lemma (ensures fn_to_eq_from f g k <==> (forall (i: fin n). (i <: nat) >= k ==> f i == g i))
          (decreases nat_minus n k)
  = if k >= n then ()
    else fn_to_eq_b_spec f g (nat_succ k)
#pop-options

(* fn_to_eq_b decomposes over extend_fn. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let fn_to_eq_b_extend (#k #m: nat) (f: fn_to (Prims.op_Addition k 1) m)
  (phi: fn_to k m) (j: fin m)
  : Lemma (fn_to_eq_b f (extend_fn #k #m phi j) <==>
           (fn_to_eq_b (fun (i: fin k) -> f (i <: fin (Prims.op_Addition k 1))) phi
            /\ f (k <: fin (Prims.op_Addition k 1)) == j))
  = fn_to_eq_b_spec f (extend_fn #k #m phi j) 0;
    fn_to_eq_b_spec (fun (i: fin k) -> f (i <: fin (Prims.op_Addition k 1))) phi 0
#pop-options

(* Count fn_to_eq matches in a list. *)
let rec fn_eq_count (#n #m: nat) (f: fn_to n m) (xs: list (fn_to n m))
  : Tot nat (decreases xs)
  = match xs with
  | [] -> 0
  | h :: tl -> Prims.op_Addition (if fn_to_eq_b f h then 1 else 0) (fn_eq_count f tl)

let rec fn_eq_count_append (#n #m: nat) (f: fn_to n m) (xs ys: list (fn_to n m))
  : Lemma (ensures fn_eq_count f (L.append xs ys) ==
           Prims.op_Addition (fn_eq_count f xs) (fn_eq_count f ys))
          (decreases xs)
  = match xs with
  | [] -> ()
  | _ :: tl -> fn_eq_count_append f tl ys

(* Each fin m value appears exactly once in all_fins m. *)
let rec all_fins_from_count (m: nat) (j: fin m) (k: nat{k <= m})
  : Lemma (ensures L.count j (all_fins_from m k) ==
           (if (j <: nat) >= k then 1 else 0))
          (decreases Prims.op_Subtraction m k)
  = if k = m then ()
    else all_fins_from_count m j (Prims.op_Addition k 1)

let all_fins_count_one (m: nat) (j: fin m)
  : Lemma (L.count j (all_fins m) == 1)
  = all_fins_from_count m j 0

(* Count of f in map(extend_fn phi)(js). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec fn_eq_count_map_extend (#k #m: nat)
  (f: fn_to (Prims.op_Addition k 1) m)
  (phi: fn_to k m) (js: list (fin m))
  : Lemma (ensures fn_eq_count f
             (L.map (fun (j: fin m) -> extend_fn #k #m phi j) js) ==
           (if fn_to_eq_b (fun (i: fin k) ->
                  f (i <: fin (Prims.op_Addition k 1))) phi
            then L.count (f (k <: fin (Prims.op_Addition k 1))) js
            else 0))
          (decreases js)
  = match js with
  | [] -> ()
  | j :: tl ->
      fn_to_eq_b_extend f phi j;
      fn_eq_count_map_extend f phi tl
#pop-options

(* all_fns_to_succ unfolds one step on cons. *)
private let all_fns_to_succ_cons (#k: nat) (m: nat) (phi: fn_to k m) (tl: list (fn_to k m))
  : Lemma (all_fns_to_succ #k m (phi :: tl) ==
           L.append (L.map (fun (j: fin m) -> extend_fn #k #m phi j) (all_fins m))
                    (all_fns_to_succ #k m tl))
  = ()

(* Counting through all_fns_to_succ reduces to counting the tail. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec count_through_succ (#k #m: nat)
  (f: fn_to (Prims.op_Addition k 1) m)
  (xs: list (fn_to k m))
  : Lemma (ensures fn_eq_count f (all_fns_to_succ #k m xs) ==
                   fn_eq_count (fun (i: fin k) ->
                     f (i <: fin (Prims.op_Addition k 1))) xs)
          (decreases xs)
  = let fk : fin m = f (k <: fin (Prims.op_Addition k 1)) in
    match xs with
    | [] -> ()
    | phi :: tl ->
        all_fns_to_succ_cons #k m phi tl;
        fn_eq_count_append f
          (L.map (fun (j: fin m) -> extend_fn #k #m phi j) (all_fins m))
          (all_fns_to_succ #k m tl);
        fn_eq_count_map_extend f phi (all_fins m);
        all_fins_count_one m fk;
        count_through_succ f tl
#pop-options

(* Every fn_to appears exactly once in all_fns_to. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec all_fns_to_count_one (n m: nat) (f: fn_to n m)
  : Lemma (ensures fn_eq_count f (all_fns_to n m) == 1)
          (decreases n)
  = if n = 0 then
      fn_to_eq_b_spec f (nullary m) 0
    else begin
      let k : nat = Prims.op_Subtraction n 1 in
      all_fns_to_succ_eq k m;
      count_through_succ #k #m f (all_fns_to k m);
      all_fns_to_count_one k m
        (fun (i: fin k) -> f (i <: fin n))
    end
#pop-options