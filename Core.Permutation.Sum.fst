module Core.Permutation.Sum

(*
   Sums of a function `f : permutation n -> t` over all permutations,
   where `t` is an additive commutative monoid.

   We sum `f` along the explicit list `all_permutations n` produced by
   `Core.Permutation.Enum`. This list has exactly `n!` elements,
   each `perm_eq`-equivalence class of `permutation n` appearing exactly
   once (completeness + no-dup).

   This module:

     - Defines `sum_over_perms`.
     - Sets up a list-permutation relation `list_perm` based on
       `perm_eq`-counts per equivalence class.
     - States (but does not yet fully prove) the headline *reindexing*
       lemma:

         sum_over_perms n (fun s -> f (compose s q)) = sum_over_perms n f

       for any fixed `q : permutation n`, provided `f` respects `perm_eq`.
*)

module TC = FStar.Tactics.Typeclasses
open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Algebra.Helpers
open Core.Permutation
open Core.Permutation.Enum
open Core.FinSum

module L = FStar.List.Tot

(* -------------------------------------------------------------------- *)
(*  Local trans_lemma helper (mirrors the private one in FinSum.fst).   *)
(* -------------------------------------------------------------------- *)

private let rec trans_condition (#t: Type) {| equatable t |}
                                (l: list t{L.length l > 1}) : bool
  = match l with
    | h1 :: tail ->
      match tail with
      | [h2] -> h1 = h2
      | h2 :: _ -> h1 = h2 && trans_condition tail

private let rec trans_lemma (#t: Type) {| equatable t |}
                            (xs: list t{L.length xs > 1})
  : Lemma (requires trans_condition xs)
          (ensures L.hd xs = L.last xs)
          (decreases xs)
  = match xs with
    | [_; _] -> ()
    | h1 :: h2 :: rest ->
      trans_lemma (h2 :: rest);
      transitivity h1 h2 (L.last rest)

(* Private aliases for removed Permutation API — now implemented via
   reveal_opaque + perm_eq_bool_from helpers. *)
private let perm_eq_sym (#n: nat) (p q: permutation n)
  : Lemma (requires perm_eq p q) (ensures perm_eq q p)
  = reveal_opaque (`%perm_eq) (perm_eq p q);
    reveal_opaque (`%perm_eq) (perm_eq q p);
    perm_eq_bool_from_sym p q 0

private let perm_eq_trans (#n: nat) (p q r: permutation n)
  : Lemma (requires perm_eq p q /\ perm_eq q r) (ensures perm_eq p r)
  = reveal_opaque (`%perm_eq) (perm_eq p q);
    reveal_opaque (`%perm_eq) (perm_eq q r);
    reveal_opaque (`%perm_eq) (perm_eq p r);
    perm_eq_bool_from_trans p q r 0

private let perm_eq_refl (#n: nat) (p: permutation n)
  : Lemma (perm_eq p p)
  = perm_eq_intro p p (fun _ -> ())

private let perm_eq_bool_refl (#n: nat) (p: permutation n)
  : Lemma (perm_eq p p) = perm_eq_refl p

(* -------------------------------------------------------------------- *)
(*  Definition.                                                         *)
(* -------------------------------------------------------------------- *)

let sum_over_perms
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t) : t
  = sum_list (L.map f (all_permutations n))

let sum_over_perms_reveal
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t)
  : Lemma (sum_over_perms n f == sum_list (L.map f (all_permutations n)))
  = ()

(* -------------------------------------------------------------------- *)
(*  Congruence under pointwise-equal functions.                         *)
(* -------------------------------------------------------------------- *)

let sum_over_perms_congruence
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f g: permutation n -> t)
  (h: (s: permutation n) -> Lemma (f s = g s))
  : Lemma (ensures sum_over_perms n f = sum_over_perms n g)
  = sum_list_map_congruence f g (all_permutations n) h

(* Negation distributes over sum_over_perms. *)
let sum_over_perms_neg
  (#t: Type) {| g: add_comm_group t |}
  (n: nat) (f: permutation n -> t)
  : Lemma (sum_over_perms n (pointwise_neg f) = (- (sum_over_perms n f)))
  = sum_list_map_neg f (all_permutations n)

let sum_over_perms_neg_named
  (#t: Type) {| g: add_comm_group t |}
  (n: nat) (nf f: permutation n -> t)
  (h: (s: permutation n) -> Lemma (nf s = (- (f s))))
  : Lemma (ensures sum_over_perms n nf = (- (sum_over_perms n f)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_over_perms_neg n f;
    let h' (s: permutation n) : Lemma (nf s = pointwise_neg f s)
      = h s;
        pointwise_neg_unfold f s;
        symmetry (pointwise_neg f s) ((- (f s))) in
    sum_over_perms_congruence n nf (pointwise_neg f) h';
    transitivity (sum_over_perms n nf)
                 (sum_over_perms n (pointwise_neg f))
                 ((- (sum_over_perms n f)))

(* Pointwise additivity. *)
let sum_over_perms_add
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f g: permutation n -> t)
  : Lemma (sum_over_perms n (pointwise_add f g)
         = sum_over_perms n f + sum_over_perms n g)
  = sum_list_map_add f g (all_permutations n)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let sum_over_perms_add_named
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (s f g: permutation n -> t)
  (h: (p: permutation n) -> Lemma (s p = f p + g p))
  : Lemma (ensures  sum_over_perms n s = sum_over_perms n f + sum_over_perms n g)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_over_perms_add n f g;
    let h' (p: permutation n) : Lemma (s p = pointwise_add f g p)
      = h p;
        pointwise_add_unfold f g p;
        symmetry (pointwise_add f g p) (f p + g p) in
    sum_over_perms_congruence n s (pointwise_add f g) h';
    transitivity (sum_over_perms n s)
                 (sum_over_perms n (pointwise_add f g))
                 (sum_over_perms n f + sum_over_perms n g)
#pop-options

(* Left-scaling distributes over sum_over_perms. *)
let sum_over_perms_mul_left
  (#t: Type) {| r: ring t |}
  (n: nat) (c: t) (f: permutation n -> t)
  : Lemma (c * sum_over_perms n f = sum_over_perms n (pointwise_mul (const c) f))
  = sum_list_map_mul_left c f (all_permutations n)

let sum_over_perms_mul_left_named
  (#t: Type) {| r: ring t |}
  (n: nat) (c: t) (cf f: permutation n -> t)
  (h: (s: permutation n) -> Lemma (cf s = c * f s))
  : Lemma (ensures  sum_over_perms n cf = c * sum_over_perms n f)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_over_perms_mul_left n c f;
    let h' (s: permutation n) : Lemma (cf s = pointwise_mul (const c) f s)
      = h s;
        pointwise_mul_unfold (const c) f s;
        const_unfold c s;
        symmetry (pointwise_mul (const c) f s) (c * f s) in
    sum_over_perms_congruence n cf (pointwise_mul (const c) f) h';
    transitivity (sum_over_perms n cf)
                 (sum_over_perms n (pointwise_mul (const c) f))
                 (c * sum_over_perms n f)

(* -------------------------------------------------------------------- *)
(*  Base case: n = 0 reduces to f applied to the identity.              *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 30"
let sum_over_perms_zero
  (#t: Type) {| m: add_comm_group t |}
  (f: permutation 0 -> t)
  : Lemma (sum_over_perms 0 f = f (identity 0) + zero)
  = elim_equatable_laws t ();
    all_permutations_zero ();
    sum_list_cons (f (identity 0)) [];
    sum_list_nil #t #m
#pop-options

let respects_perm_eq_intro
  (#t: Type) {| equatable t |}
  (#n: nat) (f: permutation n -> t)
  (h: (p: permutation n) -> (q: permutation n) ->
      Lemma (requires perm_eq p q) (ensures f p = f q))
  : Lemma (ensures respects_perm_eq f)
  = reveal_opaque (`%respects_perm_eq) (respects_perm_eq #t #_ #n f);
    let prf (p q: permutation n) : Lemma (perm_eq p q ==> f p = f q)
      = Classical.move_requires (h p) q
    in
    Classical.forall_intro_2 prf

let respects_perm_eq_elim
  (#t: Type) {| equatable t |}
  (#n: nat) (f: permutation n -> t) (p q: permutation n)
  : Lemma (requires respects_perm_eq f /\ perm_eq p q)
          (ensures f p = f q)
  = reveal_opaque (`%respects_perm_eq) (respects_perm_eq #t #_ #n f)

(* -------------------------------------------------------------------- *)
(*  List-permutation relation via per-equivalence-class counts.         *)
(*                                                                      *)
(*  Two lists are list_perm-equivalent if every permutation has the     *)
(*  same number of perm_eq-matches in each list.                        *)
(* -------------------------------------------------------------------- *)

let rec perm_eq_count (#n: nat) (p: permutation n) (xs: list (permutation n)) : nat
  = match xs with
    | [] -> 0
    | h :: tl ->
        (if perm_eq p h then 1 else 0) ++ perm_eq_count p tl

let perm_eq_count_nil (#n: nat) (p: permutation n)
  : Lemma (perm_eq_count p [] == 0)
  = ()

let perm_eq_count_cons (#n: nat) (p h: permutation n) (tl: list (permutation n))
  : Lemma (perm_eq_count p (h :: tl) ==
           bool_to_nat (perm_eq p h) ++ perm_eq_count p tl)
  = ()

let list_perm (#n: nat) (xs ys: list (permutation n)) : prop
  = forall (p: permutation n). perm_eq_count p xs == perm_eq_count p ys

(* -------------------------------------------------------------------- *)
(*  Basic facts about perm_eq_count.                                    *)
(* -------------------------------------------------------------------- *)

let rec perm_eq_count_append (#n: nat) (p: permutation n) (xs ys: list (permutation n))
  : Lemma (ensures perm_eq_count p (L.append xs ys) ==
                   perm_eq_count p xs ++ perm_eq_count p ys)
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: tl -> perm_eq_count_append p tl ys

let perm_eq_count_map_cons (#n #m: nat) (f: permutation m -> permutation n)
  (p: permutation n) (h: permutation m) (tl: list (permutation m))
  : Lemma (perm_eq_count p (L.map f (h :: tl)) ==
           bool_to_nat (perm_eq p (f h)) ++ perm_eq_count p (L.map f tl))
  = ()

let perm_eq_count_map_nil (#n #m: nat) (f: permutation m -> permutation n)
  (p: permutation n)
  : Lemma (perm_eq_count p (L.map f []) == 0)
  = ()

(* -------------------------------------------------------------------- *)
(*  list_perm is an equivalence.                                        *)
(* -------------------------------------------------------------------- *)

let list_perm_refl (#n: nat) (xs: list (permutation n))
  : Lemma (list_perm xs xs)
  = ()

let list_perm_sym (#n: nat) (xs ys: list (permutation n))
  : Lemma (requires list_perm xs ys) (ensures list_perm ys xs)
  = ()

let list_perm_trans (#n: nat) (xs ys zs: list (permutation n))
  : Lemma (requires list_perm xs ys /\ list_perm ys zs)
          (ensures list_perm xs zs)
  = ()

(* -------------------------------------------------------------------- *)
(*  Congruence: prepending the same element preserves list_perm.        *)
(* -------------------------------------------------------------------- *)

let list_perm_cons (#n: nat) (x: permutation n) (xs ys: list (permutation n))
  : Lemma (requires list_perm xs ys)
          (ensures list_perm (x :: xs) (x :: ys))
  = ()

(* -------------------------------------------------------------------- *)
(*  Swap of adjacent elements.                                          *)
(* -------------------------------------------------------------------- *)

let list_perm_swap_head (#n: nat) (x y: permutation n) (xs: list (permutation n))
  : Lemma (list_perm (x :: y :: xs) (y :: x :: xs))
  = ()

(* -------------------------------------------------------------------- *)
(*  sum_list distributes over append.                                   *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec sum_list_append
  (#t: Type) {| m: add_comm_group t |}
  (xs ys: list t)
  : Lemma (ensures sum_list (L.append xs ys) = sum_list xs + sum_list ys)
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] ->
        sum_list_nil #t #m;
        zero_plus_x (sum_list ys)
    | h :: tl ->
        sum_list_append tl ys;
        sum_list_cons h tl;
        sum_list_cons h (L.append tl ys);
        add_congruence h (sum_list (L.append tl ys))
                       h (sum_list tl + sum_list ys);
        add_associativity h (sum_list tl) (sum_list ys);
        symmetry ((h + sum_list tl) + sum_list ys)
                 (h + (sum_list tl + sum_list ys));
        transitivity (h + sum_list (L.append tl ys))
                     (h + (sum_list tl + sum_list ys))
                     ((h + sum_list tl) + sum_list ys)
#pop-options
(* -------------------------------------------------------------------- *)
(*  Finding a perm_eq-match in a list with positive count.              *)
(* -------------------------------------------------------------------- *)

(* split_at_match p xs returns (pre, m, post) such that
   xs == pre ++ m :: post, perm_eq p m, and no element of pre
   is perm_eq-equal to p. *)
let rec split_at_match (#n: nat) (p: permutation n) (xs: list (permutation n))
  : Pure (list (permutation n) & permutation n & list (permutation n))
         (requires perm_eq_count p xs > 0)
         (ensures fun (pre, m, post) ->
             xs == L.append pre (m :: post) /\
             perm_eq p m /\
             perm_eq_count p pre == 0 /\
             perm_eq_count p xs ==
               1 ++ perm_eq_count p (L.append pre post))
         (decreases xs)
  = match xs with
    | h :: tl ->
        if perm_eq p h
        then ([], h, tl)
        else
          let (pre', m, post) = split_at_match p tl in
          perm_eq_count_append p pre' post;
          (h :: pre', m, post)
(* -------------------------------------------------------------------- *)
(*  Pulling an element out of a sum_list of a (pre ++ m :: post) list.  *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let sum_list_extract
  (#t: Type) {| m: add_comm_group t |}
  (a: t) (pre post: list t)
  : Lemma (sum_list (L.append pre (a :: post)) =
           a + sum_list (L.append pre post))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let sp = sum_list pre in
    let sq = sum_list post in
    sum_list_cons a post;
    (* sum_list (a :: post) == a + sq  [Prims ==, allows substitution] *)
    sum_list_append pre (a :: post);
    (* sum_list (pre ++ a :: post) = sp + sum_list (a :: post)
       by substitution: = sp + (a + sq) *)
    add_congruence sp (sum_list (a :: post)) sp (a + sq);
    (* sp + sum_list (a :: post) = sp + (a + sq) *)
    transitivity (sum_list (L.append pre (a :: post)))
                 (sp + sum_list (a :: post))
                 (sp + (a + sq));
    sum_list_append pre post;
    (* sum_list (pre ++ post) = sp + sq *)
    add_associativity sp a sq;
    (* (sp + a) + sq = sp + (a + sq) *)
    (* sp + (a + sq) = (sp + a) + sq *)
    add_commutativity sp a;
    add_congruence (sp + a) sq (a + sp) sq;
    (* (sp + a) + sq = (a + sp) + sq *)
    add_associativity a sp sq;
    (* (a + sp) + sq = a + (sp + sq) *)
    add_congruence a (sp + sq) a (sum_list (L.append pre post));
    (* a + (sp + sq) = a + sum_list (pre ++ post) *)
    transitivity (sum_list (L.append pre (a :: post))) (sp + (a + sq))
                 (a + sum_list (L.append pre post))
#pop-options
(* -------------------------------------------------------------------- *)
(*  perm_eq transports through perm_eq.                                 *)
(* -------------------------------------------------------------------- *)

let perm_eq_left_cong (#n: nat) (p h m: permutation n)
  : Lemma (requires perm_eq h m)
          (ensures perm_eq p h == perm_eq p m)
  = reveal_opaque (`%perm_eq) (perm_eq p h);
    reveal_opaque (`%perm_eq) (perm_eq p m);
    reveal_opaque (`%perm_eq) (perm_eq h m);
    if perm_eq p h then
      perm_eq_bool_from_trans p h m 0
    else if perm_eq p m then begin
      perm_eq_bool_from_sym h m 0;
      perm_eq_bool_from_trans p m h 0
    end else ()

(* -------------------------------------------------------------------- *)
(*  Empty list has zero count for everything; converse.                 *)
(* -------------------------------------------------------------------- *)

let list_perm_empty_implies_empty (#n: nat) (ys: list (permutation n))
  : Lemma (requires list_perm [] ys) (ensures ys == [])
  = match ys with
    | [] -> ()
    | h :: _ ->
        perm_eq_bool_refl h;
        assert (perm_eq_count h ys >= 1);
        assert (perm_eq_count h [] == 0)
(* -------------------------------------------------------------------- *)
(*  Cancelling a matched head: if list_perm (h :: tl) (pre ++ m :: post)*)
(*  and perm_eq h m, then list_perm tl (pre ++ post).                   *)
(* -------------------------------------------------------------------- *)

let list_perm_cancel_match
  (#n: nat)
  (h m: permutation n) (tl pre post: list (permutation n))
  : Lemma (requires list_perm (h :: tl) (L.append pre (m :: post)) /\
                    perm_eq h m)
          (ensures  list_perm tl (L.append pre post))
  = let aux (p: permutation n) : Lemma
        (perm_eq_count p tl == perm_eq_count p (L.append pre post))
      = perm_eq_count_append p pre (m :: post);
        perm_eq_count_append p pre post;
        perm_eq_left_cong p h m
    in Classical.forall_intro aux
(* -------------------------------------------------------------------- *)
(*  Main invariance theorem.                                            *)
(*                                                                      *)
(*  If two lists of permutations are list_perm-equivalent, and a        *)
(*  function f respects perm_eq, then sum_list (map f xs) =             *)
(*  sum_list (map f ys).                                                *)
(* -------------------------------------------------------------------- *)


#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec sum_list_perm_invariance
  (#t: Type) {| m: add_comm_group t |}
  (#n: nat) (f: permutation n -> t) (xs ys: list (permutation n))
  : Lemma (requires list_perm xs ys /\ respects_perm_eq #t f)
          (ensures  sum_list (L.map f xs) = sum_list (L.map f ys))
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] ->
        list_perm_empty_implies_empty ys
    | h :: tl ->
        perm_eq_bool_refl h;
        assert (perm_eq_count h (h :: tl) >= 1);
        assert (perm_eq_count h ys >= 1);
        let (pre, mm, post) = split_at_match h ys in
        (* ys == pre ++ mm :: post, perm_eq h mm *)
        list_perm_cancel_match h mm tl pre post;
        (* list_perm tl (pre ++ post) *)
        sum_list_perm_invariance f tl (L.append pre post);
        (* sum_list (map f tl) = sum_list (map f (pre ++ post)) *)
        L.map_append f pre (mm :: post);
        (* L.map f ys = L.map f pre ++ (f mm :: L.map f post) *)
        L.map_append f pre post;
        (* L.map f (pre ++ post) = L.map f pre ++ L.map f post *)
        sum_list_extract (f mm) (L.map f pre) (L.map f post);
        (* sum_list (L.map f pre ++ f mm :: L.map f post) =
              f mm + sum_list (L.map f pre ++ L.map f post) *)
        respects_perm_eq_elim f h mm;
        (* perm_eq h mm; thus f h = f mm by respects_perm_eq *)
        assert (f h = f mm);
        sum_list_cons (f h) (L.map f tl);
        (* sum_list (L.map f (h :: tl)) == f h + sum_list (L.map f tl) *)
        add_congruence (f h) (sum_list (L.map f tl))
                       (f mm) (sum_list (L.map f (L.append pre post)));
        (* f h + sum_list (map f tl) = f mm + sum_list (map f (pre ++ post)) *)
        symmetry (sum_list (L.map f (L.append pre (mm :: post))))
                 (f mm + sum_list (L.map f (L.append pre post)));
        transitivity (f h + sum_list (L.map f tl))
                     (f mm + sum_list (L.map f (L.append pre post)))
                     (sum_list (L.map f (L.append pre (mm :: post))))
#pop-options
(* ==================================================================== *)
(*  Counting facts about all_permutations.                              *)
(* ==================================================================== *)

(* If p is not perm_eq to any element of xs, count is zero. *)
let rec count_zero_when_no_match
  (#n: nat) (p: permutation n) (xs: list (permutation n))
  : Lemma (requires forall (q: permutation n). L.memP q xs ==> ~(perm_eq p q))
          (ensures  perm_eq_count p xs == 0)
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: tl ->
        assert (L.memP h xs);
        assert (~(perm_eq p h));
        assert (forall (q: permutation n). L.memP q tl ==> L.memP q xs);
        count_zero_when_no_match p tl

(* If p is in the list (mod perm_eq) and the list is all_distinct, count is 1. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let rec count_one_when_in_distinct
  (#n: nat) (p: permutation n) (xs: list (permutation n))
  : Lemma (requires permutation_in_list p xs /\ all_distinct xs)
          (ensures  perm_eq_count p xs == 1)
          (decreases xs)
  = match xs with
    | [] -> assert False
    | h :: tl ->
        if perm_eq p h then begin
          (* perm_eq p h holds.  Show count p tl = 0 via all_distinct. *)
          assert (perm_eq p h);
          let no_match_in_tl (q: permutation n)
            : Lemma (requires L.memP q tl /\ perm_eq p q) (ensures False)
            = assert (~(perm_eq h q));
              assert (perm_eq p h);
              assert (perm_eq p q);
              perm_eq_sym p h;
              perm_eq_trans h p q;
              assert (perm_eq h q)
          in
          let no_match (q: permutation n) : Lemma (L.memP q tl ==> ~(perm_eq p q))
            = Classical.move_requires (Classical.move_requires no_match_in_tl) q
          in
          Classical.forall_intro no_match;
          count_zero_when_no_match p tl
        end else begin
          (* p is not perm_eq h. *)
          let not_h (a: permutation n) : Lemma (requires perm_eq p a /\ a == h) (ensures False)
            = assert (perm_eq p a);
              assert (a == h);
              assert (perm_eq p h);
              assert False
          in
          assert (exists (q: permutation n). L.memP q xs /\ perm_eq p q);
          let q = FStar.IndefiniteDescription.indefinite_description_ghost
                    (permutation n) (fun q -> L.memP q xs /\ perm_eq p q) in
          assert (L.memP q xs /\ perm_eq p q);
          assert (q == h \/ L.memP q tl);
          Classical.move_requires not_h q;
          assert (L.memP q tl);
          assert (permutation_in_list p tl);
          count_one_when_in_distinct p tl
        end
#pop-options

(* Headline: every permutation occurs in all_permutations n with count 1. *)
let all_permutations_count_one (n: nat) (p: permutation n)
  : Lemma (perm_eq_count p (all_permutations n) == 1)
  = all_permutations_complete n p;
    all_permutations_no_dup n;
    count_one_when_in_distinct p (all_permutations n)

(* If ys has count 1 for every permutation and f respects perm_eq,
   then sum_over_perms n f = sum_list (map f ys). *)
let sum_over_perms_via_count_one_list
  (#t: Type) {| m: add_comm_group t |}
  (#n: nat) (f: permutation n -> t) (ys: list (permutation n))
  (h_count: (p: permutation n) -> Lemma (perm_eq_count p ys == 1))
  : Lemma (requires respects_perm_eq #t f)
          (ensures sum_over_perms n f = sum_list (L.map f ys))
  = let xs = all_permutations n in
    let aux (p: permutation n) : Lemma (perm_eq_count p xs == perm_eq_count p ys)
      = all_permutations_count_one n p;
        h_count p
    in Classical.forall_intro aux;
    sum_list_perm_invariance f xs ys

(* ==================================================================== *)
(*  Right-multiplication by a fixed permutation: counting facts.        *)
(* ==================================================================== *)

(* compose_congruence in perm_eq form. *)
let compose_cong_perm_eq (#n: nat) (p1 q1 p2 q2: permutation n)
  : Lemma (requires perm_eq p1 p2 /\ perm_eq q1 q2)
          (ensures  perm_eq (compose p1 q1) (compose p2 q2))
  = compose_congruence p1 q1 p2 q2

(* Key: p ~ h*q  iff  p*q^{-1} ~ h, where ~ is perm_eq. *)
private let perm_eq_rmul_iff_prop (#n: nat) (p h q: permutation n)
  : Lemma (perm_eq p (compose h q) <==> perm_eq (compose p (inverse q)) h)
  = let q' = inverse q in
    let aux1 () : Lemma (requires perm_eq p (compose h q))
                        (ensures  perm_eq (compose p q') h)
      = perm_eq_refl q';
        compose_cong_perm_eq p q' (compose h q) q';
        (* perm_eq (compose p q') (compose (compose h q) q') *)
        compose_associative h q q';
        (* perm_eq (compose (compose h q) q') (compose h (compose q q')) *)
        perm_eq_trans (compose p q') (compose (compose h q) q') (compose h (compose q q'));
        inverse_right q;
        (* perm_eq (compose q q') (identity n) *)
        perm_eq_refl h;
        compose_cong_perm_eq h (compose q q') h (identity n);
        (* perm_eq (compose h (compose q q')) (compose h (identity n)) *)
        perm_eq_trans (compose p q') (compose h (compose q q')) (compose h (identity n));
        identity_right h;
        (* perm_eq (compose h (identity n)) h *)
        perm_eq_trans (compose p q') (compose h (identity n)) h
    in
    let aux2 () : Lemma (requires perm_eq (compose p q') h)
                        (ensures  perm_eq p (compose h q))
      = perm_eq_refl q;
        compose_cong_perm_eq (compose p q') q h q;
        (* perm_eq (compose (compose p q') q) (compose h q) *)
        compose_associative p q' q;
        perm_eq_sym (compose (compose p q') q) (compose p (compose q' q));
        inverse_left q;
        (* perm_eq (compose q' q) (identity n) *)
        perm_eq_refl p;
        compose_cong_perm_eq p (compose q' q) p (identity n);
        perm_eq_sym (compose p (compose q' q)) (compose p (identity n));
        identity_right p;
        perm_eq_sym (compose p (identity n)) p;
        perm_eq_trans p (compose p (identity n)) (compose p (compose q' q));
        perm_eq_trans p (compose p (compose q' q)) (compose (compose p q') q);
        perm_eq_trans p (compose (compose p q') q) (compose h q)
    in
    Classical.move_requires aux1 ();
    Classical.move_requires aux2 ()

(* Equality form of the same equivalence. *)
let perm_eq_rmul_iff (#n: nat) (p h q: permutation n)
  : Lemma (perm_eq p (compose h q) == perm_eq (compose p (inverse q)) h)
  = perm_eq_rmul_iff_prop p h q;
    (if perm_eq p (compose h q) then begin
        let forward () : Lemma (requires perm_eq p (compose h q))
                                 (ensures  perm_eq (compose p (inverse q)) h)
          = perm_eq_rmul_iff_prop p h q
        in
        forward ()
     end);
    (if perm_eq (compose p (inverse q)) h then begin
        let backward () : Lemma (requires perm_eq (compose p (inverse q)) h)
                                  (ensures  perm_eq p (compose h q))
          = perm_eq_rmul_iff_prop p h q
        in
        backward ()
     end)

(* Counting under right-multiplication: pulling the multiplier outside. *)
let rec perm_eq_count_map_rmul
  (#n: nat) (p q: permutation n) (xs: list (permutation n))
  : Lemma (ensures perm_eq_count p (L.map (flip compose q) xs) ==
                   perm_eq_count (compose p (inverse q)) xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: tl ->
        flip_unfold compose q h;
        perm_eq_rmul_iff p h q;
        perm_eq_count_map_rmul p q tl

(* Every permutation has count 1 in the rmul-mapped list as well. *)
let mapped_rmul_count_one (n: nat) (q: permutation n) (p: permutation n)
  : Lemma (perm_eq_count p (L.map (flip compose q) (all_permutations n)) == 1)
  = perm_eq_count_map_rmul p q (all_permutations n);
    all_permutations_count_one n (compose p (inverse q))

(* Headline: rmul by q gives a list_perm-equivalent list. *)
let rmul_q_yields_list_perm (n: nat) (q: permutation n)
  : Lemma (list_perm (all_permutations n)
                     (L.map (flip compose q) (all_permutations n)))
  = let aux (p: permutation n) : Lemma
        (perm_eq_count p (all_permutations n) ==
         perm_eq_count p (L.map (flip compose q) (all_permutations n)))
      = all_permutations_count_one n p;
        mapped_rmul_count_one n q p
    in Classical.forall_intro aux

(* ==================================================================== *)
(*  Final reindexing theorem.                                           *)
(* ==================================================================== *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let rec map_map_eq (#a #b #c: Type) (g: a -> b) (f: b -> c) (xs: list a)
  : Lemma (ensures L.map f (L.map g xs) == L.map (fcomp f g) xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: tl -> map_map_eq g f tl
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 30"
let sum_over_perms_reindex
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t) (q: permutation n)
  : Lemma (requires respects_perm_eq #t f)
          (ensures  sum_over_perms n f =
                    sum_over_perms n (fcomp f (flip compose q)))
  = rmul_q_yields_list_perm n q;
    sum_list_perm_invariance f
      (all_permutations n)
      (L.map (flip compose q) (all_permutations n));
    map_map_eq (flip compose q) f (all_permutations n)
#pop-options

(* ==================================================================== *)
(*  Reindexing by inverse: sum f(s) = sum f(s^{-1}).                    *)
(* ==================================================================== *)

(* Key bijection equivalence: p ~ h^{-1}  iff  p^{-1} ~ h. *)
private let perm_eq_inverse_iff_prop (#n: nat) (p h: permutation n)
  : Lemma (perm_eq p (inverse h) <==> perm_eq (inverse p) h)
  = let aux1 () : Lemma (requires perm_eq p (inverse h))
                        (ensures  perm_eq (inverse p) h)
      = inverse_congruence p (inverse h);
        (* perm_eq (inverse p) (inverse (inverse h)) *)
        inverse_involutive h;
        (* perm_eq (inverse (inverse h)) h *)
        perm_eq_trans (inverse p) (inverse (inverse h)) h
    in
    let aux2 () : Lemma (requires perm_eq (inverse p) h)
                        (ensures  perm_eq p (inverse h))
      = inverse_congruence (inverse p) h;
        (* perm_eq (inverse (inverse p)) (inverse h) *)
        inverse_involutive p;
        (* perm_eq (inverse (inverse p)) p *)
        perm_eq_sym (inverse (inverse p)) p;
        perm_eq_trans p (inverse (inverse p)) (inverse h)
    in
    Classical.move_requires aux1 ();
    Classical.move_requires aux2 ()

(* Equality form of the same equivalence. *)
let perm_eq_inverse_iff (#n: nat) (p h: permutation n)
  : Lemma (perm_eq p (inverse h) == perm_eq (inverse p) h)
  = perm_eq_inverse_iff_prop p h;
    (if perm_eq p (inverse h) then begin
        let forward () : Lemma (requires perm_eq p (inverse h))
                                 (ensures  perm_eq (inverse p) h)
          = perm_eq_inverse_iff_prop p h
        in
        forward ()
     end);
    (if perm_eq (inverse p) h then begin
        let backward () : Lemma (requires perm_eq (inverse p) h)
                                  (ensures  perm_eq p (inverse h))
          = perm_eq_inverse_iff_prop p h
        in
        backward ()
     end)

(* Counting under map-inverse: pulls inverse outside the count. *)
let rec perm_eq_count_map_inverse
  (#n: nat) (p: permutation n) (xs: list (permutation n))
  : Lemma (ensures perm_eq_count p (L.map inverse xs) ==
                   perm_eq_count (inverse p) xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: tl ->
        perm_eq_inverse_iff p h;
        perm_eq_count_map_inverse p tl

(* Every permutation has count 1 in the inverse-mapped list. *)
let mapped_inverse_count_one (n: nat) (p: permutation n)
  : Lemma (perm_eq_count p (L.map inverse (all_permutations n)) == 1)
  = perm_eq_count_map_inverse p (all_permutations n);
    all_permutations_count_one n (inverse p)

(* Headline: mapping by inverse yields a list_perm-equivalent list. *)
let inverse_yields_list_perm (n: nat)
  : Lemma (list_perm (all_permutations n)
                     (L.map inverse (all_permutations n)))
  = let aux (p: permutation n) : Lemma
        (perm_eq_count p (all_permutations n) ==
         perm_eq_count p (L.map inverse (all_permutations n)))
      = all_permutations_count_one n p;
        mapped_inverse_count_one n p
    in Classical.forall_intro aux

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let sum_over_perms_reindex_inverse
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t)
  : Lemma (requires respects_perm_eq #t f)
          (ensures  sum_over_perms n f =
                    sum_over_perms n (fcomp f inverse))
  = inverse_yields_list_perm n;
    sum_list_perm_invariance f
      (all_permutations n)
      (L.map inverse (all_permutations n));
    map_map_eq inverse f (all_permutations n)
#pop-options
(* -------------------------------------------------------------------- *)
(*  Single-nonzero-summand lemma.                                       *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
private let rec sum_list_const_zero
  (#t: Type) {| m: add_comm_group t |} (n: nat)
  (f: permutation n -> t) (xs: list (permutation n))
  : Lemma (requires forall (q: permutation n). L.memP q xs ==> f q = zero)
          (ensures sum_list (L.map f xs) = zero)
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] -> sum_list_nil #t #m
    | h :: tl ->
        assert (L.memP h (h :: tl));
        assert (f h = zero);
        let tl_aux (q: permutation n) : Lemma (L.memP q tl ==> f q = zero)
          = eliminate L.memP q tl \/ ~(L.memP q tl)
            returns L.memP q tl ==> f q = zero
            with _. () and _. ()
        in
        Classical.forall_intro tl_aux;
        sum_list_cons (f h) (L.map f tl);
        sum_list_const_zero n f tl;
        add_congruence (f h) (sum_list (L.map f tl)) (zero #t) (zero #t);
        zero_plus_x (zero #t);
        assert (sum_list (L.map f (h :: tl)) = f h + sum_list (L.map f tl));
        transitivity (sum_list (L.map f (h :: tl))) (f h + sum_list (L.map f tl)) (zero #t)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let rec sum_list_pick
  (#n: nat) (#t: Type) {| m: add_comm_group t |}
  (xs: list (permutation n)) (f: permutation n -> t) (q: permutation n)
  : Lemma (requires all_distinct xs /\ L.memP q xs /\
                    (forall (q': permutation n).
                       L.memP q' xs /\ ~(perm_eq q q') ==> f q' = zero))
          (ensures sum_list (L.map f xs) = f q)
          (decreases xs)
  = elim_equatable_laws t ();
   trans_for_calc t ();
   match xs with
   | [] -> ()
   | h :: tl ->
       sum_list_cons (f h) (L.map f tl);
       eliminate (h == q) \/ ~(h == q)
       returns sum_list (L.map f (h :: tl)) = f q
       with _h_eq_q.
          begin
            let aux (p: permutation n) : Lemma (L.memP p tl ==> f p = zero)
              = eliminate L.memP p tl \/ ~(L.memP p tl)
                returns L.memP p tl ==> f p = zero
                with _. ()
                and _. ()
            in
            Classical.forall_intro aux;
            sum_list_const_zero n f tl;
            add_congruence (f h) (sum_list (L.map f tl)) (f q) (zero #t);
            x_plus_zero (f q);
            assert (sum_list (L.map f (h :: tl)) = f h + sum_list (L.map f tl));
            transitivity (sum_list (L.map f (h :: tl))) (f h + sum_list (L.map f tl)) (f q)
          end
        and _h_neq_q.
          begin
            assert (L.memP q tl);
            assert (~(perm_eq h q));
            let neq_qh () : Lemma (requires perm_eq q h) (ensures False)
              = perm_eq_sym q h;
                assert False
            in
            Classical.move_requires neq_qh ();
            assert (~(perm_eq q h));
            sum_list_pick tl f q;
            add_congruence (f h) (sum_list (L.map f tl)) (zero #t) (f q);
            zero_plus_x (f q);
            assert (sum_list (L.map f (h :: tl)) = f h + sum_list (L.map f tl));
            transitivity (sum_list (L.map f (h :: tl))) (f h + sum_list (L.map f tl)) (f q)
          end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let sum_over_perms_single
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t) (p0: permutation n)
  (h_zero: (q: permutation n) ->
           Lemma (requires ~(perm_eq p0 q)) (ensures f q = zero))
  : Lemma (requires respects_perm_eq #t f)
          (ensures sum_over_perms n f = f p0)
  = elim_equatable_laws t ();
    all_permutations_no_dup n;
    all_permutations_complete n p0;
    let xs = all_permutations n in
    eliminate exists (q: permutation n). L.memP q xs /\ perm_eq p0 q
      returns sum_over_perms n f = f p0 with _.
      begin
        let only_q (q': permutation n)
          : Lemma (requires L.memP q' xs /\ ~(perm_eq q q'))
                  (ensures f q' = zero)
          = let not_p0_q' () : Lemma (requires perm_eq p0 q') (ensures False)
              = perm_eq_sym p0 q;
                perm_eq_trans q p0 q';
                assert False
            in
            Classical.move_requires not_p0_q' ();
            assert (~(perm_eq p0 q'));
            h_zero q'
        in
        Classical.forall_intro (Classical.move_requires only_q);
        sum_list_pick xs f q;
        perm_eq_sym p0 q;
        respects_perm_eq_elim f q p0;

        transitivity (sum_over_perms n f) (sum_list (L.map f xs)) (f q);
        transitivity (sum_over_perms n f) (f q) (f p0)
      end
#pop-options

let sum_over_perms_all_zero
  (#t: Type) {| m: add_comm_group t |}
  (n: nat) (f: permutation n -> t)
  (h: (p: permutation n) -> Lemma (f p = zero))
  : Lemma (ensures  sum_over_perms n f = zero)
  = Classical.forall_intro h;
    sum_list_const_zero n f (all_permutations n)

(* ==================================================================== *)
(*  τ-orbit pair-cancellation lemma.                                    *)
(*                                                                      *)
(*  If τ is a fixed-point-free involution (i.e. τ ≠ id and τ ∘ τ = id), *)
(*  and f satisfies f σ + f (σ∘τ) = 0 for every σ, and f respects       *)
(*  perm_eq, then sum_over_perms n f = 0.                                *)
(*                                                                      *)
(*  We pair-partition the enumeration: each orbit {σ, σ∘τ} contributes  *)
(*  zero.  This avoids the 2·S = 0 doubling argument and therefore works *)
(*  in any commutative additive group.                                  *)
(* ==================================================================== *)

(* If h ≡ h∘τ then τ ≡ id, by injectivity of h.fwd. *)
private let not_self_tau_partner (#n: nat) (h tau: permutation n)
  : Lemma (requires ~(perm_eq tau (identity n)))
          (ensures  ~(perm_eq h (compose h tau)))
  = let derive_id ()
      : Lemma (requires perm_eq h (compose h tau))
              (ensures  perm_eq tau (identity n))
      = let aux (i: fin n) : Lemma (tau.fwd i == (identity n).fwd i)
          = perm_eq_elim h (compose h tau) i;
            compose_fwd h tau i;
            assert (h.fwd i == h.fwd (tau.fwd i));
            fwd_injective h i (tau.fwd i);
            identity_fwd n i
        in
        Classical.forall_intro aux;
        perm_eq_intro tau (identity n) aux
    in
    Classical.move_requires derive_id ()

(* Right-cancellation of perm_eq by composition. *)
private let perm_eq_right_cancel (#n: nat) (a b q: permutation n)
  : Lemma (requires perm_eq (compose a q) (compose b q))
          (ensures  perm_eq a b)
  = let aux (i: fin n) : Lemma (a.fwd i == b.fwd i)
      = let j = q.bwd i in
        perm_eq_elim (compose a q) (compose b q) j;
        compose_fwd a q j;
        compose_fwd b q j;
        q.fwd_bwd_id i
    in
    Classical.forall_intro aux;
    perm_eq_intro a b aux

(* From positive count, find a memP-witness. *)
private let rec memP_from_perm_eq_count
  (#n: nat) (p: permutation n) (xs: list (permutation n))
  : Ghost (permutation n)
          (requires perm_eq_count p xs > 0)
          (ensures fun q -> L.memP q xs /\ perm_eq p q)
          (decreases xs)
  = match xs with
    | h :: tl ->
        if perm_eq p h then h
        else memP_from_perm_eq_count p tl

(* From a memP-witness with perm_eq match, conclude positive count. *)
private let rec count_positive_from_match
  (#n: nat) (p q: permutation n) (xs: list (permutation n))
  : Lemma (requires L.memP q xs /\ perm_eq p q)
          (ensures  perm_eq_count p xs > 0)
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: tl ->
        if FStar.IndefiniteDescription.strong_excluded_middle (q == h) then ()
        else count_positive_from_match p q tl

(* permutation_in_list → positive count. *)
private let in_list_to_count_pos
  (#n: nat) (m: permutation n) (xs: list (permutation n))
  : Lemma (requires permutation_in_list m xs)
          (ensures  perm_eq_count m xs > 0)
  = let q = FStar.IndefiniteDescription.indefinite_description_ghost
              (permutation n) (fun q -> L.memP q xs /\ perm_eq m q) in
    count_positive_from_match m q xs

(* permutation_in_list with explicit witness. *)
private let in_list_witness
  (#n: nat) (m: permutation n) (xs: list (permutation n))
  : Ghost (permutation n)
          (requires permutation_in_list m xs)
          (ensures fun q -> L.memP q xs /\ perm_eq m q)
  = FStar.IndefiniteDescription.indefinite_description_ghost
      (permutation n) (fun q -> L.memP q xs /\ perm_eq m q)

(* Drop an element from a permutation_in_list when it's not perm_eq to the head. *)
private let in_list_cons_drop_head
  (#n: nat) (h m: permutation n) (tl: list (permutation n))
  : Lemma (requires permutation_in_list m (h :: tl) /\ ~(perm_eq m h))
          (ensures  permutation_in_list m tl)
  = let q = in_list_witness m (h :: tl) in
    (* L.memP q (h :: tl) means q == h \/ L.memP q tl. *)
    if FStar.IndefiniteDescription.strong_excluded_middle (q == h)
    then begin
      (* q == h, but perm_eq m q ⇒ perm_eq m h, contradicting hypothesis. *)
      assert (perm_eq m h);
      assert False
    end else begin
      assert (L.memP q tl)
    end

(* Append-memP: m ∈ pre ++ post iff m ∈ pre or m ∈ post. *)
private let memP_append_perm
  (#n: nat) (m: permutation n) (pre post: list (permutation n))
  : Lemma (L.memP m (L.append pre post) <==> (L.memP m pre \/ L.memP m post))
  = L.append_memP pre post m

(* permutation_in_list on append. *)
private let in_list_append
  (#n: nat) (m: permutation n) (pre post: list (permutation n))
  : Lemma ((permutation_in_list m (L.append pre post)) <==>
           (permutation_in_list m pre \/ permutation_in_list m post))
  = let l = L.append pre post in
    let split_dir () : Lemma (requires permutation_in_list m l)
                             (ensures  permutation_in_list m pre \/
                                       permutation_in_list m post)
      = let q = in_list_witness m l in
        L.append_memP pre post q
    in
    Classical.move_requires split_dir ();
    let merge_left () : Lemma (requires permutation_in_list m pre)
                              (ensures  permutation_in_list m l)
      = let q = in_list_witness m pre in
        L.append_memP pre post q
    in
    Classical.move_requires merge_left ();
    let merge_right () : Lemma (requires permutation_in_list m post)
                               (ensures  permutation_in_list m l)
      = let q = in_list_witness m post in
        L.append_memP pre post q
    in
    Classical.move_requires merge_right ()

(* Removing a middle element preserves all_distinct. *)
private let rec all_distinct_drop_middle
  (#n: nat) (pre post: list (permutation n)) (m: permutation n)
  : Lemma (requires all_distinct (L.append pre (m :: post)))
          (ensures  all_distinct (L.append pre post))
          (decreases pre)
  = match pre with
    | [] -> ()
    | h :: tl ->
        (* all_distinct (h :: (tl ++ m :: post)) gives:
              forall p. L.memP p (tl ++ m :: post) ==> ~(perm_eq h p)
              /\ all_distinct (tl ++ m :: post). *)
        all_distinct_drop_middle tl post m;
        let aux (p: permutation n)
          : Lemma (requires L.memP p (L.append tl post))
                  (ensures  ~(perm_eq h p))
          = L.append_memP tl post p;
            L.append_memP tl (m :: post) p
        in
        Classical.forall_intro (Classical.move_requires aux)

(* If all_distinct (pre ++ m :: post), every element of pre++post is ≢ m. *)
private let rec memP_append_drop_not_perm_eq
  (#n: nat) (pre post: list (permutation n)) (m p: permutation n)
  : Lemma (requires all_distinct (L.append pre (m :: post)) /\
                    L.memP p (L.append pre post))
          (ensures  ~(perm_eq m p))
          (decreases pre)
  = match pre with
    | [] ->
        (* all_distinct (m :: post). Body says: forall p ∈ post. ~(perm_eq m p). *)
        (* L.memP p (L.append [] post) == L.memP p post. *)
        L.append_memP [] post p;
        assert (L.memP p post);
        assert (~(perm_eq m p))
    | h :: tl ->
        (* all_distinct (h :: (tl ++ m :: post)). *)
        L.append_memP tl post p;
        (* p == h or memP p (tl ++ post). *)
        if FStar.IndefiniteDescription.strong_excluded_middle (p == h) then begin
          (* h appears in tl ++ m :: post (as m, at least). all_distinct says
             ~(perm_eq h m). Need ~(perm_eq m h). *)
          L.append_memP tl (m :: post) m;
          (* m ∈ tl ++ m :: post. all_distinct gives ~(perm_eq h m). *)
          assert (L.memP m (L.append tl (m :: post)));
          assert (~(perm_eq h m));
          let neq_mh () : Lemma (requires perm_eq m h) (ensures False)
            = perm_eq_sym m h;
              assert False
          in
          Classical.move_requires neq_mh ();
          assert (~(perm_eq m h))
        end else begin
          assert (L.memP p (L.append tl post));
          memP_append_drop_not_perm_eq tl post m p
        end

(* permutation_in_list on (pre ++ post) excludes anything perm_eq m
   if all_distinct (pre ++ m :: post). *)
private let in_list_drop_not_perm_eq
  (#n: nat) (pre post: list (permutation n)) (m: permutation n)
  : Lemma (requires all_distinct (L.append pre (m :: post)))
          (ensures  forall (s: permutation n).
              permutation_in_list s (L.append pre post) ==> ~(perm_eq m s))
  = let aux (s: permutation n)
      : Lemma (requires permutation_in_list s (L.append pre post))
              (ensures  ~(perm_eq m s))
      = let q = in_list_witness s (L.append pre post) in
        memP_append_drop_not_perm_eq pre post m q;
        (* ~(perm_eq m q); transitively ~(perm_eq m s) via perm_eq s q. *)
        let neq_ms () : Lemma (requires perm_eq m s) (ensures False)
          = perm_eq_trans m s q;
            assert False
        in
        Classical.move_requires neq_ms ();
        assert (~(perm_eq m s))
    in
    Classical.forall_intro (Classical.move_requires aux)

(* If perm_eq (compose s tau) y, then perm_eq s (compose y tau) (using τ involutive). *)
private let partner_swap (#n: nat) (s y tau: permutation n)
  : Lemma (requires perm_eq (compose s tau) y /\
                    perm_eq (compose tau tau) (identity n))
          (ensures  perm_eq s (compose y tau))
  = (* Compose both sides on the right by tau. *)
    perm_eq_refl tau;
    compose_cong_perm_eq (compose s tau) tau y tau;
    (* perm_eq (compose (compose s tau) tau) (compose y tau). *)
    compose_associative s tau tau;
    perm_eq_sym (compose (compose s tau) tau) (compose s (compose tau tau));
    (* perm_eq (compose s (compose tau tau)) (compose (compose s tau) tau). *)
    perm_eq_refl s;
    compose_cong_perm_eq s (compose tau tau) s (identity n);
    (* perm_eq (compose s (compose tau tau)) (compose s (identity n)). *)
    perm_eq_sym (compose s (compose tau tau)) (compose s (identity n));
    identity_right s;
    perm_eq_sym (compose s (identity n)) s;
    perm_eq_trans s (compose s (identity n)) (compose s (compose tau tau));
    perm_eq_trans s (compose s (compose tau tau)) (compose (compose s tau) tau);
    perm_eq_trans s (compose (compose s tau) tau) (compose y tau)
    (* Chain gives perm_eq s (compose y tau). *)

(* Single-element τ-closure step for the partition list (pre ++ post).
   Given that xs = h :: (pre ++ m' :: post) is τ-closed and all_distinct,
   and m' is the τ-partner of h, then the τ-partner of any s in (pre ++ post)
   is also in (pre ++ post). Peeled out of sum_orbit_partition_zero so each VC
   stays small. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 5"
private let closure_pp_step
  (#n: nat)
  (h tau: permutation n)
  (pre post: list (permutation n))
  (m': permutation n)
  (s: permutation n)
  : Lemma (requires
              perm_eq (compose tau tau) (identity n) /\
              all_distinct (h :: L.append pre (m' :: post)) /\
              perm_eq (compose h tau) m' /\
              (forall (u: permutation n).
                  permutation_in_list u (h :: L.append pre (m' :: post)) ==>
                  permutation_in_list (compose u tau)
                                      (h :: L.append pre (m' :: post))) /\
              permutation_in_list s (L.append pre post))
          (ensures  permutation_in_list (compose s tau) (L.append pre post))
  = let tl = L.append pre (m' :: post) in
    let xs = h :: tl in
    let pp = L.append pre post in
    let m = compose h tau in
    assert (perm_eq m m');
    (* s ∈ pre ++ post ⊆ tl ⊆ xs, so partner ∈ xs. *)
    in_list_append s pre post;
    let bridge_to_tl () : Lemma (permutation_in_list s tl)
      = L.append_memP pre (m' :: post) (in_list_witness s pp);
        let q = in_list_witness s pp in
        L.append_memP pre post q
    in
    bridge_to_tl ();
    assert (permutation_in_list s tl);
    let to_xs () : Lemma (permutation_in_list s xs)
      = let q = in_list_witness s tl in
        assert (L.memP q xs)
    in
    to_xs ();
    assert (permutation_in_list (compose s tau) xs);
    let part = compose s tau in
    (* (a) ~(perm_eq part h). *)
    let part_neq_h () : Lemma (requires perm_eq part h) (ensures False)
      = partner_swap s h tau;
        assert (perm_eq s m);
        assert (perm_eq m m');
        perm_eq_trans s m m';
        assert (perm_eq s m');
        in_list_drop_not_perm_eq pre post m';
        assert (~(perm_eq m' s));
        perm_eq_sym s m';
        assert False
    in
    Classical.move_requires part_neq_h ();
    (* (b) ~(perm_eq part m'). *)
    let part_neq_mprime () : Lemma (requires perm_eq part m') (ensures False)
      = assert (perm_eq part m');
        perm_eq_sym m m';
        assert (perm_eq m' m);
        let pt = compose s tau in
        assert (perm_eq pt m');
        perm_eq_trans pt m' m;
        assert (perm_eq pt m);
        assert (perm_eq pt (compose h tau));
        perm_eq_right_cancel s h tau;
        assert (perm_eq s h);
        let qs = in_list_witness s pp in
        L.append_memP pre post qs;
        L.append_memP pre (m' :: post) qs;
        assert (L.memP qs tl);
        assert (~(perm_eq h qs));
        perm_eq_sym s h;
        perm_eq_trans h s qs;
        assert (perm_eq h qs)
    in
    Classical.move_requires part_neq_mprime ();
    assert (~(perm_eq part h));
    assert (~(perm_eq part m'));
    in_list_cons_drop_head h part tl;
    assert (permutation_in_list part tl);
    let qp = in_list_witness part tl in
    L.append_memP pre (m' :: post) qp;
    if FStar.IndefiniteDescription.strong_excluded_middle (L.memP qp pre) then begin
      L.append_memP pre post qp;
      assert (L.memP qp pp);
      assert (permutation_in_list part pp)
    end else begin
      assert (L.memP qp (m' :: post));
      if FStar.IndefiniteDescription.strong_excluded_middle (qp == m') then begin
        assert (perm_eq part m');
        assert False
      end else begin
        assert (L.memP qp post);
        L.append_memP pre post qp;
        assert (L.memP qp pp);
        assert (permutation_in_list part pp)
      end
    end
#pop-options

(* Main lemma: pair-cancel on a τ-closed all_distinct list. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 20 --split_queries always"
private let rec sum_orbit_partition_zero
  (#t: Type) {| g: add_comm_group t |}
  (#n: nat) (f: permutation n -> t) (tau: permutation n) (xs: list (permutation n))
  : Lemma (requires
              respects_perm_eq #t f /\
              ~ (perm_eq tau (identity n)) /\
              perm_eq (compose tau tau) (identity n) /\
              (forall (s: permutation n). f s + f (compose s tau) = zero) /\
              all_distinct xs /\
              (forall (s: permutation n).
                  permutation_in_list s xs ==>
                  permutation_in_list (compose s tau) xs))
          (ensures sum_list (L.map f xs) = zero)
          (decreases L.length xs)
  = match xs with
    | [] ->
        elim_equatable_laws t ();
        sum_list_nil #t #(g)
    | h :: tl ->
        elim_equatable_laws t ();
        trans_for_calc t ();
        let m = compose h tau in
        (* h is in xs. *)
        perm_eq_refl h;
        assert (permutation_in_list h xs);
        assert (permutation_in_list m xs);
        (* h is not perm_eq m. *)
        not_self_tau_partner h tau;
        assert (~(perm_eq h m));
        (* Hence m is in tl. *)
        let mh_sym () : Lemma (requires perm_eq m h) (ensures False)
          = perm_eq_sym m h;
            assert False
        in
        Classical.move_requires mh_sym ();
        assert (~(perm_eq m h));
        in_list_cons_drop_head h m tl;
        assert (permutation_in_list m tl);
        in_list_to_count_pos m tl;
        let (pre, m', post) = split_at_match m tl in
        (* tl == pre ++ m' :: post, perm_eq m m'. *)
        assert (perm_eq m m');
        (* From all_distinct xs derive: all_distinct tl, then all_distinct (pre ++ post). *)
        assert (all_distinct tl);
        all_distinct_drop_middle pre post m';
        assert (all_distinct (L.append pre post));
        (* Compute sums step by step. *)
        let pp = L.append pre post in
        let pmp = L.append pre (m' :: post) in
        assert (tl == pmp);
        (* map f and sum on tl. *)
        L.map_append f pre (m' :: post);
        L.map_append f pre post;
        sum_list_extract (f m') (L.map f pre) (L.map f post);
        (* sum_list (map f tl) = f m' + sum_list (map f (pre ++ post)). *)
        let smt = sum_list (L.map f tl) in
        let spp = sum_list (L.map f pp) in
        assert (smt = f m' + spp);
        (* sum_list (map f xs) = f h + sum_list (map f tl) = f h + (f m' + spp). *)
        sum_list_cons (f h) (L.map f tl);
        let sxs = sum_list (L.map f xs) in
        add_congruence (f h) smt (f h) (f m' + spp);
        assert (f h + smt = f h + (f m' + spp));
        assert (sxs = f h + smt);
        assert (sxs = f h + (f m' + spp));
        (* Re-associate: f h + (f m' + spp) = (f h + f m') + spp. *)
        add_associativity (f h) (f m') spp;
        assert (f h + (f m' + spp) = (f h + f m') + spp);
        (* f m' = f m by respects_perm_eq. *)
        perm_eq_sym m m';
        respects_perm_eq_elim f m' m;
        assert (f m' = f m);
        (* f h + f m' = f h + f m. *)
        add_congruence (f h) (f m') (f h) (f m);
        assert (f h + f m' = f h + f m);
        (* f h + f m = zero by hypothesis (instantiate at s = h). *)
        assert (f h + f m = zero);
        (* Chain to (f h + f m') + spp = zero + spp. *)
        add_congruence (f h + f m') spp (f h + f m) spp;
        assert ((f h + f m') + spp = (f h + f m) + spp);
        add_congruence (f h + f m) spp (zero #t) spp;
        assert ((f h + f m) + spp = zero #t + spp);
        zero_plus_x spp;
        assert (zero #t + spp = spp);
        (* Build sxs = spp via stepwise transitivity. *)
        (* Establish τ-closure on (pre ++ post) via the peeled-out helper. *)
        assert (xs == h :: L.append pre (m' :: post));
        introduce forall (s: permutation n).
            permutation_in_list s pp ==>
            permutation_in_list (compose s tau) pp
        with introduce _ ==> _
        with _. closure_pp_step h tau pre post m' s;
        (* Recursive call on (pre ++ post). *)
        L.append_length pre (m' :: post);
        L.append_length pre post;
        assert (L.length pp < L.length xs);
        sum_orbit_partition_zero f tau pp;
        assert (spp = zero #t);
        (* Hence sxs = spp = zero. *)
        transitivity sxs spp (zero #t)
#pop-options

(* Final theorem on the full enumeration. *)
let sum_over_perms_pair_cancel
  (#t: Type) {| g: add_comm_group t |}
  (n: nat) (f: permutation n -> t) (tau: permutation n)
  (h_pair: (s: permutation n) -> Lemma (f s + f (compose s tau) = zero))
  : Lemma (requires
              respects_perm_eq #t f /\
              ~ (perm_eq tau (identity n)) /\
              perm_eq (compose tau tau) (identity n))
          (ensures sum_over_perms n f = zero)
  = all_permutations_no_dup n;
    Classical.forall_intro h_pair;
    let xs = all_permutations n in
    let closure (s: permutation n) : Lemma (permutation_in_list (compose s tau) xs)
      = all_permutations_complete n (compose s tau)
    in
    Classical.forall_intro closure;
    sum_orbit_partition_zero f tau xs
