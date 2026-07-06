module Core.Risch.RTAnswerEnd

(* ================================================================ *)
(*  END-TO-END (abstract-group form):  the LRT answer's derivative,  *)
(*  folded over the CONSTRUCTED residue-class partition of `roots`,   *)
(*  equals p/q.                                                       *)
(*                                                                   *)
(*    answer_deriv p roots (residue_partition p roots) = Fraction p q *)
(*                                                                   *)
(*  Chain:  answer_deriv = frac_sum_over_groups                       *)
(*          = frac_sum p roots (flatten groups)        [frac_sum_flatten]   *)
(*          = frac_sum p roots roots                   [frac_sum_perm — NEW] *)
(*          = Fraction p q                             [partial_fraction_decomposition] *)
(*                                                                   *)
(*  `frac_sum_perm` (permutation invariance of the fraction sum) is   *)
(*  the key new primitive; it needs `flatten (residue_partition …)`   *)
(*  to be all_distinct (a permutation of the distinct `roots`).       *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module RP = Core.Risch.ResiduePartition

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Fractions
open Core.Risch.RTSoundness

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  LIST / all_distinct machinery.                                   *)
(*  `all_distinct` (Core.Polynomial.Roots) uses the typeclass bool   *)
(*  `=`; `L.memP` uses Leibniz `==`.  Reflexivity of `=` (via        *)
(*  H.elim_equatable_laws) bridges the two: x == y ==> x = y.        *)
(* ================================================================ *)

(* Decompose cons-membership at spec-typing time, so the Pure         *)
(* preconditions of `frac_sum`/`frac_sum_append` on lists of the form *)
(* `append pre (b :: post)` discharge automatically.                  *)
let memP_cons (#t:Type) (a x: t) (l: list t)
  : Lemma (ensures (L.memP x (a :: l) <==> (x == a \/ L.memP x l)))
          [SMTPat (L.memP x (a :: l))]
  = ()

(* In an all_distinct list, a bool-`=` collision between two memP-members
   forces Leibniz identity. *)
let rec distinct_eq_implies_id (#t:Type) {| f: field t |} (amb: list t) (a b: t)
  : Lemma (requires all_distinct amb /\ L.memP a amb /\ L.memP b amb /\ (a = b))
          (ensures a == b)
          (decreases amb)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match amb with
    | [] -> ()
    | c :: cs ->
        (* all_distinct head: forall d. memP d cs ==> not (c = d). *)
        assert ((forall (d:t). L.memP d cs ==> not (c = d)) /\ all_distinct cs);
        eliminate (a == c) \/ (L.memP a cs)
        returns a == b
        with _ha. (
          eliminate (b == c) \/ (L.memP b cs)
          returns a == b
          with _hb. ()  (* a == c == b *)
          and _hb. (
            (* a == c, memP b cs.  a = b ==> c = b (a==c).  but not (c = b). *)
            assert (c = b);
            assert (not (c = b))
          )
        )
        and _ha. (
          eliminate (b == c) \/ (L.memP b cs)
          returns a == b
          with _hb. (
            (* memP a cs, b == c.  a = b ==> a = c ==> c = a (symm).  but not (c=a). *)
            assert (a = c);

            assert (c = a);
            assert (not (c = a))
          )
          and _hb. distinct_eq_implies_id cs a b
        )

(* The head of an all_distinct list does not memP-occur in its tail. *)
let distinct_head_not_mem (#t:Type) {| f: field t |} (b: t) (l: list t)
  : Lemma (requires all_distinct (b :: l))
          (ensures ~(L.memP b l))
  = H.elim_equatable_laws t ();
    (* all_distinct (b::l) = (forall d. memP d l ==> not (b = d)) /\ all_distinct l *)
    assert (forall (d:t). L.memP d l ==> not (b = d));
    introduce L.memP b l ==> False
    with _hb. (
      (* memP b l : some d in l with b == d; but then b = d (refl), contradiction *)
      assert (b = b)
    )

(* all_distinct is preserved when we drop the middle element b of pre@(b::post),
   and b memP-occurs in neither pre nor post. *)
let rec all_distinct_split (#t:Type) {| f: field t |} (pre: list t) (b: t) (post: list t)
  : Lemma (requires all_distinct (L.append pre (b :: post)))
          (ensures all_distinct (L.append pre post) /\
                   ~(L.memP b pre) /\ ~(L.memP b post))
          (decreases pre)
  = H.elim_equatable_laws t ();
    match pre with
    | [] ->
        (* append [] (b::post) == b::post ; all_distinct (b::post). *)
        distinct_head_not_mem b post
    | c :: cs ->
        (* append (c::cs) (b::post) == c :: append cs (b::post). *)
        (* all_distinct head: forall d. memP d (append cs (b::post)) ==> not (c=d). *)
        assert ((forall (d:t). L.memP d (L.append cs (b :: post)) ==> not (c = d)) /\
                all_distinct (L.append cs (b :: post)));
        all_distinct_split cs b post;
        (* memP d (append cs post) ==> memP d (append cs (b::post)) ==> not (c=d). *)
        L.append_memP cs post b;
        L.append_memP cs (b :: post) b;
        introduce forall (d:t). L.memP d (L.append cs post) ==> not (c = d)
        with introduce L.memP d (L.append cs post) ==> not (c = d)
        with _hd. (
          L.append_memP cs post d;
          L.append_memP cs (b :: post) d;
          assert (L.memP d (L.append cs (b :: post)))
        );
        (* b not in (c::cs): b not in cs (from rec), and b<>c... actually need b != c
           via Leibniz failing.  memP b (c::cs) = (b==c \/ memP b cs).  b not in cs by IH.
           if b==c then c memP (b::post)? c==b means memP c (append cs (b::post)), but head
           distinctness says not (c=c) — contradiction since c=c. *)
        introduce L.memP b (c :: cs) ==> False
        with _hb. (
          eliminate (b == c) \/ (L.memP b cs)
          returns False
          with _h1. (
            (* b == c ; c occurs at head of (b::post) inside the big append. *)
            L.append_memP cs (b :: post) c;
            assert (L.memP c (L.append cs (b :: post)));
            assert (c = c)
          )
          and _h2. ()  (* contradicts ~(memP b cs) from IH *)
        )

(* all_distinct of (b::l1') from all_distinct (b::l1'): gives all_distinct l1'. *)
let distinct_tail (#t:Type) {| f: field t |} (b: t) (l: list t)
  : Lemma (requires all_distinct (b :: l))
          (ensures all_distinct l)
  = ()

(* ================================================================ *)
(*  frac_sum REMOVAL: hoist the simple term of b (a middle element)   *)
(*  to the front of frac_sum over pre@(b::post).                      *)
(*    frac_sum (pre@(b::post)) = simple_term b (+) frac_sum (pre@post)*)
(* ================================================================ *)
let frac_sum_remove (#t:Type) {| f: field t |} (p: polynomial t) (roots pre post: list t) (b: t)
  : Lemma (requires all_distinct roots /\ L.memP b roots /\
                    (forall (x:t). L.memP x pre ==> L.memP x roots) /\
                    (forall (x:t). L.memP x post ==> L.memP x roots))
          (ensures
            (frac_sum p roots (L.append pre (b :: post)))
              = (fraction_add #(polynomial t) #(polynomial_id #t #(id_of_f t))
                   (simple_term p roots b)
                   (frac_sum p roots (L.append pre post))))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    (* membership facts for the appends. *)
    L.append_memP pre (b :: post) b;
    L.append_memP pre post b;
    let st  : fraction id_p = simple_term p roots b in
    let fpre : fraction id_p = frac_sum p roots pre in
    let fpost: fraction id_p = frac_sum p roots post in
    (* (A)  frac_sum (pre @ (b::post)) = fpre (+) frac_sum (b::post). *)
    frac_sum_append p roots pre (b :: post);
    (* frac_sum (b::post) = st (+) fpost  (definitional). *)
    (* so RHS of (A): fpre (+) (st (+) fpost). *)
    (* (B)  hoist:  fpre (+) (st (+) fpost) = st (+) (fpre (+) fpost). *)
    (* B.1  st (+) fpost = fpost (+) st   (comm). *)
    frac_add_comm st fpost;
    (* B.2  fpre (+) (st (+) fpost) = fpre (+) (fpost (+) st)  (right cong). *)
    frac_add_cong_r fpre
      (fraction_add st fpost)
      (fraction_add fpost st);
    (* B.3  fpre (+) (fpost (+) st) = (fpre (+) fpost) (+) st  (assoc backwards). *)
    frac_add_assoc fpre fpost st;
    symmetry (fraction_add
                (fraction_add fpre fpost) st)
             (fraction_add fpre
                (fraction_add fpost st));
    (* B.4  (fpre (+) fpost) (+) st = st (+) (fpre (+) fpost)  (comm). *)
    frac_add_comm
      (fraction_add fpre fpost) st;
    (* (C)  fpre (+) fpost = frac_sum (pre @ post)  (append backwards). *)
    frac_sum_append p roots pre post;
    symmetry (frac_sum p roots (L.append pre post))
             (fraction_add fpre fpost);
    (* (D)  st (+) (fpre (+) fpost) = st (+) frac_sum (pre@post)  (right cong). *)
    frac_add_cong_r st
      (fraction_add fpre fpost)
      (frac_sum p roots (L.append pre post));
    (* Now chain everything.
       L := frac_sum (pre@(b::post))
       T1 := fpre (+) (st (+) fpost)               [= frac_sum (pre@(b::post)) by (A)]
       T2 := fpre (+) (fpost (+) st)               [B.2]
       T3 := (fpre (+) fpost) (+) st               [B.3 backwards]
       T4 := st (+) (fpre (+) fpost)               [B.4]
       T5 := st (+) frac_sum (pre@post)            [D] *)
    let t1 : fraction id_p =
      fraction_add fpre
        (fraction_add st fpost) in
    let t2 : fraction id_p =
      fraction_add fpre
        (fraction_add fpost st) in
    let t3 : fraction id_p =
      fraction_add
        (fraction_add fpre fpost) st in
    let t4 : fraction id_p =
      fraction_add st
        (fraction_add fpre fpost) in
    let t5 : fraction id_p =
      fraction_add st
        (frac_sum p roots (L.append pre post)) in
    transitivity (frac_sum p roots (L.append pre (b :: post))) t1 t2;
    transitivity (frac_sum p roots (L.append pre (b :: post))) t2 t3;
    transitivity (frac_sum p roots (L.append pre (b :: post))) t3 t4;
    transitivity (frac_sum p roots (L.append pre (b :: post))) t4 t5

(* ================================================================ *)
(*  Permutation invariance of frac_sum: equal-membership duplicate-  *)
(*  free sublists of `roots` give equal sums.                        *)
(* ================================================================ *)
let rec frac_sum_perm (#t:Type) {| f: field t |} (p: polynomial t) (roots l1 l2: list t)
  : Lemma (requires all_distinct roots /\ all_distinct l1 /\ all_distinct l2 /\
                    (forall (b:t). L.memP b l1 ==> L.memP b roots) /\
                    (forall (b:t). L.memP b l2 ==> L.memP b roots) /\
                    (forall (b:t). L.memP b l1 <==> L.memP b l2))
          (ensures frac_sum p roots l1 = frac_sum p roots l2)
          (decreases l1)
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    match l1 with
    | [] ->
        (* l2 has no members ==> l2 = []. *)
        (match l2 with
         | [] -> ()
         | c :: cs ->
             (* c memP l2 ==> c memP l1 = [] : impossible. *)
             assert (L.memP c l2);
             assert (L.memP c l1))
    | b :: l1' ->
        (* b memP l1 ==> b memP l2. *)
        assert (L.memP b l1);
        assert (L.memP b l2);
        (* split l2 at b. *)
        let pre, suf = L.split_using l2 b in
        L.lemma_split_using l2 b;
        (* suf = b :: post ; pre @ suf == l2 ; ~(b memP pre). *)
        let post : list t = L.tl suf in
        assert (suf == b :: post);
        assert (L.append pre suf == l2);
        assert (~(L.memP b pre));
        (* membership: pre, post ⊆ roots (subset of l2 ⊆ roots). *)
        L.append_memP pre suf b;
        introduce forall (x:t). L.memP x pre ==> L.memP x roots
        with introduce L.memP x pre ==> L.memP x roots
        with _hx. (L.append_memP pre suf x);
        introduce forall (x:t). L.memP x post ==> L.memP x roots
        with introduce L.memP x post ==> L.memP x roots
        with _hx. (L.append_memP pre suf x);
        (* all_distinct facts on the split. *)
        all_distinct_split pre b post;
        (* all_distinct (pre@post) and ~(b memP pre), ~(b memP post). *)
        distinct_tail b l1';
        (* IH preconditions: equal membership of l1' and (pre@post). *)
        introduce forall (x:t). L.memP x l1' <==> L.memP x (L.append pre post)
        with (
          L.append_memP pre post x;
          L.append_memP pre suf x;
          (* memP x l1 = (x==b \/ memP x l1'); memP x l2 = memP x pre \/ memP x suf
             = memP x pre \/ x==b \/ memP x post. *)
          eliminate (x == b) \/ (~(x == b))
          returns L.memP x l1' <==> L.memP x (L.append pre post)
          with _he. (
            (* x == b : memP b l1' false (distinct (b::l1')); b not in pre/post. *)
            distinct_head_not_mem b l1'
          )
          and _hne. ()
        );
        (* IH on l1' and (pre@post). *)
        frac_sum_perm p roots l1' (L.append pre post);
        (* frac_sum l1 = st (+) frac_sum l1'. *)
        let st  : fraction id_p = simple_term p roots b in
        let f1' : fraction id_p = frac_sum p roots l1' in
        let fpp : fraction id_p = frac_sum p roots (L.append pre post) in
        (* st (+) frac_sum l1' = st (+) frac_sum (pre@post)  (right cong via IH). *)
        frac_add_cong_r st f1' fpp;
        (* frac_sum_remove: frac_sum l2 = st (+) frac_sum (pre@post). *)
        (* l2 == pre @ (b::post) == pre @ suf. *)
        assert (L.append pre (b :: post) == l2);
        frac_sum_remove p roots pre post b;
        symmetry (frac_sum p roots (L.append pre (b :: post)))
                 (fraction_add st fpp);
        (* chain: frac_sum l1 = st (+) f1' = st (+) fpp = frac_sum l2. *)
        transitivity (frac_sum p roots l1)
                     (fraction_add st f1')
                     (fraction_add st fpp);
        transitivity (frac_sum p roots l1)
                     (fraction_add st fpp)
                     (frac_sum p roots l2)

(* ================================================================ *)
(*  all_distinct (flatten (group_by p roots sub)).                   *)
(*  flatten (group_by sub) is a permutation of the distinct `sub`,   *)
(*  hence distinct.  Proved alongside its membership characterisation *)
(*  (group_by_memP) and the disjointness of the head class from the  *)
(*  diff recursion.                                                  *)
(* ================================================================ *)

(* Generic: append of two all_distinct lists with NO bool-`=` collision across
   them is all_distinct.  Standalone (self-recursive only). *)
let rec all_distinct_append (#t:Type) {| f: field t |} (l1 l2: list t)
  : Lemma (requires all_distinct l1 /\ all_distinct l2 /\
                    (forall (a b:t). L.memP a l1 ==> L.memP b l2 ==> not (a = b)))
          (ensures all_distinct (L.append l1 l2))
          (decreases l1)
  = match l1 with
    | [] -> ()
    | c :: cs ->
        (* all_distinct (c::cs): forall d. memP d cs ==> not (c=d), all_distinct cs. *)
        assert ((forall (d:t). L.memP d cs ==> not (c = d)) /\ all_distinct cs);
        all_distinct_append cs l2;
        (* head: forall d. memP d (append cs l2) ==> not (c=d). *)
        introduce forall (d:t). L.memP d (L.append cs l2) ==> not (c = d)
        with introduce L.memP d (L.append cs l2) ==> not (c = d)
        with _hd. (
          L.append_memP cs l2 d;
          eliminate (L.memP d cs) \/ (L.memP d l2)
          returns not (c = d)
          with _h1. ()                          (* memP d cs ==> not (c=d) (head distinctness) *)
          and _h2. ()                           (* memP c l1 (head) /\ memP d l2 ==> not (c=d) *)
        )

(* head class (x::same) is distinct and disjoint (memP-wise) from
   flatten (group_by diff): an element of (x::same) has residue = residue x,
   an element of flatten(group_by diff) is in diff (residue != residue x). *)
let rec group_by_flatten_distinct (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t)
  : Lemma (requires all_distinct roots /\ RP.group_by_inv p roots sub)
          (ensures all_distinct (L.flatten (RP.group_by p roots sub)))
          (decreases L.length sub)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match sub with
    | [] -> ()
    | x :: xs ->
        RP.group_by_inv_cons p roots x xs;     (* memP x roots, all_memP_in xs roots *)
        RP.all_memP_in_elim xs roots;          (* memP y xs ==> memP y roots *)
        let same = RP.split_same p roots x xs in
        let diff = RP.split_diff p roots x xs in
        RP.group_by_diff_inv p roots x xs;
        RP.split_diff_length_le p roots x xs;
        let gb_diff = RP.group_by p roots diff in
        (* group_by sub == (x::same) :: gb_diff
           flatten == (x::same) @ flatten gb_diff *)
        (* head class is a good_group: distinct etc. *)
        RP.head_group_good p roots x xs;
        RP.good_group_elim p roots (x :: same);   (* expose all_distinct (x::same) etc. *)
        (* IH on diff: flatten gb_diff distinct. *)
        group_by_flatten_distinct p roots diff;
        (* membership characterisation of flatten gb_diff = memP in diff. *)
        introduce forall (b:t). L.memP b (L.flatten gb_diff) <==> L.memP b diff
        with RP.group_by_memP p roots diff b;
        (* x::same memberships. *)
        RP.split_same_subset p roots x xs;
        RP.all_memP_in_elim same xs;           (* memP y same ==> memP y xs *)
        introduce forall (b:t). L.memP b (x :: same) ==> L.memP b roots
        with introduce L.memP b (x :: same) ==> L.memP b roots
        with _hb. (
          eliminate (b == x) \/ (L.memP b same)
          returns L.memP b roots
          with _h. ()
          and _h. ()
        );
        (* homogeneity: every b in (x::same) has residue = residue x. *)
        introduce forall (b:t). L.memP b (x :: same) ==> residue p roots b = residue p roots x
        with introduce L.memP b (x :: same) ==> residue p roots b = residue p roots x
        with _hb. RP.hom_body p roots x xs b;
        (* diff: every b in diff has residue != residue x, and b in roots. *)
        RP.split_diff_subset p roots x xs;
        RP.all_memP_in_elim diff xs;           (* memP y diff ==> memP y xs *)
        introduce forall (b:t). L.memP b diff ==> L.memP b roots
        with introduce L.memP b diff ==> L.memP b roots
        with _hb. ();
        introduce forall (b:t). L.memP b diff ==> not (residue p roots b = residue p roots x)
        with introduce L.memP b diff ==> not (residue p roots b = residue p roots x)
        with _hb. RP.split_diff_memP p roots x xs b;
        (* bool-`=` disjointness across (x::same) and flatten gb_diff. *)
        introduce forall (a b:t).
            L.memP a (x :: same) ==> L.memP b (L.flatten gb_diff) ==> not (a = b)
        with introduce L.memP a (x :: same) ==>
                       (L.memP b (L.flatten gb_diff) ==> not (a = b))
        with _ha. introduce L.memP b (L.flatten gb_diff) ==> not (a = b)
        with _hb. (
          (* b in flatten gb_diff ==> b in diff ==> b in roots, residue b != residue x. *)
          assert (L.memP b diff);
          assert (L.memP b roots);
          assert (residue p roots a = residue p roots x);
          assert (not (residue p roots b = residue p roots x));
          (* if a = b then a == b (both in roots, distinct), residues coincide. *)
          introduce (a = b) ==> False
          with _heq. (
            distinct_eq_implies_id roots a b;
            assert (a == b);
            assert (residue p roots b = residue p roots x)
          )
        );
        (* assemble all_distinct ((x::same) @ flatten gb_diff). *)
        all_distinct_append (x :: same) (L.flatten gb_diff)

(* ================================================================ *)
(*  flatten (residue_partition p roots) is all_distinct.             *)
(* ================================================================ *)
let residue_partition_flatten_distinct (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  : Lemma (requires all_distinct roots)
          (ensures all_distinct (L.flatten (RP.residue_partition p roots)))
  = (* residue_partition p roots == group_by p roots roots (definitional). *)
    RP.all_memP_in_intro roots roots (fun z -> ());
    RP.group_by_inv_intro p roots roots;
    group_by_flatten_distinct p roots roots

(* ================================================================ *)
(*  The end-to-end identity over the constructed residue partition.  *)
(* ================================================================ *)
let rt_answer_constructed (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  : Lemma (requires Cons? roots /\ all_distinct roots /\
                    deg p < L.length roots)
          (ensures
            is_nonzero (poly_prod_linears roots) /\
            (answer_deriv p roots (RP.residue_partition p roots))
              = (Fraction #(polynomial t) #(polynomial_id #t #(id_of_f t))
                   p (poly_prod_linears roots)))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    prod_linears_nonzero roots;
    let q : (qq:polynomial t{is_nonzero qq}) = poly_prod_linears roots in
    let groups = RP.residue_partition p roots in
    (* residue_partition ensures: per-group well-formedness + flatten membership. *)
    (* (1) answer_deriv = frac_sum_over_groups. *)
    answer_eq_frac_sum_over_groups p roots groups;
    (* (2) frac_sum_over_groups = frac_sum p roots (flatten groups). *)
    frac_sum_flatten p roots groups;
    (* (3) flatten groups is all_distinct. *)
    residue_partition_flatten_distinct p roots;
    (* (4) frac_sum p roots (flatten groups) = frac_sum p roots roots
           (permutation invariance; equal membership from residue_partition). *)
    frac_sum_perm p roots (L.flatten groups) roots;
    (* (5) partial fractions: Fraction p q = frac_sum p roots roots. *)
    partial_fraction_decomposition p roots;
    symmetry (Fraction p q)
             (frac_sum p roots roots);
    (* chain:
         answer_deriv groups
           = frac_sum_over_groups groups            [step 1]
           = frac_sum p roots (flatten groups)      [step 2]
           = frac_sum p roots roots                 [step 4]
           = Fraction p q                           [step 5 backwards]. *)
    transitivity (answer_deriv p roots groups)
                 (frac_sum_over_groups p roots groups)
                 (frac_sum p roots (L.flatten groups));
    transitivity (answer_deriv p roots groups)
                 (frac_sum p roots (L.flatten groups))
                 (frac_sum p roots roots);
    transitivity (answer_deriv p roots groups)
                 (frac_sum p roots roots)
                 (Fraction p q)
