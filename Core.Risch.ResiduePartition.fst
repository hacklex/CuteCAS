module Core.Risch.ResiduePartition

(* ================================================================ *)
(*  Construct the RESIDUE-CLASS PARTITION of `roots`:  partition the  *)
(*  distinct root list into maximal sublists of equal residue.        *)
(*                                                                   *)
(*  This is the last gap to the end-to-end RT answer theorem: feed    *)
(*  the result to `rt_soundness_partition` (Σ group_contribution=p/q) *)
(*  and `RTAnswer.group_contribution_is_vc_term` (each group's term   *)
(*  IS the algorithm's c·v_c'/v_c) to conclude                        *)
(*    d/dx[Σ_c c·log(gcd(p−c·q', q))] = p/q.                          *)
(*                                                                   *)
(*  The "can't L.filter by residue" wall is sidestepped by carrying   *)
(*  the membership invariant: residue is total on `b:t{memP b roots}`.*)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Risch.RTSoundness

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  Opaque membership-invariant predicate.  `all_memP_in l roots`    *)
(*  hides the recurring pointwise hypothesis                         *)
(*    forall z. memP z l ==> memP z roots                            *)
(*  so it never lands raw in a consumer's SMT context.  Bridges:     *)
(*  `_elim` (reveal the forall) and `_intro` (build it from a fn).   *)
(* ================================================================ *)
[@@"opaque_to_smt"]
let all_memP_in (#t:Type) (l roots: list t) : prop =
  forall (z:t). L.memP z l ==> L.memP z roots

let all_memP_in_elim (#t:Type) (l: list t) (roots: list t{all_memP_in l roots})
  : Lemma (forall (z:t). L.memP z l ==> L.memP z roots)
  = reveal_opaque (`%all_memP_in) (all_memP_in l roots)

let all_memP_in_proof (#t:Type) (l roots: list t)
  = (z:t) -> Lemma (L.memP z l ==> L.memP z roots)

let all_memP_in_intro (#t:Type) (l roots: list t)
  (proof: all_memP_in_proof l roots)
  : Lemma (all_memP_in l roots)
  = reveal_opaque (`%all_memP_in) (all_memP_in l roots);
    Classical.forall_intro proof

(* `all_memP_in (y::ys) roots` ==> `all_memP_in ys roots` (tail). *)
let all_memP_in_tail (#t:Type) (y:t) (ys roots: list t)
  : Lemma (requires all_memP_in (y :: ys) roots)
          (ensures all_memP_in ys roots /\ L.memP y roots)
  = all_memP_in_elim (y :: ys) roots;
    all_memP_in_intro ys roots (fun z -> ())

(* ================================================================ *)
(*  split_by_residue: partition a list `l` (all of whose elements    *)
(*  are roots) into the elements with residue equal to that of `x`    *)
(*  (`same`) and the complement (`diff`).  Order-preserving.         *)
(*                                                                   *)
(*  `x` is itself a root so `residue p roots x` is well-defined;     *)
(*  the membership invariant on `l` guards every `residue p roots y`. *)
(* ================================================================ *)

let rec split_same (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (l: list t)
  : Pure (list t)
    (requires all_distinct roots /\ L.memP x roots /\
              all_memP_in l roots)
    (ensures fun _ -> True)
    (decreases l)
  = match l with
    | [] -> []
    | y :: ys ->
        all_memP_in_tail y ys roots;
        let rest = split_same p roots x ys in
        if residue p roots y = residue p roots x
        then y :: rest
        else rest

let rec split_diff (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (l: list t)
  : Pure (list t)
    (requires all_distinct roots /\ L.memP x roots /\
              all_memP_in l roots)
    (ensures fun _ -> True)
    (decreases l)
  = match l with
    | [] -> []
    | y :: ys ->
        all_memP_in_tail y ys roots;
        let rest = split_diff p roots x ys in
        if residue p roots y = residue p roots x
        then rest
        else y :: rest

(* ---------------------------------------------------------------- *)
(*  Membership characterisation of split_same / split_diff.          *)
(* ---------------------------------------------------------------- *)

let rec split_same_memP (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (l: list t) (y:t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_memP_in l roots /\
                    (L.memP y l ==> L.memP y roots))
          (ensures (L.memP y (split_same p roots x l)
                      <==> (L.memP y l /\
                            residue p roots y = residue p roots x)))
          (decreases l)
  = all_memP_in_elim l roots;
    match l with
    | [] -> ()
    | z :: zs ->
        all_memP_in_tail z zs roots;
        split_same_memP p roots x zs y

let rec split_diff_memP (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (l: list t) (y:t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_memP_in l roots /\
                    (L.memP y l ==> L.memP y roots))
          (ensures (L.memP y (split_diff p roots x l)
                      <==> (L.memP y l /\
                            not (residue p roots y = residue p roots x))))
          (decreases l)
  = all_memP_in_elim l roots;
    match l with
    | [] -> ()
    | z :: zs ->
        all_memP_in_tail z zs roots;
        split_diff_memP p roots x zs y

(* Subset facts: every element of split_same / split_diff is in `l`. *)
let split_same_subset (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (l: list t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_memP_in l roots)
          (ensures all_memP_in (split_same p roots x l) l)
  = all_memP_in_elim l roots;
    all_memP_in_intro (split_same p roots x l) l
      (fun y -> Classical.move_requires (split_same_memP p roots x l) y)

let split_diff_subset (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (l: list t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_memP_in l roots)
          (ensures all_memP_in (split_diff p roots x l) l)
  = all_memP_in_elim l roots;
    all_memP_in_intro (split_diff p roots x l) l
      (fun y -> Classical.move_requires (split_diff_memP p roots x l) y)

(* ---------------------------------------------------------------- *)
(*  all_distinct of a sublist (filtered subsequence) of an           *)
(*  all_distinct list.  Proved by a generic sublist lemma.           *)
(* ---------------------------------------------------------------- *)

(* If `s` is a list each of whose elements is in `l`, and `l` is      *)
(* all_distinct, AND `s` has no internal duplicates by virtue of      *)
(* being a subsequence of `l`, then `s` is all_distinct.  We prove a  *)
(* dedicated lemma for split_same / split_diff that uses the          *)
(* membership characterisation + distinctness of `l`.                 *)

let rec split_same_distinct (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (l: list t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_distinct l /\
                    all_memP_in l roots)
          (ensures all_distinct (split_same p roots x l))
          (decreases l)
  = match l with
    | [] -> ()
    | z :: zs ->
        all_memP_in_tail z zs roots;
        (* all_distinct (z::zs) = (forall d. memP d zs ==> not (z=d)) /\ all_distinct zs *)
        assert ((forall (d:t). L.memP d zs ==> not (z = d)) /\ all_distinct zs);
        split_same_distinct p roots x zs;
        let rest = split_same p roots x zs in
        if residue p roots z = residue p roots x
        then begin
          (* head is z; need: forall d in rest. not (z = d), and all_distinct rest. *)
          split_same_subset p roots x zs;   (* memP d rest ==> memP d zs *)
          all_memP_in_elim rest zs;
          assert (forall (d:t). L.memP d rest ==> not (z = d));
          assert (split_same p roots x l == z :: rest)
        end
        else ()

let rec split_diff_distinct (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (l: list t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_distinct l /\
                    all_memP_in l roots)
          (ensures all_distinct (split_diff p roots x l))
          (decreases l)
  = match l with
    | [] -> ()
    | z :: zs ->
        all_memP_in_tail z zs roots;
        assert ((forall (d:t). L.memP d zs ==> not (z = d)) /\ all_distinct zs);
        split_diff_distinct p roots x zs;
        let rest = split_diff p roots x zs in
        if residue p roots z = residue p roots x
        then ()
        else begin
          split_diff_subset p roots x zs;
          all_memP_in_elim rest zs;
          assert (forall (d:t). L.memP d rest ==> not (z = d));
          assert (split_diff p roots x l == z :: rest)
        end

(* ================================================================ *)
(*  Length bound on split_diff (for termination of group_by).        *)
(* ================================================================ *)

let rec split_diff_length_le (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (l: list t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_memP_in l roots)
          (ensures L.length (split_diff p roots x l) <= L.length l)
          (decreases l)
  = match l with
    | [] -> ()
    | z :: zs ->
        all_memP_in_tail z zs roots;
        split_diff_length_le p roots x zs

(* ================================================================ *)
(*  group_by: the recursive maximal grouping.                        *)
(*                                                                   *)
(*  Invariant carried on `sub`:                                      *)
(*   (I1) all_distinct sub                                           *)
(*   (I2) forall y. memP y sub ==> memP y roots                      *)
(*   (I3) forall b z. memP b roots /\ memP z sub /\                  *)
(*                    residue b = residue z ==> memP b sub           *)
(*       "sub holds FULL residue classes of every residue present".  *)
(* ================================================================ *)

[@@"opaque_to_smt"]
let group_by_inv (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t) : prop =
  all_distinct roots /\
  all_distinct sub /\
  (forall (y:t). L.memP y sub ==> L.memP y roots) /\
  (forall (b z:t). L.memP b roots ==> L.memP z roots ==> L.memP z sub ==>
                   (residue p roots b = residue p roots z ==> L.memP b sub))

(* Reveal the raw conjuncts of `group_by_inv` to the SMT context. *)
let group_by_inv_elim (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (sub: list t{group_by_inv p roots sub})
  : Lemma (all_distinct roots /\
           all_distinct sub /\
           (forall (y:t). L.memP y sub ==> L.memP y roots) /\
           (forall (b z:t). L.memP b roots ==> L.memP z roots ==> L.memP z sub ==>
                            (residue p roots b = residue p roots z ==> L.memP b sub)))
  = reveal_opaque (`%group_by_inv) (group_by_inv p roots sub)

(* Build `group_by_inv` from its raw conjuncts. *)
let group_by_inv_intro (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t)
  : Lemma (requires all_distinct roots /\
                    all_distinct sub /\
                    (forall (y:t). L.memP y sub ==> L.memP y roots) /\
                    (forall (b z:t). L.memP b roots ==> L.memP z roots ==> L.memP z sub ==>
                                     (residue p roots b = residue p roots z ==> L.memP b sub)))
          (ensures group_by_inv p roots sub)
  = reveal_opaque (`%group_by_inv) (group_by_inv p roots sub)

(* group prop, parameterized by the FULL roots list (so hd-residue
   and completeness can refer to roots).  Both residue-conjuncts are
   guarded by `all_distinct roots` so the partial `residue` is total. *)
[@@"opaque_to_smt"]
let good_group (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (g: list t) : prop =
  all_distinct roots /\
  Cons? g /\ all_distinct g /\
  (forall (b:t). L.memP b g ==> L.memP b roots) /\
  (forall (b:t). L.memP b g ==>
     residue p roots b = residue p roots (L.hd g)) /\
  (forall (b:t). L.memP b roots ==>
     (residue p roots b = residue p roots (L.hd g) ==> L.memP b g))

(* Reveal the raw conjuncts of `good_group` to the SMT context. *)
let good_group_elim (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (g: list t{good_group p roots g})
  : Lemma (all_distinct roots /\
           Cons? g /\ all_distinct g /\
           (forall (b:t). L.memP b g ==> L.memP b roots) /\
           (forall (b:t). L.memP b g ==>
              residue p roots b = residue p roots (L.hd g)) /\
           (forall (b:t). L.memP b roots ==>
              (residue p roots b = residue p roots (L.hd g) ==> L.memP b g)))
  = reveal_opaque (`%good_group) (good_group p roots g)

(* Build `good_group` from its raw conjuncts. *)
let good_group_intro (#t:Type) {| f: field t |} (p: polynomial t) (roots g: list t)
  : Lemma (requires all_distinct roots /\
                    Cons? g /\ all_distinct g /\
                    (forall (b:t). L.memP b g ==> L.memP b roots) /\
                    (forall (b:t). L.memP b g ==>
                       residue p roots b = residue p roots (L.hd g)) /\
                    (forall (b:t). L.memP b roots ==>
                       (residue p roots b = residue p roots (L.hd g) ==> L.memP b g)))
          (ensures good_group p roots g)
  = reveal_opaque (`%good_group) (good_group p roots g)

(* From `group_by_inv p roots (x::xs)` derive the building blocks the
   split lemmas consume: `memP x roots`, `all_memP_in xs roots`, and
   the distinctness facts.  (The raw I3 is exposed via the elim.) *)
let group_by_inv_cons (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (xs: list t)
  : Lemma (requires group_by_inv p roots (x :: xs))
          (ensures L.memP x roots /\ all_memP_in xs roots /\
                   all_memP_in (x :: xs) roots /\
                   all_distinct xs /\ all_distinct (x :: xs) /\
                   (forall (d:t). L.memP d xs ==> not (x = d)))
  = group_by_inv_elim p roots (x :: xs);
    all_memP_in_intro (x :: xs) roots (fun z -> ());
    all_memP_in_intro xs roots (fun z -> ())

(* The key class-fullness step for diff, factored into a helper. *)
let split_diff_full_class (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (xs: list t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_memP_in xs roots /\
                    group_by_inv p roots (x :: xs))
          (ensures (forall (b z:t). L.memP b roots ==> L.memP z roots ==>
                      L.memP z (split_diff p roots x xs) ==>
                      (residue p roots b = residue p roots z ==>
                       L.memP b (split_diff p roots x xs))))
  = let diff = split_diff p roots x xs in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    group_by_inv_cons p roots x xs;   (* memP x roots, all_memP_in xs roots, I3 raw *)
    all_memP_in_elim xs roots;        (* memP z xs ==> memP z roots *)
    split_diff_subset p roots x xs;   (* all_memP_in diff xs *)
    all_memP_in_elim diff xs;         (* memP z diff ==> memP z xs *)
    let aux (b z:t)
      : Lemma (requires L.memP b roots /\ L.memP z roots /\ L.memP z diff /\
                        residue p roots b = residue p roots z)
              (ensures L.memP b diff)
      = (* z in diff ==> z in xs and residue z != residue x *)
        group_by_inv_elim p roots (x :: xs);   (* re-expose I3 in aux's VC *)
        split_diff_memP p roots x xs z;
        assert (L.memP z xs /\ not (residue p roots z = residue p roots x));
        (* From invariant I3 on (x::xs): b in roots, z in (x::xs),
           residue b = residue z ==> b in (x::xs). *)
        assert (L.memP z (x :: xs));
        assert (L.memP b (x :: xs));         (* by I3 of group_by_inv (x::xs) *)
        if b = x then begin
          assert (b == x);
          assert (residue p roots b == residue p roots x);
          assert (residue p roots x = residue p roots z);
          assert (residue p roots z = residue p roots x);  (* contradiction *)
          ()
        end
        else begin
          assert (L.memP b xs);
          assert (not (residue p roots b = residue p roots x));
          split_diff_memP p roots x xs b;
          assert (L.memP b diff)
        end
    in
    Classical.forall_intro_2 (Classical.move_requires_2 aux)

(* diff preserves the group_by invariant. *)
let group_by_diff_inv (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (xs: list t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_memP_in xs roots /\
                    group_by_inv p roots (x :: xs))
          (ensures group_by_inv p roots (split_diff p roots x xs))
  = let diff = split_diff p roots x xs in
    group_by_inv_cons p roots x xs;              (* memP x roots, all_memP_in xs roots, ... *)
    split_diff_distinct p roots x xs;            (* I1 *)
    split_diff_subset p roots x xs;              (* all_memP_in diff xs *)
    all_memP_in_elim diff xs;                    (* memP z diff ==> memP z xs *)
    all_memP_in_elim xs roots;                   (* memP z xs ==> memP z roots *)
    assert (forall (z:t). L.memP z diff ==> L.memP z roots);  (* I2 raw *)
    split_diff_full_class p roots x xs;          (* I3 raw *)
    group_by_inv_intro p roots diff

let rec group_by (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t)
  : Pure (list (list t))
    (requires all_distinct roots /\ group_by_inv p roots sub)
    (ensures fun _ -> True)
    (decreases L.length sub)
  = match sub with
    | [] -> []
    | x :: xs ->
        group_by_inv_cons p roots x xs;
        let same = split_same p roots x xs in
        let diff = split_diff p roots x xs in
        group_by_diff_inv p roots x xs;
        split_diff_length_le p roots x xs;
        (x :: same) :: group_by p roots diff

(* ================================================================ *)
(*  (1)  flatten (group_by sub) has the same membership as sub.      *)
(*       (Literal `==` is NOT achievable: maximal grouping reorders.) *)
(* ================================================================ *)

let rec group_by_memP (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t) (b:t)
  : Lemma (requires all_distinct roots /\ group_by_inv p roots sub)
          (ensures (L.memP b (L.flatten (group_by p roots sub)) <==> L.memP b sub))
          (decreases L.length sub)
  = match sub with
    | [] -> ()
    | x :: xs ->
        group_by_inv_cons p roots x xs;
        all_memP_in_elim xs roots;
        let same = split_same p roots x xs in
        let diff = split_diff p roots x xs in
        group_by_diff_inv p roots x xs;
        split_diff_length_le p roots x xs;
        (* group_by sub == (x::same) :: group_by diff *)
        let gb_diff = group_by p roots diff in
        (* flatten ((x::same) :: gb_diff) == (x::same) @ flatten gb_diff *)
        L.append_memP (x :: same) (L.flatten gb_diff) b;
        (* IH on diff *)
        group_by_memP p roots diff b;
        (* membership of same / diff in xs *)
        split_same_memP p roots x xs b;
        split_diff_memP p roots x xs b;
        ()

(* ================================================================ *)
(*  (2)+(3)+(4)  The HEAD group `x :: same` is a `good_group`.        *)
(* ================================================================ *)

(* homogeneity body for the head group. *)
let hom_body (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (xs: list t) (b:t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_memP_in xs roots /\
                    group_by_inv p roots (x :: xs) /\
                    L.memP b roots /\ L.memP b (x :: split_same p roots x xs))
          (ensures residue p roots b = residue p roots x)
  = let same = split_same p roots x xs in
    H.elim_equatable_laws t ();
    group_by_inv_cons p roots x xs;
    all_memP_in_elim xs roots;
    (* memP b (x::same)  ==  (b == x) \/ memP b same  (Leibniz on head). *)
    eliminate (b == x) \/ (L.memP b same)
    returns residue p roots b = residue p roots x
    with _h. ()                                   (* b == x: residue congruence + refl *)
    and  _h. split_same_memP p roots x xs b (* memP b same: spec gives = *)

(* completeness body for the head group. *)
let comp_body (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (xs: list t) (b:t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_memP_in xs roots /\
                    group_by_inv p roots (x :: xs) /\
                    L.memP b roots /\
                    residue p roots b = residue p roots x)
          (ensures L.memP b (x :: split_same p roots x xs))
  = let same = split_same p roots x xs in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    group_by_inv_cons p roots x xs;
    group_by_inv_elim p roots (x :: xs);
    all_memP_in_elim xs roots;
    (* I3 with z = x in sub = (x::xs): b in (x::xs). *)
    assert (L.memP x (x :: xs));
    assert (L.memP b (x :: xs));
    (* memP b (x::xs)  ==  (b == x) \/ memP b xs. *)
    eliminate (b == x) \/ (L.memP b xs)
    returns L.memP b (x :: same)
    with _h. ()                                   (* b == x: head of (x::same) *)
    and  _h. (split_same_memP p roots x xs b)  (* memP b xs /\ res= ==> memP b same *)

let head_group_good (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  (x:t) (xs: list t)
  : Lemma (requires all_distinct roots /\ L.memP x roots /\
                    all_memP_in xs roots /\
                    group_by_inv p roots (x :: xs))
          (ensures (good_group p roots (x :: split_same p roots x xs)))
  = let same = split_same p roots x xs in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    group_by_inv_cons p roots x xs;
    (* all_distinct (x::xs) gives: x not in xs, all_distinct xs. *)
    assert ((forall (d:t). L.memP d xs ==> not (x = d)) /\ all_distinct xs);
    all_memP_in_elim xs roots;
    assert (forall (z:t). L.memP z xs ==> L.memP z roots);
    assert (L.memP x roots);
    (* all_distinct (x::same): same distinct + x not in same. *)
    split_same_distinct p roots x xs;
    split_same_subset p roots x xs;     (* all_memP_in same xs *)
    all_memP_in_elim same xs;           (* memP d same ==> memP d xs *)
    assert (forall (d:t). L.memP d same ==> not (x = d));
    assert (all_distinct (x :: same));
    (* subset: memP b (x::same) ==> memP b roots. *)
    assert (forall (b:t). L.memP b same ==> L.memP b roots);
    assert (forall (b:t). L.memP b (x :: same) ==> L.memP b roots);
    (* hd (x::same) == x. *)
    assert (L.hd (x :: same) == x);
    (* homogeneity, via `introduce forall ... with` so each residue call is
       guarded by its membership antecedent. *)
    introduce forall (b:t).
        (L.memP b (x :: same) ==>
         residue p roots b = residue p roots x)
    with introduce L.memP b (x :: same) ==>
                   residue p roots b = residue p roots x
         with _pf. hom_body p roots x xs b;
    (* completeness. *)
    introduce forall (b:t).
        (L.memP b roots ==>
         (residue p roots b = residue p roots x ==>
          L.memP b (x :: same)))
    with introduce L.memP b roots ==>
                   (residue p roots b = residue p roots x ==>
                    L.memP b (x :: same))
         with _pf.
           introduce residue p roots b = residue p roots x ==>
                     L.memP b (x :: same)
           with _pf2. comp_body p roots x xs b;
    good_group_intro p roots (x :: same)

(* ================================================================ *)
(*  (2)+(3)+(4)  Every group produced by group_by is a good_group.   *)
(* ================================================================ *)

let rec group_by_good (#t:Type) {| f: field t |} (p: polynomial t) (roots sub: list t) (g: list t)
  : Lemma (requires all_distinct roots /\ group_by_inv p roots sub /\
                    L.memP g (group_by p roots sub))
          (ensures good_group p roots g)
          (decreases L.length sub)
  = match sub with
    | [] -> ()
    | x :: xs ->
        group_by_inv_cons p roots x xs;
        let same = split_same p roots x xs in
        let diff = split_diff p roots x xs in
        group_by_diff_inv p roots x xs;
        split_diff_length_le p roots x xs;
        (* group_by sub == (x::same) :: group_by diff, so
           memP g (group_by sub) == (g == (x::same)) \/ memP g (group_by diff). *)
        eliminate (g == (x :: same)) \/ (L.memP g (group_by p roots diff))
        returns good_group p roots g
        with _h. head_group_good p roots x xs
        and  _h. group_by_good p roots diff g

(* ================================================================ *)
(*  TOP-LEVEL: residue_partition = group_by over the full root list.  *)
(*                                                                   *)
(*  PRIMARY (1) is delivered in MEMBERSHIP form                       *)
(*      (forall b. memP b (flatten groups) <==> memP b roots)        *)
(*  because maximal residue-grouping necessarily REORDERS roots, so   *)
(*  literal `L.flatten groups == roots` is mathematically false in    *)
(*  general.  Conjuncts (2)+(3)+(4) are delivered in full.           *)
(* ================================================================ *)

(* NOTE: the ensures of `residue_partition` is kept SPELLED OUT (raw
   quantifiers) rather than wrapped in an opaque predicate.  Reason
   (R2 / owner-decision): the conjunct
     (forall g. memP g groups ==> Cons? g /\ all_distinct g /\
                (forall b. memP b g ==> memP b roots) /\ …)
   is exactly the PRECONDITION of `RTSoundness.answer_deriv`, and the
   consumer `RTAnswerEnd.rt_answer_constructed` mentions
   `answer_deriv p roots (residue_partition p roots)` in its OWN ensures.
   Well-definedness of that ensures is checked at the signature level, so
   it cannot be discharged by a body-level `_elim` of an opaque post — it
   needs the spelled-out post visible to the SMT.  An opaque wrap here
   would make `rt_answer_constructed`'s signature un-typecheckable with no
   in-blast-radius fix (would require changing `answer_deriv`'s requires in
   RTSoundness).  Hence this single ensures is REVERTED / left raw. *)
let residue_partition (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t)
  : Pure (list (list t))
    (requires all_distinct roots)
    (ensures fun groups ->
       (forall (b:t). L.memP b (L.flatten groups) <==> L.memP b roots) /\
       (forall (g:list t). L.memP g groups ==>
          (Cons? g /\ all_distinct g /\
           (forall (b:t). L.memP b g ==> L.memP b roots) /\
           (forall (b:t). L.memP b g ==> residue p roots b = residue p roots (L.hd g)) /\
           (forall (b:t). (L.memP b roots /\ residue p roots b = residue p roots (L.hd g))
                          ==> L.memP b g))))
  = (* The full root list trivially satisfies group_by_inv (sub = roots):
       all residue classes present are full because every root is in sub. *)
    all_memP_in_intro roots roots (fun z -> ());
    group_by_inv_intro p roots roots;
    let groups = group_by p roots roots in
    (* (1) membership form of flatten. *)
    Classical.forall_intro (Classical.move_requires (group_by_memP p roots roots));
    (* (2)+(3)+(4): every group is a good_group; reveal good_group to the
       exact conjuncts of the ensures. *)
    Classical.forall_intro (Classical.move_requires (group_by_good p roots roots));
    assert (forall (g:list t). L.memP g groups ==> good_group p roots g);
    Classical.forall_intro
      (Classical.move_requires (good_group_elim p roots));
    groups
