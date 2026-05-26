module Core.Permutation.Enum

(*
   Enumeration of all permutations of `fin n` via insertion.

   The canonical recursion: a permutation of `fin (n+1)` is uniquely
   determined by

     (1) its image of the new element `n`, an arbitrary `k : fin (n+1)`, and
     (2) a permutation `p` of `fin n`, used for the rest by shifting up
         entries that would collide with `k`.

   Hence  |S_{n+1}|  =  (n+1) * |S_n|  =  (n+1)!.

   This file builds that construction and proves the standard completeness
   and pairwise-distinctness lemmas.
*)

module TC = FStar.Tactics.Typeclasses
module Atomic = Core.Algebra
open Core.Algebra
open Core.Permutation
open Core.FinSum

(* Local aliases for perm_eq sym/trans. *)
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

(* -------------------------------------------------------------------- *)
(*  Insertion: build a permutation of fin (n+1) from a permutation of
    fin n and a target index k for the new element.

    fwd:  i = n        |->  k
          i < n        |->  let v = p.fwd i in
                            if v < k then v else v+1

    bwd:  j = k        |->  n
          j < k        |->  p.bwd j   (cast: j < k <= n, so j < n)
          j > k        |->  p.bwd (j-1)
*)

let insert_fwd (#n: nat) (p: permutation n) (k: fin (n+1)) (i: fin (n+1))
  : fin (n+1)
  = if i = n then k
    else
      let i' : fin n = i in
      let v = p.fwd i' in
      if v < k then v
      else (v + 1)

let insert_bwd (#n: nat) (p: permutation n) (k: fin (n+1)) (j: fin (n+1))
  : fin (n+1)
  = if j = k then n
    else if j < k then
      let j' : fin n = j in     (* j < k <= n *)
      p.bwd j'
    else
      (* j > k, j < n+1, so j >= 1; (j-1) < n *)
      let j' : fin n = j - 1 in
      p.bwd j'

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let insert_fwd_bwd_id (#n: nat) (p: permutation n) (k: fin (n+1)) (j: fin (n+1))
  : Lemma (insert_fwd p k (insert_bwd p k j) == j)
  = if j = k then ()
    else if j < k then begin
      let j' : fin n = j in
      p.fwd_bwd_id j';
      let v = p.fwd (p.bwd j') in
      assert (v == j');
      assert (v < k)
    end else begin
      let j' : fin n = j - 1 in
      p.fwd_bwd_id j';
      let v = p.fwd (p.bwd j') in
      assert (v == j');
      assert (v >= k)
    end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let insert_bwd_fwd_id (#n: nat) (p: permutation n) (k: fin (n+1)) (i: fin (n+1))
  : Lemma (insert_bwd p k (insert_fwd p k i) == i)
  = if i = n then ()
    else begin
      let i' : fin n = i in
      let v = p.fwd i' in
      p.bwd_fwd_id i';
      if v < k then begin
        assert (insert_fwd p k i == v);
        assert (v < k);
        assert (insert_bwd p k v == p.bwd v);
        assert (p.bwd v == i')
      end else begin
        assert (insert_fwd p k i == v + 1);
        assert (v + 1 > k);
        assert (insert_bwd p k (v + 1) == p.bwd v);
        assert (p.bwd v == i')
      end
    end
#pop-options

let insert (#n: nat) (p: permutation n) (k: fin (n+1)) : permutation (n+1) = {
  fwd = insert_fwd p k;
  bwd = insert_bwd p k;
  fwd_bwd_id = (fun j -> insert_fwd_bwd_id p k j);
  bwd_fwd_id = (fun i -> insert_bwd_fwd_id p k i);
}

(* -------------------------------------------------------------------- *)
(*  Sanity: insert maps n to k by construction. *)
let insert_top (#n: nat) (p: permutation n) (k: fin (n+1))
  : Lemma ((insert p k).fwd n == k)
  = ()

(*  Inserted permutation, restricted to indices below n, agrees with p
    up to a shift at the threshold k. *)
let insert_below (#n: nat) (p: permutation n) (k: fin (n+1)) (i: fin n)
  : Lemma (let v = p.fwd i in
           (insert p k).fwd i == (if v < k then v else v + 1))
  = ()

(* -------------------------------------------------------------------- *)
(*  Recursive enumeration.                                              *)

module L = FStar.List.Tot

(* expand p inserts p at every position 0..n, producing n+1 permutations
   of fin (n+1). *)
let rec expand_aux (#n: nat) (p: permutation n) (k: nat{k <= n+1})
  : Tot (list (permutation (n+1))) (decreases (n + 1 - k))
  = if k = n+1 then []
    else (insert p k) :: expand_aux p (k + 1)

let expand (#n: nat) (p: permutation n) : list (permutation (n+1))
  = expand_aux p 0

(* Build all permutations of fin (m+1) from those of fin m. *)
let all_permutations_succ (#m: nat) (xs: list (permutation m)) : list (permutation (m+1))
  = L.concatMap (fun (p: permutation m) -> expand #m p) xs

let rec all_permutations (n: nat) : Tot (list (permutation n)) (decreases n)
  = match n with
    | 0 -> [identity 0]
    | _ -> all_permutations_succ #(n - 1) (all_permutations (n - 1))

let all_permutations_zero () : Lemma (all_permutations 0 == [identity 0]) = ()

(* Definitional unfolding for the recursive case. *)
#push-options "--fuel 2 --ifuel 2"
let all_permutations_succ_eq (m: nat)
  : Lemma (all_permutations (m + 1) == all_permutations_succ #m (all_permutations m))
  = ()
#pop-options

(* -------------------------------------------------------------------- *)
(*  Length: |all_permutations n| = n!                                   *)

let rec factorial (n: nat) : Tot nat
  = if n = 0 then 1 else n * factorial (n - 1)

let rec expand_aux_length (#n: nat) (p: permutation n) (k: nat{k <= n+1})
  : Lemma (ensures L.length (expand_aux p k) == (n + 1) - k)
          (decreases (n + 1 - k))
  = if k = n + 1 then ()
    else expand_aux_length p (k + 1)

let expand_length (#n: nat) (p: permutation n)
  : Lemma (L.length (expand p) == n + 1)
  = expand_aux_length p 0

(* Length of concatMap = sum of lengths of mapped pieces. *)
let rec length_concatMap_const
  (#a #b: Type)
  (f: a -> list b)
  (xs: list a)
  (c: nat)
  : Lemma (requires forall (x: a). L.memP x xs ==> L.length (f x) == c)
          (ensures L.length (L.concatMap f xs) == c * L.length xs)
  = match xs with
    | [] -> ()
    | x :: tl ->
        length_concatMap_const f tl c;
        L.append_length (f x) (L.concatMap f tl)

#push-options "--fuel 2 --ifuel 2"
let all_permutations_step (n: nat{n > 0})
  : Lemma (all_permutations n ==
           all_permutations_succ #(n-1) (all_permutations (n-1)))
  = ()
#pop-options

let rec all_permutations_length (n: nat)
  : Lemma (ensures L.length (all_permutations n) == factorial n)
          (decreases n)
  = match n with
    | 0 -> ()
    | _ ->
      let m : nat = n - 1 in
      all_permutations_length m;
      let f : (permutation m -> list (permutation (m+1))) = fun p -> expand p in
      let aux (p: permutation m) : Lemma (L.length (f p) == m + 1) =
        expand_length p
      in
      Classical.forall_intro aux;
      length_concatMap_const f (all_permutations m) (m + 1);
      all_permutations_succ_eq m

(* -------------------------------------------------------------------- *)
(*  Reduction: inverse of insert.                                     *)
(*                                                                      *)
(*  Given p : permutation (m+1), define a permutation reduce p        *)
(*  of fin m by removing the image of m (call it k) and shifting        *)
(*  entries above k down by one.                                        *)
(* -------------------------------------------------------------------- *)

let fwd_top_image (#m: nat) (p: permutation (m+1)) : fin (m+1)
  = p.fwd m

(* For i: fin m, p.fwd i (lifted to fin (m+1)) is distinct from p.fwd m. *)
let fwd_below_top_distinct (#m: nat) (p: permutation (m+1)) (i: fin m)
  : Lemma (p.fwd (i <: fin (m+1)) <> p.fwd m)
  = let i' : fin (m+1) = i in
    if p.fwd i' = p.fwd m then fwd_injective p i' m

(* For i: fin m (so i < m < m+1) the image p.fwd i differs from k = p.fwd m.
   We project it back into fin m. *)
let reduce_fwd_value (#m: pos) (p: permutation (m+1)) (i: fin m) : fin m
  = let k = fwd_top_image p in
    let i' : fin (m+1) = i in
    let v : fin (m+1) = p.fwd i' in
    fwd_below_top_distinct p i;   (* v <> k *)
    if v < k then v
    else (v - 1)

(* For j: fin m, build the corresponding j' in fin (m+1) by skipping k. *)
let reduce_bwd_lift (#m: nat) (k: fin (m+1)) (j: fin m) : fin (m+1)
  = if j < k then j else j + 1

(* j' = reduce_bwd_lift k j is distinct from k. *)
let reduce_bwd_lift_distinct (#m: nat) (k: fin (m+1)) (j: fin m)
  : Lemma (reduce_bwd_lift k j <> k)
  = ()

(* p.bwd j' is distinct from m when j' <> k = p.fwd m. *)
let bwd_distinct_from_top (#m: nat) (p: permutation (m+1)) (j': fin (m+1))
  : Lemma (requires j' <> p.fwd m) (ensures p.bwd j' <> m)
  = p.fwd_bwd_id j'

let reduce_bwd_value (#m: pos) (p: permutation (m+1)) (j: fin m) : fin m
  = let k = fwd_top_image p in
    let j' = reduce_bwd_lift k j in
    reduce_bwd_lift_distinct k j;
    bwd_distinct_from_top p j';
    let i : fin (m+1) = p.bwd j' in
    (* i <> m and i < m+1, so i < m *)
    i

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let reduce_fwd_bwd_id (#m: pos) (p: permutation (m+1)) (j: fin m)
  : Lemma (reduce_fwd_value p (reduce_bwd_value p j) == j)
  = let k = fwd_top_image p in
    let j' = reduce_bwd_lift k j in
    let i = reduce_bwd_value p j in
    let i' : fin (m+1) = i in
    p.fwd_bwd_id j';                  (* p.fwd i' == j' *)
    fwd_below_top_distinct p i;       (* j' <> k *)
    if j < k then begin
      assert (j' == (j <: nat));
      assert (j' < k);
      assert (reduce_fwd_value p i == j')
    end else begin
      assert (j' == j + 1);
      assert (j' > k);
      assert (reduce_fwd_value p i == j' - 1);
      assert (j' - 1 == j)
    end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let reduce_bwd_fwd_id (#m: pos) (p: permutation (m+1)) (i: fin m)
  : Lemma (reduce_bwd_value p (reduce_fwd_value p i) == i)
  = let k = fwd_top_image p in
    let i' : fin (m+1) = i in
    let v : fin (m+1) = p.fwd i' in
    fwd_below_top_distinct p i;       (* v <> k *)
    p.bwd_fwd_id i';                  (* p.bwd v == i' *)
    if v < k then begin
      let j : fin m = v in
      assert (reduce_fwd_value p i == j);
      assert (reduce_bwd_lift k j == (j <: nat))
    end else begin
      let j : fin m = v - 1 in
      assert (reduce_fwd_value p i == j);
      assert (j + 1 == (v <: nat));
      assert (j >= k);
      assert (reduce_bwd_lift k j == j + 1)
    end
#pop-options

let reduce (#m: pos) (p: permutation (m+1)) : permutation m = {
  fwd = reduce_fwd_value p;
  bwd = reduce_bwd_value p;
  fwd_bwd_id = (fun j -> reduce_fwd_bwd_id p j);
  bwd_fwd_id = (fun i -> reduce_bwd_fwd_id p i);
}

(* -------------------------------------------------------------------- *)
(*  Bridging lemma: insert (reduce p) (p.fwd m) is perm-eq to p.        *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let insert_reduce_pointwise (#m: pos) (p: permutation (m+1)) (i: fin (m+1))
  : Lemma ((insert (reduce p) (p.fwd m)).fwd i == p.fwd i)
  = let k = p.fwd m in
    let q = reduce p in
    if i = m then
      assert ((insert q k).fwd i == k)
    else begin
      let i' : fin m = i in
      let w : fin (m+1) = p.fwd i in
      fwd_below_top_distinct p i';    (* w <> k *)
      let v = q.fwd i' in              (* = reduce_fwd_value p i' *)
      if w < k then begin
        assert (v == (w <: nat));
        assert ((insert q k).fwd i == v);
        assert (v < k);
        assert ((insert q k).fwd i == w)
      end else begin
        assert (w > k);
        assert (v == w - 1);
        assert (v >= k);
        assert ((insert q k).fwd i == v + 1);
        assert (v + 1 == (w <: nat))
      end
    end
#pop-options

let insert_reduce_perm_eq (#m: pos) (p: permutation (m+1))
  : Lemma (perm_eq (insert (reduce p) (p.fwd m)) p)
  = Classical.forall_intro (insert_reduce_pointwise p);
    perm_eq_intro (insert (reduce p) (p.fwd m)) p (insert_reduce_pointwise p)

(* -------------------------------------------------------------------- *)
(*  Membership lemmas for concatMap and expand.                         *)
(* -------------------------------------------------------------------- *)

let rec mem_concatMap
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
          = mem_concatMap f y tl x in
        Classical.move_requires aux ()

let rec mem_expand_aux (#n: nat) (p: permutation n) (start: nat{start <= n + 1}) (k: nat)
  : Lemma (requires start <= k /\ k <= n)
          (ensures L.memP (insert p k) (expand_aux p start))
          (decreases (n + 1 - start))
  = if start = k then ()
    else mem_expand_aux p (start + 1) k

let mem_expand (#n: nat) (p: permutation n) (k: fin (n + 1))
  : Lemma (L.memP (insert p k) (expand p))
  = mem_expand_aux p 0 k

(* -------------------------------------------------------------------- *)
(*  insert is a congruence in its permutation argument.                 *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let insert_congruence_pointwise (#n: nat) (p q: permutation n) (k: fin (n+1)) (i: fin (n+1))
  : Lemma (requires perm_eq p q)
          (ensures (insert p k).fwd i == (insert q k).fwd i)
  = if i = n then ()
    else begin
      let i' : fin n = i in
      perm_eq_elim p q i'
    end
#pop-options

let insert_congruence (#n: nat) (p q: permutation n) (k: fin (n+1))
  : Lemma (requires perm_eq p q)
          (ensures perm_eq (insert p k) (insert q k))
  = Classical.forall_intro (Classical.move_requires (insert_congruence_pointwise p q k));
    let pwd (i: fin (n+1)) : Lemma ((insert p k).fwd i == (insert q k).fwd i)
      = insert_congruence_pointwise p q k i in
    perm_eq_intro (insert p k) (insert q k) pwd

(* -------------------------------------------------------------------- *)
(*  Completeness of all_permutations.                                   *)
(* -------------------------------------------------------------------- *)

let completeness_base (p: permutation 0)
  : Lemma (permutation_in_list p (all_permutations 0))
  = perm_eq_intro p (identity 0) (fun _ -> ());
    assert (L.memP (identity 0) (all_permutations 0))

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let completeness_step (m: nat) (p: permutation (m+1))
  (ih: (q: permutation m -> Lemma (permutation_in_list q (all_permutations m))))
  : Lemma (permutation_in_list p (all_permutations (m+1)))
  = match m with
    | 0 ->
        let k : fin 1 = p.fwd 0 in
        let q0 : permutation 0 = identity 0 in
        assert (L.memP q0 (all_permutations 0));
        all_permutations_succ_eq 0;
        mem_expand q0 k;
        mem_concatMap (fun (r: permutation 0) -> expand r) q0 (all_permutations 0)
                      (insert q0 k);
        perm_eq_intro p (insert q0 k) (fun _ -> ())
    | _ ->
        let m_pos : pos = m in
        let k = p.fwd m in
        let p' : permutation m = reduce #m_pos p in
        ih p';
        let aux (q': permutation m)
          : Lemma (requires L.memP q' (all_permutations m) /\ perm_eq p' q')
                  (ensures permutation_in_list p (all_permutations (m+1)))
          = insert_congruence p' q' k;
            insert_reduce_perm_eq #m_pos p;
            perm_eq_sym (insert p' k) p;
            perm_eq_trans p (insert p' k) (insert q' k);
            all_permutations_succ_eq m;
            mem_expand q' k;
            mem_concatMap (fun (r: permutation m) -> expand r) q' (all_permutations m)
                          (insert q' k)
          in
        Classical.exists_elim
          (permutation_in_list p (all_permutations (m+1)))
          #(permutation m)
          #(fun q' -> L.memP q' (all_permutations m) /\ perm_eq p' q')
          ()
          (fun q' -> aux q')
#pop-options

let rec all_permutations_complete (n: nat) (p: permutation n)
  : Lemma (ensures permutation_in_list p (all_permutations n))
          (decreases n)
  = match n with
    | 0 -> completeness_base p
    | _ ->
        let m : nat = n - 1 in
        completeness_step m p (fun q -> all_permutations_complete m q)

(* -------------------------------------------------------------------- *)
(*  Injectivity of insert: recover (p, k) from (insert p k).            *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let insert_top_recovers_k (#n: nat) (p: permutation n) (k: fin (n+1))
  : Lemma ((insert p k).fwd n == k) = ()
#pop-options

let insert_injective_k (#n: nat) (p q: permutation n) (k1 k2: fin (n+1))
  : Lemma (requires perm_eq (insert p k1) (insert q k2)) (ensures k1 == k2)
  = insert_top_recovers_k p k1;
    insert_top_recovers_k q k2;
    perm_eq_elim (insert p k1) (insert q k2) n

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let insert_injective_pointwise (#n: nat) (p q: permutation n)
  (k: fin (n+1)) (i: fin n)
  : Lemma (requires perm_eq (insert p k) (insert q k))
          (ensures p.fwd i == q.fwd i)
  = let i' : fin (n+1) = i in
    perm_eq_elim (insert p k) (insert q k) i';
    let vp = p.fwd i in
    let vq = q.fwd i in
    assert ((insert p k).fwd i' == (if vp < k then (vp <: fin (n+1)) else vp + 1));
    assert ((insert q k).fwd i' == (if vq < k then (vq <: fin (n+1)) else vq + 1))
#pop-options

let insert_injective_p (#n: nat) (p q: permutation n) (k: fin (n+1))
  : Lemma (requires perm_eq (insert p k) (insert q k))
          (ensures perm_eq p q)
  = Classical.forall_intro
      (Classical.move_requires (insert_injective_pointwise p q k));
    let pwd (i: fin n) : Lemma (p.fwd i == q.fwd i)
      = insert_injective_pointwise p q k i in
    perm_eq_intro p q pwd

(* -------------------------------------------------------------------- *)
(*  No-duplicates lemma for all_permutations.                           *)
(* -------------------------------------------------------------------- *)

let rec expand_aux_membership (#n: nat) (p: permutation n) (start: nat{start <= n+1})
  (q: permutation (n+1))
  : Lemma (requires L.memP q (expand_aux p start))
          (ensures exists (k: fin (n+1)). k >= start /\ q == insert p k)
          (decreases (n + 1 - start))
  = if start = n + 1 then ()
    else begin
      let tail = expand_aux p (start + 1) in
      let goal : prop = exists (k: fin (n+1)). k >= start /\ q == insert p k in
      let aux () : Lemma (requires L.memP q tail) (ensures goal)
        = expand_aux_membership p (start + 1) q in
      Classical.move_requires aux ()
    end

let rec expand_aux_distinct (#n: nat) (p: permutation n) (start: nat{start <= n+1})
  : Lemma (ensures all_distinct (expand_aux p start))
          (decreases (n + 1 - start))
  = if start = n + 1 then ()
    else begin
      expand_aux_distinct p (start + 1);
      let head = insert p start in
      let tail = expand_aux p (start + 1) in
      let aux (q: permutation (n+1))
        : Lemma (requires L.memP q tail) (ensures ~(perm_eq head q))
        = expand_aux_membership p (start + 1) q;
          let aux2 (k: fin (n+1))
            : Lemma (requires k >= start + 1 /\ q == insert p k)
                    (ensures ~(perm_eq head q))
            = let bad () : Lemma (requires perm_eq head q) (ensures False)
                = insert_injective_k p p start k in
              Classical.move_requires bad ()
          in
          Classical.forall_intro (Classical.move_requires aux2)
      in
      Classical.forall_intro (Classical.move_requires aux)
    end

(* -------------------------------------------------------------------- *)
(*  Append/concatMap distinctness lemmas.                               *)
(* -------------------------------------------------------------------- *)

let rec append_distinct (#n: nat) (xs ys: list (permutation n))
  : Lemma (requires all_distinct xs /\ all_distinct ys /\
                    (forall (a: permutation n) (b: permutation n).
                       L.memP a xs /\ L.memP b ys ==> ~(perm_eq a b)))
          (ensures all_distinct (L.append xs ys))
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: tl ->
        append_distinct tl ys;
        let aux (p: permutation n)
          : Lemma (requires L.memP p (L.append tl ys)) (ensures ~(perm_eq h p))
          = L.append_memP tl ys p
        in
        Classical.forall_intro (Classical.move_requires aux)

let concatMap_eq (#a #b: Type) (f: a -> list b) (xs: list a)
  : Lemma (ensures L.concatMap f xs ==
                   (match xs with [] -> [] | h :: tl -> L.append (f h) (L.concatMap f tl)))
  = match xs with
    | [] -> ()
    | _ :: _ -> ()

(* Two expand segments from non-equal base permutations are perm_eq-disjoint. *)
#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let cross_segment_distinct_pointwise (#m: nat) (p q: permutation m)
  (a: permutation (m+1)) (b: permutation (m+1))
  : Lemma (requires ~(perm_eq p q) /\
                    L.memP a (expand p) /\ L.memP b (expand q))
          (ensures ~(perm_eq a b))
  = expand_aux_membership p 0 a;
    expand_aux_membership q 0 b;
    let bad () : Lemma (requires perm_eq a b) (ensures False)
      = let ela
            (ka: fin (m+1))
          : Lemma (requires ka >= 0 /\ a == insert p ka) (ensures False)
          = let elb
                (kb: fin (m+1))
              : Lemma (requires kb >= 0 /\ b == insert q kb) (ensures False)
              = insert_injective_k p q ka kb;
                insert_injective_p p q ka
            in
            Classical.forall_intro (Classical.move_requires elb)
        in
        Classical.forall_intro (Classical.move_requires ela)
    in
    Classical.move_requires bad ()
#pop-options

let cross_segment_distinct (#m: nat) (p q: permutation m)
  : Lemma (requires ~(perm_eq p q))
          (ensures forall (a: permutation (m+1)) (b: permutation (m+1)).
                     L.memP a (expand p) /\ L.memP b (expand q) ==> ~(perm_eq a b))
  = let aux (a: permutation (m+1)) (b: permutation (m+1))
      : Lemma (L.memP a (expand p) /\ L.memP b (expand q) ==> ~(perm_eq a b))
      = let body () : Lemma (requires L.memP a (expand p) /\ L.memP b (expand q))
                            (ensures ~(perm_eq a b))
          = cross_segment_distinct_pointwise p q a b in
        Classical.move_requires body ()
    in
    Classical.forall_intro_2 aux

let rec mem_concatMap_inv (#a #b: Type) (f: a -> list b) (xs: list a) (x: b)
  : Lemma (requires L.memP x (L.concatMap f xs))
          (ensures exists (y: a). L.memP y xs /\ L.memP x (f y))
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: tl ->
        L.append_memP (f h) (L.concatMap f tl) x;
        let goal: prop = exists (y: a). L.memP y xs /\ L.memP x (f y) in
        let aux () : Lemma (requires L.memP x (L.concatMap f tl)) (ensures goal)
          = mem_concatMap_inv f tl x in
        Classical.move_requires aux ()

let rec concatMap_distinct_helper (m: nat) (outer: list (permutation m))
  : Lemma (requires all_distinct outer /\
                    (forall (p: permutation m). L.memP p outer ==> all_distinct (expand p)))
          (ensures all_distinct (L.concatMap (fun (p: permutation m) -> expand p) outer))
          (decreases outer)
  = match outer with
    | [] -> ()
    | h :: tl ->
        concatMap_distinct_helper m tl;
        let xs = expand h in
        let ys = L.concatMap (fun (p: permutation m) -> expand p) tl in
        let cross (a: permutation (m+1)) (b: permutation (m+1))
          : Lemma (L.memP a xs /\ L.memP b ys ==> ~(perm_eq a b))
          = let body () : Lemma (requires L.memP a xs /\ L.memP b ys)
                                (ensures ~(perm_eq a b))
              = mem_concatMap_inv (fun (p: permutation m) -> expand p) tl b;
                let pick (q: permutation m)
                  : Lemma (requires L.memP q tl /\ L.memP b (expand q))
                          (ensures ~(perm_eq a b))
                  = assert (~(perm_eq h q));
                    cross_segment_distinct h q;
                    assert (L.memP a (expand h) /\ L.memP b (expand q))
                in
                Classical.forall_intro (Classical.move_requires pick)
            in
            Classical.move_requires body ()
        in
        Classical.forall_intro_2 cross;
        append_distinct xs ys

let rec all_permutations_no_dup (n: nat)
  : Lemma (ensures all_distinct (all_permutations n))
          (decreases n)
  = match n with
    | 0 -> ()
    | _ ->
        let m : nat = n - 1 in
        all_permutations_no_dup m;
        all_permutations_succ_eq m;
        let f : permutation m -> list (permutation (m+1)) = fun p -> expand p in
        let outer = all_permutations m in
        let aux (p: permutation m) : Lemma (all_distinct (f p))
          = expand_aux_distinct p 0
        in
        Classical.forall_intro aux;
        concatMap_distinct_helper m outer