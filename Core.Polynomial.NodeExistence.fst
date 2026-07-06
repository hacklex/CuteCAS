module Core.Polynomial.NodeExistence

(*
   D1 — NODE EXISTENCE for the Kronecker coefficient bound.

   The Kronecker/Lagrange machinery (Core.Polynomial.KroneckerBound.
   kronecker_coeff_bound) REQUIRES a list of distinct integer nodes on
   which the polynomial F does not vanish:

       all_distinct int_cs /\
       deg g < L.length int_cs /\
       (forall j. j < L.length int_cs ==> poly_eval bigF (L.index int_cs j) <> 0)

   This module SUPPLIES such nodes: for a nonzero integer polynomial and
   any requested count `n`, a valid node list of length `n` exists.

   Route:
     (A) A nonzero F in Z[X] has at most `deg F` distinct integer roots.
         Proved by descent to Q: embed_zq : Z[X] -> Q[X] is a ring hom
         with eval descent (Core.Polynomial.EmbedQ); over the FIELD qq the
         classical root bound Core.Polynomial.RootBound.poly_roots_le_degree
         applies, and deg is preserved (embed_zq_deg).
     (B) From the pool [0; 1; ...; deg F + n] of `deg F + 1 + n` distinct
         integers, split into roots / non-roots.  The root part is a
         distinct list of roots, so by (A) it has length <= deg F; hence
         the non-root part has length >= n + 1.  Take the first `n`.
*)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module RB = Core.Polynomial.RootBound
module UN = Core.Polynomial.Unique

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Polynomial.EmbedQ
open Core.Polynomial.LagrangeBasisBound

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* `nonzero_iff_some_deg` (is_nonzero p <==> deg p >= 0) now lives publicly in
   Core.Polynomial.Unique (UN.nonzero_iff_some_deg). *)

(* ================================================================ *)
(*  (A)  INTEGER ROOT COUNT BOUND.                                  *)
(*    A nonzero integer polynomial has at most `deg` distinct        *)
(*    integer roots.  Roots are supplied as a per-element proof-fn   *)
(*    argument (Q1: no raw forall in the spec).                      *)
(* ================================================================ *)

#push-options "--z3rlimit 40"
let int_root_count_bound
  (bigF: polynomial int) (rs: list int)
  (pf: (c:int) -> Lemma (requires L.memP c rs) (ensures poly_eval bigF c == 0))
  : Lemma (requires deg bigF >= 0 /\ all_distinct rs)
          (ensures L.length rs <= deg bigF)
  = let eg  = embed_zq bigF in
    let qcs = L.map embed_zq_const rs in
    embed_zq_deg bigF;                       (* deg eg == deg bigF >= 0 *)
    UN.nonzero_iff_some_deg eg;               (* is_nonzero eg *)
    let sq : squash (all_distinct #qq #crq qcs) = embed_all_distinct_sq rs in
    (* every node of qcs is a root of eg over Q *)
    let surv (r: qq) : Lemma (requires L.memP r qcs) (ensures poly_eval eg r = zero) =
      H.elim_equatable_laws qq ();
      H.trans_for_calc qq ();
      L.memP_map_elim embed_zq_const r rs;
      eliminate exists (y: int). L.memP y rs /\ embed_zq_const y == r
      returns poly_eval eg r = zero
      with _hy.
      begin
        pf y;                                 (* poly_eval bigF y == 0 *)
        embed_zq_eval bigF y;                 (* poly_eval eg (embed y) = embed (poly_eval bigF y) = embed 0 *)
        embed_zq_const_zero ();               (* embed 0 = crq.cr_r.r_add.zero *)
        assert (crq.cr_r.r_add.zero == zero) by (FStar.Tactics.trefl ())
      end
    in
    RB.all_roots_vanish_intro eg qcs surv;
    RB.poly_roots_le_degree eg qcs;           (* length qcs <= deg eg *)
    L.map_lemma embed_zq_const rs             (* length qcs == length rs *)
#pop-options

(* ================================================================ *)
(*  (B0)  The candidate pool  [m-1; m-2; ...; 0]  of m distinct      *)
(*  integers.                                                        *)
(* ================================================================ *)

private let rec range_list (m: nat) : Tot (list int) (decreases m) =
  if m = 0 then [] else (m - 1) :: range_list (m - 1)

private let rec range_list_length (m: nat)
  : Lemma (ensures L.length (range_list m) == m) (decreases m)
  = if m = 0 then () else range_list_length (m - 1)

private let rec range_list_mem_bound (m: nat) (c: int)
  : Lemma (ensures L.memP c (range_list m) ==> (0 <= c /\ c < m)) (decreases m)
  = if m = 0 then () else range_list_mem_bound (m - 1) c

private let rec range_list_distinct (m: nat)
  : Lemma (ensures all_distinct (range_list m)) (decreases m)
  = if m = 0 then ()
    else begin
      range_list_distinct (m - 1);
      let aux (d:int) : Lemma (L.memP d (range_list (m - 1)) ==> not ((m - 1) = d)) =
        introduce L.memP d (range_list (m - 1)) ==> not ((m - 1) = d)
        with _p. range_list_mem_bound (m - 1) d
      in
      Classical.forall_intro aux
    end

(* ================================================================ *)
(*  (B1)  Split a pool into (non-roots, roots) of bigF.             *)
(* ================================================================ *)

private let rec split_roots (bigF: polynomial int) (pool: list int)
  : Tot (list int & list int) (decreases pool)
  = match pool with
    | [] -> ([], [])
    | c :: cs ->
      let (nr, rt) = split_roots bigF cs in
      if poly_eval bigF c <> 0 then (c :: nr, rt) else (nr, c :: rt)

private let rec split_roots_length (bigF: polynomial int) (pool: list int)
  : Lemma (ensures (let (nr, rt) = split_roots bigF pool in
                    L.length nr ++ L.length rt == L.length pool))
          (decreases pool)
  = match pool with
    | [] -> ()
    | _ :: cs -> split_roots_length bigF cs

private let rec split_roots_sub (bigF: polynomial int) (pool: list int) (c: int)
  : Lemma (ensures (let (nr, rt) = split_roots bigF pool in
                    (L.memP c nr ==> L.memP c pool) /\
                    (L.memP c rt ==> L.memP c pool)))
          (decreases pool)
  = match pool with
    | [] -> ()
    | _ :: cs -> split_roots_sub bigF cs c

private let rec split_roots_rt_root (bigF: polynomial int) (pool: list int) (c: int)
  : Lemma (ensures (let (_, rt) = split_roots bigF pool in
                    L.memP c rt ==> poly_eval bigF c == 0))
          (decreases pool)
  = match pool with
    | [] -> ()
    | _ :: cs -> split_roots_rt_root bigF cs c

private let rec split_roots_nr_nonroot (bigF: polynomial int) (pool: list int) (c: int)
  : Lemma (ensures (let (nr, _) = split_roots bigF pool in
                    L.memP c nr ==> poly_eval bigF c <> 0))
          (decreases pool)
  = match pool with
    | [] -> ()
    | _ :: cs -> split_roots_nr_nonroot bigF cs c

private let rec split_roots_distinct (bigF: polynomial int) (pool: list int)
  : Lemma (requires all_distinct pool)
          (ensures (let (nr, rt) = split_roots bigF pool in
                    all_distinct nr /\ all_distinct rt))
          (decreases pool)
  = match pool with
    | [] -> ()
    | x :: xs ->
      split_roots_distinct bigF xs;
      let (nr', rt') = split_roots bigF xs in
      let aux_nr (d:int) : Lemma (L.memP d nr' ==> not (x = d)) =
        introduce L.memP d nr' ==> not (x = d)
        with _p. split_roots_sub bigF xs d
      in
      let aux_rt (d:int) : Lemma (L.memP d rt' ==> not (x = d)) =
        introduce L.memP d rt' ==> not (x = d)
        with _p. split_roots_sub bigF xs d
      in
      Classical.forall_intro aux_nr;
      Classical.forall_intro aux_rt

(* ================================================================ *)
(*  (B2)  Take the first n elements.                                *)
(* ================================================================ *)

private let rec take (n: nat) (l: list int{n <= L.length l}) : Tot (list int) (decreases n) =
  if n = 0 then []
  else (match l with | x :: xs -> x :: take (n - 1) xs)

private let rec take_length (n: nat) (l: list int{n <= L.length l})
  : Lemma (ensures L.length (take n l) == n) (decreases n)
  = if n = 0 then () else (match l with | _ :: xs -> take_length (n - 1) xs)

private let rec take_mem (n: nat) (l: list int{n <= L.length l}) (c: int)
  : Lemma (ensures L.memP c (take n l) ==> L.memP c l) (decreases n)
  = if n = 0 then () else (match l with | _ :: xs -> take_mem (n - 1) xs c)

private let rec take_distinct (n: nat) (l: list int{n <= L.length l})
  : Lemma (requires all_distinct l)
          (ensures all_distinct (take n l))
          (decreases n)
  = if n = 0 then ()
    else match l with
    | x :: xs ->
      take_distinct (n - 1) xs;
      let aux (d:int) : Lemma (L.memP d (take (n - 1) xs) ==> not (x = d)) =
        introduce L.memP d (take (n - 1) xs) ==> not (x = d)
        with _p. take_mem (n - 1) xs d
      in
      Classical.forall_intro aux

(* ================================================================ *)
(*  MAIN — node existence.                                          *)
(* ================================================================ *)

#push-options "--z3rlimit 40"
let nodes_exist (bigF: polynomial int) (n: nat)
  : Lemma (requires deg bigF >= 0)
          (ensures exists (int_cs: list int).
             L.length int_cs == n /\ all_distinct int_cs /\
             (forall (j:nat). j < n ==>
                poly_eval bigF (L.index int_cs j) <> 0))
  = let d : nat = deg bigF in
    let m : nat = d ++ 1 ++ n in
    let pool = range_list m in
    range_list_length m;                       (* length pool == m *)
    range_list_distinct m;                      (* all_distinct pool *)
    let (nr, rt) = split_roots bigF pool in
    split_roots_length bigF pool;               (* length nr + length rt == m *)
    split_roots_distinct bigF pool;             (* all_distinct nr, rt *)
    let pf (c:int) : Lemma (requires L.memP c rt) (ensures poly_eval bigF c == 0) =
      split_roots_rt_root bigF pool c
    in
    int_root_count_bound bigF rt pf;            (* length rt <= d *)
    assert (L.length nr >= n);
    let int_cs = take n nr in
    take_length n nr;                           (* length int_cs == n *)
    take_distinct n nr;                          (* all_distinct int_cs *)
    let jpf (j:nat)
      : Lemma (j < L.length int_cs ==> poly_eval bigF (L.index int_cs j) <> 0) =
      if j < L.length int_cs then begin
        L.lemma_index_memP int_cs j;            (* memP (index int_cs j) int_cs *)
        take_mem n nr (L.index int_cs j);        (* memP ... nr *)
        split_roots_nr_nonroot bigF pool (L.index int_cs j)
      end
    in
    Classical.forall_intro jpf;
    introduce exists (cs: list int).
       L.length cs == n /\ all_distinct cs /\
       (forall (j:nat). j < n ==>
          poly_eval bigF (L.index cs j) <> 0)
    with int_cs and ()
#pop-options
