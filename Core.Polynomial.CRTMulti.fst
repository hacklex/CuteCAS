module Core.Polynomial.CRTMulti

(* ================================================================ *)
(*  n-ary Chinese Remainder Theorem  (stage A of #29).              *)
(*                                                                   *)
(*  For pairwise-coprime moduli  ms = [m_0; ...; m_{r-1}]  (each     *)
(*  deg m_i >= 1) over a field, with  M := poly_prod ms, the         *)
(*  simultaneous-residue map                                         *)
(*     h  |->  (h mod m_0, ..., h mod m_{r-1})                        *)
(*  is a BIJECTION between residues mod M (polys of deg < deg M) and  *)
(*  tuples of residues (rs_i of deg < deg m_i).                       *)
(*                                                                   *)
(*  This module packages the bijection as the pair                   *)
(*     crt_multi_inj      (uniqueness)                                *)
(*     crt_multi_witness  (existence: builds a witness w that is      *)
(*                         congruent to the given residue tuple rs    *)
(*                         at every modulus, i.e. all_cong_vec)       *)
(*  stated over OPAQUE list-predicates (Q1), ready for the           *)
(*  cardinality-counting consumer (stage C).                         *)
(*                                                                   *)
(*  Generic over any  {| f: field t |}  (Core.Polynomial layer; no   *)
(*  fp / zmod specifics).  Reuses the binary CRT (Core.Polynomial.CRT)*)
(*  and the pairwise-coprime machinery (Core.Polynomial.Irreducible).*)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Tactics.CanonRing
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.GCD
open Core.Polynomial.SquareFree
open Core.Polynomial.Roots
open Core.Polynomial.Irreducible
open Core.Polynomial.CRT

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ================================================================ *)
(*  Abstract ring rearrangements (proved over an abstract            *)
(*  commutative_ring, transported to  polynomial t).                 *)
(* ================================================================ *)

(* (x -- y) + (y -- z) = (x -- z). *)
private let abstract_sub_chain (#p:Type) {| pr: commutative_ring p |} (x y z: p)
  : Lemma ((x -- y) + (y -- z) = (x -- z))
  = assert ((x -- y) + (y -- z) = (x -- z)) by (canon_ring ())

(* index of a cons at 0 (offloaded to a clean context). *)
private let cons_index0 (#a:Type) (x:a) (xs:list a) : Lemma (L.index (x :: xs) 0 == x) = ()

(* index of a cons at a successor position (cons-index shift). *)
private let cons_index_succ (#a:Type) (x:a) (xs:list a) (k:nat)
  : Lemma (requires k < L.length xs)
          (ensures  L.index (x :: xs) (k ++ 1) == L.index xs k) = ()

(* head case of the n-ary congruence, proved in a clean small context:
   for k = 0 the residue map at index k is  m0 | (w -- r0). *)
private let head_index_divides (#t:Type) {| f: field t |}
  (m0: polynomial t) (rest: list (polynomial t))
  (r0: polynomial t) (rrest: list (polynomial t))
  (w: polynomial t) (k:nat)
  : Lemma (requires ~(k >= 1) /\ divides m0 (w -- r0))
          (ensures  divides (L.index (m0 :: rest) k)
                            (w -- (L.index (r0 :: rrest) k)))
  = ()

(* tail case (k = j+1) in a clean small context: chain
     m_{j} | pp | (w -- hr)   and   m_{j} | (hr -- rrest_j)
   into   m_{j} | (w -- rrest_j)   = residue map at index k. *)
private let tail_index_divides (#t:Type) {| f: field t |}
  (m0: polynomial t) (rest: list (polynomial t))
  (r0: polynomial t) (rrest: list (polynomial t))
  (pp w hr: polynomial t) (k j: nat)
  : Lemma (requires k >= 1 /\ k < L.length (m0 :: rest) /\
                    L.length rrest == L.length rest /\
                    k == j ++ 1 /\ j < L.length rest /\ j < L.length rrest /\
                    divides pp (w -- hr) /\
                    divides (L.index rest j) pp /\
                    divides (L.index rest j) (hr -- (L.index rrest j)))
          (ensures  divides (L.index (m0 :: rest) k)
                            (w -- (L.index (r0 :: rrest) k)))
  = H.elim_equatable_laws (polynomial t) ();
    let mk = L.index rest j in
    let rrj = L.index rrest j in
    assert (L.index (m0 :: rest) k == mk);
    assert (L.index (r0 :: rrest) k == rrj);
    divides_trans mk pp (w -- hr);              (* mk | (w -- hr) *)
    divides_add mk (w -- hr) (hr -- rrj);       (* mk | (w--hr)+(hr--rrj) *)
    abstract_sub_chain w hr rrj;                (* (w--hr)+(hr--rrj) = w--rrj *)
    divides_congruence_right mk ((w -- hr) + (hr -- rrj)) (w -- rrj)

(* ================================================================ *)
(*  flat_product (Irreducible/SquareFree layer)  ==  poly_prod       *)
(*  (Roots layer).  Structurally identical folds; bridged once so     *)
(*  the two families of reusable lemmas compose at  M = poly_prod ms. *)
(* ================================================================ *)

let rec flat_eq_prod (#t:Type) {| f: field t |} (ms: list (polynomial t))
  : Lemma (ensures flat_product ms == poly_prod ms) (decreases ms)
  = match ms with
    | []      -> ()
    | _ :: rest -> flat_eq_prod rest

(* each modulus divides the product  M = poly_prod ms. *)
let prod_factor_divides (#t:Type) {| f: field t |}
  (ms: list (polynomial t)) (k:nat)
  : Lemma (requires k < L.length ms)
          (ensures  divides (L.index ms k) (poly_prod ms))
  = flat_product_factor_divides ms k;
    flat_eq_prod ms

(* ================================================================ *)
(*  Opaque list-predicates (Q1: no raw quantifiers in the public      *)
(*  business lemmas).  Each has  _elim  (reveal) and  _intro.         *)
(* ================================================================ *)

(* -- pairwise coprimality: now IR.pairwise_coprime (raw-nat spelling,
   shared with Core.Polynomial.SubsetProd); resolves via the unqualified
   `open Core.Polynomial.Irreducible` above. *)

(* -- each modulus has degree >= 1 (non-units). *)
[@@"opaque_to_smt"]
let all_deg_ge1 (#t:Type) {| f: field t |} (ms: list (polynomial t))
  : prop = forall (k:nat). k < L.length ms ==> deg (L.index ms k) >= 1

let all_deg_ge1_elim (#t:Type) {| f: field t |}
  (ms: list (polynomial t){all_deg_ge1 ms})
  : Lemma (forall (k:nat). k < L.length ms ==> deg (L.index ms k) >= 1)
  = reveal_opaque (`%all_deg_ge1) (all_deg_ge1 ms)

let all_deg_ge1_proof (#t:Type) {| f: field t |} (ms: list (polynomial t))
  = (k:nat{k < L.length ms}) -> Lemma (deg (L.index ms k) >= 1)

let all_deg_ge1_intro (#t:Type) {| f: field t |} (ms: list (polynomial t))
  (proof: all_deg_ge1_proof ms)
  : Lemma (all_deg_ge1 ms)
  = reveal_opaque (`%all_deg_ge1) (all_deg_ge1 ms);
    let aux (k:nat) : Lemma (k < L.length ms ==> deg (L.index ms k) >= 1)
      = if k < L.length ms then proof k else ()
    in
    Classical.forall_intro aux

(* -- w is congruent to rs componentwise: m_k | (w -- rs_k) for all k. *)
[@@"opaque_to_smt"]
let all_cong_vec (#t:Type) {| f: field t |} (ms: list (polynomial t))
  (w: polynomial t) (rs: list (polynomial t))
  : prop = forall (k:nat). k < L.length ms /\ k < L.length rs ==>
             divides (L.index ms k) (w -- (L.index rs k))

let all_cong_vec_elim (#t:Type) {| f: field t |} (ms: list (polynomial t))
  (w: polynomial t) (rs: list (polynomial t){all_cong_vec ms w rs})
  : Lemma (forall (k:nat). k < L.length ms /\ k < L.length rs ==>
             divides (L.index ms k) (w -- (L.index rs k)))
  = reveal_opaque (`%all_cong_vec) (all_cong_vec ms w rs)

let all_cong_vec_proof (#t:Type) {| f: field t |} (ms: list (polynomial t))
  (w: polynomial t) (rs: list (polynomial t))
  = (k:nat{k < L.length ms /\ k < L.length rs})
  -> Lemma (divides (L.index ms k) (w -- (L.index rs k)))

let all_cong_vec_intro (#t:Type) {| f: field t |} (ms: list (polynomial t))
  (w: polynomial t) (rs: list (polynomial t))
  (proof: all_cong_vec_proof ms w rs)
  : Lemma (ensures  all_cong_vec ms w rs)
  = reveal_opaque (`%all_cong_vec) (all_cong_vec ms w rs);
    let aux (k:nat) : Lemma (k < L.length ms /\ k < L.length rs ==>
                              divides (L.index ms k) (w -- (L.index rs k)))
      = if k < L.length ms && k < L.length rs then proof k else ()
    in
    Classical.forall_intro aux

(* ================================================================ *)
(*  Degree of the product is non-negative.                           *)
(* ================================================================ *)

let deg_prod_nonneg (#t:Type) {| f: field t |} (ms: list (polynomial t))
  : Lemma (requires all_deg_ge1 ms)
          (ensures  deg (poly_prod ms) >= 0)
  = all_deg_ge1_elim ms;
    degree_flat_product ms;
    flat_eq_prod ms

(* ================================================================ *)
(*  A2.  n-ary INJECTIVITY.                                           *)
(*    If  a, b  are residues mod M (deg < deg M) and  m_i | (a -- b)  *)
(*    for every i (per-index proof-fn), then  a = b.                  *)
(* ================================================================ *)

let crt_multi_inj (#t:Type) {| f: field t |}
  (ms: list (polynomial t)) (a b: polynomial t)
  (cong_pf: (k:nat{k < L.length ms}) -> Lemma (divides (L.index ms k) (a -- b)))
  : Lemma (requires pairwise_coprime ms /\ all_deg_ge1 ms /\
                    deg a < deg (poly_prod ms) /\ deg b < deg (poly_prod ms))
          (ensures  a = b)
  = pairwise_coprime_elim ms;
    all_deg_ge1_elim ms;
    deg_prod_nonneg ms;
    (* raw-forall hypotheses for pairwise_coprime_divides *)
    Classical.forall_intro cong_pf;
    (* flat_product ms | (a -- b) *)
    pairwise_coprime_divides ms (a -- b);
    flat_eq_prod ms;                              (* poly_prod ms | (a -- b) *)
    let m = poly_prod ms in
    let dm : nat = deg m in
    poly_sub_degree_bound a b dm;                 (* deg (a -- b) < deg m *)
    (* deg (a -- b) < 0 : else divides_degree_le forces deg m <= deg (a--b) < deg m *)
    if deg (a -- b) >= 0 then divides_degree_le m (a -- b);
    degree_none_poly_eq_zero (a -- b);            (* (a -- b) = poly_zero *)
    sub_zero_implies_eq a b

(* ================================================================ *)
(*  A3.  n-ary SURJECTIVITY.                                          *)
(*  Engine: build (by induction, reusing the binary CRT) a witness w  *)
(*  with  m_k | (w -- rs_k)  for all k.  Then reduce mod M.           *)
(* ================================================================ *)

(* Per-index congruence for the assembled witness, in a clean isolated
   context (the two cases dispatch to head_/tail_index_divides).  Kept a
   top-level lemma — not an inline lambda inside crt_multi_witness — so its
   obligations verify on their own small VC rather than rolling into the
   witness's aggregate post-condition.  The IH (rest_i | hr -- rrest_i) is
   taken as a per-index PROOF-FN rather than a raw forall in requires: the
   tail case needs it at a single index j, so a forall precondition would
   force Z3 into unpatterned forall-to-forall matching inside the caller's
   aggregate query (the "incomplete quantifiers" failure). *)
#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
private let witness_cong_at (#t:Type) {| f: field t |}
  (m0: polynomial t) (rest: list (polynomial t))
  (r0: polynomial t) (rrest: list (polynomial t))
  (pp w hr: polynomial t) (k: nat)
  (ih_pf: (i:nat{i < L.length rest /\ i < L.length rrest})
          -> Lemma (divides (L.index rest i) (hr -- (L.index rrest i))))
  : Lemma (requires
             k < L.length (m0 :: rest) /\ k < L.length (r0 :: rrest) /\
             L.length rrest == L.length rest /\
             pp == poly_prod rest /\
             divides m0 (w -- r0) /\ divides pp (w -- hr))
          (ensures  divides (L.index (m0 :: rest) k)
                            (w -- (L.index (r0 :: rrest) k)))
  = if k >= 1 then begin
      let j : n:nat{n < L.length rest /\ n < L.length rrest} = k - 1 in
      prod_factor_divides rest j;                 (* index rest j | poly_prod rest = pp *)
      ih_pf j;                                     (* index rest j | hr -- index rrest j *)
      tail_index_divides m0 rest r0 rrest pp w hr k j
    end
    else head_index_divides m0 rest r0 rrest w k
#pop-options

(* Assemble the full congruence vector from the head/tail facts.  A
   top-level lemma (not an inline body in crt_multi_witness) so that the
   proof-fn passed to all_cong_vec_intro discharges witness_cong_at from
   this lemma's stable PRECONDITIONS — transient Lemma-facts in the caller
   are not visible inside a lambda value, but preconditions are.  The IH is
   threaded as a proof-fn (see witness_cong_at). *)
#push-options "--z3rlimit 10 --fuel 2 --ifuel 2"
private let assemble_cong_vec (#t:Type) {| f: field t |}
  (ms: list (polynomial t)) (m0: polynomial t) (rest: list (polynomial t))
  (rs: list (polynomial t)) (r0: polynomial t) (rrest: list (polynomial t))
  (pp w hr: polynomial t)
  (ih_pf: (i:nat{i < L.length rest /\ i < L.length rrest})
          -> Lemma (divides (L.index rest i) (hr -- (L.index rrest i))))
  : Lemma (requires
             ms == m0 :: rest /\ rs == r0 :: rrest /\
             L.length rrest == L.length rest /\
             pp == poly_prod rest /\
             divides m0 (w -- r0) /\ divides pp (w -- hr))
          (ensures  all_cong_vec ms w rs)
  = let pf (k:nat{k < L.length (m0 :: rest) /\ k < L.length (r0 :: rrest)})
      : Lemma (divides (L.index (m0 :: rest) k) (w -- (L.index (r0 :: rrest) k)))
      = witness_cong_at m0 rest r0 rrest pp w hr k ih_pf
    in
    all_cong_vec_intro (m0 :: rest) w (r0 :: rrest) pf
    (* ms == m0::rest, rs == r0::rrest close the opaque-predicate congruence
       in this clean context (the caller's aggregate query cannot). *)
#pop-options

(* Opaque wrapper around the (unfold) binary crt_witness.  Returning it as
   an abstract symbol — rather than letting `crt_witness` unfold to its full
   Bezout expression — keeps the assembled witness `w` a single term in both
   the assemble_cong_vec ensures and the function post-condition, so the
   opaque all_cong_vec fact matches the goal syntactically (the unfolded
   giant term does not, causing the "incomplete quantifiers" saturation). *)
private let crt_witness_sym (#t:Type) {| f: field t |} (m0 pp r0 hr: polynomial t)
  : Pure (polynomial t)
         (requires deg m0 >= 0 /\ coprime m0 pp)
         (ensures  fun w -> w == crt_witness m0 pp r0 hr)
  = crt_witness m0 pp r0 hr

(* -- shift the pairwise-coprime / degree hypotheses from  m0::rest  down to
   rest.  Each proof-fn re-derives from the STABLE opaque precondition (a
   lambda value cannot see transient Lemma-facts, but preconditions persist),
   so the _elim call lives inside the lambda. *)

private let tail_pairwise_coprime (#t:Type) {| f: field t |}
  (m0: polynomial t) (rest: list (polynomial t))
  : Lemma (requires pairwise_coprime (m0 :: rest))
          (ensures  pairwise_coprime rest)
  = let cpf (i:nat{i < L.length rest}) (j:nat{j < L.length rest /\ j <> i})
      : Lemma (coprime (L.index rest i) (L.index rest j))
      = pairwise_coprime_elim (m0 :: rest);
        cons_index_succ m0 rest i; cons_index_succ m0 rest j
    in
    pairwise_coprime_intro rest cpf

private let tail_all_deg_ge1 (#t:Type) {| f: field t |}
  (m0: polynomial t) (rest: list (polynomial t))
  : Lemma (requires all_deg_ge1 (m0 :: rest))
          (ensures  all_deg_ge1 rest)
  = let dpf (k:nat{k < L.length rest}) : Lemma (deg (L.index rest k) >= 1)
      = all_deg_ge1_elim (m0 :: rest); cons_index_succ m0 rest k
    in
    all_deg_ge1_intro rest dpf

(* head modulus is coprime to the product of the tail. *)
private let head_coprime_prod (#t:Type) {| f: field t |}
  (m0: polynomial t) (rest: list (polynomial t))
  : Lemma (requires pairwise_coprime (m0 :: rest) /\ deg m0 >= 0)
          (ensures  coprime m0 (poly_prod rest))
  = let cwa_pf (k:nat{k < L.length rest}) : Lemma (coprime m0 (L.index rest k))
      = pairwise_coprime_elim (m0 :: rest);
        cons_index0 m0 rest; cons_index_succ m0 rest k
    in
    coprime_with_all_intro m0 rest cwa_pf;
    coprime_to_prod m0 rest

(* head modulus has degree >= 0 (from all_deg_ge1 at index 0). *)
private let head_deg_nonneg (#t:Type) {| f: field t |}
  (m0: polynomial t) (rest: list (polynomial t))
  : Lemma (requires all_deg_ge1 (m0 :: rest))
          (ensures  deg m0 >= 0)
  = all_deg_ge1_elim (m0 :: rest); cons_index0 m0 rest

(* ---------------------------------------------------------------- *)
(*  The witness VALUE, computed by structural recursion on the       *)
(*  moduli, reusing the binary crt_witness at each step.  The        *)
(*  correctness (all_cong_vec) is proved SEPARATELY by cmw_cong: a    *)
(*  value function with trivial post + a Lemma over its result        *)
(*  sidesteps the guard-free continuation encoding that a recursive   *)
(*  Pure function with a rich post-condition otherwise generates.     *)
(*  Preconditions travel as OPAQUE predicates (not proof-fn lambdas)  *)
(*  so the value has no lambda arguments and matches across the       *)
(*  recursive call. *)
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
private let rec cmw_val (#t:Type) {| f: field t |} (ms rs: list (polynomial t))
  : Pure (polynomial t)
         (requires L.length rs == L.length ms /\
                   pairwise_coprime ms /\ all_deg_ge1 ms)
         (ensures  fun _ -> True)
         (decreases ms)
  = match ms with
    | [] -> poly_zero #t
    | m0 :: rest ->
      match rs with
      | [] -> poly_zero #t                        (* dead: len rs == len ms *)
      | r0 :: rrest ->
        let pp = poly_prod rest in
        head_deg_nonneg m0 rest;                  (* deg m0 >= 0 *)
        head_coprime_prod m0 rest;                (* coprime m0 pp *)
        tail_pairwise_coprime m0 rest;            (* pairwise_coprime rest *)
        tail_all_deg_ge1 m0 rest;                 (* all_deg_ge1 rest *)
        let hr = cmw_val rest rrest in
        crt_witness_sym m0 pp r0 hr
#pop-options

(* Correctness of cmw_val: the residue map hits it at every index.  The
   fuel-2 unfold of cmw_val one step gives  cmw_val ms rs == w  in the cons
   case, bridging assemble_cong_vec's ensures to the goal. *)
#push-options "--z3rlimit 10 --fuel 2 --ifuel 1"
private let rec cmw_cong (#t:Type) {| f: field t |} (ms rs: list (polynomial t))
  : Lemma (requires L.length rs == L.length ms /\
                    pairwise_coprime ms /\ all_deg_ge1 ms)
          (ensures  all_cong_vec ms (cmw_val ms rs) rs)
          (decreases ms)
  = match ms with
    | [] -> all_cong_vec_intro ms (cmw_val ms rs) rs (fun _ -> ())
    | m0 :: rest ->
      match rs with
      | [] -> ()                                  (* dead: len rs == len ms *)
      | r0 :: rrest ->
        let pp = poly_prod rest in
        head_deg_nonneg m0 rest;                  (* deg m0 >= 0 *)
        head_coprime_prod m0 rest;                (* coprime m0 pp *)
        tail_pairwise_coprime m0 rest;            (* pairwise_coprime rest *)
        tail_all_deg_ge1 m0 rest;                 (* all_deg_ge1 rest *)
        deg_prod_nonneg rest;                     (* deg pp >= 0 *)
        cmw_cong rest rrest;                      (* all_cong_vec rest hr rrest *)
        let hr = cmw_val rest rrest in
        let w = crt_witness_sym m0 pp r0 hr in    (* == cmw_val ms rs (fuel unfold) *)
        crt_surj_f m0 pp r0 hr;                   (* m0 | (w -- r0) *)
        crt_surj_g m0 pp r0 hr;                   (* pp | (w -- hr) *)
        let ih_pf (i:nat{i < L.length rest /\ i < L.length rrest})
          : Lemma (divides (L.index rest i) (hr -- (L.index rrest i)))
          = all_cong_vec_elim rest hr rrest
        in
        assemble_cong_vec ms m0 rest rs r0 rrest pp w hr ih_pf
#pop-options

(* Public engine: assemble the pairwise-coprime / degree proof-fns into the
   opaque predicates, then hand off to the value + correctness pair. *)
let crt_multi_witness (#t:Type) {| f: field t |}
  (ms rs: list (polynomial t))
  (cop_pf: (i:nat{i < L.length ms}) -> (j:nat{j < L.length ms /\ j <> i})
           -> Lemma (coprime (L.index ms i) (L.index ms j)))
  (deg_pf: (k:nat{k < L.length ms}) -> Lemma (deg (L.index ms k) >= 1))
  : Pure (polynomial t)
         (requires L.length rs == L.length ms)
         (ensures  fun w -> all_cong_vec ms w rs)
  = pairwise_coprime_intro ms cop_pf;
    all_deg_ge1_intro ms deg_pf;
    cmw_cong ms rs;
    cmw_val ms rs
