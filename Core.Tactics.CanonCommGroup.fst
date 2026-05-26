module Core.Tactics.CanonCommGroup
(*
   Additive commutative group canonicalization tactic.

   Ported from `..\new\FStar.CAS.Tactics.CanonCommGroup.fst`. The AST
   and normalization machinery (Parts B-E) are TC-agnostic and unchanged.
   Part F (the add_comm_group_to_acg_eq builder + its helpers) is
   retargeted to the new tower's `add_comm_group` class.

   NOTE: the meta-tactic (canon_comm_group) is deferred — see CanonRing
   port for analogous reasoning. `acg_reflect` is available for manual use.
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open FStar.List.Tot.Base

(* ================================================================== *)
(*  Part B: Flat group record (acg_eq)                                *)
(* ================================================================== *)

noeq type acg_eq (a:Type) = {
  eq: equatable a;
  add: a -> a -> a;
  neg: a -> a;
  sub: a -> a -> a;
  zero: a;
  add_associativity: (x:a -> y:a -> z:a -> Lemma (eq.eq (add (add x y) z) (add x (add y z))));
  add_commutativity:  (x:a -> y:a -> Lemma (eq.eq (add x y) (add y x)));
  zero_plus_x: (x:a -> Lemma (eq.eq (add zero x) x));
  add_neg_r: (x:a -> Lemma (eq.eq (add x (neg x)) zero));
  add_cong: (x:a -> y:a -> z:a -> w:a ->
    Lemma (requires eq.eq x z /\ eq.eq y w)
          (ensures eq.eq (add x y) (add z w)));
  neg_cong: (x:a -> y:a ->
    Lemma (requires eq.eq x y)
          (ensures eq.eq (neg x) (neg y)));
  neg_add: (x:a -> y:a -> Lemma (eq.eq (neg (add x y)) (add (neg y) (neg x))));
  double_neg: (x:a -> Lemma (eq.eq (neg (neg x)) x));
  subtraction_definition: (x:a -> y:a -> Lemma (eq.eq (sub x y) (add x (neg y))));
}

(* ================================================================== *)
(*  Part C: Group expression AST and canonical form                   *)
(* ================================================================== *)

let atom : eqtype = nat

type gexp =
  | GZero : gexp
  | GAtom : atom -> gexp
  | GAdd  : gexp -> gexp -> gexp
  | GNeg  : gexp -> gexp
  | GSub  : gexp -> gexp -> gexp

(* Canonical form: sorted list of signed atoms (bool & nat) *)
type signed_atom : eqtype = bool & nat
type canon = list signed_atom

let vmap (a:Type) = list (atom & a) & a

let vmap_lookup (#a:Type) (i: atom) (vm: vmap a) : a =
  match assoc i (fst vm) with
  | Some x -> x
  | None -> snd vm

let sa_denote (#a:Type) (r: acg_eq a) (vm: vmap a) (sa: signed_atom) : a =
  let (sign, i) = sa in
  let v = vmap_lookup i vm in
  if sign then v else r.neg v

let rec canon_denote (#a:Type) (r: acg_eq a) (vm: vmap a) (c: canon) : a =
  match c with
  | [] -> r.zero
  | sa :: rest -> r.add (sa_denote r vm sa) (canon_denote r vm rest)

let rec gdenote (#a:Type) (r: acg_eq a) (vm: vmap a) (e: gexp) : a =
  match e with
  | GZero -> r.zero
  | GAtom i -> vmap_lookup i vm
  | GAdd e1 e2 -> r.add (gdenote r vm e1) (gdenote r vm e2)
  | GNeg e1 -> r.neg (gdenote r vm e1)
  | GSub e1 e2 -> r.sub (gdenote r vm e1) (gdenote r vm e2)

(* ================================================================== *)
(*  Normalization functions                                           *)
(* ================================================================== *)

let negate_all (c: canon) : canon =
  map (fun (s, i) -> (not s, i)) c

let rec expand (e: gexp) : canon =
  match e with
  | GZero -> []
  | GAtom i -> [(true, i)]
  | GAdd e1 e2 -> expand e1 @ expand e2
  | GNeg e1 -> negate_all (expand e1)
  | GSub e1 e2 -> expand e1 @ negate_all (expand e2)

(* Insertion sort on signed atoms: sort by atom index, break ties by sign *)
let sa_leq (sa1 sa2: signed_atom) : bool =
  let (s1, i1) = sa1 in
  let (s2, i2) = sa2 in
  i1 < i2 || (i1 = i2 && (not s1 || s2))

let rec insert_sa (sa: signed_atom) (c: canon) : canon =
  match c with
  | [] -> [sa]
  | sa2 :: rest ->
    if sa_leq sa sa2 then sa :: c
    else sa2 :: insert_sa sa rest

let rec isort (c: canon) : canon =
  match c with
  | [] -> []
  | sa :: rest -> insert_sa sa (isort rest)

(* Cancellation: adjacent atoms with same index but opposite signs cancel *)
let rec cancel (c: canon) : canon =
  match c with
  | (s1, i1) :: (s2, i2) :: rest ->
    if i1 = i2 && s1 <> s2 then cancel rest
    else (s1, i1) :: cancel ((s2, i2) :: rest)
  | _ -> c

let normalize (e: gexp) : canon =
  cancel (isort (expand e))

(* ================================================================== *)
(*  Part D: Correctness proofs                                        *)
(* ================================================================== *)

private let trans (#a:Type) (r: acg_eq a) (x1 x2 x3: a)
  : Lemma (requires r.eq.eq x1 x2 /\ r.eq.eq x2 x3)
          (ensures r.eq.eq x1 x3)
  = r.eq.transitivity x1 x2 x3

private let trans3 (#a:Type) (r: acg_eq a) (x1 x2 x3 x4: a)
  : Lemma (requires r.eq.eq x1 x2 /\ r.eq.eq x2 x3 /\ r.eq.eq x3 x4)
          (ensures r.eq.eq x1 x4)
  = r.eq.transitivity x1 x2 x3; r.eq.transitivity x1 x3 x4

private let trans4 (#a:Type) (r: acg_eq a) (x1 x2 x3 x4 x5: a)
  : Lemma (requires r.eq.eq x1 x2 /\ r.eq.eq x2 x3
                 /\ r.eq.eq x3 x4 /\ r.eq.eq x4 x5)
          (ensures r.eq.eq x1 x5)
  = trans3 r x1 x2 x3 x4; r.eq.transitivity x1 x4 x5

(* Derived: x + 0 = x *)
private let x_plus_zero (#a:Type) (r: acg_eq a) (x: a)
  : Lemma (r.eq.eq (r.add x r.zero) x)
  = r.add_commutativity x r.zero; r.zero_plus_x x;
    trans r (r.add x r.zero) (r.add r.zero x) x

(* Derived: neg zero = zero *)
private let neg_zero (#a:Type) (r: acg_eq a)
  : Lemma (r.eq.eq (r.neg r.zero) r.zero)
  = r.zero_plus_x (r.neg r.zero); r.add_neg_r r.zero;
    r.eq.symmetry (r.add r.zero (r.neg r.zero)) (r.neg r.zero);
    trans r (r.neg r.zero) (r.add r.zero (r.neg r.zero)) r.zero

(* Negating a signed atom *)
private let negate_sa_correct (#a:Type) (r: acg_eq a) (vm: vmap a) (s: bool) (i: nat)
  : Lemma (r.eq.eq (sa_denote r vm (not s, i)) (r.neg (sa_denote r vm (s, i))))
  = if s then r.eq.reflexivity (r.neg (vmap_lookup i vm))
    else (r.double_neg (vmap_lookup i vm);
          r.eq.symmetry (r.neg (r.neg (vmap_lookup i vm))) (vmap_lookup i vm))

(* Append preserves sum *)
private let rec canon_denote_append (#a:Type) (r: acg_eq a) (vm: vmap a) (c1 c2: canon)
  : Lemma (ensures r.eq.eq (canon_denote r vm (c1 @ c2))
                                   (r.add (canon_denote r vm c1) (canon_denote r vm c2)))
          (decreases c1) =
  match c1 with
  | [] ->
    r.zero_plus_x (canon_denote r vm c2);
    r.eq.symmetry (r.add r.zero (canon_denote r vm c2)) (canon_denote r vm c2)
  | sa :: rest ->
    canon_denote_append r vm rest c2;
    let s = sa_denote r vm sa in
    let cr = canon_denote r vm rest in
    let cc = canon_denote r vm c2 in
    r.eq.reflexivity s;
    r.add_cong s (canon_denote r vm (rest @ c2)) s (r.add cr cc);
    r.add_associativity s cr cc;
    r.eq.symmetry (r.add (r.add s cr) cc) (r.add s (r.add cr cc));
    trans r (r.add s (canon_denote r vm (rest @ c2)))
           (r.add s (r.add cr cc))
           (r.add (r.add s cr) cc)

(* Negation distributes over canonical sums *)
private let rec negate_all_correct (#a:Type) (r: acg_eq a) (vm: vmap a) (c: canon)
  : Lemma (ensures r.eq.eq (r.neg (canon_denote r vm c))
                                   (canon_denote r vm (negate_all c)))
          (decreases c) =
  match c with
  | [] -> neg_zero r
  | (s, i) :: rest ->
    let sd = sa_denote r vm (s, i) in
    let cd_rest = canon_denote r vm rest in
    r.neg_add sd cd_rest;
    negate_all_correct r vm rest;
    negate_sa_correct r vm s i;
    r.eq.symmetry (sa_denote r vm (not s, i)) (r.neg sd);
    r.eq.reflexivity (canon_denote r vm (negate_all rest));
    r.add_cong (r.neg cd_rest) (r.neg sd) (canon_denote r vm (negate_all rest)) (sa_denote r vm (not s, i));
    r.add_commutativity (canon_denote r vm (negate_all rest)) (sa_denote r vm (not s, i));
    trans3 r (r.neg (r.add sd cd_rest))
             (r.add (r.neg cd_rest) (r.neg sd))
             (r.add (canon_denote r vm (negate_all rest)) (sa_denote r vm (not s, i)))
             (r.add (sa_denote r vm (not s, i)) (canon_denote r vm (negate_all rest)))

(* Expansion preserves denotation *)
let rec expand_correct (#a:Type) (r: acg_eq a) (vm: vmap a) (e: gexp)
  : Lemma (ensures r.eq.eq (gdenote r vm e) (canon_denote r vm (expand e)))
          (decreases e) =
  match e with
  | GZero -> r.eq.reflexivity r.zero
  | GAtom i ->
    let vi = vmap_lookup i vm in
    x_plus_zero r vi;
    r.eq.symmetry (r.add vi r.zero) vi
  | GAdd e1 e2 ->
    expand_correct r vm e1; expand_correct r vm e2;
    r.add_cong (gdenote r vm e1) (gdenote r vm e2) (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2));
    canon_denote_append r vm (expand e1) (expand e2);
    r.eq.symmetry (canon_denote r vm (expand e1 @ expand e2))
                  (r.add (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2)));
    trans r (r.add (gdenote r vm e1) (gdenote r vm e2))
           (r.add (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2)))
           (canon_denote r vm (expand e1 @ expand e2))
  | GNeg e1 ->
    expand_correct r vm e1;
    r.neg_cong (gdenote r vm e1) (canon_denote r vm (expand e1));
    negate_all_correct r vm (expand e1);
    trans r (r.neg (gdenote r vm e1)) (r.neg (canon_denote r vm (expand e1)))
           (canon_denote r vm (negate_all (expand e1)))
  | GSub e1 e2 ->
    let d1 = gdenote r vm e1 in
    let d2 = gdenote r vm e2 in
    r.subtraction_definition d1 d2;
    expand_correct r vm e1; expand_correct r vm e2;
    r.neg_cong d2 (canon_denote r vm (expand e2));
    negate_all_correct r vm (expand e2);
    trans r (r.neg d2) (r.neg (canon_denote r vm (expand e2)))
           (canon_denote r vm (negate_all (expand e2)));
    r.add_cong d1 (r.neg d2) (canon_denote r vm (expand e1)) (canon_denote r vm (negate_all (expand e2)));
    canon_denote_append r vm (expand e1) (negate_all (expand e2));
    r.eq.symmetry (canon_denote r vm (expand e1 @ negate_all (expand e2)))
                  (r.add (canon_denote r vm (expand e1)) (canon_denote r vm (negate_all (expand e2))));
    trans3 r (r.sub d1 d2)
             (r.add d1 (r.neg d2))
             (r.add (canon_denote r vm (expand e1)) (canon_denote r vm (negate_all (expand e2))))
             (canon_denote r vm (expand e1 @ negate_all (expand e2)))

(* Insertion preserves sum *)
private let rec insert_correct (#a:Type) (r: acg_eq a) (vm: vmap a) (sa: signed_atom) (c: canon)
  : Lemma (ensures r.eq.eq (canon_denote r vm (insert_sa sa c))
                                   (r.add (sa_denote r vm sa) (canon_denote r vm c)))
          (decreases c) =
  match c with
  | [] -> r.eq.reflexivity (r.add (sa_denote r vm sa) r.zero)
  | sa2 :: rest ->
    if sa_leq sa sa2 then
      r.eq.reflexivity (r.add (sa_denote r vm sa) (canon_denote r vm (sa2 :: rest)))
    else begin
      insert_correct r vm sa rest;
      let s = sa_denote r vm sa in
      let s2 = sa_denote r vm sa2 in
      let cr = canon_denote r vm rest in
      r.eq.reflexivity s2;
      r.add_cong s2 (canon_denote r vm (insert_sa sa rest)) s2 (r.add s cr);
      r.add_associativity s2 s cr;
      r.eq.symmetry (r.add (r.add s2 s) cr) (r.add s2 (r.add s cr));
      r.add_commutativity s2 s;
      r.eq.reflexivity cr;
      r.add_cong (r.add s2 s) cr (r.add s s2) cr;
      r.add_associativity s s2 cr;
      trans4 r (r.add s2 (canon_denote r vm (insert_sa sa rest)))
               (r.add s2 (r.add s cr))
               (r.add (r.add s2 s) cr)
               (r.add (r.add s s2) cr)
               (r.add s (r.add s2 cr))
    end

(* Insertion sort preserves sum *)
private let rec isort_correct (#a:Type) (r: acg_eq a) (vm: vmap a) (c: canon)
  : Lemma (ensures r.eq.eq (canon_denote r vm (isort c)) (canon_denote r vm c))
          (decreases c) =
  match c with
  | [] -> r.eq.reflexivity r.zero
  | sa :: rest ->
    isort_correct r vm rest;
    insert_correct r vm sa (isort rest);
    r.eq.reflexivity (sa_denote r vm sa);
    r.add_cong (sa_denote r vm sa) (canon_denote r vm (isort rest)) (sa_denote r vm sa) (canon_denote r vm rest);
    r.eq.symmetry (r.add (sa_denote r vm sa) (canon_denote r vm rest))
                  (r.add (sa_denote r vm sa) (canon_denote r vm (isort rest)));
    trans r (canon_denote r vm (insert_sa sa (isort rest)))
           (r.add (sa_denote r vm sa) (canon_denote r vm (isort rest)))
           (r.add (sa_denote r vm sa) (canon_denote r vm rest))

(* Cancellation preserves denotation *)
private let rec cancel_correct (#a:Type) (r: acg_eq a) (vm: vmap a) (c: canon)
  : Lemma (ensures r.eq.eq (canon_denote r vm c) (canon_denote r vm (cancel c)))
          (decreases c) =
  match c with
  | (s1, i1) :: (s2, i2) :: rest ->
    if i1 = i2 && s1 <> s2 then begin
      let vi = vmap_lookup i1 vm in
      let cr = canon_denote r vm rest in
      let v1 = sa_denote r vm (s1, i1) in
      let v2 = sa_denote r vm (s2, i2) in
      (if s1 then begin
        (* v1 = vi, v2 = neg vi *)
        r.add_neg_r vi
      end else begin
        (* v1 = neg vi, v2 = vi *)
        r.add_commutativity (r.neg vi) vi;
        r.add_neg_r vi;
        trans r (r.add (r.neg vi) vi) (r.add vi (r.neg vi)) r.zero
      end);
      r.add_associativity v1 v2 cr;
      r.eq.symmetry (r.add (r.add v1 v2) cr) (r.add v1 (r.add v2 cr));
      r.eq.reflexivity cr;
      r.add_cong (r.add v1 v2) cr r.zero cr;
      r.zero_plus_x cr;
      trans3 r (r.add v1 (r.add v2 cr))
               (r.add (r.add v1 v2) cr)
               (r.add r.zero cr)
               cr;
      cancel_correct r vm rest;
      trans r (r.add v1 (r.add v2 cr)) cr (canon_denote r vm (cancel rest))
    end else begin
      cancel_correct r vm ((s2, i2) :: rest);
      let v1 = sa_denote r vm (s1, i1) in
      r.eq.reflexivity v1;
      r.add_cong v1 (canon_denote r vm ((s2, i2) :: rest)) v1 (canon_denote r vm (cancel ((s2, i2) :: rest)))
    end
  | _ -> r.eq.reflexivity (canon_denote r vm c)

let normalize_correct (#a:Type) (r: acg_eq a) (vm: vmap a) (e: gexp)
  : Lemma (r.eq.eq (gdenote r vm e) (canon_denote r vm (normalize e))) =
  expand_correct r vm e;
  isort_correct r vm (expand e);
  r.eq.symmetry (canon_denote r vm (isort (expand e))) (canon_denote r vm (expand e));
  cancel_correct r vm (isort (expand e));
  trans3 r (gdenote r vm e) (canon_denote r vm (expand e))
           (canon_denote r vm (isort (expand e)))
           (canon_denote r vm (cancel (isort (expand e))))

(* ================================================================== *)
(*  Part E: Reflection lemma                                          *)
(* ================================================================== *)

let acg_reflect (#a:Type) (r: acg_eq a) (vm: vmap a) (e1 e2: gexp)
  : Lemma (requires normalize e1 == normalize e2)
          (ensures r.eq.eq (gdenote r vm e1) (gdenote r vm e2)) =
  normalize_correct r vm e1;
  normalize_correct r vm e2;
  r.eq.symmetry (gdenote r vm e2) (canon_denote r vm (normalize e2));
  trans r (gdenote r vm e1) (canon_denote r vm (normalize e1)) (gdenote r vm e2)

let acg_reflect_v2 (#a:Type) (r: acg_eq a) (vm: vmap a) (e1 e2: gexp) (a1 a2: a)
    (_ : squash (normalize e1 == normalize e2))
    (_ : squash (a1 == gdenote r vm e1))
    (_ : squash (a2 == gdenote r vm e2))
  : squash (r.eq.eq a1 a2)
  = acg_reflect r vm e1 e2

(* ================================================================== *)
(*  Part F: acg_to_acg_eq constructor                                 *)
(* ================================================================== *)

(* Helper: right-cancel  a+c = b+c => a = b *)

(* ================================================================== *)
(*  Part F: add_comm_group_to_acg_eq constructor (new-tower)           *)
(* ================================================================== *)

(* The new tower's add_comm_group is flat:
     g.acg_eq           : equatable t
     g.add, g.zero, g.neg
     g.add_associativity, g.add_commutativity
     g.add_congruence, g.neg_congruence
     g.add_zero  : (add x 0 = x) /\ (add 0 x = x)
     g.add_negation : (add (neg x) x = 0) /\ (add x (neg x) = 0)
   No nested `acg_acm`, no `acg_sub`/`acg_sub_def`. We synthesize
   subtraction inline as `g.add x (g.neg y)`. *)

module H = Core.Algebra.Helpers

(* Helper: right-cancellation in an additive comm group. *)
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let acg_cancel_right (#t:Type) (g: add_comm_group t) (a b c: t)
  : Lemma (requires g.acg_eq.eq (g.add a c) (g.add b c))
          (ensures  g.acg_eq.eq a b)
  = let nc = g.neg c in
    g.acg_eq.reflexivity nc;
    g.add_congruence (g.add a c) nc (g.add b c) nc;
    g.add_associativity a c nc;
    g.add_associativity b c nc;
    g.add_negation c;
    g.acg_eq.reflexivity a;
    g.acg_eq.reflexivity b;
    g.add_congruence a (g.add c nc) a g.zero;
    g.add_congruence b (g.add c nc) b g.zero;
    g.add_zero a;
    g.add_zero b;
    g.acg_eq.symmetry (g.add a g.zero) a;
    g.acg_eq.symmetry (g.add a (g.add c nc)) (g.add a g.zero);
    g.acg_eq.symmetry (g.add (g.add a c) nc) (g.add a (g.add c nc));
    g.acg_eq.symmetry (g.add b g.zero) b;
    g.acg_eq.symmetry (g.add b (g.add c nc)) (g.add b g.zero);
    g.acg_eq.symmetry (g.add (g.add b c) nc) (g.add b (g.add c nc));
    g.acg_eq.transitivity a (g.add a g.zero) (g.add a (g.add c nc));
    g.acg_eq.transitivity a (g.add a (g.add c nc)) (g.add (g.add a c) nc);
    g.acg_eq.transitivity a (g.add (g.add a c) nc) (g.add (g.add b c) nc);
    g.acg_eq.transitivity a (g.add (g.add b c) nc) (g.add b (g.add c nc));
    g.acg_eq.transitivity a (g.add b (g.add c nc)) (g.add b g.zero);
    g.acg_eq.transitivity a (g.add b g.zero) b
#pop-options

(* Helper: neg (x + y) = neg y + neg x *)
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let acg_neg_add (#t:Type) (g: add_comm_group t) (x y: t)
  : Lemma (g.acg_eq.eq (g.neg (g.add x y)) (g.add (g.neg y) (g.neg x)))
  = let nx = g.neg x in
    let ny = g.neg y in
    let xy = g.add x y in
    let nynx = g.add ny nx in
    let neg_xy = g.neg xy in
    g.add_associativity nx x y;
    g.acg_eq.symmetry (g.add (g.add nx x) y) (g.add nx xy);
    g.add_negation x;
    g.acg_eq.reflexivity y;
    g.add_congruence (g.add nx x) y g.zero y;
    g.add_zero y;
    g.acg_eq.transitivity (g.add nx xy) (g.add (g.add nx x) y) (g.add g.zero y);
    g.acg_eq.transitivity (g.add nx xy) (g.add g.zero y) y;
    g.acg_eq.reflexivity ny;
    g.add_congruence ny (g.add nx xy) ny y;
    g.add_negation y;
    g.acg_eq.transitivity (g.add ny (g.add nx xy)) (g.add ny y) g.zero;
    g.add_associativity ny nx xy;
    g.acg_eq.transitivity (g.add nynx xy) (g.add ny (g.add nx xy)) g.zero;
    g.add_negation xy;
    g.acg_eq.symmetry g.zero (g.add neg_xy xy);
    g.acg_eq.transitivity (g.add nynx xy) g.zero (g.add neg_xy xy);
    acg_cancel_right g nynx neg_xy xy;
    g.acg_eq.symmetry nynx neg_xy
#pop-options

(* Helper: neg (neg x) = x *)
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let acg_double_neg_lem (#t:Type) (g: add_comm_group t) (x: t)
  : Lemma (g.acg_eq.eq (g.neg (g.neg x)) x)
  = let nx = g.neg x in
    let nnx = g.neg nx in
    g.add_negation nx;
    g.add_negation x;
    g.acg_eq.symmetry g.zero (g.add x nx);
    g.acg_eq.transitivity (g.add nnx nx) g.zero (g.add x nx);
    acg_cancel_right g nnx x nx
#pop-options

let add_comm_group_to_acg_eq (#t:Type) {| g: add_comm_group t |} : acg_eq t =
  {
    eq = g.acg_eq;
    add   = g.add;
    neg   = g.neg;
    sub   = (fun x y -> g.add x (g.neg y));
    zero  = g.zero;
    add_associativity = (fun x y z -> g.add_associativity x y z);
    add_commutativity  = (fun x y -> g.add_commutativity x y);
    zero_plus_x = (fun x -> g.add_zero x);
    add_neg_r  = (fun x -> g.add_negation x);
    add_cong   = (fun x y z w -> g.add_congruence x y z w);
    neg_cong   = (fun x y -> g.neg_congruence x y);
    neg_add    = (fun x y -> acg_neg_add g x y);
    double_neg = (fun x -> acg_double_neg_lem g x);
    subtraction_definition = (fun x y -> g.acg_eq.reflexivity (g.add x (g.neg y)));
  }

(* ================================================================== *)
(*  Part G: Meta-tactic canon_comm_group()  (new-tower projector names) *)
(* ================================================================== *)

module T  = FStar.Tactics.V2
module Lst = FStar.List.Tot.Base
module R  = FStar.Reflection.V2
module RT = FStar.Reflection.TermEq.Simple

open FStar.Tactics.V2
open Core.Algebra.Notation

private let rec where_aux_g (n:nat) (x:T.term) (xs:list T.term) : T.Tac (option nat) =
  match xs with
  | [] -> None
  | x'::xs' -> if RT.term_eq x x' then Some n else where_aux_g (Prims.op_Addition n 1) x xs'

private let where_g (x: T.term) (xs: list T.term) : T.Tac (option nat) = where_aux_g 0 x xs

private let fatom_g (t: T.term) (ts: list T.term) (vm: list (atom & T.term) & T.term)
  : T.Tac (gexp & list T.term & (list (atom & T.term) & T.term)) =
  match where_g t ts with
  | Some v -> (GAtom v, ts, vm)
  | None ->
    let vfresh = Lst.length ts in
    let (m, def) = vm in
    (GAtom vfresh, ts @ [t], (m @ [(vfresh, t)], def))

private let rec explicit_args_g (args: list (T.term & T.aqualv)) : list T.term =
  match args with
  | [] -> []
  | (a, R.Q_Explicit) :: rest -> a :: explicit_args_g rest
  | _ :: rest -> explicit_args_g rest

private let rec last_in_list_g (xs: list string) : string =
  match xs with
  | [] -> ""
  | [x] -> x
  | _ :: rest -> last_in_list_g rest

private let head_short_name_g (t: T.term) : T.Tac string =
  match T.inspect t with
  | T.Tv_FVar fv -> last_in_list_g (R.inspect_fv fv)
  | T.Tv_UInst fv _ -> last_in_list_g (R.inspect_fv fv)
  | _ -> ""

private let rec reify_gexp
    (ts: list T.term) (vm: list (atom & T.term) & T.term)
    (t: T.term)
  : T.Tac (gexp & list T.term & (list (atom & T.term) & T.term)) =
  let hd, all_args = T.collect_app t in
  let exps = explicit_args_g all_args in
  let hname = head_short_name_g hd in
  let is_proj_add  = hname = "__proj__Mkadd_comm_group__item__add" in
  let is_proj_neg  = hname = "__proj__Mkadd_comm_group__item__neg" in
  let is_proj_zero = hname = "__proj__Mkadd_comm_group__item__zero" in
  let is_g_add  = hname = "op_Plus" || is_proj_add in
  let is_g_sub  = hname = "op_Subtraction" in
  let is_g_neg  = hname = "op_Minus" || is_proj_neg in
  let is_g_zero = hname = "zero" || is_proj_zero in
  let is_record_proj = is_proj_add || is_proj_neg || is_proj_zero in
  let ops = if is_record_proj && Cons? exps then Lst.tail exps else exps in
  if is_g_zero && Lst.length ops = 0 then (GZero, ts, vm)
  else
  match ops with
  | [t1; t2] ->
    if is_g_add then
      let (e1, ts1, vm1) = reify_gexp ts vm t1 in
      let (e2, ts2, vm2) = reify_gexp ts1 vm1 t2 in
      (GAdd e1 e2, ts2, vm2)
    else if is_g_sub then
      let (e1, ts1, vm1) = reify_gexp ts vm t1 in
      let (e2, ts2, vm2) = reify_gexp ts1 vm1 t2 in
      (GSub e1 e2, ts2, vm2)
    else fatom_g t ts vm
  | [t1] ->
    if is_g_neg then
      let (e1, ts1, vm1) = reify_gexp ts vm t1 in
      (GNeg e1, ts1, vm1)
    else fatom_g t ts vm
  | _ -> fatom_g t ts vm

private let rec quote_gexp (e: gexp) : T.Tac T.term =
  match e with
  | GZero -> `(GZero)
  | GAtom n ->
    let nt = R.pack_ln (R.Tv_Const (R.C_Int n)) in
    `(GAtom (`#nt))
  | GAdd e1 e2 -> `(GAdd (`#(quote_gexp e1)) (`#(quote_gexp e2)))
  | GNeg e1    -> `(GNeg (`#(quote_gexp e1)))
  | GSub e1 e2 -> `(GSub (`#(quote_gexp e1)) (`#(quote_gexp e2)))

private let rec quote_vmap_list_g (m: list (atom & T.term)) : T.Tac T.term =
  match m with
  | [] -> `([])
  | (a, t)::ps ->
    let at = R.pack_ln (R.Tv_Const (R.C_Int a)) in
    `(((`#at), (`#t)) :: (`#(quote_vmap_list_g ps)))

private let quote_vmap_g (vm: list (atom & T.term) & T.term) : T.Tac T.term =
  let (m, def) = vm in
  `((`#(quote_vmap_list_g m), (`#def)))

private let canon_lhs_rhs_acg_with (r_t: T.term) (lhs rhs: T.term) : T.Tac unit =
  let vm0 : list (atom & T.term) & T.term = ([], lhs) in
  let (ge1, ts1, vm1) = reify_gexp [] vm0 lhs in
  let (ge2, _,   vm2) = reify_gexp ts1 vm1 rhs in
  let vm_t  = quote_vmap_g vm2 in
  let ge1_t = quote_gexp ge1 in
  let ge2_t = quote_gexp ge2 in
  T.apply (`(acg_reflect_v2 (`#r_t) (`#vm_t) (`#ge1_t) (`#ge2_t) (`#lhs) (`#rhs)));
  T.norm [delta; iota; zeta; primops]; T.trefl ();
  T.norm [delta; iota; zeta; primops]; T.trefl ();
  T.norm [delta; iota; zeta; primops]; T.trefl ()

let canon_comm_group_with (r_t: T.term) : T.Tac unit =
  T.norm [delta_only [`%op_Plus; `%op_Minus; `%( -- );
                       `%Core.Algebra.eq_of_acg];
          iota; zeta; primops];
  let g = T.cur_goal () in
  let _, args = T.collect_app g in
  let rec last_two_g (args: list (T.term & T.aqualv)) : T.Tac (T.term & T.term) =
    match args with
    | [(inner, _)] ->
      let _, a2 = T.collect_app inner in
      last_two_g a2
    | [(lhs, R.Q_Explicit); (rhs, R.Q_Explicit)] -> (lhs, rhs)
    | _::rest -> last_two_g rest
    | [] -> T.fail "canon_comm_group: could not find lhs/rhs in goal"
  in
  let (lhs, rhs) = last_two_g args in
  canon_lhs_rhs_acg_with r_t lhs rhs

private let rec find_acg_binder (bs: list T.binding) : T.Tac (option (T.binding & T.term)) =
  match bs with
  | [] -> None
  | b :: rest ->
    let bty = b.sort in
    let hd, args = T.collect_app bty in
    let hname = head_short_name_g hd in
    if hname = "add_comm_group" then
      match args with
      | (tt, _) :: _ -> Some (b, tt)
      | _ -> find_acg_binder rest
    else find_acg_binder rest

(* Locate an `add_comm_group t` (or higher class projecting to one) in scope. *)
let canon_comm_group () : T.Tac unit =
  let bs = T.vars_of_env (T.cur_env ()) in
  match find_acg_binder bs with
  | None -> T.fail "canon_comm_group: no `add_comm_group _` instance binder in scope"
  | Some (b, t_term) ->
    let acg_term = T.pack (T.Tv_Var b) in
    let r_t = `(add_comm_group_to_acg_eq #(`#t_term) #(`#acg_term)) in
    canon_comm_group_with r_t
