module Core.Tactics.CanonRing
(*
   Ring canonicalization tactic for the CuteCAS diamond-free `core/` tower.

   Provides:
   1. A flat cr_eq record bundling ring operations + axioms.
   2. A full ring normalizer: distributes, flattens, sorts, reflects.
   3. ring_reflect: if normalized forms match, the originals are equivalent.
   4. canon_ring (): a tactic that normalizes commutative-ring goals.

   This is a port from `..\new\FStar.CAS.Tactics.CanonRing.fst`. The flat
   cr_eq record and the AST/normalization machinery are unchanged. Only
   the TC-touching parts (helper lemmas and the comm_ring_to_cr_eq
   builder) have been retargeted to `Core.Algebra`'s class structure.
*)

module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open FStar.List.Tot.Base

(* ================================================================== *)
(*  Part B: Flat ring record (cr_eq)                                  *)
(* ================================================================== *)

noeq type cr_eq (a:Type) = {
  eq: equatable a;
  add: a -> a -> a;
  mul: a -> a -> a;
  neg: a -> a;
  sub: a -> a -> a;
  zero: a;
  one: a;
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
  mul_associativity: (x:a -> y:a -> z:a -> Lemma (eq.eq (mul (mul x y) z) (mul x (mul y z))));
  mul_commutativity:  (x:a -> y:a -> Lemma (eq.eq (mul x y) (mul y x)));
  one_mul_x: (x:a -> Lemma (eq.eq (mul one x) x));
  mul_cong: (x:a -> y:a -> z:a -> w:a ->
    Lemma (requires eq.eq x z /\ eq.eq y w)
          (ensures eq.eq (mul x y) (mul z w)));
  left_distributivity: (x:a -> y:a -> z:a -> Lemma (eq.eq (mul x (add y z)) (add (mul x y) (mul x z))));
  zero_mul_l: (x:a -> Lemma (eq.eq (mul zero x) zero));
  neg_mul_l: (x:a -> y:a -> Lemma (eq.eq (mul (neg x) y) (neg (mul x y))));
  neg_add: (x:a -> y:a -> Lemma (eq.eq (neg (add x y)) (add (neg y) (neg x))));
  double_neg: (x:a -> Lemma (eq.eq (neg (neg x)) x));
  subtraction_definition: (x:a -> y:a -> Lemma (eq.eq (sub x y) (add x (neg y))));
}

(* ================================================================== *)
(*  Part C: Ring expression AST and canonical form                    *)
(* ================================================================== *)

let atom : eqtype = nat

type rexp =
  | RZero  : rexp
  | ROne   : rexp
  | RAtom  : atom -> rexp
  | RAdd   : rexp -> rexp -> rexp
  | RMul   : rexp -> rexp -> rexp
  | RNeg   : rexp -> rexp
  | RSub   : rexp -> rexp -> rexp

type monom = list atom
type signed_monom : eqtype = bool & monom
type canon = list signed_monom

let vmap (a:Type) = list (atom & a) & a

let vmap_lookup (#a:Type) (i: atom) (vm: vmap a) : a =
  match assoc i (fst vm) with
  | Some x -> x
  | None -> snd vm

(* Uniform denotation: no singleton shortcuts, for clean induction *)
let rec monom_denote (#a:Type) (r: cr_eq a) (vm: vmap a) (m: monom) : a =
  match m with
  | [] -> r.one
  | i :: rest -> r.mul (vmap_lookup i vm) (monom_denote r vm rest)

let sm_denote (#a:Type) (r: cr_eq a) (vm: vmap a) (sm: signed_monom) : a =
  let (sign, m) = sm in
  let v = monom_denote r vm m in
  if sign then v else r.neg v

let rec canon_denote (#a:Type) (r: cr_eq a) (vm: vmap a) (c: canon) : a =
  match c with
  | [] -> r.zero
  | sm :: rest -> r.add (sm_denote r vm sm) (canon_denote r vm rest)

let rec rdenote (#a:Type) (r: cr_eq a) (vm: vmap a) (e: rexp) : a =
  match e with
  | RZero -> r.zero
  | ROne -> r.one
  | RAtom i -> vmap_lookup i vm
  | RAdd e1 e2 -> r.add (rdenote r vm e1) (rdenote r vm e2)
  | RMul e1 e2 -> r.mul (rdenote r vm e1) (rdenote r vm e2)
  | RNeg e1 -> r.neg (rdenote r vm e1)
  | RSub e1 e2 -> r.sub (rdenote r vm e1) (rdenote r vm e2)

(* ================================================================== *)
(*  Normalization functions                                           *)
(* ================================================================== *)

private let ( +% ) (x y: nat) : nat = Prims.op_Addition x y

let rec monom_merge (m1 m2: monom) : Tot monom (decreases (length m1 +% length m2)) =
  match m1, m2 with
  | [], _ -> m2
  | _, [] -> m1
  | i :: rest1, j :: rest2 ->
    if i <= j then i :: monom_merge rest1 m2
    else j :: monom_merge m1 rest2

let sign_mul (s1 s2: bool) : bool = (s1 = s2)

let sm_mul (sm1 sm2: signed_monom) : signed_monom =
  let (s1, m1) = sm1 in
  let (s2, m2) = sm2 in
  (sign_mul s1 s2, monom_merge m1 m2)

let negate_all (c: canon) : canon =
  map (fun (s, m) -> (not s, m)) c

let rec cross_one (sm: signed_monom) (c: canon) : canon =
  match c with
  | [] -> []
  | sm2 :: rest -> sm_mul sm sm2 :: cross_one sm rest

let rec cross (c1 c2: canon) : canon =
  match c1 with
  | [] -> []
  | sm :: rest -> cross_one sm c2 @ cross rest c2

let rec expand (e: rexp) : canon =
  match e with
  | RZero -> []
  | ROne -> [(true, [])]
  | RAtom i -> [(true, [i])]
  | RAdd e1 e2 -> expand e1 @ expand e2
  | RNeg e1 -> negate_all (expand e1)
  | RMul e1 e2 -> cross (expand e1) (expand e2)
  | RSub e1 e2 -> expand e1 @ negate_all (expand e2)

(* Insertion sort on signed monomials *)
let rec monom_lt (m1 m2: monom) : bool =
  match m1, m2 with
  | [], [] -> false
  | [], _ -> true
  | _, [] -> false
  | i :: rest1, j :: rest2 ->
    if i < j then true
    else if i = j then monom_lt rest1 rest2
    else false

let sm_leq (sm1 sm2: signed_monom) : bool =
  let (s1, m1) = sm1 in
  let (s2, m2) = sm2 in
  monom_lt m1 m2 || (m1 = m2 && (not s1 || s2))

let rec insert_sm (sm: signed_monom) (c: canon) : canon =
  match c with
  | [] -> [sm]
  | sm2 :: rest ->
    if sm_leq sm sm2 then sm :: c
    else sm2 :: insert_sm sm rest

let rec isort (c: canon) : canon =
  match c with
  | [] -> []
  | sm :: rest -> insert_sm sm (isort rest)

(* Cancellation: after sorting, adjacent monomials with same atoms but
   opposite signs cancel to zero. *)
let rec cancel (c: canon) : canon =
  match c with
  | (s1, m1) :: (s2, m2) :: rest ->
    if m1 = m2 && s1 <> s2 then cancel rest
    else (s1, m1) :: cancel ((s2, m2) :: rest)
  | _ -> c

let normalize (e: rexp) : canon =
  cancel (isort (expand e))

(* ================================================================== *)
(*  Part D: Correctness proofs                                        *)
(* ================================================================== *)

(* Transitivity chain helpers *)
private let trans (#a:Type) (r: cr_eq a) (x1 x2 x3: a)
  : Lemma (requires r.eq.eq x1 x2 /\ r.eq.eq x2 x3)
          (ensures r.eq.eq x1 x3)
  = r.eq.transitivity x1 x2 x3

private let trans3 (#a:Type) (r: cr_eq a) (x1 x2 x3 x4: a)
  : Lemma (requires r.eq.eq x1 x2 /\ r.eq.eq x2 x3 /\ r.eq.eq x3 x4)
          (ensures r.eq.eq x1 x4)
  = r.eq.transitivity x1 x2 x3; r.eq.transitivity x1 x3 x4

private let trans4 (#a:Type) (r: cr_eq a) (x1 x2 x3 x4 x5: a)
  : Lemma (requires r.eq.eq x1 x2 /\ r.eq.eq x2 x3
                 /\ r.eq.eq x3 x4 /\ r.eq.eq x4 x5)
          (ensures r.eq.eq x1 x5)
  = trans3 r x1 x2 x3 x4; r.eq.transitivity x1 x4 x5

(* Derived ring lemmas *)
private let x_plus_zero (#a:Type) (r: cr_eq a) (x: a)
  : Lemma (r.eq.eq (r.add x r.zero) x)
  = r.add_commutativity x r.zero; r.zero_plus_x x;
    trans r (r.add x r.zero) (r.add r.zero x) x

private let x_mul_one (#a:Type) (r: cr_eq a) (x: a)
  : Lemma (r.eq.eq (r.mul x r.one) x)
  = r.mul_commutativity x r.one; r.one_mul_x x;
    trans r (r.mul x r.one) (r.mul r.one x) x

private let mul_zero_r (#a:Type) (r: cr_eq a) (x: a)
  : Lemma (r.eq.eq (r.mul x r.zero) r.zero)
  = r.mul_commutativity x r.zero; r.zero_mul_l x;
    trans r (r.mul x r.zero) (r.mul r.zero x) r.zero

private let neg_zero (#a:Type) (r: cr_eq a)
  : Lemma (r.eq.eq (r.neg r.zero) r.zero)
  = r.zero_plus_x (r.neg r.zero); r.add_neg_r r.zero;
    r.eq.symmetry (r.add r.zero (r.neg r.zero)) (r.neg r.zero);
    trans r (r.neg r.zero) (r.add r.zero (r.neg r.zero)) r.zero

private let neg_mul_r (#a:Type) (r: cr_eq a) (x y: a)
  : Lemma (r.eq.eq (r.mul x (r.neg y)) (r.neg (r.mul x y)))
  = r.mul_commutativity x (r.neg y); r.neg_mul_l y x;
    r.mul_commutativity y x; r.neg_cong (r.mul y x) (r.mul x y);
    trans3 r (r.mul x (r.neg y)) (r.mul (r.neg y) x)
             (r.neg (r.mul y x)) (r.neg (r.mul x y))

private let right_distributivity (#a:Type) (r: cr_eq a) (x y z: a)
  : Lemma (r.eq.eq (r.mul (r.add x y) z) (r.add (r.mul x z) (r.mul y z)))
  = r.mul_commutativity (r.add x y) z; r.left_distributivity z x y;
    r.mul_commutativity z x; r.mul_commutativity z y;
    r.add_cong (r.mul z x) (r.mul z y) (r.mul x z) (r.mul y z);
    trans3 r (r.mul (r.add x y) z) (r.mul z (r.add x y))
             (r.add (r.mul z x) (r.mul z y)) (r.add (r.mul x z) (r.mul y z))

(* Negating a signed monomial *)
private let negate_sm_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (s: bool) (m: monom)
  : Lemma (r.eq.eq (sm_denote r vm (not s, m)) (r.neg (sm_denote r vm (s, m))))
  = if s then r.eq.reflexivity (r.neg (monom_denote r vm m))
    else (r.double_neg (monom_denote r vm m);
          r.eq.symmetry (r.neg (r.neg (monom_denote r vm m))) (monom_denote r vm m))

(* Append preserves sum *)
private let rec canon_denote_append (#a:Type) (r: cr_eq a) (vm: vmap a) (c1 c2: canon)
  : Lemma (ensures r.eq.eq (canon_denote r vm (c1 @ c2))
                                   (r.add (canon_denote r vm c1) (canon_denote r vm c2)))
          (decreases c1) =
  match c1 with
  | [] ->
    r.zero_plus_x (canon_denote r vm c2);
    r.eq.symmetry (r.add r.zero (canon_denote r vm c2)) (canon_denote r vm c2)
  | sm :: rest ->
    canon_denote_append r vm rest c2;
    let s = sm_denote r vm sm in
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
private let rec negate_all_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (c: canon)
  : Lemma (ensures r.eq.eq (r.neg (canon_denote r vm c))
                                   (canon_denote r vm (negate_all c)))
          (decreases c) =
  match c with
  | [] -> neg_zero r
  | (s, m) :: rest ->
    let sd_sm = sm_denote r vm (s, m) in
    let cd_rest = canon_denote r vm rest in
    r.neg_add sd_sm cd_rest;
    negate_all_correct r vm rest;
    negate_sm_correct r vm s m;
    r.eq.symmetry (sm_denote r vm (not s, m)) (r.neg sd_sm);
    r.eq.reflexivity (canon_denote r vm (negate_all rest));
    r.add_cong (r.neg cd_rest) (r.neg sd_sm) (canon_denote r vm (negate_all rest)) (sm_denote r vm (not s, m));
    r.add_commutativity (canon_denote r vm (negate_all rest)) (sm_denote r vm (not s, m));
    trans3 r (r.neg (r.add sd_sm cd_rest))
             (r.add (r.neg cd_rest) (r.neg sd_sm))
             (r.add (canon_denote r vm (negate_all rest)) (sm_denote r vm (not s, m)))
             (r.add (sm_denote r vm (not s, m)) (canon_denote r vm (negate_all rest)))

(* Sorted merge preserves product *)
private let rec monom_merge_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (m1 m2: monom)
  : Lemma (ensures r.eq.eq (r.mul (monom_denote r vm m1) (monom_denote r vm m2))
                                   (monom_denote r vm (monom_merge m1 m2)))
          (decreases (length m1 +% length m2)) =
  match m1, m2 with
  | [], _ -> r.one_mul_x (monom_denote r vm m2)
  | _, [] -> x_mul_one r (monom_denote r vm m1)
  | i :: rest1, j :: rest2 ->
    let vi = vmap_lookup i vm in
    let vj = vmap_lookup j vm in
    let mr1 = monom_denote r vm rest1 in
    let mr2 = monom_denote r vm rest2 in
    let mm1 = monom_denote r vm m1 in
    let mm2 = monom_denote r vm m2 in
    if i <= j then begin
      monom_merge_correct r vm rest1 m2;
      r.mul_associativity vi mr1 mm2;
      r.eq.reflexivity vi;
      r.mul_cong vi (r.mul mr1 mm2) vi (monom_denote r vm (monom_merge rest1 m2));
      trans r (r.mul mm1 mm2) (r.mul vi (r.mul mr1 mm2))
             (r.mul vi (monom_denote r vm (monom_merge rest1 m2)))
    end else begin
      monom_merge_correct r vm m1 rest2;
      r.mul_associativity mm1 vj mr2;
      r.eq.symmetry (r.mul (r.mul mm1 vj) mr2) (r.mul mm1 (r.mul vj mr2));
      r.mul_commutativity mm1 vj;
      r.eq.reflexivity mr2;
      r.mul_cong (r.mul mm1 vj) mr2 (r.mul vj mm1) mr2;
      r.mul_associativity vj mm1 mr2;
      r.eq.reflexivity vj;
      r.mul_cong vj (r.mul mm1 mr2) vj (monom_denote r vm (monom_merge m1 rest2));
      trans4 r (r.mul mm1 mm2)
               (r.mul (r.mul mm1 vj) mr2)
               (r.mul (r.mul vj mm1) mr2)
               (r.mul vj (r.mul mm1 mr2))
               (r.mul vj (monom_denote r vm (monom_merge m1 rest2)))
    end

(* Signed monomial multiplication *)
private let sm_mul_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (sm1 sm2: signed_monom)
  : Lemma (r.eq.eq (r.mul (sm_denote r vm sm1) (sm_denote r vm sm2))
                           (sm_denote r vm (sm_mul sm1 sm2))) =
  let (s1, m1) = sm1 in
  let (s2, m2) = sm2 in
  let md1 = monom_denote r vm m1 in
  let md2 = monom_denote r vm m2 in
  let mdm = monom_denote r vm (monom_merge m1 m2) in
  monom_merge_correct r vm m1 m2;
  match s1, s2 with
  | true, true -> ()
  | true, false ->
    neg_mul_r r md1 md2;
    r.neg_cong (r.mul md1 md2) mdm;
    trans r (r.mul md1 (r.neg md2)) (r.neg (r.mul md1 md2)) (r.neg mdm)
  | false, true ->
    r.neg_mul_l md1 md2;
    r.neg_cong (r.mul md1 md2) mdm;
    trans r (r.mul (r.neg md1) md2) (r.neg (r.mul md1 md2)) (r.neg mdm)
  | false, false ->
    r.neg_mul_l md1 (r.neg md2);
    neg_mul_r r md1 md2;
    r.neg_cong (r.mul md1 (r.neg md2)) (r.neg (r.mul md1 md2));
    r.double_neg (r.mul md1 md2);
    trans4 r (r.mul (r.neg md1) (r.neg md2))
             (r.neg (r.mul md1 (r.neg md2)))
             (r.neg (r.neg (r.mul md1 md2)))
             (r.mul md1 md2)
             mdm

(* Cross product with one element *)
private let rec cross_one_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (sm: signed_monom) (c: canon)
  : Lemma (ensures r.eq.eq (r.mul (sm_denote r vm sm) (canon_denote r vm c))
                                   (canon_denote r vm (cross_one sm c)))
          (decreases c) =
  match c with
  | [] -> mul_zero_r r (sm_denote r vm sm)
  | sm2 :: rest ->
    let sd = sm_denote r vm sm in
    let sd2 = sm_denote r vm sm2 in
    let cr = canon_denote r vm rest in
    r.left_distributivity sd sd2 cr;
    sm_mul_correct r vm sm sm2;
    cross_one_correct r vm sm rest;
    r.add_cong (r.mul sd sd2) (r.mul sd cr) (sm_denote r vm (sm_mul sm sm2)) (canon_denote r vm (cross_one sm rest));
    trans r (r.mul sd (r.add sd2 cr))
           (r.add (r.mul sd sd2) (r.mul sd cr))
           (r.add (sm_denote r vm (sm_mul sm sm2)) (canon_denote r vm (cross_one sm rest)))

(* Full cross product *)
private let rec cross_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (c1 c2: canon)
  : Lemma (ensures r.eq.eq (r.mul (canon_denote r vm c1) (canon_denote r vm c2))
                                   (canon_denote r vm (cross c1 c2)))
          (decreases c1) =
  match c1 with
  | [] -> r.zero_mul_l (canon_denote r vm c2)
  | sm :: rest ->
    let sd = sm_denote r vm sm in
    let cr = canon_denote r vm rest in
    let cc = canon_denote r vm c2 in
    right_distributivity r sd cr cc;
    cross_one_correct r vm sm c2;
    cross_correct r vm rest c2;
    r.add_cong (r.mul sd cc) (r.mul cr cc) (canon_denote r vm (cross_one sm c2)) (canon_denote r vm (cross rest c2));
    canon_denote_append r vm (cross_one sm c2) (cross rest c2);
    r.eq.symmetry (canon_denote r vm (cross_one sm c2 @ cross rest c2))
                  (r.add (canon_denote r vm (cross_one sm c2)) (canon_denote r vm (cross rest c2)));
    trans3 r (r.mul (r.add sd cr) cc)
             (r.add (r.mul sd cc) (r.mul cr cc))
             (r.add (canon_denote r vm (cross_one sm c2)) (canon_denote r vm (cross rest c2)))
             (canon_denote r vm (cross_one sm c2 @ cross rest c2))

(* Expansion preserves denotation *)
let rec expand_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (e: rexp)
  : Lemma (ensures r.eq.eq (rdenote r vm e) (canon_denote r vm (expand e)))
          (decreases e) =
  match e with
  | RZero -> r.eq.reflexivity r.zero
  | ROne ->
    x_plus_zero r r.one;
    r.eq.symmetry (r.add r.one r.zero) r.one
  | RAtom i ->
    let vi = vmap_lookup i vm in
    x_mul_one r vi;
    r.eq.symmetry (r.mul vi r.one) vi;
    x_plus_zero r (r.mul vi r.one);
    r.eq.symmetry (r.add (r.mul vi r.one) r.zero) (r.mul vi r.one);
    trans r vi (r.mul vi r.one) (r.add (r.mul vi r.one) r.zero)
  | RAdd e1 e2 ->
    expand_correct r vm e1; expand_correct r vm e2;
    r.add_cong (rdenote r vm e1) (rdenote r vm e2) (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2));
    canon_denote_append r vm (expand e1) (expand e2);
    r.eq.symmetry (canon_denote r vm (expand e1 @ expand e2))
                  (r.add (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2)));
    trans r (r.add (rdenote r vm e1) (rdenote r vm e2))
           (r.add (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2)))
           (canon_denote r vm (expand e1 @ expand e2))
  | RNeg e1 ->
    expand_correct r vm e1;
    r.neg_cong (rdenote r vm e1) (canon_denote r vm (expand e1));
    negate_all_correct r vm (expand e1);
    trans r (r.neg (rdenote r vm e1)) (r.neg (canon_denote r vm (expand e1)))
           (canon_denote r vm (negate_all (expand e1)))
  | RMul e1 e2 ->
    expand_correct r vm e1; expand_correct r vm e2;
    r.mul_cong (rdenote r vm e1) (rdenote r vm e2) (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2));
    cross_correct r vm (expand e1) (expand e2);
    trans r (r.mul (rdenote r vm e1) (rdenote r vm e2))
           (r.mul (canon_denote r vm (expand e1)) (canon_denote r vm (expand e2)))
           (canon_denote r vm (cross (expand e1) (expand e2)))
  | RSub e1 e2 ->
    (* sub x y = add x (neg y), by subtraction_definition. Then same as RAdd e1 (RNeg e2). *)
    let d1 = rdenote r vm e1 in
    let d2 = rdenote r vm e2 in
    r.subtraction_definition d1 d2;
    (* r.sub d1 d2 = r.add d1 (r.neg d2) *)
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
private let rec insert_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (sm: signed_monom) (c: canon)
  : Lemma (ensures r.eq.eq (canon_denote r vm (insert_sm sm c))
                                   (r.add (sm_denote r vm sm) (canon_denote r vm c)))
          (decreases c) =
  match c with
  | [] -> r.eq.reflexivity (r.add (sm_denote r vm sm) r.zero)
  | sm2 :: rest ->
    if sm_leq sm sm2 then
      r.eq.reflexivity (r.add (sm_denote r vm sm) (canon_denote r vm (sm2 :: rest)))
    else begin
      insert_correct r vm sm rest;
      let s = sm_denote r vm sm in
      let s2 = sm_denote r vm sm2 in
      let cr = canon_denote r vm rest in
      r.eq.reflexivity s2;
      r.add_cong s2 (canon_denote r vm (insert_sm sm rest)) s2 (r.add s cr);
      r.add_associativity s2 s cr;
      r.eq.symmetry (r.add (r.add s2 s) cr) (r.add s2 (r.add s cr));
      r.add_commutativity s2 s;
      r.eq.reflexivity cr;
      r.add_cong (r.add s2 s) cr (r.add s s2) cr;
      r.add_associativity s s2 cr;
      trans4 r (r.add s2 (canon_denote r vm (insert_sm sm rest)))
               (r.add s2 (r.add s cr))
               (r.add (r.add s2 s) cr)
               (r.add (r.add s s2) cr)
               (r.add s (r.add s2 cr))
    end

(* Insertion sort preserves sum *)
private let rec isort_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (c: canon)
  : Lemma (ensures r.eq.eq (canon_denote r vm (isort c)) (canon_denote r vm c))
          (decreases c) =
  match c with
  | [] -> r.eq.reflexivity r.zero
  | sm :: rest ->
    isort_correct r vm rest;
    insert_correct r vm sm (isort rest);
    r.eq.reflexivity (sm_denote r vm sm);
    r.add_cong (sm_denote r vm sm) (canon_denote r vm (isort rest)) (sm_denote r vm sm) (canon_denote r vm rest);
    r.eq.symmetry (r.add (sm_denote r vm sm) (canon_denote r vm rest))
                  (r.add (sm_denote r vm sm) (canon_denote r vm (isort rest)));
    trans r (canon_denote r vm (insert_sm sm (isort rest)))
           (r.add (sm_denote r vm sm) (canon_denote r vm (isort rest)))
           (r.add (sm_denote r vm sm) (canon_denote r vm rest))

(* Cancellation preserves denotation: opposite-signed same-monom pairs sum to zero *)
private let rec cancel_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (c: canon)
  : Lemma (ensures r.eq.eq (canon_denote r vm c) (canon_denote r vm (cancel c)))
          (decreases c) =
  match c with
  | (s1, m1) :: (s2, m2) :: rest ->
    if m1 = m2 && s1 <> s2 then begin
      (* sm_denote of opposite signs with same monom sum to zero *)
      let md = monom_denote r vm m1 in
      let cr = canon_denote r vm rest in
      (* The two signed monoms: one is md, other is neg md *)
      let v1 = sm_denote r vm (s1, m1) in
      let v2 = sm_denote r vm (s2, m2) in
      (* v1 + v2 = zero because they have opposite signs on same monom *)
      (if s1 then begin
        (* v1 = md, v2 = neg md *)
        r.add_neg_r md;
        (* md + neg md = zero *)
        ()
      end else begin
        (* v1 = neg md, v2 = md *)
        r.add_commutativity (r.neg md) md;
        r.add_neg_r md;
        trans r (r.add (r.neg md) md) (r.add md (r.neg md)) r.zero
      end);
      (* canon_denote c = v1 + (v2 + cr) *)
      (* = (v1 + v2) + cr  [assoc] *)
      r.add_associativity v1 v2 cr;
      r.eq.symmetry (r.add (r.add v1 v2) cr) (r.add v1 (r.add v2 cr));
      (* = zero + cr  [v1+v2=zero] *)
      r.eq.reflexivity cr;
      r.add_cong (r.add v1 v2) cr r.zero cr;
      (* = cr  [zero_plus_x] *)
      r.zero_plus_x cr;
      trans3 r (r.add v1 (r.add v2 cr))
               (r.add (r.add v1 v2) cr)
               (r.add r.zero cr)
               cr;
      (* Now chain: canon_denote c = cr = canon_denote (cancel rest) *)
      cancel_correct r vm rest;
      trans r (r.add v1 (r.add v2 cr)) cr (canon_denote r vm (cancel rest))
    end else begin
      cancel_correct r vm ((s2, m2) :: rest);
      let v1 = sm_denote r vm (s1, m1) in
      r.eq.reflexivity v1;
      r.add_cong v1 (canon_denote r vm ((s2, m2) :: rest)) v1 (canon_denote r vm (cancel ((s2, m2) :: rest)))
    end
  | _ -> r.eq.reflexivity (canon_denote r vm c)
let normalize_correct (#a:Type) (r: cr_eq a) (vm: vmap a) (e: rexp)
  : Lemma (r.eq.eq (rdenote r vm e) (canon_denote r vm (normalize e))) =
  expand_correct r vm e;
  isort_correct r vm (expand e);
  r.eq.symmetry (canon_denote r vm (isort (expand e))) (canon_denote r vm (expand e));
  cancel_correct r vm (isort (expand e));
  trans3 r (rdenote r vm e) (canon_denote r vm (expand e))
           (canon_denote r vm (isort (expand e)))
           (canon_denote r vm (cancel (isort (expand e))))

(* ================================================================== *)
(*  Part E: Reflection lemma                                          *)
(* ================================================================== *)

let ring_reflect (#a:Type) (r: cr_eq a) (vm: vmap a) (e1 e2: rexp)
  : Lemma (requires normalize e1 == normalize e2)
          (ensures r.eq.eq (rdenote r vm e1) (rdenote r vm e2)) =
  normalize_correct r vm e1;
  normalize_correct r vm e2;
  r.eq.symmetry (rdenote r vm e2) (canon_denote r vm (normalize e2));
  trans r (rdenote r vm e1) (canon_denote r vm (normalize e1)) (rdenote r vm e2)

let ring_reflect_sq (#a:Type) (r: cr_eq a) (vm: vmap a) (e1 e2: rexp)
    (_ : squash (normalize e1 == normalize e2))
  : squash (r.eq.eq (rdenote r vm e1) (rdenote r vm e2))
  = ring_reflect r vm e1 e2

let ring_reflect_v2 (#a:Type) (r: cr_eq a) (vm: vmap a) (e1 e2: rexp) (a1 a2: a)
    (_ : squash (normalize e1 == normalize e2))
    (_ : squash (a1 == rdenote r vm e1))
    (_ : squash (a2 == rdenote r vm e2))
  : squash (r.eq.eq a1 a2)
  = ring_reflect r vm e1 e2

(* ================================================================== *)
(*  Part F: comm_ring_to_cr_eq constructor (retargeted to Core.Algebra) *)
(* ================================================================== *)

(* In the new tower we already have:
     zero_mul_x  (Helpers): zero * x = zero
     x_mul_zero  (Helpers): x * zero = zero
     neg_of_sum  (Helpers): neg (x+y) = neg y + neg x
   We need extra helpers for neg_mul_l and double_neg. *)

#push-options "--z3rlimit 40"
private let cr_neg_mul_l (#t:Type) {| r: ring t |} (x y: t)
  : Lemma (r.r_add.acg_eq.eq (r.mul (r.r_add.neg x) y)
                              (r.r_add.neg (r.mul x y)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let nx = neg x in
    let xy = x * y in
    let nxy = neg xy in
    let nxx_y = (nx + x) * y in
    let nxy_xy = (nx * y) + xy in
    (* (nx + x) * y = nx*y + x*y *)
    r.right_distributivity y nx x;
    (* nx + x = 0 ; so (nx+x)*y = 0*y = 0 *)
    H.neg_x_plus_x x;
    reflexivity y;
    mul_congruence (nx + x) y (zero #t) y;
    H.zero_mul_x y;
    H.trans2 nxx_y (zero * y) (zero #t);
    (* so 0 = (nx+x)*y = nx*y + x*y *)
    symmetry nxx_y nxy_xy;
    symmetry nxx_y (zero #t);
    H.trans2 (zero #t) nxx_y nxy_xy;
    (* nxy + xy = 0 *)
    H.neg_x_plus_x xy;
    (* nx*y + xy = nxy + xy: both equal to zero *)
    symmetry (zero #t) (nxy + xy);
    H.trans2 nxy_xy (zero #t) (nxy + xy);
    (* cancel xy on right *)
    add_associativity (nx * y) xy (neg xy);
    add_associativity nxy xy (neg xy);
    H.x_plus_neg_x xy;
    reflexivity (nx * y);
    reflexivity nxy;
    add_congruence (nx * y) (xy + neg xy) (nx * y) (zero #t);
    add_congruence nxy (xy + neg xy) nxy (zero #t);
    H.x_plus_zero (nx * y);
    H.x_plus_zero nxy;
    reflexivity (neg xy);
    add_congruence nxy_xy (neg xy) (nxy + xy) (neg xy);
    transitivity ((nx * y) + xy + neg xy) (nxy + xy + neg xy)
                 (nxy + (xy + neg xy));
    transitivity ((nx * y) + xy + neg xy) (nxy + (xy + neg xy)) (nxy + zero);
    transitivity ((nx * y) + xy + neg xy) (nxy + zero) nxy;
    (* Also nx*y + xy + (-xy) = nx*y + (xy + -xy) = nx*y + 0 = nx*y *)
    symmetry ((nx * y) + xy + neg xy) ((nx * y) + (xy + neg xy));
    transitivity (nx * y) ((nx * y) + zero) ((nx * y) + (xy + neg xy));
    symmetry ((nx * y) + zero) (nx * y);
    transitivity (nx * y) ((nx * y) + (xy + neg xy)) ((nx * y) + xy + neg xy);
    transitivity (nx * y) ((nx * y) + xy + neg xy) nxy
#pop-options

#push-options "--z3rlimit 40"
private let cr_double_neg (#t:Type) {| r: ring t |} (x: t)
  : Lemma (r.r_add.acg_eq.eq (r.r_add.neg (r.r_add.neg x)) x)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let nx = neg x in
    let nnx = neg nx in
    (* nnx + nx = 0 ; x + nx = 0 ; so nnx = x by right-cancellation *)
    H.neg_x_plus_x nx;
    H.x_plus_neg_x x;
    symmetry (x + nx) (zero #t);
    transitivity (nnx + nx) (zero #t) (x + nx);
    add_associativity nnx nx (neg nx);
    add_associativity x nx (neg nx);
    H.x_plus_neg_x nx;
    reflexivity nnx;
    reflexivity x;
    add_congruence nnx (nx + neg nx) nnx (zero #t);
    add_congruence x (nx + neg nx) x (zero #t);
    H.x_plus_zero nnx;
    H.x_plus_zero x;
    reflexivity (neg nx);
    add_congruence (nnx + nx) (neg nx) (x + nx) (neg nx);
    transitivity (nnx + nx + neg nx) (x + nx + neg nx) (x + (nx + neg nx));
    transitivity (nnx + nx + neg nx) (x + (nx + neg nx)) (x + zero);
    transitivity (nnx + nx + neg nx) (x + zero) x;
    symmetry (nnx + nx + neg nx) (nnx + (nx + neg nx));
    transitivity nnx (nnx + zero) (nnx + (nx + neg nx));
    symmetry (nnx + zero) nnx;
    transitivity nnx (nnx + (nx + neg nx)) (nnx + nx + neg nx);
    transitivity nnx (nnx + nx + neg nx) x
#pop-options

unfold let comm_ring_to_cr_eq (#t:Type) {| cr: commutative_ring t |} : cr_eq t =
  let r : ring t = cr.cr_r in
  let g : add_comm_group t = r.r_add in
  let e : equatable t = g.acg_eq in
  {
    eq = {
      eq          = e.eq;
      reflexivity  = e.reflexivity;
      symmetry     = e.symmetry;
      transitivity = e.transitivity;
    };
    add      = g.add;
    mul      = r.mul;
    neg      = g.neg;
    sub      = (fun x y -> g.add x (g.neg y));
    zero     = g.zero;
    one      = r.one;
    add_associativity = (fun x y z -> g.add_associativity x y z);
    add_commutativity  = (fun x y -> g.add_commutativity x y);
    H.zero_plus_x       = (fun x -> g.add_zero x);
    add_neg_r         = (fun x -> g.add_negation x);
    add_cong          = (fun x y z w -> g.add_congruence x y z w);
    neg_cong          = (fun x y -> g.neg_congruence x y);
    mul_associativity = (fun x y z -> r.mul_associativity x y z);
    mul_commutativity  = (fun x y -> cr.cr_mic.mul_commutativity x y);
    H.one_mul_x         = (fun x -> r.mul_one x);
    mul_cong          = (fun x y z w -> r.mul_congruence x y z w);
    left_distributivity = (fun x y z -> r.left_distributivity x y z);
    zero_mul_l        = (fun x -> H.zero_mul_x #t #r x);
    neg_mul_l         = (fun x y -> cr_neg_mul_l #t #r x y);
    neg_add           = (fun x y -> H.neg_of_sum #t #g x y);
    double_neg        = (fun x -> cr_double_neg #t #r x);
    subtraction_definition = (fun x y -> reflexivity (g.add x (g.neg y)));
  }

(* ================================================================== *)
(*  Part G: Meta-tactic canon_ring()  (new-tower projector names)      *)
(* ================================================================== *)

module T  = FStar.Tactics.V2
module Lst = FStar.List.Tot.Base
module R  = FStar.Reflection.V2
module RT = FStar.Reflection.TermEq.Simple

open FStar.Tactics.V2

private let rec where_aux (n:nat) (x:T.term) (xs:list T.term) : T.Tac (option nat) =
  match xs with
  | [] -> None
  | x'::xs' -> if RT.term_eq x x' then Some n else where_aux (Prims.op_Addition n 1) x xs'

private let where (x: T.term) (xs: list T.term) : T.Tac (option nat) = where_aux 0 x xs

private let fatom_r (t: T.term) (ts: list T.term) (vm: list (atom & T.term) & T.term)
  : T.Tac (rexp & list T.term & (list (atom & T.term) & T.term)) =
  match where t ts with
  | Some v -> (RAtom v, ts, vm)
  | None ->
    let vfresh = Lst.length ts in
    let (m, def) = vm in
    (RAtom vfresh, ts @ [t], (m @ [(vfresh, t)], def))

private let rec explicit_args (args: list (T.term & T.aqualv)) : list T.term =
  match args with
  | [] -> []
  | (a, R.Q_Explicit) :: rest -> a :: explicit_args rest
  | _ :: rest -> explicit_args rest

private let rec last_in_list (xs: list string) : string =
  match xs with
  | [] -> ""
  | [x] -> x
  | _ :: rest -> last_in_list rest

private let head_short_name (t: T.term) : T.Tac string =
  match T.inspect t with
  | T.Tv_FVar fv -> last_in_list (R.inspect_fv fv)
  | T.Tv_UInst fv _ -> last_in_list (R.inspect_fv fv)
  | _ -> ""

(* New-tower projector names. After `norm [delta; iota; zeta]`, the
   typeclass-resolved operators present as direct projector applications:
     add  → __proj__Mkadd_comm_group__item__add  (record, x, y)
     mul  → __proj__Mkring__item__mul             (record, x, y)
     neg  → __proj__Mkadd_comm_group__item__neg   (record, x)
     zero → __proj__Mkadd_comm_group__item__zero  (record)
     one  → __proj__Mkring__item__one             (record)
   We also keep the `op_Plus`/`op_Star`/`op_Minus`/`zero`/`one`/`neg`
   short names so users of the Notation operators are matched even when
   inlining is incomplete. *)
private let rec reify_rexp
    (ts: list T.term) (vm: list (atom & T.term) & T.term)
    (t: T.term)
  : T.Tac (rexp & list T.term & (list (atom & T.term) & T.term)) =
  let hd, all_args = T.collect_app t in
  let exps = explicit_args all_args in
  let hname = head_short_name hd in
  let is_proj_add  = hname = "__proj__Mkadd_comm_group__item__add" in
  let is_proj_mul  = hname = "__proj__Mkring__item__mul" in
  let is_proj_neg  = hname = "__proj__Mkadd_comm_group__item__neg" in
  let is_proj_zero = hname = "__proj__Mkadd_comm_group__item__zero" in
  let is_proj_one  = hname = "__proj__Mkring__item__one" in
  let is_ring_add  = hname = "op_Plus"  || hname = "add" || is_proj_add in
  let is_ring_mul  = hname = "op_Star"  || hname = "mul" || is_proj_mul in
  let is_ring_sub  = hname = "op_Subtraction" || hname = "sub" in
  let is_ring_neg  = hname = "op_Minus" || hname = "neg" || is_proj_neg in
  let is_ring_zero = hname = "zero" || is_proj_zero in
  let is_ring_one  = hname = "one"  || is_proj_one  in
  (* Projectors take the record as the FIRST explicit arg; strip it.
     Short names from Notation (op_Plus etc.) do NOT have a leading
     record arg — their record is implicit. *)
  let is_record_proj = is_proj_add || is_proj_mul || is_proj_neg
                    || is_proj_zero || is_proj_one in
  let ops = if is_record_proj && Cons? exps then Lst.tail exps else exps in
  if is_ring_zero && Lst.length ops = 0 then (RZero, ts, vm)
  else if is_ring_one && Lst.length ops = 0 then (ROne, ts, vm)
  else
  match ops with
  | [t1; t2] ->
    if is_ring_add then
      let (e1, ts1, vm1) = reify_rexp ts vm t1 in
      let (e2, ts2, vm2) = reify_rexp ts1 vm1 t2 in
      (RAdd e1 e2, ts2, vm2)
    else if is_ring_mul then
      let (e1, ts1, vm1) = reify_rexp ts vm t1 in
      let (e2, ts2, vm2) = reify_rexp ts1 vm1 t2 in
      (RMul e1 e2, ts2, vm2)
    else if is_ring_sub then
      let (e1, ts1, vm1) = reify_rexp ts vm t1 in
      let (e2, ts2, vm2) = reify_rexp ts1 vm1 t2 in
      (RSub e1 e2, ts2, vm2)
    else fatom_r t ts vm
  | [t1] ->
    if is_ring_neg then
      let (e1, ts1, vm1) = reify_rexp ts vm t1 in
      (RNeg e1, ts1, vm1)
    else fatom_r t ts vm
  | _ -> fatom_r t ts vm

private let rec quote_rexp (e: rexp) : T.Tac T.term =
  match e with
  | RZero -> `(RZero)
  | ROne  -> `(ROne)
  | RAtom n ->
    let nt = R.pack_ln (R.Tv_Const (R.C_Int n)) in
    `(RAtom (`#nt))
  | RAdd e1 e2 -> `(RAdd (`#(quote_rexp e1)) (`#(quote_rexp e2)))
  | RMul e1 e2 -> `(RMul (`#(quote_rexp e1)) (`#(quote_rexp e2)))
  | RNeg e1    -> `(RNeg (`#(quote_rexp e1)))
  | RSub e1 e2 -> `(RSub (`#(quote_rexp e1)) (`#(quote_rexp e2)))

private let rec quote_vmap_list (m: list (atom & T.term)) : T.Tac T.term =
  match m with
  | [] -> `([])
  | (a, t)::ps ->
    let at = R.pack_ln (R.Tv_Const (R.C_Int a)) in
    `(((`#at), (`#t)) :: (`#(quote_vmap_list ps)))

private let quote_vmap (vm: list (atom & T.term) & T.term) : T.Tac T.term =
  let (m, def) = vm in
  `((`#(quote_vmap_list m), (`#def)))

private let canon_lhs_rhs_with (r_t: T.term) (lhs rhs: T.term) : T.Tac unit =
  let vm0 : list (atom & T.term) & T.term = ([], lhs) in
  let (re1, ts1, vm1) = reify_rexp [] vm0 lhs in
  let (re2, _,   vm2) = reify_rexp ts1 vm1 rhs in
  let vm_t  = quote_vmap vm2 in
  let re1_t = quote_rexp re1 in
  let re2_t = quote_rexp re2 in
  T.apply (`(ring_reflect_v2 (`#r_t) (`#vm_t) (`#re1_t) (`#re2_t) (`#lhs) (`#rhs)));
  T.norm [delta; iota; zeta; primops]; T.trefl ();
  T.norm [delta; iota; zeta; primops]; T.trefl ();
  T.norm [delta; iota; zeta; primops]; T.trefl ()

(* Top-level tactic taking an explicit cr_eq term. *)
(* Find a binder in the env whose type yields a `commutative_ring _`,
   either directly or via a TC projection (integral_domain, field, ...).
   Returns the type term and a Tac action producing the cr term. *)
private let rec find_cr_binder_aux
    (target: option T.term)
    (bs: list T.binding)
  : T.Tac (option (T.term & T.term)) =
  match bs with
  | [] -> None
  | b :: rest ->
    let bty = b.sort in
    let hd, args = T.collect_app bty in
    let hname = head_short_name hd in
    let b_term = T.pack (T.Tv_Var b) in
    (match args with
     | (tt, _) :: _ ->
       let type_matches =
         match target with
         | None -> true
         | Some tgt -> RT.term_eq tt tgt
       in
       if not type_matches then find_cr_binder_aux target rest
       else if hname = "commutative_ring" then
         Some (tt, b_term)
       else if hname = "integral_domain" then
         let f = (`Core.Algebra.cr_of_id) in
         let app1 = T.pack (T.Tv_App f (tt, T.Q_Explicit)) in
         let app2 = T.pack (T.Tv_App app1 (b_term, T.Q_Implicit)) in
         Some (tt, app2)
       else if hname = "field" then
         let f_id_of_f = (`Core.Algebra.id_of_f) in
         let id1 = T.pack (T.Tv_App f_id_of_f (tt, T.Q_Explicit)) in
         let id2 = T.pack (T.Tv_App id1 (b_term, T.Q_Implicit)) in
         let f = (`Core.Algebra.cr_of_id) in
         let app1 = T.pack (T.Tv_App f (tt, T.Q_Explicit)) in
         let app2 = T.pack (T.Tv_App app1 (id2, T.Q_Implicit)) in
         Some (tt, app2)
       else find_cr_binder_aux target rest
     | _ -> find_cr_binder_aux target rest)

private let find_cr_binder (bs: list T.binding)
  : T.Tac (option (T.term & T.term)) =
  find_cr_binder_aux None bs

let canon_ring_with (r_t: T.term) : T.Tac unit =
  T.norm [delta_only [`%op_Plus; `%op_Star; `%op_Minus; `%( -- );
                       `%Core.Algebra.acg_of_r; `%Core.Algebra.r_of_cr;
                       `%Core.Algebra.r_of_d; `%Core.Algebra.d_of_id;
                       `%Core.Algebra.cr_of_id; `%Core.Algebra.id_of_f;
                       `%Core.Algebra.eq_of_acg];
          iota; zeta; primops];
  let g = T.cur_goal () in
  let _, args = T.collect_app g in
  let rec last_two (args: list (T.term & T.aqualv)) : T.Tac (T.term & T.term) =
    match args with
    | [(inner, _)] ->
      let _, a2 = T.collect_app inner in
      last_two a2
    | [(lhs, R.Q_Explicit); (rhs, R.Q_Explicit)] -> (lhs, rhs)
    | _::rest -> last_two rest
    | [] -> T.fail "canon_ring: could not find lhs/rhs in goal"
  in
  let (lhs, rhs) = last_two args in
  canon_lhs_rhs_with r_t lhs rhs

(* Zero-arg convenience: locate a `commutative_ring t` binder in scope
   and feed `comm_ring_to_cr_eq #t #cr` (fully applied) to canon_ring_with.
   Preference order: a CR binder whose carrier-type matches the goal's
   LHS type (so polynomial-CR wins over base-ring-CR when both are in
   scope), falling back to the first available CR/ID/field binder. *)
let canon_ring () : T.Tac unit =
  let bs = T.vars_of_env (T.cur_env ()) in
  let goal_target : option T.term =
    try
      let g = T.cur_goal () in
      let _, args = T.collect_app g in
      let rec last_two (args: list (T.term & T.aqualv)) : T.Tac (T.term & T.term) =
        match args with
        | [(inner, _)] ->
          let _, a2 = T.collect_app inner in
          last_two a2
        | [(lhs, R.Q_Explicit); (rhs, R.Q_Explicit)] -> (lhs, rhs)
        | _::rest -> last_two rest
        | [] -> T.fail "no eq args"
      in
      let (lhs, _rhs) = last_two args in
      let ty = T.tc (T.cur_env ()) lhs in
      Some ty
    with _ -> None
  in
  let chosen =
    match goal_target with
    | None -> find_cr_binder bs
    | Some tgt ->
      (match find_cr_binder_aux (Some tgt) bs with
       | Some r -> Some r
       | None -> find_cr_binder bs)
  in
  match chosen with
  | None -> T.fail "canon_ring: no `commutative_ring _` (or integral_domain/field) instance binder in scope"
  | Some (t_term, cr_term) ->
    let r_t = `(comm_ring_to_cr_eq #(`#t_term) #(`#cr_term)) in
    canon_ring_with r_t

(* ================================================================== *)
(*  Part H: canon_ring_subst — substitute equal subterms then canon   *)
(* ================================================================== *)

private let rec drop_n (#a:Type) (n:nat) (xs: list a) : list a =
  if n = 0 then xs
  else match xs with
       | [] -> []
       | _::rest -> drop_n (n-1) rest

private let last_n (#a:Type) (n:nat) (xs: list a) : list a =
  let len = Lst.length xs in
  if len <= n then xs else drop_n (len - n) xs

(* Find a hypothesis proving `e1 = e2` (possibly nested inside conjunctions
   or under squash/b2t/auto_squash wrappers). Returns a tactic that, when
   invoked with current goal `squash (e1 = e2)`, closes it. *)

private let l_and_left  (#a #b: prop) (_: squash (a /\ b)) : Lemma a = ()
private let l_and_right (#a #b: prop) (_: squash (a /\ b)) : Lemma b = ()

private let rec scan_hyp_type
    (e1_t e2_t: T.term)
    (ty: T.term)
    (cont: unit -> T.Tac unit)
  : T.Tac (option (unit -> T.Tac unit)) =
  let hd, args = T.collect_app ty in
  let hname = head_short_name hd in
  if hname = "squash" || hname = "b2t" || hname = "auto_squash" then
    (match explicit_args args with
     | [inner] -> scan_hyp_type e1_t e2_t inner cont
     | _ -> None)
  else if hname = "l_and" || hname = "op_AmpAmp" || hname = "/\\" then
    (match explicit_args args with
     | [a_ty; b_ty] ->
       let left_cont () : T.Tac unit =
         T.apply_lemma (`(l_and_left #_ #(`#b_ty))); cont ()
       in
       (match scan_hyp_type e1_t e2_t a_ty left_cont with
        | Some k -> Some k
        | None ->
          let right_cont () : T.Tac unit =
            T.apply_lemma (`(l_and_right #(`#a_ty) #_)); cont ()
          in
          scan_hyp_type e1_t e2_t b_ty right_cont)
     | _ -> None)
  else
    let exps = explicit_args args in
    (match last_n 2 exps with
     | [a; b'] ->
       if RT.term_eq a e1_t && RT.term_eq b' e2_t
       then Some cont
       else None
     | _ -> None)

private let rec find_eq_hyp (e1_t e2_t: T.term) (bs: list T.binding)
  : T.Tac (option (unit -> T.Tac unit)) =
  match bs with
  | [] -> None
  | b :: rest ->
    let b_term = T.pack (T.Tv_Var b) in
    let _ = b_term in
    (* When the equality is found, the binder is in SMT scope; close leaf via smt. *)
    let cont () : T.Tac unit = T.smt () in
    (match scan_hyp_type e1_t e2_t b.sort cont with
     | Some k -> Some k
     | None -> find_eq_hyp e1_t e2_t rest)


(* Helpers with arg orderings suitable for tactic apply_lemma:
   the "key" arg comes first so it can be supplied explicitly while
   F* unifies the remaining args against the goal. *)
private let eq_trans_via (#t:Type) {| equatable t |} (m: t) (x z: t)
  (_: squash (x = m)) (_: squash (m = z)) : Lemma (x = z)
  = transitivity x m z

private let eq_symm_l (#t:Type) {| equatable t |} (y x: t)
  (_: squash (y = x)) : Lemma (x = y)
  = symmetry x y

(* Recursively walk t, return (t_subst, proof_tac) where proof_tac, when
   invoked with current goal `t = t_subst`, closes it. *)
private let rec build_subst
    (e1_t e2_t: T.term) (h_tac: unit -> T.Tac unit) (t: T.term)
  : T.Tac (T.term & (unit -> T.Tac unit)) =
  if RT.term_eq t e1_t then
    (e2_t, h_tac)
  else
    let hd, args = T.collect_app t in
    let hname = head_short_name hd in
    let exps = explicit_args args in
    let n = Lst.length exps in
    let is_add = (hname = "add" || hname = "op_Plus"
                  || hname = "__proj__Mkadd_comm_group__item__add") && n >= 2 in
    let is_mul = (hname = "mul" || hname = "op_Star"
                  || hname = "__proj__Mkring__item__mul") && n >= 2 in
    let is_neg = (hname = "neg" || hname = "op_Minus"
                  || hname = "__proj__Mkadd_comm_group__item__neg") && n >= 1 in
    let refl_close (_term: T.term) () : T.Tac unit =
      (* lhs and rhs of this subgoal are the same term by construction.
         The goal shape is `squash (term = term)` where `=` is the equatable
         op. Discharge by introducing `eq_refl term` as a fact and SMT. *)
      T.norm [delta_only [`%Core.Algebra.Notation.op_Equals]; iota; zeta];
      T.smt ()
    in
    if is_add || is_mul then
      (match last_n 2 exps with
       | [a; b] ->
         let (a', ta) = build_subst e1_t e2_t h_tac a in
         let (b', tb) = build_subst e1_t e2_t h_tac b in
         if RT.term_eq a a' && RT.term_eq b b' then
           (t, refl_close t)
         else
           let rec rep2 (xs: list (T.term & T.aqualv))
             : T.Tac (list (T.term & T.aqualv)) =
             match xs with
             | [(_, q1); (_, q2)] -> [(a', q1); (b', q2)]
             | x :: rest -> x :: rep2 rest
             | [] -> []
           in
           let t' = T.mk_app hd (rep2 args) in
           let close () : T.Tac unit =
             (if is_add then
                T.apply_lemma (`Core.Algebra.add_congruence)
              else
                T.apply_lemma (`Core.Algebra.mul_congruence));
             T.split ();
             ta ();
             tb ()
           in
           (t', close)
       | _ -> (t, refl_close t))
    else if is_neg then
      (match last_n 1 exps with
       | [a] ->
         let (a', ta) = build_subst e1_t e2_t h_tac a in
         if RT.term_eq a a' then
           (t, refl_close t)
         else
           let rec rep1 (xs: list (T.term & T.aqualv))
             : T.Tac (list (T.term & T.aqualv)) =
             match xs with
             | [(_, q)] -> [(a', q)]
             | x :: rest -> x :: rep1 rest
             | [] -> []
           in
           let t' = T.mk_app hd (rep1 args) in
           let close () : T.Tac unit =
             T.apply_lemma (`Core.Algebra.neg_congruence);
             ta ()
           in
           (t', close)
       | _ -> (t, refl_close t))
    else
      (t, refl_close t)

(* Walk a binder's sort, collect candidate (a, b) pairs corresponding to a
   buried equality `a = b`. Handles squash/b2t/auto_squash wrappers and
   conjunctions. Does NOT descend into binders (forall/exists) or
   implications — those typically wrap the lemma's ensures/conclusion,
   not usable hypotheses. *)
private let rec collect_eq_candidates (ty: T.term) : T.Tac (list (T.term & T.term)) =
  let hd, args = T.collect_app ty in
  let hname = head_short_name hd in
  if hname = "squash" || hname = "b2t" || hname = "auto_squash" then
    (match explicit_args args with
     | [inner] -> collect_eq_candidates inner
     | _ -> [])
  else if hname = "l_and" || hname = "op_AmpAmp" || hname = "/\\" then
    (match explicit_args args with
     | [a_ty; b_ty] ->
       Lst.append (collect_eq_candidates a_ty) (collect_eq_candidates b_ty)
     | _ -> [])
  else if hname = "l_Forall" || hname = "Forall" || hname = "l_Exists"
       || hname = "Exists"   || hname = "l_imp"  || hname = "==>" then
    []  (* skip binders and implications *)
  else
    (* Also skip terms that are themselves lambdas/arrows *)
    match T.inspect ty with
    | T.Tv_Abs _ _ -> []
    | T.Tv_Arrow _ _ -> []
    | _ ->
      let exps = explicit_args args in
      (match last_n 2 exps with
       | [a; b'] -> [(a, b')]
       | _ -> [])

(* Term occurs-check: does `needle` appear as a subterm of `haystack`?
   Uses syntactic equality (RT.term_eq). Walks all sub-terms. *)
private let rec term_occurs (needle haystack: T.term) : T.Tac bool =
  if RT.term_eq needle haystack then true
  else
    let _, args = T.collect_app haystack in
    let rec any_arg (xs: list (T.term & T.aqualv)) : T.Tac bool =
      match xs with
      | [] -> false
      | (a, _) :: rest -> if term_occurs needle a then true else any_arg rest
    in
    any_arg args

(* Tactic: in a `commutative_ring`/`integral_domain`/`field` goal of shape
   `lhs = rhs`, with a hypothesis `h : e1 = e2` in scope, prove the goal
   by substituting e1 -> e2 on both sides and closing the residual with
   canon_ring (). *)
let canon_ring_subst (e1_t e2_t: T.term) : T.Tac unit =
  let bs = T.vars_of_env (T.cur_env ()) in
  let h_tac =
    match find_eq_hyp e1_t e2_t bs with
    | Some k -> k
    | None -> T.fail "canon_ring_subst: no matching `e1 = e2` hypothesis found in scope"
  in
  (* Snapshot the cr/r_t term NOW, before any apply_lemma can perturb the env. *)
  let r_t =
    match find_cr_binder bs with
    | None -> T.fail "canon_ring_subst: no `commutative_ring _` (or integral_domain/field) instance binder in scope"
    | Some (t_term, cr_term) ->
      `(comm_ring_to_cr_eq #(`#t_term) #(`#cr_term))
  in
  T.norm [delta_only [`%op_Plus; `%op_Star; `%op_Minus; `%( -- );
                       `%Core.Algebra.acg_of_r; `%Core.Algebra.r_of_cr;
                       `%Core.Algebra.r_of_d; `%Core.Algebra.d_of_id;
                       `%Core.Algebra.cr_of_id; `%Core.Algebra.id_of_f;
                       `%Core.Algebra.eq_of_acg];
          iota; zeta; primops];
  let g = T.cur_goal () in
  let _, gargs = T.collect_app g in
  let rec last_two (args: list (T.term & T.aqualv)) : T.Tac (T.term & T.term) =
    match args with
    | [(inner, _)] ->
      let _, a2 = T.collect_app inner in
      last_two a2
    | [(lhs, R.Q_Explicit); (rhs, R.Q_Explicit)] -> (lhs, rhs)
    | _ :: rest -> last_two rest
    | [] -> T.fail "canon_ring_subst: could not find lhs/rhs in goal"
  in
  let (lhs, rhs) = last_two gargs in
  let (lhs', close_lhs) = build_subst e1_t e2_t h_tac lhs in
  let (rhs', close_rhs) = build_subst e1_t e2_t h_tac rhs in
  T.apply_lemma (`(eq_trans_via (`#rhs')));
  T.apply_lemma (`(eq_trans_via (`#lhs')));
  close_lhs ();
  canon_ring_with r_t;
  T.apply_lemma (`eq_symm_l);
  close_rhs ()

(* Like canon_ring_subst, but auto-discovers (e1, e2) from an in-scope
   equality hypothesis whose LHS appears as a subterm of the goal. *)
let canon_ring_subst_auto () : T.Tac unit =
  T.norm [delta_only [`%op_Plus; `%op_Star; `%op_Minus; `%( -- );
                       `%Core.Algebra.acg_of_r; `%Core.Algebra.r_of_cr;
                       `%Core.Algebra.r_of_d; `%Core.Algebra.d_of_id;
                       `%Core.Algebra.cr_of_id; `%Core.Algebra.id_of_f;
                       `%Core.Algebra.eq_of_acg];
          iota; zeta; primops];
  let env = T.cur_env () in
  let bs = T.vars_of_env env in
  let g = T.cur_goal () in
  let _, gargs = T.collect_app g in
  let rec last_two (args: list (T.term & T.aqualv)) : T.Tac (T.term & T.term) =
    match args with
    | [(inner, _)] ->
      let _, a2 = T.collect_app inner in
      last_two a2
    | [(lhs, R.Q_Explicit); (rhs, R.Q_Explicit)] -> (lhs, rhs)
    | _ :: rest -> last_two rest
    | [] -> T.fail "canon_ring_subst_auto: could not find lhs/rhs in goal"
  in
  let (glhs, grhs) = last_two gargs in
  let rec find_match (bs: list T.binding) : T.Tac (option (T.term & T.term)) =
    match bs with
    | [] -> None
    | b :: rest ->
      let cands = collect_eq_candidates b.sort in
      let rec try_cands (cs: list (T.term & T.term)) : T.Tac (option (T.term & T.term)) =
        match cs with
        | [] -> None
        | (a, b') :: rs ->
          if term_occurs a glhs || term_occurs a grhs
          then Some (a, b')
          else try_cands rs
      in
      (match try_cands cands with
       | Some p -> Some p
       | None -> find_match rest)
  in
  match find_match bs with
  | None -> T.fail "canon_ring_subst_auto: no in-scope equality hypothesis matches a goal subterm"
  | Some (e1_t, e2_t) -> canon_ring_subst e1_t e2_t
