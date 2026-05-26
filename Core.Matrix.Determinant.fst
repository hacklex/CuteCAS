module Core.Matrix.Determinant

(*   Determinant of a square matrix via the Leibniz formula:
       det(M) = Σ_{σ ∈ S_n}  sign(σ) · ∏_{i=0..n-1} M(i, σ(i))

   Ported from `..\new\FStar.CAS.Matrix.Determinant.fst` to the new
   diamond-free `core/` tower.

   Author: A. Rozanov (CuteCAS).
*)

module L = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Tactics.CanonRing
open Core.FinSum
open Core.Permutation
open Core.Permutation.Enum
open Core.Permutation.Sum
open Core.Matrix

(* -------------------------------------------------------------------- *)
(*  Local synthesis: add_comm_group from ring.                          *)
(*  In the core tower this is just `r.r_add` (already an add_comm_group), *)
(*  but we keep this alias name to minimize diff vs. the original file.   *)
(* -------------------------------------------------------------------- *)

unfold let acg_of_ring_local (t: Type) (r: ring t) : add_comm_group t = r.r_add


(* -------------------------------------------------------------------- *)
(*  Private ring-level helpers missing from Core.Algebra.Helpers.        *)
(*  TODO: promote these to Helpers once stable.                          *)
(* -------------------------------------------------------------------- *)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
private let priv_group_cancel_right (#t:Type) (g: add_comm_group t) (a b c: t)
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

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
(* (-x)*y = -(x*y) *)
private let priv_neg_mul_l (#t:Type) (r: ring t) (x y: t)
  : Lemma (r.r_add.acg_eq.eq (r.mul (r.r_add.neg x) y)
                              (r.r_add.neg (r.mul x y)))
  = H.elim_equatable_laws t #(r.r_add.acg_eq) ();
    H.trans_for_calc t #(r.r_add.acg_eq) ();
    let g = r.r_add in
    let nx = g.neg x in
    let xy = r.mul x y in
    let nxy = g.neg xy in
    (* (nx + x) * y = nx*y + x*y *)
    r.right_distributivity y nx x;
    g.add_negation x;
    g.acg_eq.reflexivity y;
    r.mul_congruence (g.add nx x) y g.zero y;
    H.zero_mul_x #t #r y;
    g.acg_eq.transitivity (r.mul (g.add nx x) y) (r.mul g.zero y) g.zero;
    g.acg_eq.symmetry (r.mul (g.add nx x) y) (g.add (r.mul nx y) (r.mul x y));
    g.acg_eq.transitivity g.zero (r.mul (g.add nx x) y) (g.add (r.mul nx y) (r.mul x y));
    g.acg_eq.symmetry g.zero (g.add (r.mul nx y) (r.mul x y));
    (* nxy + xy = 0 *)
    g.add_negation xy;
    (* So nx*y + xy = nxy + xy. Cancel xy on right. *)
    g.acg_eq.symmetry g.zero (g.add nxy xy);
    g.acg_eq.transitivity (g.add (r.mul nx y) xy) g.zero (g.add nxy xy);
    priv_group_cancel_right g (r.mul nx y) nxy xy
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
(* -(x*y) = x*(-y), for commutative_ring *)
private let priv_neg_mul_r (#t:Type) (cr: commutative_ring t) (x y: t)
  : Lemma (cr.cr_r.r_add.acg_eq.eq (cr.cr_r.r_add.neg (cr.cr_r.mul x y))
                                    (cr.cr_r.mul x (cr.cr_r.r_add.neg y)))
  = let r = cr.cr_r in
    let g = r.r_add in
    (* (-y)*x = -(y*x); by commutativity:
         (-y)*x = x*(-y), y*x = x*y, so x*(-y) = -(x*y), i.e. -(x*y) = x*(-y) *)
    priv_neg_mul_l r y x;                       (* (-y)*x = -(y*x) *)
    cr.cr_mic.mul_commutativity (g.neg y) x;     (* (-y)*x = x*(-y) *)
    cr.cr_mic.mul_commutativity y x;             (* y*x = x*y *)
    g.neg_congruence (r.mul y x) (r.mul x y);    (* -(y*x) = -(x*y) *)
    g.acg_eq.symmetry (r.mul (g.neg y) x) (r.mul x (g.neg y));
    (* combine: x*(-y) = (-y)*x = -(y*x) = -(x*y) *)
    g.acg_eq.transitivity (r.mul x (g.neg y)) (r.mul (g.neg y) x) (g.neg (r.mul y x));
    g.acg_eq.transitivity (r.mul x (g.neg y)) (g.neg (r.mul y x)) (g.neg (r.mul x y));
    g.acg_eq.symmetry (r.mul x (g.neg y)) (g.neg (r.mul x y))
#pop-options

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
(* -x = (-1) * x *)
private let priv_neg_x_eq_neg_one_mul (#t:Type) (r: ring t) (x: t)
  : Lemma (r.r_add.acg_eq.eq (r.r_add.neg x) (r.mul (r.r_add.neg r.one) x))
  = let g = r.r_add in
    (* (-1)*x = -(1*x) by priv_neg_mul_l with x:=1, y:=x *)
    priv_neg_mul_l r r.one x;
    (* 1*x = x *)
    r.mul_one x;
    g.neg_congruence (r.mul r.one x) x;          (* -(1*x) = -x *)
    g.acg_eq.transitivity (r.mul (g.neg r.one) x) (g.neg (r.mul r.one x)) (g.neg x);
    g.acg_eq.symmetry (r.mul (g.neg r.one) x) (g.neg x)
#pop-options

(* -------------------------------------------------------------------- *)
(*  Local trans_lemma helper                                             *)
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

(* -------------------------------------------------------------------- *)
(*  Local ring-derived helpers.  All use canon_ring / canon_comm_group   *)
(*  since the determinant module always has commutative_ring available.  *)
(* -------------------------------------------------------------------- *)

(* Private alias for removed Permutation API. *)
private let perm_eq_sym_local (#n: nat) (p q: permutation n)
  : Lemma (requires perm_eq p q) (ensures perm_eq q p)
  = reveal_opaque (`%perm_eq) (perm_eq p q);
    reveal_opaque (`%perm_eq) (perm_eq q p);
    perm_eq_bool_from_sym p q 0

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let ring_zero_is_left_absorber (#t: Type) {| cr: commutative_ring t |} (x: t)
  : Lemma (zero * x = zero)
  = H.zero_mul_x #t #cr.cr_r x

let ring_zero_is_right_absorber (#t: Type) {| cr: commutative_ring t |} (x: t)
  : Lemma (x * zero = zero)
  = H.x_mul_zero #t #cr.cr_r x

let neg_congruence_lem (#t:Type) {| cr: commutative_ring t |} (a b: t)
  : Lemma (requires a = b) (ensures (-a) = (-b))
  = neg_congruence a b

let neg_zero_lem (#t:Type) {| cr: commutative_ring t |}
  : Lemma ((-(zero #t)) = zero)
  = let g = cr.cr_r.r_add in
    H.neg_zero #t #g ();
    g.acg_eq.symmetry g.zero (g.neg g.zero)

let double_negation_lemma (#t: Type) {| cr: commutative_ring t |} (x: t)
  : Lemma ((-(-x)) = x)
  = assert ((-(-x)) = x) by canon_ring ()

let neg_of_sum_local (#t: Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (-(x + y) = (-x) + (-y))
  = assert (-(x + y) = (-x) + (-y)) by canon_ring ()

let ring_neg_x_is_minus_one_times_x (#t: Type) {| cr: commutative_ring t |} (x: t)
  : Lemma ((-x) = (-(one #t)) * x)
  = priv_neg_x_eq_neg_one_mul cr.cr_r x

let ring_neg_xy_is_x_times_neg_y (#t: Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (-(x * y) = x * (-y))
  = priv_neg_mul_r cr x y

let ring_neg_xy_is_neg_x_times_y (#t: Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (-(x * y) = (-x) * y)
  = priv_neg_mul_l cr.cr_r x y;
    cr.cr_r.r_add.acg_eq.symmetry (cr.cr_r.mul (cr.cr_r.r_add.neg x) y)
                                   (cr.cr_r.r_add.neg (cr.cr_r.mul x y))
#pop-options

(* `semiring_of_cr_local` deleted: the new tower has no `semiring` class.
   Every former consumer takes `{| ring t |}` (or `{| commutative_ring t |}`)
   directly. Calls that used `#(cr.cr_r)` need to be
   rewritten to use the consumer API's actual instance, typically a
   plain `{| cr.cr_r |}` resolution. *)


(* -------------------------------------------------------------------- *)
(*  Product along a permutation: ∏_{i=0..n-1} M(i, p.fwd i).            *)
(* -------------------------------------------------------------------- *)
let perm_product (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (p: permutation n) : t
  = prod_range
      (fun (i: nat) -> if i < n then m (i <: fin n) (p.fwd (i <: fin n)) else one)
      0 n

let perm_product_unfold (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (perm_product m p ==
           prod_range (fun (k: nat) -> if k < n then m (k <: fin n) (p.fwd (k <: fin n)) else one) 0 n)
  = ()

(* -------------------------------------------------------------------- *)
(*  Signed Leibniz summand.                                             *)
(* -------------------------------------------------------------------- *)
let leibniz_term (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (p: permutation n) : t
  = if parity p
    then perm_product m p
    else (-(perm_product m p))

(* -------------------------------------------------------------------- *)
(*  Determinant.                                                         *)
(* -------------------------------------------------------------------- *)
let det (#t: Type) {| cr: commutative_ring t |} (#n: nat) (m: square_matrix t n) : t
  = sum_over_perms n (leibniz_term m)

let det_unfold (#t: Type) {| cr: commutative_ring t |} (#n: nat) (m: square_matrix t n)
  : Lemma (det m == sum_over_perms n (leibniz_term m))
  = ()

(* -------------------------------------------------------------------- *)
(*  Helpers on prod_range needed by det_identity.                       *)
(* -------------------------------------------------------------------- *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec prod_range_const_one (#t: Type) {| cr: commutative_ring t |} (lo hi: nat)
  : Lemma (ensures prod_range #t #(cr.cr_r)
                   (fun _ -> one #t #(cr.cr_r)) lo hi = one #t #(cr.cr_r))
          (decreases (hi - lo))
  = H.elim_equatable_laws t ();
    if hi <= lo then begin
      prod_range_empty #t #(cr.cr_r) (fun _ -> one #t #(cr.cr_r)) lo hi;
      H.leibniz_to_eq (prod_range #t #(cr.cr_r) (fun _ -> one #t #(cr.cr_r)) lo hi)
                      (one #t #(cr.cr_r))
    end else begin
      prod_range_unfold_left #t #(cr.cr_r) (fun _ -> one #t #(cr.cr_r)) lo hi;
      prod_range_const_one #t #cr (nat_succ lo) hi;
      let pr_tail : t = prod_range #t #(cr.cr_r) (fun _ -> one #t #(cr.cr_r)) (nat_succ lo) hi in
      let one_t : t = one #t #(cr.cr_r) in
      let step : t = one_t * pr_tail in
      H.leibniz_to_eq (prod_range #t #(cr.cr_r) (fun _ -> one #t #(cr.cr_r)) lo hi) step;
      reflexivity one_t;
      mul_congruence one_t pr_tail one_t one_t;
      H.one_mul_x one_t;
      H.trans3 (prod_range #t #(cr.cr_r) (fun _ -> one #t #(cr.cr_r)) lo hi)
               step (one_t * one_t) one_t
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec prod_range_zero_factor (#t: Type) {| cr: commutative_ring t |}
  (f: nat -> t) (lo hi: nat) (k: nat)
  : Lemma (requires lo <= k /\ k < hi /\ f k = zero)
          (ensures  prod_range f lo hi = zero)
          (decreases (hi - lo))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    prod_range_unfold_left #t #(cr.cr_r) f lo hi;
    if k = lo then begin
      mul_congruence (f lo) (prod_range #t #(cr.cr_r) f (nat_succ lo) hi)
                     (zero #t) (prod_range #t #(cr.cr_r) f (nat_succ lo) hi);
      ring_zero_is_left_absorber (prod_range #t #(cr.cr_r) f (nat_succ lo) hi);
      transitivity (f lo * prod_range #t #(cr.cr_r) f (nat_succ lo) hi)
                   (zero * prod_range #t #(cr.cr_r) f (nat_succ lo) hi)
                   (zero #t)
    end else begin
      prod_range_zero_factor f (nat_succ lo) hi k;
      mul_congruence (f lo) (prod_range #t #(cr.cr_r) f (nat_succ lo) hi)
                     (f lo) (zero #t);
      ring_zero_is_right_absorber (f lo);
      transitivity (f lo * prod_range #t #(cr.cr_r) f (nat_succ lo) hi)
                   (f lo * zero)
                   (zero #t)
    end
#pop-options
(* -------------------------------------------------------------------- *)
(*  det (identity matrix) = one                                          *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let perm_product_id_identity (#t: Type) {| cr: commutative_ring t |} (n: nat)
  : Lemma (perm_product (id_matrix #t n) (identity n) = one)
  = H.elim_equatable_laws t ();
    let const_one : nat -> t = fun _ -> one #t #(cr.cr_r) in
    let aux (k: nat) : Lemma (0 <= k /\ k < n ==>
        (if k < n
         then id_matrix #t n (k <: fin n) ((identity n).fwd (k <: fin n))
         else one #t #(cr.cr_r)) = const_one k)
      = if k < n then begin
          let i : fin n = k in
          identity_fwd n i;
          id_matrix_diag #t n i;
          reflexivity (one #t #(cr.cr_r))
        end
    in
    Classical.forall_intro aux;
    prod_range_congruence #t #(cr.cr_r)
      (fun (i: nat) ->
         if i < n
         then id_matrix #t n (i <: fin n) ((identity n).fwd (i <: fin n))
         else one #t #(cr.cr_r))
      const_one 0 n (fun _ -> ());
    prod_range_const_one #t #cr 0 n;
    perm_product_unfold (id_matrix #t n) (identity n);
    let pp = perm_product (id_matrix #t n) (identity n) in
    let pr_body = prod_range #t #(cr.cr_r)
      (fun (k: nat) ->
         if k < n
         then id_matrix #t n (k <: fin n) ((identity n).fwd (k <: fin n))
         else one #t #(cr.cr_r))
      0 n in
    let pr_one = prod_range #t #(cr.cr_r) const_one 0 n in
    H.leibniz_then_eq pp pr_body pr_one;
    transitivity pp pr_one (one #t #(cr.cr_r))
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let perm_product_id_nonidentity (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (p: permutation n)
  : Lemma (requires ~(perm_eq p (identity n)))
          (ensures  perm_product (id_matrix #t n) p = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let phi (i: fin n) : prop = ~(p.fwd i == i) in
    let helper (assume_not : (i: fin n -> Lemma (~(phi i)))) : Lemma False
      = let pwd (i: fin n) : Lemma (p.fwd i == (identity n).fwd i)
          = assume_not i; identity_fwd n i in
        perm_eq_intro p (identity n) pwd;
        assert False
    in
    Classical.exists_intro_not_all_not #(fin n) #phi helper;
    eliminate exists (i: fin n). phi i
      returns perm_product (id_matrix #t n) p = zero with _.
      begin
        let k : nat = i in
        id_matrix_off #t n i (p.fwd i);
        reflexivity (zero #t);
        prod_range_zero_factor #t #cr
          (fun (j: nat) ->
            if j < n
            then id_matrix #t n (j <: fin n) (p.fwd (j <: fin n))
            else one #t #(cr.cr_r))
          0 n k;
        perm_product_unfold (id_matrix #t n) p;
        let pp = perm_product (id_matrix #t n) p in
        let pr_body = prod_range #t #(cr.cr_r)
          (fun (j: nat) ->
            if j < n
            then id_matrix #t n (j <: fin n) (p.fwd (j <: fin n))
            else one #t #(cr.cr_r))
          0 n in
        H.leibniz_then_eq pp pr_body (zero #t #(cr.cr_r.r_add))
      end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let perm_product_id_respects_perm_eq (#t: Type) {| cr: commutative_ring t |} (n: nat)
  (p q: permutation n)
  : Lemma (requires perm_eq p q)
          (ensures  perm_product (id_matrix #t n) p = perm_product (id_matrix #t n) q)
  = H.elim_equatable_laws t ();
    let aux (k: nat) : Lemma (0 <= k /\ k < n ==>
        (if k < n then id_matrix #t n (k <: fin n) (p.fwd (k <: fin n)) else one #t #(cr.cr_r))
      = (if k < n then id_matrix #t n (k <: fin n) (q.fwd (k <: fin n)) else one #t #(cr.cr_r)))
      = if k < n then begin
          let i : fin n = k in
          perm_eq_elim p q i;
          reflexivity (id_matrix #t n (k <: fin n) (p.fwd (k <: fin n)))
        end
    in
    Classical.forall_intro aux;
    prod_range_congruence #t #(cr.cr_r)
      (fun (i: nat) ->
        if i < n then id_matrix #t n (i <: fin n) (p.fwd (i <: fin n)) else one #t #(cr.cr_r))
      (fun (i: nat) ->
        if i < n then id_matrix #t n (i <: fin n) (q.fwd (i <: fin n)) else one #t #(cr.cr_r))
      0 n (fun _ -> ());
    perm_product_unfold (id_matrix #t n) p;
    perm_product_unfold (id_matrix #t n) q;
    let pp = perm_product (id_matrix #t n) p in
    let qq = perm_product (id_matrix #t n) q in
    let pr_p = prod_range #t #(cr.cr_r)
      (fun (k: nat) ->
        if k < n then id_matrix #t n (k <: fin n) (p.fwd (k <: fin n)) else one #t #(cr.cr_r))
      0 n in
    let pr_q = prod_range #t #(cr.cr_r)
      (fun (k: nat) ->
        if k < n then id_matrix #t n (k <: fin n) (q.fwd (k <: fin n)) else one #t #(cr.cr_r))
      0 n in
    H.leibniz_then_eq pp pr_p pr_q;
    symmetry qq pr_q;
    transitivity pp pr_q qq
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let leibniz_term_id_respects_perm_eq (#t: Type) {| cr: commutative_ring t |} (n: nat)
  : Lemma (respects_perm_eq #t (leibniz_term (id_matrix #t n)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let f = leibniz_term (id_matrix #t n) in
    let aux (p q: permutation n) : Lemma (perm_eq p q ==> f p = f q)
      = if FStar.IndefiniteDescription.strong_excluded_middle (perm_eq p q) then begin
          parity_perm_eq_invariant p q;
          perm_product_id_respects_perm_eq #t #cr n p q;
          if parity p then reflexivity (f p)
          else begin
            let pp = perm_product (id_matrix #t n) p in
            let qq = perm_product (id_matrix #t n) q in
            assert (pp = qq);
            neg_congruence pp qq;
            reflexivity (f p)
          end
        end
    in
    Classical.forall_intro_2 aux;
    respects_perm_eq_intro f (fun _ _ -> ())
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_identity (#t: Type) {| cr: commutative_ring t |} (n: nat)
  : Lemma (det (id_matrix #t n) = one)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let f = leibniz_term (id_matrix #t n) in
    let p0 = identity n in
    leibniz_term_id_respects_perm_eq #t #cr n;
    let vanish (q: permutation n) : Lemma (~(perm_eq p0 q) ==> f q = zero)
      = if FStar.IndefiniteDescription.strong_excluded_middle (~(perm_eq p0 q)) then begin
          let not_q_p0 () : Lemma (requires perm_eq q p0) (ensures False)
            = perm_eq_sym_local q p0;
              assert (perm_eq p0 q)
          in
          Classical.move_requires not_q_p0 ();
          perm_product_id_nonidentity #t #cr #n q;
          parity_identity n;
          if parity q then reflexivity (f q)
          else begin
            let pp = perm_product (id_matrix #t n) q in
            assert (pp = zero #t);
            neg_zero_lem #t #cr;
            neg_congruence pp (zero #t);
            transitivity (-(pp)) (-(zero #t)) (zero #t);
            reflexivity (f q)
          end
        end
    in
    Classical.forall_intro vanish;
    (* Re-prove respects_perm_eq in the current TC context *)
    let re_aux (p q: permutation n) : Lemma (perm_eq p q ==> f p = f q)
      = if FStar.IndefiniteDescription.strong_excluded_middle (perm_eq p q) then begin
          parity_perm_eq_invariant p q;
          perm_product_id_respects_perm_eq #t #cr n p q;
          if parity p then reflexivity (f p)
          else neg_congruence (perm_product (id_matrix #t n) p)
                              (perm_product (id_matrix #t n) q)
        end
    in
    Classical.forall_intro_2 re_aux;
    respects_perm_eq_intro f (fun _ _ -> ());
    sum_over_perms_single n f p0 (fun _ -> ());
    parity_identity n;
    perm_product_id_identity #t #cr n;
    det_unfold (id_matrix #t n);
    assert (parity p0 == true);
    assert (f p0 == perm_product (id_matrix #t n) p0);
    transitivity (det (id_matrix #t n)) (sum_over_perms n f) (f p0);
    transitivity (det (id_matrix #t n)) (f p0) (perm_product (id_matrix #t n) p0);
    transitivity (det (id_matrix #t n)) (perm_product (id_matrix #t n) p0) (one #t)
#pop-options
(* -------------------------------------------------------------------- *)
(*  det of a matrix with a zero row is zero.                            *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let perm_product_zero_row
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (k: fin n)
  (zrow: squash (forall (j: fin n). m k j = zero))
  (p: permutation n)
  : Lemma (perm_product m p = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let body : nat -> t =
      fun (i: nat) -> if i < n then m (i <: fin n) (p.fwd (i <: fin n)) else one in
    assert (body k == m k (p.fwd k));
    assert (m k (p.fwd k) = zero);
    prod_range_zero_factor #t #cr body 0 n k;
    perm_product_unfold m p
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_zero_row
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (k: fin n)
  : Lemma (requires forall (j: fin n). m k j = zero)
          (ensures  det m = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let zrow : squash (forall (j: fin n). m k j = zero) = () in
    let f = leibniz_term m in
    let term_zero (p: permutation n) : Lemma (f p = zero)
      = perm_product_zero_row #t #cr #n m k zrow p;
        if parity p then reflexivity (f p)
        else begin
          let pp = perm_product m p in
          assert (pp = zero #t);
          neg_zero_lem #t #cr;
          neg_congruence pp (zero #t);
          transitivity (-(pp)) (-(zero #t)) (zero #t)
        end
    in
    Classical.forall_intro term_zero;
    assert (forall (p: permutation n). f p = zero);
    sum_over_perms_all_zero n f (fun _ -> ());
    det_unfold m;
    transitivity (det m) (sum_over_perms n f) (zero #t)
#pop-options

(* -------------------------------------------------------------------- *)
(*  det(M^T) = det(M).                                                  *)
(* -------------------------------------------------------------------- *)

(* perm_product respects perm_eq in its permutation argument. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let perm_product_respects_perm_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (p q: permutation n)
  : Lemma (requires perm_eq p q)
          (ensures  perm_product m p = perm_product m q)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bp : nat -> t =
      fun i -> if i < n then m (i <: fin n) (p.fwd (i <: fin n)) else one in
    let bq : nat -> t =
      fun i -> if i < n then m (i <: fin n) (q.fwd (i <: fin n)) else one in
    let h (k: nat) : Lemma (requires 0 <= k /\ k < n) (ensures bp k = bq k)
      = perm_eq_elim p q (k <: fin n);
        reflexivity (m (k <: fin n) (p.fwd (k <: fin n)))
    in
    Classical.forall_intro (Classical.move_requires h);
    prod_range_congruence #t #(cr.cr_r) bp bq 0 n (fun _ -> ());
    perm_product_unfold m p;
    perm_product_unfold m q
#pop-options

(* leibniz_term respects perm_eq in its permutation argument. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let leibniz_term_respects_perm_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n)
  : Lemma (respects_perm_eq #t (leibniz_term m))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let f = leibniz_term m in
    let aux (p q: permutation n) : Lemma (requires perm_eq p q) (ensures f p = f q)
      = perm_product_respects_perm_eq m p q;
        parity_perm_eq_invariant p q;
        if parity p then ()
        else neg_congruence (perm_product m p) (perm_product m q)
    in
    Classical.forall_intro_2 (fun p q -> Classical.move_requires (aux p) q);
    respects_perm_eq_intro f (fun _ _ -> ())
#pop-options

(* perm_product (transpose m) (inverse p) = perm_product m p, in any comm_ring. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let perm_product_transpose_inverse
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (perm_product (transpose m) (inverse p) = perm_product m p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let bigF : nat -> t =
      fun (k: nat) -> if k < n then m (k <: fin n) (p.fwd (k <: fin n)) else one in
    let bigG : nat -> t =
      fun (k: nat) -> if k < n
               then (transpose m) (k <: fin n) ((inverse p).fwd (k <: fin n))
               else one in
    let body_p : nat -> t =
      fun (k: nat) -> if k < n then bigF ((inverse p).fwd (k <: fin n)) else one in
    (* Pointwise bigG = body_p on [0, n). *)
    let hGH (k: nat) : Lemma (requires 0 <= k /\ k < n) (ensures bigG k = body_p k)
      = let kf : fin n = k <: fin n in
        inverse_fwd p kf;
        let j : fin n = (inverse p).fwd kf in
        p.fwd_bwd_id kf;
        reflexivity (m j (p.fwd j))
    in
    Classical.forall_intro (Classical.move_requires hGH);
    prod_range_congruence #t #(cr.cr_r) bigG body_p 0 n (fun _ -> ());
    (* prod_range body_p 0 n = prod_range bigF 0 n via perm_invariance. *)
    let bp_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==> body_p k = bigF ((inverse p).fwd (k <: fin n)))
      = if 0 <= k && k < n then
          reflexivity (bigF ((inverse p).fwd (k <: fin n))) in
    Classical.forall_intro bp_hyp;
    let bi_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==> bigF k = bigF k)
      = if 0 <= k && k < n then reflexivity (bigF k) in
    Classical.forall_intro bi_hyp;
    prod_range_perm_invariance_fn #t #cr #n bigF body_p bigF (inverse p)
      (fun _ -> ()) (fun _ -> ());
    perm_product_unfold (transpose m) (inverse p);
    perm_product_unfold m p;
    transitivity (prod_range #t #(cr.cr_r) bigG 0 n)
                 (prod_range #t #(cr.cr_r) body_p 0 n)
                 (prod_range #t #(cr.cr_r) bigF 0 n)
#pop-options

(* leibniz_term (transpose m) (inverse p) = leibniz_term m p. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let leibniz_transpose_inverse_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (leibniz_term (transpose m) (inverse p) = leibniz_term m p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    parity_inverse p;
    perm_product_transpose_inverse #t #cr #n m p;
    if parity p then ()
    else neg_congruence (perm_product (transpose m) (inverse p)) (perm_product m p)
#pop-options

(* Headline: det(M^T) = det(M) over any commutative ring. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let det_transpose
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n)
  : Lemma (det (transpose m) = det m)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let f = leibniz_term (transpose m) in
    let g = leibniz_term m in
    leibniz_term_respects_perm_eq #t #cr #n (transpose m);
    leibniz_term_respects_perm_eq #t #cr #n m;
    (* sum_over_perms n f = sum_over_perms n (fcomp f inverse) *)
    sum_over_perms_reindex_inverse n f;
    (* fcomp f inverse is pointwise equal to g *)
    let pointwise (s: permutation n) : Lemma (fcomp f inverse s = g s)
      = fcomp_unfold f inverse s;
        leibniz_transpose_inverse_eq #t #cr #n m s in
    Classical.forall_intro pointwise;
    sum_over_perms_congruence n (fcomp f inverse) g (fun _ -> ());
    det_unfold (transpose m);
    det_unfold m;
    transitivity (det (transpose m))
                 (sum_over_perms n f)
                 (sum_over_perms n (fcomp f inverse));
    transitivity (det (transpose m))
                 (sum_over_perms n (fcomp f inverse))
                 (sum_over_perms n g);
    transitivity (det (transpose m)) (sum_over_perms n g) (det m)
#pop-options
(* -------------------------------------------------------------------- *)
(*  Row swap and alternating property.                                  *)
(*  row_swap m i j is m with rows i and j swapped.                      *)
(*  Headline: det(row_swap m i j) = -det(m) when i <> j.                 *)
(* -------------------------------------------------------------------- *)
let row_swap (#t: Type) (#n: nat) (m: square_matrix t n) (i j: fin n)
  : square_matrix t n
  = fun (k: fin n) (l: fin n) -> m ((transposition n i j).fwd k) l

(* Key calculation: perm_product (row_swap m i j) p = perm_product m (compose p σ),
   where σ = transposition n i j. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let perm_product_row_swap
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n) (p: permutation n)
  : Lemma (perm_product (row_swap m i j) p =
           perm_product m (compose p (transposition n i j)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sigma = transposition n i j in
    let q = compose p sigma in
    let lhs_body : nat -> t =
      fun (k: nat) -> if k < n
                  then (row_swap m i j) (k <: fin n) (p.fwd (k <: fin n))
                  else one in
    let rhs_body : nat -> t =
      fun (k: nat) -> if k < n
                  then m (k <: fin n) (q.fwd (k <: fin n))
                  else one in
    let f : nat -> t =
      fun (k: nat) -> if k < n
                  then m (k <: fin n) (p.fwd ((sigma.fwd (k <: fin n)) <: fin n))
                  else one in
    transposition_self_inverse n i j;
    let body_p_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==>
       lhs_body k = f (sigma.fwd (k <: fin n)))
      = if 0 <= k && k < n then begin
          let kf : fin n = k <: fin n in
          let sk : fin n = sigma.fwd kf in
          compose_fwd sigma sigma kf;
          perm_eq_elim (compose sigma sigma) (identity n) kf;
          identity_fwd n kf;
          reflexivity (m kf (p.fwd kf))
        end in
    Classical.forall_intro body_p_hyp;
    let body_id_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==> rhs_body k = f k)
      = if 0 <= k && k < n then begin
          let kf : fin n = k <: fin n in
          compose_fwd p sigma kf;
          reflexivity (m kf (p.fwd (sigma.fwd kf)))
        end in
    Classical.forall_intro body_id_hyp;
    prod_range_perm_invariance_fn #t #cr #n f lhs_body rhs_body sigma
      (fun _ -> ()) (fun _ -> ());
    perm_product_unfold (row_swap m i j) p;
    perm_product_unfold m q
#pop-options

(* leibniz_term (row_swap m i j) p = -(leibniz_term m (compose p σ)) when i <> j. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let leibniz_term_row_swap
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n) (p: permutation n)
  : Lemma (requires ~(i == j))
          (ensures  leibniz_term (row_swap m i j) p =
                    -(leibniz_term m (compose p (transposition n i j))))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sigma = transposition n i j in
    let q = compose p sigma in
    perm_product_row_swap #t #cr #n m i j p;
    parity_transposition n i j;
    sign_homomorphism p sigma;
    let pp1 = perm_product (row_swap m i j) p in
    let pp2 = perm_product m q in
    if parity p
    then begin
      (* lhs = pp1, rhs = -(-(pp2)), need pp1 = pp2 = -(-(pp2)) *)
      double_negation_lemma pp2;
      symmetry (-(-pp2)) pp2;
      transitivity pp1 pp2 (-(-pp2))
    end else begin
      (* lhs = -(pp1), rhs = -(pp2), need -(pp1) = -(pp2) *)
      neg_congruence pp1 pp2
    end
#pop-options

(* Headline: det(row_swap m i j) = -det(m) when i <> j. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let det_row_swap
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires ~(i == j))
          (ensures  det (row_swap m i j) = -(det m))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sigma = transposition n i j in
    let f = leibniz_term (row_swap m i j) in
    let g = leibniz_term m in
    leibniz_term_respects_perm_eq #t #cr #n m;
    (* By reindexing: sum_over_perms n g = sum_over_perms n (fcomp g (flip compose sigma)). *)
    sum_over_perms_reindex n g sigma;
    (* By leibniz_term_row_swap: f s = -(g (compose s sigma)) for every s. *)
    let pointwise (s: permutation n) : Lemma (f s = -(g (compose s sigma)))
      = leibniz_term_row_swap #t #cr #n m i j s in
    Classical.forall_intro pointwise;
    (* Use the named variant from Permutation.Sum.fsti — proven against
       add_comm_group directly, avoiding the acg_of_ring lambda diamond. *)
    sum_over_perms_neg_named #t #(acg_of_ring_local t cr.cr_r) n f
      (fcomp g (flip compose sigma)) (fun _ -> ());
    (* Now: sum n f = -(sum n (fcomp g (flip compose sigma))) *)
    (* But sum n (fcomp g (flip compose sigma)) = sum n g by reindex *)
    det_unfold (row_swap m i j);
    det_unfold m;
    symmetry (sum_over_perms n g) (sum_over_perms n (fcomp g (flip compose sigma)));
    neg_congruence (sum_over_perms n (fcomp g (flip compose sigma)))
                   (sum_over_perms n g);
    neg_congruence (sum_over_perms n g) (det m);
    transitivity (det (row_swap m i j))
                 (sum_over_perms n f)
                 (-(sum_over_perms n (fcomp g (flip compose sigma))));
    transitivity (det (row_swap m i j))
                 (-(sum_over_perms n (fcomp g (flip compose sigma))))
                 (-(sum_over_perms n g));
    transitivity (det (row_swap m i j))
                 (-(sum_over_perms n g))
                 (-(det m))
#pop-options

(* ==================================================================== *)
(*  ELEMENTARY MATRICES                                                  *)
(*                                                                      *)
(*  Three flavours, each an n x n matrix:                                *)
(*    e_swap_mat n i j     = identity with rows i, j swapped             *)
(*    e_scale_mat n i c    = identity with the (i,i) entry replaced by c *)
(*    e_add_mat n i j c    = identity plus c at off-diagonal slot (i,j)  *)
(*                           (i <> j ; preserves triangularity)          *)
(* ==================================================================== *)

let e_swap_mat (#t: Type) {| ring t |}
  (n: nat) (i j: fin n) : square_matrix t n
  = row_swap (id_matrix #t n) i j

let e_scale_mat (#t: Type) {| ring t |}
  (n: nat) (i: fin n) (c: t) : square_matrix t n
  = fun a b -> if a = i && b = i then c
               else if a = b then one
               else zero

let e_add_mat (#t: Type) {| ring t |}
  (n: nat) (i j: fin n) (c: t) : square_matrix t n
  = fun a b -> if a = b then one
               else if a = i && b = j then c
               else zero

(* det (E_swap n i j) = -(one). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let det_e_swap (#t: Type) {| cr: commutative_ring t |} (n: nat) (i j: fin n)
  : Lemma (requires ~(i == j))
          (ensures  det (e_swap_mat #t #_ n i j) = -(one #t))
  = let r : ring t = cr.cr_r in
    let m0 = id_matrix #t n in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    det_row_swap #t #cr #n m0 i j;
    det_identity #t #cr n;
    neg_congruence_lem (det m0) (one #t);
    assert (det (row_swap m0 i j) = -(det m0));
    assert (det m0 = one #t);
    assert (-(det m0) = -(one #t));
    ()
#pop-options

(* perm_product is zero whenever one of its factors vanishes. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let perm_product_has_zero_factor
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (p: permutation n) (k: fin n)
  : Lemma (requires m k (p.fwd k) = zero)
          (ensures  perm_product m p = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let body : nat -> t
      = fun (j: nat) ->
          if j < n then m (j <: fin n) (p.fwd (j <: fin n)) else one in
    let kk : nat = k in
    assert (body kk == m k (p.fwd k));
    reflexivity (m k (p.fwd k));
    transitivity (body kk) (m k (p.fwd k)) (zero #t);
    prod_range_zero_factor #t body 0 n kk;
    perm_product_unfold m p;
    reflexivity (perm_product m p);
    transitivity (perm_product m p) (prod_range body 0 n) (zero #t)
#pop-options

(* prod_range with all-ones except at one position equals the value at that position. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let prod_range_one_except_at
  (#t: Type) {| cr: commutative_ring t |} (f: nat -> t) (lo hi: nat) (i: nat)
  : Lemma (requires lo <= i /\ i < hi /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> f k = one))
          (ensures  prod_range f lo hi = f i)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let const_one : nat -> t = fun _ -> one in
    let aux_left (k: nat) : Lemma (lo <= k /\ k < i ==> f k = const_one k)
      = if lo <= k && k < i then begin
          assert (f k = one);
          reflexivity (one #t)
        end
    in
    let aux_right (k: nat) : Lemma (nat_succ i <= k /\ k < hi ==> f k = const_one k)
      = if nat_succ i <= k && k < hi then begin
          assert (f k = one);
          reflexivity (one #t)
        end
    in
    Classical.forall_intro aux_left;
    Classical.forall_intro aux_right;
    prod_range_split f lo i hi;
    prod_range_unfold_left f i hi;
    prod_range_congruence #t f const_one lo i (fun _ -> ());
    prod_range_congruence #t f const_one (nat_succ i) hi (fun _ -> ());
    prod_range_const_one #t #cr lo i;
    prod_range_const_one #t #cr (nat_succ i) hi;
    let p_left = prod_range f lo i in
    let p_right_tail = prod_range f (nat_succ i) hi in
    let p_right = prod_range f i hi in
    trans_lemma [ p_left; prod_range const_one lo i; one #t ];
    trans_lemma [ p_right_tail; prod_range const_one (nat_succ i) hi; one #t ];
    reflexivity (f i);
    mul_congruence (f i) p_right_tail (f i) (one #t);
    H.x_mul_one (f i);
    prod_range_unfold_left f i hi;
    assert (p_right = f i * p_right_tail);
    trans_lemma [ p_right; f i * p_right_tail; f i * one; f i ];
    mul_congruence p_left p_right (one #t) (f i);
    H.one_mul_x (f i);
    assert (prod_range f lo hi = p_left * p_right);
    trans_lemma [ prod_range f lo hi; p_left * p_right; one * f i; f i ]
#pop-options

(* det (E_scale n i c) = c. *)
(* Helper: perm_product is one when all diagonal entries m(k, p.fwd k) = one. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let perm_product_all_ones
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (requires forall (k: fin n). m k (p.fwd k) = one)
          (ensures  perm_product m p = one)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let body : nat -> t
      = fun (j: nat) -> if j < n then m (j <: fin n) (p.fwd (j <: fin n)) else one in
    let const_one : nat -> t = fun _ -> one in
    let aux (k: nat) : Lemma (0 <= k /\ k < n ==> body k = const_one k)
      = if k < n then reflexivity (one #t)
    in
    Classical.forall_intro aux;
    prod_range_congruence #t body const_one 0 n (fun _ -> ());
    prod_range_const_one #t #cr 0 n;
    perm_product_unfold m p;
    transitivity (perm_product m p) (prod_range body 0 n) (prod_range const_one 0 n);
    transitivity (perm_product m p) (prod_range const_one 0 n) (one #t)
#pop-options

(* Helper: perm_product of a diagonal-like matrix under any permutation equals
   the value at position i when all other diagonal entries are one. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let perm_product_diag_matrix_identity
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (p: permutation n) (i: fin n) (c: t)
  : Lemma (requires (forall (k: fin n). k =!= i ==> m k (p.fwd k) = one) /\
                    m i (p.fwd i) = c)
          (ensures  perm_product m p = c)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let body : nat -> t
      = fun (j: nat) -> if j < n then m (j <: fin n) (p.fwd (j <: fin n)) else one in
    let aux_diag (k: nat) : Lemma (0 <= k /\ k < n /\ k <> (i <: nat) ==> body k = one)
      = if k < n && k <> (i <: nat) then begin
          let kk : fin n = k in
          reflexivity (one #t)
        end
    in
    Classical.forall_intro aux_diag;
    let aux_at_i : unit -> Lemma (body (i <: nat) = c) = fun () ->
      reflexivity c
    in
    aux_at_i ();
    prod_range_one_except_at #t #cr body 0 n (i <: nat);
    transitivity (prod_range body 0 n) (body (i <: nat)) c;
    perm_product_unfold m p;
    transitivity (perm_product m p) (prod_range body 0 n) c
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_e_scale (#t: Type) {| cr: commutative_ring t |} (n: nat) (i: fin n) (c: t)
  : Lemma (det (e_scale_mat #t #_ n i c) = c)
  = let r : ring t = cr.cr_r in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let m = e_scale_mat #t #_ n i c in
    let f = leibniz_term #t #cr #n m in
    let p0 = identity n in
    leibniz_term_respects_perm_eq #t #cr #n m;
    let vanish (q: permutation n) : Lemma (~(perm_eq p0 q) ==> f q = zero)
      = if FStar.IndefiniteDescription.strong_excluded_middle (~(perm_eq p0 q)) then begin
          let phi (k: fin n) : prop = ~(q.fwd k == k) in
          let helper (assume_not : (k: fin n -> Lemma (~(phi k)))) : Lemma False
            = let pwd (k: fin n) : Lemma (p0.fwd k == q.fwd k)
                = identity_fwd n k; assume_not k in
              perm_eq_intro p0 q pwd
          in
          Classical.exists_intro_not_all_not #(fin n) #phi helper;
          eliminate exists (k: fin n). phi k
            returns f q = zero with _.
            begin
              assert (~(k == q.fwd k));
              assert (m k (q.fwd k) == zero #t);
              reflexivity (zero #t);
              perm_product_has_zero_factor #t #cr #n m q k;
              let pp = perm_product m q in
              if parity q then begin
                reflexivity (f q);
                transitivity (f q) pp (zero #t)
              end else begin
                neg_zero_lem #t #cr;
                neg_congruence_lem pp (zero #t);
                reflexivity (f q);
                transitivity (f q) (-pp) ((-(zero #t)));
                transitivity (f q) (-(zero #t)) (zero #t)
              end
            end
        end
    in
    Classical.forall_intro vanish;
    sum_over_perms_single #t #(r.r_add) n f p0 (fun _ -> ());
    parity_identity n;
    (* prove preconditions for perm_product_diag_matrix_identity *)
    let aux_diag (k: fin n) : Lemma (k =!= i ==> m k ((identity n).fwd k) = one)
      = if k <> i then begin
          identity_fwd n k;
          assert ((identity n).fwd k == k);
          assert (m k k == one #t);
          reflexivity (one #t)
        end
    in
    Classical.forall_intro (Classical.move_requires aux_diag);
    identity_fwd n i;
    assert (m i ((identity n).fwd i) == c);
    reflexivity c;
    perm_product_diag_matrix_identity #t #cr #n m p0 i c;
    transitivity (f p0) (perm_product m p0) c;
    det_unfold m;
    transitivity (det m) (sum_over_perms n f) (f p0);
    transitivity (det m) (f p0) c
#pop-options

(* det (E_add n i j c) = one, i <> j. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_e_add (#t: Type) {| cr: commutative_ring t |} (n: nat) (i j: fin n) (c: t)
  : Lemma (requires ~(i == j))
          (ensures  det (e_add_mat #t #_ n i j c) = one)
  = let r : ring t = cr.cr_r in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let m = e_add_mat #t #_ n i j c in
    let f = leibniz_term #t #cr #n m in
    let p0 = identity n in
    leibniz_term_respects_perm_eq #t #cr #n m;
    let vanish (q: permutation n) : Lemma (~(perm_eq p0 q) ==> f q = zero)
      = if FStar.IndefiniteDescription.strong_excluded_middle (~(perm_eq p0 q)) then begin
          let phi (k: fin n) : prop = m k (q.fwd k) = zero in
          let helper (assume_not : (k: fin n -> Lemma (~(phi k)))) : Lemma False
            = Classical.forall_intro assume_not;
              let cls (k: fin n) : Lemma (q.fwd k == k \/ ((k <: nat) == (i <: nat) /\ q.fwd k == j))
                = if (k = q.fwd k) then ()
                  else if (k = i && q.fwd k = j) then ()
                  else begin
                    assert (m k (q.fwd k) == zero #t);
                    reflexivity (zero #t);
                    assert (~(m k (q.fwd k) = zero));
                    ()
                  end
              in
              Classical.forall_intro cls;
              assert (q.fwd j == j \/ ((j <: nat) == (i <: nat) /\ q.fwd j == j));
              assert (q.fwd j == j);
              assert (q.fwd i == i \/ q.fwd i == j);
              if q.fwd i = j then begin
                fwd_injective q i j;
                assert (i == j);
                ()
              end else begin
                assert (q.fwd i == i);
                let cls2 (k: fin n) : Lemma (q.fwd k == k)
                  = if (k <: nat) = (i <: nat) then ()
                    else begin
                      let _ = cls k in
                      assert (q.fwd k == k \/ ((k <: nat) == (i <: nat) /\ q.fwd k == j));
                      ()
                    end
                in
                Classical.forall_intro cls2;
                let pwd (k: fin n) : Lemma (p0.fwd k == q.fwd k)
                  = identity_fwd n k; cls2 k in
                perm_eq_intro p0 q pwd;
                ()
              end
          in
          Classical.exists_intro_not_all_not #(fin n) #phi helper;
          eliminate exists (k: fin n). phi k
            returns f q = zero with _.
            begin
              perm_product_has_zero_factor #t #cr #n m q k;
              let pp = perm_product m q in
              if parity q then begin
                reflexivity (f q);
                transitivity (f q) pp (zero #t)
              end else begin
                neg_zero_lem #t #cr;
                neg_congruence_lem pp (zero #t);
                reflexivity (f q);
                transitivity (f q) (-pp) ((-(zero #t)));
                transitivity (f q) (-(zero #t)) (zero #t)
              end
            end
        end
    in
    Classical.forall_intro vanish;
    sum_over_perms_single #t #(r.r_add) n f p0 (fun _ -> ());
    parity_identity n;
    let body : nat -> t
      = fun (jj: nat) -> if jj < n then m (jj <: fin n) (p0.fwd (jj <: fin n)) else one in
    let const_one : nat -> t = fun _ -> one in
    let aux_one (k: nat) : Lemma (0 <= k /\ k < n ==> body k = const_one k)
      = if k < n then begin
          let kk : fin n = k in
          identity_fwd n kk;
          assert (p0.fwd kk == kk);
          assert (m kk kk == one #t);
          reflexivity (one #t);
          reflexivity (body k)
        end
    in
    Classical.forall_intro aux_one;
    (* All diagonal entries are one, so perm_product m p0 = one *)
    let aux_pp (k: fin n) : Lemma (m k (p0.fwd k) = one)
      = identity_fwd n k;
        assert (p0.fwd k == k);
        assert (m k k == one #t);
        reflexivity (one #t)
    in
    Classical.forall_intro aux_pp;
    perm_product_all_ones #t #cr #n m p0;
    parity_identity n;
    transitivity (f p0) (perm_product m p0) (one #t);
    det_unfold m;
    transitivity (det m) (sum_over_perms n f) (f p0);
    transitivity (det m) (f p0) (one #t)
#pop-options

(* ==================================================================== *)
(*  Row operations as data                                              *)
(* ==================================================================== *)
(* Multiply row i by scalar c. *)
let row_scale (#t: Type) {| ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (c: t) : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality a i then c * m a b else m a b

(* Add c times row j to row i (i <> j). *)
let row_add (#t: Type) {| ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n) (c: t) : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality a i then m a b + c * m j b else m a b

(* ==================================================================== *)
(*  MULTILINEARITY: det(row_scale m i c) = c * det m                   *)
(* ==================================================================== *)

(* Helper: shape lemma for prod_range built from split + unfold_left. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let prod_range_shape_at
  (#t: Type) {| cr: commutative_ring t |}
  (f: nat -> t) (lo hi: nat) (i: nat)
  : Lemma (requires lo <= i /\ i < hi)
          (ensures prod_range f lo hi =
                   prod_range f lo i * (f i * prod_range f (nat_succ i) hi))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    prod_range_split f lo i hi;
    prod_range_unfold_left f i hi;
    assert (prod_range f i hi == f i * prod_range f (nat_succ i) hi);
    reflexivity (prod_range f lo i);
    reflexivity (f i * prod_range f (nat_succ i) hi);
    mul_congruence (prod_range f lo i) (prod_range f i hi)
                   (prod_range f lo i) (f i * prod_range f (nat_succ i) hi);
    trans_lemma [ prod_range f lo hi;
                  prod_range f lo i * prod_range f i hi;
                  prod_range f lo i * (f i * prod_range f (nat_succ i) hi) ]
#pop-options

(* prod_range body' lo hi = c * prod_range body lo hi when body' differs
   from body only at index i where body' i = c * body i. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let prod_range_extract_scalar_left
  (#t: Type) {| cr: commutative_ring t |}
  (body body': nat -> t) (lo hi: nat) (i: nat) (c: t)
  : Lemma (requires lo <= i /\ i < hi /\
                    body' i = c * body i /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> body' k = body k))
          (ensures prod_range body' lo hi = c * prod_range body lo hi)
  = let mcm = cr.cr_mic in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    prod_range_shape_at body  lo hi i;
    prod_range_shape_at body' lo hi i;
    prod_range_congruence #t body' body lo i (fun _ -> ());
    prod_range_congruence #t body' body (nat_succ i) hi (fun _ -> ());
    let l   = prod_range body lo i in
    let r0  = prod_range body (nat_succ i) hi in
    let bi  = body i in
    let bi' = body' i in
    let p   = bi * r0 in
    assert (prod_range body' lo i = l);
    assert (prod_range body' (nat_succ i) hi = r0);
    assert (bi' = c * bi);
    assert (prod_range body  lo hi = l * (bi * r0));
    reflexivity bi';
    mul_congruence bi' (prod_range body' (nat_succ i) hi) bi' r0;
    reflexivity (prod_range body' lo i);
    mul_congruence (prod_range body' lo i) (bi' * prod_range body' (nat_succ i) hi)
                   l (bi' * r0);
    trans_lemma [ prod_range body' lo hi;
                  prod_range body' lo i * (bi' * prod_range body' (nat_succ i) hi);
                  l * (bi' * r0) ];
    reflexivity r0;
    mul_congruence bi' r0 (c * bi) r0;
    mul_associativity c bi r0;
    trans_lemma [ bi' * r0; (c * bi) * r0; c * (bi * r0) ];
    reflexivity l;
    mul_congruence l (bi' * r0) l (c * p);
    (* l * (c * p) = c * (l * p) via comm/assoc *)
    mul_associativity l c p;
    symmetry ((l * c) * p) (l * (c * p));
    cr.cr_mic.mul_commutativity l c;
    reflexivity p;
    mul_congruence (l * c) p (c * l) p;
    mul_associativity c l p;
    trans_lemma [ l * (c * p);
                  (l * c) * p;
                  (c * l) * p;
                  c * (l * p) ];
    reflexivity c;
    symmetry (prod_range body lo hi) (l * p);
    mul_congruence c (l * p) c (prod_range body lo hi);
    trans_lemma [ prod_range body' lo hi;
                  l * (bi' * r0);
                  l * (c * p);
                  c * (l * p);
                  c * prod_range body lo hi ]
#pop-options

(* perm_product (row_scale m i c) p = c * perm_product m p. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let perm_product_row_scale
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (c: t) (p: permutation n)
  : Lemma (perm_product (row_scale m i c) p = c * perm_product m p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let body  : nat -> t =
      fun (k: nat) -> if k < n then m (k <: fin n) (p.fwd (k <: fin n)) else one in
    let body' : nat -> t =
      fun (k: nat) ->
        if k < n then (row_scale m i c) (k <: fin n) (p.fwd (k <: fin n)) else one in
    assert ((row_scale m i c) i (p.fwd i) == c * m i (p.fwd i));
    reflexivity (c * m i (p.fwd i));
    assert (body' (i <: nat) = c * body (i <: nat));
    let agree_off (k: nat) : Lemma (0 <= k /\ k < n /\ k <> (i <: nat) ==> body' k = body k)
      = if k < n && k <> (i <: nat) then begin
          let kf : fin n = k in
          assert (kf <> i);
          assert ((row_scale m i c) kf (p.fwd kf) == m kf (p.fwd kf));
          reflexivity (m kf (p.fwd kf))
        end
    in
    Classical.forall_intro agree_off;
    prod_range_extract_scalar_left #t #cr body body' 0 n (i <: nat) c;
    perm_product_unfold (row_scale m i c) p;
    perm_product_unfold m p
#pop-options

(* leibniz_term (row_scale m i c) p = c * leibniz_term m p. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let leibniz_term_row_scale
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (c: t) (p: permutation n)
  : Lemma (leibniz_term (row_scale m i c) p = c * leibniz_term m p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    perm_product_row_scale #t #cr #n m i c p;
    let pp  = perm_product m p in
    let pp' = perm_product (row_scale m i c) p in
    assert (pp' = c * pp);
    if parity p then begin
      assert (leibniz_term (row_scale m i c) p == pp');
      assert (leibniz_term m p == pp);
      reflexivity (c * pp)
    end else begin
      assert (leibniz_term (row_scale m i c) p == -pp');
      assert (leibniz_term m p == -pp);
      neg_congruence_lem pp' (c * pp);
      ring_neg_xy_is_x_times_neg_y c pp;
      transitivity (-pp') (-(c * pp)) (c * (-pp))
    end
#pop-options

(* det(row_scale m i c) = c * det m. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_row_scale
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (c: t)
  : Lemma (det (row_scale m i c) = c * det m)
  = let r : ring t = cr.cr_r in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let g = leibniz_term m in
    let f = leibniz_term (row_scale m i c) in
    let pointwise (s: permutation n) : Lemma (f s = c * g s)
      = leibniz_term_row_scale #t #cr #n m i c s in
    Classical.forall_intro pointwise;
    sum_over_perms_mul_left_named #t #(cr.cr_r) n c f g (fun _ -> ());
    det_unfold (row_scale m i c);
    det_unfold m
#pop-options

(* ==================================================================== *)
(*  ALTERNATING: det m = 0 when two rows of m are equal                  *)
(* ==================================================================== *)

(* perm_product depends only on the pointwise values of m. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let perm_product_pointwise_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m1 m2: square_matrix t n) (p: permutation n)
  : Lemma (requires forall (a b: fin n). m1 a b = m2 a b)
          (ensures  perm_product m1 p = perm_product m2 p)
  = let body1 : nat -> t =
      fun (k: nat) -> if k < n then m1 (k <: fin n) (p.fwd (k <: fin n)) else one in
    let body2 : nat -> t =
      fun (k: nat) -> if k < n then m2 (k <: fin n) (p.fwd (k <: fin n)) else one in
    let pw (k: nat) : Lemma (0 <= k /\ k < n ==> body1 k = body2 k)
      = if k < n then begin
          let kf : fin n = k in
          assert (m1 kf (p.fwd kf) = m2 kf (p.fwd kf));
          ()
        end
    in
    Classical.forall_intro pw;
    prod_range_congruence #t body1 body2 0 n (fun _ -> ());
    perm_product_unfold m1 p;
    perm_product_unfold m2 p
#pop-options

(* leibniz_term is stable under pointwise equality. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let leibniz_term_pointwise_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m1 m2: square_matrix t n) (p: permutation n)
  : Lemma (requires forall (a b: fin n). m1 a b = m2 a b)
          (ensures  leibniz_term m1 p = leibniz_term m2 p)
  = H.elim_equatable_laws t ();
    perm_product_pointwise_eq #t #cr #n m1 m2 p;
    if parity p
    then ()
    else neg_congruence_lem (perm_product m1 p) (perm_product m2 p)
#pop-options

(* Pointwise-equal matrices have equal determinants. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let det_pointwise_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: nat) (m1 m2: square_matrix t n)
  : Lemma (requires forall (a b: fin n). m1 a b = m2 a b)
          (ensures  det m1 = det m2)
  = let pw (p: permutation n) : Lemma (leibniz_term m1 p = leibniz_term m2 p)
      = leibniz_term_pointwise_eq #t #cr #n m1 m2 p in
    Classical.forall_intro pw;
    sum_over_perms_congruence n (leibniz_term m1) (leibniz_term m2) (fun _ -> ())
#pop-options

(* If rows i and j of m are equal, swapping them yields a pointwise-equal matrix. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let row_swap_equal_rows_pointwise
  (#t: Type) {| equatable t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires forall (k: fin n). m i k = m j k)
          (ensures  forall (a b: fin n). row_swap m i j a b = m a b)
  = let aux (a b: fin n) : Lemma (row_swap m i j a b = m a b)
      = if a = i then begin
          transposition_fwd_left n i j;
          assert (row_swap m i j a b == m j b);
          assert (m i b = m j b);
          symmetry (m i b) (m j b);
          reflexivity (row_swap m i j a b);
          transitivity (row_swap m i j a b) (m j b) (m i b)
        end
        else if a = j then begin
          transposition_fwd_right n i j;
          assert (row_swap m i j a b == m i b);
          assert (m i b = m j b);
          reflexivity (row_swap m i j a b);
          transitivity (row_swap m i j a b) (m i b) (m j b)
        end
        else begin
          transposition_fwd_other n i j a;
          assert (row_swap m i j a b == m a b);
          reflexivity (m a b)
        end
    in
    Classical.forall_intro_2 aux
#pop-options

(* Strengthened alternating result over a general commutative ring. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_two_equal_rows_cr
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires ~(i == j) /\
                    (forall (k: fin n). m i k = m j k))
          (ensures  det m = zero)
  = let r : ring t = cr.cr_r in
    let acg : add_comm_group t = acg_of_ring_local t r in
    let tau = transposition n i j in
    let f : permutation n -> t = leibniz_term m in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    leibniz_term_respects_perm_eq #t #cr #n m;
    transposition_self_inverse n i j;
    let tau_ne_id_aux ()
      : Lemma (requires perm_eq tau (identity n)) (ensures False)
      = parity_perm_eq_invariant tau (identity n);
        parity_transposition n i j;
        parity_identity n
    in
    Classical.move_requires tau_ne_id_aux ();
    assert (~(perm_eq tau (identity n)));
    row_swap_equal_rows_pointwise #t #_ #n m i j;
    let pair_zero (s: permutation n)
      : Lemma (f s + f (compose s tau) = zero)
      = let a = f s in
        let b = f (compose s tau) in
        leibniz_term_row_swap #t #cr #n m i j s;
        assert (leibniz_term (row_swap m i j) s = -b);
        leibniz_term_pointwise_eq #t #cr #n (row_swap m i j) m s;
        assert (leibniz_term (row_swap m i j) s = a);
        symmetry (leibniz_term (row_swap m i j) s) a;
        transitivity a (leibniz_term (row_swap m i j) s) (-b);
        assert (a = -b);
        reflexivity b;
        add_congruence a b (-b) b;
        acg.add_negation b;
        transitivity (a + b) (-b + b) (zero #t)
    in
    Classical.forall_intro pair_zero;
    sum_over_perms_pair_cancel #t #acg n f tau (fun _ -> ());
    det_unfold m;
    reflexivity (det m);
    transitivity (det m) (sum_over_perms n f) (zero #t)
#pop-options

(* ==================================================================== *)
(*  ROW-REPLACE helper                                                   *)
(*  row_replace m i u : matrix with row i replaced by the function u.    *)
(* ==================================================================== *)
let row_replace (#t: Type) (#n: nat)
  (m: square_matrix t n) (i: fin n) (u: fin n -> t)
  : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality a i then u b else m a b

(* prod_range_extract_add_left: given body_add i = body i + c * body_repl i
   and agreement elsewhere, prod_range body_add = prod_range body + c * prod_range body_repl. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let prod_range_extract_add_left
  (#t: Type) {| cr: commutative_ring t |}
  (b ba br: nat -> t) (lo hi: nat) (i: nat) (c: t)
  : Lemma (requires lo <= i /\ i < hi /\
                    ba i = b i + c * br i /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> ba k = b k) /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> br k = b k))
          (ensures prod_range ba lo hi = prod_range b lo hi + c * prod_range br lo hi)
  = let mcm = cr.cr_mic in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    prod_range_shape_at b  lo hi i;
    prod_range_shape_at ba lo hi i;
    prod_range_shape_at br lo hi i;
    prod_range_congruence #t ba b lo i (fun _ -> ());
    prod_range_congruence #t ba b (nat_succ i) hi (fun _ -> ());
    prod_range_congruence #t br b lo i (fun _ -> ());
    prod_range_congruence #t br b (nat_succ i) hi (fun _ -> ());
    let l = prod_range b lo i in
    let rr = prod_range b (nat_succ i) hi in
    let u = b i in
    let v = br i in
    let bai = ba i in
    assert (bai = u + c * v);
    (* prod_range ba lo hi = l * (bai * rr) *)
    reflexivity bai;
    mul_congruence bai (prod_range ba (nat_succ i) hi) bai rr;
    mul_congruence (prod_range ba lo i) (bai * prod_range ba (nat_succ i) hi) l (bai * rr);
    assert (prod_range ba lo hi = l * (bai * rr));
    (* prod_range b lo hi = l * (u * rr) *)
    reflexivity u;
    mul_congruence u (prod_range b (nat_succ i) hi) u rr;
    reflexivity l;
    mul_congruence (prod_range b lo i) (u * prod_range b (nat_succ i) hi) l (u * rr);
    assert (prod_range b lo hi = l * (u * rr));
    (* prod_range br lo hi = l * (v * rr) *)
    reflexivity v;
    mul_congruence v (prod_range br (nat_succ i) hi) v rr;
    mul_congruence (prod_range br lo i) (v * prod_range br (nat_succ i) hi) l (v * rr);
    assert (prod_range br lo hi = l * (v * rr));
    (* l * (bai * rr) = l * ((u + c*v) * rr) *)
    reflexivity rr;
    mul_congruence bai rr (u + c * v) rr;
    reflexivity l;
    mul_congruence l (bai * rr) l ((u + c * v) * rr);
    assert (l * (bai * rr) = l * ((u + c * v) * rr));
    (* (u + c*v) * rr = u * rr + (c*v) * rr *)
    right_distributivity rr u (c * v);
    reflexivity l;
    mul_congruence l ((u + c * v) * rr) l (u * rr + (c * v) * rr);
    assert (l * ((u + c * v) * rr) = l * (u * rr + (c * v) * rr));
    (* l * (u*rr + (c*v)*rr) = l*(u*rr) + l*((c*v)*rr) *)
    left_distributivity l (u * rr) ((c * v) * rr);
    assert (l * (u * rr + (c * v) * rr) = l * (u * rr) + l * ((c * v) * rr));
    (* l * ((c*v) * rr) = c * (l * (v * rr)) using comm/assoc *)
    mul_associativity c v rr;
    assert ((c * v) * rr = c * (v * rr));
    mul_congruence l ((c * v) * rr) l (c * (v * rr));
    assert (l * ((c * v) * rr) = l * (c * (v * rr)));
    let p1 = v * rr in
    mul_associativity l c p1;
    symmetry ((l * c) * p1) (l * (c * p1));
    cr.cr_mic.mul_commutativity l c;
    reflexivity p1;
    mul_congruence (l * c) p1 (c * l) p1;
    mul_associativity c l p1;
    trans_lemma [ l * (c * p1); (l * c) * p1; (c * l) * p1; c * (l * p1) ];
    assert (l * (c * (v * rr)) = c * (l * (v * rr)));
    transitivity (l * ((c * v) * rr)) (l * (c * (v * rr))) (c * (l * (v * rr)));
    symmetry (prod_range b lo hi) (l * (u * rr));
    symmetry (prod_range br lo hi) (l * (v * rr));
    reflexivity c;
    mul_congruence c (l * (v * rr)) c (prod_range br lo hi);
    transitivity (l * ((c * v) * rr)) (c * (l * (v * rr))) (c * prod_range br lo hi);
    add_congruence (l * (u * rr)) (l * ((c * v) * rr))
                   (prod_range b lo hi) (c * prod_range br lo hi);
    assert (l * (u * rr) + l * ((c * v) * rr) = prod_range b lo hi + c * prod_range br lo hi);
    transitivity (prod_range ba lo hi) (l * (bai * rr)) (l * ((u + c * v) * rr));
    transitivity (prod_range ba lo hi) (l * ((u + c * v) * rr)) (l * (u * rr + (c * v) * rr));
    transitivity (prod_range ba lo hi) (l * (u * rr + (c * v) * rr)) (l * (u * rr) + l * ((c * v) * rr));
    transitivity (prod_range ba lo hi) (l * (u * rr) + l * ((c * v) * rr))
                 (prod_range b lo hi + c * prod_range br lo hi)
#pop-options

(* ==================================================================== *)
(*  ALTERNATING (additive form):                                         *)
(*  det (row_add m i j c) = det m                                        *)
(* ==================================================================== *)

(* perm_product (row_add m i j c) p splits additively. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let perm_product_row_add_split
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n) (c: t) (p: permutation n)
  : Lemma (requires ~(i == j))
          (ensures  perm_product (row_add m i j c) p
                  = perm_product m p
                  + c * perm_product (row_replace m i (m j)) p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let body  : nat -> t =
      fun (k: nat) -> if k < n then m (k <: fin n) (p.fwd (k <: fin n)) else one in
    let body_add : nat -> t =
      fun (k: nat) ->
        if k < n then (row_add m i j c) (k <: fin n) (p.fwd (k <: fin n)) else one in
    let body_repl : nat -> t =
      fun (k: nat) ->
        if k < n then (row_replace m i (m j)) (k <: fin n) (p.fwd (k <: fin n)) else one in
    let in_ : nat = i in
    let agree_add (k: nat) : Lemma (0 <= k /\ k < n /\ k <> in_ ==> body_add k = body k)
      = if k < n && k <> in_ then begin
          let kf : fin n = k in
          assert (kf <> i);
          reflexivity (m kf (p.fwd kf))
        end
    in
    Classical.forall_intro agree_add;
    let agree_repl (k: nat) : Lemma (0 <= k /\ k < n /\ k <> in_ ==> body_repl k = body k)
      = if k < n && k <> in_ then begin
          let kf : fin n = k in
          assert (kf <> i);
          reflexivity (m kf (p.fwd kf))
        end
    in
    Classical.forall_intro agree_repl;
    let u = m i (p.fwd i) in
    let v = m j (p.fwd i) in
    assert (body_add in_ == u + c * v);
    assert (body in_ == u);
    assert (body_repl in_ == v);
    reflexivity v;
    reflexivity c;
    mul_congruence c v c (body_repl in_);
    reflexivity u;
    add_congruence u (c * v) (body in_) (c * body_repl in_);
    assert (body_add in_ = body in_ + c * body_repl in_);
    prod_range_extract_add_left #t #cr body body_add body_repl 0 n in_ c;
    perm_product_unfold (row_add m i j c) p;
    perm_product_unfold m p;
    perm_product_unfold (row_replace m i (m j)) p
#pop-options

(* leibniz_term version of the same split. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let leibniz_term_row_add_split
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n) (c: t) (p: permutation n)
  : Lemma (requires ~(i == j))
          (ensures  leibniz_term (row_add m i j c) p
                  = leibniz_term m p
                  + c * leibniz_term (row_replace m i (m j)) p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    perm_product_row_add_split #t #cr #n m i j c p;
    let pp_ra = perm_product (row_add m i j c) p in
    let pp_m  = perm_product m p in
    let pp_r  = perm_product (row_replace m i (m j)) p in
    assert (pp_ra = pp_m + c * pp_r);
    if parity p
    then begin
      assert (leibniz_term (row_add m i j c) p == pp_ra);
      assert (leibniz_term m p == pp_m);
      assert (leibniz_term (row_replace m i (m j)) p == pp_r);
      reflexivity (pp_m + c * pp_r)
    end
    else begin
      neg_congruence_lem pp_ra (pp_m + c * pp_r);
      assert ((-pp_ra) = -(pp_m + c * pp_r));
      neg_of_sum_local pp_m (c * pp_r);
      assert (-(pp_m + c * pp_r) = (-pp_m) + (-(c * pp_r)));
      ring_neg_xy_is_x_times_neg_y c pp_r;
      assert (-(c * pp_r) = c * (-pp_r));
      reflexivity (-pp_m);
      add_congruence (-pp_m) (-(c * pp_r)) (-pp_m) (c * (-pp_r));
      transitivity (-pp_ra) (-(pp_m + c * pp_r)) ((-pp_m) + (-(c * pp_r)));
      transitivity (-pp_ra) ((-pp_m) + (-(c * pp_r))) ((-pp_m) + c * (-pp_r));
      assert (leibniz_term (row_add m i j c) p == -pp_ra);
      assert (leibniz_term m p == -pp_m);
      assert (leibniz_term (row_replace m i (m j)) p == -pp_r);
      reflexivity ((-pp_m) + c * (-pp_r))
    end
#pop-options

(* row_replace m i (m j) has rows i and j both equal to m j. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let row_replace_with_other_row_has_equal_rows
  (#t: Type) {| equatable t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires ~(i == j))
          (ensures  forall (k: fin n).
                      (row_replace m i (m j)) i k = (row_replace m i (m j)) j k)
  = let aux (k: fin n)
      : Lemma ((row_replace m i (m j)) i k = (row_replace m i (m j)) j k)
      = assert ((row_replace m i (m j)) i k == m j k);
        assert ((row_replace m i (m j)) j k == m j k);
        reflexivity (m j k)
    in
    Classical.forall_intro aux
#pop-options

(* Headline: det (row_add m i j c) = det m, in a commutative ring
   (using det_two_equal_rows_cr which works without char≠2). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_row_add
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n) (c: t)
  : Lemma (requires ~(i == j))
          (ensures  det (row_add m i j c) = det m)
  = let r : ring t = cr.cr_r in
    let sr : ring t = cr.cr_r in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let f = leibniz_term (row_add m i j c) in
    let g = leibniz_term m in
    let h = leibniz_term (row_replace m i (m j)) in
    let pw (p: permutation n) : Lemma (f p = g p + c * h p)
      = leibniz_term_row_add_split #t #cr #n m i j c p in
    Classical.forall_intro pw;
    let ch : permutation n -> t = fun p -> c * h p in
    let ch_eq (p: permutation n) : Lemma (ch p = c * h p) = () in
    Classical.forall_intro ch_eq;
    sum_over_perms_add_named n f g ch (fun _ -> ());
    assert (sum_over_perms n f = sum_over_perms n g + sum_over_perms n ch);
    sum_over_perms_mul_left_named #t #(cr.cr_r) n c ch h (fun _ -> ());
    assert (sum_over_perms n ch = c * sum_over_perms n h);
    reflexivity (sum_over_perms n g);
    add_congruence (sum_over_perms n g) (sum_over_perms n ch)
                   (sum_over_perms n g) (c * sum_over_perms n h);
    det_unfold (row_add m i j c);
    det_unfold m;
    det_unfold (row_replace m i (m j));
    row_replace_with_other_row_has_equal_rows #t #_ #n m i j;
    det_two_equal_rows_cr #t #cr #n (row_replace m i (m j)) i j;
    assert (det (row_replace m i (m j)) = zero);
    reflexivity (sum_over_perms n h);
    symmetry (det (row_replace m i (m j))) (sum_over_perms n h);
    transitivity (sum_over_perms n h) (det (row_replace m i (m j))) (zero #t);
    reflexivity c;
    mul_congruence c (sum_over_perms n h) c (zero #t);
    ring_zero_is_right_absorber c;
    transitivity (c * sum_over_perms n h) (c * zero #t) (zero #t);
    reflexivity (sum_over_perms n g);
    add_congruence (sum_over_perms n g) (c * sum_over_perms n h)
                   (sum_over_perms n g) (zero #t);
    H.x_plus_zero (sum_over_perms n g);
    transitivity (sum_over_perms n g + c * sum_over_perms n h)
                 (sum_over_perms n g + zero)
                 (sum_over_perms n g);
    symmetry (det m) (sum_over_perms n g);
    transitivity (det (row_add m i j c)) (sum_over_perms n f) (sum_over_perms n g + sum_over_perms n ch);
    transitivity (det (row_add m i j c)) (sum_over_perms n g + sum_over_perms n ch) (sum_over_perms n g + c * sum_over_perms n h);
    transitivity (det (row_add m i j c)) (sum_over_perms n g + c * sum_over_perms n h) (sum_over_perms n g);
    transitivity (det (row_add m i j c)) (sum_over_perms n g) (det m)
#pop-options

(* ====================================================================== *)
(*  Additive multilinearity of det in a row (row split).                  *)
(* ====================================================================== *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let perm_product_row_split
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (u v uv: fin n -> t) (p: permutation n)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures perm_product (row_replace m i uv) p
                 = perm_product (row_replace m i u) p
                 + perm_product (row_replace m i v) p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let muv = row_replace m i uv in
    let mu  = row_replace m i u in
    let mv  = row_replace m i v in
    let body : nat -> t =
      fun (k: nat) -> if k < n then mu (k <: fin n) (p.fwd (k <: fin n)) else one in
    let body_uv : nat -> t =
      fun (k: nat) -> if k < n then muv (k <: fin n) (p.fwd (k <: fin n)) else one in
    let body_v : nat -> t =
      fun (k: nat) -> if k < n then mv (k <: fin n) (p.fwd (k <: fin n)) else one in
    let in_ : nat = i in
    let agree_uv (k: nat)
      : Lemma (0 <= k /\ k < n /\ k <> in_ ==> body_uv k = body k)
      = if k < n && k <> in_ then begin
          let kf : fin n = k in
          assert (kf <> i);
          reflexivity (m kf (p.fwd kf))
        end
    in
    Classical.forall_intro agree_uv;
    let agree_v (k: nat)
      : Lemma (0 <= k /\ k < n /\ k <> in_ ==> body_v k = body k)
      = if k < n && k <> in_ then begin
          let kf : fin n = k in
          assert (kf <> i);
          reflexivity (m kf (p.fwd kf))
        end
    in
    Classical.forall_intro agree_v;
    let upi = u (p.fwd i) in
    let vpi = v (p.fwd i) in
    let uvi = uv (p.fwd i) in
    assert (uvi = upi + vpi);
    assert (body_uv in_ == uvi);
    assert (body    in_ == upi);
    assert (body_v  in_ == vpi);
    reflexivity (body_uv in_);
    transitivity (body_uv in_) uvi (upi + vpi);
    assert (body_uv in_ = upi + vpi);
    H.one_mul_x vpi;
    symmetry (one * vpi) vpi;
    reflexivity upi;
    add_congruence upi vpi upi (one * vpi);
    transitivity (body_uv in_) (upi + vpi) (upi + one * vpi);
    assert (body_uv in_ = body in_ + one * body_v in_);
    prod_range_extract_add_left #t #cr body body_uv body_v 0 n in_ (one #t);
    assert (prod_range body_uv 0 n
            = prod_range body 0 n + one * prod_range body_v 0 n);
    H.one_mul_x (prod_range body_v 0 n);
    reflexivity (prod_range body 0 n);
    add_congruence (prod_range body 0 n) (one * prod_range body_v 0 n)
                   (prod_range body 0 n) (prod_range body_v 0 n);
    transitivity (prod_range body_uv 0 n)
                 (prod_range body 0 n + one * prod_range body_v 0 n)
                 (prod_range body 0 n + prod_range body_v 0 n);
    perm_product_unfold muv p;
    perm_product_unfold mu  p;
    perm_product_unfold mv  p;
    reflexivity (perm_product muv p);
    reflexivity (perm_product mu p);
    reflexivity (perm_product mv p);
    symmetry (perm_product mu p) (prod_range body   0 n);
    symmetry (perm_product mv p) (prod_range body_v 0 n);
    add_congruence (prod_range body 0 n) (prod_range body_v 0 n)
                   (perm_product mu p)   (perm_product mv p);
    transitivity (perm_product muv p) (prod_range body_uv 0 n)
                 (prod_range body 0 n + prod_range body_v 0 n);
    transitivity (perm_product muv p)
                 (prod_range body 0 n + prod_range body_v 0 n)
                 (perm_product mu p + perm_product mv p)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let leibniz_term_row_split
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (u v uv: fin n -> t) (p: permutation n)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures leibniz_term (row_replace m i uv) p
                 = leibniz_term (row_replace m i u) p
                 + leibniz_term (row_replace m i v) p)
  = let acg : add_comm_group t = acg_of_ring_local t cr.cr_r in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    perm_product_row_split #t #cr #n m i u v uv p;
    let muv = row_replace m i uv in
    let mu  = row_replace m i u in
    let mv  = row_replace m i v in
    let pp_uv = perm_product muv p in
    let pp_u  = perm_product mu  p in
    let pp_v  = perm_product mv  p in
    if parity p
    then begin
      assert (leibniz_term muv p == pp_uv);
      assert (leibniz_term mu  p == pp_u);
      assert (leibniz_term mv  p == pp_v);
      reflexivity (pp_u + pp_v)
    end else begin
      neg_congruence_lem pp_uv (pp_u + pp_v);
      neg_of_sum_local pp_u pp_v;
      acg.add_commutativity (-pp_v) (-pp_u);
      trans_lemma [ -pp_uv;
                    -(pp_u + pp_v);
                    (-pp_v) + (-pp_u);
                    (-pp_u) + (-pp_v) ];
      assert (leibniz_term muv p == -pp_uv);
      assert (leibniz_term mu  p == -pp_u);
      assert (leibniz_term mv  p == -pp_v);
      reflexivity ((-pp_u) + (-pp_v))
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_row_split
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (u v uv: fin n -> t)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures det (row_replace m i uv)
                 = det (row_replace m i u) + det (row_replace m i v))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let muv = row_replace m i uv in
    let mu  = row_replace m i u in
    let mv  = row_replace m i v in
    let f = leibniz_term muv in
    let g = leibniz_term mu in
    let h = leibniz_term mv in
    let pw (p: permutation n) : Lemma (f p = g p + h p)
      = leibniz_term_row_split #t #cr #n m i u v uv p in
    Classical.forall_intro pw;
    sum_over_perms_add_named n f g h (fun _ -> ());
    det_unfold muv;
    det_unfold mu;
    det_unfold mv;
    reflexivity (sum_over_perms n f);
    reflexivity (sum_over_perms n g);
    reflexivity (sum_over_perms n h);
    symmetry (det mu) (sum_over_perms n g);
    symmetry (det mv) (sum_over_perms n h);
    add_congruence (sum_over_perms n g) (sum_over_perms n h)
                   (det mu)             (det mv);
    transitivity (det muv) (sum_over_perms n f)
                 (sum_over_perms n g + sum_over_perms n h);
    transitivity (det muv) (sum_over_perms n g + sum_over_perms n h)
                 (det mu + det mv)
#pop-options

(* ============================================================== *)
(* Column operations and determinant lemmas, derived via transpose. *)
(* ============================================================== *)

let col_swap (#t: Type) (#n: nat)
  (m: square_matrix t n) (i j: fin n) : square_matrix t n
  = permute_cols m (transposition n i j)

let col_scale (#t: Type) {| ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (c: t) : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality b i then m a b * c else m a b

let col_add (#t: Type) {| ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n) (c: t) : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality b i then m a b + m a j * c else m a b

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let transpose_col_swap_pointwise (#t: Type) (#n: nat)
  (m: square_matrix t n) (i j: fin n) (a b: fin n)
  : Lemma (transpose (col_swap m i j) a b == row_swap (transpose m) i j a b)
  = ()
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let det_col_swap (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires ~(i == j))
          (ensures det (col_swap m i j) = -(det m))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pw (a b: fin n)
      : Lemma (transpose (col_swap m i j) a b = row_swap (transpose m) i j a b)
      = transpose_col_swap_pointwise #t #n m i j a b;
        reflexivity (transpose (col_swap m i j) a b)
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq #t #cr #n (transpose (col_swap m i j)) (row_swap (transpose m) i j);
    det_transpose #t #cr #n (col_swap m i j);
    det_row_swap #t #cr #n (transpose m) i j;
    det_transpose #t #cr #n m;
    neg_congruence_lem (det (transpose m)) (det m);
    symmetry (det (transpose (col_swap m i j))) (det (col_swap m i j));
    transitivity (det (col_swap m i j))
                 (det (transpose (col_swap m i j)))
                 (det (row_swap (transpose m) i j));
    transitivity (det (col_swap m i j))
                 (det (row_swap (transpose m) i j))
                 (-(det (transpose m)));
    transitivity (det (col_swap m i j))
                 (-(det (transpose m)))
                 (-(det m))
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let transpose_col_scale_to_row_scale (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (c: t) (a b: fin n)
  : Lemma (transpose (col_scale m i c) a b = row_scale (transpose m) i c a b)
  = H.elim_equatable_laws t ();
    if (a <: nat) = (i <: nat) then begin
      assert (transpose (col_scale m i c) a b == m b a * c);
      assert (row_scale (transpose m) i c a b == c * m b a);
      (cr.cr_mic).mul_commutativity (m b a) c
    end else begin
      assert (transpose (col_scale m i c) a b == m b a);
      reflexivity (m b a)
    end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let det_col_scale (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i: fin n) (c: t)
  : Lemma (det (col_scale m i c) = c * det m)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pw (a b: fin n)
      : Lemma (transpose (col_scale m i c) a b = row_scale (transpose m) i c a b)
      = transpose_col_scale_to_row_scale #t #cr #n m i c a b
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq #t #cr #n (transpose (col_scale m i c)) (row_scale (transpose m) i c);
    det_transpose #t #cr #n (col_scale m i c);
    det_row_scale #t #cr #n (transpose m) i c;
    det_transpose #t #cr #n m;
    reflexivity c;
    mul_congruence c (det (transpose m)) c (det m);
    symmetry (det (transpose (col_scale m i c))) (det (col_scale m i c));
    transitivity (det (col_scale m i c))
                 (det (transpose (col_scale m i c)))
                 (det (row_scale (transpose m) i c));
    transitivity (det (col_scale m i c))
                 (det (row_scale (transpose m) i c))
                 (c * det (transpose m));
    transitivity (det (col_scale m i c))
                 (c * det (transpose m))
                 (c * det m)
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let transpose_col_add_to_row_add (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n) (c: t) (a b: fin n)
  : Lemma (requires ~(i == j))
          (ensures transpose (col_add m i j c) a b = row_add (transpose m) i j c a b)
  = H.elim_equatable_laws t ();
    if (a <: nat) = (i <: nat) then begin
      assert (transpose (col_add m i j c) a b == m b a + m b j * c);
      assert (row_add (transpose m) i j c a b == m b a + c * m b j);
      (cr.cr_mic).mul_commutativity (m b j) c;
      reflexivity (m b a);
      add_congruence (m b a) (m b j * c) (m b a) (c * m b j)
    end else begin
      reflexivity (m b a)
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_col_add (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (i j: fin n) (c: t)
  : Lemma (requires ~(i == j))
          (ensures det (col_add m i j c) = det m)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pw (a b: fin n)
      : Lemma (transpose (col_add m i j c) a b = row_add (transpose m) i j c a b)
      = transpose_col_add_to_row_add #t #cr #n m i j c a b
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq #t #cr #n (transpose (col_add m i j c)) (row_add (transpose m) i j c);
    det_transpose #t #cr #n (col_add m i j c);
    det_row_add #t #cr #n (transpose m) i j c;
    det_transpose #t #cr #n m;
    symmetry (det (transpose (col_add m i j c))) (det (col_add m i j c));
    transitivity (det (col_add m i j c))
                 (det (transpose (col_add m i j c)))
                 (det (row_add (transpose m) i j c));
    transitivity (det (col_add m i j c))
                 (det (row_add (transpose m) i j c))
                 (det (transpose m));
    transitivity (det (col_add m i j c))
                 (det (transpose m))
                 (det m)
#pop-options

(* det_zero_column: derived from det_zero_row via transpose. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let det_zero_column (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (j: fin n)
  : Lemma (requires forall (k: fin n). m k j = zero #t)
          (ensures det m = zero #t)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let mt = transpose m in
    let pw (k: fin n) : Lemma (mt j k = zero #t)
      = assert (mt j k == m k j);
        reflexivity (m k j)
    in
    Classical.forall_intro pw;
    det_zero_row #t #cr #n mt j;
    det_transpose #t #cr #n m;
    transitivity (det m) (det mt) (zero #t)
#pop-options

(* ====================================================================== *)
(*  Column counterpart: col_replace and det_col_split, via transpose.     *)
(* ====================================================================== *)

let col_replace (#t: Type) (#n: nat)
  (m: square_matrix t n) (j: fin n) (u: fin n -> t)
  : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality b j then u a else m a b

#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let transpose_col_replace_pointwise (#t: Type) (#n: nat)
  (m: square_matrix t n) (j: fin n) (u: fin n -> t) (a b: fin n)
  : Lemma (transpose (col_replace m j u) a b == row_replace (transpose m) j u a b)
  = ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_col_split
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (j: fin n) (u v uv: fin n -> t)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures det (col_replace m j uv)
                 = det (col_replace m j u) + det (col_replace m j v))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cuv = col_replace m j uv in
    let cu  = col_replace m j u  in
    let cv  = col_replace m j v  in
    let mt  = transpose m in
    let ruv = row_replace mt j uv in
    let ru  = row_replace mt j u  in
    let rv  = row_replace mt j v  in
    let pw_uv (a b: fin n)
      : Lemma (transpose cuv a b = ruv a b)
      = transpose_col_replace_pointwise #t #n m j uv a b;
        reflexivity (ruv a b) in
    Classical.forall_intro_2 pw_uv;
    let pw_u (a b: fin n)
      : Lemma (transpose cu a b = ru a b)
      = transpose_col_replace_pointwise #t #n m j u a b;
        reflexivity (ru a b) in
    Classical.forall_intro_2 pw_u;
    let pw_v (a b: fin n)
      : Lemma (transpose cv a b = rv a b)
      = transpose_col_replace_pointwise #t #n m j v a b;
        reflexivity (rv a b) in
    Classical.forall_intro_2 pw_v;
    det_pointwise_eq #t #cr #n (transpose cuv) ruv;
    det_pointwise_eq #t #cr #n (transpose cu)  ru;
    det_pointwise_eq #t #cr #n (transpose cv)  rv;
    det_transpose #t #cr #n cuv;
    det_transpose #t #cr #n cu;
    det_transpose #t #cr #n cv;
    det_row_split #t #cr #n mt j u v uv;
    symmetry (det (transpose cuv)) (det cuv);
    symmetry (det (transpose cu))  (det cu);
    symmetry (det (transpose cv))  (det cv);
    transitivity (det cuv) (det (transpose cuv)) (det ruv);
    transitivity (det cu)  (det (transpose cu))  (det ru);
    transitivity (det cv)  (det (transpose cv))  (det rv);
    assert (det ruv = det ru + det rv);
    symmetry (det ru) (det cu);
    symmetry (det rv) (det cv);
    add_congruence (det ru) (det rv) (det cu) (det cv);
    transitivity (det cuv) (det ruv) (det ru + det rv);
    transitivity (det cuv) (det ru + det rv) (det cu + det cv)
#pop-options

(* ====================================================================== *)
(*  L3: General row-permutation determinant law                            *)
(*       det (permute_rows m sigma) = sign(sigma) * det m                  *)
(*  We split into the two parity cases for clarity.                        *)
(* ====================================================================== *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let perm_product_permute_rows
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n) (p: permutation n)
  : Lemma (perm_product (permute_rows m sigma) p =
           perm_product m (compose p (inverse sigma)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sigma_inv = inverse sigma in
    let q = compose p sigma_inv in
    let lhs_body : nat -> t =
      fun (k: nat) -> if k < n
                  then (permute_rows m sigma) (k <: fin n) (p.fwd (k <: fin n))
                  else one in
    let rhs_body : nat -> t =
      fun (k: nat) -> if k < n
                  then m (k <: fin n) (q.fwd (k <: fin n))
                  else one in
    let f : nat -> t =
      fun (k: nat) -> if k < n
                  then m (k <: fin n) (p.fwd ((sigma_inv.fwd (k <: fin n)) <: fin n))
                  else one in
    inverse_left sigma;
    let body_p_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==>
       lhs_body k = f (sigma.fwd (k <: fin n)))
      = if 0 <= k && k < n then begin
          let kf : fin n = k <: fin n in
          let sk : fin n = sigma.fwd kf in
          compose_fwd sigma_inv sigma kf;
          perm_eq_elim (compose sigma_inv sigma) (identity n) kf;
          identity_fwd n kf;
          assert (sigma_inv.fwd sk == kf);
          reflexivity (m sk (p.fwd kf))
        end in
    Classical.forall_intro body_p_hyp;
    let body_id_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==> rhs_body k = f k)
      = if 0 <= k && k < n then begin
          let kf : fin n = k <: fin n in
          compose_fwd p sigma_inv kf;
          reflexivity (m kf (p.fwd (sigma_inv.fwd kf)))
        end in
    Classical.forall_intro body_id_hyp;
    prod_range_perm_invariance_fn #t #cr #n f lhs_body rhs_body sigma
      (fun _ -> ()) (fun _ -> ());
    perm_product_unfold (permute_rows m sigma) p;
    perm_product_unfold m q;
    reflexivity (perm_product (permute_rows m sigma) p);
    reflexivity (perm_product m q);
    trans_lemma [ perm_product (permute_rows m sigma) p;
                  prod_range lhs_body 0 n;
                  prod_range rhs_body 0 n;
                  perm_product m q ]
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let leibniz_term_permute_rows_even
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n) (p: permutation n)
  : Lemma (requires parity sigma == true)
          (ensures leibniz_term (permute_rows m sigma) p =
                   leibniz_term m (compose p (inverse sigma)))
  = let sigma_inv = inverse sigma in
    let q = compose p sigma_inv in
    perm_product_permute_rows #t #cr #n m sigma p;
    sign_homomorphism p sigma_inv;
    parity_inverse sigma;
    let lhs = leibniz_term (permute_rows m sigma) p in
    let pp1 = perm_product (permute_rows m sigma) p in
    let pp2 = perm_product m q in
    let rhs = leibniz_term m q in
    if parity p then begin
      assert (parity q == true);
      assert (lhs == pp1);
      assert (rhs == pp2);
      reflexivity pp1;
      reflexivity pp2;
      assert (pp1 = pp2);
      assert (lhs = rhs)
    end else begin
      assert (parity q == false);
      assert (lhs == -pp1);
      assert (rhs == -pp2);
      neg_congruence pp1 pp2;
      assert ((-pp1) = (-pp2));
      assert (lhs = rhs)
    end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let leibniz_term_permute_rows_odd
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n) (p: permutation n)
  : Lemma (requires parity sigma == false)
          (ensures leibniz_term (permute_rows m sigma) p =
                   -(leibniz_term m (compose p (inverse sigma))))
  = let sigma_inv = inverse sigma in
    let q = compose p sigma_inv in
    perm_product_permute_rows #t #cr #n m sigma p;
    sign_homomorphism p sigma_inv;
    parity_inverse sigma;
    let lhs = leibniz_term (permute_rows m sigma) p in
    let pp1 = perm_product (permute_rows m sigma) p in
    let pp2 = perm_product m q in
    let rhs = -(leibniz_term m q) in
    if parity p then begin
      assert (parity q == false);
      assert (lhs == pp1);
      assert (leibniz_term m q == -pp2);
      assert (rhs == -(-pp2));
      reflexivity pp1;
      reflexivity pp2;
      double_negation_lemma #t #cr pp2;
      symmetry (-(-pp2)) pp2;
      transitivity pp1 pp2 (-(-pp2))
    end else begin
      assert (parity q == true);
      assert (lhs == -pp1);
      assert (leibniz_term m q == pp2);
      assert (rhs == -pp2);
      neg_congruence pp1 pp2;
      assert ((-pp1) = (-pp2));
      assert (lhs = rhs)
    end
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 80"
let det_permute_rows_even
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n)
  : Lemma (requires parity sigma == true)
          (ensures  det (permute_rows m sigma) = det m)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sigma_inv = inverse sigma in
    let f = leibniz_term (permute_rows m sigma) in
    let g = leibniz_term m in
    leibniz_term_respects_perm_eq #t #cr #n m;
    sum_over_perms_reindex n g sigma_inv;
    let pointwise (s: permutation n) : Lemma (f s = g (compose s sigma_inv))
      = leibniz_term_permute_rows_even #t #cr #n m sigma s in
    Classical.forall_intro pointwise;
    sum_over_perms_congruence n f (fcomp g (flip compose sigma_inv)) (fun _ -> ());
    symmetry (sum_over_perms n g) (sum_over_perms n (fcomp g (flip compose sigma_inv)));
    det_unfold (permute_rows m sigma);
    det_unfold m;
    reflexivity (sum_over_perms n f);
    reflexivity (sum_over_perms n g);
    symmetry (det m) (sum_over_perms n g);
    transitivity (det (permute_rows m sigma))
                 (sum_over_perms n f)
                 (sum_over_perms n (fcomp g (flip compose sigma_inv)));
    transitivity (det (permute_rows m sigma))
                 (sum_over_perms n (fcomp g (flip compose sigma_inv)))
                 (sum_over_perms n g);
    transitivity (det (permute_rows m sigma))
                 (sum_over_perms n g)
                 (det m)
#pop-options

#push-options "--fuel 6 --ifuel 2 --z3rlimit 80"
let det_permute_rows_odd
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n)
  : Lemma (requires parity sigma == false)
          (ensures  det (permute_rows m sigma) = -(det m))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let sigma_inv = inverse sigma in
    let f = leibniz_term (permute_rows m sigma) in
    let g = leibniz_term m in
    leibniz_term_respects_perm_eq #t #cr #n m;
    sum_over_perms_reindex n g sigma_inv;
    let pointwise (s: permutation n) : Lemma (f s = -(g (compose s sigma_inv)))
      = leibniz_term_permute_rows_odd #t #cr #n m sigma s in
    Classical.forall_intro pointwise;
    sum_over_perms_congruence n f (fcomp neg (fcomp g (flip compose sigma_inv))) (fun _ -> ());
    sum_over_perms_neg_named #t #(acg_of_ring_local t cr.cr_r) n f
      (fcomp g (flip compose sigma_inv)) (fun _ -> ());
    symmetry (sum_over_perms n g) (sum_over_perms n (fcomp g (flip compose sigma_inv)));
    det_unfold (permute_rows m sigma);
    det_unfold m;
    symmetry (det m) (sum_over_perms n g);
    neg_congruence (sum_over_perms n (fcomp g (flip compose sigma_inv)))
                   (sum_over_perms n g);
    neg_congruence (sum_over_perms n g) (det m);
    (* Chain: det(perm) = sum f = -(sum (g ∘ σ⁻¹)) = -(sum g) = -(det m) *)
    transitivity (det (permute_rows m sigma))
                 (sum_over_perms n f)
                 (-(sum_over_perms n (fcomp g (flip compose sigma_inv))));
    transitivity (det (permute_rows m sigma))
                 (-(sum_over_perms n (fcomp g (flip compose sigma_inv))))
                 (-(sum_over_perms n g));
    transitivity (det (permute_rows m sigma))
                 (-(sum_over_perms n g))
                 (-(det m))
#pop-options

let det_permute_rows
  (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (sigma: permutation n)
  : Lemma (det (permute_rows m sigma) =
           (if parity sigma then det m else -(det m)))
  = if parity sigma
    then det_permute_rows_even #t #cr #n m sigma
    else det_permute_rows_odd  #t #cr #n m sigma

(* ====================================================================== *)
(*  Laplace expansion: definitions and helpers.                           *)
(*                                                                        *)
(*  We add:                                                               *)
(*    - minus_one_pow : nat -> t  (the ring element (-1)^k)               *)
(*    - skip          : fin (n-1) -> fin n, skipping a chosen index       *)
(*    - minor         : square_matrix t n -> fin n -> fin n               *)
(*                       -> square_matrix t (n-1)                         *)
(*                                                                        *)
(*  These are the foundational definitions used by the Laplace row        *)
(*  expansion theorem.                                                    *)
(* ====================================================================== *)

(* (-1)^k as a ring element. *)
let minus_one_pow (#t: Type) {| cr: commutative_ring t |} (k: nat) : t
  = if Prims.op_Modulus k 2 = 0 then one else (- (one #t))

let minus_one_pow_zero (#t: Type) {| cr: commutative_ring t |}
  : Lemma (minus_one_pow #t 0 == one)
  = ()

let minus_one_pow_one (#t: Type) {| cr: commutative_ring t |}
  : Lemma (minus_one_pow #t 1 == (- (one #t)))
  = ()

let minus_one_pow_even (#t: Type) {| cr: commutative_ring t |} (k: nat)
  : Lemma (requires Prims.op_Modulus k 2 = 0)
          (ensures  minus_one_pow #t k == one)
  = ()

let minus_one_pow_odd (#t: Type) {| cr: commutative_ring t |} (k: nat)
  : Lemma (requires Prims.op_Modulus k 2 = 1)
          (ensures  minus_one_pow #t k == (- (one #t)))
  = ()

(* Skip the index `i` when injecting fin (n-1) into fin n. *)
let skip (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1)) : fin n
  = if (a <: nat) < (i <: nat) then (a <: nat) else Prims.op_Addition a 1

let skip_lt (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1))
  : Lemma (requires (a <: nat) < (i <: nat))
          (ensures  (skip i a <: nat) == (a <: nat))
  = ()

let skip_ge (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1))
  : Lemma (requires (a <: nat) >= (i <: nat))
          (ensures  (skip i a <: nat) == Prims.op_Addition a 1)
  = ()

(* skip is injective. *)
let skip_injective (#n: pos) (i: fin n) (a b: fin (Prims.op_Subtraction n 1))
  : Lemma (requires (skip i a <: nat) == (skip i b <: nat))
          (ensures  (a <: nat) == (b <: nat))
  = ()

(* skip never lands on i. *)
let skip_avoids (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1))
  : Lemma (~((skip i a <: nat) == (i <: nat)))
  = ()

(* The (n-1) x (n-1) minor of m at row i, column j: delete row i and column j. *)
let minor (#t: Type) (#n: pos) (m: square_matrix t n) (i j: fin n)
  : square_matrix t (Prims.op_Subtraction n 1)
  = fun (a: fin (Prims.op_Subtraction n 1)) (b: fin (Prims.op_Subtraction n 1))
      -> m (skip i a) (skip j b)

let minor_at (#t: Type) (#n: pos) (m: square_matrix t n) (i j: fin n)
             (a b: fin (Prims.op_Subtraction n 1))
  : Lemma (minor m i j a b == m (skip i a) (skip j b))
  = ()

(* ====================================================================== *)
(*  inject: building a permutation of fin n from a permutation of         *)
(*          fin (n-1) and a chosen image j for position i.                *)
(* ====================================================================== *)

(* Partial inverse of `skip i`: removes index i, mapping fin n \ {i} into fin (n-1). *)
let unskip (#n: pos) (i: fin n) (k: fin n{(k <: nat) <> (i <: nat)})
  : fin (Prims.op_Subtraction n 1)
  = if (k <: nat) < (i <: nat) then (k <: nat) else Prims.op_Subtraction k 1

let skip_unskip (#n: pos) (i: fin n) (k: fin n)
  : Lemma (requires (k <: nat) <> (i <: nat))
          (ensures  (skip i (unskip i k) <: nat) == (k <: nat))
  = ()

let unskip_skip (#n: pos) (i: fin n) (a: fin (Prims.op_Subtraction n 1))
  : Lemma ((unskip i (skip i a) <: nat) == (a <: nat))
  = ()

(* Build a permutation of fin n with sigma(i) = j whose action on the
   remaining positions is determined by sigma' via the canonical relabelling. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let inject (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1))
           (i j: fin n)
  : permutation n
  = let fwd (k: fin n) : fin n
      = if (k <: nat) = (i <: nat) then j
        else skip j (sigma'.fwd (unskip i k)) in
    let bwd (l: fin n) : fin n
      = if (l <: nat) = (j <: nat) then i
        else skip i (sigma'.bwd (unskip j l)) in
    let fwd_bwd_id (l: fin n) : Lemma (fwd (bwd l) == l)
      = if (l <: nat) = (j <: nat) then ()
        else begin
          let u : fin (Prims.op_Subtraction n 1) = unskip j l in
          let a' : fin (Prims.op_Subtraction n 1) = sigma'.bwd u in
          let k : fin n = skip i a' in
          skip_avoids i a';
          unskip_skip i a';
          sigma'.fwd_bwd_id u;
          skip_unskip j l
        end in
    let bwd_fwd_id (k: fin n) : Lemma (bwd (fwd k) == k)
      = if (k <: nat) = (i <: nat) then ()
        else begin
          let a : fin (Prims.op_Subtraction n 1) = unskip i k in
          let b : fin (Prims.op_Subtraction n 1) = sigma'.fwd a in
          let l : fin n = skip j b in
          skip_avoids j b;
          unskip_skip j b;
          sigma'.bwd_fwd_id a;
          skip_unskip i k
        end in
    { fwd; bwd; fwd_bwd_id; bwd_fwd_id }
#pop-options

let inject_fwd_at_i (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1))
                    (i j: fin n)
  : Lemma ((inject sigma' i j).fwd i == j)
  = ()

let inject_fwd_off (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1))
                   (i j: fin n) (k: fin n)
  : Lemma (requires (k <: nat) <> (i <: nat))
          (ensures  (inject sigma' i j).fwd k
                    == skip j (sigma'.fwd (unskip i k)))
  = ()

let inject_bwd_at_j (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1))
                    (i j: fin n)
  : Lemma ((inject sigma' i j).bwd j == i)
  = ()

(* ====================================================================== *)
(*  project: inverse of `inject`.                                         *)
(* ====================================================================== *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let project (#n: pos) (sigma: permutation n) (i: fin n)
  : permutation (Prims.op_Subtraction n 1)
  = let j : fin n = sigma.fwd i in
    sigma.bwd_fwd_id i;
    assert (sigma.bwd j == i);
    sigma.fwd_bwd_id (sigma.fwd i);
    let fwd (a: fin (Prims.op_Subtraction n 1))
      : fin (Prims.op_Subtraction n 1)
      = let k : fin n = skip i a in
        skip_avoids i a;
        assert (~((k <: nat) == (i <: nat)));
        let v : fin n = sigma.fwd k in
        sigma.bwd_fwd_id k;
        assert (sigma.bwd v == k);
        sigma.bwd_fwd_id i;
        assert (sigma.bwd j == i);
        assert (~((v <: nat) == (j <: nat)));
        unskip j v in
    let bwd (b: fin (Prims.op_Subtraction n 1))
      : fin (Prims.op_Subtraction n 1)
      = let l : fin n = skip j b in
        skip_avoids j b;
        assert (~((l <: nat) == (j <: nat)));
        let w : fin n = sigma.bwd l in
        sigma.fwd_bwd_id l;
        assert (sigma.fwd w == l);
        sigma.bwd_fwd_id i;
        assert (sigma.bwd j == i);
        assert (~((w <: nat) == (i <: nat)));
        unskip i w in
    let fwd_bwd_id (b: fin (Prims.op_Subtraction n 1))
      : Lemma (fwd (bwd b) == b)
      = let l : fin n = skip j b in
        skip_avoids j b;
        let w : fin n = sigma.bwd l in
        sigma.fwd_bwd_id l;
        assert (~((w <: nat) == (i <: nat)));
        let a : fin (Prims.op_Subtraction n 1) = unskip i w in
        skip_unskip i w;
        assert ((skip i a <: nat) == (w <: nat));
        let v : fin n = sigma.fwd (skip i a) in
        assert ((skip i a <: nat) == (w <: nat));
        assert (sigma.fwd w == l);
        unskip_skip j b in
    let bwd_fwd_id (a: fin (Prims.op_Subtraction n 1))
      : Lemma (bwd (fwd a) == a)
      = let k : fin n = skip i a in
        skip_avoids i a;
        let v : fin n = sigma.fwd k in
        sigma.bwd_fwd_id k;
        assert (~((v <: nat) == (j <: nat)));
        let b : fin (Prims.op_Subtraction n 1) = unskip j v in
        skip_unskip j v;
        assert ((skip j b <: nat) == (v <: nat));
        let w : fin n = sigma.bwd (skip j b) in
        assert (sigma.bwd v == k);
        unskip_skip i a in
    { fwd; bwd; fwd_bwd_id; bwd_fwd_id }
#pop-options

(* Roundtrip: inject (project sigma i) i (sigma.fwd i) is perm_eq to sigma. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let inject_project_roundtrip (#n: pos) (sigma: permutation n) (i: fin n)
  : Lemma (perm_eq (inject (project sigma i) i (sigma.fwd i)) sigma)
  = let j : fin n = sigma.fwd i in
    let sigma' = project sigma i in
    let injected = inject sigma' i j in
    sigma.bwd_fwd_id i;
    assert (sigma.bwd j == i);
    let pointwise (k: fin n) : Lemma (injected.fwd k == sigma.fwd k)
      = if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i sigma' i j
        end else begin
          inject_fwd_off sigma' i j k;
          let a : fin (Prims.op_Subtraction n 1) = unskip i k in
          assert (injected.fwd k == skip j (sigma'.fwd a));
          skip_unskip i k;
          assert ((skip i a <: nat) == (k <: nat));
          sigma'.bwd_fwd_id a;
          let b : fin (Prims.op_Subtraction n 1) = sigma'.fwd a in
          let lhs1 : fin n = skip j b in
          skip_avoids j b;
          assert (~((lhs1 <: nat) == (j <: nat)));
          let w : fin n = sigma.bwd lhs1 in
          sigma.fwd_bwd_id lhs1;
          assert (sigma.fwd w == lhs1);
          assert (~((w <: nat) == (i <: nat)));
          assert (sigma'.bwd b == unskip i w);
          assert (unskip i w == a);
          skip_unskip i w;
          assert ((skip i (unskip i w) <: nat) == (w <: nat));
          assert ((skip i a <: nat) == (w <: nat));
          assert ((w <: nat) == (k <: nat));
          assert (sigma.fwd w == skip j b);
          assert ((w <: nat) == (k <: nat));
          assert (sigma.fwd k == sigma.fwd w);
          assert (injected.fwd k == skip j (sigma'.fwd a))
        end in
    Classical.forall_intro pointwise;
    perm_eq_intro injected sigma pointwise
#pop-options

(* --- Lemma: inject id i i is identity --------------------------------- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let inject_id_is_identity (#n: pos) (i: fin n)
  : Lemma (perm_eq (inject (identity (Prims.op_Subtraction n 1)) i i) (identity n))
  = let sigma' = identity (Prims.op_Subtraction n 1) in
    let inj = inject sigma' i i in
    let pointwise (k: fin n) : Lemma (inj.fwd k == (identity n).fwd k)
      = if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i sigma' i i;
          identity_fwd n k
        end else begin
          inject_fwd_off sigma' i i k;
          identity_fwd (Prims.op_Subtraction n 1) (unskip i k);
          skip_unskip i k;
          identity_fwd n k
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj (identity n) pointwise
#pop-options

(* --- Lemma: inject (compose σ1 σ2) i i ≡ compose (inject σ1 i i) (inject σ2 i i) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let inject_compose_diag (#n: pos)
  (sigma1 sigma2: permutation (Prims.op_Subtraction n 1)) (i: fin n)
  : Lemma (perm_eq (inject (compose sigma1 sigma2) i i)
                   (compose (inject sigma1 i i) (inject sigma2 i i)))
  = let c = compose sigma1 sigma2 in
    let inj_c = inject c i i in
    let comp = compose (inject sigma1 i i) (inject sigma2 i i) in
    let pointwise (k: fin n) : Lemma (inj_c.fwd k == comp.fwd k)
      = compose_fwd (inject sigma1 i i) (inject sigma2 i i) k;
        if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i c i i;
          inject_fwd_at_i sigma2 i i;
          inject_fwd_at_i sigma1 i i
        end else begin
          inject_fwd_off c i i k;
          inject_fwd_off sigma2 i i k;
          let a : fin (Prims.op_Subtraction n 1) = unskip i k in
          let b : fin (Prims.op_Subtraction n 1) = sigma2.fwd a in
          let m : fin n = skip i b in
          skip_avoids i b;
          inject_fwd_off sigma1 i i m;
          unskip_skip i b;
          compose_fwd sigma1 sigma2 a
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj_c comp pointwise
#pop-options

(* --- Lemma: inject (transposition a b) i i ≡ transposition n (skip i a) (skip i b) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let inject_transposition_diag (#n: pos)
  (a b: fin (Prims.op_Subtraction n 1)) (i: fin n)
  : Lemma (perm_eq (inject (transposition (Prims.op_Subtraction n 1) a b) i i)
                   (transposition n (skip i a) (skip i b)))
  = let tau = transposition (Prims.op_Subtraction n 1) a b in
    let inj = inject tau i i in
    let sa : fin n = skip i a in
    let sb : fin n = skip i b in
    let tr = transposition n sa sb in
    let pointwise (k: fin n) : Lemma (inj.fwd k == tr.fwd k)
      = if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i tau i i;
          skip_avoids i a;
          skip_avoids i b;
          transposition_fwd_other n sa sb i
        end else begin
          inject_fwd_off tau i i k;
          let u : fin (Prims.op_Subtraction n 1) = unskip i k in
          if (u <: nat) = (a <: nat) then begin
            transposition_fwd_left (Prims.op_Subtraction n 1) a b;
            assert (tau.fwd u == b);
            assert (skip i (tau.fwd u) == sb);
            unskip_skip i a;
            assert ((u <: nat) == (a <: nat));
            skip_unskip i k;
            assert ((skip i u <: nat) == (k <: nat));
            assert ((k <: nat) == (sa <: nat));
            transposition_fwd_left n sa sb
          end else if (u <: nat) = (b <: nat) then begin
            transposition_fwd_right (Prims.op_Subtraction n 1) a b;
            assert (tau.fwd u == a);
            assert (skip i (tau.fwd u) == sa);
            unskip_skip i b;
            skip_unskip i k;
            assert ((k <: nat) == (sb <: nat));
            transposition_fwd_right n sa sb
          end else begin
            transposition_fwd_other (Prims.op_Subtraction n 1) a b u;
            assert (tau.fwd u == u);
            assert (skip i (tau.fwd u) == skip i u);
            skip_unskip i k;
            assert ((skip i u <: nat) == (k <: nat));
            skip_avoids i a;
            skip_avoids i b;
            unskip_skip i a;
            unskip_skip i b;
            assert (~((k <: nat) == (sa <: nat)));
            assert (~((k <: nat) == (sb <: nat)));
            transposition_fwd_other n sa sb k
          end
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj tr pointwise
#pop-options

(* --- skip i d ≠ skip i (d+1) when d+1 < n-1 --- *)
let skip_adjacent_distinct (#n: pos) (i: fin n) (d: nat{Prims.op_Addition d 1 < Prims.op_Subtraction n 1})
  : Lemma (~((skip i (d <: fin (Prims.op_Subtraction n 1)) <: nat) ==
             (skip i ((Prims.op_Addition d 1) <: fin (Prims.op_Subtraction n 1)) <: nat)))
  = let a : fin (Prims.op_Subtraction n 1) = d in
    let b : fin (Prims.op_Subtraction n 1) = Prims.op_Addition d 1 in
    let h () : Lemma (requires (skip i a <: nat) == (skip i b <: nat)) (ensures False)
      = skip_injective i a b
    in
    Classical.move_requires h ()

(* --- parity_inject_diag: parity (inject σ' i i) == parity σ' --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let rec parity_inject_diag (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1)) (i: fin n)
  : Lemma (ensures parity (inject sigma' i i) == parity sigma')
          (decreases (inversion_count sigma'))
  = let nm1 = Prims.op_Subtraction n 1 in
    match find_descent sigma' 0 with
    | None ->
      find_descent_none_implies_inv_zero sigma';
      let aux (k: fin nm1) : Lemma (sigma'.fwd k == k)
        = inv_zero_implies_identity_fwd sigma' k
      in
      Classical.forall_intro aux;
      let aux2 (k: fin nm1) : Lemma (sigma'.fwd k == (identity nm1).fwd k)
        = aux k; identity_fwd nm1 k
      in
      Classical.forall_intro aux2;
      perm_eq_intro sigma' (identity nm1) aux2;
      parity_perm_eq_invariant sigma' (identity nm1);
      parity_identity nm1;
      inject_id_is_identity i;
      let inj_id = inject (identity nm1) i i in
      let inj_s = inject sigma' i i in
      let pw (k: fin n) : Lemma (inj_s.fwd k == inj_id.fwd k)
        = if (k <: nat) = (i <: nat) then begin
            inject_fwd_at_i sigma' i i;
            inject_fwd_at_i (identity nm1) i i
          end else begin
            inject_fwd_off sigma' i i k;
            inject_fwd_off (identity nm1) i i k;
            identity_fwd nm1 (unskip i k)
          end
      in
      Classical.forall_intro pw;
      perm_eq_intro inj_s inj_id pw;
      parity_perm_eq_invariant inj_s inj_id;
      parity_perm_eq_invariant inj_id (identity n);
      parity_identity n
    | Some d ->
      inv_right_swap_at_descent sigma' d;
      let sigma2 = right_swap sigma' d in
      let tau_small = transposition nm1 (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1) in
      inject_compose_diag sigma' tau_small i;
      inject_transposition_diag (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1) i;
      let inj_tau = inject tau_small i i in
      let sa : fin n = skip i (d <: fin nm1) in
      let sb : fin n = skip i ((Prims.op_Addition d 1) <: fin nm1) in
      let tau_big = transposition n sa sb in
      parity_perm_eq_invariant inj_tau tau_big;
      parity_transposition n sa sb;
      skip_adjacent_distinct i d;
      assert (parity tau_big == false);
      assert (parity inj_tau == false);
      let comp = compose sigma' tau_small in
      let pw_comp (k: fin nm1) : Lemma (comp.fwd k == sigma2.fwd k)
        = compose_fwd sigma' tau_small k;
          if (k <: nat) = d then begin
            right_swap_fwd_at_i sigma' d;
            transposition_fwd_left nm1 (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1)
          end else if (k <: nat) = Prims.op_Addition d 1 then begin
            right_swap_fwd_at_i_plus_1 sigma' d;
            transposition_fwd_right nm1 (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1)
          end else begin
            right_swap_fwd_at_other sigma' d k;
            transposition_fwd_other nm1 (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1) k
          end
      in
      Classical.forall_intro pw_comp;
      perm_eq_intro comp sigma2 pw_comp;
      parity_perm_eq_invariant comp sigma2;
      let inj_comp = inject comp i i in
      let inj_s = inject sigma' i i in
      let composed = compose inj_s inj_tau in
      let inj_s2 = inject sigma2 i i in
      let pw_s2 (k: fin n) : Lemma (inj_comp.fwd k == inj_s2.fwd k)
        = if (k <: nat) = (i <: nat) then begin
            inject_fwd_at_i comp i i;
            inject_fwd_at_i sigma2 i i
          end else begin
            inject_fwd_off comp i i k;
            inject_fwd_off sigma2 i i k
          end
      in
      Classical.forall_intro pw_s2;
      perm_eq_intro inj_comp inj_s2 pw_s2;
      parity_perm_eq_invariant inj_comp inj_s2;
      parity_perm_eq_invariant inj_comp composed;
      sign_homomorphism inj_s inj_tau;
      parity_inject_diag sigma2 i;
      assert (parity inj_s2 == parity sigma2);
      sign_homomorphism sigma' tau_small;
      parity_transposition nm1 (d <: fin nm1) ((Prims.op_Addition d 1) <: fin nm1);
      perm_eq_sym_local comp sigma2;
      parity_perm_eq_invariant sigma2 comp;
      assert (parity comp == (parity sigma' = parity tau_small));
      assert (parity tau_small == false);
      assert (parity sigma2 == not (parity sigma'));
      assert (parity composed == (parity inj_s = parity inj_tau));
      assert (parity inj_tau == false);
      assert (parity inj_comp == parity composed);
      assert (parity inj_comp == parity inj_s2)
#pop-options

(* --- inject σ' i j ≡ compose (inject id i j) (inject σ' i i) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 40"
let inject_compose_decomp (#n: pos)
  (sigma': permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (perm_eq (inject sigma' i j)
                   (compose (inject (identity (Prims.op_Subtraction n 1)) i j)
                            (inject sigma' i i)))
  = let nm1 = Prims.op_Subtraction n 1 in
    let id_perm = identity nm1 in
    let inj_s = inject sigma' i j in
    let inj_id = inject id_perm i j in
    let inj_diag = inject sigma' i i in
    let comp = compose inj_id inj_diag in
    let pointwise (k: fin n) : Lemma (inj_s.fwd k == comp.fwd k)
      = compose_fwd inj_id inj_diag k;
        if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i sigma' i j;
          inject_fwd_at_i sigma' i i;
          inject_fwd_at_i id_perm i j
        end else begin
          inject_fwd_off sigma' i j k;
          inject_fwd_off sigma' i i k;
          let a : fin nm1 = unskip i k in
          let b : fin nm1 = sigma'.fwd a in
          let m : fin n = skip i b in
          skip_avoids i b;
          inject_fwd_off id_perm i j m;
          identity_fwd nm1 (unskip i m);
          unskip_skip i b
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj_s comp pointwise
#pop-options

(* --- inject id step: for i < j, inject id i j ≡ compose (transposition (j-1) j) (inject id i (j-1)) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let inject_id_step_down (#n: pos) (i j: fin n)
  : Lemma (requires (i <: nat) < (j <: nat))
          (ensures perm_eq (inject (identity (Prims.op_Subtraction n 1)) i j)
                           (compose (transposition n (Prims.op_Subtraction j 1 <: fin n) j)
                                    (inject (identity (Prims.op_Subtraction n 1)) i (Prims.op_Subtraction j 1 <: fin n))))
  = let nm1 = Prims.op_Subtraction n 1 in
    let id_perm = identity nm1 in
    let jm1 : fin n = Prims.op_Subtraction j 1 in
    let inj_j = inject id_perm i j in
    let inj_jm1 = inject id_perm i jm1 in
    let tau = transposition n jm1 j in
    let comp = compose tau inj_jm1 in
    let pointwise (k: fin n) : Lemma (inj_j.fwd k == comp.fwd k)
      = compose_fwd tau inj_jm1 k;
        if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i id_perm i j;
          inject_fwd_at_i id_perm i jm1;
          transposition_fwd_left n jm1 j
        end else begin
          inject_fwd_off id_perm i j k;
          inject_fwd_off id_perm i jm1 k;
          identity_fwd nm1 (unskip i k);
          let u : fin nm1 = unskip i k in
          let val_j : fin n = skip j u in
          let val_jm1 : fin n = skip jm1 u in
          if (u <: nat) < (Prims.op_Subtraction j 1) then begin
            skip_lt j u;
            skip_lt jm1 u;
            assert ((val_j <: nat) == (u <: nat));
            assert ((val_jm1 <: nat) == (u <: nat));
            transposition_fwd_other n jm1 j val_jm1
          end else if (u <: nat) = Prims.op_Subtraction j 1 then begin
            skip_lt j u;
            skip_ge jm1 u;
            assert ((val_j <: nat) == (u <: nat));
            assert ((val_jm1 <: nat) == Prims.op_Addition u 1);
            assert ((val_j <: nat) == Prims.op_Subtraction j 1);
            assert ((val_jm1 <: nat) == (j <: nat));
            transposition_fwd_right n jm1 j
          end else begin
            skip_ge j u;
            skip_ge jm1 u;
            assert ((val_j <: nat) == Prims.op_Addition u 1);
            assert ((val_jm1 <: nat) == Prims.op_Addition u 1);
            transposition_fwd_other n jm1 j val_jm1
          end
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj_j comp pointwise
#pop-options

(* --- inject id step: for j < i, inject id i j ≡ compose (transposition j (j+1)) (inject id i (j+1)) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let inject_id_step_up (#n: pos) (i j: fin n)
  : Lemma (requires (j <: nat) < (i <: nat))
          (ensures perm_eq (inject (identity (Prims.op_Subtraction n 1)) i j)
                           (compose (transposition n j (Prims.op_Addition j 1 <: fin n))
                                    (inject (identity (Prims.op_Subtraction n 1)) i (Prims.op_Addition j 1 <: fin n))))
  = let nm1 = Prims.op_Subtraction n 1 in
    let id_perm = identity nm1 in
    let jp1 : fin n = Prims.op_Addition j 1 in
    let inj_j = inject id_perm i j in
    let inj_jp1 = inject id_perm i jp1 in
    let tau = transposition n j jp1 in
    let comp = compose tau inj_jp1 in
    let pointwise (k: fin n) : Lemma (inj_j.fwd k == comp.fwd k)
      = compose_fwd tau inj_jp1 k;
        if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i id_perm i j;
          inject_fwd_at_i id_perm i jp1;
          transposition_fwd_right n j jp1
        end else begin
          inject_fwd_off id_perm i j k;
          inject_fwd_off id_perm i jp1 k;
          identity_fwd nm1 (unskip i k);
          let u : fin nm1 = unskip i k in
          let val_j : fin n = skip j u in
          let val_jp1 : fin n = skip jp1 u in
          if (u <: nat) < (j <: nat) then begin
            skip_lt j u;
            skip_lt jp1 u;
            assert ((val_j <: nat) == (u <: nat));
            assert ((val_jp1 <: nat) == (u <: nat));
            transposition_fwd_other n j jp1 val_jp1
          end else if (u <: nat) = (j <: nat) then begin
            skip_ge j u;
            skip_lt jp1 u;
            assert ((val_j <: nat) == Prims.op_Addition u 1);
            assert ((val_jp1 <: nat) == (u <: nat));
            assert ((val_j <: nat) == (jp1 <: nat));
            assert ((val_jp1 <: nat) == (j <: nat));
            transposition_fwd_left n j jp1
          end else begin
            skip_ge j u;
            skip_ge jp1 u;
            assert ((val_j <: nat) == Prims.op_Addition u 1);
            assert ((val_jp1 <: nat) == Prims.op_Addition u 1);
            transposition_fwd_other n j jp1 val_jp1
          end
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj_j comp pointwise
#pop-options

(* --- Boolean arithmetic helper --- *)
private let bool_not_even_succ (a b: nat)
  : Lemma (not ((Prims.op_Addition a b) % 2 = 0) == ((Prims.op_Addition a (Prims.op_Addition b 1)) % 2 = 0))
  = ()

private let bool_not_even_pred (a b: nat)
  : Lemma (requires b > 0)
          (ensures not ((Prims.op_Addition a b) % 2 = 0) == ((Prims.op_Addition a (Prims.op_Subtraction b 1)) % 2 = 0))
  = ()

(* --- parity_inject_id: parity (inject id i j) == ((i+j) % 2 = 0) --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let rec parity_inject_id (#n: pos) (i j: fin n)
  : Lemma (ensures parity (inject (identity (Prims.op_Subtraction n 1)) i j) ==
                   ((Prims.op_Addition (i <: nat) (j <: nat)) % 2 = 0))
          (decreases (if (j <: nat) >= (i <: nat) then Prims.op_Subtraction (j <: nat) (i <: nat) else Prims.op_Subtraction (i <: nat) (j <: nat)))
  = let nm1 = Prims.op_Subtraction n 1 in
    let id_perm = identity nm1 in
    if (j <: nat) = (i <: nat) then begin
      inject_id_is_identity i;
      parity_perm_eq_invariant (inject id_perm i j) (identity n);
      parity_identity n
    end else if (j <: nat) > (i <: nat) then begin
      let jm1 : fin n = Prims.op_Subtraction j 1 in
      inject_id_step_down i j;
      let tau = transposition n jm1 j in
      let inj_jm1 = inject id_perm i jm1 in
      let comp = compose tau inj_jm1 in
      parity_perm_eq_invariant (inject id_perm i j) comp;
      sign_homomorphism tau inj_jm1;
      parity_transposition n jm1 j;
      assert (parity tau == false);
      parity_inject_id i jm1;
      assert (parity inj_jm1 == ((Prims.op_Addition (i <: nat) (jm1 <: nat)) % 2 = 0));
      assert (parity comp == (parity tau = parity inj_jm1));
      assert (parity comp == (false = parity inj_jm1));
      assert (parity comp == not (parity inj_jm1));
      bool_not_even_pred (i <: nat) (j <: nat)
    end else begin
      let jp1 : fin n = Prims.op_Addition j 1 in
      inject_id_step_up i j;
      let tau = transposition n j jp1 in
      let inj_jp1 = inject id_perm i jp1 in
      let comp = compose tau inj_jp1 in
      parity_perm_eq_invariant (inject id_perm i j) comp;
      sign_homomorphism tau inj_jp1;
      parity_transposition n j jp1;
      assert (parity tau == false);
      parity_inject_id i jp1;
      assert (parity inj_jp1 == ((Prims.op_Addition (i <: nat) (jp1 <: nat)) % 2 = 0));
      assert (parity comp == not (parity inj_jp1));
      bool_not_even_succ (i <: nat) (j <: nat)
    end
#pop-options

(* --- MAIN: parity_inject --- *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let parity_inject (#n: pos) (sigma': permutation (Prims.op_Subtraction n 1))
                  (i j: fin n)
  : Lemma (parity (inject sigma' i j) ==
           (parity sigma' = ((Prims.op_Addition (i <: nat) (j <: nat)) % 2 = 0)))
  = let nm1 = Prims.op_Subtraction n 1 in
    let id_perm = identity nm1 in
    inject_compose_decomp sigma' i j;
    let inj_s = inject sigma' i j in
    let inj_id = inject id_perm i j in
    let inj_diag = inject sigma' i i in
    let comp = compose inj_id inj_diag in
    parity_perm_eq_invariant inj_s comp;
    sign_homomorphism inj_id inj_diag;
    parity_inject_id i j;
    parity_inject_diag sigma' i;
    assert (parity comp == (parity inj_id = parity inj_diag));
    assert (parity inj_id == ((Prims.op_Addition (i <: nat) (j <: nat)) % 2 = 0));
    assert (parity inj_diag == parity sigma')
#pop-options

(* ====================================================================== *)
(*  inject preserves/reflects perm_eq                                     *)
(* ====================================================================== *)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let inject_preserves_perm_eq (#n: pos)
  (sp1 sp2: permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (requires perm_eq sp1 sp2)
          (ensures perm_eq (inject sp1 i j) (inject sp2 i j))
  = let aux (k: fin n) : Lemma ((inject sp1 i j).fwd k == (inject sp2 i j).fwd k)
      = if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i sp1 i j;
          inject_fwd_at_i sp2 i j
        end else begin
          inject_fwd_off sp1 i j k;
          inject_fwd_off sp2 i j k;
          perm_eq_elim sp1 sp2 (unskip i k)
        end
    in Classical.forall_intro aux;
    perm_eq_intro (inject sp1 i j) (inject sp2 i j) aux
#pop-options

(* inject reflects perm_eq *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let inject_reflects_perm_eq (#n: pos)
  (sp1 sp2: permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (requires perm_eq (inject sp1 i j) (inject sp2 i j))
          (ensures perm_eq sp1 sp2)
  = let aux (a: fin (Prims.op_Subtraction n 1))
      : Lemma (sp1.fwd a == sp2.fwd a)
      = let k = skip i a in
        skip_avoids i a;
        inject_fwd_off sp1 i j k;
        inject_fwd_off sp2 i j k;
        assert ((inject sp1 i j).fwd k == skip j (sp1.fwd a));
        assert ((inject sp2 i j).fwd k == skip j (sp2.fwd a));
        perm_eq_elim (inject sp1 i j) (inject sp2 i j) k;
        skip_injective j (sp1.fwd a) (sp2.fwd a)
    in Classical.forall_intro aux;
    perm_eq_intro sp1 sp2 aux
#pop-options

(* respects_perm_eq transfers through inject *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let respects_perm_eq_inject (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  : Lemma (requires respects_perm_eq f)
          (ensures respects_perm_eq (fun s' -> f (inject s' i j)))
  = let g : permutation (Prims.op_Subtraction n 1) -> t
      = fun s' -> f (inject s' i j) in
    let aux (sp1 sp2: permutation (Prims.op_Subtraction n 1))
      : Lemma (perm_eq sp1 sp2 ==> g sp1 = g sp2)
      = if FStar.IndefiniteDescription.strong_excluded_middle (perm_eq sp1 sp2) then begin
          inject_preserves_perm_eq sp1 sp2 i j;
          respects_perm_eq_elim f (inject sp1 i j) (inject sp2 i j)
        end
    in Classical.forall_intro_2 aux;
    respects_perm_eq_intro g (fun _ _ -> ())
#pop-options

(* ====================================================================== *)
(*  Fiber list: partition S_n by the image of i.                          *)
(* ====================================================================== *)

(* If perm_eq p (inject sp i j), then p.fwd i == j *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let perm_eq_inject_fwd_i (#n: pos) (p: permutation n)
  (sp: permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (requires perm_eq p (inject sp i j))
          (ensures (p.fwd i <: nat) == (j <: nat))
  = inject_fwd_at_i sp i j;
    perm_eq_elim p (inject sp i j) i
#pop-options

(* If p.fwd i ≠ j, then perm_eq p (inject sp i j) is false. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let perm_eq_inject_false (#n: pos) (p: permutation n)
  (sp: permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (requires (p.fwd i <: nat) <> (j <: nat))
          (ensures perm_eq p (inject sp i j) == false)
  = inject_fwd_at_i sp i j;
    if perm_eq p (inject sp i j) then
      perm_eq_elim p (inject sp i j) i
    else ()
#pop-options

(* If p.fwd i == j, then perm_eq p (inject sp i j) ==
   perm_eq (project p i) sp. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let perm_eq_inject_match (#n: pos) (p: permutation n)
  (sp: permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (requires (p.fwd i <: nat) == (j <: nat))
          (ensures perm_eq p (inject sp i j) == perm_eq (project p i) sp)
  = let pp = project p i in
    if perm_eq p (inject sp i j) then begin
      inject_project_roundtrip p i;
      let inj_pp = inject pp i j in
      let aux (k: fin n) : Lemma (inj_pp.fwd k == (inject sp i j).fwd k)
        = perm_eq_elim inj_pp p k;
          perm_eq_elim p (inject sp i j) k
      in Classical.forall_intro aux;
      perm_eq_intro inj_pp (inject sp i j) aux;
      inject_reflects_perm_eq pp sp i j;
      let aux2 (a: fin (Prims.op_Subtraction n 1)) : Lemma (pp.fwd a == sp.fwd a)
        = perm_eq_elim pp sp a
      in Classical.forall_intro aux2;
      perm_eq_intro pp sp aux2
    end else begin
      if perm_eq pp sp then begin
        let aux_eq (a: fin (Prims.op_Subtraction n 1)) : Lemma (pp.fwd a == sp.fwd a)
          = perm_eq_elim pp sp a
        in Classical.forall_intro aux_eq;
        perm_eq_intro pp sp aux_eq;
        inject_preserves_perm_eq pp sp i j;
        inject_project_roundtrip p i;
        let aux_fwd (k: fin n) : Lemma (p.fwd k == (inject sp i j).fwd k)
          = let inj_pp = inject pp i j in
            perm_eq_elim inj_pp p k;
            perm_eq_elim inj_pp (inject sp i j) k
        in Classical.forall_intro aux_fwd;
        perm_eq_intro p (inject sp i j) aux_fwd
      end else ()
    end
#pop-options

(* Build the inject-image list directly, avoiding L.map to help Z3. *)
let rec fiber_list (#n: pos) (i j: fin n)
  (xs: list (permutation (Prims.op_Subtraction n 1)))
  : Tot (list (permutation n)) (decreases xs)
  = match xs with
    | [] -> []
    | hd :: tl -> inject hd i j :: fiber_list i j tl

(* Named wrapper for inject with i,j fixed — avoids anonymous lambda in L.map. *)
let inject_at (#n: pos) (i j: fin n) (sp: permutation (Prims.op_Subtraction n 1))
  : permutation n
  = inject sp i j

(* fiber_list is the same as L.map (inject_at i j). *)
let rec fiber_list_eq_map (#n: pos) (i j: fin n)
  (xs: list (permutation (Prims.op_Subtraction n 1)))
  : Lemma (ensures fiber_list i j xs == L.map (inject_at i j) xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: tl -> fiber_list_eq_map i j tl

(* Counting perm_eq matches in fiber_list: case p.fwd i ≠ j. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let rec fiber_list_count_ne (#n: pos) (p: permutation n)
  (i j: fin n) (xs: list (permutation (Prims.op_Subtraction n 1)))
  : Lemma (requires (p.fwd i <: nat) <> (j <: nat))
          (ensures perm_eq_count p (fiber_list i j xs) == 0)
          (decreases xs)
  = match xs with
    | [] ->
      perm_eq_count_nil p
    | hd :: xs' ->
        let injected = inject hd i j in
        let fl = fiber_list i j xs' in
        perm_eq_inject_false p hd i j;
        perm_eq_count_cons p injected fl;
        fiber_list_count_ne p i j xs'
#pop-options

(* Counting perm_eq matches in fiber_list: case p.fwd i == j. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec fiber_list_count_eq (#n: pos) (p: permutation n)
  (i j: fin n) (xs: list (permutation (Prims.op_Subtraction n 1)))
  : Lemma (requires (p.fwd i <: nat) == (j <: nat))
          (ensures perm_eq_count p (fiber_list i j xs) ==
                   perm_eq_count (project p i) xs)
          (decreases xs)
  = match xs with
    | [] ->
      perm_eq_count_nil p;
      perm_eq_count_nil (project p i)
    | hd :: xs' ->
        let injected = inject hd i j in
        let fl = fiber_list i j xs' in
        perm_eq_count_cons p injected fl;
        perm_eq_count_cons (project p i) hd xs';
        perm_eq_inject_match p hd i j;
        fiber_list_count_eq p i j xs'
#pop-options

(* Each fiber has count 0 or 1. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let fiber_count (#n: pos) (p: permutation n) (i j: fin n)
  : Lemma (perm_eq_count p (fiber_list i j (all_permutations (Prims.op_Subtraction n 1))) ==
           (if (p.fwd i <: nat) = (j <: nat) then 1 else 0))
  = let nm1 = Prims.op_Subtraction n 1 in
    if (p.fwd i <: nat) = (j <: nat) then begin
      fiber_list_count_eq p i j (all_permutations nm1);
      all_permutations_count_one nm1 (project p i)
    end else
      fiber_list_count_ne p i j (all_permutations nm1)
#pop-options

(* Build concatenated fibers from j_lo up to n-1. *)
let rec concat_fibers_from (#n: pos) (i: fin n) (j_lo: nat{j_lo <= n})
  : Tot (list (permutation n)) (decreases (Prims.op_Subtraction n j_lo))
  = if j_lo >= n then []
    else L.append
           (fiber_list i (j_lo <: fin n) (all_permutations (Prims.op_Subtraction n 1)))
           (concat_fibers_from i (Prims.op_Addition j_lo 1))

let concat_fibers (#n: pos) (i: fin n) : list (permutation n)
  = concat_fibers_from i 0

(* Count in concatenated fibers equals 1 for every permutation. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 70"
let rec concat_fibers_from_count (#n: pos) (p: permutation n)
  (i: fin n) (j_lo: nat{j_lo <= n})
  : Lemma (ensures perm_eq_count p (concat_fibers_from i j_lo) ==
                   (if (p.fwd i <: nat) >= j_lo then 1 else 0))
          (decreases (Prims.op_Subtraction n j_lo))
  = if j_lo >= n then perm_eq_count_nil p
    else begin
      let fl = fiber_list i (j_lo <: fin n)
                 (all_permutations (Prims.op_Subtraction n 1)) in
      let rest = concat_fibers_from i (Prims.op_Addition j_lo 1) in
      perm_eq_count_append p fl rest;
      fiber_count p i (j_lo <: fin n);
      concat_fibers_from_count p i (Prims.op_Addition j_lo 1)
    end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 50"
let concat_fibers_count_one (#n: pos) (p: permutation n) (i: fin n)
  : Lemma (perm_eq_count p (concat_fibers i) == 1)
  = concat_fibers_from_count p i 0
#pop-options

(* Named per-fiber function to avoid lambda-matching issues. *)
let per_fiber_fn (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  (sp: permutation (Prims.op_Subtraction n 1)) : t
  = f (inject_at i j sp)

(* sum_list (map f (fiber_list i j xs)) = sum_list (map (per_fiber_fn f i j) xs). *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let fiber_list_sum (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  (xs: list (permutation (Prims.op_Subtraction n 1)))
  : Lemma (ensures sum_list (L.map f (fiber_list i j xs)) =
                   sum_list (L.map (per_fiber_fn #t #cr f i j) xs))
  = fiber_list_eq_map i j xs;
    map_map_eq (inject_at i j) f xs;
    let pfn = per_fiber_fn #t #cr f i j in
    let g = fcomp f (inject_at i j) in
    let eq_pw (sp: permutation (Prims.op_Subtraction n 1))
      : Lemma (requires L.memP sp xs) (ensures pfn sp = g sp)
      = fcomp_unfold f (inject_at i j) sp;
        reflexivity (pfn sp)
    in Classical.forall_intro (Classical.move_requires eq_pw);
    sum_list_map_congruence pfn g xs (fun _ -> ());
    symmetry (sum_list (L.map pfn xs)) (sum_list (L.map g xs));
    reflexivity (sum_list (L.map f (fiber_list i j xs)))
#pop-options

(* Connect sum_list of fiber_list to sum_over_perms via per_fiber_fn. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let fiber_list_to_sum_over_perms (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  : Lemma (requires respects_perm_eq f)
          (ensures sum_list (L.map f (fiber_list i j (all_permutations (Prims.op_Subtraction n 1)))) =
                   sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #cr f i j))
  = let nm1 = Prims.op_Subtraction n 1 in
    let g = per_fiber_fn #t #cr f i j in
    fiber_list_sum #t #cr f i j (all_permutations nm1);
    let g_respects (s1 s2: permutation nm1)
      : Lemma (requires perm_eq s1 s2) (ensures g s1 = g s2)
      = inject_preserves_perm_eq s1 s2 i j;
        respects_perm_eq_elim f (inject s1 i j) (inject s2 i j)
    in Classical.forall_intro_2 (Classical.move_requires_2 g_respects);
    respects_perm_eq_intro g (fun _ _ -> ());
    let count_one (p: permutation nm1) : Lemma (perm_eq_count p (all_permutations nm1) == 1)
      = all_permutations_count_one nm1 p
    in Classical.forall_intro count_one;
    sum_over_perms_via_count_one_list g (all_permutations nm1) (fun _ -> ());
    symmetry (sum_over_perms nm1 g) (sum_list (L.map g (all_permutations nm1)));
    transitivity (sum_list (L.map f (fiber_list i j (all_permutations nm1))))
                 (sum_list (L.map g (all_permutations nm1)))
                 (sum_over_perms nm1 g)
#pop-options

(* Sum over concat_fibers_from decomposes into sum_range of sum_over_perms of fibers. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let rec concat_fibers_from_sum (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i: fin n)
  (j_lo: nat{j_lo <= n})
  : Lemma (requires respects_perm_eq f)
          (ensures sum_list (L.map f (concat_fibers_from i j_lo)) =
                   sum_range
                     (fun (k: nat) -> if k < n then sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #cr f i (k <: fin n)) else zero)
                     j_lo n)
          (decreases (Prims.op_Subtraction n j_lo))
  = let g (k: nat) : t = if k < n then sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #cr f i (k <: fin n)) else zero in
    if j_lo >= n then begin
      sum_list_nil #t #(cr.cr_r.r_add);
      sum_range_empty g j_lo n;
      reflexivity (zero #t)
    end else begin
      let j : fin n = j_lo in
      let nm1 = Prims.op_Subtraction n 1 in
      let fl = fiber_list i j (all_permutations nm1) in
      let rest = concat_fibers_from i (Prims.op_Addition j_lo 1) in
      L.map_append f fl rest;
      sum_list_append (L.map f fl) (L.map f rest);
      fiber_list_to_sum_over_perms #t #cr f i j;
      concat_fibers_from_sum #t #cr f i (Prims.op_Addition j_lo 1);
      sum_range_unfold_left g j_lo n;
      let a = sum_list (L.map f fl) in
      let b = sum_over_perms nm1 (per_fiber_fn #t #cr f i j) in
      let c = sum_list (L.map f rest) in
      let d = sum_range g (Prims.op_Addition j_lo 1) n in
      add_congruence a c b d;
      (* sum_range_unfold_left: sum_range g j_lo n == g j_lo + d propositionally,
         and g j_lo == b, so b+d == sum_range g j_lo n propositionally => reflexivity bridges *)
      reflexivity (sum_range g j_lo n);
      transitivity (a `( + )` c) (sum_range g j_lo n) (sum_range g j_lo n);
      transitivity (sum_list (L.map f (concat_fibers_from i j_lo)))
                   (a `( + )` c)
                   (sum_range g j_lo n)
    end
#pop-options

(* fin_sum form. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
let concat_fibers_sum_eq_fin_sum (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i: fin n)
  : Lemma (requires respects_perm_eq f)
          (ensures sum_list (L.map f (concat_fibers i)) =
                   fin_sum (fun (j: fin n) ->
                     sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #cr f i j)))
  = concat_fibers_from_sum #t #cr f i 0;
    assert (fin_sum (fun (j: fin n) ->
              sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #cr f i j))
            == sum_range
              (fun (k: nat) -> if k < n then sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #cr f i (k <: fin n)) else zero)
              0 n)
      by (FStar.Tactics.norm [delta_only [`%fin_sum]; iota; zeta; primops]; FStar.Tactics.trefl ())
#pop-options

(* === Main theorem: sum_over_perms_partition === *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let sum_over_perms_partition (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (i: fin n) (f: permutation n -> t)
  : Lemma (requires respects_perm_eq f)
          (ensures sum_over_perms n f =
                   fin_sum (fun (j: fin n) ->
                     sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #cr f i j)))
  = let count_one (p: permutation n)
      : Lemma (perm_eq_count p (concat_fibers i) == 1)
      = concat_fibers_count_one p i
    in Classical.forall_intro count_one;
    sum_over_perms_via_count_one_list f (concat_fibers i) (fun _ -> ());
    concat_fibers_sum_eq_fin_sum #t #cr f i;
    transitivity (sum_over_perms n f)
                 (sum_list (L.map f (concat_fibers i)))
                 (fin_sum (fun (j: fin n) -> sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #cr f i j)))
#pop-options

(* Partition targeting a named function g, bypassing anonymous-lambda issues. *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
private let rec concat_fibers_from_sum_target (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i: fin n) (g: fin n -> t)
  (j_lo: nat{j_lo <= n})
  : Lemma (requires respects_perm_eq f /\
                    (forall (j: fin n). sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #cr f i j) = g j))
          (ensures sum_list (L.map f (concat_fibers_from i j_lo)) =
                   sum_range
                     (fun (k: nat) -> if k < n then g (k <: fin n) else zero)
                     j_lo n)
          (decreases (Prims.op_Subtraction n j_lo))
  = let h (k: nat) : t = if k < n then g (k <: fin n) else zero in
    if j_lo >= n then begin
      sum_list_nil #t #(cr.cr_r.r_add);
      sum_range_empty h j_lo n;
      reflexivity (zero #t)
    end else begin
      let j : fin n = j_lo in
      let nm1 = Prims.op_Subtraction n 1 in
      let fl = fiber_list i j (all_permutations nm1) in
      let rest = concat_fibers_from i (Prims.op_Addition j_lo 1) in
      L.map_append f fl rest;
      sum_list_append (L.map f fl) (L.map f rest);
      fiber_list_to_sum_over_perms #t #cr f i j;
      concat_fibers_from_sum_target #t #cr f i g (Prims.op_Addition j_lo 1);
      sum_range_unfold_left h j_lo n;
      let a = sum_list (L.map f fl) in
      let b = sum_over_perms nm1 (per_fiber_fn #t #cr f i j) in
      let c = sum_list (L.map f rest) in
      let d = sum_range h (Prims.op_Addition j_lo 1) n in
      transitivity a b (g j);
      add_congruence a c (h j_lo) d;
      reflexivity (sum_range h j_lo n);
      transitivity (sum_list (L.map f (concat_fibers_from i j_lo)))
                   (a `( + )` c)
                   (sum_range h j_lo n)
    end
#pop-options

#push-options "--fuel 2 --ifuel 2 --z3rlimit 80"
let sum_over_perms_partition_target (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (i: fin n) (f: permutation n -> t) (g: fin n -> t)
  : Lemma (requires respects_perm_eq f /\
                    (forall (j: fin n). sum_over_perms (Prims.op_Subtraction n 1) (per_fiber_fn #t #cr f i j) = g j))
          (ensures sum_over_perms n f = fin_sum g)
  = let count_one (p: permutation n)
      : Lemma (perm_eq_count p (concat_fibers i) == 1)
      = concat_fibers_count_one p i
    in Classical.forall_intro count_one;
    sum_over_perms_via_count_one_list f (concat_fibers i) (fun _ -> ());
    concat_fibers_from_sum_target #t #cr f i g 0;
    assert (fin_sum g
            == sum_range
              (fun (k: nat) -> if k < n then g (k <: fin n) else zero)
              0 n)
      by (FStar.Tactics.norm [delta_only [`%fin_sum]; iota; zeta; primops]; FStar.Tactics.trefl ());
    transitivity (sum_over_perms n f)
                 (sum_list (L.map f (concat_fibers i)))
                 (fin_sum g)
#pop-options

(* ====================================================================== *)
(*  P3: perm_product factorization through inject.                        *)
(*                                                                        *)
(*  perm_product m (inject sigma' i j) = m i j * perm_product (minor m i j) sigma'*)
(* ====================================================================== *)

(* prod_range offset lemma: if g a == f (a+lo) pointwise, then
   prod_range f lo hi = prod_range g 0 (hi-lo). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let rec prod_range_offset_lem
  (#t: Type) {| cr: commutative_ring t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires lo <= hi /\
                     (forall (a: nat). 0 <= a /\ a < Prims.op_Subtraction hi lo ==>
                        g a = f (Prims.op_Addition a lo)))
          (ensures prod_range f lo hi = prod_range g 0 (Prims.op_Subtraction hi lo))
          (decreases (Prims.op_Subtraction hi lo))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let len = Prims.op_Subtraction hi lo in
    if lo >= hi then begin
      prod_range_empty f lo hi;
      prod_range_empty g 0 0
    end else begin
      prod_range_unfold_left f lo hi;
      prod_range_unfold_left g 0 len;
      assert (g 0 = f (Prims.op_Addition 0 lo));
      assert (Prims.op_Addition 0 lo == lo);
      let lo' = Prims.op_Addition lo 1 in
      let len' = Prims.op_Subtraction len 1 in
      let g' (a: nat) : t = g (Prims.op_Addition a 1) in
      let h (a: nat) : Lemma (requires 0 <= a /\ a < len')
                              (ensures g' a = f (Prims.op_Addition a lo'))
        = assert (g (Prims.op_Addition a 1) = f (Prims.op_Addition (Prims.op_Addition a 1) lo));
          assert (Prims.op_Addition (Prims.op_Addition a 1) lo == Prims.op_Addition a lo')
      in
      Classical.forall_intro (Classical.move_requires h);
      prod_range_offset_lem f g' lo' hi;
      prod_range_offset_lem g g' (nat_succ 0) len;
      assert (Prims.op_Subtraction len (nat_succ 0) == len');
      reflexivity (g 0);
      mul_congruence (g 0) (prod_range g (nat_succ 0) len)
                     (g 0) (prod_range g' 0 len');
      symmetry (prod_range g 0 len)
               (g 0 * prod_range g (nat_succ 0) len);
      transitivity (prod_range g 0 len)
                   (g 0 * prod_range g (nat_succ 0) len)
                   (g 0 * prod_range g' 0 len');
      symmetry (prod_range f lo' hi) (prod_range g' 0 len');
      mul_congruence (g 0) (prod_range g' 0 len')
                     (g 0) (prod_range f lo' hi);
      transitivity (prod_range g 0 len)
                   (g 0 * prod_range g' 0 len')
                   (g 0 * prod_range f lo' hi);
      symmetry (g 0) (f lo);
      mul_congruence (g 0) (prod_range f lo' hi)
                     (f lo) (prod_range f lo' hi);
      transitivity (prod_range g 0 len)
                   (g 0 * prod_range f lo' hi)
                   (f lo * prod_range f lo' hi);
      symmetry (prod_range f lo hi) (f lo * prod_range f lo' hi);
      transitivity (prod_range g 0 len)
                   (f lo * prod_range f lo' hi)
                   (prod_range f lo hi);
      symmetry (prod_range g 0 len) (prod_range f lo hi)
    end
#pop-options

(* Bridge lemma: prod_range of a body function = perm_product,
   given pointwise equality on [0, n). *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let prod_range_eq_perm_product (#t: Type) {| cr: commutative_ring t |} (#n: nat)
  (m: square_matrix t n) (p: permutation n) (body: nat -> t)
  : Lemma (requires forall (k: nat). 0 <= k /\ k < n ==> body k = m (k <: fin n) (p.fwd (k <: fin n)))
          (ensures prod_range body 0 n = perm_product m p)
  = H.elim_equatable_laws t ();
    let pp_body (k: nat) : t =
      if k < n then m (k <: fin n) (p.fwd (k <: fin n)) else one in
    let pw (k: nat) : Lemma (0 <= k /\ k < n ==> body k = pp_body k)
      = if k >= 0 && k < n then () in
    Classical.forall_intro pw;
    prod_range_congruence body pp_body 0 n (fun _ -> ());
    perm_product_unfold m p
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let perm_product_inject_factor
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (sigma': permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (perm_product m (inject sigma' i j)
           = m i j * perm_product (minor m i j) sigma')
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let nm1 = Prims.op_Subtraction n 1 in
    let ip1 = Prims.op_Addition (i <: nat) 1 in
    let sigma = inject sigma' i j in
    perm_product_unfold m sigma;
    perm_product_unfold (minor m i j) sigma';
    let body_big (k: nat) : t =
      if k < n then m (k <: fin n) (sigma.fwd (k <: fin n)) else one in
    let body_small (a: nat) : t =
      if a < nm1
      then (minor m i j) (a <: fin nm1) (sigma'.fwd (a <: fin nm1))
      else one in
    prod_range_shape_at #t #cr body_big 0 n (i <: nat);
    inject_fwd_at_i sigma' i j;
    assert (body_big (i <: nat) == m i j);
    let h_left (k: nat) : Lemma (requires 0 <= k /\ k < (i <: nat))
                                 (ensures body_big k = body_small k)
      = let kf : fin n = k in
        inject_fwd_off sigma' i j kf;
        let a : fin nm1 = unskip i kf in
        assert ((a <: nat) == (k <: nat));
        minor_at m i j a (sigma'.fwd a);
        skip_lt i a;
        reflexivity (m kf (skip j (sigma'.fwd a)))
    in
    Classical.forall_intro (Classical.move_requires h_left);
    prod_range_congruence body_big body_small 0 (i <: nat) (fun _ -> ());
    let shifted_big (a: nat) : t = body_big (Prims.op_Addition a ip1) in
    let shifted_small (a: nat) : t = body_small (Prims.op_Addition a (i <: nat)) in
    let len = Prims.op_Subtraction nm1 (i <: nat) in
    let h_right (a: nat) : Lemma (requires 0 <= a /\ a < len)
                                  (ensures shifted_big a = shifted_small a)
      = let k : nat = Prims.op_Addition a ip1 in
        let kf : fin n = k in
        inject_fwd_off sigma' i j kf;
        let u : fin nm1 = unskip i kf in
        assert ((u <: nat) == Prims.op_Subtraction k 1);
        assert ((u <: nat) == Prims.op_Addition a (i <: nat));
        minor_at m i j u (sigma'.fwd u);
        skip_ge i u;
        assert ((skip i u <: nat) == Prims.op_Addition u 1);
        assert ((skip i u <: nat) == k);
        reflexivity (m kf (skip j (sigma'.fwd u)))
    in
    Classical.forall_intro (Classical.move_requires h_right);
    prod_range_congruence shifted_big shifted_small 0 len (fun _ -> ());
    let h_big_offset (a: nat) : Lemma (requires 0 <= a /\ a < len)
                                       (ensures shifted_big a = body_big (Prims.op_Addition a ip1))
      = reflexivity (shifted_big a)
    in
    Classical.forall_intro (Classical.move_requires h_big_offset);
    prod_range_offset_lem #t #cr body_big shifted_big ip1 n;
    let h_small_offset (a: nat) : Lemma (requires 0 <= a /\ a < len)
                                         (ensures shifted_small a = body_small (Prims.op_Addition a (i <: nat)))
      = reflexivity (shifted_small a)
    in
    Classical.forall_intro (Classical.move_requires h_small_offset);
    prod_range_offset_lem #t #cr body_small shifted_small (i <: nat) nm1;
    assert (Prims.op_Subtraction n ip1 == len);
    assert (Prims.op_Subtraction nm1 (i <: nat) == len);
    transitivity (prod_range body_big ip1 n)
                 (prod_range shifted_big 0 len)
                 (prod_range shifted_small 0 len);
    symmetry (prod_range body_small (i <: nat) nm1)
             (prod_range shifted_small 0 len);
    transitivity (prod_range body_big ip1 n)
                 (prod_range shifted_small 0 len)
                 (prod_range body_small (i <: nat) nm1);
    let lp = prod_range body_big 0 (i <: nat) in
    let slp = prod_range body_small 0 (i <: nat) in
    let rp = prod_range body_big ip1 n in
    let srp = prod_range body_small (i <: nat) nm1 in
    assert (lp = slp);
    assert (rp = srp);
    prod_range_split body_small 0 (i <: nat) nm1;
    symmetry (prod_range body_small 0 nm1) (slp * srp);
    reflexivity (m i j);
    mul_congruence (m i j) rp (m i j) srp;
    mul_congruence lp (m i j * rp) slp (m i j * srp);
    mul_associativity slp (m i j) srp;
    symmetry ((slp * m i j) * srp) (slp * (m i j * srp));
    mul_commutativity slp (m i j);
    reflexivity srp;
    mul_congruence (slp * m i j) srp (m i j * slp) srp;
    mul_associativity (m i j) slp srp;
    transitivity (slp * (m i j * srp))
                 ((slp * m i j) * srp)
                 ((m i j * slp) * srp);
    transitivity (slp * (m i j * srp))
                 ((m i j * slp) * srp)
                 (m i j * (slp * srp));
    reflexivity (m i j);
    mul_congruence (m i j) (slp * srp) (m i j) (prod_range body_small 0 nm1);
    transitivity (slp * (m i j * srp))
                 (m i j * (slp * srp))
                 (m i j * prod_range body_small 0 nm1);
    transitivity (prod_range body_big 0 n)
                 (lp * (m i j * rp))
                 (slp * (m i j * srp));
    transitivity (prod_range body_big 0 n)
                 (slp * (m i j * srp))
                 (m i j * prod_range body_small 0 nm1);
    let h_bb (k: nat) : Lemma (0 <= k /\ k < n ==> body_big k = m (k <: fin n) (sigma.fwd (k <: fin n)))
      = if k >= 0 && k < n then reflexivity (body_big k) in
    Classical.forall_intro h_bb;
    prod_range_eq_perm_product m sigma body_big;
    let h_bs (k: nat) : Lemma (0 <= k /\ k < nm1 ==> body_small k = (minor m i j) (k <: fin nm1) (sigma'.fwd (k <: fin nm1)))
      = if k >= 0 && k < nm1 then reflexivity (body_small k) in
    Classical.forall_intro h_bs;
    prod_range_eq_perm_product (minor m i j) sigma' body_small;
    symmetry (prod_range body_big 0 n) (perm_product m sigma);
    symmetry (prod_range body_small 0 nm1) (perm_product (minor m i j) sigma');
    reflexivity (m i j);
    mul_congruence (m i j) (prod_range body_small 0 nm1) (m i j) (perm_product (minor m i j) sigma');
    transitivity (prod_range body_big 0 n)
                 (m i j * prod_range body_small 0 nm1)
                 (m i j * perm_product (minor m i j) sigma');
    symmetry (prod_range body_big 0 n) (perm_product m sigma);
    transitivity (perm_product m sigma)
                 (prod_range body_big 0 n)
                 (m i j * perm_product (minor m i j) sigma')
#pop-options

(* ====================================================================== *)
(*  P4 helper: leibniz_inject_factor                                      *)
(*                                                                        *)
(*  leibniz_term m (inject sigma' i j)                                    *)
(*    = minus_one_pow(i+j) * m i j * leibniz_term (minor m i j) sigma'    *)
(* ====================================================================== *)

(* minus_one_pow squared = one *)
#push-options "--fuel 2 --ifuel 2 --z3rlimit 60"
private let minus_one_pow_square (#t: Type) {| cr: commutative_ring t |} (k: nat)
  : Lemma (minus_one_pow #t k * minus_one_pow #t k = one)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if Prims.op_Modulus k 2 = 0 then begin
      minus_one_pow_even #t #cr k;
      H.one_mul_x (one #t)
    end else begin
      minus_one_pow_odd #t #cr k;
      let acg : add_comm_group t = acg_of_ring_local t cr.cr_r in
      ring_neg_x_is_minus_one_times_x (-(one #t));
      symmetry (-(-(one #t))) ((-(one #t)) * (-(one #t)));
      double_negation_lemma (one #t);
      transitivity ((-(one #t)) * (-(one #t)))
                   (-(-(one #t)))
                   (one #t)
    end
#pop-options

(* Combine P1 and P3 into the signed factorization *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let leibniz_inject_factor
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (sigma': permutation (Prims.op_Subtraction n 1)) (i j: fin n)
  : Lemma (leibniz_term m (inject sigma' i j)
           = minus_one_pow #t #cr (Prims.op_Addition (i <: nat) (j <: nat))
             * m i j
             * leibniz_term #t #cr (minor m i j) sigma')
  = let r : ring t = cr.cr_r in
    let acg : add_comm_group t = acg_of_ring_local t cr.cr_r in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let nm1 = Prims.op_Subtraction n 1 in
    let sigma = inject sigma' i j in
    let ij = Prims.op_Addition (i <: nat) (j <: nat) in
    parity_inject sigma' i j;
    perm_product_inject_factor #t #cr #n m sigma' i j;
    let pp = perm_product m sigma in
    let pp_min = perm_product #t #cr (minor m i j) sigma' in
    assert (pp = m i j * pp_min);
    let lhs = leibniz_term m sigma in
    let sign_sp = parity sigma' in
    let ij_even = (Prims.op_Modulus ij 2 = 0) in
    let mop = minus_one_pow #t #cr ij in
    if sign_sp then begin
      if ij_even then begin
        minus_one_pow_even #t #cr ij;
        assert (lhs == pp);
        assert (leibniz_term #t #cr (minor m i j) sigma' == pp_min);
        mul_associativity mop (m i j) pp_min;
        reflexivity (m i j * pp_min);
        mul_congruence mop (m i j * pp_min) (one #t) (m i j * pp_min);
        H.one_mul_x (m i j * pp_min);
        symmetry pp (m i j * pp_min);
        trans_lemma [ mop * m i j * pp_min;
                      mop * (m i j * pp_min);
                      one * (m i j * pp_min);
                      m i j * pp_min;
                      pp ]
      end else begin
        minus_one_pow_odd #t #cr ij;
        assert (lhs == -pp);
        assert (leibniz_term #t #cr (minor m i j) sigma' == pp_min);
        mul_associativity mop (m i j) pp_min;
        reflexivity (m i j * pp_min);
        mul_congruence mop (m i j * pp_min) (-(one #t)) (m i j * pp_min);
        ring_neg_x_is_minus_one_times_x (m i j * pp_min);
        symmetry (-(m i j * pp_min)) ((-(one #t)) * (m i j * pp_min));
        neg_congruence_lem pp (m i j * pp_min);
        symmetry (-pp) (-(m i j * pp_min));
        trans_lemma [ mop * m i j * pp_min;
                      mop * (m i j * pp_min);
                      (-(one #t)) * (m i j * pp_min);
                      -(m i j * pp_min);
                      -pp ]
      end
    end else begin
      if ij_even then begin
        minus_one_pow_even #t #cr ij;
        assert (lhs == -pp);
        assert (leibniz_term #t #cr (minor m i j) sigma' == -pp_min);
        let lt_min = -pp_min in
        mul_associativity mop (m i j) lt_min;
        reflexivity (m i j * lt_min);
        mul_congruence mop (m i j * lt_min) (one #t) (m i j * lt_min);
        H.one_mul_x (m i j * lt_min);
        trans_lemma [ mop * m i j * lt_min;
                      mop * (m i j * lt_min);
                      one * (m i j * lt_min);
                      m i j * lt_min ];
        ring_neg_xy_is_x_times_neg_y (m i j) pp_min;
        symmetry (-(m i j * pp_min)) (m i j * lt_min);
        neg_congruence_lem pp (m i j * pp_min);
        symmetry (-pp) (-(m i j * pp_min));
        trans_lemma [ mop * m i j * lt_min;
                      m i j * lt_min;
                      -(m i j * pp_min);
                      -pp ]
      end else begin
        minus_one_pow_odd #t #cr ij;
        assert (lhs == pp);
        assert (leibniz_term #t #cr (minor m i j) sigma' == -pp_min);
        let lt_min = -pp_min in
        mul_associativity mop (m i j) lt_min;
        reflexivity (m i j * lt_min);
        mul_congruence mop (m i j * lt_min) (-(one #t)) (m i j * lt_min);
        ring_neg_x_is_minus_one_times_x (m i j * lt_min);
        symmetry (-(m i j * lt_min)) ((-(one #t)) * (m i j * lt_min));
        ring_neg_xy_is_x_times_neg_y (m i j) pp_min;
        symmetry (-(m i j * pp_min)) (m i j * lt_min);
        neg_congruence_lem (m i j * lt_min) (-(m i j * pp_min));
        double_negation_lemma (m i j * pp_min);
        symmetry pp (m i j * pp_min);
        trans_lemma [ mop * m i j * lt_min;
                      mop * (m i j * lt_min);
                      (-(one #t)) * (m i j * lt_min);
                      -(m i j * lt_min) ];
        trans_lemma [ -(m i j * lt_min);
                      -(-(m i j * pp_min));
                      m i j * pp_min;
                      pp ];
        transitivity (mop * m i j * lt_min) (-(m i j * lt_min)) pp
      end
    end
#pop-options

(* ====================================================================== *)
(*  P4: det_laplace_row -- Laplace expansion along row i.                 *)
(*                                                                        *)
(*    det m = fin_sum (fun j -> (-1)^(i+j) * m(i,j) * det(minor m i j))  *)
(* ====================================================================== *)

(* Module-level cofactor function *)
let cofactor_term (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) : t
  = minus_one_pow #t #cr (Prims.op_Addition (i <: nat) (j <: nat))
    * m i j
    * det #t #cr #(Prims.op_Subtraction n 1) (minor m i j)

(* Helper: the per-fiber sum equals the cofactor expansion term. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let inner_sum_eq_cofactor
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (
      sum_over_perms (Prims.op_Subtraction n 1)
        (per_fiber_fn #t #cr (leibniz_term m) i j)
      = minus_one_pow #t #cr (Prims.op_Addition (i <: nat) (j <: nat))
        * m i j
        * det #t #cr #(Prims.op_Subtraction n 1) (minor m i j))
  = let r : ring t = cr.cr_r in
    let sr : ring t = cr.cr_r in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let nm1 = Prims.op_Subtraction n 1 in
    let ij = Prims.op_Addition (i <: nat) (j <: nat) in
    let mop = minus_one_pow #t #cr ij in
    let f = per_fiber_fn #t #cr (leibniz_term m) i j in
    let g (sp: permutation nm1) : t
      = mop * m i j * leibniz_term #t #cr (minor m i j) sp in
    let pw (sp: permutation nm1) : Lemma (f sp = g sp)
      = leibniz_inject_factor #t #cr #n m sp i j
    in
    Classical.forall_intro pw;
    sum_over_perms_congruence nm1 f g (fun _ -> ());
    let c = mop * m i j in
    let h = leibniz_term #t #cr #nm1 (minor m i j) in
    let ch (sp: permutation nm1) : t = c * h sp in
    let pw2 (sp: permutation nm1) : Lemma (g sp = ch sp)
      = mul_associativity mop (m i j) (h sp)
    in
    Classical.forall_intro pw2;
    sum_over_perms_congruence nm1 g ch (fun _ -> ());
    sum_over_perms_mul_left_named #t #(cr.cr_r) nm1 c ch h (fun _ -> ());
    transitivity (sum_over_perms nm1 g)
                 (sum_over_perms nm1 ch)
                 (c * sum_over_perms nm1 h);
    transitivity (sum_over_perms nm1 f) (sum_over_perms nm1 g)
                 (c * sum_over_perms nm1 h);
    det_unfold #t #cr #nm1 (minor m i j);
    symmetry (det #t #cr (minor m i j)) (sum_over_perms nm1 h);
    reflexivity c;
    mul_congruence c (sum_over_perms nm1 h) c (det #t #cr (minor m i j));
    transitivity (sum_over_perms nm1 f) (c * sum_over_perms nm1 h)
                 (c * det #t #cr (minor m i j));
    reflexivity (c * det #t #cr (minor m i j))
#pop-options

(* Main theorem: Laplace expansion along row i. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let det_laplace_row
  (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (m: square_matrix t n) (i: fin n)
  : Lemma (det #t #cr #n m =
           fin_sum (cofactor_term #t #cr m i))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    leibniz_term_respects_perm_eq #t #cr #n m;
    let pw (j: fin n) : Lemma (
      sum_over_perms (Prims.op_Subtraction n 1)
        (per_fiber_fn #t #cr (leibniz_term m) i j)
      = cofactor_term #t #cr m i j)
      = inner_sum_eq_cofactor #t #cr #n m i j
    in
    Classical.forall_intro pw;
    sum_over_perms_partition_target #t #cr #n
      i (leibniz_term m) (cofactor_term #t #cr m i);
    det_unfold m;
    assert (fin_sum (cofactor_term #t #cr m i)
            == sum_range
              (fun (k: nat) -> if k < n then (cofactor_term #t #cr m i) (k <: fin n) else zero)
              0 n)
      by (FStar.Tactics.norm [delta_only [`%fin_sum]; iota; zeta; primops]; FStar.Tactics.trefl ());
    transitivity (det m)
                 (sum_over_perms n (leibniz_term m))
                 (fin_sum (cofactor_term #t #cr m i))
#pop-options
