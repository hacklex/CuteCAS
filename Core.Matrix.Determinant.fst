module Core.Matrix.Determinant

(*   Determinant of a square matrix via the Leibniz formula:
       det(M) = Σ_{σ ∈ S_n}  sign(σ) · ∏_{i=0..n-1} M(i, σ(i))

   Ported from `..\new\FStar.CAS.Matrix.Determinant.fst` to the new
   diamond-free `core/` tower.

   Author: A. Rozanov (CuteCAS).
*)

module L = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Algebra.Helpers
open Core.Tactics.CanonRing
open Core.FinSum
open Core.Permutation
open Core.Permutation.Enum
open Core.Permutation.Sum
open Core.Matrix
open Core.Vector
open FStar.List.Tot.Base

module H = Core.Algebra.Helpers

(* -------------------------------------------------------------------- *)
(*  Local synthesis: add_comm_group from ring.                          *)
(*  In the core tower this is just `r.r_add` (already an add_comm_group), *)
(*  but we keep this alias name to minimize diff vs. the original file.   *)
(* -------------------------------------------------------------------- *)

(* `acg_of_ring_local` is defined in the .fsti; do not redefine here. *)

(* -------------------------------------------------------------------- *)
(*  Private ring-level helpers missing from Core.Algebra.Helpers.        *)
(*  TODO: promote these to Helpers once stable.                          *)
(* -------------------------------------------------------------------- *)

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
private let perm_eq_sym_local (#n: pos) (p q: permutation n)
  : Lemma (requires perm_eq p q) (ensures perm_eq q p)
  = reveal_opaque (`%perm_eq) (perm_eq p q);
    reveal_opaque (`%perm_eq) (perm_eq q p);
    perm_eq_bool_from_sym p q 0

let ring_zero_is_left_absorber (#t: Type) {| cr: commutative_ring t |} (x: t)
  : Lemma (zero * x = zero) = zero_mul_x x
let ring_zero_is_right_absorber (#t: Type) {| cr: commutative_ring t |} (x: t)
  : Lemma (x * zero = zero)
  = x_mul_zero x
let neg_congruence_lem (#t:Type) {| cr: commutative_ring t |} (a b: t)
  : Lemma (requires a = b) (ensures (-a) = (-b))
  = neg_congruence a b
let neg_zero_lem (#t:Type) {| cr: commutative_ring t |}
  : Lemma ((-(zero #t)) = zero)
  = assert ((-(zero #t)) = zero) by canon_ring ()
let double_negation_lemma (#t: Type) {| cr: commutative_ring t |} (x: t)
  : Lemma ((-(-x)) = x)
  = assert ((-(-x)) = x) by canon_ring ()
let neg_of_sum_local (#t: Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (-(x + y) = (-x) + (-y))
  = assert (-(x + y) = (-x) + (-y)) by canon_ring ()
let ring_neg_x_is_minus_one_times_x (#t: Type) {| cr: commutative_ring t |} (x: t)
  : Lemma (-x = (-one) * x)
  = assert ((-x) = (-one) * x) by canon_ring ()
let ring_neg_xy_is_x_times_neg_y (#t: Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (-(x * y) = x * (-y))
  = assert (-(x * y) = x * (-y)) by canon_ring ()
let ring_neg_xy_is_neg_x_times_y (#t: Type) {| cr: commutative_ring t |} (x y: t)
  : Lemma (-(x * y) = (-x) * y)
  = assert (-(x * y) = (-x) * y) by canon_ring ()

(* `semiring_of_cr_local` deleted: the new tower has no `semiring` class.
   Every former consumer takes `{| ring t |}` (or `{| commutative_ring t |}`)
   directly. Calls that used `#(cr.cr_r)` need to be
   rewritten to use the consumer API's actual instance, typically a
   plain `{| cr.cr_r |}` resolution. *)

(* -------------------------------------------------------------------- *)
(*  Product along a permutation: ∏_{i=0..n-1} M(i, p.fwd i).            *)
(* -------------------------------------------------------------------- *)
(* perm_product, leibniz_term, det defined in .fsti *)

let perm_product_unfold (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (perm_product m p ==
           prod_range (fun k -> if k < n then m k (p.fwd k) else one) 0 n)
  = ()

let perm_product_via (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (perm_product m p == prod_range (perm_entry m p) 0 n)
  = assert (perm_product m p == prod_range (perm_entry m p) 0 n)
      by (FStar.Tactics.norm [delta_only [`%perm_product; `%perm_entry]; iota; zeta; primops];
          FStar.Tactics.trefl ())

let det_unfold (#t: Type) {| cr: commutative_ring t |} (#n: pos) (m: square_matrix t n)
  : Lemma (det m == sum_over_perms n (leibniz_term m))
  = ()

(* -------------------------------------------------------------------- *)
(*  Leibniz-term-is-zero helper: factored from repeated pattern.         *)
(*  If perm_product m q = zero, then leibniz_term m q = zero.            *)
(* -------------------------------------------------------------------- *)
private let leibniz_term_zero_of_pp_zero
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (q: permutation n)
  : Lemma (requires perm_product m q = zero)
          (ensures  leibniz_term m q = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if parity q then ()
    else begin
      neg_zero_lem #t #cr;
      neg_congruence (perm_product m q) (zero)
    end

(* -------------------------------------------------------------------- *)
(*  Helpers on prod_range needed by det_identity.                       *)
(* -------------------------------------------------------------------- *)

let rec prod_range_const_one (#t: Type) {| cr: commutative_ring t |} (lo hi: nat)
  : Lemma (ensures prod_range (fun _ -> one #t) lo hi = one)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    if hi <= lo then
      prod_range_empty (fun _ -> one #t #(cr.cr_r)) lo hi
    else begin
      prod_range_unfold_left (fun _ -> one #t #(cr.cr_r)) lo hi;
      prod_range_const_one #t #cr ((lo ++ 1)) hi;
      let pr_tail : t = prod_range #t #(cr.cr_r) (fun _ -> one #t #(cr.cr_r)) ((lo ++ 1)) hi in
      let one_t : t = one #t #(cr.cr_r) in
      mul_congruence one_t pr_tail one_t one_t;
      one_mul_x one_t;
      trans3 (prod_range #t #(cr.cr_r) (fun _ -> one #t #(cr.cr_r)) lo hi)
               (one_t * pr_tail) (one_t * one_t) one_t
    end

let rec prod_range_zero_factor (#t: Type) {| cr: commutative_ring t |}
  (f: nat -> t) (lo hi: nat) (k: nat)
  : Lemma (requires lo <= k /\ k < hi /\ f k = zero)
          (ensures  prod_range f lo hi = zero)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    prod_range_unfold_left f lo hi;
    if k = lo then begin
      mul_congruence (f lo) (prod_range f ((lo ++ 1)) hi)
                     (zero) (prod_range f ((lo ++ 1)) hi);
      ring_zero_is_left_absorber (prod_range f ((lo ++ 1)) hi);
      transitivity (f lo * prod_range f ((lo ++ 1)) hi)
                   (zero * prod_range f ((lo ++ 1)) hi)
                   (zero)
    end else begin
      prod_range_zero_factor f ((lo ++ 1)) hi k;
      mul_congruence (f lo) (prod_range f ((lo ++ 1)) hi)
                     (f lo) (zero);
      ring_zero_is_right_absorber (f lo);
      transitivity (f lo * prod_range f ((lo ++ 1)) hi)
                   (f lo * zero)
                   (zero)
    end

(* -------------------------------------------------------------------- *)
(*  det (identity matrix) = one                                          *)
(* -------------------------------------------------------------------- *)

let perm_product_id_identity (#t: Type) {| cr: commutative_ring t |} (n: pos)
  : Lemma (perm_product (id_matrix #t) (identity n) = one)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let const_one : nat -> t = fun _ -> one in
    prod_range_congruence
      (fun i -> if i < n then id_matrix i ((identity n).fwd i) else one)
      const_one 0 n (fun _ -> ());
    prod_range_const_one #t #cr 0 n;
    perm_product_unfold (id_matrix #t) (identity n)

let perm_product_id_nonidentity (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (p: permutation n)
  : Lemma (requires ~(perm_eq p (identity n)))
          (ensures  perm_product (id_matrix #t) p = zero)
  = elim_equatable_laws t ();
    let phi (i: fin n) : prop = ~(p.fwd i == i) in
    let helper (assume_not : (i: fin n -> Lemma (~(phi i)))) : Lemma False
      = let pwd (i: fin n) : Lemma (p.fwd i == (identity n).fwd i)
          = assume_not i; identity_fwd n i in
        perm_eq_intro p (identity n) pwd;
        assert False
    in
    Classical.exists_intro_not_all_not helper;
    eliminate exists (i: fin n). phi i
      returns perm_product (id_matrix #t) p = zero with _.
      begin
        id_matrix_off #t i (p.fwd i);
        prod_range_zero_factor
          (fun j -> if j < n then id_matrix #t j (p.fwd j) else one)
          0 n (i <: nat);
        perm_product_unfold (id_matrix #t) p
      end

let perm_product_id_respects_perm_eq (#t: Type) {| cr: commutative_ring t |} (n: pos)
  (p q: permutation n)
  : Lemma (requires perm_eq p q)
          (ensures  perm_product (id_matrix #t) p = perm_product (id_matrix #t) q)
  = elim_equatable_laws t ();
    Classical.forall_intro (Classical.move_requires (perm_eq_elim p q));    
    prod_range_congruence
      (fun i -> if i < n then id_matrix #t i (p.fwd i) else one)
      (fun i -> if i < n then id_matrix #t i (q.fwd i) else one)
      0 n (fun _ -> ());
    perm_product_unfold (id_matrix #t) p;
    perm_product_unfold (id_matrix #t) q

let leibniz_term_id_respects_perm_eq (#t: Type) {| cr: commutative_ring t |} (n: pos)
  : Lemma (respects_perm_eq #t (leibniz_term (id_matrix #t #_ #n)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let f = leibniz_term (id_matrix #t #_ #n) in
    let aux (p q: permutation n) : Lemma (perm_eq p q ==> f p = f q)
      = if perm_eq p q then begin
          parity_perm_eq_invariant p q;
          perm_product_id_respects_perm_eq #t #cr n p q;
          if parity p then ()
          else neg_congruence (perm_product (id_matrix #t #_ #n) p)
                              (perm_product (id_matrix #t #_ #n) q)
        end
    in
    Classical.forall_intro_2 aux;
    respects_perm_eq_intro f (fun _ _ -> ())

let det_identity (#t: Type) {| cr: commutative_ring t |} (n: pos)
  : Lemma (det (id_matrix #t #_ #n) = one)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let f = leibniz_term (id_matrix #t #_ #n) in
    let p0 = identity n in
    leibniz_term_id_respects_perm_eq #t #cr n;
    let vanish (q: permutation n) : Lemma (~(perm_eq p0 q) ==> f q = zero)
      = if not (perm_eq p0 q) then begin          
          Classical.move_requires (perm_eq_sym_local q) |> Classical.forall_intro;
          perm_product_id_nonidentity #t #cr #n q;
          leibniz_term_zero_of_pp_zero (id_matrix #t #_ #n) q
        end
    in
    Classical.forall_intro vanish;
    (* Re-prove respects_perm_eq in the current TC context *)
    let re_aux (p q: permutation n) : Lemma (perm_eq p q ==> f p = f q)
      = if perm_eq p q then begin
          parity_perm_eq_invariant p q;
          perm_product_id_respects_perm_eq #t #cr n p q;
          if parity p then ()
          else neg_congruence (perm_product (id_matrix #t #_ #n) p)
                              (perm_product (id_matrix #t #_ #n) q)
        end
    in
    Classical.forall_intro_2 re_aux;
    respects_perm_eq_intro f (fun _ _ -> ());
    sum_over_perms_single n f p0 obvious;
    parity_identity n;
    perm_product_id_identity #t #cr n

(* -------------------------------------------------------------------- *)
(*  det of a matrix with a zero row is zero.                            *)
(* -------------------------------------------------------------------- *)

let perm_product_zero_row
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (k: fin n)
  (zrow: squash (forall (j: fin n). m k j = zero))
  (p: permutation n)
  : Lemma (perm_product m p = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let body (i:nat) = if i < n then m i (p.fwd i) else one in
    prod_range_zero_factor body 0 n k 

let det_zero_row
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (k: fin n)
  : Lemma (requires forall (j: fin n). m k j = zero)
          (ensures  det m = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let f = leibniz_term m in
    let term_zero (p: permutation n) : Lemma (f p = zero)
      = perm_product_zero_row m k () p;
        leibniz_term_zero_of_pp_zero m p
    in
    sum_over_perms_all_zero n f term_zero

(* -------------------------------------------------------------------- *)
(*  det(M^T) = det(M).                                                  *)
(* -------------------------------------------------------------------- *)

(* perm_product respects perm_eq in its permutation argument. *)

let perm_product_respects_perm_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p q: permutation n)
  : Lemma (requires perm_eq p q)
          (ensures  perm_product m p = perm_product m q)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let bp (i:nat) = if i < n then m i (p.fwd i) else one in
    let bq (i:nat) = if i < n then m i (q.fwd i) else one in
    perm_eq_elim p q |> Classical.move_requires |> Classical.forall_intro;    
    prod_range_congruence bp bq 0 n obvious

(* leibniz_term respects perm_eq in its permutation argument. *)

let leibniz_term_respects_perm_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n)
  : Lemma (respects_perm_eq (leibniz_term m))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let f = leibniz_term m in
    let aux (p q: permutation n) : Lemma (requires perm_eq p q) (ensures f p = f q)
      = perm_product_respects_perm_eq m p q;
        parity_perm_eq_invariant p q;
        neg_congruence (perm_product m p) (perm_product m q)
    in
    respects_perm_eq_intro f aux

(* perm_product (transpose m) (inverse p) = perm_product m p, in any comm_ring. *)

let perm_product_transpose_inverse
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (perm_product (transpose m) (inverse p) = perm_product m p)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let bigF : nat -> t =
      fun k -> if k < n then m k (p.fwd k) else one in
    let bigG : nat -> t =
      fun k -> if k < n
               then (transpose m) k ((inverse p).fwd k)
               else one in
    let body_p : nat -> t =
      fun k -> if k < n then bigF ((inverse p).fwd k) else one in
    (* Pointwise bigG = body_p on [0, n). *)
    let hGH (k: nat) : Lemma (requires 0 <= k /\ k < n) (ensures bigG k = body_p k)
      = inverse_fwd p k;
        p.fwd_bwd_id k
    in
    Classical.forall_intro (Classical.move_requires hGH);
    prod_range_congruence bigG body_p 0 n (fun _ -> ());
    (* prod_range body_p 0 n = prod_range bigF 0 n via perm_invariance. *)
    prod_range_perm_invariance_fn bigF body_p bigF (inverse p)
      (fun _ -> ()) (fun _ -> ());
    perm_product_unfold (transpose m) (inverse p);
    perm_product_unfold m p

(* leibniz_term (transpose m) (inverse p) = leibniz_term m p. *)

let leibniz_transpose_inverse_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (leibniz_term (transpose m) (inverse p) = leibniz_term m p)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    parity_inverse p;
    perm_product_transpose_inverse m p;
    neg_congruence (perm_product (transpose m) (inverse p)) (perm_product m p)

(* Headline: det(M^T) = det(M) over any commutative ring. *)

let det_transpose
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n)
  : Lemma (det (transpose m) = det m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let f = leibniz_term (transpose m) in
    let g = leibniz_term m in
    leibniz_term_respects_perm_eq (transpose m);
    leibniz_term_respects_perm_eq m;
    (* sum_over_perms n f = sum_over_perms n (fcomp f inverse) *)
    sum_over_perms_reindex_inverse n f;
    (* fcomp f inverse is pointwise equal to g *)
    let pointwise (s: permutation n) : Lemma (fcomp f inverse s = g s)
      = fcomp_unfold f inverse s;
        leibniz_transpose_inverse_eq m s in 
    sum_over_perms_congruence n (fcomp f inverse) g pointwise

(* -------------------------------------------------------------------- *)
(*  Row swap and alternating property.                                  *)
(*  row_swap m i j is m with rows i and j swapped.                      *)
(*  Headline: det(row_swap m i j) = -det(m) when i <> j.                 *)
(* -------------------------------------------------------------------- *)
let row_swap (#t: Type) (#n: pos) (m: square_matrix t n) (i j: fin n)
  : square_matrix t n
  = fun (k: fin n) (l: fin n) -> m ((transposition n i j).fwd k) l

(* Key calculation: perm_product (row_swap m i j) p = perm_product m (compose p σ),
   where σ = transposition n i j. *)

let perm_product_row_swap
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (p: permutation n)
  : Lemma (perm_product (row_swap m i j) p =
           perm_product m (compose p (transposition n i j)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let sigma = transposition n i j in
    let q = compose p sigma in
    let lhs_body : nat -> t =
      fun k -> if k < n
                  then (row_swap m i j) k (p.fwd k)
                  else one in
    let rhs_body : nat -> t =
      fun k -> if k < n
                  then m k (q.fwd k)
                  else one in
    let f : nat -> t =
      fun k -> if k < n
                  then m k (p.fwd ((sigma.fwd k) <: fin n))
                  else one in
    transposition_self_inverse n i j;
    let body_p_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==>
       lhs_body k = f (sigma.fwd k))
      = if 0 <= k && k < n then begin
          let kf : fin n = k <: fin n in
          compose_fwd sigma sigma kf;
          perm_eq_elim (compose sigma sigma) (identity n) kf;
          identity_fwd n kf
        end in
    Classical.forall_intro body_p_hyp;
    let body_id_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==> rhs_body k = f k)
      = if 0 <= k && k < n then begin
          let kf : fin n = k <: fin n in
          compose_fwd p sigma kf
        end in
    Classical.forall_intro body_id_hyp;
    prod_range_perm_invariance_fn f lhs_body rhs_body sigma
      (fun _ -> ()) (fun _ -> ());
    perm_product_unfold (row_swap m i j) p;
    perm_product_unfold m q

(* leibniz_term (row_swap m i j) p = -(leibniz_term m (compose p σ)) when i <> j. *)

let leibniz_term_row_swap
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (p: permutation n)
  : Lemma (requires ~(i == j))
          (ensures  leibniz_term (row_swap m i j) p =
                    -(leibniz_term m (compose p (transposition n i j))))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let sigma = transposition n i j in
    let q = compose p sigma in
    perm_product_row_swap m i j p;
    parity_transposition n i j;
    sign_homomorphism p sigma;
    let pp1 = perm_product (row_swap m i j) p in
    let pp2 = perm_product m q in
    if parity p
    then begin
      (* lhs = pp1, rhs = -(-(pp2)), need pp1 = pp2 = -(-(pp2)) *)
      double_negation_lemma pp2;
      transitivity pp1 pp2 (-(-pp2))
    end else begin
      (* lhs = -(pp1), rhs = -(pp2), need -(pp1) = -(pp2) *)
      neg_congruence pp1 pp2
    end

(* Headline: det(row_swap m i j) = -det(m) when i <> j. *)

let det_row_swap
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires ~(i == j))
          (ensures  det (row_swap m i j) = -(det m))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let sigma = transposition n i j in
    let f = leibniz_term (row_swap m i j) in
    let g = leibniz_term m in
    leibniz_term_respects_perm_eq m;
    (* By reindexing: sum_over_perms n g = sum_over_perms n (fcomp g (flip compose sigma)). *)
    sum_over_perms_reindex n g sigma;
    (* By leibniz_term_row_swap: f s = -(g (compose s sigma)) for every s. *)
    let pointwise (s: permutation n) : Lemma (f s = -(g (compose s sigma)))
      = leibniz_term_row_swap m i j s in
    Classical.forall_intro pointwise;
    (* Use the named variant from Permutation.Sum.fsti — proven against
       add_comm_group directly, avoiding the acg_of_ring lambda diamond. *)
    sum_over_perms_neg_named n f
      (fcomp g (flip compose sigma)) (fun _ -> ());
    (* Now: sum n f = -(sum n (fcomp g (flip compose sigma))) *)
    (* But sum n (fcomp g (flip compose sigma)) = sum n g by reindex *)
    det_unfold (row_swap m i j);
    det_unfold m;
    neg_congruence (sum_over_perms n (fcomp g (flip compose sigma)))
                   (sum_over_perms n g);
    neg_congruence (sum_over_perms n g) (det m)

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
  (n: pos) (i j: fin n) : square_matrix t n
  = row_swap (id_matrix #t) i j

let e_scale_mat (#t: Type) {| ring t |}
  (n: pos) (i: fin n) (c: t) : square_matrix t n
  = fun a b -> if a = i && b = i then c
               else if a = b then one
               else zero

let e_add_mat (#t: Type) {| ring t |}
  (n: pos) (i j: fin n) (c: t) : square_matrix t n
  = fun a b -> if a = b then one
               else if a = i && b = j then c
               else zero

(* det (E_swap n i j) = -(one). *)

let det_e_swap (#t: Type) {| cr: commutative_ring t |} (n: pos) (i j: fin n)
  : Lemma (requires ~(i == j))
          (ensures  det (e_swap_mat n i j) = -(one #t))
  = let m0 = id_matrix #t in
    trans_for_calc t ();
    det_row_swap m0 i j;
    det_identity #t #cr n;
    neg_congruence_lem (det m0) (one #t)

(* perm_product is zero whenever one of its factors vanishes. *)

let perm_product_has_zero_factor
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n) (k: fin n)
  : Lemma (requires m k (p.fwd k) = zero)
          (ensures  perm_product m p = zero)
  = let body : nat -> t 
      = fun j -> if j < n then m j (p.fwd j) else one in    
    assert (body k == m k (p.fwd k));
    prod_range_zero_factor body 0 n k

(* prod_range with all-ones except at one position equals the value at that position. *)

let prod_range_one_except_at
  (#t: Type) {| cr: commutative_ring t |} (f: nat -> t) (lo hi: nat) (i: nat)
  : Lemma (requires lo <= i /\ i < hi /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> f k = one))
          (ensures  prod_range f lo hi = f i)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let const_one : nat -> t = fun _ -> one in
    prod_range_split f lo i hi;
    prod_range_congruence f const_one lo i (fun _ -> ());
    prod_range_congruence f const_one ((i ++ 1)) hi (fun _ -> ());
    prod_range_const_one #t lo i;
    prod_range_const_one #t ((i ++ 1)) hi;
    let p_left = prod_range f lo i in
    let p_right_tail = prod_range f ((i ++ 1)) hi in
    let p_right = prod_range f i hi in
    mul_congruence (f i) p_right_tail (f i) one;
    mul_one (f i);
    prod_range_unfold_left f i hi;
    mul_congruence p_left p_right one (f i)

(* det (E_scale n i c) = c. *)
(* Helper: perm_product is one when all diagonal entries m(k, p.fwd k) = one. *)

private let perm_product_all_ones
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n)
  : Lemma (requires forall (k: fin n). m k (p.fwd k) = one)
          (ensures  perm_product m p = one)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let body : nat -> t
      = fun j -> if j < n then m j (p.fwd j) else one in
    let const_one : nat -> t = fun _ -> one in
    prod_range_congruence body const_one 0 n (fun _ -> ());
    prod_range_const_one #t #cr 0 n;
    perm_product_unfold m p

(* Helper: perm_product of a diagonal-like matrix under any permutation equals
   the value at position i when all other diagonal entries are one. *)

private let perm_product_diag_matrix_identity #t {| commutative_ring t |} #n
  (m: square_matrix t n) (p: permutation n) (i: fin n) (c: t)
  : Lemma (requires (forall k. (k <> i) ==> (m k (p.fwd k) = one)) /\ m i (p.fwd i) = c)
          (ensures  perm_product m p = c)
  = trans_for_calc t ();
    let body (j:nat) = if j < n then m j (p.fwd j) else one in
    prod_range_one_except_at body 0 n i    

let det_e_scale (#t: Type) {| cr: commutative_ring t |} (n: pos) (i: fin n) (c: t)
  : Lemma (det (e_scale_mat n i c) = c)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let m = e_scale_mat n i c in
    let f = leibniz_term m in
    let p0 = identity n in
    leibniz_term_respects_perm_eq m;
    let vanish (q: permutation n) : Lemma (~(perm_eq p0 q) ==> f q = zero)
      = if not (perm_eq p0 q) then begin
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
              assert (m k (q.fwd k) == zero);
              perm_product_has_zero_factor m q k;
              leibniz_term_zero_of_pp_zero m q
            end
        end
    in
    Classical.forall_intro vanish;
    sum_over_perms_single n f p0 (fun _ -> ());
    parity_identity n;
    (* prove preconditions for perm_product_diag_matrix_identity *)
    let aux_diag (k: fin n) : Lemma (k =!= i ==> m k ((identity n).fwd k) = one)
      = if k <> i then begin
          identity_fwd n k
        end
    in
    Classical.forall_intro (Classical.move_requires aux_diag);
    identity_fwd n i;
    assert (m i ((identity n).fwd i) == c);
    perm_product_diag_matrix_identity m p0 i c;
    det_unfold m

(* det (E_add n i j c) = one, i <> j. *)

let det_e_add (#t: Type) {| cr: commutative_ring t |} (n: pos) (i j: fin n) (c: t)
  : Lemma (requires ~(i == j))
          (ensures  det (e_add_mat n i j c) = one)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let m = e_add_mat n i j c in
    let f = leibniz_term m in
    let p0 = identity n in
    leibniz_term_respects_perm_eq m;
    let vanish (q: permutation n) : Lemma (~(perm_eq p0 q) ==> f q = zero)
      = if not (perm_eq p0 q) then begin
          let phi k : prop = m k (q.fwd k) = zero in
          let helper (assume_not : (k: fin n -> Lemma (~(phi k)))) : Lemma (False)
            = Classical.forall_intro assume_not;
              if q.fwd i = j then fwd_injective q i j
              else perm_eq_intro p0 q (fun _ -> ())
          in
          Classical.exists_intro_not_all_not helper;
          eliminate exists k. phi k
            returns f q = zero with _.
            begin
              perm_product_has_zero_factor m q k;
              leibniz_term_zero_of_pp_zero m q
            end
        end
    in
    Classical.forall_intro vanish;
    sum_over_perms_single n f p0 (fun _ -> ());
    parity_identity n;    
    perm_product_all_ones m p0

(* ==================================================================== *)
(*  Row operations as data                                              *)
(* ==================================================================== *)
(* Multiply row i by scalar c. *)
let row_scale (#t: Type) {| ring t |} (#n: pos)
  (m: square_matrix t n) (i: fin n) (c: t) : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality a i then c * m a b else m a b

(* Add c times row j to row i (i <> j). *)
let row_add (#t: Type) {| ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t) : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality a i then m a b + c * m j b else m a b

(* ==================================================================== *)
(*  MULTILINEARITY: det(row_scale m i c) = c * det m                   *)
(* ==================================================================== *)

(* Helper: shape lemma for prod_range built from split + unfold_left. *)

private let prod_range_shape_at
  (#t: Type) {| cr: commutative_ring t |}
  (f: nat -> t) (lo hi: nat) (i: nat)
  : Lemma (requires lo <= i /\ i < hi)
          (ensures prod_range f lo hi =
                   prod_range f lo i * (f i * prod_range f ((i ++ 1)) hi))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    prod_range_split f lo i hi;
    prod_range_unfold_left f i hi;
    assert (prod_range f i hi == f i * prod_range f ((i ++ 1)) hi);
    mul_congruence (prod_range f lo i) (prod_range f i hi)
                   (prod_range f lo i) (f i * prod_range f ((i ++ 1)) hi)

(* prod_range body' lo hi = c * prod_range body lo hi when body' differs
   from body only at index i where body' i = c * body i. *)

let prod_range_extract_scalar_left
  (#t: Type) {| cr: commutative_ring t |}
  (body body': nat -> t) (lo hi: nat) (i: nat) (c: t)
  : Lemma (requires lo <= i /\ i < hi /\
                    body' i = c * body i /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> body' k = body k))
          (ensures prod_range body' lo hi = c * prod_range body lo hi)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    prod_range_shape_at body  lo hi i;
    prod_range_shape_at body' lo hi i;
    prod_range_congruence body' body lo i (fun _ -> ());
    prod_range_congruence body' body ((i ++ 1)) hi (fun _ -> ());
    let l   = prod_range body lo i in
    let r0  = prod_range body ((i ++ 1)) hi in
    let bi  = body i in
    let bi' = body' i in
    let p   = bi * r0 in
    assert (prod_range body' lo i = l);
    assert (prod_range body' ((i ++ 1)) hi = r0);
    assert (bi' = c * bi);
    assert (prod_range body  lo hi = l * (bi * r0));
    mul_congruence bi' (prod_range body' ((i ++ 1)) hi) bi' r0;
    mul_congruence (prod_range body' lo i) (bi' * prod_range body' ((i ++ 1)) hi)
                   l (bi' * r0);
    trans_lemma [ prod_range body' lo hi;
                  prod_range body' lo i * (bi' * prod_range body' ((i ++ 1)) hi);
                  l * (bi' * r0) ];
    mul_congruence bi' r0 (c * bi) r0;
    mul_associativity c bi r0;
    trans_lemma [ bi' * r0; (c * bi) * r0; c * (bi * r0) ];
    mul_congruence l (bi' * r0) l (c * p);
    (* l * (c * p) = c * (l * p) via comm/assoc *)
    mul_associativity l c p;
    cr.cr_mic.mul_commutativity l c;
    mul_congruence (l * c) p (c * l) p;
    mul_associativity c l p;
    trans_lemma [ l * (c * p);
                  (l * c) * p;
                  (c * l) * p;
                  c * (l * p) ];
    mul_congruence c (l * p) c (prod_range body lo hi);
    trans_lemma [ prod_range body' lo hi;
                  l * (bi' * r0);
                  l * (c * p);
                  c * (l * p);
                  c * prod_range body lo hi ]

(* perm_product (row_scale m i c) p = c * perm_product m p. *)

let perm_product_row_scale
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i: fin n) (c: t) (p: permutation n)
  : Lemma (perm_product (row_scale m i c) p = c * perm_product m p)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let body  : nat -> t =
      fun k -> if k < n then m k (p.fwd k) else one in
    let body' : nat -> t =
      fun k ->
        if k < n then (row_scale m i c) k (p.fwd k) else one in
    assert ((row_scale m i c) i (p.fwd i) == c * m i (p.fwd i));
    assert (body' (i <: nat) = c * body (i <: nat));
    let agree_off (k: nat) : Lemma (0 <= k /\ k < n /\ k <> (i <: nat) ==> body' k = body k)
      = if k < n && k <> (i <: nat) then begin
          let kf : fin n = k in
          assert (kf <> i);
          assert ((row_scale m i c) kf (p.fwd kf) == m kf (p.fwd kf))
        end
    in
    Classical.forall_intro agree_off;
    prod_range_extract_scalar_left body body' 0 n (i <: nat) c;
    perm_product_unfold (row_scale m i c) p;
    perm_product_unfold m p

(* leibniz_term (row_scale m i c) p = c * leibniz_term m p. *)

let leibniz_term_row_scale
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i: fin n) (c: t) (p: permutation n)
  : Lemma (leibniz_term (row_scale m i c) p = c * leibniz_term m p)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    perm_product_row_scale m i c p;
    let pp  = perm_product m p in
    let pp' = perm_product (row_scale m i c) p in
    assert (pp' = c * pp);
    if parity p then ()
    else begin
      neg_congruence_lem pp' (c * pp);
      ring_neg_xy_is_x_times_neg_y c pp
    end

(* det(row_scale m i c) = c * det m. *)

let det_row_scale
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i: fin n) (c: t)
  : Lemma (det (row_scale m i c) = c * det m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let g = leibniz_term m in
    let f = leibniz_term (row_scale m i c) in
    let pointwise (s: permutation n) : Lemma (f s = c * g s)
      = leibniz_term_row_scale m i c s in
    Classical.forall_intro pointwise;
    sum_over_perms_mul_left_named n c f g (fun _ -> ());
    det_unfold (row_scale m i c);
    det_unfold m

(* ==================================================================== *)
(*  ALTERNATING: det m = 0 when two rows of m are equal                  *)
(* ==================================================================== *)

(* perm_product depends only on the pointwise values of m. *)

let perm_product_pointwise_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m1 m2: square_matrix t n) (p: permutation n)
  : Lemma (requires forall (a b: fin n). m1 a b = m2 a b)
          (ensures  perm_product m1 p = perm_product m2 p)
  = let body1 : nat -> t =
      fun k -> if k < n then m1 k (p.fwd k) else one in
    let body2 : nat -> t =
      fun k -> if k < n then m2 k (p.fwd k) else one in
    let pw (k: nat) : Lemma (0 <= k /\ k < n ==> body1 k = body2 k)
      = if k < n then begin
          let kf : fin n = k in
          assert (m1 kf (p.fwd kf) = m2 kf (p.fwd kf));
          ()
        end
    in
    Classical.forall_intro pw;
    prod_range_congruence body1 body2 0 n (fun _ -> ());
    perm_product_unfold m1 p;
    perm_product_unfold m2 p

(* leibniz_term is stable under pointwise equality. *)

let leibniz_term_pointwise_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m1 m2: square_matrix t n) (p: permutation n)
  : Lemma (requires forall (a b: fin n). m1 a b = m2 a b)
          (ensures  leibniz_term m1 p = leibniz_term m2 p)
  = elim_equatable_laws t ();
    perm_product_pointwise_eq m1 m2 p;
    if parity p
    then ()
    else neg_congruence_lem (perm_product m1 p) (perm_product m2 p)

(* Pointwise-equal matrices have equal determinants. *)

let det_pointwise_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: pos) (m1 m2: square_matrix t n)
  : Lemma (requires forall (a b: fin n). m1 a b = m2 a b)
          (ensures  det m1 = det m2)
  = let pw (p: permutation n) : Lemma (leibniz_term m1 p = leibniz_term m2 p)
      = leibniz_term_pointwise_eq m1 m2 p in
    Classical.forall_intro pw;
    sum_over_perms_congruence n (leibniz_term m1) (leibniz_term m2) (fun _ -> ())

(* If rows i and j of m are equal, swapping them yields a pointwise-equal matrix. *)

let row_swap_equal_rows_pointwise
  (#t: Type) {| equatable t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires forall (k: fin n). m i k = m j k)
          (ensures  forall (a b: fin n). row_swap m i j a b = m a b)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let aux (a b: fin n) : Lemma (row_swap m i j a b = m a b)
      = if a = i then begin
          transposition_fwd_left n i j
        end
        else if a = j then begin
          transposition_fwd_right n i j
        end
        else begin
          transposition_fwd_other n i j a
        end
    in
    Classical.forall_intro_2 aux

(* Strengthened alternating result over a general commutative ring. *)

let det_two_equal_rows_cr
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires ~(i == j) /\
                    (forall (k: fin n). m i k = m j k))
          (ensures  det m = zero)
  = let r : ring t = cr.cr_r in
    let acg : add_comm_group t = acg_of_ring_local t r in
    let tau = transposition n i j in
    let f : permutation n -> t = leibniz_term m in
    elim_equatable_laws t ();
    trans_for_calc t ();
    leibniz_term_respects_perm_eq m;
    transposition_self_inverse n i j;
    let tau_ne_id_aux ()
      : Lemma (requires perm_eq tau (identity n)) (ensures False)
      = parity_perm_eq_invariant tau (identity n);
        parity_transposition n i j;
        parity_identity n
    in
    Classical.move_requires tau_ne_id_aux ();
    assert (~(perm_eq tau (identity n)));
    row_swap_equal_rows_pointwise m i j;
    let pair_zero (s: permutation n)
      : Lemma (f s + f (compose s tau) = zero)
      = let a = f s in
        let b = f (compose s tau) in
        leibniz_term_row_swap m i j s;
        assert (leibniz_term (row_swap m i j) s = -b);
        leibniz_term_pointwise_eq (row_swap m i j) m s;
        assert (leibniz_term (row_swap m i j) s = a);
        assert (a = -b);
        add_congruence a b (-b) b;
        acg.add_negation b;
        transitivity (a + b) (-b + b) (zero)
    in
    Classical.forall_intro pair_zero;
    sum_over_perms_pair_cancel n f tau (fun _ -> ());
    det_unfold m

(* ==================================================================== *)
(*  ROW-REPLACE helper                                                   *)
(*  row_replace m i u : matrix with row i replaced by the function u.    *)
(* ==================================================================== *)
let row_replace (#t: Type) (#n: pos)
  (m: square_matrix t n) (i: fin n) (u: fin n -> t)
  : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality a i then u b else m a b

(* prod_range_extract_add_left: given body_add i = body i + c * body_repl i
   and agreement elsewhere, prod_range body_add = prod_range body + c * prod_range body_repl. *)

private let prod_range_extract_add_left
  (#t: Type) {| cr: commutative_ring t |}
  (b ba br: nat -> t) (lo hi: nat) (i: nat) (c: t)
  : Lemma (requires lo <= i /\ i < hi /\
                    ba i = b i + c * br i /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> ba k = b k) /\
                    (forall (k: nat). lo <= k /\ k < hi /\ k <> i ==> br k = b k))
          (ensures prod_range ba lo hi = prod_range b lo hi + c * prod_range br lo hi)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    prod_range_shape_at b  lo hi i;
    prod_range_shape_at ba lo hi i;
    prod_range_shape_at br lo hi i;
    prod_range_congruence ba b lo i (fun _ -> ());
    prod_range_congruence ba b ((i ++ 1)) hi (fun _ -> ());
    prod_range_congruence br b lo i (fun _ -> ());
    prod_range_congruence br b ((i ++ 1)) hi (fun _ -> ());
    let l = prod_range b lo i in
    let rr = prod_range b ((i ++ 1)) hi in
    let u = b i in
    let v = br i in
    let bai = ba i in
    assert (bai = u + c * v);
    (* prod_range ba lo hi = l * (bai * rr) *)
    mul_congruence bai (prod_range ba ((i ++ 1)) hi) bai rr;
    mul_congruence (prod_range ba lo i) (bai * prod_range ba ((i ++ 1)) hi) l (bai * rr);
    assert (prod_range ba lo hi = l * (bai * rr));
    (* prod_range b lo hi = l * (u * rr) *)
    mul_congruence u (prod_range b ((i ++ 1)) hi) u rr;
    mul_congruence (prod_range b lo i) (u * prod_range b ((i ++ 1)) hi) l (u * rr);
    assert (prod_range b lo hi = l * (u * rr));
    (* prod_range br lo hi = l * (v * rr) *)
    mul_congruence v (prod_range br ((i ++ 1)) hi) v rr;
    mul_congruence (prod_range br lo i) (v * prod_range br ((i ++ 1)) hi) l (v * rr);
    assert (prod_range br lo hi = l * (v * rr));
    (* l * (bai * rr) = l * ((u + c*v) * rr) *)
    mul_congruence bai rr (u + c * v) rr;
    mul_congruence l (bai * rr) l ((u + c * v) * rr);
    assert (l * (bai * rr) = l * ((u + c * v) * rr));
    (* (u + c*v) * rr = u * rr + (c*v) * rr *)
    right_distributivity rr u (c * v);
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
    cr.cr_mic.mul_commutativity l c;
    mul_congruence (l * c) p1 (c * l) p1;
    mul_associativity c l p1;
    trans_lemma [ l * (c * p1); (l * c) * p1; (c * l) * p1; c * (l * p1) ];
    assert (l * (c * (v * rr)) = c * (l * (v * rr)));
    mul_congruence c (l * (v * rr)) c (prod_range br lo hi);
    add_congruence (l * (u * rr)) (l * ((c * v) * rr))
                   (prod_range b lo hi) (c * prod_range br lo hi);
    assert (l * (u * rr) + l * ((c * v) * rr) = prod_range b lo hi + c * prod_range br lo hi);
    transitivity (prod_range ba lo hi) (l * (u * rr) + l * ((c * v) * rr))
                 (prod_range b lo hi + c * prod_range br lo hi)

(* ==================================================================== *)
(*  ALTERNATING (additive form):                                         *)
(*  det (row_add m i j c) = det m                                        *)
(* ==================================================================== *)

(* perm_product (row_add m i j c) p splits additively. *)

let perm_product_row_add_split
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t) (p: permutation n)
  : Lemma (requires ~(i == j))
          (ensures  perm_product (row_add m i j c) p
                  = perm_product m p
                  + c * perm_product (row_replace m i (m j)) p)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let body  : nat -> t =
      fun k -> if k < n then m k (p.fwd k) else one in
    let body_add : nat -> t =
      fun k ->
        if k < n then (row_add m i j c) k (p.fwd k) else one in
    let body_repl : nat -> t =
      fun k ->
        if k < n then (row_replace m i (m j)) k (p.fwd k) else one in
    let in_ : nat = i in
    let u = m i (p.fwd i) in
    let v = m j (p.fwd i) in
    assert (body_add in_ == u + c * v);
    assert (body in_ == u);
    assert (body_repl in_ == v);
    mul_congruence c v c (body_repl in_);
    add_congruence u (c * v) (body in_) (c * body_repl in_);
    assert (body_add in_ = body in_ + c * body_repl in_);
    prod_range_extract_add_left body body_add body_repl 0 n in_ c;
    perm_product_unfold (row_add m i j c) p;
    perm_product_unfold m p;
    perm_product_unfold (row_replace m i (m j)) p

(* leibniz_term version of the same split. *)

let leibniz_term_row_add_split
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t) (p: permutation n)
  : Lemma (requires ~(i == j))
          (ensures  leibniz_term (row_add m i j c) p
                  = leibniz_term m p
                  + c * leibniz_term (row_replace m i (m j)) p)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    perm_product_row_add_split m i j c p;
    let pp_ra = perm_product (row_add m i j c) p in
    let pp_m  = perm_product m p in
    let pp_r  = perm_product (row_replace m i (m j)) p in
    assert (pp_ra = pp_m + c * pp_r);
    if parity p
    then ()
    else begin
      neg_congruence_lem pp_ra (pp_m + c * pp_r);
      neg_of_sum_local pp_m (c * pp_r);
      ring_neg_xy_is_x_times_neg_y c pp_r;
      add_congruence (-pp_m) (-(c * pp_r)) (-pp_m) (c * (-pp_r));
      trans_lemma [ -pp_ra; -(pp_m + c * pp_r); (-pp_m) + (-(c * pp_r)); (-pp_m) + c * (-pp_r) ]
    end

(* row_replace m i (m j) has rows i and j both equal to m j. *)

let row_replace_with_other_row_has_equal_rows
  (#t: Type) {| equatable t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires ~(i == j))
          (ensures  forall k. row_replace m i (m j) i k = row_replace m i (m j) j k)
  = elim_equatable_laws t ()

(* Headline: det (row_add m i j c) = det m, in a commutative ring
   (using det_two_equal_rows_cr which works without char≠2). *)

let det_row_add
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t)
  : Lemma (requires ~(i == j))
          (ensures  det (row_add m i j c) = det m) =
    elim_equatable_laws t ();
    trans_for_calc t ();
    let f = leibniz_term (row_add m i j c) in
    let g = leibniz_term m in
    let h = leibniz_term (row_replace m i (m j)) in
    let pw (p: permutation n) : Lemma (f p = g p + c * h p)
      = leibniz_term_row_add_split m i j c p in
    Classical.forall_intro pw;
    let ch : permutation n -> t = fun p -> c * h p in
    sum_over_perms_add_named n f g ch (fun _ -> ());
    sum_over_perms_mul_left_named n c ch h (fun _ -> ());
    add_congruence (sum_over_perms n g) (sum_over_perms n ch)
                   (sum_over_perms n g) (c * sum_over_perms n h);
    det_unfold (row_add m i j c);
    det_unfold m;
    det_unfold (row_replace m i (m j));
    row_replace_with_other_row_has_equal_rows m i j;
    det_two_equal_rows_cr (row_replace m i (m j)) i j;
    mul_congruence c (sum_over_perms n h) c (zero);
    ring_zero_is_right_absorber c;
    add_congruence (sum_over_perms n g) (c * sum_over_perms n h)
                   (sum_over_perms n g) (zero);
    x_plus_zero (sum_over_perms n g)

(* ====================================================================== *)
(*  Additive multilinearity of det in a row (row split).                  *)
(* ====================================================================== *)

let perm_product_row_split
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i: fin n) (u v uv: fin n -> t) (p: permutation n)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures perm_product (row_replace m i uv) p
                 = perm_product (row_replace m i u) p
                 + perm_product (row_replace m i v) p)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let muv = row_replace m i uv in
    let mu  = row_replace m i u in
    let mv  = row_replace m i v in
    let body : nat -> t =
      fun k -> if k < n then mu k (p.fwd k) else one in
    let body_uv : nat -> t =
      fun k -> if k < n then muv k (p.fwd k) else one in
    let body_v : nat -> t =
      fun k -> if k < n then mv k (p.fwd k) else one in
    let in_ : nat = i in
    let upi = u (p.fwd i) in
    let vpi = v (p.fwd i) in
    let uvi = uv (p.fwd i) in
    assert (uvi = upi + vpi);
    assert (body_uv in_ == uvi);
    assert (body    in_ == upi);
    assert (body_v  in_ == vpi);
    one_mul_x vpi;
    add_congruence upi vpi upi (one * vpi);
    assert (body_uv in_ = body in_ + one * body_v in_);
    prod_range_extract_add_left body body_uv body_v 0 n in_ (one);
    assert (prod_range body_uv 0 n
            = prod_range body 0 n + one * prod_range body_v 0 n);
    one_mul_x (prod_range body_v 0 n);
    add_congruence (prod_range body 0 n) (one * prod_range body_v 0 n)
                   (prod_range body 0 n) (prod_range body_v 0 n);
    transitivity (prod_range body_uv 0 n)
                 (prod_range body 0 n + one * prod_range body_v 0 n)
                 (prod_range body 0 n + prod_range body_v 0 n);
    perm_product_unfold muv p;
    perm_product_unfold mu  p;
    perm_product_unfold mv  p;
    add_congruence (prod_range body 0 n) (prod_range body_v 0 n)
                   (perm_product mu p)   (perm_product mv p);
    transitivity (perm_product muv p) (prod_range body_uv 0 n)
                 (prod_range body 0 n + prod_range body_v 0 n);
    transitivity (perm_product muv p)
                 (prod_range body 0 n + prod_range body_v 0 n)
                 (perm_product mu p + perm_product mv p)

let leibniz_term_row_split
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i: fin n) (u v uv: fin n -> t) (p: permutation n)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures leibniz_term (row_replace m i uv) p
                 = leibniz_term (row_replace m i u) p
                 + leibniz_term (row_replace m i v) p)
  = let acg : add_comm_group t = acg_of_ring_local t cr.cr_r in
    elim_equatable_laws t ();
    trans_for_calc t ();
    perm_product_row_split m i u v uv p;
    let muv = row_replace m i uv in
    let mu  = row_replace m i u in
    let mv  = row_replace m i v in
    let pp_uv = perm_product muv p in
    let pp_u  = perm_product mu  p in
    let pp_v  = perm_product mv  p in
    if parity p
    then ()
    else begin
      neg_congruence_lem pp_uv (pp_u + pp_v);
      neg_of_sum_local pp_u pp_v;
      acg.add_commutativity (-pp_v) (-pp_u);
      trans_lemma [ -pp_uv;
                    -(pp_u + pp_v);
                    (-pp_v) + (-pp_u);
                    (-pp_u) + (-pp_v) ]
    end

let det_row_split
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i: fin n) (u v uv: fin n -> t)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures det (row_replace m i uv)
                 = det (row_replace m i u) + det (row_replace m i v))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let muv = row_replace m i uv in
    let mu  = row_replace m i u in
    let mv  = row_replace m i v in
    let f = leibniz_term muv in
    let g = leibniz_term mu in
    let h = leibniz_term mv in
    let pw (p: permutation n) : Lemma (f p = g p + h p)
      = leibniz_term_row_split m i u v uv p in
    Classical.forall_intro pw;
    sum_over_perms_add_named n f g h (fun _ -> ());
    det_unfold muv;
    det_unfold mu;
    det_unfold mv;
    add_congruence (sum_over_perms n g) (sum_over_perms n h)
                   (det mu)             (det mv);
    transitivity (det muv) (sum_over_perms n f)
                 (sum_over_perms n g + sum_over_perms n h);
    transitivity (det muv) (sum_over_perms n g + sum_over_perms n h)
                 (det mu + det mv)

(* ============================================================== *)
(* Column operations and determinant lemmas, derived via transpose. *)
(* ============================================================== *)

let col_swap (#t: Type) (#n: pos)
  (m: square_matrix t n) (i j: fin n) : square_matrix t n
  = permute_cols m (transposition n i j)

let col_scale (#t: Type) {| ring t |} (#n: pos)
  (m: square_matrix t n) (i: fin n) (c: t) : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality b i then m a b * c else m a b

(* col_add defined in .fsti *)

let transpose_col_swap_pointwise (#t: Type) (#n: pos)
  (m: square_matrix t n) (i j: fin n) (a b: fin n)
  : Lemma (transpose (col_swap m i j) a b == row_swap (transpose m) i j a b)
  = ()

let det_col_swap (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires ~(i == j))
          (ensures det (col_swap m i j) = -(det m))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let pw (a b: fin n)
      : Lemma (transpose (col_swap m i j) a b = row_swap (transpose m) i j a b)
      = transpose_col_swap_pointwise m i j a b
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq (transpose (col_swap m i j)) (row_swap (transpose m) i j);
    det_transpose (col_swap m i j);
    det_row_swap (transpose m) i j;
    det_transpose m;
    neg_congruence_lem (det (transpose m)) (det m);
    transitivity (det (col_swap m i j))
                 (det (transpose (col_swap m i j)))
                 (det (row_swap (transpose m) i j));
    transitivity (det (col_swap m i j))
                 (det (row_swap (transpose m) i j))
                 (-(det (transpose m)));
    transitivity (det (col_swap m i j))
                 (-(det (transpose m)))
                 (-(det m))

let transpose_col_scale_to_row_scale (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i: fin n) (c: t) (a b: fin n)
  : Lemma (transpose (col_scale m i c) a b = row_scale (transpose m) i c a b)
  = elim_equatable_laws t ();
    if (a <: nat) = (i <: nat) then begin
      assert (transpose (col_scale m i c) a b == m b a * c);
      assert (row_scale (transpose m) i c a b == c * m b a);
      (cr.cr_mic).mul_commutativity (m b a) c
    end else begin
      assert (transpose (col_scale m i c) a b == m b a)
    end

let det_col_scale (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i: fin n) (c: t)
  : Lemma (det (col_scale m i c) = c * det m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let pw (a b: fin n)
      : Lemma (transpose (col_scale m i c) a b = row_scale (transpose m) i c a b)
      = transpose_col_scale_to_row_scale m i c a b
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq (transpose (col_scale m i c)) (row_scale (transpose m) i c);
    det_transpose (col_scale m i c);
    det_row_scale (transpose m) i c;
    det_transpose m;
    mul_congruence c (det (transpose m)) c (det m);
    transitivity (det (col_scale m i c))
                 (det (transpose (col_scale m i c)))
                 (det (row_scale (transpose m) i c));
    transitivity (det (col_scale m i c))
                 (det (row_scale (transpose m) i c))
                 (c * det (transpose m));
    transitivity (det (col_scale m i c))
                 (c * det (transpose m))
                 (c * det m)

let transpose_col_add_to_row_add (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t) (a b: fin n)
  : Lemma (requires ~(i == j))
          (ensures transpose (col_add m i j c) a b = row_add (transpose m) i j c a b)
  = elim_equatable_laws t ();
    if (a <: nat) = (i <: nat) then begin
      assert (transpose (col_add m i j c) a b == m b a + m b j * c);
      assert (row_add (transpose m) i j c a b == m b a + c * m b j);
      (cr.cr_mic).mul_commutativity (m b j) c;
      add_congruence (m b a) (m b j * c) (m b a) (c * m b j)
    end else ()

let det_col_add (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t)
  : Lemma (requires ~(i == j))
          (ensures det (col_add m i j c) = det m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let pw (a b: fin n)
      : Lemma (transpose (col_add m i j c) a b = row_add (transpose m) i j c a b)
      = transpose_col_add_to_row_add m i j c a b
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq (transpose (col_add m i j c)) (row_add (transpose m) i j c);
    det_transpose (col_add m i j c);
    det_row_add (transpose m) i j c;
    det_transpose m;
    transitivity (det (col_add m i j c))
                 (det (transpose (col_add m i j c)))
                 (det (row_add (transpose m) i j c));
    transitivity (det (col_add m i j c))
                 (det (row_add (transpose m) i j c))
                 (det (transpose m));
    transitivity (det (col_add m i j c))
                 (det (transpose m))
                 (det m)

(* det_zero_column: derived from det_zero_row via transpose. *)

let det_zero_column (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (j: fin n)
  : Lemma (requires forall (k: fin n). m k j = zero)
          (ensures det m = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let mt = transpose m in
    let pw (k: fin n) : Lemma (mt j k = zero)
      = assert (mt j k == m k j)
    in
    Classical.forall_intro pw;
    det_zero_row mt j;
    det_transpose m;
    transitivity (det m) (det mt) (zero)

(* ====================================================================== *)
(*  Column counterpart: col_replace and det_col_split, via transpose.     *)
(* ====================================================================== *)

let col_replace (#t: Type) (#n: pos)
  (m: square_matrix t n) (j: fin n) (u: fin n -> t)
  : square_matrix t n
  = fun (a: fin n) (b: fin n) -> if Prims.op_Equality b j then u a else m a b

let transpose_col_replace_pointwise (#t: Type) (#n: pos)
  (m: square_matrix t n) (j: fin n) (u: fin n -> t) (a b: fin n)
  : Lemma (transpose (col_replace m j u) a b == row_replace (transpose m) j u a b)
  = ()

let det_col_split
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (j: fin n) (u v uv: fin n -> t)
  : Lemma (requires forall (k: fin n). uv k = u k + v k)
          (ensures det (col_replace m j uv)
                 = det (col_replace m j u) + det (col_replace m j v))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let cuv = col_replace m j uv in
    let cu  = col_replace m j u  in
    let cv  = col_replace m j v  in
    let mt  = transpose m in
    let ruv = row_replace mt j uv in
    let ru  = row_replace mt j u  in
    let rv  = row_replace mt j v  in
    let pw_uv (a b: fin n)
      : Lemma (transpose cuv a b = ruv a b)
      = transpose_col_replace_pointwise m j uv a b in
    Classical.forall_intro_2 pw_uv;
    let pw_u (a b: fin n)
      : Lemma (transpose cu a b = ru a b)
      = transpose_col_replace_pointwise m j u a b in
    Classical.forall_intro_2 pw_u;
    let pw_v (a b: fin n)
      : Lemma (transpose cv a b = rv a b)
      = transpose_col_replace_pointwise m j v a b in
    Classical.forall_intro_2 pw_v;
    det_pointwise_eq (transpose cuv) ruv;
    det_pointwise_eq (transpose cu)  ru;
    det_pointwise_eq (transpose cv)  rv;
    det_transpose cuv;
    det_transpose cu;
    det_transpose cv;
    det_row_split mt j u v uv;
    assert (det ruv = det ru + det rv);
    add_congruence (det ru) (det rv) (det cu) (det cv);
    transitivity (det cuv) (det ru + det rv) (det cu + det cv)

(* ====================================================================== *)
(*  L3: General row-permutation determinant law                            *)
(*       det (permute_rows m sigma) = sign(sigma) * det m                  *)
(*  We split into the two parity cases for clarity.                        *)
(* ====================================================================== *)

let perm_product_permute_rows
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (sigma: permutation n) (p: permutation n)
  : Lemma (perm_product (permute_rows m sigma) p =
           perm_product m (compose p (inverse sigma)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let sigma_inv = inverse sigma in
    let q = compose p sigma_inv in
    let lhs_body : nat -> t =
      fun k -> if k < n
                  then (permute_rows m sigma) k (p.fwd k)
                  else one in
    let rhs_body : nat -> t =
      fun k -> if k < n
                  then m k (q.fwd k)
                  else one in
    let f : nat -> t =
      fun k -> if k < n
                  then m k (p.fwd ((sigma_inv.fwd k) <: fin n))
                  else one in
    inverse_left sigma;
    let body_p_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==>
       lhs_body k = f (sigma.fwd k))
      = if 0 <= k && k < n then begin
          let kf : fin n = k <: fin n in
          let sk : fin n = sigma.fwd kf in
          compose_fwd sigma_inv sigma kf;
          perm_eq_elim (compose sigma_inv sigma) (identity n) kf;
          identity_fwd n kf;
          assert (sigma_inv.fwd sk == kf)
        end in
    Classical.forall_intro body_p_hyp;
    let body_id_hyp (k: nat) : Lemma
      (0 <= k /\ k < n ==> rhs_body k = f k)
      = if 0 <= k && k < n then begin
          let kf : fin n = k <: fin n in
          compose_fwd p sigma_inv kf
        end in
    Classical.forall_intro body_id_hyp;
    prod_range_perm_invariance_fn f lhs_body rhs_body sigma
      (fun _ -> ()) (fun _ -> ());
    perm_product_unfold (permute_rows m sigma) p;
    perm_product_unfold m q

let leibniz_term_permute_rows_even
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (sigma: permutation n) (p: permutation n)
  : Lemma (requires parity sigma == true)
          (ensures leibniz_term (permute_rows m sigma) p =
                   leibniz_term m (compose p (inverse sigma)))
  = let sigma_inv = inverse sigma in
    let q = compose p sigma_inv in
    perm_product_permute_rows m sigma p;
    sign_homomorphism p sigma_inv;
    parity_inverse sigma;
    let lhs = leibniz_term (permute_rows m sigma) p in
    let pp1 = perm_product (permute_rows m sigma) p in
    let pp2 = perm_product m q in
    let rhs = leibniz_term m q in
    if parity p then begin
      assert (parity q == true);
      assert (lhs == pp1);
      assert (rhs == pp2)
    end else begin
      assert (parity q == false);
      assert (lhs == -pp1);
      assert (rhs == -pp2);
      neg_congruence pp1 pp2
    end

let leibniz_term_permute_rows_odd
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (sigma: permutation n) (p: permutation n)
  : Lemma (requires parity sigma == false)
          (ensures leibniz_term (permute_rows m sigma) p =
                   -(leibniz_term m (compose p (inverse sigma))))
  = let sigma_inv = inverse sigma in
    let q = compose p sigma_inv in
    perm_product_permute_rows m sigma p;
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
      double_negation_lemma #t #cr pp2;
      symmetry (-(-pp2)) pp2;
      transitivity pp1 pp2 (-(-pp2))
    end else begin
      assert (parity q == true);
      assert (lhs == -pp1);
      assert (leibniz_term m q == pp2);
      assert (rhs == -pp2);
      neg_congruence pp1 pp2
    end

let det_permute_rows_even
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (sigma: permutation n)
  : Lemma (requires parity sigma == true)
          (ensures  det (permute_rows m sigma) = det m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let sigma_inv = inverse sigma in
    let f = leibniz_term (permute_rows m sigma) in
    let g = leibniz_term m in
    leibniz_term_respects_perm_eq m;
    sum_over_perms_reindex n g sigma_inv;
    let pointwise (s: permutation n) : Lemma (f s = g (compose s sigma_inv))
      = leibniz_term_permute_rows_even m sigma s in
    Classical.forall_intro pointwise;
    sum_over_perms_congruence n f (fcomp g (flip compose sigma_inv)) (fun _ -> ());
    det_unfold (permute_rows m sigma);
    det_unfold m;
    transitivity (det (permute_rows m sigma))
                 (sum_over_perms n f)
                 (sum_over_perms n (fcomp g (flip compose sigma_inv)));
    transitivity (det (permute_rows m sigma))
                 (sum_over_perms n (fcomp g (flip compose sigma_inv)))
                 (sum_over_perms n g);
    transitivity (det (permute_rows m sigma))
                 (sum_over_perms n g)
                 (det m)

let det_permute_rows_odd
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (sigma: permutation n)
  : Lemma (requires parity sigma == false)
          (ensures  det (permute_rows m sigma) = -(det m))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let sigma_inv = inverse sigma in
    let f = leibniz_term (permute_rows m sigma) in
    let g = leibniz_term m in
    leibniz_term_respects_perm_eq m;
    sum_over_perms_reindex n g sigma_inv;
    let pointwise (s: permutation n) : Lemma (f s = -(g (compose s sigma_inv)))
      = leibniz_term_permute_rows_odd m sigma s in
    Classical.forall_intro pointwise;
    sum_over_perms_congruence n f (fcomp neg (fcomp g (flip compose sigma_inv))) (fun _ -> ());
    sum_over_perms_neg_named n f
      (fcomp g (flip compose sigma_inv)) (fun _ -> ());
    det_unfold (permute_rows m sigma);
    det_unfold m;
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

let det_permute_rows
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (sigma: permutation n)
  : Lemma (det (permute_rows m sigma) =
           (if parity sigma then det m else -(det m)))
  = if parity sigma
    then det_permute_rows_even m sigma
    else det_permute_rows_odd  m sigma

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

(* (-1)^k, skip, minor are defined in .fsti *)

let minus_one_pow_zero (#t: Type) {| cr: commutative_ring t |}
  : Lemma (minus_one_pow #t 0 == one)
  = ()

let minus_one_pow_one (#t: Type) {| cr: commutative_ring t |}
  : Lemma (minus_one_pow #t 1 == (- (one)))
  = ()

let minus_one_pow_even (#t: Type) {| cr: commutative_ring t |} (k: nat)
  : Lemma (requires Prims.op_Modulus k 2 = 0)
          (ensures  minus_one_pow #t k == one)
  = ()

let minus_one_pow_odd (#t: Type) {| cr: commutative_ring t |} (k: nat)
  : Lemma (requires Prims.op_Modulus k 2 = 1)
          (ensures  minus_one_pow #t k == (- (one)))
  = ()

let skip_lt (#n: pos) (i: fin n) (a: fin ((n - 1)))
  : Lemma (requires (a <: nat) < (i <: nat))
          (ensures  (skip i a <: nat) == (a <: nat))
  = ()

let skip_ge (#n: pos) (i: fin n) (a: fin ((n - 1)))
  : Lemma (requires (a <: nat) >= (i <: nat))
          (ensures  (skip i a <: nat) == (a ++ 1))
  = ()

(* skip is injective. *)
let skip_injective (#n: pos) (i: fin n) (a b: fin ((n - 1)))
  : Lemma (requires (skip i a <: nat) == (skip i b <: nat))
          (ensures  (a <: nat) == (b <: nat))
  = ()

(* skip never lands on i. *)
let skip_avoids (#n: pos) (i: fin n) (a: fin ((n - 1)))
  : Lemma (~((skip i a <: nat) == (i <: nat)))
  = ()

let minor_at (#t: Type) (#n: pos{ n > 1 }) (m: square_matrix t n) (i j: fin n)
             (a b: fin ((n - 1)))
  : Lemma (minor m i j a b == m (skip i a) (skip j b))
  = ()

(* ====================================================================== *)
(*  inject: building a permutation of fin n from a permutation of         *)
(*          fin (n-1) and a chosen image j for position i.                *)
(* ====================================================================== *)

(* Partial inverse of `skip i`: removes index i, mapping fin n \ {i} into fin (n-1). *)
let unskip (#n: pos) (i: fin n) (k: fin n{(k <: nat) <> (i <: nat)})
  : fin ((n - 1))
  = if (k <: nat) < (i <: nat) then (k <: nat) else (k - 1)

let skip_unskip (#n: pos) (i: fin n) (k: fin n)
  : Lemma (requires (k <: nat) <> (i <: nat))
          (ensures  (skip i (unskip i k) <: nat) == (k <: nat))
  = ()

let unskip_skip (#n: pos) (i: fin n) (a: fin ((n - 1)))
  : Lemma ((unskip i (skip i a) <: nat) == (a <: nat))
  = ()

(* Build a permutation of fin n with sigma(i) = j whose action on the
   remaining positions is determined by sigma' via the canonical relabelling. *)

let inject (#n: pos) (sigma': permutation ((n - 1)))
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
          let u : fin ((n - 1)) = unskip j l in
          let a' : fin ((n - 1)) = sigma'.bwd u in
          let k : fin n = skip i a' in
          skip_avoids i a';
          unskip_skip i a';
          sigma'.fwd_bwd_id u;
          skip_unskip j l
        end in
    let bwd_fwd_id (k: fin n) : Lemma (bwd (fwd k) == k)
      = if (k <: nat) = (i <: nat) then ()
        else begin
          let a : fin ((n - 1)) = unskip i k in
          let b : fin ((n - 1)) = sigma'.fwd a in
          let l : fin n = skip j b in
          skip_avoids j b;
          unskip_skip j b;
          sigma'.bwd_fwd_id a;
          skip_unskip i k
        end in
    { fwd; bwd; fwd_bwd_id; bwd_fwd_id }

let inject_fwd_at_i (#n: pos) (sigma': permutation ((n - 1)))
                    (i j: fin n)
  : Lemma ((inject sigma' i j).fwd i == j)
  = ()

let inject_fwd_off (#n: pos) (sigma': permutation ((n - 1)))
                   (i j: fin n) (k: fin n)
  : Lemma (requires (k <: nat) <> (i <: nat))
          (ensures  (inject sigma' i j).fwd k
                    == skip j (sigma'.fwd (unskip i k)))
  = ()

let inject_bwd_at_j (#n: pos) (sigma': permutation ((n - 1)))
                    (i j: fin n)
  : Lemma ((inject sigma' i j).bwd j == i)
  = ()

(* ====================================================================== *)
(*  project: inverse of `inject`.                                         *)
(* ====================================================================== *)

let project (#n: pos) (sigma: permutation n) (i: fin n)
  : permutation ((n - 1))
  = let j : fin n = sigma.fwd i in
    sigma.bwd_fwd_id i;
    assert (sigma.bwd j == i);
    sigma.fwd_bwd_id (sigma.fwd i);
    let fwd (a: fin ((n - 1)))
      : fin ((n - 1))
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
    let bwd (b: fin ((n - 1)))
      : fin ((n - 1))
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
    let fwd_bwd_id (b: fin ((n - 1)))
      : Lemma (fwd (bwd b) == b)
      = let l : fin n = skip j b in
        skip_avoids j b;
        let w : fin n = sigma.bwd l in
        sigma.fwd_bwd_id l;
        assert (~((w <: nat) == (i <: nat)));
        let a : fin ((n - 1)) = unskip i w in
        skip_unskip i w;
        assert ((skip i a <: nat) == (w <: nat));
        let v : fin n = sigma.fwd (skip i a) in
        assert ((skip i a <: nat) == (w <: nat));
        assert (sigma.fwd w == l);
        unskip_skip j b in
    let bwd_fwd_id (a: fin ((n - 1)))
      : Lemma (bwd (fwd a) == a)
      = let k : fin n = skip i a in
        skip_avoids i a;
        let v : fin n = sigma.fwd k in
        sigma.bwd_fwd_id k;
        assert (~((v <: nat) == (j <: nat)));
        let b : fin ((n - 1)) = unskip j v in
        skip_unskip j v;
        assert ((skip j b <: nat) == (v <: nat));
        let w : fin n = sigma.bwd (skip j b) in
        assert (sigma.bwd v == k);
        unskip_skip i a in
    { fwd; bwd; fwd_bwd_id; bwd_fwd_id }

(* Roundtrip: inject (project sigma i) i (sigma.fwd i) is perm_eq to sigma. *)

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
          let a : fin ((n - 1)) = unskip i k in
          assert (injected.fwd k == skip j (sigma'.fwd a));
          skip_unskip i k;
          assert ((skip i a <: nat) == (k <: nat));
          sigma'.bwd_fwd_id a;
          let b : fin ((n - 1)) = sigma'.fwd a in
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

(* --- Lemma: inject id i i is identity --------------------------------- *)

let inject_id_is_identity (#n: pos) (i: fin n)
  : Lemma (perm_eq (inject (identity ((n - 1))) i i) (identity n))
  = let sigma' = identity ((n - 1)) in
    let inj = inject sigma' i i in
    let pointwise (k: fin n) : Lemma (inj.fwd k == (identity n).fwd k)
      = if (k <: nat) = (i <: nat) then begin
          inject_fwd_at_i sigma' i i;
          identity_fwd n k
        end else begin
          inject_fwd_off sigma' i i k;
          identity_fwd ((n - 1)) (unskip i k);
          skip_unskip i k;
          identity_fwd n k
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj (identity n) pointwise

(* --- Lemma: inject (compose σ1 σ2) i i ≡ compose (inject σ1 i i) (inject σ2 i i) --- *)

let inject_compose_diag (#n: pos)
  (sigma1 sigma2: permutation ((n - 1))) (i: fin n)
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
          let a : fin ((n - 1)) = unskip i k in
          let b : fin ((n - 1)) = sigma2.fwd a in
          let m : fin n = skip i b in
          skip_avoids i b;
          inject_fwd_off sigma1 i i m;
          unskip_skip i b;
          compose_fwd sigma1 sigma2 a
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj_c comp pointwise

(* --- Lemma: inject (transposition a b) i i ≡ transposition n (skip i a) (skip i b) --- *)

let inject_transposition_diag (#n: pos)
  (a b: fin ((n - 1))) (i: fin n)
  : Lemma (perm_eq (inject (transposition ((n - 1)) a b) i i)
                   (transposition n (skip i a) (skip i b)))
  = let tau = transposition ((n - 1)) a b in
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
          let u : fin ((n - 1)) = unskip i k in
          if (u <: nat) = (a <: nat) then begin
            transposition_fwd_left ((n - 1)) a b;
            assert (tau.fwd u == b);
            assert (skip i (tau.fwd u) == sb);
            unskip_skip i a;
            assert ((u <: nat) == (a <: nat));
            skip_unskip i k;
            assert ((skip i u <: nat) == (k <: nat));
            assert ((k <: nat) == (sa <: nat));
            transposition_fwd_left n sa sb
          end else if (u <: nat) = (b <: nat) then begin
            transposition_fwd_right ((n - 1)) a b;
            assert (tau.fwd u == a);
            assert (skip i (tau.fwd u) == sa);
            unskip_skip i b;
            skip_unskip i k;
            assert ((k <: nat) == (sb <: nat));
            transposition_fwd_right n sa sb
          end else begin
            transposition_fwd_other ((n - 1)) a b u;
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

(* --- skip i d ≠ skip i (d+1) when d+1 < n-1 --- *)
let skip_adjacent_distinct (#n: pos) (i: fin n) (d: nat{(d ++ 1) < (n - 1)})
  : Lemma (~((skip i (d <: fin ((n - 1))) <: nat) ==
             (skip i (((d ++ 1)) <: fin ((n - 1))) <: nat)))
  = let a : fin ((n - 1)) = d in
    let b : fin ((n - 1)) = (d ++ 1) in
    let h () : Lemma (requires (skip i a <: nat) == (skip i b <: nat)) (ensures False)
      = skip_injective i a b
    in
    Classical.move_requires h ()

(* --- parity_inject_diag: parity (inject σ' i i) == parity σ' --- *)

let rec parity_inject_diag (#n: pos) (sigma': permutation ((n - 1))) (i: fin n)
  : Lemma (ensures parity (inject sigma' i i) == parity sigma')
          (decreases (inversion_count sigma'))
  = let nm1 = (n - 1) in
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
      let tau_small = transposition nm1 d (((d ++ 1)) <: fin nm1) in
      inject_compose_diag sigma' tau_small i;
      inject_transposition_diag d (((d ++ 1)) <: fin nm1) i;
      let inj_tau = inject tau_small i i in
      let sa : fin n = skip i d in
      let sb : fin n = skip i (((d ++ 1)) <: fin nm1) in
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
            transposition_fwd_left nm1 d (((d ++ 1)) <: fin nm1)
          end else if (k <: nat) = (d ++ 1) then begin
            right_swap_fwd_at_i_plus_1 sigma' d;
            transposition_fwd_right nm1 d (((d ++ 1)) <: fin nm1)
          end else begin
            right_swap_fwd_at_other sigma' d k;
            transposition_fwd_other nm1 d (((d ++ 1)) <: fin nm1) k
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
      parity_transposition nm1 d (((d ++ 1)) <: fin nm1);
      perm_eq_sym_local comp sigma2;
      parity_perm_eq_invariant sigma2 comp;
      assert (parity comp == (parity sigma' = parity tau_small));
      assert (parity tau_small == false);
      assert (parity sigma2 == not (parity sigma'));
      assert (parity composed == (parity inj_s = parity inj_tau));
      assert (parity inj_tau == false);
      assert (parity inj_comp == parity composed);
      assert (parity inj_comp == parity inj_s2)

(* --- inject σ' i j ≡ compose (inject id i j) (inject σ' i i) --- *)

let inject_compose_decomp (#n: pos)
  (sigma': permutation ((n - 1))) (i j: fin n)
  : Lemma (perm_eq (inject sigma' i j)
                   (compose (inject (identity ((n - 1))) i j)
                            (inject sigma' i i)))
  = let nm1 = (n - 1) in
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

(* --- inject id step: for i < j, inject id i j ≡ compose (transposition (j-1) j) (inject id i (j-1)) --- *)

let inject_id_step_down (#n: pos) (i j: fin n)
  : Lemma (requires (i <: nat) < (j <: nat))
          (ensures perm_eq (inject (identity ((n - 1))) i j)
                           (compose (transposition n ((j - 1) <: fin n) j)
                                    (inject (identity ((n - 1))) i ((j - 1) <: fin n))))
  = let nm1 = (n - 1) in
    let id_perm = identity nm1 in
    let jm1 : fin n = (j - 1) in
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
          if (u <: nat) < ((j - 1)) then begin
            skip_lt j u;
            skip_lt jm1 u;
            assert ((val_j <: nat) == (u <: nat));
            assert ((val_jm1 <: nat) == (u <: nat));
            transposition_fwd_other n jm1 j val_jm1
          end else if (u <: nat) = (j - 1) then begin
            skip_lt j u;
            skip_ge jm1 u;
            assert ((val_j <: nat) == (u <: nat));
            assert ((val_jm1 <: nat) == (u ++ 1));
            assert ((val_j <: nat) == (j - 1));
            assert ((val_jm1 <: nat) == (j <: nat));
            transposition_fwd_right n jm1 j
          end else begin
            skip_ge j u;
            skip_ge jm1 u;
            assert ((val_j <: nat) == (u ++ 1));
            assert ((val_jm1 <: nat) == (u ++ 1));
            transposition_fwd_other n jm1 j val_jm1
          end
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj_j comp pointwise

(* --- inject id step: for j < i, inject id i j ≡ compose (transposition j (j+1)) (inject id i (j+1)) --- *)

let inject_id_step_up (#n: pos) (i j: fin n)
  : Lemma (requires (j <: nat) < (i <: nat))
          (ensures perm_eq (inject (identity ((n - 1))) i j)
                           (compose (transposition n j ((j ++ 1) <: fin n))
                                    (inject (identity ((n - 1))) i ((j ++ 1) <: fin n))))
  = let nm1 = (n - 1) in
    let id_perm = identity nm1 in
    let jp1 : fin n = (j ++ 1) in
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
            assert ((val_j <: nat) == (u ++ 1));
            assert ((val_jp1 <: nat) == (u <: nat));
            assert ((val_j <: nat) == (jp1 <: nat));
            assert ((val_jp1 <: nat) == (j <: nat));
            transposition_fwd_left n j jp1
          end else begin
            skip_ge j u;
            skip_ge jp1 u;
            assert ((val_j <: nat) == (u ++ 1));
            assert ((val_jp1 <: nat) == (u ++ 1));
            transposition_fwd_other n j jp1 val_jp1
          end
        end
    in
    Classical.forall_intro pointwise;
    perm_eq_intro inj_j comp pointwise

(* --- Boolean arithmetic helper --- *)
private let bool_not_even_succ (a b: nat)
  : Lemma (not (((a ++ b)) % 2 = 0) == (((a ++ ((b ++ 1)))) % 2 = 0))
  = ()

private let bool_not_even_pred (a b: nat)
  : Lemma (requires b > 0)
          (ensures not (((a ++ b)) % 2 = 0) == (((a ++ ((b - 1)))) % 2 = 0))
  = ()

(* --- parity_inject_id: parity (inject id i j) == ((i+j) % 2 = 0) --- *)

let rec parity_inject_id (#n: pos) (i j: fin n)
  : Lemma (ensures parity (inject (identity ((n - 1))) i j) ==
                   ((((i <: nat) ++ (j <: nat))) % 2 = 0))
          (decreases (if (j <: nat) >= (i <: nat) then ((j <: nat) - (i <: nat)) else ((i <: nat) - (j <: nat))))
  = let nm1 = (n - 1) in
    let id_perm = identity nm1 in
    if (j <: nat) = (i <: nat) then begin
      inject_id_is_identity i;
      parity_perm_eq_invariant (inject id_perm i j) (identity n);
      parity_identity n
    end else if (j <: nat) > (i <: nat) then begin
      let jm1 : fin n = (j - 1) in
      inject_id_step_down i j;
      let tau = transposition n jm1 j in
      let inj_jm1 = inject id_perm i jm1 in
      let comp = compose tau inj_jm1 in
      parity_perm_eq_invariant (inject id_perm i j) comp;
      sign_homomorphism tau inj_jm1;
      parity_transposition n jm1 j;
      assert (parity tau == false);
      parity_inject_id i jm1;
      assert (parity inj_jm1 == ((((i <: nat) ++ (jm1 <: nat))) % 2 = 0));
      assert (parity comp == (parity tau = parity inj_jm1));
      assert (parity comp == (false = parity inj_jm1));
      assert (parity comp == not (parity inj_jm1));
      bool_not_even_pred (i <: nat) (j <: nat)
    end else begin
      let jp1 : fin n = (j ++ 1) in
      inject_id_step_up i j;
      let tau = transposition n j jp1 in
      let inj_jp1 = inject id_perm i jp1 in
      let comp = compose tau inj_jp1 in
      parity_perm_eq_invariant (inject id_perm i j) comp;
      sign_homomorphism tau inj_jp1;
      parity_transposition n j jp1;
      assert (parity tau == false);
      parity_inject_id i jp1;
      assert (parity inj_jp1 == ((((i <: nat) ++ (jp1 <: nat))) % 2 = 0));
      assert (parity comp == not (parity inj_jp1));
      bool_not_even_succ (i <: nat) (j <: nat)
    end

(* --- MAIN: parity_inject --- *)

let parity_inject (#n: pos) (sigma': permutation ((n - 1)))
                  (i j: fin n)
  : Lemma (parity (inject sigma' i j) ==
           (parity sigma' = ((((i <: nat) ++ (j <: nat))) % 2 = 0)))
  = let nm1 = (n - 1) in
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
    assert (parity inj_id == ((((i <: nat) ++ (j <: nat))) % 2 = 0));
    assert (parity inj_diag == parity sigma')

(* ====================================================================== *)
(*  inject preserves/reflects perm_eq                                     *)
(* ====================================================================== *)

let inject_preserves_perm_eq (#n: pos)
  (sp1 sp2: permutation ((n - 1))) (i j: fin n)
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

(* inject reflects perm_eq *)

let inject_reflects_perm_eq (#n: pos)
  (sp1 sp2: permutation ((n - 1))) (i j: fin n)
  : Lemma (requires perm_eq (inject sp1 i j) (inject sp2 i j))
          (ensures perm_eq sp1 sp2)
  = let aux (a: fin ((n - 1)))
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

(* respects_perm_eq transfers through inject *)

let respects_perm_eq_inject (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  : Lemma (requires respects_perm_eq f)
          (ensures respects_perm_eq (fun s' -> f (inject s' i j)))
  = let g : permutation ((n - 1)) -> t
      = fun s' -> f (inject s' i j) in
    let aux (sp1 sp2: permutation ((n - 1)))
      : Lemma (perm_eq sp1 sp2 ==> g sp1 = g sp2)
      = if perm_eq sp1 sp2 then begin
          inject_preserves_perm_eq sp1 sp2 i j;
          respects_perm_eq_elim f (inject sp1 i j) (inject sp2 i j)
        end
    in Classical.forall_intro_2 aux;
    respects_perm_eq_intro g (fun _ _ -> ())

(* ====================================================================== *)
(*  Fiber list: partition S_n by the image of i.                          *)
(* ====================================================================== *)

(* If perm_eq p (inject sp i j), then p.fwd i == j *)

let perm_eq_inject_fwd_i (#n: pos) (p: permutation n)
  (sp: permutation ((n - 1))) (i j: fin n)
  : Lemma (requires perm_eq p (inject sp i j))
          (ensures (p.fwd i <: nat) == (j <: nat))
  = inject_fwd_at_i sp i j;
    perm_eq_elim p (inject sp i j) i

(* If p.fwd i ≠ j, then perm_eq p (inject sp i j) is false. *)

let perm_eq_inject_false (#n: pos) (p: permutation n)
  (sp: permutation ((n - 1))) (i j: fin n)
  : Lemma (requires (p.fwd i <: nat) <> (j <: nat))
          (ensures perm_eq p (inject sp i j) == false)
  = inject_fwd_at_i sp i j;
    if perm_eq p (inject sp i j) then
      perm_eq_elim p (inject sp i j) i
    else ()

(* If p.fwd i == j, then perm_eq p (inject sp i j) ==
   perm_eq (project p i) sp. *)

let perm_eq_inject_match (#n: pos) (p: permutation n)
  (sp: permutation ((n - 1))) (i j: fin n)
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
      let aux2 (a: fin ((n - 1))) : Lemma (pp.fwd a == sp.fwd a)
        = perm_eq_elim pp sp a
      in Classical.forall_intro aux2;
      perm_eq_intro pp sp aux2
    end else begin
      if perm_eq pp sp then begin
        let aux_eq (a: fin ((n - 1))) : Lemma (pp.fwd a == sp.fwd a)
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

(* Build the inject-image list directly, avoiding L.map to help Z3. *)
let rec fiber_list (#n: pos) (i j: fin n)
  (xs: list (permutation ((n - 1))))
  : Tot (list (permutation n)) (decreases xs)
  = match xs with
    | [] -> []
    | hd :: tl -> inject hd i j :: fiber_list i j tl

(* Named wrapper for inject with i,j fixed — avoids anonymous lambda in L.map. *)
let inject_at (#n: pos) (i j: fin n) (sp: permutation ((n - 1)))
  : permutation n
  = inject sp i j

(* fiber_list is the same as L.map (inject_at i j). *)
let rec fiber_list_eq_map (#n: pos) (i j: fin n)
  (xs: list (permutation ((n - 1))))
  : Lemma (ensures fiber_list i j xs == L.map (inject_at i j) xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: tl -> fiber_list_eq_map i j tl

(* Counting perm_eq matches in fiber_list: case p.fwd i ≠ j. *)

let rec fiber_list_count_ne (#n: pos) (p: permutation n)
  (i j: fin n) (xs: list (permutation ((n - 1))))
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

(* Counting perm_eq matches in fiber_list: case p.fwd i == j. *)

let rec fiber_list_count_eq (#n: pos) (p: permutation n)
  (i j: fin n) (xs: list (permutation ((n - 1))))
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

(* Each fiber has count 0 or 1. *)

let fiber_count (#n: pos) (p: permutation n) (i j: fin n)
  : Lemma (perm_eq_count p (fiber_list i j (all_permutations ((n - 1)))) ==
           (if (p.fwd i <: nat) = (j <: nat) then 1 else 0))
  = let nm1 = (n - 1) in
    if (p.fwd i <: nat) = (j <: nat) then begin
      fiber_list_count_eq p i j (all_permutations nm1);
      all_permutations_count_one nm1 (project p i)
    end else
      fiber_list_count_ne p i j (all_permutations nm1)

(* Build concatenated fibers from j_lo up to n-1. *)
let rec concat_fibers_from (#n: pos) (i: fin n) (j_lo: nat{j_lo <= n})
  : Tot (list (permutation n)) (decreases ((n - j_lo)))
  = if j_lo >= n then []
    else L.append
           (fiber_list i j_lo (all_permutations ((n - 1))))
           (concat_fibers_from i ((j_lo ++ 1)))

let concat_fibers (#n: pos) (i: fin n) : list (permutation n)
  = concat_fibers_from i 0

(* Count in concatenated fibers equals 1 for every permutation. *)

let rec concat_fibers_from_count (#n: pos) (p: permutation n)
  (i: fin n) (j_lo: nat{j_lo <= n})
  : Lemma (ensures perm_eq_count p (concat_fibers_from i j_lo) ==
                   (if (p.fwd i <: nat) >= j_lo then 1 else 0))
          (decreases ((n - j_lo)))
  = if j_lo >= n then perm_eq_count_nil p
    else begin
      let fl = fiber_list i j_lo
                 (all_permutations ((n - 1))) in
      let rest = concat_fibers_from i ((j_lo ++ 1)) in
      perm_eq_count_append p fl rest;
      fiber_count p i j_lo;
      concat_fibers_from_count p i ((j_lo ++ 1))
    end

let concat_fibers_count_one (#n: pos) (p: permutation n) (i: fin n)
  : Lemma (perm_eq_count p (concat_fibers i) == 1)
  = concat_fibers_from_count p i 0

(* Named per-fiber function to avoid lambda-matching issues. *)
let per_fiber_fn (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  (sp: permutation ((n - 1))) : t
  = f (inject_at i j sp)

(* sum_list (map f (fiber_list i j xs)) = sum_list (map (per_fiber_fn f i j) xs). *)

let fiber_list_sum (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  (xs: list (permutation ((n - 1))))
  : Lemma (ensures sum_list (L.map f (fiber_list i j xs)) =
                   sum_list (L.map (per_fiber_fn f i j) xs))
  = elim_equatable_laws t ();
    fiber_list_eq_map i j xs;
    map_map_eq (inject_at i j) f xs;
    let pfn = per_fiber_fn f i j in
    let g = fcomp f (inject_at i j) in
    let eq_pw (sp: permutation ((n - 1)))
      : Lemma (requires L.memP sp xs) (ensures pfn sp = g sp)
      = fcomp_unfold f (inject_at i j) sp
    in Classical.forall_intro (Classical.move_requires eq_pw);
    sum_list_map_congruence pfn g xs (fun _ -> ())

(* Connect sum_list of fiber_list to sum_over_perms via per_fiber_fn. *)

let fiber_list_to_sum_over_perms (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i j: fin n)
  : Lemma (requires respects_perm_eq f)
          (ensures sum_list (L.map f (fiber_list i j (all_permutations ((n - 1))))) =
                   sum_over_perms ((n - 1)) (per_fiber_fn f i j))
  = let nm1 = (n - 1) in
    let g = per_fiber_fn f i j in
    fiber_list_sum f i j (all_permutations nm1);
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

(* Sum over concat_fibers_from decomposes into sum_range of sum_over_perms of fibers. *)

let rec concat_fibers_from_sum (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i: fin n)
  (j_lo: nat{j_lo <= n})
  : Lemma (requires respects_perm_eq f)
          (ensures sum_list (L.map f (concat_fibers_from i j_lo)) =
                   sum_range
                     (fun k -> if k < n then sum_over_perms ((n - 1)) (per_fiber_fn f i k) else zero)
                     j_lo n)
          (decreases ((n - j_lo)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let g (k: nat) : t = if k < n then sum_over_perms ((n - 1)) (per_fiber_fn f i k) else zero in
    if j_lo >= n then begin
      sum_list_nil #t #(cr.cr_r.r_add);
      sum_range_empty g j_lo n
    end else begin
      let j : fin n = j_lo in
      let nm1 = (n - 1) in
      let fl = fiber_list i j (all_permutations nm1) in
      let rest = concat_fibers_from i ((j_lo ++ 1)) in
      L.map_append f fl rest;
      sum_list_append (L.map f fl) (L.map f rest);
      fiber_list_to_sum_over_perms f i j;
      concat_fibers_from_sum f i ((j_lo ++ 1));
      sum_range_unfold_left g j_lo n;
      let a = sum_list (L.map f fl) in
      let b = sum_over_perms nm1 (per_fiber_fn f i j) in
      let c = sum_list (L.map f rest) in
      let d = sum_range g ((j_lo ++ 1)) n in
      add_congruence a c b d;
      transitivity (sum_list (L.map f (concat_fibers_from i j_lo)))
                   (a `( + )` c)
                   (sum_range g j_lo n)
    end

(* fin_sum form. *)

let concat_fibers_sum_eq_fin_sum (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i: fin n)
  : Lemma (requires respects_perm_eq f)
          (ensures sum_list (L.map f (concat_fibers i)) =
                   fin_sum (fun (j: fin n) ->
                     sum_over_perms ((n - 1)) (per_fiber_fn f i j)))
  = concat_fibers_from_sum f i 0;
    assert_norm (fin_sum (fun (j: fin n) ->
              sum_over_perms ((n - 1)) (per_fiber_fn f i j))
            == sum_range
              (fun k -> if k < n then sum_over_perms ((n - 1)) (per_fiber_fn f i k) else zero)
              0 n)

(* === Main theorem: sum_over_perms_partition === *)

let sum_over_perms_partition (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (i: fin n) (f: permutation n -> t)
  : Lemma (requires respects_perm_eq f)
          (ensures sum_over_perms n f =
                   fin_sum (fun (j: fin n) ->
                     sum_over_perms ((n - 1)) (per_fiber_fn f i j)))
  = let count_one (p: permutation n)
      : Lemma (perm_eq_count p (concat_fibers i) == 1)
      = concat_fibers_count_one p i
    in Classical.forall_intro count_one;
    sum_over_perms_via_count_one_list f (concat_fibers i) (fun _ -> ());
    concat_fibers_sum_eq_fin_sum f i;
    transitivity (sum_over_perms n f)
                 (sum_list (L.map f (concat_fibers i)))
                 (fin_sum (fun (j: fin n) -> sum_over_perms ((n - 1)) (per_fiber_fn f i j)))

(* Partition targeting a named function g, bypassing anonymous-lambda issues. *)

private let rec concat_fibers_from_sum_target (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (f: permutation n -> t) (i: fin n) (g: fin n -> t)
  (j_lo: nat{j_lo <= n})
  : Lemma (requires respects_perm_eq f /\
                    (forall (j: fin n). sum_over_perms ((n - 1)) (per_fiber_fn f i j) = g j))
          (ensures sum_list (L.map f (concat_fibers_from i j_lo)) =
                   sum_range
                     (fun k -> if k < n then g k else zero)
                     j_lo n)
          (decreases ((n - j_lo)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let h (k: nat) : t = if k < n then g k else zero in
    if j_lo >= n then begin
      sum_list_nil #t #(cr.cr_r.r_add);
      sum_range_empty h j_lo n
    end else begin
      let j : fin n = j_lo in
      let nm1 = (n - 1) in
      let fl = fiber_list i j (all_permutations nm1) in
      let rest = concat_fibers_from i ((j_lo ++ 1)) in
      L.map_append f fl rest;
      sum_list_append (L.map f fl) (L.map f rest);
      fiber_list_to_sum_over_perms f i j;
      concat_fibers_from_sum_target f i g ((j_lo ++ 1));
      sum_range_unfold_left h j_lo n;
      let a = sum_list (L.map f fl) in
      let b = sum_over_perms nm1 (per_fiber_fn f i j) in
      let c = sum_list (L.map f rest) in
      let d = sum_range h ((j_lo ++ 1)) n in
      add_congruence a c (h j_lo) d;
      transitivity (sum_list (L.map f (concat_fibers_from i j_lo)))
                   (a `( + )` c)
                   (sum_range h j_lo n)
    end

let sum_over_perms_partition_target (#t: Type) {| cr: commutative_ring t |}
  (#n: pos) (i: fin n) (f: permutation n -> t) (g: fin n -> t)
  : Lemma (requires respects_perm_eq f /\
                    (forall (j: fin n). sum_over_perms ((n - 1)) (per_fiber_fn f i j) = g j))
          (ensures sum_over_perms n f = fin_sum g)
  = let count_one (p: permutation n)
      : Lemma (perm_eq_count p (concat_fibers i) == 1)
      = concat_fibers_count_one p i
    in Classical.forall_intro count_one;
    sum_over_perms_via_count_one_list f (concat_fibers i) (fun _ -> ());
    concat_fibers_from_sum_target f i g 0;
    assert_norm (fin_sum g
            == sum_range
              (fun k -> if k < n then g k else zero)
              0 n);
    transitivity (sum_over_perms n f)
                 (sum_list (L.map f (concat_fibers i)))
                 (fin_sum g)

(* ====================================================================== *)
(*  P3: perm_product factorization through inject.                        *)
(*                                                                        *)
(*  perm_product m (inject sigma' i j) = m i j * perm_product (minor m i j) sigma'*)
(* ====================================================================== *)

(* prod_range offset lemma: if g a == f (a+lo) pointwise, then
   prod_range f lo hi = prod_range g 0 (hi-lo). *)

private let rec prod_range_offset_lem
  (#t: Type) {| cr: commutative_ring t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma (requires lo <= hi /\
                     (forall (a: nat). 0 <= a /\ a < (hi - lo) ==>
                        g a = f ((a ++ lo))))
          (ensures prod_range f lo hi = prod_range g 0 ((hi - lo)))
          (decreases ((hi - lo)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let len = (hi - lo) in
    if lo >= hi then begin
      prod_range_empty f lo hi;
      prod_range_empty g 0 0
    end else begin
      prod_range_unfold_left f lo hi;
      prod_range_unfold_left g 0 len;
      assert (g 0 = f ((0 ++ lo)));
      assert ((0 ++ lo) == lo);
      let lo' = (lo ++ 1) in
      let len' = (len - 1) in
      let g' (a: nat) : t = g ((a ++ 1)) in
      let h (a: nat) : Lemma (requires 0 <= a /\ a < len')
                              (ensures g' a = f ((a ++ lo')))
        = assert (g ((a ++ 1)) = f ((((a ++ 1)) ++ lo)));
          assert ((((a ++ 1)) ++ lo) == (a ++ lo'))
      in
      Classical.forall_intro (Classical.move_requires h);
      prod_range_offset_lem f g' lo' hi;
      prod_range_offset_lem g g' ((0 ++ 1)) len;
      assert ((len - ((0 ++ 1))) == len');
      mul_congruence (g 0) (prod_range g ((0 ++ 1)) len)
                     (g 0) (prod_range g' 0 len');
      symmetry (prod_range g 0 len)
               (g 0 * prod_range g ((0 ++ 1)) len);
      transitivity (prod_range g 0 len)
                   (g 0 * prod_range g ((0 ++ 1)) len)
                   (g 0 * prod_range g' 0 len');
      mul_congruence (g 0) (prod_range g' 0 len')
                     (g 0) (prod_range f lo' hi);
      transitivity (prod_range g 0 len)
                   (g 0 * prod_range g' 0 len')
                   (g 0 * prod_range f lo' hi);
      mul_congruence (g 0) (prod_range f lo' hi)
                     (f lo) (prod_range f lo' hi);
      transitivity (prod_range g 0 len)
                   (g 0 * prod_range f lo' hi)
                   (f lo * prod_range f lo' hi);
      transitivity (prod_range g 0 len)
                   (f lo * prod_range f lo' hi)
                   (prod_range f lo hi)
    end

(* Bridge lemma: prod_range of a body function = perm_product,
   given pointwise equality on [0, n). *)

private let prod_range_eq_perm_product (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (p: permutation n) (body: nat -> t)
  : Lemma (requires forall (k: nat). 0 <= k /\ k < n ==> body k = m k (p.fwd k))
          (ensures prod_range body 0 n = perm_product m p)
  = elim_equatable_laws t ();
    let pp_body (k: nat) : t =
      if k < n then m k (p.fwd k) else one in
    let pw (k: nat) : Lemma (0 <= k /\ k < n ==> body k = pp_body k)
      = if k >= 0 && k < n then () in
    Classical.forall_intro pw;
    prod_range_congruence body pp_body 0 n (fun _ -> ());
    perm_product_unfold m p

let perm_product_inject_factor
  (#t: Type) {| cr: commutative_ring t |} (#n: pos{ n > 1 })
  (m: square_matrix t n) (sigma': permutation ((n - 1))) (i j: fin n)
  : Lemma (perm_product m (inject sigma' i j)
           = m i j * perm_product (minor m i j) sigma')
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let nm1 = (n - 1) in
    let ip1 = ((i <: nat) ++ 1) in
    let sigma = inject sigma' i j in
    perm_product_unfold m sigma;
    perm_product_unfold (minor m i j) sigma';
    let body_big (k: nat) : t =
      if k < n then m k (sigma.fwd k) else one in
    let body_small (a: nat) : t =
      if a < nm1
      then (minor m i j) a (sigma'.fwd a)
      else one in
    prod_range_shape_at body_big 0 n (i <: nat);
    inject_fwd_at_i sigma' i j;
    assert (body_big (i <: nat) == m i j);
    let h_left (k: nat) : Lemma (requires 0 <= k /\ k < (i <: nat))
                                 (ensures body_big k = body_small k)
      = let kf : fin n = k in
        inject_fwd_off sigma' i j kf;
        let a : fin nm1 = unskip i kf in
        assert ((a <: nat) == (k <: nat));
        minor_at m i j a (sigma'.fwd a);
        skip_lt i a
    in
    Classical.forall_intro (Classical.move_requires h_left);
    prod_range_congruence body_big body_small 0 (i <: nat) (fun _ -> ());
    let shifted_big (a: nat) : t = body_big ((a ++ ip1)) in
    let shifted_small (a: nat) : t = body_small ((a ++ (i <: nat))) in
    let len = (nm1 - (i <: nat)) in
    let h_right (a: nat) : Lemma (requires 0 <= a /\ a < len)
                                  (ensures shifted_big a = shifted_small a)
      = let k : nat = (a ++ ip1) in
        let kf : fin n = k in
        inject_fwd_off sigma' i j kf;
        let u : fin nm1 = unskip i kf in
        assert ((u <: nat) == (k - 1));
        assert ((u <: nat) == (a ++ (i <: nat)));
        minor_at m i j u (sigma'.fwd u);
        skip_ge i u;
        assert ((skip i u <: nat) == (u ++ 1));
        assert ((skip i u <: nat) == k)
    in
    Classical.forall_intro (Classical.move_requires h_right);
    prod_range_congruence shifted_big shifted_small 0 len (fun _ -> ());
    prod_range_offset_lem body_big shifted_big ip1 n;
    prod_range_offset_lem body_small shifted_small (i <: nat) nm1;
    assert ((n - ip1) == len);
    assert ((nm1 - (i <: nat)) == len);
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
    mul_congruence (m i j) rp (m i j) srp;
    mul_congruence lp (m i j * rp) slp (m i j * srp);
    mul_associativity slp (m i j) srp;
    mul_commutativity slp (m i j);
    mul_congruence (slp * m i j) srp (m i j * slp) srp;
    mul_associativity (m i j) slp srp;
    transitivity (slp * (m i j * srp))
                 ((slp * m i j) * srp)
                 ((m i j * slp) * srp);
    transitivity (slp * (m i j * srp))
                 ((m i j * slp) * srp)
                 (m i j * (slp * srp));
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
    prod_range_eq_perm_product m sigma body_big;
    prod_range_eq_perm_product (minor m i j) sigma' body_small;
    mul_congruence (m i j) (prod_range body_small 0 nm1) (m i j) (perm_product (minor m i j) sigma');
    transitivity (prod_range body_big 0 n)
                 (m i j * prod_range body_small 0 nm1)
                 (m i j * perm_product (minor m i j) sigma');
    transitivity (perm_product m sigma)
                 (prod_range body_big 0 n)
                 (m i j * perm_product (minor m i j) sigma')

(* ====================================================================== *)
(*  P4 helper: leibniz_inject_factor                                      *)
(*                                                                        *)
(*  leibniz_term m (inject sigma' i j)                                    *)
(*    = minus_one_pow(i+j) * m i j * leibniz_term (minor m i j) sigma'    *)
(* ====================================================================== *)

(* minus_one_pow squared = one *)

private let minus_one_pow_square (#t: Type) {| cr: commutative_ring t |} (k: nat)
  : Lemma (minus_one_pow #t k * minus_one_pow #t k = one)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if Prims.op_Modulus k 2 = 0 then begin
      minus_one_pow_even #t #cr k;
      one_mul_x (one #t)
    end else begin
      minus_one_pow_odd #t #cr k;
      let acg : add_comm_group t = acg_of_ring_local t cr.cr_r in
      ring_neg_x_is_minus_one_times_x (-(one #t));
      double_negation_lemma (one #t);
      transitivity ((-(one #t)) * (-(one #t)))
                   (-(-(one #t)))
                   (one #t)
    end

(* Combine P1 and P3 into the signed factorization *)

let leibniz_inject_factor
  (#t: Type) {| cr: commutative_ring t |} (#n: pos{ n > 1 })
  (m: square_matrix t n) (sigma': permutation ((n - 1))) (i j: fin n)
  : Lemma (leibniz_term m (inject sigma' i j)
           = minus_one_pow #t #cr (((i <: nat) ++ (j <: nat)))
             * m i j
             * leibniz_term (minor m i j) sigma')
  = let r : ring t = cr.cr_r in
    let acg : add_comm_group t = acg_of_ring_local t cr.cr_r in
    elim_equatable_laws t ();
    trans_for_calc t ();
    let nm1 = (n - 1) in
    let sigma = inject sigma' i j in
    let ij = ((i <: nat) ++ (j <: nat)) in
    parity_inject sigma' i j;
    perm_product_inject_factor m sigma' i j;
    let pp = perm_product m sigma in
    let pp_min = perm_product (minor m i j) sigma' in
    assert (pp = m i j * pp_min);
    let lhs = leibniz_term m sigma in
    let sign_sp = parity sigma' in
    let ij_even = (Prims.op_Modulus ij 2 = 0) in
    let mop = minus_one_pow ij in
    if sign_sp then begin
      if ij_even then begin
        minus_one_pow_even #t #cr ij;
        assert (lhs == pp);
        assert (leibniz_term (minor m i j) sigma' == pp_min);
        mul_associativity mop (m i j) pp_min;
        mul_congruence mop (m i j * pp_min) (one) (m i j * pp_min);
        one_mul_x (m i j * pp_min);
        trans_lemma [ mop * m i j * pp_min;
                      mop * (m i j * pp_min);
                      one * (m i j * pp_min);
                      m i j * pp_min;
                      pp ]
      end else begin
        minus_one_pow_odd #t #cr ij;
        assert (lhs == -pp);
        assert (leibniz_term (minor m i j) sigma' == pp_min);
        mul_associativity mop (m i j) pp_min;
        mul_congruence mop (m i j * pp_min) (-(one)) (m i j * pp_min);
        ring_neg_x_is_minus_one_times_x (m i j * pp_min);
        neg_congruence_lem pp (m i j * pp_min);
        trans_lemma [ mop * m i j * pp_min;
                      mop * (m i j * pp_min);
                      (-(one)) * (m i j * pp_min);
                      -(m i j * pp_min);
                      -pp ]
      end
    end else begin
      if ij_even then begin
        minus_one_pow_even #t #cr ij;
        assert (lhs == -pp);
        assert (leibniz_term (minor m i j) sigma' == -pp_min);
        let lt_min = -pp_min in
        mul_associativity mop (m i j) lt_min;
        mul_congruence mop (m i j * lt_min) (one) (m i j * lt_min);
        one_mul_x (m i j * lt_min);
        trans_lemma [ mop * m i j * lt_min;
                      mop * (m i j * lt_min);
                      one * (m i j * lt_min);
                      m i j * lt_min ];
        ring_neg_xy_is_x_times_neg_y (m i j) pp_min;
        neg_congruence_lem pp (m i j * pp_min);
        trans_lemma [ mop * m i j * lt_min;
                      m i j * lt_min;
                      -(m i j * pp_min);
                      -pp ]
      end else begin
        minus_one_pow_odd #t #cr ij;
        assert (lhs == pp);
        assert (leibniz_term (minor m i j) sigma' == -pp_min);
        let lt_min = -pp_min in
        mul_associativity mop (m i j) lt_min;
        mul_congruence mop (m i j * lt_min) (-(one)) (m i j * lt_min);
        ring_neg_x_is_minus_one_times_x (m i j * lt_min);
        ring_neg_xy_is_x_times_neg_y (m i j) pp_min;
        neg_congruence_lem (m i j * lt_min) (-(m i j * pp_min));
        double_negation_lemma (m i j * pp_min);
        trans_lemma [ mop * m i j * lt_min;
                      mop * (m i j * lt_min);
                      (-(one)) * (m i j * lt_min);
                      -(m i j * lt_min) ];
        trans_lemma [ -(m i j * lt_min);
                      -(-(m i j * pp_min));
                      m i j * pp_min;
                      pp ];
        transitivity (mop * m i j * lt_min) (-(m i j * lt_min)) pp
      end
    end

(* ====================================================================== *)
(*  P4: det_laplace_row -- Laplace expansion along row i.                 *)
(*                                                                        *)
(*    det m = fin_sum (fun j -> (-1)^(i+j) * m(i,j) * det(minor m i j))  *)
(* ====================================================================== *)

(* Module-level cofactor function *)
(* cofactor_term defined in .fsti *)

(* Helper: the per-fiber sum equals the cofactor expansion term. *)

private let inner_sum_eq_cofactor
  (#t: Type) {| cr: commutative_ring t |} (#n: pos{ n > 1 })
  (m: square_matrix t n) (i j: fin n)
  : Lemma (
      sum_over_perms ((n - 1))
        (per_fiber_fn (leibniz_term m) i j)
      = minus_one_pow #t #cr (((i <: nat) ++ (j <: nat)))
        * m i j
        * det (minor m i j))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let nm1 = (n - 1) in
    let ij = ((i <: nat) ++ (j <: nat)) in
    let mop = minus_one_pow ij in
    let f = per_fiber_fn (leibniz_term m) i j in
    let g (sp: permutation nm1) : t
      = mop * m i j * leibniz_term (minor m i j) sp in
    let pw (sp: permutation nm1) : Lemma (f sp = g sp)
      = leibniz_inject_factor m sp i j
    in
    Classical.forall_intro pw;
    sum_over_perms_congruence nm1 f g (fun _ -> ());
    let c = mop * m i j in
    let h = leibniz_term (minor m i j) in
    let ch (sp: permutation nm1) : t = c * h sp in
    let pw2 (sp: permutation nm1) : Lemma (g sp = ch sp)
      = mul_associativity mop (m i j) (h sp)
    in
    Classical.forall_intro pw2;
    sum_over_perms_congruence nm1 g ch (fun _ -> ());
    sum_over_perms_mul_left_named nm1 c ch h (fun _ -> ());
    transitivity (sum_over_perms nm1 g)
                 (sum_over_perms nm1 ch)
                 (c * sum_over_perms nm1 h);
    transitivity (sum_over_perms nm1 f) (sum_over_perms nm1 g)
                 (c * sum_over_perms nm1 h);
    det_unfold (minor m i j);
    mul_congruence c (sum_over_perms nm1 h) c (det (minor m i j));
    transitivity (sum_over_perms nm1 f) (c * sum_over_perms nm1 h)
                 (c * det (minor m i j))

(* Main theorem: Laplace expansion along row i. *)

let det_laplace_row
  (#t: Type) {| cr: commutative_ring t |}
  (#n: pos{ n > 1 }) (m: square_matrix t n) (i: fin n)
  : Lemma (det m =
           fin_sum (cofactor_term m i))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    leibniz_term_respects_perm_eq m;
    let pw (j: fin n) : Lemma (
      sum_over_perms ((n - 1))
        (per_fiber_fn (leibniz_term m) i j)
      = cofactor_term m i j)
      = inner_sum_eq_cofactor m i j
    in
    Classical.forall_intro pw;
    sum_over_perms_partition_target
      i (leibniz_term m) (cofactor_term m i);
    det_unfold m;
    assert_norm (fin_sum (cofactor_term m i)
            == sum_range
              (fun k -> if k < n then (cofactor_term m i) k else zero)
              0 n);
    transitivity (det m)
                 (sum_over_perms n (leibniz_term m))
                 (fin_sum (cofactor_term m i))


(* ================================================================== *)
(*  MERGED FROM Core.Matrix.MultiDistrib  (private scaffolding)        *)

(* ================================================================== *)

(* -------------------------------------------------------------------- *)
(*  Types: fin_map, nullary, extend_fn, all_fins_from/all_fins,           *)
(*  all_fns_to  -- inlined from legacy Function.Enum.                   *)
(* -------------------------------------------------------------------- *)

let fin_map (n m: nat) = fin n -> fin m

let nullary (m: nat) : fin_map 0 m =
  fun (i: fin 0) -> false_elim #(fin m) ()

let rec all_fins_from (m: nat) (k: nat{k <= m})
  : Tot (list (fin m)) (decreases ((m - k)))
  = if k = m then []
    else (k <: fin m) :: all_fins_from m ((k ++ 1))

let all_fins (m: nat) : list (fin m) = all_fins_from m 0

let extend_fn (#n #m: nat) (phi: fin_map n m) (j: fin m)
  : fin_map ((n ++ 1)) m
  = fun (i: fin ((n ++ 1))) ->
      if i = n then j
      else phi (i <: fin n)

let extend_to_all (#k #m: nat) (phi: fin_map k m)
  : list (fin_map ((k ++ 1)) m)
  = map (extend_fn phi) (all_fins m)

let all_fns_to_succ_list (#k m: nat) (xs: list (fin_map k m))
  : list (fin_map ((k ++ 1)) m)
  = concatMap (extend_to_all #k #m) xs

let rec all_fns_to (n m: nat) : Tot (list (fin_map n m)) (decreases n)
  = match n with
    | 0 -> [nullary m]
    | _ ->
        all_fns_to_succ_list m
          (all_fns_to ((n - 1)) m)

#push-options "--fuel 2 --ifuel 2 --z3rlimit 30"
let all_fns_to_succ_eq (k m: nat)
  : Lemma (all_fns_to ((k ++ 1)) m ==
           all_fns_to_succ_list m (all_fns_to k m))
  = ()
#pop-options

(* -------------------------------------------------------------------- *)
(*  sum_over_fns_to                                                     *)
(* -------------------------------------------------------------------- *)

let sum_over_fns_to
  (#t: Type) {| g: add_comm_group t |}
  (n m: nat) (f: fin_map n m -> t) : t
  = sum_list (map f (all_fns_to n m))

(* -------------------------------------------------------------------- *)
(*  sum_list over list append.                                          *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
let rec sum_list_append
  (#t: Type) {| g: add_comm_group t |}
  (xs ys: list t)
  : Lemma (ensures sum_list (append xs ys) = sum_list xs + sum_list ys)
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] ->
        sum_list_nil #t #g;
        zero_plus_x (sum_list ys)
    | x :: tl ->
        sum_list_append tl ys;
        sum_list_cons x (append tl ys);
        sum_list_cons x tl;
        g.add_congruence x (sum_list (append tl ys)) x (sum_list tl + sum_list ys);
        g.add_associativity x (sum_list tl) (sum_list ys)
#pop-options

(* -------------------------------------------------------------------- *)
(*  sum_list over concatMap.                                            *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
let rec sum_list_concatMap
  (#a #t: Type) {| g: add_comm_group t |}
  (f: a -> list t) (xs: list a)
  : Lemma (ensures sum_list (concatMap f xs)
                 = sum_list (map (fun (x:a) -> sum_list (f x)) xs))
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] ->
        sum_list_nil #t #g
    | x :: tl ->
        sum_list_concatMap f tl;
        sum_list_append (f x) (concatMap f tl);
        sum_list_cons (sum_list (f x)) (map (fun (y:a) -> sum_list (f y)) tl);
        g.add_congruence
          (sum_list (f x)) (sum_list (concatMap f tl))
          (sum_list (f x)) (sum_list (map (fun (y:a) -> sum_list (f y)) tl));
        transitivity
          (sum_list (concatMap f (x :: tl)))
          (sum_list (f x) + sum_list (concatMap f tl))
          (sum_list (f x) + sum_list (map (fun (y:a) -> sum_list (f y)) tl))
#pop-options

(* -------------------------------------------------------------------- *)
(*  map distributes over concatMap.                                     *)
(* -------------------------------------------------------------------- *)

let rec map_concatMap
  (#a #b #c: Type) (g: b -> c) (f: a -> list b) (xs: list a)
  : Lemma (ensures map g (concatMap f xs)
                 == concatMap (fun (x:a) -> map g (f x)) xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | x :: tl ->
        map_concatMap g f tl;
        L.map_append g (f x) (concatMap f tl)

(* -------------------------------------------------------------------- *)
(*  sum_list (map g (map h xs)) = sum_list (map (g . h) xs).            *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
let rec sum_list_map_compose
  (#a #b #t: Type) {| g: add_comm_group t |}
  (gf: b -> t) (h: a -> b) (xs: list a)
  : Lemma (ensures sum_list (map gf (map h xs))
                 = sum_list (map (fun (x:a) -> gf (h x)) xs))
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] -> sum_list_nil #t #g; reflexivity (zero #t)
    | x :: tl ->
        sum_list_map_compose gf h tl;
        sum_list_cons (gf (h x)) (map gf (map h tl));
        sum_list_cons (gf (h x)) (map (fun (y:a) -> gf (h y)) tl);
        g.add_congruence
          (gf (h x)) (sum_list (map gf (map h tl)))
          (gf (h x)) (sum_list (map (fun (y:a) -> gf (h y)) tl))
#pop-options

(* -------------------------------------------------------------------- *)
(*  Bridge: sum_list (map f (all_fins m)) = fin_sum f.                  *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec sum_list_map_all_fins_from_eq_sum_range
  (#t: Type) {| g: add_comm_group t |}
  (m: nat) (k: nat{k <= m}) (f: fin m -> t)
  : Lemma (ensures
            sum_list (map f (all_fins_from m k))
          = sum_range (fun (j: nat) -> if j < m then f (j <: fin m) else zero) k m)
          (decreases ((m - k)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if k = m then begin
      sum_list_nil #t #g;
      sum_range_empty
        (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k m
    end else begin
      let k1 = (k ++ 1) in
      sum_list_map_all_fins_from_eq_sum_range m k1 f;
      sum_list_cons (f (k <: fin m)) (map f (all_fins_from m k1));
      sum_range_unfold_left
        (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k m;
      g.add_congruence
        (f (k <: fin m))
        (sum_list (map f (all_fins_from m k1)))
        (f (k <: fin m))
        (sum_range (fun (j: nat) -> if j < m then f (j <: fin m) else zero #t) k1 m)
    end
#pop-options

let sum_list_map_all_fins_eq_fin_sum
  (#t: Type) {| g: add_comm_group t |}
  (m: nat) (f: fin m -> t)
  : Lemma (sum_list (map f (all_fins m)) = fin_sum f)
  = sum_list_map_all_fins_from_eq_sum_range m 0 f

(* -------------------------------------------------------------------- *)
(*  Split-head for sum_over_fns_to.                                     *)
(* -------------------------------------------------------------------- *)

unfold let extend_fin_sum
  (#t: Type) {| g: add_comm_group t |}
  (n m: nat) (gg: fin_map ((n ++ 1)) m -> t) (phi: fin_map n m) : t =
  fin_sum (fun (k: fin m) -> gg (extend_fn phi k))

let extend_fin_sum_def
  (#t: Type) {| g: add_comm_group t |}
  (n m: nat) (gg: fin_map ((n ++ 1)) m -> t) (phi: fin_map n m)
  : Lemma (extend_fin_sum n m gg phi
           == fin_sum (fun (k: fin m) -> gg (extend_fn phi k))) = ()

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let sum_over_fns_to_split_head
  (#t: Type) {| g: add_comm_group t |}
  (n m: nat) (gg: fin_map ((n ++ 1)) m -> t)
  : Lemma (sum_over_fns_to ((n ++ 1)) m gg
         = sum_over_fns_to n m (extend_fin_sum n m gg))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let n1 = (n ++ 1) in
    all_fns_to_succ_eq n m;
    map_concatMap gg
      (extend_to_all #n #m)
      (all_fns_to n m);
    sum_list_concatMap
      (fun (phi: fin_map n m) ->
         map gg (extend_to_all phi))
      (all_fns_to n m);
    let h' (phi: fin_map n m) : t =
      fin_sum (fun (k: fin m) -> gg (extend_fn phi k))
    in
    let pf (phi: fin_map n m)
      : Lemma
        (sum_list (map gg (extend_to_all phi))
         = h' phi)
      = assert (extend_to_all phi ==
                map (extend_fn phi) (all_fins m))
          by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
        sum_list_map_compose gg (extend_fn phi) (all_fins m);
        sum_list_map_all_fins_eq_fin_sum m (fun (j: fin m) -> gg (extend_fn phi j));
        transitivity
          (sum_list (map gg (extend_to_all phi)))
          (sum_list (map (fun (j: fin m) -> gg (extend_fn phi j)) (all_fins m)))
          (h' phi)
    in
    Classical.forall_intro pf;
    sum_list_map_congruence
      (fun (phi: fin_map n m) ->
         sum_list (map gg (extend_to_all phi)))
      h'
      (all_fns_to n m) (fun _ -> ());
    let cong_h_ext (phi: fin_map n m) : Lemma (h' phi = extend_fin_sum n m gg phi)
      = extend_fin_sum_def n m gg phi;
        reflexivity (h' phi) in
    Classical.forall_intro cong_h_ext;
    sum_list_map_congruence h' (extend_fin_sum n m gg) (all_fns_to n m) (fun _ -> ());
    transitivity
      (sum_over_fns_to n1 m gg)
      (sum_list (map h' (all_fns_to n m)))
      (sum_over_fns_to n m (extend_fin_sum n m gg))
#pop-options

(* -------------------------------------------------------------------- *)
(*  sum_list scalar multiplication on the right.                        *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
let rec sum_list_map_mul_right
  (#a:Type) (#t:Type) {| r: ring t |}
  (f: a -> t) (c: t) (xs: list a)
  : Lemma (ensures sum_list (map f xs) * c = sum_list (map (fun x -> f x * c) xs))
          (decreases xs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    match xs with
    | [] ->
        sum_list_nil #t #(acg_of_r t #r);
        zero_mul_x c
    | hx :: rest ->
        sum_list_map_mul_right f c rest;
        sum_list_cons (f hx) (map f rest);
        sum_list_cons (f hx * c) (map (fun x -> f x * c) rest);
        let h = f hx in
        let trest = sum_list (map f rest) in
        let crest = sum_list (map (fun x -> f x * c) rest) in
        r.right_distributivity c h trest;
        r.r_add.add_congruence (h * c) (trest * c) (h * c) crest;
        transitivity (sum_list (map f (hx :: rest)) * c)
                     ((h + trest) * c)
                     (h * c + trest * c);
        transitivity (sum_list (map f (hx :: rest)) * c)
                     (h * c + trest * c)
                     (h * c + crest)
#pop-options

(* -------------------------------------------------------------------- *)
(*  sum_over_fns_to scalar mul right.                                   *)
(* -------------------------------------------------------------------- *)

let sum_over_fns_to_mul_right
  (#t: Type) {| r: ring t |}
  (n m: nat) (f: fin_map n m -> t) (c: t)
  : Lemma (sum_over_fns_to n m f * c
         = sum_over_fns_to n m (fun (phi: fin_map n m) -> f phi * c))
  = sum_list_map_mul_right f c (all_fns_to n m)

(* -------------------------------------------------------------------- *)
(*  Pointwise inductive step: prod_range over extended function.        *)
(* -------------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let prod_range_extend_pointwise
  (#t: Type) {| r: ring t |}
  (n m: nat) (a: fin ((n ++ 1)) -> fin m -> t)
  (phi: fin_map n m) (k: fin m)
  : Lemma
    (prod_range (fun (i: nat) ->
       if i < (n ++ 1)
       then a (i <: fin ((n ++ 1)))
              ((extend_fn phi k) (i <: fin ((n ++ 1))))
       else one) 0 ((n ++ 1))
     = prod_range (fun (i: nat) ->
         if i < n
         then a (i <: fin ((n ++ 1))) (phi (i <: fin n))
         else one) 0 n
       * a (n <: fin ((n ++ 1))) k)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let body_full (i: nat) : t =
      if i < (n ++ 1)
      then a (i <: fin ((n ++ 1)))
             ((extend_fn phi k) (i <: fin ((n ++ 1))))
      else one in
    let body_short (i: nat) : t =
      if i < n
      then a (i <: fin ((n ++ 1))) (phi (i <: fin n))
      else one in
    prod_range_unfold_right body_full 0 ((n ++ 1));
    let cong (i: nat)
      : Lemma (0 <= i /\ i < n ==> body_full i = body_short i)
      = if 0 <= i && i < n then
          ()
    in
    Classical.forall_intro cong;
    prod_range_congruence body_full body_short 0 n (fun _ -> ());
    r.mul_congruence
      (prod_range body_full 0 n)
      (body_full n)
      (prod_range body_short 0 n)
      (a (n <: fin ((n ++ 1))) k);
    transitivity
      (prod_range body_full 0 ((n ++ 1)))
      (prod_range body_full 0 n * body_full n)
      (prod_range body_short 0 n * a (n <: fin ((n ++ 1))) k)
#pop-options

(* Helper: each phi maps to the sum over k of g_rhs(extend phi k). *)
#restart-solver
#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let per_phi_lemma
  (#t: Type) {| r: ring t |}
  (n_m1 m: nat) (a: fin ((n_m1 ++ 1)) -> fin m -> t)
  (phi: fin_map n_m1 m)
  : Lemma (
    prod_range (fun (i: nat) ->
        if i < n_m1 then a (i <: fin ((n_m1 ++ 1))) (phi (i <: fin n_m1)) else one) 0 n_m1
    * fin_sum (a (n_m1 <: fin ((n_m1 ++ 1))))
    = fin_sum (fun (k: fin m) ->
        prod_range (fun (i: nat) ->
          if i < (n_m1 ++ 1)
          then a (i <: fin ((n_m1 ++ 1)))
                 ((extend_fn phi k) (i <: fin ((n_m1 ++ 1))))
          else one) 0 ((n_m1 ++ 1))))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let g_ih = prod_range (fun (i: nat) ->
        if i < n_m1 then a (i <: fin ((n_m1 ++ 1))) (phi (i <: fin n_m1)) else one) 0 n_m1 in
    fin_sum_mul_left g_ih (a (n_m1 <: fin ((n_m1 ++ 1))));
    (* g_ih * fin_sum (a n_m1) = fin_sum (pointwise_mul (const g_ih) (a n_m1)) *)
    let pw_bridge (k: fin m) : Lemma
      (pointwise_mul (const g_ih) (a (n_m1 <: fin ((n_m1 ++ 1)))) k
       = g_ih * a (n_m1 <: fin ((n_m1 ++ 1))) k)
      = pointwise_mul_unfold (const g_ih) (a (n_m1 <: fin ((n_m1 ++ 1)))) k;
        const_unfold g_ih k;
        reflexivity (g_ih * a (n_m1 <: fin ((n_m1 ++ 1))) k) in
    fin_sum_congruence (pointwise_mul (const g_ih) (a (n_m1 <: fin ((n_m1 ++ 1)))))
                  (fun (k: fin m) -> g_ih * a (n_m1 <: fin ((n_m1 ++ 1))) k) pw_bridge;
    let pk (k: fin m) : Lemma (
        g_ih * a (n_m1 <: fin ((n_m1 ++ 1))) k =
        prod_range (fun (i: nat) ->
          if i < (n_m1 ++ 1)
          then a (i <: fin ((n_m1 ++ 1)))
                 ((extend_fn phi k) (i <: fin ((n_m1 ++ 1))))
          else one) 0 ((n_m1 ++ 1)))
      = prod_range_extend_pointwise n_m1 m a phi k
    in
    Classical.forall_intro pk;
    fin_sum_congruence #t #(acg_of_r t #r) #m
      (fun (k: fin m) -> g_ih * a (n_m1 <: fin ((n_m1 ++ 1))) k)
      (fun (k: fin m) -> prod_range (fun (i: nat) ->
          if i < (n_m1 ++ 1)
          then a (i <: fin ((n_m1 ++ 1)))
                 ((extend_fn phi k) (i <: fin ((n_m1 ++ 1))))
          else one) 0 ((n_m1 ++ 1))) (fun _ -> ());
    trans3
      (g_ih * fin_sum (a (n_m1 <: fin ((n_m1 ++ 1)))))
      (fin_sum (pointwise_mul (const g_ih) (a (n_m1 <: fin ((n_m1 ++ 1))))))
      (fin_sum (fun (k: fin m) -> g_ih * a (n_m1 <: fin ((n_m1 ++ 1))) k))
      (fin_sum (fun (k: fin m) -> prod_range (fun (i: nat) ->
          if i < (n_m1 ++ 1)
          then a (i <: fin ((n_m1 ++ 1)))
                 ((extend_fn phi k) (i <: fin ((n_m1 ++ 1))))
          else one) 0 ((n_m1 ++ 1))))
#pop-options

(* -------------------------------------------------------------------- *)
(*  Main theorem: prod_range_of_fin_sum.                                *)
(*                                                                       *)
(*    Pi_i (Sigma_k a i k) = Sigma_phi Pi_i (a i (phi i))                *)
(* -------------------------------------------------------------------- *)

#restart-solver
#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
let rec prod_range_of_fin_sum
  (#t: Type) {| r: ring t |}
  (n m: nat) (a: fin n -> fin m -> t)
  : Lemma
    (ensures
      prod_range (fun (i: nat) ->
        if i < n then fin_sum (a (i <: fin n)) else one) 0 n
    = sum_over_fns_to n m
        (fun (phi: fin_map n m) ->
          prod_range (fun (i: nat) ->
            if i < n then a (i <: fin n) (phi (i <: fin n)) else one) 0 n))
    (decreases n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if n = 0 then begin
     let inner_body (phi: fin_map n m) (i: nat) : t =
       if i < n then a (i <: fin n) (phi (i <: fin n)) else one in
     let inner_body_def (phi: fin_map n m) (i: nat) : Lemma (inner_body phi i ==
       (if i < n then a (i <: fin n) (phi (i <: fin n)) else one #t)) = () in
     Classical.forall_intro_2 inner_body_def;
     let g_rhs (phi: fin_map n m) : t =
       prod_range (inner_body phi) 0 n in
     let g_rhs_def (phi: fin_map n m) : Lemma (g_rhs phi ==
       prod_range (inner_body phi) 0 n) = () in
     Classical.forall_intro g_rhs_def;
     assert (all_fns_to 0 m == [nullary m]);
     sum_list_cons (g_rhs (nullary m)) [];
     sum_list_nil #t #(acg_of_r t #r);
     x_plus_zero (g_rhs (nullary m));
     assert (sum_over_fns_to n m g_rhs = g_rhs (nullary m));
     prod_range_empty (inner_body (nullary m)) 0 0;
     assert (g_rhs (nullary m) = one #t);
     prod_range_empty
       (fun (i: nat) -> if i < n then fin_sum (a (i <: fin n)) else one) 0 0;
     let lhs = prod_range (fun (i: nat) ->
       if i < n then fin_sum (a (i <: fin n)) else one) 0 n in
     assert (lhs = one #t);



     transitivity lhs (one #t) (sum_over_fns_to n m g_rhs);
     let pc_lambda (phi: fin_map n m) : t =
       prod_range (fun (i: nat) ->
         if i < n then a (i <: fin n) (phi (i <: fin n)) else one) 0 n in
     let pc_lambda_def (phi: fin_map n m) : Lemma (pc_lambda phi ==
       prod_range (fun (i: nat) ->
         if i < n then a (i <: fin n) (phi (i <: fin n)) else one) 0 n) = () in
     Classical.forall_intro pc_lambda_def;
     let cong_prod (phi: fin_map n m) : Lemma (g_rhs phi = pc_lambda phi)
       = let body2 (i: nat) : t =
           if i < n then a (i <: fin n) (phi (i <: fin n)) else one in
         let cong_i (i: nat) : Lemma (0 <= i /\ i < n ==> inner_body phi i = body2 i)
           = if 0 <= i && i < n then
               ()
         in
         Classical.forall_intro cong_i;
         prod_range_congruence (inner_body phi) body2 0 n (fun _ -> ())
     in
     Classical.forall_intro cong_prod;
     sum_list_map_congruence g_rhs pc_lambda (all_fns_to n m) (fun _ -> ());
     transitivity lhs
       (sum_over_fns_to n m g_rhs)
       (sum_over_fns_to n m pc_lambda)
    end else begin
      let n_m1 : nat = (n - 1) in
      assert ((n_m1 ++ 1) == n);
      [@@inline_let] let a' : fin n_m1 -> fin m -> t =
        fun (i: fin n_m1) (k: fin m) -> a (i <: fin n) k in
      prod_range_of_fin_sum n_m1 m a';
      [@@inline_let] let body_lhs (i: nat) : t =
        if i < n then fin_sum (a (i <: fin n)) else one in
      [@@inline_let] let body_ih_lhs (i: nat) : t =
        if i < n_m1 then fin_sum (a' (i <: fin n_m1)) else one #t in
      [@@inline_let] let g_rhs (phi: fin_map n m) : t =
        prod_range (fun (i: nat) ->
          if i < n then a (i <: fin n) (phi (i <: fin n)) else one #t) 0 n in
      [@@inline_let] let g_ih (phi: fin_map n_m1 m) : t =
        prod_range (fun (i: nat) ->
          if i < n_m1 then a' (i <: fin n_m1) (phi (i <: fin n_m1)) else one #t) 0 n_m1 in
      prod_range_unfold_right body_lhs 0 n;
      let s_n : t = fin_sum (a (n_m1 <: fin n)) in
      assert (body_lhs n_m1 == s_n);
      let cong_lhs (i: nat)
        : Lemma (0 <= i /\ i < n_m1 ==> body_lhs i = body_ih_lhs i)
        = if 0 <= i && i < n_m1 then begin
            let aux (k: fin m) : Lemma (a (i <: fin n) k = a' (i <: fin n_m1) k)
              = reflexivity (a (i <: fin n) k) in
            Classical.forall_intro aux;
            fin_sum_congruence (a (i <: fin n)) (a' (i <: fin n_m1)) (fun _ -> ())
          end
      in
      Classical.forall_intro cong_lhs;
      prod_range_congruence body_lhs body_ih_lhs 0 n_m1 (fun _ -> ());
      let sum_ih : t = sum_over_fns_to n_m1 m g_ih in
      let pr_n_m1 : t = prod_range body_lhs 0 n_m1 in
      let pr_ih   : t = prod_range body_ih_lhs 0 n_m1 in
      transitivity pr_n_m1 pr_ih sum_ih;

      r.mul_congruence pr_n_m1 s_n sum_ih s_n;
      sum_over_fns_to_mul_right n_m1 m g_ih s_n;
      let h1 (pp: fin_map n_m1 m) : t = g_ih pp * s_n in
      let g_step (pp: fin_map n_m1 m) : t =
        fin_sum (fun (k: fin m) -> g_rhs (extend_fn pp k)) in
      let per_phi (phi: fin_map n_m1 m)
        : Lemma (h1 phi = g_step phi)
        = let h1_def () : Lemma (h1 phi == g_ih phi * s_n) = () in
          h1_def ();
          fin_sum_mul_left (g_ih phi) (a (n_m1 <: fin n));
          (* g_ih phi * fin_sum (a (n_m1 ...)) = fin_sum (pointwise_mul (const (g_ih phi)) (a (n_m1 ...))) *)
          let pw_b (k: fin m) : Lemma
            (pointwise_mul (const (g_ih phi)) (a (n_m1 <: fin n)) k
             = g_ih phi * a (n_m1 <: fin n) k)
            = pointwise_mul_unfold (const (g_ih phi)) (a (n_m1 <: fin n)) k;
              const_unfold (g_ih phi) k;
              reflexivity (g_ih phi * a (n_m1 <: fin n) k) in
          fin_sum_congruence
            (pointwise_mul (const (g_ih phi)) (a (n_m1 <: fin n)))
            (fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k) pw_b;
          transitivity
            (g_ih phi * fin_sum (a (n_m1 <: fin n)))
            (fin_sum (pointwise_mul (const (g_ih phi)) (a (n_m1 <: fin n))))
            (fin_sum (fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k));
          let body_mul (k: fin m) : t = g_ih phi * a (n_m1 <: fin n) k in
          let body_ext (k: fin m) : t = g_rhs (extend_fn phi k) in
          let body_mul_def (k: fin m) : Lemma (body_mul k == g_ih phi * a (n_m1 <: fin n) k) = () in
          let body_ext_def (k: fin m) : Lemma (body_ext k == g_rhs (extend_fn phi k)) = () in
          let g_step_def () : Lemma (g_step phi ==
            fin_sum (fun (k: fin m) -> g_rhs (extend_fn phi k))) = () in
          Classical.forall_intro body_mul_def;
          Classical.forall_intro body_ext_def;
          g_step_def ();
          let per_k (k: fin m) : Lemma (body_mul k = body_ext k)
            = let phi_ext : fin_map n m = extend_fn phi k in
              let gd_body (i: nat) : t =
                if i < n then a (i <: fin n) (phi_ext (i <: fin n)) else one in
              let body_ih_inner (i: nat) : t =
                if i < n_m1 then a' (i <: fin n_m1) (phi (i <: fin n_m1)) else one in
              let gd_body_def (i: nat) : Lemma (gd_body i ==
                (if i < n then a (i <: fin n) (phi_ext (i <: fin n)) else one #t)) = () in
              let phi_ext_def (i: fin n) : Lemma (phi_ext i ==
                (if i = n_m1 then k else phi (i <: fin n_m1))) = () in
              let body_ih_inner_def (i: nat) : Lemma (body_ih_inner i ==
                (if i < n_m1 then a' (i <: fin n_m1) (phi (i <: fin n_m1)) else one #t)) = () in
              Classical.forall_intro gd_body_def;
              Classical.forall_intro phi_ext_def;
              Classical.forall_intro body_ih_inner_def;
              prod_range_unfold_right gd_body 0 n;
              assert (gd_body n_m1 == a (n_m1 <: fin n) k);
              let cong3 (i: nat)
                : Lemma (0 <= i /\ i < n_m1 ==> gd_body i = body_ih_inner i)
                = if 0 <= i && i < n_m1 then
                    ()
              in
              Classical.forall_intro cong3;
              prod_range_congruence gd_body body_ih_inner 0 n_m1 (fun _ -> ());

              r.mul_congruence
                (prod_range gd_body 0 n_m1) (a (n_m1 <: fin n) k)
                (prod_range body_ih_inner 0 n_m1) (a (n_m1 <: fin n) k);
              transitivity
                (prod_range gd_body 0 n)
                (prod_range gd_body 0 n_m1 * a (n_m1 <: fin n) k)
                (prod_range body_ih_inner 0 n_m1 * a (n_m1 <: fin n) k)
          in
          Classical.forall_intro per_k;
          let cong_bm (k: fin m) : Lemma
            ((fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k) k = body_mul k)
            = reflexivity (g_ih phi * a (n_m1 <: fin n) k) in
          Classical.forall_intro cong_bm;
          fin_sum_congruence #t #(acg_of_r t #r) #m
            (fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k)
            body_mul (fun _ -> ());
          fin_sum_congruence #t #(acg_of_r t #r) #m body_mul body_ext (fun _ -> ());
          let cong_be (k: fin m) : Lemma
            (body_ext k = (fun (k: fin m) -> g_rhs (extend_fn phi k)) k)
            = reflexivity (g_rhs (extend_fn phi k)) in
          Classical.forall_intro cong_be;
          fin_sum_congruence #t #(acg_of_r t #r) #m body_ext
            (fun (k: fin m) -> g_rhs (extend_fn phi k)) (fun _ -> ());
          let s1 : t = g_ih phi * s_n in
          let s2 : t = fin_sum (fun (k: fin m) -> g_ih phi * a (n_m1 <: fin n) k) in
          let s3 : t = fin_sum body_mul in
          let s4 : t = fin_sum body_ext in
          let s5 : t = fin_sum (fun (k: fin m) -> g_rhs (extend_fn phi k)) in
          assert (h1 phi == s1);
          assert (g_step phi == s5);


          assert (h1 phi = s1);
          assert (g_step phi = s5);
          assert (s1 = s2);
          assert (s2 = s3);
          assert (s3 = s4);
          assert (s4 = s5);
          transitivity (h1 phi) s1 s2;
          transitivity (h1 phi) s2 s3;
          transitivity (h1 phi) s3 s4;
          transitivity (h1 phi) s4 s5;
          transitivity (h1 phi) s5 (g_step phi)
      in
      Classical.forall_intro per_phi;
      sum_list_map_congruence h1 g_step (all_fns_to n_m1 m) (fun _ -> ());
      sum_over_fns_to_split_head n_m1 m g_rhs;
      let cong_ext (phi: fin_map n_m1 m) : Lemma
        (extend_fin_sum n_m1 m g_rhs phi = g_step phi)
        = assert (extend_fin_sum n_m1 m g_rhs phi ==
                  fin_sum (fun (k: fin m) -> g_rhs (extend_fn phi k)))
            by (FStar.Tactics.norm [delta_only [`%extend_fin_sum]]; FStar.Tactics.trefl ());
          reflexivity (g_step phi) in
      Classical.forall_intro cong_ext;
      sum_list_map_congruence
        (extend_fin_sum n_m1 m g_rhs)
        g_step (all_fns_to n_m1 m) (fun _ -> ());
      transitivity
        (sum_over_fns_to ((n_m1 ++ 1)) m g_rhs)
        (sum_over_fns_to n_m1 m (extend_fin_sum n_m1 m g_rhs))
        (sum_over_fns_to n_m1 m g_step);
      let lhs_n = prod_range body_lhs 0 n in
      let rhs_n = sum_over_fns_to n m g_rhs in
      let t1 : t = pr_n_m1 * s_n in
      let t2 : t = sum_ih * s_n in
      let t3 : t = sum_over_fns_to n_m1 m h1 in
      let t4 : t = sum_over_fns_to n_m1 m g_step in
      let t5 : t = sum_over_fns_to n_m1 m (fun (phi: fin_map n_m1 m) -> g_ih phi * s_n) in
      reflexivity lhs_n; reflexivity rhs_n;
      reflexivity t1; reflexivity t2; reflexivity t3; reflexivity t4; reflexivity t5;
      assert (lhs_n = t1);
      assert (t1 = t2);
      let cong_h1 (phi: fin_map n_m1 m) : Lemma
        ((fun (phi: fin_map n_m1 m) -> g_ih phi * s_n) phi = h1 phi)
        = reflexivity (g_ih phi * s_n) in
      Classical.forall_intro cong_h1;
      sum_list_map_congruence
        (fun (phi: fin_map n_m1 m) -> g_ih phi * s_n) h1 (all_fns_to n_m1 m) (fun _ -> ());
      assert (t5 = t3);
      assert (t2 = t5);
      assert (t3 = t4);
      assert (rhs_n == sum_over_fns_to ((n_m1 ++ 1)) m g_rhs);

      assert (rhs_n = sum_over_fns_to ((n_m1 ++ 1)) m g_rhs);
      assert (sum_over_fns_to ((n_m1 ++ 1)) m g_rhs = t4);
      transitivity rhs_n (sum_over_fns_to ((n_m1 ++ 1)) m g_rhs) t4;

      transitivity lhs_n t1 t2;
      transitivity lhs_n t2 t5;
      transitivity lhs_n t5 t3;
      transitivity lhs_n t3 t4;
      transitivity lhs_n t4 rhs_n
    end
#pop-options


(* ================================================================== *)
(*  MERGED FROM Core.Matrix.Adjugate                                   *)

(* ================================================================== *)

(* ================================================================== *)
(*  The signed cofactor (without the entry): C(M, i, j)               *)
(*  = (-1)^(i+j) * det(minor M i j)                                   *)
(* ================================================================== *)

let signed_cofactor (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) : t
  = minus_one_pow #t #cr (((i <: nat) ++ (j <: nat)))
    * det (minor m i j)

(* cofactor_term m i j = m(i,j) * signed_cofactor m i j
   (modulo associativity/commutativity) *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let cofactor_term_eq_entry_times_signed_cofactor
  (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (cofactor_term m i j = m i j * signed_cofactor m i j)
  = H.elim_equatable_laws t ();
    (* cofactor_term = mop * m(i,j) * det_min
       m(i,j) * signed_cofactor = m(i,j) * (mop * det_min)
       Need: (a*b)*c = b*(a*c) *)
    let mop = minus_one_pow (((i <: nat) ++ (j <: nat))) in
    let det_min = det (minor m i j) in
    let e = m i j in
    (* cofactor_term = (mop * e) * det_min *)
    mul_associativity mop e det_min;
    (* mop * e * det_min = mop * (e * det_min) *)
    mul_commutativity mop (e * det_min);
    (* = (e * det_min) * mop ... no, let me just do mop*e = e*mop *)
    mul_commutativity mop e;
    (* mop * e = e * mop *)
    mul_congruence (mop * e) det_min (e * mop) det_min;
    mul_associativity e mop det_min;
    (* (e * mop) * det_min = e * (mop * det_min) = e * signed_cofactor *)
    transitivity (cofactor_term m i j) ((e * mop) * det_min) (e * signed_cofactor m i j)
#pop-options

(* ================================================================== *)
(*  The adjugate matrix                                               *)
(* ================================================================== *)

let adjugate (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) : square_matrix t n
  = fun (i: fin n) (j: fin n) -> signed_cofactor m j i

(* ================================================================== *)
(*  Key identity: (adj M * M)(i,j) = det(M) * delta(i,j)             *)
(*                                                                     *)
(*  Split into two cases:                                              *)
(*    Diagonal (i=j): Laplace expansion along row i → det M.          *)
(*    Off-diagonal (i≠j): Laplace of a matrix with duplicate row → 0. *)
(* ================================================================== *)

(* The identity matrix. *)
let identity_matrix (#t: Type) {| cr: commutative_ring t |} (n: pos)
  : square_matrix t n
  = fun (i: fin n) (j: fin n) ->
      if (i <: nat) = (j <: nat) then one else zero

(* Scalar multiple of identity. *)
let scalar_identity (#t: Type) {| cr: commutative_ring t |} (#n: pos) (c: t)
  : square_matrix t n
  = fun (i: fin n) (j: fin n) ->
      if (i <: nat) = (j <: nat) then c else zero

(* ------------------------------------------------------------------ *)
(*  Diagonal case: (adj M * M)(i,i) = det M                           *)
(*                                                                     *)
(*  (adj M * M)(i,i) = Σ_k adj(M)(i,k) * M(k,i)                     *)
(*                    = Σ_k signed_cofactor(M, k, i) * M(k,i)         *)
(*                    = Σ_k cofactor_term(M, k, i) ... by the         *)
(*                      rearrangement of cofactor_term.                *)
(*                                                                     *)
(*  Wait: cofactor_term m k i = (-1)^(k+i) * m(k,i) * det(minor m k i) *)
(*      = m(k,i) * signed_cofactor m k i                               *)
(*      = m(k,i) * adj(M)(i,k)                                        *)
(*      = M(k,i) * adj(M)(i,k)                                        *)
(*                                                                     *)
(*  So Σ_k adj(M)(i,k) * M(k,i) = Σ_k cofactor_term m k i = det M   *)
(*  by det_laplace_row applied with expansion row = ... wait, no.     *)
(*                                                                     *)
(*  Actually det_laplace_row expands along row i:                      *)
(*    det M = Σ_j cofactor_term m i j                                  *)
(*  But we need expansion along COLUMN i:                              *)
(*    det M = Σ_k cofactor_term m k i                                  *)
(*  This is Laplace expansion along column i.                          *)
(*                                                                     *)
(*  We can get this from det_laplace_row applied to M^T:               *)
(*    det(M^T) = Σ_j cofactor_term(M^T, i, j)                         *)
(*  and det(M^T) = det(M), minor(M^T, i, j) = transpose(minor(M,j,i)) *)
(* ------------------------------------------------------------------ *)

(* Laplace expansion along a column, derived from row expansion of transpose. *)

(* First: minor of transpose = transpose of minor (with swapped indices). *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let minor_transpose (#t: Type) (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (a b: fin ((n - 1)))
  : Lemma (minor (transpose m) i j a b == minor m j i b a)
  = ()
#pop-options

let minor_transpose_eq (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (matrix_eq #t #(cr.cr_r.r_add.acg_eq) #((n - 1))
             (minor (transpose m) i j)
             (transpose (minor m j i)))
  = let lhs = minor (transpose m) i j in
    let rhs = transpose (minor m j i) in
    let aux (a b: fin ((n - 1)))
      : Lemma (lhs a b = rhs a b)
      = minor_transpose m i j a b;
        reflexivity (minor m j i b a)
    in
    Classical.forall_intro_2 aux

(* det of minor of transpose = det of minor (via det_transpose + det_pointwise_eq). *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let det_minor_transpose (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (det (minor (transpose m) i j)
            = det (minor m j i))
  = H.elim_equatable_laws t ();
    let nm1 = (n - 1) in
    minor_transpose_eq m i j;
    det_pointwise_eq #t #cr #nm1
      (minor (transpose m) i j)
      (transpose (minor m j i));
    det_transpose (minor m j i);
    transitivity
      (det (minor (transpose m) i j))
      (det (transpose (minor m j i)))
      (det (minor m j i))
#pop-options

(* signed_cofactor of transpose relates to signed_cofactor of original. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let signed_cofactor_transpose (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (signed_cofactor (transpose m) i j = signed_cofactor m j i)
  = H.elim_equatable_laws t ();
    det_minor_transpose m i j;
    (* (-1)^(i+j) * det(minor(M^T, i, j)) = (-1)^(j+i) * det(minor(M, j, i))
       and i+j = j+i *)
    assert (((i <: nat) ++ (j <: nat)) =
            ((j <: nat) ++ (i <: nat)));
    mul_congruence
      (minus_one_pow #t #cr (((i <: nat) ++ (j <: nat))))
      (det (minor (transpose m) i j))
      (minus_one_pow #t #cr (((j <: nat) ++ (i <: nat))))
      (det (minor m j i))
#pop-options

(* Laplace expansion along column j:
   det M = Σ_i cofactor_term_col m i j
   where cofactor_term_col m i j = m(i,j) * signed_cofactor m i j. *)

(* Actually we define a simpler "column cofactor summand": *)
let col_cofactor_summand (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (j: fin n) (i: fin n) : t
  = m i j * signed_cofactor m i j

#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let det_laplace_col
  (#t: Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n) (j: fin n)
  : Lemma (det m = fin_sum (col_cofactor_summand m j))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    det_transpose m;

    det_laplace_row (transpose m) j;
    (* now: det m = det(M^T) and det(M^T) = fin_sum(cofactor_term M^T j) *)
    transitivity (det m) (det (transpose m))
                 (fin_sum (cofactor_term (transpose m) j));
    (* now: det m = fin_sum(cofactor_term M^T j) *)
    let pw (i: fin n) : Lemma (cofactor_term (transpose m) j i
                              = col_cofactor_summand m j i)
      = cofactor_term_eq_entry_times_signed_cofactor (transpose m) j i;
        signed_cofactor_transpose m j i;

        mul_congruence (transpose m j i) (signed_cofactor (transpose m) j i)
                       (m i j) (signed_cofactor m i j);
        transitivity (cofactor_term (transpose m) j i)
                     (transpose m j i * signed_cofactor (transpose m) j i)
                     (m i j * signed_cofactor m i j)
    in
    Classical.forall_intro pw;
    fin_sum_congruence (cofactor_term (transpose m) j)
                       (col_cofactor_summand m j) (fun _ -> ());
    transitivity (det m) (fin_sum (cofactor_term (transpose m) j))
                 (fin_sum (col_cofactor_summand m j))
#pop-options


(* ------------------------------------------------------------------ *)
(*  "Fake" Laplace: expand along column j using row entries from       *)
(*  a DIFFERENT column i ≠ j. This gives zero (because it's the       *)
(*  determinant of a matrix with two equal columns).                   *)
(* ------------------------------------------------------------------ *)

(* Matrix with column j replaced by column i. *)
let col_duplicate (#t: Type) (#n: pos)
  (m: square_matrix t n) (i j: fin n) : square_matrix t n
  = fun (r: fin n) (c: fin n) ->
      if (c <: nat) = (j <: nat) then m r i else m r c

(* The minor at (k, j) of col_duplicate is the same as minor at (k, j) of m,
   since we only changed column j and minor deletes column j. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let minor_col_duplicate_at_j (#t: Type) (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (k: fin n)
  (a b: fin ((n - 1)))
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  minor (col_duplicate m i j) k j a b == minor m k j a b)
  = (* In minor we delete column j, so column index c = skip j b ≠ j.
       Hence col_duplicate m i j (skip k a) (skip j b) = m (skip k a) (skip j b). *)
    skip_avoids j b
#pop-options

let minor_col_duplicate_eq (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (k: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  matrix_eq #t #(cr.cr_r.r_add.acg_eq)
                      #((n - 1))
                      (minor (col_duplicate m i j) k j)
                      (minor m k j))
  = let aux (a b: fin ((n - 1)))
      : Lemma (minor (col_duplicate m i j) k j a b = minor m k j a b)
      = minor_col_duplicate_at_j m i j k a b;
        reflexivity (minor m k j a b)
    in
    Classical.forall_intro_2 aux

(* The "fake Laplace" sum: Σ_k m(k,i) * signed_cofactor(m, k, j). *)
let fake_laplace_summand (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (k: fin n) : t
  = m k i * signed_cofactor m k j

(* This equals det of col_duplicate m i j = 0 (two equal columns). *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let fake_laplace_is_det_col_duplicate
  (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  fin_sum (fake_laplace_summand m i j)
                  = det (col_duplicate m i j))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    det_laplace_col (col_duplicate m i j) j;
    (* det(col_dup) = fin_sum(col_cofactor_summand (col_dup) j) *)
    let pw (k: fin n)
      : Lemma (col_cofactor_summand (col_duplicate m i j) j k
             = fake_laplace_summand m i j k)
      = minor_col_duplicate_eq m i j k;
        det_pointwise_eq #t #cr #((n - 1))
          (minor (col_duplicate m i j) k j) (minor m k j);
        mul_congruence
          (minus_one_pow #t #cr (((k <: nat) ++ (j <: nat))))
          (det (minor (col_duplicate m i j) k j))
          (minus_one_pow #t #cr (((k <: nat) ++ (j <: nat))))
          (det (minor m k j));
        mul_congruence (col_duplicate m i j k j)
                       (signed_cofactor (col_duplicate m i j) k j)
                       (m k i) (signed_cofactor m k j)
    in
    Classical.forall_intro pw;
    fin_sum_congruence (col_cofactor_summand (col_duplicate m i j) j)
                       (fake_laplace_summand m i j) (fun _ -> ());
    transitivity (det (col_duplicate m i j))
                 (fin_sum (col_cofactor_summand (col_duplicate m i j) j))
                 (fin_sum (fake_laplace_summand m i j))
#pop-options

(* col_duplicate has two equal columns → det = 0. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let det_col_duplicate_zero (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  det (col_duplicate m i j) = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let m' = col_duplicate m i j in
    let tm = transpose m' in
    let cols_eq (r: fin n) : Lemma (m' r i = m' r j)
      = reflexivity (m r i)
    in
    Classical.forall_intro cols_eq;
    let rows_eq (c: fin n) : Lemma (tm i c = tm j c)
      = cols_eq c
    in
    Classical.forall_intro rows_eq;
    det_two_equal_rows_cr tm i j;
    (* det tm = zero *)
    det_transpose m';
    (* det tm = det m' *)
    (* det m' = det tm *)
    transitivity (det m') (det tm) zero
#pop-options

(* Combine: fake Laplace sum = 0 when i ≠ j. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let fake_laplace_zero (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  fin_sum (fake_laplace_summand m i j) = zero)
  = H.trans_for_calc t ();
    fake_laplace_is_det_col_duplicate m i j;
    det_col_duplicate_zero m i j;
    transitivity (fin_sum (fake_laplace_summand m i j))
                 (det (col_duplicate m i j)) zero
#pop-options

(* ================================================================== *)
(*  Main theorem: adj(M) * M = det(M) * I                             *)
(* ================================================================== *)

(* Entry (i,j) of adj(M) * M. *)
(* (adj M * M)(i,j) = Σ_k adj(M)(i,k) * M(k,j)
                     = Σ_k signed_cofactor(M, k, i) * M(k,j) *)

(* When i = j: this is col_cofactor_summand m i = Σ_k M(k,i) * signed_cofactor(M,k,i) = det M *)
(* When i ≠ j: this is fake_laplace_summand m j i = Σ_k M(k,j) * signed_cofactor(M,k,i) = 0 *)

(* adj_mul_summand m i j k = adjugate m i k * m k j
                           = signed_cofactor m k i * m k j
                           = m k j * signed_cofactor m k i (by commutativity) *)

(* Diagonal entry: *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let adj_mul_diagonal (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i: fin n)
  : Lemma (matrix_mul (adjugate m) m i i = det m)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    matrix_mul_to_fin_sum (adjugate m) m i i;
    H.leibniz_to_eq (matrix_mul (adjugate m) m i i)
                    (fin_sum #t #(acg_of_r t #cr.cr_r) #n
                      (pointwise_mul (row (adjugate m) i) (col m i)));
    let pw (k: fin n)
      : Lemma (pointwise_mul (row (adjugate m) i) (col m i) k
             = col_cofactor_summand m i k)
      = mul_commutativity (signed_cofactor m k i) (m k i)
    in
    Classical.forall_intro pw;
    fin_sum_congruence #t #(acg_of_r t #cr.cr_r) #n
      (pointwise_mul (row (adjugate m) i) (col m i))
      (col_cofactor_summand m i) (fun _ -> ());
    transitivity (matrix_mul (adjugate m) m i i)
                 (fin_sum #t #(acg_of_r t #cr.cr_r) #n
                   (pointwise_mul (row (adjugate m) i) (col m i)))
                 (fin_sum (col_cofactor_summand m i));
    det_laplace_col m i;
    transitivity (matrix_mul (adjugate m) m i i)
                 (fin_sum (col_cofactor_summand m i)) (det m)
#pop-options

(* Off-diagonal entry: *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let adj_mul_off_diagonal (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  matrix_mul (adjugate m) m i j = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    matrix_mul_to_fin_sum (adjugate m) m i j;
    H.leibniz_to_eq (matrix_mul (adjugate m) m i j)
                    (fin_sum #t #(acg_of_r t #cr.cr_r) #n
                      (pointwise_mul (row (adjugate m) i) (col m j)));
    let pw (k: fin n)
      : Lemma (pointwise_mul (row (adjugate m) i) (col m j) k
             = fake_laplace_summand m j i k)
      = mul_commutativity (signed_cofactor m k i) (m k j)
    in
    Classical.forall_intro pw;
    fin_sum_congruence #t #(acg_of_r t #cr.cr_r) #n
      (pointwise_mul (row (adjugate m) i) (col m j))
      (fake_laplace_summand m j i) (fun _ -> ());
    transitivity (matrix_mul (adjugate m) m i j)
                 (fin_sum #t #(acg_of_r t #cr.cr_r) #n
                   (pointwise_mul (row (adjugate m) i) (col m j)))
                 (fin_sum (fake_laplace_summand m j i));
    fake_laplace_zero m j i;
    transitivity (matrix_mul (adjugate m) m i j)
                 (fin_sum (fake_laplace_summand m j i)) zero
#pop-options

(* ================================================================== *)
(*  Headline: adj(M) * M = det(M) * I  (pointwise equality)          *)
(* ================================================================== *)

#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let adjugate_mul_eq_det_identity (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n)
  : Lemma (matrix_eq (matrix_mul (adjugate m) m) (scalar_identity (det m)))
  = H.elim_equatable_laws t ();
    let lhs = matrix_mul (adjugate m) m in
    let rhs = scalar_identity (det m) in
    let pointwise (i j: fin n) : Lemma (lhs i j = rhs i j)
      = if (i <: nat) = (j <: nat) then begin
          adj_mul_diagonal m i
        end else begin
          adj_mul_off_diagonal m i j
        end
    in
    Classical.forall_intro_2 pointwise
#pop-options


(* ================================================================== *)
(*  MERGED FROM Core.Matrix.Determinant.Mul                            *)

(* ================================================================== *)

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ============================================================ *)
(*  Section A: Named term builders.                              *)
(*  Every function used in a lemma statement is named here so    *)
(*  SMT sees a stable symbol across sites.                       *)
(* ============================================================ *)

(* Inner expansion term: a(i,k) * b(k, sigma i).
   Used inside `fin_sum` for matrix_mul_eq_at expansion. *)
let ab_k (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (i: fin n) (k: fin n) : t
  = a i k * b k (sigma.fwd i)

(* Outer Leibniz term, expanded via matrix_mul:
   if i<n then (AB)(i, sigma i) else one. *)
let ab_perm_body (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (i: nat) : t
  = if i < n then (matrix_mul a b) (i <: fin n) (sigma.fwd (i <: fin n))
    else one

(* Same outer term but expanded as fin_sum:
   if i<n then sum_k a(i,k) b(k, sigma i) else one. *)
let finsum_perm_body (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (i: nat) : t
  = if i < n then fin_sum (ab_k a b sigma (i <: fin n))
    else one

(* Multi-distrib expansion: pick a representative φ for each factor.
   if i<n then a(i, φ i) * b(φ i, sigma i) else one. *)
let phi_inner_body (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n) (i: nat) : t
  = if i < n then ab_k a b sigma (i <: fin n) (phi (i <: fin n))
    else one

(* prod_range of phi_inner_body — one summand of the multi-distrib sum
   over fin_map n n. *)
let phi_outer (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n) : t
  = prod_range (phi_inner_body a b sigma phi) 0 n

(* ============================================================ *)
(*  Section B: perm_product expanded as a sum over fin_map n n.    *)
(* ============================================================ *)

(* Step B.1: perm_product (matrix_mul a b) sigma
            = prod_range (finsum_perm_body a b sigma) 0 n.

   Pointwise, ab_perm_body i = finsum_perm_body i (for i < n) by
   matrix_mul_eq_at.  Then prod_range_congruence. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let perm_product_as_finsum_prod
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (perm_product (matrix_mul a b) sigma
           = prod_range (finsum_perm_body a b sigma) 0 n)
  = H.elim_equatable_laws t ();
    let pointwise (i: nat)
      : Lemma (requires 0 <= i /\ i < n)
              (ensures ab_perm_body a b sigma i = finsum_perm_body a b sigma i)
      = let ii : fin n = i in
        assert (matrix_mul a b ii (sigma.fwd ii) ==
                fin_sum (ab_k a b sigma ii))
          by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
        H.leibniz_to_eq (matrix_mul a b ii (sigma.fwd ii))
                        (fin_sum (ab_k a b sigma ii))
    in
    Classical.forall_intro (Classical.move_requires pointwise);
    prod_range_congruence (ab_perm_body a b sigma) (finsum_perm_body a b sigma) 0 n (fun _ -> ());
    assert (perm_product (matrix_mul a b) sigma ==
            prod_range (ab_perm_body a b sigma) 0 n)
      by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
    H.leibniz_then_eq (perm_product (matrix_mul a b) sigma)
                      (prod_range (ab_perm_body a b sigma) 0 n)
                      (prod_range (finsum_perm_body a b sigma) 0 n)
#pop-options

(* Step B.2: Apply multi-distrib expansion.
   prod_range (finsum_perm_body a b sigma) 0 n
     = sum_over_fns_to n n (phi_outer a b sigma).                         *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let prod_range_finsum_to_sum_over_fns
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (prod_range (finsum_perm_body a b sigma) 0 n
           = sum_over_fns_to n n (phi_outer a b sigma))
  = H.elim_equatable_laws t ();
    prod_range_of_fin_sum n n (ab_k a b sigma);
    (* That gives:
         prod_range (fun i -> if i<n then fin_sum (ab_k a b sigma i) else one) 0 n
         = sum_over_fns_to n n (fun phi -> prod_range (fun i -> if i<n then ab_k a b sigma i (phi i) else one) 0 n)
       Both sides definitionally match our named functions.            *)
    assert (prod_range (finsum_perm_body a b sigma) 0 n ==
            prod_range (fun (i: nat) ->
              if i < n then fin_sum (ab_k a b sigma (i <: fin n)) else one) 0 n)
      by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
    assert (sum_over_fns_to n n (phi_outer a b sigma) ==
            sum_over_fns_to #t #(acg_of_r t #(cr.cr_r)) n n
              (fun (phi: fin_map n n) ->
                prod_range (fun (i: nat) ->
                  if i < n then ab_k a b sigma (i <: fin n) (phi (i <: fin n))
                  else one) 0 n))
      by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
    ()
#pop-options
(* Step B.3: Compose B.1 + B.2.
   perm_product (matrix_mul a b) sigma = sum_over_fns_to n n (phi_outer a b sigma).  *)
let perm_product_to_sum_over_fns
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (perm_product (matrix_mul a b) sigma
           = sum_over_fns_to n n (phi_outer a b sigma))
  = perm_product_as_finsum_prod a b sigma;
    prod_range_finsum_to_sum_over_fns a b sigma;
    transitivity (perm_product (matrix_mul a b) sigma)
                 (prod_range (finsum_perm_body a b sigma) 0 n)
                 (sum_over_fns_to n n (phi_outer a b sigma))

(* ============================================================ *)
(* Section C: Factor phi_outer = phi_prod * perm_product(phi_mat) *)
(* ============================================================ *)

(* Named: prod_i a(i, phi i), via fin_prod over apply_along.   *)
let phi_prod (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a: square_matrix t n) (phi: fin_map n n) : t
  = fin_prod (apply_along a phi)

(* Named: matrix whose row i is row (phi i) of b.               *)
let phi_matrix (#t: Type) (#n: pos)
  (b: square_matrix t n) (phi: fin_map n n) : square_matrix t n
  = fun i j -> b (phi i) j

(* Named: ab_perm_body for the phi_matrix:                       *)
let phi_matrix_perm_body (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (b: square_matrix t n) (phi: fin_map n n) (sigma: permutation n) (i: nat) : t
  = if i < n then (phi_matrix b phi) (i <: fin n) (sigma.fwd (i <: fin n))
    else one
(* ============================================================ *)
(*  Section C-pre: Helper lemma — pointwise product factors.    *)
(* ============================================================ *)

(* Named pairwise product. *)
let pw_mul (#t: Type) {| cr: commutative_ring t |} (f g: nat -> t) (i: nat) : t
  = f i * g i

(* Helper: (a*b) * (c*d) = (a*c) * (b*d). *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let four_swap_cr
  (#t: Type) {| cr: commutative_ring t |} (a b c d: t)
  : Lemma ((a * b) * (c * d) = (a * c) * (b * d))
  = assert ((a * b) * (c * d) = (a * c) * (b * d)) by canon_ring ()
#pop-options
(* prod_range_factor: pointwise multiplicative factoring of prod_range over
   commutative ring.  Uses the named pw_mul to avoid lambda-in-postcondition. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
let rec prod_range_factor
  (#t: Type) {| cr: commutative_ring t |}
  (f g: nat -> t) (lo hi: nat)
  : Lemma
    (ensures prod_range (pw_mul f g) lo hi
           = prod_range f lo hi * prod_range g lo hi)
    (decreases (hi - lo))
  = H.elim_equatable_laws t ();
    if lo >= hi then begin
      prod_range_empty (pw_mul f g) lo hi;
      prod_range_empty f lo hi;
      prod_range_empty g lo hi;
      mul_congruence (prod_range f lo hi) (prod_range g lo hi) (one #t) (one #t);
      H.one_mul_x (one #t);
      transitivity (prod_range f lo hi * prod_range g lo hi)
                   (one #t * one #t) (one #t);
      transitivity (prod_range (pw_mul f g) lo hi)
                   (one #t)
                   (prod_range f lo hi * prod_range g lo hi)
    end else begin
      prod_range_unfold_left (pw_mul f g) lo hi;
      prod_range_unfold_left f lo hi;
      prod_range_unfold_left g lo hi;
      prod_range_factor f g ((lo ++ 1)) hi;
      let pf = prod_range f ((lo ++ 1)) hi in
      let pg = prod_range g ((lo ++ 1)) hi in
      let pfg = prod_range (pw_mul f g) ((lo ++ 1)) hi in
      (* pfg = pf * pg by IH *)
      mul_congruence (f lo * g lo) pfg (f lo * g lo) (pf * pg);
      four_swap_cr (f lo) (g lo) pf pg;
      (* now: (f lo * g lo) * pfg = (f lo * g lo) * (pf*pg) = (f lo * pf) * (g lo * pg) *)
      transitivity ((f lo * g lo) * pfg)
                   ((f lo * g lo) * (pf * pg))
                   ((f lo * pf) * (g lo * pg));
      mul_congruence (f lo * pf) (g lo * pg)
                     (prod_range f lo hi) (prod_range g lo hi);
      transitivity ((f lo * g lo) * pfg)
                   ((f lo * pf) * (g lo * pg))
                   (prod_range f lo hi * prod_range g lo hi);
      (* finally: prod_range (pw_mul f g) lo hi = (f lo * g lo) * pfg = ... *)
      H.leibniz_to_eq (prod_range (pw_mul f g) lo hi) ((f lo * g lo) * pfg);
      transitivity (prod_range (pw_mul f g) lo hi)
                   ((f lo * g lo) * pfg)
                   (prod_range f lo hi * prod_range g lo hi)
    end
#pop-options
(* The two named factors of phi_inner_body: the a-side and the b-side. *)
let phi_a_part (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a: square_matrix t n) (phi: fin_map n n) (i: nat) : t
  = if i < n then a (i <: fin n) (phi (i <: fin n)) else one

let phi_b_part (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (b: square_matrix t n) (phi: fin_map n n) (sigma: permutation n) (i: nat) : t
  = if i < n then b (phi (i <: fin n)) (sigma.fwd (i <: fin n)) else one

(* phi_inner_body = pw_mul (phi_a_part a phi) (phi_b_part b phi sigma). *)
let phi_inner_body_def
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n)
  : Lemma (forall (i: nat). phi_inner_body a b sigma phi i =
                            pw_mul (phi_a_part a phi) (phi_b_part b phi sigma) i)
  = H.elim_equatable_laws t ();
    let aux (i: nat) : Lemma (phi_inner_body a b sigma phi i =
                              pw_mul (phi_a_part a phi) (phi_b_part b phi sigma) i)
      = if i < n then
          ()
        else begin
          H.one_mul_x (one #t)
        end
    in
    Classical.forall_intro aux

(* Factor lemma: prod_range phi_inner_body = prod a-part * prod b-part. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let phi_outer_factored
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n)
  : Lemma (phi_outer a b sigma phi =
           prod_range (phi_a_part a phi) 0 n
           * prod_range (phi_b_part b phi sigma) 0 n)
  = H.elim_equatable_laws t ();
    phi_inner_body_def a b sigma phi;
    prod_range_congruence (phi_inner_body a b sigma phi)
                          (pw_mul (phi_a_part a phi) (phi_b_part b phi sigma))
                          0 n (fun _ -> ());
    prod_range_factor (phi_a_part a phi) (phi_b_part b phi sigma) 0 n;
    transitivity (phi_outer a b sigma phi)
                 (prod_range (pw_mul (phi_a_part a phi) (phi_b_part b phi sigma)) 0 n)
                 (prod_range (phi_a_part a phi) 0 n * prod_range (phi_b_part b phi sigma) 0 n)
#pop-options
(* Compose: phi_outer = phi_prod * perm_product (phi_matrix b phi).        *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let phi_outer_eq_a_prod_perm_product
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n)
  : Lemma (phi_outer a b sigma phi =
           phi_prod a phi * perm_product (phi_matrix b phi) sigma)
  = H.elim_equatable_laws t ();
    phi_outer_factored a b sigma phi;
    (* prod_range (phi_a_part a phi) 0 n == phi_prod a phi by eta. *)
    assert (prod_range (phi_a_part a phi) 0 n == phi_prod a phi)
      by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
    (* prod_range (phi_b_part b phi sigma) 0 n == perm_product (phi_matrix b phi) sigma. *)
    assert (prod_range (phi_b_part b phi sigma) 0 n ==
            perm_product (phi_matrix b phi) sigma)
      by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
    H.leibniz_to_eq (prod_range (phi_a_part a phi) 0 n) (phi_prod a phi);
    H.leibniz_to_eq (prod_range (phi_b_part b phi sigma) 0 n)
                    (perm_product (phi_matrix b phi) sigma);
    mul_congruence (prod_range (phi_a_part a phi) 0 n)
                   (prod_range (phi_b_part b phi sigma) 0 n)
                   (phi_prod a phi)
                   (perm_product (phi_matrix b phi) sigma);
    transitivity (phi_outer a b sigma phi)
                 (prod_range (phi_a_part a phi) 0 n
                  * prod_range (phi_b_part b phi sigma) 0 n)
                 (phi_prod a phi * perm_product (phi_matrix b phi) sigma)
#pop-options
(* ============================================================ *)
(*  Section E.1: Non-injective phi forces det(phi_matrix b phi) = 0. *)
(* ============================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let det_phi_matrix_non_inj
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (b: square_matrix t n) (phi: fin_map n n) (i j: fin n)
  : Lemma (requires ~(i == j) /\ phi i == phi j)
          (ensures  det (phi_matrix b phi) = zero)
  = H.elim_equatable_laws t ();
    let m = phi_matrix b phi in
    let aux (k: fin n) : Lemma (m i k = m j k)
      = assert (m i k == b (phi i) k);
        assert (m j k == b (phi j) k);
        assert (phi i == phi j)
    in
    Classical.forall_intro aux;
    det_two_equal_rows_cr m i j
#pop-options
(* ============================================================ *)
(*  Section D: Combinatorial machinery on fin_map n n.            *)
(*  search_preimage, compress_val, injective_surjective,        *)
(*  inverse_fn, perm_of_injective_fn, is_injective_b.           *)
(* ============================================================ *)

private let rec search_preimage (#n: pos) (f: fin_map n n) (target: fin n) (k: nat)
  : Tot (option (fin n)) (decreases (n - k))
  = if k >= n then None
    else if f (k <: fin n) = target then Some (k <: fin n)
    else search_preimage f target ((k ++ 1))

private let rec search_preimage_spec (#n: pos) (f: fin_map n n) (target: fin n) (k: nat)
  : Lemma (ensures (match search_preimage f target k with
                    | Some j -> f j == target
                    | None -> forall (j: fin n). (j <: nat) >= k ==> ~(f j == target)))
          (decreases (n - k))
  = if k >= n then ()
    else if f (k <: fin n) = target then ()
    else search_preimage_spec f target ((k ++ 1))

private let compress_val (n: nat{n >= 2}) (gap: fin n) (v: fin n) : fin ((n - 1))
  = if (v <: nat) < (gap <: nat) then (v <: nat)
    else if (v <: nat) = (gap <: nat) then 0
    else ((v <: nat) - 1)

private let compress_val_injective (n: nat{n >= 2}) (gap: fin n) (v1 v2: fin n)
  : Lemma (requires ~(v1 == gap) /\ ~(v2 == gap) /\ compress_val n gap v1 == compress_val n gap v2)
          (ensures v1 == v2)
  = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
private let rec injective_surjective (#n: pos) (f: fin_map n n) (target: fin n)
  : Lemma (requires forall (i j: fin n). f i == f j ==> i == j)
          (ensures Some? (search_preimage f target 0))
          (decreases n)
  = if n = 0 then ()
    else if n = 1 then
      search_preimage_spec f target 0
    else begin
      search_preimage_spec f target 0;
      if Some? (search_preimage f target 0) then ()
      else begin
        let n1 : nat = (n - 1) in
        let last : fin n = n1 in
        let g : fin_map n1 n1 = fun (i: fin n1) -> compress_val n target (f (i <: fin n)) in
        let g_inj (i1 i2: fin n1)
          : Lemma (requires g i1 == g i2) (ensures i1 == i2) =
            compress_val_injective n target (f (i1 <: fin n)) (f (i2 <: fin n))
        in
        Classical.forall_intro_2 (fun i1 -> Classical.move_requires (g_inj i1));
        let target' : fin n1 = compress_val n target (f last) in
        injective_surjective g target';
        search_preimage_spec g target' 0;
        let j' = Some?.v (search_preimage g target' 0) in
        compress_val_injective n target (f (j' <: fin n)) (f last);
        assert False
      end
    end
#pop-options

private let inverse_fn (#n: pos) (f: fin_map n n)
  (f_inj: squash (forall (i j: fin n). f i == f j ==> i == j))
  (target: fin n) : fin n
  = injective_surjective f target;
    search_preimage_spec f target 0;
    Some?.v (search_preimage f target 0)

private let inverse_fn_spec (#n: pos) (f: fin_map n n)
  (f_inj: squash (forall (i j: fin n). f i == f j ==> i == j))
  (target: fin n) : Lemma (f (inverse_fn f f_inj target) == target)
  = injective_surjective f target;
    search_preimage_spec f target 0

#push-options "--fuel 1 --ifuel 1 --z3rlimit 40"
let perm_of_injective_fn (#n: pos) (f: fin_map n n)
  (f_inj: squash (forall (i j: fin n). f i == f j ==> i == j))
  : (p: permutation n { forall (i: fin n). p.fwd i == f i })
  = let bwd = inverse_fn f f_inj in
    let fwd_bwd (i: fin n) : Lemma (f (bwd i) == i)
      = inverse_fn_spec f f_inj i in
    let bwd_fwd (i: fin n) : Lemma (bwd (f i) == i)
      = inverse_fn_spec f f_inj (f i)
    in
    { fwd = f; bwd = bwd; fwd_bwd_id = fwd_bwd; bwd_fwd_id = bwd_fwd }
#pop-options

private let rec is_injective_from (#n: pos) (f: fin_map n n) (k: nat)
  : Tot bool (decreases (n - k))
  = if k >= n then true
    else
      let _ = search_preimage_spec f (f (k <: fin n)) 0 in
      match search_preimage f (f (k <: fin n)) 0 with
      | None -> false
      | Some j -> if (j <: nat) = k then is_injective_from f ((k ++ 1))
                  else false

let is_injective_b (#n: pos) (f: fin_map n n) : bool
  = is_injective_from f 0

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let rec is_injective_from_true (#n: pos) (f: fin_map n n) (k: nat)
  : Lemma (requires is_injective_from f k)
          (ensures forall (i: fin n). (i <: nat) >= k ==>
                   search_preimage f (f i) 0 == Some i)
          (decreases (n - k))
  = if k >= n then ()
    else begin
      search_preimage_spec f (f (k <: fin n)) 0;
      is_injective_from_true f ((k ++ 1))
    end
#pop-options

let is_injective_true (#n: pos) (f: fin_map n n)
  : Lemma (requires is_injective_b f)
          (ensures forall (i j: fin n). f i == f j ==> i == j)
  = is_injective_from_true f 0

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let rec is_injective_from_false (#n: pos) (f: fin_map n n) (k: nat)
  : Lemma (requires not (is_injective_from f k) /\ k < n)
          (ensures exists (a b: fin n). ~(a == b) /\ f a == f b)
          (decreases (n - k))
  = search_preimage_spec f (f (k <: fin n)) 0;
    match search_preimage f (f (k <: fin n)) 0 with
    | None -> ()
    | Some j ->
        if (j <: nat) = k then begin
          if (k ++ 1) >= n then ()
          else is_injective_from_false f ((k ++ 1))
        end
        else ()
#pop-options

let is_injective_false (#n: pos) (f: fin_map n n)
  : Lemma (requires not (is_injective_b f) /\ n > 0)
          (ensures exists (a b: fin n). ~(a == b) /\ f a == f b)
  = is_injective_from_false f 0
(* ============================================================ *)
(*  Section E.2: Injective phi → det(phi_matrix) = sign * det b *)
(* ============================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let det_phi_matrix_inj
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (b: square_matrix t n) (phi: fin_map n n)
  (phi_inj: squash (forall (i j: fin n). phi i == phi j ==> i == j))
  : Lemma (det (phi_matrix b phi) =
           (if parity (perm_of_injective_fn phi phi_inj) then det b
            else -(det b)))
  = H.elim_equatable_laws t ();
    let p = perm_of_injective_fn phi phi_inj in
    let m1 = phi_matrix b phi in
    let m2 = permute_rows b p in
    let cell_eq (i j: fin n) : Lemma (m1 i j = m2 i j)
      = assert (m1 i j == b (phi i) j);
        assert (m2 i j == b (p.fwd i) j);
        assert (p.fwd i == phi i)
    in
    Classical.forall_intro_2 cell_eq;
    det_pointwise_eq m1 m2;
    det_permute_rows b p;
    transitivity (det m1) (det m2)
                 (if parity p then det b else -(det b))
#pop-options
(* ============================================================ *)
(*  Section F: sum_list_fubini.                                 *)
(* ============================================================ *)

private let inner_sum_x_branch
  (#a #b #t: Type) {| acg: add_comm_group t |}
  (f: a -> b -> t) (ys: list b) (x: a)
  : t
  = sum_list (L.map (f x) ys)

private let inner_sum_y_branch
  (#a #b #t: Type) {| acg: add_comm_group t |}
  (f: a -> b -> t) (xs: list a) (y: b)
  : t
  = sum_list (L.map (swap_args f y) xs)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec sum_list_zeros
  (#a #t: Type) {| acg: add_comm_group t |}
  (xs: list a)
  : Lemma (ensures sum_list (L.map (const (zero #t)) xs) = zero #t)
          (decreases xs)
  = H.elim_equatable_laws t ();
    match xs with
    | [] -> sum_list_nil #t #acg
    | _ :: rest ->
      let tl = L.map (const (zero #t)) rest in
      sum_list_cons (zero #t) tl;
      sum_list_zeros #a #t #acg rest;
      add_congruence (zero #t) (sum_list tl) (zero #t) (zero #t);
      H.zero_plus_x (zero #t);
      transitivity (zero #t + sum_list tl) (zero #t + zero #t) (zero #t);
      transitivity (sum_list ((zero #t) :: tl)) (zero #t + sum_list tl) (zero #t)
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let sum_list_fubini_step
  (#a #b #t: Type) {| acg: add_comm_group t |}
  (f: a -> b -> t) (xs: list a {Cons? xs}) (ys: list b)
  : Lemma
    (requires sum_list (L.map (inner_sum_x_branch f ys) (Cons?.tl xs))
            = sum_list (L.map (inner_sum_y_branch f (Cons?.tl xs)) ys))
    (ensures  sum_list (L.map (inner_sum_x_branch f ys) xs)
            = sum_list (L.map (inner_sum_y_branch f xs) ys))
  = H.elim_equatable_laws t ();
    let x = Cons?.hd xs in
    let xs' = Cons?.tl xs in
    assert (xs == x :: xs');
    let f_x_ys = inner_sum_x_branch f ys x in
    let inner_xs' = sum_list (L.map (inner_sum_x_branch f ys) xs') in
    let inner_xs'_swapped = sum_list (L.map (inner_sum_y_branch f xs') ys) in
    let lhs = sum_list (L.map (inner_sum_x_branch f ys) xs) in
    let rhs = sum_list (L.map (inner_sum_y_branch f xs) ys) in
    sum_list_cons f_x_ys (L.map (inner_sum_x_branch f ys) xs');
    assert (lhs == f_x_ys + inner_xs');

    assert (inner_xs' = inner_xs'_swapped);
    add_congruence f_x_ys inner_xs' f_x_ys inner_xs'_swapped;
    assert (lhs = f_x_ys + inner_xs'_swapped);
    let g_x : b -> t = f x in
    let g_xs' : b -> t = inner_sum_y_branch f xs' in
    let map_xy_combined = L.map (pointwise_add g_x g_xs') ys in
    sum_list_map_add g_x g_xs' ys;
    assert (sum_list map_xy_combined = sum_list (L.map g_x ys) + sum_list (L.map g_xs' ys));
    assert (sum_list (L.map g_x ys) == f_x_ys);
    assert (sum_list (L.map g_xs' ys) == inner_xs'_swapped);
    assert (sum_list map_xy_combined = f_x_ys + inner_xs'_swapped);

    transitivity lhs (f_x_ys + inner_xs'_swapped) (sum_list map_xy_combined);
    let pw (y: b) : Lemma (L.memP y ys ==>
      pointwise_add g_x g_xs' y = inner_sum_y_branch f xs y)
      = if L.memP y ys then begin
          pointwise_add_unfold g_x g_xs' y;
          assert (inner_sum_y_branch f xs y
                  == sum_list (L.map (swap_args f y) xs));
          assert (L.map (swap_args f y) xs
                  == (swap_args f y x) :: L.map (swap_args f y) xs');
          swap_args_unfold f y x;
          sum_list_cons (swap_args f y x) (L.map (swap_args f y) xs');
          assert (sum_list ((swap_args f y x) :: L.map (swap_args f y) xs')
                  = swap_args f y x + sum_list (L.map (swap_args f y) xs'));
          assert (sum_list (L.map (swap_args f y) xs') == g_xs' y)
        end
    in
    Classical.forall_intro pw;
    sum_list_map_congruence
      (pointwise_add g_x g_xs')
      (inner_sum_y_branch f xs)
      ys (fun _ -> ());
    transitivity lhs (sum_list map_xy_combined) rhs
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
let rec sum_list_fubini
  (#a #b #t: Type) {| acg: add_comm_group t |}
  (f: a -> b -> t) (xs: list a) (ys: list b)
  : Lemma
    (ensures sum_list (L.map (inner_sum_x_branch f ys) xs)
           = sum_list (L.map (inner_sum_y_branch f xs) ys))
    (decreases xs)
  = H.elim_equatable_laws t ();
    if Nil? xs then begin
      sum_list_nil #t #acg;
      let aux (y: b) : Lemma (L.memP y ys ==>
        inner_sum_y_branch f xs y = (zero #t))
        = if L.memP y ys then
            sum_list_nil #t #acg
      in
      Classical.forall_intro aux;
      sum_list_map_congruence
        (inner_sum_y_branch f xs)
        (const (zero #t))
        ys (fun _ -> ());
      sum_list_zeros #b #t #acg ys;
      transitivity
        (sum_list (L.map (inner_sum_y_branch f xs) ys))
        (sum_list (L.map (const (zero #t)) ys))
        (zero #t);
      symmetry
        (sum_list (L.map (inner_sum_y_branch f xs) ys))
        (zero #t);
      assert (sum_list (L.map (inner_sum_x_branch f ys) xs) = (zero #t));
      transitivity
        (sum_list (L.map (inner_sum_x_branch f ys) xs))
        (zero #t)
        (sum_list (L.map (inner_sum_y_branch f xs) ys))
    end else begin
      sum_list_fubini f (Cons?.tl xs) ys;
      sum_list_fubini_step f xs ys
    end
#pop-options

(* ============================================================ *)
(*  Section F.2: sum_over_fns_to_pointwise                      *)
(* ============================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let sum_over_fns_to_pointwise
  (#t: Type) {| acg: add_comm_group t |}
  (n m: nat) (f g: fin_map n m -> t)
  : Lemma (requires (forall (phi: fin_map n m). f phi = g phi))
          (ensures sum_over_fns_to n m f = sum_over_fns_to n m g)
  = sum_list_map_congruence f g (all_fns_to n m) (fun _ -> ())
#pop-options
(* ============================================================ *)
(*  Section G: perm_product_expand                              *)
(* ============================================================ *)

let phi_pp_term (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n) : t
  = phi_prod a phi * perm_product (phi_matrix b phi) sigma

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let perm_product_expand
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (perm_product (matrix_mul a b) sigma
           = sum_over_fns_to n n (phi_pp_term a b sigma))
  = H.elim_equatable_laws t ();
    perm_product_to_sum_over_fns a b sigma;
    let pw (phi: fin_map n n)
      : Lemma (phi_outer a b sigma phi = phi_pp_term a b sigma phi)
      = phi_outer_eq_a_prod_perm_product a b sigma phi
    in
    Classical.forall_intro pw;
    sum_over_fns_to_pointwise n n (phi_outer a b sigma) (phi_pp_term a b sigma);
    transitivity
      (perm_product (matrix_mul a b) sigma)
      (sum_over_fns_to n n (phi_outer a b sigma))
      (sum_over_fns_to n n (phi_pp_term a b sigma))
#pop-options

(* ============================================================ *)
(*  Section H: leibniz_expand                                   *)
(* ============================================================ *)

let phi_lt_term (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n) : t
  = phi_prod a phi * leibniz_term (phi_matrix b phi) sigma

let neg_phi_pp_term (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) (phi: fin_map n n) : t
  = -(phi_pp_term a b sigma phi)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let leibniz_expand
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n)
  : Lemma (leibniz_term (matrix_mul a b) sigma
           = sum_over_fns_to n n (phi_lt_term a b sigma))
  = H.elim_equatable_laws t ();
    perm_product_expand a b sigma;
    if parity sigma then begin
      let pw (phi: fin_map n n)
        : Lemma (phi_pp_term a b sigma phi = phi_lt_term a b sigma phi)
        = reflexivity (phi_pp_term a b sigma phi)
      in
      Classical.forall_intro pw;
      sum_over_fns_to_pointwise n n (phi_pp_term a b sigma) (phi_lt_term a b sigma);
      transitivity
        (leibniz_term (matrix_mul a b) sigma)
        (sum_over_fns_to n n (phi_pp_term a b sigma))
        (sum_over_fns_to n n (phi_lt_term a b sigma))
    end else begin
      neg_congruence
        (perm_product (matrix_mul a b) sigma)
        (sum_over_fns_to n n (phi_pp_term a b sigma));
      sum_list_map_neg
        (phi_pp_term a b sigma)
        (all_fns_to n n);
      let pw (phi: fin_map n n)
        : Lemma (neg_phi_pp_term a b sigma phi = phi_lt_term a b sigma phi)
        = ring_neg_xy_is_x_times_neg_y (phi_prod a phi) (perm_product (phi_matrix b phi) sigma)
      in
      Classical.forall_intro pw;
      sum_list_map_congruence
        (neg_phi_pp_term a b sigma)
        (phi_lt_term a b sigma)
        (all_fns_to n n) (fun _ -> ());
      let pp_fn = phi_pp_term a b sigma in
      sum_list_map_neg pp_fn (all_fns_to n n);
      (* gives: sum_list (L.map (pointwise_neg pp_fn) xs) = neg (sum_list (L.map pp_fn xs)) *)
      let lambda_eq (phi: fin_map n n)
        : Lemma (pointwise_neg pp_fn phi = neg_phi_pp_term a b sigma phi)
        = pointwise_neg_unfold pp_fn phi
      in
      Classical.forall_intro lambda_eq;
      sum_list_map_congruence
        (pointwise_neg pp_fn)
        (neg_phi_pp_term a b sigma)
        (all_fns_to n n) (fun _ -> ());
      symmetry
        (sum_list (L.map (pointwise_neg pp_fn) (all_fns_to n n)))
        (sum_list (L.map (neg_phi_pp_term a b sigma) (all_fns_to n n)));
      transitivity
        (sum_list (L.map (neg_phi_pp_term a b sigma) (all_fns_to n n)))
        (sum_list (L.map (pointwise_neg pp_fn) (all_fns_to n n)))
        (- (sum_list (L.map pp_fn (all_fns_to n n))));
      assert (sum_list (L.map (neg_phi_pp_term a b sigma) (all_fns_to n n))
              = (- (sum_over_fns_to n n (phi_pp_term a b sigma))));
      symmetry
        (sum_list (L.map (neg_phi_pp_term a b sigma) (all_fns_to n n)))
        (- (sum_over_fns_to n n (phi_pp_term a b sigma)));
      transitivity
        (- (sum_over_fns_to n n (phi_pp_term a b sigma)))
        (sum_list (L.map (neg_phi_pp_term a b sigma) (all_fns_to n n)))
        (sum_over_fns_to n n (phi_lt_term a b sigma));
      assert (leibniz_term (matrix_mul a b) sigma
              = (- (sum_over_fns_to n n (phi_pp_term a b sigma))));
      transitivity
        (leibniz_term (matrix_mul a b) sigma)
        (- (sum_over_fns_to n n (phi_pp_term a b sigma)))
        (sum_over_fns_to n n (phi_lt_term a b sigma))
    end
#pop-options

(* ============================================================ *)
(*  Section I: factor_inner_perm_sum + det_expand               *)
(* ============================================================ *)

let phi_det_term (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n) : t
  = phi_prod a phi * det (phi_matrix b phi)

(* Helper: for fixed phi, summing phi_lt_term over sigma in all_permutations n
   equals phi_det_term. *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let factor_inner_perm_sum
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n)
  : Lemma (sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n))
           = phi_det_term a b phi)
  = H.elim_equatable_laws t ();
    let c = phi_prod a phi in
    let lt = leibniz_term (phi_matrix b phi) in
    sum_list_map_mul_left c lt (all_permutations n);
    (* c * sum_list (map lt ps) = sum_list (map (pointwise_mul (const c) lt) ps) *)
    let pw (sigma: permutation n)
      : Lemma (pointwise_mul (const c) lt sigma = swap_args (phi_lt_term a b) phi sigma)
      = pointwise_mul_unfold (const c) lt sigma;
        const_unfold c sigma;
        swap_args_unfold (phi_lt_term a b) phi sigma
    in
    Classical.forall_intro pw;
    sum_list_map_congruence
      (pointwise_mul (const c) lt)
      (swap_args (phi_lt_term a b) phi)
      (all_permutations n) (fun _ -> ());
    symmetry
      (sum_list (L.map (pointwise_mul (const c) lt) (all_permutations n)))
      (sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n)));
    symmetry (c * sum_list (L.map lt (all_permutations n)))
             (sum_list (L.map (pointwise_mul (const c) lt) (all_permutations n)));
    transitivity
      (sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n)))
      (sum_list (L.map (pointwise_mul (const c) lt) (all_permutations n)))
      (c * sum_list (L.map lt (all_permutations n)));
    leibniz_term_respects_perm_eq (phi_matrix b phi);
    Classical.forall_intro (all_permutations_count_one n);
    sum_over_perms_via_count_one_list lt (all_permutations n) (fun _ -> ());
    mul_congruence c (sum_list (L.map lt (all_permutations n)))
                   c (sum_over_perms n lt);
    transitivity
      (sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n)))
      (c * sum_list (L.map lt (all_permutations n)))
      (c * sum_over_perms n lt);
    det_unfold (phi_matrix b phi);
    H.leibniz_to_eq (det (phi_matrix b phi)) (sum_over_perms n lt);
    mul_congruence c (sum_over_perms n lt) c (det (phi_matrix b phi));
    transitivity
      (sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n)))
      (c * sum_over_perms n lt)
      (c * det (phi_matrix b phi))
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let det_expand
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n)
  : Lemma (det (matrix_mul a b) = sum_over_fns_to n n (phi_det_term a b))
  = H.elim_equatable_laws t ();
    det_unfold (matrix_mul a b);
    H.leibniz_to_eq (det (matrix_mul a b))
                    (sum_over_perms n (leibniz_term (matrix_mul a b)));
    leibniz_term_respects_perm_eq (matrix_mul a b);
    Classical.forall_intro (all_permutations_count_one n);
    sum_over_perms_via_count_one_list
      (leibniz_term (matrix_mul a b)) (all_permutations n) (fun _ -> ());
    transitivity
      (det (matrix_mul a b))
      (sum_over_perms n (leibniz_term (matrix_mul a b)))
      (sum_list (L.map (leibniz_term (matrix_mul a b)) (all_permutations n)));
    let pw_sigma (sigma: permutation n)
      : Lemma (leibniz_term (matrix_mul a b) sigma
               = inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n) sigma)
      = leibniz_expand a b sigma;
        assert (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n) sigma
                == sum_over_fns_to n n (phi_lt_term a b sigma))
          by (FStar.Tactics.compute (); FStar.Tactics.trefl ());
        H.leibniz_to_eq
          (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n) sigma)
          (sum_over_fns_to n n (phi_lt_term a b sigma));
        symmetry
          (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n) sigma)
          (sum_over_fns_to n n (phi_lt_term a b sigma));
        transitivity
          (leibniz_term (matrix_mul a b) sigma)
          (sum_over_fns_to n n (phi_lt_term a b sigma))
          (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n) sigma)
    in
    Classical.forall_intro pw_sigma;
    sum_list_map_congruence
      (leibniz_term (matrix_mul a b))
      (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n))
      (all_permutations n) (fun _ -> ());
    transitivity
      (det (matrix_mul a b))
      (sum_list (L.map (leibniz_term (matrix_mul a b)) (all_permutations n)))
      (sum_list (L.map (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n))
                       (all_permutations n)));
    sum_list_fubini #(permutation n) #(fin_map n n)
      (phi_lt_term a b) (all_permutations n) (all_fns_to n n);
    transitivity
      (det (matrix_mul a b))
      (sum_list (L.map (inner_sum_x_branch (phi_lt_term a b) (all_fns_to n n))
                       (all_permutations n)))
      (sum_list (L.map (inner_sum_y_branch (phi_lt_term a b) (all_permutations n))
                       (all_fns_to n n)));
    let pw_phi (phi: fin_map n n)
      : Lemma (inner_sum_y_branch (phi_lt_term a b) (all_permutations n) phi
               = phi_det_term a b phi)
      = factor_inner_perm_sum a b phi
        (* factor_inner_perm_sum gives:
           sum_list (L.map (swap_args (phi_lt_term a b) phi) (all_permutations n))
             = phi_det_term a b phi.
           inner_sum_y_branch unfolds to the same shape. *)
    in
    Classical.forall_intro pw_phi;
    sum_list_map_congruence
      (inner_sum_y_branch (phi_lt_term a b) (all_permutations n))
      (phi_det_term a b)
      (all_fns_to n n) (fun _ -> ());
    transitivity
      (det (matrix_mul a b))
      (sum_list (L.map (inner_sum_y_branch (phi_lt_term a b) (all_permutations n))
                       (all_fns_to n n)))
      (sum_over_fns_to n n (phi_det_term a b))
#pop-options

(* ============================================================ *)
(*  Section J: Combinatorial machinery — fin_map <-> permutation. *)
(* ============================================================ *)

private let rec fn_to_eq_from (#n #m: nat) (f g: fin_map n m) (k: nat)
  : Tot bool (decreases (n - k))
  = if k >= n then true
    else if f (k <: fin n) = g (k <: fin n)
         then fn_to_eq_from f g ((k ++ 1))
         else false

private let fn_to_eq_b (#n #m: nat) (f g: fin_map n m) : bool = fn_to_eq_from f g 0

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
private let rec fn_to_eq_b_spec (#n #m: nat) (f g: fin_map n m) (k: nat)
  : Lemma (ensures (if fn_to_eq_from f g k
                    then forall (i: fin n). (i <: nat) >= k ==> f i == g i
                    else exists (i: fin n). (i <: nat) >= k /\ ~(f i == g i)))
          (decreases (n - k))
  = if k >= n then ()
    else if f (k <: fin n) = g (k <: fin n)
         then fn_to_eq_b_spec f g ((k ++ 1))
         else ()
#pop-options

private let rec fn_eq_count (#n #m: nat) (f: fin_map n m) (xs: list (fin_map n m))
  : Tot nat (decreases xs)
  = match xs with
    | [] -> 0
    | h :: tl -> ((if fn_to_eq_b f h then 1 else 0) ++ (fn_eq_count f tl))

private let all_funs (n: pos) : list (fin_map n n) = all_fns_to n n

private let sum_over_funs (#t: Type) {| g: add_comm_group t |} (n: pos)
  (h: fin_map n n -> t) : t
  = sum_over_fns_to n n h

private let rec fn_eq_count_append (#n #m: nat) (f: fin_map n m) (xs ys: list (fin_map n m))
  : Lemma (ensures fn_eq_count f (L.append xs ys) ==
           ((fn_eq_count f xs) ++ (fn_eq_count f ys)))
          (decreases xs)
  = match xs with
    | [] -> ()
    | _ :: tl -> fn_eq_count_append f tl ys

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let fn_to_eq_b_extend (#k #m: nat) (f: fin_map ((k ++ 1)) m)
  (phi: fin_map k m) (j: fin m)
  : Lemma (fn_to_eq_b f (extend_fn phi j) ==
           (f k = j && fn_to_eq_b (restrict_fn f) phi))
  = fn_to_eq_b_spec f (extend_fn phi j) 0;
    fn_to_eq_b_spec (restrict_fn f) phi 0
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 60"
private let rec all_fins_from_mem (m: nat) (k: nat{k <= m}) (x: fin m)
  : Lemma (ensures L.mem x (all_fins_from m k) == (x >= k))
          (decreases ((m - k)))
  = if k = m then ()
    else all_fins_from_mem m ((k ++ 1)) x

private let rec all_fins_from_noRepeats (m: nat) (k: nat{k <= m})
  : Lemma (ensures L.noRepeats (all_fins_from m k))
          (decreases ((m - k)))
  = if k = m then ()
    else begin
      all_fins_from_noRepeats m ((k ++ 1));
      all_fins_from_mem m ((k ++ 1)) (k <: fin m)
    end
#pop-options

private let all_fins_noRepeats (m: nat) : Lemma (L.noRepeats (all_fins m))
  = all_fins_from_noRepeats m 0

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec fn_eq_count_map_extend (#k #m: nat)
  (f: fin_map ((k ++ 1)) m) (phi: fin_map k m) (js: list (fin m))
  : Lemma (requires L.noRepeats js)
          (ensures fn_eq_count f
             (L.map (extend_fn phi) js) ==
           (if fn_to_eq_b (restrict_fn f) phi
               && L.mem (f k) js
            then 1 else 0))
          (decreases js)
  = match js with
    | [] -> ()
    | j :: rest ->
      fn_to_eq_b_extend f phi j;
      fn_eq_count_map_extend f phi rest
#pop-options

#push-options "--fuel 8 --ifuel 4 --z3rlimit 80"
private let all_fns_to_succ_list_cons (#k m: nat)
  (phi: fin_map k m) (tl: list (fin_map k m))
  : Lemma (all_fns_to_succ_list m (phi :: tl) ==
           L.append (extend_to_all phi)
                    (all_fns_to_succ_list m tl))
  = ()
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec fn_eq_count_succ (#k #m: nat)
  (f: fin_map ((k ++ 1)) m) (xs: list (fin_map k m))
  : Lemma (ensures fn_eq_count f (all_fns_to_succ_list m xs) ==
                   fn_eq_count (restrict_fn f) xs)
          (decreases xs)
  = match xs with
    | [] -> ()
    | phi :: tl ->
        all_fns_to_succ_list_cons m phi tl;
        fn_eq_count_append f
          (extend_to_all phi)
          (all_fns_to_succ_list m tl);
        all_fins_noRepeats m;
        all_fins_from_mem m 0 (f k);
        fn_eq_count_map_extend f phi (all_fins m);
        fn_eq_count_succ f tl
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let rec all_fns_to_count_one (n m: nat) (f: fin_map n m)
  : Lemma (ensures fn_eq_count f (all_fns_to n m) == 1)
          (decreases n)
  = if n = 0 then
      fn_to_eq_b_spec f (nullary m) 0
    else begin
      let k = (n - 1) in
      all_fns_to_count_one k m (restrict_fn f);
      all_fns_to_succ_eq k m;
      fn_eq_count_succ f (all_fns_to k m)
    end
#pop-options

private let is_injective_b_of_injective (#n: pos) (phi: fin_map n n)
  : Lemma (requires forall (i j: fin n). phi i == phi j ==> i == j)
          (ensures is_injective_b phi == true)
  = if n = 0 then ()
    else if is_injective_b phi then ()
    else begin is_injective_false phi; assert False end

private let perm_of_inj_fn (#n: pos) (phi: fin_map n n{is_injective_b phi})
  : (q: permutation n{forall (i: fin n). q.fwd i == phi i})
  = is_injective_true phi;
    perm_of_injective_fn phi ()

private let rec perm_list_from_funs (#n: pos) (xs: list (fin_map n n))
  : Tot (list (permutation n)) (decreases xs)
  = match xs with
    | [] -> []
    | phi :: tl ->
      if is_injective_b phi
      then perm_of_inj_fn phi :: perm_list_from_funs tl
      else perm_list_from_funs tl

private let perm_list_from_funs_cons_inj (#n: pos) (phi: fin_map n n)
  (tl: list (fin_map n n))
  : Lemma (requires is_injective_b phi)
          (ensures perm_list_from_funs (phi :: tl) ==
                   perm_of_inj_fn phi :: perm_list_from_funs tl)
  = ()

private let perm_list_from_funs_cons_non (#n: pos) (phi: fin_map n n)
  (tl: list (fin_map n n))
  : Lemma (requires not (is_injective_b phi))
          (ensures perm_list_from_funs (phi :: tl) == perm_list_from_funs tl)
  = ()

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let fn_eq_perm_eq_bridge (#n: pos) (p: permutation n)
  (phi: fin_map n n) (q: permutation n{forall (i: fin n). q.fwd i == phi i})
  : Lemma (fn_to_eq_b p.fwd phi == perm_eq p q)
  = fn_to_eq_b_spec p.fwd phi 0;
    if fn_to_eq_b p.fwd phi then begin
      let aux (i: fin n) : Lemma (p.fwd i == q.fwd i) = () in
      Classical.forall_intro aux;
      perm_eq_intro p q aux
    end
    else if perm_eq p q then begin
      let aux (i: fin n) : Lemma (p.fwd i == phi i) =
        perm_eq_elim p q i in
      Classical.forall_intro aux
    end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
private let fn_eq_implies_injective (#n: pos) (p: permutation n)
  (phi: fin_map n n)
  : Lemma (requires forall (i: fin n). p.fwd i == phi i)
          (ensures forall (i j: fin n). phi i == phi j ==> i == j)
  = let aux (i j: fin n) : Lemma (requires phi i == phi j) (ensures i == j) =
      p.bwd_fwd_id i; p.bwd_fwd_id j
    in
    let aux2 (i j: fin n) : Lemma (phi i == phi j ==> i == j) =
      Classical.move_requires (aux i) j
    in
    Classical.forall_intro_2 aux2
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec perm_count_from_funs (#n: pos) (p: permutation n)
  (xs: list (fin_map n n))
  : Lemma (ensures perm_eq_count p (perm_list_from_funs xs) ==
                   fn_eq_count p.fwd xs)
          (decreases xs)
  = match xs with
    | [] ->
      perm_eq_count_nil p
    | phi :: tl ->
      perm_count_from_funs p tl;
      if is_injective_b phi
      then begin
        let q = perm_of_inj_fn phi in
        perm_list_from_funs_cons_inj phi tl;
        perm_eq_count_cons p q (perm_list_from_funs tl);
        fn_eq_perm_eq_bridge p phi q
      end
      else begin
        perm_list_from_funs_cons_non phi tl;
        fn_to_eq_b_spec p.fwd phi 0;
        if fn_to_eq_b p.fwd phi then begin
          fn_eq_implies_injective p phi;
          is_injective_b_of_injective phi
        end
      end
#pop-options

#push-options "--fuel 4 --ifuel 2 --z3rlimit 80"
private let rec sum_filter_eq
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (f: permutation n -> t) (g: fin_map n n -> t) (xs: list (fin_map n n))
  : Lemma
      (requires forall (phi: fin_map n n).
        g phi == (if is_injective_b phi then f (perm_of_inj_fn phi) else zero))
      (ensures sum_list (L.map g xs) = sum_list (L.map f (perm_list_from_funs xs)))
      (decreases xs)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match xs with
    | [] ->
      sum_list_nil #t #(cr.cr_r.r_add)
    | phi :: tl ->
      sum_filter_eq f g tl;
      sum_list_cons (g phi) (L.map g tl);
      if is_injective_b phi
      then begin
        perm_list_from_funs_cons_inj phi tl;
        sum_list_cons (f (perm_of_inj_fn phi)) (L.map f (perm_list_from_funs tl));
        add_congruence (g phi) (sum_list (L.map g tl))
                       (g phi) (sum_list (L.map f (perm_list_from_funs tl)))
      end
      else begin
        perm_list_from_funs_cons_non phi tl;
        let s = sum_list (L.map g tl) in
        add_zero s;
        transitivity (g phi + s) s (sum_list (L.map f (perm_list_from_funs tl)))
      end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let sum_funs_eq_perms
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (f: permutation n -> t) (g: fin_map n n -> t)
  : Lemma
      (requires respects_perm_eq f /\
               (forall (phi: fin_map n n).
                 g phi == (if is_injective_b phi then f (perm_of_inj_fn phi) else zero)))
      (ensures sum_over_funs n g = sum_over_perms n f)
  = let perm_list = perm_list_from_funs (all_funs n) in
    sum_filter_eq f g (all_funs n);
    let count_one (p: permutation n) : Lemma (perm_eq_count p perm_list == 1)
      = perm_count_from_funs p (all_funs n);
        all_fns_to_count_one n n p.fwd
    in
    Classical.forall_intro count_one;
    sum_over_perms_via_count_one_list f perm_list (fun _ -> ());
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    transitivity (sum_over_funs n g) (sum_list (L.map f perm_list)) (sum_over_perms n f)
#pop-options
(* ============================================================ *)
(*  Section K: phi_term split — injective vs non-injective.    *)
(* ============================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let phi_term_non_inj
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n)
  : Lemma (requires is_injective_b phi = false)
          (ensures phi_det_term a b phi = zero)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if n = 0 then
      assert (is_injective_b phi = true)
    else begin
      is_injective_false phi;
      let wit (i j: fin n)
        : Lemma (requires ~(i == j) /\ phi i == phi j)
                (ensures det (phi_matrix b phi) = zero)
        = det_phi_matrix_non_inj b phi i j
      in
      let wit2 (i: fin n) : (j: fin n) -> Lemma ((~(i == j) /\ phi i == phi j) ==> det (phi_matrix b phi) = zero) =
        Classical.move_requires (wit i)
      in
      Classical.forall_intro_2 wit2;
      H.x_mul_zero (phi_prod a phi);
      mul_congruence (phi_prod a phi) (det (phi_matrix b phi))
                     (phi_prod a phi) (zero <: t);
      transitivity (phi_det_term a b phi)
                   (phi_prod a phi * zero)
                   (zero <: t)
    end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let pa_eq_perm_product
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a: square_matrix t n) (phi: fin_map n n)
  : Lemma (requires is_injective_b phi = true)
          (ensures phi_prod a phi = perm_product a (perm_of_inj_fn phi))
  = H.elim_equatable_laws t ();
    is_injective_true phi;
    let p = perm_of_inj_fn phi in
    perm_product_unfold a p;
    let pwd (i: fin n) : Lemma (apply_along a phi i = apply_along a p.fwd i)
      = apply_along_unfold a phi i;
        apply_along_unfold a p.fwd i in
    fin_prod_congruence (apply_along a phi) (apply_along a p.fwd) pwd
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let phi_term_inj
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n)
  : Lemma (requires is_injective_b phi = true)
          (ensures phi_det_term a b phi =
                   leibniz_term a (perm_of_inj_fn phi) * det b)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    is_injective_true phi;
    let p = perm_of_inj_fn phi in
    pa_eq_perm_product a phi;
    det_phi_matrix_inj b phi ();
    if parity p then begin
      mul_congruence (phi_prod a phi) (det (phi_matrix b phi))
                     (perm_product a p) (det b)
    end else begin
      mul_congruence (phi_prod a phi) (det (phi_matrix b phi))
                     (perm_product a p) (-(det b));
      ring_neg_xy_is_x_times_neg_y (perm_product a p) (det b);
      symmetry (-(perm_product a p * det b))
               (perm_product a p * (-(det b)));
      transitivity (phi_det_term a b phi)
                   (perm_product a p * (-(det b)))
                   (-(perm_product a p * det b));
      ring_neg_xy_is_neg_x_times_y (perm_product a p) (det b);
      transitivity (phi_det_term a b phi)
                   (-(perm_product a p * det b))
                   ((-(perm_product a p)) * det b)
    end
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let phi_term_value
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n)
  : Lemma (phi_det_term a b phi =
           (if is_injective_b phi
            then leibniz_term a (perm_of_inj_fn phi) * det b
            else zero))
  = if is_injective_b phi
    then phi_term_inj a b phi
    else phi_term_non_inj a b phi
#pop-options

(* ============================================================ *)
(*  Section L: det_expand_to_perms                              *)
(* ============================================================ *)

private let lt_det_b
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) : t
  = leibniz_term a sigma * det b

private let lt_det_b_filtered
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (phi: fin_map n n) : t
  = if is_injective_b phi
    then lt_det_b a b (perm_of_inj_fn phi)
    else zero

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
private let det_expand_to_perms
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n)
  : Lemma (sum_over_fns_to n n (phi_det_term a b)
           = sum_over_perms n (lt_det_b a b))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let f = lt_det_b a b in
    let h = lt_det_b_filtered a b in
    let pw (phi: fin_map n n)
      : Lemma (phi_det_term a b phi = h phi)
      = phi_term_value a b phi
    in
    Classical.forall_intro pw;
    sum_list_map_congruence
      (phi_det_term a b)
      h (all_fns_to n n) (fun _ -> ());
    leibniz_term_respects_perm_eq a;
    let rpe_prod (p q: permutation n)
      : Lemma (requires perm_eq p q)
              (ensures f p = f q)
      = respects_perm_eq_elim (leibniz_term a) p q;
        mul_congruence (leibniz_term a p) (det b) (leibniz_term a q) (det b)
    in
    let rpe_prod2 (p: permutation n) : (q: permutation n) -> Lemma (perm_eq p q ==> f p = f q) =
      Classical.move_requires (rpe_prod p)
    in
    Classical.forall_intro_2 rpe_prod2;
    respects_perm_eq_intro f (fun _ _ -> ());
    sum_funs_eq_perms f h;
    transitivity
      (sum_over_fns_to n n (phi_det_term a b))
      (sum_over_funs n h)
      (sum_over_perms n f)
#pop-options

(* ============================================================ *)
(*  Section M: det_mul — the headline theorem.                  *)
(* ============================================================ *)

private let db_lt_a
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (sigma: permutation n) : t
  = det b * leibniz_term a sigma

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let det_mul
  (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n)
  : Lemma (det (matrix_mul a b) = det a * det b)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    det_expand a b;
    det_expand_to_perms a b;
    transitivity (det (matrix_mul a b))
                 (sum_over_fns_to n n (phi_det_term a b))
                 (sum_over_perms n (lt_det_b a b));
    let comm_step (sigma: permutation n)
      : Lemma (lt_det_b a b sigma = db_lt_a a b sigma)
      = mul_commutativity (leibniz_term a sigma) (det b)
    in
    Classical.forall_intro comm_step;
    sum_over_perms_congruence n (lt_det_b a b) (db_lt_a a b) (fun _ -> ());
    transitivity (det (matrix_mul a b))
                 (sum_over_perms n (lt_det_b a b))
                 (sum_over_perms n (db_lt_a a b));
    sum_over_perms_mul_left_named n (det b) (db_lt_a a b) (leibniz_term a) (fun _ -> ());
    transitivity (det (matrix_mul a b))
                 (sum_over_perms n (db_lt_a a b))
                 (det b * sum_over_perms n (leibniz_term a));
    det_unfold a;
    mul_congruence (det b) (sum_over_perms n (leibniz_term a))
                   (det b) (det a);
    transitivity (det (matrix_mul a b))
                 (det b * sum_over_perms n (leibniz_term a))
                 (det b * det a);
    mul_commutativity (det b) (det a);
    transitivity (det (matrix_mul a b))
                 (det b * det a)
                 (det a * det b)
#pop-options


(* ================================================================== *)
(*  MERGED FROM Core.Matrix.Triangular                                 *)

(* ================================================================== *)

(* Triangular originally relied on F* default options (fuel 2 / ifuel 1).
   The preceding merged sections leave fuel 1 active, so restore here. *)
#push-options "--fuel 2 --ifuel 1"

(* ================================================================ *)
(*  Diagonal product and triangularity.                              *)
(* ================================================================ *)

(* diagonal_product_from / diagonal_product / is_lower_triangular are
   declared concretely in the .fsti (merged from Triangular); not redefined here. *)

(* ================================================================ *)
(*  Base case: determinant of a 1x1 matrix is its single entry.      *)
(* ================================================================ *)

let determinant_size_one (#t:Type) {| cr: commutative_ring t |} (m: square_matrix t 1)
  : Lemma (det m = m (0 <: fin 1) (0 <: fin 1))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let f = leibniz_term m in
    let p0 : permutation 1 = identity 1 in
    leibniz_term_respects_perm_eq m;
    let h_zero (q: permutation 1)
      : Lemma (requires ~(perm_eq p0 q)) (ensures f q = (zero <: t))
      = perm_eq_intro p0 q (fun i -> identity_fwd 1 i)   (* size 1: every perm agrees with identity, contra *)
    in
    sum_over_perms_single 1 f p0 h_zero;            (* sum_over_perms 1 f = f p0 *)
    det_unfold m;                                    (* det m == sum_over_perms 1 f *)
    parity_identity 1;                               (* parity p0 == true, so f p0 = perm_product m p0 *)
    perm_product_unfold m p0;                        (* perm_product m p0 == prod_range (...) 0 1 *)
    let body : nat -> t = fun k -> if k < 1 then m (k <: fin 1) (p0.fwd (k <: fin 1)) else one in
    prod_range_unfold_left body 0 1;                 (* = body 0 * prod_range body 1 1 *)
    prod_range_empty body 1 1;                       (* prod_range body 1 1 == one *)
    H.x_mul_one (body 0);                            (* body 0 * one = body 0 *)
    mul_congruence (body 0) (prod_range body 1 1) (body 0) (one <: t);
    (* body 0 == m 0 (p0.fwd 0) == m 0 0 ; chain det m = ... = m 0 0 *)
    transitivity (det m) (prod_range body 0 1) (m (0 <: fin 1) (0 <: fin 1))

(* ================================================================ *)
(*  The (0,0) minor of a lower-triangular matrix is lower-triangular. *)
(* ================================================================ *)

let minor_zero_zero_lower_triangular (#t:Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n)
  : Lemma (requires is_lower_triangular m)
          (ensures  is_lower_triangular (minor m (0 <: fin n) (0 <: fin n)))
  = ()                                              (* minor[a][b] = m (skip 0 a)(skip 0 b) = m (a+1)(b+1); b>a => b+1>a+1 *)

(* ================================================================ *)
(*  Cofactor expansion along row 0 collapses to the corner term.     *)
(* ================================================================ *)

(* Off-diagonal cofactors of row 0 vanish (the entry m[0][k] is zero for k>0). *)
let cofactor_row_zero_off_diagonal (#t:Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n) (k: fin n)
  : Lemma (requires is_lower_triangular m /\ (k <: nat) > 0)
          (ensures  cofactor_term m (0 <: fin n) k = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let i0 : fin n = 0 <: fin n in
    let mp = minus_one_pow #t #cr (((i0 <: nat) ++ (k <: nat))) in
    let dm = det (minor m i0 k) in
    assert (m i0 k = (zero <: t));                   (* lower-triangular, k > 0 *)
    mul_congruence mp (m i0 k) mp (zero <: t);
    H.x_mul_zero mp;
    mul_congruence (mp * m i0 k) dm (zero <: t) dm;
    H.zero_mul_x dm;
    transitivity ((mp * m i0 k) * dm) ((zero <: t) * dm) (zero <: t)

let cofactor_row_zero_collapses (#t:Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n)
  : Lemma (requires is_lower_triangular m)
          (ensures  fin_sum (cofactor_term m (0 <: fin n))
                  = cofactor_term m (0 <: fin n) (0 <: fin n))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let agree (k: fin n)
      : Lemma (cofactor_term m (0 <: fin n) k
             = pointwise_mul (fin_kronecker_delta (0 <: fin n)) (cofactor_term m (0 <: fin n)) k)
      = if (k <: nat) = 0 then
          H.one_mul_x (cofactor_term m (0 <: fin n) k)   (* delta = one: term = one * cof = cof *)
        else begin
          cofactor_row_zero_off_diagonal m k;            (* cofactor = zero (k > 0) *)
          H.zero_mul_x (cofactor_term m (0 <: fin n) k)  (* delta = zero: term = zero * cof = zero *)
        end
    in
    fin_sum_congruence (cofactor_term m (0 <: fin n))
                       (pointwise_mul (fin_kronecker_delta (0 <: fin n)) (cofactor_term m (0 <: fin n)))
                       agree;
    fin_sum_kronecker (0 <: fin n) (cofactor_term m (0 <: fin n));
    transitivity (fin_sum (cofactor_term m (0 <: fin n)))
                 (fin_sum (pointwise_mul (fin_kronecker_delta (0 <: fin n)) (cofactor_term m (0 <: fin n))))
                 (cofactor_term m (0 <: fin n) (0 <: fin n))

(* ================================================================ *)
(*  Diagonal of the (0,0) minor:  the tail of m's diagonal.          *)
(*    diagonal_product_from (minor m 0 0) j  =  diagonal_product_from m (j+1) *)
(* ================================================================ *)

let rec diagonal_from_minor (#t:Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n) (j: nat{j <= n - 1})
  : Lemma (ensures diagonal_product_from (minor m (0 <: fin n) (0 <: fin n)) j
                 = diagonal_product_from m ((j ++ 1)))
          (decreases (n - 1 - j))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let mm = minor m (0 <: fin n) (0 <: fin n) in
    if j >= n - 1 then ()                              (* both products are empty = one *)
    else begin
      diagonal_from_minor m ((j ++ 1));   (* IH: tail of minor = tail of m *)
      (* mm[j][j] = m (skip 0 j)(skip 0 j) = m[j+1][j+1] *)
      mul_congruence (mm (j <: fin (n - 1)) (j <: fin (n - 1)))
                     (diagonal_product_from mm ((j ++ 1)))
                     (m ((j ++ 1) <: fin n) ((j ++ 1) <: fin n))
                     (diagonal_product_from m ((j ++ 2)))
    end

(* ================================================================ *)
(*  diagonal_product m = m[0][0] * diagonal_product (minor m 0 0).    *)
(* ================================================================ *)

let diagonal_product_peel (#t:Type) {| cr: commutative_ring t |}
  (#n: pos{n > 1}) (m: square_matrix t n)
  : Lemma (diagonal_product m
         = m (0 <: fin n) (0 <: fin n)
           * diagonal_product (minor m (0 <: fin n) (0 <: fin n)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    (* diagonal_product m = diagonal_product_from m 0 = m[0][0] * diagonal_product_from m 1 (n>1) *)
    diagonal_from_minor m 0;                           (* diag_from (minor) 0 = diag_from m 1 *)
    mul_congruence (m (0 <: fin n) (0 <: fin n)) (diagonal_product_from m 1)
                   (m (0 <: fin n) (0 <: fin n))
                   (diagonal_product_from (minor m (0 <: fin n) (0 <: fin n)) 0)

(* ================================================================ *)
(*  Main theorem.                                                    *)
(* ================================================================ *)

let rec det_lower_triangular (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m: square_matrix t n)
  : Lemma (requires is_lower_triangular m)
          (ensures  det m = diagonal_product m)
          (decreases n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    mul_one (m 0 0);
    if n = 1 then determinant_size_one m                        (* det m = m 0 0 *)      
    else begin
      det_laplace_row m 0;                (* det m = fin_sum (cofactor_term m 0) *)
      cofactor_row_zero_collapses m;                 (* fin_sum = cofactor_term m 0 0 *)
      minor_zero_zero_lower_triangular m;            (* minor m 0 0 is lower-triangular *)
      det_lower_triangular (minor m 0 0);   (* IH *)
      diagonal_product_peel m;                        (* diagonal_product m = m00 * diagonal_product(minor) *)
      (* cofactor_term m 0 0 = minus_one_pow 0 * m00 * det(minor) = m00 * det(minor) = m00 * diagonal_product(minor) *)
      let mm = minor m 0 0 in
      (* cofactor_term m 0 0 == (minus_one_pow 0 * m00) * det mm == (one * m00) * det mm *)      
      mul_congruence (one * m 0 0) (det mm)
                     (m 0 0) (det mm);   (* (one*m00)*det = m00*det *)
      mul_congruence (m 0 0) (det mm)
                     (m 0 0) (diagonal_product mm)
    end

(* ================================================================ *)
(*  diagonal_product depends only on the diagonal; upper-triangular  *)
(*  determinant (companion of the lower-triangular theorem).         *)
(* ================================================================ *)

let rec diagonal_product_from_pointwise (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m1 m2: square_matrix t n)
  (heq: squash (forall (i: fin n). m1 i i = m2 i i)) (k: nat{k <= n})
  : Lemma (ensures diagonal_product_from m1 k = diagonal_product_from m2 k)
          (decreases (n - k))
  = elim_equatable_laws t ();
    if k >= n then reflexivity #t one
    else begin    
      diagonal_product_from_pointwise m1 m2 heq ((k ++ 1));
      mul_congruence (m1 k k) (diagonal_product_from m1 ((k ++ 1)))
                     (m2 k k) (diagonal_product_from m2 ((k ++ 1)))
    end

let diagonal_product_pointwise (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m1 m2: square_matrix t n)
  : Lemma (requires forall (i: fin n). m1 i i = m2 i i)
          (ensures  diagonal_product m1 = diagonal_product m2)
  = diagonal_product_from_pointwise m1 m2 () 0

(* is_upper_triangular is declared concretely in the .fsti; not redefined here. *)

let det_upper_triangular (#t:Type) {| cr: commutative_ring t |}
  (#n: pos) (m: square_matrix t n)
  : Lemma (requires is_upper_triangular m)
          (ensures  det m = diagonal_product m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    det_transpose m;                                  (* det (transpose m) = det m *)
    det_lower_triangular (transpose m);               (* det (transpose m) = diagonal_product (transpose m) *)
    diagonal_product_pointwise (transpose m) m       (* same diagonal *)    
#pop-options

(* ================================================================== *)
(*  MERGED FROM Core.Matrix.KernelDet                                  *)

(* KernelDet + NullVec relied on F* default options (fuel 2 / ifuel 1)
   outside their own explicit #push-options blocks. *)
#push-options "--fuel 2 --ifuel 1"

(* ================================================================== *)

(* ================================================================== *)
(*  Part A: Right adjugate identity M · adj(M) = det(M) · I           *)
(*                                                                     *)
(*  Diagonal:   (M · adj(M))(i,i) = Σ_k M(i,k)·adj(M)(k,i)          *)
(*            = Σ_k M(i,k)·signed_cofactor(M,i,k)                     *)
(*            = Σ_k cofactor_term(M,i,k) = det M  (Laplace row i)     *)
(*                                                                     *)
(*  Off-diag:  (M · adj(M))(i,j) = Σ_k M(i,k)·signed_cofactor(M,j,k) *)
(*            = det(M with row j replaced by row i) = 0                *)
(*            (two equal rows ⟹ det=0)                                *)
(* ================================================================== *)

(* Row-replaced matrix: row j is replaced by row i. *)
let kd_row_replace (#t: Type) (#n: pos) (m: square_matrix t n) (src dst: fin n)
  : square_matrix t n
  = fun (r: fin n) (c: fin n) -> if (r <: nat) = (dst <: nat) then m src c else m r c

(* Row Laplace summand: M(i,k) * signed_cofactor(M, j, k). *)
let row_adj_summand (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (k: fin n) : t
  = m i k * signed_cofactor m j k

(* minor of kd_row_replace at the replaced row = minor of original *)
(* minor of kd_row_replace at the deleted row = minor of original.
   Key: deleting row dst from (kd_row_replace m src dst) leaves all other
   rows unchanged (they still come from m). *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let minor_row_replace_at_dst (#t: Type) (#n: pos{n > 1})
  (m: square_matrix t n) (src dst: fin n) (col: fin n)
  (a b: fin ((n - 1)))
  : Lemma (requires (src <> dst))
          (ensures  minor (kd_row_replace m src dst) dst col a b == minor m dst col a b)
  = skip_avoids dst a
#pop-options

(* Row-adj summand = cofactor_term of row-replaced matrix along row dst. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let row_adj_summand_eq_cofactor_of_replaced
  (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n) (k: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  row_adj_summand m i j k = cofactor_term (kd_row_replace m i j) j k)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    minor_row_replace_at_dst m i j k
      |> Classical.move_requires_2
      |> Classical.forall_intro_2;
    let mop = minus_one_pow (j ++ k) in
    let det_min = det (minor m j k) in
    let det_rep = det (minor (kd_row_replace m i j) j k) in
    let e = m i k in
    (* cofactor_term(replace, j, k) = (mop * e) * det_rep  [by definition]
       det_rep = det_min  [from det_pointwise_eq]
       row_adj_summand = e * (mop * det_min)  [by definition]
       Need: e * (mop * det_min) = (mop * e) * det_min *)    
    det_pointwise_eq (minor (kd_row_replace m i j) j k) (minor m j k);
    (* det_rep = det_min *)
    mul_congruence (mop * e) det_rep (mop * e) det_min;
    mul_commutativity mop e;
    mul_congruence (mop * e) det_min (e * mop) det_min;
    mul_associativity e mop det_min
#pop-options

(* The fake row Laplace sum is zero for i ≠ j. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let fake_row_laplace_zero (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires i <> j)
          (ensures  fin_sum (row_adj_summand m i j) = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    (* Σ_k row_adj_summand m i j k = Σ_k cofactor_term(replace, j, k) *)    
    row_adj_summand_eq_cofactor_of_replaced m i j
      |> Classical.move_requires
      |> Classical.forall_intro;
    fin_sum_congruence (row_adj_summand m i j)
                       (cofactor_term (kd_row_replace m i j) j) obvious;
    det_laplace_row (kd_row_replace m i j) j;
    det_two_equal_rows_cr (kd_row_replace m i j) i j;
    transitivity (fin_sum (row_adj_summand m i j))
                 (det (kd_row_replace m i j)) (zero <: t)
#pop-options

(* Right adjugate: (M · adj(M))(i,j) = 0 for i ≠ j. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let right_adj_off_diagonal (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires (i <: nat) <> (j <: nat))
          (ensures  matrix_mul m (adjugate m) i j = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    matrix_mul_to_fin_sum m (adjugate m) i j;
    H.leibniz_to_eq (matrix_mul m (adjugate m) i j)
                    (fin_sum (pointwise_mul (row m i) (col (adjugate m) j)));
    fin_sum_congruence (pointwise_mul (row m i) (col (adjugate m) j))
                       (row_adj_summand m i j) obvious;
    fake_row_laplace_zero m i j;
    transitivity (matrix_mul m (adjugate m) i j)
                 (fin_sum (pointwise_mul (row m i) (col (adjugate m) j)))
                 (fin_sum (row_adj_summand m i j));
    transitivity (matrix_mul m (adjugate m) i j)
                 (fin_sum (row_adj_summand m i j)) (zero <: t)
#pop-options

(* Right adjugate: (M · adj(M))(i,i) = det M. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 80"
let right_adj_diagonal (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i: fin n)
  : Lemma (matrix_mul m (adjugate m) i i = det m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    matrix_mul_to_fin_sum m (adjugate m) i i;
    H.leibniz_to_eq (matrix_mul m (adjugate m) i i)
                    (fin_sum #t #(acg_of_r t #cr.cr_r) #n
                      (pointwise_mul (row m i) (col (adjugate m) i)));
    (* Σ_k m(i,k) * adj(m)(k,i) = Σ_k m(i,k) * signed_cofactor(m,i,k)
       = Σ_k cofactor_term(m, i, k) = det m *)
    let pw (k: fin n)
      : Lemma (pointwise_mul (row m i) (col (adjugate m) i) k
             = cofactor_term m i k)
      = cofactor_term_eq_entry_times_signed_cofactor m i k
    in
    Classical.forall_intro pw;
    fin_sum_congruence (pointwise_mul (row m i) (col (adjugate m) i))
                       (cofactor_term m i) (fun _ -> ());
    det_laplace_row m i;
    transitivity (matrix_mul m (adjugate m) i i)
                 (fin_sum (pointwise_mul (row m i) (col (adjugate m) i)))
                 (fin_sum (cofactor_term m i));
    transitivity (matrix_mul m (adjugate m) i i)
                 (fin_sum (cofactor_term m i)) (det m)
#pop-options

(* Corollary: if det(M) = 0, then M · (column j of adj(M)) = zero vector. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let adj_column_in_kernel (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (j: fin n) (i: fin n)
  : Lemma (requires det m = (zero <: t))
          (ensures  matrix_mul m (adjugate m) i j = (zero <: t))
  = trans_for_calc t ();
    if i = j then right_adj_diagonal m i else right_adj_off_diagonal m i j
#pop-options

(* ================================================================== *)
(*  Part B: Column elimination                                        *)
(*                                                                     *)
(*  Given M with M(i₀,j₀) ≠ 0, eliminate all other entries in        *)
(*  column j₀ via row operations. The resulting matrix has column j₀  *)
(*  = M(i₀,j₀)·e_{i₀} and det unchanged.                            *)
(* ================================================================== *)

(* The eliminated matrix. *)
let elim_col (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r: fin n) (piv_c: fin n{is_nonzero (m piv_r piv_c)})
  : square_matrix t n
  = let pivot_inv : t = inv (m piv_r piv_c) in
    fun (i: fin n) (j: fin n) ->
      if (i <: nat) = (piv_r <: nat) then m i j
      else m i j -- (m i piv_c * pivot_inv) * m piv_r j

(* Column piv_c of eliminated matrix: zero except at pivot. *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
let elim_col_pivot (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n)
  : Lemma (requires is_nonzero (m piv_r piv_c))
          (ensures  elim_col m piv_r piv_c piv_r piv_c = m piv_r piv_c)
  = elim_equatable_laws t ();
    assert (elim_col m piv_r piv_c piv_r piv_c == m piv_r piv_c)
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
let elim_col_zero (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n) (i: fin n)
  : Lemma (requires is_nonzero (m piv_r piv_c) /\ (i <: nat) <> (piv_r <: nat))
          (ensures  elim_col m piv_r piv_c i piv_c = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let pivot_inv : t = inv (m piv_r piv_c) in
    let c : t = m i piv_c * pivot_inv in
    (* Need: c * pivot = m i piv_c *)
    inversion_lemma (m piv_r piv_c);
    (* inv(piv) * piv = one *)
    mul_associativity (m i piv_c) pivot_inv (m piv_r piv_c);
    (* (m i piv_c * inv(piv)) * piv = m i piv_c * (inv(piv) * piv) *)
    mul_congruence (m i piv_c) (pivot_inv * m piv_r piv_c)
                   (m i piv_c) (one <: t);
    (* m i piv_c * (inv(piv) * piv) = m i piv_c * one *)
    x_mul_one (m i piv_c);
    (* m i piv_c * one = m i piv_c *)
    transitivity (c * m piv_r piv_c) (m i piv_c * (pivot_inv * m piv_r piv_c))
                 (m i piv_c * (one <: t));
    (* c * pivot = m i piv_c *)
    neg_congruence (c * m piv_r piv_c) (m i piv_c);
    (* neg(c * pivot) = neg(m i piv_c) *)
    add_congruence (m i piv_c) (- (c * m piv_r piv_c))
                   (m i piv_c) (- (m i piv_c));
    (* m i piv_c + neg(c * pivot) = m i piv_c + neg(m i piv_c) *)
    x_plus_neg_x (m i piv_c)
    (* m i piv_c + neg(m i piv_c) = zero *)
#pop-options

(* Determinant of eliminated matrix equals original determinant.
   Each row operation is: row_i -= c * row_{piv_r}, which preserves det.
   We prove this for ONE row operation; the general case follows by induction
   over rows i ≠ piv_r. For simplicity we prove det(elim) = det(m) directly
   by showing elim = sequential row_adds applied to m. *)

(* Row addition (local): add c * row_j to row_i. *)
let row_add_local (#t: Type) {| r: ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t) : square_matrix t n
  = fun (a: fin n) (b: fin n) ->
      if (a <: nat) = (i <: nat) then m a b + c * m j b else m a b

(* det(row_add m i j c) = det m, via transpose + det_col_add. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
let kd_det_row_add (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (m: square_matrix t n) (i j: fin n) (c: t)
  : Lemma (requires ~(i == j))
          (ensures  det (row_add_local m i j c) = det m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let ra = row_add_local m i j c in
    let ca = col_add (transpose m) i j c in
    let pw (a b: fin n) : Lemma (transpose ra a b = ca a b)
      = mul_commutativity c (m j a);
        if Prims.op_Equality (b <: nat) (i <: nat) then
          add_congruence (m b a) (c * m j a) (m b a) (m j a * c)
        else ()
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq (transpose ra) ca;
    det_transpose ra;
    det_col_add (transpose m) i j c;
    det_transpose m
#pop-options

(* ================================================================== *)
(*  Part B2: det(elim_col) = det(m)                                    *)
(*                                                                     *)
(*  Strategy: partial_elim processes one row at a time. Each step is   *)
(*  a row_add that preserves det. Chain gives the result.              *)
(* ================================================================== *)

(* Partial elimination: rows below index k (excluding piv_r) are
   already eliminated; rows at or above k stay as original m. *)
private let partial_elim (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n{is_nonzero (m piv_r piv_c)})
  (k: nat{k <= n})
  : square_matrix t n
  = fun (i: fin n) (j: fin n) ->
      if (i <: nat) < k && (i <: nat) <> (piv_r <: nat)
      then elim_col m piv_r piv_c i j
      else m i j

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
private let partial_elim_zero (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n{is_nonzero (m piv_r piv_c)})
  : Lemma (det (partial_elim m piv_r piv_c 0) = det m)
  = elim_equatable_laws t ();
    let pw (a b: fin n)
      : Lemma (partial_elim m piv_r piv_c 0 a b = m a b)
      = ()
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq (partial_elim m piv_r piv_c 0) m
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 40"
private let partial_elim_full (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n{is_nonzero (m piv_r piv_c)})
  : Lemma (det (partial_elim m piv_r piv_c n) = det (elim_col m piv_r piv_c))
  = elim_equatable_laws t ();
    let pw (a b: fin n)
      : Lemma (partial_elim m piv_r piv_c n a b = elim_col m piv_r piv_c a b)
      = if (a <: nat) = (piv_r <: nat) then ()
        else ()
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq (partial_elim m piv_r piv_c n) (elim_col m piv_r piv_c)
#pop-options

#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
private let partial_elim_step (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n{is_nonzero (m piv_r piv_c)})
  (k: fin n)
  : Lemma (det (partial_elim m piv_r piv_c (((k <: nat) ++ 1)))
         = det (partial_elim m piv_r piv_c (k <: nat)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let pivot_inv : t = inv (m piv_r piv_c) in
    let c_k : t = (- (m k piv_c * pivot_inv)) in
    let pe_k = partial_elim m piv_r piv_c (k <: nat) in
    let pe_k1 = partial_elim m piv_r piv_c (((k <: nat) ++ 1)) in
    if (k <: nat) = (piv_r <: nat) then begin
      let pw (a b: fin n)
        : Lemma (pe_k1 a b = pe_k a b)
        = ()
      in
      Classical.forall_intro_2 pw;
      det_pointwise_eq pe_k1 pe_k
    end
    else begin
      let ra = row_add_local #t #(cr_of_id t #(id_of_f t)).cr_r pe_k k piv_r c_k in
      let pw (a b: fin n)
        : Lemma (pe_k1 a b = ra a b)
        = if (a <: nat) = (k <: nat) then begin
            let x = m k piv_c * pivot_inv in
            let y = m piv_r b in
            neg_mul_l x y;
            add_congruence (m k b) (- (x * y)) (m k b) ((- x) * y)
          end
          else ()
      in
      Classical.forall_intro_2 pw;
      det_pointwise_eq pe_k1 ra;
      kd_det_row_add pe_k k piv_r c_k
    end
#pop-options

private let rec det_partial_elim_eq (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n{is_nonzero (m piv_r piv_c)})
  (k: nat{k <= n})
  : Lemma (ensures det (partial_elim m piv_r piv_c k) = det m)
          (decreases k)
  = if k = 0 then partial_elim_zero m piv_r piv_c
    else begin
      det_partial_elim_eq m piv_r piv_c (k - 1);
      partial_elim_step m piv_r piv_c (k - 1 <: fin n);
      elim_equatable_laws t ();
      transitivity (det (partial_elim m piv_r piv_c k))
                   (det (partial_elim m piv_r piv_c (k - 1)))
                   (det m)
    end

let det_elim_col_eq (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (piv_r piv_c: fin n)
  : Lemma (requires is_nonzero (m piv_r piv_c))
          (ensures  det (elim_col m piv_r piv_c) = det m)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    det_partial_elim_eq m piv_r piv_c n;
    partial_elim_full m piv_r piv_c;
    transitivity (det (elim_col m piv_r piv_c))
                 (det (partial_elim m piv_r piv_c n))
                 (det m)

(* ================================================================== *)
(*  Part B3: Laplace helpers for the inductive case                    *)
(*                                                                     *)
(*  These bridge the TC diamond between field and commutative_ring     *)
(*  contexts, enabling det_laplace_row's postcondition to be used      *)
(*  in field-context proofs.                                           *)
(* ================================================================== *)

(* fin_sum_only_at: if f vanishes off index k, then fin_sum f = f k *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 120"
private let fin_sum_only_at (#t: Type) {| r: ring t |} (#n: pos)
  (f: fin n -> t) (k: fin n)
  (h: (j: fin n) -> Lemma (requires j <> k) (ensures f j = (zero <: t)))
  : Lemma (fin_sum f = f k)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let pw_eq (j: fin n) : Lemma (f j = pointwise_mul (fin_kronecker_delta k) f j)
      = pointwise_mul_unfold (fin_kronecker_delta k) f j;
        fin_kronecker_delta_unfold #t #r #n k j;
        if (j <: nat) = (k <: nat) then begin
          one_mul_x (f j)
        end else begin
          h j;
          zero_mul_x (f j);
          transitivity (f j) (zero <: t) ((zero <: t) * f j)
        end
    in
    fin_sum_congruence f (pointwise_mul (fin_kronecker_delta k) f) pw_eq;
    fin_sum_kronecker k f
#pop-options

(* cofactor_term is zero when the matrix entry is zero *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
private let cofactor_term_zero_entry (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (requires m i j = (zero <: t))
          (ensures  cofactor_term m i j = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let r = cr.cr_r in
    let s = minus_one_pow (((i <: nat) ++ (j <: nat))) in
    let d = det (minor m i j) in
    x_mul_zero s;
    mul_congruence s (m i j) s (zero <: t);
    zero_mul_x d;
    mul_congruence (s * m i j) d (zero <: t) d;
    transitivity (s * m i j * d) ((zero <: t) * d) (zero <: t)
#pop-options

(* -(one) is nonzero in any field *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
private let neg_one_nonzero (#t: Type) {| f: field t |}
  : Lemma (is_nonzero (-(one <: t)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let one_ne_zero : squash (is_nonzero (one <: t)) = (id_of_f t #f).id_one_ne_zero in
    if not (is_nonzero (-(one <: t))) then begin
      x_plus_neg_x (one <: t);
      add_congruence (one <: t) (-(one <: t)) (one <: t) (zero <: t);
      add_zero (one <: t);
      ()
    end else ()
#pop-options

(* (-1)^k is nonzero in any field *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
private let minus_one_pow_nonzero (#t: Type) {| f: field t |} (k: nat)
  : Lemma (is_nonzero (minus_one_pow #t #(cr_of_id t #(id_of_f t)) k))
  = if Prims.op_Modulus k 2 = 0 then
      (id_of_f t #f).id_one_ne_zero
    else
      neg_one_nonzero #t #f
#pop-options

(* TC bridge wrappers: re-state det lemmas in field context *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
private let det_laplace_row_f (#t: Type) {| f: field t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i: fin n)
  : Lemma (det m = fin_sum (cofactor_term m i))
  = det_laplace_row m i

private let det_minor_transpose_f (#t: Type) {| f: field t |} (#n: pos{n > 1})
  (m: square_matrix t n) (i j: fin n)
  : Lemma (det (minor (transpose m) i j) = det (minor m j i))
  = det_minor_transpose m i j
#pop-options

(* Laplace column argument: if a matrix has a single-nonzero-entry column
   and det = 0, then the minor at that entry also has det = 0. *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 80"
private let det_zero_single_entry_col (#t: Type) {| f: field t |} (#n: pos{n > 1})
  (m: square_matrix t n) (r c: fin n)
  : Lemma (requires det m = (zero <: t) /\ is_nonzero (m r c) /\
                   (forall (i: fin n). (i <: nat) <> (r <: nat) ==> m i c = (zero <: t)))
          (ensures  det (minor m r c) = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    det_transpose m;
    det_laplace_row_f (transpose m) c;
    let ct_zero (j: fin n)
      : Lemma (requires j <> r) (ensures cofactor_term (transpose m) c j = (zero <: t))
      = assert ((transpose m) c j == m j c);
        cofactor_term_zero_entry (transpose m) c j
    in
    fin_sum_only_at (cofactor_term (transpose m) c) r ct_zero;
    transitivity (det (transpose m)) (fin_sum (cofactor_term (transpose m) c))
                 (cofactor_term (transpose m) c r);
    assert ((transpose m) c r == m r c);
    let s = minus_one_pow (((c <: nat) ++ (r <: nat))) in
    det_minor_transpose_f m c r;
    mul_congruence (s * m r c) (det (minor (transpose m) c r))
                   (s * m r c) (det (minor m r c));
    let d : domain t = (id_of_f t #f).id_d in
    minus_one_pow_nonzero #t #f (((c <: nat) ++ (r <: nat)));
    domain_nonzero_mul_nonzero s (m r c);
    d.domain_law (s * m r c) (det (minor m r c))
#pop-options

(* ================================================================== *)
(*  Part C: Main theorem — det(M)=0 ⟹ ∃ nonzero v ∈ ker(M)          *)
(*                                                                     *)
(*  We state the result as a Lemma with an existential conclusion.    *)
(*  The proof is by strong induction on n.                            *)
(* ================================================================== *)

(* det_1x1: for a 1×1 matrix, det m = m 0 0 *)
#push-options "--fuel 2 --ifuel 1 --z3rlimit 200"
private let det_1x1 (#t: Type) {| f: field t |} (m: square_matrix t 1)
  : Lemma (det m = m 0 0)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let id1 = identity 1 in
    let all_eq_id (q: permutation 1)
      : Lemma (perm_eq id1 q)
      = let pf (i: fin 1) : Lemma (id1.fwd i == q.fwd i) = () in
        perm_eq_intro id1 q pf
    in
    let h_zero (q: permutation 1)
      : Lemma (requires ~(perm_eq id1 q))
              (ensures  leibniz_term m q = (zero <: t))
      = all_eq_id q
    in
    leibniz_term_respects_perm_eq m;
    sum_over_perms_single 1 (leibniz_term m) id1 h_zero;
    parity_identity 1;
    perm_product_unfold m id1;
    prod_range_singleton (fun (i:nat) -> if i < 1 then m i (id1.fwd i) else (one <: t)) 0;
    x_mul_one (m (0 <: fin 1) (id1.fwd (0 <: fin 1)))
#pop-options

(* ================================================================== *)
(*  Part C: Main theorem                                              *)
(*                                                                     *)
(*  Case 1 (adj ≠ 0): column j of adj(M) is a kernel vector.          *)
(*  Case 2 (adj = 0, M ≠ 0): elimination-based inductive argument.    *)
(*  Case 3 (M = 0): any basis vector works.                           *)
(* ================================================================== *)

(* Case 1: If det(M) = 0 and adj(M)(r,j) ≠ 0, then column j of adj(M)
   is a nonzero kernel vector of M. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
let adj_nonzero_gives_kernel (#t: Type) {| cr: commutative_ring t |} (#n: pos{n > 1})
  (m: square_matrix t n) (r j: fin n)
  : Lemma (requires det m = (zero <: t) /\ is_nonzero (adjugate m r j))
          (ensures  is_nonzero (col (adjugate m) j r) /\
                    (forall (i: fin n).
                      matrix_mul m (adjugate m) i j = (zero <: t)))
  = let col_j_at_r () : Lemma (is_nonzero (col (adjugate m) j r)) = () in
    col_j_at_r ();
    let kernel_i (i: fin n)
      : Lemma (matrix_mul m (adjugate m) i j = (zero <: t))
      = adj_column_in_kernel m j i
    in
    Classical.forall_intro kernel_i
#pop-options

(* Bridge: matrix_mul entry to vector_dot. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
let mul_entry_is_dot (#t: Type) {| cr: commutative_ring t |} (#n: pos)
  (a b: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a b i j = vector_dot (row a i) (col b j))
  = matrix_mul_unfold a b i j;
    H.leibniz_to_eq (matrix_mul a b i j) (vector_dot (row a i) (col b j))
#pop-options

(* ================================================================== *)
(*  fin_sum_skip_reindex infrastructure                                *)
(*                                                                     *)
(*  If f(c) = 0 and g(b) = f(skip c b), then fin_sum f = fin_sum g.   *)
(*  Used for the vector extension in det_zero_implies_null_vec.        *)
(* ================================================================== *)

(* unskip / skip_unskip / unskip_skip are defined above (Determinant body);
   the identical KernelDet-local copies were dropped during the merge. *)

#push-options "--fuel 1 --ifuel 0 --z3rlimit 200"
private let sum_range_reindex_helper (#t: Type) {| acg: add_comm_group t |} (#n: pos{n > 1})
  (f: fin n -> t) (c: fin n) (g: fin ((n - 1)) -> t)
  (big: nat -> t) (small: nat -> t)
  (h_skip: (b: fin ((n - 1))) -> Lemma (f (skip c b) = g b))
  (h_big: (k: nat{k < n}) -> Lemma (big k = f (k <: fin n)))
  (h_big_else: (k: nat{k >= n}) -> Lemma (big k = (zero <: t)))
  (h_small: (k: nat{k < (n - 1)}) -> Lemma (small k = g (k <: fin ((n - 1)))))
  (h_small_else: (k: nat{k >= (n - 1)}) -> Lemma (small k = (zero <: t)))
  : Lemma (sum_range small 0 ((n - 1)) =
           sum_range big 0 c + sum_range big ((c ++ 1)) n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let nm1 : pos = (n - 1) in
    sum_range_split small 0 c nm1;
    let first_half (k: nat{0 <= k /\ k < c})
      : Lemma (big k = small k)
      = h_skip (k <: fin nm1);
        h_big k;
        h_small k;
        H.leibniz_to_eq (f (skip c (k <: fin nm1))) (f (k <: fin n));
        transitivity (big k) (g (k <: fin nm1)) (small k)
    in
    sum_range_congruence big small 0 c first_half;
    let second_half (k: nat{c <= k /\ k < nm1})
      : Lemma (small k = big ((k ++ 1)))
      = h_skip (k <: fin nm1);
        h_small k;
        let kp1 : fin n = (k ++ 1) in
        h_big kp1;
        H.leibniz_to_eq (f (skip c (k <: fin nm1))) (f kp1)
    in
    let big_plus1 : (nat -> t) = (fun (j:nat) -> big ((j ++ 1))) in
    sum_range_congruence small big_plus1 c nm1 second_half;
    sum_range_shift big 1 c nm1;
    transitivity (sum_range small c nm1) (sum_range big_plus1 c nm1)
                 (sum_range big ((c ++ 1)) n);
    add_congruence (sum_range small 0 c) (sum_range small c nm1)
                   (sum_range big 0 c) (sum_range big ((c ++ 1)) n);
    transitivity (sum_range small 0 nm1)
                 (sum_range small 0 c + sum_range small c nm1)
                 (sum_range big 0 c + sum_range big ((c ++ 1)) n)
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 120"
private let fin_sum_eliminate_zero_helper (#t: Type) {| acg: add_comm_group t |} (#n: pos{n > 1})
  (f: fin n -> t) (c: fin n) (big: nat -> t)
  (h_zero: squash (f c = (zero <: t)))
  (h_big: squash (fin_sum f = sum_range big 0 n))
  (h_big_c: squash (big c = f c))
  : Lemma (fin_sum f = sum_range big 0 c + sum_range big ((c ++ 1)) n)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    sum_range_split big 0 c n;
    sum_range_unfold_left big c n;
    H.leibniz_to_eq (sum_range big c n) (big c + sum_range big ((c ++ 1)) n);
    zero_plus_x (sum_range big ((c ++ 1)) n);
    add_congruence (big c) (sum_range big ((c ++ 1)) n)
                   (zero <: t) (sum_range big ((c ++ 1)) n);
    transitivity (big c + sum_range big ((c ++ 1)) n)
                 ((zero <: t) + sum_range big ((c ++ 1)) n)
                 (sum_range big ((c ++ 1)) n);
    transitivity (sum_range big c n)
                 (big c + sum_range big ((c ++ 1)) n)
                 (sum_range big ((c ++ 1)) n);
    add_congruence (sum_range big 0 c) (sum_range big c n)
                   (sum_range big 0 c) (sum_range big ((c ++ 1)) n);
    transitivity (sum_range big 0 n) (sum_range big 0 c + sum_range big c n)
                 (sum_range big 0 c + sum_range big ((c ++ 1)) n);
    transitivity (fin_sum f) (sum_range big 0 n)
                 (sum_range big 0 c + sum_range big ((c ++ 1)) n)
#pop-options

#push-options "--fuel 0 --ifuel 0 --z3rlimit 30"
private let derive_eq_via_mid (#t: Type) {| acg: add_comm_group t |}
  (fg: t) (sr_small: t) (rhs: t)
  (h1: squash (fg = sr_small))
  (h2: squash (sr_small = rhs))
  : Lemma (fg = rhs)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    transitivity fg sr_small rhs
#pop-options

(* (a + neg b) + b = a — used in elim_col decomposition *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
private let sub_add_cancel (#t: Type) {| acg: add_comm_group t |} (a b: t)
  : Lemma ((a + (- b)) + b = a)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    add_associativity a (- b) b;
    neg_x_plus_x b;
    add_congruence a ((- b) + b) a (zero <: t);
    x_plus_zero a;
    transitivity ((a + (- b)) + b) (a + (zero <: t)) a
#pop-options

#push-options "--fuel 1 --ifuel 0 --z3rlimit 80"
private let fin_sum_skip_reindex (#t: Type) {| acg: add_comm_group t |} (#n: pos{n > 1})
  (f: fin n -> t) (c: fin n) (g: fin ((n - 1)) -> t)
  (h_zero: squash (f c = (zero <: t)))
  (h_skip: (b: fin ((n - 1))) -> Lemma (f (skip c b) = g b))
  : Lemma (fin_sum f = fin_sum g)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let nm1 : pos = (n - 1) in
    let big : (nat -> t) = (fun (k: nat) -> if k < n then f (k <: fin n) else zero) in
    let small : (nat -> t) = (fun (k: nat) -> if k < (n - 1) then g (k <: fin ((n - 1))) else zero) in
    H.leibniz_to_eq (fin_sum g) (sum_range small 0 ((n - 1)));
    let h_fg : squash (fin_sum g = sum_range small 0 nm1) = () in
    H.leibniz_to_eq (fin_sum f) (sum_range big 0 n);
    fin_sum_eliminate_zero_helper f c big h_zero () ();
    sum_range_reindex_helper f c g big small h_skip
      (fun k -> ()) (fun k -> ()) (fun k -> ()) (fun k -> ());
    let rhs = sum_range big 0 c + sum_range big ((c ++ 1)) n in
    let h_sr : squash (sum_range small 0 nm1 = rhs) = () in
    derive_eq_via_mid (fin_sum g) (sum_range small 0 nm1) rhs h_fg h_sr
#pop-options

(* Combined: fin_sum f = 0 when f[c]=0, f[skip c j]=g j, and fin_sum g = 0.
   All three fin_sum forms are elaborated in the SAME function, avoiding the
   cross-site lambda identity problem in SMT. *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 80"
private let fin_sum_skip_zero (#t: Type) {| acg: add_comm_group t |} (#n: pos{n > 1})
  (f: fin n -> t) (c: fin n) (g: fin ((n - 1)) -> t)
  (h_zero: squash (f c = (zero <: t)))
  (h_skip: (b: fin ((n - 1))) -> Lemma (f (skip c b) = g b))
  (h_g_zero: squash (fin_sum g = (zero <: t)))
  : Lemma (fin_sum f = (zero <: t))
  = fin_sum_skip_reindex f c g h_zero h_skip;
    trans_for_calc t ();
    ()
#pop-options

(* Chain helper: given sum_pw = f2+f1, f2 = neg x, f1 = x, prove sum_pw = 0.
   All equality uses the same acg, avoiding TC diamond. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 40"
private let sum_split_neg_cancel (#t: Type) {| acg: add_comm_group t |}
  (sum_pw: t) (sum_f2: t) (sum_f1: t) (x: t)
  (h_split: squash (sum_pw = sum_f2 + sum_f1))
  (h_f2: squash (sum_f2 = (- x)))
  (h_f1: squash (sum_f1 = x))
  : Lemma (sum_pw = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    neg_x_plus_x x;
    add_congruence sum_f2 sum_f1 (- x) x;
    transitivity sum_pw ((- x) + x) (zero <: t)
#pop-options

(* fin_sum of a function that is val_c at one index and zero elsewhere. *)
#push-options "--fuel 1 --ifuel 0 --z3rlimit 60"
private let fin_sum_single (#t: Type) {| r: ring t |} (#n: pos)
  (f: fin n -> t) (c: fin n) (val_c: t)
  (h_c: squash (f c = val_c))
  (h_nc: (j: fin n) -> Lemma (requires (j <: nat) <> (c <: nat)) (ensures f j = (zero <: t)))
  : Lemma (fin_sum f = val_c)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let bridge (j: fin n) : Lemma (f j = pointwise_mul (fin_kronecker_delta c) (const val_c) j)
      = pointwise_mul_unfold (fin_kronecker_delta c) (const val_c) j;
        if (j <: nat) = (c <: nat) then begin
          one_mul_x val_c;
          transitivity (f j) val_c (one * val_c)
        end else begin
          h_nc j;
          zero_mul_x val_c;
          transitivity (f j) (zero <: t) (zero * val_c)
        end
    in
    fin_sum_congruence f (pointwise_mul (fin_kronecker_delta c) (const val_c)) bridge;
    fin_sum_kronecker c (const val_c)
#pop-options

(* The main theorem statement is declared in the .fsti
   (det_zero_implies_null_vec); the recursive impl appears below. *)

(* ================================================================== *)
(*  Case helpers for the main proof                                    *)
(* ================================================================== *)

(* Case adj≠0: column of adjugate is kernel vector. *)
#push-options "--fuel 0 --ifuel 0 --z3rlimit 60"
private let case_adj_nonzero (#t: Type) {| f: field t |} (#n: pos{n > 1})
  (m: square_matrix t n) (r j: fin n)
  : Lemma (requires det m = (zero <: t) /\ is_nonzero (adjugate m r j))
          (ensures  exists (v: fin n -> t) (k: fin n).
                      is_nonzero (v k) /\
                      (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
  = adj_nonzero_gives_kernel m r j;
    let v : (fin n -> t) = col (adjugate m) j in
    let dot_zero (i: fin n)
      : Lemma (vector_dot (row m i) v = (zero <: t))
      = mul_entry_is_dot m (adjugate m) i j;
        elim_equatable_laws t ();
        transitivity (vector_dot (row m i) v)
                     (matrix_mul m (adjugate m) i j)
                     (zero <: t)
    in
    Classical.forall_intro dot_zero
#pop-options

(* Case M=0: any basis vector works. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 80"
private let case_m_zero (#t: Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n)
  : Lemma (requires forall (r c: fin n). m r c = (zero <: t))
          (ensures  exists (v: fin n -> t) (k: fin n).
                      is_nonzero (v k) /\
                      (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let _ : squash (not ((one <: t) `eq` (zero <: t))) =
      (id_of_f t #f).id_one_ne_zero in
    let v : (fin n -> t) = fun _ -> (one <: t) in
    let cr : commutative_ring t = cr_of_id t #(id_of_f t #f) in
    let dot_zero (i: fin n)
      : Lemma (vector_dot (row m i) v = (zero <: t))
      = let pw = pointwise_mul #(fin n) #t #cr.cr_r (row m i) v in
        let f_zero (k: fin n)
          : Lemma (pw k = (zero <: t))
          = pointwise_mul_unfold #(fin n) #t #cr.cr_r (row m i) v k;
            zero_mul_x #t #cr.cr_r (one <: t);
            mul_congruence #t #cr.cr_r (m i k) (one <: t) (zero <: t) (one <: t)
        in
        Classical.forall_intro f_zero;
        fin_sum_zero_ext #t #(acg_of_r t #cr.cr_r) #n pw f_zero;
        fin_sum_eq_pointwise #t #(acg_of_r t #cr.cr_r) pw (pointwise_mul (row m i) v);
        vector_dot_reveal #t #cr.cr_r #n (row m i) v
      in
    Classical.forall_intro dot_zero;
    assert (is_nonzero (v (0 <: fin n)));
    assert (forall (i: fin n). vector_dot (row m i) v = (zero <: t))
#pop-options

(* The main theorem body.
   Currently uses admits for: base case n=1 and inductive case (adj=0,M≠0).
   The adj≠0 case and M=0 case are fully proved above. *)
#push-options "--fuel 1 --ifuel 1 --z3rlimit 200"
let rec det_zero_implies_null_vec #t #f #n m =
  if n = 1 then begin
    (* Base case: det m = m 0 0 for 1×1, so m 0 0 = zero, use case_m_zero *)
    det_1x1 m;
    elim_equatable_laws t ();
    trans_for_calc t ();
    let all_zero (r: fin 1) (c: fin 1)
      : Lemma (m r c = (zero <: t))
      = () (* r=0, c=0 is the only case *)
    in
    Classical.forall_intro_2 all_zero;
    case_m_zero m
  end
  else begin
    (* n ≥ 2: case split via excluded middle + move_requires *)
    let adj_has_nonzero ()
      : Lemma (requires exists (r: fin n) (j: fin n). is_nonzero (adjugate m r j))
              (ensures  exists (v: fin n -> t) (k: fin n).
                          is_nonzero (v k) /\
                          (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
      = let helper (r: fin n) (j: fin n)
          : Lemma (requires is_nonzero (adjugate m r j))
                  (ensures  exists (v: fin n -> t) (k: fin n).
                              is_nonzero (v k) /\
                              (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
          = case_adj_nonzero m r j
        in
        let helper2 (r: fin n) (j: fin n)
          : Lemma (is_nonzero (adjugate m r j) ==>
                   (exists (v: fin n -> t) (k: fin n).
                      is_nonzero (v k) /\
                      (forall (i: fin n). vector_dot (row m i) v = (zero <: t))))
          = Classical.move_requires (helper r) j
        in
        Classical.forall_intro_2 helper2
    in
    let adj_all_zero ()
      : Lemma (requires ~(exists (r: fin n) (j: fin n). is_nonzero (adjugate m r j)))
              (ensures  exists (v: fin n -> t) (k: fin n).
                          is_nonzero (v k) /\
                          (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
      = (* Sub-case: M has a nonzero entry — inductive case *)
        let m_has_nonzero (r: fin n) (c: fin n)
          : Lemma (requires is_nonzero (m r c))
                  (ensures exists (v: fin n -> t) (k: fin n).
                             is_nonzero (v k) /\
                             (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
          = (* Step 1: column elimination preserves det *)
            elim_equatable_laws t ();
            trans_for_calc t ();
            let e = elim_col m r c in
            det_elim_col_eq m r c;
            (* det e = det m = zero *)
            (* Step 2: Laplace along column c → det(minor(E, r, c)) = 0 *)
            let minor_e : square_matrix t ((n - 1)) = minor e r c in
            (* e has column c all zeros except at (r,c) *)
            let elim_col_precond (i: fin n)
              : Lemma (requires (i <: nat) <> (r <: nat))
                      (ensures  e i c = (zero <: t))
              = elim_col_zero m r c i
            in
            Classical.forall_intro (Classical.move_requires elim_col_precond);
            elim_col_pivot m r c;
            det_zero_single_entry_col e r c;
            (* Step 3: IH gives w in kernel of minor *)
            det_zero_implies_null_vec #t #f #((n - 1)) minor_e;
            (* Now: exists (w: fin(n-1)->t) (k0: fin(n-1)). is_nonzero(w k0) /\ ... *)
            (* Step 4: extend w to v in kernel of M *)
            let nm1 : pos = (n - 1) in
            let vector_extend (w: fin nm1 -> t) (k0: fin nm1)
              : Lemma (requires is_nonzero (w k0) /\
                                (forall (i: fin nm1). vector_dot (row minor_e i) w = (zero <: t)))
                      (ensures  exists (v: fin n -> t) (k: fin n).
                                  is_nonzero (v k) /\
                                  (forall (i: fin n). vector_dot (row m i) v = (zero <: t)))
              = let rr : ring t = f.f_sf.sf_r in
                let f_x : (fin nm1 -> t) = (fun (b: fin nm1) -> m r (skip c b) * w b) in
                let x : t = fin_sum #t #(rr.r_add) #((n - 1)) f_x in
                let mig : mul_is_group t = mig_of_sf t #f.f_sf in
                let inv_mrc : t = mig.inv (m r c) in
                let neg_inv : t = (- inv_mrc) in
                let vc : t = neg_inv * x in
                let v (j: fin n) : t =
                  if (j <: nat) = (c <: nat) then vc else w (unskip c j)
                in
                let k : fin n = skip c k0 in
                assert (v k == w k0);
                elim_equatable_laws t ();
                trans_for_calc t ();
                (* --- Row r: vector_dot (row m r) v = zero --- *)
                let row_r_zero ()
                  : Lemma (vector_dot (row m r) v = (zero <: t))
                  = let pw_r : (fin n -> t) = pointwise_mul (row m r) v in
                    let f1 (j: fin n) : t = if (j <: nat) = (c <: nat) then zero else pw_r j in
                    let f2 (j: fin n) : t = if (j <: nat) = (c <: nat) then pw_r c else zero in
                    let split_cb (j: fin n) : Lemma (pw_r j = f2 j + f1 j)
                      = if (j <: nat) = (c <: nat) then
                          x_plus_zero #t #(rr.r_add) (pw_r j)
                        else
                          zero_plus_x #t #(rr.r_add) (pw_r j)
                    in
                    fin_sum_add_ext #t #(rr.r_add) #n f2 f1 (pointwise_mul (row m r) v) split_cb;
                    (* fin_sum f1 = x via skip_reindex *)
                    let f1_skip (b: fin nm1) : Lemma (f1 (skip c b) = f_x b)
                      = skip_avoids c b;
                        unskip_skip c b;
                        H.leibniz_to_eq (v (skip c b)) (w b);
                        H.leibniz_to_eq (pw_r (skip c b)) (m r (skip c b) * w b);
                        H.leibniz_to_eq (f1 (skip c b)) (pw_r (skip c b))
                    in
                    fin_sum_skip_reindex #t #(rr.r_add) #n f1 c f_x () f1_skip;
                    (* Bridge: skip_reindex gives fin_sum f1 = fin_sum f_x = x *)
                    derive_eq_via_mid #t #(rr.r_add)
                      (fin_sum #t #(rr.r_add) #n f1)
                      (fin_sum #t #(rr.r_add) #((n - 1)) f_x) x () ();
                    (* Now have: fin_sum f1 = x *)
                    (* Show m r c * vc = neg x *)
                    mul_associativity #t #rr (m r c) neg_inv x;
                    neg_mul_r #t #rr (m r c) inv_mrc;
                    mig.inversion_lemma (m r c);
                    mul_congruence #t #rr (m r c * neg_inv) x
                                          (- (m r c * inv_mrc)) x;
                    neg_congruence #t #(rr.r_add) (m r c * inv_mrc) one;
                    mul_congruence #t #rr (- (m r c * inv_mrc)) x (- one) x;
                    neg_mul_l #t #rr one x;
                    one_mul_x #t #rr x;
                    neg_congruence #t #(rr.r_add) (one * x) x;
                    transitivity ((m r c * neg_inv) * x)
                                 ((- (m r c * inv_mrc)) * x) (- x);
                    symmetry ((m r c * neg_inv) * x)
                             (m r c * (neg_inv * x));
                    transitivity (m r c * vc)
                                 (m r c * (neg_inv * x))
                                 (- x);
                    transitivity (m r c * vc)
                                 ((m r c * neg_inv) * x) (- x);
                    (* Now: m r c * vc = neg x *)
                    let f2_nc (j: fin n)
                      : Lemma (requires (j <: nat) <> (c <: nat))
                              (ensures f2 j = (zero <: t)) = ()
                    in
                    fin_sum_single #t #rr #n f2 c (- x) () f2_nc;
                    (* fin_sum f2 = neg x, fin_sum f1 = x *)
                    add_congruence #t #(rr.r_add)
                      (fin_sum #t #(rr.r_add) #n f2) (fin_sum #t #(rr.r_add) #n f1)
                      (- x) x;
                    neg_x_plus_x #t #(rr.r_add) x;
                    transitivity (fin_sum #t #(rr.r_add) #n f2 + fin_sum #t #(rr.r_add) #n f1)
                                 ((- x) + x) (zero <: t);
                    transitivity (fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                                 (fin_sum #t #(rr.r_add) #n f2 + fin_sum #t #(rr.r_add) #n f1)
                                 (zero <: t);
                    vector_dot_reveal #t #rr #n (row m r) v
                in
                row_r_zero ();
                (* --- Row i≠r: vector_dot (row m i) v = zero --- *)
                let dot_zero (i: fin n)
                  : Lemma (vector_dot (row m i) v = (zero <: t))
                  = if (i <: nat) = (r <: nat) then
                      row_r_zero ()
                    else begin
                      (* Row i≠r: uses elim_col decomposition + IH *)
                      let ih_row : fin nm1 = unskip r i in
                      let coeff_i : t = m i c * inv_mrc in
                      (* Named combinator forms (NO local lambdas): *)
                      let f1 : (fin n -> t) = pointwise_mul (row e i) v in
                      let f2 : (fin n -> t) = pointwise_mul (const coeff_i) (pointwise_mul (row m r) v) in
                      (* Step 1: pointwise decomposition
                         (pw (row m i) v) j = f1 j + f2 j *)
                      let pw_split (j: fin n)
                        : Lemma ((pointwise_mul (row m i) v) j = f1 j + f2 j)
                        = pointwise_mul_unfold #(fin n) #t #rr (row m i) v j;
                          pointwise_mul_unfold #(fin n) #t #rr (row e i) v j;
                          pointwise_add_unfold #(fin n) #t #(rr.r_add) f1 f2 j;
                          pointwise_mul_unfold #(fin n) #t #rr (const coeff_i) (pointwise_mul (row m r) v) j;
                          pointwise_mul_unfold #(fin n) #t #rr (row m r) v j;
                          (* e i j == m i j + neg (coeff_i * m r j) definitionally *)
                          H.leibniz_to_eq (e i j) (m i j + (- (coeff_i * m r j)));
                          (* (a + b)*c = a*c + b*c *)
                          right_distributivity #t #rr (v j) (m i j) (- (coeff_i * m r j));
                          (* neg(a)*b = neg(a*b) *)
                          neg_mul_l #t #rr (coeff_i * m r j) (v j);
                          (* (coeff_i * m r j) * v j = coeff_i * (m r j * v j) *)
                          mul_associativity #t #rr coeff_i (m r j) (v j);
                          neg_congruence #t #(rr.r_add) ((coeff_i * m r j) * v j) (coeff_i * (m r j * v j));
                          transitivity ((- (coeff_i * m r j)) * v j)
                                       (- ((coeff_i * m r j) * v j))
                                       (- (coeff_i * (m r j * v j)));
                          (* chain: e i j * v j = m i j * v j + neg(coeff_i*(m r j * v j)) *)
                          add_congruence #t #(rr.r_add) (m i j * v j) ((- (coeff_i * m r j)) * v j)
                                         (m i j * v j) (- (coeff_i * (m r j * v j)));
                          transitivity ((m i j + (- (coeff_i * m r j))) * v j)
                                       (m i j * v j + (- (coeff_i * m r j)) * v j)
                                       (m i j * v j + (- (coeff_i * (m r j * v j))));
                          mul_congruence #t #rr (e i j) (v j) (m i j + (- (coeff_i * m r j))) (v j);
                          transitivity (e i j * v j)
                                       ((m i j + (- (coeff_i * m r j))) * v j)
                                       (m i j * v j + (- (coeff_i * (m r j * v j))));
                          (* sub_add_cancel: (a + neg b) + b = a *)
                          sub_add_cancel #t #(rr.r_add) (m i j * v j) (coeff_i * (m r j * v j));
                          add_congruence #t #(rr.r_add) (e i j * v j) (coeff_i * (m r j * v j))
                                         (m i j * v j + (- (coeff_i * (m r j * v j)))) (coeff_i * (m r j * v j));
                          transitivity (e i j * v j + coeff_i * (m r j * v j))
                                       ((m i j * v j + (- (coeff_i * (m r j * v j)))) + coeff_i * (m r j * v j))
                                       (m i j * v j);
                          (* So m i j * v j = f1 j + f2 j *)
                          H.leibniz_to_eq (f1 j) (e i j * v j);
                          H.leibniz_to_eq (f2 j) (coeff_i * (m r j * v j));
                          H.leibniz_to_eq ((pointwise_mul (row m i) v) j) (m i j * v j);
                          transitivity ((pointwise_mul (row m i) v) j) (m i j * v j) (f1 j + f2 j)
                      in
                      (* Step 2: fin_sum (pw (row m i) v) = fin_sum f1 + fin_sum f2 *)
                      fin_sum_add_ext #t #(rr.r_add) #n f1 f2 (pointwise_mul (row m i) v) pw_split;
                      (* Step 3: fin_sum f1 = 0 via skip_reindex + IH *)
                      let f1_at_c ()
                        : Lemma (f1 c = (zero <: t))
                        = pointwise_mul_unfold #(fin n) #t #rr (row e i) v c;
                          H.leibniz_to_eq (f1 c) (e i c * v c);
                          elim_col_zero m r c i;
                          zero_mul_x #t #rr (v c);
                          mul_congruence #t #rr (e i c) (v c) (zero <: t) (v c);
                          transitivity (f1 c) ((zero <: t) * v c) (zero <: t)
                      in
                      f1_at_c ();
                      let f1_skip (b: fin nm1)
                        : Lemma (f1 (skip c b) = (pointwise_mul #(fin ((n - 1))) #t #rr (row minor_e ih_row) w) b)
                        = pointwise_mul_unfold #(fin n) #t #rr (row e i) v (skip c b);
                          H.leibniz_to_eq (f1 (skip c b)) (e i (skip c b) * v (skip c b));
                          pointwise_mul_unfold #(fin ((n - 1))) #t #rr (row minor_e ih_row) w b;
                          skip_unskip r i;
                          skip_unskip c (skip c b);
                          unskip_skip c b;
                          skip_avoids c b;
                          H.leibniz_to_eq (v (skip c b)) (w (unskip c (skip c b)));
                          H.leibniz_to_eq (w (unskip c (skip c b))) (w b);
                          H.leibniz_to_eq (e i (skip c b)) (minor_e ih_row b);
                          mul_congruence #t #rr (e i (skip c b)) (v (skip c b))
                                                (minor_e ih_row b) (w b);
                          transitivity (f1 (skip c b)) (e i (skip c b) * v (skip c b))
                                       (minor_e ih_row b * w b);
                          transitivity (f1 (skip c b)) (minor_e ih_row b * w b) ((pointwise_mul #(fin ((n - 1))) #t #rr (row minor_e ih_row) w) b)
                      in
                      vector_dot_reveal #t #rr #((n - 1)) (row minor_e ih_row) w;
                      assert (vector_dot #t #rr #((n - 1)) (row minor_e ih_row) w == fin_sum #t #(rr.r_add) #((n - 1)) (pointwise_mul #(fin ((n - 1))) #t #rr (row minor_e ih_row) w));
                      assert (fin_sum #t #(rr.r_add) #((n - 1)) (pointwise_mul #(fin ((n - 1))) #t #rr (row minor_e ih_row) w) = (zero <: t));
                      fin_sum_skip_zero #t #(rr.r_add) #n f1 c (pointwise_mul #(fin ((n - 1))) #t #rr (row minor_e ih_row) w) () f1_skip ();
                      (* fin_sum f1 = 0 *)
                      (* Step 4: fin_sum f2 = 0 via fin_sum_mul_left + row_r_zero *)
                      fin_sum_mul_left #t #rr #n coeff_i (pointwise_mul (row m r) v);
                      (* coeff_i * fin_sum (pw (row m r) v) = fin_sum f2 *)
                      let f2_bridge (j: fin n)
                        : Lemma (f2 j = (pointwise_mul (const coeff_i) (pointwise_mul (row m r) v)) j)
                        = reflexivity (f2 j)
                      in
                      fin_sum_congruence #t #(rr.r_add) #n f2
                        (pointwise_mul (const coeff_i) (pointwise_mul (row m r) v)) f2_bridge;
                      symmetry (coeff_i * fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                               (fin_sum #t #(rr.r_add) #n (pointwise_mul (const coeff_i) (pointwise_mul (row m r) v)));
                      derive_eq_via_mid #t #(rr.r_add)
                        (fin_sum #t #(rr.r_add) #n f2)
                        (fin_sum #t #(rr.r_add) #n (pointwise_mul (const coeff_i) (pointwise_mul (row m r) v)))
                        (coeff_i * fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                        () ();
                      (* fin_sum f2 = coeff_i * fin_sum (pw (row m r) v) *)
                      row_r_zero ();
                      vector_dot_reveal #t #rr #n (row m r) v;
                      assert (vector_dot #t #rr #n (row m r) v == fin_sum #t #(rr.r_add) #n (pointwise_mul #(fin n) #t #rr (row m r) v));
                      mul_congruence #t #rr coeff_i
                        (fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                        coeff_i (zero <: t);
                      x_mul_zero #t #rr coeff_i;
                      transitivity (coeff_i * fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                                   (coeff_i * (zero <: t)) (zero <: t);
                      transitivity (fin_sum #t #(rr.r_add) #n f2)
                                   (coeff_i * fin_sum #t #(rr.r_add) #n (pointwise_mul (row m r) v))
                                   (zero <: t);
                      (* fin_sum f2 = 0 *)
                      (* Step 5: fin_sum f1 + fin_sum f2 = 0 + 0 = 0 *)
                      add_congruence #t #(rr.r_add)
                        (fin_sum #t #(rr.r_add) #n f1) (fin_sum #t #(rr.r_add) #n f2)
                        (zero <: t) (zero <: t);
                      zero_plus_x #t #(rr.r_add) (zero <: t);
                      transitivity (fin_sum #t #(rr.r_add) #n f1 + fin_sum #t #(rr.r_add) #n f2)
                                   ((zero <: t) + (zero <: t)) (zero <: t);
                      (* Step 6: chain to vector_dot *)
                      symmetry (fin_sum #t #(rr.r_add) #n (pointwise_mul (row m i) v))
                               (fin_sum #t #(rr.r_add) #n f1 + fin_sum #t #(rr.r_add) #n f2);
                      transitivity (fin_sum #t #(rr.r_add) #n (pointwise_mul (row m i) v))
                                   (fin_sum #t #(rr.r_add) #n f1 + fin_sum #t #(rr.r_add) #n f2)
                                   (zero <: t);
                      vector_dot_reveal #t #rr #n (row m i) v
                    end
                in
                Classical.forall_intro dot_zero
            in
            Classical.forall_intro_2 (Classical.move_requires_2 vector_extend)
        in
        let m_has_nonzero2 (r: fin n) (c: fin n)
          : Lemma (is_nonzero (m r c) ==>
                   (exists (v: fin n -> t) (k: fin n).
                      is_nonzero (v k) /\
                      (forall (i: fin n). vector_dot (row m i) v = (zero <: t))))
          = Classical.move_requires (m_has_nonzero r) c
        in
        Classical.forall_intro_2 m_has_nonzero2;
        (* Now SMT knows: forall r c. is_nonzero (m r c) ==> goal *)
        (* Case: all entries zero *)
        Classical.excluded_middle
          (exists (r: fin n) (c: fin n). is_nonzero (m r c));
        Classical.move_requires case_m_zero m
    in
    Classical.excluded_middle
      (exists (r: fin n) (j: fin n). is_nonzero (adjugate m r j));
    Classical.move_requires adj_has_nonzero ();
    Classical.move_requires adj_all_zero ()
  end
#pop-options


(* ================================================================== *)
(*  MERGED FROM Core.Matrix.NullVec                                    *)

(* ================================================================== *)

(* ================================================================ *)
(*  Elimination matrix                                               *)
(* ================================================================ *)

(* Elimination matrix E: column k = v/v(k), other columns = identity *)
let elim_matrix (#t:Type) {| f: skewfield t |} (#n: pos) 
                (v: fin n -> t) (k: fin n{is_nonzero (v k)}) (i j: fin n) =      
      if j=k then ((v i) * (inv (v k)))
      else if i=j then one else zero

(* ================================================================ *)
(*  M · E has zero column k when Mv = 0                             *)
(* ================================================================ *)

(* null_vec_hyp is declared concretely in the .fsti; not redefined here. *)

let me_col_k_is_zero (#t:Type) {| f: field t |} (#n: pos)
  (m: square_matrix t n) (v: fin n -> t) (k i: fin n)
  : Lemma (requires is_nonzero (v k) /\ vector_dot (row m i) v = zero)
          (ensures matrix_mul m (elim_matrix v k) i k = zero)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    (* Bridge: unfold vector_dot to fin_sum form for the proof body *)
    let e = elim_matrix v k in
    let mi_v = pointwise_mul (row m i) v in    
    let inv_vk = inv (v k) in
    let mil_elk = pointwise_mul (row m i) (col e k) in       
    vector_dot_reveal (row m i) v;
    vector_dot_reveal (row m i) (col e k);
    fin_sum_eq_pointwise mil_elk (pointwise_mul (row m i) (col e k));
    (* pointwise congruence: m i l * e l k = pointwise_mul (...) (const inv_vk) l *)
    fin_sum_congruence mil_elk (pointwise_mul mi_v (const inv_vk)) 
                               (fun l -> mul_associativity (m i l) (v l) inv_vk);
    (* gives: fin_sum (fun l -> m i l * e l k) = fin_sum (pointwise_mul (...) (const inv_vk)) *)
    fin_sum_mul_right mi_v inv_vk;
    (* gives: fin_sum (fun l -> m i l * v l) * inv_vk = fin_sum (pointwise_mul (...) (const inv_vk)) *)    
    (* gives: fin_sum (fun l -> m i l * e l k) = fin_sum (fun l -> m i l * v l) * inv_vk *)
    zero_mul_x inv_vk;
    fin_sum_eq_pointwise mi_v (pointwise_mul (row m i) v);
    mul_congruence (fin_sum mi_v) inv_vk zero inv_vk

(* ================================================================ *)
(*  det(E) = 1                                                       *)
(*  Proof: E is obtained from I by col_add operations, each          *)
(*  preserving det. det(I) = 1 (det_identity).                       *)
(* ================================================================ *)

(* col_add_step: matrix obtained from I by adding (v(j)/v(k)) * col_j to col_k
   for all j < step, j ≠ k *)
let rec col_add_steps (#t:Type) {| f: field t |} (#n: pos)
  (v: fin n -> t) (k: fin n) (step: nat{step <= n})
  : Pure (square_matrix t n)
         (requires is_nonzero (v k))
         (ensures fun _ -> True)
         (decreases step)
  = if step = 0 then id_matrix
    else
      let prev = col_add_steps v k (step - 1) in
      let j : nat = step - 1 in
      if j = k then prev
      else col_add prev k j ((v j) * (inv (v k)))

(* det of col_add_steps = 1 at every step *)
let rec det_col_add_steps_eq_one (#t:Type) {| f: field t |} (#n: pos)
  (v: fin n -> t) (k: fin n) (step: nat{step <= n})
  : Lemma (requires is_nonzero (v k))
          (ensures det (col_add_steps v k step) = one)
          (decreases step)
  = trans_for_calc t ();
    if step = 0 then
      det_identity #t n
    else begin
      det_col_add_steps_eq_one v k (step - 1);
      let prev = col_add_steps v k (step - 1) in
      let j : nat = step - 1 in
      if j = k then reflexivity (det prev)
      else det_col_add prev k j ((v j) * (inv (v k)))
    end


(* Helper: explicitly state what col_add computes at a given index *)
private let col_add_at (#t:Type) {| r: ring t |} (#n: pos)
  (m: square_matrix t n) (target src: fin n) (c: t) (a b: fin n)
  : Lemma (col_add m target src c a b ==
           (if b = target then m a b + m a src * c else m a b)) = ()


(* Propositional-equality version of col_add_steps characterization.
   We use = (equatable eq) because the j=k column entries require
   ring axioms (zero*c=zero, one*c=c) that only give propositional equality. *)

let rec col_add_steps_eq_elim (#t:Type) {| f: field t |} (#n: pos)
  (v: fin n -> t) (k: fin n) (step: nat{step <= n})
  (i j: fin n)
  : Lemma (requires is_nonzero (v k))
          (ensures col_add_steps v k step i j =
                   (if j = k then
                      (if i = k then one
                       else if i < step then ((v i) * (inv (v k)))
                       else zero)
                    else (if i = j then one else zero)))
          (decreases step)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let one_t, zero_t = one #t, zero #t in
    if step = 0 then
      ()
    else begin
      let s : nat = step - 1 in
      col_add_steps_eq_elim v k (step - 1) i j;
      if s = k then begin
        (* col_add_steps v k step = prev (skip s=k). Postcondition at step 
           matches step-1 since the only difference is i<step vs i<step-1,
           and the gap is i=s=k which falls into the "i=k → one_t" branch. *)
        ()
      end
      else begin
        col_add_steps_eq_elim v k (step - 1) i j;
        col_add_steps_eq_elim v k (step - 1) i s;
        let prev = col_add_steps v k (step - 1) in
        let c : t = ((v s) * (inv (v k))) in
        col_add_at prev k s c i j;
        if j <> k then ()
        else begin
          (* j=k: col_add gives prev[i,k] + prev[i,s] * c *)
          let pik = prev i k in
          let pis = prev i s in
          if i = k then begin
            (* pik = one_t, pis = zero_t → one_t + zero_t*c = one_t *)
            mul_congruence pis c zero_t c;
            zero_mul_x c;
            add_congruence pik (pis * c) one_t zero_t;
            x_plus_zero one_t;
            transitivity (pik + pis * c) (one_t + zero_t) one_t
          end
          else if i = s then begin
            (* pik = zero_t, pis = one_t → zero_t + one_t*c = c *)
            mul_congruence pis c one_t c;
            one_mul_x c;
            add_congruence pik (pis * c) zero_t c;
            zero_plus_x c;
            transitivity (pik + pis * c) (zero_t + c) c
          end
          else if i < s then begin
            (* pik = v(i)*inv(vk), pis = zero_t → v(i)*inv(vk) + zero_t*c = v(i)*inv(vk) *)
            let vi_inv = ((v i) * (inv (v k))) in
            mul_congruence pis c zero_t c;
            zero_mul_x c;
            add_congruence pik (pis * c) vi_inv zero_t;
            x_plus_zero vi_inv;
            transitivity (pik + pis * c) (vi_inv + zero_t) vi_inv
          end
          else begin
            (* pik = zero_t, pis = zero_t → zero_t + zero_t*c = zero_t *)
            assert (pis = zero_t);
            assert (pik = zero_t);
            mul_congruence pis c zero_t c;
            zero_mul_x c;
            add_congruence pik (pis * c) zero_t zero_t;
            x_plus_zero zero_t;
            transitivity (pik + pis * c) (zero_t + zero_t) zero_t
          end
        end
      end
    end

(* Bridge: col_add_steps n and elim_matrix are propositionally equal *)
#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let col_add_steps_n_eq_elim (#t:Type) {| f: field t |} (#n: nat{n > 0})
  (v: fin n -> t) (k: fin n) (i j: fin n)
  : Lemma (requires is_nonzero (v k))
          (ensures col_add_steps v k n i j = elim_matrix v k i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    col_add_steps_eq_elim v k n i j;
    let inv_vk = inv (v k) in
    if (j <: nat) = (k <: nat) then begin
      if (i <: nat) = (k <: nat) then begin
        (* col_add_steps gives: one
           elim_matrix gives: v(k) * inv(v(k))
           Bridge: inversion_lemma gives mul (v k) (inv (v k)) = one *)
        f.f_sf.sf_mig.inversion_lemma (v k)
      end
      else begin
        (* Both give v(i) * inv(v(k)), since i < n always for i: fin n *)
        ()
      end
    end
    else begin
      (* Both give identity: if i=j then one else zero *)
      if (i <: nat) = (j <: nat) then reflexivity (one <: t)
      else reflexivity (zero <: t)
    end
#pop-options

(* ================================================================ *)
(*  Main theorem                                                     *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 0 --ifuel 0"
let null_vec_implies_det_zero (#t:Type) {| f: field t |} (#n: nat{n > 0})
  (m: square_matrix t n) (v: fin n -> t) (k: fin n)
  : Lemma (requires is_nonzero (v k) /\
                    (forall (i: fin n). null_vec_hyp m v i))
          (ensures det m = (zero <: t))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let e = elim_matrix v k in
    let me = matrix_mul m e in
    (* Step 1: me has zero column k *)
    let col_k_zero (i: fin n) : Lemma (me i k = (zero <: t))
      = me_col_k_is_zero m v k i
    in
    Classical.forall_intro col_k_zero;
    det_zero_column me k;
    (* det(me) = zero *)
    (* Step 2: det(me) = det(m) * det(e) *)
    det_mul m e;
    (* det(matrix_mul m e) = det m * det e *)
    (* Step 3: det(e) = one *)
    let e_steps = col_add_steps v k n in
    det_col_add_steps_eq_one v k n;
    (* det e_steps = one *)
    let pw (i j: fin n) : Lemma (e_steps i j = e i j)
      = col_add_steps_n_eq_elim v k i j
    in
    Classical.forall_intro_2 pw;
    det_pointwise_eq e_steps e;
    (* det e_steps = det e *)
    (* det e = one *)
    (* Step 4: det(m) * one = det(m) = det(me) = zero *)
    x_mul_one (det m);
    (* det m * one = det m *)
    mul_congruence (det m) (det e) (det m) (one <: t);
    (* det m * det e = det m * one *)
    (* det m * det e = det m *)
    (* det m * det e = det(me) *)
    (* det m = det(me) *)
    transitivity (det m) (det (matrix_mul m e)) (zero <: t)
    (* det m = zero *)
#pop-options

#pop-options  (* close the KernelDet+NullVec fuel-2 wrapper *)
