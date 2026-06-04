module Core.Matrix.ResultantConverse

(* ================================================================ *)
(*  Converse of the resultant theorem:                              *)
(*    resultant m_deg n_deg pp qq = 0  ==>  deg(gcd pp qq) >= 1.     *)
(*                                                                   *)
(*  Argument (see plan.md TASK 2):                                   *)
(*    1. resultant = det Syl = det (transpose Syl).                  *)
(*    2. det (Syl^T) = 0  ==>  exists null vector w of S^T rows.     *)
(*    3. combo_vec_surjective: w = combo_vec u v for u,v read off w. *)
(*    4. sylvester_action ==> coeff (u*pp + v*qq) j = 0 for all j     *)
(*       ==> u*pp + v*qq ~ 0.                                         *)
(*    5. not_both_zero: w nonzero ==> not (u ~ 0 /\ v ~ 0).           *)
(*    6. coprime endgame: coprime pp qq leads to contradiction, so   *)
(*       not coprime, i.e. deg(gcd) >= 1.                            *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module TC  = FStar.Tactics.Typeclasses
module L   = FStar.List.Tot
module H   = Core.Algebra.Helpers
module RES = Core.Matrix.Resultant
module RM  = Core.Matrix.ResultantMul
module KD  = Core.Matrix.KernelDet
module DET = Core.Matrix.Determinant
module SYL = Core.Matrix.Sylvester
module GC  = Core.Polynomial.GCD
module IR  = Core.Polynomial.Irreducible
module SF  = Core.Polynomial.SquareFree
module UN  = Core.Polynomial.Unique

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Helpers
open Core.Algebra.Divisibility
open Core.Algebra.Combinators
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Coeff
open Core.Polynomial.GCD
open Core.Permutation
open Core.Matrix
open Core.Matrix.Sylvester
open Core.Matrix.Determinant
open Core.Vector
open Core.FinSum

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ---------------------------------------------------------------- *)
(*  List builder: build_from off len g = [g off; ...; g (off+len-1)] *)
(* ---------------------------------------------------------------- *)

let rec build_from (#t:Type) (off: nat) (len: nat) (g: nat -> t)
  : Tot (l:list t {L.length l == len}) (decreases len)
  = if len = 0 then []
    else g off :: build_from #t (Prims.op_Addition off 1) (Prims.op_Subtraction len 1) g

let rec build_from_index (#t:Type) (off: nat) (len: nat) (g: nat -> t) (i: nat{i < len})
  : Lemma (ensures L.index (build_from off len g) i == g (Prims.op_Addition off i)) (decreases len)
  = if i = 0 then ()
    else build_from_index #t (Prims.op_Addition off 1) (Prims.op_Subtraction len 1) g (Prims.op_Subtraction i 1)

let rec trim_length_le (#t:Type) {| cr: commutative_ring t |} (cs: list t)
  : Lemma (ensures L.length (trim #t #cr cs) <= L.length cs) (decreases cs)
  = match cs with [] -> () | _ :: cs' -> trim_length_le #t #cr cs'

(* coeff (poly_mul a b) j = 0 once j+1 >= len a + len b *)
let poly_mul_coeff_high (#t:Type) {| cr: commutative_ring t |}
  (a b: polynomial t) (j: nat)
  : Lemma (requires j + 1 >= Prims.op_Addition (L.length a) (L.length b))
          (ensures  coeff (poly_mul a b) j = (zero <: t))
  = H.elim_equatable_laws t ();
    let g (i:nat) : t = coeff a i * coeff b (Prims.op_Subtraction j i) in
    coeff_poly_mul_named a b j g
      (fun (i:nat) -> reflexivity (coeff a i * coeff b (Prims.op_Subtraction j i)));
    sum_range_all_zero g 0 (L.length a)
      (fun (i:nat{0 <= i /\ i < L.length a}) ->
        assert (Prims.op_Subtraction j i >= L.length b);
        H.x_mul_zero (coeff a i));
    transitivity (coeff (poly_mul a b) j) (sum_range g 0 (L.length a)) (zero <: t)

(* vector_dot is congruent in its right argument (pointwise =) *)
#push-options "--z3rlimit 80"
let vector_dot_cong_right (#t:Type) {| cr: commutative_ring t |} (#n: pos)
  (a b1 b2: vector t n)
  (h: (j: fin n) -> Lemma (b1 j = b2 j))
  : Lemma (vector_dot a b1 = vector_dot a b2)
  = H.elim_equatable_laws t ();
    let per (k: fin n) : Lemma (pointwise_mul a b1 k = pointwise_mul a b2 k)
      = pointwise_mul_unfold a b1 k;
        pointwise_mul_unfold a b2 k;
        h k;
        reflexivity (a k);
        mul_congruence (a k) (b1 k) (a k) (b2 k);
        transitivity (pointwise_mul a b1 k) (a k * b1 k) (a k * b2 k);
        transitivity (pointwise_mul a b1 k) (a k * b2 k) (pointwise_mul a b2 k)
    in
    fin_sum_congruence (pointwise_mul a b1) (pointwise_mul a b2) per;
    vector_dot_reveal a b1;
    vector_dot_reveal a b2;
    transitivity (vector_dot a b1) (fin_sum (pointwise_mul a b1)) (fin_sum (pointwise_mul a b2));
    symmetry (vector_dot a b2) (fin_sum (pointwise_mul a b2));
    transitivity (vector_dot a b1) (fin_sum (pointwise_mul a b2)) (vector_dot a b2)
#pop-options

(* ---------------------------------------------------------------- *)
(*  Step 3: combo_vec_surjective                                     *)
(* ---------------------------------------------------------------- *)

(* index function reading w reversed in the u-block (j < n_deg) *)
let gu_idx (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (w: fin (Prims.op_Addition m_deg n_deg) -> t) (i: nat) : t
  = if i < n_deg
    then w (Prims.op_Subtraction (Prims.op_Subtraction n_deg 1) i <: fin (Prims.op_Addition m_deg n_deg))
    else (zero <: t)

(* index function reading w reversed in the v-block (j >= n_deg) *)
let gv_idx (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (w: fin (Prims.op_Addition m_deg n_deg) -> t) (i: nat) : t
  = if i < m_deg
    then w (Prims.op_Subtraction (Prims.op_Subtraction (Prims.op_Addition m_deg n_deg) 1) i
            <: fin (Prims.op_Addition m_deg n_deg))
    else (zero <: t)

let mk_u (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (w: fin (Prims.op_Addition m_deg n_deg) -> t) : polynomial t
  = trim (build_from 0 n_deg (gu_idx m_deg n_deg w))

let mk_v (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (w: fin (Prims.op_Addition m_deg n_deg) -> t) : polynomial t
  = trim (build_from 0 m_deg (gv_idx m_deg n_deg w))

let mk_u_length (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (w: fin (Prims.op_Addition m_deg n_deg) -> t)
  : Lemma (L.length (mk_u m_deg n_deg w) <= n_deg)
  = trim_length_le #t #cr (build_from 0 n_deg (gu_idx m_deg n_deg w))

let mk_v_length (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (w: fin (Prims.op_Addition m_deg n_deg) -> t)
  : Lemma (L.length (mk_v m_deg n_deg w) <= m_deg)
  = trim_length_le #t #cr (build_from 0 m_deg (gv_idx m_deg n_deg w))

let mk_u_coeff (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (w: fin (Prims.op_Addition m_deg n_deg) -> t) (i: nat{i < n_deg})
  : Lemma (coeff (mk_u m_deg n_deg w) i = gu_idx m_deg n_deg w i)
  = H.elim_equatable_laws t ();
    let lst = build_from 0 n_deg (gu_idx m_deg n_deg w) in
    coeff_trim lst i;
    build_from_index 0 n_deg (gu_idx m_deg n_deg w) i

let mk_v_coeff (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (w: fin (Prims.op_Addition m_deg n_deg) -> t) (i: nat{i < m_deg})
  : Lemma (coeff (mk_v m_deg n_deg w) i = gv_idx m_deg n_deg w i)
  = H.elim_equatable_laws t ();
    let lst = build_from 0 m_deg (gv_idx m_deg n_deg w) in
    coeff_trim lst i;
    build_from_index 0 m_deg (gv_idx m_deg n_deg w) i

(* combo_vec (mk_u) (mk_v) reproduces w at each index *)
#push-options "--z3rlimit 80"
let combo_vec_surjective (#t:Type) {| cr: commutative_ring t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (w: fin (Prims.op_Addition m_deg n_deg) -> t)
  (j: fin (Prims.op_Addition m_deg n_deg))
  : Lemma (RM.combo_vec m_deg n_deg (mk_u m_deg n_deg w) (mk_v m_deg n_deg w) j = w j)
  = H.elim_equatable_laws t ();
    let size = Prims.op_Addition m_deg n_deg in
    let u = mk_u m_deg n_deg w in
    let v = mk_v m_deg n_deg w in
    if (j <: nat) < n_deg then begin
      let i : nat = Prims.op_Subtraction (Prims.op_Subtraction n_deg 1) (j <: nat) in
      assert (i < n_deg);
      assert (RM.combo_vec m_deg n_deg u v j == coeff u i);
      mk_u_coeff m_deg n_deg w i;
      assert (gu_idx m_deg n_deg w i == w (j <: fin size))
    end
    else begin
      let i : nat = Prims.op_Subtraction (Prims.op_Subtraction m_deg 1)
                      (Prims.op_Subtraction (j <: nat) n_deg) in
      assert (i < m_deg);
      assert (RM.combo_vec m_deg n_deg u v j == coeff v i);
      mk_v_coeff m_deg n_deg w i;
      assert (gv_idx m_deg n_deg w i == w (j <: fin size))
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  Step 4 tail: all coeffs zero ==> poly_eq r poly_zero             *)
(* ---------------------------------------------------------------- *)

let all_coeffs_zero_poly_eq (#t:Type) {| cr: commutative_ring t |}
  (r: polynomial t)
  : Lemma (requires (forall (i:nat). coeff r i = (zero <: t)))
          (ensures  poly_eq r (poly_zero #t))
  = H.elim_equatable_laws t ();
    let aux (j:nat) : Lemma (coeff r j = coeff (poly_zero #t) j)
      = reflexivity (coeff r j) in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq r (poly_zero #t)

(* ---------------------------------------------------------------- *)
(*  Step 4: the combination polynomial u*pp + v*qq vanishes          *)
(* ---------------------------------------------------------------- *)

(* coeff s k = 0 for indices k in [0, size): via sylvester_action.    *)
#push-options "--z3rlimit 120 --fuel 2"
let s_coeff_zero_low (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (pp qq: polynomial t)
  (w: fin (Prims.op_Addition m_deg n_deg) -> t)
  (k: nat{k < Prims.op_Addition m_deg n_deg})
  : Lemma (requires (let cr = cr_of_id t #(id_of_f t) in
                     let st = transpose (sylvester_matrix #t #cr m_deg n_deg pp qq) in
                     forall (i: fin (Prims.op_Addition m_deg n_deg)).
                        vector_dot #t #cr.cr_r (row st i) w = (zero <: t)))
          (ensures (let cr = cr_of_id t #(id_of_f t) in
                    coeff (poly_add (poly_mul (mk_u m_deg n_deg w) pp)
                                    (poly_mul (mk_v m_deg n_deg w) qq)) k = (zero <: t)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let size : pos = Prims.op_Addition m_deg n_deg in
    let u = mk_u m_deg n_deg w in
    let v = mk_v m_deg n_deg w in
    let st = transpose (sylvester_matrix #t #cr m_deg n_deg pp qq) in
    let i : fin size = Prims.op_Subtraction (Prims.op_Subtraction size 1) k in
    mk_u_length m_deg n_deg w;
    mk_v_length m_deg n_deg w;
    (* sylvester_action: vector_dot (row st i) (combo_vec u v) = coeff s (size-1-i) = coeff s k *)
    RM.sylvester_action #t #cr m_deg n_deg pp qq u v i;
    (* combo_vec u v = w pointwise, so vector_dot (row st i) (combo_vec u v) = vector_dot (row st i) w = 0 *)
    let cv = RM.combo_vec m_deg n_deg u v in
    vector_dot_cong_right #t #cr (row st i) cv w
      (fun (jj: fin size) -> combo_vec_surjective m_deg n_deg w jj);
    assert (vector_dot #t #cr.cr_r (row st i) w = (zero <: t));
    transitivity (vector_dot #t #cr.cr_r (row st i) cv) (vector_dot #t #cr.cr_r (row st i) w) (zero <: t);
    assert (Prims.op_Subtraction (Prims.op_Subtraction size 1) (i <: nat) == k);
    symmetry (vector_dot #t #cr.cr_r (row st i) cv)
             (coeff (poly_add (poly_mul u pp) (poly_mul v qq)) k);
    transitivity (coeff (poly_add (poly_mul u pp) (poly_mul v qq)) k)
                 (vector_dot #t #cr.cr_r (row st i) cv)
                 (zero <: t)
#pop-options

(* coeff s k = 0 for indices k >= size: via degree/length bound.      *)
#push-options "--z3rlimit 100"
let s_coeff_zero_high (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (pp qq: polynomial t)
  (w: fin (Prims.op_Addition m_deg n_deg) -> t)
  (k: nat{k >= Prims.op_Addition m_deg n_deg})
  : Lemma (requires L.length pp <= Prims.op_Addition m_deg 1 /\
                    L.length qq <= Prims.op_Addition n_deg 1)
          (ensures (let cr = cr_of_id t #(id_of_f t) in
                    coeff (poly_add (poly_mul (mk_u m_deg n_deg w) pp)
                                    (poly_mul (mk_v m_deg n_deg w) qq)) k = (zero <: t)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let u = mk_u m_deg n_deg w in
    let v = mk_v m_deg n_deg w in
    mk_u_length m_deg n_deg w;   (* len u <= n_deg *)
    mk_v_length m_deg n_deg w;   (* len v <= m_deg *)
    poly_mul_coeff_high #t #cr u pp k;   (* k+1 >= n_deg + (m_deg+1) >= len u + len pp *)
    poly_mul_coeff_high #t #cr v qq k;   (* k+1 >= m_deg + (n_deg+1) >= len v + len qq *)
    poly_add_coeff (poly_mul u pp) (poly_mul v qq) k;
    H.x_plus_zero (zero <: t);
    add_congruence (coeff (poly_mul u pp) k) (coeff (poly_mul v qq) k)
                   (zero <: t) (zero <: t);
    transitivity (coeff (poly_add (poly_mul u pp) (poly_mul v qq)) k)
                 (coeff (poly_mul u pp) k + coeff (poly_mul v qq) k)
                 ((zero <: t) + (zero <: t));
    transitivity (coeff (poly_add (poly_mul u pp) (poly_mul v qq)) k)
                 ((zero <: t) + (zero <: t))
                 (zero <: t)
#pop-options

(* The combination polynomial u*pp + v*qq is poly_eq to zero.         *)
#push-options "--z3rlimit 80"
let s_is_zero (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (pp qq: polynomial t)
  (w: fin (Prims.op_Addition m_deg n_deg) -> t)
  : Lemma (requires (let cr = cr_of_id t #(id_of_f t) in
                     L.length pp <= Prims.op_Addition m_deg 1 /\
                     L.length qq <= Prims.op_Addition n_deg 1 /\
                     (let st = transpose (sylvester_matrix #t #cr m_deg n_deg pp qq) in
                      forall (i: fin (Prims.op_Addition m_deg n_deg)).
                         vector_dot #t #cr.cr_r (row st i) w = (zero <: t))))
          (ensures (let cr = cr_of_id t #(id_of_f t) in
                    poly_eq (poly_add (poly_mul (mk_u m_deg n_deg w) pp)
                                      (poly_mul (mk_v m_deg n_deg w) qq)) (poly_zero #t)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let size = Prims.op_Addition m_deg n_deg in
    let s = poly_add (poly_mul (mk_u m_deg n_deg w) pp) (poly_mul (mk_v m_deg n_deg w) qq) in
    let all_zero (k: nat) : Lemma (coeff s k = (zero <: t))
      = if k < size then s_coeff_zero_low #t #f m_deg n_deg pp qq w k
        else s_coeff_zero_high #t #f m_deg n_deg pp qq w k
    in
    Classical.forall_intro all_zero;
    all_coeffs_zero_poly_eq #t #cr s
#pop-options

(* ---------------------------------------------------------------- *)
(*  Step 5: not both u and v are zero (since w has a nonzero entry)   *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 80"
let not_both_zero (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (w: fin (Prims.op_Addition m_deg n_deg) -> t)
  (k: fin (Prims.op_Addition m_deg n_deg))
  : Lemma (requires is_nonzero (w k))
          (ensures  not (poly_eq (mk_u m_deg n_deg w) (poly_zero #t) /\
                         poly_eq (mk_v m_deg n_deg w) (poly_zero #t)))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let u = mk_u m_deg n_deg w in
    let v = mk_v m_deg n_deg w in
    let contra () : Lemma (requires poly_eq u (poly_zero #t) /\ poly_eq v (poly_zero #t))
                          (ensures  False)
      = combo_vec_surjective m_deg n_deg w k;
        (* combo_vec u v k = w k; but combo_vec entries are coeffs of u or v, both ~0 *)
        if (k <: nat) < n_deg then begin
          let i : nat = Prims.op_Subtraction (Prims.op_Subtraction n_deg 1) (k <: nat) in
          assert (RM.combo_vec m_deg n_deg u v k == coeff u i);
          poly_eq_means_equal_coeffs u (poly_zero #t) i;
          assert (coeff u i = (zero <: t));
          assert (w k = (zero <: t))
        end
        else begin
          let i : nat = Prims.op_Subtraction (Prims.op_Subtraction m_deg 1)
                          (Prims.op_Subtraction (k <: nat) n_deg) in
          assert (RM.combo_vec m_deg n_deg u v k == coeff v i);
          poly_eq_means_equal_coeffs v (poly_zero #t) i;
          assert (coeff v i = (zero <: t));
          assert (w k = (zero <: t))
        end
    in
    Classical.move_requires contra ()
#pop-options

(* ---------------------------------------------------------------- *)
(*  Step 6: divisibility relation + coprime endgame                  *)
(* ---------------------------------------------------------------- *)

(* generic comm-group: a + b = 0 ==> a = neg b *)
let add_eq_zero_gives_eq_neg (#t:Type) {| acg: add_comm_group t |} (a b: t)
  : Lemma (requires (a + b) = (zero <: t))
          (ensures  a = neg b)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    x_plus_neg_x b; reflexivity a;
    add_congruence a (b + neg b) a (zero <: t);
    x_plus_zero a;
    transitivity (a + (b + neg b)) (a + (zero <: t)) a;
    add_associativity a b (neg b);
    transitivity ((a + b) + neg b) (a + (b + neg b)) a;
    reflexivity (neg b);
    add_congruence (a + b) (neg b) (zero <: t) (neg b);
    zero_plus_x (neg b);
    transitivity ((a + b) + neg b) ((zero <: t) + neg b) (neg b);
    symmetry ((a + b) + neg b) (neg b);
    symmetry ((a + b) + neg b) a;
    transitivity (neg b) ((a + b) + neg b) a;
    symmetry (neg b) a

(* from u*pp + v*qq ~ 0, derive qq | u*pp *)
let relation_gives_div (#t:Type) {| f: field t |}
  (u v pp qq: polynomial t)
  : Lemma (requires poly_eq (poly_add (poly_mul u pp) (poly_mul v qq)) (poly_zero #t))
          (ensures  divides qq (poly_mul u pp))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    let acg : add_comm_group (polynomial t) = polynomial_acg cr in
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a = poly_mul u pp in
    let b = poly_mul v qq in
    polynomial_acg_add_reveal #t cr a b;
    polynomial_acg_zero_reveal #t cr;
    polynomial_acg_eq_reveal #t cr (poly_add a b) (poly_zero #t);
    assert (acg.add a b == poly_add a b);
    add_eq_zero_gives_eq_neg #(polynomial t) #acg a b;
    polynomial_acg_neg_reveal #t cr b;
    assert (poly_eq a (poly_neg b));
    poly_mul_commutativity v qq;
    divides_intro qq (poly_mul qq v) v;
    divides_congruence_right qq (poly_mul qq v) (poly_mul v qq);
    divides_neg qq (poly_mul v qq);
    poly_eq_symmetry a (poly_neg b);
    divides_congruence_right qq (poly_neg b) a

(* given the relation and not-both-zero, coprime pp qq is impossible *)
let not_coprime_endgame (#t:Type) {| f: field t |}
  (u v pp qq: polynomial t)
  : Lemma (requires
      poly_eq (poly_add (poly_mul u pp) (poly_mul v qq)) (poly_zero #t) /\
      divides qq (poly_mul u pp) /\
      not (poly_eq u (poly_zero #t) /\ poly_eq v (poly_zero #t)) /\
      Some? (poly_deg pp) /\ Some? (poly_deg qq) /\
      (None? (poly_deg u) \/ Some?.v (poly_deg u) < Some?.v (poly_deg qq)))
    (ensures  not (coprime #t #f pp qq))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let contra () : Lemma (requires coprime #t #f pp qq) (ensures False)
      = IR.coprime_symmetric #t #f pp qq;
        euclid_lemma #t #f qq pp u;
        (match poly_deg u with
         | Some _ ->
             IR.divides_degree_le #t #f qq u
         | None ->
             UN.degree_none_poly_eq_zero u;
             poly_eq_reflexivity pp;
             poly_mul_congruence u pp (poly_zero #t) pp;
             assert (poly_mul (poly_zero #t) pp == (poly_zero #t));
             poly_eq_reflexivity (poly_mul v qq);
             poly_add_congruence (poly_mul u pp) (poly_mul v qq) (poly_zero #t) (poly_mul v qq);
             poly_add_zero (poly_mul v qq);
             poly_eq_symmetry (poly_add (poly_zero #t) (poly_mul v qq)) (poly_mul v qq);
             poly_eq_symmetry (poly_add (poly_mul u pp) (poly_mul v qq)) (poly_zero #t);
             poly_eq_transitivity (poly_mul v qq)
                (poly_add (poly_zero #t) (poly_mul v qq))
                (poly_add (poly_mul u pp) (poly_mul v qq));
             poly_eq_transitivity (poly_mul v qq)
                (poly_add (poly_mul u pp) (poly_mul v qq)) (poly_zero #t);
             poly_domain_law v qq)
    in
    Classical.move_requires contra ()

(* gcd of (pp, qq) with qq nonzero has a degree *)
let gcd_pos (#t:Type) {| f: field t |}
  (pp qq: polynomial t)
  : Lemma (requires Some? (poly_deg qq))
          (ensures  Some? (poly_deg (poly_gcd #t #f pp qq)))
  = H.elim_equatable_laws (polynomial t) ();
    let g = poly_gcd #t #f pp qq in
    gcd_divides_right #t #f pp qq;
    match poly_deg g with
    | Some _ -> ()
    | None ->
        UN.degree_none_poly_eq_zero g;
        poly_eq_symmetry g (poly_zero #t);
        divides_congruence_left g (poly_zero #t) qq;
        eliminate exists (c: polynomial t). poly_eq qq (poly_mul (poly_zero #t) c)
        returns False
        with _hyp.
          begin
            assert (poly_mul (poly_zero #t) c == (poly_zero #t));
            UN.degree_well_defined qq (poly_zero #t)
          end

(* when pp ~ 0, gcd(pp,qq) has the same degree as qq *)
#push-options "--z3rlimit 120"
let gcd_deg_when_pp_zero (#t:Type) {| f: field t |}
  (pp qq: polynomial t)
  : Lemma (requires None? (poly_deg pp) /\ Some? (poly_deg qq))
          (ensures  Some? (poly_deg (poly_gcd #t #f pp qq)) /\
                    Some?.v (poly_deg (poly_gcd #t #f pp qq)) == Some?.v (poly_deg qq))
  = H.elim_equatable_laws (polynomial t) ();
    let g = poly_gcd #t #f pp qq in
    gcd_pos #t #f pp qq;
    gcd_divides_right #t #f pp qq;
    IR.divides_degree_le #t #f g qq;
    UN.degree_none_poly_eq_zero pp;
    divides_zero #(polynomial t) qq;
    poly_eq_symmetry pp (poly_zero #t);
    divides_congruence_right qq (poly_zero #t) pp;
    divides_refl #(polynomial t) qq;
    gcd_is_maximal #t #f pp qq qq;
    IR.divides_degree_le #t #f qq g
#pop-options

(* ---------------------------------------------------------------- *)
(*  Main theorem: resultant = 0 ==> deg(gcd) >= 1                     *)
(* ---------------------------------------------------------------- *)

(* core step given the null vector w with nonzero entry at k *)
#push-options "--z3rlimit 120 --fuel 2"
let resultant_converse_core (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (pp qq: polynomial t)
  (w: fin (Prims.op_Addition m_deg n_deg) -> t)
  (k: fin (Prims.op_Addition m_deg n_deg))
  : Lemma (requires (let cr = cr_of_id t #(id_of_f t) in
                     L.length pp <= Prims.op_Addition m_deg 1 /\
                     L.length qq <= Prims.op_Addition n_deg 1 /\
                     Some? (poly_deg qq) /\ Some?.v (poly_deg qq) == n_deg /\ n_deg >= 1 /\
                     is_nonzero (w k) /\
                     (let st = transpose (sylvester_matrix #t #cr m_deg n_deg pp qq) in
                      forall (i: fin (Prims.op_Addition m_deg n_deg)).
                         vector_dot #t #cr.cr_r (row st i) w = (zero <: t))))
          (ensures  Some? (poly_deg (poly_gcd #t #f pp qq)) /\
                    Some?.v (poly_deg (poly_gcd #t #f pp qq)) >= 1)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws (polynomial t) ();
    let u = mk_u m_deg n_deg w in
    let v = mk_v m_deg n_deg w in
    s_is_zero #t #f m_deg n_deg pp qq w;
    gcd_pos #t #f pp qq;
    (match poly_deg pp with
     | None -> gcd_deg_when_pp_zero #t #f pp qq
     | Some _ ->
         relation_gives_div #t #f u v pp qq;
         not_both_zero #t #f m_deg n_deg w k;
         mk_u_length m_deg n_deg w;
         not_coprime_endgame #t #f u v pp qq;
         coprime_reveal #t #f pp qq)
#pop-options

let resultant_converse (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (pp qq: polynomial t)
  : Lemma (requires RES.resultant #t #(cr_of_id t #(id_of_f t)) m_deg n_deg pp qq = (zero <: t) /\
                    L.length pp <= Prims.op_Addition m_deg 1 /\
                    L.length qq <= Prims.op_Addition n_deg 1 /\
                    Some? (poly_deg qq) /\ Some?.v (poly_deg qq) == n_deg /\ n_deg >= 1)
          (ensures  Some? (poly_deg (GC.poly_gcd #t #f pp qq)) /\
                    Some?.v (poly_deg (GC.poly_gcd #t #f pp qq)) >= 1)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let sm = sylvester_matrix #t #cr m_deg n_deg pp qq in
    let st = transpose sm in
    RES.resultant_unfold #t #cr m_deg n_deg pp qq;
    det_transpose #t #cr sm;
    transitivity (det st) (det sm) (zero <: t);
    KD.det_zero_implies_null_vec #t #f st;
    eliminate exists (w: fin (Prims.op_Addition m_deg n_deg) -> t)
                     (k: fin (Prims.op_Addition m_deg n_deg)).
                is_nonzero (w k) /\
                (forall (i: fin (Prims.op_Addition m_deg n_deg)).
                   vector_dot #t #cr.cr_r (row st i) w = (zero <: t))
    returns Some? (poly_deg (GC.poly_gcd #t #f pp qq)) /\
            Some?.v (poly_deg (GC.poly_gcd #t #f pp qq)) >= 1
    with _hyp.
      resultant_converse_core #t #f m_deg n_deg pp qq w k

(* ================================================================ *)
(*  The full matrix-level equivalence (forward + converse):          *)
(*    resultant m n pp qq = 0  <==>  deg(gcd pp qq) >= 1.            *)
(*  (pp nonzero; forward = resultant_zero_of_common_divisor,         *)
(*   backward = resultant_converse.)                                 *)
(* ================================================================ *)
#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let resultant_vanishing_iff (#t:Type) {| f: field t |}
  (m_deg n_deg: nat{Prims.op_Addition m_deg n_deg > 0})
  (pp qq: polynomial t)
  : Lemma (requires L.length pp <= Prims.op_Addition m_deg 1 /\
                    L.length qq <= Prims.op_Addition n_deg 1 /\
                    Some? (poly_deg pp) /\ Some?.v (poly_deg pp) <= m_deg /\
                    Some? (poly_deg qq) /\ Some?.v (poly_deg qq) == n_deg /\ n_deg >= 1)
          (ensures  (RES.resultant #t #(cr_of_id t #(id_of_f t)) m_deg n_deg pp qq = (zero <: t))
                    <==>
                    (Some? (poly_deg (GC.poly_gcd #t #f pp qq)) /\
                     Some?.v (poly_deg (GC.poly_gcd #t #f pp qq)) >= 1))
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    let g = GC.poly_gcd #t #f pp qq in
    let bwd () : Lemma (requires RES.resultant #t #cr m_deg n_deg pp qq = (zero <: t))
                       (ensures  Some? (poly_deg g) /\ Some?.v (poly_deg g) >= 1)
      = resultant_converse #t #f m_deg n_deg pp qq in
    let fwd () : Lemma (requires Some? (poly_deg g) /\ Some?.v (poly_deg g) >= 1)
                       (ensures  RES.resultant #t #cr m_deg n_deg pp qq = (zero <: t))
      = GC.gcd_divides_left  #t #f pp qq;
        GC.gcd_divides_right #t #f pp qq;
        RES.resultant_zero_of_common_divisor #t #f m_deg n_deg pp qq g in
    FStar.Classical.move_requires bwd ();
    FStar.Classical.move_requires fwd ()
#pop-options
