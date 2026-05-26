module Core.Matrix.Ring

(*
  Multiplicative tower for square matrices.

  Given `{| r: ring t |}` we lift the structure to `square_matrix t n`
  and provide a `ring (square_matrix t n)` instance.

  Ported from FStar.CAS.Matrix.Ring into the diamond-free `core/` tower.
  Differences from the old version:
  - Old tower had a separate `semiring` class with explicit `sr_zero_absorb_l/r`
    fields. The new tower has only `ring`; the zero-absorption is a derived
    fact `zero_mul_x` / `x_mul_zero` in `Core.Algebra.Helpers`.
  - Old `mul_one_l/r` → new `one_mul_x` / `x_mul_one` (in Helpers).
  - We deliberately omit any semiring instance — there's no such class.
*)

module TC = FStar.Tactics.Typeclasses

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Algebra.Helpers
open Core.FinSum
open Core.Permutation
open Core.Matrix

(* ----------------------------------------------------------------- *)
(*  Congruence of matrix_mul                                         *)
(* ----------------------------------------------------------------- *)

let matrix_mul_pointwise_congruence
  (#t: Type) {| r: ring t |} (#n: nat)
  (a b c d: square_matrix t n) (i j: fin n)
  : Lemma (requires matrix_eq a c /\ matrix_eq b d)
          (ensures matrix_mul a b i j = matrix_mul c d i j)
  = let pf (k: fin n) : Lemma (a i k * b k j = c i k * d k j)
      = r.mul_congruence (a i k) (b k j) (c i k) (d k j)
    in
    Classical.forall_intro pf;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> a i k * b k j)
      (fun (k: fin n) -> c i k * d k j) (fun _ -> ())

let matrix_mul_congruence
  (#t: Type) {| r: ring t |} (#n: nat)
  (a b c d: square_matrix t n)
  : Lemma (requires matrix_eq_bool a c /\ matrix_eq_bool b d)
          (ensures matrix_eq_bool (matrix_mul a b) (matrix_mul c d))
  = matrix_eq_bool_iff_pointwise a c;
    matrix_eq_bool_iff_pointwise b d;
    let pf (i j: fin n) : Lemma (matrix_mul a b i j = matrix_mul c d i j)
      = matrix_mul_pointwise_congruence a b c d i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul a b) (matrix_mul c d)

(* ----------------------------------------------------------------- *)
(*  Left/right identities                                            *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_mul_left_identity_pointwise
  (#t: Type) {| r: ring t |} (#n: nat)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (id_matrix n) a i j = a i j)
  = elim_equatable_laws t ();
    let id_mat = id_matrix #t #r n in
    let pf (k: fin n) : Lemma
        (id_mat i k * a k j
         = (if (i <: nat) = (k <: nat) then one else zero #t) * a k j)
      = assert_norm (id_mat i k == (if (i <: nat) = (k <: nat) then r.one else r.r_add.zero));
        reflexivity (id_mat i k * a k j)
    in
    Classical.forall_intro pf;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> id_mat i k * a k j)
      (fun (k: fin n) -> (if (i <: nat) = (k <: nat) then one else zero #t) * a k j) (fun _ -> ());
    let g_row : fin n -> t = fun (k: fin n) -> a k j in
    let pf2 (k: fin n) : Lemma ((fun (k: fin n) -> (if (i <: nat) = (k <: nat) then one else zero #t) * a k j) k
                              = pointwise_mul (fin_kronecker_delta i) g_row k)
      = pointwise_mul_unfold (fin_kronecker_delta i) g_row k;
        fin_kronecker_delta_unfold #t i k;
        reflexivity ((if (i <: nat) = (k <: nat) then one else zero #t) * g_row k);
        symmetry (pointwise_mul (fin_kronecker_delta i) g_row k)
                 ((if (i <: nat) = (k <: nat) then one else zero #t) * g_row k)
    in
    Classical.forall_intro pf2;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> (if (i <: nat) = (k <: nat) then one else zero #t) * a k j)
      (pointwise_mul (fin_kronecker_delta i) g_row) (fun _ -> ());
    fin_sum_kronecker i g_row;
    trans3
      (fin_sum (fun (k: fin n) -> id_mat i k * a k j))
      (fin_sum (fun (k: fin n) ->
         (if (i <: nat) = (k <: nat) then one else zero #t) * a k j))
      (fin_sum (pointwise_mul (fin_kronecker_delta i) g_row))
      (a i j);
    matrix_mul_eq_at id_mat a i j
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_mul_right_identity_pointwise
  (#t: Type) {| r: ring t |} (#n: nat)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a (id_matrix n) i j = a i j)
  = elim_equatable_laws t ();
    let id_mat = id_matrix #t #r n in
    let pf (k: fin n) : Lemma
        (a i k * id_mat k j
         = (if (j <: nat) = (k <: nat) then one else zero #t) * a i k)
      = assert_norm (id_mat k j == (if (k <: nat) = (j <: nat) then r.one else r.r_add.zero));
        if (k <: nat) = (j <: nat) then begin
          x_mul_one (a i k);
          one_mul_x (a i k);
          symmetry (one * a i k) (a i k);
          transitivity (a i k * id_mat k j) (a i k) (one * a i k)
        end else begin
          x_mul_zero (a i k);
          zero_mul_x (a i k);
          symmetry (zero * a i k) (zero #t);
          transitivity (a i k * id_mat k j) (zero #t) (zero * a i k)
        end
    in
    Classical.forall_intro pf;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> a i k * id_mat k j)
      (fun (k: fin n) -> (if (j <: nat) = (k <: nat) then one else zero #t) * a i k) (fun _ -> ());
    let g_row : fin n -> t = fun (k: fin n) -> a i k in
    let pf2 (k: fin n) : Lemma ((fun (k: fin n) -> (if (j <: nat) = (k <: nat) then one else zero #t) * a i k) k
                              = pointwise_mul (fin_kronecker_delta j) g_row k)
      = pointwise_mul_unfold (fin_kronecker_delta j) g_row k;
        fin_kronecker_delta_unfold #t j k;
        reflexivity ((if (j <: nat) = (k <: nat) then one else zero #t) * g_row k);
        symmetry (pointwise_mul (fin_kronecker_delta j) g_row k)
                 ((if (j <: nat) = (k <: nat) then one else zero #t) * g_row k)
    in
    Classical.forall_intro pf2;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> (if (j <: nat) = (k <: nat) then one else zero #t) * a i k)
      (pointwise_mul (fin_kronecker_delta j) g_row) (fun _ -> ());
    fin_sum_kronecker j g_row;
    trans3
      (fin_sum (fun (k: fin n) -> a i k * id_mat k j))
      (fin_sum (fun (k: fin n) ->
         (if (j <: nat) = (k <: nat) then one else zero #t) * a i k))
      (fin_sum (pointwise_mul (fin_kronecker_delta j) g_row))
      (a i j);
    matrix_mul_eq_at a id_mat i j
#pop-options

let matrix_mul_left_identity
  (#t: Type) {| r: ring t |} (#n: nat) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul (id_matrix n) a) a)
  = let id_mat = id_matrix #t #r n in
    let pf (i j: fin n) : Lemma (matrix_mul id_mat a i j = a i j)
      = matrix_mul_left_identity_pointwise a i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul id_mat a) a

let matrix_mul_right_identity
  (#t: Type) {| r: ring t |} (#n: nat) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul a (id_matrix n)) a)
  = let id_mat = id_matrix #t #r n in
    let pf (i j: fin n) : Lemma (matrix_mul a id_mat i j = a i j)
      = matrix_mul_right_identity_pointwise a i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul a id_mat) a

(* ----------------------------------------------------------------- *)
(*  Associativity                                                    *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let matrix_mul_associativity_pointwise
  (#t: Type) {| r: ring t |} (#n: nat)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (matrix_mul a b) c i j
        = matrix_mul a (matrix_mul b c) i j)
  = elim_equatable_laws t ();
    let ab = matrix_mul a b in
    let bc = matrix_mul b c in

    let pf_A (l: fin n) : Lemma
      (ab i l * c l j
       = fin_sum (fun (k: fin n) -> a i k * b k l) * c l j)
      = matrix_mul_eq_at a b i l;
        reflexivity (fin_sum (fun (k: fin n) -> a i k * b k l) * c l j)
    in
    Classical.forall_intro pf_A;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (l: fin n) -> ab i l * c l j)
      (fun (l: fin n) -> fin_sum (fun (k: fin n) -> a i k * b k l) * c l j) (fun _ -> ());

    let pf_B (l: fin n) : Lemma
      (fin_sum (fun (k: fin n) -> a i k * b k l) * c l j
       = fin_sum (fun (k: fin n) -> (a i k * b k l) * c l j))
      = elim_equatable_laws t ();
        trans_for_calc t ();
        fin_sum_mul_right (fun (k: fin n) -> a i k * b k l) (c l j);
        (* gives: fin_sum (fun k -> a i k * b k l) * c l j
                = fin_sum (pointwise_mul (fun k -> a i k * b k l) (const (c l j))) *)
        let pwk (k: fin n) : Lemma
          (pointwise_mul (fun (k: fin n) -> a i k * b k l) (const (c l j)) k
           = (a i k * b k l) * c l j)
          = pointwise_mul_unfold (fun (k: fin n) -> a i k * b k l) (const (c l j)) k;
            const_unfold (c l j) k;
            reflexivity ((a i k * b k l) * c l j);
            symmetry (pointwise_mul (fun (k: fin n) -> a i k * b k l) (const (c l j)) k)
                     ((a i k * b k l) * c l j) in
        fin_sum_congruence
          (pointwise_mul (fun (k: fin n) -> a i k * b k l) (const (c l j)))
          (fun (k: fin n) -> (a i k * b k l) * c l j) pwk;
        transitivity (fin_sum (fun (k: fin n) -> a i k * b k l) * c l j)
                     (fin_sum (pointwise_mul (fun (k: fin n) -> a i k * b k l) (const (c l j))))
                     (fin_sum (fun (k: fin n) -> (a i k * b k l) * c l j))
    in
    Classical.forall_intro pf_B;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (l: fin n) -> fin_sum (fun (k: fin n) -> a i k * b k l) * c l j)
      (fun (l: fin n) -> fin_sum (fun (k: fin n) -> (a i k * b k l) * c l j)) (fun _ -> ());

    let pf_C (l: fin n) : Lemma
      (fin_sum (fun (k: fin n) -> (a i k * b k l) * c l j)
       = fin_sum (fun (k: fin n) -> a i k * (b k l * c l j)))
      = let pfk (k: fin n) : Lemma ((a i k * b k l) * c l j
                                  = a i k * (b k l * c l j))
          = r.mul_associativity (a i k) (b k l) (c l j)
        in
        Classical.forall_intro pfk;
        fin_sum_congruence #t #(acg_of_r t #r) #n
          (fun (k: fin n) -> (a i k * b k l) * c l j)
          (fun (k: fin n) -> a i k * (b k l * c l j)) (fun _ -> ())
    in
    Classical.forall_intro pf_C;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (l: fin n) -> fin_sum (fun (k: fin n) -> (a i k * b k l) * c l j))
      (fun (l: fin n) -> fin_sum (fun (k: fin n) -> a i k * (b k l * c l j))) (fun _ -> ());

    fin_sum_swap #t #(acg_of_r t #r) #n
      (fun (l: fin n) (k: fin n) -> a i k * (b k l * c l j));
    (* gives: fin_sum (fin_sum_curry F) = fin_sum (fin_sum_curry (swap_args F))
       where F = (fun l k -> a i k * (b k l * c l j))
       After fin_sum_curry unfold:
         LHS = fin_sum (fun l -> fin_sum ((fun l k -> ...) l))
             = fin_sum (fun l -> fin_sum (fun k -> a i k * (b k l * c l j)))
         RHS = fin_sum (fun k -> fin_sum (swap_args F k))
       We bridge the RHS to the lambda shape via swap_args_unfold.        *)
    let pf_rhs (k: fin n) : Lemma
      (fin_sum (swap_args (fun (l: fin n) (k: fin n) -> a i k * (b k l * c l j)) k)
       = fin_sum (fun (l: fin n) -> a i k * (b k l * c l j)))
      = let inner_pf (l: fin n) : Lemma
          (swap_args (fun (l: fin n) (k: fin n) -> a i k * (b k l * c l j)) k l
           = a i k * (b k l * c l j))
          = swap_args_unfold (fun (l: fin n) (k: fin n) -> a i k * (b k l * c l j)) k l;
            reflexivity (a i k * (b k l * c l j));
            symmetry (swap_args (fun (l: fin n) (k: fin n) -> a i k * (b k l * c l j)) k l)
                     (a i k * (b k l * c l j)) in
        fin_sum_congruence
          (swap_args (fun (l: fin n) (k: fin n) -> a i k * (b k l * c l j)) k)
          (fun (l: fin n) -> a i k * (b k l * c l j)) inner_pf in
    Classical.forall_intro pf_rhs;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> fin_sum (swap_args (fun (l: fin n) (k: fin n) -> a i k * (b k l * c l j)) k))
      (fun (k: fin n) -> fin_sum (fun (l: fin n) -> a i k * (b k l * c l j))) (fun _ -> ());
    transitivity
      (fin_sum (fun (l: fin n) -> fin_sum (fun (k: fin n) -> a i k * (b k l * c l j))))
      (fin_sum (fun (k: fin n) -> fin_sum (swap_args (fun (l: fin n) (k: fin n) -> a i k * (b k l * c l j)) k)))
      (fin_sum (fun (k: fin n) -> fin_sum (fun (l: fin n) -> a i k * (b k l * c l j))));

    let pf_E (k: fin n) : Lemma
      (fin_sum (fun (l: fin n) -> a i k * (b k l * c l j))
       = a i k * fin_sum (fun (l: fin n) -> b k l * c l j))
      = elim_equatable_laws t ();
        trans_for_calc t ();
        fin_sum_mul_left (a i k) (fun (l: fin n) -> b k l * c l j);
        (* gives: a i k * fin_sum (fun l -> b k l * c l j)
                = fin_sum (pointwise_mul (const (a i k)) (fun l -> b k l * c l j))     *)
        let pwl (l: fin n) : Lemma
          (pointwise_mul (const (a i k)) (fun (l: fin n) -> b k l * c l j) l
           = a i k * (b k l * c l j))
          = pointwise_mul_unfold (const (a i k)) (fun (l: fin n) -> b k l * c l j) l;
            const_unfold (a i k) l;
            reflexivity (a i k * (b k l * c l j));
            symmetry (pointwise_mul (const (a i k)) (fun (l: fin n) -> b k l * c l j) l)
                     (a i k * (b k l * c l j)) in
        fin_sum_congruence
          (pointwise_mul (const (a i k)) (fun (l: fin n) -> b k l * c l j))
          (fun (l: fin n) -> a i k * (b k l * c l j)) pwl;
        symmetry (a i k * fin_sum (fun (l: fin n) -> b k l * c l j))
                 (fin_sum (pointwise_mul (const (a i k)) (fun (l: fin n) -> b k l * c l j)));
        transitivity
          (fin_sum (fun (l: fin n) -> a i k * (b k l * c l j)))
          (fin_sum (pointwise_mul (const (a i k)) (fun (l: fin n) -> b k l * c l j)))
          (a i k * fin_sum (fun (l: fin n) -> b k l * c l j))
    in
    Classical.forall_intro pf_E;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> fin_sum (fun (l: fin n) -> a i k * (b k l * c l j)))
      (fun (k: fin n) -> a i k * fin_sum (fun (l: fin n) -> b k l * c l j)) (fun _ -> ());

    let pf_F (k: fin n) : Lemma
      (a i k * fin_sum (fun (l: fin n) -> b k l * c l j) = a i k * bc k j)
      = matrix_mul_eq_at b c k j;
        reflexivity (a i k * fin_sum (fun (l: fin n) -> b k l * c l j))
    in
    Classical.forall_intro pf_F;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> a i k * fin_sum (fun (l: fin n) -> b k l * c l j))
      (fun (k: fin n) -> a i k * bc k j) (fun _ -> ());

    matrix_mul_eq_at ab c i j;
    matrix_mul_eq_at a bc i j;
    transitivity
      (fin_sum (fun (l: fin n) -> ab i l * c l j))
      (fin_sum (fun (l: fin n) -> fin_sum (fun (k: fin n) -> a i k * b k l) * c l j))
      (fin_sum (fun (l: fin n) -> fin_sum (fun (k: fin n) -> (a i k * b k l) * c l j)));
    transitivity
      (fin_sum (fun (l: fin n) -> ab i l * c l j))
      (fin_sum (fun (l: fin n) -> fin_sum (fun (k: fin n) -> (a i k * b k l) * c l j)))
      (fin_sum (fun (l: fin n) -> fin_sum (fun (k: fin n) -> a i k * (b k l * c l j))));
    transitivity
      (fin_sum (fun (l: fin n) -> ab i l * c l j))
      (fin_sum (fun (l: fin n) -> fin_sum (fun (k: fin n) -> a i k * (b k l * c l j))))
      (fin_sum (fun (k: fin n) -> fin_sum (fun (l: fin n) -> a i k * (b k l * c l j))));
    transitivity
      (fin_sum (fun (l: fin n) -> ab i l * c l j))
      (fin_sum (fun (k: fin n) -> fin_sum (fun (l: fin n) -> a i k * (b k l * c l j))))
      (fin_sum (fun (k: fin n) -> a i k * fin_sum (fun (l: fin n) -> b k l * c l j)));
    transitivity
      (fin_sum (fun (l: fin n) -> ab i l * c l j))
      (fin_sum (fun (k: fin n) -> a i k * fin_sum (fun (l: fin n) -> b k l * c l j)))
      (fin_sum (fun (k: fin n) -> a i k * bc k j))
#pop-options

let matrix_mul_associativity
  (#t: Type) {| r: ring t |} (#n: nat) (a b c: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul (matrix_mul a b) c)
                          (matrix_mul a (matrix_mul b c)))
  = let pf (i j: fin n) : Lemma (matrix_mul (matrix_mul a b) c i j
                              = matrix_mul a (matrix_mul b c) i j)
      = matrix_mul_associativity_pointwise a b c i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul (matrix_mul a b) c)
                                 (matrix_mul a (matrix_mul b c))

(* ----------------------------------------------------------------- *)
(*  Left distributivity:  a * (b + c) = a*b + a*c                    *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_left_distributivity_pointwise
  (#t: Type) {| r: ring t |} (#n: nat)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a (matrix_add b c) i j
        = matrix_add (matrix_mul a b) (matrix_mul a c) i j)
  = elim_equatable_laws t ();

    let pf1 (k: fin n) : Lemma
      (a i k * matrix_add b c k j = a i k * (b k j + c k j))
      = reflexivity (a i k * (b k j + c k j))
    in
    Classical.forall_intro pf1;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> a i k * matrix_add b c k j)
      (fun (k: fin n) -> a i k * (b k j + c k j)) (fun _ -> ());

    let pf2 (k: fin n) : Lemma
      (a i k * (b k j + c k j) = a i k * b k j + a i k * c k j)
      = r.left_distributivity (a i k) (b k j) (c k j)
    in
    Classical.forall_intro pf2;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> a i k * (b k j + c k j))
      (fun (k: fin n) -> a i k * b k j + a i k * c k j) (fun _ -> ());

    let h (k: fin n) : t = a i k * b k j + a i k * c k j in
    fin_sum_add_ext #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> a i k * b k j)
      (fun (k: fin n) -> a i k * c k j)
      h (fun _ -> ());
    let pf_h_eq (k: fin n) : Lemma
      (h k = (fun (k: fin n) -> a i k * b k j + a i k * c k j) k)
      = reflexivity (a i k * b k j + a i k * c k j)
    in
    Classical.forall_intro pf_h_eq;
    fin_sum_congruence #t #(acg_of_r t #r) #n h
      (fun (k: fin n) -> a i k * b k j + a i k * c k j) (fun _ -> ());
    symmetry (fin_sum h) (fin_sum (fun (k: fin n) -> a i k * b k j + a i k * c k j));

    matrix_mul_eq_at a (matrix_add b c) i j;
    matrix_mul_eq_at a b i j;
    matrix_mul_eq_at a c i j;

    transitivity
      (fin_sum (fun (k: fin n) -> a i k * matrix_add b c k j))
      (fin_sum (fun (k: fin n) -> a i k * (b k j + c k j)))
      (fin_sum (fun (k: fin n) -> a i k * b k j + a i k * c k j));
    transitivity
      (fin_sum (fun (k: fin n) -> a i k * b k j + a i k * c k j))
      (fin_sum h)
      (fin_sum (fun (k: fin n) -> a i k * b k j)
     + fin_sum (fun (k: fin n) -> a i k * c k j));
    transitivity
      (fin_sum (fun (k: fin n) -> a i k * matrix_add b c k j))
      (fin_sum (fun (k: fin n) -> a i k * b k j + a i k * c k j))
      (fin_sum (fun (k: fin n) -> a i k * b k j)
     + fin_sum (fun (k: fin n) -> a i k * c k j))
#pop-options

let matrix_left_distributivity
  (#t: Type) {| r: ring t |} (#n: nat) (a b c: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul a (matrix_add b c))
                          (matrix_add (matrix_mul a b) (matrix_mul a c)))
  = let pf (i j: fin n) : Lemma (matrix_mul a (matrix_add b c) i j
                              = matrix_add (matrix_mul a b) (matrix_mul a c) i j)
      = matrix_left_distributivity_pointwise a b c i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul a (matrix_add b c))
                                 (matrix_add (matrix_mul a b) (matrix_mul a c))

(* ----------------------------------------------------------------- *)
(*  Right distributivity:  (b + c) * a = b*a + c*a                   *)
(*  Note arg order matches `r.right_distributivity x y z`:           *)
(*    (y+z)*x = y*x + z*x  — first arg is the RIGHT factor.          *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_right_distributivity_pointwise
  (#t: Type) {| r: ring t |} (#n: nat)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (matrix_add a b) c i j
        = matrix_add (matrix_mul a c) (matrix_mul b c) i j)
  = elim_equatable_laws t ();
    let pf1 (k: fin n) : Lemma
      (matrix_add a b i k * c k j = (a i k + b i k) * c k j)
      = reflexivity ((a i k + b i k) * c k j)
    in
    Classical.forall_intro pf1;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> matrix_add a b i k * c k j)
      (fun (k: fin n) -> (a i k + b i k) * c k j) (fun _ -> ());

    let pf2 (k: fin n) : Lemma
      ((a i k + b i k) * c k j = a i k * c k j + b i k * c k j)
      = r.right_distributivity (c k j) (a i k) (b i k)
    in
    Classical.forall_intro pf2;
    fin_sum_congruence #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> (a i k + b i k) * c k j)
      (fun (k: fin n) -> a i k * c k j + b i k * c k j) (fun _ -> ());

    let h (k: fin n) : t = a i k * c k j + b i k * c k j in
    fin_sum_add_ext #t #(acg_of_r t #r) #n
      (fun (k: fin n) -> a i k * c k j)
      (fun (k: fin n) -> b i k * c k j)
      h (fun _ -> ());
    let pf_h_eq (k: fin n) : Lemma
      (h k = (fun (k: fin n) -> a i k * c k j + b i k * c k j) k)
      = reflexivity (a i k * c k j + b i k * c k j)
    in
    Classical.forall_intro pf_h_eq;
    fin_sum_congruence #t #(acg_of_r t #r) #n h
      (fun (k: fin n) -> a i k * c k j + b i k * c k j) (fun _ -> ());
    symmetry (fin_sum h) (fin_sum (fun (k: fin n) -> a i k * c k j + b i k * c k j));

    matrix_mul_eq_at (matrix_add a b) c i j;
    matrix_mul_eq_at a c i j;
    matrix_mul_eq_at b c i j;

    transitivity
      (fin_sum (fun (k: fin n) -> matrix_add a b i k * c k j))
      (fin_sum (fun (k: fin n) -> (a i k + b i k) * c k j))
      (fin_sum (fun (k: fin n) -> a i k * c k j + b i k * c k j));
    transitivity
      (fin_sum (fun (k: fin n) -> a i k * c k j + b i k * c k j))
      (fin_sum h)
      (fin_sum (fun (k: fin n) -> a i k * c k j)
     + fin_sum (fun (k: fin n) -> b i k * c k j));
    transitivity
      (fin_sum (fun (k: fin n) -> matrix_add a b i k * c k j))
      (fin_sum (fun (k: fin n) -> a i k * c k j + b i k * c k j))
      (fin_sum (fun (k: fin n) -> a i k * c k j)
     + fin_sum (fun (k: fin n) -> b i k * c k j))
#pop-options

let matrix_right_distributivity
  (#t: Type) {| r: ring t |} (#n: nat) (a b c: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul (matrix_add a b) c)
                          (matrix_add (matrix_mul a c) (matrix_mul b c)))
  = let pf (i j: fin n) : Lemma (matrix_mul (matrix_add a b) c i j
                              = matrix_add (matrix_mul a c) (matrix_mul b c) i j)
      = matrix_right_distributivity_pointwise a b c i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul (matrix_add a b) c)
                                 (matrix_add (matrix_mul a c) (matrix_mul b c))

(* ----------------------------------------------------------------- *)
(*  Zero absorption (derived: needed for the ring instance closure)  *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_left_absorption_pointwise
  (#t: Type) {| r: ring t |} (#n: nat)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (zero_matrix n) a i j = zero #t)
  = elim_equatable_laws t ();
    let zm = zero_matrix #t #(acg_of_r t #r) n in
    let pf (k: fin n) : Lemma (zm i k * a k j = zero #t)
      = assert_norm (zm i k == zero #t);
        zero_mul_x (a k j);
        r.mul_congruence (zm i k) (a k j) (zero #t) (a k j);
        transitivity (zm i k * a k j) (zero #t * a k j) (zero #t)
    in
    Classical.forall_intro pf;
    fin_sum_zero_ext #t #(acg_of_r t #r) #n (fun (k: fin n) -> zm i k * a k j) (fun _ -> ());
    assert (fin_sum (fun (k: fin n) -> zm i k * a k j) = zero #t);
    assert_norm (matrix_mul zm a i j == fin_sum #t #(acg_of_r t #r) #n
                                          (fun (k: fin n) -> zm i k * a k j));
    reflexivity (matrix_mul zm a i j);
    transitivity
      (matrix_mul zm a i j)
      (fin_sum (fun (k: fin n) -> zm i k * a k j))
      (zero #t)
#pop-options

let matrix_left_absorption
  (#t: Type) {| r: ring t |} (#n: nat) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul (zero_matrix n) a) (zero_matrix n))
  = let zm = zero_matrix #t #(acg_of_r t #r) n in
    let pf (i j: fin n) : Lemma (matrix_mul zm a i j = zm i j)
      = matrix_left_absorption_pointwise a i j;
        reflexivity (zero #t);
        symmetry (zm i j) (zero #t);
        transitivity (matrix_mul zm a i j) (zero #t) (zm i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul zm a) zm

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_right_absorption_pointwise
  (#t: Type) {| r: ring t |} (#n: nat)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a (zero_matrix n) i j = zero #t)
  = elim_equatable_laws t ();
    let zm = zero_matrix #t #(acg_of_r t #r) n in
    let pf (k: fin n) : Lemma (a i k * zm k j = zero #t)
      = assert_norm (zm k j == zero #t);
        x_mul_zero (a i k);
        r.mul_congruence (a i k) (zm k j) (a i k) (zero #t);
        transitivity (a i k * zm k j) (a i k * zero #t) (zero #t)
    in
    Classical.forall_intro pf;
    fin_sum_zero_ext #t #(acg_of_r t #r) #n (fun (k: fin n) -> a i k * zm k j) (fun _ -> ());
    assert (fin_sum (fun (k: fin n) -> a i k * zm k j) = zero #t);
    assert_norm (matrix_mul a zm i j == fin_sum #t #(acg_of_r t #r) #n
                                          (fun (k: fin n) -> a i k * zm k j));
    reflexivity (matrix_mul a zm i j);
    transitivity
      (matrix_mul a zm i j)
      (fin_sum (fun (k: fin n) -> a i k * zm k j))
      (zero #t)
#pop-options

let matrix_right_absorption
  (#t: Type) {| r: ring t |} (#n: nat) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul a (zero_matrix n)) (zero_matrix n))
  = let zm = zero_matrix #t #(acg_of_r t #r) n in
    let pf (i j: fin n) : Lemma (matrix_mul a zm i j = zm i j)
      = matrix_right_absorption_pointwise a i j;
        reflexivity (zero #t);
        symmetry (zm i j) (zero #t);
        transitivity (matrix_mul a zm i j) (zero #t) (zm i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul a zm) zm

(* ----------------------------------------------------------------- *)
(*  ring (square_matrix t n) instance                                *)
(* ----------------------------------------------------------------- *)

instance matrix_ring (t: Type) {| r: ring t |} (n: nat)
  : ring (square_matrix t n)
  = let g : add_comm_group t = acg_of_r t #r in
    let macg : add_comm_group (square_matrix t n) = matrix_add_comm_group t #g n in
    {
      r_add                = macg;
      one                  = id_matrix #t #r n;
      mul                  = (fun a b -> matrix_mul #t #r #n a b);
      mul_congruence       = (fun a b c d -> matrix_mul_congruence #t #r #n a b c d);
      mul_associativity    = (fun a b c -> matrix_mul_associativity #t #r #n a b c);
      mul_one              = (fun a ->
                                matrix_mul_left_identity #t #r #n a;
                                matrix_mul_right_identity #t #r #n a);
      left_distributivity  = (fun a b c -> matrix_left_distributivity #t #r #n a b c);
      right_distributivity = (fun a b c -> matrix_right_distributivity #t #r #n b c a);
    }
