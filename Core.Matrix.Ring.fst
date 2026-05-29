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
open Core.Vector

(* ----------------------------------------------------------------- *)
(*  Congruence of matrix_mul                                         *)
(* ----------------------------------------------------------------- *)

let matrix_mul_pointwise_congruence
  (#t: Type) {| r: ring t |} (#n: pos)
  (a b c d: square_matrix t n) (i j: fin n)
  : Lemma (requires matrix_eq a c /\ matrix_eq b d)
          (ensures matrix_mul a b i j = matrix_mul c d i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    matrix_mul_to_fin_sum a b i j;
    matrix_mul_to_fin_sum c d i j;
    let pf (k: fin n) : Lemma (pointwise_mul (row a i) (col b j) k 
                              = pointwise_mul (row c i) (col d j) k)
      = mul_congruence (a i k) (b k j) (c i k) (d k j)
    in
    fin_sum_congruence (pointwise_mul (row a i) (col b j))
                       (pointwise_mul (row c i) (col d j)) pf

let matrix_mul_congruence
  (#t: Type) {| r: ring t |} (#n: pos)
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

#push-options "--fuel 2 --ifuel 1 --z3rlimit 60"
let matrix_mul_left_identity_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul ((id_matrix #t #r #n)) a i j = a i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    matrix_mul_to_fin_sum id_matrix a i j;
    fin_sum_congruence (pointwise_mul (row id_matrix i) (col a j))
                       (pointwise_mul (fin_kronecker_delta i) (col a j)) (fun _ -> ());
    fin_sum_kronecker i (col a j)

let matrix_mul_right_identity_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a ((id_matrix #t #r #n)) i j = a i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    matrix_mul_to_fin_sum a id_matrix i j;
    let pf (k: fin n) : Lemma (pointwise_mul (row a i) (col id_matrix j) k
                              = pointwise_mul (fin_kronecker_delta j) (row a i) k)
      = if (k <: nat) = (j <: nat) then (x_mul_one (a i k); one_mul_x (a i k))
        else (x_mul_zero (a i k); zero_mul_x (a i k))
    in
    fin_sum_congruence (pointwise_mul (row a i) (col id_matrix j))
                       (pointwise_mul (fin_kronecker_delta j) (row a i)) pf;
    fin_sum_kronecker j (row a i)
#pop-options

let matrix_mul_left_identity
  (#t: Type) {| r: ring t |} (#n: pos) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul ((id_matrix #t #r #n)) a) a)
  = let id_mat = id_matrix #t #r #n in
    let pf (i j: fin n) : Lemma (matrix_mul id_mat a i j = a i j)
      = matrix_mul_left_identity_pointwise a i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul id_mat a) a

let matrix_mul_right_identity
  (#t: Type) {| r: ring t |} (#n: pos) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul a ((id_matrix #t #r #n))) a)
  = let id_mat = id_matrix #t #r #n in
    let pf (i j: fin n) : Lemma (matrix_mul a id_mat i j = a i j)
      = matrix_mul_right_identity_pointwise a i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul a id_mat) a

(* ----------------------------------------------------------------- *)
(*  Associativity                                                    *)
(* ----------------------------------------------------------------- *)

(* Clean proof using only combinators, no lambdas. 
   Goal: (AB)C_{ij} = A(BC)_{ij}
   
   Strategy (all sums are fin_sum):
     LHS == Σₗ (AB)ᵢₗ·cₗⱼ
         == Σₗ (Σₖ aᵢₖ·bₖₗ)·cₗⱼ           (expand AB)
         == Σₗ Σₖ (aᵢₖ·bₖₗ)·cₗⱼ            (fin_sum_mul_right)
         == Σₗ Σₖ aᵢₖ·(bₖₗ·cₗⱼ)            (ring associativity)
         == Σₖ Σₗ aᵢₖ·(bₖₗ·cₗⱼ)            (fin_sum_swap)
         == Σₖ aᵢₖ·(Σₗ bₖₗ·cₗⱼ)            (fin_sum_mul_left)
         == Σₖ aᵢₖ·(BC)ₖⱼ                   (fold BC)
         == RHS
*)

let matrix_mul_assoc_clean
  (#t: Type) {| r: ring t |} (#n: pos)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (matrix_mul a b) c i j
        = matrix_mul a (matrix_mul b c) i j)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let ab = matrix_mul a b in
    let bc = matrix_mul b c in
    let ri  = row a i in    (* ri k  = a i k *)
    let cj  = col c j in    (* cj l  = c l j *)

    (* The key curried double-sum: double_lk l k = aᵢₖ·(bₖₗ·cₗⱼ) *)
    let double_lk (l: fin n) (k: fin n) : t = ri k * (b k l * cj l) in
    let rhs_summand (k: fin n) : t = ri k * bc k j in

    (* ——— LHS unfolding ———
       matrix_mul ab c i j 
       == fin_sum (pointwise_mul (row ab i) cj)         [matrix_mul_to_fin_sum]
       Each summand: (row ab i) l * cj l 
                   = ab i l * cj l
                   = fin_sum (pointwise_mul ri (col b l)) * cj l   [step1]
                   = fin_sum (double_lk l)                         [step2]
                   = fin_sum_curry double_lk l *)
    let lhs_to_double (l: fin n) : Lemma (pointwise_mul (row ab i) cj l = fin_sum_curry double_lk l) = 
        matrix_mul_to_fin_sum a b i l;
        fin_sum_mul_right (pointwise_mul (row a i) (col b l)) (col c j l);
        Classical.forall_intro_3 #t mul_associativity;
        fin_sum_congruence
          (pointwise_mul (pointwise_mul (row a i) (col b l)) (const (col c j l)))
          (double_lk l) (fun _ -> ())
    in
    matrix_mul_to_fin_sum (matrix_mul a b) c i j;
    fin_sum_congruence (pointwise_mul (row (matrix_mul a b) i) (col c j)) 
                       (fin_sum_curry double_lk) lhs_to_double;
    (* Now: matrix_mul ab c i j = fin_sum (fin_sum_curry double_lk) *)
    (* ——— Sum swap ———
       fin_sum (fin_sum_curry double_lk) = fin_sum (fin_sum_curry (swap_args double_lk)) *)
    fin_sum_swap double_lk;
    (* ——— RHS folding ———
       fin_sum_curry (swap_args double_lk) k
       = fin_sum (swap_args double_lk k)
       = Σₗ double_lk l k
       = Σₗ aᵢₖ·(bₖₗ·cₗⱼ)
       = aᵢₖ · Σₗ bₖₗ·cₗⱼ                  [fin_sum_mul_left]
       = aᵢₖ · (BC)ₖⱼ                       [fold BC]
       = rhs_summand k *)
    let double_to_rhs (k: fin n) : Lemma
      (fin_sum_curry (swap_args double_lk) k = rhs_summand k)
      = fin_sum_congruence (swap_args double_lk k)
          (pointwise_mul (const (row a i k)) (pointwise_mul (row b k) (col c j))) (fun _ -> ());
        fin_sum_mul_left (row a i k) (pointwise_mul (row b k) (col c j));
        matrix_mul_to_fin_sum b c k j;
        mul_congruence (row a i k) (fin_sum (pointwise_mul (row b k) (col c j)))
                         (row a i k) (matrix_mul b c k j)
    in
    fin_sum_congruence (fin_sum_curry (swap_args double_lk)) rhs_summand double_to_rhs;
    (* Now: fin_sum (fin_sum_curry (swap_args double_lk)) = fin_sum rhs_summand *)

    (* RHS: matrix_mul a (matrix_mul b c) i j = fin_sum rhs_summand *)
    matrix_mul_to_fin_sum a (matrix_mul b c) i j;
    fin_sum_congruence (pointwise_mul (row a i) (col (matrix_mul b c) j)) rhs_summand (fun _ -> ())    

let matrix_mul_associativity
  (#t: Type) {| r: ring t |} (#n: pos) (a b c: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul (matrix_mul a b) c)
                          (matrix_mul a (matrix_mul b c)))
  = Classical.forall_intro_2 (matrix_mul_assoc_clean a b c);
    matrix_eq_bool_iff_pointwise (matrix_mul (matrix_mul a b) c)
                                 (matrix_mul a (matrix_mul b c))

(* ----------------------------------------------------------------- *)
(*  Left distributivity:  a * (b + c) = a*b + a*c                    *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let matrix_left_distributivity_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a (matrix_add b c) i j
        = matrix_add (matrix_mul a b) (matrix_mul a c) i j)
  = elim_equatable_laws t ();
    matrix_mul_to_fin_sum a (matrix_add b c) i j;
    matrix_mul_to_fin_sum a b i j;
    matrix_mul_to_fin_sum a c i j;
    let pf (k: fin n) : Lemma (pointwise_mul (row a i) (col (matrix_add b c) j) k 
                              = pointwise_mul (row a i) (col b j) k + pointwise_mul (row a i) (col c j) k)
      = left_distributivity (a i k) (b k j) (c k j) in
    fin_sum_add_ext (pointwise_mul (row a i) (col b j))
                    (pointwise_mul (row a i) (col c j))
                    (pointwise_mul (row a i) (col (matrix_add b c) j)) pf;
    add_congruence (fin_sum (pointwise_mul (row a i) (col b j)))
                   (fin_sum (pointwise_mul (row a i) (col c j)))
                   (matrix_mul a b i j) (matrix_mul a c i j)
#pop-options

let matrix_left_distributivity
  (#t: Type) {| r: ring t |} (#n: pos) (a b c: square_matrix t n)
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

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let matrix_right_distributivity_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (matrix_add a b) c i j = matrix_add (matrix_mul a c) (matrix_mul b c) i j) = 
    elim_equatable_laws t ();
    matrix_mul_to_fin_sum (matrix_add a b) c i j;
    matrix_mul_to_fin_sum a c i j;
    matrix_mul_to_fin_sum b c i j;
    let pf (k: fin n) : Lemma (pointwise_mul (row (matrix_add a b) i) (col c j) k
                              = pointwise_mul (row a i) (col c j) k + pointwise_mul (row b i) (col c j) k)
      = right_distributivity (c k j) (a i k) (b i k)
    in
    fin_sum_add_ext (pointwise_mul (row a i) (col c j))
                    (pointwise_mul (row b i) (col c j))
                    (pointwise_mul (row (matrix_add a b) i) (col c j)) pf;
    add_congruence (fin_sum (pointwise_mul (row a i) (col c j)))
                   (fin_sum (pointwise_mul (row b i) (col c j)))
                   (matrix_mul a c i j) (matrix_mul b c i j)
#pop-options

let matrix_right_distributivity
  (#t: Type) {| r: ring t |} (#n: pos) (a b c: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul (matrix_add a b) c)
                          (matrix_add (matrix_mul a c) (matrix_mul b c)))
  = Classical.forall_intro_2 (matrix_right_distributivity_pointwise a b c);
    matrix_eq_bool_iff_pointwise (matrix_mul (matrix_add a b) c)
                                 (matrix_add (matrix_mul a c) (matrix_mul b c))

(* ----------------------------------------------------------------- *)
(*  Zero absorption (derived: needed for the ring instance closure)  *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_left_absorption_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul zero_matrix a i j = zero)
  = matrix_mul_to_fin_sum zero_matrix a i j;
    Classical.forall_intro #t (zero_mul_x);
    fin_sum_zero_ext (pointwise_mul (row zero_matrix i) (col a j)) (fun _ -> ())
#pop-options

let matrix_left_absorption
  (#t: Type) {| r: ring t |} (#n: pos) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul zero_matrix a) zero_matrix)
  = Classical.forall_intro_2 (matrix_left_absorption_pointwise a);    
    matrix_eq_bool_iff_pointwise (matrix_mul zero_matrix a) zero_matrix

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_right_absorption_pointwise
  (#t: Type) {| r: ring t |} (#n: pos)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a zero_matrix i j = zero) = 
    matrix_mul_to_fin_sum a zero_matrix i j;
    Classical.forall_intro #t (x_mul_zero);
    fin_sum_zero_ext (pointwise_mul (row a i) (col zero_matrix j)) (fun _ -> ())
#pop-options

let matrix_right_absorption
  (#t: Type) {| r: ring t |} (#n: pos) (a: square_matrix t n)
  : Lemma (matrix_eq_bool (matrix_mul a zero_matrix) zero_matrix)
  = Classical.forall_intro_2 (matrix_right_absorption_pointwise a);   
    matrix_eq_bool_iff_pointwise (matrix_mul a zero_matrix) zero_matrix

(* ----------------------------------------------------------------- *)
(*  ring (square_matrix t n) instance                                *)
(* ----------------------------------------------------------------- *)

instance matrix_ring (t: Type) {| r: ring t |} (n: pos)
  : ring (square_matrix t n)
  = let g : add_comm_group t = acg_of_r t #r in
    let macg : add_comm_group (square_matrix t n) = matrix_add_comm_group t #g n in
    {
      r_add                = macg;
      one                  = id_matrix #t #r #n;
      mul                  = (fun a b -> matrix_mul #t #r #n a b);
      mul_congruence       = (fun a b c d -> matrix_mul_congruence #t #r #n a b c d);
      mul_associativity    = (fun a b c -> matrix_mul_associativity #t #r #n a b c);
      mul_one              = (fun a ->
                                matrix_mul_left_identity #t #r #n a;
                                matrix_mul_right_identity #t #r #n a);
      left_distributivity  = (fun a b c -> matrix_left_distributivity #t #r #n a b c);
      right_distributivity = (fun a b c -> matrix_right_distributivity #t #r #n b c a);
    }
