module FStar.CAS.Matrix.Ring

(*
  Multiplicative tower for square matrices.

  Given a `semiring t` (resp. `ring t`), we lift the structure to
  `square_matrix t n` and provide a `semiring` (resp. `ring`) instance.

  Author: A. Rozanov (CuteCAS).
*)

module TC = FStar.Tactics.Typeclasses

open FStar.CAS.Equatable
open FStar.CAS.Grouplikes
open FStar.CAS.Ringlikes
open FStar.CAS.FinSum
open FStar.CAS.Permutation
open FStar.CAS.Matrix

(* ----------------------------------------------------------------- *)
(*  Pointwise congruence of matrix_mul                               *)
(* ----------------------------------------------------------------- *)

let matrix_mul_pointwise_congruence
  (#t: Type) {| r: semiring t |} (#n: nat)
  (a b c d: square_matrix t n) (i j: fin n)
  : Lemma (requires matrix_eq a c /\ matrix_eq b d)
          (ensures matrix_mul a b i j = matrix_mul c d i j)
  = let pf (k: fin n) : Lemma (a i k * b k j = c i k * d k j)
      = mul_congruence (a i k) (b k j) (c i k) (d k j)
    in
    Classical.forall_intro pf;
    fin_sum_congruence (fun (k: fin n) -> a i k * b k j)
                       (fun (k: fin n) -> c i k * d k j)

let matrix_mul_congruence
  (#t: Type) {| r: semiring t |} (#n: nat)
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
(*  has_one / has_mul instances                                      *)
(* ----------------------------------------------------------------- *)

instance matrix_has_one (t: Type) {| h0: has_zero t |} {| h1: has_one t |}
  (h_eq: squash (h0.eq == h1.eq)) (n: nat)
  : has_one (square_matrix t n)
  = {
    eq = matrix_equatable t #h0.eq n;
    one = id_matrix #t #h0 #h1 n;
  }

instance matrix_has_one_of_semiring (t: Type) {| r: semiring t |} (n: nat)
  : has_one (square_matrix t n)
  = {
    eq = matrix_equatable t #(he_r r) n;
    one = id_matrix #t #(r.add_comm_monoid.add_monoid.has_zero)
                       #(r.mul_monoid.has_one) n;
  }

instance matrix_has_mul (t: Type) {| r: semiring t |} (n: nat)
  : has_mul (square_matrix t n)
  = {
    ( * ) = matrix_mul;
    eq = matrix_equatable t #(he_r r) n;
    congruence = matrix_mul_congruence #t #r #n;
  }

(* ----------------------------------------------------------------- *)
(*  Pointwise left and right identities                              *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_mul_left_identity_pointwise
  (#t: Type) {| r: semiring t |} (#n: nat)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (id_matrix #t #(r.add_comm_monoid.add_monoid.has_zero)
                                    #(r.mul_monoid.has_one) n) a i j = a i j)
  = elim_equatable_laws t;
    let id_mat = id_matrix #t #(r.add_comm_monoid.add_monoid.has_zero)
                              #(r.mul_monoid.has_one) n in
    let pf (k: fin n) : Lemma
        (id_mat i k * a k j
         = (if (i <: nat) = (k <: nat) then one else zero #t) * a k j)
      = assert_norm (id_mat i k == (if (i <: nat) = (k <: nat) then one else zero #t));
        reflexivity (id_mat i k * a k j)
    in
    Classical.forall_intro pf;
    fin_sum_congruence
      (fun (k: fin n) -> id_mat i k * a k j)
      (fun (k: fin n) -> (if (i <: nat) = (k <: nat) then one else zero #t) * a k j);
    fin_sum_kronecker i (fun (k: fin n) -> a k j);
    transitivity
      (fin_sum (fun (k: fin n) -> id_mat i k * a k j))
      (fin_sum (fun (k: fin n) ->
         (if (i <: nat) = (k <: nat) then one else zero #t) * a k j))
      (a i j);
    matrix_mul_eq_at id_mat a i j
#pop-options

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_mul_right_identity_pointwise
  (#t: Type) {| r: semiring t |} (#n: nat)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a (id_matrix #t #(r.add_comm_monoid.add_monoid.has_zero)
                                      #(r.mul_monoid.has_one) n) i j = a i j)
  = elim_equatable_laws t;
    let id_mat = id_matrix #t #(r.add_comm_monoid.add_monoid.has_zero)
                              #(r.mul_monoid.has_one) n in
    let pf (k: fin n) : Lemma
        (a i k * id_mat k j
         = (if (j <: nat) = (k <: nat) then one else zero #t) * a i k)
      = assert_norm (id_mat k j == (if (k <: nat) = (j <: nat) then one else zero #t));
        if (k <: nat) = (j <: nat) then begin
          right_mul_identity (a i k);
          left_mul_identity (a i k);
          symmetry (one * a i k) (a i k);
          transitivity (a i k * id_mat k j) (a i k) (one * a i k)
        end else begin
          right_absorption (a i k);
          left_absorption (a i k);
          symmetry (zero * a i k) (zero #t);
          transitivity (a i k * id_mat k j) (zero #t) (zero * a i k)
        end
    in
    Classical.forall_intro pf;
    fin_sum_congruence
      (fun (k: fin n) -> a i k * id_mat k j)
      (fun (k: fin n) -> (if (j <: nat) = (k <: nat) then one else zero #t) * a i k);
    fin_sum_kronecker j (fun (k: fin n) -> a i k);
    transitivity
      (fin_sum (fun (k: fin n) -> a i k * id_mat k j))
      (fin_sum (fun (k: fin n) ->
         (if (j <: nat) = (k <: nat) then one else zero #t) * a i k))
      (a i j);
    matrix_mul_eq_at a id_mat i j
#pop-options

let matrix_mul_left_identity
  (#t: Type) {| r: semiring t |} (#n: nat) (a: square_matrix t n)
  : Lemma (matrix_mul (id_matrix #t #(r.add_comm_monoid.add_monoid.has_zero)
                                    #(r.mul_monoid.has_one) n) a = a)
  = let id_mat = id_matrix #t #(r.add_comm_monoid.add_monoid.has_zero)
                              #(r.mul_monoid.has_one) n in
    let pf (i j: fin n) : Lemma (matrix_mul id_mat a i j = a i j)
      = matrix_mul_left_identity_pointwise a i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul id_mat a) a

let matrix_mul_right_identity
  (#t: Type) {| r: semiring t |} (#n: nat) (a: square_matrix t n)
  : Lemma (matrix_mul a (id_matrix #t #(r.add_comm_monoid.add_monoid.has_zero)
                                      #(r.mul_monoid.has_one) n) = a)
  = let id_mat = id_matrix #t #(r.add_comm_monoid.add_monoid.has_zero)
                              #(r.mul_monoid.has_one) n in
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
  (#t: Type) {| r: semiring t |} (#n: nat)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (matrix_mul a b) c i j
        = matrix_mul a (matrix_mul b c) i j)
  = elim_equatable_laws t;
    let ab = matrix_mul a b in
    let bc = matrix_mul b c in

    (* Step A: (AB)C[i,j] = fin_sum_l ((AB)[i,l] * c[l,j])
                          = fin_sum_l ( (fin_sum_k a[i,k] b[k,l]) * c[l,j] )
       via matrix_mul_eq_at and a fin_sum_congruence step. *)
    let pf_A (l: fin n) : Lemma
      (ab i l * c l j
       = fin_sum (fun (k: fin n) -> a i k * b k l) * c l j)
      = matrix_mul_eq_at a b i l;
        reflexivity (fin_sum (fun (k: fin n) -> a i k * b k l) * c l j)
    in
    Classical.forall_intro pf_A;
    fin_sum_congruence
      (fun (l: fin n) -> ab i l * c l j)
      (fun (l: fin n) -> fin_sum (fun (k: fin n) -> a i k * b k l) * c l j);

    (* Step B: distribute c[l,j] into the inner sum (fin_sum_mul_right). *)
    let pf_B (l: fin n) : Lemma
      (fin_sum (fun (k: fin n) -> a i k * b k l) * c l j
       = fin_sum (fun (k: fin n) -> (a i k * b k l) * c l j))
      = fin_sum_mul_right (fun (k: fin n) -> a i k * b k l) (c l j)
    in
    Classical.forall_intro pf_B;
    fin_sum_congruence
      (fun (l: fin n) -> fin_sum (fun (k: fin n) -> a i k * b k l) * c l j)
      (fun (l: fin n) -> fin_sum (fun (k: fin n) -> (a i k * b k l) * c l j));

    (* Step C: pointwise mul_associativity inside the inner sum. *)
    let pf_C (l: fin n) : Lemma
      (fin_sum (fun (k: fin n) -> (a i k * b k l) * c l j)
       = fin_sum (fun (k: fin n) -> a i k * (b k l * c l j)))
      = let pfk (k: fin n) : Lemma ((a i k * b k l) * c l j
                                  = a i k * (b k l * c l j))
          = mul_associativity (a i k) (b k l) (c l j)
        in
        Classical.forall_intro pfk;
        fin_sum_congruence
          (fun (k: fin n) -> (a i k * b k l) * c l j)
          (fun (k: fin n) -> a i k * (b k l * c l j))
    in
    Classical.forall_intro pf_C;
    fin_sum_congruence
      (fun (l: fin n) -> fin_sum (fun (k: fin n) -> (a i k * b k l) * c l j))
      (fun (l: fin n) -> fin_sum (fun (k: fin n) -> a i k * (b k l * c l j)));

    (* Step D: swap outer/inner sums. *)
    fin_sum_swap (fun (l: fin n) (k: fin n) -> a i k * (b k l * c l j));

    (* Step E: pull a[i,k] out of the inner sum (fin_sum_mul_left). *)
    let pf_E (k: fin n) : Lemma
      (fin_sum (fun (l: fin n) -> a i k * (b k l * c l j))
       = a i k * fin_sum (fun (l: fin n) -> b k l * c l j))
      = fin_sum_mul_left (a i k) (fun (l: fin n) -> b k l * c l j);
        symmetry (a i k * fin_sum (fun (l: fin n) -> b k l * c l j))
                 (fin_sum (fun (l: fin n) -> a i k * (b k l * c l j)))
    in
    Classical.forall_intro pf_E;
    fin_sum_congruence
      (fun (k: fin n) -> fin_sum (fun (l: fin n) -> a i k * (b k l * c l j)))
      (fun (k: fin n) -> a i k * fin_sum (fun (l: fin n) -> b k l * c l j));

    (* Step F: identify fin_sum_l (b[k,l] * c[l,j]) with (BC)[k,j]. *)
    let pf_F (k: fin n) : Lemma
      (a i k * fin_sum (fun (l: fin n) -> b k l * c l j) = a i k * bc k j)
      = matrix_mul_eq_at b c k j;
        reflexivity (a i k * fin_sum (fun (l: fin n) -> b k l * c l j))
    in
    Classical.forall_intro pf_F;
    fin_sum_congruence
      (fun (k: fin n) -> a i k * fin_sum (fun (l: fin n) -> b k l * c l j))
      (fun (k: fin n) -> a i k * bc k j);

    (* Now stitch using matrix_mul_eq_at on both sides. *)
    matrix_mul_eq_at ab c i j;
    matrix_mul_eq_at a bc i j;
    (* matrix_mul ab c i j == fin_sum (fun l -> ab i l * c l j)
       matrix_mul a bc i j == fin_sum (fun k -> a i k * bc k j) *)
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
  (#t: Type) {| r: semiring t |} (#n: nat) (a b c: square_matrix t n)
  : Lemma (matrix_mul (matrix_mul a b) c = matrix_mul a (matrix_mul b c))
  = let pf (i j: fin n) : Lemma (matrix_mul (matrix_mul a b) c i j
                              = matrix_mul a (matrix_mul b c) i j)
      = matrix_mul_associativity_pointwise a b c i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul (matrix_mul a b) c)
                                 (matrix_mul a (matrix_mul b c))

(* ----------------------------------------------------------------- *)
(*  Distributivity                                                   *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_left_distributivity_pointwise
  (#t: Type) {| r: semiring t |} (#n: nat)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a (matrix_add b c) i j
        = matrix_add (matrix_mul a b) (matrix_mul a c) i j)
  = elim_equatable_laws t;

    (* Step 1: rewrite a i k * (b+c) k j to a i k * (b k j + c k j). *)
    let pf1 (k: fin n) : Lemma
      (a i k * matrix_add b c k j = a i k * (b k j + c k j))
      = reflexivity (a i k * (b k j + c k j))
    in
    Classical.forall_intro pf1;
    fin_sum_congruence
      (fun (k: fin n) -> a i k * matrix_add b c k j)
      (fun (k: fin n) -> a i k * (b k j + c k j));

    (* Step 2: distributivity pointwise. *)
    let pf2 (k: fin n) : Lemma
      (a i k * (b k j + c k j) = a i k * b k j + a i k * c k j)
      = left_distributivity (a i k) (b k j) (c k j)
    in
    Classical.forall_intro pf2;
    fin_sum_congruence
      (fun (k: fin n) -> a i k * (b k j + c k j))
      (fun (k: fin n) -> a i k * b k j + a i k * c k j);

    (* Step 3: combine with fin_sum_add_ext to split the sum cleanly. *)
    let h (k: fin n) : t = a i k * b k j + a i k * c k j in
    fin_sum_add_ext
      (fun (k: fin n) -> a i k * b k j)
      (fun (k: fin n) -> a i k * c k j)
      h;
    let pf_h_eq (k: fin n) : Lemma
      (h k = (fun (k: fin n) -> a i k * b k j + a i k * c k j) k)
      = reflexivity (a i k * b k j + a i k * c k j)
    in
    Classical.forall_intro pf_h_eq;
    fin_sum_congruence h (fun (k: fin n) -> a i k * b k j + a i k * c k j);
    symmetry (fin_sum h) (fin_sum (fun (k: fin n) -> a i k * b k j + a i k * c k j));

    (* Bring it home via matrix_mul_eq_at for both products. *)
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
  (#t: Type) {| r: semiring t |} (#n: nat) (a b c: square_matrix t n)
  : Lemma (matrix_mul a (matrix_add b c)
        = matrix_add (matrix_mul a b) (matrix_mul a c))
  = let pf (i j: fin n) : Lemma (matrix_mul a (matrix_add b c) i j
                              = matrix_add (matrix_mul a b) (matrix_mul a c) i j)
      = matrix_left_distributivity_pointwise a b c i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul a (matrix_add b c))
                                 (matrix_add (matrix_mul a b) (matrix_mul a c))

#push-options "--fuel 2 --ifuel 1 --z3rlimit 40"
let matrix_right_distributivity_pointwise
  (#t: Type) {| r: semiring t |} (#n: nat)
  (a b c: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (matrix_add a b) c i j
        = matrix_add (matrix_mul a c) (matrix_mul b c) i j)
  = elim_equatable_laws t;
    let pf1 (k: fin n) : Lemma
      (matrix_add a b i k * c k j = (a i k + b i k) * c k j)
      = reflexivity ((a i k + b i k) * c k j)
    in
    Classical.forall_intro pf1;
    fin_sum_congruence
      (fun (k: fin n) -> matrix_add a b i k * c k j)
      (fun (k: fin n) -> (a i k + b i k) * c k j);

    let pf2 (k: fin n) : Lemma
      ((a i k + b i k) * c k j = a i k * c k j + b i k * c k j)
      = right_distributivity (a i k) (b i k) (c k j)
    in
    Classical.forall_intro pf2;
    fin_sum_congruence
      (fun (k: fin n) -> (a i k + b i k) * c k j)
      (fun (k: fin n) -> a i k * c k j + b i k * c k j);

    let h (k: fin n) : t = a i k * c k j + b i k * c k j in
    fin_sum_add_ext
      (fun (k: fin n) -> a i k * c k j)
      (fun (k: fin n) -> b i k * c k j)
      h;
    let pf_h_eq (k: fin n) : Lemma
      (h k = (fun (k: fin n) -> a i k * c k j + b i k * c k j) k)
      = reflexivity (a i k * c k j + b i k * c k j)
    in
    Classical.forall_intro pf_h_eq;
    fin_sum_congruence h (fun (k: fin n) -> a i k * c k j + b i k * c k j);
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
  (#t: Type) {| r: semiring t |} (#n: nat) (a b c: square_matrix t n)
  : Lemma (matrix_mul (matrix_add a b) c
        = matrix_add (matrix_mul a c) (matrix_mul b c))
  = let pf (i j: fin n) : Lemma (matrix_mul (matrix_add a b) c i j
                              = matrix_add (matrix_mul a c) (matrix_mul b c) i j)
      = matrix_right_distributivity_pointwise a b c i j
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul (matrix_add a b) c)
                                 (matrix_add (matrix_mul a c) (matrix_mul b c))

(* ----------------------------------------------------------------- *)
(*  Absorption                                                       *)
(* ----------------------------------------------------------------- *)

#push-options "--fuel 4 --ifuel 2 --z3rlimit 200"
let matrix_left_absorption_pointwise
  (#t: Type) {| r: semiring t |} (#n: nat)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul (zero_matrix #t #(r.add_comm_monoid.add_monoid.has_zero) n) a i j
        = zero #t)
  = elim_equatable_laws t;
    let zm = zero_matrix #t #(r.add_comm_monoid.add_monoid.has_zero) n in
    let pf (k: fin n) : Lemma (zm i k * a k j = zero #t)
      = assert_norm (zm i k == zero #t);
        left_absorption (a k j);
        mul_congruence (zm i k) (a k j) (zero #t) (a k j);
        transitivity (zm i k * a k j) (zero #t * a k j) (zero #t)
    in
    Classical.forall_intro pf;
    fin_sum_zero_ext (fun (k: fin n) -> zm i k * a k j);
    assert (fin_sum (fun (k: fin n) -> zm i k * a k j) = zero #t);
    assert_norm (matrix_mul zm a i j == fin_sum (fun (k: fin n) -> zm i k * a k j));
    reflexivity (matrix_mul zm a i j);
    transitivity
      (matrix_mul zm a i j)
      (fin_sum (fun (k: fin n) -> zm i k * a k j))
      (zero #t)
#pop-options

let matrix_left_absorption
  (#t: Type) {| r: semiring t |} (#n: nat) (a: square_matrix t n)
  : Lemma (matrix_mul (zero_matrix #t #(r.add_comm_monoid.add_monoid.has_zero) n) a
        = zero_matrix #t #(r.add_comm_monoid.add_monoid.has_zero) n)
  = let zm = zero_matrix #t #(r.add_comm_monoid.add_monoid.has_zero) n in
    let pf (i j: fin n) : Lemma (matrix_mul zm a i j = zm i j)
      = matrix_left_absorption_pointwise a i j;
        reflexivity (zero #t);
        symmetry (zm i j) (zero #t);
        transitivity (matrix_mul zm a i j) (zero #t) (zm i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul zm a) zm

let matrix_right_absorption_pointwise
  (#t: Type) {| r: semiring t |} (#n: nat)
  (a: square_matrix t n) (i j: fin n)
  : Lemma (matrix_mul a (zero_matrix #t #(r.add_comm_monoid.add_monoid.has_zero) n) i j
        = zero #t)
  = elim_equatable_laws t;
    let zm = zero_matrix #t #(r.add_comm_monoid.add_monoid.has_zero) n in
    let pf (k: fin n) : Lemma (a i k * zm k j = zero #t)
      = assert_norm (zm k j == zero #t);
        right_absorption (a i k);
        mul_congruence (a i k) (zm k j) (a i k) (zero #t);
        transitivity (a i k * zm k j) (a i k * zero #t) (zero #t)
    in
    Classical.forall_intro pf;
    fin_sum_zero_ext (fun (k: fin n) -> a i k * zm k j);
    assert (fin_sum (fun (k: fin n) -> a i k * zm k j) = zero #t);
    assert_norm (matrix_mul a zm i j == fin_sum (fun (k: fin n) -> a i k * zm k j));
    reflexivity (matrix_mul a zm i j);
    transitivity
      (matrix_mul a zm i j)
      (fin_sum (fun (k: fin n) -> a i k * zm k j))
      (zero #t)

let matrix_right_absorption
  (#t: Type) {| r: semiring t |} (#n: nat) (a: square_matrix t n)
  : Lemma (matrix_mul a (zero_matrix #t #(r.add_comm_monoid.add_monoid.has_zero) n)
        = zero_matrix #t #(r.add_comm_monoid.add_monoid.has_zero) n)
  = let zm = zero_matrix #t #(r.add_comm_monoid.add_monoid.has_zero) n in
    let pf (i j: fin n) : Lemma (matrix_mul a zm i j = zm i j)
      = matrix_right_absorption_pointwise a i j;
        reflexivity (zero #t);
        symmetry (zm i j) (zero #t);
        transitivity (matrix_mul a zm i j) (zero #t) (zm i j)
    in
    Classical.forall_intro_2 pf;
    matrix_eq_bool_iff_pointwise (matrix_mul a zm) zm

(* ----------------------------------------------------------------- *)
(*  Multiplicative tower instances                                   *)
(* ----------------------------------------------------------------- *)

instance matrix_mul_semigroup (t: Type) {| r: semiring t |} (n: nat)
  : mul_semigroup (square_matrix t n)
  = {
    has_mul = matrix_has_mul t #r n;
    associativity = matrix_mul_associativity #t #r #n;
  }

instance matrix_mul_monoid (t: Type) {| r: semiring t |} (n: nat)
  : mul_monoid (square_matrix t n)
  = {
    mul_semigroup = matrix_mul_semigroup t #r n;
    has_one = matrix_has_one_of_semiring t #r n;
    left_mul_identity = matrix_mul_left_identity #t #r #n;
    right_mul_identity = matrix_mul_right_identity #t #r #n;
  }

instance matrix_semiring (t: Type) {| r: semiring t |} (n: nat)
  : semiring (square_matrix t n)
  = {
    add_comm_monoid = matrix_add_comm_monoid t #r.add_comm_monoid n;
    mul_monoid = matrix_mul_monoid t #r n;
    left_absorption = matrix_left_absorption #t #r #n;
    right_absorption = matrix_right_absorption #t #r #n;
    left_distributivity = matrix_left_distributivity #t #r #n;
    right_distributivity = matrix_right_distributivity #t #r #n;
  }

instance matrix_ring (t: Type) {| r: ring t |} (n: nat)
  : ring (square_matrix t n)
  = {
    semiring = matrix_semiring t #r.semiring n;
    add_comm_group = matrix_add_comm_group t #r.add_comm_group n;
  }
