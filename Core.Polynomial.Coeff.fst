module Core.Polynomial.Coeff

(*
   Coefficient-level theory for polynomial multiplication.

   Main results:
     - coeff_poly_mul: convolution identity
         coeff(p*q, k) = sum_range (fun i -> coeff p i * coeff q (k-i)) 0 (L.length p)
     - coeff_sum_range: linearity of coeff over polynomial-valued sum_range
     - monomial_decomposition: p = sum_range (fun i -> monomial (coeff p i) i) 0 (L.length p)
*)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Helpers
open Core.Algebra.Combinators
open Core.Polynomial
open Core.Polynomial.Div
open Core.FinSum

(* ================================================================ *)
(*  Helpers                                                          *)
(* ================================================================ *)

(* Index shift for sum_range:
   sum_range (fun j -> f (j + offset)) lo hi = sum_range f (lo+offset) (hi+offset) *)
let rec sum_range_shift
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (offset lo hi: nat)
  : Lemma (ensures sum_range (fun (j:nat) -> f (Prims.op_Addition j offset)) lo hi
                 = sum_range f (Prims.op_Addition lo offset) (Prims.op_Addition hi offset))
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo >= hi then begin
      sum_range_empty (fun (j:nat) -> f (Prims.op_Addition j offset)) lo hi;
      sum_range_empty f (Prims.op_Addition lo offset) (Prims.op_Addition hi offset);
      reflexivity (zero <: t)
    end
    else begin
      sum_range_unfold_left (fun (j:nat) -> f (Prims.op_Addition j offset)) lo hi;
      sum_range_unfold_left f (Prims.op_Addition lo offset) (Prims.op_Addition hi offset);
      assert (Prims.op_Addition (nat_succ lo) offset == nat_succ (Prims.op_Addition lo offset));
      sum_range_shift f offset (nat_succ lo) hi;
      reflexivity (f (Prims.op_Addition lo offset));
      add_congruence (f (Prims.op_Addition lo offset))
                     (sum_range (fun (j:nat) -> f (Prims.op_Addition j offset)) (nat_succ lo) hi)
                     (f (Prims.op_Addition lo offset))
                     (sum_range f (Prims.op_Addition (nat_succ lo) offset) (Prims.op_Addition hi offset))
    end

(* Coefficient of zero-cons: coeff (zero @ p) 0 = zero *)
private let coeff_zero_cons_at_zero (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t)
  : Lemma (coeff ((zero <: t) @ p) 0 = (zero <: t))
  = reflexivity (zero <: t)

(* Coefficient of zero-cons at k >= 1: coeff (zero @ p) k = coeff p (k-1) *)
private let coeff_zero_cons_at_succ (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (k: nat{k >= 1})
  : Lemma (coeff ((zero <: t) @ p) k = coeff p (Prims.op_Subtraction k 1))
  = zero_shift_coeff p (Prims.op_Subtraction k 1)

(* sum_range of all-zero function = zero *)
let rec sum_range_all_zero
  (#t:Type) {| m: add_comm_group t |}
  (f: nat -> t) (lo hi: nat)
  (h: (k: nat{lo <= k /\ k < hi}) -> Lemma (f k = (zero <: t)))
  : Lemma (ensures sum_range f lo hi = (zero <: t))
          (decreases (hi - lo))
  = if lo >= hi then begin
      sum_range_empty f lo hi;
      reflexivity (zero <: t)
    end
    else begin
      sum_range_unfold_left f lo hi;
      h lo;
      sum_range_all_zero f (nat_succ lo) hi
        (fun (k: nat{nat_succ lo <= k /\ k < hi}) -> h k);
      elim_equatable_laws t ();
      trans_for_calc t ();
      m.add_zero (zero <: t);
      add_congruence (f lo) (sum_range f (nat_succ lo) hi)
                     (zero <: t) (zero <: t);
      transitivity (sum_range f lo hi)
                   (f lo + sum_range f (nat_succ lo) hi)
                   ((zero <: t) + (zero <: t));
      transitivity (sum_range f lo hi)
                   ((zero <: t) + (zero <: t))
                   (zero <: t)
    end

(* ================================================================ *)
(*  Convolution identity: coeff (poly_mul p q) k                    *)
(*    = sum_range (fun i -> coeff p i * coeff q (k - i)) 0 len_p    *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let rec coeff_poly_mul (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t) (k: nat)
  : Lemma (ensures coeff (poly_mul p q) k
                 = sum_range (fun (i:nat) -> coeff p i * coeff q (Prims.op_Subtraction k i))
                             0 (L.length p))
          (decreases (L.length p))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if L.length p = 0 then begin
      (* p = []; poly_mul [] q == []; coeff [] k = zero *)
      assert (p == ([] <: polynomial t));
      sum_range_empty (fun (i:nat) -> coeff p i * coeff q (Prims.op_Subtraction k i)) 0 0;
      reflexivity (zero <: t)
    end
    else begin
      let a : t = L.hd p in
      let p' : polynomial t = L.tl p in
      assert (L.length p' == Prims.op_Subtraction (L.length p) 1);

      (* Step 1: poly_mul_reveal gives us the recursive structure *)
      poly_mul_reveal a p' q;
      let scalar_part : polynomial t = poly_mul (a @ poly_zero) q in
      let shifted_part : polynomial t = (zero <: t) @ (poly_mul p' q) in
      let rhs_poly : polynomial t = poly_add scalar_part shifted_part in

      (* Step 2: extract coefficients from both sides *)
      poly_eq_means_equal_coeffs (poly_mul (a @ p') q) rhs_poly k;
      poly_add_coeff scalar_part shifted_part k;

      (* Step 3: scalar part coefficient *)
      poly_mul_singleton_coeff a q k;

      (* Step 4: shifted part coefficient *)
      let shifted_coeff : t =
        if k = 0 then begin
          coeff_zero_cons_at_zero (poly_mul p' q);
          (zero <: t)
        end
        else begin
          coeff_zero_cons_at_succ (poly_mul p' q) k;
          coeff (poly_mul p' q) (Prims.op_Subtraction k 1)
        end
      in

      (* Step 5: IH on the tail *)
      if k >= 1 then begin
        coeff_poly_mul p' q (Prims.op_Subtraction k 1);
        (* coeff (poly_mul p' q) (k-1)
           = sum_range (fun j -> coeff p' j * coeff q ((k-1)-j)) 0 (L.length p') *)
        ()
      end;

      (* Step 6: Assemble the convolution sum *)
      (* Target: sum_range (fun i -> coeff p i * coeff q (k-i)) 0 (L.length p)
         = coeff p 0 * coeff q k + sum_range (fun i -> coeff p i * coeff q (k-i)) 1 (L.length p)
         by sum_range_unfold_left *)
      let conv_f (i:nat) : t = coeff p i * coeff q (Prims.op_Subtraction k i) in
      sum_range_unfold_left conv_f 0 (L.length p);
      (* RHS = conv_f 0 + sum_range conv_f 1 (L.length p)
             = coeff p 0 * coeff q k + sum_range conv_f 1 (L.length p) *)

      (* Step 7: Show coeff p 0 = a *)
      assert (coeff p 0 == a);

      (* Step 8: Show sum_range conv_f 1 (L.length p) equals the shifted IH *)
      (* conv_f j = coeff p j * coeff q (k-j)  for j >= 1
         = coeff p' (j-1) * coeff q (k-j)      [since coeff (a::p') j = coeff p' (j-1) for j>=1]
         Let g j = coeff p' j * coeff q ((k-1)-j).
         Then conv_f (j+1) = coeff p' j * coeff q (k-(j+1)) = coeff p' j * coeff q ((k-1)-j) = g j.
         So sum_range conv_f 1 (L.length p) = sum_range (fun j -> conv_f (j+1)) 0 (L.length p - 1)
            = sum_range g 0 (L.length p')
         which is the IH result when k >= 1, or zero when k = 0. *)
      let g (j:nat) : t = coeff p' j * coeff q (Prims.op_Subtraction (Prims.op_Subtraction k 1) j) in

      (* Use sum_range_shift to relate conv_f on [1, len_p) to g on [0, len_p') *)
      sum_range_shift conv_f 1 0 (L.length p');
      (* sum_range (fun j -> conv_f (j+1)) 0 (L.length p')
         = sum_range conv_f 1 (L.length p) *)

      (* Show pointwise equality: conv_f (j+1) = g j for j in [0, len_p') *)
      let conv_f_shifted_eq_g (j: nat{j < L.length p'})
        : Lemma (conv_f (Prims.op_Addition j 1) = g j)
        = (* conv_f (j+1) = coeff p (j+1) * coeff q (k - (j+1))
             coeff p (j+1) = coeff (a :: p') (j+1) = coeff p' j  [list index]
             coeff q (k - (j+1)) = coeff q ((k-1) - j)
             So conv_f (j+1) = coeff p' j * coeff q ((k-1) - j) = g j *)
          assert (coeff p (Prims.op_Addition j 1) == coeff p' j);
          assert (Prims.op_Subtraction k (Prims.op_Addition j 1) ==
                  Prims.op_Subtraction (Prims.op_Subtraction k 1) j);
          reflexivity (coeff p' j * coeff q (Prims.op_Subtraction (Prims.op_Subtraction k 1) j))
      in

      sum_range_congruence
        (fun (j:nat) -> conv_f (Prims.op_Addition j 1)) g 0 (L.length p')
        (fun (j: nat{0 <= j /\ j < L.length p'}) -> conv_f_shifted_eq_g j);

      (* Now chain everything together *)
      if k = 0 then begin
        (* shifted part is zero, and sum_range g 0 (L.length p') should also be zero *)
        (* g j = coeff p' j * coeff q (-1 - j) = coeff p' j * zero = zero *)
        let g_zero (j: nat{0 <= j /\ j < L.length p'})
          : Lemma (g j = (zero <: t))
          = assert (Prims.op_Subtraction (Prims.op_Subtraction k 1) j < 0);
            (* coeff q (negative) = zero *)
            mul_congruence (coeff p' j) (coeff q (Prims.op_Subtraction (Prims.op_Subtraction k 1) j))
                           (coeff p' j) (zero <: t);
            reflexivity (coeff p' j);
            x_mul_zero (coeff p' j);
            transitivity (g j) (coeff p' j * (zero <: t)) (zero <: t)
        in
        sum_range_all_zero g 0 (L.length p') g_zero;
        (* LHS = coeff (poly_mul p q) k
               = coeff rhs_poly k  [by poly_eq_means_equal_coeffs]
               = coeff scalar_part k + coeff shifted_part k  [poly_add_coeff]
               = a * coeff q k + zero
           RHS = sum_range conv_f 0 (L.length p)
               = conv_f 0 + sum_range conv_f 1 (L.length p)
               = a * coeff q k + sum_range (fun j -> conv_f (j+1)) 0 (L.length p')
               = a * coeff q k + sum_range g 0 (L.length p')  [congruence]
               = a * coeff q k + zero  [g is all zero]

           Both = a * coeff q k. *)
        let target : t = a * coeff q k in
        let lhs_val : t = coeff (poly_mul (a @ p') q) k in
        let sum_val : t = sum_range conv_f 0 (L.length p) in

        (* LHS chain: lhs_val = target *)
        add_congruence (coeff scalar_part k) (coeff shifted_part k)
                       target (zero <: t);
        x_plus_zero target;
        transitivity lhs_val
                     (coeff scalar_part k + coeff shifted_part k)
                     (target + (zero <: t));
        transitivity lhs_val (target + (zero <: t)) target;

        (* Chain: sum_range conv_f 1 (L.length p) = zero *)
        symmetry (sum_range (fun (j:nat) -> conv_f (Prims.op_Addition j 1)) 0 (L.length p'))
                 (sum_range conv_f 1 (L.length p));
        transitivity (sum_range conv_f 1 (L.length p))
                     (sum_range (fun (j:nat) -> conv_f (Prims.op_Addition j 1)) 0 (L.length p'))
                     (sum_range g 0 (L.length p'));
        transitivity (sum_range conv_f 1 (L.length p))
                     (sum_range g 0 (L.length p'))
                     (zero <: t);

        (* RHS chain: sum_val = target *)
        reflexivity (conv_f 0);
        add_congruence (conv_f 0) (sum_range conv_f 1 (L.length p))
                       (conv_f 0) (zero <: t);
        x_plus_zero (conv_f 0);
        transitivity sum_val
                     (conv_f 0 + sum_range conv_f 1 (L.length p))
                     (conv_f 0 + (zero <: t));
        transitivity sum_val (conv_f 0 + (zero <: t)) (conv_f 0);
        (* conv_f 0 == target propositionally *)

        (* Final: lhs_val = target = sum_val *)
        symmetry sum_val target;
        transitivity lhs_val target sum_val
      end
      else begin
        (* k >= 1: shifted part = coeff (poly_mul p' q) (k-1) = sum_range g 0 (L.length p') by IH *)
        reflexivity (a * coeff q k);
        add_congruence (coeff scalar_part k) (coeff shifted_part k)
                       (a * coeff q k) (coeff (poly_mul p' q) (Prims.op_Subtraction k 1));
        add_congruence (a * coeff q k) (coeff (poly_mul p' q) (Prims.op_Subtraction k 1))
                       (a * coeff q k) (sum_range g 0 (L.length p'));
        let lhs_val : t = coeff (poly_mul (a @ p') q) k in
        let sum_val : t = sum_range conv_f 0 (L.length p) in
        let mid : t = a * coeff q k + sum_range g 0 (L.length p') in
        transitivity lhs_val (coeff scalar_part k + coeff shifted_part k) mid;

        (* Chain: sum_range conv_f 1 (L.length p) = sum_range g 0 (L.length p') *)
        symmetry (sum_range (fun (j:nat) -> conv_f (Prims.op_Addition j 1)) 0 (L.length p'))
                 (sum_range conv_f 1 (L.length p));
        transitivity (sum_range conv_f 1 (L.length p))
                     (sum_range (fun (j:nat) -> conv_f (Prims.op_Addition j 1)) 0 (L.length p'))
                     (sum_range g 0 (L.length p'));
        (* Now: conv_f 0 + sum_range conv_f 1 (L.length p) = mid *)
        reflexivity (conv_f 0);
        add_congruence (conv_f 0) (sum_range conv_f 1 (L.length p))
                       (conv_f 0) (sum_range g 0 (L.length p'));
        (* conv_f 0 == a * coeff q k propositionally, so this is mid *)
        transitivity sum_val
                     (conv_f 0 + sum_range conv_f 1 (L.length p))
                     mid;
        symmetry sum_val mid;
        transitivity lhs_val mid sum_val
      end
    end
#pop-options

(* ================================================================ *)
(*  Linearity of coeff over polynomial-valued sum_range             *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec coeff_sum_range (#t:Type) {| cr: commutative_ring t |}
  (f: nat -> polynomial t) (lo hi: nat) (k: nat)
  : Lemma (ensures coeff (sum_range #(polynomial t) #(polynomial_acg cr) f lo hi) k
                 = sum_range (fun (i:nat) -> coeff (f i) k) lo hi)
          (decreases (hi - lo))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo >= hi then begin
      sum_range_empty #(polynomial t) #(polynomial_acg cr) f lo hi;
      sum_range_empty (fun (i:nat) -> coeff (f i) k) lo hi;
      (* LHS: coeff (zero <: polynomial t) k = coeff [] k = zero *)
      (* RHS: zero *)
      reflexivity (zero <: t)
    end
    else begin
      sum_range_unfold_left #(polynomial t) #(polynomial_acg cr) f lo hi;
      (* sum_range f lo hi == (polynomial_acg cr).add (f lo) (sum_range f (lo+1) hi)
                           == poly_add (f lo) (sum_range f (lo+1) hi) *)
      let rest : polynomial t = sum_range #(polynomial t) #(polynomial_acg cr) f (nat_succ lo) hi in
      poly_add_coeff (f lo) rest k;
      coeff_sum_range f (nat_succ lo) hi k;
      sum_range_unfold_left (fun (i:nat) -> coeff (f i) k) lo hi;
      (* LHS = coeff (poly_add (f lo) rest) k
             = coeff (f lo) k + coeff rest k  [poly_add_coeff]
             = coeff (f lo) k + sum_range (fun i -> coeff (f i) k) (lo+1) hi  [IH]
         RHS = (fun lo -> coeff (f lo) k) lo + sum_range (fun i -> coeff (f i) k) (lo+1) hi
             = coeff (f lo) k + sum_range (fun i -> coeff (f i) k) (lo+1) hi  *)
      reflexivity (coeff (f lo) k);
      add_congruence (coeff (f lo) k) (coeff rest k)
                     (coeff (f lo) k) (sum_range (fun (i:nat) -> coeff (f i) k) (nat_succ lo) hi);
      let lhs : t = coeff (sum_range #(polynomial t) #(polynomial_acg cr) f lo hi) k in
      let mid : t = coeff (f lo) k + sum_range (fun (i:nat) -> coeff (f i) k) (nat_succ lo) hi in
      let rhs : t = sum_range (fun (i:nat) -> coeff (f i) k) lo hi in
      transitivity lhs (coeff (f lo) k + coeff rest k) mid;
      symmetry rhs mid;
      transitivity lhs mid rhs
    end
#pop-options

(* ================================================================ *)
(*  Monomial decomposition: p = sum of its monomial components      *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let monomial_decomposition (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (n: nat{n >= L.length p})
  : Lemma (ensures poly_eq
             (sum_range #(polynomial t) #(polynomial_acg cr)
                (fun (i:nat) -> monomial (coeff p i) i) 0 n)
             p)
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let decomp : polynomial t =
      sum_range #(polynomial t) #(polynomial_acg cr)
        (fun (i:nat) -> monomial (coeff p i) i) 0 n in
    let aux (j: nat) : Lemma (coeff decomp j = coeff p j) =
      coeff_sum_range (fun (i:nat) -> monomial (coeff p i) i) 0 n j;
      (* coeff decomp j = sum_range (fun i -> coeff (monomial (coeff p i) i) j) 0 n *)
      (* By monomial_coeff: coeff (monomial c m) j = if m = j then c else zero *)
      let term (i:nat) : t = coeff (monomial (coeff p i) i) j in
      let target_term (i:nat) : t = if i = j then coeff p i else (zero <: t) in
      let term_eq (i: nat{0 <= i /\ i < n}) : Lemma (term i = target_term i) =
        monomial_coeff (coeff p i) i j;
        if i = j then reflexivity (coeff p i)
        else reflexivity (zero <: t)
      in
      sum_range_congruence term target_term 0 n term_eq;
      (* Now: sum_range target_term 0 n.
         If j < n: target_term j = coeff p j, all others are zero.
         If j >= n: all terms are zero, and coeff p j = zero (since n >= L.length p). *)
      if j < n then begin
        sum_range_kronecker_in_range j (fun (i:nat) -> coeff p i) 0 n;
        (* sum_range (pointwise_mul (kronecker_delta j) (fun i -> coeff p i)) 0 n = coeff p j *)
        let pw : nat -> t = pointwise_mul (kronecker_delta j) (fun (i:nat) -> coeff p i) in
        let pw_eq_target (i: nat{0 <= i /\ i < n}) : Lemma (pw i = target_term i) =
          pointwise_mul_unfold (kronecker_delta j) (fun (i:nat) -> coeff p i) i;
          if i = j then begin
            one_mul_x (coeff p j);
            reflexivity (coeff p j);
            symmetry (target_term i) (coeff p j)
          end
          else begin
            zero_mul_x (coeff p i);
            reflexivity (zero <: t);
            symmetry (target_term i) (zero <: t)
          end
        in
        sum_range_congruence pw target_term 0 n pw_eq_target;
        (* sum_range pw 0 n = sum_range target_term 0 n *)
        (* Chain: coeff decomp j = sum_range target_term 0 n *)
        transitivity (coeff decomp j) (sum_range term 0 n) (sum_range target_term 0 n);
        (* Chain: sum_range target_term 0 n = coeff p j *)
        symmetry (sum_range pw 0 n) (sum_range target_term 0 n);
        transitivity (sum_range target_term 0 n) (sum_range pw 0 n) (coeff p j);
        (* Final *)
        transitivity (coeff decomp j)
                     (sum_range target_term 0 n)
                     (coeff p j)
      end
      else begin
        (* j >= n >= L.length p, so coeff p j = zero *)
        (* All terms in sum are zero (since i < n <= j means i ≠ j, so target_term i = zero) *)
        sum_range_all_zero target_term 0 n
          (fun (i: nat{0 <= i /\ i < n}) -> reflexivity (zero <: t));
        (* Chain: coeff decomp j = sum_range target_term 0 n *)
        transitivity (coeff decomp j) (sum_range term 0 n) (sum_range target_term 0 n);
        (* coeff p j = zero since j >= L.length p *)
        reflexivity (zero <: t);
        transitivity (coeff decomp j) (sum_range target_term 0 n) (coeff p j)
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq decomp p
#pop-options
