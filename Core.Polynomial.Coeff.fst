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
open Core.FinSum

(* Coefficient of zero-cons: coeff (zero @ p) 0 = zero *)
private let coeff_zero_cons_at_zero (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t)
  : Lemma (coeff ((zero <: t) @ p) 0 = (zero <: t))
  = elim_equatable_laws t ()

(* Coefficient of zero-cons at k >= 1: coeff (zero @ p) k = coeff p (k-1) *)
private let coeff_zero_cons_at_succ (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (k: nat{k >= 1})
  : Lemma (coeff ((zero <: t) @ p) k = coeff p ((k - 1)))
  = zero_shift_coeff p ((k - 1))

(* ================================================================ *)
(*  Convolution identity: coeff (poly_mul p q) k                    *)
(*    = sum_range (fun i -> coeff p i * coeff q (k - i)) 0 len_p    *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let rec coeff_poly_mul (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t) (k: nat)
  : Lemma (ensures coeff (p * q) k
                 = sum_range (fun (i:nat) -> coeff p i * coeff q ((k - i)))
                             0 (L.length p))

  = elim_equatable_laws t ();
    trans_for_calc t ();
    if L.length p = 0 then begin
      (* p = []; poly_mul [] q == []; coeff [] k = zero *)
      assert (p == ([] <: polynomial t));
      sum_range_empty (fun (i:nat) -> coeff p i * coeff q ((k - i))) 0 0;
      ()
    end
    else begin
      let a : t = L.hd p in
      let p' : polynomial t = L.tl p in
      assert (L.length p' == ((L.length p) - 1));

      (* Step 1: poly_mul_reveal gives us the recursive structure *)
      poly_mul_reveal a p' q;
      let scalar_part : polynomial t = ((a @ poly_zero) * q) in
      let shifted_part : polynomial t = (zero <: t) @ ((p' * q)) in
      let rhs_poly : polynomial t = (scalar_part + shifted_part) in

      (* Step 2: extract coefficients from both sides *)
      poly_eq_means_equal_coeffs ((a @ p') * q) rhs_poly k;
      poly_add_coeff scalar_part shifted_part k;

      (* Step 3: scalar part coefficient *)
      poly_mul_singleton_coeff a q k;

      (* Step 4: shifted part coefficient *)
      let shifted_coeff : t =
        if k = 0 then begin
          coeff_zero_cons_at_zero ((p' * q));
          (zero <: t)
        end
        else begin
          coeff_zero_cons_at_succ ((p' * q)) k;
          coeff ((p' * q)) ((k - 1))
        end
      in

      (* Step 5: IH on the tail *)
      if k >= 1 then begin
        coeff_poly_mul p' q ((k - 1));
        (* coeff (poly_mul p' q) (k-1)
           = sum_range (fun j -> coeff p' j * coeff q ((k-1)-j)) 0 (L.length p') *)
        ()
      end;

      (* Step 6: Assemble the convolution sum *)
      (* Target: sum_range (fun i -> coeff p i * coeff q (k-i)) 0 (L.length p)
         = coeff p 0 * coeff q k + sum_range (fun i -> coeff p i * coeff q (k-i)) 1 (L.length p)
         by sum_range_unfold_left *)
      let conv_f (i:nat) : t = coeff p i * coeff q ((k - i)) in
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
      let g (j:nat) : t = coeff p' j * coeff q ((((k - 1)) - j)) in

      (* Use sum_range_shift to relate conv_f on [1, len_p) to g on [0, len_p') *)
      sum_range_shift conv_f 1 0 (L.length p');
      (* sum_range (fun j -> conv_f (j+1)) 0 (L.length p')
         = sum_range conv_f 1 (L.length p) *)

      (* Show pointwise equality: conv_f (j+1) = g j for j in [0, len_p') *)
      let conv_f_shifted_eq_g (j: nat{j < L.length p'})
        : Lemma (conv_f ((j ++ 1)) = g j)
        = (* conv_f (j+1) = coeff p (j+1) * coeff q (k - (j+1))
             coeff p (j+1) = coeff (a :: p') (j+1) = coeff p' j  [list index]
             coeff q (k - (j+1)) = coeff q ((k-1) - j)
             So conv_f (j+1) = coeff p' j * coeff q ((k-1) - j) = g j *)
          assert (coeff p ((j ++ 1)) == coeff p' j);
          assert ((k - ((j ++ 1))) ==
                  (((k - 1)) - j));
          ()
      in

      sum_range_congruence
        (fun (j:nat) -> conv_f ((j ++ 1))) g 0 (L.length p')
        (fun (j: nat{0 <= j /\ j < L.length p'}) -> conv_f_shifted_eq_g j);

      (* Now chain everything together *)
      if k = 0 then begin
        (* shifted part is zero, and sum_range g 0 (L.length p') should also be zero *)
        (* g j = coeff p' j * coeff q (-1 - j) = coeff p' j * zero = zero *)
        let g_zero (j: nat{0 <= j /\ j < L.length p'})
          : Lemma (g j = (zero <: t))
          = assert ((((k - 1)) - j) < 0);
            (* coeff q (negative) = zero *)
            mul_congruence (coeff p' j) (coeff q ((((k - 1)) - j)))
                           (coeff p' j) (zero <: t);
            x_mul_zero (coeff p' j);
            ()
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
        let lhs_val : t = coeff ((a @ p') * q) k in
        let sum_val : t = sum_range conv_f 0 (L.length p) in

        (* LHS chain: lhs_val = target *)
        add_congruence (coeff scalar_part k) (coeff shifted_part k)
                       target (zero <: t);
        x_plus_zero target;
        ();



        (* Chain: sum_range conv_f 1 (L.length p) = zero *)
        ();

        ();


        ();



        (* RHS chain: sum_val = target *)
        add_congruence (conv_f 0) (sum_range conv_f 1 (L.length p))
                       (conv_f 0) (zero <: t);
        x_plus_zero (conv_f 0);
        ();


        (* conv_f 0 == target propositionally *)

        (* Final: lhs_val = target = sum_val *)
        ()
      end
      else begin
        (* k >= 1: shifted part = coeff (poly_mul p' q) (k-1) = sum_range g 0 (L.length p') by IH *)
        add_congruence (coeff scalar_part k) (coeff shifted_part k)
                       (a * coeff q k) (coeff ((p' * q)) ((k - 1)));
        add_congruence (a * coeff q k) (coeff ((p' * q)) ((k - 1)))
                       (a * coeff q k) (sum_range g 0 (L.length p'));
        let lhs_val : t = coeff ((a @ p') * q) k in
        let sum_val : t = sum_range conv_f 0 (L.length p) in
        let mid : t = a * coeff q k + sum_range g 0 (L.length p') in

        (* Chain: sum_range conv_f 1 (L.length p) = sum_range g 0 (L.length p') *)
        ();

        ();


        (* Now: conv_f 0 + sum_range conv_f 1 (L.length p) = mid *)
        add_congruence (conv_f 0) (sum_range conv_f 1 (L.length p))
                       (conv_f 0) (sum_range g 0 (L.length p'));
        (* conv_f 0 == a * coeff q k propositionally, so this is mid *)
        ();


        ()
      end
    end
#pop-options

(* ================================================================ *)
(*  Linearity of coeff over polynomial-valued sum_range             *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 1 --ifuel 1"
let rec coeff_sum_range (#t:Type) {| cr: commutative_ring t |}
  (f: nat -> polynomial t) (lo hi: nat) (k: nat)
  : Lemma (ensures coeff (sum_range f lo hi) k
                 = sum_range (fun (i:nat) -> coeff (f i) k) lo hi)

  = elim_equatable_laws t ();
    trans_for_calc t ();
    if lo >= hi then begin
      sum_range_empty f lo hi;
      sum_range_empty (fun (i:nat) -> coeff (f i) k) lo hi;
      (* LHS: coeff (zero <: polynomial t) k = coeff [] k = zero *)
      (* RHS: zero *)
      ()
    end
    else begin
      sum_range_unfold_left f lo hi;
      (* sum_range f lo hi == (polynomial_acg cr).add (f lo) (sum_range f (lo+1) hi)
                           == poly_add (f lo) (sum_range f (lo+1) hi) *)
      let rest : polynomial t = sum_range f ((lo ++ 1)) hi in
      poly_add_coeff (f lo) rest k;
      coeff_sum_range f ((lo ++ 1)) hi k;
      sum_range_unfold_left (fun (i:nat) -> coeff (f i) k) lo hi;
      (* LHS = coeff (poly_add (f lo) rest) k
             = coeff (f lo) k + coeff rest k  [poly_add_coeff]
             = coeff (f lo) k + sum_range (fun i -> coeff (f i) k) (lo+1) hi  [IH]
         RHS = (fun lo -> coeff (f lo) k) lo + sum_range (fun i -> coeff (f i) k) (lo+1) hi
             = coeff (f lo) k + sum_range (fun i -> coeff (f i) k) (lo+1) hi  *)
      add_congruence (coeff (f lo) k) (coeff rest k)
                     (coeff (f lo) k) (sum_range (fun (i:nat) -> coeff (f i) k) ((lo ++ 1)) hi);
      let lhs : t = coeff (sum_range f lo hi) k in
      let mid : t = coeff (f lo) k + sum_range (fun (i:nat) -> coeff (f i) k) ((lo ++ 1)) hi in
      let rhs : t = sum_range (fun (i:nat) -> coeff (f i) k) lo hi in
      ()
    end
#pop-options

(* ================================================================ *)
(*  Monomial decomposition: p = sum of its monomial components      *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let monomial_decomposition (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (n: nat{n >= L.length p})
  : Lemma (ensures ((sum_range
                (fun (i:nat) -> monomial (coeff p i) i) 0 n)
             = p))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    let decomp : polynomial t =
      sum_range
        (fun (i:nat) -> monomial (coeff p i) i) 0 n in
    let aux (j: nat) : Lemma (coeff decomp j = coeff p j) =
      coeff_sum_range (fun (i:nat) -> monomial (coeff p i) i) 0 n j;
      (* coeff decomp j = sum_range (fun i -> coeff (monomial (coeff p i) i) j) 0 n *)
      (* By monomial_coeff: coeff (monomial c m) j = if m = j then c else zero *)
      let term (i:nat) : t = coeff (monomial (coeff p i) i) j in
      let target_term (i:nat) : t = if i = j then coeff p i else (zero <: t) in
      let term_eq (i: nat{0 <= i /\ i < n}) : Lemma (term i = target_term i) =
        monomial_coeff (coeff p i) i j;
        if i = j then ()
        else ()
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
            ()
          end
          else begin
            zero_mul_x (coeff p i);
            ()
          end
        in
        sum_range_congruence pw target_term 0 n pw_eq_target;
        (* sum_range pw 0 n = sum_range target_term 0 n *)
        (* Chain: coeff decomp j = sum_range target_term 0 n *)
        (* Chain: sum_range target_term 0 n = coeff p j *)
        (* Final *)
        ()


      end
      else begin
        (* j >= n >= L.length p, so coeff p j = zero *)
        (* All terms in sum are zero (since i < n <= j means i ≠ j, so target_term i = zero) *)
        sum_range_all_zero target_term 0 n
          (fun (i: nat{0 <= i /\ i < n}) -> ());
        (* Chain: coeff decomp j = sum_range target_term 0 n *)
        (* coeff p j = zero since j >= L.length p *)
        ()
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq decomp p
#pop-options

(* ================================================================ *)
(*  Named-function variant of coeff_poly_mul                         *)
(* ================================================================ *)

#push-options "--z3rlimit 40 --fuel 0 --ifuel 0"
let coeff_poly_mul_named (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t) (k: nat) (g: nat -> t)
  (h: (i:nat) -> Lemma (g i = coeff p i * coeff q ((k - i))))
  : Lemma (ensures coeff ((p * q)) k = sum_range g 0 (L.length p))
  = elim_equatable_laws t ();
    trans_for_calc t ();
    coeff_poly_mul p q k;
    let conv (i:nat) : t = coeff p i * coeff q ((k - i)) in
    let pw (i: nat{0 <= i /\ i < L.length p}) : Lemma (conv i = g i)
      = h i;
        ()
    in
    sum_range_congruence conv g 0 (L.length p) pw;
    ()
                 
                 
#pop-options
