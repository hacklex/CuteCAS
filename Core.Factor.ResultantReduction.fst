module Core.Factor.ResultantReduction

(* ================================================================ *)
(*  C4b — RESULTANT-REDUCTION algebra closing good-prime existence.  *)
(*                                                                   *)
(*  Layer 2 of the good-prime argument (see Core.Factor.PrimeExists  *)
(*  for Layers 1 and 3).  Establishes, for a prime p and B in ℤ[z]:  *)
(*                                                                   *)
(*    1. lc_survives         : p ∤ lc B ⟹ deg B̄ = deg B             *)
(*    2. deriv_reduce_commute : reduce (B') = (reduce B)'            *)
(*    3. resultant_reduces    : res(B̄, B̄') = φ_p(res(B,B'))          *)
(*         where φ_p = zf ∘ to_fp p : ℤ → 𝔽ₚ is the coeff hom, via   *)
(*         the generic determinant-homomorphism (Core.Matrix.DetHom).*)
(*    4. res_nonzero_coprime  : res(B̄,B̄') ≠ 0 ⟹ coprime B̄ B̄'        *)
(*         (contrapositive of resultant_zero_of_common_divisor).     *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module Cl  = FStar.Classical
module H   = Core.Algebra.Helpers
module DH  = Core.Matrix.DetHom
module DET = Core.Matrix.Determinant
module SYL = Core.Polynomial.Sylvester
module RES = Core.Polynomial.Resultant

open Core.NumberTheory
open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Int
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Permutation
open Core.Vector
open Core.Matrix
open Core.Polynomial.Derivative
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Centered
open Core.Modular.ResidueRing.IntReduce
open Core.Modular.ResidueRing.CenteredPoly
open Core.Modular.PrimeField
open Core.Modular.FpZmodBridge
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.GCD
open Core.Polynomial.SquareFree
open Core.Factor.PrimeSelect

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ---------------------------------------------------------------- *)
(*  The scalar coefficient reduction  φ_p : ℤ → 𝔽ₚ  and its ring-    *)
(*  homomorphism laws.  φ_p a = zf (to_fp p a).                      *)
(* ---------------------------------------------------------------- *)

let phi_c (p:int{is_prime p}) (a:int) : fp p
  = zf #p (to_fp p a)

(* zmod ring +/* are definitionally zmod_add / zmod_mul. *)
private let zadd_reveal (p:int{p > 1}) (a b: zmod p)
  : Lemma (a + b == zmod_add a b) = ()
private let zmul_reveal (p:int{p > 1}) (a b: zmod p)
  : Lemma (a * b == zmod_mul a b) = ()

let phi_c_add (p:int{is_prime p}) (a b:int)
  : Lemma (phi_c p (a + b) = phi_c p a + phi_c p b)
  = H.elim_equatable_laws (fp p) ();
    let x = to_fp p a in
    let y = to_fp p b in
    to_fp_add p a b;                                (* to_fp (a+b) == zmod_add x y *)
    zadd_reveal p x y;                              (* x + y == zmod_add x y *)
    zf_add x y                                      (* zf (x + y) == zf x + zf y *)

let phi_c_mul (p:int{is_prime p}) (a b:int)
  : Lemma (phi_c p (a * b) = phi_c p a * phi_c p b)
  = H.elim_equatable_laws (fp p) ();
    let x = to_fp p a in
    let y = to_fp p b in
    to_fp_mul p a b;                                (* to_fp (a*b) == zmod_mul x y *)
    zmul_reveal p x y;                              (* x * y == zmod_mul x y *)
    zf_mul x y                                      (* zf (x * y) == zf x * zf y *)

let phi_c_one (p:int{is_prime p})
  : Lemma (phi_c p (one #int) = (one #(fp p)))
  = H.elim_equatable_laws (fp p) ();
    to_fp_one p;                                    (* to_fp p 1 == zmod_one p *)
    zf_one p                                        (* zf (zmod_one p) == fp_one p *)

let phi_c_zero (p:int{is_prime p})
  : Lemma (phi_c p (zero #int) = (zero #(fp p)))
  = H.elim_equatable_laws (fp p) ();
    H.trans_for_calc (fp p) ();
    let a = phi_c p 0 in
    phi_c_add p 0 0;                                (* phi_c (0+0) = a + a ; 0+0 == 0 so a = a + a *)
    H.x_plus_zero a;                                (* a + 0 = a *)
    (* a + a = a = a + 0, cancel left a *)
    transitivity (a + a) a (a + (zero #(fp p)));
    H.group_cancel_left a a (zero #(fp p))

(* neg follows from add + zero by group cancellation. *)
let phi_c_neg (p:int{is_prime p}) (a:int)
  : Lemma (phi_c p (- a) = - (phi_c p a))
  = H.elim_equatable_laws (fp p) ();
    H.trans_for_calc (fp p) ();
    let nn = phi_c p (- a) in
    let pp = phi_c p a in
    (* φ(-a) + φ(a) = φ(-a + a) = φ(0) = 0, so φ(-a) = -(φ(a)). *)
    phi_c_add p (- a) a;                            (* nn + pp = φ(-a + a) ; (-a)+a==0 *)
    phi_c_zero p;                                   (* φ(0) = 0, hence nn + pp = 0 *)
    H.neg_x_plus_x pp;                              (* (-pp) + pp = 0 *)
    add_commutativity nn pp;                        (* nn + pp = pp + nn *)
    add_commutativity (- pp) pp;                    (* (-pp) + pp = pp + (-pp) *)
    (* pp + nn = 0 = pp + (-pp), cancel left pp *)
    transitivity (pp + nn) (nn + pp) (zero #(fp p));
    transitivity (pp + (- pp)) ((- pp) + pp) (zero #(fp p));
    transitivity (pp + nn) (zero #(fp p)) (pp + (- pp));
    H.group_cancel_left pp nn (- pp)

(* Bridge:  coeff (reduce_to_fp p b) i = φ_p (coeff b i). *)
let reduce_coeff_phi (p:int{is_prime p}) (b: polynomial int) (i:int)
  : Lemma (coeff (reduce_to_fp p b) i == phi_c p (coeff b i))
  = reduce_to_fp_coeff p b i

(* φ_p is a congruence on int (which is an eqtype). *)
let phi_c_congr (p:int{is_prime p}) (a b:int)
  : Lemma (requires a = b) (ensures phi_c p a = phi_c p b)
  = H.elim_equatable_laws (fp p) ()

(* φ_p commutes with nat_scale (additive iteration). *)
let rec phi_c_nat_scale (p:int{is_prime p}) (n:nat) (x:int)
  : Lemma (ensures phi_c p (nat_scale n x) = nat_scale n (phi_c p x))
          (decreases n)
  = H.elim_equatable_laws (fp p) ();
    H.trans_for_calc (fp p) ();
    if n = 0 then begin
      nat_scale_zero #int x;                         (* nat_scale 0 x == zero *)
      nat_scale_zero #(fp p) (phi_c p x);            (* nat_scale 0 (phi x) == zero *)
      phi_c_zero p
    end else begin
      let m : nat = n - 1 in
      nat_scale_succ #int m x;                        (* nat_scale n x == x + nat_scale m x *)
      nat_scale_succ #(fp p) m (phi_c p x);           (* nat_scale n (phi x) == phi x + nat_scale m (phi x) *)
      phi_c_add p x (nat_scale m x);                  (* phi (x + nat_scale m x) = phi x + phi (nat_scale m x) *)
      phi_c_nat_scale p m x;                          (* phi (nat_scale m x) = nat_scale m (phi x) *)
      add_congruence (phi_c p x) (phi_c p (nat_scale m x))
                     (phi_c p x) (nat_scale m (phi_c p x));
      transitivity (phi_c p (nat_scale n x))
                   (phi_c p x + phi_c p (nat_scale m x))
                   (phi_c p x + nat_scale m (phi_c p x))
    end

(* ---------------------------------------------------------------- *)
(*  Lemma 2 : reduction commutes with the formal derivative.        *)
(* ---------------------------------------------------------------- *)

let deriv_reduce_commute (p:int{is_prime p}) (b: polynomial int)
  : Lemma (reduce_to_fp p (poly_deriv b) = poly_deriv (reduce_to_fp p b))
  = let lhs = reduce_to_fp p (poly_deriv b) in
    let rhs = poly_deriv (reduce_to_fp p b) in
    let h (j:nat) : Lemma (coeff lhs j = coeff rhs j) =
      H.elim_equatable_laws (fp p) ();
      H.trans_for_calc (fp p) ();
      let cbj1 = coeff b (j ++ 1) in
      (* LHS: coeff lhs j == phi (coeff (poly_deriv b) j) = phi (nat_scale (j+1) cbj1) *)
      reduce_coeff_phi p (poly_deriv b) j;
      poly_deriv_coeff #int b j;                      (* coeff (poly_deriv b) j = nat_scale (j+1) cbj1 *)
      phi_c_congr p (coeff (poly_deriv b) j) (nat_scale (j ++ 1) cbj1);
      phi_c_nat_scale p (j ++ 1) cbj1;                 (* phi (nat_scale (j+1) cbj1) = nat_scale (j+1) (phi cbj1) *)
      (* RHS: coeff rhs j = nat_scale (j+1) (coeff (reduce b) (j+1)) = nat_scale (j+1) (phi cbj1) *)
      poly_deriv_coeff #(fp p) (reduce_to_fp p b) j;
      reduce_coeff_phi p b (j ++ 1);                   (* coeff (reduce b) (j+1) == phi cbj1 *)
      nat_scale_congruence #(fp p) (j ++ 1)
        (coeff (reduce_to_fp p b) (j ++ 1)) (phi_c p cbj1)
    in
    poly_eq_by_coeff lhs rhs h

(* ---------------------------------------------------------------- *)
(*  Lemma 3 : the resultant reduces mod p.                          *)
(*    res(B̄, B̄') = φ_p(res(B, B'))   for ANY formal degree bounds.  *)
(*  Sylvester entries are coefficients of B / B'; φ_p is a ring hom  *)
(*  on those coefficients, so the entrywise-reduced Sylvester matrix *)
(*  is  map_matrix φ_p (Sylvester B B'),  and det commutes with the  *)
(*  ring hom (Core.Matrix.DetHom.det_hom).                           *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let resultant_reduces (p:int{is_prime p})
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (b b': polynomial int)
  : Lemma (RES.resultant m_deg n_deg (reduce_to_fp p b) (reduce_to_fp p b')
         = phi_c p (RES.resultant m_deg n_deg b b'))
  = H.elim_equatable_laws (fp p) ();
    H.trans_for_calc (fp p) ();
    let sz : pos = m_deg ++ n_deg in
    let rb  = reduce_to_fp p b in
    let rb' = reduce_to_fp p b' in
    let sB  : square_matrix int sz = SYL.sylvester_matrix m_deg n_deg b b' in
    let sRB : square_matrix (fp p) sz = SYL.sylvester_matrix m_deg n_deg rb rb' in
    let mapS : square_matrix (fp p) sz = DH.map_matrix (phi_c p) sB in
    (* entrywise:  sRB i j = φ_p (sB i j) = mapS i j *)
    let syl_entry (i j: fin sz) : Lemma (sRB i j = mapS i j) =
      H.elim_equatable_laws (fp p) ();
      if (i <: nat) < n_deg then begin
        SYL.sylvester_p_block_lookup m_deg n_deg rb rb' i j;
        SYL.sylvester_p_block_lookup m_deg n_deg b b' i j;
        reduce_coeff_phi p b ((m_deg ++ (i <: nat)) - (j <: nat))
      end else begin
        SYL.sylvester_q_block_lookup m_deg n_deg rb rb' i j;
        SYL.sylvester_q_block_lookup m_deg n_deg b b' i j;
        reduce_coeff_phi p b' ((i <: nat) - (j <: nat))
      end
    in
    Cl.forall_intro_2 syl_entry;
    DET.det_pointwise_eq sRB mapS;                 (* det sRB = det mapS *)
    phi_c_zero p;
    phi_c_one p;
    DH.det_hom (phi_c p) () () (phi_c_add p) (phi_c_mul p) (phi_c_neg p) sB;
                                                   (* φ_p (det sB) = det mapS *)
    RES.resultant_unfold m_deg n_deg b b';         (* res b b' == det sB *)
    RES.resultant_unfold m_deg n_deg rb rb';       (* res(reduce) == det sRB *)
    symmetry (phi_c p (DET.det sB)) (DET.det mapS);
    transitivity (RES.resultant m_deg n_deg rb rb') (DET.det sRB) (DET.det mapS);
    transitivity (RES.resultant m_deg n_deg rb rb') (DET.det mapS)
                 (phi_c p (RES.resultant m_deg n_deg b b'))
#pop-options

(* ---------------------------------------------------------------- *)
(*  Lemma 1 : the leading coefficient survives reduction (no degree  *)
(*  drop) when p does not divide it.                                 *)
(* ---------------------------------------------------------------- *)

(* φ_p a ≠ 0 whenever p ∤ a  (a % p ≠ 0).  φ_p a = ((a%p)+p)%p. *)
let phi_c_nonzero_of_not_div (p:int{is_prime p}) (a:int)
  : Lemma (requires a % p <> 0)
          (ensures not (phi_c p a = (zero #(fp p))))
  = assert (phi_c p a == ((a % p) + p) % p);
    FStar.Math.Lemmas.lemma_mod_lt a p

#push-options "--z3rlimit 40"
let lc_survives_deg (p:int{is_prime p}) (b: polynomial int)
  : Lemma (requires deg b >= 0 /\ not (phi_c p (poly_lc b) = (zero #(fp p))))
          (ensures deg (reduce_to_fp p b) == deg b)
  = let rb = reduce_to_fp p b in
    let d : nat = deg b in
    H.elim_equatable_laws (fp p) ();
    (* top coefficient survives:  coeff rb d = φ_p (poly_lc b) ≠ 0 *)
    poly_lc_reveal b;                               (* poly_lc b == L.last b *)
    last_eq_index b d;                              (* L.index b d == L.last b *)
    reduce_coeff_phi p b d;                         (* coeff rb d == φ_p (coeff b d) *)
    assert (coeff b d == poly_lc b);
    assert (not (coeff rb d = (zero #(fp p))));
    (* length bound:  length rb <= length b, so deg rb <= d *)
    L.map_lemma (to_fp p) b;
    trim_length_le #(zmod p) (L.map (to_fp p) b);
    L.map_lemma (zf #p) (poly_to_fp p b);
    trim_length_le #(fp p) (L.map (zf #p) (poly_to_fp p b));
    (* deg rb >= d:  else coeff rb d would vanish *)
    let _ : squash (deg rb >= d) =
      if deg rb < d then coeff_above_degree rb d else () in
    ()
#pop-options

(* p ∤ lc B (i.e. lc B % p ≠ 0)  ⟹  deg B̄ = deg B. *)
let lc_survives (p:int{is_prime p}) (b: polynomial int)
  : Lemma (requires deg b >= 0 /\ (poly_lc b) % p <> 0)
          (ensures deg (reduce_to_fp p b) == deg b)
  = phi_c_nonzero_of_not_div p (poly_lc b);
    lc_survives_deg p b

(* ---------------------------------------------------------------- *)
(*  Lemma 4 : res(B̄, B̄') ≠ 0  ⟹  coprime B̄ B̄'.                     *)
(*  Contrapositive of resultant_zero_of_common_divisor: a common     *)
(*  divisor of positive degree forces res = 0.  The degenerate case  *)
(*  B̄' = 0 also forces res = 0 (zero q-row, via skew-symmetry).      *)
(* ---------------------------------------------------------------- *)

(* res(pp, 0) = 0  (the q-argument gives an all-zero Sylvester row). *)
#push-options "--z3rlimit 40 --ifuel 2"
let res_zero_of_q_zero (p:int{is_prime p})
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (pp qq: polynomial (fp p))
  : Lemma (requires m_deg > 0 /\ deg qq < 0)
          (ensures RES.resultant m_deg n_deg pp qq = (zero #(fp p)))
  = H.elim_equatable_laws (fp p) ();
    deg_neg_one_iff_zero qq;                        (* qq == poly_zero == [] *)
    RES.resultant_zero_when_p_all_zero n_deg m_deg qq pp;
    RES.resultant_skew_symmetry m_deg n_deg pp qq;
    let r = RES.resultant m_deg n_deg pp qq in
    H.neg_neg r;                                    (* -(-r) = r *)
    H.neg_zero #(fp p) ()                           (* 0 = -0 *)
#pop-options

#push-options "--z3rlimit 40 --ifuel 2"
let res_nonzero_coprime (p:int{is_prime p})
  (m_deg n_deg: nat{(m_deg ++ n_deg) > 0})
  (bbar bbar': polynomial (fp p))
  : Lemma (requires deg bbar >= 1 /\ deg bbar <= m_deg /\
                    deg bbar' <= n_deg /\
                    not (RES.resultant m_deg n_deg bbar bbar' = (zero #(fp p))))
          (ensures coprime bbar bbar')
  = if coprime bbar bbar' then ()
    else begin
      coprime_reveal bbar bbar';                    (* coprime = (deg gcd = 0) *)
      let g = poly_gcd bbar bbar' in
      gcd_has_degree bbar bbar';                    (* deg g >= 0 ; with ≠0 ⟹ deg g >= 1 *)
      gcd_divides_left bbar bbar';
      gcd_divides_right bbar bbar';
      if deg bbar' >= 0 then
        RES.resultant_zero_of_common_divisor m_deg n_deg bbar bbar' g
      else
        res_zero_of_q_zero p m_deg n_deg bbar bbar'
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  Degree bounds for the assembly.                                 *)
(* ---------------------------------------------------------------- *)

(* deg(f') < deg f  (the formal derivative drops the degree). *)
let deriv_deg_lt (#t:Type) {| cr: commutative_ring t |} (b: polynomial t)
  : Lemma (requires deg b >= 0) (ensures deg (poly_deriv b) <= deg b - 1)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let d' = deg (poly_deriv b) in
    if d' < 0 then ()
    else begin
      leading_coeff_nonzero (poly_deriv b);          (* coeff (poly_deriv b) d' <> 0 *)
      if d' >= deg b then begin
        poly_deriv_coeff #t b d';                     (* coeff (poly_deriv b) d' = nat_scale (d'+1) (coeff b (d'+1)) *)
        coeff_above_degree b (d' ++ 1);               (* coeff b (d'+1) = zero *)
        nat_scale_congruence #t (d' ++ 1) (coeff b (d' ++ 1)) (zero <: t);
        nat_scale_zero_element #t (d' ++ 1);          (* nat_scale (d'+1) zero = zero *)
        transitivity (coeff (poly_deriv b) d')
                     (nat_scale (d' ++ 1) (coeff b (d' ++ 1)))
                     (nat_scale (d' ++ 1) (zero <: t));
        transitivity (coeff (poly_deriv b) d')
                     (nat_scale (d' ++ 1) (zero <: t)) (zero <: t)
      end else ()
    end

(* deg(reduce B) <= deg B  (coefficient reduction never raises degree). *)
let reduce_deg_le (p:int{is_prime p}) (b: polynomial int)
  : Lemma (deg (reduce_to_fp p b) <= deg b)
  = L.map_lemma (to_fp p) b;
    trim_length_le #(zmod p) (L.map (to_fp p) b);
    L.map_lemma (zf #p) (poly_to_fp p b);
    trim_length_le #(fp p) (L.map (zf #p) (poly_to_fp p b))

(* ---------------------------------------------------------------- *)
(*  Assembly : good_of_not_bad.                                     *)
(* ---------------------------------------------------------------- *)

(* coprimality transfers across a poly_eq second argument. *)
let coprime_deriv_transfer (p:int{is_prime p}) (bbar y1 y2: polynomial (fp p))
  : Lemma (requires (y1 = y2) /\ coprime bbar y1)
          (ensures coprime bbar y2)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    reflexivity bbar;                             (* bbar = bbar *)
    gcd_congruence bbar bbar y1 y2;               (* poly_gcd bbar y1 = poly_gcd bbar y2 *)
    degree_well_defined (poly_gcd bbar y1) (poly_gcd bbar y2);
    coprime_reveal bbar y1;
    coprime_reveal bbar y2

(* The "bad" integer whose prime divisors are exactly the bad primes:
   lc(B) · res(B, B').  A prime not dividing it is a good prime. *)
let bad_int (b: polynomial int{deg b >= 1}) : int
  = poly_lc b * RES.resultant (deg b) (deg b - 1) b (poly_deriv b)

let bad_int_unfold (b: polynomial int{deg b >= 1})
  : Lemma (bad_int b == poly_lc b * RES.resultant (deg b) (deg b - 1) b (poly_deriv b))
  = ()

(* p ∤ bad_int B  ⟹  p ∤ lc B. *)
let not_div_lc (p:int{is_prime p}) (b: polynomial int{deg b >= 1})
  : Lemma (requires ~(p `divides` (bad_int b))) (ensures (poly_lc b) % p <> 0)
  = let r = RES.resultant (deg b) (deg b - 1) b (poly_deriv b) in
    if (poly_lc b) % p = 0 then begin
      mod_divides (poly_lc b) p;                  (* p | poly_lc b *)
      divides_mult_right r (poly_lc b) p          (* p | (r * poly_lc b) == bad_int b *)
    end else ()

(* p ∤ bad_int B  ⟹  p ∤ res(B, B'). *)
let not_div_res (p:int{is_prime p}) (b: polynomial int{deg b >= 1})
  : Lemma (requires ~(p `divides` (bad_int b)))
          (ensures (RES.resultant (deg b) (deg b - 1) b (poly_deriv b)) % p <> 0)
  = let r = RES.resultant (deg b) (deg b - 1) b (poly_deriv b) in
    if r % p = 0 then begin
      mod_divides r p;                            (* p | r *)
      divides_mult_right (poly_lc b) r p          (* p | (poly_lc b * r) == bad_int b *)
    end else ()

#push-options "--z3rlimit 60 --ifuel 2"
let good_of_not_bad (p:int{is_prime p}) (b: polynomial int{deg b >= 1})
  : Lemma (requires ~(p `divides` (bad_int b)))
          (ensures is_good_prime p b)
  = let md : nat = deg b in
    let nd : nat = deg b - 1 in
    let rb  = reduce_to_fp p b in
    let rb' = reduce_to_fp p (poly_deriv b) in
    (* (1) p ∤ lc B *)
    not_div_lc p b;
    (* (2) same degree *)
    lc_survives p b;                              (* deg rb == deg b *)
    (* (3) squarefree over 𝔽ₚ *)
    not_div_res p b;
    let r = RES.resultant md nd b (poly_deriv b) in
    phi_c_nonzero_of_not_div p r;                 (* φ_p r ≠ 0 *)
    resultant_reduces p md nd b (poly_deriv b);   (* res(rb, rb') = φ_p r ≠ 0 *)
    reduce_deg_le p (poly_deriv b);               (* deg rb' <= deg (poly_deriv b) *)
    deriv_deg_lt #int b;                          (* deg (poly_deriv b) <= deg b - 1 *)
    res_nonzero_coprime p md nd rb rb';           (* coprime rb rb' *)
    deriv_reduce_commute p b;                     (* rb' = poly_deriv rb *)
    coprime_deriv_transfer p rb rb' (poly_deriv rb)
                                                  (* coprime rb (poly_deriv rb) = square_free rb *)
#pop-options
