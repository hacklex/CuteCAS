module Core.Factor.BerlekampComplete6

(* ================================================================ *)
(*  B.4 CRT lift + discharge of kernel_span_cover_t, making          *)
(*  berlekamp_factor_all_irreducible UNCONDITIONAL, and B.5.         *)
(*  Fast rebuild of the discharge; representation lives in           *)
(*  Core.Factor.BerlekampRepr.  NO admit / assume / sorry.          *)
(* ================================================================ *)

module L   = FStar.List.Tot
module NS  = Core.LinearAlgebra.FpNullSpace
module BF  = Core.Factor.BerlekampFactor
module FM  = Core.Factor.FrobeniusMatrix
module CM  = Core.Algebra.CongruenceMod
module IR  = Core.Polynomial.Irreducible
module H   = Core.Algebra.Helpers
module EU  = Core.NumberTheory
module BK  = Core.Modular.PrimeField.Berlekamp
module BRR = Core.Factor.BerlekampReachesR
module SF  = Core.Polynomial.SquareFree
module SP  = Core.Polynomial.SubsetProd
module CRT = Core.Polynomial.CRTMulti
module GC  = Core.Polynomial.GCD

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Modular.PrimeField
open Core.Tactics.CanonRing
open Core.Factor.BerlekampRepr
open Core.Factor.BerlekampReprSpan

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* cong is preserved by taking powers. *)
let rec cong_pow (p:int{EU.is_prime p}) (m a b: polynomial (fp p)) (k:nat)
  : Lemma (requires CM.cong #(polynomial (fp p)) m a b)
          (ensures  CM.cong #(polynomial (fp p)) m (poly_power a k) (poly_power b k))
          (decreases k)
  = if k = 0 then CM.cong_refl #(polynomial (fp p)) m (poly_power a 0)
    else begin
      cong_pow p m a b (k - 1);
      CM.cong_mul #(polynomial (fp p)) m a b (poly_power a (k - 1)) (poly_power b (k - 1))
    end

(* d | a  ==>  d | a^k   (k >= 1). *)
let divides_power (p:int{EU.is_prime p}) (d a: polynomial (fp p)) (k:nat)
  : Lemma (requires divides #(polynomial (fp p)) d a /\ k >= 1)
          (ensures  divides #(polynomial (fp p)) d (poly_power a k))
  = divides_mul_right #(polynomial (fp p)) d a (poly_power a (k - 1))

(* cof | w  ==>  cong cof (w^p) w. *)
let cong_of_divides (p:int{EU.is_prime p}) (cof w: polynomial (fp p))
  : Lemma (requires divides #(polynomial (fp p)) cof w)
          (ensures  CM.cong #(polynomial (fp p)) cof (poly_power #(fp p) w (p <: nat)) w)
  = divides_power p cof w (p <: nat);                        (* cof | w^p *)
    divides_sub #(polynomial (fp p)) cof (poly_power #(fp p) w (p <: nat)) w;
    CM.cong_reveal #(polynomial (fp p)) cof (poly_power #(fp p) w (p <: nat)) w


private let test #t {|ring t|} (a b:t) : Lemma (- (a -- b) = b -- a)
  = 
  H.elim_equatable_laws t();
  H.trans_for_calc t();
  H.neg_of_sum a (-b);
  H.neg_neg b;
  add_congruence (-(-b)) (-a) b (-a)

(* - (a -- b) = b -- a , in the polynomial ring (named lemmas; canon_ring is
   notation-blind under open Notation). *)
private
#push-options "--fuel 0 --ifuel 0 --z3rlimit 1"
let neg_sub_eq (#p:int{EU.is_prime p}) (a b: polynomial (fp p))
  : Lemma ((- (a -- b)) = (b -- a))
  = H.neg_of_sum a (- b);
    H.neg_neg b;
    reflexivity (- a);
    add_congruence (- (- b)) (- a) b (- a);
    transitivity (- (a -- b)) ((- (- b)) + (- a)) (b -- a)
#pop-options

(* divides d (wt -- 0)  ==>  divides d wt , isolated at fuel 0. *)
private
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let div_sub_zero (#p:int{EU.is_prime p}) (d wt: polynomial (fp p))
  : Lemma (requires divides #(polynomial (fp p)) d (wt -- (poly_zero #(fp p))))
          (ensures  divides #(polynomial (fp p)) d wt)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    add_sub_cancel #(polynomial (fp p)) (poly_zero #(fp p)) wt;   (* (0+wt) -- 0 = wt *)
    H.zero_plus_x wt;                                             (* 0 + wt = wt *)
    poly_eq_symmetry ((poly_zero #(fp p)) + wt) wt;               (* wt = 0 + wt *)
    poly_eq_reflexivity (poly_zero #(fp p));
    sub_congruence #(polynomial (fp p)) wt (poly_zero #(fp p))
      ((poly_zero #(fp p)) + wt) (poly_zero #(fp p));             (* wt--0 = (0+wt)--0 *)
    poly_eq_transitivity (wt -- (poly_zero #(fp p)))
      (((poly_zero #(fp p)) + wt) -- (poly_zero #(fp p))) wt;     (* wt--0 = wt *)
    divides_congruence_right #(polynomial (fp p)) d (wt -- (poly_zero #(fp p))) wt
#pop-options

(* g, cof are pairwise coprime (both orders) — the CRT modulus hypothesis. *)
private
let crt_pair_coprime (p:int{EU.is_prime p}) (fbar g cof: polynomial (fp p))
  : Lemma (requires SF.square_free fbar /\ deg fbar >= 0 /\ fbar = (g * cof) /\
                    deg g >= 1 /\ deg cof >= 1)
          (ensures  GC.coprime #(fp p) g cof /\ GC.coprime #(fp p) cof g)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    (* (g*cof) | fbar *)
    divides_refl #(polynomial (fp p)) (g * cof);
    poly_eq_symmetry fbar (g * cof);
    divides_congruence_right #(polynomial (fp p)) (g * cof) (g * cof) fbar;
    BRR.coprime_of_split_squarefree p fbar g cof;                              (* coprime g cof *)
    (* (cof*g) | fbar *)
    divides_refl #(polynomial (fp p)) (cof * g);
    mul_commutativity cof g;
    transitivity (cof * g) (g * cof) fbar;
    divides_congruence_right #(polynomial (fp p)) (cof * g) (cof * g) fbar;
    BRR.coprime_of_split_squarefree p fbar cof g                              (* coprime cof g *)

(* the CRT lift of a g-Berlekamp element to an fbar-Berlekamp element. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let crt_lift (p:int{EU.is_prime p}) (fbar g cof w': polynomial (fp p))
  : Lemma (requires SF.square_free fbar /\ deg fbar >= 1 /\ fbar = (g * cof) /\
                    deg g >= 1 /\ deg cof >= 1 /\
                    CM.cong #(polynomial (fp p)) g (poly_power #(fp p) w' (p <: nat)) w')
          (ensures  (exists (wt: polynomial (fp p)).
                       divides #(polynomial (fp p)) g (wt -- w') /\
                       CM.cong #(polynomial (fp p)) fbar (poly_power #(fp p) wt (p <: nat)) wt))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let ms : list (polynomial (fp p)) = [g; cof] in
    let rs : list (polynomial (fp p)) = [w'; poly_zero #(fp p)] in
    let deg_pf (kk:nat{kk < L.length ms}) : Lemma (deg (L.index ms kk) >= 1)
      = assert_norm (L.index [g; cof] 0 == g);
        assert_norm (L.index [g; cof] 1 == cof) in
    let cop_pf (i:nat{i < L.length ms}) (j:nat{j < L.length ms /\ j <> i})
      : Lemma (GC.coprime (L.index ms i) (L.index ms j))
      = crt_pair_coprime p fbar g cof;                       (* coprime g cof /\ coprime cof g *)
        assert_norm (L.index [g; cof] 0 == g);
        assert_norm (L.index [g; cof] 1 == cof) in
    let wt = CRT.crt_multi_witness ms rs cop_pf deg_pf in
    CRT.all_cong_vec_elim ms wt rs;
    assert (divides #(polynomial (fp p)) g (wt -- w'));
    assert (divides #(polynomial (fp p)) cof (wt -- (poly_zero #(fp p))));
    div_sub_zero #p cof wt;                                                       (* cof | wt *)
    (* cong g (wt^p) wt *)
    CM.cong_reveal #(polynomial (fp p)) g wt w';
    cong_pow p g wt w' (p <: nat);
    CM.cong_trans #(polynomial (fp p)) g (poly_power #(fp p) wt (p <: nat))
      (poly_power #(fp p) w' (p <: nat)) w';
    CM.cong_sym #(polynomial (fp p)) g wt w';
    CM.cong_trans #(polynomial (fp p)) g (poly_power #(fp p) wt (p <: nat)) w' wt;
    (* cong cof (wt^p) wt *)
    cong_of_divides p cof wt;
    (* cong fbar (wt^p) wt via coprime product *)
    crt_pair_coprime p fbar g cof;                                 (* coprime g cof *)
    CM.cong_reveal #(polynomial (fp p)) g (poly_power #(fp p) wt (p <: nat)) wt;   (* g | (wt^p -- wt) *)
    CM.cong_reveal #(polynomial (fp p)) cof (poly_power #(fp p) wt (p <: nat)) wt; (* cof | (wt^p -- wt) *)
    IR.coprime_divides_product #(fp p) g cof
      ((poly_power #(fp p) wt (p <: nat)) -- wt);
    poly_eq_symmetry fbar (g * cof);
    divides_congruence_left #(polynomial (fp p)) (g * cof) fbar
      ((poly_power #(fp p) wt (p <: nat)) -- wt);
    CM.cong_reveal #(polynomial (fp p)) fbar (poly_power #(fp p) wt (p <: nat)) wt;
    introduce exists (wtt: polynomial (fp p)).
                divides #(polynomial (fp p)) g (wtt -- w') /\
                CM.cong #(polynomial (fp p)) fbar (poly_power #(fp p) wtt (p <: nat)) wtt
    with wt and ()
#pop-options

(* B.4 CRT branch:  deg cof >= 1  (g and cof are a coprime split). *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let crt_branch (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1}) (g cof w w': polynomial (fp p))
  : Lemma (requires SF.square_free fbar /\ fbar = (g * cof) /\
                    deg g >= 1 /\ deg cof >= 1 /\
                    divides #(polynomial (fp p)) g (w -- w') /\
                    CM.cong #(polynomial (fp p)) g (poly_power #(fp p) w' (p <: nat)) w' /\
                    (forall (hh: polynomial (fp p)).
                       L.memP hh (BF.berlekamp_kernel p fbar) ==>
                       BK.kernel_is_const_shifted p g hh))
          (ensures  BK.kernel_is_const_shifted p g w)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    crt_lift p fbar g cof w';
    eliminate exists (wt: polynomial (fp p)).
                divides #(polynomial (fp p)) g (wt -- w') /\
                CM.cong #(polynomial (fp p)) fbar (poly_power #(fp p) wt (p <: nat)) wt
    returns BK.kernel_is_const_shifted p g w
    with _.
    begin
      let wt2 = poly_rem wt fbar in
      CM.cong_of_divmod #(polynomial (fp p)) wt fbar (fst (poly_divmod #(fp p) wt fbar)) wt2;
      cong_pow p fbar wt wt2 (p <: nat);
      CM.cong_sym #(polynomial (fp p)) fbar (poly_power #(fp p) wt (p <: nat)) (poly_power #(fp p) wt2 (p <: nat));
      CM.cong_trans #(polynomial (fp p)) fbar (poly_power #(fp p) wt2 (p <: nat))
        (poly_power #(fp p) wt (p <: nat)) wt;
      CM.cong_trans #(polynomial (fp p)) fbar (poly_power #(fp p) wt2 (p <: nat)) wt wt2;
      pdeg_eq p fbar;                                    (* deg wt2 < deg fbar = pdeg *)
      span_const_shift p fbar g wt2;                     (* const_shift g wt2 *)
      CM.cong_reveal #(polynomial (fp p)) fbar wt wt2;
      divides_trans #(polynomial (fp p)) g fbar (wt -- wt2);
      const_shift_cong p g wt wt2;                       (* const_shift g wt *)
      divides_neg #(polynomial (fp p)) g (wt -- w');
      neg_sub_eq #p wt w';                                (* -(wt -- w') = w' -- wt *)
      divides_congruence_right #(polynomial (fp p)) g (- (wt -- w')) (w' -- wt);
      divides_add #(polynomial (fp p)) g (w -- w') (w' -- wt);
      sub_chain #(polynomial (fp p)) w w' wt;
      divides_congruence_right #(polynomial (fp p)) g ((w -- w') + (w' -- wt)) (w -- wt);
      const_shift_cong p g w wt
    end
#pop-options

(* B.4 unit branch:  deg cof <= 0  (g is an associate of fbar). *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let unit_branch (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1}) (g cof w w': polynomial (fp p))
  : Lemma (requires fbar = (g * cof) /\ deg g >= 1 /\ deg cof <= 0 /\
                    deg w' < BF.pdeg fbar /\
                    divides #(polynomial (fp p)) g (w -- w') /\
                    CM.cong #(polynomial (fp p)) g (poly_power #(fp p) w' (p <: nat)) w' /\
                    (forall (hh: polynomial (fp p)).
                       L.memP hh (BF.berlekamp_kernel p fbar) ==>
                       BK.kernel_is_const_shifted p g hh))
          (ensures  BK.kernel_is_const_shifted p g w)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    if deg cof < 0 then begin
      Core.Polynomial.Unique.degree_none_poly_eq_zero #(fp p) cof;
      poly_mul_congruence g cof g (poly_zero #(fp p));
      H.x_mul_zero #(polynomial (fp p)) g;
      transitivity fbar (g * cof) (g * (poly_zero #(fp p)));
      transitivity fbar (g * (poly_zero #(fp p))) (poly_zero #(fp p));
      deg_bound_of_coeffs #(fp p) fbar 0
        (fun (i:nat) -> poly_eq_means_equal_coeffs #(fp p) fbar (poly_zero #(fp p)) i)
    end;
    BF.deg0_mul_associate #(fp p) cof g;                 (* divides (cof*g) g *)
    mul_commutativity cof g;
    transitivity (cof * g) (g * cof) fbar;               (* cof*g = fbar *)
    divides_congruence_left #(polynomial (fp p)) (cof * g) fbar g;   (* fbar | g *)
    CM.cong_reveal #(polynomial (fp p)) g (poly_power #(fp p) w' (p <: nat)) w';
    divides_trans #(polynomial (fp p)) fbar g
      ((poly_power #(fp p) w' (p <: nat)) + (- w'));     (* fbar | (w'^p -- w') *)
    CM.cong_reveal #(polynomial (fp p)) fbar (poly_power #(fp p) w' (p <: nat)) w';
    span_const_shift p fbar g w';                        (* const_shift g w' *)
    const_shift_cong p g w w'
#pop-options

(* B.4 — the SPANNING RESIDUAL, discharged.  (uses square_free.) *)
#push-options "--z3rlimit 30 --fuel 2 --ifuel 1"
let kernel_span_cover_discharge (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1}) (g w: polynomial (fp p))
  : Lemma (requires SF.square_free fbar /\
                    L.memP g (BF.berlekamp_factor p fbar) /\
                    (forall (hh: polynomial (fp p)).
                       L.memP hh (BF.berlekamp_kernel p fbar) ==>
                       BK.kernel_is_const_shifted p g hh) /\
                    CM.cong #(polynomial (fp p)) g (poly_power #(fp p) w (p <: nat)) w)
          (ensures  BK.kernel_is_const_shifted p g w)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    BF.berlekamp_factor_sound p fbar g;                      (* deg g >= 1, g | fbar *)
    eliminate exists (cof: polynomial (fp p)). fbar = (g * cof)
    returns BK.kernel_is_const_shifted p g w
    with _.
    begin
      let w' = poly_rem w g in
      CM.cong_of_divmod #(polynomial (fp p)) w g (fst (poly_divmod #(fp p) w g)) w';  (* cong g w w' *)
      cong_pow p g w w' (p <: nat);
      CM.cong_sym #(polynomial (fp p)) g (poly_power #(fp p) w (p <: nat)) (poly_power #(fp p) w' (p <: nat));
      CM.cong_trans #(polynomial (fp p)) g (poly_power #(fp p) w' (p <: nat))
        (poly_power #(fp p) w (p <: nat)) w;
      CM.cong_trans #(polynomial (fp p)) g (poly_power #(fp p) w' (p <: nat)) w w';  (* cong g (w'^p) w' *)
      CM.cong_reveal #(polynomial (fp p)) g w w';           (* g | (w -- w') *)
      IR.divides_degree_le #(fp p) g fbar;                   (* deg g <= deg fbar *)
      pdeg_eq p fbar;                                        (* pdeg fbar = deg fbar, deg w' < deg g <= pdeg *)
      if deg cof >= 1 then crt_branch p fbar g cof w w'
      else unit_branch p fbar g cof w w'
    end
#pop-options

(* B.5 — berlekamp_factor_all_irreducible, UNCONDITIONAL. *)
let berlekamp_factor_all_irreducible (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1})
  : Lemma (requires SF.square_free fbar)
          (ensures  SP.all_irreducible (BF.berlekamp_factor p fbar))
  = let ksc (g w: polynomial (fp p))
      : Lemma (requires L.memP g (BF.berlekamp_factor p fbar) /\
                        (forall (hh: polynomial (fp p)).
                           L.memP hh (BF.berlekamp_kernel p fbar) ==>
                           BK.kernel_is_const_shifted p g hh) /\
                        CM.cong #(polynomial (fp p)) g (poly_power #(fp p) w (p <: nat)) w)
              (ensures  BK.kernel_is_const_shifted p g w)
      = kernel_span_cover_discharge p fbar g w
    in
    BRR.berlekamp_factor_all_irreducible p fbar ksc
