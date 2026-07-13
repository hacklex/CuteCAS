(* ================================================================ *)
(*  Core.Factor.ZassCompleteMod                                      *)
(*                                                                   *)
(*  Modular-reduction discharge lemmas for Zassenhaus completeness:  *)
(*  the mod-p / Hensel-input hypotheses of                           *)
(*    Core.Modular.FpZmodBridge.recombination_complete_fp   and      *)
(*    Core.Factor.HenselCompute.hensel_lift_multi_compute_correct.   *)
(*                                                                   *)
(*  The concrete Berlekamp output  berlekamp_factor p fbar  is a     *)
(*  list of Euclidean gcds — NOT monic-normalised.  Hence the        *)
(*  strongest true forms use the monic normalisation                 *)
(*    bfm p fbar = L.map make_monic (berlekamp_factor p fbar).       *)
(*                                                                   *)
(*  NO admit / assume / sorry.  Lemma / ghost / Tot only.            *)
(* ================================================================ *)

module Core.Factor.ZassCompleteMod

module L   = FStar.List.Tot
module H   = Core.Algebra.Helpers
module IR  = Core.Polynomial.Irreducible
module SP  = Core.Polynomial.SubsetProd
module PR  = Core.Polynomial.Roots
module SF  = Core.Polynomial.SquareFree
module EU  = Core.NumberTheory
module BF  = Core.Factor.BerlekampFactor
module BL  = Core.Factor.BerlekampLoop
module BC6 = Core.Factor.BerlekampComplete6
module BCM = Core.Modular.PrimeField.BerlekampComplete
module BD  = Core.Modular.PrimeField.BerlekampDim
module CP  = Core.Modular.ResidueRing.CenteredPoly
module IRd = Core.Modular.ResidueRing.IntReduce
module HL  = Core.Modular.ResidueRing.Hensel.Lift
module HR  = Core.Modular.ResidueRing.Hensel.Reduce
module CT  = Core.Modular.ResidueRing.Centered
module ML  = FStar.Math.Lemmas
module PS  = Core.Factor.PrimeSelect
module PF  = Core.Polynomial.PartialFraction
module HM  = Core.Modular.ResidueRing.Hensel.Multi
module Z   = Core.Factor.Zassenhaus

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Int
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Monic
open Core.Polynomial.GCD
open Core.Modular.ResidueRing
open Core.Modular.PrimeField
open Core.Modular.FpZmodBridge

#set-options "--fuel 2 --ifuel 1 --z3rlimit 20"

(* ---------------------------------------------------------------- *)
(*  Monic-normalised Berlekamp output.                              *)
(* ---------------------------------------------------------------- *)

let bfm (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  : list (polynomial (fp p))
  = L.map make_monic (BF.berlekamp_factor p fbar)

(* ================================================================ *)
(*  1.  berlekamp_monic — all_monic (bfm p fbar).                    *)
(* ================================================================ *)

let berlekamp_monic (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  : Lemma (SP.all_monic (bfm p fbar))
  = let bf = BF.berlekamp_factor p fbar in
    let gs = bfm p fbar in
    let pmon (h: polynomial (fp p){L.memP h gs}) : Lemma (monic h)
      = L.memP_map_elim make_monic h bf;
        eliminate exists (x: polynomial (fp p)). L.memP x bf /\ make_monic x == h
        returns monic h
        with _. (BF.berlekamp_factor_sound p fbar x; make_monic_monic x) in
    SP.all_monic_intro gs pmon

(* ================================================================ *)
(*  2.  berlekamp_coprime — pairwise_coprime (bfm p fbar).           *)
(* ================================================================ *)

#push-options "--z3rlimit 40"
let berlekamp_coprime (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  : Lemma (requires SF.square_free fbar)
          (ensures  IR.pairwise_coprime (bfm p fbar))
  = let bf = BF.berlekamp_factor p fbar in
    let gs = bfm p fbar in
    L.map_lemma make_monic bf;                          (* L.length gs == L.length bf *)
    BL.berlekamp_factor_pairwise_coprime p fbar;        (* pairwise_coprime bf *)
    IR.pairwise_coprime_elim bf;
    let ppc (i:nat{i < L.length gs}) (j:nat{j < L.length gs /\ j <> i})
      : Lemma (coprime #(fp p) (L.index gs i) (L.index gs j))
      = BD.index_map make_monic bf i;                   (* gs.[i] = make_monic bf.[i] *)
        BD.index_map make_monic bf j;
        L.lemma_index_memP bf i; L.lemma_index_memP bf j;
        BF.berlekamp_factor_sound p fbar (L.index bf i);  (* deg bf.[i] >= 1 *)
        BF.berlekamp_factor_sound p fbar (L.index bf j);
        BCM.coprime_make_monic (L.index bf i) (L.index bf j) in
    IR.pairwise_coprime_intro gs ppc
#pop-options

(* ================================================================ *)
(*  Generic helper: two monic mutual-divisors are equal.            *)
(* ================================================================ *)

#push-options "--z3rlimit 40"
let monic_assoc_equal (#t:Type) {| f: field t |} (a b: polynomial t)
  : Lemma (requires monic a /\ monic b /\
                    divides #(polynomial t) a b /\ divides #(polynomial t) b a)
          (ensures a = b)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    IR.divides_degree_le a b;           (* deg a <= deg b *)
    IR.divides_degree_le b a;           (* deg b <= deg a  ⟹ deg a == deg b *)
    IR.divides_same_degree b a;         (* exists c. a = b*c /\ deg c == 0 *)
    eliminate exists (c: polynomial t). (a = (b * c)) /\ deg c == 0
    returns a = b
    with _.
    begin
      degree_zero_is_singleton c;       (* c == [poly_lc c], poly_lc c <> zero *)
      let cc : t = poly_lc c in
      monomial_zero_n_reveal cc;        (* monomial cc 0 == [cc]  (cc <> zero) *)
      assert (poly_const cc == c);      (* poly_const cc = monomial cc 0 = [cc] = c *)
      mul_commutativity b c;            (* b*c = c*b *)
      poly_eq_transitivity a (b * c) (c * b);  (* a = c*b *)
      (* c == poly_const cc structurally ⟹ c*b == poly_const cc * b *)
      poly_eq_transitivity a (c * b) (poly_const cc * b);
      monic_assoc_eq a b cc             (* monic a, monic b, cc<>zero, a = poly_const cc * b ⟹ a = b *)
    end
#pop-options

(* ================================================================ *)
(*  3.  berlekamp_prod_eq — poly_prod (bfm p fbar) = fbar.           *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let berlekamp_prod_eq (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  : Lemma (requires SF.square_free fbar /\ monic fbar)
          (ensures  PR.poly_prod (bfm p fbar) = fbar)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    H.trans_for_calc (polynomial (fp p)) ();
    let bf = BF.berlekamp_factor p fbar in
    let gs = bfm p fbar in
    BL.berlekamp_factor_product p fbar;   (* divides (poly_prod bf) fbar /\ divides fbar (poly_prod bf) *)
    (* Cons? bf : else poly_prod bf = poly_one, fbar | poly_one ⟹ deg fbar <= 0 *)
    (if Nil? bf then begin
        assert (PR.poly_prod bf == poly_one #(fp p));
        IR.divides_degree_le fbar (poly_one #(fp p))
     end else ());
    (* per-factor degree >= 0 for prod_map_make_monic *)
    let hdeg (k:nat{k < L.length bf}) : Lemma (deg (L.index bf k) >= 0)
      = L.lemma_index_memP bf k;
        BF.berlekamp_factor_sound p fbar (L.index bf k) in
    prod_map_make_monic bf hdeg;          (* monic (poly_prod gs) /\ exists u. poly_prod gs = poly_const u * poly_prod bf *)
    eliminate exists (u: fp p). not (u = (zero <: fp p)) /\
                (PR.poly_prod gs = (poly_const u * PR.poly_prod bf))
    returns PR.poly_prod gs = fbar
    with _.
    begin
      (* poly_prod gs ~ poly_prod bf  (associate via nonzero constant u) *)
      poly_const_deg u;                   (* deg (poly_const u) == 0 *)
      BF.deg0_mul_associate (poly_const u) (PR.poly_prod bf);  (* poly_const u * pbf ~ pbf both directions *)
      poly_eq_symmetry (PR.poly_prod gs) (poly_const u * PR.poly_prod bf);  (* (const u * pbf) = poly_prod gs *)
      divides_congruence_left  #(polynomial (fp p)) (poly_const u * PR.poly_prod bf) (PR.poly_prod gs) (PR.poly_prod bf);
      divides_congruence_right #(polynomial (fp p)) (PR.poly_prod bf) (poly_const u * PR.poly_prod bf) (PR.poly_prod gs);
      (* chain to fbar: poly_prod gs | poly_prod bf | fbar and reverse *)
      divides_trans #(polynomial (fp p)) (PR.poly_prod gs) (PR.poly_prod bf) fbar;
      divides_trans #(polynomial (fp p)) fbar (PR.poly_prod bf) (PR.poly_prod gs);
      monic_assoc_equal (PR.poly_prod gs) fbar
    end
#pop-options

(* ================================================================ *)
(*  Reduction homomorphism infrastructure (ℤ → ℤ/pᵏ → ℤ/p → 𝔽ₚ).    *)
(* ================================================================ *)

(* scalar reduce-commute:  (a mod pᵏ) mod p  ==  a mod p  in zmod p. *)
let to_base_to_fp_scalar (p:int{p > 1}) (k:pos) (a:int)
  : Lemma (HL.to_base p k (CT.to_fp (HR.ppow p k) a) == CT.to_fp p a)
  = let bigP = HR.ppow p k in
    HR.ppow_gt_one p k;
    HL.ppow_pred p k;
    let q = HR.ppow p (k - 1) in
    ML.lemma_mod_lt a bigP;
    ML.lemma_mod_plus (a % bigP) 1 bigP;
    ML.lemma_mod_twice a bigP;
    ML.lemma_mod_lt a p;
    ML.lemma_mod_plus (a % p) 1 p;
    ML.lemma_mod_twice a p;
    ML.modulo_modulo_lemma a p q

(* poly-level reduce-commute:  poly_to_base∘poly_to_fp(pᵏ) = poly_to_fp(p). *)
let poly_to_base_to_fp (p:int{p > 1}) (k:pos) (b: polynomial int #int_cr)
  : Lemma (HL.poly_to_base p k (CP.poly_to_fp (HR.ppow p k) b) = CP.poly_to_fp p b)
  = let bigP = HR.ppow p k in
    HR.ppow_gt_one p k;
    H.elim_equatable_laws (zmod p) ();
    let lhs = HL.poly_to_base p k (CP.poly_to_fp bigP b) in
    let rhs = CP.poly_to_fp p b in
    let h (j:nat) : Lemma (coeff lhs j = coeff rhs j)
      = HL.poly_to_base_coeff p k (CP.poly_to_fp bigP b) j;
        CP.poly_to_fp_coeff bigP b j;
        CP.poly_to_fp_coeff p b j;
        to_base_to_fp_scalar p k (coeff #int #int_cr b j)
    in
    poly_eq_by_coeff lhs rhs h

(* poly_zf is multiplicative (derived from poly_fz_mul via round-trips). *)
let poly_zf_mul (#p:int{EU.is_prime p}) (a b: polynomial (zmod p))
  : Lemma (poly_zf (a * b) = (poly_zf a * poly_zf b))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    H.elim_equatable_laws (polynomial (zmod p)) ();
    let x = poly_zf a in
    let y = poly_zf b in
    poly_fz_zf a;
    poly_fz_zf b;
    poly_fz_mul x y;
    mul_congruence (poly_fz x) (poly_fz y) a b;
    poly_eq_transitivity (poly_fz (x * y)) (poly_fz x * poly_fz y) (a * b);
    poly_eq_symmetry (poly_fz (x * y)) (a * b);
    poly_zf_congr (a * b) (poly_fz (x * y));
    poly_zf_fz (x * y);
    poly_eq_transitivity (poly_zf (a * b)) (poly_zf (poly_fz (x * y))) (x * y)

(* reduce_to_fp is multiplicative. *)
let reduce_to_fp_mul (p:int{EU.is_prime p}) (g w: polynomial int)
  : Lemma (PS.reduce_to_fp p (g * w) = (PS.reduce_to_fp p g * PS.reduce_to_fp p w))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    IRd.poly_to_fp_mul p g w;
    poly_zf_congr (CP.poly_to_fp p (g * w)) (CP.poly_to_fp p g * CP.poly_to_fp p w);
    poly_zf_mul (CP.poly_to_fp p g) (CP.poly_to_fp p w);
    poly_eq_transitivity (PS.reduce_to_fp p (g * w))
                         (poly_zf (CP.poly_to_fp p g * CP.poly_to_fp p w))
                         (PS.reduce_to_fp p g * PS.reduce_to_fp p w)

(* reduce_to_fp respects poly_eq. *)
let reduce_to_fp_congr (p:int{EU.is_prime p}) (a b: polynomial int)
  : Lemma (requires a = b) (ensures PS.reduce_to_fp p a = PS.reduce_to_fp p b)
  = IRd.poly_to_fp_congr p a b;
    poly_zf_congr (CP.poly_to_fp p a) (CP.poly_to_fp p b)

(* reduce_to_fp preserves divisibility. *)
let reduce_to_fp_divides (p:int{EU.is_prime p}) (g b: polynomial int)
  : Lemma (requires divides g b)
          (ensures  divides (PS.reduce_to_fp p g) (PS.reduce_to_fp p b))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    eliminate exists (w: polynomial int). b = (g * w)
    returns divides (PS.reduce_to_fp p g) (PS.reduce_to_fp p b)
    with _.
    begin
      reduce_to_fp_mul p g w;
      reduce_to_fp_congr p b (g * w);
      poly_eq_transitivity (PS.reduce_to_fp p b) (PS.reduce_to_fp p (g * w))
                           (PS.reduce_to_fp p g * PS.reduce_to_fp p w);
      divides_intro (PS.reduce_to_fp p g) (PS.reduce_to_fp p b) (PS.reduce_to_fp p w)
    end

(* reduce through the pᵏ tower to fp lands exactly at reduce_to_fp. *)
let reduce_via_tower (p:int{EU.is_prime p}) (k:pos) (b: polynomial int)
  : Lemma (poly_zf (HL.poly_to_base p k (CP.poly_to_fp (HR.ppow p k) b)) = PS.reduce_to_fp p b)
  = poly_to_base_to_fp p k b;
    poly_zf_congr (HL.poly_to_base p k (CP.poly_to_fp (HR.ppow p k) b)) (CP.poly_to_fp p b)

(* ================================================================ *)
(*  bbar and ∏(bfm p bbar) are associates (no monic needed).        *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let bbar_prod_bfm_assoc (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  : Lemma (divides #(polynomial (fp p)) fbar (PR.poly_prod (bfm p fbar)) /\
           divides #(polynomial (fp p)) (PR.poly_prod (bfm p fbar)) fbar)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    H.trans_for_calc (polynomial (fp p)) ();
    let bf = BF.berlekamp_factor p fbar in
    let gs = bfm p fbar in
    BL.berlekamp_factor_product p fbar;   (* divides (poly_prod bf) fbar /\ divides fbar (poly_prod bf) *)
    (if Nil? bf then begin
        assert (PR.poly_prod bf == poly_one #(fp p));
        IR.divides_degree_le fbar (poly_one #(fp p))
     end else ());
    let hdeg (kk:nat{kk < L.length bf}) : Lemma (deg (L.index bf kk) >= 0)
      = L.lemma_index_memP bf kk;
        BF.berlekamp_factor_sound p fbar (L.index bf kk) in
    prod_map_make_monic bf hdeg;
    eliminate exists (u: fp p). not (u = (zero <: fp p)) /\
                (PR.poly_prod gs = (poly_const u * PR.poly_prod bf))
    returns (divides #(polynomial (fp p)) fbar (PR.poly_prod gs) /\
             divides #(polynomial (fp p)) (PR.poly_prod gs) fbar)
    with _.
    begin
      poly_const_deg u;
      BF.deg0_mul_associate (poly_const u) (PR.poly_prod bf);
      poly_eq_symmetry (PR.poly_prod gs) (poly_const u * PR.poly_prod bf);
      divides_congruence_left  #(polynomial (fp p)) (poly_const u * PR.poly_prod bf) (PR.poly_prod gs) (PR.poly_prod bf);
      divides_congruence_right #(polynomial (fp p)) (PR.poly_prod bf) (poly_const u * PR.poly_prod bf) (PR.poly_prod gs);
      divides_trans #(polynomial (fp p)) fbar (PR.poly_prod bf) (PR.poly_prod gs);
      divides_trans #(polynomial (fp p)) (PR.poly_prod gs) (PR.poly_prod bf) fbar
    end
#pop-options

(* ================================================================ *)
(*  4.  true_factor_divides_prod.                                    *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let true_factor_divides_prod (p:int{EU.is_prime p}) (n:nat) (b g: polynomial int)
  : Lemma (requires monic #int g /\ divides g b /\ PS.is_good_prime p b /\ deg b >= 1)
          (ensures  divides
                      (poly_zf (HL.poly_to_base p (n ++ 1) (CP.poly_to_fp (HR.ppow p (n ++ 1)) g)))
                      (PR.poly_prod (bfm p (PS.reduce_to_fp p b))))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let bbar = PS.reduce_to_fp p b in
    let gbar = PS.reduce_to_fp p g in
    let reduced_g = poly_zf (HL.poly_to_base p (n ++ 1) (CP.poly_to_fp (HR.ppow p (n ++ 1)) g)) in
    PS.good_prime_sound p b;                 (* deg bbar == deg b, square_free bbar *)
    reduce_via_tower p (n ++ 1) g;           (* reduced_g = gbar *)
    reduce_to_fp_divides p g b;              (* divides gbar bbar *)
    bbar_prod_bfm_assoc p bbar;              (* divides bbar (poly_prod (bfm p bbar)) *)
    divides_trans #(polynomial (fp p)) gbar bbar (PR.poly_prod (bfm p bbar));  (* gbar | poly_prod bfm *)
    poly_eq_symmetry reduced_g gbar;         (* gbar = reduced_g *)
    divides_congruence_left #(polynomial (fp p)) gbar reduced_g (PR.poly_prod (bfm p bbar))
#pop-options

(* ================================================================ *)
(*  5.  hensel_input_eq.                                             *)
(*                                                                   *)
(*  STRONGEST TRUE form.  The literal deliverable (RAW berlekamp     *)
(*  factors, non-monic) is FALSE: poly_prod (berlekamp_factor …) is  *)
(*  only an ASSOCIATE of B̄, so equality fails unless B̄ is monic.    *)
(*  Hence: (a) use the monic-normalised factor list bfm, and         *)
(*  (b) add the explicit hypothesis  monic (reduce_to_fp p b).       *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let hensel_input_eq (p:int{EU.is_prime p}) (n:nat) (b: polynomial int)
  : Lemma (requires PS.is_good_prime p b /\ deg b >= 1 /\ monic (PS.reduce_to_fp p b))
          (ensures  HL.poly_to_base p (n ++ 1) (CP.poly_to_fp (HR.ppow p (n ++ 1)) b)
                    = PR.poly_prod (L.map (poly_fz #p) (bfm p (PS.reduce_to_fp p b))))
  = H.elim_equatable_laws (polynomial (zmod p)) ();
    H.trans_for_calc (polynomial (zmod p)) ();
    let bbar = PS.reduce_to_fp p b in
    PS.good_prime_sound p b;                            (* deg bbar == deg b, square_free bbar *)
    let aa = HL.poly_to_base p (n ++ 1) (CP.poly_to_fp (HR.ppow p (n ++ 1)) b) in
    let bb = CP.poly_to_fp p b in
    let cc = poly_fz bbar in
    let dd = poly_fz (PR.poly_prod (bfm p bbar)) in
    let ee = PR.poly_prod (L.map (poly_fz #p) (bfm p bbar)) in
    poly_to_base_to_fp p (n ++ 1) b;                    (* aa = bb *)
    berlekamp_prod_eq p bbar;                           (* poly_prod (bfm p bbar) = bbar *)
    poly_fz_poly_prod (bfm p bbar);                     (* dd = ee *)
    poly_fz_congr (PR.poly_prod (bfm p bbar)) bbar;     (* dd = cc *)
    poly_fz_zf (CP.poly_to_fp p b);                     (* cc = bb  (bbar = poly_zf (poly_to_fp p b)) *)
    poly_eq_symmetry cc bb;                             (* bb = cc *)
    poly_eq_symmetry dd cc;                             (* cc = dd *)
    poly_eq_transitivity aa bb cc;                      (* aa = cc *)
    poly_eq_transitivity aa cc dd;                      (* aa = dd *)
    poly_eq_transitivity aa dd ee                       (* aa = ee *)
#pop-options

(* ================================================================ *)
(*  6.  bezout_chain_of_coprime.                                     *)
(* ================================================================ *)

(* coprime to a list product from pairwise coprimality with each factor. *)
let rec coprime_poly_prod (#t:Type) {| f: field t |}
  (a: polynomial t) (ds: list (polynomial t))
  : Lemma (requires deg a >= 0 /\
                    (forall (k:nat). k < L.length ds ==> coprime a (L.index ds k)))
          (ensures  coprime a (PR.poly_prod ds))
          (decreases ds)
  = H.elim_equatable_laws (polynomial t) ();
    match ds with
    | [] ->
        coprime_reveal a (poly_one #t);
        SF.gcd_has_degree a (poly_one #t);
        gcd_divides_right a (poly_one #t);
        IR.divides_degree_le (poly_gcd a (poly_one #t)) (poly_one #t)
    | d :: rest ->
        assert (coprime a d);
        assert (forall (k:nat). k < L.length rest ==>
                  L.index (d :: rest) (k ++ 1) == L.index rest k);
        coprime_poly_prod a rest;
        IR.coprime_mul_right a d (PR.poly_prod rest)

(* pairwise_coprime is inherited by the tail. *)
let pairwise_coprime_tail (#t:Type) {| f: field t |}
  (h: polynomial t) (tail: list (polynomial t))
  : Lemma (requires IR.pairwise_coprime (h :: tail))
          (ensures  IR.pairwise_coprime tail)
  = IR.pairwise_coprime_elim (h :: tail);
    let proof (i:nat{i < L.length tail}) (j:nat{j < L.length tail /\ j <> i})
      : Lemma (coprime (L.index tail i) (L.index tail j))
      = assert (L.index tail i == L.index (h :: tail) (i ++ 1));
        assert (L.index tail j == L.index (h :: tail) (j ++ 1)) in
    IR.pairwise_coprime_intro tail proof

#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec bezout_chain_of_coprime (p:int{EU.is_prime p}) (fps: list (polynomial (fp p)))
  : Lemma (requires SP.all_irreducible fps /\ SP.all_monic fps /\ IR.pairwise_coprime fps)
          (ensures  HM.bezout_chain p (L.map (poly_fz #p) fps) (Z.compute_bez p fps))
          (decreases fps)
  = H.elim_equatable_laws (polynomial (zmod p)) ();
    H.trans_for_calc (polynomial (zmod p)) ();
    match fps with
    | []  -> ()
    | [_] -> ()
    | h :: tail ->
        let pt = PR.poly_prod tail in
        SP.all_irreducible_elim fps;
        L.lemma_index_memP fps 0;
        assert (L.index fps 0 == h);
        assert (IR.poly_irreducible h);
        IR.pairwise_coprime_elim fps;
        let hcop (k:nat) : Lemma (k < L.length tail ==> coprime h (L.index tail k))
          = if k < L.length tail then begin
              assert (L.index tail k == L.index fps (k ++ 1));
              assert (coprime (L.index fps 0) (L.index fps (k ++ 1)))
            end else () in
        Classical.forall_intro hcop;
        coprime_poly_prod h tail;
        let bl = PF.bezout_left  h pt in
        let br = PF.bezout_right h pt in
        let s' = poly_fz #p bl in
        let t' = poly_fz #p br in
        PF.bezout_identity h pt;
        poly_fz_congr ((bl * h) + (br * pt)) (poly_one #(fp p));
        poly_fz_one #p;
        poly_eq_transitivity (poly_fz ((bl * h) + (br * pt)))
                             (poly_fz (poly_one #(fp p))) (poly_one #(zmod p));
        poly_fz_add (bl * h) (br * pt);
        poly_fz_mul bl h;
        poly_fz_mul br pt;
        poly_fz_poly_prod tail;
        let ph  = poly_fz #p h in
        let ppt = poly_fz #p pt in
        let mtail = PR.poly_prod (L.map (poly_fz #p) tail) in
        add_congruence (poly_fz (bl * h)) (poly_fz (br * pt)) (s' * ph) (t' * ppt);
        mul_congruence t' ppt t' mtail;
        add_congruence (s' * ph) (t' * ppt) (s' * ph) (t' * mtail);
        poly_eq_transitivity (poly_fz ((bl * h) + (br * pt)))
                             (poly_fz (bl * h) + poly_fz (br * pt)) ((s' * ph) + (t' * ppt));
        poly_eq_transitivity (poly_fz ((bl * h) + (br * pt)))
                             ((s' * ph) + (t' * ppt)) ((s' * ph) + (t' * mtail));
        poly_eq_symmetry (poly_fz ((bl * h) + (br * pt))) ((s' * ph) + (t' * mtail));
        poly_eq_transitivity ((s' * ph) + (t' * mtail))
                             (poly_fz ((bl * h) + (br * pt))) (poly_one #(zmod p));
        SP.all_irreducible_tail h tail;
        SP.all_monic_tail h tail;
        pairwise_coprime_tail h tail;
        bezout_chain_of_coprime p tail
#pop-options
