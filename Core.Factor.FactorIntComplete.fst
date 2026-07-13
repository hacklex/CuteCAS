module Core.Factor.FactorIntComplete

(* ================================================================ *)
(*  LITERAL, EXECUTABLE, SOUND + COMPLETE integer factorizer.        *)
(*                                                                   *)
(*  Built on Core.Factor.FactorQComplete.factor_Q_complete (the      *)
(*  candidate-list completeness) plus a DE-MONICIZATION step that     *)
(*  recovers the literal integer factor from a monic candidate:      *)
(*                                                                   *)
(*    demonicize L d = primitive_part (d(L*x))                       *)
(*                                                                   *)
(*  where d(L*x) substitutes x |-> L*x coefficient-wise              *)
(*  (coeff i |-> coeff d i * L^i).  For d ~ monic_factor_of b g this  *)
(*  inverts the monic-ization back to (a sign of) g.                 *)
(*                                                                   *)
(*  Standalone (NOT on build-all).  NO admit / assume / sorry.       *)
(* ================================================================ *)

module L    = FStar.List.Tot
module NMZ  = Core.Factor.NonMonicZass
module ZCplt = Core.Factor.ZassComplete
module PS   = Core.Factor.PrimeSelect
module ZQC  = Core.Factor.FactorQComplete
module R    = Core.Polynomial.Roots
module HT   = Core.Polynomial.Height
module DV   = Core.Algebra.Divisibility
module H    = Core.Algebra.Helpers
module E    = Core.NumberTheory
module SF   = Core.Polynomial.SquareFree
module BIN  = Core.Factor.BadIntNonzero
module GI   = Core.Factor.GaussIrred
module DIV  = Core.Polynomial.Div
module Z    = Core.Factor.Zassenhaus
module RC   = Core.Factor.Recombine
module RCC  = Core.Factor.RecombineComplete
module PE   = Core.Factor.PrimeExists
module EQ   = Core.Polynomial.EmbedQ

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Monic
open Core.Factor.Content
open Core.Factor.Gauss
open Core.Tactics.CanonRing

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ================================================================ *)
(*  1.  The substitution  x |-> l*x  as a coefficient-wise map.      *)
(*      coeff i  |-->  coeff d i * l^i.                               *)
(* ================================================================ *)

let rec subst_aux (b: list int) (l:int) (e:nat) : Tot (list int) (decreases b) =
  match b with
  | []        -> []
  | a :: rest -> (Prims.op_Star a (NMZ.ipow l e)) :: subst_aux rest l (Prims.op_Addition e 1)

let rec subst_aux_length (b: list int) (l:int) (e:nat)
  : Lemma (ensures L.length (subst_aux b l e) == L.length b) (decreases b)
  = match b with | [] -> () | _ :: rest -> subst_aux_length rest l (Prims.op_Addition e 1)

let rec subst_aux_index (b: list int) (l:int) (e:nat) (i:nat)
  : Lemma (requires i < L.length b)
          (ensures  (subst_aux_length b l e;
                     L.index (subst_aux b l e) i
                       == Prims.op_Star (L.index b i) (NMZ.ipow l (Prims.op_Addition e i))))
          (decreases b)
  = subst_aux_length b l e;
    match b with
    | _ :: rest ->
        subst_aux_length rest l (Prims.op_Addition e 1);
        if i = 0 then () else subst_aux_index rest l (Prims.op_Addition e 1) (i - 1)

let subst_cx (l:int) (d: polynomial int) : polynomial int = trim (subst_aux d l 0)

(* clean per-coefficient description valid at EVERY nonnegative index. *)
let subst_cx_coeff (l:int) (d: polynomial int) (i:nat)
  : Lemma (coeff (subst_cx l d) i == Prims.op_Star (coeff d i) (NMZ.ipow l i))
  = subst_aux_length d l 0;
    coeff_trim (subst_aux d l 0) i;                    (* coeff (trim ..) i = index or 0 *)
    if i < L.length d then subst_aux_index d l 0 i     (* index = coeff d i * ipow l i *)
    else ()                                            (* i >= length: coeff d i = 0 *)

(* ================================================================ *)
(*  2.  Elementary scaling / negation algebra (coefficient-wise).    *)
(* ================================================================ *)

(* ipow of a nonzero base is nonzero. *)
let rec ipow_nonzero (l:int) (k:nat)
  : Lemma (requires l <> 0) (ensures NMZ.ipow l k <> 0) (decreases k)
  = if k = 0 then () else ipow_nonzero l (k - 1)

(* poly_scale a (poly_scale b p)  ~  poly_scale (a*b) p. *)
let scale_scale (a b: int) (p: polynomial int)
  : Lemma (poly_eq (R.poly_scale a (R.poly_scale b p)) (R.poly_scale (Prims.op_Star a b) p))
  = let lhs = R.poly_scale a (R.poly_scale b p) in
    let rhs = R.poly_scale (Prims.op_Star a b) p in
    let aux (i:int) : Lemma (coeff lhs i == coeff rhs i) =
      if i < 0 then ()
      else begin
        HT.coeff_scale a (R.poly_scale b p) i;
        HT.coeff_scale b p i;
        HT.coeff_scale (Prims.op_Star a b) p i;
        assert (Prims.op_Star a (Prims.op_Star b (coeff p i))
                == Prims.op_Star (Prims.op_Star a b) (coeff p i))
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* poly_scale 1 p ~ p. *)
let scale_one (p: polynomial int)
  : Lemma (poly_eq (R.poly_scale 1 p) p)
  = let aux (i:int) : Lemma (coeff (R.poly_scale 1 p) i == coeff p i) =
      if i < 0 then () else HT.coeff_scale 1 p i
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (R.poly_scale 1 p) p

(* poly_neg p ~ poly_scale (-1) p. *)
let neg_is_scale (p: polynomial int)
  : Lemma (poly_eq (poly_neg p) (R.poly_scale (-1) p))
  = let aux (i:int) : Lemma (coeff (poly_neg p) i == coeff (R.poly_scale (-1) p) i) =
      if i < 0 then ()
      else begin
        poly_neg_coeff p i;
        HT.coeff_scale (-1) p i
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_neg p) (R.poly_scale (-1) p)

(* subst_cx commutes with constant scaling. *)
let subst_cx_scale (l c: int) (p: polynomial int)
  : Lemma (poly_eq (subst_cx l (R.poly_scale c p)) (R.poly_scale c (subst_cx l p)))
  = let lhs = subst_cx l (R.poly_scale c p) in
    let rhs = R.poly_scale c (subst_cx l p) in
    let aux (i:int) : Lemma (coeff lhs i == coeff rhs i) =
      if i < 0 then ()
      else begin
        subst_cx_coeff l (R.poly_scale c p) i;
        HT.coeff_scale c p i;
        subst_cx_coeff l p i;
        HT.coeff_scale c (subst_cx l p) i;
        assert (Prims.op_Star c (Prims.op_Star (coeff p i) (NMZ.ipow l i))
                == Prims.op_Star (Prims.op_Star c (coeff p i)) (NMZ.ipow l i))
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* ================================================================ *)
(*  3.  The primitive-part descent (isolated algebra).               *)
(*                                                                   *)
(*  Given the two scaling identities                                 *)
(*     poly_scale c  ee  =  poly_scale k  g       (inversion)        *)
(*     poly_scale sg ee  =  poly_scale cw ppW     (content split)    *)
(*  with c,k,cw <> 0 and sg = +/-1, ppW and g primitive, conclude    *)
(*  ppW ~ +/- g.  This is the Gauss descent that strips the stray    *)
(*  constants introduced by the substitution and the content.        *)
(* ================================================================ *)

(* subst_cx commutes with negation. *)
let subst_cx_neg (l: int) (p: polynomial int)
  : Lemma (poly_eq (subst_cx l (poly_neg p)) (poly_neg (subst_cx l p)))
  = let lhs = subst_cx l (poly_neg p) in
    let rhs = poly_neg (subst_cx l p) in
    let aux (i:int) : Lemma (coeff lhs i == coeff rhs i) =
      if i < 0 then ()
      else begin
        subst_cx_coeff l (poly_neg p) i;
        poly_neg_coeff p i;
        subst_cx_coeff l p i;
        poly_neg_coeff (subst_cx l p) i
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* product of nonzero integers is nonzero. *)
let int_mul_nonzero (a b: int)
  : Lemma (requires a <> 0 /\ b <> 0) (ensures Prims.op_Star a b <> 0)
  = ()

(* CRUX INVERSION IDENTITY:
     subst_cx l (scaleL g l)  ~  poly_scale (l^(deg g)) g.
   Substituting x |-> l*x into the uniform l-scaling of g recovers g
   scaled by the constant l^(deg g). *)
#push-options "--z3rlimit 20"
let subst_scaleL_identity (g: polynomial int) (l:int)
  : Lemma (requires deg g >= 0)
          (ensures poly_eq (subst_cx l (NMZ.scaleL g l))
                           (R.poly_scale (NMZ.ipow l (deg g)) g))
  = let n = deg g in
    NMZ.scaleL_length g l;                              (* deg (scaleL g l) == n *)
    let sg = NMZ.scaleL g l in
    let k  = NMZ.ipow l n in
    let lhs = subst_cx l sg in
    let rhs = R.poly_scale k g in
    let aux (i:int) : Lemma (coeff lhs i == coeff rhs i) =
      if i < 0 then ()
      else begin
        subst_cx_coeff l sg i;                          (* coeff lhs i = coeff sg i * l^i *)
        NMZ.scaleL_coeff g l i;                         (* coeff sg i = coeff g i * l^(n-i) (in range) *)
        HT.coeff_scale k g i;                           (* coeff rhs i = k * coeff g i *)
        if 0 <= i && i <= n then begin
          NMZ.ipow_add l (n - i) i;                     (* l^(n-i) * l^i = l^n *)
          assert (Prims.op_Star (Prims.op_Star (coeff g i) (NMZ.ipow l (n - i)))
                                (NMZ.ipow l i)
                  == Prims.op_Star k (coeff g i))
        end
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs
#pop-options

(* the isolated descent lemma. *)
let scale_recover (ee g ppW: polynomial int) (c k cw sg: int)
  : Lemma (requires is_primitive ppW /\ is_primitive g /\
                    c <> 0 /\ k <> 0 /\ cw <> 0 /\ (sg == 1 \/ sg == -1) /\
                    R.poly_scale c ee == R.poly_scale k g /\
                    R.poly_scale sg ee == R.poly_scale cw ppW)
          (ensures poly_eq ppW g \/ poly_eq ppW (poly_neg g))
  = H.elim_equatable_laws (polynomial int) ();
    let nn = Prims.op_Star c cw in
    let mm = Prims.op_Star sg k in
    scale_scale c cw ppW;
    GI.poly_eq_int_eq (R.poly_scale c (R.poly_scale cw ppW)) (R.poly_scale nn ppW);
    scale_scale c sg ee;
    GI.poly_eq_int_eq (R.poly_scale c (R.poly_scale sg ee)) (R.poly_scale (Prims.op_Star c sg) ee);
    scale_scale sg c ee;
    GI.poly_eq_int_eq (R.poly_scale sg (R.poly_scale c ee)) (R.poly_scale (Prims.op_Star sg c) ee);
    scale_scale sg k g;
    GI.poly_eq_int_eq (R.poly_scale sg (R.poly_scale k g)) (R.poly_scale mm g);
    (* nn <> 0 and mm <> 0 *)
    int_mul_nonzero c cw;
    (if sg = 1 then assert (mm == k) else assert (mm == Prims.op_Star (-1) k));
    assert (mm <> 0);
    (* the two scale-forms coincide, so primitivity descent applies. *)
    assert (R.poly_scale nn ppW == R.poly_scale mm g);
    poly_eq_reflexivity (R.poly_scale nn ppW);
    GI.primitive_qq_associate_implies_int_associate ppW g nn mm

(* ================================================================ *)
(*  4.  DE-MONICIZATION and the recovery theorem.                    *)
(* ================================================================ *)

let demonicize (l:int) (d: polynomial int) : polynomial int =
  primitive_part (subst_cx l d)

(*  CRUX RECOVERY:  for a primitive integer factor g (deg >= 1) of b,       *)
(*  and any d that equals the monic candidate monic_factor_of b g,          *)
(*  demonicize (poly_lc b) d recovers g up to sign.                         *)
#push-options "--z3rlimit 30"
let demonicize_recovers (b g d: polynomial int)
  : Lemma (requires deg b >= 1 /\ is_primitive g /\ deg g >= 1 /\
                    DV.divides g b /\
                    poly_eq d (NMZ.monic_factor_of b g))
          (ensures poly_eq (demonicize (poly_lc b) d) g \/
                   poly_eq (demonicize (poly_lc b) d) (poly_neg g))
  = H.elim_equatable_laws (polynomial int) ();
    let lc = poly_lc b in
    NMZ.poly_lc_int_nonzero b;                    (* lc <> 0 *)
    let n : nat = deg g in
    let mfo = NMZ.monic_factor_of b g in
    GI.poly_eq_int_eq d mfo;                       (* d == mfo *)
    let sgl = NMZ.scaleL g lc in
    NMZ.scaleL_length g lc;                        (* deg sgl = deg g, sgl nonempty *)
    let pp = primitive_part sgl in
    let ee = subst_cx lc pp in
    let ww = subst_cx lc mfo in
    (* inversion identity:  poly_scale cc ee == poly_scale kk g  *)
    let cc = int_content sgl in
    content_pos sgl;                               (* cc > 0 *)
    content_times_primitive sgl;                   (* sgl ~ scale cc pp *)
    GI.poly_eq_int_eq sgl (R.poly_scale cc pp);    (* sgl == scale cc pp *)
    subst_cx_scale lc cc pp;
    GI.poly_eq_int_eq (subst_cx lc (R.poly_scale cc pp)) (R.poly_scale cc ee);
    let kk = NMZ.ipow lc n in
    subst_scaleL_identity g lc;
    GI.poly_eq_int_eq (subst_cx lc sgl) (R.poly_scale kk g);
    ipow_nonzero lc n;                             (* kk <> 0 *)
    assert (R.poly_scale cc ee == R.poly_scale kk g);
    (* ww is nonempty (leading coeff of the monic candidate survives). *)
    NMZ.monic_factor_deg b g;                      (* deg mfo == n *)
    subst_cx_coeff lc mfo n;                       (* coeff ww n = coeff mfo n * lc^n *)
    DIV.leading_coeff_nonzero mfo;                 (* coeff mfo n <> 0 *)
    int_mul_nonzero (coeff mfo n) (NMZ.ipow lc n); (* coeff ww n <> 0 *)
    assert (~(ww == []));
    let ccw = int_content ww in
    content_pos ww;                                (* ccw > 0 *)
    content_times_primitive ww;                    (* ww ~ scale ccw (primitive_part ww) *)
    GI.poly_eq_int_eq ww (R.poly_scale ccw (primitive_part ww));
    primitive_part_is_primitive ww;               (* is_primitive (primitive_part ww) *)
    (* sign split: mfo = pp  or  mfo = poly_neg pp. *)
    if poly_lc pp = 1 then begin
      (* mfo == pp,  ww == ee *)
      scale_one ee;
      GI.poly_eq_int_eq (R.poly_scale 1 ee) ee;
      scale_recover ee g (primitive_part ww) cc kk ccw 1
    end else begin
      (* mfo == poly_neg pp,  ww == poly_neg ee == poly_scale (-1) ee *)
      subst_cx_neg lc pp;
      GI.poly_eq_int_eq ww (poly_neg ee);
      neg_is_scale ee;
      GI.poly_eq_int_eq (poly_neg ee) (R.poly_scale (-1) ee);
      scale_recover ee g (primitive_part ww) cc kk ccw (-1)
    end
#pop-options

(* ================================================================ *)
(*  5.  The NAMED executable integer factorizer.                     *)
(* ================================================================ *)

(*  Pipeline (all executable):                                              *)
(*    m  = monicize_pos b                          (monic image of b)       *)
(*    cs = monic_candidates m p                     (recombination sweep)    *)
(*    ks = filter (keep_int m) cs                   (survivors: MONIC divisors*)
(*                                                   of m, certified by the   *)
(*                                                   divides-test which is    *)
(*                                                   COMPLETE for monic m)    *)
(*    factor_int_complete = map (demonicize L) ks   (literal ℤ-factors of b)  *)
(*                                                                            *)
(*  Filtering at the MONIC level is essential: the divides-test              *)
(*  (monic long division) is complete only for monic divisors, and the       *)
(*  monic candidates are monic, whereas the de-monicized literal factors      *)
(*  are primitive (non-monic).                                               *)
let factor_int_complete (b: polynomial int{deg b >= 1}) (p:int{E.is_prime p})
  : Pure (list (polynomial int))
         (requires PS.is_good_prime p (NMZ.monicize_pos b) /\
                   monic (PS.reduce_to_fp p (NMZ.monicize_pos b)))
         (ensures  fun _ -> True)
  = L.map (demonicize (poly_lc b))
      (L.filter (Z.keep_int (NMZ.monicize_pos b))
                (ZCplt.monic_candidates (NMZ.monicize_pos b) p))

(* ================================================================ *)
(*  6.  COMPLETENESS of the named factorizer.                        *)
(* ================================================================ *)

(* products of divisibilities:  x|y and u|v  ==>  (x*u)|(y*v). *)
let divides_mul_combine (#t:Type) {| cr: commutative_ring t |} (x y u v: t)
  : Lemma (requires DV.divides x y /\ DV.divides u v)
          (ensures  DV.divides (mul x u) (mul y v))
  = H.elim_equatable_laws t ();
    eliminate exists (k1:t). eq y (mul x k1)
    returns DV.divides (mul x u) (mul y v)
    with _.
    eliminate exists (k2:t). eq v (mul u k2)
    returns DV.divides (mul x u) (mul y v)
    with _.
    begin
      mul_congruence y v (mul x k1) (mul u k2);      (* y*v = (x*k1)*(u*k2) *)
      assert (eq (mul (mul x k1) (mul u k2)) (mul (mul x u) (mul k1 k2))) by (canon_ring ());
      transitivity (mul y v) (mul (mul x k1) (mul u k2)) (mul (mul x u) (mul k1 k2));
      DV.divides_intro (mul x u) (mul y v) (mul k1 k2)
    end

(* the recovered-factor product is an associate of the original product. *)
let rec prod_recover_assoc (b: polynomial int) (facs: list (polynomial int))
  : Lemma (requires deg b >= 1 /\
                    (forall (g: polynomial int). L.memP g facs ==>
                       (is_primitive g /\ deg g >= 1 /\ DV.divides g b)))
          (ensures  (let recf = L.map (fun (g: polynomial int) ->
                                   demonicize (poly_lc b) (NMZ.monic_factor_of b g)) facs in
                     DV.divides (R.poly_prod recf) (R.poly_prod facs) /\
                     DV.divides (R.poly_prod facs) (R.poly_prod recf)))
          (decreases facs)
  = H.elim_equatable_laws (polynomial int) ();
    match facs with
    | [] -> DV.divides_refl (R.poly_prod #int ([] <: list (polynomial int)))
    | g :: rest ->
        let gp = demonicize (poly_lc b) (NMZ.monic_factor_of b g) in
        let pr  = R.poly_prod rest in
        let recr = L.map (fun (g0: polynomial int) ->
                            demonicize (poly_lc b) (NMZ.monic_factor_of b g0)) rest in
        let prr = R.poly_prod recr in
        (* head recovers up to sign *)
        poly_eq_reflexivity (NMZ.monic_factor_of b g);
        demonicize_recovers b g (NMZ.monic_factor_of b g);        (* gp ~ +/- g *)
        ZQC.mutual_divides_of_assoc gp g;                          (* gp|g /\ g|gp *)
        (* tail by induction *)
        prod_recover_assoc b rest;                                 (* prr|pr /\ pr|prr *)
        (* combine *)
        divides_mul_combine gp g prr pr;                           (* (gp*prr)|(g*pr) *)
        divides_mul_combine g gp pr prr                            (* (g*pr)|(gp*prr) *)

(* map preserves non-emptiness. *)
let map_nonempty (#a #b:Type) (f:a -> b) (l: list a)
  : Lemma (requires Cons? l) (ensures Cons? (L.map f l))
  = match l with | _ :: _ -> ()

(* a recovered literal factor divides b. *)
let recovered_divides (b g: polynomial int)
  : Lemma (requires deg b >= 1 /\ is_primitive g /\ deg g >= 1 /\ DV.divides g b)
          (ensures  DV.divides (demonicize (poly_lc b) (NMZ.monic_factor_of b g)) b)
  = H.elim_equatable_laws (polynomial int) ();
    let gp = demonicize (poly_lc b) (NMZ.monic_factor_of b g) in
    poly_eq_reflexivity (NMZ.monic_factor_of b g);
    demonicize_recovers b g (NMZ.monic_factor_of b g);   (* gp ~ +/- g *)
    ZQC.mutual_divides_of_assoc gp g;                     (* gp|g /\ g|gp *)
    DV.divides_trans gp g b                               (* gp|g|b ==> gp|b *)

(* every real factor's recovered image is present in the output, up to poly_eq. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let factor_reached_in_output (b g: polynomial int) (p:int{E.is_prime p})
  : Lemma (requires is_primitive b /\ deg b >= 1 /\ is_primitive g /\ deg g >= 1 /\
                    DV.divides g b /\
                    PS.is_good_prime p (NMZ.monicize_pos b) /\
                    monic (PS.reduce_to_fp p (NMZ.monicize_pos b)))
          (ensures  exists (d': polynomial int).
                      L.memP d' (factor_int_complete b p) /\
                      poly_eq d' (demonicize (poly_lc b) (NMZ.monic_factor_of b g)))
  = H.elim_equatable_laws (polynomial int) ();
    let m   = NMZ.monicize_pos b in
    let mfo = NMZ.monic_factor_of b g in
    NMZ.monicize_monic b;
    NMZ.monicize_deg b;
    eliminate exists (c: polynomial int). poly_eq b (g * c)
    returns (exists (d': polynomial int).
               L.memP d' (factor_int_complete b p) /\
               poly_eq d' (demonicize (poly_lc b) mfo))
    with _hc.
    begin
      NMZ.monic_factor_monic b g c;              (* monic mfo *)
      NMZ.monic_factor_deg b g;                  (* deg mfo == deg g >= 1 *)
      NMZ.monic_factor_divides b g c;            (* divides mfo m *)
      RCC.divides_test_complete m mfo;           (* divides_test m mfo = true *)
      NMZ.nonmonic_factor_reached b g p;         (* reached in monic_candidates *)
      eliminate exists (d0: polynomial int).
          L.memP d0 (ZCplt.monic_candidates m p) /\ poly_eq d0 mfo
      returns (exists (d': polynomial int).
                 L.memP d' (factor_int_complete b p) /\
                 poly_eq d' (demonicize (poly_lc b) mfo))
      with _hd0.
      begin
        GI.poly_eq_int_eq d0 mfo;                (* d0 == mfo *)
        let cs = ZCplt.monic_candidates m p in
        let ks = L.filter (Z.keep_int m) cs in
        L.mem_filter (Z.keep_int m) cs d0;       (* memP d0 ks <==> memP d0 cs /\ keep_int m d0 *)
        assert (Z.keep_int m d0);                (* deg d0 = deg mfo >= 1, divides_test m d0 = true *)
        L.memP_map_intro (demonicize (poly_lc b)) d0 ks;
        poly_eq_reflexivity (demonicize (poly_lc b) d0);
        introduce exists (d': polynomial int).
            L.memP d' (factor_int_complete b p) /\
            poly_eq d' (demonicize (poly_lc b) mfo)
        with (demonicize (poly_lc b) d0) and ()
      end
    end
#pop-options

(* CAPSTONE COMPLETENESS: the named function's output contains, up to poly_eq,
   a complete factorization of b into divisors of b. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let factor_int_complete_complete (b: polynomial int)
  : Lemma (requires is_primitive b /\ deg b >= 1 /\
                    SF.square_free #EQ.qq #BIN.ff (EQ.embed_zq (NMZ.monicize_pos b)))
          (ensures exists (p:int{E.is_prime p}) (facs': list (polynomial int)).
             PS.is_good_prime p (NMZ.monicize_pos b) /\
             monic (PS.reduce_to_fp p (NMZ.monicize_pos b)) /\
             Cons? facs' /\
             (DV.divides (R.poly_prod facs') b /\ DV.divides b (R.poly_prod facs')) /\
             (forall (g: polynomial int). L.memP g facs' ==> DV.divides g b) /\
             (forall (g: polynomial int). L.memP g facs' ==>
                (exists (d': polynomial int).
                   L.memP d' (factor_int_complete b p) /\ poly_eq d' g)))
  = H.elim_equatable_laws (polynomial int) ();
    let m = NMZ.monicize_pos b in
    NMZ.monicize_monic b;
    NMZ.monicize_deg b;
    ZQC.int_factorization_exists b;
    PE.good_prime_exists_sqfree m;
    eliminate exists (p:int{E.is_prime p}). PS.is_good_prime p m
    returns (exists (p:int{E.is_prime p}) (facs': list (polynomial int)).
               PS.is_good_prime p m /\
               monic (PS.reduce_to_fp p m) /\
               Cons? facs' /\
               (DV.divides (R.poly_prod facs') b /\ DV.divides b (R.poly_prod facs')) /\
               (forall (g: polynomial int). L.memP g facs' ==> DV.divides g b) /\
               (forall (g: polynomial int). L.memP g facs' ==>
                  (exists (d': polynomial int).
                     L.memP d' (factor_int_complete b p) /\ poly_eq d' g)))
    with hp.
    begin
      NMZ.good_prime_monic_reduction p m;
      eliminate exists (facs: list (polynomial int)).
          Cons? facs /\
          (DV.divides (R.poly_prod facs) b /\ DV.divides b (R.poly_prod facs)) /\
          (forall (g: polynomial int). L.memP g facs ==>
             (is_primitive g /\ deg g >= 1 /\ DV.divides g b))
      returns (exists (p:int{E.is_prime p}) (facs': list (polynomial int)).
                 PS.is_good_prime p m /\
                 monic (PS.reduce_to_fp p m) /\
                 Cons? facs' /\
                 (DV.divides (R.poly_prod facs') b /\ DV.divides b (R.poly_prod facs')) /\
                 (forall (g: polynomial int). L.memP g facs' ==> DV.divides g b) /\
                 (forall (g: polynomial int). L.memP g facs' ==>
                    (exists (d': polynomial int).
                       L.memP d' (factor_int_complete b p) /\ poly_eq d' g)))
      with hf.
      begin
        let recmap = (fun (g: polynomial int) ->
                        demonicize (poly_lc b) (NMZ.monic_factor_of b g)) in
        let facs' = L.map recmap facs in
        map_nonempty recmap facs;                       (* Cons? facs' *)
        prod_recover_assoc b facs;                       (* prod facs' ~ prod facs *)
        DV.divides_trans (R.poly_prod facs') (R.poly_prod facs) b;
        DV.divides_trans b (R.poly_prod facs) (R.poly_prod facs');
        (* per-element : divides b *)
        introduce forall (g': polynomial int). L.memP g' facs' ==> DV.divides g' b
        with begin
          introduce L.memP g' facs' ==> DV.divides g' b
          with _hm.
          begin
            L.memP_map_elim recmap g' facs;              (* exists x. memP x facs /\ recmap x == g' *)
            eliminate exists (x: polynomial int). L.memP x facs /\ recmap x == g'
            returns DV.divides g' b
            with _hx. recovered_divides b x
          end
        end;
        (* per-element : reached in output *)
        introduce forall (g': polynomial int). L.memP g' facs' ==>
                    (exists (d': polynomial int).
                       L.memP d' (factor_int_complete b p) /\ poly_eq d' g')
        with begin
          introduce L.memP g' facs' ==>
                      (exists (d': polynomial int).
                         L.memP d' (factor_int_complete b p) /\ poly_eq d' g')
          with _hm.
          begin
            L.memP_map_elim recmap g' facs;
            eliminate exists (x: polynomial int). L.memP x facs /\ recmap x == g'
            returns (exists (d': polynomial int).
                       L.memP d' (factor_int_complete b p) /\ poly_eq d' g')
            with _hx. factor_reached_in_output b x p
          end
        end;
        introduce exists (p2:int{E.is_prime p2}) (facs2: list (polynomial int)).
                    PS.is_good_prime p2 m /\
                    monic (PS.reduce_to_fp p2 m) /\
                    Cons? facs2 /\
                    (DV.divides (R.poly_prod facs2) b /\ DV.divides b (R.poly_prod facs2)) /\
                    (forall (g: polynomial int). L.memP g facs2 ==> DV.divides g b) /\
                    (forall (g: polynomial int). L.memP g facs2 ==>
                       (exists (d': polynomial int).
                          L.memP d' (factor_int_complete b p2) /\ poly_eq d' g))
        with p facs' and ()
      end
    end
#pop-options

(* ================================================================ *)
(*  7.  SOUNDNESS of the named factorizer.                           *)
(*                                                                   *)
(*  Mirror of NonMonicZass.monicize_divides_factor, but for the      *)
(*  INVERSE substitution subst_cx: the de-monicized image of any     *)
(*  monic candidate that (the executable divides-test certifies)     *)
(*  divides monicize_pos b is a genuine integer divisor of the       *)
(*  primitive b.                                                     *)
(* ================================================================ *)

module CF   = Core.Polynomial.Coeff
module FS   = Core.FinSum
module CB   = Core.Algebra.Combinators

(* length preservation for nonzero l: subst_aux is already trimmed. *)
let subst_cx_length (l:int{l <> 0}) (d: polynomial int)
  : Lemma (ensures L.length (subst_cx l d) == L.length d)
  = subst_aux_length d l 0;
    let raw = subst_aux d l 0 in
    if L.length d = 0 then ()
    else begin
      let n : nat = L.length d - 1 in
      subst_aux_index d l 0 n;                     (* index raw n == index d n * ipow l n *)
      last_eq_index d n;                           (* L.last d == L.index d n *)
      last_eq_index raw n;                         (* L.last raw == L.index raw n *)
      assert (L.index d n <> 0);                   (* d trimmed and nonempty *)
      ipow_nonzero l n;                            (* ipow l n <> 0 *)
      int_mul_nonzero (L.index d n) (NMZ.ipow l n);
      assert (L.last raw <> 0);
      assert (is_trimmed raw);
      trim_poly_does_nothing raw                   (* trim raw == raw *)
    end

(* per-term factoring of the substituted convolution:  the shared power
   l^k pulls cleanly out of every product term of coeff (d*e) k. *)
let subst_term_eq (l:int) (d e: polynomial int) (k:nat) (a:nat)
  : Lemma (ensures coeff (subst_cx l d) a * coeff (subst_cx l e) (k - a)
                   == NMZ.ipow l k * (coeff d a * coeff e (k - a)))
  = subst_cx_coeff l d a;
    if a <= k then begin
      let dd : nat = k - a in
      subst_cx_coeff l e dd;
      NMZ.ipow_add l a dd;                         (* ipow l a * ipow l dd == ipow l k *)
      NMZ.mul4_rearrange (coeff d a) (NMZ.ipow l a) (coeff e dd) (NMZ.ipow l dd)
    end
    else ()

(* the substituted convolution collapses to  l^k * coeff (d*e) k. *)
let subst_mul_coeff (l:int{l <> 0}) (d e: polynomial int) (k:nat)
  : Lemma (coeff ((subst_cx l d) * (subst_cx l e)) k == coeff (subst_cx l (d * e)) k)
  = let cP = subst_cx l d in
    let cQ = subst_cx l e in
    let c0 = NMZ.ipow l k in
    let bfun : nat -> int = CB.pointwise_mul (CB.const c0) (NMZ.term d e k) in
    CF.coeff_poly_mul_named cP cQ k bfun (fun (a:nat) -> subst_term_eq l d e k a);
    subst_cx_length l d;                           (* L.length cP == L.length d *)
    FS.sum_range_mul_left c0 (NMZ.term d e k) 0 (L.length d);
    CF.coeff_poly_mul_named d e k (NMZ.term d e k) (fun (a:nat) -> ());
    subst_cx_coeff l (d * e) k

(* CRUX MULTIPLICATIVITY of the inverse substitution (nonzero l). *)
let subst_cx_mul (l:int{l <> 0}) (d e: polynomial int)
  : Lemma (poly_eq (subst_cx l (d * e)) ((subst_cx l d) * (subst_cx l e)))
  = let aux (j:int) : Lemma (coeff (subst_cx l (d * e)) j
                             == coeff ((subst_cx l d) * (subst_cx l e)) j) =
      if j >= 0 then subst_mul_coeff l d e j else ()
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (subst_cx l (d * e)) ((subst_cx l d) * (subst_cx l e))

(* subst_cx of the monic-ization recovers b scaled by L^(deg b - 1). *)
#push-options "--z3rlimit 20"
let subst_cx_monicize (b: polynomial int{deg b >= 1})
  : Lemma (poly_eq (subst_cx (poly_lc b) (NMZ.monicize_pos b))
                   (R.poly_scale (NMZ.ipow (poly_lc b) (deg b - 1)) b))
  = let l = poly_lc b in
    let n : nat = deg b in
    NMZ.monicize_deg b;
    let m = NMZ.monicize_pos b in
    let kk : nat = n - 1 in
    let lhs = subst_cx l m in
    let rhs = R.poly_scale (NMZ.ipow l kk) b in
    let aux (i:int) : Lemma (coeff lhs i == coeff rhs i) =
      if i < 0 then ()
      else begin
        subst_cx_coeff l m i;                      (* coeff lhs i = coeff m i * ipow l i *)
        NMZ.monicize_coeff b i;
        HT.coeff_scale (NMZ.ipow l kk) b i;        (* coeff rhs i = ipow l kk * coeff b i *)
        if i > n then ()
        else if i = n then begin
          last_eq_index b n; poly_lc_reveal b;     (* coeff b n == l *)
          NMZ.ipow_add l kk 1;                     (* ipow l kk * ipow l 1 == ipow l n *)
          NMZ.ipow_one l
        end
        else begin
          let e : nat = n - 1 - i in
          NMZ.ipow_add l e i                       (* ipow l e * ipow l i == ipow l kk *)
        end
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs
#pop-options

(*  SOUNDNESS of de-monicization: a divisor d (deg >= 1) of monicize_pos b
    de-monicizes to a genuine integer divisor of the primitive b.
    (monic-ness of d is NOT needed — the content/Gauss descent handles any
    divisor.)  Mirror of NonMonicZass.monicize_divides_factor. *)
#push-options "--z3rlimit 40"
let demonicize_soundness (b d: polynomial int)
  : Lemma (requires deg b >= 1 /\ is_primitive b /\ deg d >= 1 /\
                    DV.divides d (NMZ.monicize_pos b))
          (ensures DV.divides (demonicize (poly_lc b) d) b)
  = H.elim_equatable_laws (polynomial int) ();
    let lc = poly_lc b in
    NMZ.poly_lc_int_nonzero b;                        (* lc <> 0 *)
    let n : nat = deg b in
    let m = NMZ.monicize_pos b in
    NMZ.monicize_deg b;                               (* deg m == n *)
    let bigK = NMZ.ipow lc (n - 1) in
    ipow_nonzero lc (n - 1);                          (* bigK <> 0 *)
    eliminate exists (e: polynomial int). eq m (d * e)
    returns DV.divides (demonicize lc d) b
    with _he.
    begin
      NMZ.factor_snd_deg_nonneg m d e;               (* deg e >= 0 *)
      GI.poly_eq_int_eq m (d * e);                    (* m == d * e *)
      let cP = subst_cx lc d in
      let cQ = subst_cx lc e in
      subst_cx_mul lc d e;                            (* subst_cx lc (d*e) ~ cP*cQ *)
      subst_cx_monicize b;                            (* subst_cx lc m ~ scale bigK b *)
      poly_eq_symmetry (subst_cx lc (d * e)) (cP * cQ);
      poly_eq_transitivity (cP * cQ) (subst_cx lc m)
                           (R.poly_scale bigK b);     (* cP*cQ ~ scale bigK b *)
      subst_cx_length lc d;                           (* length cP == length d >= 2 *)
      subst_cx_length lc e;                           (* length cQ == length e >= 1 *)
      assert (~(cP == []));
      assert (~(cQ == []));
      let ppP = primitive_part cP in                  (* == demonicize lc d *)
      let ppQ = primitive_part cQ in
      primitive_part_is_primitive cP;
      primitive_part_is_primitive cQ;
      primitive_mul_primitive ppP ppQ;                (* is_primitive (ppP*ppQ) *)
      content_pos cP; content_pos cQ;
      let ccP = int_content cP in
      let ccQ = int_content cQ in
      assert (ccP * ccQ <> 0);
      GI.int_content_factor cP cQ;                    (* cP*cQ ~ scale (ccP*ccQ) (ppP*ppQ) *)
      poly_eq_symmetry (cP * cQ) (R.poly_scale (ccP * ccQ) (ppP * ppQ));
      poly_eq_transitivity (R.poly_scale (ccP * ccQ) (ppP * ppQ)) (cP * cQ)
                           (R.poly_scale bigK b);
      GI.primitive_qq_associate_implies_int_associate (ppP * ppQ) b (ccP * ccQ) bigK;
      eliminate (poly_eq (ppP * ppQ) b) \/ (poly_eq (ppP * ppQ) (poly_neg b))
      returns DV.divides ppP b
      with _hpos. begin
        poly_eq_symmetry (ppP * ppQ) b;
        DV.divides_intro ppP b ppQ
      end
      and _hneg. begin
        poly_neg_congruence (ppP * ppQ) (poly_neg b);
        H.neg_neg b;
        poly_eq_transitivity (poly_neg (ppP * ppQ)) (poly_neg (poly_neg b)) b;
        H.neg_mul_r ppP ppQ;
        poly_eq_transitivity (ppP * (poly_neg ppQ)) (poly_neg (ppP * ppQ)) b;
        poly_eq_symmetry (ppP * (poly_neg ppQ)) b;
        DV.divides_intro ppP b (poly_neg ppQ)
      end
    end
#pop-options

(* CAPSTONE SOUNDNESS: every output of the named factorizer is a genuine
   integer divisor of the primitive b. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 2"
let factor_int_complete_sound
  (b: polynomial int{deg b >= 1}) (p:int{E.is_prime p}) (d: polynomial int)
  : Lemma (requires is_primitive b /\
                    PS.is_good_prime p (NMZ.monicize_pos b) /\
                    monic (PS.reduce_to_fp p (NMZ.monicize_pos b)) /\
                    L.memP d (factor_int_complete b p))
          (ensures  DV.divides d b)
  = H.elim_equatable_laws (polynomial int) ();
    let lc = poly_lc b in
    let m  = NMZ.monicize_pos b in
    let cs = ZCplt.monic_candidates m p in
    let ks = L.filter (Z.keep_int m) cs in
    L.memP_map_elim (demonicize lc) d ks;
    eliminate exists (d0: polynomial int). L.memP d0 ks /\ demonicize lc d0 == d
    returns DV.divides d b
    with _hd0.
    begin
      L.mem_filter (Z.keep_int m) cs d0;             (* keep_int m d0 = true *)
      assert (Z.keep_int m d0);
      assert (deg d0 >= 1);
      assert (RC.divides_test m d0 = true);
      RC.divides_test_sound m d0;                    (* divides d0 m *)
      demonicize_soundness b d0                      (* divides (demonicize lc d0) b == divides d b *)
    end
#pop-options
