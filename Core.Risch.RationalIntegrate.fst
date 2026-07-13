module Core.Risch.RationalIntegrate

(* ================================================================ *)
(*  MASTER REDUCTION IDENTITY for an arbitrary rational function     *)
(*  over a char_zero field:                                          *)
(*                                                                   *)
(*     D(R)  (+)  Σⱼ Fraction remⱼ dⱼ   =   Fraction p q             *)
(*                                                                   *)
(*  where each `Fraction remⱼ dⱼ` is a PROPER fraction over a        *)
(*  SQUAREFREE denominator dⱼ (deg remⱼ < deg dⱼ, square_free dⱼ,    *)
(*  deg dⱼ >= 1), so `rt_unconditional` certifies its elementary     *)
(*  integrability.                                                   *)
(*                                                                   *)
(*  Assembly (A3 design):                                            *)
(*    Q = poly_prod (moduli_of (yun_facs q));  q ~ Q  (associate).   *)
(*    Fraction p q = Fraction p' Q  (associate normalization).       *)
(*    divmod p' Q -> (s, r);  split_sound_frac: D(∫s) ⊕ r/Q = p'/Q.  *)
(*    pf_frac_sum_sound: r/Q = Σⱼ rⱼ/mⱼ.                             *)
(*    per modulus mⱼ = dⱼ^eⱼ:  hermite_fraction_identity +           *)
(*      residual divmod  =>  D(hermⱼ ⊕ ∫quⱼ) ⊕ remⱼ/dⱼ = rⱼ/mⱼ.      *)
(*    fold  =>  D(R) ⊕ Σⱼ remⱼ/dⱼ = Fraction p q.                    *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module PA = Core.Risch.PolyAntideriv

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Derivative
open Core.Polynomial.SquareFree
open Core.Polynomial.Irreducible
open Core.Polynomial.CRTMulti
open Core.Polynomial.Roots
open Core.Polynomial.PartialFraction
open Core.Polynomial.Monic
open Core.Fractions
open Core.Fractions.Derivative
open Core.Fractions.DerivativeSum
open Core.Risch.Hermite
open Core.Risch.HermiteFracLift
open Core.Risch.RationalEuclid
open Core.Risch.RationalSound
open Core.Risch.RationalSplitField
open Core.Risch.RationalFull
open Core.Risch.RTSoundness
open Core.Risch.RTUnconditional
open Core.Risch.YunFacs

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  Fraction-monoid: right identity.                                *)
(* ================================================================ *)

let frac_add_zero_r (#t:Type) {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_add x (fraction_zero t #d) = x)
  = H.elim_equatable_laws (fraction d) ();
    H.trans_for_calc (fraction d) ();
    frac_add_comm x (fraction_zero t #d);
    frac_add_zero_l x;
    transitivity
      (fraction_add x (fraction_zero t #d))
      (fraction_add (fraction_zero t #d) x)
      x

(* ================================================================ *)
(*  Degree-zero polynomial is its own leading constant.             *)
(* ================================================================ *)

let deg_zero_eq_const (#t:Type) {| f: field t |} (c: polynomial t)
  : Lemma (requires deg c == 0)
          (ensures  (c = poly_const (poly_lc c)) /\ not (poly_lc c = (zero <: t)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    leading_coeff_nonzero c;                        (* poly_lc c <> zero *)
    let lc : t = poly_lc c in
    last_eq_index c ((L.length c) - 1);             (* L.last c == L.index c 0 *)
    poly_lc_reveal c;                               (* poly_lc c == L.last c *)
    (* coeff c 0 == L.index c 0 == L.last c == poly_lc c == lc *)
    assert (coeff c 0 == lc);
    (* per-coefficient equality c = poly_const lc *)
    poly_eq_by_coeff c (poly_const lc)
      (fun (j:nat) ->
        if j = 0 then (poly_const_coeff0 lc; reflexivity lc)
        else (coeff_above_degree c j; poly_const_coeff_high lc j))

(* ================================================================ *)
(*  Inverse of a nonzero constant polynomial.                       *)
(*    c has deg 0  =>  c * poly_const (inv (poly_lc c)) = poly_one.  *)
(* ================================================================ *)

let const_mul_inv (#t:Type) {| f: field t |} (c: polynomial t)
  : Lemma (requires deg c == 0)
          (ensures  (c * poly_const (inv (poly_lc c))) = (poly_one #t))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    deg_zero_eq_const c;                             (* c = poly_const lc, lc <> zero *)
    let lc : t = poly_lc c in
    let ci : polynomial t = poly_const (inv lc) in
    (* c * ci  =  poly_const lc * ci *)
    mul_congruence c ci (poly_const lc) ci;
    (* poly_const lc * poly_const (inv lc) = poly_const (lc * inv lc) *)
    poly_const_mul lc (inv lc);                      (* poly_const (lc*inv lc) = poly_const lc * ci *)
    symmetry (poly_const (lc * inv lc)) ((poly_const lc) * ci);
    (* lc * inv lc = one *)
    inversion_lemma lc;                              (* lc * inv lc = one *)
    poly_const_congr (lc * inv lc) (one <: t);       (* poly_const (lc*inv lc) = poly_const one *)
    poly_const_one #t ();                            (* poly_const one = poly_one *)
    (* chain:  c*ci = poly_const lc * ci = poly_const (lc*inv lc)
                    = poly_const one = poly_one *)
    transitivity (c * ci) ((poly_const lc) * ci) (poly_const (lc * inv lc));
    transitivity (c * ci) (poly_const (lc * inv lc)) (poly_const (one <: t));
    transitivity (c * ci) (poly_const (one <: t)) (poly_one #t)

(* ================================================================ *)
(*  Associate normalization:  Fraction p q  =  Fraction p' Q        *)
(*  when q ~ Q  (both nonzero, mutually dividing).                   *)
(* ================================================================ *)

(* Pure ring rearrangement behind the cross-multiplication. *)
private let assoc_rearrange (#r:Type) {| cr: commutative_ring r |}
  (bigQ cc ci pp: r)
  : Lemma ((bigQ * cc) * (ci * pp) = (bigQ * pp) * (cc * ci))
  = assert ((bigQ * cc) * (ci * pp) = (bigQ * pp) * (cc * ci))
      by (Core.Tactics.CanonRing.canon_ring ())

(* ================================================================ *)
(*  A power of a nonzero polynomial is nonzero.                      *)
(* ================================================================ *)

let poly_power_nz (#t:Type) {| f: field t |} (d: polynomial t) (k: nat)
  : Lemma (requires deg d >= 0) (ensures is_nonzero (poly_power d k))
  = if k = 0 then
      polynomial_one_ne_zero #t #(id_of_f t)         (* poly_power d 0 == poly_one *)
    else begin
      poly_power_has_degree d k;                     (* deg (poly_power d k) >= 0 *)
      deg_nonneg_nonzero (poly_power d k)
    end

(* ================================================================ *)
(*  Euclidean division in the  quot*d + rem  orientation, matching   *)
(*  euclid_fraction_identity / split_sound_frac.                     *)
(* ================================================================ *)

let divmod_qr (#t:Type) {| f: field t |} (p d: polynomial t)
  : Pure (polynomial t & polynomial t)
         (requires True)
         (ensures fun (quot, rem) ->
            (p = ((quot * d) + rem)) /\
            (deg d >= 0 ==> deg rem < deg d))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let (quot, rem) = poly_divmod p d in            (* p = (d*quot)+rem *)
    mul_commutativity quot d;                        (* quot*d = d*quot *)
    symmetry (quot * d) (d * quot);                  (* d*quot = quot*d *)
    add_congruence (d * quot) rem (quot * d) rem;    (* (d*quot)+rem = (quot*d)+rem *)
    transitivity p ((d * quot) + rem) ((quot * d) + rem);
    (quot, rem)

let frac_denom_normalize (#t:Type) {| f: field t |}
  (p: polynomial t)
  (q: (x:polynomial t{is_nonzero x}))
  (bigQ: (x:polynomial t{is_nonzero x}))
  : Pure (polynomial t)
         (requires deg q >= 0 /\ deg bigQ >= 0 /\ divides bigQ q /\ divides q bigQ)
         (ensures fun p' ->
            (let id_p = polynomial_id #t #(id_of_f t) in
             (Fraction #(polynomial t) #id_p p q)
             = (Fraction #(polynomial t) #id_p p' bigQ)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let id_p = polynomial_id #t #(id_of_f t) in
    (* deg bigQ == deg q from mutual divisibility *)
    divides_degree_le bigQ q;                         (* deg bigQ <= deg q *)
    divides_degree_le q bigQ;                         (* deg q <= deg bigQ *)
    let c : polynomial t = poly_div q bigQ in
    poly_div_correct q bigQ;                          (* (bigQ * c) = q *)
    poly_div_degree q bigQ;                           (* deg c == deg q - deg bigQ == 0 *)
    let lc : t = poly_lc c in
    let ci : polynomial t = poly_const (inv lc) in
    const_mul_inv c;                                  (* (c * ci) = one *)
    let p' : polynomial t = ci * p in
    (* cross product:  p * bigQ = q * p' *)
    symmetry (bigQ * c) q;                            (* q = bigQ * c *)
    mul_congruence q (ci * p) (bigQ * c) (ci * p);    (* q*(ci*p) = (bigQ*c)*(ci*p) *)
    assoc_rearrange bigQ c ci p;                      (* (bigQ*c)*(ci*p) = (bigQ*p)*(c*ci) *)
    mul_congruence ((bigQ * p)) (c * ci) (bigQ * p) (poly_one #t);
                                                      (* (bigQ*p)*(c*ci) = (bigQ*p)*poly_one *)
    mul_one (bigQ * p);                               (* (bigQ*p)*one = bigQ*p *)
    mul_commutativity bigQ p;                         (* bigQ*p = p*bigQ *)
    transitivity (q * (ci * p)) ((bigQ * c) * (ci * p)) ((bigQ * p) * (c * ci));
    transitivity (q * (ci * p)) ((bigQ * p) * (c * ci)) ((bigQ * p) * (poly_one #t));
    transitivity (q * (ci * p)) ((bigQ * p) * (poly_one #t)) (bigQ * p);
    transitivity (q * (ci * p)) (bigQ * p) (p * bigQ);
    symmetry (q * (ci * p)) (p * bigQ);              (* p*bigQ = q*p' *)
    fraction_eq_reveal
      (Fraction #(polynomial t) #id_p p q)
      (Fraction #(polynomial t) #id_p p' bigQ);
    p'

(* ================================================================ *)
(*  (Deliverable 1)  PER-FACTOR proper normalization.               *)
(*                                                                   *)
(*  For a squarefree base dⱼ (deg >= 1), power eⱼ, pf numerator rⱼ,   *)
(*  mⱼ = dⱼ^eⱼ:  Hermite reduction + residual divmod produce a        *)
(*  rational part Rⱼ and a PROPER remainder remⱼ (deg remⱼ < deg dⱼ)  *)
(*  with                                                             *)
(*     D(Rⱼ)  (+)  Fraction remⱼ dⱼ   =   Fraction rⱼ mⱼ.            *)
(* ================================================================ *)

#push-options "--z3rlimit 40 --fuel 1 --ifuel 1"
let per_factor_reduce (#t:Type) {| f: field t |}
  (rj dj: polynomial t) (ej: pos)
  : Pure (rational_function f & polynomial t)
         (requires char_zero f /\ deg dj >= 1 /\ square_free dj)
         (ensures fun (rr, rem) ->
            is_nonzero dj /\ is_nonzero (poly_power dj ej) /\ deg rem < deg dj /\
            (let id_p = polynomial_id #t #(id_of_f t) in
             let dd : (x:polynomial t{is_nonzero x}) = dj in
             let mm : (x:polynomial t{is_nonzero x}) = poly_power dj ej in
             (fraction_add
                (rational_deriv rr)
                (Fraction #(polynomial t) #id_p rem dd))
             = (Fraction #(polynomial t) #id_p rj mm)))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    deg_nonneg_nonzero dj;                            (* is_nonzero dj *)
    poly_power_nz dj ej;                              (* is_nonzero (poly_power dj ej) *)
    let dd : (x:polynomial t{is_nonzero x}) = dj in
    let mm : (x:polynomial t{is_nonzero x}) = poly_power dj ej in
    (* Hermite reduction of rⱼ / dⱼ^eⱼ. *)
    let (parts, residual) = hermite_reduce_power rj dj ej in
    let nn : polynomial t = combined_num parts dj in
    poly_power_nz dj (ej - 1);                        (* is_nonzero dm *)
    let dm : (x:polynomial t{is_nonzero x}) = poly_power dj (ej - 1) in
    let herm_frac : fraction id_p = Fraction #(polynomial t) #id_p nn dm in
    let rhs : fraction id_p = Fraction #(polynomial t) #id_p rj mm in
    let fres : fraction id_p = Fraction #(polynomial t) #id_p residual dd in
    let rd_herm : fraction id_p = rational_deriv herm_frac in
    (* HFI:  rd_herm (+) fres = rhs. *)
    hermite_fraction_identity rj dj ej;
    (* Residual divmod:  residual = qu*dj + rem,  deg rem < deg dj. *)
    let (qu, rem) = divmod_qr residual dj in
    let frem : fraction id_p = Fraction #(polynomial t) #id_p rem dd in
    (* EFI:  fres = poly_to_rational qu (+) frem. *)
    euclid_fraction_identity residual dj qu rem;
    let ptr_qu : fraction id_p = poly_to_rational qu in
    let efi_rhs : fraction id_p = fraction_add ptr_qu frem in
    (* PPC:  D(∫qu) = poly_to_rational qu. *)
    let intq : fraction id_p = poly_to_rational (PA.antideriv qu) in
    let d_intq : fraction id_p = rational_deriv intq in
    poly_part_correct qu;                             (* d_intq = ptr_qu *)
    symmetry d_intq ptr_qu;                           (* ptr_qu = d_intq *)
    (* G = D(∫qu) (+) frem;  fres = efi_rhs = G. *)
    let gg : fraction id_p = fraction_add d_intq frem in
    frac_add_cong ptr_qu d_intq frem;                 (* efi_rhs = gg *)
    transitivity fres efi_rhs gg;                     (* fres = gg *)
    (* substitute fres = gg into HFI. *)
    frac_add_cong_r rd_herm fres gg;                  (* rd_herm+fres = rd_herm+gg *)
    symmetry (fraction_add rd_herm fres) (fraction_add rd_herm gg);
    transitivity (fraction_add rd_herm gg) (fraction_add rd_herm fres) rhs;
    (* reassociate:  rd_herm (+) (d_intq (+) frem)
                       = (rd_herm (+) d_intq) (+) frem. *)
    frac_add_assoc rd_herm d_intq frem;
    symmetry
      (fraction_add (fraction_add rd_herm d_intq) frem)
      (fraction_add rd_herm gg);
    transitivity
      (fraction_add (fraction_add rd_herm d_intq) frem)
      (fraction_add rd_herm gg)
      rhs;
    (* pull D out of the sum:  rd_herm (+) d_intq = D(herm_frac (+) ∫qu). *)
    let rr : rational_function f = fraction_add herm_frac intq in
    rational_deriv_add herm_frac intq;                (* D rr = rd_herm + d_intq *)
    symmetry (rational_deriv rr) (fraction_add rd_herm d_intq);
    frac_add_cong (fraction_add rd_herm d_intq) (rational_deriv rr) frem;
    transitivity
      (fraction_add (rational_deriv rr) frem)
      (fraction_add (fraction_add rd_herm d_intq) frem)
      rhs;
    (rr, rem)
#pop-options

(* ================================================================ *)
(*  Fold infrastructure: fraction-sum list, log spec, well-formedness*)
(* ================================================================ *)

(* Right-fold of fraction_add over a list of fractions. *)
let rec frac_sum_list (#t:Type) {| d: integral_domain t |}
  (l: list (fraction d)) : Tot (fraction d) (decreases l)
  = match l with
    | [] -> fraction_zero t #d
    | x :: rest -> fraction_add x (frac_sum_list rest)

(* A log spec: proper numerator paired with a NONZERO squarefree denom. *)
unfold let log_spec (#t:Type) (f: field t) : Type =
  (polynomial t & (x:polynomial t{is_nonzero x}))

(* A log spec (rm, d) with d already carrying nonzero-ness, mapped to  *)
(* the proper fraction Fraction rm d. *)
let log_frac (#t:Type) {| f: field t |}
  (pr: log_spec f)
  : rational_function f
  = Fraction #(polynomial t) #(polynomial_id #t #(id_of_f t)) (fst pr) (snd pr)

(* Well-formedness of a single log spec: squarefree denom of deg >= 1  *)
(* and a proper numerator. *)
let logspec_ok (#t:Type) {| f: field t |}
  (pr: log_spec f)
  : bool
  = square_free (snd pr) && (deg (snd pr) >= 1) && (deg (fst pr) < deg (snd pr))

(* ================================================================ *)
(*  4-way regrouping:  (a+b)+(c+e) = (a+c)+(b+e).                    *)
(* ================================================================ *)

let frac_add_swap4 (#t:Type) {| d: integral_domain t |}
  (a b c e: fraction d)
  : Lemma (fraction_add (fraction_add a b) (fraction_add c e)
           = fraction_add (fraction_add a c) (fraction_add b e))
  = H.elim_equatable_laws (fraction d) ();
    H.trans_for_calc (fraction d) ();
    (* (a+b)+(c+e) = a+(b+(c+e)) *)
    frac_add_assoc a b (fraction_add c e);
    (* b+(c+e) = (b+c)+e *)
    frac_add_assoc b c e;
    symmetry (fraction_add (fraction_add b c) e) (fraction_add b (fraction_add c e));
    (* (b+c) = (c+b) *)
    frac_add_comm b c;
    frac_add_cong (fraction_add b c) (fraction_add c b) e;   (* (b+c)+e = (c+b)+e *)
    (* (c+b)+e = c+(b+e) *)
    frac_add_assoc c b e;
    transitivity (fraction_add (fraction_add b c) e)
                 (fraction_add (fraction_add c b) e)
                 (fraction_add c (fraction_add b e));
    (* b+(c+e) = c+(b+e) *)
    transitivity (fraction_add b (fraction_add c e))
                 (fraction_add (fraction_add b c) e)
                 (fraction_add c (fraction_add b e));
    (* a+(b+(c+e)) = a+(c+(b+e)) *)
    frac_add_cong_r a (fraction_add b (fraction_add c e))
                      (fraction_add c (fraction_add b e));
    transitivity (fraction_add (fraction_add a b) (fraction_add c e))
                 (fraction_add a (fraction_add b (fraction_add c e)))
                 (fraction_add a (fraction_add c (fraction_add b e)));
    (* a+(c+(b+e)) = (a+c)+(b+e) *)
    frac_add_assoc a c (fraction_add b e);
    symmetry (fraction_add (fraction_add a c) (fraction_add b e))
             (fraction_add a (fraction_add c (fraction_add b e)));
    transitivity (fraction_add (fraction_add a b) (fraction_add c e))
                 (fraction_add a (fraction_add c (fraction_add b e)))
                 (fraction_add (fraction_add a c) (fraction_add b e))

(* ================================================================ *)
(*  (Deliverable 2)  THE MASTER FOLD.                               *)
(*                                                                   *)
(*  Distribute the numerator r across the squarefree-factor list,    *)
(*  Hermite-reduce each factor, and assemble one rational part R and *)
(*  a list of PROPER log specs (remⱼ, dⱼ) with                       *)
(*    D(R) (+) Σⱼ Fraction remⱼ dⱼ  =  pf_frac_sum r (moduli_of facs)*)
(*  and every dⱼ squarefree of deg >= 1 with deg remⱼ < deg dⱼ.       *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec distribute_factors (#t:Type) {| f: field t |}
  (r: polynomial t) (facs: list (sf_factor f))
  : Pure (rational_function f
          & list (log_spec f))
         (requires char_zero f /\ Cons? facs /\
                   pairwise_coprime (moduli_of facs) /\
                   all_deg_ge1 (moduli_of facs))
         (ensures fun (rr, logspecs) ->
            (fraction_add
               (rational_deriv rr)
               (frac_sum_list (L.map log_frac logspecs)))
            = pf_frac_sum r (moduli_of facs)
            /\ L.for_all logspec_ok logspecs)
         (decreases facs)
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    let bp0 = L.hd facs in
    let facsrest = L.tl facs in
    let d0 : polynomial t = fst bp0 in
    let e0 : pos = snd bp0 in
    let m0 : polynomial t = poly_power d0 e0 in
    let ms = moduli_of facs in
    assert (ms == m0 :: moduli_of facsrest);          (* map unfolds head *)
    let rest = moduli_of facsrest in
    match facsrest with
    | [] ->
        (* singleton: pf_frac_sum r [m0] = Fraction r m0. *)
        head_deg m0 rest;
        deg_nonneg_nonzero m0;
        let mm0 : (x:polynomial t{is_nonzero x}) = m0 in
        (* per-factor reduction of r / m0. *)
        let (rr0, rem0) = per_factor_reduce r d0 e0 in
        deg_nonneg_nonzero d0;
        let dd0 : (x:polynomial t{is_nonzero x}) = d0 in
        let b0 : fraction id_p = Fraction #(polynomial t) #id_p rem0 dd0 in
        (* per_factor:  D(rr0) (+) b0 = Fraction r m0 = pf_frac_sum r [m0]. *)
        let logspecs : list (log_spec f) =
          [(rem0, dd0)] in
        (* frac_sum_list (map log_frac [(rem0,dd0)]) = b0 (+) 0 = b0. *)
        frac_add_zero_r b0;                            (* b0 (+) 0 = b0 *)
        frac_add_cong_r (rational_deriv rr0)
          (frac_sum_list (L.map log_frac logspecs)) b0;
        (* D(rr0) (+) frac_sum_list(..) = D(rr0) (+) b0 = pf_frac_sum r ms *)
        transitivity
          (fraction_add (rational_deriv rr0)
             (frac_sum_list (L.map log_frac logspecs)))
          (fraction_add (rational_deriv rr0) b0)
          (pf_frac_sum r ms);
        (rr0, logspecs)
    | _ ->
        (* general step. *)
        head_deg m0 rest;
        head_coprime m0 rest;
        tail_pc m0 rest;
        tail_deg m0 rest;
        deg_prod_nonneg rest;
        deg_nonneg_nonzero m0;
        let pr : polynomial t = poly_prod rest in
        let (a0, a2) = partial_fraction_two r m0 pr in
        (* pf_frac_sum r ms = (Fraction a0 m0) (+) pf_frac_sum a2 rest. *)
        (* per-factor reduction of a0 / m0. *)
        let (rr0, rem0) = per_factor_reduce a0 d0 e0 in
        deg_nonneg_nonzero d0;
        let dd0 : (x:polynomial t{is_nonzero x}) = d0 in
        let b0 : fraction id_p = Fraction #(polynomial t) #id_p rem0 dd0 in
        (* per_factor:  D(rr0) (+) b0 = Fraction a0 m0. *)
        let fa0m0 : fraction id_p = Fraction #(polynomial t) #id_p a0 m0 in
        (* recursive fold on the tail. *)
        let (rrR, logsR) = distribute_factors a2 facsrest in
        let srest : fraction id_p = frac_sum_list (L.map log_frac logsR) in
        (* IH:  D(rrR) (+) srest = pf_frac_sum a2 rest. *)
        (* assemble R and logspecs. *)
        let rr : rational_function f = fraction_add rr0 rrR in
        let logspecs : list (log_spec f) =
          (rem0, dd0) :: logsR in
        (* frac_sum_list (map log_frac logspecs) = b0 (+) srest. *)
        (* target sum = D(rr) (+) (b0 (+) srest). *)
        (* Step A: Fraction a0 m0 = D(rr0) (+) b0. *)
        symmetry (fraction_add (rational_deriv rr0) b0) fa0m0;
        frac_add_cong fa0m0 (fraction_add (rational_deriv rr0) b0)
                      (pf_frac_sum a2 rest);
        (* pf_frac_sum r ms = (D rr0 (+) b0) (+) pf_frac_sum a2 rest. *)
        (* Step B: pf_frac_sum a2 rest = D(rrR) (+) srest. *)
        symmetry (fraction_add (rational_deriv rrR) srest) (pf_frac_sum a2 rest);
        frac_add_cong_r (fraction_add (rational_deriv rr0) b0)
                        (pf_frac_sum a2 rest)
                        (fraction_add (rational_deriv rrR) srest);
        transitivity
          (fraction_add fa0m0 (pf_frac_sum a2 rest))
          (fraction_add (fraction_add (rational_deriv rr0) b0)
                        (pf_frac_sum a2 rest))
          (fraction_add (fraction_add (rational_deriv rr0) b0)
                        (fraction_add (rational_deriv rrR) srest));
        (* Step C: 4-way swap. *)
        frac_add_swap4 (rational_deriv rr0) b0 (rational_deriv rrR) srest;
        transitivity
          (fraction_add fa0m0 (pf_frac_sum a2 rest))
          (fraction_add (fraction_add (rational_deriv rr0) b0)
                        (fraction_add (rational_deriv rrR) srest))
          (fraction_add (fraction_add (rational_deriv rr0) (rational_deriv rrR))
                        (fraction_add b0 srest));
        (* Step D: pull D out:  D rr0 (+) D rrR = D(rr0 (+) rrR). *)
        rational_deriv_add rr0 rrR;                    (* D rr = D rr0 (+) D rrR *)
        symmetry (rational_deriv rr)
                 (fraction_add (rational_deriv rr0) (rational_deriv rrR));
        frac_add_cong (fraction_add (rational_deriv rr0) (rational_deriv rrR))
                      (rational_deriv rr)
                      (fraction_add b0 srest);
        transitivity
          (fraction_add fa0m0 (pf_frac_sum a2 rest))
          (fraction_add (fraction_add (rational_deriv rr0) (rational_deriv rrR))
                        (fraction_add b0 srest))
          (fraction_add (rational_deriv rr) (fraction_add b0 srest));
        (* now:  pf_frac_sum r ms = D(rr) (+) (b0 (+) srest). *)
        (* and frac_sum_list (map log_frac logspecs) = b0 (+) srest. *)
        symmetry
          (fraction_add fa0m0 (pf_frac_sum a2 rest))
          (fraction_add (rational_deriv rr) (fraction_add b0 srest));
        (rr, logspecs)
#pop-options

(* ================================================================ *)
(*  (Deliverable 3)  THE MASTER REDUCTION IDENTITY.                 *)
(*                                                                   *)
(*  Any p/q (q nonzero, deg q >= 1) reduces to                       *)
(*     D(R)  (+)  Σⱼ Fraction remⱼ dⱼ   =   Fraction p q             *)
(*  with each (remⱼ, dⱼ) a PROPER fraction over a SQUAREFREE dⱼ of    *)
(*  degree >= 1  (so rt_unconditional certifies its elementary        *)
(*  integrability).                                                  *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rational_reduces (#t:Type) {| f: field t |}
  (p q: polynomial t)
  : Lemma (requires char_zero f /\ is_nonzero q /\ deg q >= 1)
          (ensures
            (is_nonzero q /\
             (exists (rr: rational_function f)
                     (logspecs: list (log_spec f)).
                (let id_p = polynomial_id #t #(id_of_f t) in
                 let qn : (x:polynomial t{is_nonzero x}) = q in
                 (fraction_add
                    (rational_deriv rr)
                    (frac_sum_list (L.map log_frac logspecs)))
                 = (Fraction #(polynomial t) #id_p p qn))
                /\ L.for_all logspec_ok logspecs)))
  = let id_p = polynomial_id #t #(id_of_f t) in
    H.elim_equatable_laws (fraction id_p) ();
    H.trans_for_calc (fraction id_p) ();
    let facs = yun_facs q in
    let ms = moduli_of facs in
    yun_facs_deg q;                                   (* all_deg_ge1 ms *)
    yun_facs_coprime q;                               (* pairwise_coprime ms *)
    yun_facs_associates q;                            (* divides Q q /\ divides q Q *)
    deg_prod_nonneg ms;                               (* deg (poly_prod ms) >= 0 *)
    let bigQ0 : polynomial t = poly_prod ms in
    deg_nonneg_nonzero bigQ0;                         (* is_nonzero bigQ0 *)
    let bigQ : (x:polynomial t{is_nonzero x}) = bigQ0 in
    let qn : (x:polynomial t{is_nonzero x}) = q in
    (* deg bigQ >= deg q >= 1 *)
    divides_degree_le q bigQ;                         (* deg q <= deg bigQ *)
    (* Cons? facs (empty product would have deg 0). *)
    (match facs with
     | [] -> assert (deg bigQ0 == 0)                  (* poly_prod [] = poly_one *)
     | _  -> ());
    (* associate normalization:  Fraction p q = Fraction p' bigQ. *)
    let p' : polynomial t = frac_denom_normalize p qn bigQ in
    (* Euclidean split of p' / bigQ. *)
    let (s, rnum) = divmod_qr p' bigQ in              (* p' = s*bigQ + rnum *)
    let pd : fraction id_p = Fraction #(polynomial t) #id_p rnum bigQ in
    let intS : rational_function f = poly_to_rational (PA.antideriv s) in
    let ssplit : fraction id_p = rational_deriv intS in
    split_sound_frac p' bigQ s rnum pd;              (* ssplit (+) pd = Fraction p' bigQ *)
    (* Fraction p q = Fraction p' bigQ  (associate). *)
    let fpq  : fraction id_p = Fraction #(polynomial t) #id_p p qn in
    let fpbq : fraction id_p = Fraction #(polynomial t) #id_p p' bigQ in
    symmetry fpq fpbq;                                (* Fraction p' bigQ = Fraction p q *)
    transitivity (fraction_add ssplit pd) fpbq fpq;  (* ssplit (+) pd = Fraction p q *)
    (* pd = pf_frac_sum rnum ms. *)
    pf_frac_sum_sound rnum ms;                        (* Fraction rnum bigQ = pf_frac_sum rnum ms *)
    (* distribute across factors. *)
    let (rr_fold, logspecs) = distribute_factors rnum facs in
    let sfold : fraction id_p = frac_sum_list (L.map log_frac logspecs) in
    (* IH: D(rr_fold) (+) sfold = pf_frac_sum rnum ms. *)
    (* pd = pf_frac_sum rnum ms = D(rr_fold) (+) sfold. *)
    symmetry (fraction_add (rational_deriv rr_fold) sfold) (pf_frac_sum rnum ms);
    transitivity pd (pf_frac_sum rnum ms)
                    (fraction_add (rational_deriv rr_fold) sfold);
    (* substitute pd into split identity. *)
    frac_add_cong_r ssplit pd (fraction_add (rational_deriv rr_fold) sfold);
    symmetry (fraction_add ssplit pd)
             (fraction_add ssplit (fraction_add (rational_deriv rr_fold) sfold));
    transitivity
      (fraction_add ssplit (fraction_add (rational_deriv rr_fold) sfold))
      (fraction_add ssplit pd)
      fpq;
    (* reassociate. *)
    frac_add_assoc ssplit (rational_deriv rr_fold) sfold;
    transitivity
      (fraction_add (fraction_add ssplit (rational_deriv rr_fold)) sfold)
      (fraction_add ssplit (fraction_add (rational_deriv rr_fold) sfold))
      fpq;
    (* pull D out:  ssplit (+) D rr_fold = D (intS (+) rr_fold). *)
    let rr : rational_function f = fraction_add intS rr_fold in
    rational_deriv_add intS rr_fold;                 (* D rr = ssplit (+) D rr_fold *)
    symmetry (rational_deriv rr)
             (fraction_add ssplit (rational_deriv rr_fold));
    frac_add_cong (fraction_add ssplit (rational_deriv rr_fold))
                  (rational_deriv rr) sfold;
    transitivity
      (fraction_add (rational_deriv rr) sfold)
      (fraction_add (fraction_add ssplit (rational_deriv rr_fold)) sfold)
      fpq;
    (* witness:  body holds for the concrete (rr, logspecs). *)
    assert (fraction_add (rational_deriv rr)
              (frac_sum_list (L.map log_frac logspecs)) = fpq);
    assert (L.for_all logspec_ok logspecs)
#pop-options
