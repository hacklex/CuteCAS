module Core.Factor.NonMonicZass

(* ================================================================ *)
(*  Non-monic Zassenhaus via MONIC-IZATION.                          *)
(*                                                                   *)
(*  DELIVERABLE 1 (self-contained arithmetic):                       *)
(*    monicize : for a primitive integer poly b of degree n >= 1     *)
(*    with leading coeff L = poly_lc b, produce the MONIC integer     *)
(*    polynomial  b~(x) = L^(n-1) * b(x/L),  whose coefficients are   *)
(*      coeff_i (b~) = a_i * L^(n-1-i)   for 0 <= i < n               *)
(*      coeff_n (b~) = 1                  (a_n = L cancels L^{-1})     *)
(*    proven MONIC of the same degree as b.                          *)
(*                                                                   *)
(*  Standalone (NOT on build-all).  NO admit / assume / sorry.       *)
(* ================================================================ *)

module L = FStar.List.Tot
module EQ = Core.Polynomial.EmbedQ

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Int
open Core.Polynomial
open Core.Polynomial.Monic

(* ---------------------------------------------------------------- *)
(*  Integer power, total on all integer exponents (1 on k <= 0).     *)
(* ---------------------------------------------------------------- *)

let rec ipow (l:int) (k:int) : Tot int (decreases (if k <= 0 then 0 else k)) =
  if k <= 0 then 1 else l * ipow l (k - 1)

(* ---------------------------------------------------------------- *)
(*  The raw monic-ization on a plain int list.                       *)
(*   - []            -> []                                            *)
(*   - [_]  (a_n)     -> [1]        (leading coeff becomes 1)         *)
(*   - a :: rest      -> a * L^(|rest|-1) :: recurse                  *)
(*  For a full list [a_0;..;a_n] the head a_i sits over a suffix of   *)
(*  length n-i+1, so its exponent |rest|-1 = n-1-i, matching          *)
(*  coeff_i = a_i * L^(n-1-i).                                        *)
(* ---------------------------------------------------------------- *)

let rec monicize_aux (b: list int) (l:int) : Tot (list int) (decreases b) =
  match b with
  | [] -> []
  | [_] -> [1]
  | a :: rest -> (a * ipow l (L.length rest - 1)) :: monicize_aux rest l

let rec monicize_aux_length (b: list int) (l:int)
  : Lemma (ensures L.length (monicize_aux b l) == L.length b)
          (decreases b)
  = match b with
    | [] -> ()
    | [_] -> ()
    | _ :: rest -> monicize_aux_length rest l

let rec monicize_aux_last (b: list int) (l:int)
  : Lemma (requires Cons? b)
          (ensures L.last (monicize_aux b l) == 1)
          (decreases b)
  = match b with
    | [_] -> ()
    | _ :: rest ->
        monicize_aux_length rest l;   (* monicize_aux rest l is nonempty *)
        monicize_aux_last rest l

(* ---------------------------------------------------------------- *)
(*  DELIVERABLE 1: the monic-ization as an integer polynomial.       *)
(* ---------------------------------------------------------------- *)

let monicize (b: polynomial int{deg b >= 1}) : polynomial int =
  let raw = monicize_aux b (poly_lc b) in
  monicize_aux_length b (poly_lc b);   (* L.length raw == L.length b >= 2 *)
  monicize_aux_last b (poly_lc b);     (* L.last raw == 1 <> 0 => is_trimmed *)
  raw

let monicize_deg (b: polynomial int{deg b >= 1})
  : Lemma (deg (monicize b) == deg b)
  = monicize_aux_length b (poly_lc b)

let monicize_monic (b: polynomial int{deg b >= 1})
  : Lemma (monic (monicize b))
  = monicize_aux_length b (poly_lc b);
    monicize_aux_last b (poly_lc b)

(* ---------------------------------------------------------------- *)
(*  The exact coefficient formula, verifying the derivation.         *)
(* ---------------------------------------------------------------- *)

let rec monicize_aux_index (b: list int) (l:int) (i:nat)
  : Lemma (requires i < L.length b /\ L.length (monicize_aux b l) == L.length b)
          (ensures L.index (monicize_aux b l) i ==
                   (if i = L.length b - 1 then 1
                    else L.index b i * ipow l (L.length b - 2 - i)))
          (decreases b)
  = match b with
    | [_] -> ()
    | _ :: rest ->
        monicize_aux_length rest l;
        if i = 0 then ()
        else monicize_aux_index rest l (i - 1)

let monicize_coeff (b: polynomial int{deg b >= 1}) (i:int)
  : Lemma (coeff (monicize b) i ==
           (if i < 0 || i > deg b then 0
            else if i = deg b then 1
            else coeff b i * ipow (poly_lc b) (deg b - 1 - i)))
  = monicize_aux_length b (poly_lc b);
    if 0 <= i && i <= deg b then monicize_aux_index b (poly_lc b) i

(* ---------------------------------------------------------------- *)
(*  DELIVERABLE 2 (partial): lift the coefficient correspondence to  *)
(*  the rationals ℚ = fraction int.  The embedded monic-ization's     *)
(*  coefficients are the ℚ-embeddings of the integer monic-ization    *)
(*  coefficients — the scaled originals a_i * L^(n-1-i) (and 1 at the  *)
(*  top).  This is the coefficient half of the root correspondence:   *)
(*  it pins embed(monicize b) as the L-scaling of embed b in ℚ[X].    *)
(* ---------------------------------------------------------------- *)

let monicize_embed_coeff (b: polynomial int{deg b >= 1}) (i:int)
  : Lemma (EQ.crq.cr_r.r_add.acg_eq.eq
             (coeff (EQ.embed_zq (monicize b)) i)
             (EQ.embed_zq_const
                (if i < 0 || i > deg b then 0
                 else if i = deg b then 1
                 else coeff b i * ipow (poly_lc b) (deg b - 1 - i))))
  = EQ.embed_zq_coeff (monicize b) i;   (* coeff(embed(monicize b)) i =eq= embed(coeff(monicize b) i) *)
    monicize_coeff b i                    (* coeff(monicize b) i == the scaled integer *)

(* ================================================================ *)
(*  DELIVERABLE 3 : the UNIFORM L-scaling  scaleL b l  and its       *)
(*  MULTIPLICATIVITY, the scalar identity linking it to monicize,    *)
(*  and — for a factorisation b ~ g*h — the exact integer product    *)
(*  identity  (scaleL g L)*(scaleL h L) = L * monicize b  together    *)
(*  with the resulting divisibility (scaled form).                   *)
(*                                                                   *)
(*  scaleL b l  is  [ a_i * l^(n-i) ]  (n = deg b), an integer poly   *)
(*  whose leading coeff is preserved (= lc b), UNLIKE monicize which  *)
(*  divides the top by an extra l.  It is a ring homomorphism on      *)
(*  products whose factor degrees add:                               *)
(*      scaleL (g*h) l  =  (scaleL g l) * (scaleL h l).               *)
(*  With l = lc b it recovers  scaleL b (lc b) = (lc b) * monicize b. *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

open Core.Algebra.Combinators

module HT = Core.Polynomial.Height
module R  = Core.Polynomial.Roots
module CF = Core.Polynomial.Coeff
module FS = Core.FinSum
module H  = Core.Algebra.Helpers
module DV = Core.Algebra.Divisibility

(* ipow is additive in the exponent for NONNEGATIVE exponents. *)
let rec ipow_add (l:int) (a b:nat)
  : Lemma (ensures ipow l (a + b) == ipow l a * ipow l b)
          (decreases a)
  = if a = 0 then () else ipow_add l (a - 1) b

#push-options "--fuel 3 --ifuel 1"
let ipow_one (l:int) : Lemma (ipow l 1 == l) = ()
#pop-options

(* raw uniform L-scaling of an int list:  head a_i over suffix rest of
   length n-i, so its exponent is |rest| (one MORE than monicize_aux). *)
let rec scaleL_aux (b: list int) (l:int) : Tot (list int) (decreases b) =
  match b with
  | [] -> []
  | a :: rest -> (a * ipow l (L.length rest)) :: scaleL_aux rest l

let rec scaleL_aux_length (b: list int) (l:int)
  : Lemma (ensures L.length (scaleL_aux b l) == L.length b) (decreases b)
  = match b with | [] -> () | _ :: rest -> scaleL_aux_length rest l

let rec scaleL_aux_last (b: list int) (l:int)
  : Lemma (requires Cons? b) (ensures L.last (scaleL_aux b l) == L.last b) (decreases b)
  = match b with
    | [_] -> ()
    | _ :: rest -> scaleL_aux_length rest l; scaleL_aux_last rest l

(* the uniform L-scaling as a genuine (trimmed) integer polynomial
   (last coeff preserved => trimmed); parameterised by ARBITRARY l. *)
let scaleL (b: polynomial int) (l:int) : polynomial int =
  let raw = scaleL_aux b l in
  (match b with | [] -> () | _ -> scaleL_aux_last b l);
  scaleL_aux_length b l;
  raw

let scaleL_length (b: polynomial int) (l:int)
  : Lemma (L.length (scaleL b l) == L.length b) = scaleL_aux_length b l

let rec scaleL_aux_index (b: list int) (l:int) (i:nat)
  : Lemma (requires i < L.length b /\ L.length (scaleL_aux b l) == L.length b)
          (ensures L.index (scaleL_aux b l) i == L.index b i * ipow l (L.length b - 1 - i))
          (decreases b)
  = match b with
    | [_] -> ()
    | _ :: rest -> scaleL_aux_length rest l; if i = 0 then () else scaleL_aux_index rest l (i - 1)

let scaleL_coeff (b: polynomial int) (l:int) (i:int)
  : Lemma (coeff (scaleL b l) i ==
           (if i < 0 || i > deg b then 0 else coeff b i * ipow l (deg b - i)))
  = scaleL_aux_length b l;
    if 0 <= i && i <= deg b then scaleL_aux_index b l i

(* small integer-multiplication rearrangements. *)
let mul4_rearrange (a b c d: int) : Lemma ((a * b) * (c * d) == (a * c) * (b * d)) = ()
let mul3_rearrange (x l y: int) : Lemma (x * (l * y) == l * (x * y)) = ()

let term (p q: polynomial int) (k: nat) (i: nat) : int = coeff p i * coeff q (k - i)

(* per-term factoring of the scaled convolution:  the shared power
   l^(n-k) (n = deg g + deg h) pulls cleanly out of every product term. *)
let smul_term_eq (g h: polynomial int) (l:int) (k:nat) (a:nat)
  : Lemma (requires deg g >= 0 /\ deg h >= 0 /\ a <= deg g)
          (ensures coeff (scaleL g l) a * coeff (scaleL h l) (k - a)
                   == ipow l (deg g + deg h - k) * (coeff g a * coeff h (k - a)))
  = scaleL_coeff g l a;
    let d = k - a in
    scaleL_coeff h l d;
    if 0 <= d && d <= deg h then begin
      ipow_add l (deg g - a) (deg h - d);
      assert (ipow l (deg g - a) * ipow l (deg h - d) == ipow l (deg g + deg h - k));
      mul4_rearrange (coeff g a) (ipow l (deg g - a)) (coeff h d) (ipow l (deg h - d));
      assert (coeff (scaleL g l) a == coeff g a * ipow l (deg g - a));
      assert (coeff (scaleL h l) d == coeff h d * ipow l (deg h - d))
    end
    else ()

(* the scaled convolution collapses to  l^(n-k) * coeff(g*h) k. *)
let scaleL_conv_eq (g h: polynomial int) (l:int) (k:nat)
  : Lemma (requires deg g >= 0 /\ deg h >= 0)
          (ensures coeff ((scaleL g l) * (scaleL h l)) k
                   == ipow l (deg g + deg h - k) * coeff (g * h) k)
  = let cP = scaleL g l in
    let cQ = scaleL h l in
    scaleL_length g l;
    let c0 = ipow l (deg g + deg h - k) in
    let bfun : nat -> int = pointwise_mul (const c0) (term g h k) in
    CF.coeff_poly_mul_named cP cQ k bfun
      (fun (a:nat) -> if a <= deg g then smul_term_eq g h l k a else ());
    FS.sum_range_mul_left c0 (term g h k) 0 (L.length g);
    CF.coeff_poly_mul_named g h k (term g h k) (fun (a:nat) -> ())

let scaleL_mul_coeff (g h: polynomial int) (l:int) (k:nat)
  : Lemma (requires deg g >= 0 /\ deg h >= 0)
          (ensures coeff ((scaleL g l) * (scaleL h l)) k == coeff (scaleL (g * h) l) k)
  = scaleL_conv_eq g h l k; deg_mul g h; scaleL_coeff (g * h) l k

(* CRUX MULTIPLICATIVITY: the uniform L-scaling is a homomorphism on
   products whose factor degrees add (integral-domain degree additivity). *)
let scaleL_mul (g h: polynomial int) (l:int)
  : Lemma (requires deg g >= 0 /\ deg h >= 0)
          (ensures poly_eq ((scaleL g l) * (scaleL h l)) (scaleL (g * h) l))
  = let cP = scaleL g l in
    let cQ = scaleL h l in
    let aux (j:int) : Lemma (coeff (cP * cQ) j == coeff (scaleL (g * h) l) j) =
      if j >= 0 then scaleL_mul_coeff g h l j else ()
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (cP * cQ) (scaleL (g * h) l)

(* scaleL respects poly_eq of its base (same scalar). *)
let scaleL_congr (b1 b2: polynomial int) (l:int)
  : Lemma (requires poly_eq b1 b2) (ensures poly_eq (scaleL b1 l) (scaleL b2 l))
  = poly_eq_length b1 b2;
    let aux (i:int) : Lemma (coeff (scaleL b1 l) i == coeff (scaleL b2 l) i) =
      scaleL_coeff b1 l i; scaleL_coeff b2 l i;
      if 0 <= i && i <= deg b1 then poly_eq_means_equal_coeffs b1 b2 i else ()
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (scaleL b1 l) (scaleL b2 l)

(* SCALAR IDENTITY:  scaleL b (lc b) = (lc b) * monicize b.
   the uniform L-scaling of b equals L times its monic-ization. *)
let monicize_scaleL_identity (b: polynomial int{deg b >= 1})
  : Lemma (poly_eq (scaleL b (poly_lc b)) (R.poly_scale (poly_lc b) (monicize b)))
  = let n = deg b in
    let l = poly_lc b in
    let ms = R.poly_scale l (monicize b) in
    let aux (i:int) : Lemma (coeff (scaleL b l) i == coeff ms i) =
      scaleL_coeff b l i;
      if i < 0 then ()
      else begin
        HT.coeff_scale l (monicize b) i;
        monicize_coeff b i;
        if i > n then ()
        else if i < n then begin
          let e : nat = n - 1 - i in
          calc (==) {
            ipow l (n - i);
            == { assert (n - i == 1 + e) }
            ipow l (1 + e);
            == { ipow_add l 1 e }
            ipow l 1 * ipow l e;
            == { ipow_one l }
            l * ipow l e;
          };
          mul3_rearrange (coeff b i) l (ipow l e);
          assert (coeff b i * ipow l (n - i) == l * (coeff b i * ipow l e))
        end
        else last_eq_index b n
      end
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (scaleL b l) ms

(* PRODUCT IDENTITY: if b ~ g*h then the L-scalings of g and h multiply to
   L * monicize b   (L = poly_lc b).  Exact integer identity. *)
let scaleL_factor_identity (b g h: polynomial int)
  : Lemma (requires deg b >= 1 /\ deg g >= 1 /\ deg h >= 0 /\ poly_eq b (g * h))
          (ensures poly_eq ((scaleL g (poly_lc b)) * (scaleL h (poly_lc b)))
                           (R.poly_scale (poly_lc b) (monicize b)))
  = let lc = poly_lc b in
    H.elim_equatable_laws (polynomial int) ();
    H.trans_for_calc (polynomial int) ();
    scaleL_mul g h lc;
    scaleL_congr (g * h) b lc;
    monicize_scaleL_identity b

(* CRUX (scaled form): the uniform L-scaling of any factor g of b divides
   L * monicize b.  Descending the stray factor L to the exact
   divides (primitive_part (scaleL g L)) (monicize b) is the remaining
   content/Gauss step (see the header note of this deliverable). *)
let monicize_divides_factor_scaled (b g h: polynomial int)
  : Lemma (requires deg b >= 1 /\ deg g >= 1 /\ deg h >= 0 /\ poly_eq b (g * h))
          (ensures DV.divides (scaleL g (poly_lc b))
                              (R.poly_scale (poly_lc b) (monicize b)))
  = let lc = poly_lc b in
    scaleL_factor_identity b g h;
    H.elim_equatable_laws (polynomial int) ();
    DV.divides_intro (scaleL g lc) (R.poly_scale lc (monicize b)) (scaleL h lc)

(* ================================================================ *)
(*  DELIVERABLE 4 : THE CONTENT DESCENT (strip the stray L), the      *)
(*  MONIC FACTOR reached, and the non-monic CAPSTONE.                 *)
(*                                                                   *)
(*  A (content descent)  primitive_part (scaleL g L) | monicize b.    *)
(*  B (monic up to sign) poly_lc (primitive_part (scaleL g L)) = ±1,  *)
(*     so its sign-fix monic_factor_of b g is genuinely MONIC and     *)
(*     still divides monicize b, of degree deg g.                     *)
(*  D (capstone)  a divides-factor g of a primitive non-monic b is    *)
(*     reached (up to poly_eq) in ZassComplete.monic_candidates of    *)
(*     monicize b, as the monic image monic_factor_of b g.            *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module E     = Core.NumberTheory
module ZCplt = Core.Factor.ZassComplete
module PS    = Core.Factor.PrimeSelect

open Core.Polynomial.Div
open Core.Factor.Content
open Core.Factor.Gauss
open Core.Factor.GaussIrred
open Core.Tactics.CanonRing

(* monic integer poly is primitive: content divides lc = 1, content > 0. *)
let monic_primitive (m: polynomial int)
  : Lemma (requires monic m) (ensures is_primitive m)
  = H.elim_equatable_laws int ();
    assert (L.length m >= 1);
    assert (~(m == []));
    content_pos m;
    int_content_nonneg m;
    let n : nat = deg m in
    last_eq_index m n;
    poly_lc_reveal m;
    assert (coeff m n == L.index m n);
    assert (coeff m n == 1);
    content_divides_coeff m n;
    E.divides_1 (int_content m)

(* leading coefficient of a nonempty integer poly is nonzero. *)
let poly_lc_int_nonzero (b: polynomial int)
  : Lemma (requires deg b >= 0) (ensures poly_lc b <> 0)
  = H.elim_equatable_laws int ();
    leading_coeff_nonzero b;
    last_eq_index b (deg b);
    poly_lc_reveal b

(* poly_eq b (g*h) with deg b >= 1 forces deg h >= 0. *)
let factor_snd_deg_nonneg (b g h: polynomial int)
  : Lemma (requires deg b >= 1 /\ poly_eq b (g * h))
          (ensures deg h >= 0)
  = poly_eq_length b (g * h);
    if deg h < 0 then begin
      assert (h == (poly_zero #int));
      poly_eq_reflexivity h;
      poly_domain_law g h;
      poly_eq_length (poly_mul g h) (poly_zero #int)
    end

(* DELIVERABLE A — content descent: pp(scaleL g L) divides monicize b. *)
#push-options "--z3rlimit 40"
let monicize_divides_factor (b g h: polynomial int)
  : Lemma (requires deg b >= 1 /\ deg g >= 1 /\ poly_eq b (g * h))
          (ensures DV.divides (primitive_part (scaleL g (poly_lc b))) (monicize b))
  = H.elim_equatable_laws (polynomial int) ();
    let lc = poly_lc b in
    factor_snd_deg_nonneg b g h;                 (* deg h >= 0 *)
    let bigP = scaleL g lc in
    let bigQ = scaleL h lc in
    let m = monicize b in
    scaleL_length g lc;                          (* length bigP == length g >= 2 *)
    scaleL_length h lc;                          (* length bigQ == length h >= 1 *)
    assert (~(bigP == []));
    assert (~(bigQ == []));
    monicize_deg b;
    monicize_monic b;
    monic_primitive m;                           (* is_primitive m *)
    let ppP = primitive_part bigP in
    let ppQ = primitive_part bigQ in
    primitive_part_is_primitive bigP;
    primitive_part_is_primitive bigQ;
    primitive_mul_primitive ppP ppQ;             (* is_primitive (ppP*ppQ) *)
    content_pos bigP;   content_pos bigQ;        (* cP>0, cQ>0 *)
    let cP = int_content bigP in
    let cQ = int_content bigQ in
    assert (cP * cQ <> 0);
    poly_lc_int_nonzero b;                        (* lc <> 0 *)
    (* poly_scale (cP*cQ) (ppP*ppQ)  ~  bigP*bigQ  ~  poly_scale lc m *)
    int_content_factor bigP bigQ;                 (* bigP*bigQ ~ scale (cP*cQ)(ppP*ppQ) *)
    scaleL_factor_identity b g h;                 (* bigP*bigQ ~ scale lc m *)
    poly_eq_symmetry (bigP * bigQ) (R.poly_scale (cP * cQ) (ppP * ppQ));
    poly_eq_transitivity (R.poly_scale (cP * cQ) (ppP * ppQ)) (bigP * bigQ)
                         (R.poly_scale lc m);
    primitive_qq_associate_implies_int_associate (ppP * ppQ) m (cP * cQ) lc;
    eliminate (poly_eq (ppP * ppQ) m) \/ (poly_eq (ppP * ppQ) (poly_neg m))
    returns DV.divides ppP m
    with _hpos. begin
      poly_eq_symmetry (ppP * ppQ) m;             (* poly_eq m (ppP*ppQ) *)
      DV.divides_intro ppP m ppQ
    end
    and _hneg. begin
      poly_neg_congruence (ppP * ppQ) (poly_neg m);   (* neg(ppP*ppQ) ~ neg(neg m) *)
      H.neg_neg m;                                    (* neg(neg m) ~ m *)
      poly_eq_transitivity (poly_neg (ppP * ppQ)) (poly_neg (poly_neg m)) m;
      H.neg_mul_r ppP ppQ;                            (* ppP*(neg ppQ) ~ neg(ppP*ppQ) *)
      poly_eq_transitivity (ppP * (poly_neg ppQ)) (poly_neg (ppP * ppQ)) m;
      poly_eq_symmetry (ppP * (poly_neg ppQ)) m;      (* poly_eq m (ppP*(neg ppQ)) *)
      DV.divides_intro ppP m (poly_neg ppQ)
    end
#pop-options

(* ---------------- DELIVERABLE B: reached factor is monic up to sign. ------- *)

(* leading coeff of a negated integer poly. *)
let poly_lc_neg (p: polynomial int)
  : Lemma (requires deg p >= 0) (ensures poly_lc (poly_neg p) == - poly_lc p)
  = H.elim_equatable_laws int ();
    let n = deg p in
    poly_neg_degree p;
    last_eq_index p n; poly_lc_reveal p;
    last_eq_index (poly_neg p) n; poly_lc_reveal (poly_neg p);
    poly_neg_coeff p n

(* an integer whose product with another is a unit is itself a unit. *)
let int_unit_of_prod_pm1 (a bb: int)
  : Lemma (requires a * bb == 1 \/ a * bb == -1) (ensures a == 1 \/ a == -1)
  = (if a * bb = 1 then
       introduce exists (q:int). (1 <: int) == q * a with bb and ()
     else
       introduce exists (q:int). (1 <: int) == q * a with (- bb) and ());
    E.divides_1 a

(* the leading coefficient of the reached primitive factor is a unit. *)
#push-options "--z3rlimit 40"
let pp_lc_pm1 (b g h: polynomial int)
  : Lemma (requires deg b >= 1 /\ deg g >= 1 /\ poly_eq b (g * h))
          (ensures (poly_lc (primitive_part (scaleL g (poly_lc b))) == 1 \/
                    poly_lc (primitive_part (scaleL g (poly_lc b))) == -1))
  = H.elim_equatable_laws int ();
    H.elim_equatable_laws (polynomial int) ();
    let lc = poly_lc b in
    factor_snd_deg_nonneg b g h;
    let bigP = scaleL g lc in
    let bigQ = scaleL h lc in
    let m = monicize b in
    scaleL_length g lc; scaleL_length h lc;
    assert (~(bigP == [])); assert (~(bigQ == []));
    monicize_deg b; monicize_monic b; monic_primitive m;
    let ppP = primitive_part bigP in
    let ppQ = primitive_part bigQ in
    primitive_part_is_primitive bigP;   primitive_part_is_primitive bigQ;
    primitive_nonempty ppP;  primitive_nonempty ppQ;
    primitive_mul_primitive ppP ppQ;
    content_pos bigP; content_pos bigQ;
    let cP = int_content bigP in let cQ = int_content bigQ in
    assert (cP * cQ <> 0);
    poly_lc_int_nonzero b;
    int_content_factor bigP bigQ;
    scaleL_factor_identity b g h;
    poly_eq_symmetry (bigP * bigQ) (R.poly_scale (cP * cQ) (ppP * ppQ));
    poly_eq_transitivity (R.poly_scale (cP * cQ) (ppP * ppQ)) (bigP * bigQ)
                         (R.poly_scale lc m);
    primitive_qq_associate_implies_int_associate (ppP * ppQ) m (cP * cQ) lc;
    R.poly_lc_mul ppP ppQ;
    assert (poly_lc m == 1);
    eliminate (poly_eq (ppP * ppQ) m) \/ (poly_eq (ppP * ppQ) (poly_neg m))
    returns (poly_lc ppP == 1 \/ poly_lc ppP == -1)
    with _hpos. begin
      R.poly_eq_lc (ppP * ppQ) m;
      int_unit_of_prod_pm1 (poly_lc ppP) (poly_lc ppQ)
    end
    and _hneg. begin
      poly_neg_degree m;
      poly_lc_neg m;
      R.poly_eq_lc (ppP * ppQ) (poly_neg m);
      int_unit_of_prod_pm1 (poly_lc ppP) (poly_lc ppQ)
    end
#pop-options

(* ---- the actual monic integer factor: sign-fix pp so lc becomes 1. -------- *)

let monic_factor_of (b g: polynomial int) : polynomial int =
  let pp = primitive_part (scaleL g (poly_lc b)) in
  if poly_lc pp = 1 then pp else poly_neg pp

(* divisibility is insensitive to negating the divisor. *)
let divides_neg_left (#t:Type) {| cr: commutative_ring t |} (d a: t)
  : Lemma (requires DV.divides d a) (ensures DV.divides (- d) a)
  = H.elim_equatable_laws t ();
    eliminate exists (k: t). a = d * k
    returns DV.divides (- d) a
    with _.
    begin
      assert ((d * k) = ((- d) * (- k))) by canon_ring ();
      transitivity a (d * k) ((- d) * (- k));
      DV.divides_intro (- d) a (- k)
    end

let monic_factor_deg (b g: polynomial int)
  : Lemma (requires deg g >= 1) (ensures deg (monic_factor_of b g) == deg g)
  = let lc = poly_lc b in
    scaleL_length g lc;
    assert (~(scaleL g lc == []));
    primitive_part_deg (scaleL g lc);
    let pp = primitive_part (scaleL g lc) in
    poly_neg_degree pp

(* DELIVERABLE B — the reached monic factor is genuinely monic. *)
#push-options "--z3rlimit 40"
let monic_factor_monic (b g h: polynomial int)
  : Lemma (requires deg b >= 1 /\ deg g >= 1 /\ poly_eq b (g * h))
          (ensures monic (monic_factor_of b g))
  = H.elim_equatable_laws int ();
    let lc = poly_lc b in
    scaleL_length g lc;
    assert (~(scaleL g lc == []));
    let pp = primitive_part (scaleL g lc) in
    primitive_part_deg (scaleL g lc);
    pp_lc_pm1 b g h;
    poly_neg_degree pp;
    if poly_lc pp = 1 then () else poly_lc_neg pp
#pop-options

(* and it divides monicize b (stripping the sign off the descent). *)
#push-options "--z3rlimit 40"
let monic_factor_divides (b g h: polynomial int)
  : Lemma (requires deg b >= 1 /\ deg g >= 1 /\ poly_eq b (g * h))
          (ensures DV.divides (monic_factor_of b g) (monicize b))
  = H.elim_equatable_laws int ();
    let lc = poly_lc b in
    let pp = primitive_part (scaleL g lc) in
    monicize_divides_factor b g h;
    pp_lc_pm1 b g h;
    if poly_lc pp = 1 then () else divides_neg_left pp (monicize b)
#pop-options

(* degree-refined monic-ization, so `monic_candidates` typechecks in the
   capstone postcondition (deg (monicize b) >= 1 provable up front). *)
let monicize_pos (b: polynomial int{deg b >= 1}) : (r: polynomial int{deg r >= 1}) =
  monicize_deg b;
  monicize b

(* ---------------- DELIVERABLE D (CAPSTONE) -------------------------------- *)
(*  A divides-factor g (deg >= 1) of a primitive non-monic b is reached,      *)
(*  up to poly_eq, in ZassComplete.monic_candidates (monicize b) p — as the   *)
(*  monic image monic_factor_of b g of g.  (Irreducibility of g is NOT        *)
(*  needed: monic_factor_reached is about candidate-list membership.)         *)
#push-options "--z3rlimit 40"
let nonmonic_factor_reached (b g: polynomial int) (p:int{E.is_prime p})
  : Lemma (requires is_primitive b /\ deg b >= 1 /\ deg g >= 1 /\
                    DV.divides g b /\
                    PS.is_good_prime p (monicize_pos b) /\
                    monic (PS.reduce_to_fp p (monicize_pos b)))
          (ensures exists (d: polynomial int).
             L.memP d (ZCplt.monic_candidates (monicize_pos b) p) /\
             poly_eq d (monic_factor_of b g))
  = H.elim_equatable_laws (polynomial int) ();
    let m = monicize_pos b in
    monicize_monic b;
    monicize_deg b;
    eliminate exists (c: polynomial int). poly_eq b (g * c)
    returns (exists (d: polynomial int).
               L.memP d (ZCplt.monic_candidates m p) /\ poly_eq d (monic_factor_of b g))
    with _hc. begin
      let gt = monic_factor_of b g in
      monic_factor_monic b g c;
      monic_factor_divides b g c;
      ZCplt.monic_factor_reached m gt p
    end
#pop-options

(* ---------------- DISCHARGING THE PRIME HYPOTHESES ----------------------- *)

module PE   = Core.Factor.PrimeExists
module IntR = Core.Modular.ResidueRing.IntReduce
module FZB  = Core.Modular.FpZmodBridge
module CP   = Core.Modular.ResidueRing.CenteredPoly
module BIN  = Core.Factor.BadIntNonzero
module SF   = Core.Polynomial.SquareFree

(*  reduce_to_fp p = poly_zf . poly_to_fp preserves monicity: the integer
    leading 1 survives ℤ→ℤ/p (poly_to_fp_monic, p>1) then ℤ/p→𝔽ₚ
    (poly_zf_monic, is_prime p).  is_good_prime is not actually needed. *)
let good_prime_monic_reduction (p:int{E.is_prime p}) (m: polynomial int)
  : Lemma (requires monic m /\ PS.is_good_prime p m)
          (ensures monic (PS.reduce_to_fp p m))
  = E.is_prime_gt1 p;
    IntR.poly_to_fp_monic p m;
    FZB.poly_zf_monic (CP.poly_to_fp p m)

(*  Unconditional in the good prime: given squarefreeness over ℚ of the
    monic-ization, a good prime EXISTS (good_prime_exists_sqfree) and its
    fp-reduction is monic (good_prime_monic_reduction), so the divides-factor
    g is reached in monic_candidates without ANY prime hypothesis.

    NB: the ℚ-squarefreeness of `monicize_pos b` is mathematically
    necessary — a good prime exists iff bad_int <> 0 iff the input is
    squarefree over ℚ; primitivity alone (int_content = 1) does not
    suffice.  The `monic (reduce_to_fp ..)` conjunct in the postcondition
    is required for `monic_candidates` (a Pure with that precondition) to
    be well-typed inside the existential. *)
let nonmonic_factor_reached_uncond (b g: polynomial int)
  : Lemma (requires is_primitive b /\ deg b >= 1 /\ deg g >= 1 /\
                    DV.divides g b /\
                    SF.square_free #EQ.qq #BIN.ff (EQ.embed_zq (monicize_pos b)))
          (ensures exists (p:int{E.is_prime p}) (d: polynomial int).
             PS.is_good_prime p (monicize_pos b) /\
             monic (PS.reduce_to_fp p (monicize_pos b)) /\
             L.memP d (ZCplt.monic_candidates (monicize_pos b) p) /\
             poly_eq d (monic_factor_of b g))
  = let m = monicize_pos b in
    monicize_monic b;
    monicize_deg b;
    PE.good_prime_exists_sqfree m;
    eliminate exists (p:int{E.is_prime p}). PS.is_good_prime p m
    returns (exists (p:int{E.is_prime p}) (d: polynomial int).
               PS.is_good_prime p m /\ monic (PS.reduce_to_fp p m) /\
               L.memP d (ZCplt.monic_candidates m p) /\
               poly_eq d (monic_factor_of b g))
    with hp. begin
      good_prime_monic_reduction p m;
      nonmonic_factor_reached b g p;
      eliminate exists (d: polynomial int).
        L.memP d (ZCplt.monic_candidates m p) /\ poly_eq d (monic_factor_of b g)
      returns (exists (p:int{E.is_prime p}) (d: polynomial int).
                 PS.is_good_prime p m /\ monic (PS.reduce_to_fp p m) /\
                 L.memP d (ZCplt.monic_candidates m p) /\
                 poly_eq d (monic_factor_of b g))
      with hd.
        introduce exists (p:int{E.is_prime p}) (d: polynomial int).
          PS.is_good_prime p m /\ monic (PS.reduce_to_fp p m) /\
          L.memP d (ZCplt.monic_candidates m p) /\
          poly_eq d (monic_factor_of b g)
        with p d and ()
    end
