module Core.Field.BerlekampSplitCorrect

(* ================================================================ *)
(*  Correctness of the Berlekamp FACTORIZATION STEP.                 *)
(*                                                                   *)
(*  Fix a prime p, a squarefree monic f over fp p, and a Berlekamp   *)
(*  element h (h^p = h (mod f)).  The factor list                    *)
(*                                                                   *)
(*      berlekamp_factors h = map (fun c -> gcd(f, h - c)) (fp_enum p)*)
(*                                                                   *)
(*  is a genuine factorization of f:                                 *)
(*    1. each entry divides f                  (gcd | f);            *)
(*    2. the entries are PAIRWISE COPRIME       (because, for c<>c',  *)
(*       (h-c)-(h-c') = c'-c is a nonzero CONSTANT / unit, so any     *)
(*       common divisor of h-c and h-c' divides that unit and hence   *)
(*       has degree 0);                                              *)
(*    3. their PRODUCT divides f                (iterate crt_inj /    *)
(*       pairwise_coprime_divides over the factor list).             *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module BK = Core.Field.Berlekamp
module FE = Core.Field.FpEnum
module SF = Core.Polynomial.SquareFree
module IR = Core.Polynomial.Irreducible
module UN = Core.Polynomial.Unique

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Tactics.CanonRing
open Core.Field.Fp
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD

module EU = FStar.Math.Euclid

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* The polynomial commutative ring over a field t. *)
let crp (t:Type) {| f: field t |} : commutative_ring (polynomial t) = TC.solve

(* ================================================================ *)
(*  const_poly facts:  coeff (const_poly c) 0 = c, and the high      *)
(*  coefficients vanish.  (const_poly c = trim [c] = monomial c 0.)  *)
(* ================================================================ *)

(* const_poly c = trim [c], which reduces to (if c = zero then [] else [c]). *)
#push-options "--fuel 4 --ifuel 2"
let const_poly_is_if (#t:Type) {| f: field t |} (c: t)
  : Lemma (BK.const_poly #t #f c == (if c = (zero <: t) then ([] <: polynomial t) else [c]))
  = assert (BK.const_poly #t #f c == (if c = (zero <: t) then ([] <: polynomial t) else [c]))
      by (FStar.Tactics.norm [delta; iota; zeta; primops]; FStar.Tactics.trefl ())
#pop-options

let const_poly_coeff0 (#t:Type) {| f: field t |} (c: t)
  : Lemma (coeff (BK.const_poly #t #f c) 0 = c)
  = H.elim_equatable_laws t ();
    const_poly_is_if #t #f c;
    if c = (zero <: t) then begin
      (* coeff [] 0 = zero ; and c = zero, so coeff = c *)
      assert (coeff (BK.const_poly #t #f c) 0 == (zero <: t));
      symmetry c (zero <: t)
    end else
      reflexivity c

let const_poly_coeff_high (#t:Type) {| f: field t |} (c: t) (i:nat)
  : Lemma (requires i >= 1)
          (ensures  coeff (BK.const_poly #t #f c) i = (zero <: t))
  = H.elim_equatable_laws t ();
    const_poly_is_if #t #f c;
    reflexivity (zero <: t)

(* const_poly has degree 0 (if c <> 0) or None (if c = 0): in either case < 1. *)
let const_poly_deg_le0 (#t:Type) {| f: field t |} (c: t)
  : Lemma (None? (poly_deg (BK.const_poly #t #f c)) \/
           Some?.v (poly_deg (BK.const_poly #t #f c)) < 1)
  = const_poly_is_if #t #f c

(* ================================================================ *)
(*  The difference of the two shifts is the constant  c' - c.        *)
(*    (h - [c]) - (h - [c'])  ~  [c'] - [c]   (pure ring identity).   *)
(* ================================================================ *)

(* Abstract ring identity:  (h - cc) - (h - cc')  =  cc' - cc.
   Proved over an abstract commutative_ring (canon_ring reflects on a
   variable instance; it FAILS on the concrete polynomial ring), then
   instantiated at p = polynomial t. *)
let abstract_shift_diff (#p:Type) {| pr: commutative_ring p |} (h cc cc': p)
  : Lemma ((h + neg cc) + neg (h + neg cc') = cc' + neg cc)
  = assert ((h + neg cc) + neg (h + neg cc') = cc' + neg cc) by (canon_ring ())

let shift_diff_is_const (#t:Type) {| f: field t |} (h: polynomial t) (c c': t)
  : Lemma (poly_eq
             (poly_sub (poly_sub h (BK.const_poly #t #f c))
                       (poly_sub h (BK.const_poly #t #f c')))
             (poly_sub (BK.const_poly #t #f c') (BK.const_poly #t #f c)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let acg = cr_p.cr_r.r_add in
    let cc  = BK.const_poly #t #f c  in
    let cc' = BK.const_poly #t #f c' in
    let s1 = poly_sub h cc  in
    let s2 = poly_sub h cc' in
    (* unfold every poly_sub to add/neg of the polynomial ring *)
    poly_sub_reveal h cc;                                 (* s1 == poly_add h (poly_neg cc) *)
    poly_sub_reveal h cc';                                (* s2 == poly_add h (poly_neg cc') *)
    poly_sub_reveal s1 s2;                                (* lhs == poly_add s1 (poly_neg s2) *)
    poly_sub_reveal cc' cc;                               (* rhs == poly_add cc' (poly_neg cc) *)
    (* poly_add == add #acg, poly_neg == neg #acg (definitional for the poly instance) *)
    assert (poly_sub s1 s2
            == add #(polynomial t) #acg
                 (add #(polynomial t) #acg h (neg #(polynomial t) #acg cc))
                 (neg #(polynomial t) #acg (add #(polynomial t) #acg h (neg #(polynomial t) #acg cc'))));
    assert (poly_sub cc' cc
            == add #(polynomial t) #acg cc' (neg #(polynomial t) #acg cc));
    abstract_shift_diff #(polynomial t) #cr_p h cc cc'

(* ================================================================ *)
(*  The constant  c' - c  is a NONZERO unit  (degree 0)  when c'<>c.  *)
(*    poly_deg (poly_sub (const_poly c') (const_poly c)) = Some 0.    *)
(* ================================================================ *)

#push-options "--z3rlimit 80"
let const_diff_deg (#t:Type) {| f: field t |} (c c': t)
  : Lemma (requires not (c' = c))
          (ensures  poly_deg (poly_sub (BK.const_poly #t #f c') (BK.const_poly #t #f c))
                    == (Some 0 <: option nat))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cr = cr_of_id t #(id_of_f t) in
    let cc  = BK.const_poly #t #f c  in
    let cc' = BK.const_poly #t #f c' in
    let r = poly_sub cc' cc in
    (* coeff r 0 = c' - c <> 0 *)
    poly_sub_coeff #t #cr cc' cc 0;
    const_poly_coeff0 #t #f c;
    const_poly_coeff0 #t #f c';
    neg_congruence (coeff cc 0) c;                       (* neg(coeff cc 0) = neg c *)
    reflexivity (coeff cc' 0);
    add_congruence (coeff cc' 0) (neg (coeff cc 0)) c' (neg c);   (* coeff cc' 0 + neg(coeff cc 0) = c' + neg c *)
    transitivity (coeff r 0) (coeff cc' 0 + neg (coeff cc 0)) (c' + neg c);
    (* c' + neg c <> 0  (since c' <> c)  via group cancellation *)
    let nonzero () : Lemma (requires (c' + neg c) = (zero <: t)) (ensures False) =
      H.x_plus_neg_x c;                                  (* c + neg c = zero *)
      (* c' + neg c = zero = c + neg c  ==>  c' = c (cancel neg c) *)
      symmetry (c + neg c) (zero <: t);
      transitivity (c' + neg c) (zero <: t) (c + neg c); (* c' + neg c = c + neg c *)
      add_commutativity c' (neg c);                      (* c' + neg c = neg c + c' *)
      add_commutativity c (neg c);                       (* c + neg c = neg c + c *)
      symmetry (c' + neg c) (neg c + c');
      transitivity (neg c + c') (c' + neg c) (c + neg c);
      transitivity (neg c + c') (c + neg c) (neg c + c);
      H.group_cancel_left (neg c) c' c                   (* c' = c, contradiction *)
    in
    Classical.move_requires nonzero ();
    assert (not ((c' + neg c) = (zero <: t)));
    assert (not (coeff r 0 = (zero <: t)));
    (* coeff r 0 <> 0  ==>  poly_deg r is Some k with k >= 0 *)
    Classical.move_requires (coeff_above_degree r) 0;    (* contrapositive: not (deg r = None or < 0) *)
    (* and deg r <= 0 via degree bound (both const_polys have deg <= 0). *)
    const_poly_deg_le0 #t #f c;
    const_poly_deg_le0 #t #f c';
    poly_sub_degree_bound #t #cr cc' cc 1;               (* deg (cc' - cc) < 1, i.e. <= 0 or None *)
    (* combine: deg r exists and is <= 0, so = Some 0 *)
    ()
#pop-options

(* ================================================================ *)
(*  PAIRWISE COPRIMALITY of the two shift-gcds.                      *)
(*                                                                   *)
(*    c <> c'  ==>  coprime (gcd(f, h-c)) (gcd(f, h-c')).            *)
(*                                                                   *)
(*  A common divisor d of (h-c) and (h-c') divides their difference  *)
(*  c'-c, a nonzero constant; so deg d <= 0.  Applied to the gcd of  *)
(*  the two split factors, this forces deg(gcd of them) = 0.         *)
(* ================================================================ *)

#push-options "--z3rlimit 120"
let berlekamp_split_pairwise_coprime (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (c c': t)
  : Lemma (requires not (c' = c))
          (ensures  coprime #t #f (BK.berlekamp_split #t #f fpoly h c)
                                  (BK.berlekamp_split #t #f fpoly h c'))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    H.trans_for_calc (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    let g1 = BK.berlekamp_split #t #f fpoly h c  in
    let g2 = BK.berlekamp_split #t #f fpoly h c' in
    let s1 = poly_sub h (BK.const_poly #t #f c)  in
    let s2 = poly_sub h (BK.const_poly #t #f c') in
    let d  = poly_gcd #t #f g1 g2 in
    (* d | g1 | s1   and   d | g2 | s2 *)
    gcd_divides_left  #t #f g1 g2;                        (* d | g1 *)
    gcd_divides_right #t #f g1 g2;                        (* d | g2 *)
    BK.berlekamp_split_divides_shift #t #f fpoly h c;     (* g1 | s1 *)
    BK.berlekamp_split_divides_shift #t #f fpoly h c';    (* g2 | s2 *)
    divides_trans #(polynomial t) #cr_p d g1 s1;          (* d | s1 *)
    divides_trans #(polynomial t) #cr_p d g2 s2;          (* d | s2 *)
    (* d | (s1 - s2) *)
    divides_sub #(polynomial t) #cr_p d s1 s2;            (* d | add s1 (neg s2) *)
    poly_sub_reveal s1 s2;                                (* poly_sub s1 s2 == add s1 (neg s2) *)
    (* s1 - s2 ~ [c'] - [c] =: r,  a nonzero constant *)
    shift_diff_is_const #t #f h c c';
    let r = poly_sub (BK.const_poly #t #f c') (BK.const_poly #t #f c) in
    divides_congruence_right #(polynomial t) #cr_p d (poly_sub s1 s2) r;  (* d | r *)
    const_diff_deg #t #f c c';                            (* poly_deg r = Some 0 *)
    (* coprime g1 g2  <==>  poly_deg d = Some 0; we have d | r (deg 0). *)
    coprime_reveal #t #f g1 g2;
    (* deg d <= deg r = 0, and d | r with r nonzero.  If deg d = None then
       d ~ 0, but 0 does not divide a nonzero r.  So Some? (poly_deg d). *)
    let dnonzero () : Lemma (requires None? (poly_deg d)) (ensures False) =
      (* d = poly_zero ; d | r  ==>  r ~ d * k = 0, contradicting deg r = Some 0 *)
      assert (d == (poly_zero #t));
      let aux (k: polynomial t) : Lemma (requires poly_eq r (poly_mul d k)) (ensures False) =
        H.x_mul_zero #(polynomial t) #cr_p.cr_r k;        (* poly_mul 0 k ~ 0 (after comm) *)
        poly_mul_commutativity d k;                       (* d*k ~ k*d = k*0 *)
        transitivity r (poly_mul d k) (poly_mul k d);
        H.x_mul_zero #(polynomial t) #cr_p.cr_r k;
        transitivity r (poly_mul k d) (poly_zero #t);
        UN.degree_well_defined r (poly_zero #t)
      in
      Classical.forall_intro (Classical.move_requires aux)
    in
    Classical.move_requires dnonzero ();
    assert (Some? (poly_deg d));
    IR.divides_degree_le #t #f d r;                       (* deg d <= deg r = 0 *)
    assert (Some?.v (poly_deg d) <= 0)
#pop-options

(* ================================================================ *)
(*  The factor list  berlekamp_factors h = map (gcd(f, h-c)) enum.   *)
(* ================================================================ *)

let berlekamp_factors (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t) : list (polynomial t)
  = L.map (fun c -> BK.berlekamp_split #t #f fpoly h c) cs

(* index commutes with map (ulib lacks a packaged lemma). *)
let rec index_map (#a #b:Type) (g: a -> b) (l: list a) (k:nat)
  : Lemma (requires k < L.length l)
          (ensures  L.length (L.map g l) == L.length l /\
                    L.index (L.map g l) k == g (L.index l k))
          (decreases l)
  = match l with
    | x :: xs -> if k = 0 then () else index_map g xs (k - 1)

(* the factor list's length and entries. *)
let berlekamp_factors_length (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t)
  : Lemma (L.length (berlekamp_factors #t #f fpoly h cs) == L.length cs)
  = (if L.length cs > 0 then
       index_map (fun c -> BK.berlekamp_split #t #f fpoly h c) cs 0)

let berlekamp_factors_index (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t) (k:nat)
  : Lemma (requires k < L.length cs)
          (ensures  L.length (berlekamp_factors #t #f fpoly h cs) == L.length cs /\
                    L.index (berlekamp_factors #t #f fpoly h cs) k
                    == BK.berlekamp_split #t #f fpoly h (L.index cs k))
  = index_map (fun c -> BK.berlekamp_split #t #f fpoly h c) cs k

(* poly_prod and flat_product are the same fold. *)
let rec poly_prod_is_flat (#t:Type) {| cr: commutative_ring t |} (ps: list (polynomial t))
  : Lemma (ensures Core.Polynomial.Product.poly_prod ps == SF.flat_product ps)
          (decreases ps)
  = match ps with
    | [] -> ()
    | _ :: rest -> poly_prod_is_flat rest

(* ================================================================ *)
(*  PART 1.  Each Berlekamp factor divides f.                        *)
(* ================================================================ *)

let berlekamp_factors_divide_f (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t) (k:nat)
  : Lemma (requires k < L.length cs)
          (ensures  L.length (berlekamp_factors #t #f fpoly h cs) == L.length cs /\
                    divides #(polynomial t) #(crp t)
                            (L.index (berlekamp_factors #t #f fpoly h cs) k) fpoly)
  = index_map (fun c -> BK.berlekamp_split #t #f fpoly h c) cs k;
    BK.berlekamp_split_divides_f #t #f fpoly h (L.index cs k)

(* ================================================================ *)
(*  Each factor is NONZERO (has a degree) when f does.               *)
(* ================================================================ *)

let berlekamp_factors_have_degree (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t) (k:nat)
  : Lemma (requires k < L.length cs /\ Some? (poly_deg fpoly))
          (ensures  Some? (poly_deg (L.index (berlekamp_factors #t #f fpoly h cs) k)))
  = index_map (fun c -> BK.berlekamp_split #t #f fpoly h c) cs k;
    let c = L.index cs k in
    (* berlekamp_split f h c = gcd(f, h - c); gcd has degree since f does. *)
    SF.gcd_has_degree #t #f fpoly (poly_sub h (BK.const_poly #t #f c))

(* ================================================================ *)
(*  PART 3 (forward direction):  the PRODUCT of the factors divides f.*)
(*                                                                   *)
(*  From pairwise coprimality (distinct enum entries) + each gcd | f,*)
(*  iterate crt_inj via `pairwise_coprime_divides`.                  *)
(* ================================================================ *)

(* the enumeration value at index k is  lo + k  (as a nat). *)
let rec fp_enum_from_index (p:int{p > 1}) (lo:nat{lo <= p}) (k:nat)
  : Lemma (requires k < L.length (FE.fp_enum_from p lo))
          (ensures  (L.index (FE.fp_enum_from p lo) k <: nat) == Prims.op_Addition lo k)
          (decreases (p - lo))
  = FE.fp_enum_from_length p lo;
    if lo = p then ()
    else if k = 0 then ()
    else fp_enum_from_index p (Prims.op_Addition lo 1) (k - 1)

let fp_enum_index (p:int{p > 1}) (k:nat)
  : Lemma (requires k < L.length (FE.fp_enum p))
          (ensures  (L.index (FE.fp_enum p) k <: nat) == k)
  = fp_enum_from_index p 0 k

#push-options "--z3rlimit 150 --fuel 2 --ifuel 2"
let berlekamp_factors_product_divides_f (p:int{EU.is_prime p})
  (fpoly h: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (requires Some? (poly_deg #(fp p) #(fp_comm_ring p) fpoly))
          (ensures  (let cr_p : commutative_ring (polynomial (fp p)) = crp (fp p) #(fp_field p) in
                     divides #(polynomial (fp p)) #cr_p
                       (Core.Polynomial.Product.poly_prod #(fp p) #(cr_of_id (fp p) #(id_of_f (fp p) #(fp_field p)))
                          (berlekamp_factors #(fp p) #(fp_field p) fpoly h (FE.fp_enum p)))
                       fpoly))
  = let ff = fp_field p in
    let cr_p : commutative_ring (polynomial (fp p)) = crp (fp p) #ff in
    let cs = FE.fp_enum p in
    let ds = berlekamp_factors #(fp p) #ff fpoly h cs in
    FE.fp_enum_length p;
    berlekamp_factors_length #(fp p) #ff fpoly h cs;       (* L.length ds == L.length cs == p *)
    assert (L.length ds == L.length cs);
    (* each factor divides f *)
    let div_all (k:nat{k < L.length ds})
      : Lemma (divides #(polynomial (fp p)) #cr_p (L.index ds k) fpoly) =
        berlekamp_factors_divide_f #(fp p) #ff fpoly h cs k
    in
    Classical.forall_intro div_all;
    (* each factor has a degree *)
    let deg_all (k:nat{k < L.length ds})
      : Lemma (Some? (poly_deg (L.index ds k))) =
        berlekamp_factors_have_degree #(fp p) #ff fpoly h cs k
    in
    Classical.forall_intro deg_all;
    (* pairwise coprime: distinct indices give distinct enum values c <> c'. *)
    let copr (i:nat{i < L.length ds}) (j:nat{j < L.length ds})
      : Lemma (i <> j ==> coprime #(fp p) #ff (L.index ds i) (L.index ds j)) =
      let aux () : Lemma (requires i <> j)
                         (ensures coprime #(fp p) #ff (L.index ds i) (L.index ds j)) =
        berlekamp_factors_index #(fp p) #ff fpoly h cs i;
        berlekamp_factors_index #(fp p) #ff fpoly h cs j;
        fp_enum_index p i;
        fp_enum_index p j;
        let ci = L.index cs i in
        let cj = L.index cs j in
        assert ((ci <: nat) == i);                          (* underlying nat is the index *)
        assert ((cj <: nat) == j);
        (* i <> j  ==>  cj <> ci as nats  ==>  cj <> ci over fp p (eq = ==) *)
        assert (not ((cj <: nat) == (ci <: nat)));
        assert (not ((cj <: fp p) = (ci <: fp p)));
        berlekamp_split_pairwise_coprime #(fp p) #ff fpoly h ci cj
      in Classical.move_requires aux ()
    in
    Classical.forall_intro_2 copr;
    (* iterate crt_inj over the whole list *)
    IR.pairwise_coprime_divides #(fp p) #ff ds fpoly;
    (* flat_product ds | f ; poly_prod ds == flat_product ds *)
    poly_prod_is_flat #(fp p) #(fp_comm_ring p) ds
#pop-options
