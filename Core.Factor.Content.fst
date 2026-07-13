module Core.Factor.Content

(* ================================================================ *)
(*  M2 · S1 — content / primitive part (ℤ[z] ↔ ℚ[z]) + Gauss bridge. *)
(*                                                                   *)
(*  int_content p              = gcd of the |coefficients| (>= 0)     *)
(*  primitive_part p           = p scaled down by its content        *)
(*  is_primitive p             = int_content p = 1                    *)
(*  content_times_primitive    = p = content · primitive_part        *)
(*  primitive_part_is_primitive= content (primitive_part p) = 1       *)
(*  embed_zq_prod              = Gauss transport (product direction): *)
(*                               embed_zq of a ℤ-product is the       *)
(*                               ℚ-product of the embeddings.         *)
(*                                                                   *)
(*  Built on FStar.Math.Euclid (divides / is_gcd / euclid_gcd),      *)
(*  Core.Polynomial.Height (iabs, coeff_scale), Core.Polynomial.Roots *)
(*  (poly_scale, poly_prod) and Core.Polynomial.EmbedQ / EmbedQProd  *)
(*  (the ring-hom ℤ[z] → ℚ[z] and embed_zq_one).                     *)
(*                                                                   *)
(*  `gcd2` is opaque_to_smt: its extended-Euclid guts (a Pure spec    *)
(*  with an is_gcd `forall`) would otherwise blow up every VC that    *)
(*  unfolds the content fold.  All facts flow through the small       *)
(*  clean lemmas below.                                              *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module E  = Core.NumberTheory
module R  = Core.Polynomial.Roots
module HT = Core.Polynomial.Height
module ML = FStar.Math.Lemmas

module EP = Core.Polynomial.EmbedQProd

module F = Core.Fractions

open Core.Algebra
open Core.Algebra.Int
open Core.Polynomial
open Core.Polynomial.EmbedQ

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  1.  Integer gcd of two values (nonneg), from the extended        *)
(*      Euclidean algorithm, taking the sign-normalised result.      *)
(*      Opaque: only the lemmas below expose its behaviour.          *)
(* ================================================================ *)

[@@"opaque_to_smt"]
let gcd2 (a b: int) : int =
  let (_, _, d) = E.euclid_gcd a b in
  HT.iabs d

let gcd2_nonneg (a b: int) : Lemma (gcd2 a b >= 0)
  = reveal_opaque (`%gcd2) (gcd2 a b)

(* gcd2 a b is a genuine gcd of a and b (Euclid result up to sign). *)
let gcd2_is_gcd (a b: int) : Lemma (E.is_gcd a b (gcd2 a b))
  = reveal_opaque (`%gcd2) (gcd2 a b);
    let (r, s, d) = E.euclid_gcd a b in    (* ensures is_gcd a b d *)
    if d >= 0 then ()
    else begin
      E.is_gcd_opp a b d;                  (* is_gcd b a (-d) *)
      E.is_gcd_symmetric b a (- d)         (* is_gcd a b (-d) *)
    end

(* Clean projections (no is_gcd `forall` leaks to callers). *)
let gcd2_div_left  (a b: int) : Lemma (E.divides (gcd2 a b) a) = gcd2_is_gcd a b
let gcd2_div_right (a b: int) : Lemma (E.divides (gcd2 a b) b) = gcd2_is_gcd a b

let gcd2_maximal (a b x: int)
  : Lemma (requires E.divides x a /\ E.divides x b)
          (ensures  E.divides x (gcd2 a b))
  = gcd2_is_gcd a b

(* ================================================================ *)
(*  2.  Content of a raw coefficient list = gcd of all entries.      *)
(* ================================================================ *)

let rec content_list (l: list int) : Tot int (decreases l) =
  match l with
  | [] -> 0
  | x :: tl -> gcd2 x (content_list tl)

let content_list_nonneg (l: list int)
  : Lemma (ensures content_list l >= 0)
  = match l with
    | [] -> ()
    | x :: tl -> gcd2_nonneg x (content_list tl)

(* content_list divides every entry of the list. *)
let rec content_list_divides (l: list int) (i: nat{i < L.length l})
  : Lemma (ensures E.divides (content_list l) (L.index l i)) (decreases l)
  = match l with
    | [] -> ()
    | x :: tl ->
      if i = 0 then gcd2_div_left x (content_list tl)          (* g | x *)
      else begin
        gcd2_div_right x (content_list tl);                    (* g | content_list tl *)
        content_list_divides tl (i - 1);                       (* content_list tl | index tl (i-1) *)
        E.divides_transitive (content_list l) (content_list tl) (L.index tl (i - 1))
      end

(* Maximality: any common divisor of all entries divides the content. *)
let rec content_list_maximal (l: list int) (x: int)
  (pf: (i:nat{i < L.length l}) -> Lemma (E.divides x (L.index l i)))
  : Lemma (ensures E.divides x (content_list l)) (decreases l)
  = match l with
    | [] -> E.divides_0 x
    | a :: tl ->
      pf 0;                                          (* x | a *)
      let pf' (i:nat{i < L.length tl}) : Lemma (E.divides x (L.index tl i)) = pf (i + 1) in
      content_list_maximal tl x pf';                 (* x | content_list tl *)
      gcd2_maximal a (content_list tl) x             (* x | gcd2 a (content_list tl) = content_list l *)

(* ================================================================ *)
(*  3.  int_content and its divisibility soundness (all coeffs).     *)
(* ================================================================ *)

let int_content (p: polynomial int) : int = content_list p

let int_content_nonneg (p: polynomial int)
  : Lemma (int_content p >= 0)
  = content_list_nonneg p

let content_divides_coeff (p: polynomial int) (i: nat)
  : Lemma (E.divides (int_content p) (coeff p i))
  = if i < L.length p then content_list_divides p i
    else E.divides_0 (int_content p)

(* content = 0  only for the zero polynomial. *)
let content_zero_means_empty (p: polynomial int)
  : Lemma (requires int_content p = 0) (ensures p == [])
  = if L.length p = 0 then ()
    else begin
      let n = L.length p - 1 in
      content_list_divides p n;                     (* 0 | index p n  ⇒  index p n = 0 *)
      last_eq_index p n;                            (* L.last p == L.index p n *)
      assert (L.index p n == 0);
      assert (L.last p <> (0 <: int))               (* contradicts is_trimmed p *)
    end

(* nonzero polynomial ⇒ strictly positive content. *)
let content_pos (p: polynomial int)
  : Lemma (requires ~(p == [])) (ensures int_content p > 0)
  = int_content_nonneg p;
    if int_content p = 0 then content_zero_means_empty p

(* ================================================================ *)
(*  4.  primitive_part : divide every coefficient by the content.    *)
(* ================================================================ *)

let div_by (c x: int) : int = if c = 0 then 0 else x / c

let primitive_part (p: polynomial int) : polynomial int =
  let c = int_content p in
  if c = 0 then p
  else trim (L.map (div_by c) p)

(* index of a mapped list. *)
private let rec index_map_lemma (#a #b:Type) (g: a -> b) (l: list a) (i:nat{i < L.length l})
  : Lemma (ensures (L.map_lemma g l; L.index (L.map g l) i == g (L.index l i)))
          (decreases i)
  = L.map_lemma g l;
    if i = 0 then () else index_map_lemma g (L.tl l) (i - 1)

(* coefficients of primitive_part are the divided coefficients. *)
let primitive_coeff (p: polynomial int) (i: nat)
  : Lemma (requires int_content p <> 0)
          (ensures coeff (primitive_part p) i == coeff p i / int_content p)
  = let c = int_content p in
    let mapped : list int = L.map (div_by c) p in
    L.map_lemma (div_by c) p;                       (* length mapped == length p *)
    coeff_trim mapped i;
    if i < L.length p then index_map_lemma (div_by c) p i
    else ()                                          (* both sides 0 : 0/c = 0 *)

(* ================================================================ *)
(*  5.  content · primitive_part = p   (exact, coefficient-wise).    *)
(* ================================================================ *)

(* c | a and c <> 0  ⇒  c * (a / c) == a. *)
let exact_div (c a: int)
  : Lemma (requires E.divides c a /\ c <> 0)
          (ensures c * (a / c) == a)
  = E.divides_mod a c;                              (* a % c = 0 *)
    ML.lemma_div_mod a c                            (* a = (a/c)*c + a%c *)

let content_times_primitive (p: polynomial int)
  : Lemma (poly_eq p (R.poly_scale (int_content p) (primitive_part p)))
  = H.elim_equatable_laws int ();
    let c  = int_content p in
    let pp = primitive_part p in
    let per (i:nat) : Lemma (coeff (R.poly_scale c pp) i == coeff p i) =
      HT.coeff_scale c pp i;                         (* coeff (scale c pp) i == c * coeff pp i *)
      if c = 0 then content_zero_means_empty p       (* p = [] ⇒ coeff p i = 0 = c * _ *)
      else begin
        primitive_coeff p i;                         (* coeff pp i == coeff p i / c *)
        content_divides_coeff p i;                   (* c | coeff p i *)
        exact_div c (coeff p i)                      (* c * (coeff p i / c) == coeff p i *)
      end
    in
    poly_eq_by_coeff p (R.poly_scale c pp) per

(* ================================================================ *)
(*  6.  is_primitive and primitive_part_is_primitive.                *)
(* ================================================================ *)

let is_primitive (p: polynomial int) : prop = int_content p == 1

(* d | a  ⇒  (c*d) | (c*a). *)
let divides_scale (c d a: int)
  : Lemma (requires E.divides d a) (ensures E.divides (c * d) (c * a))
  = eliminate exists (q:int). a == q * d
    returns E.divides (c * d) (c * a)
    with _.
      introduce exists (q2:int). c * a == q2 * (c * d)
      with q
      and ()

(* (c*g) | c with c>0, g>=0  ⇒  g == 1. *)
let cg_divides_c_gives_one (c g: int)
  : Lemma (requires c > 0 /\ g >= 0 /\ E.divides (c * g) c) (ensures g == 1)
  = eliminate exists (q:int). c == q * (c * g)
    returns g == 1
    with _.
    begin
      assert (q * (c * g) == c * (q * g));
      assert (c == c * (q * g))
    end

let primitive_part_is_primitive (p: polynomial int)
  : Lemma (requires ~(p == [])) (ensures is_primitive (primitive_part p))
  = H.elim_equatable_laws int ();
    content_pos p;                                   (* c > 0 *)
    let c  = int_content p in
    let pp = primitive_part p in
    let g  = int_content pp in
    int_content_nonneg pp;                           (* g >= 0 *)
    content_times_primitive p;                       (* poly_eq p (poly_scale c pp) *)
    let pf (i:nat{i < L.length p}) : Lemma (E.divides (c * g) (L.index p i)) =
      poly_eq_means_equal_coeffs p (R.poly_scale c pp) i;   (* coeff p i = coeff (scale c pp) i *)
      HT.coeff_scale c pp i;                          (* coeff (scale c pp) i == c * coeff pp i *)
      content_divides_coeff pp i;                     (* g | coeff pp i *)
      divides_scale c g (coeff pp i)                  (* (c*g) | (c * coeff pp i) = coeff p i *)
    in
    content_list_maximal p (c * g) pf;               (* (c*g) | content_list p = c *)
    cg_divides_c_gives_one c g                        (* g == 1 *)

(* ================================================================ *)
(*  7.  Gauss transport (product direction): embed_zq is             *)
(*      multiplicative over an arbitrary product of ℤ-polys, so a    *)
(*      ℤ-factorization  p = g1 * ... * gn  maps to the              *)
(*      ℚ-factorization  embed p = embed g1 * ... * embed gn.        *)
(* ================================================================ *)

let rec embed_zq_prod (gs: list (polynomial int #int_cr))
  : Lemma (ensures poly_eq
             (embed_zq (R.poly_prod gs))
             (R.poly_prod #qq #crq (L.map embed_zq gs)))
          (decreases gs)
  = match gs with
    | [] -> EP.embed_zq_one ()
    | g :: rest ->
        let lhs = embed_zq (R.poly_prod gs) in
        embed_zq_mul g (R.poly_prod rest);                 (* lhs ~ poly_mul (embed g) (embed (prod rest)) *)
        embed_zq_prod rest;                                 (* IH: embed (prod rest) ~ poly_prod (map embed rest) *)
        poly_eq_reflexivity (embed_zq g);
        poly_mul_congruence
          (embed_zq g) (embed_zq (R.poly_prod rest))
          (embed_zq g) (R.poly_prod #qq #crq (L.map embed_zq rest));
        poly_eq_transitivity lhs
          (poly_mul (embed_zq g) (embed_zq (R.poly_prod rest)))
          (poly_mul (embed_zq g) (R.poly_prod #qq #crq (L.map embed_zq rest)))

(* ================================================================ *)
(*  8.  clear_denominators : ℚ[z] → (common denominator d, ℤ[z] n)   *)
(*      with  embed_zq n  =  d · r  in ℚ[z]  (so r = (1/d)·embed n). *)
(* ================================================================ *)

let qnum (x: qq) : int = F.Fraction?.num x
let qden (x: qq) : (nz:int{nz <> 0}) = F.Fraction?.den x

(* common denominator = product of all coefficient denominators. *)
let rec denom_prod (l: list qq) : Tot int (decreases l) =
  match l with
  | [] -> 1
  | x :: tl -> qden x * denom_prod tl

let rec denom_prod_nonzero (l: list qq)
  : Lemma (ensures denom_prod l <> 0) (decreases l)
  = match l with
    | [] -> ()
    | x :: tl -> denom_prod_nonzero tl

(* every coefficient denominator divides the common denominator. *)
let rec den_divides_prod (l: list qq) (i:nat{i < L.length l})
  : Lemma (ensures E.divides (qden (L.index l i)) (denom_prod l)) (decreases l)
  = match l with
    | [] -> ()
    | x :: tl ->
      if i = 0 then E.divides_mult_right (denom_prod tl) (qden x) (qden x)
      else begin
        den_divides_prod tl (i - 1);
        E.divides_mult_right (qden x) (denom_prod tl) (qden (L.index tl (i - 1)))
      end

let clear_num (d: int) (x: qq) : int = (d * qnum x) / qden x

let clear_denominators (r: polynomial qq) : (int & polynomial int) =
  let d = denom_prod r in
  (d, trim (L.map (clear_num d) r))

(* num / den of the base embedding n ↦ n/1. *)
let embed_const_num_den (n: int)
  : Lemma (F.Fraction?.num (embed_zq_const n) == n /\ F.Fraction?.den (embed_zq_const n) == 1)
  = ()

(* per-coefficient soundness of the cleared numerator:
   ((d·a)/b) / 1  =  (d/1) · (a/b)   in ℚ, when b | d·a. *)
let clear_num_correct (d: int) (x: qq)
  : Lemma (requires E.divides (qden x) (d * qnum x))
          (ensures crq.cr_r.r_add.acg_eq.eq
                     (embed_zq_const ((d * qnum x) / qden x))
                     (F.fraction_mul (embed_zq_const d) x))
  = H.elim_equatable_laws qq ();
    let a = qnum x in
    let b = qden x in
    let m = (d * a) / b in
    exact_div b (d * a);                             (* b * m == d*a *)
    embed_const_num_den d;
    embed_const_num_den m;
    F.fraction_mul_reveal (embed_zq_const d) x;        (* num = d*a, den = 1*b *)
    assert (m * (1 * b) == 1 * (d * a));               (* the fraction cross-product *)
    F.fraction_eq_reveal (embed_zq_const m) (F.fraction_mul (embed_zq_const d) x)

(* embed_zq n  =  d · r   (r reconstructed over ℚ from the integer poly). *)
let clear_denominators_sound (r: polynomial qq)
  : Lemma (poly_eq (embed_zq (snd (clear_denominators r)))
                   (R.poly_scale (embed_zq_const (fst (clear_denominators r))) r))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let d = denom_prod r in
    let mapped : list int = L.map (clear_num d) r in
    let n = trim mapped in
    let k = embed_zq_const d in
    L.map_lemma (clear_num d) r;                     (* length mapped == length r *)
    let per (i:nat) : Lemma (crq.cr_r.r_add.acg_eq.eq (coeff (embed_zq n) i) (coeff (R.poly_scale k r) i)) =
      H.elim_equatable_laws qq ();
      H.trans_for_calc qq ();
      embed_zq_coeff n i;                            (* coeff(embed n) i =eq= embed_const (coeff n i) *)
      coeff_trim mapped i;                           (* coeff n i = if i<len then index mapped i else 0 *)
      poly_mul_singleton_coeff k r i;                (* coeff(scale k r) i =eq= k *_qq coeff r i *)
      F.fraction_ring_mul_reveal k (coeff r i);        (* k *_qq coeff r i == fraction_mul k (coeff r i) *)
      if i < L.length r then begin
        index_map_lemma (clear_num d) r i;           (* index mapped i == clear_num d (coeff r i) *)
        den_divides_prod r i;                        (* qden(coeff r i) | d *)
        E.divides_mult_right (qnum (coeff r i)) d (qden (coeff r i)); (* qden | (qnum * d) = d*qnum *)
        clear_num_correct d (coeff r i)              (* embed_const(clear_num d (r_i)) = fraction_mul k (r_i) *)
      end else begin
        embed_zq_const_zero ();                      (* embed_const 0 =eq= zero#qq *)
        mul_congruence k (coeff r i) k (crq.cr_r.r_add.zero);
        H.x_mul_zero k                               (* k *_qq zero =eq= zero *)
      end
    in
    poly_eq_by_coeff (embed_zq n) (R.poly_scale k r) per
