module Core.Factor.GaussIrred

(* ================================================================ *)
(*  C3b · Gauss's irreducibility transfer.                           *)
(*                                                                   *)
(*  qq_irreducible_of_no_int_factorization : for a primitive         *)
(*  integer polynomial p with deg p >= 1, if p admits no proper      *)
(*  factorization into two degree>=1 integer polynomials, then       *)
(*  embed_zq p is irreducible over ℚ.  This is the direction         *)
(*  factor_Q completeness consumes.                                  *)
(*                                                                   *)
(*  Crux : primitive_qq_associate_implies_int_associate — two        *)
(*  primitive integer polynomials whose integer multiples agree      *)
(*  (poly_scale N p = poly_scale M q) are equal up to sign.          *)
(*                                                                   *)
(*  Reuses Core.Factor.Gauss.content_mul / primitive_mul_primitive,  *)
(*  Core.Factor.Content, Core.Polynomial.EmbedQ.                     *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module E  = Core.NumberTheory
module ML = FStar.Math.Lemmas
module R  = Core.Polynomial.Roots
module HT = Core.Polynomial.Height
module H  = Core.Algebra.Helpers
module F  = Core.Fractions

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Polynomial
open Core.Factor.Content
open Core.Factor.Gauss
open Core.Polynomial.EmbedQ
open Core.Polynomial.Irreducible

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ================================================================ *)
(*  1.  Small integer / poly bridges.                                *)
(* ================================================================ *)

(* poly_eq over ℤ collapses to structural equality (int uses the
   default equatable `==`, and polynomials are trimmed lists). *)
let rec poly_eq_int_eq (p q: polynomial int)
  : Lemma (requires poly_eq p q) (ensures p == q) (decreases p)
  = match p, q with
    | [], [] -> ()
    | a :: p', b :: q' -> poly_eq_int_eq p' q'

(* integer left-cancellation: a<>0, a*x=a*y  ⇒  x=y. *)
let int_cancel (a x y: int)
  : Lemma (requires a <> 0 /\ a * x == a * y) (ensures x == y)
  = ML.swap_mul a x;              (* a*x == x*a *)
    ML.swap_mul a y;              (* a*y == y*a *)
    ML.cancel_mul_div x a;        (* (x*a)/a == x *)
    ML.cancel_mul_div y a         (* (y*a)/a == y *)

(* ================================================================ *)
(*  2.  Content of a scaled polynomial : |c|·content.                *)
(* ================================================================ *)

(* pure arithmetic finish, isolated so Z3 does not mix it with the
   is_gcd quantifiers.  g nonneg and g = ±n forces g = |n|. *)
let finish_iabs (g n: int)
  : Lemma (requires g >= 0 /\ (g == n \/ g + n == 0)) (ensures g == HT.iabs n)
  = ()

(* gcd of n and 0 is |n| (n<>0). *)
#push-options "--fuel 0 --ifuel 0"
let gcd2_of_zero (n: int)
  : Lemma (requires n <> 0) (ensures gcd2 n 0 == HT.iabs n)
  = E.is_gcd_0 n;                  (* is_gcd n 0 n *)
    gcd2_is_gcd n 0;               (* is_gcd n 0 (gcd2 n 0) *)
    gcd2_nonneg n 0;
    E.is_gcd_unique n 0 (gcd2 n 0) n;  (* gcd2 n 0 = n \/ = -n *)
    finish_iabs (gcd2 n 0) n
#pop-options

(* content of the constant singleton [n] (n<>0) is |n|. *)
#push-options "--fuel 2"
let content_singleton (n: int)
  : Lemma (requires n <> 0) (ensures int_content (n @ poly_zero) == HT.iabs n)
  = assert (n @ poly_zero == [n]);
    assert (content_list ([n] <: polynomial int) == gcd2 n (content_list ([] <: polynomial int)));
    assert (int_content (n @ poly_zero) == gcd2 n 0);
    gcd2_of_zero n
#pop-options

(* content(poly_scale n p) == |n|·content(p)  (n<>0), via content_mul. *)
let content_scale (n: int) (p: polynomial int)
  : Lemma (requires n <> 0)
          (ensures int_content (R.poly_scale n p) == HT.iabs n * int_content p)
  = content_mul (n @ poly_zero) p;          (* content((n@0)*p) = content(n@0)*content p *)
    content_singleton n                     (* content(n@0) = |n| *)
    (* R.poly_scale n p == (n @ poly_zero) * p definitionally *)

(* ================================================================ *)
(*  3.  The crux : primitive p, q whose integer multiples agree      *)
(*      (scale nn p = scale mm q) are equal up to sign.              *)
(* ================================================================ *)

(* cancel a nonzero integer scalar from a poly_eq of scaled polys. *)
let scale_cancel (p q: polynomial int) (nn: int)
  : Lemma (requires nn <> 0 /\ poly_eq (R.poly_scale nn p) (R.poly_scale nn q))
          (ensures  poly_eq p q)
  = let per (i:nat) : Lemma (coeff p i = coeff q i) =
      poly_eq_means_equal_coeffs (R.poly_scale nn p) (R.poly_scale nn q) i; (* coeff sp i = coeff sq i *)
      HT.coeff_scale nn p i;           (* coeff sp i == nn * coeff p i *)
      HT.coeff_scale nn q i;           (* coeff sq i == nn * coeff q i *)
      int_cancel nn (coeff p i) (coeff q i)
    in
    Classical.forall_intro per;
    equal_coeffs_means_poly_eq p q

(* scale mm q = scale nn (- q)  when  mm + nn = 0. *)
let scale_neg_eq (nn mm: int) (q: polynomial int)
  : Lemma (requires mm + nn == 0)
          (ensures  poly_eq (R.poly_scale mm q) (R.poly_scale nn (poly_neg q)))
  = let per (i:nat) : Lemma (coeff (R.poly_scale mm q) i = coeff (R.poly_scale nn (poly_neg q)) i) =
      HT.coeff_scale mm q i;                 (* == mm * coeff q i *)
      HT.coeff_scale nn (poly_neg q) i;      (* == nn * coeff (neg q) i *)
      poly_neg_coeff q i;                    (* coeff (neg q) i == - (coeff q i) *)
      ML.neg_mul_left nn (coeff q i);        (* (- nn) * cq == - (nn * cq) *)
      ML.neg_mul_right nn (coeff q i)        (* nn * (- cq) == - (nn * cq) *)
    in
    Classical.forall_intro per;
    equal_coeffs_means_poly_eq (R.poly_scale mm q) (R.poly_scale nn (poly_neg q))

(* the |nn| = |mm| step, isolated so content_mul's machinery is not
   mixed with the rest of the crux. *)
let abs_eq_of_scale (p q: polynomial int) (nn mm: int)
  : Lemma (requires is_primitive p /\ is_primitive q /\ nn <> 0 /\ mm <> 0 /\
                    poly_eq (R.poly_scale nn p) (R.poly_scale mm q))
          (ensures  HT.iabs nn == HT.iabs mm)
  = poly_eq_int_eq (R.poly_scale nn p) (R.poly_scale mm q);  (* sp == sq *)
    content_scale nn p;                (* content sp == |nn| * content p == |nn| *)
    content_scale mm q                 (* content sq == |mm| * content q == |mm| *)

(* pure sign step. *)
let sign_flip (nn mm: int)
  : Lemma (requires HT.iabs nn == HT.iabs mm /\ mm <> nn) (ensures mm + nn == 0)
  = ()

(* THE CRUX. *)
let primitive_qq_associate_implies_int_associate
  (p q: polynomial int) (nn mm: int)
  : Lemma (requires is_primitive p /\ is_primitive q /\ nn <> 0 /\ mm <> 0 /\
                    poly_eq (R.poly_scale nn p) (R.poly_scale mm q))
          (ensures  poly_eq p q \/ poly_eq p (poly_neg q))
  = abs_eq_of_scale p q nn mm;            (* |nn| == |mm| *)
    if mm = nn then
      scale_cancel p q nn                 (* poly_eq p q *)
    else begin
      sign_flip nn mm;                    (* mm + nn == 0 *)
      scale_neg_eq nn mm q;               (* scale mm q =eq= scale nn (neg q) *)
      poly_eq_transitivity (R.poly_scale nn p) (R.poly_scale mm q)
                           (R.poly_scale nn (poly_neg q));
      scale_cancel p (poly_neg q) nn      (* poly_eq p (neg q) *)
    end

(* ================================================================ *)
(*  4.  embed_zq bridges for the descent to ℤ.                       *)
(* ================================================================ *)

(* embed_zq_const is injective (n/1 = m/1 iff n = m). *)
let embed_const_inj (m n: int)
  : Lemma (requires crq.cr_r.r_add.acg_eq.eq (embed_zq_const m) (embed_zq_const n))
          (ensures  m == n)
  = H.elim_equatable_laws qq ();
    embed_const_num_den m;   embed_const_num_den n;
    F.fraction_eq_reveal (embed_zq_const m) (embed_zq_const n)

(* embed_zq is injective as a coefficient-wise ring hom ℤ[z] → ℚ[z]. *)
let embed_zq_injective (p q: polynomial int)
  : Lemma (requires poly_eq (embed_zq p) (embed_zq q)) (ensures poly_eq p q)
  = let per (i:nat) : Lemma (coeff p i = coeff q i) =
      H.elim_equatable_laws qq ();
      H.trans_for_calc qq ();
      poly_eq_means_equal_coeffs (embed_zq p) (embed_zq q) i; (* coeff(ep)i =eq= coeff(eq)i *)
      embed_zq_coeff p i;                     (* coeff(ep)i =eq= embed_const(coeff p i) *)
      embed_zq_coeff q i;                     (* coeff(eq)i =eq= embed_const(coeff q i) *)
      embed_const_inj (coeff p i) (coeff q i)
    in
    Classical.forall_intro per;
    equal_coeffs_means_poly_eq p q

(* embed_zq commutes with an integer scaling (n<>0). *)
let embed_scale (n: int) (p: polynomial int)
  : Lemma (requires n <> 0)
          (ensures poly_eq (embed_zq (R.poly_scale n p))
                           (R.poly_scale (embed_zq_const n) (embed_zq p)))
  = let lhs = embed_zq (R.poly_scale n p) in
    let rhs = R.poly_scale (embed_zq_const n) (embed_zq p) in
    let per (i:nat) : Lemma (coeff lhs i = coeff rhs i) =
      H.elim_equatable_laws qq ();
      H.trans_for_calc qq ();
      embed_zq_coeff (R.poly_scale n p) i;   (* coeff lhs i =eq= embed_const(coeff(scale n p) i) *)
      HT.coeff_scale n p i;                  (* coeff(scale n p) i == n * coeff p i (Prims) *)
      poly_mul_singleton_coeff (embed_zq_const n) (embed_zq p) i; (* coeff rhs i =eq= embed_n *_qq coeff(embed p)i *)
      embed_zq_coeff p i;                    (* coeff(embed p) i =eq= embed_const(coeff p i) *)
      mul_congruence (embed_zq_const n) (coeff (embed_zq p) i)
                     (embed_zq_const n) (embed_zq_const (coeff p i));
      F.fraction_ring_mul_reveal (embed_zq_const n) (embed_zq_const (coeff p i));
      embed_zq_const_mul n (coeff p i)       (* fraction_mul(embed n)(embed cp) = embed(n*cp) *)
    in
    Classical.forall_intro per;
    equal_coeffs_means_poly_eq lhs rhs

(* ================================================================ *)
(*  5.  Generic poly_scale algebra (any commutative ring).           *)
(* ================================================================ *)

(* poly_scale respects poly_eq of the polynomial argument. *)
let scale_congr_poly (#t:Type) {| cr: commutative_ring t |} (a: t) (x y: polynomial t)
  : Lemma (requires (x = y)) (ensures (R.poly_scale a x = R.poly_scale a y))
  = H.elim_equatable_laws (polynomial t) ();
    poly_eq_reflexivity (a @ poly_zero);
    poly_mul_congruence (a @ poly_zero) x (a @ poly_zero) y

(* (scale a x) * y = scale a (x * y). *)
let scale_mul_l (#t:Type) {| cr: commutative_ring t |} (a: t) (x y: polynomial t)
  : Lemma ((R.poly_scale a x * y) = R.poly_scale a (x * y))
  = H.elim_equatable_laws (polynomial t) ();
    poly_mul_associativity (a @ poly_zero) x y

(* x * (scale a y) = scale a (x * y). *)
let scale_mul_r (#t:Type) {| cr: commutative_ring t |} (a: t) (x y: polynomial t)
  : Lemma ((x * R.poly_scale a y) = R.poly_scale a (x * y))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    poly_mul_commutativity x (R.poly_scale a y);   (* x*scale a y = (scale a y)*x *)
    scale_mul_l a y x;                             (* (scale a y)*x = scale a (y*x) *)
    poly_mul_commutativity y x;                    (* y*x = x*y *)
    scale_congr_poly a (y * x) (x * y)             (* scale a (y*x) = scale a (x*y) *)

(* scale a (scale b w) = scale (a*b) w. *)
let scale_scale (#t:Type) {| cr: commutative_ring t |} (a b: t) (w: polynomial t)
  : Lemma (poly_eq (R.poly_scale a (R.poly_scale b w)) (R.poly_scale (a * b) w))
  = let lhs = R.poly_scale a (R.poly_scale b w) in
    let rhs = R.poly_scale (a * b) w in
    let per (i:nat) : Lemma (coeff lhs i = coeff rhs i) =
      H.elim_equatable_laws t ();
      H.trans_for_calc t ();
      poly_mul_singleton_coeff a (R.poly_scale b w) i;  (* coeff lhs i = a * coeff(scale b w) i *)
      poly_mul_singleton_coeff b w i;                   (* coeff(scale b w) i = b * coeff w i *)
      poly_mul_singleton_coeff (a * b) w i;             (* coeff rhs i = (a*b) * coeff w i *)
      mul_congruence a (coeff (R.poly_scale b w) i) a (b * coeff w i);
      mul_associativity a b (coeff w i)
    in
    Classical.forall_intro per;
    equal_coeffs_means_poly_eq lhs rhs

(* (scale a x) * (scale b y) = scale (a*b) (x*y). *)
let scale_mul_combine (#t:Type) {| cr: commutative_ring t |} (a b: t) (x y: polynomial t)
  : Lemma (poly_eq (R.poly_scale a x * R.poly_scale b y) (R.poly_scale (a * b) (x * y)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    scale_mul_l a x (R.poly_scale b y);        (* (scale a x)*(scale b y) = scale a (x * scale b y) *)
    scale_mul_r b x y;                          (* x * scale b y = scale b (x*y) *)
    scale_congr_poly a (x * R.poly_scale b y) (R.poly_scale b (x * y));
    scale_scale a b (x * y)                     (* scale a (scale b (x*y)) = scale (a*b)(x*y) *)

(* ================================================================ *)
(*  6.  Degree helpers.                                              *)
(* ================================================================ *)

(* scaling by a nonzero field constant preserves degree. *)
#push-options "--fuel 2"
let deg_scale_nonzero (#t:Type) {| f: field t |} (c: t) (x: polynomial t)
  : Lemma (requires ~(c = (zero <: t)) /\ deg x >= 0)
          (ensures  deg (R.poly_scale c x) == deg x)
  = assert (c @ poly_zero == [c]);
    assert (deg ([c] <: polynomial t) == 0);
    deg_mul (c @ poly_zero) x
#pop-options

(* primitive_part preserves degree (nonzero polynomial). *)
let primitive_part_deg (a0: polynomial int)
  : Lemma (requires ~(a0 == [])) (ensures deg (primitive_part a0) == deg a0)
  = content_pos a0;
    content_times_primitive a0;                 (* poly_eq a0 (scale ca ah) *)
    primitive_part_is_primitive a0;
    primitive_nonempty (primitive_part a0);      (* ah nonempty *)
    poly_scale_length (int_content a0) (primitive_part a0);
    poly_eq_length a0 (R.poly_scale (int_content a0) (primitive_part a0))

(* ================================================================ *)
(*  7.  Descent to ℤ : the cleared-denominator identity.             *)
(* ================================================================ *)

(* From embed p = A*B and cleared-denominator soundness for A, B,
   derive the integer identity  scale (da*db) p  =  a0 * b0. *)
#push-options "--z3rlimit 10"
let int_identity (p: polynomial int) (bigA bigB: polynomial qq)
  (da db: int) (a0 b0: polynomial int)
  : Lemma (requires da <> 0 /\ db <> 0 /\
                    (embed_zq p = (bigA * bigB)) == true /\
                    poly_eq (embed_zq a0) (R.poly_scale (embed_zq_const da) bigA) /\
                    poly_eq (embed_zq b0) (R.poly_scale (embed_zq_const db) bigB))
          (ensures poly_eq (R.poly_scale (da * db) p) (a0 * b0))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let sa = R.poly_scale (embed_zq_const da) bigA in
    let sb = R.poly_scale (embed_zq_const db) bigB in
    let sc = embed_zq_const da * embed_zq_const db in       (* qq scalar *)
    let t0 = embed_zq (a0 * b0) in
    let t1 = embed_zq a0 * embed_zq b0 in
    let t2 = sa * sb in
    let t3 = R.poly_scale sc (bigA * bigB) in
    let t4 = R.poly_scale (embed_zq_const (da * db)) (bigA * bigB) in
    let t5 = R.poly_scale (embed_zq_const (da * db)) (embed_zq p) in
    let t6 = embed_zq (R.poly_scale (da * db) p) in
    (* t0 ~ t1 *)
    embed_zq_mul a0 b0;
    (* t1 ~ t2 *)
    poly_mul_congruence (embed_zq a0) (embed_zq b0) sa sb;
    (* t2 ~ t3 *)
    scale_mul_combine (embed_zq_const da) (embed_zq_const db) bigA bigB;
    (* t3 ~ t4 : scalar congruence *)
    embed_zq_const_mul da db;
    F.fraction_ring_mul_reveal (embed_zq_const da) (embed_zq_const db);
    R.poly_scale_scalar_congr sc (embed_zq_const (da * db)) (bigA * bigB);
    (* t4 ~ t5 : bigA*bigB ~ embed p *)
    poly_eq_symmetry (embed_zq p) (bigA * bigB);
    scale_congr_poly (embed_zq_const (da * db)) (bigA * bigB) (embed_zq p);
    (* t5 ~ t6 *)
    embed_scale (da * db) p;
    poly_eq_symmetry t6 t5;
    (* chain t0 ~ ... ~ t6 *)
    poly_eq_transitivity t0 t1 t2;
    poly_eq_transitivity t0 t2 t3;
    poly_eq_transitivity t0 t3 t4;
    poly_eq_transitivity t0 t4 t5;
    poly_eq_transitivity t0 t5 t6;
    (* embed injective : a0*b0 ~ scale(da*db) p *)
    embed_zq_injective (a0 * b0) (R.poly_scale (da * db) p);
    poly_eq_symmetry (a0 * b0) (R.poly_scale (da * db) p)
#pop-options

(* a0 * b0 = (content a0 · content b0) · (primitive a0 · primitive b0). *)
let int_content_factor (a0 b0: polynomial int)
  : Lemma (requires ~(a0 == []) /\ ~(b0 == []))
          (ensures poly_eq (a0 * b0)
                     (R.poly_scale (int_content a0 * int_content b0)
                                   (primitive_part a0 * primitive_part b0)))
  = H.elim_equatable_laws (polynomial int) ();
    H.trans_for_calc (polynomial int) ();
    let ca = int_content a0 in
    let cb = int_content b0 in
    let ah = primitive_part a0 in
    let bh = primitive_part b0 in
    content_times_primitive a0;   (* a0 ~ scale ca ah *)
    content_times_primitive b0;   (* b0 ~ scale cb bh *)
    poly_mul_congruence a0 b0 (R.poly_scale ca ah) (R.poly_scale cb bh);
    scale_mul_combine ca cb ah bh;
    poly_eq_transitivity (a0 * b0)
      (R.poly_scale ca ah * R.poly_scale cb bh)
      (R.poly_scale (ca * cb) (ah * bh))

(* ================================================================ *)
(*  8.  The contrapositive : a proper ℚ-factorization of embed p     *)
(*      yields a proper ℤ-factorization of p, contradicting hyp.     *)
(* ================================================================ *)

#push-options "--z3rlimit 10"
let gauss_contra (p: polynomial int) (bigA bigB: polynomial qq)
  (hyp: (a: polynomial int) -> (b: polynomial int) -> Lemma
          (requires (p = (a * b)) == true)
          (ensures  deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0))
  : Lemma (requires is_primitive p /\ deg p >= 1 /\
                    (embed_zq p = (bigA * bigB)) == true /\
                    deg bigA >= 1 /\ deg bigB >= 1)
          (ensures False)
  = H.elim_equatable_laws (polynomial int) ();
    H.trans_for_calc (polynomial int) ();
    H.elim_equatable_laws qq ();
    let da = fst (clear_denominators bigA) in
    let a0 = snd (clear_denominators bigA) in
    let db = fst (clear_denominators bigB) in
    let b0 = snd (clear_denominators bigB) in
    denom_prod_nonzero bigA;    denom_prod_nonzero bigB;    (* da, db <> 0 *)
    clear_denominators_sound bigA;   clear_denominators_sound bigB;
    embed_zq_const_zero_iff da;   embed_zq_const_zero_iff db;  (* embed da, db <> 0_qq *)
    (* deg a0 = deg bigA, deg b0 = deg bigB *)
    deg_scale_nonzero (embed_zq_const da) bigA;
    poly_eq_length (embed_zq a0) (R.poly_scale (embed_zq_const da) bigA);
    embed_zq_deg a0;
    deg_scale_nonzero (embed_zq_const db) bigB;
    poly_eq_length (embed_zq b0) (R.poly_scale (embed_zq_const db) bigB);
    embed_zq_deg b0;
    assert (deg a0 >= 1);   assert (deg b0 >= 1);
    assert (L.length a0 >= 2);   assert (L.length b0 >= 2);
    assert (~(a0 == []));   assert (~(b0 == []));
    let ca = int_content a0 in   let cb = int_content b0 in
    let ah = primitive_part a0 in   let bh = primitive_part b0 in
    content_pos a0;   content_pos b0;                       (* ca, cb > 0 *)
    primitive_part_deg a0;   primitive_part_deg b0;          (* deg ah, bh >= 1 *)
    primitive_part_is_primitive a0;   primitive_part_is_primitive b0;
    primitive_mul_primitive ah bh;                          (* ah*bh primitive *)
    (* integer identities : scale(da*db) p ~ a0*b0 ~ scale(ca*cb)(ah*bh) *)
    int_identity p bigA bigB da db a0 b0;
    int_content_factor a0 b0;
    poly_eq_transitivity (R.poly_scale (da * db) p) (a0 * b0)
                         (R.poly_scale (ca * cb) (ah * bh));
    (* crux : p ~ ±(ah*bh) *)
    primitive_qq_associate_implies_int_associate p (ah * bh) (da * db) (ca * cb);
    eliminate (poly_eq p (ah * bh)) \/ (poly_eq p (poly_neg (ah * bh)))
    returns False
    with _hpos. hyp ah bh                                    (* deg ah/bh <= 0 : ⊥ *)
    and  _hneg. begin
      H.neg_mul_l ah bh;                                     (* (neg ah)*bh =eq= neg(ah*bh) *)
      poly_eq_symmetry ((poly_neg ah) * bh) (poly_neg (ah * bh));
      poly_eq_transitivity p (poly_neg (ah * bh)) ((poly_neg ah) * bh);
      Core.Polynomial.Div.poly_neg_degree ah;                (* deg(neg ah)==deg ah>=1 *)
      hyp (poly_neg ah) bh                                   (* deg(neg ah)/bh <= 0 : ⊥ *)
    end
#pop-options

(* ================================================================ *)
(*  9.  MAIN THEOREM.                                                 *)
(* ================================================================ *)

let qq_irreducible_of_no_int_factorization (p: polynomial int)
  : Lemma (requires is_primitive p /\ deg p >= 1 /\
                    (forall (a b: polynomial int). ((p = (a * b)) == true) ==>
                       (deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0)))
          (ensures poly_irreducible #qq (embed_zq p))
  = embed_zq_deg p;                        (* deg(embed p) == deg p >= 1 *)
    let hyp (a b: polynomial int)
      : Lemma (requires (p = (a * b)) == true)
              (ensures  deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0)
      = () in
    let aux (bigA bigB: polynomial qq)
      : Lemma (requires (embed_zq p = (bigA * bigB)) == true)
              (ensures  deg bigA == 0 \/ deg bigA < 0 \/ deg bigB == 0 \/ deg bigB < 0)
      = if deg bigA >= 1 && deg bigB >= 1 then gauss_contra p bigA bigB hyp
    in
    Classical.forall_intro_2 (Classical.move_requires_2 aux)
