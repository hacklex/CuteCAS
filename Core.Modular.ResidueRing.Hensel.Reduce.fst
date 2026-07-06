module Core.Modular.ResidueRing.Hensel.Reduce

(* ================================================================ *)
(*  §C foundation — the reduction ring-homomorphism  ℤ/pᵏ⁺¹ → ℤ/pᵏ.  *)
(*                                                                   *)
(*  Merged from:                                                      *)
(*    Core.Modular.ResidueRing.HenselReduce      (scalar reduction ring-hom) *)
(*    Core.Modular.ResidueRing.HenselReducePoly  (poly_reduce ring-hom)      *)
(*    Core.Modular.ResidueRing.HenselQuotient    (error-quotient map)        *)
(*    Core.Modular.ResidueRing.HenselScale       (scaling + reconstruction)  *)
(*                                                                   *)
(*  The coefficient ring ℤ/pⁿ = `zmod (ppow p n)` is FREE:           *)
(*  `zmod_comm_ring (m)` needs no primality (any m > 1).  Hensel      *)
(*  lifting threads the reduction maps `ℤ/pᵏ⁺¹ → ℤ/pᵏ → … → ℤ/p =     *)
(*  𝔽_p`; this module establishes the single reduction step           *)
(*  `a ↦ a mod pᵏ` and proves it is a ring homomorphism (preserves    *)
(*  0, 1, +, ·), lifts it to polynomials, and proves the              *)
(*  error-reconstruction `e = pᵏ·δ`.                                  *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Modular.ResidueRing
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.FinSum
open FStar.Math.Lemmas

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  §1  — scalar reduction step  ℤ/pᵏ⁺¹ → ℤ/pᵏ  (from HenselReduce)  *)
(* ================================================================ *)

(* pⁿ as a positive int; > 1 whenever n ≥ 1 (p > 1). *)
let rec ppow (p:int{p > 1}) (n:nat) : Tot (r:int{r > 0}) (decreases n)
  = if n = 0 then 1 else p `Prims.op_Star` ppow p (n - 1)

let rec ppow_gt_one (p:int{p > 1}) (n:nat{n >= 1})
  : Lemma (ensures ppow p n > 1) (decreases n)
  = if n = 1 then () else ppow_gt_one p (n - 1)

(* The reduction step a ↦ a mod pᵏ : ℤ/pᵏ⁺¹ → ℤ/pᵏ. *)
let reduce_step (p:int{p > 1}) (k:pos) (a: zmod (ppow p (k ++ 1))) : zmod (ppow p k)
  = ppow_gt_one p k;
    ppow_gt_one p (k ++ 1);
    lemma_mod_lt (zv a) (ppow p k);
    Zm (zv a % (ppow p k))

(* ---------------------------------------------------------------- *)
(*  reduce_step is a ring homomorphism (preserves 0, 1, +, ·).       *)
(*  All four are modular-arithmetic facts: reducing mod pᵏ⁺¹ then     *)
(*  mod pᵏ equals reducing the operands mod pᵏ (since pᵏ | pᵏ⁺¹).     *)
(* ---------------------------------------------------------------- *)

(* pᵏ⁺¹ = pᵏ · p : the divisibility that makes reduction well-defined. *)
let ppow_succ (p:int{p > 1}) (k:nat)
  : Lemma (ppow p (k ++ 1) == ppow p k `Prims.op_Star` p)
  = ()  (* ppow p (k+1) = p * ppow p k, and Z3 closes the commutativity. *)

let reduce_step_zero (p:int{p > 1}) (k:pos)
  : Lemma (reduce_step p k (zmod_zero (ppow p (k ++ 1))) == zmod_zero (ppow p k))
  = ppow_gt_one p k;
    small_mod 0 (ppow p k)

let reduce_step_one (p:int{p > 1}) (k:pos)
  : Lemma (reduce_step p k (zmod_one (ppow p (k ++ 1))) == zmod_one (ppow p k))
  = ppow_gt_one p k;
    small_mod 1 (ppow p k)

let reduce_step_add (p:int{p > 1}) (k:pos) (a b: zmod (ppow p (k ++ 1)))
  : Lemma (reduce_step p k (zmod_add #(ppow p (k ++ 1)) a b)
           == zmod_add #(ppow p k) (reduce_step p k a) (reduce_step p k b))
  = ppow_gt_one p k;
    ppow_succ p k;
    (* m1 = m * p, so ((a+b) % m1) % m == (a+b) % m. *)
    modulo_modulo_lemma (zv a + zv b) (ppow p k) p;
    (* (a+b) % m == ((a%m) + (b%m)) % m. *)
    modulo_distributivity (zv a) (zv b) (ppow p k)

let reduce_step_mul (p:int{p > 1}) (k:pos) (a b: zmod (ppow p (k ++ 1)))
  : Lemma (reduce_step p k (zmod_mul #(ppow p (k ++ 1)) a b)
           == zmod_mul #(ppow p k) (reduce_step p k a) (reduce_step p k b))
  = ppow_gt_one p k;
    ppow_succ p k;
    (* m1 = m * p, so ((a*b) % m1) % m == (a*b) % m. *)
    modulo_modulo_lemma (zv a * zv b) (ppow p k) p;
    (* (a*b) % m == ((a%m)*b) % m == ((a%m)*(b%m)) % m. *)
    lemma_mod_mul_distr_l (zv a) (zv b) (ppow p k);
    lemma_mod_mul_distr_r (zv a % ppow p k) (zv b) (ppow p k)

(* ================================================================ *)
(*  §2  — poly_reduce ring-hom on polynomials (from HenselReducePoly) *)
(* ================================================================ *)

(* coefficient-wise reduction (zmod pᵏ⁺¹)[X] → (zmod pᵏ)[X]. *)
let poly_reduce (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  : polynomial (zmod (ppow p k))
  = trim #(zmod (ppow p k)) (L.map (reduce_step p k) f)

(* index of a mapped list:  index (map g l) i = g (index l i). *)
private let rec index_map_lemma (#a:Type) (#b:Type) (g: a -> b) (l: list a) (i:nat{i < L.length l})
  : Lemma (ensures (L.map_lemma g l; L.index (L.map g l) i == g (L.index l i)))
          (decreases i)
  = L.map_lemma g l;
    if i = 0 then ()
    else index_map_lemma g (L.tl l) (i - 1)

(* coeff characterisation:  coeff (poly_reduce f) i = reduce_step (coeff f i). *)
let poly_reduce_coeff (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1)))) (i:int)
  : Lemma (coeff (poly_reduce p k f) i
           == reduce_step p k (coeff f i))
  = let g = reduce_step p k in
    let mapped : list (zmod (ppow p k)) = L.map g f in
    L.map_lemma g f;                            (* length (map g f) == length f *)
    (* poly_reduce p k f == trim mapped *)
    if i < 0 then begin
      (* both sides are the zero of zmod (ppow p k):
         lhs = coeff (trim mapped) i = zero (i<0);
         rhs = reduce_step (zero @ zmod (ppow p (k+1))) = reduce_step (zmod_zero (ppow p (k+1)))
             = zmod_zero (ppow p k) = zero. *)
      reduce_step_zero p k
    end
    else begin
      let i : nat = i in
      coeff_trim #(zmod (ppow p k)) mapped i;
      (* coeff (trim mapped) i = (if i < length mapped then index mapped i else zero) *)
      if i < L.length f then begin
        (* lhs = index mapped i = g (index f i) = reduce_step (coeff f i) *)
        index_map_lemma g f i
      end
      else begin
        (* lhs = zero = zmod_zero (ppow p k);
           rhs = reduce_step (coeff f i) = reduce_step (zmod_zero (ppow p (k+1))) = zmod_zero (ppow p k) *)
        reduce_step_zero p k
      end
    end

(* --- ring-hom laws (poly_eq in the target ring (zmod pᵏ)[X]) --- *)

(* Bridge: the ring `+` on (zmod m) IS zmod_add (the .add field of zmod_acg m). *)
private let zmod_ring_add_reveal (m:int{m > 1}) (a b: zmod m)
  : Lemma (add a b == zmod_add #m a b)
  = ()

(* Bridge: the ring `*` on (zmod m) IS zmod_mul. *)
private let zmod_ring_mul_reveal (m:int{m > 1}) (a b: zmod m)
  : Lemma (mul a b == zmod_mul #m a b)
  = ()

(* Per-coefficient additivity. *)
private let poly_reduce_add_coeff (p:int{p > 1}) (k:pos)
  (f g: polynomial (zmod (ppow p (k ++ 1)))) (j:nat)
  : Lemma (coeff
              (poly_reduce p k (f + g)) j
           == coeff
                ((poly_reduce p k f) + (poly_reduce p k g)) j)
  = let m1 = ppow p (k ++ 1) in
    let m  = ppow p k in
    let cf = coeff f j in
    let cg = coeff g j in
    (* LHS *)
    poly_reduce_coeff p k (f + g) j;
    poly_add_coeff f g j;                              (* SMTPat: coeff(f+g) j == cf + cg (ring add) *)
    zmod_ring_add_reveal m1 cf cg;                      (* cf + cg == zmod_add cf cg *)
    reduce_step_add p k cf cg;                          (* reduce_step (zmod_add cf cg) == zmod_add (rs cf) (rs cg) *)
    poly_reduce_coeff p k f j;                          (* rs cf == coeff (poly_reduce f) j *)
    poly_reduce_coeff p k g j;                          (* rs cg == coeff (poly_reduce g) j *)
    (* RHS *)
    poly_add_coeff (poly_reduce p k f) (poly_reduce p k g) j;
    zmod_ring_add_reveal m (coeff (poly_reduce p k f) j)
                          (coeff (poly_reduce p k g) j)

let poly_reduce_add (p:int{p > 1}) (k:pos)
  (f g: polynomial (zmod (ppow p (k ++ 1))))
  : Lemma ((poly_reduce p k (f + g))
           = ((poly_reduce p k f) + (poly_reduce p k g)))
  = let lhs : polynomial (zmod (ppow p k)) = poly_reduce p k (f + g) in
    let rhs : polynomial (zmod (ppow p k)) = (poly_reduce p k f) + (poly_reduce p k g) in
    let aux (j:nat)
      : Lemma (coeff lhs j
               = coeff rhs j)
      = poly_reduce_add_coeff p k f g j in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* poly_reduce respects poly_eq (congruence). *)
let poly_reduce_congr (p:int{p > 1}) (k:pos)
  (a b: polynomial (zmod (ppow p (k ++ 1))))
  : Lemma (requires a = b)
          (ensures  (poly_reduce p k a) = (poly_reduce p k b))
  = let m = ppow p k in
    let aux (i:nat)
      : Lemma (coeff (poly_reduce p k a) i = coeff (poly_reduce p k b) i)
      = poly_reduce_coeff p k a i;                 (* coeff (reduce a) i == reduce_step (coeff a i) *)
        poly_reduce_coeff p k b i;
        poly_eq_means_equal_coeffs a b i;           (* coeff a i = coeff b i, hence == *)
        H.elim_equatable_laws (zmod m) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_reduce p k a) (poly_reduce p k b)

(* reduce_step pushes through a finite sum (additivity ⇒ hom over sum_range).
   `hh` carries the per-term image; the pointwise hypothesis avoids a lambda
   in the signature. *)
private let rec reduce_step_sum_range (p:int{p > 1}) (k:pos)
  (gg: nat -> zmod (ppow p (k ++ 1))) (hh: nat -> zmod (ppow p k))
  (pf: (i:nat) -> Lemma (hh i == reduce_step p k (gg i))) (a b: nat)
  : Lemma (ensures reduce_step p k (sum_range #(zmod (ppow p (k ++ 1))) gg a b)
                   == sum_range #(zmod (ppow p k)) hh a b)
          (decreases (b - a))
  = let m1 = ppow p (k ++ 1) in
    let m  = ppow p k in
    if a >= b then begin
      sum_range_empty #(zmod m1) gg a b;        (* sum = zero = zmod_zero m1 *)
      sum_range_empty #(zmod m) hh a b;          (* sum = zero = zmod_zero m *)
      reduce_step_zero p k                            (* reduce_step (zmod_zero m1) == zmod_zero m *)
    end
    else begin
      let tailsum1 = sum_range #(zmod m1) gg (a ++ 1) b in
      sum_range_unfold_left #(zmod m1) gg a b;  (* sum_range gg a b == gg a `+` tailsum1 *)
      (* ring add m1 == zmod_add *)
      zmod_ring_add_reveal m1 (gg a) tailsum1;        (* gg a + tailsum1 == zmod_add (gg a) tailsum1 *)
      reduce_step_add p k (gg a) tailsum1;            (* reduce_step (zmod_add ..) == zmod_add (rs (gg a)) (rs tailsum1) *)
      reduce_step_sum_range p k gg hh pf (a ++ 1) b;   (* rs tailsum1 == sum_range hh (a+1) b *)
      pf a;                                           (* rs (gg a) == hh a *)
      sum_range_unfold_left #(zmod m) hh a b;    (* sum_range hh a b == hh a `+` sum_range hh (a+1) b *)
      zmod_ring_add_reveal m (hh a) (sum_range #(zmod m) hh (a ++ 1) b)
    end

(* Convolution summand for f*g at output index j (source ring). *)
private let conv_src (p:int{p > 1}) (k:pos)
  (f g: polynomial (zmod (ppow p (k ++ 1)))) (j:nat) (i:nat)
  : zmod (ppow p (k ++ 1))
  = mul
      (coeff f i)
      (coeff g ((j - i)))

(* Convolution summand for (reduce f)*(reduce g) at output index j (target ring). *)
private let conv_tgt (p:int{p > 1}) (k:pos)
  (f g: polynomial (zmod (ppow p (k ++ 1)))) (j:nat) (i:nat)
  : zmod (ppow p k)
  = mul
      (coeff (poly_reduce p k f) i)
      (coeff (poly_reduce p k g) ((j - i)))

(* Per-term: reduce_step of a source summand is the target summand. *)
private let conv_term_reduce (p:int{p > 1}) (k:pos)
  (f g: polynomial (zmod (ppow p (k ++ 1)))) (j:nat) (i:nat)
  : Lemma (conv_tgt p k f g j i == reduce_step p k (conv_src p k f g j i))
  = let m1 = ppow p (k ++ 1) in
    let m  = ppow p k in
    let ji = (j - i) in
    let cf = coeff f i in
    let cg = coeff g ji in
    (* conv_src = cf * cg (ring mul m1) = zmod_mul cf cg *)
    zmod_ring_mul_reveal m1 cf cg;
    reduce_step_mul p k cf cg;                  (* reduce_step (zmod_mul cf cg) == zmod_mul (rs cf) (rs cg) *)
    poly_reduce_coeff p k f i;                  (* rs cf == coeff (poly_reduce f) i *)
    poly_reduce_coeff p k g ji;                 (* rs cg == coeff (poly_reduce g) (j-i) *)
    zmod_ring_mul_reveal m
      (coeff (poly_reduce p k f) i)
      (coeff (poly_reduce p k g) ji)

(* The "extra" target summands beyond length (poly_reduce f) vanish:
   coeff (poly_reduce f) i == zero there, so the product is zero. *)
private let conv_tgt_high_zero (p:int{p > 1}) (k:pos)
  (f g: polynomial (zmod (ppow p (k ++ 1)))) (j:nat)
  (i:nat{i >= L.length (poly_reduce p k f)})
  : Lemma ((eq
              (conv_tgt p k f g j i)
              (zero <: zmod (ppow p k))))
  = let m = ppow p k in
    (* coeff (poly_reduce f) i == zero (above length) *)
    let cfr = coeff (poly_reduce p k f) i in
    let cgr = coeff (poly_reduce p k g) ((j - i)) in
    (* cfr == zero (out of range), so cfr * cgr == zmod_mul 0 cgr == 0 *)
    H.elim_equatable_laws (zmod m) ();
    zmod_ring_mul_reveal m cfr cgr

(* length (poly_reduce p k f) <= length f  (trim_length_le is Core.Polynomial's) *)
private let poly_reduce_length_le (p:int{p > 1}) (k:pos)
  (f: polynomial (zmod (ppow p (k ++ 1))))
  : Lemma (L.length (poly_reduce p k f) <= L.length f)
  = let g = reduce_step p k in
    L.map_lemma g f;                              (* length (map g f) == length f *)
    trim_length_le #(zmod (ppow p k)) (L.map g f)

(* The convolution target-sum is range-independent above length (poly_reduce f):
   summing conv_tgt to lenf equals summing to lenrf (extra terms are zero). *)
private let sum_range_hh_ranges (p:int{p > 1}) (k:pos)
  (f g: polynomial (zmod (ppow p (k ++ 1)))) (j:nat)
  : Lemma (sum_range #(zmod (ppow p k))
              (conv_tgt p k f g j) 0 (L.length f)
           == sum_range #(zmod (ppow p k))
                (conv_tgt p k f g j) 0 (L.length (poly_reduce p k f)))
  = let m  = ppow p k in
    let hh  = conv_tgt p k f g j in
    let lenf  = L.length f in
    let lenrf = L.length (poly_reduce p k f) in
    poly_reduce_length_le p k f;                  (* lenrf <= lenf *)
    H.elim_equatable_laws (zmod m) ();
    H.trans_for_calc (zmod m) ();
    (* sum 0 lenf == sum 0 lenrf + sum lenrf lenf *)
    sum_range_split #(zmod m) hh 0 lenrf lenf;
    (* sum lenrf lenf == zero *)
    let allzero (i:nat{lenrf <= i /\ i < lenf}) : Lemma (hh i = (zero <: zmod m)) =
      conv_tgt_high_zero p k f g j i in
    sum_range_all_zero #(zmod m) hh lenrf lenf allzero;
    (* (sum 0 lenrf) + zero == sum 0 lenrf *)
    H.x_plus_zero #(zmod m) (sum_range #(zmod m) hh 0 lenrf)

(* Per-coefficient multiplicativity. *)
private let poly_reduce_mul_coeff (p:int{p > 1}) (k:pos)
  (f g: polynomial (zmod (ppow p (k ++ 1)))) (j:nat)
  : Lemma (coeff
              (poly_reduce p k (f * g)) j
           == coeff
                ((poly_reduce p k f) * (poly_reduce p k g)) j)
  = let m1 = ppow p (k ++ 1) in
    let m  = ppow p k in
    let lenf  = L.length f in
    let lenrf = L.length (poly_reduce p k f) in
    let gg = conv_src p k f g j in
    let hh = conv_tgt p k f g j in
    (* ---- LHS ---- *)
    poly_reduce_coeff p k (f * g) j;                    (* coeff(reduce(f*g)) j == rs (coeff (f*g) j) *)
    (* coeff_poly_mul_named bridges to the NAMED summand gg internally (sum_range_congruence). *)
    let cong1 (i:nat) : Lemma (gg i = mul (coeff #(zmod m1) f i) (coeff #(zmod m1) g ((j - i)))) =
      H.elim_equatable_laws (zmod m1) () in
    coeff_poly_mul_named #(zmod m1) f g j gg cong1;            (* coeff (f*g) j == sum_range gg 0 lenf *)
    (* reduce_step pushes through the sum *)
    let hyp (i:nat) : Lemma (hh i == reduce_step p k (gg i)) = conv_term_reduce p k f g j i in
    reduce_step_sum_range p k gg hh hyp 0 lenf;                 (* rs (sum gg 0 lenf) == sum hh 0 lenf *)
    (* ---- RHS ---- *)
    let cong2 (i:nat) : Lemma (hh i = mul (coeff #(zmod m) (poly_reduce p k f) i)
                                          (coeff #(zmod m) (poly_reduce p k g) ((j - i)))) =
      H.elim_equatable_laws (zmod m) () in
    coeff_poly_mul_named #(zmod m) (poly_reduce p k f) (poly_reduce p k g) j hh cong2; (* coeff(rf*rg) j == sum_range hh 0 lenrf *)
    (* bridge the two sum ranges: sum hh 0 lenf == sum hh 0 lenrf, extra terms zero *)
    sum_range_hh_ranges p k f g j

let poly_reduce_mul (p:int{p > 1}) (k:pos)
  (f g: polynomial (zmod (ppow p (k ++ 1))))
  : Lemma ((poly_reduce p k (f * g))
           = ((poly_reduce p k f) * (poly_reduce p k g)))
  = let lhs : polynomial (zmod (ppow p k)) = poly_reduce p k (f * g) in
    let rhs : polynomial (zmod (ppow p k)) = (poly_reduce p k f) * (poly_reduce p k g) in
    let aux (j:nat)
      : Lemma (coeff lhs j = coeff rhs j)
      = poly_reduce_mul_coeff p k f g j in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* ================================================================ *)
(*  §3  — the error-QUOTIENT map  (from HenselQuotient)              *)
(* ================================================================ *)

(* cancellation: pk>0, pk·q < pk·p  ⇒  q < p. *)
private let mul_cancel_lt (pk:pos) (q:nat) (p:int{p > 1})
  : Lemma (requires pk * q < pk * p) (ensures q < p)
  = if q < p then ()
    else begin
      (* q >= p  ⇒  pk*p <= pk*q, contradicting pk*q < pk*p *)
      lemma_mult_le_left pk p q
    end

(* a / pᵏ < p   (since a < pᵏ⁺¹ = pᵏ·p). *)
let qdiv_lt (p:int{p > 1}) (k:pos) (a: zmod (ppow p (k ++ 1)))
  : Lemma (zv a / (ppow p k) < p)
  = ppow_gt_one p k;                              (* ppow p k > 1 > 0 *)
    ppow_succ p k;                                (* ppow p (k+1) == ppow p k * p *)
    let pk : pos = ppow p k in
    multiply_fractions (zv a) pk;                 (* pk * (a / pk) <= a *)
    (* a < ppow p (k+1) == pk * p, so pk * (a/pk) <= a < pk * p *)
    mul_cancel_lt pk (zv a / pk) p

(* the quotient map  a ↦ a / pᵏ : zmod pᵏ⁺¹ → zmod p  (total). *)
let qdiv (p:int{p > 1}) (k:pos) (a: zmod (ppow p (k ++ 1))) : zmod p
  = qdiv_lt p k a; Zm (zv a / (ppow p k))

(* qdiv preserves zero. *)
let qdiv_zero (p:int{p > 1}) (k:pos)
  : Lemma (qdiv p k (zmod_zero (ppow p (k ++ 1))) == zmod_zero p)
  = ppow_gt_one p k;                              (* ppow p k > 0 *)
    small_div 0 (ppow p k)                        (* 0 / pᵏ == 0 == zmod_zero p *)

(* reconstruction:  if a is pᵏ-divisible then a = pᵏ · qdiv a. *)
let qdiv_correct (p:int{p > 1}) (k:pos) (a: zmod (ppow p (k ++ 1)))
  : Lemma (requires reduce_step p k a == zmod_zero (ppow p k))
          (ensures (zv a <: int) == (ppow p k) `Prims.op_Star` zv (qdiv p k a))
  = ppow_gt_one p k;                              (* ppow p k > 0 *)
    let pk : pos = ppow p k in
    (* reduce_step p k a == Zm (zv a % pk)  and  zmod_zero (ppow p k) == Zm 0
       ⇒  zv a % pk == 0 *)
    assert (reduce_step p k a == Zm (zv a % pk));
    assert (zv a % pk == 0);
    lemma_div_mod (zv a) pk;                       (* a == pk * (a / pk) + a % pk *)
    (* qdiv p k a == Zm (a / pk) (qdiv_lt is the only side-effect of qdiv) *)
    qdiv_lt p k a

(* coefficient-wise quotient on polynomials. *)
let poly_quotient (p:int{p > 1}) (k:pos)
  (e: polynomial (zmod (ppow p (k ++ 1))))
  : polynomial (zmod p)
  = trim #(zmod p) (L.map (qdiv p k) e)

(* coeff characterisation:  coeff (poly_quotient e) i = qdiv (coeff e i). *)
let poly_quotient_coeff (p:int{p > 1}) (k:pos)
  (e: polynomial (zmod (ppow p (k ++ 1)))) (i:int)
  : Lemma (coeff (poly_quotient p k e) i
           == qdiv p k (coeff e i))
  = let g = qdiv p k in
    let mapped : list (zmod p) = L.map g e in
    L.map_lemma g e;                            (* length (map g e) == length e *)
    (* poly_quotient p k e == trim mapped *)
    if i < 0 then begin
      (* lhs = coeff (trim mapped) i = zero (i<0) = zmod_zero p;
         rhs = qdiv (coeff e i) = qdiv (zmod_zero (ppow p (k+1))) = zmod_zero p *)
      qdiv_zero p k
    end
    else begin
      let i : nat = i in
      coeff_trim #(zmod p) mapped i;
      (* coeff (trim mapped) i = (if i < length mapped then index mapped i else zero) *)
      if i < L.length e then begin
        (* lhs = index mapped i = g (index e i) = qdiv (coeff e i) *)
        index_map_lemma g e i
      end
      else begin
        (* lhs = zero = zmod_zero p;
           rhs = qdiv (coeff e i) = qdiv (zmod_zero (ppow p (k+1))) = zmod_zero p *)
        qdiv_zero p k
      end
    end

(* ================================================================ *)
(*  §4  — the pᵏ-SCALING map + error reconstruction (from HenselScale)*)
(* ================================================================ *)

(* pᵏ·d < pᵏ⁺¹   (since d < p). *)
let mulpk_lt (p:int{p > 1}) (k:pos) (d: zmod p)
  : Lemma ((ppow p k) `Prims.op_Star` zv d < ppow p (k ++ 1))
  = ppow_gt_one p k;                              (* ppow p k > 1 > 0 *)
    ppow_succ p k;                                (* ppow p (k+1) == ppow p k * p *)
    let pk : pos = ppow p k in
    (* d < p and pk > 0  ⇒  pk*d < pk*p == ppow p (k+1) *)
    lemma_mult_lt_left pk (zv d) p

(* the scaling map  d ↦ pᵏ·d : zmod p → zmod pᵏ⁺¹. *)
let mulpk (p:int{p > 1}) (k:pos) (d: zmod p) : zmod (ppow p (k ++ 1))
  = mulpk_lt p k d; Zm ((ppow p k) `Prims.op_Star` zv d)

let mulpk_zero (p:int{p > 1}) (k:pos)
  : Lemma (mulpk p k (zmod_zero p) == zmod_zero (ppow p (k ++ 1)))
  = (* mulpk p k 0 == Zm (ppow p k * 0) == Zm 0 == zmod_zero (ppow p (k+1)) *)
    ()

(* mulpk ∘ qdiv = id on pᵏ-divisible elements:  reduce a = 0 ⇒ a = pᵏ·(a/pᵏ). *)
let mulpk_qdiv (p:int{p > 1}) (k:pos) (a: zmod (ppow p (k ++ 1)))
  : Lemma (requires reduce_step p k a == zmod_zero (ppow p k))
          (ensures mulpk p k (qdiv p k a) == a)
  = (* qdiv_correct:  (zv a <: int) == ppow p k * zv (qdiv p k a).
       mulpk p k (qdiv p k a) == Zm (ppow p k * zv (qdiv p k a)) == Zm (zv a) == a. *)
    qdiv_correct p k a

(* coefficient-wise scaling on polynomials. *)
let poly_mulpk (p:int{p > 1}) (k:pos)
  (d: polynomial (zmod p))
  : polynomial (zmod (ppow p (k ++ 1)))
  = trim #(zmod (ppow p (k ++ 1))) (L.map (mulpk p k) d)

(* coeff characterisation. *)
let poly_mulpk_coeff (p:int{p > 1}) (k:pos)
  (d: polynomial (zmod p)) (i:int)
  : Lemma (coeff (poly_mulpk p k d) i
           == mulpk p k (coeff d i))
  = let g = mulpk p k in
    let mapped : list (zmod (ppow p (k ++ 1))) = L.map g d in
    L.map_lemma g d;                            (* length (map g d) == length d *)
    (* poly_mulpk p k d == trim mapped *)
    if i < 0 then begin
      (* lhs = coeff (trim mapped) i = zero (i<0) = zmod_zero (ppow p (k+1));
         rhs = mulpk (coeff d i) = mulpk (zmod_zero p) = zmod_zero (ppow p (k+1)) *)
      mulpk_zero p k
    end
    else begin
      let i : nat = i in
      coeff_trim #(zmod (ppow p (k ++ 1))) mapped i;
      (* coeff (trim mapped) i = (if i < length mapped then index mapped i else zero) *)
      if i < L.length d then begin
        (* lhs = index mapped i = g (index d i) = mulpk (coeff d i) *)
        index_map_lemma g d i
      end
      else begin
        (* lhs = zero = zmod_zero (ppow p (k+1));
           rhs = mulpk (coeff d i) = mulpk (zmod_zero p) = zmod_zero (ppow p (k+1)) *)
        mulpk_zero p k
      end
    end

(* ERROR RECONSTRUCTION:  poly_reduce e = 0  ⇒  e = poly_mulpk (poly_quotient e). *)
let error_reconstruction (p:int{p > 1}) (k:pos)
  (e: polynomial (zmod (ppow p (k ++ 1))))
  : Lemma (requires (poly_reduce p k e)
                    = (poly_zero #(zmod (ppow p k))))
          (ensures e
                   = (poly_mulpk p k (poly_quotient p k e)))
  = let m  = ppow p k in
    let rhs = poly_mulpk p k (poly_quotient p k e) in
    (* discharge mulpk_qdiv's precondition at index i, then match coeffs. *)
    let aux (i:nat)
      : Lemma (coeff e i = coeff rhs i)
      = (* reduce_step (coeff e i) == zmod_zero m, from the hypothesis. *)
        poly_reduce_coeff p k e i;                 (* coeff (poly_reduce e) i == reduce_step (coeff e i) *)
        poly_eq_means_equal_coeffs
          (poly_reduce p k e)
          (poly_zero #(zmod m)) i; (* coeff (poly_reduce e) i = coeff poly_zero i == 0 *)
        (* now rebuild rhs coeff *)
        poly_mulpk_coeff p k (poly_quotient p k e) i;  (* coeff rhs i == mulpk (coeff (poly_quotient e) i) *)
        poly_quotient_coeff p k e i;                   (* coeff (poly_quotient e) i == qdiv (coeff e i) *)
        mulpk_qdiv p k (coeff e i)  (* mulpk (qdiv (coeff e i)) == coeff e i *)
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq e rhs
