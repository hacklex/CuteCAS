module Core.Polynomial.EmbedQ

(* ================================================================ *)
(*  §D — the canonical coefficient-wise embedding ring-hom:          *)
(*    embed_zq : ℤ[X] → ℚ[X]   (coefficient-wise n ↦ n/1)            *)
(*  is a ring homomorphism (preserves 0, +, ·) and is injective      *)
(*  (preserves degree).                                              *)
(*                                                                   *)
(*  Built on the base embedding ℤ → ℚ = `n ↦ Fraction n one`         *)
(*  (the canonical embedding into the fraction field).  Modeled      *)
(*  EXACTLY on `Core.Modular.ResidueRing.Hensel.Reduce.poly_reduce`:        *)
(*    trim (L.map fn l) + coeff_trim + index_map_lemma + the         *)
(*    out-of-range-zero case for the coeff lemma; ring-hom MUL via    *)
(*    pushing through coeff_poly_mul's convolution with a            *)
(*    *_sum_range helper + named convolution summands.               *)
(*                                                                   *)
(*  Difference from the template: the base hom laws hold only up to   *)
(*  the fraction equatable `=` (cross-multiplication), not `==`, so   *)
(*  the per-coefficient bridges use `=` and the coeff characterisation*)
(*  carries `==` only structurally.                                  *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Eval
open Core.Fractions
open Core.FinSum

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  ℚ and its commutative_ring, reached from the single published   *)
(*  `fraction_field int int_id` via the foundation chain            *)
(*  id_of_f ∘ cr_of_id (mirrors Core.Fractions.DerivationInstance). *)
(* ---------------------------------------------------------------- *)

let qq : Type = fraction int_id

let crq : commutative_ring qq =
  cr_of_id (fraction int_id) #(id_of_f (fraction int_id) #(fraction_field int int_id))

(* ---------------------------------------------------------------- *)
(*  The base embedding ℤ → ℚ : n ↦ n/1.                              *)
(*  The denominator `one #int` is nonzero by `int_id.id_one_ne_zero`.*)
(* ---------------------------------------------------------------- *)

let embed_zq_const (n: int) : fraction int_id =
  let _: squash (not ((one <: int) = (zero <: int))) = int_id.id_one_ne_zero in
  Fraction #int #int_id n (one <: int)

(* The coefficient-wise embedding ℤ[X] → ℚ[X]. *)
let embed_zq (p: polynomial int #int_cr) : polynomial qq #crq =
  trim (L.map embed_zq_const p)

(* ---------------------------------------------------------------- *)
(*  Base-hom bridges (mirror reduce_step_zero/add/mul).              *)
(* ---------------------------------------------------------------- *)

(* embed_zq_const 0 equals the ring zero of ℚ up to the fraction
   equatable `=` (cross-multiplication).  The published `fraction_field`
   instance is abstract, so we cannot reduce the projected zero to
   `Fraction 0 1`; instead we pin its numerator via the additive-identity
   law: (0/1 + z) = 0/1 forces num z = 0, hence z = 0/1 = embed_zq_const 0. *)
let embed_zq_const_zero (_:unit)
  : Lemma (embed_zq_const 0 = crq.cr_r.r_add.zero)
  = let fz = fraction_zero int #int_id in
    let z  = crq.cr_r.r_add.zero in
    H.x_plus_zero fz;  (* (fz + z) =eq= fz *)
    fraction_ring_add_reveal fz z;             (* fz + z == fraction_add fz z *)
    fraction_add_reveal fz z;
    fraction_zero_reveal int #int_id;
    fraction_eq_reveal (fraction_add fz z) fz;
    (* now num z == 0 *)
    fraction_eq_reveal (embed_zq_const 0) z

(* The ring `+` on ℚ (resolved through crq) IS fraction_add:
   crq.cr_r.r_add.add a b == a + b (projection defeq) and
   a + b == fraction_add a b (published reveal). *)
private let qq_ring_add_reveal (a b: qq)
  : Lemma (crq.cr_r.r_add.add a b == fraction_add a b)
  = fraction_ring_add_reveal a b

(* The ring `*` on ℚ (resolved through crq) IS fraction_mul. *)
private let qq_ring_mul_reveal (a b: qq)
  : Lemma (crq.cr_r.mul a b == fraction_mul a b)
  = fraction_ring_mul_reveal a b

(* Base additivity (up to fraction `=`):
     (a/1) + (b/1) = (a*1 + 1*b)/(1*1) = (a+b)/1. *)
let embed_zq_const_add (a b: int)
  : Lemma (fraction_add (embed_zq_const a) (embed_zq_const b)
           = embed_zq_const (a ++ b))
  = let x = embed_zq_const a in
    let y = embed_zq_const b in
    let s = fraction_add x y in
    fraction_add_reveal x y;
    (* num s = a*1 + 1*b = a + b ; den s = 1*1 = 1 *)
    fraction_eq_reveal s (embed_zq_const (a ++ b))
    (* s = (a+b)/1  iff  num s * 1 = den s * (a+b)
         iff  (a*1+1*b) * 1 = (1*1) * (a+b)  — true integer arithmetic. *)

(* Base multiplicativity (up to fraction `=`):
     (a/1) * (b/1) = (a*b)/(1*1) = (a*b)/1. *)
let embed_zq_const_mul (a b: int)
  : Lemma (fraction_mul (embed_zq_const a) (embed_zq_const b)
           = embed_zq_const (Prims.op_Star a b))
  = let x = embed_zq_const a in
    let y = embed_zq_const b in
    let s = fraction_mul x y in
    fraction_mul_reveal x y;
    fraction_eq_reveal s (embed_zq_const (Prims.op_Star a b))

(* embed_zq_const is injective: n/1 = 0/1 iff n = 0. *)
let embed_zq_const_zero_iff (n: int)
  : Lemma ((embed_zq_const n = crq.cr_r.r_add.zero) <==> n == 0)
  = let en = embed_zq_const n in
    let z  = crq.cr_r.r_add.zero in
    embed_zq_const_zero ();                       (* embed_zq_const 0 = z *)
    H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    fraction_eq_reveal en (embed_zq_const 0)  (* (en = embed 0) <==> n = 0 *)
    (* en = z  <==>  en = embed_zq_const 0  (since embed_zq_const 0 = z, transitivity);
       and (en = embed_zq_const 0) <==> n = 0. *)

(* ---------------------------------------------------------------- *)
(*  1. Coefficient characterisation (mirror poly_reduce_coeff).      *)
(* ---------------------------------------------------------------- *)

(* index of a mapped list:  index (map g l) i = g (index l i). *)
private let rec index_map_lemma (#a:Type) (#b:Type) (g: a -> b) (l: list a) (i:nat{i < L.length l})
  : Lemma (ensures (L.map_lemma g l; L.index (L.map g l) i == g (L.index l i)))
          (decreases i)
  = L.map_lemma g l;
    if i = 0 then ()
    else index_map_lemma g (L.tl l) (i - 1)

(* Coefficient characterisation up to the fraction equatable `=`:
   in range it is a genuine `==` (list index), out of range both sides
   are the ring zero / embed_zq_const 0, related by `embed_zq_const_zero`. *)
let embed_zq_coeff (p: polynomial int #int_cr) (i:int)
  : Lemma (crq.cr_r.r_add.acg_eq.eq
             (coeff (embed_zq p) i)
             (embed_zq_const (coeff p i)))
  = let g = embed_zq_const in
    let mapped : list qq = L.map g p in
    let z = crq.cr_r.r_add.zero in
    L.map_lemma g p;                            (* length (map g p) == length p *)
    H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    if i < 0 then
      (* lhs == z (coeff refinement); coeff p i == 0 so rhs == embed_zq_const 0;
         embed_zq_const 0 = z ⇒ z =eq= embed_zq_const 0 by symmetry. *)
      embed_zq_const_zero ()                      (* embed_zq_const 0 = z; symm closes *)
    else begin
      let i : nat = i in
      coeff_trim mapped i;
      (* coeff (trim mapped) i = (if i < length mapped then index mapped i else z) *)
      if i < L.length p then
        (* coeff(embed p) i =eq= index mapped i (coeff_trim);
           index mapped i == g (index p i) == embed_zq_const (coeff p i) (index_map_lemma). *)
        index_map_lemma g p i
      else
        (* coeff(embed p) i =eq= z (coeff_trim out of range); coeff p i == 0 ⇒
           rhs == embed_zq_const 0; z =eq= embed_zq_const 0 closes. *)
        embed_zq_const_zero ()
    end

(* ---------------------------------------------------------------- *)
(*  2. Additivity (mirror poly_reduce_add).                          *)
(* ---------------------------------------------------------------- *)

(* The ring `+` on `int` IS integer addition. *)
private let int_ring_add_reveal (a b: int)
  : Lemma (int_cr.cr_r.r_add.add a b == a ++ b)
  = ()

(* The ring `*` on `int` IS integer multiplication. *)
private let int_ring_mul_reveal (a b: int)
  : Lemma (int_cr.cr_r.mul a b == Prims.op_Star a b)
  = ()

private let embed_zq_add_coeff (p q: polynomial int #int_cr) (j:nat)
  : Lemma (coeff (embed_zq (p + q)) j
           = coeff
               (poly_add (embed_zq p) (embed_zq q)) j)
  = let cp = coeff p j in
    let cq = coeff q j in
    let ep = embed_zq p in
    let eq_ = embed_zq q in
    let ecp = embed_zq_const cp in
    let ecq = embed_zq_const cq in
    H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let lc = coeff (embed_zq (p + q)) j in
    let rc = coeff (poly_add ep eq_) j in
    (* ---- LHS: lc =eq= embed_zq_const (cp + cq) ---- *)
    embed_zq_coeff (p + q) j;   (* lc =eq= embed_zq_const (coeff(p+q) j) *)
    poly_add_coeff p q j;              (* coeff(p+q) j = cp + cq (int =, i.e. ==) *)
    int_ring_add_reveal cp cq;                      (* cp +_int cq == cp + cq (Prims) *)
    (* coeff(p+q) j == cp + cq ⇒ embed_zq_const (coeff(p+q)j) == embed_zq_const (cp+cq) *)
    (* ---- RHS: rc =eq= ecp + ecq ---- *)
    poly_add_coeff ep eq_ j;               (* rc = (coeff ep j) + (coeff eq_ j) *)
    embed_zq_coeff p j;                             (* coeff ep j =eq= ecp *)
    embed_zq_coeff q j;                             (* coeff eq_ j =eq= ecq *)
    add_congruence
      (coeff ep j) (coeff eq_ j) ecp ecq;   (* (cep)+(ceq) =eq= ecp+ecq *)
    qq_ring_add_reveal ecp ecq;                     (* ecp + ecq == fraction_add ecp ecq *)
    embed_zq_const_add cp cq;                       (* fraction_add ecp ecq =eq= embed_zq_const (cp+cq) *)
    (* chain rc =eq= ecp+ecq == fraction_add ecp ecq =eq= embed_zq_const (cp+cq) =eq= lc *)
    ()

let embed_zq_add (p q: polynomial int #int_cr)
  : Lemma (poly_eq
             (embed_zq (p + q))
             (poly_add (embed_zq p) (embed_zq q)))
  = let lhs = embed_zq (p + q) in
    let rhs = poly_add (embed_zq p) (embed_zq q) in
    let aux (j:nat)
      : Lemma (coeff lhs j = coeff rhs j)
      = embed_zq_add_coeff p q j in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* ---------------------------------------------------------------- *)
(*  5. Degree preservation (the hom is injective coeff-wise, so      *)
(*     trim removes exactly the same trailing zeros).                *)
(* ---------------------------------------------------------------- *)

(* The mapped list before trimming has the same length as p. *)
private let embed_map_length (p: polynomial int #int_cr)
  : Lemma (L.length (L.map embed_zq_const p) == L.length p)
  = L.map_lemma embed_zq_const p

(* last of a mapped list is the map of the last element.  Generic list fact;
   a twin (last_map) lives in Core.AlgebraicConstant.EmbedTransport — this
   module cannot import the AlgebraicConstant tower (layering), and no shared
   list-helpers module exists, so both copies stay (cross-referenced). *)
#push-options "--fuel 2 --ifuel 2"
private let rec last_map_lemma (#a:Type) (#b:Type) (g: a -> b) (l: list a{Cons? l})
  : Lemma (ensures (L.map_lemma g l; L.last (L.map g l) == g (L.last l)))
          (decreases l)
  = L.map_lemma g l;
    match l with
    | [_] -> ()
    | _ :: tl -> last_map_lemma g tl
#pop-options

(* The mapped list is already trimmed in ℚ: its last element is
   embed_zq_const (last p), which is nonzero since last p is nonzero
   (p is trimmed) and embed_zq_const is injective. *)
private let embed_map_is_trimmed (p: polynomial int #int_cr)
  : Lemma (is_trimmed (L.map embed_zq_const p))
  = embed_map_length p;
    if L.length p = 0 then ()
    else begin
      last_map_lemma embed_zq_const p;
      (* L.last (map g p) == embed_zq_const (L.last p) *)
      let lp : int = L.last p in
      (* p is trimmed ⇒ lp <> (zero<:int) ⇒ lp <> 0 *)
      assert (is_trimmed p);
      assert (lp <> (zero <: int));
      (* injectivity: embed_zq_const lp = zero_qq iff lp = 0 *)
      embed_zq_const_zero_iff lp;
      H.elim_equatable_laws qq ();
      (* so embed_zq_const lp <> (zero<:qq), i.e. L.last (map g p) <> zero in ℚ *)
      ()
    end

(* embed_zq p IS the mapped list (trim is a no-op:
   Core.Polynomial.trim_poly_does_nothing). *)
private let embed_zq_no_trim (p: polynomial int #int_cr)
  : Lemma (embed_zq p == L.map embed_zq_const p)
  = embed_map_is_trimmed p;
    trim_poly_does_nothing (L.map embed_zq_const p)

(* embed_zq preserves the underlying list length. *)
let embed_zq_length_eq (p: polynomial int #int_cr)
  : Lemma (L.length (embed_zq p) == L.length p)
  = embed_zq_no_trim p;
    embed_map_length p

(* degree is preserved. *)
let embed_zq_deg (p: polynomial int #int_cr)
  : Lemma (deg (embed_zq p) == deg p)
  = embed_zq_length_eq p

(* ---------------------------------------------------------------- *)
(*  3. Multiplicativity (mirror poly_reduce_mul).                    *)
(* ---------------------------------------------------------------- *)

(* Base additivity in the qq RING `+` form:
     embed_zq_const (a +_int b) =eq= embed_zq_const a + embed_zq_const b. *)
private let embed_const_add_ring (a b: int)
  : Lemma (crq.cr_r.r_add.acg_eq.eq
             (embed_zq_const (int_cr.cr_r.r_add.add a b))
             (crq.cr_r.r_add.add (embed_zq_const a) (embed_zq_const b)))
  = H.elim_equatable_laws qq ();
    int_ring_add_reveal a b;                    (* a +_int b == a + b (Prims) *)
    embed_zq_const_add a b;                     (* fraction_add (ea) (eb) =eq= embed (a+b) *)
    qq_ring_add_reveal (embed_zq_const a) (embed_zq_const b)
    (* (ea) + (eb) == fraction_add (ea) (eb) =eq= embed (a+b) ⇒ symm. *)

(* Base multiplicativity in the qq RING `*` form:
     embed_zq_const (a *_int b) =eq= embed_zq_const a * embed_zq_const b. *)
private let embed_const_mul_ring (a b: int)
  : Lemma (crq.cr_r.r_add.acg_eq.eq
             (embed_zq_const (int_cr.cr_r.mul a b))
             (crq.cr_r.mul (embed_zq_const a) (embed_zq_const b)))
  = H.elim_equatable_laws qq ();
    int_ring_mul_reveal a b;                    (* a *_int b == a * b (Prims) *)
    embed_zq_const_mul a b;                     (* fraction_mul (ea) (eb) =eq= embed (a*b) *)
    qq_ring_mul_reveal (embed_zq_const a) (embed_zq_const b)

(* embed_zq_const pushes through a finite sum (additivity ⇒ hom over
   sum_range, up to the fraction equatable `=`).  `hh` carries the
   per-term image; the pointwise hypothesis avoids a lambda in the
   signature. *)
private let rec embed_sum_range (gg: nat -> int) (hh: nat -> qq) (a b: nat)
  : Lemma (requires (forall (i:nat). crq.cr_r.r_add.acg_eq.eq (hh i) (embed_zq_const (gg i))))
          (ensures crq.cr_r.r_add.acg_eq.eq
                     (embed_zq_const (sum_range #int #(int_cr.cr_r.r_add) gg a b))
                     (sum_range #qq #(crq.cr_r.r_add) hh a b))
          (decreases (b - a))
  = let acgi = int_cr.cr_r.r_add in
    let acgq = crq.cr_r.r_add in
    H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    if a >= b then begin
      sum_range_empty #int #acgi gg a b;        (* sum_int = zero_int = 0 *)
      sum_range_empty #qq #acgq hh a b;         (* sum_qq = crq.zero *)
      embed_zq_const_zero ()                    (* embed_zq_const 0 =eq= crq.zero *)
    end
    else begin
      let tailsum_i = sum_range #int #acgi gg (a ++ 1) b in
      let tailsum_q = sum_range #qq #acgq hh (a ++ 1) b in
      sum_range_unfold_left #int #acgi gg a b;   (* sum_i a b == gg a +_int tailsum_i *)
      sum_range_unfold_left #qq #acgq hh a b;    (* sum_q a b == hh a +_qq tailsum_q *)
      (* embed (gg a +_int tailsum_i) =eq= embed (gg a) +_qq embed tailsum_i *)
      embed_const_add_ring (gg a) tailsum_i;
      (* recursion: embed tailsum_i =eq= tailsum_q *)
      embed_sum_range gg hh (a ++ 1) b;
      (* hh a =eq= embed (gg a) from the hypothesis *)
      (* combine via add_congruence: embed (gg a) +_qq embed tailsum_i
                                     =eq= hh a +_qq tailsum_q *)
      add_congruence
        (embed_zq_const (gg a)) (embed_zq_const tailsum_i) (hh a) tailsum_q
    end

(* Convolution summand for p*q at output index j (source ring ℤ). *)
private let conv_src (p q: polynomial int #int_cr) (j:nat) (i:nat) : int
  = int_cr.cr_r.mul
      (coeff p i)
      (coeff q ((j - i)))

(* Convolution summand for (embed p)*(embed q) at output index j (ℚ). *)
private let conv_tgt (p q: polynomial int #int_cr) (j:nat) (i:nat) : qq
  = crq.cr_r.mul
      (coeff (embed_zq p) i)
      (coeff (embed_zq q) ((j - i)))

(* Per-term: embed_zq_const of a source summand =eq= the target summand. *)
private let conv_term_embed (p q: polynomial int #int_cr) (j:nat) (i:nat)
  : Lemma (crq.cr_r.r_add.acg_eq.eq
             (conv_tgt p q j i)
             (embed_zq_const (conv_src p q j i)))
  = let ji = (j - i) in
    let cp = coeff p i in
    let cq = coeff q ji in
    H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    (* embed (cp *_int cq) =eq= embed cp *_qq embed cq *)
    embed_const_mul_ring cp cq;
    (* coeff (embed p) i =eq= embed cp ; coeff (embed q) ji =eq= embed cq *)
    embed_zq_coeff p i;
    embed_zq_coeff q ji;
    mul_congruence
      (coeff (embed_zq p) i)
      (coeff (embed_zq q) ji)
      (embed_zq_const cp) (embed_zq_const cq)

(* The "extra" target summands beyond length (embed_zq p) vanish:
   coeff (embed_zq p) i =eq= crq.zero there, so the product is zero. *)
private let conv_tgt_high_zero (p q: polynomial int #int_cr) (j:nat)
  (i:nat{i >= L.length (embed_zq p)})
  : Lemma (crq.cr_r.r_add.acg_eq.eq
             (conv_tgt p q j i)
             (crq.cr_r.r_add.zero))
  = let ji = (j - i) in
    let cpr = coeff (embed_zq p) i in
    let cqr = coeff (embed_zq q) ji in
    H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    (* cpr =eq= crq.zero (out of range); so cpr * cqr =eq= zero * cqr =eq= zero *)
    mul_congruence cpr cqr (crq.cr_r.r_add.zero) cqr;     (* cpr*cqr =eq= 0*cqr *)
    H.zero_mul_x cqr                                       (* 0*cqr =eq= 0 *)

(* length (embed_zq p) <= length p (here actually ==, but <= suffices). *)
private let embed_length_le (p: polynomial int #int_cr)
  : Lemma (L.length (embed_zq p) <= L.length p)
  = embed_zq_length_eq p

(* The convolution target-sum is range-independent above length (embed p):
   summing conv_tgt to length p equals summing to length (embed p). *)
private let sum_range_hh_ranges (p q: polynomial int #int_cr) (j:nat)
  : Lemma (crq.cr_r.r_add.acg_eq.eq
             (sum_range #qq #(crq.cr_r.r_add) (conv_tgt p q j) 0 (L.length p))
             (sum_range #qq #(crq.cr_r.r_add) (conv_tgt p q j) 0 (L.length (embed_zq p))))
  = let acgq = crq.cr_r.r_add in
    let hh  = conv_tgt p q j in
    let lenp  = L.length p in
    let lenep = L.length (embed_zq p) in
    embed_length_le p;                          (* lenep <= lenp *)
    H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    sum_range_split #qq #acgq hh 0 lenep lenp;  (* sum 0 lenp =eq= sum 0 lenep + sum lenep lenp *)
    let allzero (i:nat{lenep <= i /\ i < lenp}) : Lemma (acgq.acg_eq.eq (hh i) acgq.zero) =
      conv_tgt_high_zero p q j i in
    sum_range_all_zero #qq #acgq hh lenep lenp allzero;  (* sum lenep lenp =eq= zero *)
    let s0 = sum_range #qq #acgq hh 0 lenep in
    let s1 = sum_range #qq #acgq hh lenep lenp in
    (* s0 + s1 =eq= s0 + zero  (add_congruence, since s1 =eq= zero) *)
    add_congruence s0 s1 s0 acgq.zero;
    H.x_plus_zero s0                  (* s0 + zero =eq= s0 *)

(* Per-coefficient multiplicativity. *)
private let embed_zq_mul_coeff (p q: polynomial int #int_cr) (j:nat)
  : Lemma (crq.cr_r.r_add.acg_eq.eq
             (coeff (embed_zq (p * q)) j)
             (coeff (poly_mul (embed_zq p) (embed_zq q)) j))
  = let acgi = int_cr.cr_r.r_add in
    let acgq = crq.cr_r.r_add in
    let lenp  = L.length p in
    let lenep = L.length (embed_zq p) in
    let gg = conv_src p q j in
    let hh = conv_tgt p q j in
    H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    (* ---- LHS: coeff (embed (p*q)) j =eq= embed (coeff (p*q) j) =eq= embed (sum gg 0 lenp) =eq= sum hh 0 lenp ---- *)
    embed_zq_coeff (p * q) j;     (* coeff(embed(p*q)) j =eq= embed (coeff(p*q) j) *)
    (* coeff (p*q) j == sum gg 0 lenp via named convolution (dodges lambda) *)
    let cong_src (i:nat) : Lemma (gg i = int_cr.cr_r.mul (coeff p i)
                                       (coeff q ((j - i)))) =
      H.elim_equatable_laws int () in
    coeff_poly_mul_named p q j gg cong_src;   (* coeff(p*q) j = sum gg 0 lenp *)
    (* embed pushes through the source sum *)
    let hyp (i:nat) : Lemma (acgq.acg_eq.eq (hh i) (embed_zq_const (gg i))) =
      conv_term_embed p q j i in
    Classical.forall_intro hyp;
    embed_sum_range gg hh 0 lenp;                     (* embed (sum gg 0 lenp) =eq= sum hh 0 lenp *)
    (* ---- RHS: coeff (embed p * embed q) j =eq= sum hh 0 lenep ---- *)
    let cong_tgt (i:nat) : Lemma (hh i = crq.cr_r.mul
                                    (coeff (embed_zq p) i)
                                    (coeff (embed_zq q) ((j - i)))) =
      H.elim_equatable_laws qq () in
    coeff_poly_mul_named (embed_zq p) (embed_zq q) j hh cong_tgt;  (* coeff(ep*eq) j = sum hh 0 lenep *)
    (* bridge the two sum ranges: sum hh 0 lenp =eq= sum hh 0 lenep *)
    sum_range_hh_ranges p q j

let embed_zq_mul (p q: polynomial int #int_cr)
  : Lemma (poly_eq
             (embed_zq (p * q))
             (poly_mul (embed_zq p) (embed_zq q)))
  = let lhs = embed_zq (p * q) in
    let rhs = poly_mul (embed_zq p) (embed_zq q) in
    let aux (j:nat)
      : Lemma (coeff lhs j = coeff rhs j)
      = embed_zq_mul_coeff p q j in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* ---------------------------------------------------------------- *)
(*  4. Evaluation commutes with the embedding.                       *)
(*    poly_eval (embed p) (embed c) =eq= embed (poly_eval p c).      *)
(* ---------------------------------------------------------------- *)

(* embed_zq_const 1 =eq= crq.one (mirror embed_zq_const_zero; pin via
   the multiplicative-identity law: embed 1 * crq.one = embed 1 and
   fraction_mul (embed 1) crq.one == crq.one as a Fraction). *)
private let embed_const_one (_:unit)
  : Lemma (crq.cr_r.r_add.acg_eq.eq (embed_zq_const 1) crq.cr_r.one)
  = let e1 = embed_zq_const 1 in
    let o  = crq.cr_r.one in
    H.elim_equatable_laws qq ();
    H.x_mul_one e1;                          (* e1 *_qq o =eq= e1 *)
    fraction_ring_mul_reveal e1 o;  (* e1 *_qq o == fraction_mul e1 o *)
    fraction_mul_reveal e1 o
    (* fraction_mul e1 o == Fraction (1*num o) (1*den o) == o ⇒ o =eq= e1 *)

(* embed_zq_const preserves powers:
     cpow (embed_zq_const c) i =eq= embed_zq_const (cpow c i). *)
private let rec embed_cpow (c: int) (i: nat)
  : Lemma (ensures crq.cr_r.r_add.acg_eq.eq
                     (cpow (embed_zq_const c) i)
                     (embed_zq_const (cpow c i)))
          (decreases i)
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    if i = 0 then
      (* cpow (embed c) 0 == crq.one ; cpow c 0 == one#int == 1 ; embed 1 =eq= crq.one *)
      embed_const_one ()
    else begin
      let ip = (i - 1) in
      (* cpow (embed c) i == (embed c) *_qq cpow (embed c) ip *)
      (* cpow c i == c *_int cpow c ip *)
      embed_cpow c ip;                            (* cpow (embed c) ip =eq= embed (cpow c ip) *)
      mul_congruence
        (embed_zq_const c) (cpow (embed_zq_const c) ip)
        (embed_zq_const c) (embed_zq_const (cpow c ip));
      (* (embed c) *_qq (embed (cpow c ip)) =eq= embed (c *_int cpow c ip) = embed (cpow c i) *)
      embed_const_mul_ring c (cpow c ip)
    end

(* Per-term: eval_term (embed p)(embed c) i =eq= embed (eval_term p c i). *)
private let embed_eval_term (p: polynomial int #int_cr) (c: int) (i: nat)
  : Lemma (crq.cr_r.r_add.acg_eq.eq
             (eval_term (embed_zq p) (embed_zq_const c) i)
             (embed_zq_const (eval_term p c i)))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    (* eval_term (embed p)(embed c) i == coeff(embed p) i *_qq cpow (embed c) i *)
    embed_zq_coeff p i;                           (* coeff(embed p) i =eq= embed (coeff p i) *)
    embed_cpow c i;                               (* cpow (embed c) i =eq= embed (cpow c i) *)
    mul_congruence
      (coeff (embed_zq p) i) (cpow (embed_zq_const c) i)
      (embed_zq_const (coeff p i)) (embed_zq_const (cpow c i));
    (* embed (coeff p i) *_qq embed (cpow c i) =eq= embed (coeff p i *_int cpow c i)
                                                = embed (eval_term p c i) *)
    embed_const_mul_ring (coeff p i) (cpow c i)

let embed_zq_eval (p: polynomial int #int_cr) (c: int)
  : Lemma (crq.cr_r.r_add.acg_eq.eq
             (poly_eval (embed_zq p) (embed_zq_const c))
             (embed_zq_const (poly_eval p c)))
  = let gg = eval_term p c in
    let hh = eval_term (embed_zq p) (embed_zq_const c) in
    let lenp = L.length p in
    H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    (* poly_eval (embed p)(embed c) == sum hh 0 (length (embed p)) == sum hh 0 lenp *)
    embed_zq_length_eq p;                         (* length (embed p) == lenp *)
    (* embed (poly_eval p c) == embed (sum gg 0 lenp) =eq= sum hh 0 lenp *)
    let hyp (i:nat) : Lemma (crq.cr_r.r_add.acg_eq.eq (hh i) (embed_zq_const (gg i))) =
      embed_eval_term p c i in
    Classical.forall_intro hyp;
    embed_sum_range gg hh 0 lenp
