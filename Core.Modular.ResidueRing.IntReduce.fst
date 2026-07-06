module Core.Modular.ResidueRing.IntReduce

(* ================================================================ *)
(*  §D — the reduction ring-hom  ℤ → ℤ/m  and  ℤ[X] → (ℤ/m)[X].       *)
(*  `to_fp m a = a mod m` is a ring homomorphism; `poly_to_fp m`      *)
(*  lifts it coefficient-wise.  This relates an INTEGER factorization *)
(*  F = ∏ Gᵢ to its mod-m image — the bridge certifying that a        *)
(*  centered-lifted Hensel factor really divides F over ℤ.            *)
(*                                                                   *)
(*  NO admit / assume / sorry in the final version.                  *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Modular.ResidueRing
open Core.Modular.ResidueRing.Centered
open Core.Modular.ResidueRing.CenteredPoly
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Div
open Core.Polynomial.Monic
open Core.FinSum
open FStar.Math.Lemmas

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* --- scalar ring-hom laws for  to_fp m : ℤ → zmod m --- *)

(* The canonical-rep wrapper ((a % m) + m) % m equals a % m;
   so to_fp m a is the Zm-wrap of a % m. *)
private let to_fp_is_mod (m:int{m > 1}) (a:int)
  : Lemma (to_fp m a == Zm #m (a % m))
  = lemma_mod_lt a m;                  (* a % m < m, satisfies the Zm refinement *)
    lemma_mod_plus (a % m) 1 m;        (* ((a%m) + 1*m) % m == (a%m) % m *)
    lemma_mod_mod (a % m) a m          (* (a%m) % m == a % m *)

let to_fp_one (m:int{m > 1})
  : Lemma (to_fp m 1 == zmod_one m)
  = to_fp_is_mod m 1;                  (* to_fp m 1 == Zm (1 % m) *)
    small_mod 1 m                      (* 1 % m == 1 == zv (zmod_one m) *)

(* canonical-rep addition: ((x%m)+(y%m)) % m == (x+y) % m  via mod-distributivity. *)
private let canon_add (m:int{m > 1}) (x y:int)
  : Lemma ((((x % m) + (y % m)) % m) == ((x + y) % m))
  = lemma_mod_plus_distr_l x y m;      (* (x+y)%m == ((x%m)+y)%m *)
    lemma_mod_plus_distr_r (x % m) y m  (* ((x%m)+y)%m == ((x%m)+(y%m))%m *)

private let canon_mul (m:int{m > 1}) (x y:int)
  : Lemma ((((x % m) * (y % m)) % m) == ((x * y) % m))
  = lemma_mod_mul_distr_l x y m;       (* (x*y)%m == ((x%m)*y)%m *)
    lemma_mod_mul_distr_r (x % m) y m   (* ((x%m)*y)%m == ((x%m)*(y%m))%m *)

let to_fp_add (m:int{m > 1}) (a b: int)
  : Lemma (to_fp m (a + b) == zmod_add (to_fp m a) (to_fp m b))
  = to_fp_is_mod m a;                 (* to_fp m a == Zm (a % m) *)
    to_fp_is_mod m b;                 (* to_fp m b == Zm (b % m) *)
    to_fp_is_mod m (a + b);           (* to_fp m (a+b) == Zm ((a+b) % m) *)
    canon_add m a b                   (* ((a%m)+(b%m)) % m == (a+b) % m *)
    (* zmod_add (to_fp a) (to_fp b) == Zm (((a%m)+(b%m)) % m) == Zm ((a+b) % m) == to_fp (a+b) *)

let to_fp_mul (m:int{m > 1}) (a b: int)
  : Lemma (to_fp m (a * b) == zmod_mul (to_fp m a) (to_fp m b))
  = to_fp_is_mod m a;
    to_fp_is_mod m b;
    to_fp_is_mod m (a * b);
    canon_mul m a b

(* --- poly ring-hom laws  (poly_eq in (ℤ/m)[X]) --- *)

(* Bridge: the ring `+`/`*` on (zmod m) ARE zmod_add / zmod_mul. *)
private let zmod_ring_add_reveal (m:int{m > 1}) (a b: zmod m)
  : Lemma (add a b == zmod_add a b)
  = ()

private let zmod_ring_mul_reveal (m:int{m > 1}) (a b: zmod m)
  : Lemma (mul a b == zmod_mul a b)
  = ()

(* Bridge: the ring `+`/`*` on int ARE Prims `+` / `*` (int_cr fields). *)
private let int_ring_add_reveal (a b: int)
  : Lemma (int_cr.cr_r.r_add.add a b == a + b)
  = ()

private let int_ring_mul_reveal (a b: int)
  : Lemma (int_cr.cr_r.mul a b == a * b)
  = ()

(* Per-coefficient additivity. *)
private let poly_to_fp_add_coeff (m:int{m > 1}) (g h: polynomial int #int_cr) (j:nat)
  : Lemma (coeff
              (poly_to_fp m (g + h)) j
           == coeff
                ((poly_to_fp m g) + (poly_to_fp m h)) j)
  = let cg = coeff g j in
    let ch = coeff h j in
    (* LHS *)
    poly_to_fp_coeff m (g + h) j;  (* coeff(to_fp(g+h)) j == to_fp (coeff(g+h) j) *)
    poly_add_coeff g h j;                 (* coeff(g+h) j == cg + ch (int ring add) *)
    int_ring_add_reveal cg ch;                         (* cg + ch (ring) == cg + ch (Prims) *)
    to_fp_add m cg ch;                                 (* to_fp (cg+ch) == zmod_add (to_fp cg)(to_fp ch) *)
    poly_to_fp_coeff m g j;                            (* to_fp cg == coeff (poly_to_fp g) j *)
    poly_to_fp_coeff m h j;                            (* to_fp ch == coeff (poly_to_fp h) j *)
    (* RHS *)
    poly_add_coeff (poly_to_fp m g) (poly_to_fp m h) j;
    zmod_ring_add_reveal m (coeff (poly_to_fp m g) j)
                         (coeff (poly_to_fp m h) j)

let poly_to_fp_add (m:int{m > 1}) (g h: polynomial int #int_cr)
  : Lemma ((poly_to_fp m (g + h))
           = ((poly_to_fp m g) + (poly_to_fp m h)))
  = let lhs : polynomial (zmod m) = poly_to_fp m (g + h) in
    let rhs : polynomial (zmod m) = (poly_to_fp m g) + (poly_to_fp m h) in
    let aux (j:nat)
      : Lemma (coeff lhs j
               = coeff rhs j)
      = poly_to_fp_add_coeff m g h j in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* poly_to_fp respects poly_eq. *)
let poly_to_fp_congr (m:int{m > 1}) (a b: polynomial int)
  : Lemma (requires a = b)
          (ensures  (poly_to_fp m a) = (poly_to_fp m b))
  = let lhs = poly_to_fp m a in
    let rhs = poly_to_fp m b in
    let aux (i:nat) : Lemma (coeff #(zmod m) lhs i = coeff #(zmod m) rhs i)
      = poly_to_fp_coeff m a i;
        poly_to_fp_coeff m b i;
        poly_eq_means_equal_coeffs a b i;
        H.elim_equatable_laws (zmod m) () in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* poly_to_fp preserves monicity and degree:  the integer leading `1`
   maps to `zmod_one pk ≠ 0` (pk > 1), so the top coefficient survives. *)
let poly_to_fp_monic (pk:int{pk > 1}) (g: polynomial int)
  : Lemma (requires monic g)
          (ensures  monic (poly_to_fp pk g) /\
                    deg (poly_to_fp pk g) == deg g)
  = let gb = poly_to_fp pk g in
    let d  = deg g in
    H.elim_equatable_laws int ();
    H.elim_equatable_laws (zmod pk) ();
    last_eq_index g d;
    poly_lc_reveal g;
    assert (coeff g d = (one <: int));            (* coeff g d == 1 *)
    poly_to_fp_coeff pk g d;                       (* coeff gb d == to_fp pk (coeff g d) *)
    to_fp_one pk;                                  (* to_fp pk 1 == zmod_one pk *)
    assert (coeff gb d == zmod_one pk);
    assert (not ((zmod_one pk) = (zmod_zero pk)));
    L.map_lemma (to_fp pk) g;
    trim_length_le #(zmod pk) (L.map (to_fp pk) g);
    let _ : squash (deg gb >= d) =
      if deg gb < d then coeff_above_degree gb d else () in
    assert (deg gb == d);
    last_eq_index gb (deg gb);
    poly_lc_reveal gb

(* to_fp m 0 == zmod_zero m. *)
private let to_fp_zero (m:int{m > 1})
  : Lemma (to_fp m 0 == zmod_zero m)
  = small_mod 0 m

(* to_fp pushes through a finite int-sum (additivity ⇒ hom over sum_range).
   `hh` carries the per-term image; the per-index proof-function `pf` supplies
   the pointwise hypothesis, avoiding a raw `forall` in the signature. *)
private let rec to_fp_sum_range (m:int{m > 1})
  (gg: nat -> int) (hh: nat -> zmod m)
  (pf: (i:nat) -> Lemma (hh i == to_fp m (gg i)))
  (a b: nat)
  : Lemma (ensures to_fp m (sum_range #int #(int_cr.cr_r.r_add) gg a b)
                   == sum_range #(zmod m) hh a b)
          (decreases (b - a))
  = let acgi = int_cr.cr_r.r_add in
    if a >= b then begin
      sum_range_empty #int #acgi gg a b;        (* sum = zero = 0 *)
      sum_range_empty #(zmod m) hh a b;       (* sum = zero = zmod_zero m *)
      to_fp_zero m                               (* to_fp m 0 == zmod_zero m *)
    end
    else begin
      let tailsum = sum_range #int #acgi gg (a ++ 1) b in
      sum_range_unfold_left #int #acgi gg a b;   (* sum gg a b == gg a `+` tailsum *)
      int_ring_add_reveal (gg a) tailsum;        (* gg a + tailsum (ring) == gg a + tailsum (Prims) *)
      to_fp_add m (gg a) tailsum;                (* to_fp (gg a + tailsum) == zmod_add (to_fp(gg a)) (to_fp tailsum) *)
      pf a;                                      (* hh a == to_fp m (gg a) *)
      to_fp_sum_range m gg hh pf (a ++ 1) b;      (* to_fp tailsum == sum hh (a+1) b *)
      sum_range_unfold_left #(zmod m) hh a b; (* sum hh a b == hh a `+` sum hh (a+1) b *)
      zmod_ring_add_reveal m (hh a) (sum_range #(zmod m) hh (a ++ 1) b)
    end

(* Convolution summand for g*h at output index j (source ring int). *)
private let conv_src (m:int{m > 1}) (g h: polynomial int #int_cr) (j:nat) (i:nat)
  : int
  = int_cr.cr_r.mul
      (coeff g i)
      (coeff h (j - i))

(* Convolution summand for (to_fp g)*(to_fp h) at output index j (target fp m). *)
private let conv_tgt (m:int{m > 1}) (g h: polynomial int #int_cr) (j:nat) (i:nat)
  : zmod m
  = mul
      (coeff (poly_to_fp m g) i)
      (coeff (poly_to_fp m h) (j - i))

(* Unfold reveals for the private summands (so SMT sees the bodies). *)
private let conv_src_unfold (m:int{m > 1}) (g h: polynomial int #int_cr) (j:nat) (i:nat)
  : Lemma (conv_src m g h j i
           == int_cr.cr_r.mul (coeff g i)
                              (coeff h (j - i)))
  = ()

private let conv_tgt_unfold (m:int{m > 1}) (g h: polynomial int #int_cr) (j:nat) (i:nat)
  : Lemma (conv_tgt m g h j i
           == mul
                (coeff (poly_to_fp m g) i)
                (coeff (poly_to_fp m h) (j - i)))
  = ()

(* Per-term: to_fp of a source summand is the target summand. *)
private let conv_term_reduce (m:int{m > 1}) (g h: polynomial int #int_cr) (j:nat) (i:nat)
  : Lemma (conv_tgt m g h j i == to_fp m (conv_src m g h j i))
  = let ji = j - i in
    let cg = coeff g i in
    let ch = coeff h ji in
    conv_src_unfold m g h j i;                 (* conv_src == cg * ch (int ring mul) *)
    conv_tgt_unfold m g h j i;                 (* conv_tgt == (to_fp cg)*(to_fp ch) (fp ring mul) *)
    int_ring_mul_reveal cg ch;                 (* conv_src == cg * ch (Prims) *)
    to_fp_mul m cg ch;                          (* to_fp (cg*ch) == zmod_mul (to_fp cg)(to_fp ch) *)
    poly_to_fp_coeff m g i;                     (* to_fp cg == coeff (poly_to_fp g) i *)
    poly_to_fp_coeff m h ji;                    (* to_fp ch == coeff (poly_to_fp h) (j-i) *)
    zmod_ring_mul_reveal m
      (coeff (poly_to_fp m g) i)
      (coeff (poly_to_fp m h) ji)

(* The "extra" target summands beyond length (poly_to_fp g) vanish. *)
private let conv_tgt_high_zero (m:int{m > 1}) (g h: polynomial int #int_cr) (j:nat)
  (i:nat{i >= L.length (poly_to_fp m g)})
  : Lemma ((eq
              (conv_tgt m g h j i)
              (zero <: zmod m)))
  = let cfr = coeff (poly_to_fp m g) i in
    let cgr = coeff (poly_to_fp m h) (j - i) in
    (* cfr == zero (out of range), so cfr * cgr == zmod_mul 0 cgr == 0 *)
    H.elim_equatable_laws (zmod m) ();
    conv_tgt_unfold m g h j i;
    zmod_ring_mul_reveal m cfr cgr

(* length (poly_to_fp m g) <= length g  (trim_length_le is Core.Polynomial's) *)
private let poly_to_fp_length_le (m:int{m > 1}) (g: polynomial int #int_cr)
  : Lemma (L.length (poly_to_fp m g) <= L.length g)
  = let fmap = to_fp m in
    L.map_lemma fmap g;                          (* length (map fmap g) == length g *)
    trim_length_le #(zmod m) (L.map fmap g)

(* Summing conv_tgt to length g equals summing to length (poly_to_fp g)
   (extra terms are zero). *)
private let sum_range_hh_ranges (m:int{m > 1}) (g h: polynomial int #int_cr) (j:nat)
  : Lemma (sum_range #(zmod m)
              (conv_tgt m g h j) 0 (L.length g)
           == sum_range #(zmod m)
                (conv_tgt m g h j) 0 (L.length (poly_to_fp m g)))
  = let hh  = conv_tgt m g h j in
    let lenf  = L.length g in
    let lenrf = L.length (poly_to_fp m g) in
    poly_to_fp_length_le m g;                    (* lenrf <= lenf *)
    H.elim_equatable_laws (zmod m) ();
    H.trans_for_calc (zmod m) ();
    sum_range_split #(zmod m) hh 0 lenrf lenf;
    let allzero (i:nat{lenrf <= i /\ i < lenf}) : Lemma (hh i = (zero <: zmod m)) =
      conv_tgt_high_zero m g h j i in
    sum_range_all_zero #(zmod m) hh lenrf lenf allzero;
    H.x_plus_zero #(zmod m) (sum_range #(zmod m) hh 0 lenrf)

(* htgt as a top-level lemma, phrasing `=`/`*` via the zmod_comm_ring instance
   exactly as coeff_poly_mul_named's hypothesis expects. *)
private let conv_tgt_is_mul (m:int{m > 1}) (g h: polynomial int #int_cr) (j:nat) (i:nat)
  : Lemma (eq
              (conv_tgt m g h j i)
              (mul
                 (coeff (poly_to_fp m g) i)
                 (coeff (poly_to_fp m h) (j - i))))
  = H.elim_equatable_laws (zmod m) ();
    conv_tgt_unfold m g h j i

private let conv_src_is_mul (m:int{m > 1}) (g h: polynomial int #int_cr) (j:nat) (i:nat)
  : Lemma (int_cr.cr_r.r_add.acg_eq.eq
              (conv_src m g h j i)
              (int_cr.cr_r.mul
                 (coeff g i)
                 (coeff h (j - i))))
  = H.elim_equatable_laws int #(int_cr.cr_r.r_add.acg_eq) ();
    conv_src_unfold m g h j i

(* Per-coefficient multiplicativity. *)
private let poly_to_fp_mul_coeff (m:int{m > 1}) (g h: polynomial int #int_cr) (j:nat)
  : Lemma (coeff
              (poly_to_fp m (g * h)) j
           == coeff
                ((poly_to_fp m g) * (poly_to_fp m h)) j)
  = let acgi = int_cr.cr_r.r_add in
    let lenf  = L.length g in
    let lenrf = L.length (poly_to_fp m g) in
    let gg = conv_src m g h j in
    let hh = conv_tgt m g h j in
    (* ---- LHS ---- *)
    poly_to_fp_coeff m (g * h) j;  (* coeff(to_fp(g*h)) j == to_fp (coeff(g*h) j) *)
    let hsrc (i:nat)
      : Lemma (int_cr.cr_r.r_add.acg_eq.eq (gg i)
                  (int_cr.cr_r.mul (coeff g i)
                                   (coeff h (j - i)))) =
      conv_src_is_mul m g h j i in
    coeff_poly_mul_named g h j gg hsrc;   (* coeff(g*h) j == sum_range gg 0 lenf *)
    let hyp (i:nat) : Lemma (hh i == to_fp m (gg i)) = conv_term_reduce m g h j i in
    to_fp_sum_range m gg hh hyp 0 lenf;               (* to_fp (sum gg 0 lenf) == sum hh 0 lenf *)
    (* ---- RHS ---- *)
    let htgt (i:nat)
      : Lemma (eq (hh i)
                  (mul (coeff (poly_to_fp m g) i)
                       (coeff (poly_to_fp m h) (j - i)))) =
      conv_tgt_is_mul m g h j i in
    coeff_poly_mul_named (poly_to_fp m g) (poly_to_fp m h) j hh htgt;
    (* coeff(rf*rg) j == sum_range hh 0 lenrf *)
    sum_range_hh_ranges m g h j                        (* sum hh 0 lenf == sum hh 0 lenrf *)

let poly_to_fp_mul (m:int{m > 1}) (g h: polynomial int #int_cr)
  : Lemma ((poly_to_fp m (g * h))
           = ((poly_to_fp m g) * (poly_to_fp m h)))
  = let lhs : polynomial (zmod m) = poly_to_fp m (g * h) in
    let rhs : polynomial (zmod m) = (poly_to_fp m g) * (poly_to_fp m h) in
    let aux (j:nat)
      : Lemma (coeff lhs j = coeff rhs j)
      = poly_to_fp_mul_coeff m g h j in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs
