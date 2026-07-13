module Core.Modular.PrimeField.Berlekamp

(* ================================================================ *)
(*  Berlekamp factorization over the finite prime field F_p.        *)
(*                                                                   *)
(*  MERGED MODULE: this single file folds together the former        *)
(*  Core.Modular.PrimeField.Berlekamp + BerlekampFrobenius + BerlekampSplit*)
(*  + BerlekampSplitCorrect + SubstProd + BerlekampReverse +         *)
(*  BerlekampKernel + BerlekampCriterion (in dependency order).      *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module PW = Core.Algebra.Power
module CF = Core.Modular.PrimeField.Frobenius
module FR = Core.Modular.PrimeField.Frobenius
module E  = Core.Polynomial.Eval
module EV = Core.Polynomial.Eval
module SU = Core.Polynomial.Subst
module SP = Core.Polynomial.Roots
module RT = Core.Polynomial.Roots
module PR = Core.Polynomial.Roots
module DV = Core.Polynomial.Div
module SF = Core.Polynomial.SquareFree
module IR = Core.Polynomial.Irreducible
module UN = Core.Polynomial.Unique
module CR = Core.Polynomial.CRT
module CP = Core.Polynomial.CRT
module GC = Core.Polynomial.GCD
module EU = Core.NumberTheory

open Core.Algebra
open Core.Algebra.Divisibility
open Core.Algebra.CongruenceMod
open Core.Tactics.CanonRing
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Permutation
open Core.Vector
open Core.Matrix
open Core.Matrix.Determinant
open Core.Modular.PrimeField
open Core.Modular.PrimeField.Poly  (* fp_poly_cr : commutative_ring (polynomial (fp p)) *)
open Core.FinSum
open Core.Algebra.Notation

(* polynomial commutative_ring = the canonical polynomial_cr instance. *)

(* ================================================================ *)
(*  1.  Modular exponentiation and ordinary power                    *)
(* ================================================================ *)

(* g^k mod m, naive iteration:  reduce after every multiply. *)
let rec poly_pow_mod (#t:Type) {| f: field t |} (g: polynomial t) (k:nat) (m: polynomial t)
  : Tot (polynomial t) (decreases k)
  = if k = 0 then poly_rem (poly_one #t) m
    else poly_rem (g * (poly_pow_mod g (k-1) m)) m

let poly_pow_mod_zero (#t:Type) {| f: field t |} (g m: polynomial t)
  : Lemma (poly_pow_mod g 0 m == poly_rem (poly_one #t) m)
  = ()

let poly_pow_mod_succ (#t:Type) {| f: field t |} (g m: polynomial t) (k:nat)
  : Lemma (poly_pow_mod g (k ++ 1) m
           == poly_rem (g * (poly_pow_mod g k m)) m)
  = ()

(* ordinary power g^k (no reduction) is poly_power (DRY: same body). *)

(* ================================================================ *)
(*  2.  Congruence modulo m in a commutative ring                    *)
(*      cong m x y  :=  m | (x - y)                                  *)
(* ================================================================ *)

(* The congruence-mod-m family (cong, cong_reveal, cong_refl, cong_sym,
   cong_trans, cong_mul, cong_eq_right, cong_of_divmod) now lives in
   Core.Algebra.CongruenceMod (opened above) — it is the general
   divisibility-level notion, not a Berlekamp-specific one. *)

(* the remainder is congruent to the dividend modulo m *)
let rem_cong (#t:Type) {| f: field t |} (p m: polynomial t)
  : Lemma (cong m p (poly_rem p m))
  = let q = poly_div p m in
    let r = poly_rem p m in
    cong_of_divmod p m q r

(* ================================================================ *)
(*  3.  poly_pow_mod g k m  ≡  g^k   (mod m)                          *)
(* ================================================================ *)

let rec poly_pow_mod_correct (#t:Type) {| f: field t |}
  (g: polynomial t) (k:nat) (m: polynomial t)
  : Lemma (ensures cong #(polynomial t) m (poly_pow_mod g k m) (poly_power g k))
          (decreases k)
  = if k = 0 then begin
      (* poly_pow_mod g 0 m = poly_rem one m ; poly_power g 0 = one *)
      rem_cong (poly_one #t) m;                   (* cong m one (rem one m) *)
      cong_sym #(polynomial t) m
        (poly_one #t) (poly_rem (poly_one #t) m)        (* cong m (rem one m) one *)
    end
    else begin
      (* IH: poly_pow_mod g (k-1) m ≡ g^(k-1) *)
      poly_pow_mod_correct g (k-1) m;
      let pm1 = poly_pow_mod g (k-1) m in
      let pw1 = poly_power g (k-1) in
      (* g ≡ g  ⟹  g * pm1  ≡  g * pw1 = g^k. *)
      cong_refl #(polynomial t) m g;
      cong_mul #(polynomial t) m g g pm1 pw1;       (* cong m (poly_mul g pm1) (poly_mul g pw1) *)
      (* poly_pow_mod g k m = rem (poly_mul g pm1) m  ≡  poly_mul g pm1 *)
      rem_cong (g * pm1) m;                (* cong m (g * pm1) (rem (g*pm1) m) *)
      cong_sym #(polynomial t) m
        (g * pm1) (poly_rem (g * pm1) m); (* cong m (rem (g*pm1) m) (g * pm1) *)
      (* chain: rem(g*pm1) ≡ poly_mul g pm1 ≡ poly_mul g pw1 = g^k *)
      poly_pow_mod_succ g m (k-1);                      (* poly_pow_mod g k m = rem (poly_mul g pm1) m *)
      cong_trans #(polynomial t) m
        (poly_pow_mod g k m) (g * pm1) (poly_power g k)
    end

(* ================================================================ *)
(*  4.  Berlekamp Q matrix (the Frobenius map on F_q[x]/(f))         *)
(*                                                                   *)
(*  q is the field characteristic exponent (q = p for fp p).         *)
(*  basis 1, x, …, x^{n-1};  column j is the reduction of            *)
(*  (x^j)^q mod f, row i is its x^i coefficient.                     *)
(* ================================================================ *)

(* the monic monomial x^k = [0;…;0;1]. *)
let mono_x (#t:Type) {| f: field t |} (k:nat) : polynomial t
  = monomial #t (one #t) k

(* column j of Q as a polynomial:  (x^j)^q  mod f. *)
let berlekamp_qcol (#t:Type) {| f: field t |}
  (fpoly: polynomial t) (q:nat) (j:nat) : polynomial t
  = poly_pow_mod (mono_x j) q fpoly

(* The Berlekamp Q matrix as an n x n matrix over the field. *)
let berlekamp_Q (#t:Type) {| f: field t |}
  (fpoly: polynomial t) (q:nat) (n:pos) (i j: fin n) : t
  = coeff (berlekamp_qcol fpoly q (j <: nat)) (i <: nat)

(* ================================================================ *)
(*  5.  Q - I  and its kernel                                        *)
(*                                                                   *)
(*  The Berlekamp subalgebra is the kernel of  Q - I, i.e. the       *)
(*  classes h with  h^q ≡ h (mod f).  We build  Q - I  with the      *)
(*  matrix machinery and expose the determinant/kernel hook from     *)
(*  Core.Matrix.KernelDet.                                           *)
(* ================================================================ *)

(* The matrix  Q - I  over the field. *)
let berlekamp_QmI (#t:Type) {| f: field t |}
  (fpoly: polynomial t) (q:nat) (n:pos) (i j: fin n) : t
  = berlekamp_Q fpoly q n i j -- (id_matrix #t i j)

(* The transpose, whose rows are what a kernel column-vector dots with
   in the Frobenius equation  Q·v = v  (i.e. (Q - I)·v = 0). *)
let berlekamp_QmI_t (#t:Type) {| f: field t |}
  (fpoly: polynomial t) (q:nat) (n:pos) (i j: fin n) : t
  = berlekamp_QmI fpoly q n j i

(* Opaque "there is a nonzero kernel column-vector of the matrix m"            *)
(* (a v with some nonzero entry whose dot with every row of m is zero), hiding  *)
(* the existence/forall.  _elim restores the raw quantifier for consumers.      *)
[@@"opaque_to_smt"]
let has_kernel_vector (#t:Type) {| f: field t |} (#n:pos)
  (m: square_matrix t n)
  : prop = exists (v: fin n -> t) (k: fin n).
             is_nonzero (v k) /\
             (forall (i: fin n). vector_dot (row m i) v = zero)

let has_kernel_vector_elim (#t:Type) {| f: field t |} (#n:pos)
  (m: square_matrix t n{has_kernel_vector m})
  : Lemma (exists (v: fin n -> t) (k: fin n).
             is_nonzero (v k) /\
             (forall (i: fin n). vector_dot (row m i) v = zero))
  = reveal_opaque (`%has_kernel_vector) (has_kernel_vector m)

(* Kernel extraction: if  det(Q - I) = 0  then there is a nonzero coefficient
   vector  v  with  (Q - I)·v = 0  (i.e. row-wise  Σ_j (Q-I)[i][j]·v[j] = 0).
   This is the Berlekamp subalgebra membership at the coefficient-vector level;
   it is an immediate specialisation of `det_zero_implies_null_vec` to Q - I. *)
let berlekamp_kernel_vector (#t:Type) {| f: field t |}
  (fpoly: polynomial t) (q:nat) (n:pos)
  : Lemma (requires det (berlekamp_QmI fpoly q n) = zero)
          (ensures  has_kernel_vector (berlekamp_QmI fpoly q n))
  = det_zero_implies_null_vec (berlekamp_QmI fpoly q n);
    reveal_opaque (`%has_kernel_vector) (has_kernel_vector (berlekamp_QmI fpoly q n))

(* ================================================================ *)
(*  6.  Factor extraction                                            *)
(*                                                                   *)
(*  For a Berlekamp kernel element h and a constant c ∈ F,           *)
(*  gcd(f, h - c) is a factor of f.  We build the splitting step as  *)
(*  a computable function and prove the reachable divisibility       *)
(*  facts (each gcd divides f; the gcd's residue condition).         *)
(* ================================================================ *)


(* the splitting step:  gcd(f, h - c). *)
let berlekamp_split (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (c: t) : polynomial t
  = poly_gcd fpoly (h -- (poly_const #t c))

(* each candidate factor divides f. *)
let berlekamp_split_divides_f (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (c: t)
  : Lemma (divides #(polynomial t)
                   (berlekamp_split fpoly h c) fpoly)
  = gcd_divides_left fpoly (h -- (poly_const #t c))

(* each candidate factor divides h - c (the residue condition). *)
let berlekamp_split_divides_shift (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (c: t)
  : Lemma (divides #(polynomial t)
                   (berlekamp_split fpoly h c)
                   (h -- (poly_const #t c)))
  = gcd_divides_right fpoly (h -- (poly_const #t c))

(* ================================================================ *)
(*  7.  Reachable correctness:  the Frobenius / kernel polynomial    *)
(*      equation expressed through the (proven) modular-power        *)
(*      correctness.                                                 *)
(*                                                                   *)
(*  The Berlekamp subalgebra is  { h : h^q ≡ h (mod f) }.  Because    *)
(*  poly_pow_mod computes the true power modulo f (poly_pow_mod_      *)
(*  correct), the *computable* membership test  poly_pow_mod h q f ≡  *)
(*  h (mod f)  is equivalent to the mathematical condition  h^q ≡ h.  *)
(* ================================================================ *)

(* h^q ≡ h (mod f)   <==>   (h^q mod f) ≡ h (mod f).  Both directions. *)
let berlekamp_membership_via_powmod (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (q:nat)
  : Lemma (cong #(polynomial t) fpoly (poly_power h q) h
           <==>
           cong #(polynomial t) fpoly (poly_pow_mod h q fpoly) h)
  = (* poly_pow_mod h q f ≡ h^q (mod f) — proven, both orientations via sym *)
    poly_pow_mod_correct h q fpoly;               (* cong f (powmod) (pow) *)
    let fwd () : Lemma (requires cong #(polynomial t) fpoly (poly_power h q) h)
                       (ensures  cong #(polynomial t) fpoly (poly_pow_mod h q fpoly) h)
      = (* powmod ≡ pow ≡ h *)
        cong_trans #(polynomial t) fpoly
          (poly_pow_mod h q fpoly) (poly_power h q) h
    in
    let bwd () : Lemma (requires cong #(polynomial t) fpoly (poly_pow_mod h q fpoly) h)
                       (ensures  cong #(polynomial t) fpoly (poly_power h q) h)
      = (* pow ≡ powmod (sym) ≡ h *)
        cong_sym #(polynomial t) fpoly (poly_pow_mod h q fpoly) (poly_power h q);
        cong_trans #(polynomial t) fpoly
          (poly_power h q) (poly_pow_mod h q fpoly) h
    in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()

(* A Berlekamp kernel element h (one with h^q ≡ h mod f) makes every shift
   factor gcd(f, h - c) divide BOTH f and h - c; combined with the fact that
   the (h - c) for distinct c are pairwise coprime modulo f, these gcd's are
   the factor-splitting candidates.  The pairwise-coprimality / product
   identity ∏_{c}(h - c) ≡ h^q - h (mod f) is the bridge to the full
   factorization (see the wall note at the end of the module). *)
let berlekamp_kernel_residue (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (q:nat) (c: t)
  : Lemma (requires cong #(polynomial t) fpoly (poly_power h q) h)
          (ensures  divides #(polynomial t)
                            (berlekamp_split fpoly h c) fpoly /\
                    divides #(polynomial t)
                            (berlekamp_split fpoly h c)
                            (h -- (poly_const #t c)))
  = berlekamp_split_divides_f fpoly h c;
    berlekamp_split_divides_shift fpoly h c

(* =========================  SECTION: BerlekampFrobenius  ========================= *)
#set-options "--fuel 1 --ifuel 1 --z3rlimit 30"

(* ---------------------------------------------------------------- *)
(*  Exact freshman's dream in (fp p)[x]  (re-export, rpow form).    *)
(* ---------------------------------------------------------------- *)

let frobenius_add_exact (p:int{EU.is_prime p})
  (a b: polynomial (fp p))
  : Lemma ((PW.rpow #(polynomial (fp p))
                            (a + b) (p <: nat))
                   = ((PW.rpow #(polynomial (fp p)) a (p <: nat))
                             + (PW.rpow #(polynomial (fp p)) b (p <: nat))))
  = CF.frobenius_poly_fp p a b

(* ---------------------------------------------------------------- *)
(*  Bridge: Berlekamp's poly_power (field-form) = rpow (ring-form).   *)
(* ---------------------------------------------------------------- *)

let rec poly_pow_is_rpow (p:int{EU.is_prime p}) (g: polynomial (fp p)) (k:nat)
  : Lemma (ensures poly_power #(fp p) g k
                   == PW.rpow #(polynomial (fp p)) g k)
          (decreases k)
  = if k = 0 then ()
    else poly_pow_is_rpow p g (k-1)

(* ---------------------------------------------------------------- *)
(*  Frobenius map is additive modulo f  (Berlekamp poly_power form).  *)
(*                                                                   *)
(*     (a+b)^p ≡ a^p + b^p   (mod f).                               *)
(* ---------------------------------------------------------------- *)

let frobenius_additive_mod_f (p:int{EU.is_prime p})
  (f a b: polynomial (fp p))
  : Lemma (cong #(polynomial (fp p))
                   f
                   (poly_power #(fp p) (a + b) (p <: nat))
                   ((poly_power #(fp p) a (p <: nat))
                             + (poly_power #(fp p) b (p <: nat))))
  = (* exact freshman's dream:  (a+b)^p  poly_eq  a^p + b^p *)
    CF.frobenius_poly_fp p a b;
    (* rewrite both poly_power's to rpow's *)
    poly_pow_is_rpow p (a + b) p;
    poly_pow_is_rpow p a p;
    poly_pow_is_rpow p b p;
    (* the two sides are poly_eq (= over the polynomial ring), so congruent mod f *)
    let lhs = poly_power #(fp p) (a + b) (p <: nat) in
    let rhs = (poly_power #(fp p) a (p <: nat))
                       + (poly_power #(fp p) b (p <: nat)) in
    (* lhs = rhs  (poly_eq) ; cong f rhs rhs (refl) ; cong_eq_right gives cong f rhs lhs? we want cong f lhs rhs *)
    cong_refl #(polynomial (fp p)) f lhs;   (* cong f lhs lhs *)
    cong_eq_right #(polynomial (fp p)) f lhs lhs rhs

(* =========================  SECTION: BerlekampSplit  ========================= *)
#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ================================================================ *)
(*  X^p - X root theory (moved here from Core.FiniteFields.FpEnum).  *)
(*  Provides polyX, eval_polyX, eval_poly_pow, xpx, and the fact     *)
(*  that every fp p element is a root of X^p - X (via Fermat).       *)
(* ================================================================ *)

(* X := poly_linear 0  (= [neg 0; one] = the monomial x). *)
let polyX (p:int{EU.is_prime p}) : polynomial (fp p)
  = RT.poly_linear #(fp p) (fp_zero p)

(* poly_eval X c = c  (since X = x - 0). *)
let eval_polyX (p:int{EU.is_prime p}) (c: fp p)
  : Lemma (EV.poly_eval #(fp p) (polyX p) c = c)
  = H.elim_equatable_laws (fp p) (); H.trans_for_calc (fp p) ();
    RT.eval_linear #(fp p) (fp_zero p) c;   (* eval (x-0) c = neg 0 + c *)
    (* neg 0 + c = 0 + c = c *)
    H.neg_zero #(fp p) ();                            (* neg 0 = 0 *)
    add_congruence #(fp p) (- (fp_zero p)) c (fp_zero p) c;
    H.zero_plus_x #(fp p) c;
    H.trans3 (EV.poly_eval (polyX p) c)
             ((- (fp_zero p)) + c)
             ((fp_zero p) + c) c

(* poly_eval (g^k) c = (poly_eval g c)^k  (eval is a ring hom over poly_power). *)
let rec eval_poly_pow (p:int{EU.is_prime p}) (g: polynomial (fp p)) (c: fp p) (k:nat)
  : Lemma (ensures EV.poly_eval #(fp p) (poly_power #(fp p) g k) c
                   = PW.rpow #(fp p) (EV.poly_eval g c) k)
          (decreases k)
  = H.elim_equatable_laws (fp p) (); H.trans_for_calc (fp p) ();
    if k = 0 then begin
      (* poly_power g 0 = poly_one ; eval poly_one c = one ; rpow _ 0 = one *)
      EV.eval_one #(fp p) c
    end
    else begin
      (* poly_power g k = poly_mul g (poly_power g (k-1)) *)
      EV.eval_mul #(fp p) g (poly_power #(fp p) g (k-1)) c;
      eval_poly_pow p g c (k-1);                            (* IH *)
      mul_congruence #(fp p)
                     (EV.poly_eval g c)
                     (EV.poly_eval (poly_power #(fp p) g (k-1)) c)
                     (EV.poly_eval g c)
                     (PW.rpow #(fp p) (EV.poly_eval g c) (k-1))
    end

(* the polynomial  X^p - X. *)
let xpx (p:int{EU.is_prime p}) : polynomial (fp p)
  = (poly_power #(fp p) (polyX p) (p <: nat))
        -- (polyX p)

(* reveal lemmas for the published (abstract) vocabulary. *)
let polyX_reveal (p:int{EU.is_prime p})
  : Lemma (polyX p == RT.poly_linear #(fp p) (fp_zero p))
  = ()

let xpx_reveal (p:int{EU.is_prime p})
  : Lemma (xpx p == (poly_power #(fp p) (polyX p) (p <: nat)) -- (polyX p))
  = ()

(* every field element is a root of  X^p - X  (via Fermat). *)
let fp_elt_is_root_of_xpx (p:int{EU.is_prime p}) (c: fp p)
  : Lemma (EV.poly_eval #(fp p) (xpx p) c = fp_zero p)
  = H.elim_equatable_laws (fp p) (); H.trans_for_calc (fp p) ();
    let xp = poly_power #(fp p) (polyX p) (p <: nat) in
    (* eval (xp - X) c = eval xp c + neg (eval X c) *)
    assert (xpx p == (xp + (- (polyX p))));
    EV.eval_add #(fp p) xp (- (polyX p)) c;
    EV.eval_neg #(fp p) (polyX p) c;
    (* eval xp c = c^p = c  (eval_poly_pow + eval_polyX + Fermat) *)
    eval_poly_pow p (polyX p) c (p <: nat);     (* eval xp c = rpow (eval X c) p *)
    eval_polyX p c;                              (* eval X c = c *)
    CF.fermat_fp p c;                            (* rpow c p = c *)
    (* assemble:  eval (xpx) c = (eval xp c) + neg (eval X c) = c + neg c = 0 *)
    add_congruence #(fp p) (EV.poly_eval xp c) (- (EV.poly_eval (polyX p) c))
                                c (- c);
    H.x_plus_neg_x #(fp p) c

(* ================================================================ *)
(*  Monic powers:  if lc g = one and deg g = Some d (d >= 1), then   *)
(*  deg (g^k) = Some (k*d)  and  lc (g^k) = one.                     *)
(* ================================================================ *)

(* poly_one over a field is [one]: degree 0, leading coeff one. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let poly_one_deg_lc (#t:Type) {| f: field t |} ()
  : Lemma (deg (poly_one #t) == 0 /\
           poly_lc (poly_one #t) = one)
  = H.elim_equatable_laws t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    poly_lc_reveal (poly_one #t)
#pop-options

let rec poly_pow_monic (#t:Type) {| f: field t |} (g: polynomial t) (d:pos) (k:nat)
  : Lemma (requires deg g == d /\
                    poly_lc g = (one <: t))
          (ensures  deg (poly_power g k) == Prims.op_Star k d /\
                    poly_lc (poly_power g k) = one)
          (decreases k)
  = H.elim_equatable_laws t ();
    if k = 0 then begin
      (* poly_power g 0 = poly_one : deg Some 0 = 0*d, lc one. *)
      poly_one_deg_lc #t #f ();                           (* deg poly_one = Some 0, lc = one *)
      assert (Prims.op_Star 0 d == 0)
    end
    else begin
      poly_pow_monic g d (k-1);                    (* IH: deg g^(k-1) = (k-1)*d, lc = one *)
      let gk1 = poly_power g (k-1) in
      (* deg (g * g^(k-1)) = d + (k-1)*d = k*d *)
      deg_mul g gk1;
      FStar.Math.Lemmas.distributivity_sub_left k 1 d;   (* (k-1)*d = k*d - 1*d *)
      assert ((d ++ (Prims.op_Star (k-1) d)) == Prims.op_Star k d);
      (* lc (g * g^(k-1)) = lc g * lc g^(k-1) = one * one = one *)
      SP.poly_lc_mul g gk1;
      mul_congruence (poly_lc g) (poly_lc gk1) one one;
      H.one_mul_x (one <: t);                            (* one * one = one *)
      transitivity (poly_lc (poly_power g k))
                   (poly_lc g * poly_lc gk1) (one * one);
      transitivity (poly_lc (poly_power g k))
                   ((one <: t) * (one <: t)) (one <: t)
    end

(* ================================================================ *)
(*  X = polyX p  is monic of degree 1.                              *)
(* ================================================================ *)

let polyX_deg (p:int{EU.is_prime p})
  : Lemma (deg #(fp p) (polyX p) == 1 /\
           poly_lc  #(fp p) (polyX p) = (one #(fp p)))
  = H.elim_equatable_laws (fp p) ();
    RT.poly_linear_deg #(fp p) (fp_zero p);   (* deg (x-0) = Some 1 *)
    (* polyX = poly_linear 0 = [neg 0; one]; lc = one (monic). *)
    assert (polyX p == RT.poly_linear #(fp p) (fp_zero p));
    RT.poly_linear_lc #(fp p) (fp_zero p)     (* lc (x-0) = one *)

(* ================================================================ *)
(*  X^p  is monic of degree p.                                       *)
(* ================================================================ *)

let xp_monic (p:int{EU.is_prime p})
  : Lemma (deg #(fp p)
                    (poly_power #(fp p) (polyX p) (p <: nat)) == p /\
           poly_lc #(fp p)
                    (poly_power #(fp p) (polyX p) (p <: nat)) = (one #(fp p)))
  = polyX_deg p;
    poly_pow_monic #(fp p) (polyX p) 1 (p <: nat);
    assert (Prims.op_Star (p <: nat) 1 == p)

(* ================================================================ *)
(*  xpx = X^p - X  is monic of degree p.                            *)
(* ================================================================ *)

let xpx_monic (p:int{EU.is_prime p})
  : Lemma (deg #(fp p) (xpx p) == p /\
           poly_lc  #(fp p) (xpx p) = (one #(fp p)))
  = H.elim_equatable_laws (fp p) ();
    let xp = poly_power #(fp p) (polyX p) (p <: nat) in
    xp_monic p;                                          (* deg xp = Some p, lc = one *)
    polyX_deg p;                                         (* deg X = Some 1 *)
    (* xpx = X^p - X = X^p + neg X ; deg (neg X) = deg X = 1 < p *)
    assert (xpx p == (xp + (- (polyX p))));
    DV.poly_neg_degree #(fp p) (polyX p);   (* deg (neg X) = deg X = Some 1 *)
    SP.poly_add_deg_dominant #(fp p) xp (- (polyX p)) p

(* ================================================================ *)
(*  fp_enum p = [0; 1; ...; p-1] is pairwise distinct (field-eq).    *)
(* ================================================================ *)

let rec fp_enum_from_distinct (p:int{EU.is_prime p}) (lo:nat{lo <= p})
  : Lemma (ensures SP.all_distinct #(fp p) (fp_enum_from p lo))
          (decreases (p - lo))
  = if lo = p then ()
    else begin
      fp_enum_from_distinct p (lo ++ 1);   (* tail distinct *)
      (* head (lo) differs from every d in the tail (d >= lo+1 > lo) *)
      let tail = fp_enum_from p (lo ++ 1) in
      let aux (d: fp p) : Lemma (L.memP d tail ==> not ((lo <: fp p) = d)) =
        let h () : Lemma (requires L.memP d tail) (ensures not ((lo <: fp p) = d)) =
          L.mem_memP d tail;                              (* memP <==> mem (eqtype) *)
          fp_enum_from_mem p (lo ++ 1) d;  (* mem d tail == (d >= lo+1) *)
          assert (d >= lo ++ 1)
        in Classical.move_requires h ()
      in
      Classical.forall_intro aux
    end

let fp_enum_distinct (p:int{EU.is_prime p})
  : Lemma (SP.all_distinct #(fp p) (fp_enum p))
  = fp_enum_from_distinct p 0

(* ================================================================ *)
(*  THE W2 SPLITTING IDENTITY:                                       *)
(*     X^p - X  ~  prod_{c in fp p} (X - c).                         *)
(* ================================================================ *)

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let xpx_splits (p:int{EU.is_prime p})
  : Lemma ((xpx p)
             = (PR.poly_prod_linears #(fp p) (fp_enum p)))
  = H.elim_equatable_laws (fp p) ();
    H.trans_for_calc (fp p) ();
    let roots = fp_enum p in
    xpx_monic p;                                          (* deg xpx = Some p, lc = one *)
    fp_enum_length p;                                  (* length roots = p *)
    fp_enum_distinct p;                                   (* all_distinct roots *)
    (* every listed root is a root of xpx (all fp p elements are, by Fermat) *)
    let allroot (c: fp p{L.memP c roots}) : Lemma (poly_eval #(fp p) (xpx p) c = (zero <: fp p)) =
      fp_elt_is_root_of_xpx p c                          (* eval xpx c = fp_zero = zero *)
    in
    SP.all_roots_vanish_intro #(fp p) (xpx p) roots allroot;
    (* apply the distinct-roots factorization *)
    SP.poly_split_distinct_roots #(fp p) (xpx p) roots;
    (* poly_eq xpx (poly_scale (lc xpx) (prod_linears roots)); lc xpx = one *)
    let prest = PR.poly_prod_linears #(fp p) roots in
    let lc = poly_lc #(fp p) (xpx p) in
    assert ((xpx p) = (SP.poly_scale lc prest));
    (* poly_scale lc prest ~ poly_scale one prest ~ prest *)
    SP.poly_scale_scalar_congr #(fp p) lc (one #(fp p)) prest;  (* scale lc ~ scale one *)
    (* poly_scale one prest = poly_mul (one @ poly_zero) prest = poly_mul poly_one prest ~ prest *)
    assert (SP.poly_scale (one #(fp p)) prest
            == (poly_one #(fp p)) * prest);
    poly_mul_one #(fp p) prest;                       (* poly_mul poly_one prest ~ prest *)
    transitivity (xpx p) (SP.poly_scale lc prest) (SP.poly_scale (one #(fp p)) prest);
    transitivity (xpx p) (SP.poly_scale (one #(fp p)) prest) prest
#pop-options

(* =========================  SECTION: BerlekampSplitCorrect  ========================= *)
#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* The polynomial commutative ring over a field t. *)

(* ================================================================ *)
(*  poly_const facts now live in Core.Polynomial (poly_const_is_if, *)
(*  poly_const_coeff0, poly_const_coeff_high, poly_const_deg).  Only *)
(*  the degree-bound corollary is local to Berlekamp.               *)
(* ================================================================ *)

(* poly_const has degree 0 (if c <> 0) or None (if c = 0): in either case < 1. *)
let poly_const_deg_le0 (#t:Type) {| f: field t |} (c: t)
  : Lemma (deg (poly_const #t c) < 1)
  = poly_const_deg #t c

(* ================================================================ *)
(*  The difference of the two shifts is the constant  c' - c.        *)
(*    (h - [c]) - (h - [c'])  ~  [c'] - [c]   (pure ring identity).   *)
(* ================================================================ *)

(* Abstract ring identity:  (h - cc) - (h - cc')  =  cc' - cc.
   Proved over an abstract commutative_ring (canon_ring reflects on a
   variable instance; it FAILS on the concrete polynomial ring), then
   instantiated at p = polynomial t. *)
let abstract_shift_diff (#p:Type) {| pr: commutative_ring p |} (h cc cc': p)
  : Lemma ((h + (- cc)) + (- (h + (- cc'))) = cc' + (- cc))
  = assert ((h + (- cc)) + (- (h + (- cc'))) = cc' + (- cc)) by (canon_ring ())

let shift_diff_is_const (#t:Type) {| f: field t |} (h: polynomial t) (c c': t)
  : Lemma (((h -- (poly_const #t c))
                       -- (h -- (poly_const #t c')))
             =
             ((poly_const #t c') -- (poly_const #t c)))
  = let cc  = poly_const #t c  in
    let cc' = poly_const #t c' in
    let s1 = h -- cc  in
    let s2 = h -- cc' in
    (* poly_add == add, poly_neg == neg (definitional for the poly instance) *)
    assert ((s1 -- s2)
            == add #(polynomial t)
                 (h + (- cc))
                 (- (h + (- cc'))));
    assert ((cc' -- cc)
            == (cc' + (- cc)));
    abstract_shift_diff #(polynomial t) h cc cc'

(* ================================================================ *)
(*  The constant  c' - c  is a NONZERO unit  (degree 0)  when c'<>c.  *)
(*    poly_deg (poly_sub (poly_const c') (poly_const c)) = Some 0.    *)
(* ================================================================ *)

#push-options "--z3rlimit 80"
let const_diff_deg (#t:Type) {| f: field t |} (c c': t)
  : Lemma (requires not (c' = c))
          (ensures  deg ((poly_const #t c') -- (poly_const #t c))
                    == 0)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cc  = poly_const #t c  in
    let cc' = poly_const #t c' in
    let r = cc' -- cc in
    (* coeff r 0 = c' - c <> 0 *)
    poly_sub_coeff cc' cc 0;
    poly_const_coeff0 #t c;
    poly_const_coeff0 #t c';
    neg_congruence (coeff cc 0) c;                       (* neg(coeff cc 0) = neg c *)
    add_congruence (coeff cc' 0) (- (coeff cc 0)) c' (- c);   (* coeff cc' 0 + neg(coeff cc 0) = c' + neg c *)
    (* c' + neg c <> 0  (since c' <> c)  via group cancellation *)
    let nonzero () : Lemma (requires (c' + (- c)) = zero) (ensures False) =
      H.x_plus_neg_x c;                                  (* c + neg c = zero *)
      (* c' + neg c = zero = c + neg c  ==>  c' = c (cancel neg c) *)
      transitivity (c' + (- c)) zero (c + (- c)); (* c' + neg c = c + neg c *)
      add_commutativity c' (- c);                      (* c' + neg c = neg c + c' *)
      add_commutativity c (- c);                       (* c + neg c = neg c + c *)
      transitivity ((- c) + c') (c' + (- c)) (c + (- c));
      transitivity ((- c) + c') (c + (- c)) ((- c) + c);
      H.group_cancel_left (- c) c' c                   (* c' = c, contradiction *)
    in
    Classical.move_requires nonzero ();
    assert (not ((c' + (- c)) = zero));
    assert (not (coeff r 0 = zero));
    (* coeff r 0 <> 0  ==>  poly_deg r is Some k with k >= 0 *)
    Classical.move_requires (coeff_above_degree r) 0;    (* contrapositive: not (deg r = None or < 0) *)
    (* and deg r <= 0 via degree bound (both poly_consts have deg <= 0). *)
    poly_const_deg_le0 c;
    poly_const_deg_le0 #t #f c';
    poly_sub_degree_bound cc' cc 1;               (* deg (cc' - cc) < 1, i.e. <= 0 or None *)
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
          (ensures  coprime (berlekamp_split fpoly h c)
                                  (berlekamp_split fpoly h c'))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let g1 = berlekamp_split fpoly h c  in
    let g2 = berlekamp_split fpoly h c' in
    let s1 = h -- (poly_const #t c)  in
    let s2 = h -- (poly_const #t c') in
    let d  = poly_gcd g1 g2 in
    (* d | g1 | s1   and   d | g2 | s2 *)
    gcd_divides_left  g1 g2;                        (* d | g1 *)
    gcd_divides_right g1 g2;                        (* d | g2 *)
    berlekamp_split_divides_shift fpoly h c;     (* g1 | s1 *)
    berlekamp_split_divides_shift fpoly h c';    (* g2 | s2 *)
    divides_trans #(polynomial t) d g1 s1;          (* d | s1 *)
    divides_trans #(polynomial t) d g2 s2;          (* d | s2 *)
    (* d | (s1 - s2) *)
    divides_sub #(polynomial t) d s1 s2;            (* d | add s1 (neg s2) *)
    (* s1 - s2 ~ [c'] - [c] =: r,  a nonzero constant *)
    shift_diff_is_const h c c';
    let r = (poly_const #t c') -- (poly_const #t c) in
    divides_congruence_right #(polynomial t) d (s1 -- s2) r;  (* d | r *)
    const_diff_deg c c';                            (* poly_deg r = Some 0 *)
    (* coprime g1 g2  <==>  poly_deg d = Some 0; we have d | r (deg 0). *)
    coprime_reveal #t #f g1 g2;
    (* deg d <= deg r = 0, and d | r with r nonzero.  If deg d = None then
       d ~ 0, but 0 does not divide a nonzero r.  So deg d >= 0. *)
    let dnonzero () : Lemma (requires deg d < 0) (ensures False) =
      (* d = poly_zero ; d | r  ==>  r ~ d * k = 0, contradicting deg r = Some 0 *)
      assert (d == (poly_zero #t));
      let aux (k: polynomial t) : Lemma (requires (r = (d * k))) (ensures False) =
        H.x_mul_zero #(polynomial t) k;        (* poly_mul 0 k ~ 0 (after comm) *)
        poly_mul_commutativity d k;                       (* d*k ~ k*d = k*0 *)
        transitivity r (d * k) (k * d);
        H.x_mul_zero #(polynomial t) k;
        transitivity r (k * d) (poly_zero #t);
        UN.degree_well_defined r (poly_zero #t)
      in
      Classical.forall_intro (Classical.move_requires aux)
    in
    Classical.move_requires dnonzero ();
    assert (deg d >= 0);
    IR.divides_degree_le d r;                       (* deg d <= deg r = 0 *)
    assert (deg d <= 0)
#pop-options

(* ================================================================ *)
(*  The factor list  berlekamp_factors h = map (gcd(f, h-c)) enum.   *)
(* ================================================================ *)

let berlekamp_factors (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t) : list (polynomial t)
  = L.map (fun c -> berlekamp_split fpoly h c) cs

let berlekamp_factors_reveal (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t)
  : Lemma (berlekamp_factors fpoly h cs
           == L.map (fun c -> berlekamp_split fpoly h c) cs)
  = ()

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
  : Lemma (L.length (berlekamp_factors fpoly h cs) == L.length cs)
  = (if L.length cs > 0 then
       index_map (fun c -> berlekamp_split fpoly h c) cs 0)

let berlekamp_factors_index (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t) (k:nat)
  : Lemma (requires k < L.length cs)
          (ensures  L.length (berlekamp_factors fpoly h cs) == L.length cs /\
                    L.index (berlekamp_factors fpoly h cs) k
                    == berlekamp_split fpoly h (L.index cs k))
  = index_map (fun c -> berlekamp_split fpoly h c) cs k

(* poly_prod and flat_product are the same fold. *)
let rec poly_prod_is_flat (#t:Type) {| cr: commutative_ring t |} (ps: list (polynomial t))
  : Lemma (ensures Core.Polynomial.Roots.poly_prod ps == SF.flat_product ps)
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
          (ensures  L.length (berlekamp_factors fpoly h cs) == L.length cs /\
                    divides #(polynomial t)
                            (L.index (berlekamp_factors fpoly h cs) k) fpoly)
  = index_map (fun c -> berlekamp_split fpoly h c) cs k;
    berlekamp_split_divides_f fpoly h (L.index cs k)

(* ================================================================ *)
(*  Each factor is NONZERO (has a degree) when f does.               *)
(* ================================================================ *)

let berlekamp_factors_have_degree (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (cs: list t) (k:nat)
  : Lemma (requires k < L.length cs /\ deg fpoly >= 0)
          (ensures  deg (L.index (berlekamp_factors fpoly h cs) k) >= 0)
  = index_map (fun c -> berlekamp_split fpoly h c) cs k;
    let c = L.index cs k in
    (* berlekamp_split f h c = gcd(f, h - c); gcd has degree since f does. *)
    SF.gcd_has_degree fpoly (h -- (poly_const #t c))

(* ================================================================ *)
(*  PART 3 (forward direction):  the PRODUCT of the factors divides f.*)
(*                                                                   *)
(*  From pairwise coprimality (distinct enum entries) + each gcd | f,*)
(*  iterate crt_inj via `pairwise_coprime_divides`.                  *)
(* ================================================================ *)

(* the enumeration value at index k is  lo + k  (as a nat). *)
let rec fp_enum_from_index (p:int{p > 1}) (lo:nat{lo <= p}) (k:nat)
  : Lemma (requires k < L.length (fp_enum_from p lo))
          (ensures  (L.index (fp_enum_from p lo) k <: nat) == lo ++ k)
          (decreases (p - lo))
  = fp_enum_from_length p lo;
    if lo = p then ()
    else if k = 0 then ()
    else fp_enum_from_index p (lo ++ 1) (k - 1)

let fp_enum_index (p:int{p > 1}) (k:nat)
  : Lemma (requires k < L.length (fp_enum p))
          (ensures  (L.index (fp_enum p) k <: nat) == k)
  = fp_enum_from_index p 0 k

#push-options "--z3rlimit 150 --fuel 2 --ifuel 2"
let berlekamp_factors_product_divides_f (p:int{EU.is_prime p})
  (fpoly h: polynomial (fp p))
  : Lemma (requires deg #(fp p) fpoly >= 0)
          (ensures  divides #(polynomial (fp p))
                       (Core.Polynomial.Roots.poly_prod #(fp p)
                          (berlekamp_factors #(fp p) fpoly h (fp_enum p)))
                       fpoly)
  = let cs = fp_enum p in
    let ds = berlekamp_factors #(fp p) fpoly h cs in
    fp_enum_length p;
    berlekamp_factors_length #(fp p) fpoly h cs;       (* L.length ds == L.length cs == p *)
    assert (L.length ds == L.length cs);
    (* each factor divides f *)
    let div_all (k:nat{k < L.length ds})
      : Lemma (divides #(polynomial (fp p)) (L.index ds k) fpoly) =
        berlekamp_factors_divide_f #(fp p) fpoly h cs k
    in
    Classical.forall_intro div_all;
    (* each factor has a degree *)
    let deg_all (k:nat{k < L.length ds})
      : Lemma (deg (L.index ds k) >= 0) =
        berlekamp_factors_have_degree #(fp p) fpoly h cs k
    in
    Classical.forall_intro deg_all;
    (* pairwise coprime: distinct indices give distinct enum values c <> c'. *)
    let copr (i:nat{i < L.length ds}) (j:nat{j < L.length ds})
      : Lemma (i <> j ==> coprime #(fp p) (L.index ds i) (L.index ds j)) =
      let aux () : Lemma (requires i <> j)
                         (ensures coprime #(fp p) (L.index ds i) (L.index ds j)) =
        berlekamp_factors_index #(fp p) fpoly h cs i;
        berlekamp_factors_index #(fp p) fpoly h cs j;
        fp_enum_index p i;
        fp_enum_index p j;
        let ci = L.index cs i in
        let cj = L.index cs j in
        assert ((ci <: nat) == i);                          (* underlying nat is the index *)
        assert ((cj <: nat) == j);
        (* i <> j  ==>  cj <> ci as nats  ==>  cj <> ci over fp p (eq = ==) *)
        assert (not ((cj <: nat) == (ci <: nat)));
        assert (not ((cj <: fp p) = (ci <: fp p)));
        berlekamp_split_pairwise_coprime #(fp p) fpoly h ci cj
      in Classical.move_requires aux ()
    in
    Classical.forall_intro_2 copr;
    (* iterate crt_inj over the whole list *)
    IR.pairwise_coprime_divides #(fp p) ds fpoly;
    (* flat_product ds | f ; poly_prod ds == flat_product ds *)
    poly_prod_is_flat #(fp p) ds
#pop-options

(* =========================  SECTION: SubstProd  ========================= *)
#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"


(* phi_h(g^k) = (phi_h g)^k. *)
let rec subst_pow (#t:Type) {| f: field t |} (h g: polynomial t) (k:nat)
  : Lemma (ensures (SU.poly_subst #t h (poly_power #t g k))
                           = (poly_power #t (SU.poly_subst #t h g) k))
          (decreases k)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let sg = SU.poly_subst #t h g in
    if k = 0 then begin
      SU.subst_one #t h                                      (* poly_subst h poly_one ~ poly_one *)
    end else begin
      SU.subst_mul #t h g (poly_power #t g (k-1));       (* subst(g * pow) ~ subst g * subst pow *)
      subst_pow h g (k-1);                                       (* IH *)
      mul_congruence #(polynomial t)
        sg (SU.poly_subst #t h (poly_power #t g (k-1)))
        sg (poly_power #t sg (k-1))
    end

(* phi_h([c]) = [c]  (constants are fixed). *)
#push-options "--fuel 4 --ifuel 2"
let subst_const0 (#t:Type) {| f: field t |} (h: polynomial t) (c: t)
  : Lemma ((SU.poly_subst #t h (poly_const #t c)) = (poly_const #t c))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let cp = poly_const #t c in
    let f1 = SU.subst_term #t h cp in
    if c = zero then begin
      (* cp = monomial c 0 == [] ; poly_subst = empty sum = poly_zero ~ cp *)
      sum_range_empty #(polynomial t) f1 0 0;       (* poly_subst h cp = poly_zero *)
      poly_const_congr #t c (zero <: t);                       (* cp ~ const0 zero *)
      poly_const_zero #t ()                                     (* const0 zero ~ poly_zero *)
    end else begin
      (* cp = [c] : single term  const0 c * h^0 = const0 c * 1 ~ const0 c *)
      monomial_zero_n_reveal #t c;                             (* cp == [c] (c <> 0) ; length 1 *)
      assert (L.length cp == 1);
      sum_range_unfold_left #(polynomial t) f1 0 1;
      sum_range_empty #(polynomial t) f1 1 1;
      H.x_plus_zero #(polynomial t) (f1 0);
      add_congruence #(polynomial t) (f1 0) (sum_range #(polynomial t) f1 1 1)
                     (f1 0) (poly_zero #t);
      (* f1 0 = const0 (coeff cp 0) * (cpow h 0 = poly_one) = const0 c * poly_one ~ const0 c *)
      poly_const_coeff0 #t c;                                   (* coeff cp 0 = c *)
      poly_const_congr #t (coeff cp 0) c;                        (* const0 (coeff cp 0) ~ const0 c = cp *)
      H.x_mul_one #(polynomial t) cp;          (* cp * one ~ cp *)
      mul_congruence #(polynomial t)
        (poly_const #t (coeff cp 0)) (E.cpow #(polynomial t) h 0)
        cp (E.cpow #(polynomial t) h 0)
    end
#pop-options

(* phi_h(x - c) = h - [c]. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 150"
let subst_linear (#t:Type) {| f: field t |} (h: polynomial t) (c: t)
  : Lemma ((SU.poly_subst #t h (RT.poly_linear #t #f c))
                   = (h -- (poly_const #t c)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let lin = RT.poly_linear #t #f c in
    let f1 = SU.subst_term #t h lin in
    assert (lin == [(- c); (one <: t)]);
    assert (L.length lin == 2);
    assert (coeff lin 0 == (- c));
    assert (coeff lin 1 == (one <: t));
    let ck0 = E.cpow #(polynomial t) h 0 in    (* == poly_one *)
    let ck1 = E.cpow #(polynomial t) h 1 in    (* == poly_mul h poly_one *)
    (* sum_range f1 0 2 = f1 0 + (f1 1 + poly_zero) *)
    sum_range_unfold_left #(polynomial t) f1 0 2;
    sum_range_unfold_left #(polynomial t) f1 1 2;
    sum_range_empty #(polynomial t) f1 2 2;
    H.x_plus_zero #(polynomial t) (f1 1);
    add_congruence #(polynomial t) (f1 1) (sum_range #(polynomial t) f1 2 2)
                   (f1 1) (poly_zero #t);
    (* ---- f1 0 ~ poly_neg (const0 c) ---- *)
    poly_const_congr #t (coeff lin 0) (- c);                 (* const0 (coeff lin 0) ~ const0 (- c) *)
    poly_const_neg #t c;                                        (* const0 (- c) ~ poly_neg (const0 c) *)
    H.x_mul_one #(polynomial t) (poly_const #t (coeff lin 0));  (* const0(coeff lin 0)*one ~ const0(coeff lin 0) ; ck0 == one *)
    transitivity #(polynomial t)
      (f1 0) (poly_const #t (coeff lin 0)) (poly_const #t (- c));
    transitivity #(polynomial t)
      (f1 0) (poly_const #t (- c)) (- (poly_const #t c));
    (* ---- f1 1 ~ h ---- *)
    poly_const_congr #t (coeff lin 1) (one <: t);              (* const0 (coeff lin 1) ~ const0 one *)
    poly_const_one #t ();                                       (* const0 one ~ poly_one *)
    H.x_mul_one #(polynomial t) h;            (* poly_mul h poly_one ~ h ; ck1 == poly_mul h one *)
    H.one_mul_x #(polynomial t) h;           (* poly_mul poly_one h ~ h *)
    (* const0(coeff lin 1) ~ poly_one, ck1 ~ h  ⇒  f1 1 = const0(coeff lin 1)*ck1 ~ poly_one*h ~ h *)
    mul_congruence #(polynomial t)
      (poly_const #t (coeff lin 1)) ck1 (poly_one #t) h;
    transitivity #(polynomial t)
      (f1 1) ((poly_one #t) * h) h;
    (* ---- assemble:  f1 0 + (f1 1 + 0) ~ poly_neg(const0 c) + h ~ h + poly_neg(const0 c) = poly_sub h [c] ---- *)
    add_congruence #(polynomial t)
      (f1 0) (f1 1) (- (poly_const #t c)) h;
    add_commutativity #(polynomial t) (- (poly_const #t c)) h;
    transitivity #(polynomial t)
      (SU.poly_subst #t h lin)
      ((f1 0) + (f1 1))
      ((- (poly_const #t c)) + h);
    transitivity #(polynomial t)
      (SU.poly_subst #t h lin)
      ((- (poly_const #t c)) + h)
      (h -- (poly_const #t c))
#pop-options

(* poly_power respects poly_eq in the base. *)
let rec poly_pow_congr (#t:Type) {| f: field t |} (a b: polynomial t) (k:nat)
  : Lemma (requires a = b)
          (ensures (poly_power #t a k) = (poly_power #t b k))
          (decreases k)
  = H.elim_equatable_laws (polynomial t) ();
    if k = 0 then ()
    else begin
      poly_pow_congr a b (k-1);
      mul_congruence #(polynomial t)
        a (poly_power #t a (k-1)) b (poly_power #t b (k-1))
    end

(* Named single-symbol form of the shift map  c |-> h - [c], with the
   subtraction kept in NOTATION in the body.  Being `unfold`, every use
   reduces to  h -- poly_const c, so all `--`-based reasoning still sees
   through it; presenting one syntactic name `shift_const h` to every
   L.map lets the  poly_prod (L.map ...)  fact cross-unify across lemmas. *)
unfold
let shift_const (#t:Type) {| f: field t |} (h: polynomial t) (c: t)
  : polynomial t
  = h -- (poly_const #t c)

(* phi_h(prod_linears roots) = poly_prod (map (\c. h - [c]) roots). *)
let rec subst_poly_prod_linears (#t:Type) {| f: field t |} (h: polynomial t) (roots: list t)
  : Lemma (ensures (SU.poly_subst #t h (PR.poly_prod_linears #t #f roots))
                           = (PR.poly_prod #t
                              (L.map (shift_const #t h) roots)))
          (decreases roots)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match roots with
    | [] -> SU.subst_one #t h
    | c :: rest ->
      let lin = RT.poly_linear #t #f c in
      let prest = PR.poly_prod_linears #t #f rest in
      SU.subst_mul #t h lin prest;                              (* subst(lin * prest) ~ subst lin * subst prest *)
      subst_linear h c;                                             (* subst lin ~ poly_sub h [c] *)
      subst_poly_prod_linears h rest;                              (* IH: subst prest ~ poly_prod (map .. rest) *)
      mul_congruence #(polynomial t)
        (SU.poly_subst #t h lin) (SU.poly_subst #t h prest)
        (shift_const #t h c)
        (PR.poly_prod #t (L.map (shift_const #t h) rest));
      transitivity #(polynomial t)
        (SU.poly_subst #t h (PR.poly_prod_linears #t #f roots))
        ((SU.poly_subst #t h lin) * (SU.poly_subst #t h prest))
        ((shift_const #t h c)
                  * (PR.poly_prod #t (L.map (shift_const #t h) rest)))

(* poly_sub respects poly_eq in both arguments. *)
let poly_sub_congr (#t:Type) {| f: field t |} (a b a' b': polynomial t)
  : Lemma (requires a = a' /\ b = b')
          (ensures (a -- b) = (a' -- b'))
  = H.elim_equatable_laws (polynomial t) ();
    neg_congruence #(polynomial t) b b';
    add_congruence #(polynomial t) a (- b) a' (- b')

(* phi_h(X) = h. *)
let subst_X (p:int{EU.is_prime p}) (h: polynomial (fp p))
  : Lemma ((SU.poly_subst #(fp p) h (polyX p)) = h)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    H.trans_for_calc (polynomial (fp p)) ();
    (* polyX = poly_linear (fp_zero p) ; subst ~ poly_sub h (const0 (fp_zero p)) *)
    subst_linear #(fp p) h (fp_zero p);
    (* const0 (fp_zero p) ~ poly_zero *)
    poly_const_congr #(fp p) (fp_zero p) (zero <: fp p);
    poly_const_zero #(fp p) ();
    transitivity #(polynomial (fp p))
      (poly_const #(fp p) (fp_zero p)) (poly_const #(fp p) (zero <: fp p)) (poly_zero #(fp p));
    (* poly_sub h (const0 (fp_zero p)) ~ poly_sub h poly_zero ~ h *)
    poly_sub_congr #(fp p) h (poly_const #(fp p) (fp_zero p)) h (poly_zero #(fp p));
    H.neg_zero #(polynomial (fp p)) ();             (* poly_neg poly_zero ~ poly_zero *)
    add_congruence #(polynomial (fp p)) h (- (poly_zero #(fp p))) h (poly_zero #(fp p));
    H.x_plus_zero #(polynomial (fp p)) h;
    transitivity #(polynomial (fp p))
      (h -- (poly_zero #(fp p))) (h + (- (poly_zero #(fp p)))) (h + (poly_zero #(fp p)));
    transitivity #(polynomial (fp p))
      (h -- (poly_zero #(fp p))) (h + (poly_zero #(fp p))) h;
    transitivity #(polynomial (fp p))
      (SU.poly_subst #(fp p) h (polyX p))
      (h -- (poly_const #(fp p) (fp_zero p)))
      (h -- (poly_zero #(fp p)));
    transitivity #(polynomial (fp p))
      (SU.poly_subst #(fp p) h (polyX p))
      (h -- (poly_zero #(fp p)))
      h

(* ================================================================ *)
(*  THE GOAL:  h^p - h  ~  prod_{c in fp p} (h - [c]).               *)
(* ================================================================ *)
#push-options "--z3rlimit 150"
let subst_prod (p:int{EU.is_prime p}) (h: polynomial (fp p))
  : Lemma (((poly_power #(fp p) h (p <: nat)) -- h)
                   = (PR.poly_prod #(fp p)
                      (L.map (shift_const #(fp p) h) (fp_enum p))))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    H.trans_for_calc (polynomial (fp p)) ();
    let roots = fp_enum p in
    let pX = polyX p in
    let xp = poly_power #(fp p) pX (p <: nat) in
    let sh = SU.poly_subst #(fp p) h in
    let prodlin = PR.poly_prod_linears #(fp p) roots in
    let rhs = PR.poly_prod #(fp p)
                (L.map (shift_const #(fp p) h) roots) in
    let php = poly_power #(fp p) h (p <: nat) in
    (* RHS chain:  sh(xpx) ~ sh(prodlin) ~ rhs *)
    xpx_splits p;                       (* xpx ~ prodlin *)
    SU.subst_congr #(fp p) h (xpx p) prodlin;  (* sh(xpx) ~ sh(prodlin) *)
    subst_poly_prod_linears #(fp p) h roots;       (* sh(prodlin) ~ rhs *)
    transitivity #(polynomial (fp p)) (sh (xpx p)) (sh prodlin) rhs;
    (* LHS chain:  sh(xpx) ~ poly_sub (sh xp)(sh pX) ~ poly_sub php h *)
    SU.subst_sub #(fp p) h xp pX;            (* sh(poly_sub xp pX) ~ poly_sub (sh xp)(sh pX) ; xpx == poly_sub xp pX *)
    subst_pow #(fp p) h pX (p <: nat);             (* sh xp ~ poly_power (sh pX) p *)
    subst_X p h;                                                  (* sh pX ~ h *)
    poly_pow_congr #(fp p) (sh pX) h (p <: nat);   (* poly_power (sh pX) p ~ php *)
    transitivity #(polynomial (fp p))
      (sh xp) (poly_power #(fp p) (sh pX) (p <: nat)) php;   (* sh xp ~ php *)
    poly_sub_congr #(fp p) (sh xp) (sh pX) php h;  (* poly_sub (sh xp)(sh pX) ~ poly_sub php h *)
    transitivity #(polynomial (fp p))
      (sh (xpx p)) ((sh xp) -- (sh pX)) (php -- h);
    (* combine:  php -- h ~ sh(xpx) ~ rhs *)
    transitivity #(polynomial (fp p)) (php -- h) (sh (xpx p)) rhs
#pop-options

(* =========================  SECTION: BerlekampReverse  ========================= *)
#set-options "--fuel 1 --ifuel 1 --z3rlimit 80"

(* the product  prod_{c in fp p} (h - [c]). *)
let shift_product (p:int{EU.is_prime p}) (h: polynomial (fp p))
  : polynomial (fp p)
  = PR.poly_prod #(fp p)
      (L.map (shift_const #(fp p) h)
             (fp_enum p))

(* a kernel element divides the shift-product. *)
let reverse_divides (p:int{EU.is_prime p}) (fpoly h: polynomial (fp p))
  : Lemma (requires cong #(polynomial (fp p))
                            fpoly (poly_power #(fp p) h (p <: nat)) h)
          (ensures  divides #(polynomial (fp p))
                            fpoly (shift_product p h))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let xp = poly_power #(fp p) h (p <: nat) in
    (* cong fpoly xp h  =  fpoly | (xp + neg h)  =  fpoly | xp -- h *)
    (* subst_prod:  xp -- h ~ shift_product *)
    subst_prod p h;
    divides_congruence_right #(polynomial (fp p))
      fpoly (xp -- h) (shift_product p h)


(* const0 c ~ poly_const c : both are the constant polynomial [c]. *)
let const0_eq_poly_const (p:int{EU.is_prime p}) (c: fp p)
  : Lemma ((poly_const #(fp p) c)
                   = (poly_const #(fp p) c))
  = H.elim_equatable_laws (fp p) ();
    poly_eq_by_coeff #(fp p)
      (poly_const #(fp p) c) (poly_const #(fp p) c)
      (fun (j:nat) ->
        if j = 0 then begin
          poly_const_coeff0 #(fp p) c;
          poly_const_coeff0 #(fp p) c
        end else begin
          poly_const_coeff_high #(fp p) c j;
          poly_const_coeff_high #(fp p) c j
        end)


(* ================================================================ *)
(*  Per-index bridge between the two shift forms:                    *)
(*    gcd(f, h - const0 c)  ~  gcd(f, h - poly_const c)              *)
(*                          =  berlekamp_split f h c.                *)
(*  (const0 is the Subst-module embedding; poly_const the Berlekamp  *)
(*   one — they are poly_eq by const0_eq_poly_const.)                *)
(* ================================================================ *)
let split_eq_const0 (p:int{EU.is_prime p}) (fpoly h: polynomial (fp p)) (c: fp p)
  : Lemma ((GC.poly_gcd #(fp p) fpoly
                (h -- (poly_const #(fp p) c)))
             = (berlekamp_split #(fp p) fpoly h c))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    const0_eq_poly_const p c;
    poly_sub_congr #(fp p) h (poly_const #(fp p) c)
                                 h (poly_const #(fp p) c);
    GC.gcd_congruence #(fp p) fpoly fpoly
       (h -- (poly_const #(fp p) c))
       (h -- (poly_const #(fp p) c))

(* ================================================================ *)
(*  REVERSE SPLIT, direction "f | prod gcd":                         *)
(*    a kernel element h satisfies  f | prod_c gcd(f, h - [c]).       *)
(*                                                                   *)
(*  From reverse_divides (f | prod_c (h-[c])), then                  *)
(*  CP.f_divides_prod_gcd (f | prod ms ==> f | prod gcd(f,ms)),       *)
(*  then bridge the const0-shift product to the berlekamp_factors    *)
(*  (poly_const) product via CP.poly_prod_congr + split_eq_const0.   *)
(* ================================================================ *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 2"
let reverse_split_divides (p:int{EU.is_prime p}) (fpoly h: polynomial (fp p))
  : Lemma (requires cong #(polynomial (fp p))
                            fpoly (poly_power #(fp p) h (p <: nat)) h)
          (ensures  divides #(polynomial (fp p))
                      fpoly
                      (PR.poly_prod #(fp p)
                         (berlekamp_factors #(fp p) fpoly h (fp_enum p))))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let shfn = shift_const #(fp p) h in
    let shifts0 = L.map shfn (fp_enum p) in
    let gcds0 = L.map (fun m -> GC.poly_gcd #(fp p) fpoly m) shifts0 in
    let bfactors = berlekamp_factors #(fp p) fpoly h (fp_enum p) in
    reverse_divides p fpoly h;
    CP.f_divides_prod_gcd #(fp p) fpoly shifts0;
    fp_enum_length p;
    berlekamp_factors_length #(fp p) fpoly h (fp_enum p);
    index_map shfn (fp_enum p) 0;
    index_map (fun m -> GC.poly_gcd #(fp p) fpoly m) shifts0 0;
    let pointwise (i:nat{i < L.length gcds0})
      : Lemma ((L.index gcds0 i) = (L.index bfactors i))
      = index_map (fun m -> GC.poly_gcd #(fp p) fpoly m) shifts0 i;
        index_map shfn (fp_enum p) i;
        berlekamp_factors_index #(fp p) fpoly h (fp_enum p) i;
        split_eq_const0 p fpoly h (L.index (fp_enum p) i)
    in
    CP.poly_prod_congr #(fp p) gcds0 bfactors pointwise;
    divides_congruence_right #(polynomial (fp p))
      fpoly
      (PR.poly_prod #(fp p) gcds0)
      (PR.poly_prod #(fp p) bfactors)
#pop-options

(* ================================================================ *)
(*  BERLEKAMP REVERSE SPLITTING (the #28 theorem):                   *)
(*    for a squarefree-or-not f and a kernel element h,              *)
(*       prod_c gcd(f, h - [c])   and   f   are ASSOCIATES           *)
(*       (mutually divide) in fp p [X].                              *)
(*                                                                   *)
(*    direction (prod | f)  : #25 berlekamp_factors_product_divides_f *)
(*    direction (f | prod)  : reverse_split_divides (this module).    *)
(* ================================================================ *)
let berlekamp_reverse_associates (p:int{EU.is_prime p}) (fpoly h: polynomial (fp p))
  : Lemma (requires deg #(fp p) fpoly >= 0 /\
                    cong #(polynomial (fp p))
                            fpoly (poly_power #(fp p) h (p <: nat)) h)
          (ensures  (let prod = PR.poly_prod #(fp p)
                                   (berlekamp_factors #(fp p) fpoly h (fp_enum p)) in
                     divides #(polynomial (fp p)) fpoly prod /\
                     divides #(polynomial (fp p)) prod fpoly))
  = reverse_split_divides p fpoly h;
    berlekamp_factors_product_divides_f p fpoly h

(* =========================  SECTION: BerlekampKernel  ========================= *)
#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* m divides m*n  and  n divides m*n. *)
let divides_self_mul (#t:Type) {| f: field t |} (m n: polynomial t)
  : Lemma (divides #(polynomial t) m (m * n) /\
           divides #(polynomial t) n (m * n))
  = H.elim_equatable_laws (polynomial t) ();
    (* m | m*n : witness n *)
    divides_intro #(polynomial t) m (m * n) n;
    (* n | m*n : m*n ~ n*m, witness m *)
    poly_mul_commutativity m n;
    divides_congruence_right #(polynomial t) n (n * m) (m * n);
    divides_intro #(polynomial t) n (n * m) m

(* cong respects p-th powers:  cong m a b ==> cong m (a^k) (b^k). *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec cong_pow (#t:Type) {| f: field t |} (m a b: polynomial t) (k:nat)
  : Lemma (requires cong #(polynomial t) m a b)
          (ensures  cong #(polynomial t) m
                            (poly_power a k) (poly_power b k))
          (decreases k)
  = if k = 0 then begin
      cong_refl #(polynomial t) m (poly_one #t)
    end else begin
      cong_pow m a b (k - 1);              (* IH *)
      (* cong_mul: x1=a,x2=b (cong m a b) ; y1=a^{k-1},y2=b^{k-1} (IH) ;
         ensures cong m (a*a^{k-1}) (b*b^{k-1}). *)
      cong_mul #(polynomial t) m
        a b (poly_power a (k - 1)) (poly_power b (k - 1));
      (* bridge mul #crp == poly_mul == poly_power _ k *)
      assert ((a * (poly_power a (k - 1)))
              == poly_power a k);
      assert ((b * (poly_power b (k - 1)))
              == poly_power b k)
    end
#pop-options

(* The Berlekamp kernel condition splits over coprime moduli. *)
let cong_mul_iff (#t:Type) {| f: field t |} (m n x y: polynomial t)
  : Lemma (requires coprime m n /\ deg m >= 0)
          (ensures (cong #(polynomial t) (m * n) x y
                    <==> (cong #(polynomial t) m x y /\
                          cong #(polynomial t) n x y)))
  = H.elim_equatable_laws (polynomial t) ();
    let d = (x + (- y)) in
    (* cong _ x y  ==  divides _ d  (by definition of cong) *)
    divides_self_mul m n;                       (* m | m*n  and  n | m*n *)
    (* forward: divides (m*n) d  ==>  divides m d /\ divides n d *)
    let fwd () : Lemma (requires divides #(polynomial t) (m * n) d)
                       (ensures  divides #(polynomial t) m d /\
                                 divides #(polynomial t) n d)
      = divides_trans #(polynomial t) m (m * n) d;
        divides_trans #(polynomial t) n (m * n) d
    in
    Classical.move_requires fwd ();
    (* backward: divides m d /\ divides n d ==> divides (m*n) d  (crt_inj) *)
    let bwd () : Lemma (requires divides #(polynomial t) m d /\
                                 divides #(polynomial t) n d)
                       (ensures  divides #(polynomial t) (m * n) d)
      = CR.crt_inj m n d
    in
    Classical.move_requires bwd ()

(* ================================================================ *)
(*  List form:  for pairwise-coprime (nonzero) moduli ms,            *)
(*     cong (prod ms) x y  <==>  forall i. cong (ms_i) x y.          *)
(*                                                                   *)
(*  Induction on ms via cong_mul_iff + CP.coprime_to_prod.           *)
(*  (Applied with ms = the distinct irreducible factors of f and     *)
(*   x = h^p, y = h, this says: h is a Berlekamp element mod f iff    *)
(*   it is one modulo every irreducible factor — the CRT splitting    *)
(*   of the kernel.)                                                 *)
(* ================================================================ *)

let index_for #t (l: list t) = x:nat{x<L.length l}

(* NOTE: this is a SEPARATE refined spelling of pairwise-coprimality
   (index_for-refined binders + heterogeneous `=!=`), distinct from the
   raw-nat Core.Polynomial.Irreducible.pairwise_coprime shared by CRTMulti
   and SubsetProd.  The two opaque defs are not interchangeable without a
   bridge lemma; kept local here to avoid churning this file's proof. *)
[@@"opaque_to_smt"]
let pairwise_coprime #t {| f: field t |} (ms: list (polynomial t))
  : prop = forall (j k:index_for ms{j =!= k}). coprime (L.index ms j) (L.index ms k)

let pairwise_coprime_elim #t {| f: field t |} (ms: list (polynomial t){pairwise_coprime ms})
  : Lemma (forall (j k:index_for ms{j =!= k}). coprime (L.index ms j) (L.index ms k))
  = reveal_opaque (`%pairwise_coprime) (pairwise_coprime ms)

let pairwise_coprime_proof #t {| f: field t |} (ms: list (polynomial t))
  = (i:index_for ms) -> (j:index_for ms{j =!= i}) 
  -> Lemma (coprime (L.index ms i) (L.index ms j))

let pairwise_coprime_intro #t {| f: field t |} (ms: list (polynomial t)) 
                                               (proof: pairwise_coprime_proof ms)
  : Lemma (pairwise_coprime ms)                                                      
  = reveal_opaque (`%pairwise_coprime) (pairwise_coprime ms);
    Classical.forall_intro_2 proof
   
  
(* ---------------------------------------------------------------- *)
(*  Opaque predicates hiding the two `forall`s of cong_prod_deslop:   *)
(*    all_deg_nonneg ms  =  forall k. deg ms_k >= 0   (the precond)    *)
(*    all_cong ms x y    =  forall k. cong ms_k x y   (the RHS list)   *)
(*  With _elim (reveal) and _intro (build via forall_intro) bridges,   *)
(*  plus the cons-structural facts the induction needs.               *)
(* ---------------------------------------------------------------- *)
[@@"opaque_to_smt"]
let all_deg_nonneg (#t:Type) {| f: field t |} (ms: list (polynomial t))
  : prop = forall (k:index_for ms). deg (L.index ms k) >= 0

let all_deg_nonneg_elim (#t:Type) {| f: field t |}
  (ms: list (polynomial t){all_deg_nonneg ms})
  : Lemma (forall (k:index_for ms). deg (L.index ms k) >= 0)
  = reveal_opaque (`%all_deg_nonneg) (all_deg_nonneg ms)

[@@"opaque_to_smt"]
let all_cong (#t:Type) {| f: field t |} (ms: list (polynomial t)) (x y: polynomial t)
  : prop = forall (k:index_for ms). cong (L.index ms k) x y

let all_cong_elim (#t:Type) {| f: field t |}
  (ms: list (polynomial t)) (x y: polynomial t{all_cong ms x y})
  : Lemma (forall (k:index_for ms). cong (L.index ms k) x y)
  = reveal_opaque (`%all_cong) (all_cong ms x y)

let all_cong_proof (#t:Type) {| f: field t |} (ms: list (polynomial t)) (x y: polynomial t)
  = (k:index_for ms) -> Lemma (cong (L.index ms k) x y)

let all_cong_intro (#t:Type) {| f: field t |} (ms: list (polynomial t)) (x y: polynomial t)
  (proof: all_cong_proof ms x y)
  : Lemma (all_cong ms x y)
  = reveal_opaque (`%all_cong) (all_cong ms x y);
    Classical.forall_intro proof

(* tail of all_deg_nonneg: from (d::rest) extract rest. *)
let all_deg_nonneg_tail (#t:Type) {| f: field t |} (d: polynomial t) (rest: list (polynomial t))
  : Lemma (requires all_deg_nonneg (d :: rest))
          (ensures  all_deg_nonneg rest)
  = all_deg_nonneg_elim (d :: rest);
    let aux (k:index_for rest) : Lemma (deg (L.index rest k) >= 0)
      = assert (L.index (d :: rest) (k ++ 1) == L.index rest k)
    in
    Classical.forall_intro aux;
    reveal_opaque (`%all_deg_nonneg) (all_deg_nonneg rest)

(* cons-structure for all_cong:
     all_cong (d::rest) x y  <==>  cong d x y /\ all_cong rest x y. *)
let all_cong_cons (#t:Type) {| f: field t |}
  (d: polynomial t) (rest: list (polynomial t)) (x y: polynomial t)
  : Lemma ( all_cong (d :: rest) x y
            <==> (cong d x y /\ all_cong rest x y) )
  = reveal_opaque (`%all_cong) (all_cong (d :: rest) x y);
    reveal_opaque (`%all_cong) (all_cong rest x y);
    assert (L.index (d :: rest) 0 == d);
    assert (forall (k:nat). k < L.length rest ==>
              L.index (d :: rest) (k ++ 1) == L.index rest k)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let rec cong_prod_deslop (#t:Type) {| f: field t |} (ms: list (polynomial t)) (x y: polynomial t)
                         (ms_pairwise_coprime: pairwise_coprime_proof ms)
  : Lemma (requires all_deg_nonneg ms)
          (ensures (cong (PR.poly_prod ms) x y <==> all_cong ms x y))
          (decreases ms)
  = H.elim_equatable_laws (polynomial t) ();
    all_deg_nonneg_elim ms;
    match ms with
    | [] ->
        (* poly_prod [] = poly_one ; one | (x - y) ; RHS vacuously true *)
        IR.one_divides_all (x + -y);
        reveal_opaque (`%all_cong) (all_cong #t ms x y)
    | d :: rest ->
        let prest = PR.poly_prod rest in
        (* index of (d::rest): position 0 is d, position k+1 is rest_k. *)
        assert (L.index (d :: rest) 0 == d);
        assert (forall (k:nat). k < L.length rest ==>
                  L.index (d :: rest) (k ++ 1) == L.index rest k);
        (* tail is pairwise coprime: shift ms's proof by one index. *)
        let proof (i: index_for rest) (j: index_for rest{i =!= j})
          : Lemma (coprime (L.index rest i) (L.index rest j))
          = assert (L.index rest i == L.index ms (i ++ 1));
            assert (L.index rest j == L.index ms (j ++ 1));
            ms_pairwise_coprime (i ++ 1) (j ++ 1)
        in
        (* d is coprime to every tail factor (ms's proof at (0, k+1)), hence to
           their product — via the opaque coprime_with_all + coprime_to_prod. *)
        let proof_d (k:nat{k < L.length rest}) : Lemma (coprime d (L.index rest k))
          = assert (L.index rest k == L.index ms (k ++ 1));
            ms_pairwise_coprime 0 (k ++ 1)
        in
        CP.coprime_with_all_intro d rest proof_d;
        CP.coprime_to_prod d rest;            (* coprime d prest *)
        cong_mul_iff d prest x y;             (* cong (d*prest) <==> cong d /\ cong prest *)
        all_deg_nonneg_tail d rest;           (* all_deg_nonneg rest for the IH *)
        cong_prod_deslop rest x y proof;      (* IH: cong prest <==> all_cong rest *)
        all_cong_cons d rest x y              (* all_cong (d::rest) <==> cong d /\ all_cong rest *)
#pop-options

(* The former `cong_prod_iff` (forall-precondition version) is subsumed by
   `cong_prod_deslop` above (proof-as-argument pairwise coprimality, opaque
   coprime_with_all) and has been removed. *)

(* ================================================================ *)
(*  Irreducible ==> prime, and its list form.                        *)
(*  (General polynomial facts; placed here for the per-factor kernel  *)
(*   argument below.)                                                *)
(* ================================================================ *)

let abs_assoc (#u:Type) {| cr: commutative_ring u |} (x y z: u)
  : Lemma (eq ((x * y) * z) (x * (y * z)))
  = assert (eq ((x * y) * z) (x * (y * z))) by canon_ring ()

let abs_comm (#u:Type) {| cr: commutative_ring u |} (x y: u)
  : Lemma (eq (x * y) (y * x))
  = assert (eq (x * y) (y * x)) by canon_ring ()

(* k a nonzero-constant unit, q ~ g*k  ==>  q | g. *)
let unit_cofactor_divides (#t:Type) {| f: field t |} (q g k: polynomial t)
  : Lemma (requires deg k == 0 /\ q = (g * k))
          (ensures  divides #(polynomial t) q g)
  = H.elim_equatable_laws (polynomial t) ();
    degree_zero_is_singleton k;
    let c : t = poly_lc k in
    let cinv : t = inv c in
    let ci : polynomial t = [cinv] in
    singleton_inv_mul_singleton c;
    assert ((ci * k) = (poly_one #t));
    poly_mul_congruence q ci (g * k) ci;
    abs_assoc #(polynomial t) g k ci;
    transitivity (q * ci) ((g * k) * ci) (g * (k * ci));
    abs_comm #(polynomial t) k ci;
    poly_mul_congruence g (k * ci) g (ci * k);
    transitivity (q * ci) (g * (k * ci)) (g * (ci * k));
    poly_mul_congruence g (ci * k) g (poly_one #t);
    transitivity (q * ci) (g * (ci * k)) (g * (poly_one #t));
    poly_mul_one g;
    transitivity (q * ci) (g * (poly_one #t)) g;
    divides_intro #(polynomial t) q g ci

(* irreducible q dividing a product divides one of the factors. *)
let irreducible_prime (#t:Type) {| f: field t |} (q a b: polynomial t)
  : Lemma (requires IR.poly_irreducible q /\
                    divides #(polynomial t) q (a * b))
          (ensures  divides #(polynomial t) q a \/
                    divides #(polynomial t) q b)
  = H.elim_equatable_laws (polynomial t) ();
    let notb () : Lemma (requires ~(divides #(polynomial t) q a))
                        (ensures  divides #(polynomial t) q b)
      = let g = poly_gcd q a in
        SF.gcd_has_degree q a;
        gcd_divides_left  q a;
        gcd_divides_right q a;
        let show_coprime () : Lemma (deg g == 0)
          = eliminate exists (k: polynomial t). q = (g * k)
            returns deg g == 0
            with _hk.
            begin
              assert ((q = (g * k)) == true);
              if deg g = 0 then ()
              else if deg k < 0 then begin
                UN.degree_none_poly_eq_zero #t k;
                poly_mul_congruence g k g (poly_zero #t);
                H.x_mul_zero #(polynomial t) g;
                transitivity (g * k) (g * (poly_zero #t)) (poly_zero #t);
                transitivity q (g * k) (poly_zero #t);
                UN.degree_well_defined q (poly_zero #t)
              end else begin
                unit_cofactor_divides q g k;
                divides_trans #(polynomial t) q g a
              end
            end
        in
        show_coprime ();
        coprime_reveal q a;
        poly_mul_commutativity a b;
        divides_congruence_right #(polynomial t) q (a * b) (b * a);
        euclid_lemma q a b
    in
    Classical.move_requires notb ()

(* irreducible q dividing a product of a LIST divides some element. *)
(* Opaque "some index of ms is divisible by q", hiding the existence. *)
[@@"opaque_to_smt"]
let some_index_divides (#t:Type) {| f: field t |} (q: polynomial t) (ms: list (polynomial t))
  : prop = exists (k:nat). k < L.length ms /\ divides #(polynomial t) q (L.index ms k)

let some_index_divides_elim (#t:Type) {| f: field t |}
  (q: polynomial t) (ms: list (polynomial t){some_index_divides q ms})
  : Lemma (exists (k:nat). k < L.length ms /\ divides #(polynomial t) q (L.index ms k))
  = reveal_opaque (`%some_index_divides) (some_index_divides q ms)

let rec irreducible_divides_prod (#t:Type) {| f: field t |}
  (q: polynomial t) (ms: list (polynomial t))
  : Lemma (requires IR.poly_irreducible q /\
                    divides #(polynomial t) q (PR.poly_prod ms))
          (ensures  some_index_divides q ms)
          (decreases ms)
  =
    reveal_opaque (`%some_index_divides) (some_index_divides q ms);
    match ms with
    | [] ->
        (* poly_prod [] = poly_one ; q | one with deg q >= 1 is impossible. *)
        IR.divides_degree_le q (poly_one #t)
    | x :: rest ->
        irreducible_prime q x (PR.poly_prod rest);
        assert (L.index (x :: rest) 0 == x);
        eliminate (divides #(polynomial t) q x) \/
                  (divides #(polynomial t) q (PR.poly_prod rest))
        returns (exists (k:nat). k < L.length ms /\
                   divides #(polynomial t) q (L.index ms k))
        with _hx. ()
        and _hr.
          begin
            irreducible_divides_prod q rest;
            some_index_divides_elim q rest;
            eliminate exists (j:nat). j < L.length rest /\
                        divides #(polynomial t) q (L.index rest j)
            returns (exists (k:nat). k < L.length ms /\
                       divides #(polynomial t) q (L.index ms k))
            with _hj.
              assert (L.index (x :: rest) (j ++ 1) == L.index rest j)
          end

(* ================================================================ *)
(*  PER-FACTOR KERNEL STRUCTURE (toward dim = #factors):             *)
(*    if q is an irreducible factor of f and h is a Berlekamp kernel  *)
(*    element (cong q (h^p) h), then h is congruent to a CONSTANT     *)
(*    modulo q:  q | (h - [c]) for some c in 𝔽_p.                     *)
(*                                                                   *)
(*  Proof: cong q (h^p) h  =>  q | (h^p - h) ~ prod_c (h - [c])       *)
(*  (reverse_divides), and an irreducible dividing a product       *)
(*  divides one of the factors (irreducible_divides_prod).           *)
(*                                                                   *)
(*  Combined with cong_prod_iff this gives, for squarefree            *)
(*  f = prod (distinct irreducibles), that every kernel element is    *)
(*  constant on each factor.  The CONVERSE is kernel_const_is_kernel   *)
(*  below, and the two are packaged as kernel_factor_iff.  Remaining   *)
(*  for "dim = #factors": a cardinality/dimension framework (count the *)
(*  p distinct constants per factor ⇒ |kernel| = p^r) — future work.   *)
(* ================================================================ *)
(* Opaque "some enum-index constant residue divides into q", hiding the   *)
(* existence over the field enumeration.  _elim restores the raw exists.   *)
[@@"opaque_to_smt"]
let some_const_index_divides (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : prop = exists (k:nat). k < L.length (fp_enum p) /\
             divides #(polynomial (fp p))
               q (h -- (poly_const #(fp p) (L.index (fp_enum p) k)))

let some_const_index_divides_elim (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : Lemma (requires some_const_index_divides p q h)
          (ensures (exists (k:nat). k < L.length (fp_enum p) /\
                      divides #(polynomial (fp p))
                        q (h -- (poly_const #(fp p) (L.index (fp_enum p) k)))))
  = reveal_opaque (`%some_const_index_divides) (some_const_index_divides p q h)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let kernel_factor_constant (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : Lemma (requires IR.poly_irreducible #(fp p) q /\
                    cong #(polynomial (fp p))
                            q (poly_power #(fp p) h (p <: nat)) h)
          (ensures some_const_index_divides p q h)
  = reveal_opaque (`%some_const_index_divides) (some_const_index_divides p q h);
    let shiftlist = L.map (shift_const #(fp p) h) (fp_enum p) in
    fp_enum_length p;
    reverse_divides p q h;                                      (* q | shift_product p h *)
    irreducible_divides_prod #(fp p) q shiftlist;    (* some_index_divides q shiftlist *)
    some_index_divides_elim #(fp p) q shiftlist;     (* exists k. q | shiftlist_k *)
    let bridge (k:nat{k < L.length shiftlist})
      : Lemma (L.index shiftlist k ==
               shift_const #(fp p) h (L.index (fp_enum p) k))
      = index_map (shift_const #(fp p) h) (fp_enum p) k
    in
    Classical.forall_intro bridge
#pop-options

(* const0 of a power = power of const0:  (const0 c)^k ~ const0 (rpow c k). *)
let rec const0_pow (p:int{EU.is_prime p}) (c: fp p) (k:nat)
  : Lemma (ensures (poly_power #(fp p) (poly_const #(fp p) c) k)
             = (poly_const #(fp p)
               (PW.rpow #(fp p) c k)))
          (decreases k)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let c0 = poly_const #(fp p) c in
    if k = 0 then begin
      assert (poly_power #(fp p) c0 0 == poly_one #(fp p));
      PW.rpow_zero #(fp p) c;
      poly_const_one #(fp p) ()
    end else begin
      let pk1 = poly_power #(fp p) c0 (k - 1) in
      let rk1 = PW.rpow #(fp p) c (k - 1) in
      assert (poly_power #(fp p) c0 k == c0 * pk1);
      PW.rpow_succ #(fp p) c (k - 1);
      const0_pow p c (k - 1);
      poly_mul_congruence c0 pk1 c0 (poly_const #(fp p) rk1);
      poly_const_mul #(fp p) c rk1;
      transitivity (c0 * pk1)
                   (c0 * (poly_const #(fp p) rk1))
                   (poly_const #(fp p) (c * rk1))
    end

(* CONVERSE of kernel_factor_constant:                               *)
(*   q | (h - const0 c)  ==>  cong q (h^p) h.                         *)
(* (h ≡ c (mod q) ==> h^p ≡ c^p = c ≡ h, using Fermat c^p=c in 𝔽_p.)  *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let kernel_const_is_kernel (p:int{EU.is_prime p})
  (q h: polynomial (fp p)) (c: fp p)
  : Lemma (requires divides #(polynomial (fp p))
                            q (h
                                 -- (poly_const #(fp p) c)))
          (ensures  cong #(polynomial (fp p))
                            q (poly_power #(fp p) h (p <: nat)) h)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let c0 = poly_const #(fp p) c in
    let hp = poly_power #(fp p) h (p <: nat) in
    let c0p = poly_power #(fp p) c0 (p <: nat) in
    cong_pow #(fp p) q h c0 (p <: nat);  (* cong q (h^p) (c0^p) *)
    const0_pow p c (p <: nat);                         (* c0^p ~ const0 (rpow c p) *)
    FR.fermat_fp p c;                                  (* rpow c p == c *)
    assert (PW.rpow #(fp p) c (p <: nat) == c);
    assert (poly_const #(fp p) (PW.rpow #(fp p) c (p <: nat)) == c0);
    cong_eq_right #(polynomial (fp p)) q hp c0p c0;
    cong_sym #(polynomial (fp p)) q h c0;
    cong_trans #(polynomial (fp p)) q hp c0 h
#pop-options

(* ================================================================ *)
(*  PER-FACTOR KERNEL CHARACTERIZATION (the clean #29 milestone):    *)
(*    for an irreducible factor q,                                   *)
(*       cong q (h^p) h   <==>   h ≡ a constant (mod q).             *)
(* ================================================================ *)
(* Opaque "h is congruent to SOME global constant modulo q"               *)
(* (q | (h - [c]) for some c in 𝔽_p), hiding the existence over c.        *)
(* _elim restores the raw exists; _intro builds it from a witness.        *)
[@@"opaque_to_smt"]
let kernel_is_const_shifted (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : prop = exists (c:fp p).
             divides #(polynomial (fp p))
               q (h -- (poly_const #(fp p) c))

let kernel_is_const_shifted_elim (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : Lemma (requires kernel_is_const_shifted p q h)
          (ensures (exists (c:fp p).
                      divides #(polynomial (fp p))
                        q (h -- (poly_const #(fp p) c))))
  = reveal_opaque (`%kernel_is_const_shifted) (kernel_is_const_shifted p q h)

let kernel_is_const_shifted_intro (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  (c:fp p)
  : Lemma (requires divides #(polynomial (fp p))
                      q (h -- (poly_const #(fp p) c)))
          (ensures  kernel_is_const_shifted p q h)
  = reveal_opaque (`%kernel_is_const_shifted) (kernel_is_const_shifted p q h)

(* forward half: a kernel element is congruent to a constant. *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let kernel_factor_iff_fwd (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : Lemma (requires IR.poly_irreducible #(fp p) q /\
                    cong #(polynomial (fp p))
                          q (poly_power #(fp p) h (p <: nat)) h)
          (ensures  kernel_is_const_shifted p q h)
  = kernel_factor_constant p q h;       (* some_const_index_divides p q h *)
    some_const_index_divides_elim p q h; (* recover raw exists k. q | (h - const0 (enum_k)) *)
    eliminate exists (k:nat).
        k < L.length (fp_enum p) /\
        divides #(polynomial (fp p))
          q (h -- (poly_const #(fp p) (L.index (fp_enum p) k)))
    returns kernel_is_const_shifted p q h
    with _hk.
      kernel_is_const_shifted_intro p q h (L.index (fp_enum p) k)
#pop-options

(* backward half: congruence to a constant puts h in the kernel. *)
let kernel_factor_iff_bwd (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : Lemma (requires kernel_is_const_shifted p q h)
          (ensures  cong #(polynomial (fp p))
                          q (poly_power #(fp p) h (p <: nat)) h)
  = kernel_is_const_shifted_elim p q h;
    eliminate exists (c:fp p).
        divides #(polynomial (fp p))
          q (h -- (poly_const #(fp p) c))
    returns cong #(polynomial (fp p))
                    q (poly_power #(fp p) h (p <: nat)) h
    with _hc. kernel_const_is_kernel p q h c

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let kernel_factor_iff (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : Lemma (requires IR.poly_irreducible #(fp p) q)
          (ensures  (cong #(polynomial (fp p))
                             q (poly_power #(fp p) h (p <: nat)) h
                     <==> kernel_is_const_shifted p q h))
  = Classical.move_requires (kernel_factor_iff_fwd p q) h;
    Classical.move_requires (kernel_factor_iff_bwd p q) h
#pop-options

(* The p constant residues are pairwise DISTINCT mod an irreducible q:    *)
(*   c <> c'  ==>  q does not divide  const0 c - const0 c'.                *)
(* (Their difference is a nonzero constant unit, which an irreducible of   *)
(*  degree >= 1 cannot divide.)  With kernel_factor_iff this pins the      *)
(*  per-factor kernel residues to EXACTLY the p distinct constants — the   *)
(*  "= p" count, modulo a cardinality framework still to be built.         *)
#push-options "--z3rlimit 100"
let const0_distinct_mod_irred (p:int{EU.is_prime p})
  (q: polynomial (fp p)) (c c': fp p)
  : Lemma (requires IR.poly_irreducible #(fp p) q /\ not (c = c'))
          (ensures  ~(divides #(polynomial (fp p))
                        q ((poly_const #(fp p) c)
                             -- (poly_const #(fp p) c'))))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let s0  = (poly_const #(fp p) c) -- (poly_const #(fp p) c') in
    let scp = (poly_const #(fp p) c)
                                   -- (poly_const #(fp p) c') in
    const0_eq_poly_const p c;
    const0_eq_poly_const p c';
    poly_sub_congr #(fp p)
      (poly_const #(fp p) c) (poly_const #(fp p) c')
      (poly_const #(fp p) c) (poly_const #(fp p) c');
    const_diff_deg #(fp p) c' c;   (* poly_deg scp == Some 0 *)
    UN.degree_well_defined #(fp p) s0 scp;        (* poly_deg s0 == Some 0 *)
    let contra () : Lemma (requires divides #(polynomial (fp p)) q s0)
                          (ensures  False)
      = IR.divides_degree_le #(fp p) q s0
    in
    Classical.move_requires contra ()
#pop-options

(* =========================  SECTION: BerlekampCriterion  ========================= *)
#set-options "--fuel 1 --ifuel 1 --z3rlimit 100"

(* L1.  A nonunit (degree >= 1) does NOT divide a nonzero constant
   difference  const0 c - const0 c'  (c <> c').  Generalizes
   BerlekampKernel.const0_distinct_mod_irred from irreducible to nonunit. *)
let nonunit_not_div_const_diff (p:int{EU.is_prime p})
  (q: polynomial (fp p)) (c c': fp p)
  : Lemma (requires deg #(fp p) q >= 1 /\ not (c = c'))
          (ensures  ~(divides #(polynomial (fp p))
                        q ((poly_const #(fp p) c)
                             -- (poly_const #(fp p) c'))))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let s0  = (poly_const #(fp p) c) -- (poly_const #(fp p) c') in
    let scp = (poly_const #(fp p) c)
                                   -- (poly_const #(fp p) c') in
    const0_eq_poly_const p c;
    const0_eq_poly_const p c';
    poly_sub_congr #(fp p)
      (poly_const #(fp p) c) (poly_const #(fp p) c')
      (poly_const #(fp p) c) (poly_const #(fp p) c');
    const_diff_deg #(fp p) c' c;   (* poly_deg scp == Some 0 *)
    UN.degree_well_defined #(fp p) s0 scp;        (* poly_deg s0 == Some 0 *)
    let contra () : Lemma (requires divides #(polynomial (fp p)) q s0)
                          (ensures  False)
      = IR.divides_degree_le #(fp p) q s0   (* deg q <= deg s0 = 0, contra deg q >= 1 *)
    in
    Classical.move_requires contra ()

(* L2.  A w with  w ≡ 0 (mod q1)  and  w ≡ 1 (mod m)  is in the kernel
   of (q1*m):  cong (q1*m) (w^p) w.  (Constant on each coprime factor.) *)
let splitter_in_kernel (p:int{EU.is_prime p}) (q1 m w: polynomial (fp p))
  : Lemma (requires coprime #(fp p) q1 m /\
                    deg #(fp p) q1 >= 0 /\
                    divides #(polynomial (fp p))
                      q1 (w
                            -- (poly_const #(fp p) (0 <: fp p))) /\
                    divides #(polynomial (fp p))
                      m (w
                            -- (poly_const #(fp p) (1 <: fp p))))
          (ensures  cong #(polynomial (fp p))
                      (q1 * m) (poly_power #(fp p) w (p <: nat)) w)
  = kernel_const_is_kernel p q1 w (0 <: fp p);     (* cong q1 (w^p) w *)
    kernel_const_is_kernel p m  w (1 <: fp p);     (* cong m  (w^p) w *)
    cong_mul_iff #(fp p) q1 m
      (poly_power #(fp p) w (p <: nat)) w

(* helper: x | (w-ca) and x | (w-cb)  ==>  x | (cb - ca). *)
let div_const_diff_helper (p:int{EU.is_prime p})
  (x w ca cb: polynomial (fp p))
  : Lemma (requires divides #(polynomial (fp p))
                            x (w -- ca) /\
                    divides #(polynomial (fp p))
                            x (w -- cb))
          (ensures  divides #(polynomial (fp p))
                            x (cb -- ca))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let a = w -- ca in
    let b = w -- cb in
    divides_sub #(polynomial (fp p)) x a b;            (* x | a + neg b *)
    abstract_shift_diff #(polynomial (fp p)) w ca cb;  (* (w-ca)-(w-cb) = cb-ca *)
    divides_congruence_right #(polynomial (fp p))
      x (add #(polynomial (fp p)) a
             (- b))
        (cb -- ca)

(* Opaque "w is congruent to NO global constant modulo mm"                 *)
(* (no d in 𝔽_p has mm | (w - [d])), hiding the negated existence.         *)
(* _elim restores the raw ~(exists ...) for consumers.                     *)
[@@"opaque_to_smt"]
let no_const_divisor (p:int{EU.is_prime p}) (mm w: polynomial (fp p))
  : prop = ~(exists (d:fp p).
              divides #(polynomial (fp p))
                mm (w -- (poly_const #(fp p) d)))

let no_const_divisor_elim (p:int{EU.is_prime p}) (mm w: polynomial (fp p))
  : Lemma (requires no_const_divisor p mm w)
          (ensures ~(exists (d:fp p).
                       divides #(polynomial (fp p))
                         mm (w -- (poly_const #(fp p) d))))
  = reveal_opaque (`%no_const_divisor) (no_const_divisor p mm w)

(* L3.  Such a w is NOT congruent to any global constant mod (q1*m):
   if (q1*m) | (w - const0 d) then w ≡ d on both factors, forcing
   d = 0 (from q1, w≡0) and then m | (const0 1 - const0 0), impossible. *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let splitter_not_constant (p:int{EU.is_prime p}) (q1 m w: polynomial (fp p))
  : Lemma (requires deg #(fp p) q1 >= 1 /\
                    deg #(fp p) m >= 1 /\
                    divides #(polynomial (fp p))
                      q1 (w
                            -- (poly_const #(fp p) (0 <: fp p))) /\
                    divides #(polynomial (fp p))
                      m (w
                            -- (poly_const #(fp p) (1 <: fp p))))
          (ensures  no_const_divisor p (q1 * m) w)
  = reveal_opaque (`%no_const_divisor) (no_const_divisor p (q1 * m) w);
    let c0d (d:fp p) = poly_const #(fp p) d in
    let bad (d:fp p)
      : Lemma (requires divides #(polynomial (fp p))
                          (q1 * m) (w -- (c0d d)))
              (ensures  False)
      = divides_self_mul #(fp p) q1 m;                 (* q1|(q1*m), m|(q1*m) *)
        divides_trans #(polynomial (fp p)) q1 (q1 * m)
          (w -- (c0d d));           (* q1 | (w - const0 d) *)
        divides_trans #(polynomial (fp p)) m (q1 * m)
          (w -- (c0d d));           (* m  | (w - const0 d) *)
        if d = (0 <: fp p) then begin
          div_const_diff_helper p m w (c0d d) (c0d (1 <: fp p));         (* m | (const0 1 - const0 d) *)
          nonunit_not_div_const_diff p m (1 <: fp p) d                   (* 1<>0=d : contradiction *)
        end else begin
          div_const_diff_helper p q1 w (c0d d) (c0d (0 <: fp p));        (* q1 | (const0 0 - const0 d) *)
          nonunit_not_div_const_diff p q1 (0 <: fp p) d                  (* 0<>d : contradiction *)
        end
    in
    Classical.forall_intro (Classical.move_requires bad)
#pop-options

(* Opaque "there is a nontrivial Berlekamp splitter for mm = q1*m":          *)
(* a kernel element w of mm that is congruent to no global constant.          *)
(* _elim restores the raw existential for consumers.                          *)
[@@"opaque_to_smt"]
let splitter_witness_exists (p:int{EU.is_prime p}) (q1 m: polynomial (fp p))
  : prop = exists (w: polynomial (fp p)).
             cong #(polynomial (fp p))
               (q1 * m) (poly_power #(fp p) w (p <: nat)) w /\
             no_const_divisor p (q1 * m) w

let splitter_witness_exists_elim (p:int{EU.is_prime p}) (q1 m: polynomial (fp p))
  : Lemma (requires splitter_witness_exists p q1 m)
          (ensures (exists (w: polynomial (fp p)).
                      cong #(polynomial (fp p))
                        (q1 * m) (poly_power #(fp p) w (p <: nat)) w /\
                      ~(exists (d:fp p).
                          divides #(polynomial (fp p))
                            (q1 * m)
                            (w -- (poly_const #(fp p) d)))))
  = reveal_opaque (`%splitter_witness_exists) (splitter_witness_exists p q1 m);
    eliminate exists (wit: polynomial (fp p)).
        cong #(polynomial (fp p))
          (q1 * m) (poly_power #(fp p) wit (p <: nat)) wit /\
        no_const_divisor p (q1 * m) wit
    returns (exists (w: polynomial (fp p)).
               cong #(polynomial (fp p))
                 (q1 * m) (poly_power #(fp p) w (p <: nat)) w /\
               ~(exists (d:fp p).
                   divides #(polynomial (fp p))
                     (q1 * m)
                     (w -- (poly_const #(fp p) d))))
    with _hw.
      let w : polynomial (fp p) = wit in
      no_const_divisor_elim p (q1 * m) w;
      introduce exists (w0: polynomial (fp p)).
                  (cong #(polynomial (fp p))
                     (q1 * m) (poly_power #(fp p) w0 (p <: nat)) w0 /\
                   ~(exists (d:fp p).
                       divides #(polynomial (fp p))
                         (q1 * m)
                         (w0 -- (poly_const #(fp p) d))))
      with w and ()

(* L4 (the criterion).  For coprime nonunit moduli q1, m there EXISTS a
   Berlekamp kernel element of (q1*m) that is not a global constant —
   a genuine nontrivial splitter (CRT witness w ≡ 0 mod q1, w ≡ 1 mod m). *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let berlekamp_splitter_exists (p:int{EU.is_prime p}) (q1 m: polynomial (fp p))
  : Lemma (requires coprime #(fp p) q1 m /\
                    deg #(fp p) q1 >= 1 /\
                    deg #(fp p) m >= 1)
          (ensures  splitter_witness_exists p q1 m)
  = reveal_opaque (`%splitter_witness_exists) (splitter_witness_exists p q1 m);
    let b = poly_const #(fp p) (0 <: fp p) in
    let c = poly_const #(fp p) (1 <: fp p) in
    let w = CR.crt_witness #(fp p) q1 m b c in
    CR.crt_surj_f #(fp p) q1 m b c;   (* q1 | (w - b) = q1 | (w - const0 0) *)
    CR.crt_surj_g #(fp p) q1 m b c;   (* m  | (w - c) = m  | (w - const0 1) *)
    splitter_in_kernel    p q1 m w;                 (* cong (q1*m) (w^p) w *)
    splitter_not_constant p q1 m w;                 (* no_const_divisor p (q1*m) w *)
    introduce exists (w0: polynomial (fp p)).
                (cong #(polynomial (fp p))
                   (q1 * m) (poly_power #(fp p) w0 (p <: nat)) w0 /\
                 no_const_divisor p (q1 * m) w0)
    with w and ()
#pop-options

(* The complementary direction: if f is IRREDUCIBLE, every Berlekamp kernel
   element is congruent to a (global) constant — so there is no nontrivial
   splitter.  (Directly the forward half of kernel_factor_iff at q = f.)

   L4 + this give the Berlekamp irreducibility criterion:
     f has a non-constant kernel element  <==>  f is reducible
   (a coprime nonunit factorization), which with #28 turns any such element
   into a genuine factorization  f ~ prod_c gcd(f, w - c). *)
let irreducible_kernel_is_constant (p:int{EU.is_prime p}) (f h: polynomial (fp p))
  : Lemma (requires IR.poly_irreducible #(fp p) f /\
                    cong #(polynomial (fp p))
                            f (poly_power #(fp p) h (p <: nat)) h)
          (ensures  kernel_is_const_shifted p f h)
  = kernel_factor_iff p f h

