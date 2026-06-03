module Core.Field.Berlekamp

(* ================================================================ *)
(*  Berlekamp factorization over the finite prime field F_p.        *)
(*                                                                   *)
(*  Field-generic development: every construction below works over   *)
(*  an arbitrary `field t` and therefore instantiates at `fp p`      *)
(*  (Core.Field.Fp) for `p` prime.  The Berlekamp-specific pieces    *)
(*  (the Frobenius `Q` matrix) additionally require the FROBENIUS    *)
(*  exponent `p`, which the caller supplies; nothing here assumes    *)
(*  primality beyond what the `field` instance already carries.      *)
(*                                                                   *)
(*  Contents:                                                        *)
(*    1. poly_pow_mod  (g^k mod m, total) + poly_pow (g^k)           *)
(*    2. cong: congruence modulo m in a commutative ring + its       *)
(*       equivalence relation / multiplicative-congruence algebra    *)
(*    3. poly_pow_mod correctness:  poly_pow_mod g k m ≡ g^k (mod m) *)
(*    4. Berlekamp Q matrix (Frobenius map) as a square_matrix       *)
(*    5. Q - I and the kernel via Core.Matrix.KernelDet              *)
(*    6. Factor extraction  gcd(f, h - c)  + the divisibility facts  *)
(*       reachable without the full CRT decomposition.               *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Eval
open Core.Polynomial.Root
open Core.Permutation
open Core.Vector
open Core.Matrix
open Core.Matrix.Determinant
open Core.Matrix.KernelDet

(* The polynomial commutative ring over a field t. *)
let crp (t:Type) {| f: field t |} : commutative_ring (polynomial t) = TC.solve

(* ================================================================ *)
(*  1.  Modular exponentiation and ordinary power                    *)
(* ================================================================ *)

(* g^k mod m, naive iteration:  reduce after every multiply. *)
let rec poly_pow_mod (#t:Type) {| f: field t |} (g: polynomial t) (k:nat) (m: polynomial t)
  : Tot (polynomial t) (decreases k)
  = if k = 0 then poly_rem (poly_one #t) m
    else poly_rem (poly_mul g (poly_pow_mod g (k-1) m)) m

let poly_pow_mod_zero (#t:Type) {| f: field t |} (g m: polynomial t)
  : Lemma (poly_pow_mod g 0 m == poly_rem (poly_one #t) m)
  = ()

let poly_pow_mod_succ (#t:Type) {| f: field t |} (g m: polynomial t) (k:nat)
  : Lemma (poly_pow_mod g (Prims.op_Addition k 1) m
           == poly_rem (poly_mul g (poly_pow_mod g k m)) m)
  = ()

(* ordinary power g^k (no reduction). *)
let rec poly_pow (#t:Type) {| f: field t |} (g: polynomial t) (k:nat)
  : Tot (polynomial t) (decreases k)
  = if k = 0 then poly_one #t
    else poly_mul g (poly_pow g (k-1))

let poly_pow_zero (#t:Type) {| f: field t |} (g: polynomial t)
  : Lemma (poly_pow g 0 == poly_one #t)
  = ()

let poly_pow_succ (#t:Type) {| f: field t |} (g: polynomial t) (k:nat)
  : Lemma (poly_pow g (Prims.op_Addition k 1) == poly_mul g (poly_pow g k))
  = ()

(* ================================================================ *)
(*  2.  Congruence modulo m in a commutative ring                    *)
(*      cong m x y  :=  m | (x - y)                                  *)
(* ================================================================ *)

let cong (#a:Type) {| cr: commutative_ring a |} (m x y: a) : prop =
  divides m (x + (neg y))

let cong_refl (#a:Type) {| cr: commutative_ring a |} (m x: a)
  : Lemma (cong m x x)
  = H.elim_equatable_laws a ();
    H.x_plus_neg_x x;
    divides_zero m;
    divides_congruence_right m (zero <: a) (x + neg x)

let cong_sym (#a:Type) {| cr: commutative_ring a |} (m x y: a)
  : Lemma (requires cong m x y) (ensures cong m y x)
  = H.elim_equatable_laws a ();
    divides_neg m (x + neg y);
    assert (eq (neg (x + neg y)) (y + neg x)) by (Core.Tactics.CanonRing.canon_ring ());
    divides_congruence_right m (neg (x + neg y)) (y + neg x)

let cong_trans (#a:Type) {| cr: commutative_ring a |} (m x y z: a)
  : Lemma (requires cong m x y /\ cong m y z) (ensures cong m x z)
  = H.elim_equatable_laws a ();
    divides_add m (x + neg y) (y + neg z);
    assert (eq ((x + neg y) + (y + neg z)) (x + neg z)) by (Core.Tactics.CanonRing.canon_ring ());
    divides_congruence_right m ((x + neg y) + (y + neg z)) (x + neg z)

(* multiplicative compatibility *)
let cong_mul (#a:Type) {| cr: commutative_ring a |} (m x1 x2 y1 y2: a)
  : Lemma (requires cong m x1 x2 /\ cong m y1 y2)
          (ensures  cong m (x1 * y1) (x2 * y2))
  = H.elim_equatable_laws a ();
    divides_mul_right m (x1 + neg x2) y1;
    divides_mul_left  m x2 (y1 + neg y2);
    divides_add m ((x1 + neg x2) * y1) (x2 * (y1 + neg y2));
    assert (eq (((x1 + neg x2) * y1) + (x2 * (y1 + neg y2))) ((x1 * y1) + neg (x2 * y2)))
      by (Core.Tactics.CanonRing.canon_ring ());
    divides_congruence_right m (((x1 + neg x2) * y1) + (x2 * (y1 + neg y2)))
                               ((x1 * y1) + neg (x2 * y2))

(* congruence respects ring equality on the right operand *)
let cong_eq_right (#a:Type) {| cr: commutative_ring a |} (m x y y': a)
  : Lemma (requires cong m x y /\ eq y y') (ensures cong m x y')
  = H.elim_equatable_laws a ();
    neg_congruence y y';                          (* neg y = neg y' *)
    reflexivity x;
    add_congruence x (neg y) x (neg y');          (* x + neg y = x + neg y' *)
    divides_congruence_right m (x + neg y) (x + neg y')

(* ================================================================ *)
(*  helper:  p = m*q + r  ==>  m | (p - r)                            *)
(* ================================================================ *)

let cong_of_divmod (#a:Type) {| cr: commutative_ring a |} (p m q r: a)
  : Lemma (requires p `eq` ((m * q) + r))
          (ensures  cong m p r)
  = H.elim_equatable_laws a ();
    H.trans_for_calc a ();
    let mq = m * q in
    add_congruence p (neg r) (mq + r) (neg r);
    add_associativity mq r (neg r);
    H.x_plus_neg_x r;
    add_congruence mq (r + neg r) mq (zero <: a);
    H.x_plus_zero mq;
    H.trans3 (p + neg r) ((mq + r) + neg r) (mq + (r + neg r)) mq;
    divides_intro m (p + neg r) q

(* the remainder is congruent to the dividend modulo m *)
let rem_cong (#t:Type) {| f: field t |} (p m: polynomial t)
  : Lemma (cong #(polynomial t) #(crp t) m p (poly_rem #t #f p m))
  = let cr = crp t in
    poly_divmod_correct #t #f p m;
    poly_div_reveal #t #f p m;
    poly_rem_reveal #t #f p m;
    let q = poly_div #t #f p m in
    let r = poly_rem #t #f p m in
    cong_of_divmod #(polynomial t) #cr p m q r

(* ================================================================ *)
(*  3.  poly_pow_mod g k m  ≡  g^k   (mod m)                          *)
(* ================================================================ *)

let rec poly_pow_mod_correct (#t:Type) {| f: field t |}
  (g: polynomial t) (k:nat) (m: polynomial t)
  : Lemma (ensures cong #(polynomial t) #(crp t) m (poly_pow_mod g k m) (poly_pow g k))
          (decreases k)
  = let cr = crp t in
    if k = 0 then begin
      (* poly_pow_mod g 0 m = poly_rem one m ; poly_pow g 0 = one *)
      rem_cong #t #f (poly_one #t) m;                   (* cong m one (rem one m) *)
      cong_sym #(polynomial t) #cr m
        (poly_one #t) (poly_rem (poly_one #t) m)        (* cong m (rem one m) one *)
    end
    else begin
      (* IH: poly_pow_mod g (k-1) m ≡ g^(k-1) *)
      poly_pow_mod_correct g (k-1) m;
      let pm1 = poly_pow_mod g (k-1) m in
      let pw1 = poly_pow g (k-1) in
      (* g ≡ g  ⟹  g * pm1  ≡  g * pw1 = g^k.  Use poly_mul to match rem_cong. *)
      cong_refl #(polynomial t) #cr m g;
      cong_mul #(polynomial t) #cr m g g pm1 pw1;       (* cong m (poly_mul g pm1) (poly_mul g pw1) *)
      (* poly_pow_mod g k m = rem (poly_mul g pm1) m  ≡  poly_mul g pm1 *)
      rem_cong #t #f (poly_mul g pm1) m;                (* cong m (poly_mul g pm1) (rem (g*pm1) m) *)
      cong_sym #(polynomial t) #cr m
        (poly_mul g pm1) (poly_rem (poly_mul g pm1) m); (* cong m (rem (g*pm1) m) (poly_mul g pm1) *)
      (* chain: rem(g*pm1) ≡ poly_mul g pm1 ≡ poly_mul g pw1 = g^k *)
      poly_pow_mod_succ g m (k-1);                      (* poly_pow_mod g k m = rem (poly_mul g pm1) m *)
      poly_pow_succ g (k-1);                            (* poly_pow g k = poly_mul g pw1 *)
      cong_trans #(polynomial t) #cr m
        (poly_pow_mod g k m) (poly_mul g pm1) (poly_pow g k)
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
  = monomial #t #(cr_of_id t #(id_of_f t)) (one #t) k

(* column j of Q as a polynomial:  (x^j)^q  mod f. *)
let berlekamp_qcol (#t:Type) {| f: field t |}
  (fpoly: polynomial t) (q:nat) (j:nat) : polynomial t
  = poly_pow_mod (mono_x #t #f j) q fpoly

(* The Berlekamp Q matrix as an n x n matrix over the field. *)
let berlekamp_Q (#t:Type) {| f: field t |}
  (fpoly: polynomial t) (q:nat) (n:pos) (i j: fin n) : t
  = coeff (berlekamp_qcol #t #f fpoly q (j <: nat)) (i <: nat)

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
  = berlekamp_Q #t #f fpoly q n i j -- (id_matrix #t #(r_of_sf t) #n i j)

(* The transpose, whose rows are what a kernel column-vector dots with
   in the Frobenius equation  Q·v = v  (i.e. (Q - I)·v = 0). *)
let berlekamp_QmI_t (#t:Type) {| f: field t |}
  (fpoly: polynomial t) (q:nat) (n:pos) (i j: fin n) : t
  = berlekamp_QmI #t #f fpoly q n j i

(* Kernel extraction: if  det(Q - I) = 0  then there is a nonzero coefficient
   vector  v  with  (Q - I)·v = 0  (i.e. row-wise  Σ_j (Q-I)[i][j]·v[j] = 0).
   This is the Berlekamp subalgebra membership at the coefficient-vector level;
   it is an immediate specialisation of `det_zero_implies_null_vec` to Q - I. *)
let berlekamp_kernel_vector (#t:Type) {| f: field t |}
  (fpoly: polynomial t) (q:nat) (n:pos)
  : Lemma (requires det (berlekamp_QmI #t #f fpoly q n) = (zero <: t))
          (ensures  exists (v: fin n -> t) (k: fin n).
                      is_nonzero (v k) /\
                      (forall (i: fin n).
                        vector_dot (row (berlekamp_QmI #t #f fpoly q n) i) v = (zero <: t)))
  = det_zero_implies_null_vec #t #f #n (berlekamp_QmI #t #f fpoly q n)

(* ================================================================ *)
(*  6.  Factor extraction                                            *)
(*                                                                   *)
(*  For a Berlekamp kernel element h and a constant c ∈ F,           *)
(*  gcd(f, h - c) is a factor of f.  We build the splitting step as  *)
(*  a computable function and prove the reachable divisibility       *)
(*  facts (each gcd divides f; the gcd's residue condition).         *)
(* ================================================================ *)

(* the constant polynomial [c]  (a Berlekamp "shift" by c ∈ F). *)
let const_poly (#t:Type) {| f: field t |} (c: t) : polynomial t
  = trim #t #(cr_of_id t #(id_of_f t)) [c]

(* the splitting step:  gcd(f, h - c). *)
let berlekamp_split (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (c: t) : polynomial t
  = poly_gcd #t #f fpoly (poly_sub h (const_poly #t #f c))

(* each candidate factor divides f. *)
let berlekamp_split_divides_f (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (c: t)
  : Lemma (divides #(polynomial t) #(crp t)
                   (berlekamp_split #t #f fpoly h c) fpoly)
  = gcd_divides_left #t #f fpoly (poly_sub h (const_poly #t #f c))

(* each candidate factor divides h - c (the residue condition). *)
let berlekamp_split_divides_shift (#t:Type) {| f: field t |}
  (fpoly h: polynomial t) (c: t)
  : Lemma (divides #(polynomial t) #(crp t)
                   (berlekamp_split #t #f fpoly h c)
                   (poly_sub h (const_poly #t #f c)))
  = gcd_divides_right #t #f fpoly (poly_sub h (const_poly #t #f c))

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
  : Lemma (cong #(polynomial t) #(crp t) fpoly (poly_pow h q) h
           <==>
           cong #(polynomial t) #(crp t) fpoly (poly_pow_mod h q fpoly) h)
  = let cr = crp t in
    (* poly_pow_mod h q f ≡ h^q (mod f) — proven, both orientations via sym *)
    poly_pow_mod_correct #t #f h q fpoly;               (* cong f (powmod) (pow) *)
    let fwd () : Lemma (requires cong #(polynomial t) #cr fpoly (poly_pow h q) h)
                       (ensures  cong #(polynomial t) #cr fpoly (poly_pow_mod h q fpoly) h)
      = (* powmod ≡ pow ≡ h *)
        cong_trans #(polynomial t) #cr fpoly
          (poly_pow_mod h q fpoly) (poly_pow h q) h
    in
    let bwd () : Lemma (requires cong #(polynomial t) #cr fpoly (poly_pow_mod h q fpoly) h)
                       (ensures  cong #(polynomial t) #cr fpoly (poly_pow h q) h)
      = (* pow ≡ powmod (sym) ≡ h *)
        cong_sym #(polynomial t) #cr fpoly (poly_pow_mod h q fpoly) (poly_pow h q);
        cong_trans #(polynomial t) #cr fpoly
          (poly_pow h q) (poly_pow_mod h q fpoly) h
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
  : Lemma (requires cong #(polynomial t) #(crp t) fpoly (poly_pow h q) h)
          (ensures  divides #(polynomial t) #(crp t)
                            (berlekamp_split #t #f fpoly h c) fpoly /\
                    divides #(polynomial t) #(crp t)
                            (berlekamp_split #t #f fpoly h c)
                            (poly_sub h (const_poly #t #f c)))
  = berlekamp_split_divides_f #t #f fpoly h c;
    berlekamp_split_divides_shift #t #f fpoly h c
