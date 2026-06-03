module Core.Field.BerlekampCriterion

(* ================================================================ *)
(*  Berlekamp reducibility criterion (the algorithmically-essential  *)
(*  content of #29, via CRT — NO abstract dimension/cardinality):    *)
(*                                                                   *)
(*  For COPRIME NONUNIT moduli q1, m over 𝔽_p there is a Berlekamp    *)
(*  kernel element w of (q1*m) that is NOT congruent to any constant *)
(*  modulo (q1*m).  Concretely w ≡ 0 (mod q1), w ≡ 1 (mod m) (CRT),   *)
(*  so it lies in the kernel (constant on each factor) yet is not a   *)
(*  global scalar (0 ≠ 1).  Such a w yields a nontrivial split        *)
(*  f ~ ∏_c gcd(f, w-c) (#28).                                       *)
(*                                                                   *)
(*  STRUCTURAL PLAN (drilled below, lemma by lemma):                 *)
(*    L1  nonunit_not_div_const_diff : deg q>=1, c<>c' => ~(q|[c-c']) *)
(*    L2  splitter_in_kernel        : the CRT witness is in kernel    *)
(*    L3  splitter_not_constant     : ... and is not a global scalar  *)
(*    L4  berlekamp_splitter_exists : exists such w                   *)
(*  (Remaining for full "dim = #factors": a cardinality framework —   *)
(*   future; this criterion is what the algorithm actually needs.)   *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module BK = Core.Field.Berlekamp
module SU = Core.Polynomial.Subst
module SP = Core.Field.SubstProd
module BR = Core.Field.BerlekampReverse
module BSC = Core.Field.BerlekampSplitCorrect
module BKR = Core.Field.BerlekampKernel
module CR = Core.Polynomial.CRT
module IR = Core.Polynomial.Irreducible
module UN = Core.Polynomial.Unique

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Field.Fp
module EU = FStar.Math.Euclid

#set-options "--fuel 1 --ifuel 1 --z3rlimit 100"

(* L1.  A nonunit (degree >= 1) does NOT divide a nonzero constant
   difference  const0 c - const0 c'  (c <> c').  Generalizes
   BerlekampKernel.const0_distinct_mod_irred from irreducible to nonunit. *)
let nonunit_not_div_const_diff (p:int{EU.is_prime p})
  (q: polynomial (fp p) #(fp_comm_ring p)) (c c': fp p)
  : Lemma (requires Some? (poly_deg #(fp p) #(fp_comm_ring p) q) /\
                    Some?.v (poly_deg #(fp p) #(fp_comm_ring p) q) >= 1 /\ not (c = c'))
          (ensures  ~(divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                        q (poly_sub #(fp p) #(SP.fcr (fp_field p))
                             (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c)
                             (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c'))))
  = let cr = SP.fcr (fp_field p) in
    H.elim_equatable_laws (polynomial (fp p)) #((SU.pacg cr).acg_eq) ();
    let s0  = poly_sub #(fp p) #cr (SU.const0 #(fp p) #cr c) (SU.const0 #(fp p) #cr c') in
    let scp = poly_sub #(fp p) #cr (BK.const_poly #(fp p) #(fp_field p) c)
                                   (BK.const_poly #(fp p) #(fp_field p) c') in
    BR.const0_eq_const_poly p c;
    BR.const0_eq_const_poly p c';
    SP.poly_sub_congr #(fp p) #(fp_field p)
      (SU.const0 #(fp p) #cr c) (SU.const0 #(fp p) #cr c')
      (BK.const_poly #(fp p) #(fp_field p) c) (BK.const_poly #(fp p) #(fp_field p) c');
    BSC.const_diff_deg #(fp p) #(fp_field p) c' c;   (* poly_deg scp == Some 0 *)
    UN.degree_well_defined #(fp p) #cr s0 scp;        (* poly_deg s0 == Some 0 *)
    let contra () : Lemma (requires divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p)) q s0)
                          (ensures  False)
      = IR.divides_degree_le #(fp p) #(fp_field p) q s0   (* deg q <= deg s0 = 0, contra deg q >= 1 *)
    in
    Classical.move_requires contra ()

(* L2.  A w with  w ≡ 0 (mod q1)  and  w ≡ 1 (mod m)  is in the kernel
   of (q1*m):  cong (q1*m) (w^p) w.  (Constant on each coprime factor.) *)
let splitter_in_kernel (p:int{EU.is_prime p}) (q1 m w: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (requires coprime #(fp p) #(fp_field p) q1 m /\
                    Some? (poly_deg #(fp p) #(fp_comm_ring p) q1) /\
                    divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                      q1 (poly_sub #(fp p) #(SP.fcr (fp_field p)) w
                            (SU.const0 #(fp p) #(SP.fcr (fp_field p)) (0 <: fp p))) /\
                    divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                      m (poly_sub #(fp p) #(SP.fcr (fp_field p)) w
                            (SU.const0 #(fp p) #(SP.fcr (fp_field p)) (1 <: fp p))))
          (ensures  BK.cong #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                      (poly_mul q1 m) (BK.poly_pow #(fp p) #(fp_field p) w (p <: nat)) w)
  = BKR.kernel_const_is_kernel p q1 w (0 <: fp p);     (* cong q1 (w^p) w *)
    BKR.kernel_const_is_kernel p m  w (1 <: fp p);     (* cong m  (w^p) w *)
    BKR.cong_mul_iff #(fp p) #(fp_field p) q1 m
      (BK.poly_pow #(fp p) #(fp_field p) w (p <: nat)) w

(* helper: x | (w-ca) and x | (w-cb)  ==>  x | (cb - ca). *)
let div_const_diff_helper (p:int{EU.is_prime p})
  (x w ca cb: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (requires divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                            x (poly_sub #(fp p) #(SP.fcr (fp_field p)) w ca) /\
                    divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                            x (poly_sub #(fp p) #(SP.fcr (fp_field p)) w cb))
          (ensures  divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                            x (poly_sub #(fp p) #(SP.fcr (fp_field p)) cb ca))
  = let cr_p : commutative_ring (polynomial (fp p)) = BK.crp (fp p) #(fp_field p) in
    H.elim_equatable_laws (polynomial (fp p)) #(cr_p.cr_r.r_add.acg_eq) ();
    let a = poly_sub #(fp p) #(SP.fcr (fp_field p)) w ca in
    let b = poly_sub #(fp p) #(SP.fcr (fp_field p)) w cb in
    divides_sub #(polynomial (fp p)) #cr_p x a b;            (* x | a + neg b *)
    poly_sub_reveal #(fp p) #(SP.fcr (fp_field p)) w ca;     (* a == w + neg ca *)
    poly_sub_reveal #(fp p) #(SP.fcr (fp_field p)) w cb;     (* b == w + neg cb *)
    poly_sub_reveal #(fp p) #(SP.fcr (fp_field p)) cb ca;    (* (cb - ca) == cb + neg ca *)
    BSC.abstract_shift_diff #(polynomial (fp p)) #cr_p w ca cb;  (* (w-ca)-(w-cb) = cb-ca *)
    divides_congruence_right #(polynomial (fp p)) #cr_p
      x (add #(polynomial (fp p)) #(cr_p.cr_r.r_add) a
             (neg #(polynomial (fp p)) #(cr_p.cr_r.r_add) b))
        (poly_sub #(fp p) #(SP.fcr (fp_field p)) cb ca)

(* L3.  Such a w is NOT congruent to any global constant mod (q1*m):
   if (q1*m) | (w - const0 d) then w ≡ d on both factors, forcing
   d = 0 (from q1, w≡0) and then m | (const0 1 - const0 0), impossible. *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let splitter_not_constant (p:int{EU.is_prime p}) (q1 m w: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (requires Some? (poly_deg #(fp p) #(fp_comm_ring p) q1) /\
                    Some?.v (poly_deg #(fp p) #(fp_comm_ring p) q1) >= 1 /\
                    Some? (poly_deg #(fp p) #(fp_comm_ring p) m) /\
                    Some?.v (poly_deg #(fp p) #(fp_comm_ring p) m) >= 1 /\
                    divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                      q1 (poly_sub #(fp p) #(SP.fcr (fp_field p)) w
                            (SU.const0 #(fp p) #(SP.fcr (fp_field p)) (0 <: fp p))) /\
                    divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                      m (poly_sub #(fp p) #(SP.fcr (fp_field p)) w
                            (SU.const0 #(fp p) #(SP.fcr (fp_field p)) (1 <: fp p))))
          (ensures  ~(exists (d:fp p).
                        divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                          (poly_mul q1 m)
                          (poly_sub #(fp p) #(SP.fcr (fp_field p)) w
                             (SU.const0 #(fp p) #(SP.fcr (fp_field p)) d))))
  = let cr_p : commutative_ring (polynomial (fp p)) = BK.crp (fp p) #(fp_field p) in
    let c0d (d:fp p) = SU.const0 #(fp p) #(SP.fcr (fp_field p)) d in
    let bad (d:fp p)
      : Lemma (requires divides #(polynomial (fp p)) #cr_p
                          (poly_mul q1 m) (poly_sub #(fp p) #(SP.fcr (fp_field p)) w (c0d d)))
              (ensures  False)
      = BKR.divides_self_mul #(fp p) #(fp_field p) q1 m;                 (* q1|(q1*m), m|(q1*m) *)
        divides_trans #(polynomial (fp p)) #cr_p q1 (poly_mul q1 m)
          (poly_sub #(fp p) #(SP.fcr (fp_field p)) w (c0d d));           (* q1 | (w - const0 d) *)
        divides_trans #(polynomial (fp p)) #cr_p m (poly_mul q1 m)
          (poly_sub #(fp p) #(SP.fcr (fp_field p)) w (c0d d));           (* m  | (w - const0 d) *)
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

(* L4 (the criterion).  For coprime nonunit moduli q1, m there EXISTS a
   Berlekamp kernel element of (q1*m) that is not a global constant —
   a genuine nontrivial splitter (CRT witness w ≡ 0 mod q1, w ≡ 1 mod m). *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let berlekamp_splitter_exists (p:int{EU.is_prime p}) (q1 m: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (requires coprime #(fp p) #(fp_field p) q1 m /\
                    Some? (poly_deg #(fp p) #(fp_comm_ring p) q1) /\
                    Some?.v (poly_deg #(fp p) #(fp_comm_ring p) q1) >= 1 /\
                    Some? (poly_deg #(fp p) #(fp_comm_ring p) m) /\
                    Some?.v (poly_deg #(fp p) #(fp_comm_ring p) m) >= 1)
          (ensures  (exists (w: polynomial (fp p) #(fp_comm_ring p)).
                       BK.cong #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                         (poly_mul q1 m) (BK.poly_pow #(fp p) #(fp_field p) w (p <: nat)) w /\
                       ~(exists (d:fp p).
                           divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                             (poly_mul q1 m)
                             (poly_sub #(fp p) #(SP.fcr (fp_field p)) w
                                (SU.const0 #(fp p) #(SP.fcr (fp_field p)) d)))))
  = let b = SU.const0 #(fp p) #(SP.fcr (fp_field p)) (0 <: fp p) in
    let c = SU.const0 #(fp p) #(SP.fcr (fp_field p)) (1 <: fp p) in
    let w = CR.crt_witness #(fp p) #(fp_field p) q1 m b c in
    CR.crt_surj_f #(fp p) #(fp_field p) q1 m b c;   (* q1 | (w - b) = q1 | (w - const0 0) *)
    CR.crt_surj_g #(fp p) #(fp_field p) q1 m b c;   (* m  | (w - c) = m  | (w - const0 1) *)
    splitter_in_kernel    p q1 m w;                 (* cong (q1*m) (w^p) w *)
    splitter_not_constant p q1 m w;                 (* not a global constant *)
    introduce exists (w0: polynomial (fp p) #(fp_comm_ring p)).
                (BK.cong #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                   (poly_mul q1 m) (BK.poly_pow #(fp p) #(fp_field p) w0 (p <: nat)) w0 /\
                 ~(exists (d:fp p).
                     divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                       (poly_mul q1 m)
                       (poly_sub #(fp p) #(SP.fcr (fp_field p)) w0
                          (SU.const0 #(fp p) #(SP.fcr (fp_field p)) d))))
    with w and ()
#pop-options

(* The complementary direction: if f is IRREDUCIBLE, every Berlekamp kernel
   element is congruent to a (global) constant — so there is no nontrivial
   splitter.  (Directly the forward half of kernel_factor_iff at q = f.)

   L4 + this give the Berlekamp irreducibility criterion:
     f has a non-constant kernel element  <==>  f is reducible
   (a coprime nonunit factorization), which with #28 turns any such element
   into a genuine factorization  f ~ prod_c gcd(f, w - c). *)
let irreducible_kernel_is_constant (p:int{EU.is_prime p}) (f h: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (requires IR.poly_irreducible #(fp p) #(fp_field p) f /\
                    BK.cong #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                            f (BK.poly_pow #(fp p) #(fp_field p) h (p <: nat)) h)
          (ensures  (exists (c:fp p).
                       divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                         f (poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                              (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c))))
  = BKR.kernel_factor_iff p f h
