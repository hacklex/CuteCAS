module Core.Field.BerlekampKernel

(* ================================================================ *)
(*  Toward #29 (Berlekamp kernel dimension = number of factors),     *)
(*  via the CRT / counting route (NOT abstract vector-space theory). *)
(*                                                                   *)
(*  The Berlekamp kernel condition  cong m (h^p) h   (i.e. m | h^p-h) *)
(*  is MULTIPLICATIVE over coprime moduli:                           *)
(*                                                                   *)
(*     coprime m n  ==>                                              *)
(*       cong (m*n) x y  <==>  cong m x y  /\  cong n x y.           *)
(*                                                                   *)
(*  This is the inductive bridge for                                 *)
(*     kernel mod (prod f_i)  <->  prod_i (kernel mod f_i),          *)
(*  which combined with "kernel mod irreducible = scalars" (Fermat   *)
(*  in the residue field 𝔽_p[X]/(f_i), still to do) yields the       *)
(*  count |kernel| = p^(#factors), i.e. dim = #factors.              *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module BK = Core.Field.Berlekamp
module CR = Core.Polynomial.CRT
module CP = Core.Polynomial.CoprimeProduct
module PR = Core.Polynomial.Product
module IR = Core.Polynomial.Irreducible
module SF = Core.Polynomial.SquareFree
module UN = Core.Polynomial.Unique
module SU = Core.Polynomial.Subst
module SP = Core.Field.SubstProd
module BR = Core.Field.BerlekampReverse
module FE = Core.Field.FpEnum
module BSC = Core.Field.BerlekampSplitCorrect
module FR = Core.Field.Frobenius
module PW = Core.Algebra.Power
module EU = FStar.Math.Euclid

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Tactics.CanonRing
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Field.Fp

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* m divides m*n  and  n divides m*n. *)
let divides_self_mul (#t:Type) {| f: field t |} (m n: polynomial t)
  : Lemma (divides #(polynomial t) #(BK.crp t #f) m (poly_mul m n) /\
           divides #(polynomial t) #(BK.crp t #f) n (poly_mul m n))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    (* m | m*n : witness n *)
    reflexivity #(polynomial t) #(cr_p.cr_r.r_add.acg_eq) (poly_mul m n);
    divides_intro #(polynomial t) #cr_p m (poly_mul m n) n;
    (* n | m*n : m*n ~ n*m, witness m *)
    poly_mul_commutativity m n;
    divides_congruence_right #(polynomial t) #cr_p n (poly_mul n m) (poly_mul m n);
    divides_intro #(polynomial t) #cr_p n (poly_mul n m) m

(* cong respects p-th powers:  cong m a b ==> cong m (a^k) (b^k). *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 1"
let rec cong_pow (#t:Type) {| f: field t |} (m a b: polynomial t) (k:nat)
  : Lemma (requires BK.cong #(polynomial t) #(BK.crp t #f) m a b)
          (ensures  BK.cong #(polynomial t) #(BK.crp t #f) m
                            (BK.poly_pow #t #f a k) (BK.poly_pow #t #f b k))
          (decreases k)
  = if k = 0 then begin
      BK.poly_pow_zero #t #f a;
      BK.poly_pow_zero #t #f b;
      BK.cong_refl #(polynomial t) #(BK.crp t #f) m (poly_one #t)
    end else begin
      BK.poly_pow_succ #t #f a (k - 1);          (* a^k == poly_mul a (a^(k-1)) *)
      BK.poly_pow_succ #t #f b (k - 1);
      cong_pow #t #f m a b (k - 1);              (* IH *)
      (* cong_mul: x1=a,x2=b (cong m a b) ; y1=a^{k-1},y2=b^{k-1} (IH) ;
         ensures cong m (a*a^{k-1}) (b*b^{k-1}). *)
      BK.cong_mul #(polynomial t) #(BK.crp t #f) m
        a b (BK.poly_pow #t #f a (k - 1)) (BK.poly_pow #t #f b (k - 1));
      (* bridge mul #crp == poly_mul == poly_pow _ k *)
      assert (mul #(polynomial t) #((BK.crp t #f).cr_r) a (BK.poly_pow #t #f a (k - 1))
              == BK.poly_pow #t #f a k);
      assert (mul #(polynomial t) #((BK.crp t #f).cr_r) b (BK.poly_pow #t #f b (k - 1))
              == BK.poly_pow #t #f b k)
    end
#pop-options

(* The Berlekamp kernel condition splits over coprime moduli. *)
let cong_mul_iff (#t:Type) {| f: field t |} (m n x y: polynomial t)
  : Lemma (requires coprime #t #f m n /\ Some? (poly_deg m))
          (ensures (BK.cong #(polynomial t) #(BK.crp t #f) (poly_mul m n) x y
                    <==> (BK.cong #(polynomial t) #(BK.crp t #f) m x y /\
                          BK.cong #(polynomial t) #(BK.crp t #f) n x y)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    let d = add #(polynomial t) #(cr_p.cr_r.r_add) x (neg #(polynomial t) #(cr_p.cr_r.r_add) y) in
    (* cong _ x y  ==  divides _ d  (by definition of BK.cong) *)
    divides_self_mul #t #f m n;                       (* m | m*n  and  n | m*n *)
    (* forward: divides (m*n) d  ==>  divides m d /\ divides n d *)
    let fwd () : Lemma (requires divides #(polynomial t) #cr_p (poly_mul m n) d)
                       (ensures  divides #(polynomial t) #cr_p m d /\
                                 divides #(polynomial t) #cr_p n d)
      = divides_trans #(polynomial t) #cr_p m (poly_mul m n) d;
        divides_trans #(polynomial t) #cr_p n (poly_mul m n) d
    in
    Classical.move_requires fwd ();
    (* backward: divides m d /\ divides n d ==> divides (m*n) d  (crt_inj) *)
    let bwd () : Lemma (requires divides #(polynomial t) #cr_p m d /\
                                 divides #(polynomial t) #cr_p n d)
                       (ensures  divides #(polynomial t) #cr_p (poly_mul m n) d)
      = CR.crt_inj #t #f m n d
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
#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let rec cong_prod_iff (#t:Type) {| f: field t |} (ms: list (polynomial t)) (x y: polynomial t)
  : Lemma (requires (forall (k:nat). k < L.length ms ==> Some? (poly_deg (L.index ms k))) /\
                    (forall (i j:nat). i < L.length ms /\ j < L.length ms /\ i <> j ==>
                       coprime #t #f (L.index ms i) (L.index ms j)))
          (ensures (BK.cong #(polynomial t) #(BK.crp t #f) (PR.poly_prod ms) x y
                    <==> (forall (k:nat). k < L.length ms ==>
                            BK.cong #(polynomial t) #(BK.crp t #f) (L.index ms k) x y)))
          (decreases ms)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    match ms with
    | [] ->
        (* poly_prod [] = poly_one ; one | (x - y) ; RHS vacuously true *)
        IR.one_divides_all #t #f (add #(polynomial t) #(cr_p.cr_r.r_add) x
                                      (neg #(polynomial t) #(cr_p.cr_r.r_add) y))
    | d :: rest ->
        let prest = PR.poly_prod rest in
        (* index of (d::rest): position 0 is d, position k+1 is rest_k. *)
        assert (L.index (d :: rest) 0 == d);
        assert (forall (k:nat). k < L.length rest ==>
                  L.index (d :: rest) (Prims.op_Addition k 1) == L.index rest k);
        (* coprime d (rest_k) for each k, from outer pairwise at (0, k+1). *)
        assert (forall (k:nat). k < L.length rest ==> coprime #t #f d (L.index rest k));
        CP.coprime_to_prod #t #f d rest;            (* coprime d prest (Some? deg d from hyp at 0) *)
        cong_mul_iff #t #f d prest x y;             (* cong (d*prest) <==> cong d /\ cong prest *)
        (* IH: rest deg/pairwise hyps follow from the outer ones + the index shift. *)
        cong_prod_iff #t #f rest x y                (* cong prest <==> forall rest *)
#pop-options

(* ================================================================ *)
(*  Irreducible ==> prime, and its list form.                        *)
(*  (General polynomial facts; placed here for the per-factor kernel  *)
(*   argument below.)                                                *)
(* ================================================================ *)

let abs_assoc (#u:Type) {| cr: commutative_ring u |} (x y z: u)
  : Lemma (eq (mul (mul x y) z) (mul x (mul y z)))
  = assert (eq (mul (mul x y) z) (mul x (mul y z))) by canon_ring ()

let abs_comm (#u:Type) {| cr: commutative_ring u |} (x y: u)
  : Lemma (eq (mul x y) (mul y x))
  = assert (eq (mul x y) (mul y x)) by canon_ring ()

(* k a nonzero-constant unit, q ~ g*k  ==>  q | g. *)
let unit_cofactor_divides (#t:Type) {| f: field t |} (q g k: polynomial t)
  : Lemma (requires poly_deg k == Some 0 /\ poly_eq q (poly_mul g k))
          (ensures  divides #(polynomial t) #(BK.crp t #f) q g)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    degree_zero_is_singleton k;
    let c : t = poly_lc k in
    let cinv : t = f.f_sf.sf_mig.inv c in
    let ci : polynomial t = [cinv] in
    singleton_inv_mul_singleton #t #f c;
    assert (poly_eq (poly_mul ci k) (poly_one #t));
    reflexivity ci;
    poly_mul_congruence q ci (poly_mul g k) ci;
    abs_assoc #(polynomial t) #cr_p g k ci;
    transitivity (poly_mul q ci) (poly_mul (poly_mul g k) ci) (poly_mul g (poly_mul k ci));
    abs_comm #(polynomial t) #cr_p k ci;
    reflexivity g;
    poly_mul_congruence g (poly_mul k ci) g (poly_mul ci k);
    transitivity (poly_mul q ci) (poly_mul g (poly_mul k ci)) (poly_mul g (poly_mul ci k));
    poly_mul_congruence g (poly_mul ci k) g (poly_one #t);
    transitivity (poly_mul q ci) (poly_mul g (poly_mul ci k)) (poly_mul g (poly_one #t));
    poly_mul_one g;
    transitivity (poly_mul q ci) (poly_mul g (poly_one #t)) g;
    symmetry (poly_mul q ci) g;
    divides_intro #(polynomial t) #cr_p q g ci

(* irreducible q dividing a product divides one of the factors. *)
let irreducible_prime (#t:Type) {| f: field t |} (q a b: polynomial t)
  : Lemma (requires IR.poly_irreducible #t #f q /\
                    divides #(polynomial t) #(BK.crp t #f) q (poly_mul a b))
          (ensures  divides #(polynomial t) #(BK.crp t #f) q a \/
                    divides #(polynomial t) #(BK.crp t #f) q b)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    let crc : commutative_ring t = cr_of_id t #(id_of_f t #f) in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    let notb () : Lemma (requires ~(divides #(polynomial t) #cr_p q a))
                        (ensures  divides #(polynomial t) #cr_p q b)
      = let g = poly_gcd #t #f q a in
        SF.gcd_has_degree #t #f q a;
        gcd_divides_left  #t #f q a;
        gcd_divides_right #t #f q a;
        let show_coprime () : Lemma (poly_deg g == Some 0)
          = eliminate exists (k: polynomial t). poly_eq q (poly_mul g k)
            returns poly_deg g == Some 0
            with _hk.
            begin
              assert (poly_eq q (poly_mul g k) == true);
              if poly_deg g = Some 0 then ()
              else if None? (poly_deg k) then begin
                UN.degree_none_poly_eq_zero #t #crc k;
                reflexivity g;
                poly_mul_congruence g k g (poly_zero #t);
                H.x_mul_zero #(polynomial t) #(cr_p.cr_r) g;
                transitivity (poly_mul g k) (poly_mul g (poly_zero #t)) (poly_zero #t);
                transitivity q (poly_mul g k) (poly_zero #t);
                UN.degree_well_defined #t #crc q (poly_zero #t)
              end else begin
                unit_cofactor_divides #t #f q g k;
                divides_trans #(polynomial t) #cr_p q g a
              end
            end
        in
        show_coprime ();
        coprime_reveal #t #f q a;
        poly_mul_commutativity a b;
        divides_congruence_right #(polynomial t) #cr_p q (poly_mul a b) (poly_mul b a);
        euclid_lemma #t #f q a b
    in
    Classical.move_requires notb ()

(* irreducible q dividing a product of a LIST divides some element. *)
let rec irreducible_divides_prod (#t:Type) {| f: field t |}
  (q: polynomial t) (ms: list (polynomial t))
  : Lemma (requires IR.poly_irreducible #t #f q /\
                    divides #(polynomial t) #(BK.crp t #f) q (PR.poly_prod ms))
          (ensures  (exists (k:nat). k < L.length ms /\
                       divides #(polynomial t) #(BK.crp t #f) q (L.index ms k)))
          (decreases ms)
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    match ms with
    | [] ->
        (* poly_prod [] = poly_one ; q | one with deg q >= 1 is impossible. *)
        IR.divides_degree_le #t #f q (poly_one #t)
    | x :: rest ->
        irreducible_prime #t #f q x (PR.poly_prod rest);
        assert (L.index (x :: rest) 0 == x);
        eliminate (divides #(polynomial t) #cr_p q x) \/
                  (divides #(polynomial t) #cr_p q (PR.poly_prod rest))
        returns (exists (k:nat). k < L.length ms /\
                   divides #(polynomial t) #cr_p q (L.index ms k))
        with _hx. ()
        and _hr.
          begin
            irreducible_divides_prod #t #f q rest;
            eliminate exists (j:nat). j < L.length rest /\
                        divides #(polynomial t) #cr_p q (L.index rest j)
            returns (exists (k:nat). k < L.length ms /\
                       divides #(polynomial t) #cr_p q (L.index ms k))
            with _hj.
              assert (L.index (x :: rest) (Prims.op_Addition j 1) == L.index rest j)
          end

(* ================================================================ *)
(*  PER-FACTOR KERNEL STRUCTURE (toward dim = #factors):             *)
(*    if q is an irreducible factor of f and h is a Berlekamp kernel  *)
(*    element (cong q (h^p) h), then h is congruent to a CONSTANT     *)
(*    modulo q:  q | (h - [c]) for some c in 𝔽_p.                     *)
(*                                                                   *)
(*  Proof: cong q (h^p) h  =>  q | (h^p - h) ~ prod_c (h - [c])       *)
(*  (BR.reverse_divides), and an irreducible dividing a product       *)
(*  divides one of the factors (irreducible_divides_prod).           *)
(*                                                                   *)
(*  Combined with cong_prod_iff this gives, for squarefree            *)
(*  f = prod (distinct irreducibles), that every kernel element is    *)
(*  constant on each factor.  The CONVERSE is kernel_const_is_kernel   *)
(*  below, and the two are packaged as kernel_factor_iff.  Remaining   *)
(*  for "dim = #factors": a cardinality/dimension framework (count the *)
(*  p distinct constants per factor ⇒ |kernel| = p^r) — future work.   *)
(* ================================================================ *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let kernel_factor_constant (p:int{EU.is_prime p}) (q h: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (requires IR.poly_irreducible #(fp p) #(fp_field p) q /\
                    BK.cong #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                            q (BK.poly_pow #(fp p) #(fp_field p) h (p <: nat)) h)
          (ensures (exists (k:nat). k < L.length (FE.fp_enum p) /\
                      divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                        q (poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                             (SU.const0 #(fp p) #(SP.fcr (fp_field p)) (L.index (FE.fp_enum p) k)))))
  = let shiftlist = L.map (fun (c:fp p) -> poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                              (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c)) (FE.fp_enum p) in
    FE.fp_enum_length p;
    BR.reverse_divides p q h;                                      (* q | shift_product p h *)
    irreducible_divides_prod #(fp p) #(fp_field p) q shiftlist;    (* exists k. q | shiftlist_k *)
    let bridge (k:nat{k < L.length shiftlist})
      : Lemma (L.index shiftlist k ==
               poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                 (SU.const0 #(fp p) #(SP.fcr (fp_field p)) (L.index (FE.fp_enum p) k)))
      = BSC.index_map (fun (c:fp p) -> poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                          (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c)) (FE.fp_enum p) k
    in
    Classical.forall_intro bridge
#pop-options

(* const0 of a power = power of const0:  (const0 c)^k ~ const0 (rpow c k). *)
let rec const0_pow (p:int{EU.is_prime p}) (c: fp p) (k:nat)
  : Lemma (ensures poly_eq #(fp p) #(SP.fcr (fp_field p))
             (BK.poly_pow #(fp p) #(fp_field p) (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c) k)
             (SU.const0 #(fp p) #(SP.fcr (fp_field p))
               (PW.rpow #(fp p) #((SP.fcr (fp_field p)).cr_r) c k)))
          (decreases k)
  = let cr = SP.fcr (fp_field p) in
    H.elim_equatable_laws (polynomial (fp p)) #((SU.pacg cr).acg_eq) ();
    let c0 = SU.const0 #(fp p) #cr c in
    if k = 0 then begin
      BK.poly_pow_zero #(fp p) #(fp_field p) c0;
      PW.rpow_zero #(fp p) #(cr.cr_r) c;
      SU.const0_one #(fp p) #cr ();
      symmetry (SU.const0 #(fp p) #cr (one <: fp p)) (poly_one #(fp p) #cr)
    end else begin
      let pk1 = BK.poly_pow #(fp p) #(fp_field p) c0 (k - 1) in
      let rk1 = PW.rpow #(fp p) #(cr.cr_r) c (k - 1) in
      BK.poly_pow_succ #(fp p) #(fp_field p) c0 (k - 1);
      PW.rpow_succ #(fp p) #(cr.cr_r) c (k - 1);
      const0_pow p c (k - 1);
      reflexivity c0;
      poly_mul_congruence c0 pk1 c0 (SU.const0 #(fp p) #cr rk1);
      SU.const0_mul #(fp p) #cr c rk1;
      symmetry (SU.const0 #(fp p) #cr (mul #(fp p) #(cr.cr_r) c rk1))
               (poly_mul c0 (SU.const0 #(fp p) #cr rk1));
      transitivity (poly_mul c0 pk1)
                   (poly_mul c0 (SU.const0 #(fp p) #cr rk1))
                   (SU.const0 #(fp p) #cr (mul #(fp p) #(cr.cr_r) c rk1))
    end

(* CONVERSE of kernel_factor_constant:                               *)
(*   q | (h - const0 c)  ==>  cong q (h^p) h.                         *)
(* (h ≡ c (mod q) ==> h^p ≡ c^p = c ≡ h, using Fermat c^p=c in 𝔽_p.)  *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let kernel_const_is_kernel (p:int{EU.is_prime p})
  (q h: polynomial (fp p) #(fp_comm_ring p)) (c: fp p)
  : Lemma (requires divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                            q (poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                                 (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c)))
          (ensures  BK.cong #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                            q (BK.poly_pow #(fp p) #(fp_field p) h (p <: nat)) h)
  = let cr = SP.fcr (fp_field p) in
    assert (cr == fp_comm_ring p);
    H.elim_equatable_laws (polynomial (fp p)) #((SU.pacg cr).acg_eq) ();
    let c0 = SU.const0 #(fp p) #cr c in
    let hp = BK.poly_pow #(fp p) #(fp_field p) h (p <: nat) in
    let c0p = BK.poly_pow #(fp p) #(fp_field p) c0 (p <: nat) in
    poly_sub_reveal #(fp p) #cr h c0;                  (* q | (h - c0) = cong q h c0 *)
    cong_pow #(fp p) #(fp_field p) q h c0 (p <: nat);  (* cong q (h^p) (c0^p) *)
    const0_pow p c (p <: nat);                         (* c0^p ~ const0 (rpow c p) *)
    FR.fermat_fp p c;                                  (* rpow c p == c *)
    assert (PW.rpow #(fp p) #(cr.cr_r) c (p <: nat) == c);
    assert (SU.const0 #(fp p) #cr (PW.rpow #(fp p) #(cr.cr_r) c (p <: nat)) == c0);
    BK.cong_eq_right #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p)) q hp c0p c0;
    BK.cong_sym #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p)) q h c0;
    BK.cong_trans #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p)) q hp c0 h
#pop-options

(* ================================================================ *)
(*  PER-FACTOR KERNEL CHARACTERIZATION (the clean #29 milestone):    *)
(*    for an irreducible factor q,                                   *)
(*       cong q (h^p) h   <==>   h ≡ a constant (mod q).             *)
(* ================================================================ *)
#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let kernel_factor_iff (p:int{EU.is_prime p}) (q h: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (requires IR.poly_irreducible #(fp p) #(fp_field p) q)
          (ensures  (BK.cong #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                             q (BK.poly_pow #(fp p) #(fp_field p) h (p <: nat)) h
                     <==> (exists (c:fp p).
                             divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                               q (poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                                    (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c)))))
  = let fwd () : Lemma
        (requires BK.cong #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                          q (BK.poly_pow #(fp p) #(fp_field p) h (p <: nat)) h)
        (ensures  (exists (c:fp p).
                     divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                       q (poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                            (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c))))
      = kernel_factor_constant p q h    (* exists k. q | (h - const0 (enum_k)) ; witness c = enum_k *)
    in
    let bwd () : Lemma
        (requires (exists (c:fp p).
                     divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                       q (poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                            (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c))))
        (ensures  BK.cong #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                          q (BK.poly_pow #(fp p) #(fp_field p) h (p <: nat)) h)
      = eliminate exists (c:fp p).
          divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
            q (poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                 (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c))
        returns BK.cong #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p))
                        q (BK.poly_pow #(fp p) #(fp_field p) h (p <: nat)) h
        with _hc. kernel_const_is_kernel p q h c
    in
    Classical.move_requires fwd ();
    Classical.move_requires bwd ()
#pop-options

(* The p constant residues are pairwise DISTINCT mod an irreducible q:    *)
(*   c <> c'  ==>  q does not divide  const0 c - const0 c'.                *)
(* (Their difference is a nonzero constant unit, which an irreducible of   *)
(*  degree >= 1 cannot divide.)  With kernel_factor_iff this pins the      *)
(*  per-factor kernel residues to EXACTLY the p distinct constants — the   *)
(*  "= p" count, modulo a cardinality framework still to be built.         *)
#push-options "--z3rlimit 100"
let const0_distinct_mod_irred (p:int{EU.is_prime p})
  (q: polynomial (fp p) #(fp_comm_ring p)) (c c': fp p)
  : Lemma (requires IR.poly_irreducible #(fp p) #(fp_field p) q /\ not (c = c'))
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
      = IR.divides_degree_le #(fp p) #(fp_field p) q s0
    in
    Classical.move_requires contra ()
#pop-options
