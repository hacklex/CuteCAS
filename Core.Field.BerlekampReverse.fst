module Core.Field.BerlekampReverse

(* ================================================================ *)
(*  Berlekamp reverse splitting, step 1:                             *)
(*    a kernel element h  (h^p = h mod f)  satisfies                 *)
(*       f | prod_{c in fp p} (h - [c]).                             *)
(*  This is  f | (h^p - h)  (the kernel condition) transported       *)
(*  through  subst_prod  (h^p - h ~ prod_c (h - [c])).               *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module SU = Core.Polynomial.Subst
module SP = Core.Field.SubstProd
module BK = Core.Field.Berlekamp
module FE = Core.Field.FpEnum
module PR = Core.Polynomial.Product
module DV = Core.Polynomial.Div

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Field.Fp
module EU = FStar.Math.Euclid

#set-options "--fuel 1 --ifuel 1 --z3rlimit 80"

(* the product  prod_{c in fp p} (h - [c]). *)
let shift_product (p:int{EU.is_prime p}) (h: polynomial (fp p) #(fp_comm_ring p))
  : polynomial (fp p) #(fp_comm_ring p)
  = PR.poly_prod #(fp p) #(SP.fcr (fp_field p))
      (L.map (fun (c:fp p) -> poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                                 (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c))
             (FE.fp_enum p))

(* a kernel element divides the shift-product. *)
let reverse_divides (p:int{EU.is_prime p}) (fpoly h: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (requires BK.cong #(polynomial (fp p) #(fp_comm_ring p)) #(BK.crp (fp p) #(fp_field p))
                            fpoly (BK.poly_pow #(fp p) #(fp_field p) h (p <: nat)) h)
          (ensures  divides #(polynomial (fp p) #(fp_comm_ring p)) #(BK.crp (fp p) #(fp_field p))
                            fpoly (shift_product p h))
  = let cr = SP.fcr (fp_field p) in
    let pcrp = SU.pcr cr in
    H.elim_equatable_laws (polynomial (fp p)) #((SU.pacg cr).acg_eq) ();
    let xp = BK.poly_pow #(fp p) #(fp_field p) h (p <: nat) in
    (* cong fpoly xp h  =  fpoly | (xp + neg h)  =  fpoly | poly_sub xp h *)
    DV.poly_sub_reveal #(fp p) #cr xp h;                  (* poly_sub xp h == poly_add xp (poly_neg h) == xp + neg h *)
    (* subst_prod:  poly_sub xp h ~ shift_product *)
    SP.subst_prod p h;
    divides_congruence_right #(polynomial (fp p)) #pcrp
      fpoly (poly_sub #(fp p) #cr xp h) (shift_product p h)

module BSC = Core.Field.BerlekampSplitCorrect

(* const0 c ~ const_poly c : both are the constant polynomial [c]. *)
let const0_eq_const_poly (p:int{EU.is_prime p}) (c: fp p)
  : Lemma (poly_eq (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c)
                   (BK.const_poly #(fp p) #(fp_field p) c))
  = H.elim_equatable_laws (fp p) ();
    SU.poly_eq_by_coeff #(fp p) #(SP.fcr (fp_field p))
      (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c) (BK.const_poly #(fp p) #(fp_field p) c)
      (fun (j:nat) ->
        if j = 0 then begin
          SU.const0_coeff0 #(fp p) #(SP.fcr (fp_field p)) c;
          BSC.const_poly_coeff0 #(fp p) #(fp_field p) c
        end else begin
          SU.const0_coeff_high #(fp p) #(SP.fcr (fp_field p)) c j;
          BSC.const_poly_coeff_high #(fp p) #(fp_field p) c j
        end)

module CP = Core.Polynomial.CoprimeProduct
module GC = Core.Polynomial.GCD

(* ================================================================ *)
(*  Per-index bridge between the two shift forms:                    *)
(*    gcd(f, h - const0 c)  ~  gcd(f, h - const_poly c)              *)
(*                          =  berlekamp_split f h c.                *)
(*  (const0 is the Subst-module embedding; const_poly the Berlekamp  *)
(*   one — they are poly_eq by const0_eq_const_poly.)                *)
(* ================================================================ *)
let split_eq_const0 (p:int{EU.is_prime p}) (fpoly h: polynomial (fp p) #(fp_comm_ring p)) (c: fp p)
  : Lemma (poly_eq #(fp p) #(fp_comm_ring p)
             (GC.poly_gcd #(fp p) #(fp_field p) fpoly
                (poly_sub #(fp p) #(SP.fcr (fp_field p)) h (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c)))
             (BK.berlekamp_split #(fp p) #(fp_field p) fpoly h c))
  = let f = fp_field p in
    H.elim_equatable_laws (polynomial (fp p)) ();
    const0_eq_const_poly p c;
    SP.poly_sub_congr #(fp p) #f h (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c)
                                 h (BK.const_poly #(fp p) #f c);
    GC.gcd_congruence #(fp p) #f fpoly fpoly
       (poly_sub #(fp p) #(SP.fcr (fp_field p)) h (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c))
       (poly_sub #(fp p) #(SP.fcr (fp_field p)) h (BK.const_poly #(fp p) #f c))

(* ================================================================ *)
(*  REVERSE SPLIT, direction "f | prod gcd":                         *)
(*    a kernel element h satisfies  f | prod_c gcd(f, h - [c]).       *)
(*                                                                   *)
(*  From reverse_divides (f | prod_c (h-[c])), then                  *)
(*  CP.f_divides_prod_gcd (f | prod ms ==> f | prod gcd(f,ms)),       *)
(*  then bridge the const0-shift product to the berlekamp_factors    *)
(*  (const_poly) product via CP.poly_prod_congr + split_eq_const0.   *)
(* ================================================================ *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 2"
let reverse_split_divides (p:int{EU.is_prime p}) (fpoly h: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (requires BK.cong #(polynomial (fp p) #(fp_comm_ring p)) #(BK.crp (fp p) #(fp_field p))
                            fpoly (BK.poly_pow #(fp p) #(fp_field p) h (p <: nat)) h)
          (ensures  divides #(polynomial (fp p) #(fp_comm_ring p)) #(BK.crp (fp p) #(fp_field p))
                      fpoly
                      (PR.poly_prod #(fp p) #(SP.fcr (fp_field p))
                         (BSC.berlekamp_factors #(fp p) #(fp_field p) fpoly h (FE.fp_enum p))))
  = let cr = SP.fcr (fp_field p) in
    let pcrp = SU.pcr cr in
    H.elim_equatable_laws (polynomial (fp p)) #((SU.pacg cr).acg_eq) ();
    let shfn = (fun (c:fp p) -> poly_sub #(fp p) #(SP.fcr (fp_field p)) h
                                  (SU.const0 #(fp p) #(SP.fcr (fp_field p)) c)) in
    let shifts0 = L.map shfn (FE.fp_enum p) in
    let gcds0 = L.map (fun m -> GC.poly_gcd #(fp p) #(fp_field p) fpoly m) shifts0 in
    let bfactors = BSC.berlekamp_factors #(fp p) #(fp_field p) fpoly h (FE.fp_enum p) in
    reverse_divides p fpoly h;
    CP.f_divides_prod_gcd #(fp p) #(fp_field p) fpoly shifts0;
    FE.fp_enum_length p;
    BSC.berlekamp_factors_length #(fp p) #(fp_field p) fpoly h (FE.fp_enum p);
    BSC.index_map shfn (FE.fp_enum p) 0;
    BSC.index_map (fun m -> GC.poly_gcd #(fp p) #(fp_field p) fpoly m) shifts0 0;
    let pointwise (i:nat{i < L.length gcds0})
      : Lemma (poly_eq (L.index gcds0 i) (L.index bfactors i))
      = BSC.index_map (fun m -> GC.poly_gcd #(fp p) #(fp_field p) fpoly m) shifts0 i;
        BSC.index_map shfn (FE.fp_enum p) i;
        BSC.berlekamp_factors_index #(fp p) #(fp_field p) fpoly h (FE.fp_enum p) i;
        split_eq_const0 p fpoly h (L.index (FE.fp_enum p) i)
    in
    Classical.forall_intro pointwise;
    CP.poly_prod_congr #(fp p) #cr gcds0 bfactors;
    divides_congruence_right #(polynomial (fp p)) #pcrp
      fpoly
      (PR.poly_prod #(fp p) #cr gcds0)
      (PR.poly_prod #(fp p) #cr bfactors)
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
let berlekamp_reverse_associates (p:int{EU.is_prime p}) (fpoly h: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (requires Some? (poly_deg #(fp p) #(fp_comm_ring p) fpoly) /\
                    BK.cong #(polynomial (fp p) #(fp_comm_ring p)) #(BK.crp (fp p) #(fp_field p))
                            fpoly (BK.poly_pow #(fp p) #(fp_field p) h (p <: nat)) h)
          (ensures  (let prod = PR.poly_prod #(fp p) #(SP.fcr (fp_field p))
                                   (BSC.berlekamp_factors #(fp p) #(fp_field p) fpoly h (FE.fp_enum p)) in
                     divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p)) fpoly prod /\
                     divides #(polynomial (fp p)) #(BK.crp (fp p) #(fp_field p)) prod fpoly))
  = reverse_split_divides p fpoly h;
    BSC.berlekamp_factors_product_divides_f p fpoly h
