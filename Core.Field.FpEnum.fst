module Core.Field.FpEnum

(* ================================================================ *)
(*  Enumeration of the finite prime field  fp p = {0,1,…,p-1}  and  *)
(*  the fact that every field element is a ROOT of  X^p − X.        *)
(*                                                                   *)
(*  This is the reachable part of the Berlekamp splitting identity   *)
(*  (W2):  it provides the list of all p field elements and shows    *)
(*  each is a root of  X^p − X  (via Fermat  c^p = c).              *)
(*                                                                   *)
(*  The remaining step  X^p − X = ∏_{c∈fp p}(X − c)  needs the      *)
(*  "monic degree-p polynomial with p distinct roots equals the      *)
(*  product of its linear factors" theorem, which is NOT in the      *)
(*  codebase — see the wall note at the end.                         *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module PW = Core.Algebra.Power
module CF = Core.Field.Frobenius
module BK = Core.Field.Berlekamp
module EV = Core.Polynomial.Eval
module RT = Core.Polynomial.Root

open Core.Algebra
open Core.Algebra.Notation
open Core.Field.Fp
open Core.Polynomial
open FStar.Math.Euclid

#set-options "--fuel 1 --ifuel 1 --z3rlimit 30"

(* ---------------------------------------------------------------- *)
(*  Enumeration  [0; 1; …; p-1]  of fp p.                           *)
(* ---------------------------------------------------------------- *)

(* the list [lo; lo+1; …; p-1]  of fp p elements (all i with lo <= i < p). *)
let rec fp_enum_from (p:int{p > 1}) (lo:nat{lo <= p}) : Tot (list (fp p)) (decreases (p - lo)) =
  if lo = p then []
  else (lo <: fp p) :: fp_enum_from p (Prims.op_Addition lo 1)

let fp_enum (p:int{p > 1}) : list (fp p) = fp_enum_from p 0

(* the enumeration has exactly p elements. *)
let rec fp_enum_from_length (p:int{p > 1}) (lo:nat{lo <= p})
  : Lemma (ensures L.length (fp_enum_from p lo) == p - lo) (decreases (p - lo))
  = if lo = p then () else fp_enum_from_length p (Prims.op_Addition lo 1)

let fp_enum_length (p:int{p > 1}) : Lemma (L.length (fp_enum p) == p)
  = fp_enum_from_length p 0

(* every element of fp p occurs in the enumeration. *)
let rec fp_enum_from_mem (p:int{p > 1}) (lo:nat{lo <= p}) (c: fp p)
  : Lemma (ensures (c >= lo) == L.mem c (fp_enum_from p lo)) (decreases (p - lo))
  = if lo = p then ()
    else fp_enum_from_mem p (Prims.op_Addition lo 1) c

let fp_enum_complete (p:int{p > 1}) (c: fp p)
  : Lemma (L.mem c (fp_enum p))
  = fp_enum_from_mem p 0 c

(* ---------------------------------------------------------------- *)
(*  Each field element is a root of  X^p − X.                       *)
(* ---------------------------------------------------------------- *)

(* X := poly_linear 0  (= [neg 0; one] = the monomial x). *)
let polyX (p:int{is_prime p}) : polynomial (fp p) #(fp_comm_ring p)
  = RT.poly_linear #(fp p) #(fp_field p) (fp_zero p)

(* poly_eval X c = c  (since X = x − 0). *)
let eval_polyX (p:int{is_prime p}) (c: fp p)
  : Lemma (EV.poly_eval #(fp p) #(fp_comm_ring p) (polyX p) c = c)
  = let acg = (fp_comm_ring p).cr_r.r_add in
    H.elim_equatable_laws (fp p) (); H.trans_for_calc (fp p) ();
    RT.eval_linear #(fp p) #(fp_field p) (fp_zero p) c;   (* eval (x-0) c = neg 0 + c *)
    (* neg 0 + c = 0 + c = c *)
    H.neg_zero #(fp p) #acg ();                            (* neg 0 = 0 *)
    reflexivity c;
    add_congruence #(fp p) #acg (acg.neg (fp_zero p)) c (fp_zero p) c;
    H.zero_plus_x #(fp p) #acg c;
    H.trans3 (EV.poly_eval (polyX p) c)
             (acg.add (acg.neg (fp_zero p)) c)
             (acg.add (fp_zero p) c) c

(* poly_eval (g^k) c = (poly_eval g c)^k  (eval is a ring hom over poly_pow). *)
let rec eval_poly_pow (p:int{is_prime p}) (g: polynomial (fp p) #(fp_comm_ring p)) (c: fp p) (k:nat)
  : Lemma (ensures EV.poly_eval #(fp p) #(fp_comm_ring p) (BK.poly_pow #(fp p) #(fp_field p) g k) c
                   = PW.rpow #(fp p) #((fp_comm_ring p).cr_r) (EV.poly_eval g c) k)
          (decreases k)
  = H.elim_equatable_laws (fp p) (); H.trans_for_calc (fp p) ();
    if k = 0 then begin
      (* poly_pow g 0 = poly_one ; eval poly_one c = one ; rpow _ 0 = one *)
      EV.eval_one #(fp p) #(fp_comm_ring p) c
    end
    else begin
      (* poly_pow g k = poly_mul g (poly_pow g (k-1)) *)
      let r = (fp_comm_ring p).cr_r in
      EV.eval_mul #(fp p) #(fp_comm_ring p) g (BK.poly_pow #(fp p) #(fp_field p) g (k-1)) c;
      eval_poly_pow p g c (k-1);                            (* IH *)
      reflexivity (EV.poly_eval g c);
      mul_congruence #(fp p) #r
                     (EV.poly_eval g c)
                     (EV.poly_eval (BK.poly_pow #(fp p) #(fp_field p) g (k-1)) c)
                     (EV.poly_eval g c)
                     (PW.rpow #(fp p) #r (EV.poly_eval g c) (k-1))
    end

(* the polynomial  X^p − X. *)
let xpx (p:int{is_prime p}) : polynomial (fp p) #(fp_comm_ring p)
  = Core.Polynomial.Div.poly_sub #(fp p) #(fp_comm_ring p)
        (BK.poly_pow #(fp p) #(fp_field p) (polyX p) (p <: nat))
        (polyX p)

(* every field element is a root of  X^p − X  (via Fermat). *)
let fp_elt_is_root_of_xpx (p:int{is_prime p}) (c: fp p)
  : Lemma (EV.poly_eval #(fp p) #(fp_comm_ring p) (xpx p) c = fp_zero p)
  = let acg = (fp_comm_ring p).cr_r.r_add in
    H.elim_equatable_laws (fp p) (); H.trans_for_calc (fp p) ();
    let xp = BK.poly_pow #(fp p) #(fp_field p) (polyX p) (p <: nat) in
    (* eval (xp - X) c = eval xp c + neg (eval X c) *)
    Core.Polynomial.Div.poly_sub_reveal #(fp p) #(fp_comm_ring p) xp (polyX p);
    assert (xpx p == poly_add xp (poly_neg (polyX p)));
    EV.eval_add #(fp p) #(fp_comm_ring p) xp (poly_neg (polyX p)) c;
    EV.eval_neg #(fp p) #(fp_comm_ring p) (polyX p) c;
    (* eval xp c = c^p = c  (eval_poly_pow + eval_polyX + Fermat) *)
    eval_poly_pow p (polyX p) c (p <: nat);     (* eval xp c = rpow (eval X c) p *)
    eval_polyX p c;                              (* eval X c = c *)
    CF.fermat_fp p c;                            (* rpow c p = c *)
    (* assemble:  eval (xpx) c = (eval xp c) + neg (eval X c) = c + neg c = 0 *)
    reflexivity (EV.poly_eval xp c);
    add_congruence #(fp p) #acg (EV.poly_eval xp c) (acg.neg (EV.poly_eval (polyX p) c))
                                c (acg.neg c);
    H.x_plus_neg_x #(fp p) #acg c
