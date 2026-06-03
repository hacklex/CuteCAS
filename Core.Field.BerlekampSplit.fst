module Core.Field.BerlekampSplit

(* ================================================================ *)
(*  W2:  X^p - X  =  prod_{c in fp p} (X - c)   over  fp p.          *)
(*                                                                   *)
(*  Both sides are monic of degree p and agree (value 0) on all p    *)
(*  distinct elements of fp p (Fermat); the distinct-roots           *)
(*  factorization `poly_split_distinct_roots` then forces equality.  *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module TC = FStar.Tactics.Typeclasses
module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module BK = Core.Field.Berlekamp
module FE = Core.Field.FpEnum
module SP = Core.Polynomial.Split
module RT = Core.Polynomial.Root
module PR = Core.Polynomial.Product
module DV = Core.Polynomial.Div

open Core.Algebra
open Core.Algebra.Notation
open Core.Field.Fp
open Core.Polynomial
open Core.Polynomial.Eval
open FStar.Math.Euclid

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ================================================================ *)
(*  Monic powers:  if lc g = one and deg g = Some d (d >= 1), then   *)
(*  deg (g^k) = Some (k*d)  and  lc (g^k) = one.                     *)
(* ================================================================ *)

(* poly_one over a field is [one]: degree 0, leading coeff one. *)
#push-options "--fuel 4 --ifuel 2 --z3rlimit 40"
let poly_one_deg_lc (#t:Type) {| f: field t |} ()
  : Lemma (poly_deg (poly_one #t) == (Some 0 <: option nat) /\
           poly_lc (poly_one #t) = (one <: t))
  = H.elim_equatable_laws t ();
    let _ : squash (not (one #t = (zero <: t))) = f.f_one_ne_zero in
    poly_lc_reveal (poly_one #t);
    reflexivity (one <: t)
#pop-options

let rec poly_pow_monic (#t:Type) {| f: field t |} (g: polynomial t) (d:pos) (k:nat)
  : Lemma (requires Some? (poly_deg g) /\ Some?.v (poly_deg g) == d /\
                    poly_lc g = (one <: t))
          (ensures  Some? (poly_deg (BK.poly_pow #t #f g k)) /\
                    Some?.v (poly_deg (BK.poly_pow #t #f g k)) == Prims.op_Star k d /\
                    poly_lc (BK.poly_pow #t #f g k) = (one <: t))
          (decreases k)
  = H.elim_equatable_laws t ();
    let id_t : integral_domain t = id_of_f t in
    let cr : commutative_ring t = cr_of_id t #id_t in
    if k = 0 then begin
      (* poly_pow g 0 = poly_one : deg Some 0 = 0*d, lc one. *)
      BK.poly_pow_zero #t #f g;                           (* poly_pow g 0 == poly_one *)
      poly_one_deg_lc #t #f ();                           (* deg poly_one = Some 0, lc = one *)
      assert (Prims.op_Star 0 d == 0)
    end
    else begin
      BK.poly_pow_succ #t #f g (k-1);                    (* g^k = g * g^(k-1) *)
      poly_pow_monic #t #f g d (k-1);                    (* IH: deg g^(k-1) = (k-1)*d, lc = one *)
      let gk1 = BK.poly_pow #t #f g (k-1) in
      (* deg (g * g^(k-1)) = d + (k-1)*d = k*d *)
      poly_deg_mul #t #id_t g gk1;
      FStar.Math.Lemmas.distributivity_sub_left k 1 d;   (* (k-1)*d = k*d - 1*d *)
      assert (Prims.op_Addition d (Prims.op_Star (k-1) d) == Prims.op_Star k d);
      (* lc (g * g^(k-1)) = lc g * lc g^(k-1) = one * one = one *)
      SP.poly_lc_mul #t #id_t g gk1;
      reflexivity (one <: t);
      mul_congruence (poly_lc g) (poly_lc gk1) (one <: t) (one <: t);
      H.one_mul_x (one <: t);                            (* one * one = one *)
      transitivity (poly_lc (BK.poly_pow #t #f g k))
                   (poly_lc g * poly_lc gk1) ((one <: t) * (one <: t));
      transitivity (poly_lc (BK.poly_pow #t #f g k))
                   ((one <: t) * (one <: t)) (one <: t)
    end

(* ================================================================ *)
(*  X = polyX p  is monic of degree 1.                              *)
(* ================================================================ *)

let polyX_deg (p:int{is_prime p})
  : Lemma (poly_deg #(fp p) #(fp_comm_ring p) (FE.polyX p) == Some 1 /\
           poly_lc  #(fp p) #(fp_comm_ring p) (FE.polyX p) = (one #(fp p) #((fp_comm_ring p).cr_r)))
  = H.elim_equatable_laws (fp p) ();
    RT.poly_linear_deg #(fp p) #(fp_field p) (fp_zero p);   (* deg (x-0) = Some 1 *)
    (* polyX = poly_linear 0 = [neg 0; one]; lc = one (monic). *)
    assert (FE.polyX p == RT.poly_linear #(fp p) #(fp_field p) (fp_zero p));
    RT.poly_linear_lc #(fp p) #(fp_field p) (fp_zero p)     (* lc (x-0) = one *)

(* ================================================================ *)
(*  X^p  is monic of degree p.                                       *)
(* ================================================================ *)

let xp_monic (p:int{is_prime p})
  : Lemma (Some? (poly_deg #(fp p) #(fp_comm_ring p)
                    (BK.poly_pow #(fp p) #(fp_field p) (FE.polyX p) (p <: nat))) /\
           Some?.v (poly_deg #(fp p) #(fp_comm_ring p)
                    (BK.poly_pow #(fp p) #(fp_field p) (FE.polyX p) (p <: nat))) == p /\
           poly_lc #(fp p) #(fp_comm_ring p)
                    (BK.poly_pow #(fp p) #(fp_field p) (FE.polyX p) (p <: nat)) = (one #(fp p) #((fp_comm_ring p).cr_r)))
  = polyX_deg p;
    poly_pow_monic #(fp p) #(fp_field p) (FE.polyX p) 1 (p <: nat);
    assert (Prims.op_Star (p <: nat) 1 == p)

(* ================================================================ *)
(*  xpx = X^p - X  is monic of degree p.                            *)
(* ================================================================ *)

let xpx_monic (p:int{is_prime p})
  : Lemma (poly_deg #(fp p) #(fp_comm_ring p) (FE.xpx p) == Some p /\
           poly_lc  #(fp p) #(fp_comm_ring p) (FE.xpx p) = (one #(fp p) #((fp_comm_ring p).cr_r)))
  = H.elim_equatable_laws (fp p) ();
    let xp = BK.poly_pow #(fp p) #(fp_field p) (FE.polyX p) (p <: nat) in
    xp_monic p;                                          (* deg xp = Some p, lc = one *)
    polyX_deg p;                                         (* deg X = Some 1 *)
    (* xpx = X^p - X = X^p + neg X ; deg (neg X) = deg X = 1 < p *)
    DV.poly_sub_reveal #(fp p) #(fp_comm_ring p) xp (FE.polyX p);
    assert (FE.xpx p == poly_add xp (poly_neg (FE.polyX p)));
    DV.poly_neg_degree #(fp p) #(fp_comm_ring p) (FE.polyX p);   (* deg (neg X) = deg X = Some 1 *)
    SP.poly_add_deg_dominant #(fp p) #(fp_comm_ring p) xp (poly_neg (FE.polyX p)) p

(* ================================================================ *)
(*  fp_enum p = [0; 1; ...; p-1] is pairwise distinct (field-eq).    *)
(* ================================================================ *)

let rec fp_enum_from_distinct (p:int{p > 1}) (lo:nat{lo <= p})
  : Lemma (ensures SP.all_distinct #(fp p) #(fp_comm_ring p) (FE.fp_enum_from p lo))
          (decreases (p - lo))
  = if lo = p then ()
    else begin
      fp_enum_from_distinct p (Prims.op_Addition lo 1);   (* tail distinct *)
      (* head (lo) differs from every d in the tail (d >= lo+1 > lo) *)
      let tail = FE.fp_enum_from p (Prims.op_Addition lo 1) in
      let aux (d: fp p) : Lemma (L.memP d tail ==> not ((lo <: fp p) = d)) =
        let h () : Lemma (requires L.memP d tail) (ensures not ((lo <: fp p) = d)) =
          L.mem_memP d tail;                              (* memP <==> mem (eqtype) *)
          FE.fp_enum_from_mem p (Prims.op_Addition lo 1) d;  (* mem d tail == (d >= lo+1) *)
          assert (d >= Prims.op_Addition lo 1)
        in Classical.move_requires h ()
      in
      Classical.forall_intro aux
    end

let fp_enum_distinct (p:int{p > 1})
  : Lemma (SP.all_distinct #(fp p) #(fp_comm_ring p) (FE.fp_enum p))
  = fp_enum_from_distinct p 0

(* ================================================================ *)
(*  THE W2 SPLITTING IDENTITY:                                       *)
(*     X^p - X  ~  prod_{c in fp p} (X - c).                         *)
(* ================================================================ *)

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let xpx_splits (p:int{is_prime p})
  : Lemma (poly_eq #(fp p) #(fp_comm_ring p)
             (FE.xpx p)
             (PR.poly_prod_linears #(fp p) #(fp_field p) (FE.fp_enum p)))
  = H.elim_equatable_laws (fp p) ();
    H.trans_for_calc (fp p) ();
    let cr = fp_comm_ring p in
    let roots = FE.fp_enum p in
    xpx_monic p;                                          (* deg xpx = Some p, lc = one *)
    FE.fp_enum_length p;                                  (* length roots = p *)
    fp_enum_distinct p;                                   (* all_distinct roots *)
    (* every listed root is a root of xpx (all fp p elements are, by Fermat) *)
    let allroot (c: fp p) : Lemma (L.memP c roots ==> poly_eval #(fp p) #cr (FE.xpx p) c = (zero <: fp p)) =
      let h () : Lemma (requires L.memP c roots) (ensures poly_eval #(fp p) #cr (FE.xpx p) c = (zero <: fp p)) =
        FE.fp_elt_is_root_of_xpx p c                      (* eval xpx c = fp_zero = zero *)
      in Classical.move_requires h ()
    in
    Classical.forall_intro allroot;
    (* apply the distinct-roots factorization *)
    SP.poly_split_distinct_roots #(fp p) #(fp_field p) (FE.xpx p) roots;
    (* poly_eq xpx (poly_scale (lc xpx) (prod_linears roots)); lc xpx = one *)
    let prest = PR.poly_prod_linears #(fp p) #(fp_field p) roots in
    let lc = poly_lc #(fp p) #cr (FE.xpx p) in
    assert (poly_eq (FE.xpx p) (SP.poly_scale lc prest));
    (* poly_scale lc prest ~ poly_scale one prest ~ prest *)
    SP.poly_scale_scalar_congr #(fp p) #cr lc (one #(fp p) #(cr.cr_r)) prest;  (* scale lc ~ scale one *)
    (* poly_scale one prest = poly_mul (one @ poly_zero) prest = poly_mul poly_one prest ~ prest *)
    assert (SP.poly_scale (one #(fp p) #(cr.cr_r)) prest
            == poly_mul (poly_one #(fp p) #cr) prest);
    poly_mul_one #(fp p) #cr prest;                       (* poly_mul poly_one prest ~ prest *)
    transitivity (FE.xpx p) (SP.poly_scale lc prest) (SP.poly_scale (one #(fp p) #(cr.cr_r)) prest);
    transitivity (FE.xpx p) (SP.poly_scale (one #(fp p) #(cr.cr_r)) prest) prest
#pop-options
