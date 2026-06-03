module Core.AlgebraicConstant.Field

(* Prereq C: algebraic t r is a FIELD when r is irreducible.
   inverse of [a] (a not div by r) = [snd (normalize_bezout r a)]. *)

module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.PartialFraction
open Core.Polynomial.Irreducible
open Core.Polynomial.Unique
open Core.AlgebraicConstant

(* An irreducible r (deg >= 1) does not divide 1. *)
let r_not_divides_one (#t:Type) {| f: field t |} (r: polynomial t)
  : Lemma (requires poly_irreducible r)
          (ensures  ~(divides r poly_one))
  = let aux () : Lemma (requires divides r poly_one)
                       (ensures False)
      = divides_degree_le r poly_one (* deg r <= deg 1 = 0, but deg r >= 1 *)
    in Classical.move_requires aux ()

(* Not divisible by r  =>  a is a nonzero polynomial (Some degree). *)
let deg_some_of_not_div (#t:Type) {| f: field t |} (r a: polynomial t)
  : Lemma (requires (
                     ~(divides r a)))
          (ensures  Some? (poly_deg a))
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let aux () : Lemma (requires None? (poly_deg a))
                       (ensures divides r a)
      = degree_none_poly_eq_zero a;                  (* a ~ poly_zero *)
        divides_zero r;        (* r | poly_zero *)
        poly_eq_symmetry (poly_zero) a;
        divides_congruence_right r (poly_zero) a
    in
    Classical.move_requires aux ()

(* Bridges between ac_eq-to-zero (= is_nonzero, once the ring is fixed) and
   ~(divides r rep).  Both follow directly from the public characterization
   ac_eq_zero_iff_divides. *)
let not_div_of_nonzero (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  (x: algebraic t r)
  : Lemma (requires not (ac_eq x ac_zero))
          (ensures (~(divides r x.ac_rep)))
  = ac_eq_zero_iff_divides x

let nonzero_of_not_div (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  (a: polynomial t)
  : Lemma (requires (~(divides r a)))
          (ensures  not (ac_eq ({ ac_rep = a }) (ac_zero #t #f #r)))
  = ac_eq_zero_iff_divides ({ ac_rep = a } <: algebraic t r)

(* ================================================================ *)
(*  Inverse in the algebraic field:  inv [a] = [bezout_right r a].  *)
(*  For coprime r a (a not divisible by irreducible r), Bezout gives *)
(*    bezout_left*r + bezout_right*a ~ 1,  so  a*bezout_right ~ 1 (mod r). *)
(* ================================================================ *)

let ac_inv (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  (x: algebraic t r)
  : Pure (algebraic t r)
         (requires poly_irreducible r /\ not (ac_eq x ac_zero))
         (ensures  fun y -> not (ac_eq y ac_zero) /\
                         coprime r x.ac_rep /\
                         y.ac_rep == bezout_right r x.ac_rep)
  = let a = x.ac_rep in
    not_div_of_nonzero x;                     (* ~(divides r a) *)
    deg_some_of_not_div r a;                  (* Some? (poly_deg a) *)
    irreducible_coprime_or_divides r a;       (* coprime r a \/ divides r a => coprime r a *)
    let br = bezout_right r a in
    let bl = bezout_left  r a in
    let y : algebraic t r = { ac_rep = br } in
    (* br is itself not divisible by r: else r | (bl*r + br*a) ~ 1. *)
    let aux () : Lemma (requires divides r br) (ensures False)
      = bezout_identity r a;                  (* bl * r + br * a ~ 1 *)
        divides_refl       r;                 (* r | r *)
        divides_mul_left   r bl r;            (* r | bl * r *)
        divides_mul_right  r br a;            (* r | br * a *)
        divides_add        r (bl * r) (br * a);
        divides_congruence_right r (bl * r + br * a) one;  (* r | 1 *)
        r_not_divides_one  r
    in
    Classical.move_requires aux ();                                 (* ~(divides r br) *)
    nonzero_of_not_div #t #f #r br;                                 (* not (ac_eq y ac_zero) *)
    y

(* ================================================================ *)
(*  Inversion identity:  [a] * [bezout_right r a] = [1]  in the     *)
(*  quotient (and symmetrically), for irreducible r and a not 0.    *)
(* ================================================================ *)

(* z - o  =  (-y) + ((y + z) - o)   *)
let residue_id (#u:Type) {| cr: commutative_ring u |} (y z o: u)
  : Lemma (z + -o = -y + (y + z + -o))
  = assert (z + -o = -y + (y + z + -o)) by Core.Tactics.CanonRing.canon_ring ()

let ac_inv_correct (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  (x: algebraic t r)
  : Lemma (requires poly_irreducible r /\ not (ac_eq x ac_zero))
          (ensures  ac_eq (ac_mul x (ac_inv x)) ac_one /\
                    ac_eq (ac_mul (ac_inv x) x) ac_one)
  = 
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let a    = x.ac_rep in
    let inv  = ac_inv x in
    let br   = inv.ac_rep in                                 (* == bezout_right r a *)
    let bl   = bezout_left r a in
    let yv   = bl * r in
    let zv   = br * a in
    let onep : polynomial t = one in
    (* expose the abstract operation reps *)
    ac_mul_rep x inv;                                        (* (x*inv).rep == a * br *)
    ac_mul_rep inv x;                                        (* (inv*x).rep == br * a = zv *)
    ac_one_rep r;                                            (* one.rep == one *)
    bezout_identity r a;                                     (* yv + zv ~ one *)
    (* r | yv  and  r | -yv *)
    divides_refl     r;
    divides_mul_left r bl r;
    divides_neg      r yv;
    (* (yv + zv) - one ~ zero,  hence r | ((yv + zv) - one) *)
    add_negation onep;                                       (* onep + -onep ~ zero *)
    add_congruence (yv + zv) (- onep) onep (- onep);
    transitivity ((yv + zv) + - onep) (onep + - onep) zero;
    divides_zero r;
    divides_congruence_right r zero ((yv + zv) + - onep);
    (* r | (-yv) + ((yv + zv) - one) *)
    divides_add r (- yv) ((yv + zv) + - onep);
    (* residue identity:  zv - one  ~  (-yv) + ((yv + zv) - one) *)
    residue_id yv zv onep;
    divides_congruence_right r
      ((- yv) + ((yv + zv) + - onep)) (zv + - onep);
    poly_sub_reveal zv onep;                                 (* poly_sub zv one == zv + -one *)
    (* now r | poly_sub zv one;  conclude the two ac_eq via ac_eq_divides *)
    ac_eq_divides (ac_mul (ac_inv x) x) ac_one;              (* zv = br * a *)
    (* first form: a * br ~ zv, transport divisibility *)
    mul_commutativity a br;                             (* a * br ~ br * a = zv *)
    add_congruence (a * br) (- onep) zv (- onep);
    poly_sub_reveal (a * br) onep;
    divides_congruence_right r (zv + - onep) ((a * br) + - onep);
    ac_eq_divides (ac_mul x (ac_inv x)) ac_one

(* ================================================================ *)
(*  Inverse respects the quotient equality (inverse is unique).      *)
(*  Standard argument: ia = ia*1 = ia*(b*ib) = (ia*b)*ib             *)
(*                        = (ia*a)*ib = 1*ib = ib.                    *)
(* ================================================================ *)

let ac_inv_congr (#t:Type) {| f: field t |} (#r: polynomial t {Some? (poly_deg r)})
  (a b: algebraic t r)
  : Lemma (requires poly_irreducible r /\
                    not (ac_eq a ac_zero) /\
                    not (ac_eq b ac_zero) /\
                    ac_eq a b)
          (ensures  ac_eq (ac_inv a) (ac_inv b))
  = let ia = ac_inv a in
    let ib = ac_inv b in
    let o  = ac_one in
    ac_elim_equatable_laws r;
    ac_inv_correct a;                         (* ac_eq (ac_mul ia a) o *)
    ac_inv_correct b;                         (* ac_eq (ac_mul b ib) o *)
    (* ia ~ ia*1 *)
    ac_mul_one ia;
    (* 1 ~ b*ib *)
    ac_mul_congruence ia o ia (ac_mul b ib);  (* ac_eq (ia*1) (ia*(b*ib)) *)
    (* ia*(b*ib) ~ (ia*b)*ib *)
    ac_mul_associativity ia b ib;             (* ac_eq ((ia*b)*ib) (ia*(b*ib)) *)
    (* (ia*b)*ib ~ (ia*a)*ib  (since b ~ a) *)
    ac_mul_congruence ia b ia a;              (* ac_eq (ia*b) (ia*a) *)
    ac_mul_congruence (ac_mul ia b) ib (ac_mul ia a) ib;
    (* (ia*a)*ib ~ 1*ib *)
    ac_mul_congruence (ac_mul ia a) ib o ib;  (* ac_eq ((ia*a)*ib) (o*ib) *)
    (* 1*ib ~ ib *)
    ac_mul_one ib                            (* ac_eq (ac_mul o ib) ib (second clause) *)    

(* ================================================================ *)
(*  Assembly:  algebraic t r is a FIELD when r is irreducible.      *)
(* ================================================================ *)

(* 1 <> 0 in the quotient: else r | 1, contradicting irreducibility. *)
let ac_one_ne_zero (#t:Type) {| f: field t |}
  (r: polynomial t {Some? (poly_deg r) /\ poly_irreducible r})
  : Lemma (not (ac_eq (ac_one #t #f #r) (ac_zero #t #f #r)))
  = ac_eq_zero_iff_divides (ac_one #t #f #r);
    ac_one_rep r;
    r_not_divides_one r

let algebraic_mig (#t:Type) {| f: field t |}
  (r: polynomial t {Some? (poly_deg r) /\ poly_irreducible r})
  : mul_is_group (algebraic t r) #((algebraic_commutative_ring #t #f #r).cr_r)
  = {
      inv             = (fun x  -> algebraic_ring_reveal #t #f #r; ac_inv x);
      inv_congr       = (fun aa bb -> algebraic_ring_reveal #t #f #r; ac_inv_congr aa bb);
      inversion_lemma = (fun x  -> algebraic_ring_reveal #t #f #r; ac_inv_correct x);
    }

let algebraic_field (#t:Type) {| f: field t |}
  (r: polynomial t {Some? (poly_deg r) /\ poly_irreducible r})
  : field (algebraic t r)
  = ac_one_ne_zero r;
    algebraic_ring_reveal #t #f #r;
    let one_ne_zero : squash (not (ac_eq (ac_one #t #f #r) (ac_zero #t #f #r))) = () in
    {
      f_sf          = { sf_r = (algebraic_commutative_ring #t #f #r).cr_r;
                        sf_mig = algebraic_mig r };
      f_mic         = (algebraic_commutative_ring #t #f #r).cr_mic;
      f_one_ne_zero = one_ne_zero;
    }
