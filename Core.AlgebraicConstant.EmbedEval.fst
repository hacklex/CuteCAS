module Core.AlgebraicConstant.EmbedEval

(*
   §E splitting-field bridge (P6): polynomial evaluation TRANSPORTS through
   the coefficient-wise embedding at embedded points.

       poly_eval (ext_embed_poly p) (ac_const a)  ~  ac_const (poly_eval p a)

   i.e. evaluating the embedded polynomial  ext_embed_poly p : (algebraic r)[X]
   at the embedded point  ac_const a : algebraic r  gives the embedding of the
   base evaluation  poly_eval p a : t.

   Route (poly_eval = Σ_{i<len} coeff p i * cpow c i):
     - ac_const_power   : ac_const (cpow a k) ~ cpow (ac_const a) k
     - embed_eval_term  : per-term transport (embed_coeff + ac_const_mul + power)
     - embed_eval_transport : push ac_const through the eval sum
                              (ac_const_sum_push) + range reconcile (embed_len_le).
*)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Eval
open Core.Polynomial.Irreducible
open Core.FinSum
open Core.AlgebraicConstant
open Core.AlgebraicConstant.Root
open Core.AlgebraicConstant.Eval
open Core.AlgebraicConstant.EmbedHom

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  0.  ac_const one ~ one  (extension one = ac_one).               *)
(* ================================================================ *)

let ac_const_one (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r}) ()
  : Lemma (ac_eq (ac_const #_ #_ #r (one <: t)) (ac_one #_ #_ #r))
  = (* (ac_const one <: polynomial t) == poly_const one ;
       (ac_one <: polynomial t) == poly_one ; poly_const one ~ poly_one. *)
    assert ((ac_const #_ #_ #r (one <: t) <: polynomial t) == poly_const (one <: t))
      by (FStar.Tactics.norm [delta_only [`%ac_const]; iota; zeta]; FStar.Tactics.trefl ());
    H.elim_equatable_laws (polynomial t) ();
    poly_const_one #t ();                              (* poly_eq (poly_const one) poly_one *)
    ac_one_rep r;                                      (* ac_one == poly_one *)
    poly_eq_implies_ac_eq (ac_const #_ #_ #r (one <: t)) (ac_one #_ #_ #r)

(* ================================================================ *)
(*  1.  ac_const pushes through the carrier power cpow.             *)
(*      ac_const (cpow a k)  ~  cpow (ac_const a) k.                *)
(* ================================================================ *)

let rec ac_const_power (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                       (a: t) (k: nat)
  : Lemma (ensures ac_eq (ac_const #_ #_ #r (cpow a k))
                         (cpow (ac_const #_ #_ #r a) k))
          (decreases k)
  = ac_elim_equatable_laws r;
    H.trans_for_calc (algebraic r) ();
    if k = 0 then
      (* cpow a 0 == one<:t ; cpow (ac_const a) 0 == one == ac_one. *)
      ac_const_one #_ #_ #r ()
    else begin
      let th : algebraic r = ac_const a in
      (* cpow a k == a * cpow a (k-1) ; cpow th k == th * cpow th (k-1). *)
      ac_const_mul #_ #_ #r a (cpow a (k - 1));
        (* ac_const (a * cpow a (k-1)) ~ ac_const a * ac_const (cpow a (k-1)) *)
      ac_const_power #_ #_ #r a (k - 1);
        (* IH: ac_const (cpow a (k-1)) ~ cpow th (k-1) *)
      mul_congruence
        (ac_const #_ #_ #r a) (ac_const #_ #_ #r (cpow a (k - 1)))
        th (cpow th (k - 1))
        (* ac_const a * ac_const (cpow a (k-1)) ~ th * cpow th (k-1) *)
    end

(* ================================================================ *)
(*  2.  Per-term transport.                                          *)
(*      eval_term (embed p) (ac_const a) i  ~  ac_const (eval_term p a i). *)
(* ================================================================ *)

private let embed_eval_term (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                            (p: polynomial t) (a: t) (i: nat)
  : Lemma (ac_eq
             (eval_term (ext_embed_poly #_ #_ #r p) (ac_const #_ #_ #r a) i)
             (ac_const #_ #_ #r (eval_term p a i)))
  = ac_elim_equatable_laws r;
    H.trans_for_calc (algebraic r) ();
    let th  : algebraic r = ac_const a in
    let ea  : polynomial (algebraic r) = ext_embed_poly p in
    let cpi : t = coeff p i in
    let cai : t = cpow a i in
    (* eval_term ea th i == coeff ea i * cpow th i         (defeq)
       ac_const (eval_term p a i) == ac_const (cpi * cai)  (defeq) *)
    embed_coeff #_ #_ #r p i;                    (* coeff ea i ~ ac_const cpi *)
    ac_const_power #_ #_ #r a i;                 (* ac_const cai ~ cpow th i *)
    mul_congruence
      (coeff ea i) (cpow th i)
      (ac_const #_ #_ #r cpi) (ac_const #_ #_ #r cai);
      (* coeff ea i * cpow th i ~ ac_const cpi * ac_const cai *)
    ac_const_mul #_ #_ #r cpi cai                (* ac_const (cpi*cai) ~ ac_const cpi * ac_const cai *)

(* ================================================================ *)
(*  3.  Eval transport.                                              *)
(* ================================================================ *)

let embed_eval_transport (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                         (p: polynomial t) (a: t)
  : Lemma (ac_eq
             (poly_eval (ext_embed_poly #_ #_ #r p) (ac_const #_ #_ #r a))
             (ac_const #_ #_ #r (poly_eval p a)))
  = ac_elim_equatable_laws r;
    H.trans_for_calc (algebraic r) ();
    let th : algebraic r = ac_const a in
    let ea : polynomial (algebraic r) = ext_embed_poly p in
    let la : nat = L.length p in
    let fe : (nat -> algebraic r) = eval_term ea th in
    let gc : (nat -> algebraic r) = ac_const_comp (eval_term p a) in
    (* poly_eval ea th == sum_range fe 0 (len ea)  (defeq).  Extend to la. *)
    embed_len_le #_ #_ #r p;                     (* len ea <= la *)
    eval_extend ea th la;                        (* sum_range fe 0 la ~ poly_eval ea th *)
    (* ac_const (poly_eval p a) == ac_const (sum_range (eval_term p a) 0 la) (defeq). *)
    ac_const_sum_push #_ #_ #r (eval_term p a) 0 la;
      (* ac_const (sum_range (eval_term p a) 0 la) ~ sum_range gc 0 la *)
    sum_range_congruence fe gc 0 la
      (fun (i:nat{0 <= i /\ i < la}) -> embed_eval_term #_ #_ #r p a i);
      (* sum_range fe 0 la ~ sum_range gc 0 la *)
    (* chain (armed symmetry/transitivity):
         poly_eval ea th ~ sum_range fe 0 la           [eval_extend]
                         ~ sum_range gc 0 la            [sum_range_congruence]
                         ~ ac_const (poly_eval p a)     [ac_const_sum_push] *)
    ()

(* ================================================================ *)
(*  P8: the embedding respects polynomial equality (congruence).     *)
(* ================================================================ *)

let ext_embed_congr (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
  (p q: polynomial t)
  : Lemma (requires p = q)
          (ensures (ext_embed_poly #t #f #r p) = (ext_embed_poly #t #f #r q))
  = let ep : polynomial (algebraic r) = ext_embed_poly #t #f #r p in
    let eq2 : polynomial (algebraic r) = ext_embed_poly #t #f #r q in
    let h (j: nat) : Lemma (coeff ep j = coeff eq2 j) =
      H.elim_equatable_laws (algebraic r) ();
      H.trans_for_calc (algebraic r) ();
      poly_eq_means_equal_coeffs p q j;             (* coeff p j = coeff q j *)
      ac_const_congr #t #f #r (coeff p j) (coeff q j);
      embed_coeff #t #f #r p j;                     (* coeff ep j = ac_const (coeff p j) *)
      embed_coeff #t #f #r q j                      (* coeff eq2 j = ac_const (coeff q j) *)
    in
    poly_eq_by_coeff ep eq2 h
