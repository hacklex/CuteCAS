module Core.AlgebraicConstant.PeelQuotient
(*    ┬зE splitting-field peel step, quotient extraction.
     Building on Core.AlgebraicConstant.Peel.peel_root_factor, which proves
	 (X - theta) | ext_embed_poly d over the extension field fe = algebraic_field r,
	 we extract the explicit QUOTIENT q with
	 ext_embed_poly d  тЙИ  (X - theta) ┬╖ q
	 (over fe's ring cr_fe)
     together with a degree drop  deg q < deg (ext_embed_poly d)  (when the latter
	 is nonzero), giving a recursable form for the splitting-field construction. *)

module H  = Core.Algebra.Helpers
module L  = FStar.List.Tot

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Polynomial.Irreducible
open Core.Polynomial.Unique
open Core.AlgebraicConstant
open Core.AlgebraicConstant.Root
open Core.AlgebraicConstant.Eval
open Core.AlgebraicConstant.Peel

#set-options "--fuel 0 --ifuel 0 --z3rlimit 50"
(* The canonical embedding is Core.AlgebraicConstant.Eval.ext_embed_poly;
    this is a thin unfold alias with the extension polynomial r EXPLICIT,
    for consumers (Peel / ExtendStep / SplitBuild) that name r at call sites. *)
unfold let embed_poly #t {| field t |} (r: polynomial t {proper_extension r}) (p: polynomial t)
  : polynomial (algebraic r)
  = ext_embed_poly #_ #_ #r p

(* ================================================================ *)
(*  Peel:  (X - theta) | (embed_poly r d)  over algebraic r.      *)
(*  The embedded d evaluates to zero at theta over the field-derived *)
(*  ring; the factor theorem peels (X - theta).  With acr r now      *)
(*  DEFEQ to the field-derived ring, ext_embed_poly d IS already     *)
(*  embed_poly r d at the field-derived index тАФ no coerce_eq needed. *)
(* ================================================================ *)
let peel_root_factor_clean (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r}) (d: polynomial t)
  : Lemma (requires divides r d)
          (ensures (divides (poly_linear theta) (embed_poly r d)))
  = theta_eval_field_zero r d;
    factor_forward (ext_embed_poly d) (theta #t #f #r)

(* The quotient extraction lemma. *)
#push-options "--z3rlimit 150 --fuel 2 --ifuel 1"
let peel_root_quotient (#t:Type) {| f: field t |}
  (r: polynomial t {proper_extension r})
  (d: polynomial t)
  : Lemma (requires (divides r d) /\ deg d >= 0)
          (ensures exists (q: polynomial (algebraic r)).
                          (embed_poly r d) = ((poly_linear (theta )) * q) /\
                          (deg (embed_poly r d) >= 0 ==> deg q >= 0 /\
                          deg q < deg (embed_poly r d)))
  = H.elim_equatable_laws (polynomial (algebraic r)) ();
    H.trans_for_calc (polynomial (algebraic r)) ();
    let ed : polynomial (algebraic r) = (embed_poly r d) in
    let th = theta #t #f #r in
    let la : polynomial (algebraic r) = poly_linear th in
    let ( * ) (x y: polynomial (algebraic r)) = (x * y) in
    let (=) (x y: polynomial (algebraic r)) = eq x y in
    poly_linear_deg th;
    (* deg la = 1 *)
    (* From Peel: (X - theta) | ed over cr_fe. *)
    peel_root_factor_clean r d;
    assert (divides la ed);
    (* divides la ed  ==  exists c. eq ed (mul la c)
       with cr_e's eq/mul, which are poly_eq / poly_mul. *)
    assert (exists (q: polynomial (algebraic r)). ed = la * q);
    eliminate exists (q: polynomial (algebraic r)). ed = la * q
    returns (exists (q: polynomial (algebraic r)).
                    ed = la * q /\ (deg ed >= 0 ==> deg q >= 0 /\ deg q < deg ed))
    with _hq. begin
      (* eq/mul of cr_e are poly_eq/poly_mul (definitional via the instance). *)
      assert (ed = la * q);
      (* Degree clause, under deg ed >= 0. *)
      let prove_deg () : Lemma (requires deg ed >= 0)
                               (ensures  deg q >= 0 /\ deg q < deg ed)
      = (* q must be nonzero: else la*q ~ 0, contradicting ed nonzero. *)
        if deg q < 0 then begin
          (* q ~ 0  ==>  la*q ~ 0 ; with ed ~ la*q, ed ~ 0, deg ed < 0.
          But requires deg ed >= 0: contradiction. *)
          degree_none_poly_eq_zero q;
          (* q ~ poly_zero *)
          mul_congruence la q la poly_zero;
          (* la*q ~ la*poly_zero *)
          H.x_mul_zero la; (* la*poly_zero ~ poly_zero *)
          transitivity (la * q) (la * poly_zero) (poly_zero);
          (* la*q ~ poly_zero *)
          degree_well_defined (la * q) (poly_zero);
          (* deg(la*q) < 0 *)
          degree_well_defined ed (la * q)
          (* deg ed = deg(la*q) < 0 *)
        end else begin
            poly_linear_deg th;
          (* deg la = 1 *)
          degree_mul la q;
          (* deg(la*q)=deg la+deg q=1+deg q *)
          degree_well_defined ed (la * q);
          assert (deg (la * q) == (1 ++ (deg q)))
        end 
      in
      introduce deg ed >= 0 ==> (deg q >= 0 /\ deg q < deg ed)
      with _pf. prove_deg ();
      introduce exists (q': polynomial (algebraic r)).
                            ed = (la * q') /\ (deg ed >= 0 ==>
                                               deg q' >= 0 /\ deg q' < deg ed)
      with q and ()
    end
#pop-options 