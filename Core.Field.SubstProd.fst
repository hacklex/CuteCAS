module Core.Field.SubstProd

(* ================================================================ *)
(*  subst_prod:  applying the substitution homomorphism  X |-> h     *)
(*  to the proven splitting identity  X^p - X ~ prod_c (X - c)        *)
(*  yields  h^p - h ~ prod_c (h - [c]),  the input to the Berlekamp   *)
(*  reverse splitting direction  f | prod_c (h - [c]).               *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module E  = Core.Polynomial.Eval
module SU = Core.Polynomial.Subst
module BK = Core.Field.Berlekamp
module FE = Core.Field.FpEnum
module PR = Core.Polynomial.Product
module RT = Core.Polynomial.Root

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div
open Core.FinSum
open Core.Field.Fp
open FStar.Math.Euclid

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* the commutative_ring a field carries (what poly_pow / poly_linear thread). *)
let fcr (#t:Type) (f: field t) : commutative_ring t = cr_of_id t #(id_of_f t #f)

(* phi_h(g^k) = (phi_h g)^k. *)
let rec subst_pow (#t:Type) {| f: field t |} (h g: polynomial t) (k:nat)
  : Lemma (ensures poly_eq (SU.poly_subst #t #(fcr f) h (BK.poly_pow #t #f g k))
                           (BK.poly_pow #t #f (SU.poly_subst #t #(fcr f) h g) k))
          (decreases k)
  = let cr = fcr f in
    H.elim_equatable_laws (polynomial t) #((SU.pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((SU.pacg cr).acg_eq) ();
    let sg = SU.poly_subst #t #cr h g in
    if k = 0 then begin
      BK.poly_pow_zero #t #f g;                                  (* poly_pow g 0 == poly_one *)
      BK.poly_pow_zero #t #f sg;                                 (* poly_pow sg 0 == poly_one *)
      SU.subst_one #t #cr h                                      (* poly_subst h poly_one ~ poly_one *)
    end else begin
      BK.poly_pow_succ #t #f g (k-1);                            (* poly_pow g k == poly_mul g (poly_pow g (k-1)) *)
      BK.poly_pow_succ #t #f sg (k-1);                           (* poly_pow sg k == poly_mul sg (poly_pow sg (k-1)) *)
      SU.subst_mul #t #cr h g (BK.poly_pow #t #f g (k-1));       (* subst(g * pow) ~ subst g * subst pow *)
      subst_pow h g (k-1);                                       (* IH *)
      reflexivity #(polynomial t) #((SU.pacg cr).acg_eq) sg;
      mul_congruence #(polynomial t) #((SU.pcr cr).cr_r)
        sg (SU.poly_subst #t #cr h (BK.poly_pow #t #f g (k-1)))
        sg (BK.poly_pow #t #f sg (k-1));
      transitivity #(polynomial t) #((SU.pacg cr).acg_eq)
        (SU.poly_subst #t #cr h (BK.poly_pow #t #f g k))
        (poly_mul sg (SU.poly_subst #t #cr h (BK.poly_pow #t #f g (k-1))))
        (poly_mul sg (BK.poly_pow #t #f sg (k-1)))
    end

(* phi_h([c]) = [c]  (constants are fixed). *)
#push-options "--fuel 4 --ifuel 2"
let subst_const0 (#t:Type) {| f: field t |} (h: polynomial t) (c: t)
  : Lemma (poly_eq (SU.poly_subst #t #(fcr f) h (SU.const0 #t #(fcr f) c)) (SU.const0 #t #(fcr f) c))
  = let cr = fcr f in
    H.elim_equatable_laws (polynomial t) #((SU.pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((SU.pacg cr).acg_eq) ();
    let cp = SU.const0 #t #cr c in
    let f1 = SU.subst_term #t #cr h cp in
    if c = (zero <: t) then begin
      (* cp = monomial c 0 == [] ; poly_subst = empty sum = poly_zero ~ cp *)
      sum_range_empty #(polynomial t) #(SU.pacg cr) f1 0 0;       (* poly_subst h cp = poly_zero *)
      SU.const0_congr #t #cr c (zero <: t);                       (* cp ~ const0 zero *)
      SU.const0_zero #t #cr ();                                    (* const0 zero ~ poly_zero *)
      transitivity #(polynomial t) #((SU.pacg cr).acg_eq) cp (SU.const0 #t #cr (zero <: t)) (poly_zero #t);
      symmetry #(polynomial t) #((SU.pacg cr).acg_eq) cp (poly_zero #t)   (* poly_zero ~ cp *)
    end else begin
      (* cp = [c] : single term  const0 c * h^0 = const0 c * 1 ~ const0 c *)
      monomial_zero_n_reveal #t #cr c;                             (* cp == [c] (c <> 0) ; length 1 *)
      assert (L.length cp == 1);
      sum_range_unfold_left #(polynomial t) #(SU.pacg cr) f1 0 1;
      sum_range_empty #(polynomial t) #(SU.pacg cr) f1 1 1;
      H.x_plus_zero #(polynomial t) #(SU.pacg cr) (f1 0);
      add_congruence #(polynomial t) #(SU.pacg cr) (f1 0) (sum_range #(polynomial t) #(SU.pacg cr) f1 1 1)
                     (f1 0) (poly_zero #t);
      (* f1 0 = const0 (coeff cp 0) * (cpow h 0 = poly_one) = const0 c * poly_one ~ const0 c *)
      SU.const0_coeff0 #t #cr c;                                   (* coeff cp 0 = c *)
      SU.const0_congr #t #cr (coeff cp 0) c;                        (* const0 (coeff cp 0) ~ const0 c = cp *)
      H.x_mul_one #(polynomial t) #((SU.pcr cr).cr_r) cp;          (* cp * one ~ cp *)
      mul_congruence #(polynomial t) #((SU.pcr cr).cr_r)
        (SU.const0 #t #cr (coeff cp 0)) (E.cpow #(polynomial t) #(SU.pcr cr) h 0)
        cp (E.cpow #(polynomial t) #(SU.pcr cr) h 0);
      transitivity #(polynomial t) #((SU.pacg cr).acg_eq)
        (f1 0) (poly_mul cp (E.cpow #(polynomial t) #(SU.pcr cr) h 0)) cp;
      transitivity #(polynomial t) #((SU.pacg cr).acg_eq)
        (SU.poly_subst #t #cr h cp) (f1 0) cp
    end
#pop-options

(* phi_h(x - c) = h - [c]. *)
#push-options "--fuel 6 --ifuel 2 --z3rlimit 150"
let subst_linear (#t:Type) {| f: field t |} (h: polynomial t) (c: t)
  : Lemma (poly_eq (SU.poly_subst #t #(fcr f) h (RT.poly_linear #t #f c))
                   (poly_sub #t #(fcr f) h (SU.const0 #t #(fcr f) c)))
  = let cr = fcr f in
    H.elim_equatable_laws (polynomial t) #((SU.pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((SU.pacg cr).acg_eq) ();
    let lin = RT.poly_linear #t #f c in
    let f1 = SU.subst_term #t #cr h lin in
    assert (lin == [((cr.cr_r.r_add).neg c); (one <: t)]);
    assert (L.length lin == 2);
    assert (coeff lin 0 == ((cr.cr_r.r_add).neg c));
    assert (coeff lin 1 == (one <: t));
    let ck0 = E.cpow #(polynomial t) #(SU.pcr cr) h 0 in    (* == poly_one *)
    let ck1 = E.cpow #(polynomial t) #(SU.pcr cr) h 1 in    (* == poly_mul h poly_one *)
    (* sum_range f1 0 2 = f1 0 + (f1 1 + poly_zero) *)
    sum_range_unfold_left #(polynomial t) #(SU.pacg cr) f1 0 2;
    sum_range_unfold_left #(polynomial t) #(SU.pacg cr) f1 1 2;
    sum_range_empty #(polynomial t) #(SU.pacg cr) f1 2 2;
    H.x_plus_zero #(polynomial t) #(SU.pacg cr) (f1 1);
    add_congruence #(polynomial t) #(SU.pacg cr) (f1 1) (sum_range #(polynomial t) #(SU.pacg cr) f1 2 2)
                   (f1 1) (poly_zero #t);
    (* ---- f1 0 ~ poly_neg (const0 c) ---- *)
    SU.const0_congr #t #cr (coeff lin 0) (((cr.cr_r.r_add).neg c));                 (* const0 (coeff lin 0) ~ const0 (((cr.cr_r.r_add).neg c)) *)
    SU.const0_neg #t #cr c;                                        (* const0 (((cr.cr_r.r_add).neg c)) ~ poly_neg (const0 c) *)
    H.x_mul_one #(polynomial t) #((SU.pcr cr).cr_r) (SU.const0 #t #cr (coeff lin 0));  (* const0(coeff lin 0)*one ~ const0(coeff lin 0) ; ck0 == one *)
    transitivity #(polynomial t) #((SU.pacg cr).acg_eq)
      (f1 0) (SU.const0 #t #cr (coeff lin 0)) (SU.const0 #t #cr (((cr.cr_r.r_add).neg c)));
    transitivity #(polynomial t) #((SU.pacg cr).acg_eq)
      (f1 0) (SU.const0 #t #cr (((cr.cr_r.r_add).neg c))) (poly_neg (SU.const0 #t #cr c));
    (* ---- f1 1 ~ h ---- *)
    SU.const0_congr #t #cr (coeff lin 1) (one <: t);              (* const0 (coeff lin 1) ~ const0 one *)
    SU.const0_one #t #cr ();                                       (* const0 one ~ poly_one *)
    H.x_mul_one #(polynomial t) #((SU.pcr cr).cr_r) h;            (* poly_mul h poly_one ~ h ; ck1 == poly_mul h one *)
    H.one_mul_x #(polynomial t) #((SU.pcr cr).cr_r) h;           (* poly_mul poly_one h ~ h *)
    (* const0(coeff lin 1) ~ poly_one, ck1 ~ h  ⇒  f1 1 = const0(coeff lin 1)*ck1 ~ poly_one*h ~ h *)
    mul_congruence #(polynomial t) #((SU.pcr cr).cr_r)
      (SU.const0 #t #cr (coeff lin 1)) ck1 (poly_one #t) h;
    transitivity #(polynomial t) #((SU.pacg cr).acg_eq)
      (f1 1) (poly_mul (poly_one #t) h) h;
    (* ---- assemble:  f1 0 + (f1 1 + 0) ~ poly_neg(const0 c) + h ~ h + poly_neg(const0 c) = poly_sub h [c] ---- *)
    add_congruence #(polynomial t) #(SU.pacg cr)
      (f1 0) (f1 1) (poly_neg (SU.const0 #t #cr c)) h;
    add_commutativity #(polynomial t) #(SU.pacg cr) (poly_neg (SU.const0 #t #cr c)) h;
    poly_sub_reveal h (SU.const0 #t #cr c);                        (* poly_sub h [c] == poly_add h (poly_neg [c]) *)
    transitivity #(polynomial t) #((SU.pacg cr).acg_eq)
      (SU.poly_subst #t #cr h lin)
      (poly_add (f1 0) (f1 1))
      (poly_add (poly_neg (SU.const0 #t #cr c)) h);
    transitivity #(polynomial t) #((SU.pacg cr).acg_eq)
      (SU.poly_subst #t #cr h lin)
      (poly_add (poly_neg (SU.const0 #t #cr c)) h)
      (poly_sub h (SU.const0 #t #cr c))
#pop-options

(* poly_pow respects poly_eq in the base. *)
let rec poly_pow_congr (#t:Type) {| f: field t |} (a b: polynomial t) (k:nat)
  : Lemma (requires poly_eq a b)
          (ensures poly_eq (BK.poly_pow #t #f a k) (BK.poly_pow #t #f b k))
          (decreases k)
  = let cr = fcr f in
    H.elim_equatable_laws (polynomial t) #((SU.pacg cr).acg_eq) ();
    if k = 0 then begin
      BK.poly_pow_zero #t #f a; BK.poly_pow_zero #t #f b;
      reflexivity #(polynomial t) #((SU.pacg cr).acg_eq) (poly_one #t)
    end else begin
      BK.poly_pow_succ #t #f a (k-1); BK.poly_pow_succ #t #f b (k-1);
      poly_pow_congr a b (k-1);
      mul_congruence #(polynomial t) #((SU.pcr cr).cr_r)
        a (BK.poly_pow #t #f a (k-1)) b (BK.poly_pow #t #f b (k-1))
    end

(* phi_h(prod_linears roots) = poly_prod (map (\c. h - [c]) roots). *)
let rec subst_poly_prod_linears (#t:Type) {| f: field t |} (h: polynomial t) (roots: list t)
  : Lemma (ensures poly_eq (SU.poly_subst #t #(fcr f) h (PR.poly_prod_linears #t #f roots))
                           (PR.poly_prod #t #(fcr f)
                              (L.map (fun (c:t) -> poly_sub #t #(fcr f) h (SU.const0 #t #(fcr f) c)) roots)))
          (decreases roots)
  = let cr = fcr f in
    H.elim_equatable_laws (polynomial t) #((SU.pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial t) #((SU.pacg cr).acg_eq) ();
    match roots with
    | [] -> SU.subst_one #t #cr h
    | c :: rest ->
      let lin = RT.poly_linear #t #f c in
      let prest = PR.poly_prod_linears #t #f rest in
      SU.subst_mul #t #cr h lin prest;                              (* subst(lin * prest) ~ subst lin * subst prest *)
      subst_linear h c;                                             (* subst lin ~ poly_sub h [c] *)
      subst_poly_prod_linears h rest;                              (* IH: subst prest ~ poly_prod (map .. rest) *)
      mul_congruence #(polynomial t) #((SU.pcr cr).cr_r)
        (SU.poly_subst #t #cr h lin) (SU.poly_subst #t #cr h prest)
        (poly_sub h (SU.const0 #t #cr c))
        (PR.poly_prod #t #(fcr f) (L.map (fun (c:t) -> poly_sub #t #(fcr f) h (SU.const0 #t #(fcr f) c)) rest));
      transitivity #(polynomial t) #((SU.pacg cr).acg_eq)
        (SU.poly_subst #t #cr h (PR.poly_prod_linears #t #f roots))
        (poly_mul (SU.poly_subst #t #cr h lin) (SU.poly_subst #t #cr h prest))
        (poly_mul (poly_sub h (SU.const0 #t #cr c))
                  (PR.poly_prod #t #(fcr f) (L.map (fun (c:t) -> poly_sub #t #(fcr f) h (SU.const0 #t #(fcr f) c)) rest)))

(* poly_sub respects poly_eq in both arguments. *)
let poly_sub_congr (#t:Type) {| f: field t |} (a b a' b': polynomial t)
  : Lemma (requires poly_eq a a' /\ poly_eq b b')
          (ensures poly_eq (poly_sub a b) (poly_sub a' b'))
  = let cr = fcr f in
    H.elim_equatable_laws (polynomial t) #((SU.pacg cr).acg_eq) ();
    poly_sub_reveal a b; poly_sub_reveal a' b';
    neg_congruence #(polynomial t) #(SU.pacg cr) b b';
    add_congruence #(polynomial t) #(SU.pacg cr) a (poly_neg b) a' (poly_neg b')

(* phi_h(X) = h. *)
let subst_X (p:int{is_prime p}) (h: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (poly_eq (SU.poly_subst #(fp p) #(fcr (fp_field p)) h (FE.polyX p)) h)
  = let f = fp_field p in let cr = fcr f in
    H.elim_equatable_laws (polynomial (fp p)) #((SU.pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial (fp p)) #((SU.pacg cr).acg_eq) ();
    (* polyX = poly_linear (fp_zero p) ; subst ~ poly_sub h (const0 (fp_zero p)) *)
    subst_linear #(fp p) #f h (fp_zero p);
    (* const0 (fp_zero p) ~ poly_zero *)
    SU.const0_congr #(fp p) #cr (fp_zero p) (zero <: fp p);
    SU.const0_zero #(fp p) #cr ();
    transitivity #(polynomial (fp p)) #((SU.pacg cr).acg_eq)
      (SU.const0 #(fp p) #cr (fp_zero p)) (SU.const0 #(fp p) #cr (zero <: fp p)) (poly_zero #(fp p));
    (* poly_sub h (const0 (fp_zero p)) ~ poly_sub h poly_zero ~ h *)
    poly_sub_congr #(fp p) #f h (SU.const0 #(fp p) #cr (fp_zero p)) h (poly_zero #(fp p));
    poly_sub_reveal h (poly_zero #(fp p));                         (* poly_sub h 0 == poly_add h (poly_neg 0) *)
    H.neg_zero #(polynomial (fp p)) #(SU.pacg cr) ();             (* poly_neg poly_zero ~ poly_zero *)
    reflexivity #(polynomial (fp p)) #((SU.pacg cr).acg_eq) h;
    add_congruence #(polynomial (fp p)) #(SU.pacg cr) h (poly_neg (poly_zero #(fp p))) h (poly_zero #(fp p));
    H.x_plus_zero #(polynomial (fp p)) #(SU.pacg cr) h;
    transitivity #(polynomial (fp p)) #((SU.pacg cr).acg_eq)
      (poly_sub h (poly_zero #(fp p))) (poly_add h (poly_neg (poly_zero #(fp p)))) (poly_add h (poly_zero #(fp p)));
    transitivity #(polynomial (fp p)) #((SU.pacg cr).acg_eq)
      (poly_sub h (poly_zero #(fp p))) (poly_add h (poly_zero #(fp p))) h;
    transitivity #(polynomial (fp p)) #((SU.pacg cr).acg_eq)
      (SU.poly_subst #(fp p) #cr h (FE.polyX p))
      (poly_sub h (SU.const0 #(fp p) #cr (fp_zero p)))
      (poly_sub h (poly_zero #(fp p)));
    transitivity #(polynomial (fp p)) #((SU.pacg cr).acg_eq)
      (SU.poly_subst #(fp p) #cr h (FE.polyX p))
      (poly_sub h (poly_zero #(fp p)))
      h

(* ================================================================ *)
(*  THE GOAL:  h^p - h  ~  prod_{c in fp p} (h - [c]).               *)
(* ================================================================ *)
#push-options "--z3rlimit 150"
let subst_prod (p:int{is_prime p}) (h: polynomial (fp p) #(fp_comm_ring p))
  : Lemma (poly_eq (poly_sub (BK.poly_pow #(fp p) #(fp_field p) h (p <: nat)) h)
                   (PR.poly_prod #(fp p) #(fcr (fp_field p))
                      (L.map (fun (c:fp p) -> poly_sub #(fp p) #(fcr (fp_field p)) h (SU.const0 #(fp p) #(fcr (fp_field p)) c)) (FE.fp_enum p))))
  = let cr = fcr (fp_field p) in
    assert (cr == fp_comm_ring p);                                (* defeq bridge: lets SMT rewrite the poly_eq instance *)
    H.elim_equatable_laws (polynomial (fp p)) #((SU.pacg cr).acg_eq) ();
    H.trans_for_calc (polynomial (fp p)) #((SU.pacg cr).acg_eq) ();
    let roots = FE.fp_enum p in
    let pX = FE.polyX p in
    let xp = BK.poly_pow #(fp p) #(fp_field p) pX (p <: nat) in
    let sh = SU.poly_subst #(fp p) #(fcr (fp_field p)) h in
    let prodlin = PR.poly_prod_linears #(fp p) #(fp_field p) roots in
    let rhs = PR.poly_prod #(fp p) #(fcr (fp_field p))
                (L.map (fun (c:fp p) -> poly_sub #(fp p) #(fcr (fp_field p)) h (SU.const0 #(fp p) #(fcr (fp_field p)) c)) roots) in
    let php = BK.poly_pow #(fp p) #(fp_field p) h (p <: nat) in
    (* RHS chain:  sh(xpx) ~ sh(prodlin) ~ rhs *)
    Core.Field.BerlekampSplit.xpx_splits p;                       (* xpx ~ prodlin *)
    SU.subst_congr #(fp p) #(fcr (fp_field p)) h (FE.xpx p) prodlin;  (* sh(xpx) ~ sh(prodlin) *)
    subst_poly_prod_linears #(fp p) #(fp_field p) h roots;       (* sh(prodlin) ~ rhs *)
    transitivity #(polynomial (fp p)) #((SU.pacg cr).acg_eq) (sh (FE.xpx p)) (sh prodlin) rhs;
    (* LHS chain:  sh(xpx) ~ poly_sub (sh xp)(sh pX) ~ poly_sub php h *)
    SU.subst_sub #(fp p) #(fcr (fp_field p)) h xp pX;            (* sh(poly_sub xp pX) ~ poly_sub (sh xp)(sh pX) ; xpx == poly_sub xp pX *)
    subst_pow #(fp p) #(fp_field p) h pX (p <: nat);             (* sh xp ~ poly_pow (sh pX) p *)
    subst_X p h;                                                  (* sh pX ~ h *)
    poly_pow_congr #(fp p) #(fp_field p) (sh pX) h (p <: nat);   (* poly_pow (sh pX) p ~ php *)
    transitivity #(polynomial (fp p)) #((SU.pacg cr).acg_eq)
      (sh xp) (BK.poly_pow #(fp p) #(fp_field p) (sh pX) (p <: nat)) php;   (* sh xp ~ php *)
    poly_sub_congr #(fp p) #(fp_field p) (sh xp) (sh pX) php h;  (* poly_sub (sh xp)(sh pX) ~ poly_sub php h *)
    transitivity #(polynomial (fp p)) #((SU.pacg cr).acg_eq)
      (sh (FE.xpx p)) (poly_sub (sh xp) (sh pX)) (poly_sub php h);
    (* combine:  poly_sub php h ~ sh(xpx) ~ rhs *)
    symmetry #(polynomial (fp p)) #((SU.pacg cr).acg_eq) (sh (FE.xpx p)) (poly_sub php h);
    transitivity #(polynomial (fp p)) #((SU.pacg cr).acg_eq) (poly_sub php h) (sh (FE.xpx p)) rhs
#pop-options
