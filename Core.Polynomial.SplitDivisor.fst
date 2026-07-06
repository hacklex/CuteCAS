module Core.Polynomial.SplitDivisor

(* ================================================================ *)
(*  A divisor of a product of DISTINCT linear factors splits         *)
(*  completely:  its degree equals the number of its roots that      *)
(*  lie among `roots`.                                               *)
(*                                                                   *)
(*  Headline:  `divisor_split_count` —                               *)
(*    vc | ∏_{β∈roots}(x−β),  roots distinct,  cset = EXACTLY the     *)
(*    members of roots that are roots of vc   ⇒   deg vc = #cset.     *)
(*                                                                   *)
(*  Reusable Roots-level theory. Consumed by Core.Risch.RTSoundness  *)
(*  (T6 / Rothstein-Trager) where, via `gcd_root_iff_residue`, the   *)
(*  vc-root set is the residue-c set, giving the count that          *)
(*  `vc_factorization_given_count` needs — closing the last T6       *)
(*  obligation and making the tier-2 RT soundness capstone           *)
(*  UNCONDITIONAL.                                                    *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module IR = Core.Polynomial.Irreducible
module CR = Core.Polynomial.CRT
module SF = Core.Polynomial.SquareFree

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Roots

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* --- self-contained copies of two tiny RTSoundness-local helpers --- *)

let poly_one_deg (#t:Type) {| f: field t |} ()
  : Lemma (deg (poly_one #t) == 0)
  = H.elim_equatable_laws t ();
    let _ : squash (not (one #t = zero)) = f.f_one_ne_zero in
    poly_lc_reveal (poly_one #t)

(* --- generic Bezout-implies-coprime helpers (moved from
       Core.AlgebraicConstant.EmbedSquareFree §A; they need poly_one_deg +
       IR.divides_degree_le, so this is their lowest possible home) --- *)

(* A divisor of the (nonzero) unit poly_one is itself nonzero. *)
let divisor_of_one_deg_ge0 (#s:Type) {| fs: field s |} (g: polynomial s)
  : Lemma (requires divides g (poly_one #s))
          (ensures  deg g >= 0)
  = H.elim_equatable_laws (polynomial s) ();
    H.trans_for_calc (polynomial s) ();
    poly_one_deg #s ();
    if deg g >= 0 then ()
    else begin
      Core.Polynomial.Unique.degree_none_poly_eq_zero g;   (* g = poly_zero *)
      let aux (c: polynomial s)
        : Lemma (requires ((poly_one #s) = (g * c))) (ensures False)
        = mul_congruence g c (poly_zero #s) c;    (* g*c = poly_zero*c *)
          H.zero_mul_x c;                          (* poly_zero*c = poly_zero *)
          transitivity (g * c) ((poly_zero #s) * c) (poly_zero #s);
          transitivity (poly_one #s) (g * c) (poly_zero #s);
          Core.Polynomial.Unique.degree_well_defined (poly_one #s) (poly_zero #s)
            (* 0 == -1 : False *)
      in
      Classical.forall_intro (Classical.move_requires aux)
    end

(* A Bezout combination equal to 1 forces coprimality. *)
let bezout_implies_coprime (#s:Type) {| fs: field s |}
  (p q sw ww: polynomial s)
  : Lemma (requires (((sw * p) + (ww * q)) = (poly_one #s)))
          (ensures  coprime p q)
  = H.elim_equatable_laws (polynomial s) ();
    H.trans_for_calc (polynomial s) ();
    coprime_reveal p q;
    let g = poly_gcd p q in
    gcd_divides_left  p q;                          (* divides g p *)
    gcd_divides_right p q;                          (* divides g q *)
    divides_mul_left g sw p;                        (* divides g (sw*p) *)
    divides_mul_left g ww q;                        (* divides g (ww*q) *)
    divides_add g (sw * p) (ww * q);                (* divides g ((sw*p)+(ww*q)) *)
    divides_congruence_right g ((sw * p) + (ww * q)) (poly_one #s);  (* divides g poly_one *)
    divisor_of_one_deg_ge0 g;                       (* deg g >= 0 *)
    poly_one_deg #s ();                             (* deg poly_one == 0 *)
    IR.divides_degree_le g (poly_one #s)            (* deg g <= 0 ; with >= 0 ⇒ = 0 *)

let rec poly_prod_linears_deg (#t:Type) {| f: field t |} (roots: list t)
  : Lemma (ensures deg (poly_prod_linears roots) == L.length roots)
          (decreases roots)
  = match roots with
    | []        -> poly_one_deg #t #f ()
    | a :: rest ->
        let la = poly_linear a in
        let pr = poly_prod_linears rest in
        poly_linear_deg a;
        poly_prod_linears_deg rest;
        deg_mul la pr

(* ================================================================ *)
(*  TARGET LEMMA.                                                     *)
(*                                                                   *)
(*  Statement: vc divides a product of distinct linears; cset is     *)
(*  EXACTLY the elements of `roots` that are roots of vc (the iff).   *)
(*  Then deg vc = #cset.                                              *)
(* ================================================================ *)

(* ---------------------------------------------------------------- *)
(*  Helper: field bool-eq refines propositional ==.                  *)
(* ---------------------------------------------------------------- *)

let eq_of_propeq (#t:Type) {| f: field t |} (a b: t)
  : Lemma (requires a == b) (ensures (a = b))
  = H.elim_equatable_laws t ()

(* ---------------------------------------------------------------- *)
(*  Helper: for b <> a, (neg a + b) is nonzero in the field.         *)
(* ---------------------------------------------------------------- *)

let neg_a_plus_b_nonzero (#t:Type) {| f: field t |} (a b: t)
  : Lemma (requires not (b = a)) (ensures not (((- a) + b) = zero))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if ((- a) + b) = zero then begin
      (* neg a + b = zero = neg a + a, cancel left -> b = a, contradiction *)
      H.neg_x_plus_x a;                              (* neg a + a = zero *)
      H.group_cancel_left (- a) b a;               (* b = a *)
      assert False
    end

(* ---------------------------------------------------------------- *)
(*  Helper: remove one element from a distinct list, length drops 1. *)
(* ---------------------------------------------------------------- *)

let rec remove_one (#t:Type) {| f: field t |} (a: t) (l: list t)
  : Pure (list t)
         (requires L.memP a l /\ all_distinct l)
         (ensures fun r -> all_distinct r /\
                           L.length l == ((L.length r) ++ 1) /\
                           (forall (b:t). L.memP b r <==>
                              (L.memP b l /\ not (b = a))))
         (decreases l)
  = match l with
    | c :: cs ->
        if c = a then begin
          (* a == c ?  We know c = a (field eq). For membership of b in cs vs l:
             memP b cs ==> not (c = b) (from all_distinct), and not(c=b) with c=a
             gives not(b=a). *)
          let aux (b: t)
            : Lemma (L.memP b cs <==> (L.memP b l /\ not (b = a)))
            = H.elim_equatable_laws t ();
              H.trans_for_calc t ();
              introduce L.memP b cs ==> (L.memP b l /\ not (b = a))
              with _hb. begin
                (* from all_distinct (c::cs): not (c = b); c = a so not (a=b) so not(b=a) *)
                assert (not (c = b))
              end;
              introduce (L.memP b l /\ not (b = a)) ==> L.memP b cs
              with _hb. begin
                (* b in (c::cs): either b==c or b in cs. If b==c then b=c=a so b=a,
                   contradicting not(b=a). *)
                eliminate L.memP b cs \/ b == c
                returns L.memP b cs
                with hcs. hcs
                and  heq. begin
                  eq_of_propeq b c;                     (* b = c *)
                  assert False
                end
              end
          in
          FStar.Classical.forall_intro aux;
          cs
        end else begin
          (* a is in cs (since a in l = c::cs and c <> a means a==c is false-ish;
             but memP uses ==. We need memP a cs. *)
          (* From memP a l: a==c \/ memP a cs. If a==c then a=c=c by eq_of_propeq,
             contradicting not(c=a). So memP a cs. *)
          H.elim_equatable_laws t ();
          eliminate a == c \/ L.memP a cs
          returns L.memP a cs
          with heq. begin
            eq_of_propeq a c;                            (* a = c *)
            assert False
          end
          and hcs. hcs;
          let r = remove_one a cs in
          let aux2 (b: t)
            : Lemma (L.memP b (c :: r) <==> (L.memP b l /\ not (b = a)))
            = H.elim_equatable_laws t ();
              H.trans_for_calc t ();
              (* memP b (c::r) <==> b==c \/ memP b r
                 memP b l       <==> b==c \/ memP b cs *)
              introduce (b == c) ==> not (b = a)
              with _heq. begin
                eq_of_propeq b c                         (* b = c *)
                (* need not(b=a): c <> a (this branch), and b=c so b<>a *)
              end
          in
          FStar.Classical.forall_intro aux2;
          c :: r
        end

(* ---------------------------------------------------------------- *)
(*  Helper: evaluation of vc = la * vc' at b factors.                *)
(* ---------------------------------------------------------------- *)

let eval_factor (#t:Type) {| f: field t |} (a: t) (vc vcp: polynomial t) (b: t)
  : Lemma (requires vc = (poly_linear a * vcp))
          (ensures poly_eval vc b = (((- a) + b) * poly_eval vcp b))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let la = poly_linear a in
    eval_congruence vc (la * vcp) b;                 (* poly_eval vc b = poly_eval (la*vcp) b *)
    eval_mul la vcp b;                               (* poly_eval (la*vcp) b = ev la b * ev vcp b *)
    eval_linear a b;                                 (* poly_eval la b = neg a + b *)
    mul_congruence (poly_eval la b) (poly_eval vcp b) ((- a) + b) (poly_eval vcp b)

(* ---------------------------------------------------------------- *)
(*  Helper: every linear polynomial (x - a) is irreducible.          *)
(* ---------------------------------------------------------------- *)

let poly_linear_irreducible (#t:Type) {| f: field t |} (a: t)
  : Lemma (IR.poly_irreducible (poly_linear a))
  = let la = poly_linear a in
    poly_linear_deg a;                                (* deg la = Some 1 *)
    let aux (p q: polynomial t)
      : Lemma (requires (la = (p * q)))
              (ensures  (deg p == 0 \/ deg p < 0 \/
                         deg q == 0 \/ deg q < 0))
      = if deg p >= 0 && deg q >= 0 then begin
          deg_mul p q;                 (* deg(p*q) = deg p + deg q *)
          Core.Polynomial.Unique.degree_well_defined la (p * q); (* deg la = deg(p*q) = 1 *)
          ()
        end
    in
    Classical.forall_intro_2 (fun p q ->
      Classical.move_requires (aux p) q)

(* ---------------------------------------------------------------- *)
(*  Helper: a non-root of vc is coprime to (x - a).                  *)
(* ---------------------------------------------------------------- *)

let nonroot_coprime_linear (#t:Type) {| f: field t |} (vc: polynomial t) (a: t)
  : Lemma (requires deg vc >= 0 /\ poly_eval vc a <> zero)
          (ensures coprime vc (poly_linear a))
  = let la = poly_linear a in
    poly_linear_deg a;                                (* deg la = Some 1 *)
    poly_linear_irreducible a;                        (* la irreducible *)
    IR.irreducible_coprime_or_divides la vc;          (* coprime la vc \/ la | vc *)
    (* la | vc would give eval vc a = 0 by factor_theorem, contradiction. *)
    factor_theorem vc a;                              (* eval vc a = 0 <==> la | vc *)
    (* so ~(la | vc), hence coprime la vc; then symmetric. *)
    IR.coprime_symmetric la vc

(* ---------------------------------------------------------------- *)
(*  Base case: roots = [] forces cset = [].                          *)
(* ---------------------------------------------------------------- *)

let empty_cset_of_no_members (#t:Type) {| f: field t |} (cset: list t)
  : Lemma (requires (forall (b:t). ~ (L.memP b cset)))
          (ensures  cset == [])
  = match cset with
    | []      -> ()
    | c :: cs -> assert (L.memP c cset)   (* contradiction: c is a member *)

(* ---------------------------------------------------------------- *)
(*  Case A cancellation: vc | (la*pr), vc = la*vc'  ==>  vc' | pr.    *)
(* ---------------------------------------------------------------- *)

let cancel_divides (#t:Type) {| f: field t |}
  (a: t) (vc vcp pr: polynomial t)
  : Lemma (requires vc = (poly_linear a * vcp) /\
                     divides vc (poly_linear a * pr))
          (ensures  divides vcp pr)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let la = poly_linear a in
    poly_linear_deg a;                                        (* deg la = Some 1 *)
    eliminate exists (m: polynomial t). (la * pr) = (vc * m)
    returns divides vcp pr
    with hm. begin
      (* la*pr = vc*m = (la*vcp)*m = la*(vcp*m) *)
      mul_congruence vc m (la * vcp) m;                        (* vc*m = (la*vcp)*m *)
      mul_associativity la vcp m;                              (* (la*vcp)*m = la*(vcp*m) *)
      Core.Polynomial.Factorization.poly_mul_left_cancel la pr (vcp * m); (* pr = vcp*m *)
      divides_intro vcp pr m                                   (* needs eq pr (vcp*m) *)
    end

(* ---------------------------------------------------------------- *)
(*  The recursive iff transport for Case A: for b with not(b=a),     *)
(*  poly_eval vc b = 0 <==> poly_eval vc' b = 0  (vc = la*vc').       *)
(* ---------------------------------------------------------------- *)

let eval_root_transport (#t:Type) {| f: field t |}
  (a: t) (vc vcp: polynomial t) (b: t)
  : Lemma (requires vc = (poly_linear a * vcp) /\ not (b = a))
          (ensures  (poly_eval vc b = zero) <==>
                    (poly_eval vcp b = zero))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    eval_factor a vc vcp b;                        (* eval vc b = (neg a + b) * eval vcp b *)
    neg_a_plus_b_nonzero a b;                      (* (neg a + b) <> 0 *)
    let lhs = (- a) + b in
    let rhs = poly_eval vcp b in
    domain_law lhs rhs;                            (* (lhs*rhs = 0) <==> lhs=0 \/ rhs=0 *)
    (* combine: eval vc b = lhs*rhs and lhs <> 0 *)
    introduce (poly_eval vcp b = zero) ==> (poly_eval vc b = zero)
    with _h. begin
      H.x_mul_zero lhs;                            (* lhs * 0 = 0 *)
      mul_congruence lhs rhs lhs zero              (* lhs*rhs = lhs*0 *)
    end

(* ================================================================ *)
(*  TARGET LEMMA (recursive over roots).                             *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let rec divisor_split_count (#t:Type) {| f: field t |} (vc: polynomial t) (roots cset: list t)
  : Lemma (requires all_distinct roots /\ all_distinct cset /\ deg vc >= 0 /\
                    divides vc (poly_prod_linears roots) /\
                    (forall (b:t). L.memP b cset <==>
                       (L.memP b roots /\ poly_eval vc b = zero)))
          (ensures deg vc == L.length cset)
          (decreases roots)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match roots with
    | [] ->
        (* poly_prod_linears [] = poly_one ; vc | poly_one ; deg <= 0 ; deg = 0 *)
        poly_one_deg #t #f ();                         (* deg poly_one = Some 0 *)
        IR.divides_degree_le vc (poly_one #t);         (* deg vc <= 0 *)
        (* iff: memP b cset <==> (memP b [] /\ ...) = False *)
        empty_cset_of_no_members cset                  (* cset = [] *)

    | a :: rest ->
        let la = poly_linear a in
        let pr = poly_prod_linears rest in
        poly_linear_deg a;                             (* deg la = Some 1 *)
        (* poly_prod_linears (a::rest) = la * pr  (definitional) *)
        assert (poly_prod_linears roots == (la * pr));
        (* all_distinct (a::rest) facts *)
        assert (all_distinct rest);
        factor_theorem vc a;                           (* eval vc a = 0 <==> la | vc *)
        if (poly_eval vc a = zero) then begin
          (* CASE A: a is a root of vc *)
          (* extract quotient vc' : vc = la * vc' *)
          eliminate exists (vcp: polynomial t). vc = (la * vcp)
          returns deg vc == L.length cset
          with hvcp. begin
            (* degrees: deg vc' present, deg vc = 1 + deg vc' *)
            Core.Polynomial.Roots.mul_linear_nonzero_quotient a vc vcp; (* deg vcp >= 0 *)
            deg_mul la vcp;                             (* deg(la*vcp) = 1 + deg vcp *)
            Core.Polynomial.Unique.degree_well_defined vc (la * vcp); (* deg vc = deg(la*vcp) *)
            (* a in cset (it's a head root that is a root of vc) *)
            assert (L.memP a roots);
            assert (L.memP a cset);
            (* cset' = remove a *)
            let cset' = remove_one a cset in
            (* vc' | pr via cancellation *)
            cancel_divides a vc vcp pr;                 (* divides vcp pr *)
            (* recursive iff *)
            let iff_b (b: t)
              : Lemma (L.memP b cset' <==>
                       (L.memP b rest /\ poly_eval vcp b = zero))
              = H.elim_equatable_laws t ();
                if (b = a) then begin
                  (* both sides false *)
                  (* memP b cset' is false (remove_one excludes a) *)
                  (* memP b rest is false: a not in rest by all_distinct *)
                  introduce L.memP b rest ==> False
                  with _hb. begin
                    (* all_distinct (a::rest): memP b rest ==> not(a=b); but b=a so a=b *)
                    assert (not (a = b))
                  end
                end else begin
                  (* b <> a *)
                  eval_root_transport a vc vcp b         (* eval vc b = 0 <==> eval vcp b = 0 *)
                end
            in
            FStar.Classical.forall_intro iff_b;
            divisor_split_count vcp rest cset';          (* deg vcp = #cset' *)
            ()
          end
        end else begin
          (* CASE B: a is NOT a root of vc *)
          nonroot_coprime_linear vc a;                   (* coprime vc la *)
          (* bridge: divides vc (pr * la) from divides vc (la * pr) *)
          mul_commutativity la pr;                       (* la*pr = pr*la *)
          divides_congruence_right vc (la * pr) (pr * la);
          euclid_lemma vc la pr;                         (* divides vc pr *)
          (* recursive iff: SAME cset *)
          let iff_b (b: t)
            : Lemma (L.memP b cset <==>
                     (L.memP b rest /\ poly_eval vc b = zero))
            = H.elim_equatable_laws t ();
              if (b = a) then begin
                (* b = a (field eq): both sides false. *)
                introduce L.memP b rest ==> False
                with _hb. begin
                  assert (not (a = b))
                end;
                (* memP b cset ==> memP b roots /\ eval vc b = 0.
                   memP b roots = (b==a \/ memP b rest); memP b rest impossible,
                   so b==a, giving eval vc b == eval vc a <> 0. *)
                introduce L.memP b cset ==> False
                with _hb. begin
                  eliminate b == a \/ L.memP b rest
                  returns False
                  with heq. ()                           (* eval vc b == eval vc a <> 0 *)
                  and  hmem. begin
                    assert (not (a = b))
                  end
                end
              end else begin
                (* b <> a (field eq): not(b==a) so memP b roots <==> memP b rest *)
                introduce b == a ==> False
                with heq. (eq_of_propeq b a)
              end
          in
          FStar.Classical.forall_intro iff_b;
          divisor_split_count vc rest cset;              (* deg vc = #cset *)
          ()
        end
#pop-options
