module Core.Factor.BerlekampLoop

(* ================================================================ *)
(*  C5 · PIECE 2 — whole-loop soundness completion for              *)
(*  berlekamp_factor.                                                *)
(*                                                                   *)
(*  PRODUCT:  poly_prod (berlekamp_factor p fbar)  is an associate   *)
(*  of  fbar  (mutual divisibility).  Composed from the single-step  *)
(*  refine1_product across the concatMap / fold_left by an           *)
(*  append-multiplicativity of poly_prod.                            *)
(*                                                                   *)
(*  PAIRWISE-COPRIME:  for a SQUARE-FREE fbar the output factors are  *)
(*  pairwise coprime — a shared irreducible q would give q^2 | fbar.  *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module H   = Core.Algebra.Helpers
module IR  = Core.Polynomial.Irreducible
module PR  = Core.Polynomial.Roots
module SF  = Core.Polynomial.SquareFree
module CM  = Core.Algebra.CongruenceMod
module BC  = Core.Modular.PrimeField.BerlekampComplete
module BF  = Core.Factor.BerlekampFactor
module BC2 = Core.Factor.BerlekampComplete2
module SP  = Core.Polynomial.SubsetProd
module EU  = Core.NumberTheory

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.GCD
open Core.Modular.PrimeField

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  A.  GENERIC helpers (over any field).                            *)
(* ================================================================ *)

(* poly_prod is multiplicative over append. *)
let rec poly_prod_append (#t:Type) {| f: field t |}
  (l1 l2: list (polynomial t))
  : Lemma (ensures (PR.poly_prod (L.append l1 l2))
                   = (PR.poly_prod l1 * PR.poly_prod l2))
          (decreases l1)
  = H.elim_equatable_laws (polynomial t) ();
    match l1 with
    | [] ->
        (* poly_prod l2 = poly_one * poly_prod l2 *)
        mul_commutativity (poly_one #t) (PR.poly_prod l2);
        poly_mul_one (PR.poly_prod l2);
        poly_eq_transitivity (poly_one #t * PR.poly_prod l2)
                             (PR.poly_prod l2 * poly_one #t) (PR.poly_prod l2);
        poly_eq_symmetry (poly_one #t * PR.poly_prod l2) (PR.poly_prod l2)
    | a :: rest ->
        poly_prod_append rest l2;                    (* prod(rest@l2) = prod rest * prod l2 *)
        let pr = PR.poly_prod rest in
        let pl = PR.poly_prod l2 in
        mul_congruence a (PR.poly_prod (L.append rest l2)) a (pr * pl);
        mul_associativity a pr pl;                   (* (a*pr)*pl = a*(pr*pl) *)
        poly_eq_symmetry ((a * pr) * pl) (a * (pr * pl));
        poly_eq_transitivity (PR.poly_prod (L.append (a :: rest) l2))
                             (a * (pr * pl)) ((a * pr) * pl)

(* associate is preserved by multiplication (both directions). *)
let mul_associate_both (#t:Type) {| f: field t |}
  (a a' b b': polynomial t)
  : Lemma (requires divides a a' /\ divides a' a /\ divides b b' /\ divides b' b)
          (ensures  divides (a * b) (a' * b') /\ divides (a' * b') (a * b))
  = H.elim_equatable_laws (polynomial t) ();
    (* forward:  a*b | a'*b | a'*b' *)
    IR.divides_mul_both_sides a a' b;                (* divides (b*a)(b*a') *)
    mul_commutativity b a;  mul_commutativity b a';
    divides_congruence_left  (b * a)  (a * b)  (b * a');
    divides_congruence_right (a * b)  (b * a') (a' * b);
    IR.divides_mul_both_sides b b' a';               (* divides (a'*b)(a'*b') *)
    divides_trans (a * b) (a' * b) (a' * b');
    (* backward:  a'*b' | a*b' | a*b *)
    IR.divides_mul_both_sides a' a b';               (* divides (b'*a')(b'*a) *)
    mul_commutativity b' a';  mul_commutativity b' a;
    divides_congruence_left  (b' * a') (a' * b') (b' * a);
    divides_congruence_right (a' * b') (b' * a) (a * b');
    IR.divides_mul_both_sides b' b a;                (* divides (a*b')(a*b) *)
    divides_trans (a' * b') (a * b') (a * b)

(* the product of two DISTINCT-index list elements divides the product. *)
let rec prod_pair_divides (#t:Type) {| f: field t |}
  (fs: list (polynomial t)) (i j:nat)
  : Lemma (requires i < L.length fs /\ j < L.length fs /\ i <> j)
          (ensures  divides #(polynomial t)
                       ((L.index fs i) * (L.index fs j)) (PR.poly_prod fs))
          (decreases fs)
  = H.elim_equatable_laws (polynomial t) ();
    match fs with
    | a :: rest ->
        (* poly_prod (a::rest) == a * poly_prod rest *)
        if i = 0 then begin
          (* fs_i == a ; fs_j == rest_{j-1} ; rest_{j-1} | poly_prod rest *)
          BC.poly_prod_index_divides rest (j - 1);
          IR.divides_mul_both_sides (L.index rest (j - 1)) (PR.poly_prod rest) a;
          (* divides (a*rest_{j-1})(a*poly_prod rest) = (a*fs_j)(poly_prod fs) *)
          ()
        end else if j = 0 then begin
          (* fs_j == a ; fs_i == rest_{i-1} *)
          BC.poly_prod_index_divides rest (i - 1);
          IR.divides_mul_both_sides (L.index rest (i - 1)) (PR.poly_prod rest) a;
          (* divides (a*rest_{i-1})(a*poly_prod rest) ; commute to fs_i*fs_j *)
          mul_commutativity a (L.index rest (i - 1));
          mul_commutativity a (PR.poly_prod rest);
          divides_congruence_left  (a * L.index rest (i - 1))
                                   (L.index rest (i - 1) * a) (a * PR.poly_prod rest);
          divides_congruence_right (L.index rest (i - 1) * a)
                                   (a * PR.poly_prod rest) (PR.poly_prod rest * a)
        end else begin
          (* both in rest : recurse, then multiply by a on the left *)
          prod_pair_divides rest (i - 1) (j - 1);      (* fs_i*fs_j | poly_prod rest *)
          divides_mul_left #(polynomial t)
            ((L.index rest (i - 1)) * (L.index rest (j - 1))) a (PR.poly_prod rest)
        end
    | [] -> ()

(* ================================================================ *)
(*  B.  cong transports to divisors of the modulus.                  *)
(* ================================================================ *)

let cong_transport (p:int{EU.is_prime p}) (fbar g h: polynomial (fp p))
  : Lemma (requires divides #(polynomial (fp p)) g fbar /\
                    CM.cong #(polynomial (fp p)) fbar (poly_power h (p <: nat)) h)
          (ensures  CM.cong #(polynomial (fp p)) g (poly_power h (p <: nat)) h)
  = CM.cong_reveal #(polynomial (fp p)) fbar (poly_power h (p <: nat)) h;
    divides_trans #(polynomial (fp p)) g fbar
      ((poly_power h (p <: nat)) + (- h));
    CM.cong_reveal #(polynomial (fp p)) g (poly_power h (p <: nat)) h

(* ================================================================ *)
(*  C.  one refinement step preserves the product (up to associate). *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec refine_list_product (p:int{EU.is_prime p})
  (fbar h: polynomial (fp p)) (gs: list (polynomial (fp p)))
  : Lemma (requires (forall (d: polynomial (fp p)). L.memP d gs ==>
                       deg d >= 1 /\ divides #(polynomial (fp p)) d fbar) /\
                    CM.cong #(polynomial (fp p)) fbar (poly_power h (p <: nat)) h)
          (ensures  divides #(polynomial (fp p))
                       (PR.poly_prod (BF.refine_list p h gs)) (PR.poly_prod gs) /\
                    divides #(polynomial (fp p))
                       (PR.poly_prod gs) (PR.poly_prod (BF.refine_list p h gs)))
          (decreases gs)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    match gs with
    | [] -> divides_refl #(polynomial (fp p)) (poly_one #(fp p))
    | g :: rest ->
        let x  = BF.refine1 p h g in
        let xs = BF.refine_list p h rest in
        (* refine_list p h (g::rest) == refine1 p h g @ refine_list p h rest *)
        assert (BF.refine_list p h (g :: rest) == L.append x xs);
        poly_prod_append x xs;                       (* poly_prod(x@xs) = a * ar *)
        let a  = PR.poly_prod x in
        let ar = PR.poly_prod xs in
        assert (PR.poly_prod (BF.refine_list p h (g :: rest)) = (a * ar));
        assert (PR.poly_prod (g :: rest) == (g * PR.poly_prod rest));
        (* single-step: poly_prod (refine1 p h g) ~ g ;  IH: poly_prod xs ~ poly_prod rest *)
        cong_transport p fbar g h;                   (* cong g (h^p) h *)
        BF.refine1_product p h g;                    (* divides g a /\ divides a g *)
        refine_list_product p fbar h rest;           (* divides ar (∏rest) /\ reverse *)
        mul_associate_both a g ar (PR.poly_prod rest);
        (* a*ar ~ g*∏rest == ∏(g::rest) ;  swap divisor to ∏(refine_list(g::rest)) *)
        divides_congruence_left  (a * ar)
          (PR.poly_prod (BF.refine_list p h (g :: rest))) (PR.poly_prod (g :: rest));
        divides_congruence_right (PR.poly_prod (g :: rest))
          (a * ar) (PR.poly_prod (BF.refine_list p h (g :: rest)))
#pop-options

(* ================================================================ *)
(*  D.  the fold preserves the product invariant.                    *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec fold_refine_product (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  (gs ks: list (polynomial (fp p)))
  : Lemma (requires (forall (d: polynomial (fp p)). L.memP d gs ==>
                       deg d >= 1 /\ divides #(polynomial (fp p)) d fbar) /\
                    (forall (h: polynomial (fp p)). L.memP h ks ==>
                       CM.cong #(polynomial (fp p)) fbar (poly_power h (p <: nat)) h) /\
                    divides #(polynomial (fp p)) (PR.poly_prod gs) fbar /\
                    divides #(polynomial (fp p)) fbar (PR.poly_prod gs))
          (ensures  divides #(polynomial (fp p))
                       (PR.poly_prod (L.fold_left (BF.refine_step p) gs ks)) fbar /\
                    divides #(polynomial (fp p)) fbar
                       (PR.poly_prod (L.fold_left (BF.refine_step p) gs ks)))
          (decreases ks)
  = match ks with
    | [] -> ()
    | h :: rest ->
        let gs' = BF.refine_step p gs h in           (* == refine_list p h gs *)
        (* product preserved by this step *)
        refine_list_product p fbar h gs;
        divides_trans #(polynomial (fp p)) (PR.poly_prod gs') (PR.poly_prod gs) fbar;
        divides_trans #(polynomial (fp p)) fbar (PR.poly_prod gs) (PR.poly_prod gs');
        (* invariant "deg>=1 /\ divides fbar" preserved *)
        BF.refine_list_preserves p fbar h gs;
        fold_refine_product p fbar gs' rest
#pop-options

(* ================================================================ *)
(*  E.  PIECE 2a — the PRODUCT theorem.                              *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let berlekamp_factor_product (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1})
  : Lemma (divides #(polynomial (fp p)) (PR.poly_prod (BF.berlekamp_factor p fbar)) fbar /\
           divides #(polynomial (fp p)) fbar (PR.poly_prod (BF.berlekamp_factor p fbar)))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    (* base list [fbar] : deg fbar >= 1, fbar | fbar *)
    let base_pf (d: polynomial (fp p))
      : Lemma (requires L.memP d [fbar])
              (ensures  deg d >= 1 /\ divides #(polynomial (fp p)) d fbar)
      = assert (d == fbar);
        divides_refl #(polynomial (fp p)) fbar
    in
    Classical.forall_intro (Classical.move_requires base_pf);
    (* every kernel element is certified for fbar *)
    let ker_pf (h: polynomial (fp p))
      : Lemma (requires L.memP h (BF.berlekamp_kernel p fbar))
              (ensures  CM.cong #(polynomial (fp p)) fbar (poly_power h (p <: nat)) h)
      = BF.berlekamp_kernel_certified p fbar h
    in
    Classical.forall_intro (Classical.move_requires ker_pf);
    (* poly_prod [fbar] == fbar * poly_one = fbar *)
    poly_mul_one fbar;                               (* fbar * poly_one = fbar *)
    divides_refl #(polynomial (fp p)) fbar;
    divides_congruence_left  fbar (PR.poly_prod [fbar]) fbar;
    divides_congruence_right fbar fbar (PR.poly_prod [fbar]);
    fold_refine_product p fbar [fbar] (BF.berlekamp_kernel p fbar)
#pop-options

(* ================================================================ *)
(*  F.  PIECE 2b — PAIRWISE COPRIMALITY  (via square-freeness).      *)
(* ================================================================ *)

let irr_deg1 (#t:Type) {| f: field t |} (q: polynomial t)
  : Lemma (requires IR.poly_irreducible q) (ensures deg q >= 1) = ()

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let berlekamp_factor_pairwise_coprime (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1})
  : Lemma (requires SF.square_free fbar)
          (ensures  IR.pairwise_coprime (BF.berlekamp_factor p fbar))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let fs = BF.berlekamp_factor p fbar in
    berlekamp_factor_product p fbar;                 (* divides (poly_prod fs) fbar *)
    let ppc (i:nat{i < L.length fs}) (j:nat{j < L.length fs /\ j <> i})
      : Lemma (coprime #(fp p) (L.index fs i) (L.index fs j))
      = let gi = L.index fs i in
        let gj = L.index fs j in
        L.lemma_index_memP fs i; L.lemma_index_memP fs j;
        BF.berlekamp_factor_sound p fbar gi;         (* deg gi >= 1 *)
        BF.berlekamp_factor_sound p fbar gj;         (* deg gj >= 1 *)
        coprime_reveal gi gj;                         (* coprime <=> deg gcd == 0 *)
        SF.gcd_has_degree gi gj;                       (* deg (poly_gcd gi gj) >= 0 *)
        let g = poly_gcd gi gj in
        if deg g = 0 then ()
        else begin
          (* deg g >= 1 : an irreducible q | g divides BOTH gi and gj ⟹ q^2 | fbar *)
          IR.irreducible_factor_exists g;
          eliminate exists (q: polynomial (fp p)). IR.poly_irreducible q /\ divides q g
          returns coprime #(fp p) gi gj
          with _.
          begin
            irr_deg1 q;
            gcd_divides_left gi gj;  gcd_divides_right gi gj;
            divides_trans #(polynomial (fp p)) q g gi;   (* q | gi *)
            divides_trans #(polynomial (fp p)) q g gj;   (* q | gj *)
            (* q*q | gi*gj *)
            IR.divides_mul_both_sides q gi q;            (* divides (q*q)(q*gi) *)
            mul_commutativity q gi;
            divides_congruence_right #(polynomial (fp p)) (q * q) (q * gi) (gi * q);
            IR.divides_mul_both_sides q gj gi;           (* divides (gi*q)(gi*gj) *)
            divides_trans #(polynomial (fp p)) (q * q) (gi * q) (gi * gj);
            (* gi*gj | poly_prod fs | fbar *)
            prod_pair_divides fs i j;
            divides_trans #(polynomial (fp p)) (q * q) (gi * gj) (PR.poly_prod fs);
            divides_trans #(polynomial (fp p)) (q * q) (PR.poly_prod fs) fbar;
            (* poly_power q 2 = q*q | fbar : contradicts square_free *)
            BC.poly_power_two q;
            poly_eq_symmetry (poly_power q 2) (q * q);
            divides_congruence_left #(polynomial (fp p)) (q * q) (poly_power q 2) fbar;
            IR.not_square_free_of_repeated_factor q fbar 2
          end
        end
    in
    IR.pairwise_coprime_intro fs ppc

(* ================================================================ *)
(*  G.  FINAL COMPLETENESS  (conditional on reaches-r).             *)
(*                                                                   *)
(*  Given the r-element irreducible factorization  irs  of a         *)
(*  square-free  fbar,  and the reaches-r fact                       *)
(*     |berlekamp_factor p fbar| == |irs|,                           *)
(*  the pigeonhole (PIECE 1) forces EVERY output factor to be        *)
(*  irreducible.  PIECE 2 discharges the pairwise-coprimality and    *)
(*  product hypotheses; berlekamp_factor_sound the degree bound.     *)
(*                                                                   *)
(*  The reaches-r hypothesis  |berlekamp_factor p fbar| == |irs|     *)
(*  is the SOLE remaining residual (R2, algorithmic); irs itself is  *)
(*  supplied unconditionally by BerlekampComplete.berlekamp_complete.*)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let berlekamp_factor_complete (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1}) (irs: list (polynomial (fp p)))
  : Lemma (requires SF.square_free fbar /\
                    SP.all_irreducible irs /\
                    (PR.poly_prod irs = fbar) /\
                    L.length (BF.berlekamp_factor p fbar) == L.length irs)
          (ensures  SP.all_irreducible (BF.berlekamp_factor p fbar))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let fs = BF.berlekamp_factor p fbar in
    (* pairwise coprime (PIECE 2b) *)
    berlekamp_factor_pairwise_coprime p fbar;
    (* every factor has degree >= 1 (soundness) *)
    let deg_pf (i:nat) : Lemma (i < L.length fs ==> deg (L.index fs i) >= 1)
      = if i < L.length fs then begin
          L.lemma_index_memP fs i;
          BF.berlekamp_factor_sound p fbar (L.index fs i)
        end
    in
    Classical.forall_intro deg_pf;
    (* divides (poly_prod fs) (poly_prod irs) : product ~ fbar == poly_prod irs *)
    berlekamp_factor_product p fbar;                 (* divides (poly_prod fs) fbar *)
    divides_congruence_right #(polynomial (fp p))
      (PR.poly_prod fs) fbar (PR.poly_prod irs);     (* divides (poly_prod fs)(poly_prod irs) *)
    BC2.pigeonhole_all_irreducible fs irs
#pop-options
