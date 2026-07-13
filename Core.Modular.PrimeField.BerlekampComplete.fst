(* ================================================================ *)
(*  Berlekamp COMPLETENESS certificate.                              *)
(*                                                                   *)
(*  For a square-free polynomial d of degree >= 1 over ANY field    *)
(*  there exists a COMPLETE factorization into irreducible,          *)
(*  pairwise-coprime factors whose product is d.  Proved            *)
(*  GENERICALLY over {| field t |} (hence at fp p and anywhere).    *)
(*                                                                   *)
(*  This discharges the all_irreducible / pairwise_coprime /         *)
(*  product hypotheses of                                            *)
(*  Core.Modular.FpZmodBridge.recombination_complete_fp.            *)
(*                                                                   *)
(*  NO admit / assume / sorry.  Lemma / ghost / Tot only.           *)
(* ================================================================ *)

module Core.Modular.PrimeField.BerlekampComplete

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module IR = Core.Polynomial.Irreducible
module SP = Core.Polynomial.SubsetProd
module PR = Core.Polynomial.Roots
module SF = Core.Polynomial.SquareFree
module LP = Core.Polynomial.LinearPeel
module ID = FStar.IndefiniteDescription
module EU = Core.NumberTheory
module FA = Core.Polynomial.Factorization
module BD  = Core.Modular.PrimeField.BerlekampDim
module BDC = Core.Modular.PrimeField.BerlekampDimCount

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.GCD
open Core.Polynomial.SquareFree
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.Monic
open Core.Modular.PrimeField

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  A list element divides the product of the list.                 *)
(* ================================================================ *)

let rec poly_prod_index_divides (#t:Type) {| f: field t |}
  (fs: list (polynomial t)) (k: nat)
  : Lemma (requires k < L.length fs)
          (ensures  divides (L.index fs k) (PR.poly_prod fs))
          (decreases fs)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match fs with
    | a :: rest ->
      if k = 0 then
        (* PR.poly_prod (a::rest) == a * PR.poly_prod rest ; witness = product of rest *)
        divides_intro a (a * (PR.poly_prod rest)) (PR.poly_prod rest)
      else begin
        let elem = L.index rest (k - 1) in
        poly_prod_index_divides rest (k - 1);           (* elem | poly_prod rest *)
        let aux (c: polynomial t)
          : Lemma (requires ((PR.poly_prod rest) = (elem * c)))
                  (ensures  divides elem (a * (PR.poly_prod rest)))
          = poly_mul_right_congruence a (PR.poly_prod rest) (elem * c);
            mul_associativity a elem c;
            mul_commutativity a elem;
            poly_mul_left_congruence (a * elem) (elem * a) c;
            poly_eq_transitivity (a * (PR.poly_prod rest))
                                 (a * (elem * c)) ((a * elem) * c);
            poly_eq_transitivity (a * (PR.poly_prod rest))
                                 ((a * elem) * c) ((elem * a) * c);
            mul_associativity elem a c;
            poly_eq_transitivity (a * (PR.poly_prod rest))
                                 ((elem * a) * c) (elem * (a * c));
            divides_intro elem (a * (PR.poly_prod rest)) (a * c)
        in
        Classical.forall_intro (Classical.move_requires aux)
      end

(* ================================================================ *)
(*  A non-zero-constant multiple of an irreducible is irreducible.  *)
(*  (associate of irreducible is irreducible; char-free, no field    *)
(*  inverse — uses Euclid + left cancellation).                     *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let irreducible_associate (#t:Type) {| f: field t |}
  (q c d: polynomial t)
  : Lemma (requires IR.poly_irreducible q /\ deg c == 0 /\ (d = (q * c)))
          (ensures  IR.poly_irreducible d)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* deg d == deg q + 0 == deg q >= 1 *)
    degree_mul q c;
    degree_well_defined d (q * c);
    (* the factorization clause *)
    let clause (a b: polynomial t)
      : Lemma (requires (d = (a * b)) == true)
              (ensures  (deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0))
      = (* q * c = d = a * b, so q | a*b *)
        poly_eq_symmetry d (a * b);
        poly_eq_transitivity (q * c) d (a * b);         (* q*c poly_eq a*b *)
        divides_intro q (q * c) c;                       (* q | q*c *)
        divides_congruence_right q (q * c) (a * b);      (* q | a*b *)
        (* a and b are non-zero: a*b poly_eq d, deg d >= 1 *)
        let anz () : Lemma (requires deg a < 0) (ensures False)
          = degree_none_poly_eq_zero a;
            poly_mul_left_congruence a (poly_zero #t) b;
            H.zero_mul_x b;
            poly_eq_transitivity (a * b) ((poly_zero #t) * b) (poly_zero #t);
            poly_eq_symmetry (a * b) (poly_zero #t);
            poly_eq_transitivity (q * c) (a * b) (poly_zero #t);
            poly_eq_symmetry (q * c) d;
            poly_eq_transitivity d (q * c) (poly_zero #t);
            degree_well_defined d (poly_zero #t)
        in
        Classical.move_requires anz ();
        let bnz () : Lemma (requires deg b < 0) (ensures False)
          = degree_none_poly_eq_zero b;
            poly_mul_right_congruence a b (poly_zero #t);
            H.x_mul_zero a;
            poly_eq_transitivity (a * b) (a * (poly_zero #t)) (poly_zero #t);
            poly_eq_symmetry (a * b) (poly_zero #t);
            poly_eq_transitivity (q * c) (a * b) (poly_zero #t);
            poly_eq_symmetry (q * c) d;
            poly_eq_transitivity d (q * c) (poly_zero #t);
            degree_well_defined d (poly_zero #t)
        in
        Classical.move_requires bnz ();
        (* deg a >= 0 /\ deg b >= 0 now hold; use Euclid on q | a*b *)
        IR.irreducible_coprime_or_divides q a;           (* coprime q a \/ q | a *)
        (* Case q | a: a poly_eq q*a'; cancel q from q*c = a*b = q*(a'*b) *)
        let via_a (a': polynomial t)
          : Lemma (requires (a = (q * a')))
                  (ensures  deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0)
          = poly_mul_left_congruence a (q * a') b;         (* a*b poly_eq (q*a')*b *)
            mul_associativity q a' b;                      (* (q*a')*b poly_eq q*(a'*b) *)
            poly_eq_transitivity (a * b) ((q * a') * b) (q * (a' * b));
            poly_eq_symmetry (a * b) (q * (a' * b));
            poly_eq_transitivity (q * c) (a * b) (q * (a' * b));  (* q*c poly_eq q*(a'*b) *)
            FA.poly_mul_left_cancel q c (a' * b);             (* c poly_eq a'*b *)
            (* deg (a'*b) == deg c == 0 ; if a', b nonzero then deg a' + deg b == 0 *)
            degree_well_defined c (a' * b);
            if deg a' >= 0 && deg b >= 0 then degree_mul a' b else ()
        in
        let via_qa () : Lemma (requires divides q a)
                              (ensures deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0)
          = eliminate exists (a': polynomial t). (a = (q * a'))
            returns deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0
            with _. via_a a'
        in
        (* Case coprime q a: Euclid gives q | b, cancel to bound deg a *)
        let via_cop () : Lemma (requires (coprime q a) == true)
                               (ensures deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0)
          = mul_commutativity a b;                          (* a*b poly_eq b*a *)
            divides_congruence_right q (a * b) (b * a);      (* q | b*a *)
            euclid_lemma q a b;                           (* q | b *)
            let via_b (b': polynomial t)
              : Lemma (requires (b = (q * b')))
                      (ensures  deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0)
              = poly_mul_right_congruence a b (q * b');       (* a*b poly_eq a*(q*b') *)
                mul_commutativity a (q * b');                 (* a*(q*b') poly_eq (q*b')*a *)
                mul_associativity q b' a;                     (* (q*b')*a poly_eq q*(b'*a) *)
                poly_eq_transitivity (a * b) (a * (q * b')) ((q * b') * a);
                poly_eq_transitivity (a * b) ((q * b') * a) (q * (b' * a));
                poly_eq_symmetry (a * b) (q * (b' * a));
                poly_eq_transitivity (q * c) (a * b) (q * (b' * a));  (* q*c poly_eq q*(b'*a) *)
                FA.poly_mul_left_cancel q c (b' * a);            (* c poly_eq b'*a *)
                degree_well_defined c (b' * a);
                if deg b' >= 0 && deg a >= 0 then degree_mul b' a else ()
            in
            eliminate exists (b': polynomial t). (b = (q * b'))
            returns deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0
            with _. via_b b'
        in
        Classical.move_requires via_qa ();
        Classical.move_requires via_cop ()
    in
    Classical.forall_intro_2 (Classical.move_requires_2 clause);
    assert (IR.poly_irreducible d)
#pop-options

(* q^2 poly_eq q*q  (poly_power unfolds to q*(q*poly_one)). *)
#push-options "--fuel 4 --ifuel 1 --z3rlimit 40"
let poly_power_two (#t:Type) {| f: field t |} (q: polynomial t)
  : Lemma ((poly_power q 2) = (q * q))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    assert (poly_power q 2 == (q * (q * (poly_one #t))));
    poly_mul_one q;                                        (* q*poly_one poly_eq q *)
    poly_mul_right_congruence q (q * (poly_one #t)) q      (* q*(q*poly_one) poly_eq q*q *)
#pop-options

(* ================================================================ *)
(*  Cons-structural bridges for the two opaque list predicates.     *)
(* ================================================================ *)

let all_irreducible_cons (#t:Type) {| f: field t |}
  (q: polynomial t) (fs': list (polynomial t))
  : Lemma (requires IR.poly_irreducible q /\ SP.all_irreducible fs')
          (ensures  SP.all_irreducible (q :: fs'))
  = let fs = q :: fs' in
    SP.all_irreducible_elim fs';
    let pir (h: polynomial t{L.memP h fs}) : Lemma (IR.poly_irreducible h)
      = assert (h == q \/ L.memP h fs')
    in
    SP.all_irreducible_intro fs pir

let pairwise_coprime_cons (#t:Type) {| f: field t |}
  (q: polynomial t) (fs': list (polynomial t))
  (hq: (k:nat{k < L.length fs'}) -> Lemma (coprime q (L.index fs' k)))
  (hdeg: (k:nat{k < L.length fs'}) -> Lemma (deg (L.index fs' k) >= 0))
  : Lemma (requires IR.pairwise_coprime fs' /\ deg q >= 0)
          (ensures  IR.pairwise_coprime (q :: fs'))
  = let fs = q :: fs' in
    IR.pairwise_coprime_elim fs';
    let ppc (i:nat{i < L.length fs}) (j:nat{j < L.length fs /\ j <> i})
      : Lemma (coprime (L.index fs i) (L.index fs j))
      = assert (L.length fs == L.length fs' ++ 1);
        if i = 0 then begin
          let jm : nat = j - 1 in
          assert (L.index fs i == q);
          assert (L.index fs j == L.index fs' jm);
          hq jm; hdeg jm;
          IR.coprime_symmetric q (L.index fs' jm);
          IR.coprime_symmetric (L.index fs' jm) q
        end
        else if j = 0 then begin
          let im : nat = i - 1 in
          assert (L.index fs j == q);
          assert (L.index fs i == L.index fs' im);
          hq im; hdeg im;
          IR.coprime_symmetric q (L.index fs' im)
        end
        else begin
          assert (L.index fs i == L.index fs' (i - 1));
          assert (L.index fs j == L.index fs' (j - 1))
        end
    in
    IR.pairwise_coprime_intro fs ppc

(* ================================================================ *)
(*  Base + step certificate builders (isolated small VCs).          *)
(* ================================================================ *)

(* an irreducible d is its own complete factorization  [d]. *)
let singleton_cert (#t:Type) {| f: field t |} (d: polynomial t)
  : Lemma (requires IR.poly_irreducible d)
          (ensures  exists (gs: list (polynomial t)).
                       Cons? gs /\ (PR.poly_prod gs = d) /\
                       SP.all_irreducible gs /\ IR.pairwise_coprime gs)
  = H.elim_equatable_laws (polynomial t) ();
    let fs : list (polynomial t) = [d] in
    poly_mul_one d;                                        (* poly_prod [d] = d*poly_one = d *)
    let pir (h: polynomial t{L.memP h fs}) : Lemma (IR.poly_irreducible h)
      = assert (h == d) in
    SP.all_irreducible_intro fs pir;
    let ppc (i:nat{i < L.length fs}) (j:nat{j < L.length fs /\ j <> i})
      : Lemma (coprime (L.index fs i) (L.index fs j))
      = assert (L.length fs == 1) in
    IR.pairwise_coprime_intro fs ppc;
    introduce exists (gs: list (polynomial t)).
                Cons? gs /\ (PR.poly_prod gs = d) /\
                SP.all_irreducible gs /\ IR.pairwise_coprime gs
    with fs and ()

(* prepend an irreducible factor coprime to the (complete) cofactor. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let cons_cert (#t:Type) {| f: field t |}
  (q cof d: polynomial t) (fs': list (polynomial t))
  : Lemma (requires IR.poly_irreducible q /\ deg cof >= 1 /\
                    (coprime q cof) /\ (d = (q * cof)) /\
                    Cons? fs' /\ (PR.poly_prod fs' = cof) /\
                    SP.all_irreducible fs' /\ IR.pairwise_coprime fs')
          (ensures  exists (gs: list (polynomial t)).
                       Cons? gs /\ (PR.poly_prod gs = d) /\
                       SP.all_irreducible gs /\ IR.pairwise_coprime gs)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let fs : list (polynomial t) = q :: fs' in
    (* product: poly_prod (q::fs') = q * poly_prod fs' poly_eq q*cof poly_eq d *)
    assert (PR.poly_prod fs == (q * (PR.poly_prod fs')));
    poly_mul_right_congruence q (PR.poly_prod fs') cof;
    poly_eq_symmetry (q * cof) d;
    poly_eq_transitivity (q * (PR.poly_prod fs')) (q * cof) d;
    (* all_irreducible (q::fs') *)
    all_irreducible_cons q fs';
    (* pairwise_coprime (q::fs') : q coprime to every factor (each divides cof) *)
    let hdeg (k:nat{k < L.length fs'}) : Lemma (deg (L.index fs' k) >= 0)
      = poly_prod_index_divides fs' k;
        divides_congruence_right (L.index fs' k) (PR.poly_prod fs') cof;
        SP.divisor_nonzero (L.index fs' k) cof
    in
    let hq (k:nat{k < L.length fs'}) : Lemma (coprime q (L.index fs' k))
      = poly_prod_index_divides fs' k;
        divides_congruence_right (L.index fs' k) (PR.poly_prod fs') cof;
        SP.divisor_nonzero (L.index fs' k) cof;
        IR.coprime_symmetric q cof;                        (* coprime cof q *)
        IR.coprime_divisor cof q (L.index fs' k);          (* coprime (index) q *)
        IR.coprime_symmetric (L.index fs' k) q             (* coprime q (index) *)
    in
    pairwise_coprime_cons q fs' hq hdeg;
    introduce exists (gs: list (polynomial t)).
                Cons? gs /\ (PR.poly_prod gs = d) /\
                SP.all_irreducible gs /\ IR.pairwise_coprime gs
    with fs and ()
#pop-options

(* ================================================================ *)
(*  MAIN existence certificate (generic over {| field t |}).        *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let rec complete_factorization_exists (#t:Type) {| f: field t |}
  (d: polynomial t)
  : Lemma (requires deg d >= 1 /\ SF.square_free d)
          (ensures  exists (fs: list (polynomial t)).
                       Cons? fs /\
                       (PR.poly_prod fs = d) /\
                       SP.all_irreducible fs /\
                       IR.pairwise_coprime fs)
          (decreases (if deg d >= 0 then deg d else 0))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* 1. get an irreducible factor q | d *)
    IR.irreducible_factor_exists d;
    let q : polynomial t =
      ID.indefinite_description_ghost (polynomial t)
        (fun q -> IR.poly_irreducible q /\ divides q d) in
    assert (IR.poly_irreducible q /\ divides q d);
    IR.divides_degree_le q d;                            (* deg q <= deg d *)
    (* 2. cofactor *)
    let cof = poly_div d q in
    poly_div_correct d q;                                (* q*cof = d *)
    IR.poly_div_degree d q;                              (* deg cof == deg d - deg q >= 0 *)
    poly_eq_symmetry (q * cof) d;                        (* d poly_eq q*cof *)
    (* 3. coprime q cof (else q^2 | d contradicts square_free) *)
    IR.irreducible_coprime_or_divides q cof;
    let refute () : Lemma (requires divides q cof) (ensures False)
      = eliminate exists (s: polynomial t). (cof = (q * s))
        returns False
        with _.
        begin
          poly_mul_right_congruence q cof (q * s);          (* q*cof poly_eq q*(q*s) *)
          mul_associativity q q s;                          (* q*(q*s) poly_eq (q*q)*s *)
          poly_eq_transitivity (q * cof) (q * (q * s)) ((q * q) * s);
          poly_power_two q;                                 (* q^2 poly_eq q*q *)
          poly_mul_left_congruence (poly_power q 2) (q * q) s;(* (q^2)*s poly_eq (q*q)*s *)
          poly_eq_transitivity (q * cof) ((q * q) * s) ((poly_power q 2) * s);
          poly_eq_symmetry (q * cof) ((poly_power q 2) * s);
          poly_eq_transitivity d (q * cof) ((poly_power q 2) * s);  (* d poly_eq (q^2)*s *)
          divides_intro (poly_power q 2) d s;               (* q^2 | d *)
          IR.not_square_free_of_repeated_factor q d 2       (* square_free d = false : contra *)
        end
    in
    Classical.move_requires refute ();
    assert ((coprime q cof) == true);
    if deg cof = 0 then begin
      (* BASE: d is (associate of) irreducible *)
      irreducible_associate q cof d;                       (* poly_irreducible d *)
      singleton_cert d
    end else begin
      (* RECURSE on the cofactor (smaller degree, still square-free) *)
      assert (deg cof >= 1);                               (* deg cof >= 0 and <> 0 *)
      mul_commutativity q cof;                             (* q*cof poly_eq cof*q *)
      poly_eq_transitivity d (q * cof) (cof * q);          (* d poly_eq cof*q *)
      divides_intro cof d q;                               (* cof | d *)
      LP.divisor_of_square_free cof d;                     (* square_free cof *)
      complete_factorization_exists cof;
      eliminate exists (fs': list (polynomial t)).
                  Cons? fs' /\ (PR.poly_prod fs' = cof) /\
                  SP.all_irreducible fs' /\ IR.pairwise_coprime fs'
      returns (exists (gs: list (polynomial t)).
                  Cons? gs /\ (PR.poly_prod gs = d) /\
                  SP.all_irreducible gs /\ IR.pairwise_coprime gs)
      with _. cons_cert q cof d fs'
    end
#pop-options

(* ================================================================ *)
(*  STEP 3 — pipeline-facing form at the prime field  fp p.         *)
(*                                                                   *)
(*  The exact predicate bundle that                                  *)
(*  Core.Modular.FpZmodBridge.recombination_complete_fp consumes:    *)
(*  all_irreducible + pairwise_coprime + product = f̄ (monic left    *)
(*  to the pipeline's normalisation — see report).                   *)
(* ================================================================ *)

let berlekamp_complete (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  : Lemma (requires deg fbar >= 1 /\ SF.square_free fbar)
          (ensures  exists (gs: list (polynomial (fp p))).
                       Cons? gs /\
                       (PR.poly_prod gs = fbar) /\
                       SP.all_irreducible gs /\
                       IR.pairwise_coprime gs)
  = complete_factorization_exists #(fp p) fbar

(* ================================================================ *)
(*  STEP 2 — tie the number of factors to the Berlekamp count (#29).*)
(*                                                                   *)
(*  Bridge SubsetProd.all_irreducible (memP form) to the index form  *)
(*  BerlekampDim.all_irreducible that BerlekampDimCount consumes.    *)
(* ================================================================ *)

let all_irreducible_to_dim (p:int{EU.is_prime p})
  (fs: list (polynomial (fp p)))
  : Lemma (requires SP.all_irreducible fs)
          (ensures  BD.all_irreducible p fs)
  = SP.all_irreducible_elim fs;
    let proof (i:nat{i < L.length fs})
      : Lemma (IR.poly_irreducible #(fp p) (L.index fs i))
      = L.lemma_index_memP fs i
    in
    BD.all_irreducible_intro p fs proof

(* The complete factorization of a square-free f̄ has EXACTLY r factors,
   where the Berlekamp set of the product has cardinality p^r — i.e.
   #irreducible-factors == log_p |B(∏gs)| (kernel dimension = #factors). *)
let berlekamp_complete_count (p:int{EU.is_prime p})
  (fbar: polynomial (fp p))
  : Lemma (requires deg fbar >= 1 /\ SF.square_free fbar)
          (ensures  exists (gs bs: list (polynomial (fp p))).
                       Cons? gs /\ (PR.poly_prod gs = fbar) /\
                       SP.all_irreducible gs /\ IR.pairwise_coprime gs /\
                       L.no_repeats_p bs /\
                       L.length bs == BDC.pow p (L.length gs) /\
                       (forall (h: polynomial (fp p)).
                          L.memP h bs <==> BD.is_berlekamp p (PR.poly_prod gs) h))
  = berlekamp_complete p fbar;
    eliminate exists (gs: list (polynomial (fp p))).
                Cons? gs /\ (PR.poly_prod gs = fbar) /\
                SP.all_irreducible gs /\ IR.pairwise_coprime gs
    returns (exists (gs bs: list (polynomial (fp p))).
                Cons? gs /\ (PR.poly_prod gs = fbar) /\
                SP.all_irreducible gs /\ IR.pairwise_coprime gs /\
                L.no_repeats_p bs /\
                L.length bs == BDC.pow p (L.length gs) /\
                (forall (h: polynomial (fp p)).
                   L.memP h bs <==> BD.is_berlekamp p (PR.poly_prod gs) h))
    with _.
    begin
      all_irreducible_to_dim p gs;
      BDC.berlekamp_count p gs;
      eliminate exists (bs: list (polynomial (fp p))).
                  L.no_repeats_p bs /\
                  L.length bs == BDC.pow p (L.length gs) /\
                  (forall (h: polynomial (fp p)).
                     L.memP h bs <==> BD.is_berlekamp p (PR.poly_prod gs) h)
      returns (exists (gs bs: list (polynomial (fp p))).
                  Cons? gs /\ (PR.poly_prod gs = fbar) /\
                  SP.all_irreducible gs /\ IR.pairwise_coprime gs /\
                  L.no_repeats_p bs /\
                  L.length bs == BDC.pow p (L.length gs) /\
                  (forall (h: polynomial (fp p)).
                     L.memP h bs <==> BD.is_berlekamp p (PR.poly_prod gs) h))
      with _.
      introduce exists (gs2 bs2: list (polynomial (fp p))).
                  Cons? gs2 /\ (PR.poly_prod gs2 = fbar) /\
                  SP.all_irreducible gs2 /\ IR.pairwise_coprime gs2 /\
                  L.no_repeats_p bs2 /\
                  L.length bs2 == BDC.pow p (L.length gs2) /\
                  (forall (h: polynomial (fp p)).
                     L.memP h bs2 <==> BD.is_berlekamp p (PR.poly_prod gs2) h)
      with gs bs and ()
    end

(* ================================================================ *)
(*  MONIC completeness certificate.                                  *)
(*                                                                   *)
(*  Normalise every factor of the (irreducible, pairwise-coprime)    *)
(*  factorisation to be monic.  For a MONIC squarefree f̄ the unit    *)
(*  scalars cancel, so the product of the monic factors is exactly   *)
(*  f̄.  This adds the missing all_monic clause, delivering ALL the   *)
(*  factor hypotheses of Core.Modular.FpZmodBridge.                   *)
(*  recombination_complete_fp.                                        *)
(* ================================================================ *)

(* make_monic p divides p (they are associates). *)
#push-options "--z3rlimit 40"
let make_monic_divides (#t:Type) {| f: field t |} (p: polynomial t)
  : Lemma (requires deg p >= 0)
          (ensures divides (make_monic p) p)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    make_monic_associate p;
    eliminate exists (u:t). not (u = (zero <: t)) /\ (make_monic p = (poly_const u * p))
    returns divides (make_monic p) p
    with _.
    begin
      let mg = make_monic p in
      inversion_lemma u;                   (* u * inv u = one /\ inv u * u = one *)
      let w : t = inv u in
      mul_congruence (poly_const w) mg (poly_const w) (poly_const u * p);
      mul_associativity (poly_const w) (poly_const u) p;
      poly_const_mul w u;
      poly_eq_symmetry (poly_const (w * u)) (poly_const w * poly_const u);
      mul_congruence (poly_const w * poly_const u) p (poly_const (w * u)) p;
      poly_const_congr (w * u) (one <: t);
      poly_const_one #t ();
      poly_eq_transitivity (poly_const (w * u)) (poly_const (one <: t)) (poly_one #t);
      mul_congruence (poly_const (w * u)) p (poly_one #t) p;
      poly_mul_one p;                      (* poly_one * p = p *)
      poly_eq_transitivity (poly_const w * mg) (poly_const w * (poly_const u * p))
                           ((poly_const w * poly_const u) * p);
      poly_eq_transitivity (poly_const w * mg) ((poly_const w * poly_const u) * p)
                           (poly_const (w * u) * p);
      poly_eq_transitivity (poly_const w * mg) (poly_const (w * u) * p) (poly_one #t * p);
      poly_eq_transitivity (poly_const w * mg) (poly_one #t * p) p;
      mul_commutativity (poly_const w) mg;
      poly_eq_symmetry (poly_const w * mg) p;
      poly_eq_transitivity p (poly_const w * mg) (mg * poly_const w);
      divides_intro mg p (poly_const w)
    end
#pop-options

(* coprimality is preserved by monic normalisation (unit scaling). *)
let coprime_make_monic (#t:Type) {| f: field t |} (a b: polynomial t)
  : Lemma (requires (coprime a b) /\ deg a >= 0 /\ deg b >= 0)
          (ensures  coprime (make_monic a) (make_monic b))
  = make_monic_monic a;                              (* monic (make_monic a) ⟹ deg >= 0 *)
    make_monic_monic b;
    make_monic_divides a;                            (* make_monic a | a *)
    make_monic_divides b;
    IR.coprime_divisor a b (make_monic a);           (* coprime (make_monic a) b *)
    IR.coprime_symmetric (make_monic a) b;           (* coprime b (make_monic a) *)
    IR.coprime_divisor b (make_monic a) (make_monic b);  (* coprime (make_monic b)(make_monic a) *)
    IR.coprime_symmetric (make_monic b) (make_monic a)   (* coprime (make_monic a)(make_monic b) *)

(* monic normalisation preserves irreducibility (associate of irreducible). *)
let make_monic_irreducible (#t:Type) {| f: field t |} (p: polynomial t)
  : Lemma (requires IR.poly_irreducible p)
          (ensures  IR.poly_irreducible (make_monic p))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    assert (deg p >= 1);
    make_monic_associate p;
    eliminate exists (u:t). not (u = (zero <: t)) /\ (make_monic p = (poly_const u * p))
    returns IR.poly_irreducible (make_monic p)
    with _.
    begin
      poly_const_deg u;                              (* deg (poly_const u) == 0 *)
      mul_commutativity (poly_const u) p;            (* poly_const u * p = p * poly_const u *)
      poly_eq_transitivity (make_monic p) (poly_const u * p) (p * poly_const u);
      irreducible_associate p (poly_const u) (make_monic p)
    end

(* ================================================================ *)
(*  STEP 3′ — MONIC pipeline-facing form at the prime field fp p.    *)
(*                                                                   *)
(*  The complete factor bundle that                                  *)
(*  Core.Modular.FpZmodBridge.recombination_complete_fp consumes on  *)
(*  its  gbars_fp  argument:  all_irreducible + all_monic +          *)
(*  pairwise_coprime + product = f̄.                                  *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let berlekamp_complete_monic (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  : Lemma (requires deg fbar >= 1 /\ SF.square_free fbar /\ monic fbar)
          (ensures  exists (gs: list (polynomial (fp p))).
                       Cons? gs /\
                       (PR.poly_prod gs = fbar) /\
                       SP.all_irreducible gs /\
                       SP.all_monic gs /\
                       IR.pairwise_coprime gs)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    H.trans_for_calc (polynomial (fp p)) ();
    berlekamp_complete p fbar;
    eliminate exists (gs0: list (polynomial (fp p))).
                Cons? gs0 /\ (PR.poly_prod gs0 = fbar) /\
                SP.all_irreducible gs0 /\ IR.pairwise_coprime gs0
    returns (exists (gs: list (polynomial (fp p))).
                Cons? gs /\ (PR.poly_prod gs = fbar) /\
                SP.all_irreducible gs /\ SP.all_monic gs /\ IR.pairwise_coprime gs)
    with _.
    begin
      let gs : list (polynomial (fp p)) = L.map make_monic gs0 in
      SP.all_irreducible_elim gs0;
      IR.pairwise_coprime_elim gs0;
      (* every gs0 element is irreducible, hence deg >= 1 *)
      let hdeg (k:nat{k < L.length gs0}) : Lemma (deg (L.index gs0 k) >= 0)
        = L.lemma_index_memP gs0 k;
          assert (IR.poly_irreducible (L.index gs0 k)) in
      (* product : poly_prod gs = poly_const u * poly_prod gs0 = poly_const u * fbar = fbar *)
      prod_map_make_monic gs0 hdeg;
      eliminate exists (u: fp p). not (u = (zero <: fp p)) /\
                  (PR.poly_prod gs = (poly_const u * PR.poly_prod gs0))
      returns (PR.poly_prod gs = fbar)
      with _.
      begin
        mul_congruence (poly_const u) (PR.poly_prod gs0) (poly_const u) fbar;
        poly_eq_transitivity (PR.poly_prod gs) (poly_const u * PR.poly_prod gs0)
                             (poly_const u * fbar);
        monic_assoc_eq (PR.poly_prod gs) fbar u
      end;
      (* all_irreducible gs *)
      let pir (h: polynomial (fp p){L.memP h gs}) : Lemma (IR.poly_irreducible h)
        = L.memP_map_elim make_monic h gs0;
          eliminate exists (x: polynomial (fp p)). L.memP x gs0 /\ make_monic x == h
          returns IR.poly_irreducible h
          with _. make_monic_irreducible x in
      SP.all_irreducible_intro gs pir;
      (* all_monic gs *)
      let pmon (h: polynomial (fp p){L.memP h gs}) : Lemma (monic h)
        = L.memP_map_elim make_monic h gs0;
          eliminate exists (x: polynomial (fp p)). L.memP x gs0 /\ make_monic x == h
          returns monic h
          with _. (assert (IR.poly_irreducible x); make_monic_monic x) in
      SP.all_monic_intro gs pmon;
      (* pairwise_coprime gs *)
      let ppc (i:nat{i < L.length gs}) (j:nat{j < L.length gs /\ j <> i})
        : Lemma (coprime (L.index gs i) (L.index gs j))
        = BD.index_map make_monic gs0 i;
          BD.index_map make_monic gs0 j;
          L.lemma_index_memP gs0 i;
          L.lemma_index_memP gs0 j;
          assert (IR.poly_irreducible (L.index gs0 i));
          assert (IR.poly_irreducible (L.index gs0 j));
          coprime_make_monic (L.index gs0 i) (L.index gs0 j) in
      IR.pairwise_coprime_intro gs ppc;
      introduce exists (gs2: list (polynomial (fp p))).
                  Cons? gs2 /\ (PR.poly_prod gs2 = fbar) /\
                  SP.all_irreducible gs2 /\ SP.all_monic gs2 /\ IR.pairwise_coprime gs2
      with gs and ()
    end
#pop-options
