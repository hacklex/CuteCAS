module Core.Polynomial.LagrangeBasisBound

(* ================================================================ *)
(*  §D Kronecker bound — the PER-TERM Lagrange basis coefficient     *)
(*  bound.                                                           *)
(*                                                                  *)
(*  For distinct integer nodes `int_cs` and `j < length int_cs`,     *)
(*  the j-th ℚ Lagrange basis polynomial at the embedded nodes has   *)
(*  every coefficient bounded in `q_abs` by the embedded integer     *)
(*  ∞-norm of the integer numerator                                 *)
(*    int_prod_linears (delete_index int_cs j).                     *)
(*                                                                  *)
(*  Proof chain (all sub-lemmas are GREEN prerequisites):           *)
(*    coeff basis i = invd * coeff numq i        [poly_scale coeff]  *)
(*    coeff numq i  = embed (coeff inum i)        [prod / embed]     *)
(*    invd          = inv (embed idenom),         [denom embed]      *)
(*       iabs idenom >= 1                          [distinct]         *)
(*    q_abs (coeff basis i)                                          *)
(*       = q_abs(invd) * embed (iabs (coeff inum i))                 *)
(*       <=_q one * embed (iabs (coeff inum i))   [inv-abs <= 1]     *)
(*       =   embed (iabs (coeff inum i))                             *)
(*       <=_q embed (poly_height inum)            [coeff <= height]  *)
(*                                                                  *)
(*  NO admit / assume / sorry.                                      *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module RA = Core.Fractions.RationalAbs
module HT = Core.Polynomial.Height

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Fractions
open Core.Polynomial.EmbedQ
open Core.Polynomial.EmbedQProd
open Core.Polynomial.EmbedQAbs
open Core.Polynomial.Height
open Core.Fractions.RationalAbs
open Core.Fractions.RationalAbsInv
open Core.Polynomial.Lagrange
open Core.Polynomial.LagrangeDenomQ

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* The ℚ field instance (= EmbedQProd's `ff`). *)
let ffld : field qq = fraction_field int int_id

(* ---------------------------------------------------------------- *)
(*  Distinctness of the embedded node list, derived from the          *)
(*  integer distinctness.  `lagrange_basis` needs this as a squash.   *)
(*                                                                   *)
(*  embed_zq_const is injective on `=` (embed_zq_const_zero_iff /      *)
(*  fraction_eq_reveal): embed a = embed b  <==>  a = b.              *)
(* ---------------------------------------------------------------- *)

(* embed_zq_const is injective up to the qq equatable `=`. *)
let embed_inj (a b: int)
  : Lemma (requires (embed_zq_const a) = (embed_zq_const b))
          (ensures  a == b)
  = embed_nd a; embed_nd b;
    (* (ea = eb) <==> num ea * den eb = den ea * num eb, i.e. a*1 = 1*b *)
    fraction_eq_reveal #int #int_id (embed_zq_const a) (embed_zq_const b)

(* all_distinct is preserved by embed_zq_const (contrapositive of inj). *)
#push-options "--fuel 2 --ifuel 2"
let rec embed_all_distinct (int_cs: list int)
  : Lemma (requires all_distinct #int #int_cr int_cs)
          (ensures  all_distinct #qq #crq (L.map embed_zq_const int_cs))
          (decreases int_cs)
  = match int_cs with
    | [] -> ()
    | x :: rest ->
      embed_all_distinct rest;
      L.map_lemma embed_zq_const rest;
      (* head: forall d in map embed rest. not (embed x = d). *)
      let ex = embed_zq_const x in
      let aux (d: qq) : Lemma (L.memP d (L.map embed_zq_const rest) ==> not (ex = d)) =
        introduce L.memP d (L.map embed_zq_const rest) ==> not (ex = d)
        with _hd. begin
          (* d is embed of some member y of rest, and x <> y by head distinctness *)
          L.memP_map_elim embed_zq_const d rest;
          eliminate exists (y: int). L.memP y rest /\ embed_zq_const y == d
          returns not (ex = d)
          with _hy. begin
            (* all_distinct head on int_cs: not (x = y) *)
            assert (forall (e:int). L.memP e rest ==> not (x = e));
            assert (not (x = y));
            (* so x <> y as ints; embed_inj contrapositive gives not (ex = embed y) = not (ex = d) *)
            introduce ex = d ==> False
            with _heq. begin
              embed_inj x y
            end
          end
        end
      in
      Classical.forall_intro aux
#pop-options

(* squash-producing wrapper, for the `lagrange_basis` instance arg. *)
let embed_all_distinct_sq (int_cs: list int)
  : Pure (squash (all_distinct #qq #crq (L.map embed_zq_const int_cs)))
         (requires all_distinct #int #int_cr int_cs)
         (ensures fun _ -> True)
  = embed_all_distinct int_cs

(* ---------------------------------------------------------------- *)
(*  Integer distinctness: index int_cs j differs (Prims `<>`) from     *)
(*  every member of (delete_index int_cs j).  `index_j_differs`        *)
(*  (Core.Polynomial.Lagrange) is field-only; re-derive over `int`     *)
(*  where the ring `=` is integer equality.                            *)
(* ---------------------------------------------------------------- *)

#push-options "--fuel 2 --ifuel 2"
let rec delete_index_neq_index (cs: list int) (j: nat{j < L.length cs}) (y: int)
  : Lemma (requires all_distinct #int #int_cr cs /\ L.memP y (delete_index cs j))
          (ensures  L.index cs j <> y)
          (decreases cs)
  = match cs with
    | x :: rest ->
      if j = 0 then begin
        (* index cs 0 = x; y in delete_index cs 0 = rest, so memP y rest;
           all_distinct head: not (x = y), i.e. x <> y as ints. *)
        assert (forall (d:int). L.memP d rest ==> not (x = d))
      end
      else begin
        (* index cs j = index rest (j-1); y in x :: delete_index rest (j-1). *)
        eliminate (y == x) \/ (L.memP y (delete_index rest (j - 1)))
        returns L.index cs j <> y
        with _heq. begin
          (* y == x.  index cs j = index rest (j-1) is a member of rest,
             so all_distinct head gives x <> that member. *)
          L.lemma_index_memP rest (j - 1);
          assert (forall (d:int). L.memP d rest ==> not (x = d));
          assert (x <> L.index rest (j - 1))
        end
        and  _h. delete_index_neq_index rest (j - 1) y
      end
#pop-options

(* ---------------------------------------------------------------- *)
(*  numq = lagrange_numer qcs j ; its coeff i is embed (coeff inum i).*)
(* ---------------------------------------------------------------- *)

let numer_coeff_embed (int_cs: list int) (j: nat{j < L.length int_cs}) (i: nat)
  : Lemma (L.length (L.map embed_zq_const int_cs) == L.length int_cs /\
           j < L.length (L.map embed_zq_const int_cs) /\
           (coeff #qq #crq (lagrange_numer #qq #ffld (L.map embed_zq_const int_cs) j) i)
             = (embed_zq_const (coeff #int #int_cr (int_prod_linears (delete_index int_cs j)) i)))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let qcs  = L.map embed_zq_const int_cs in
    L.map_lemma embed_zq_const int_cs;
    let droots = delete_index int_cs j in
    let inum   = int_prod_linears droots in
    (* delete_index qcs j == map embed droots *)
    delete_index_map embed_zq_const int_cs j;
    (* lagrange_numer qcs j == poly_prod_linears (delete_index qcs j)
                            == poly_prod_linears (map embed droots) *)
    let numq = lagrange_numer #qq #ffld qcs j in
    assert (numq == poly_prod_linears #qq #ffld (L.map embed_zq_const droots));
    (* embed_zq inum ≈ poly_prod_linears (map embed droots) *)
    embed_zq_prod_linears droots;
    (* coeff numq i = coeff (embed_zq inum) i  (poly_eq ⇒ equal coeffs) *)
    poly_eq_symmetry #qq #crq
      (embed_zq inum)
      (poly_prod_linears #qq #ffld (L.map embed_zq_const droots));
    poly_eq_means_equal_coeffs #qq #crq
      (poly_prod_linears #qq #ffld (L.map embed_zq_const droots))
      (embed_zq inum) i;
    (* coeff (embed_zq inum) i =eq= embed (coeff inum i) *)
    embed_zq_coeff inum i;
    (* chain: coeff numq i = coeff (embed inum) i = embed (coeff inum i) *)
    transitivity (coeff #qq #crq numq i)
                 (coeff #qq #crq (embed_zq inum) i)
                 (embed_zq_const (coeff #int #int_cr inum i))

(* ---------------------------------------------------------------- *)
(*  The basis coefficient equals invd * coeff numq i, in the qq        *)
(*  equatable `=`.  (poly_scale coeff + ring `*` defeq.)              *)
(* ---------------------------------------------------------------- *)

let basis_coeff_split (int_cs: list int) (j: nat{j < L.length int_cs}) (i: nat)
                      (sq: squash (all_distinct #qq #crq (L.map embed_zq_const int_cs)))
  : Lemma (let qcs  = L.map embed_zq_const int_cs in
           L.map_lemma embed_zq_const int_cs;
           (j < L.length qcs) /\
           (lagrange_denom_nonzero #qq #ffld qcs j;
            let d    = lagrange_denom #qq #ffld qcs j in
            let invd = inv d in
            (coeff #qq #crq (lagrange_basis #qq #ffld qcs j #sq) i)
              = (invd * (coeff #qq #crq (lagrange_numer #qq #ffld qcs j) i))))
  = let qcs  = L.map embed_zq_const int_cs in
    L.map_lemma embed_zq_const int_cs;
    lagrange_denom_nonzero #qq #ffld qcs j;
    let d    = lagrange_denom #qq #ffld qcs j in
    let invd = inv d in
    let numq = lagrange_numer #qq #ffld qcs j in
    (* lagrange_basis qcs j == poly_scale invd numq == poly_mul (invd @ poly_zero) numq *)
    assert (lagrange_basis #qq #ffld qcs j #sq == poly_scale #qq #crq invd numq);
    (* coeff (poly_mul (invd @ poly_zero) numq) i = invd * coeff numq i *)
    poly_mul_singleton_coeff #qq #crq invd numq i

(* ================================================================ *)
(*  The deliverable.                                                 *)
(* ================================================================ *)

#push-options "--z3rlimit 60"
let lagrange_basis_coeff_bound (int_cs: list int) (j: nat) (i: nat)
  : Lemma (requires all_distinct #int #int_cr int_cs /\ j < L.length int_cs)
          (ensures (let qcs = L.map embed_zq_const int_cs in
                    L.map_lemma embed_zq_const int_cs;
                    j < L.length qcs /\
                    (let sq : squash (all_distinct #qq #crq qcs) =
                       embed_all_distinct_sq int_cs in
                     q_le (q_abs (coeff #qq #crq (lagrange_basis #qq #ffld qcs j #sq) i))
                          (embed_zq_const
                             (poly_height (int_prod_linears (delete_index int_cs j)))))))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let qcs = L.map embed_zq_const int_cs in
    L.map_lemma embed_zq_const int_cs;
    let sq : squash (all_distinct #qq #crq qcs) = embed_all_distinct_sq int_cs in
    let droots = delete_index int_cs j in
    let inum   = int_prod_linears droots in
    let cinum  = coeff #int #int_cr inum i in
    lagrange_denom_nonzero #qq #ffld qcs j;
    let d    = lagrange_denom #qq #ffld qcs j in
    let invd = inv d in
    let numq = lagrange_numer #qq #ffld qcs j in
    let basis = lagrange_basis #qq #ffld qcs j #sq in
    let cb = coeff #qq #crq basis i in
    let cn = coeff #qq #crq numq i in

    (* ---- (A) cb = invd * cn = fraction_mul invd cn ---- *)
    basis_coeff_split int_cs j i sq;
    (* cb = invd * cn *)
    assert (cb = invd * cn);
    fraction_ring_mul_reveal #int #int_id invd cn;   (* invd * cn == fraction_mul invd cn *)
    assert (cb = fraction_mul #int #int_id invd cn);

    (* ---- (B) q_abs cb = fraction_mul (q_abs invd) (q_abs cn) ---- *)
    q_abs_well_defined cb (fraction_mul #int #int_id invd cn);   (* q_abs cb = q_abs (fmul invd cn) *)
    q_abs_mul invd cn;                                            (* q_abs (fmul invd cn) = fmul (q_abs invd)(q_abs cn) *)
    transitivity (q_abs cb)
                 (q_abs (fraction_mul #int #int_id invd cn))
                 (fraction_mul #int #int_id (q_abs invd) (q_abs cn));
    (* q_abs cb = fmul (q_abs invd) (q_abs cn) *)

    (* ---- (C) cn = embed cinum ; q_abs cn = embed (iabs cinum) ---- *)
    numer_coeff_embed int_cs j i;                  (* cn = embed cinum *)
    assert (cn = embed_zq_const cinum);
    q_abs_well_defined cn (embed_zq_const cinum);   (* q_abs cn = q_abs (embed cinum) *)
    q_abs_embed cinum;                              (* q_abs (embed cinum) = embed (iabs cinum) *)
    transitivity (q_abs cn)
                 (q_abs (embed_zq_const cinum))
                 (embed_zq_const (RA.iabs cinum));
    assert (q_abs cn = embed_zq_const (RA.iabs cinum));

    (* ---- (D) invd = inv (embed idenom), iabs idenom >= 1 ---- *)
    let idenom = int_prod_sub droots (L.index int_cs j) in
    (* distinctness: every member m of droots differs from index int_cs j *)
    let cj = L.index int_cs j in
    let aux_ne (m:int) : Lemma (L.memP m droots ==> m <> cj) =
      introduce L.memP m droots ==> m <> cj
      with _hm. begin
        (* index_j_differs over the integer commutative_ring is field-only;
           re-derive: index int_cs j differs from any member of delete_index. *)
        delete_index_neq_index int_cs j m
      end
    in
    Classical.forall_intro aux_ne;
    int_prod_sub_abs_ge_one droots cj;             (* iabs idenom >= 1 *)
    assert (RA.iabs idenom >= 1);
    (* d = embed idenom *)
    lagrange_denom_embed int_cs j;
    assert (d = embed_zq_const idenom);

    (* invd = inv d = inv (embed idenom) *)
    (* d is nonzero (lagrange_denom_nonzero, distinct nodes) *)
    lagrange_denom_nonzero #qq #ffld qcs j;
    (* iabs idenom >= 1 ⇒ idenom <> 0 ⇒ embed idenom nonzero *)
    RA.iabs_zero_iff idenom;
    assert (idenom <> 0);
    embed_nonzero idenom;                          (* is_nonzero (embed idenom) *)
    inv_congr #qq d (embed_zq_const idenom);       (* inv d = inv (embed idenom) *)
    assert (invd = inv (embed_zq_const idenom));

    (* ---- (E) q_abs invd <=_q one ---- *)
    q_abs_inv_embed_le_one idenom;                 (* q_le (q_abs (inv (embed idenom))) one *)
    (* transport along invd = inv (embed idenom): q_abs invd = q_abs (inv (embed idenom)) *)
    q_abs_well_defined invd (inv (embed_zq_const idenom));
    q_le_well_defined (q_abs (inv (embed_zq_const idenom)))
                      (q_abs invd)
                      (one <: qq) (one <: qq);
    assert (q_le (q_abs invd) (one <: qq));

    (* ---- (F) product monotonicity:
              fmul (q_abs invd)(q_abs cn) <=_q fmul one (q_abs cn) ---- *)
    (* need q_le 0 (q_abs cn) *)
    q_abs_nonneg cn;                               (* q_le (fraction_zero) (q_abs cn) *)
    q_le_mul_mono_r (q_abs invd) (one <: qq) (q_abs cn);
    (* q_le (fmul (q_abs invd)(q_abs cn)) (fmul one (q_abs cn)) *)

    (* fmul one (q_abs cn) = q_abs cn  (one is mult identity) *)
    H.one_mul_x #qq (q_abs cn);                    (* one * q_abs cn = q_abs cn *)
    fraction_ring_mul_reveal #int #int_id (one <: qq) (q_abs cn);  (* one*qabs == fmul one qabs *)
    symmetry (fraction_mul #int #int_id (one <: qq) (q_abs cn)) (q_abs cn);
    (* so q_abs cn = fmul one (q_abs cn) ; we want fmul one (q_abs cn) = q_abs cn *)
    assert (fraction_mul #int #int_id (one <: qq) (q_abs cn) = (q_abs cn));

    (* transport the q_le RHS from fmul one (q_abs cn) to q_abs cn *)
    q_le_well_defined (fraction_mul #int #int_id (q_abs invd) (q_abs cn))
                      (fraction_mul #int #int_id (q_abs invd) (q_abs cn))
                      (fraction_mul #int #int_id (one <: qq) (q_abs cn))
                      (q_abs cn);
    assert (q_le (fraction_mul #int #int_id (q_abs invd) (q_abs cn)) (q_abs cn));

    (* and q_abs cb = fmul (q_abs invd)(q_abs cn), so q_le (q_abs cb) (q_abs cn) *)
    q_le_well_defined (fraction_mul #int #int_id (q_abs invd) (q_abs cn))
                      (q_abs cb)
                      (q_abs cn) (q_abs cn);
    assert (q_le (q_abs cb) (q_abs cn));

    (* ---- (G) q_abs cn = embed (iabs cinum) <=_q embed (poly_height inum) ---- *)
    coeff_abs_le_height inum i;                    (* iabs cinum <= poly_height inum (HT.iabs) *)
    (* HT.iabs and RA.iabs agree definitionally *)
    assert (RA.iabs cinum == HT.iabs cinum);
    q_le_embed (RA.iabs cinum) (poly_height inum);
    (* q_le (embed (iabs cinum)) (embed (poly_height inum)) since iabs cinum <= height *)
    assert (q_le (embed_zq_const (RA.iabs cinum))
                 (embed_zq_const (poly_height inum)));
    (* q_abs cn = embed (iabs cinum), so transport q_le LHS to q_abs cn *)
    q_le_well_defined (embed_zq_const (RA.iabs cinum))
                      (q_abs cn)
                      (embed_zq_const (poly_height inum))
                      (embed_zq_const (poly_height inum));
    assert (q_le (q_abs cn) (embed_zq_const (poly_height inum)));

    (* ---- (H) chain: q_le (q_abs cb) (q_abs cn) (q_abs cn) <= height ---- *)
    q_le_trans (q_abs cb) (q_abs cn) (embed_zq_const (poly_height inum))
#pop-options
