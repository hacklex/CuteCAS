module Core.Polynomial.KroneckerBound

(* ================================================================ *)
(*  §D capstone — the KRONECKER COEFFICIENT BOUND.                   *)
(*                                                                   *)
(*  If  F = g·k  over ℤ and g has degree < #nodes for a list of      *)
(*  distinct integer nodes `int_cs` at which F never vanishes, then  *)
(*  every coefficient of g is bounded in absolute value by the       *)
(*  computable integer sum                                           *)
(*    Σ_{j<len} |F(cⱼ)| · ‖∏_{m≠j}(X−c_m)‖∞ .                         *)
(*                                                                   *)
(*  Assembly of the (all-green) §D prerequisites:                    *)
(*    embed_interpolation  (g = its Lagrange interpolant over ℚ)     *)
(*    coeff_sum_range      (coeff commutes with finite sums)         *)
(*    lagrange_basis_coeff_bound  (per-basis coeff bound)            *)
(*    eval_factor_abs_le   (|g(c)| ≤ |F(c)| for a factor)            *)
(*    q_abs_sum_le / q_le_sum_mono / q_le_mul_mono_r  (ℚ order glue) *)
(*    embed_zq_eval / q_abs_embed / q_le_embed  (ℤ ↔ ℚ descent)      *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module RA = Core.Fractions.RationalAbs
module FF = Core.Modular.LagrangeBound

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Roots
open Core.Fractions
open Core.FinSum
open Core.Polynomial.Eval
open Core.Polynomial.Height
open Core.Polynomial.EmbedQProd
open Core.Polynomial.EmbedQ
open Core.Polynomial.EmbedQAbs
open Core.Fractions.RationalAbs
open Core.Polynomial.Lagrange
open Core.Polynomial.LagrangeInterp
open Core.Polynomial.LagrangeBasisBound
open Core.Polynomial.EmbedQInterp
open Core.Polynomial.CoeffSum

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

let ff : field qq = fraction_field int int_id

(* ================================================================ *)
(*  The integer right-fold matching `sum_range`'s right-unfold.      *)
(* ================================================================ *)

let rec int_sum (h: nat -> int) (lo hi: nat)
  : Tot int (decreases (if hi <= lo then 0 else hi - lo))
  = if hi <= lo then 0
    else int_sum h lo (hi - 1) ++ h (hi - 1)

(* ================================================================ *)
(*  (S1)  embed_zq_const pushes through int_sum:                     *)
(*    Σ_{j<·} (embed (h j))  =eq=  embed (int_sum h)                 *)
(* ================================================================ *)

#push-options "--fuel 2 --ifuel 1 --z3rlimit 80"
let rec embed_int_sum (h: nat -> int) (lo hi: nat)
  : Lemma (ensures
      sum_range #qq #qacg (fun (j:nat) -> embed_zq_const (h j)) lo hi
      = embed_zq_const (int_sum h lo hi))
    (decreases (if hi <= lo then 0 else hi - lo))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let hq : nat -> qq = fun (j:nat) -> embed_zq_const (h j) in
    if hi <= lo then begin
      sum_range_empty #qq #qacg hq lo hi;           (* sum = qacg.zero *)
      (* int_sum h lo hi == 0 ; embed 0 =eq= qacg.zero ; symm *)
      embed_zq_const_zero ()                          (* embed 0 = crq.zero = qacg.zero *)
    end
    else begin
      let hp = hi - 1 in
      sum_range_unfold_right #qq #qacg hq lo hi;     (* sum lo hi = sum lo hp + hq hp *)
      qacg_add_reveal (sum_range #qq #qacg hq lo hp) (hq hp);
      (* sum lo hi = fraction_add (sum lo hp) (hq hp) *)
      (* IH: sum lo hp =eq= embed (int_sum h lo hp) *)
      embed_int_sum h lo hp;
      (* hq hp == embed (h hp) by beta; reflexivity is in scope via elim_equatable_laws *)
      add_congruence #qq #qacg
        (sum_range #qq #qacg hq lo hp) (hq hp)
        (embed_zq_const (int_sum h lo hp)) (embed_zq_const (h hp));
      (* fraction_add (embed (int_sum h lo hp)) (embed (h hp)) =eq= embed (int_sum h lo hp + h hp) *)
      qacg_add_reveal (embed_zq_const (int_sum h lo hp)) (embed_zq_const (h hp));
      embed_zq_const_add (int_sum h lo hp) (h hp);
      (* int_sum h lo hi == int_sum h lo hp + h hp (definitional) *)
      ()
    end
#pop-options

(* ================================================================ *)
(*  The per-index integer summand and the RHS bound.                *)
(* ================================================================ *)

let kterm (bigF: polynomial int #int_cr) (int_cs: list int) (j: nat) : int =
  if j < L.length int_cs
  then RA.iabs (poly_eval #int #int_cr bigF (L.index int_cs j))
       * poly_height (int_prod_linears (delete_index int_cs j))
  else 0

let kbound_rhs (bigF: polynomial int #int_cr) (int_cs: list int) : int =
  int_sum (kterm bigF int_cs) 0 (L.length int_cs)

(* ================================================================ *)
(*  Small glue lemmas for S2.                                       *)
(* ================================================================ *)

(* index of the embedded node list. *)
let rec index_map_kb (cs: list int) (j: nat{j < L.length cs})
  : Lemma (ensures (L.map_lemma embed_zq_const cs;
                    L.index (L.map embed_zq_const cs) j == embed_zq_const (L.index cs j)))
          (decreases j)
  = L.map_lemma embed_zq_const cs;
    if j = 0 then () else index_map_kb (L.tl cs) (j - 1)

(* fraction multiplication is commutative up to the fraction equatable `=`. *)
let fmul_comm_eq (a b: qq)
  : Lemma (fraction_mul #int #int_id a b = fraction_mul #int #int_id b a)
  = H.elim_equatable_laws qq ();
    fraction_ring_mul_reveal #int #int_id a b;     (* a *_qq b == fmul a b *)
    fraction_ring_mul_reveal #int #int_id b a;     (* b *_qq a == fmul b a *)
    H.mul_commutativity_cr #qq #crq a b              (* a *_qq b =eq= b *_qq a *)

(* a nonnegative embedded integer is ≥_q the rational zero. *)
let embed_nonneg_ge_zero (n: int)
  : Lemma (requires n >= 0)
          (ensures q_le (fraction_zero int #int_id) (embed_zq_const n))
  = H.elim_equatable_laws qq ();
    (* embed 0 = fraction_zero (cross-mult: 0*1 = 1*0) *)
    fraction_zero_reveal int #int_id;
    fraction_eq_reveal #int #int_id (embed_zq_const 0) (fraction_zero int #int_id);
    (* q_le (embed 0) (embed n) == (0 <= n) == true *)
    q_le_embed 0 n;
    (* transport LHS embed 0 -> fraction_zero *)
    q_le_well_defined (embed_zq_const 0) (fraction_zero int #int_id)
                      (embed_zq_const n) (embed_zq_const n)

let q_abs_embed_le_zero_lemma (n: int)
  : Lemma (q_le (fraction_zero int #int_id) (embed_zq_const (RA.iabs n)))
  = RA.iabs_nonneg n;
    embed_nonneg_ge_zero (RA.iabs n)

(* ================================================================ *)
(*  (S2)  Per-term factor bound.                                    *)
(*    q_abs (coeff (interp_term eg qcs j) i)  ≤_q  embed (kterm j)   *)
(*  for j < len, under F = g·k and F(cⱼ) ≠ 0.                        *)
(* ================================================================ *)

#push-options "--z3rlimit 100 --split_queries always"
let per_term_bound
  (g k bigF: polynomial int #int_cr) (int_cs: list int) (i: nat)
  (j: nat{j < L.length int_cs})
  (sq: squash (all_distinct #qq #crq (L.map embed_zq_const int_cs)))
  : Lemma (requires
        bigF = g * k /\
        all_distinct #int #int_cr int_cs /\
        poly_eval #int #int_cr bigF (L.index int_cs j) <> 0)
      (ensures (let qcs = L.map embed_zq_const int_cs in
                L.map_lemma embed_zq_const int_cs;
                q_le (q_abs (coeff
                               (interp_term #qq #ff (embed_zq g) qcs #sq j) i))
                     (embed_zq_const (kterm bigF int_cs j))))
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let qcs = L.map embed_zq_const int_cs in
    L.map_lemma embed_zq_const int_cs;
    let cj  = L.index int_cs j in
    let eg  = embed_zq g in
    let basis = lagrange_basis #qq #ff qcs j #sq in
    let aq  = poly_eval #qq #crq eg (L.index qcs j) in   (* g(cⱼ) embedded *)
    let cbasis = coeff basis i in
    let droots = delete_index int_cs j in
    let inum   = int_prod_linears droots in
    let hgt    = poly_height inum in

    (* ---- index of the mapped node list ---- *)
    index_map_kb int_cs j;                               (* index qcs j == embed cj *)
    assert (L.index qcs j == embed_zq_const cj);

    (* ---- (A) coeff (interp_term ... j) i = aq * cbasis ---- *)
    (* interp_term ... j = poly_scale aq basis (j < len) ;
       poly_scale aq basis = poly_mul (aq @ poly_zero) basis. *)
    assert (interp_term #qq #ff eg qcs #sq j
            == poly_scale #qq #crq aq basis);
    poly_mul_singleton_coeff #qq #crq aq basis i;        (* coeff (pmul (aq@z) basis) i = aq * cbasis *)
    let cterm = coeff (interp_term #qq #ff eg qcs #sq j) i in
    assert (cterm = aq * cbasis);
    fraction_ring_mul_reveal #int #int_id aq cbasis;     (* aq *_qq cbasis == fraction_mul aq cbasis *)
    assert (cterm = fraction_mul #int #int_id aq cbasis);

    (* ---- (B) q_abs cterm = fmul (q_abs aq) (q_abs cbasis) ---- *)
    q_abs_well_defined cterm (fraction_mul #int #int_id aq cbasis);
    q_abs_mul aq cbasis;
    assert (q_abs cterm = fraction_mul #int #int_id (q_abs aq) (q_abs cbasis));

    (* ---- (C) q_abs aq <=_q embed (iabs (eval bigF cj)) ---- *)
    (* aq = eval eg (embed cj) =eq= embed (eval g cj) *)
    embed_zq_eval g cj;
    assert (aq = embed_zq_const (poly_eval #int #int_cr g cj));
    q_abs_well_defined aq (embed_zq_const (poly_eval #int #int_cr g cj));
    q_abs_embed (poly_eval #int #int_cr g cj);           (* q_abs (embed (g cj)) = embed (iabs (g cj)) *)
    assert (q_abs aq = embed_zq_const (RA.iabs (poly_eval #int #int_cr g cj)));
    (* iabs (g cj) <= iabs (bigF cj) *)
    FF.eval_factor_abs_le bigF g k cj;
    assert (FF.iabs (poly_eval #int #int_cr g cj) <= FF.iabs (poly_eval #int #int_cr bigF cj));
    assert (RA.iabs (poly_eval #int #int_cr g cj) == FF.iabs (poly_eval #int #int_cr g cj));
    assert (RA.iabs (poly_eval #int #int_cr bigF cj) == FF.iabs (poly_eval #int #int_cr bigF cj));
    q_le_embed (RA.iabs (poly_eval #int #int_cr g cj)) (RA.iabs (poly_eval #int #int_cr bigF cj));
    assert (q_le (embed_zq_const (RA.iabs (poly_eval #int #int_cr g cj)))
                 (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))));
    (* transport to q_abs aq *)
    q_le_well_defined (embed_zq_const (RA.iabs (poly_eval #int #int_cr g cj)))
                      (q_abs aq)
                      (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj)))
                      (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj)));
    assert (q_le (q_abs aq) (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))));

    (* ---- (D) q_abs cbasis <=_q embed hgt ---- *)
    lagrange_basis_coeff_bound int_cs j i;
    assert (q_le (q_abs cbasis) (embed_zq_const hgt));

    (* ---- (E) 0 <=_q q_abs cbasis ; product monotonicity (right) ---- *)
    q_abs_nonneg cbasis;                                 (* q_le 0 (q_abs cbasis) *)
    (* q_le (q_abs aq) (embed (iabs bigF cj)) and q_le 0 (q_abs cbasis):
       fmul (q_abs aq) (q_abs cbasis) <=_q fmul (embed (iabs bigF cj)) (q_abs cbasis) *)
    q_le_mul_mono_r (q_abs aq) (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj)))
                    (q_abs cbasis);
    assert (q_le (fraction_mul #int #int_id (q_abs aq) (q_abs cbasis))
                 (fraction_mul #int #int_id
                    (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj)))
                    (q_abs cbasis)));

    (* ---- (F) product monotonicity (left): need
              fmul (embed (iabs bigF cj)) (q_abs cbasis)
              <=_q fmul (embed (iabs bigF cj)) (embed hgt) ---- *)
    (* 0 <=_q embed (iabs bigF cj) *)
    q_abs_embed_le_zero_lemma (RA.iabs (poly_eval #int #int_cr bigF cj));
    (* commute to use mul_mono_r on the right factor *)
    q_le_mul_mono_r (q_abs cbasis) (embed_zq_const hgt)
                    (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj)));
    assert (q_le (fraction_mul #int #int_id (q_abs cbasis)
                    (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))))
                 (fraction_mul #int #int_id (embed_zq_const hgt)
                    (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj)))));
    (* fmul commutes (up to =) to reorder factors *)
    fmul_comm_eq (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))) (q_abs cbasis);
    fmul_comm_eq (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))) (embed_zq_const hgt);
    q_le_well_defined
      (fraction_mul #int #int_id (q_abs cbasis)
         (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))))
      (fraction_mul #int #int_id
         (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))) (q_abs cbasis))
      (fraction_mul #int #int_id (embed_zq_const hgt)
         (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))))
      (fraction_mul #int #int_id
         (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))) (embed_zq_const hgt));
    assert (q_le (fraction_mul #int #int_id
                    (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))) (q_abs cbasis))
                 (fraction_mul #int #int_id
                    (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj)))
                    (embed_zq_const hgt)));

    (* ---- (G) chain (E) then (F): q_abs cterm <=_q embed(iabs bigF cj) * embed hgt ---- *)
    (* transport q_le LHS from fmul(q_abs aq)(q_abs cbasis) to q_abs cterm *)
    q_le_well_defined (fraction_mul #int #int_id (q_abs aq) (q_abs cbasis))
                      (q_abs cterm)
                      (fraction_mul #int #int_id
                         (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))) (q_abs cbasis))
                      (fraction_mul #int #int_id
                         (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))) (q_abs cbasis));
    assert (q_le (q_abs cterm)
                 (fraction_mul #int #int_id
                    (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))) (q_abs cbasis)));
    q_le_trans (q_abs cterm)
               (fraction_mul #int #int_id
                  (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))) (q_abs cbasis))
               (fraction_mul #int #int_id
                  (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj))) (embed_zq_const hgt));
    assert (q_le (q_abs cterm)
                 (fraction_mul #int #int_id
                    (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj)))
                    (embed_zq_const hgt)));

    (* ---- (H) embed(a)·embed(b) = embed(a·b) = embed (kterm j) ---- *)
    embed_zq_const_mul (RA.iabs (poly_eval #int #int_cr bigF cj)) hgt;
    assert (fraction_mul #int #int_id
              (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj)))
              (embed_zq_const hgt)
            = embed_zq_const (kterm bigF int_cs j));
    q_le_well_defined (q_abs cterm) (q_abs cterm)
                      (fraction_mul #int #int_id
                         (embed_zq_const (RA.iabs (poly_eval #int #int_cr bigF cj)))
                         (embed_zq_const hgt))
                      (embed_zq_const (kterm bigF int_cs j))
#pop-options

(* ================================================================ *)
(*  (S3)  The KRONECKER COEFFICIENT BOUND — full assembly.          *)
(* ================================================================ *)

(* The summand whose sum is the coefficient of the interpolant. *)
let cterm_fn (g: polynomial int #int_cr) (int_cs: list int) (i: nat)
             (sq: squash (all_distinct #qq #crq (L.map embed_zq_const int_cs)))
  : nat -> qq
  = coeff_at_term #qq #crq i (interp_term #qq #ff (embed_zq g) (L.map embed_zq_const int_cs) #sq)

(* The embedded RHS summand. *)
let embed_kterm_fn (bigF: polynomial int #int_cr) (int_cs: list int) : nat -> qq
  = fun (j:nat) -> embed_zq_const (kterm bigF int_cs j)

#push-options "--z3rlimit 150 --split_queries always"
let kronecker_coeff_bound
  (g k bigF: polynomial int #int_cr) (int_cs: list int) (i: nat)
  : Lemma (requires
        bigF = g * k /\
        all_distinct #int #int_cr int_cs /\
        deg #int #int_cr g < L.length int_cs /\
        (forall (j:nat). j < L.length int_cs ==>
            poly_eval #int #int_cr bigF (L.index int_cs j) <> 0))
      (ensures RA.iabs (coeff g i) <= kbound_rhs bigF int_cs)
  = H.elim_equatable_laws qq ();
    H.trans_for_calc qq ();
    let qcs = L.map embed_zq_const int_cs in
    L.map_lemma embed_zq_const int_cs;
    let len = L.length int_cs in
    let eg  = embed_zq g in
    let cgi = coeff g i in

    (* ---- (1) g embeds to its Lagrange interpolant over ℚ ---- *)
    embed_interpolation g int_cs;
    let sq : squash (all_distinct #qq #crq qcs) = embed_all_distinct_sq int_cs in
    let interp = lagrange_interpolant #qq #ff eg qcs #sq in
    assert (eg = interp);

    (* ---- (2) coeff eg i = coeff interp i ---- *)
    poly_eq_means_equal_coeffs #qq #crq eg interp i;
    assert (coeff eg i = coeff interp i);

    (* ---- (3) coeff interp i = sum_range (cterm_fn) 0 len ---- *)
    (* interp == sum_range #(poly qq) #(pacg (crf qq #ff)) (interp_term eg qcs) 0 len *)
    coeff_sum_range #qq #crq (interp_term #qq #ff eg qcs #sq) 0 len i;
    let cfn = cterm_fn g int_cs i sq in
    assert (coeff interp i
            = sum_range #qq #qacg cfn 0 len);

    (* ---- (4) coeff eg i =eq= embed (coeff g i) ---- *)
    embed_zq_coeff g i;                                  (* coeff eg i =eq= embed cgi *)
    assert (coeff eg i = embed_zq_const cgi);

    (* chain: embed cgi = coeff eg i = coeff interp i = sum_range cfn 0 len *)
    assert (embed_zq_const cgi = sum_range #qq #qacg cfn 0 len);

    (* ---- (5) q_abs both sides: embed (iabs cgi) = q_abs (sum_range cfn) ---- *)
    q_abs_well_defined (embed_zq_const cgi) (sum_range #qq #qacg cfn 0 len);
    q_abs_embed cgi;                                     (* q_abs (embed cgi) = embed (iabs cgi) *)
    assert (embed_zq_const (RA.iabs cgi) = q_abs (sum_range #qq #qacg cfn 0 len));

    (* ---- (6) q_abs (sum cfn) <=_q sum (qabs_of cfn) ---- *)
    q_abs_sum_le cfn len;
    assert (q_le (q_abs (sum_range #qq #qacg cfn 0 len))
                 (sum_range #qq #qacg (qabs_of cfn) 0 len));

    (* ---- (7) sum (qabs_of cfn) <=_q sum (embed_kterm_fn) ---- *)
    let pf (j:nat{j < len}) : Lemma
        (q_le (qabs_of cfn j) (embed_kterm_fn bigF int_cs j)) =
      per_term_bound g k bigF int_cs i j sq
    in
    q_le_sum_mono (qabs_of cfn) (embed_kterm_fn bigF int_cs) len pf;
    assert (q_le (sum_range #qq #qacg (qabs_of cfn) 0 len)
                 (sum_range #qq #qacg (embed_kterm_fn bigF int_cs) 0 len));

    (* ---- (8) sum (embed_kterm_fn) =eq= embed (kbound_rhs) ---- *)
    embed_int_sum (kterm bigF int_cs) 0 len;
    assert (sum_range #qq #qacg (embed_kterm_fn bigF int_cs) 0 len
            = embed_zq_const (int_sum (kterm bigF int_cs) 0 len));
    assert (int_sum (kterm bigF int_cs) 0 len == kbound_rhs bigF int_cs);

    (* ---- (9) chain all q_le's: embed (iabs cgi) <=_q embed (kbound_rhs) ---- *)
    (* transport q_abs_sum_le LHS from q_abs(sum cfn) to embed(iabs cgi) *)
    q_le_well_defined (q_abs (sum_range #qq #qacg cfn 0 len))
                      (embed_zq_const (RA.iabs cgi))
                      (sum_range #qq #qacg (qabs_of cfn) 0 len)
                      (sum_range #qq #qacg (qabs_of cfn) 0 len);
    assert (q_le (embed_zq_const (RA.iabs cgi))
                 (sum_range #qq #qacg (qabs_of cfn) 0 len));
    q_le_trans (embed_zq_const (RA.iabs cgi))
               (sum_range #qq #qacg (qabs_of cfn) 0 len)
               (sum_range #qq #qacg (embed_kterm_fn bigF int_cs) 0 len);
    (* transport RHS sum(embed_kterm_fn) to embed (kbound_rhs) *)
    q_le_well_defined (embed_zq_const (RA.iabs cgi))
                      (embed_zq_const (RA.iabs cgi))
                      (sum_range #qq #qacg (embed_kterm_fn bigF int_cs) 0 len)
                      (embed_zq_const (kbound_rhs bigF int_cs));
    assert (q_le (embed_zq_const (RA.iabs cgi))
                 (embed_zq_const (kbound_rhs bigF int_cs)));

    (* ---- (10) descend q_le on embeds to the integer order ---- *)
    q_le_embed (RA.iabs cgi) (kbound_rhs bigF int_cs)
#pop-options
