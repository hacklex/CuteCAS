module Core.Risch.LogPartFactored

(*
   M3 / S10 — factor the Rothstein-Trager resultant R(z) into irreducible
   factors and REGROUP the LRT logarithmic part accordingly.

   An LRT `root_sum` (Core.Risch.LRT) denotes the logarithmic answer
       Σ_{β : R(β)=0}  β · log(gcd(p − β·q', q))
   where R = rs_resultant, p = rs_p, q = rs_q, q' = rs_qprime.

   Its VALUE (what the RTSoundness stack proves it denotes) is, at the
   fraction level and relative to a splitting root-list `roots` of R,
       Σ_{β ∈ sub}  residue(β)/(x − β)    =   frac_sum p roots sub
   (Core.Risch.RTSoundness.frac_sum / simple_term / residue), with
   residue(β) = p(β)·inv(q'(β)) taken w.r.t. the FULL denominator q.

   Factoring R = ∏ⱼ Rⱼ partitions its roots  roots(R) = ⊔ⱼ roots(Rⱼ),
   so
       Σ over roots(R)   =   Σⱼ  Σ over roots(Rⱼ)
   which — at the value level — is exactly RTSoundness.frac_sum_flatten:
       frac_sum p roots (flatten groups) = Σⱼ frac_sum p roots groupⱼ.

   This module delivers:
     * regroup            — one root_sum per irreducible factor (executable Tot),
     * collapse_linear    — a deg-1 factor a·z+b collapses to the explicit
                            (β = −b/a, gcd(p − β·q', q)) log term,
     * the algebraic roots-of-product decomposition
         poly_prod (map poly_prod_linears groups) = poly_prod_linears (flatten groups)
       (roots of a product = concatenation of the roots),
     * the value-level regrouping identity (frac_sum_flatten wrapper),
     * a ℚ wrapper factor_log_part obtaining the factorization from factor_Q.

   Generic over {| f: field t |}; only the ℚ wrapper is qq-specific.
   Verify standalone (NOT on build-all).

   NO admit / assume / sorry.
*)

module L   = FStar.List.Tot
module H   = Core.Algebra.Helpers
module LRT = Core.Risch.LRT
module RTS = Core.Risch.RTSoundness
module LP  = Core.Polynomial.LinearPeel
module Z   = Core.Factor.Zassenhaus
module EQ  = Core.Polynomial.EmbedQ
module FR  = Core.Fractions

open Core.NumberTheory
open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Eval
open Core.Polynomial.Roots
open Core.Risch.LRT
open Core.Risch.RTSoundness

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  Deliverable 1 — the regrouped representation.                    *)
(*  We REUSE `root_sum` per factor: one root_sum whose rs_resultant   *)
(*  is the irreducible factor Rⱼ, sharing rs_p / rs_q / rs_qprime.    *)
(* ================================================================ *)

let factored_root_sum (#t:Type) (f: field t) = list (root_sum f)

(* Project the resultant factors carried by a factored representation. *)
let resultants (#t:Type) {| f: field t |} (frs: factored_root_sum f)
  : list (polynomial t)
  = L.map (fun (r:root_sum f) -> r.rs_resultant) frs

(* ================================================================ *)
(*  Deliverable 2 — regroup.  Executable Tot: one root_sum per        *)
(*  factor Rⱼ, keeping the same p / q / q'.                           *)
(*                                                                    *)
(*  The product relation  poly_prod rfs = rs.rs_resultant  is NOT     *)
(*  needed to COMPUTE the regrouping (it is a pure relabelling), so   *)
(*  it is decoupled: it appears only as a hypothesis of the           *)
(*  soundness identities below.  This lets the ℚ wrapper feed the     *)
(*  (soundness-gapped) factor_Q output directly.                      *)
(* ================================================================ *)

let regroup (#t:Type) {| f: field t |} (rs: root_sum f) (rfs: list (polynomial t))
  : factored_root_sum f
  = L.map (fun (rj:polynomial t) -> { rs with rs_resultant = rj }) rfs

(* The resultants of the regrouped list ARE the supplied factors. *)
let rec regroup_resultants (#t:Type) {| f: field t |} (rs: root_sum f) (rfs: list (polynomial t))
  : Lemma (ensures resultants (regroup rs rfs) == rfs)
          (decreases rfs)
  = match rfs with
    | []       -> ()
    | _ :: tl  -> regroup_resultants rs tl

(* Each regrouped root_sum shares p / q / q' and carries the i-th factor. *)
let rec regroup_index (#t:Type) {| f: field t |} (rs: root_sum f) (rfs: list (polynomial t)) (i:nat)
  : Lemma (requires i < L.length rfs)
          (ensures (let rsi = L.index (regroup rs rfs) i in
                    rsi.rs_p == rs.rs_p /\ rsi.rs_q == rs.rs_q /\
                    rsi.rs_qprime == rs.rs_qprime /\
                    rsi.rs_resultant == L.index rfs i))
          (decreases rfs)
  = match rfs with
    | _ :: tl -> if i = 0 then () else regroup_index rs tl (i - 1)

(* ================================================================ *)
(*  Deliverable 3 — collapse_linear.  A linear factor Rⱼ = a·z + b    *)
(*  has the single rational root β = −b/a in the base field; the      *)
(*  term collapses to the explicit  (β, gcd(p − β·q', q)) = β·log(v). *)
(* ================================================================ *)

let collapse_linear (#t:Type) {| f: field t |} (rj: polynomial t{deg rj == 1}) (rs: root_sum f)
  : Pure (t & polynomial t)
         (requires deg rs.rs_q >= 0)
         (ensures fun _ -> True)
  = let beta = LP.linear_root rj in
    (beta, LRT.lrt_log_argument rs.rs_p rs.rs_q rs.rs_qprime beta)

(* β is a genuine root of the linear factor. *)
let collapse_linear_root (#t:Type) {| f: field t |} (rj: polynomial t{deg rj == 1}) (rs: root_sum f)
  : Lemma (requires deg rs.rs_q >= 0)
          (ensures poly_eval rj (fst (collapse_linear rj rs)) = zero)
  = LP.linear_root_is_root rj

(* The collapsed log-argument v is a genuine factor of q (a real log). *)
let collapse_linear_divides_q (#t:Type) {| f: field t |} (rj: polynomial t{deg rj == 1}) (rs: root_sum f)
  : Lemma (requires deg rs.rs_q >= 0)
          (ensures divides (snd (collapse_linear rj rs)) rs.rs_q)
  = LRT.lrt_log_argument_divides_q rs.rs_p rs.rs_q rs.rs_qprime (LP.linear_root rj)

(* ================================================================ *)
(*  Deliverable 4a — roots-of-product decomposition (pure algebra).   *)
(*                                                                    *)
(*  poly_prod_linears distributes over list append:                   *)
(*    ∏(x − a), a ∈ xs @ ys   =   (∏ over xs) · (∏ over ys).          *)
(* ================================================================ *)

let rec poly_prod_linears_append (#t:Type) {| f: field t |} (xs ys: list t)
  : Lemma (ensures (poly_prod_linears (L.append xs ys))
                     = ((poly_prod_linears xs) * (poly_prod_linears ys)))
          (decreases xs)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match xs with
    | [] ->
        (* poly_prod_linears ([]@ys) == poly_prod_linears ys;
           poly_prod_linears [] == poly_one; goal: ppl ys = poly_one * ppl ys. *)
        H.one_mul_x (poly_prod_linears ys);         (* poly_one * ppl ys = ppl ys *)
        symmetry ((poly_one #t) * (poly_prod_linears ys)) (poly_prod_linears ys)
    | a :: rest ->
        let la = poly_linear a in
        let pr = poly_prod_linears rest in
        let py = poly_prod_linears ys in
        (* poly_prod_linears ((a::rest)@ys) == la * poly_prod_linears (rest@ys). *)
        poly_prod_linears_append rest ys;            (* ppl(rest@ys) = pr * py *)
        reflexivity la;
        mul_congruence la (poly_prod_linears (L.append rest ys)) la (pr * py);
        (* la * (pr * py) = (la * pr) * py. *)
        mul_associativity la pr py;
        symmetry ((la * pr) * py) (la * (pr * py));
        transitivity (poly_prod_linears (L.append (a :: rest) ys))
                     (la * (pr * py))
                     ((la * pr) * py)

(* poly_prod of the per-group linear products = the product over the    *)
(* concatenation of all groups' roots.  I.e. R = ∏ⱼ Rⱼ (each Rⱼ split   *)
(* as ∏ over groupⱼ) means R splits as ∏ over (flatten groups).         *)
let rec prod_linears_flatten (#t:Type) {| f: field t |} (groups: list (list t))
  : Lemma (ensures (poly_prod (L.map poly_prod_linears groups))
                     = (poly_prod_linears (L.flatten groups)))
          (decreases groups)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    match groups with
    | [] -> reflexivity (poly_one #t)
    | g :: gs ->
        let pg  = poly_prod_linears g in
        (* poly_prod (map ppl (g::gs)) == pg * poly_prod (map ppl gs). *)
        prod_linears_flatten gs;                     (* poly_prod (map ppl gs) = ppl (flatten gs) *)
        reflexivity pg;
        mul_congruence pg (poly_prod (L.map poly_prod_linears gs))
                       pg (poly_prod_linears (L.flatten gs));
        (* pg * ppl(flatten gs) = ppl (g @ flatten gs) = ppl (flatten (g::gs)). *)
        poly_prod_linears_append g (L.flatten gs);
        symmetry (poly_prod_linears (L.append g (L.flatten gs)))
                 (pg * (poly_prod_linears (L.flatten gs)));
        transitivity (poly_prod (L.map poly_prod_linears groups))
                     (pg * (poly_prod_linears (L.flatten gs)))
                     (poly_prod_linears (L.flatten groups))

(* ================================================================ *)
(*  Deliverable 4b — the value-level regrouping identity.             *)
(*                                                                    *)
(*  With `roots` the splitting root-list of R (residue base) and      *)
(*  `groups` the ordered partition roots(R) = ⊔ roots(Rⱼ) (so         *)
(*  flatten groups lists the roots factor-by-factor), the LRT log     *)
(*  VALUE summed over roots(R) equals Σⱼ the value summed over        *)
(*  roots(Rⱼ):                                                        *)
(*    frac_sum p roots (flatten groups) = frac_sum_over_groups p roots groups. *)
(*                                                                    *)
(*  Each summand  frac_sum p roots groupⱼ  is the log value of the    *)
(*  j-th regrouped root_sum (same p, residue over the full roots).    *)
(*  Directly RTSoundness.frac_sum_flatten (reoriented).               *)
(* ================================================================ *)

let regroup_frac_sum (#t:Type) {| f: field t |} (p: polynomial t) (roots: list t) (groups: list (list t))
  : Lemma (requires (forall (g:list t). L.memP g groups ==>
                        (forall (b:t). L.memP b g ==> L.memP b roots)) /\
                    all_distinct roots)
          (ensures (RTS.frac_sum p roots (L.flatten groups))
                     = (RTS.frac_sum_over_groups p roots groups))
  = H.elim_equatable_laws (FR.fraction (polynomial_id #t)) ();
    RTS.frac_sum_flatten p roots groups;
    symmetry (RTS.frac_sum_over_groups p roots groups)
             (RTS.frac_sum p roots (L.flatten groups))

(* ================================================================ *)
(*  Deliverable 5 — ℚ wrapper.                                        *)
(*                                                                    *)
(*  Obtain the factorization of the resultant R ∈ ℚ[z] from           *)
(*  Core.Factor.Zassenhaus.factor_Q, then regroup.  factor_Q's        *)
(*  soundness (factor_Q_sound / factor_Q_associate) gives each factor *)
(*  dividing R up to a nonzero ℚ-unit; the full product relation is a *)
(*  COMPLETENESS property (R2-gapped in the Zassenhaus stage), so the *)
(*  soundness identities above are applied under that hypothesis.     *)
(* ================================================================ *)

let qq_field : field EQ.qq = FR.fraction_field int int_id

let factor_log_part (rs: root_sum #EQ.qq qq_field)
                    (primes: list (p:int{is_prime p}))
  : factored_root_sum #EQ.qq qq_field
  = regroup #EQ.qq #qq_field rs (Z.factor_Q rs.rs_resultant primes)

(* The ℚ regrouping carries exactly the factor_Q factors as resultants. *)
let factor_log_part_resultants (rs: root_sum #EQ.qq qq_field)
                               (primes: list (p:int{is_prime p}))
  : Lemma (resultants (factor_log_part rs primes)
             == Z.factor_Q rs.rs_resultant primes)
  = regroup_resultants #EQ.qq #qq_field rs (Z.factor_Q rs.rs_resultant primes)

(* Collapse the deg-1 (rational-root) factors of a factored answer to    *)
(* explicit β·log(v) terms; keep the higher-degree factors as RootSums.  *)
let collapse_if_linear (#t:Type) {| f: field t |} (rs: root_sum f)
  : Pure (either (t & polynomial t) (root_sum f))
         (requires deg rs.rs_q >= 0)
         (ensures fun _ -> True)
  = if deg rs.rs_resultant = 1
    then Inl (collapse_linear rs.rs_resultant rs)
    else Inr rs
