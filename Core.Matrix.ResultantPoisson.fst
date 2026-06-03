module Core.Matrix.ResultantPoisson

(*
   Poisson product formula for the resultant (step 4).

   For a polynomial presented as a PROVIDED factorization

       A  =  lc * (x - a1) * (x - a2) * ... * (x - ak)

   (leading coefficient `lc`, root list `[a1; ...; ak]`), and any nonzero B,

       Res(A, B)  =  cpow lc (deg B)  *  prod_i (poly_eval B ai).

   We do NOT construct a splitting field: the factorization is an input.
   The polynomial A is built by  `scaled_prod lc roots`  (the linear factors
   folded on the outside of the constant [lc]), so that

       scaled_prod lc (a :: rest) == poly_mul (poly_linear a) (scaled_prod lc rest),

   which lets the peeling lemma peel one  (x - a)  per induction step,
   contributing  poly_eval B a;  the base case  scaled_prod lc [] = [lc]  gives
   `Res_{0,n}([lc], B) = cpow lc n` by `resultant_const`.

   Formal degree of `scaled_prod lc roots` is `length roots` (each linear is
   monic degree 1, lc nonzero), so the resultant is taken at  m_deg = length
   roots  and  n_deg = n (>= deg B).
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Helpers
open Core.Matrix
open Core.Matrix.Sylvester
open Core.Matrix.Resultant
open Core.Matrix.ResultantLinear
open Core.Matrix.ResultantPeel
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Unique
open Core.Polynomial.Eval
open Core.Polynomial.Root
open Core.Polynomial.Product
open Core.Tactics.CanonRing

(* ================================================================ *)
(*  The provided factorization  A = lc * prod (x - ai).             *)
(*  Linear factors folded on the OUTSIDE so the head peels first.    *)
(* ================================================================ *)

let rec scaled_prod (#t:Type) {| f: field t |} (lc: t{not (lc = (zero <: t))}) (roots: list t)
  : Tot (polynomial t) (decreases roots)
  = match roots with
    | []        -> ([lc] <: polynomial t)
    | a :: rest -> poly_mul (poly_linear #t #f a) (scaled_prod #t #f lc rest)

(* ring rearrangement:  x * (y * z) = y * (x * z)  *)
let mul_swap_mid (#t:Type) {| cr: commutative_ring t |} (x y z: t)
  : Lemma (x * (y * z) = y * (x * z))
  = assert (x * (y * z) = y * (x * z)) by canon_ring ()

(* The Poisson right-hand side:  prod_i (poly_eval b ai). *)
let rec root_eval_product (#t:Type) {| f: field t |} (b: polynomial t) (roots: list t)
  : Tot t (decreases roots)
  = match roots with
    | []        -> one #t
    | a :: rest -> poly_eval b a * root_eval_product #t #f b rest

(* ================================================================ *)
(*  Degree of the provided factorization.                           *)
(*    poly_deg (scaled_prod lc roots) = Some (length roots)   (lc<>0) *)
(*  hence  L.length (scaled_prod lc roots) = length roots + 1.       *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 2"
let rec scaled_prod_degree (#t:Type) {| f: field t |} (lc: t{not (lc = (zero <: t))}) (roots: list t)
  : Lemma (ensures Some? (poly_deg (scaled_prod #t #f lc roots)) /\
                   Some?.v (poly_deg (scaled_prod #t #f lc roots)) == L.length roots)
          (decreases roots)
  = let id_t : integral_domain t = id_of_f t in
    match roots with
    | []        ->
        (* scaled_prod = [lc], lc <> 0, so poly_deg = Some 0 *)
        ()
    | a :: rest ->
        scaled_prod_degree #t #f lc rest;                 (* deg (scaled_prod rest) = length rest *)
        poly_linear_deg #t #f a;                          (* deg (x-a) = Some 1 *)
        degree_mul #t #id_t (poly_linear #t #f a) (scaled_prod #t #f lc rest)
        (* deg (poly_mul (x-a) (scaled_prod rest)) = 1 + length rest = length (a::rest) *)
#pop-options

let scaled_prod_length (#t:Type) {| f: field t |} (lc: t{not (lc = (zero <: t))}) (roots: list t)
  : Lemma (L.length (scaled_prod #t #f lc roots) <= Prims.op_Addition (L.length roots) 1)
  = scaled_prod_degree #t #f lc roots
    (* poly_deg p = Some (L.length p - 1) on nonempty p; deg = length roots,
       so L.length p = length roots + 1. *)

(* ================================================================ *)
(*  THE POISSON PRODUCT FORMULA.                                     *)
(*                                                                   *)
(*    Res_{k, n}(scaled_prod lc roots, B)                            *)
(*      =  cpow lc n  *  prod_i (poly_eval B ai)                     *)
(*                                                                   *)
(*  where  k = length roots,  n >= deg B,  lc nonzero, B nonzero.    *)
(*  Induction on the root list:  head peels via `peel` (factor       *)
(*  poly_eval B a), base case `resultant_const` (cpow lc n).         *)
(* ================================================================ *)

#push-options "--z3rlimit 200 --fuel 2 --ifuel 2"
let rec poisson (#t:Type) {| f: field t |} (lc: t{not (lc = (zero <: t))}) (roots: list t)
  (b: polynomial t) (n: nat{n >= 1})
  : Lemma (requires Some? (poly_deg b) /\ Some?.v (poly_deg b) <= n)
          (ensures (let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
                    resultant #t #cr (L.length roots) n (scaled_prod #t #f lc roots) b
                  = cpow lc n * root_eval_product #t #f b roots))
          (decreases roots)
  = let cr : commutative_ring t = cr_of_id t #(id_of_f t) in
    H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match roots with
    | []        ->
        (* Res_{0,n}([lc], B) = cpow lc n = cpow lc n * one = cpow lc n * root_eval_product b [] *)
        resultant_const #t #f lc b n;                     (* Res_{0,n}([lc],B) = cpow lc n *)
        H.x_mul_one (cpow lc n);                          (* cpow lc n * one = cpow lc n *)
        symmetry (cpow lc n * (one <: t)) (cpow lc n);
        transitivity (resultant #t #cr (L.length roots) n (scaled_prod #t #f lc roots) b)
                     (cpow lc n) (cpow lc n * (one <: t))
    | a :: rest ->
        let arest = scaled_prod #t #f lc rest in
        (* peel one (x-a) factor:
             Res_{m'+1,n}((x-a)*arest, B) = poly_eval B a * Res_{m',n}(arest, B),
           with m' = length rest. *)
        scaled_prod_length #t #f lc rest;                 (* L.length arest <= length rest + 1 *)
        peel #t #f a arest b (L.length rest) n;
        (* IH: Res_{m',n}(arest, B) = cpow lc n * root_eval_product B rest *)
        poisson #t #f lc rest b n;
        let m' = L.length rest in
        let resA  = resultant #t #cr (Prims.op_Addition m' 1) n
                              (poly_mul (poly_linear #t #f a) arest) b in
        let resA' = resultant #t #cr m' n arest b in
        let rep   = root_eval_product #t #f b rest in
        (* resA = poly_eval b a * resA'  (peel) *)
        (* resA' = cpow lc n * rep        (IH) *)
        reflexivity (poly_eval b a);
        mul_congruence (poly_eval b a) resA' (poly_eval b a) (cpow lc n * rep);
        transitivity resA (poly_eval b a * resA') (poly_eval b a * (cpow lc n * rep));
        (* rearrange  poly_eval b a * (cpow lc n * rep)  =  cpow lc n * (poly_eval b a * rep) *)
        mul_swap_mid (poly_eval b a) (cpow lc n) rep;
        transitivity resA (poly_eval b a * (cpow lc n * rep)) (cpow lc n * (poly_eval b a * rep))
#pop-options
