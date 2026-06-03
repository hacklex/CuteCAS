module Core.Polynomial.EvalSum

(* ================================================================ *)
(*  poly_eval (evaluation at c) commutes with finite sums/products   *)
(*  over a range:  it is a ring homomorphism polynomial t -> t       *)
(*  (Core.Polynomial.Eval, #15), so it carries through `sum_range`   *)
(*  and `prod_range`.  Foundation for the DETERMINANT SPECIALIZATION *)
(*  (plan §5.1.b): det commutes with eval => resultant specialization*)
(*  R(c) = res_x(p - c*q', q).                                       *)
(*                                                                   *)
(*  The polynomial sum/product use `polynomial_acg cr` /             *)
(*  `(polynomial_commutative_ring_instance).pcr.cr_r`, whose add/mul  *)
(*  fields ARE poly_add / poly_mul, matching Eval's eval_add/eval_mul.*)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Eval
open Core.FinSum

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* eval (sum_range g lo hi) = sum_range (eval . g) lo hi. *)
let rec eval_sum_range (#t:Type) {| cr: commutative_ring t |}
  (g: nat -> polynomial t) (c: t) (lo hi: nat)
  : Lemma (ensures poly_eval #t #cr
                     (sum_range #(polynomial t) #(polynomial_acg cr) g lo hi) c
                   = sum_range #t #(cr.cr_r.r_add) (fun (i:nat) -> poly_eval #t #cr (g i) c) lo hi)
          (decreases (hi - lo))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let evg = (fun (i:nat) -> poly_eval #t #cr (g i) c) in
    if lo >= hi then begin
      sum_range_empty #(polynomial t) #(polynomial_acg cr) g lo hi;
      sum_range_empty #t #(cr.cr_r.r_add) evg lo hi;
      eval_zero #t #cr c
    end else begin
      let rest = sum_range #(polynomial t) #(polynomial_acg cr) g (nat_succ lo) hi in
      let sum' = sum_range #t #(cr.cr_r.r_add) evg (nat_succ lo) hi in
      sum_range_unfold_left #(polynomial t) #(polynomial_acg cr) g lo hi;  (* sum == poly_add (g lo) rest *)
      sum_range_unfold_left #t #(cr.cr_r.r_add) evg lo hi;
      eval_add #t #cr (g lo) rest c;                       (* eval (poly_add (g lo) rest) = eval(g lo) + eval rest *)
      eval_sum_range #t #cr g c (nat_succ lo) hi;           (* IH: eval rest = sum' *)
      reflexivity (poly_eval #t #cr (g lo) c);
      add_congruence #t #(cr.cr_r.r_add)
                     (poly_eval #t #cr (g lo) c) (poly_eval #t #cr rest c)
                     (poly_eval #t #cr (g lo) c) sum';
      transitivity (poly_eval #t #cr (poly_add (g lo) rest) c)
                   (add #t #(cr.cr_r.r_add) (poly_eval #t #cr (g lo) c) (poly_eval #t #cr rest c))
                   (add #t #(cr.cr_r.r_add) (poly_eval #t #cr (g lo) c) sum')
    end

(* eval (prod_range g lo hi) = prod_range (eval . g) lo hi. *)
let rec eval_prod_range (#t:Type) {| cr: commutative_ring t |}
  (g: nat -> polynomial t) (c: t) (lo hi: nat)
  : Lemma (ensures poly_eval #t #cr
                     (prod_range #(polynomial t)
                        #((polynomial_commutative_ring_instance #t #cr).pcr.cr_r) g lo hi) c
                   = prod_range #t #(cr.cr_r) (fun (i:nat) -> poly_eval #t #cr (g i) c) lo hi)
          (decreases (hi - lo))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let pring = (polynomial_commutative_ring_instance #t #cr).pcr.cr_r in
    let evg = (fun (i:nat) -> poly_eval #t #cr (g i) c) in
    if lo >= hi then begin
      prod_range_empty #(polynomial t) #pring g lo hi;       (* == one == poly_one *)
      prod_range_empty #t #(cr.cr_r) evg lo hi;
      eval_one #t #cr c                                      (* poly_eval poly_one c = one *)
    end else begin
      let rest = prod_range #(polynomial t) #pring g (nat_succ lo) hi in
      let prod' = prod_range #t #(cr.cr_r) evg (nat_succ lo) hi in
      prod_range_unfold_left #(polynomial t) #pring g lo hi;  (* prod == poly_mul (g lo) rest *)
      prod_range_unfold_left #t #(cr.cr_r) evg lo hi;
      eval_mul #t #cr (g lo) rest c;                          (* eval (poly_mul (g lo) rest) = eval(g lo)*eval rest *)
      eval_prod_range #t #cr g c (nat_succ lo) hi;            (* IH *)
      reflexivity (poly_eval #t #cr (g lo) c);
      mul_congruence #t #(cr.cr_r)
                     (poly_eval #t #cr (g lo) c) (poly_eval #t #cr rest c)
                     (poly_eval #t #cr (g lo) c) prod';
      transitivity (poly_eval #t #cr (poly_mul (g lo) rest) c)
                   (mul #t #(cr.cr_r) (poly_eval #t #cr (g lo) c) (poly_eval #t #cr rest c))
                   (mul #t #(cr.cr_r) (poly_eval #t #cr (g lo) c) prod')
    end

(* eval (sum_list xs) = sum_list (map (eval . _) xs).
   (sum_over_perms is sum_list over the permutation enumeration, so this is
    the bridge for the determinant specialization.) *)
let rec eval_sum_list (#t:Type) {| cr: commutative_ring t |}
  (xs: list (polynomial t)) (c: t)
  : Lemma (ensures poly_eval #t #cr (sum_list #(polynomial t) #(polynomial_acg cr) xs) c
                   = sum_list #t #(cr.cr_r.r_add)
                       (L.map (fun (p: polynomial t) -> poly_eval #t #cr p c) xs))
          (decreases xs)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match xs with
    | [] ->
      sum_list_nil #(polynomial t) #(polynomial_acg cr);
      sum_list_nil #t #(cr.cr_r.r_add);
      eval_zero #t #cr c
    | p :: rest ->
      let prest = sum_list #(polynomial t) #(polynomial_acg cr) rest in
      let srest = sum_list #t #(cr.cr_r.r_add)
                    (L.map (fun (q: polynomial t) -> poly_eval #t #cr q c) rest) in
      sum_list_cons #(polynomial t) #(polynomial_acg cr) p rest;   (* sum == poly_add p prest *)
      sum_list_cons #t #(cr.cr_r.r_add) (poly_eval #t #cr p c)
                    (L.map (fun (q: polynomial t) -> poly_eval #t #cr q c) rest);
      eval_add #t #cr p prest c;                                   (* eval (poly_add p prest) = eval p + eval prest *)
      eval_sum_list #t #cr rest c;                                 (* IH *)
      reflexivity (poly_eval #t #cr p c);
      add_congruence #t #(cr.cr_r.r_add)
                     (poly_eval #t #cr p c) (poly_eval #t #cr prest c)
                     (poly_eval #t #cr p c) srest;
      transitivity (poly_eval #t #cr (poly_add p prest) c)
                   (add #t #(cr.cr_r.r_add) (poly_eval #t #cr p c) (poly_eval #t #cr prest c))
                   (add #t #(cr.cr_r.r_add) (poly_eval #t #cr p c) srest)
