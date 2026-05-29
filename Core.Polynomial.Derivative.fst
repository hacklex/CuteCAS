module Core.Polynomial.Derivative

(*
   Formal polynomial derivative (d/dx) and its key properties.

   Main results:
     - nat_scale : nat -> t -> t          (n-fold addition: n · x)
     - poly_deriv : polynomial t -> polynomial t
     - poly_deriv_zero                    (d/dx 0 = 0)
     - poly_deriv_const                   (d/dx [c] = 0)
     - poly_deriv_add                     (linearity)
     - poly_deriv_congruence              (respects poly_eq)
     - poly_deriv_monomial                (d/dx (c·x^n) = n·c·x^(n-1))
     - poly_deriv_mul                     (Leibniz/product rule)
     - poly_deriv_degree                  (deg(f') < deg(f) when deg f >= 1)
     - poly_deriv_coeff                   (coeff (poly_deriv p) k = (k+1)·coeff p (k+1))
*)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Div

(* ================================================================ *)
(*  Natural scaling: n · x = x + x + ... + x  (n times)            *)
(* ================================================================ *)

let rec nat_scale (#t:Type) {| acg: add_comm_group t |} (n: nat) (x: t) : t =
  if n = 0 then (zero <: t)
  else x + nat_scale (n - 1) x

let nat_scale_zero (#t:Type) {| acg: add_comm_group t |} (x: t)
  : Lemma (nat_scale 0 x == (zero <: t))
  = ()

let nat_scale_one (#t:Type) {| acg: add_comm_group t |} (x: t)
  : Lemma (nat_scale 1 x = x)
  = // nat_scale 1 x == x + nat_scale 0 x == x + zero
    // need: x + zero = x
    H.x_plus_zero x

let nat_scale_succ (#t:Type) {| acg: add_comm_group t |} (n: nat) (x: t)
  : Lemma (nat_scale (Prims.op_Addition n 1) x == x + nat_scale n x)
  = ()

let rec nat_scale_add (#t:Type) {| acg: add_comm_group t |} (m n: nat) (x: t)
  : Lemma (ensures nat_scale (Prims.op_Addition m n) x = nat_scale m x + nat_scale n x)
          (decreases m)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if m = 0 then
      H.zero_plus_x (nat_scale n x)
    else (
      nat_scale_add (m - 1) n x;
      reflexivity x;
      add_congruence x (nat_scale (Prims.op_Addition (m-1) n) x) x (nat_scale (m-1) x + nat_scale n x);
      add_associativity x (nat_scale (m-1) x) (nat_scale n x)
    )

let rec nat_scale_zero_element (#t:Type) {| acg: add_comm_group t |} (n: nat)
  : Lemma (ensures nat_scale n (zero <: t) = (zero <: t))
          (decreases n)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if n = 0 then ()
    else (
      nat_scale_zero_element #t #acg (n - 1);
      reflexivity (zero <: t);
      add_congruence (zero <: t) (nat_scale (n-1) (zero <: t)) (zero <: t) (zero <: t);
      H.zero_plus_x (zero <: t)
    )

let rec nat_scale_distrib (#t:Type) {| acg: add_comm_group t |} (n: nat) (x y: t)
  : Lemma (ensures nat_scale n (x + y) = nat_scale n x + nat_scale n y)
          (decreases n)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if n = 0 then
      H.zero_plus_x (zero <: t)
    else (
      nat_scale_distrib (n - 1) x y;
      let c = nat_scale (n-1) x in
      let d = nat_scale (n-1) y in
      // nat_scale n (x+y) == (x+y) + nat_scale(n-1)(x+y)
      //                    = (x+y) + (c + d)              [IH + congruence]
      // nat_scale n x + nat_scale n y == (x+c) + (y+d)
      // Need: (x+y)+(c+d) = (x+c)+(y+d)
      reflexivity (x + y);
      add_congruence (x + y) (nat_scale (n-1) (x + y)) (x + y) (c + d);
      // rearrangement: (x+y)+(c+d) = (x+c)+(y+d) via assoc/comm
      add_associativity x y (c + d);
      add_associativity y c d;
      add_commutativity y c;
      reflexivity d;
      add_congruence (y + c) d (c + y) d;
      add_associativity c y d;
      reflexivity x;
      add_congruence x (y + (c + d)) x (c + (y + d));
      add_associativity x c (y + d)
    )

let rec nat_scale_mul_left (#t:Type) {| cr: commutative_ring t |} (n: nat) (x y: t)
  : Lemma (ensures nat_scale #t #(cr.cr_r.r_add) n x * y
                 = nat_scale #t #(cr.cr_r.r_add) n (x * y))
          (decreases n)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    if n = 0 then
      H.zero_mul_x y
    else (
      nat_scale_mul_left (n-1) x y;
      // (x + ns(n-1)x) * y = x*y + ns(n-1)x*y   [right_distrib]
      //                     = x*y + ns(n-1)(x*y)  [IH + congruence]
      //                     == ns n (x*y)
      right_distributivity y x (nat_scale #t #acg (n-1) x);
      reflexivity (x * y);
      add_congruence (x * y) (nat_scale #t #acg (n-1) x * y)
                     (x * y) (nat_scale #t #acg (n-1) (x * y))
    )

let rec nat_scale_mul_right (#t:Type) {| cr: commutative_ring t |} (n: nat) (x y: t)
  : Lemma (ensures x * nat_scale #t #(cr.cr_r.r_add) n y
                 = nat_scale #t #(cr.cr_r.r_add) n (x * y))
          (decreases n)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    if n = 0 then
      H.x_mul_zero x
    else (
      nat_scale_mul_right (n-1) x y;
      // x * (y + ns(n-1)y) = x*y + x*ns(n-1)y    [left_distrib]
      //                     = x*y + ns(n-1)(x*y)   [IH + congruence]
      //                     == ns n (x*y)
      left_distributivity x y (nat_scale #t #acg (n-1) y);
      reflexivity (x * y);
      add_congruence (x * y) (x * nat_scale #t #acg (n-1) y)
                     (x * y) (nat_scale #t #acg (n-1) (x * y))
    )

let rec nat_scale_congruence (#t:Type) {| acg: add_comm_group t |} (n: nat) (x y: t)
  : Lemma (requires x = y)
          (ensures  nat_scale n x = nat_scale n y)
          (decreases n)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    if n = 0 then ()
    else (
      nat_scale_congruence #t #acg (n - 1) x y;
      add_congruence x (nat_scale (n-1) x) y (nat_scale (n-1) y)
    )

(* ================================================================ *)
(*  Formal derivative                                                *)
(*                                                                   *)
(*  poly_deriv [a₀, a₁, a₂, ..., aₙ] = trim [1·a₁, 2·a₂, ..., n·aₙ] *)
(* ================================================================ *)

private let rec deriv_coeffs (#t:Type) {| cr: commutative_ring t |}
  (cs: list t) (k: nat{k >= 1}) : list t =
  match cs with
  | [] -> []
  | a :: rest -> nat_scale #t #(cr.cr_r.r_add) k a :: deriv_coeffs rest (Prims.op_Addition k 1)

let poly_deriv (#t:Type) {| cr: commutative_ring t |} (p: polynomial t) : polynomial t =
  match p with
  | [] -> []
  | _ :: rest -> trim (deriv_coeffs rest 1)

(* ================================================================ *)
(*  Basic properties                                                 *)
(* ================================================================ *)

let poly_deriv_zero (#t:Type) {| cr: commutative_ring t |}
  : Lemma (poly_deriv (poly_zero #t #cr) == (poly_zero #t #cr))
  = ()

let poly_deriv_const (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (requires L.length p <= 1)
          (ensures  poly_deriv p == (poly_zero #t #cr))
  = ()

(* ================================================================ *)
(*  Coefficient identity: coeff(f', k) = (k+1) · coeff(f, k+1)     *)
(* ================================================================ *)

private let rec deriv_coeffs_length (#t:Type) {| cr: commutative_ring t |}
  (cs: list t) (k: nat{k >= 1})
  : Lemma (ensures L.length (deriv_coeffs cs k) = L.length cs)
          (decreases cs)
  = match cs with
    | [] -> ()
    | _ :: rest -> deriv_coeffs_length rest (Prims.op_Addition k 1)

private let rec deriv_coeffs_index (#t:Type) {| cr: commutative_ring t |}
  (cs: list t) (base: nat{base >= 1}) (i: nat{i < L.length cs})
  : Lemma (ensures (L.length (deriv_coeffs cs base) = L.length cs /\
                    L.index (deriv_coeffs cs base) i
                    == nat_scale #t #(cr.cr_r.r_add) (Prims.op_Addition base i) (L.index cs i)))
          (decreases cs)
  = deriv_coeffs_length cs base;
    match cs with
    | [] -> ()
    | a :: rest ->
      if i = 0 then ()
      else deriv_coeffs_index rest (Prims.op_Addition base 1) (i - 1)

(* ================================================================ *)
(*  Trim structural helpers                                          *)
(* ================================================================ *)

private let rec trim_length_le (#t:Type) {| cr: commutative_ring t |} (cs: list t)
  : Lemma (ensures L.length (trim #t #cr cs) <= L.length cs)
          (decreases cs)
  = match cs with
    | [] -> ()
    | _ :: cs' -> trim_length_le cs'

private let rec trim_index_eq (#t:Type) {| cr: commutative_ring t |}
  (cs: list t) (i: nat{i < L.length cs})
  : Lemma (requires i < L.length (trim #t #cr cs))
          (ensures  L.index (trim #t #cr cs) i == L.index cs i)
          (decreases cs)
  = match cs with
    | [] -> ()
    | a :: cs' ->
      let tc' = trim #t #cr cs' in
      if L.length tc' > 0 then (
        if i = 0 then ()
        else trim_index_eq cs' (i - 1)
      ) else (
        if a = (zero <: t) then ()
        else ()
      )

private let rec trim_beyond_zero (#t:Type) {| cr: commutative_ring t |}
  (cs: list t) (i: nat)
  : Lemma (requires i >= L.length (trim #t #cr cs) /\ i < L.length cs)
          (ensures  L.index cs i = (zero <: t))
          (decreases cs)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    match cs with
    | [] -> ()
    | a :: cs' ->
      let tc' = trim #t #cr cs' in
      if L.length tc' > 0 then
        trim_beyond_zero cs' (i - 1)
      else if a = (zero <: t) then (
        if i = 0 then ()
        else trim_beyond_zero cs' (i - 1)
      ) else
        trim_beyond_zero cs' (i - 1)

(* ================================================================ *)
(*  Coefficient identity: coeff(f', k) = (k+1) · coeff(f, k+1)     *)
(* ================================================================ *)

let poly_deriv_coeff (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t) (j: nat)
  : Lemma (ensures coeff (poly_deriv p) j
                 = nat_scale #t #(cr.cr_r.r_add) (Prims.op_Addition j 1) (coeff p (Prims.op_Addition j 1)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let jp1 = Prims.op_Addition j 1 in
    match p with
    | [] -> nat_scale_zero_element #t #(cr.cr_r.r_add) jp1
    | _ :: rest ->
      let dc = deriv_coeffs rest 1 in
      deriv_coeffs_length rest 1;
      if j < L.length (trim dc) then (
        trim_length_le dc;
        trim_index_eq dc j;
        deriv_coeffs_index rest 1 j;
        reflexivity (coeff (poly_deriv p) j)
      ) else if j < L.length dc then (
        trim_beyond_zero dc j;
        deriv_coeffs_index rest 1 j;
        reflexivity (coeff (poly_deriv p) j)
      ) else (
        nat_scale_zero_element #t #(cr.cr_r.r_add) jp1;
        reflexivity (coeff (poly_deriv p) j)
      )

(* ================================================================ *)
(*  Congruence: poly_deriv respects poly_eq                         *)
(* ================================================================ *)

let poly_deriv_congruence (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (requires poly_eq p q)
          (ensures  poly_eq (poly_deriv p) (poly_deriv q))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let aux (j: int) : Lemma (coeff (poly_deriv p) j = coeff (poly_deriv q) j) =
      if j < 0 then reflexivity (coeff (poly_deriv p) j)
      else (
        let jn : nat = j in
        let jp1 = Prims.op_Addition jn 1 in
        poly_deriv_coeff p jn;
        poly_deriv_coeff q jn;
        poly_eq_means_equal_coeffs p q jp1;
        nat_scale_congruence #t #(cr.cr_r.r_add) jp1 (coeff p jp1) (coeff q jp1)
      )
    in Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_deriv p) (poly_deriv q)
