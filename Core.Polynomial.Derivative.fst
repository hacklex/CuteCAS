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

(* ================================================================ *)
(*  Linearity: poly_deriv (p + q) = poly_deriv p + poly_deriv q     *)
(* ================================================================ *)

let poly_deriv_add (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (ensures poly_eq (poly_deriv (poly_add p q))
                           (poly_add (poly_deriv p) (poly_deriv q)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let aux (j: int) : Lemma (coeff (poly_deriv (poly_add p q)) j
                            = coeff (poly_add (poly_deriv p) (poly_deriv q)) j) =
      if j < 0 then reflexivity (coeff (poly_deriv (poly_add p q)) j)
      else (
        let jn : nat = j in
        let jp1 = Prims.op_Addition jn 1 in
        let acg = cr.cr_r.r_add in
        // Step 1: coeff(D(p+q), j) = nat_scale(j+1, coeff(p+q, j+1))
        poly_deriv_coeff (poly_add p q) jn;
        // Step 2: coeff(p+q, j+1) = coeff(p, j+1) + coeff(q, j+1)
        poly_add_coeff p q jp1;
        // Step 3: nat_scale(j+1, coeff(p+q, j+1)) = nat_scale(j+1, coeff(p,j+1) + coeff(q,j+1))
        nat_scale_congruence #t #acg jp1 (coeff (poly_add p q) jp1) (coeff p jp1 + coeff q jp1);
        // Step 4: nat_scale(j+1, coeff(p,j+1)+coeff(q,j+1)) = nat_scale(j+1, coeff(p,j+1)) + nat_scale(j+1, coeff(q,j+1))
        nat_scale_distrib #t #acg jp1 (coeff p jp1) (coeff q jp1);
        // Step 5,6: coeff(D(p), j) = nat_scale(j+1, coeff(p,j+1)), same for q
        poly_deriv_coeff p jn;
        poly_deriv_coeff q jn;
        // Step 7: nat_scale(j+1, coeff(p,j+1)) + nat_scale(j+1, coeff(q,j+1)) = coeff(D(p),j) + coeff(D(q),j)
        symmetry (coeff (poly_deriv p) jn) (nat_scale #t #acg jp1 (coeff p jp1));
        symmetry (coeff (poly_deriv q) jn) (nat_scale #t #acg jp1 (coeff q jp1));
        add_congruence (nat_scale #t #acg jp1 (coeff p jp1)) (nat_scale #t #acg jp1 (coeff q jp1))
                       (coeff (poly_deriv p) jn) (coeff (poly_deriv q) jn);
        // Step 8: coeff(D(p)+D(q), j) = coeff(D(p), j) + coeff(D(q), j)
        poly_add_coeff (poly_deriv p) (poly_deriv q) jn;
        symmetry (coeff (poly_add (poly_deriv p) (poly_deriv q)) jn)
                 (coeff (poly_deriv p) jn + coeff (poly_deriv q) jn);
        // Chain: coeff(D(p+q), j) → ... → coeff(D(p)+D(q), j)
        let a = coeff (poly_deriv (poly_add p q)) jn in
        let b = nat_scale #t #acg jp1 (coeff (poly_add p q) jp1) in
        let c = nat_scale #t #acg jp1 (coeff p jp1 + coeff q jp1) in
        let d = nat_scale #t #acg jp1 (coeff p jp1) + nat_scale #t #acg jp1 (coeff q jp1) in
        let e = coeff (poly_deriv p) jn + coeff (poly_deriv q) jn in
        let f = coeff (poly_add (poly_deriv p) (poly_deriv q)) jn in
        transitivity a b c;
        transitivity a c d;
        transitivity a d e;
        transitivity a e f
      )
    in Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_deriv (poly_add p q))
                               (poly_add (poly_deriv p) (poly_deriv q))

(* ================================================================ *)
(*  nat_scale distributes over negation: n · (-x) = -(n · x)       *)
(* ================================================================ *)

let nat_scale_neg (#t:Type) {| acg: add_comm_group t |} (n: nat) (x: t)
  : Lemma (ensures nat_scale n (neg x) = neg (nat_scale n x))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let a = nat_scale n x in
    let b = nat_scale n (neg x) in
    nat_scale_distrib n x (neg x);
    (* nat_scale n (x + neg x) = a + b *)
    H.x_plus_neg_x x;
    (* x + neg x = zero *)
    nat_scale_congruence n (x + neg x) (zero <: t);
    (* nat_scale n (x + neg x) = nat_scale n zero *)
    nat_scale_zero_element #t #acg n;
    (* nat_scale n zero = zero *)
    symmetry (nat_scale n (x + neg x)) (a + b);
    transitivity (a + b) (nat_scale n (x + neg x)) (nat_scale #t #acg n (zero <: t));
    transitivity (a + b) (nat_scale #t #acg n (zero <: t)) (zero <: t);
    (* Also: a + neg a = zero *)
    H.x_plus_neg_x a;
    (* So a + b = zero = a + neg a *)
    symmetry (a + neg a) (zero <: t);
    transitivity (a + b) (zero <: t) (a + neg a);
    H.group_cancel_left a b (neg a)

(* ================================================================ *)
(*  Derivative of negation: D(-p) = -(D(p))                         *)
(* ================================================================ *)

let poly_deriv_neg (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t)
  : Lemma (ensures poly_eq (poly_deriv (poly_neg p))
                          (poly_neg (poly_deriv p)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let dp = poly_deriv p in
    let np = poly_neg p in
    let dnp = poly_deriv np in
    let ndp = poly_neg dp in
    let acg = cr.cr_r.r_add in
    let aux (j: nat)
      : Lemma (coeff dnp j = coeff ndp j)
      = let jn = Prims.op_Addition j 1 in
        poly_deriv_coeff np j;
        (* a = b: coeff(D(neg p), j) = nat_scale(j+1, coeff(neg p, j+1)) *)
        poly_neg_coeff p jn;
        (* coeff(neg p, j+1) = neg(coeff(p, j+1)) *)
        nat_scale_congruence #t #acg jn (coeff np jn) (neg (coeff p jn));
        (* b = c: nat_scale(j+1, coeff(neg p, j+1)) = nat_scale(j+1, neg(coeff(p, j+1))) *)
        nat_scale_neg #t #acg jn (coeff p jn);
        (* c = d: nat_scale(j+1, neg(coeff(p, j+1))) = neg(nat_scale(j+1, coeff(p, j+1))) *)
        poly_deriv_coeff p j;
        (* coeff(D(p), j) = nat_scale(j+1, coeff(p, j+1)) *)
        symmetry (coeff dp j) (nat_scale #t #acg jn (coeff p jn));
        neg_congruence (nat_scale #t #acg jn (coeff p jn)) (coeff dp j);
        (* d = e: neg(nat_scale(...)) = neg(coeff(D(p), j)) *)
        poly_neg_coeff dp j;
        (* e = f: neg(coeff(D(p), j)) = coeff(neg(D(p)), j) *)
        symmetry (coeff ndp j) (neg (coeff dp j));
        (* f = e reversed for chain direction *)
        let a = coeff dnp j in
        let b = nat_scale #t #acg jn (coeff np jn) in
        let c = nat_scale #t #acg jn (neg (coeff p jn)) in
        let d = neg (nat_scale #t #acg jn (coeff p jn)) in
        let e = neg (coeff dp j) in
        let f = coeff ndp j in
        transitivity a b c;
        transitivity a c d;
        transitivity a d e;
        transitivity a e f
    in Classical.forall_intro aux;
    equal_coeffs_means_poly_eq dnp ndp

(* ================================================================ *)
(*  Derivative of subtraction: D(p - q) = D(p) - D(q)              *)
(* ================================================================ *)

let poly_deriv_sub (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (ensures poly_eq (poly_deriv (poly_sub p q))
                          (poly_sub (poly_deriv p) (poly_deriv q)))
  = let nq = poly_neg q in
    let dp = poly_deriv p in
    let dq = poly_deriv q in
    (* Reveal: poly_sub x y == poly_add x (poly_neg y) *)
    poly_sub_reveal p q;
    poly_sub_reveal dp dq;
    (* Now poly_deriv (poly_sub p q) == poly_deriv (poly_add p nq)
       and  poly_sub dp dq == poly_add dp (poly_neg dq). *)
    (* D(p + neg q) ≈ D(p) + D(neg q) *)
    poly_deriv_add p nq;
    (* D(neg q) ≈ neg(D(q)) *)
    poly_deriv_neg q;
    (* D(p) + D(neg q) ≈ D(p) + neg(D(q)) by congruence *)
    poly_eq_reflexivity dp;
    poly_add_congruence dp (poly_deriv nq) dp (poly_neg dq);
    (* Chain: poly_deriv(poly_add p nq) ≈ poly_add dp (poly_deriv nq)
                                       ≈ poly_add dp (poly_neg dq) *)
    poly_eq_transitivity
      (poly_deriv (poly_add p nq))
      (poly_add dp (poly_deriv nq))
      (poly_add dp (poly_neg dq))

(* ================================================================ *)
(*  Product rule helpers                                             *)
(* ================================================================ *)

(* Coefficient of the shifted polynomial zero@f:
   coeff(zero@f, 0) = zero, coeff(zero@f, k+1) = coeff(f, k). *)
let coeff_shift (#t:Type) {| cr: commutative_ring t |} (f: polynomial t) (k: nat)
  : Lemma (coeff ((zero <: t) @ f) k = (if k = 0 then (zero <: t) else coeff f (k - 1)))
  = H.elim_equatable_laws t ();
    match f with
    | [] -> (* zero@[] = [], coeff([],k) = zero for all k *)
        if k = 0 then reflexivity (zero <: t)
        else reflexivity (zero <: t)
    | _ :: _ -> (* zero@(b::rest) = zero::b::rest *)
        if k = 0 then reflexivity (zero <: t)
        else reflexivity (coeff f (k - 1))

(* Derivative commutes with scalar multiplication:
   D([c] · q) ≈ [c] · D(q).
   Proof: coefficient comparison using nat_scale_mul_right. *)
let poly_deriv_scalar_mul (#t:Type) {| cr: commutative_ring t |}
  (c: t) (q: polynomial t)
  : Lemma (ensures poly_eq (poly_deriv (poly_mul (c @ poly_zero) q))
                           (poly_mul (c @ poly_zero) (poly_deriv q)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    let cq : polynomial t = poly_mul (c @ poly_zero) q in
    let dq : polynomial t = poly_deriv q in
    let cdq : polynomial t = poly_mul (c @ poly_zero) dq in
    let dcq : polynomial t = poly_deriv cq in
    let aux (k: nat) : Lemma (coeff dcq k = coeff cdq k) =
      let kp1 = Prims.op_Addition k 1 in
      (* coeff(dcq, k) = nat_scale(k+1)(coeff(cq, k+1)) *)
      poly_deriv_coeff cq k;
      (* coeff(cq, k+1) = c * coeff(q, k+1) *)
      poly_mul_singleton_coeff c q kp1;
      (* So coeff(dcq, k) = nat_scale(k+1)(c * coeff(q, k+1)) *)
      nat_scale_congruence #t #acg kp1 (coeff cq kp1) (c * coeff q kp1);
      (* coeff(cdq, k) = c * coeff(dq, k) *)
      poly_mul_singleton_coeff c dq k;
      (* coeff(dq, k) = nat_scale(k+1)(coeff(q, k+1)) *)
      poly_deriv_coeff q k;
      (* So coeff(cdq, k) = c * nat_scale(k+1)(coeff(q, k+1)) *)
      mul_congruence c (coeff dq k) c (nat_scale #t #acg kp1 (coeff q kp1));
      (* nat_scale(k+1)(c * coeff(q,k+1)) = c * nat_scale(k+1)(coeff(q,k+1))
         by nat_scale_mul_right *)
      nat_scale_mul_right kp1 c (coeff q kp1);
      (* Chain the equalities *)
      transitivity (coeff dcq k) (nat_scale #t #acg kp1 (coeff cq kp1))
                   (nat_scale #t #acg kp1 (c * coeff q kp1));
      transitivity (coeff dcq k) (nat_scale #t #acg kp1 (c * coeff q kp1))
                   (c * nat_scale #t #acg kp1 (coeff q kp1));
      symmetry (coeff cdq k) (c * coeff dq k);
      transitivity (c * coeff dq k) (c * nat_scale #t #acg kp1 (coeff q kp1))
                   (coeff cdq k);
      symmetry (coeff dcq k) (c * nat_scale #t #acg kp1 (coeff q kp1));
      transitivity (coeff dcq k)
                   (c * nat_scale #t #acg kp1 (coeff q kp1))
                   (coeff cdq k)
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq dcq cdq

(* Shift distributes over addition: zero@(A+B) ≈ (zero@A) + (zero@B).
   Proof by coefficient comparison. *)
let shift_add (#t:Type) {| cr: commutative_ring t |}
  (a b: polynomial t)
  : Lemma (poly_eq ((zero <: t) @ (poly_add a b))
                   (poly_add ((zero <: t) @ a) ((zero <: t) @ b)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let lhs : polynomial t = (zero <: t) @ (poly_add a b) in
    let rhs : polynomial t = poly_add ((zero <: t) @ a) ((zero <: t) @ b) in
    let aux (k: nat) : Lemma (coeff lhs k = coeff rhs k) =
      coeff_shift (poly_add a b) k;
      poly_add_coeff ((zero <: t) @ a) ((zero <: t) @ b) k;
      coeff_shift a k;
      coeff_shift b k;
      if k = 0 then (
        (* lhs: zero. rhs: coeff(0@a,0) + coeff(0@b,0) = zero + zero = zero *)
        add_congruence (coeff ((zero <: t) @ a) k) (coeff ((zero <: t) @ b) k)
                       (zero <: t) (zero <: t);
        H.zero_plus_x (zero <: t);
        transitivity (coeff rhs k) (coeff ((zero <: t) @ a) k + coeff ((zero <: t) @ b) k)
                     ((zero <: t) + (zero <: t));
        transitivity (coeff rhs k) ((zero <: t) + (zero <: t)) (zero <: t);
        symmetry (coeff rhs k) (zero <: t);
        transitivity (coeff lhs k) (zero <: t) (coeff rhs k)
      ) else (
        (* lhs: coeff(a+b, k-1). rhs: coeff(a,k-1) + coeff(b,k-1) *)
        poly_add_coeff a b (k - 1);
        (* coeff(a+b,k-1) = coeff(a,k-1) + coeff(b,k-1) *)
        add_congruence (coeff ((zero <: t) @ a) k) (coeff ((zero <: t) @ b) k)
                       (coeff a (k-1)) (coeff b (k-1));
        transitivity (coeff rhs k)
          (coeff ((zero <: t) @ a) k + coeff ((zero <: t) @ b) k)
          (coeff a (k-1) + coeff b (k-1));
        symmetry (coeff rhs k) (coeff a (k-1) + coeff b (k-1));
        transitivity (coeff lhs k) (coeff a (k-1) + coeff b (k-1)) (coeff rhs k)
      )
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* Derivative of shifted polynomial: D(zero@f) ≈ f + zero@D(f).
   This is the formal version of D(x·f(x)) = f(x) + x·f'(x).
   Proof by coefficient comparison using nat_scale_add. *)
let poly_deriv_shift (#t:Type) {| cr: commutative_ring t |}
  (f: polynomial t)
  : Lemma (poly_eq (poly_deriv ((zero <: t) @ f))
                   (poly_add f ((zero <: t) @ (poly_deriv f))))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    let xf : polynomial t = (zero <: t) @ f in
    let df : polynomial t = poly_deriv f in
    let lhs : polynomial t = poly_deriv xf in
    let rhs : polynomial t = poly_add f ((zero <: t) @ df) in
    let aux (k: nat) : Lemma (coeff lhs k = coeff rhs k) =
      let kp1 = Prims.op_Addition k 1 in
      (* coeff(lhs, k) = nat_scale(k+1)(coeff(xf, k+1)) *)
      poly_deriv_coeff xf k;
      (* coeff(xf, k+1) = coeff(f, k) since k+1 >= 1 *)
      coeff_shift f kp1;
      assert (kp1 <> 0);
      nat_scale_congruence #t #acg kp1 (coeff xf kp1) (coeff f k);
      transitivity (coeff lhs k) (nat_scale #t #acg kp1 (coeff xf kp1))
                   (nat_scale #t #acg kp1 (coeff f k));
      (* coeff(rhs, k) = coeff(f, k) + coeff(zero@df, k) *)
      poly_add_coeff f ((zero <: t) @ df) k;
      coeff_shift df k;
      if k = 0 then (
        (* coeff(zero@df, 0) = zero. rhs = coeff(f,0) + zero = coeff(f,0) *)
        add_congruence (coeff f 0) (coeff ((zero <: t) @ df) 0) (coeff f 0) (zero <: t);
        H.x_plus_zero (coeff f 0);
        transitivity (coeff rhs 0) (coeff f 0 + coeff ((zero <: t) @ df) 0)
                     (coeff f 0 + (zero <: t));
        transitivity (coeff rhs 0) (coeff f 0 + (zero <: t)) (coeff f 0);
        (* lhs: nat_scale 1 (coeff f 0) = coeff f 0 *)
        nat_scale_one #t #acg (coeff f 0);
        symmetry (coeff rhs 0) (coeff f 0);
        transitivity (coeff lhs 0) (nat_scale #t #acg 1 (coeff f 0)) (coeff f 0);
        transitivity (coeff lhs 0) (coeff f 0) (coeff rhs 0)
      ) else (
        (* coeff(zero@df, k) = coeff(df, k-1) = nat_scale k (coeff f k)  *)
        poly_deriv_coeff f (k - 1);
        assert (Prims.op_Addition (k-1) 1 = k);
        (* So coeff(df, k-1) = nat_scale k (coeff(f, k)) *)
        add_congruence (coeff f k) (coeff ((zero <: t) @ df) k)
                       (coeff f k) (coeff df (k-1));
        transitivity (coeff rhs k) (coeff f k + coeff ((zero <: t) @ df) k)
                     (coeff f k + coeff df (k-1));
        (* coeff(f,k) = nat_scale 1 (coeff f k) *)
        nat_scale_one #t #acg (coeff f k);
        symmetry (nat_scale #t #acg 1 (coeff f k)) (coeff f k);
        add_congruence (coeff f k) (coeff df (k-1))
                       (nat_scale #t #acg 1 (coeff f k)) (nat_scale #t #acg k (coeff f k));
        transitivity (coeff rhs k) (coeff f k + coeff df (k-1))
                     (nat_scale #t #acg 1 (coeff f k) + nat_scale #t #acg k (coeff f k));
        (* nat_scale 1 x + nat_scale k x = nat_scale (1+k) x = nat_scale (k+1) x *)
        nat_scale_add #t #acg 1 k (coeff f k);
        assert (Prims.op_Addition 1 k = kp1);
        symmetry (coeff rhs k)
                 (nat_scale #t #acg 1 (coeff f k) + nat_scale #t #acg k (coeff f k));
        transitivity (coeff rhs k)
          (nat_scale #t #acg 1 (coeff f k) + nat_scale #t #acg k (coeff f k))
          (nat_scale #t #acg kp1 (coeff f k));
        symmetry (coeff rhs k) (nat_scale #t #acg kp1 (coeff f k));
        transitivity (coeff lhs k) (nat_scale #t #acg kp1 (coeff f k)) (coeff rhs k)
      )
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* Shift commutes with multiplication on the left:
   (zero@f) * g ≈ zero@(f*g).
   Proof: apply poly_mul_reveal with a=zero, giving
   (zero@f)*g = [zero]*g + zero@(f*g). [zero]*g ≈ zero (scalar 0), so result follows. *)
let shift_mul (#t:Type) {| cr: commutative_ring t |}
  (f g: polynomial t)
  : Lemma (poly_eq (poly_mul ((zero <: t) @ f) g)
                   ((zero <: t) @ (poly_mul f g)))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let lhs : polynomial t = poly_mul ((zero <: t) @ f) g in
    let rhs : polynomial t = (zero <: t) @ (poly_mul f g) in
    let aux (k: nat) : Lemma (coeff lhs k = coeff rhs k) =
      coeff_shift (poly_mul f g) k;
      poly_mul_singleton_coeff (zero <: t) g k;
      H.zero_mul_x (coeff g k);
      poly_add_coeff (poly_mul ((zero <: t) @ poly_zero) g) ((zero <: t) @ (poly_mul f g)) k;
      poly_mul_reveal (zero <: t) f g;
      poly_eq_means_equal_coeffs lhs (poly_add (poly_mul ((zero <: t) @ poly_zero) g)
                                               ((zero <: t) @ (poly_mul f g))) k;
      let c1 = coeff (poly_mul ((zero <: t) @ poly_zero) g) k in
      let c2 = coeff ((zero <: t) @ (poly_mul f g)) k in
      transitivity c1 ((zero <: t) * coeff g k) (zero <: t);
      add_congruence c1 c2 (zero <: t) c2;
      H.zero_plus_x c2;
      transitivity (c1 + c2) ((zero <: t) + c2) c2;
      assert (c2 == coeff rhs k);
      transitivity (coeff lhs k) (c1 + c2) c2;
      reflexivity (coeff rhs k)
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* Shift respects poly_eq: if poly_eq f g then poly_eq (zero@f) (zero@g). *)
let shift_congruence (#t:Type) {| cr: commutative_ring t |}
  (f g: polynomial t)
  : Lemma (requires poly_eq f g) (ensures poly_eq ((zero <: t) @ f) ((zero <: t) @ g))
  = H.elim_equatable_laws t ();
    let lhs = (zero <: t) @ f in
    let rhs = (zero <: t) @ g in
    let aux (k: nat) : Lemma (coeff lhs k = coeff rhs k) =
      coeff_shift f k; coeff_shift g k;
      if k = 0 then reflexivity (zero <: t)
      else poly_eq_means_equal_coeffs f g (k - 1)
    in Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

(* Four-term rearrangement: A+(B+(C+D)) ≈ (B+C)+(A+D) for polynomial addition.
   Used in the product rule proof. *)
private let poly_add_rearrange (#t:Type) {| cr: commutative_ring t |}
  (a b c d: polynomial t)
  : Lemma (poly_eq (poly_add a (poly_add b (poly_add c d)))
                   (poly_add (poly_add b c) (poly_add a d)))
  = (* Step 1: B+(C+D) ≈ (B+C)+D [reverse of assoc] *)
    poly_add_associativity b c d;
    poly_eq_symmetry (poly_add (poly_add b c) d) (poly_add b (poly_add c d));
    (* Now poly_eq (poly_add b (poly_add c d)) (poly_add (poly_add b c) d) *)
    poly_eq_reflexivity a;
    poly_add_congruence a (poly_add b (poly_add c d)) a (poly_add (poly_add b c) d);
    (* A+(B+(C+D)) ≈ A+((B+C)+D) *)
    (* Step 2: A+((B+C)+D) ≈ (A+(B+C))+D [reverse of assoc] *)
    poly_add_associativity a (poly_add b c) d;
    poly_eq_symmetry (poly_add (poly_add a (poly_add b c)) d)
                     (poly_add a (poly_add (poly_add b c) d));
    poly_eq_transitivity (poly_add a (poly_add b (poly_add c d)))
                         (poly_add a (poly_add (poly_add b c) d))
                         (poly_add (poly_add a (poly_add b c)) d);
    (* A+(B+(C+D)) ≈ (A+(B+C))+D *)
    (* Step 3: A+(B+C) ≈ (B+C)+A [comm] *)
    poly_add_commutativity a (poly_add b c);
    poly_eq_reflexivity d;
    poly_add_congruence (poly_add a (poly_add b c)) d (poly_add (poly_add b c) a) d;
    poly_eq_transitivity (poly_add a (poly_add b (poly_add c d)))
                         (poly_add (poly_add a (poly_add b c)) d)
                         (poly_add (poly_add (poly_add b c) a) d);
    (* A+(B+(C+D)) ≈ ((B+C)+A)+D *)
    (* Step 4: ((B+C)+A)+D ≈ (B+C)+(A+D) [assoc] *)
    poly_add_associativity (poly_add b c) a d;
    poly_eq_transitivity (poly_add a (poly_add b (poly_add c d)))
                         (poly_add (poly_add (poly_add b c) a) d)
                         (poly_add (poly_add b c) (poly_add a d))

(* Derivative of a cons: D(a::p') ≈ p' + 0@D(p').
   Same identity as poly_deriv_shift but for an ARBITRARY leading coefficient a.
   The leading coefficient doesn't affect the derivative.
   Takes non-empty polynomial p; result is in terms of tail of p. *)
#push-options "--z3rlimit 40"
let poly_deriv_cons (#t:Type) {| cr: commutative_ring t |}
  (p: polynomial t)
  : Lemma (requires Cons? p)
          (ensures (let p' : polynomial t = L.tl p in
                   poly_eq (poly_deriv p)
                           (poly_add p' ((zero <: t) @ (poly_deriv p')))))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let acg = cr.cr_r.r_add in
    let a = L.hd p in
    let p' : polynomial t = L.tl p in
    let dp' = poly_deriv p' in
    let lhs = poly_deriv p in
    let rhs = poly_add p' ((zero <: t) @ dp') in
    let aux (k: nat) : Lemma (coeff lhs k = coeff rhs k) =
      let kp1 = Prims.op_Addition k 1 in
      poly_deriv_coeff p k;
      assert (coeff p kp1 == coeff p' k);
      nat_scale_congruence #t #acg kp1 (coeff p kp1) (coeff p' k);
      transitivity (coeff lhs k) (nat_scale #t #acg kp1 (coeff p kp1))
                   (nat_scale #t #acg kp1 (coeff p' k));
      poly_add_coeff p' ((zero <: t) @ dp') k;
      coeff_shift dp' k;
      if k = 0 then (
        add_congruence (coeff p' 0) (coeff ((zero <: t) @ dp') 0) (coeff p' 0) (zero <: t);
        H.x_plus_zero (coeff p' 0);
        transitivity (coeff rhs 0) (coeff p' 0 + coeff ((zero <: t) @ dp') 0)
                     (coeff p' 0 + (zero <: t));
        transitivity (coeff rhs 0) (coeff p' 0 + (zero <: t)) (coeff p' 0);
        nat_scale_one #t #acg (coeff p' 0);
        symmetry (coeff rhs 0) (coeff p' 0);
        transitivity (coeff lhs 0) (nat_scale #t #acg 1 (coeff p' 0)) (coeff p' 0);
        transitivity (coeff lhs 0) (coeff p' 0) (coeff rhs 0)
      ) else (
        poly_deriv_coeff p' (k - 1);
        assert (Prims.op_Addition (k-1) 1 = k);
        add_congruence (coeff p' k) (coeff ((zero <: t) @ dp') k)
                       (coeff p' k) (coeff dp' (k-1));
        transitivity (coeff rhs k) (coeff p' k + coeff ((zero <: t) @ dp') k)
                     (coeff p' k + coeff dp' (k-1));
        nat_scale_one #t #acg (coeff p' k);
        symmetry (nat_scale #t #acg 1 (coeff p' k)) (coeff p' k);
        add_congruence (coeff p' k) (coeff dp' (k-1))
                       (nat_scale #t #acg 1 (coeff p' k)) (nat_scale #t #acg k (coeff p' k));
        transitivity (coeff rhs k) (coeff p' k + coeff dp' (k-1))
                     (nat_scale #t #acg 1 (coeff p' k) + nat_scale #t #acg k (coeff p' k));
        nat_scale_add #t #acg 1 k (coeff p' k);
        assert (Prims.op_Addition 1 k = kp1);
        symmetry (coeff rhs k)
                 (nat_scale #t #acg 1 (coeff p' k) + nat_scale #t #acg k (coeff p' k));
        transitivity (coeff rhs k)
          (nat_scale #t #acg 1 (coeff p' k) + nat_scale #t #acg k (coeff p' k))
          (nat_scale #t #acg kp1 (coeff p' k));
        symmetry (coeff rhs k) (nat_scale #t #acg kp1 (coeff p' k));
        transitivity (coeff lhs k) (nat_scale #t #acg kp1 (coeff p' k)) (coeff rhs k)
      )
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs
#pop-options

(* ================================================================ *)
(*  PRODUCT RULE (Leibniz rule):                                     *)
(*    D(p · q) ≈ D(p) · q + p · D(q)                                *)
(*                                                                   *)
(*  Proof by structural induction on p.                              *)
(* ================================================================ *)

#push-options "--z3rlimit 40"
let rec poly_deriv_mul (#t:Type) {| cr: commutative_ring t |}
  (p q: polynomial t)
  : Lemma (ensures poly_eq (poly_deriv (poly_mul p q))
                           (poly_add (poly_mul (poly_deriv p) q)
                                     (poly_mul p (poly_deriv q))))
          (decreases L.length p)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let dp = poly_deriv p in
    let dq = poly_deriv q in
    let pq = poly_mul p q in
    let lhs = poly_deriv pq in
    let rhs = poly_add (poly_mul dp q) (poly_mul p dq) in
    match p with
    | [] ->
      (* D([]·q) = D([]) = []. RHS = D([])·q + []·D(q) = []·q + []·D(q) = []+[] = [] *)
      assert (pq == ([] <: polynomial t));
      assert (dp == ([] <: polynomial t));
      assert (lhs == ([] <: polynomial t));
      assert (poly_mul dp q == ([] <: polynomial t));
      assert (poly_mul p dq == ([] <: polynomial t));
      assert (rhs == poly_add ([] <: polynomial t) ([] <: polynomial t));
      poly_add_zero ([] <: polynomial t);
      poly_eq_symmetry (poly_add (poly_zero #t) (poly_zero #t)) (poly_zero #t)
    | a :: p' ->
      (* IH: D(p'·q) ≈ D(p')·q + p'·D(q) *)
      poly_deriv_mul p' q;
      let dp' = poly_deriv p' in
      let p'q = poly_mul p' q in
      let p'dq = poly_mul p' dq in
      let dp'q = poly_mul dp' q in
      let aq  = poly_mul (a @ poly_zero) q in  (* [a]·q *)
      let adq = poly_mul (a @ poly_zero) dq in (* [a]·D(q) *)
      (* (a::p')·q ≈ [a]·q + 0@(p'·q) by poly_mul_reveal *)
      poly_mul_reveal a p' q;
      let xp'q : polynomial t = (zero <: t) @ p'q in (* 0@(p'·q) *)
      (* --- LHS computation --- *)
      (* D(pq) ≈ D([a]·q + 0@(p'·q)) by congruence *)
      poly_deriv_congruence pq (poly_add aq xp'q);
      (* = D([a]·q) + D(0@(p'·q)) by linearity *)
      poly_deriv_add aq xp'q;
      poly_eq_transitivity lhs (poly_deriv (poly_add aq xp'q))
                               (poly_add (poly_deriv aq) (poly_deriv xp'q));
      (* D([a]·q) ≈ [a]·D(q) *)
      poly_deriv_scalar_mul a q;
      (* D(0@(p'·q)) ≈ p'·q + 0@D(p'·q) *)
      poly_deriv_shift p'q;
      let dp'q_term = poly_deriv p'q in
      let xdp'q = (zero <: t) @ dp'q_term in
      (* By IH: D(p'·q) ≈ D(p')·q + p'·D(q) *)
      (* So 0@D(p'·q) ≈ 0@(D(p')·q + p'·D(q)) *)
      shift_congruence dp'q_term (poly_add dp'q p'dq);
      (* ≈ 0@(D(p')·q) + 0@(p'·D(q)) by shift_add *)
      let xdp'q2 = (zero <: t) @ (poly_add dp'q p'dq) in
      shift_add dp'q p'dq;
      poly_eq_transitivity xdp'q xdp'q2 (poly_add ((zero <: t) @ dp'q) ((zero <: t) @ p'dq));
      (* So D(0@(p'·q)) ≈ p'·q + (0@(D(p')·q) + 0@(p'·D(q))) *)
      let shift_dp'q = (zero <: t) @ dp'q in
      let shift_p'dq = (zero <: t) @ p'dq in
      poly_eq_reflexivity p'q;
      poly_add_congruence p'q xdp'q p'q (poly_add shift_dp'q shift_p'dq);
      poly_eq_transitivity (poly_deriv xp'q) (poly_add p'q xdp'q)
                           (poly_add p'q (poly_add shift_dp'q shift_p'dq));
      (* LHS ≈ D([a]·q) + D(0@(p'·q)) ≈ adq + (p'·q + (0@(D(p')·q) + 0@(p'·D(q)))) *)
      poly_add_congruence (poly_deriv aq) (poly_deriv xp'q)
                          adq (poly_add p'q (poly_add shift_dp'q shift_p'dq));
      poly_eq_transitivity lhs
        (poly_add (poly_deriv aq) (poly_deriv xp'q))
        (poly_add adq (poly_add p'q (poly_add shift_dp'q shift_p'dq)));
      (* --- RHS computation --- *)
      (* D(a::p') ≈ p' + 0@D(p') by poly_deriv_cons *)
      poly_deriv_cons p;
      let xdp' = (zero <: t) @ dp' in
      (* D(a::p')·q ≈ (p' + 0@D(p'))·q *)
      poly_eq_reflexivity q;
      poly_mul_congruence dp q (poly_add p' xdp') q;
      (* (p' + 0@D(p'))·q ≈ p'·q + (0@D(p'))·q by right_distributivity *)
      poly_right_distributivity q p' xdp';
      poly_eq_transitivity (poly_mul dp q) (poly_mul (poly_add p' xdp') q)
                           (poly_add (poly_mul p' q) (poly_mul xdp' q));
      (* (0@D(p'))·q ≈ 0@(D(p')·q) by shift_mul *)
      shift_mul dp' q;
      poly_eq_reflexivity p'q;
      poly_add_congruence p'q (poly_mul xdp' q) p'q shift_dp'q;
      poly_eq_transitivity (poly_mul dp q)
        (poly_add p'q (poly_mul xdp' q))
        (poly_add p'q shift_dp'q);
      (* (a::p')·D(q) ≈ [a]·D(q) + 0@(p'·D(q)) by poly_mul_reveal *)
      poly_mul_reveal a p' dq;
      (* RHS = D(a::p')·q + (a::p')·D(q) ≈ (p'·q + 0@(D(p')·q)) + (adq + 0@(p'·D(q))) *)
      poly_add_congruence (poly_mul dp q) (poly_mul p dq)
                          (poly_add p'q shift_dp'q) (poly_add adq shift_p'dq);
      (* rhs ≈ (p'q + shift_dp'q) + (adq + shift_p'dq) *)
      (* We need: adq + (p'q + (shift_dp'q + shift_p'dq)) ≈ rhs *)
      poly_add_rearrange adq p'q shift_dp'q shift_p'dq;
      (* rearrange: mid ≈ (p'q + shift_dp'q) + (adq + shift_p'dq) *)
      let mid = poly_add adq (poly_add p'q (poly_add shift_dp'q shift_p'dq)) in
      let target = poly_add (poly_add p'q shift_dp'q) (poly_add adq shift_p'dq) in
      (* We have: poly_eq mid target, poly_eq rhs target. Need: poly_eq mid rhs *)
      poly_eq_symmetry rhs target;
      poly_eq_transitivity mid target rhs;
      poly_eq_transitivity lhs mid rhs
#pop-options
