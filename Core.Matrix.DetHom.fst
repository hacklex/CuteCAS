module Core.Matrix.DetHom

(* INTERNAL — a ring homomorphism  phi : a -> b  commutes with the
   determinant:   phi (det m) = det (map_matrix phi m).

   This is the generic version of Core.Matrix.DetEval (which specialises
   the source ring to `polynomial t` and the hom to `poly_eval _ c`).
   Here the hom laws are supplied as explicit lemma arguments so the
   result applies to ANY pair of commutative rings and any ring hom
   between them (in particular  int -> fp p,  the coefficient reduction
   that transports the Sylvester matrix / resultant mod p).

   Pieces (mirroring DetEval):
     hom_sum_list        : phi commutes with sum_list
     hom_prod_range      : phi commutes with prod_range
     hom_sum_over_perms  : phi commutes with sum_over_perms
     perm_product_hom    : phi commutes with perm_product
     leibniz_hom         : phi commutes with leibniz_term
     det_hom             : phi commutes with det

   NO admit / assume / sorry. *)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers
module PS = Core.Permutation.Sum
module DET = Core.Matrix.Determinant

open Core.Algebra
open Core.Algebra.Notation
open Core.FinSum
open Core.Permutation
open Core.Permutation.Enum
open Core.Vector
open Core.Matrix

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ---------------------------------------------------------------- *)
(*  Entrywise map of a square matrix.                               *)
(* ---------------------------------------------------------------- *)

let map_matrix (#a #b:Type) (#n:pos) (phi: a -> b) (m: square_matrix a n)
  : square_matrix b n
  = fun (i:fin n) (j:fin n) -> phi (m i j)

(* ---------------------------------------------------------------- *)
(*  phi commutes with sum_list.                                     *)
(* ---------------------------------------------------------------- *)

let rec hom_sum_list (#a #b:Type) {| cra: commutative_ring a |} {| crb: commutative_ring b |}
  (phi: a -> b)
  (hzero: squash (phi (zero #a) = (zero #b)))
  (hadd: (x:a) -> (y:a) -> Lemma (phi (x + y) = phi x + phi y))
  (xs: list a)
  : Lemma (ensures phi (sum_list xs) = sum_list (L.map phi xs))
          (decreases xs)
  = H.elim_equatable_laws b ();
    H.trans_for_calc b ();
    match xs with
    | [] ->
      sum_list_nil #a #(cra.cr_r.r_add);
      sum_list_nil #b #(crb.cr_r.r_add)
    | p :: rest ->
      let prest = sum_list rest in
      let srest = sum_list (L.map phi rest) in
      sum_list_cons p rest;                          (* sum_list xs == p + prest *)
      sum_list_cons (phi p) (L.map phi rest);        (* sum_list (map phi xs) == phi p + srest *)
      hadd p prest;                                  (* phi (p + prest) = phi p + phi prest *)
      hom_sum_list phi hzero hadd rest;              (* phi prest = srest *)
      add_congruence (phi p) (phi prest) (phi p) srest;
      transitivity (phi (sum_list xs)) (phi p + phi prest) (phi p + srest)

(* ---------------------------------------------------------------- *)
(*  phi commutes with prod_range.                                   *)
(* ---------------------------------------------------------------- *)

let rec hom_prod_range (#a #b:Type) {| cra: commutative_ring a |} {| crb: commutative_ring b |}
  (phi: a -> b)
  (hone: squash (phi (one #a) = (one #b)))
  (hmul: (x:a) -> (y:a) -> Lemma (phi (x * y) = phi x * phi y))
  (g: nat -> a) (lo hi: nat)
  : Lemma (ensures phi (prod_range g lo hi)
                 = prod_range (fun (i:nat) -> phi (g i)) lo hi)
          (decreases (hi - lo))
  = H.elim_equatable_laws b ();
    H.trans_for_calc b ();
    let pg : nat -> b = (fun (i:nat) -> phi (g i)) in
    if lo >= hi then begin
      prod_range_empty g lo hi;                      (* prod_range g == one #a *)
      prod_range_empty pg lo hi;                     (* prod_range pg == one #b *)
      reflexivity (one #b)
    end else begin
      let rest = prod_range g (lo ++ 1) hi in
      let prest = prod_range pg (lo ++ 1) hi in
      prod_range_unfold_left g lo hi;                (* prod == g lo * rest *)
      prod_range_unfold_left pg lo hi;               (* prod pg == phi (g lo) * prest *)
      hmul (g lo) rest;                              (* phi (g lo * rest) = phi (g lo) * phi rest *)
      hom_prod_range phi hone hmul g (lo ++ 1) hi;   (* phi rest = prest *)
      mul_congruence (phi (g lo)) (phi rest) (phi (g lo)) prest;
      transitivity (phi (prod_range g lo hi))
                   (phi (g lo) * phi rest)
                   (phi (g lo) * prest)
    end

(* ---------------------------------------------------------------- *)
(*  map fusion:  map phi (map f l) == map (phi . f) l.              *)
(* ---------------------------------------------------------------- *)

let rec map_hom_map (#a #b:Type) (#n:nat)
  (phi: a -> b) (f: permutation n -> a) (l: list (permutation n))
  : Lemma (ensures L.map phi (L.map f l)
                   == L.map (fun (p: permutation n) -> phi (f p)) l)
          (decreases l)
  = match l with
    | [] -> ()
    | x :: rest -> map_hom_map phi f rest

(* ---------------------------------------------------------------- *)
(*  phi commutes with sum_over_perms.                               *)
(* ---------------------------------------------------------------- *)

let hom_sum_over_perms (#a #b:Type) {| cra: commutative_ring a |} {| crb: commutative_ring b |}
  (phi: a -> b)
  (hzero: squash (phi (zero #a) = (zero #b)))
  (hadd: (x:a) -> (y:a) -> Lemma (phi (x + y) = phi x + phi y))
  (n: nat) (f: permutation n -> a)
  : Lemma (phi (PS.sum_over_perms n f)
         = PS.sum_over_perms n (fun (p: permutation n) -> phi (f p)))
  = H.elim_equatable_laws b ();
    PS.sum_over_perms_reveal n f;
    PS.sum_over_perms_reveal n (fun (p: permutation n) -> phi (f p));
    hom_sum_list phi hzero hadd (L.map f (all_permutations n));
    map_hom_map phi f (all_permutations n)

(* ---------------------------------------------------------------- *)
(*  phi commutes with perm_product.                                 *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 100 --fuel 2 --ifuel 2"
let perm_product_hom (#a #b:Type) {| cra: commutative_ring a |} {| crb: commutative_ring b |}
  (phi: a -> b)
  (hone: squash (phi (one #a) = (one #b)))
  (hmul: (x:a) -> (y:a) -> Lemma (phi (x * y) = phi x * phi y))
  (#n:pos) (m: square_matrix a n) (p: permutation n)
  : Lemma (phi (DET.perm_product m p)
         = DET.perm_product (map_matrix phi m) p)
  = H.elim_equatable_laws b ();
    H.trans_for_calc b ();
    let pe : nat -> b = (fun (i:nat) -> phi (DET.perm_entry m p i)) in
    DET.perm_product_via m p;
    DET.perm_product_via (map_matrix phi m) p;
    hom_prod_range phi hone hmul (DET.perm_entry m p) 0 n;
    let h (i:nat{0 <= i /\ i < n})
      : Lemma (pe i = DET.perm_entry (map_matrix phi m) p i)
      = H.elim_equatable_laws b ();
        assert (DET.perm_entry m p i == m i (p.fwd i));
        assert (pe i == phi (m i (p.fwd i)));
        assert (DET.perm_entry (map_matrix phi m) p i == phi (m i (p.fwd i)))
    in
    prod_range_congruence pe (DET.perm_entry (map_matrix phi m) p) 0 n h
#pop-options

(* ---------------------------------------------------------------- *)
(*  phi commutes with leibniz_term.                                 *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let leibniz_hom (#a #b:Type) {| cra: commutative_ring a |} {| crb: commutative_ring b |}
  (phi: a -> b)
  (hone: squash (phi (one #a) = (one #b)))
  (hmul: (x:a) -> (y:a) -> Lemma (phi (x * y) = phi x * phi y))
  (hneg: (x:a) -> Lemma (phi (- x) = - (phi x)))
  (#n:pos) (m: square_matrix a n) (p: permutation n)
  : Lemma (phi (DET.leibniz_term m p)
         = DET.leibniz_term (map_matrix phi m) p)
  = H.elim_equatable_laws b ();
    perm_product_hom phi hone hmul m p;
    if parity p then ()
    else begin
      let ppm = DET.perm_product m p in
      hneg ppm;                                      (* phi (- ppm) = - (phi ppm) *)
      neg_congruence (phi ppm) (DET.perm_product (map_matrix phi m) p);
      transitivity (phi (DET.leibniz_term m p))
                   ((- (phi ppm)))
                   ((- (DET.perm_product (map_matrix phi m) p)))
    end
#pop-options

(* ---------------------------------------------------------------- *)
(*  THE DETERMINANT HOMOMORPHISM.                                   *)
(* ---------------------------------------------------------------- *)

#push-options "--z3rlimit 120 --fuel 2 --ifuel 2"
let det_hom (#a #b:Type) {| cra: commutative_ring a |} {| crb: commutative_ring b |}
  (phi: a -> b)
  (hzero: squash (phi (zero #a) = (zero #b)))
  (hone: squash (phi (one #a) = (one #b)))
  (hadd: (x:a) -> (y:a) -> Lemma (phi (x + y) = phi x + phi y))
  (hmul: (x:a) -> (y:a) -> Lemma (phi (x * y) = phi x * phi y))
  (hneg: (x:a) -> Lemma (phi (- x) = - (phi x)))
  (#n:pos) (m: square_matrix a n)
  : Lemma (phi (DET.det m) = DET.det (map_matrix phi m))
  = H.elim_equatable_laws b ();
    H.trans_for_calc b ();
    let lt = DET.leibniz_term m in
    let lhsf : permutation n -> b =
      (fun (p: permutation n) -> phi (lt p)) in
    let lt' = DET.leibniz_term (map_matrix phi m) in
    DET.det_unfold m;
    DET.det_unfold (map_matrix phi m);
    hom_sum_over_perms phi hzero hadd n lt;
    PS.sum_over_perms_congruence n lhsf lt'
      (fun (p: permutation n) -> leibniz_hom phi hone hmul hneg m p)
#pop-options
