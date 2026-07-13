module Core.Factor.BerlekampFactor

(* ================================================================ *)
(*  M2 · S5 — EXECUTABLE Berlekamp factorization over  fp p.        *)
(*                                                                   *)
(*  Input:  a MONIC SQUAREFREE  fbar : polynomial (fp p)  of         *)
(*  degree >= 1.  Output:  a list of its factors, obtained by the    *)
(*  Berlekamp gcd-splitting loop driven by the null space of the    *)
(*  Frobenius matrix  Q - I.                                         *)
(*                                                                   *)
(*  THREE executable Tot functions:                                  *)
(*    berlekamp_matrix  — the Frobenius matrix Q - I as row-list;    *)
(*    berlekamp_kernel  — null-space basis, read back as polys,      *)
(*                        FILTERED by a DECIDABLE Berlekamp          *)
(*                        membership test (the verified trust cap);  *)
(*    berlekamp_factor  — refine [fbar] by gcd(g, h - c) splits.     *)
(*                                                                   *)
(*  SOUNDNESS is made independent of the (S3-deferred) null-space    *)
(*  SPANNING by the decidable membership filter: every polynomial    *)
(*  the loop actually uses is CERTIFIED to satisfy  h^p ≡ h (mod     *)
(*  fbar),  so every split product-preserves via the reverse-split   *)
(*  theorem  berlekamp_reverse_associates.                           *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module NS  = Core.LinearAlgebra.FpNullSpace
module BK  = Core.Modular.PrimeField.Berlekamp
module PR  = Core.Polynomial.Roots
module IR  = Core.Polynomial.Irreducible
module SF  = Core.Polynomial.SquareFree
module SP  = Core.Polynomial.SubsetProd
module GC  = Core.Polynomial.GCD
module CM  = Core.Algebra.CongruenceMod
module BDC = Core.Modular.PrimeField.BerlekampDimCount
module EU  = Core.NumberTheory
module H   = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.Modular.PrimeField

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ---------------------------------------------------------------- *)
(*  0.  degree as a nat (fbar always has deg >= 1 in the pipeline).  *)
(* ---------------------------------------------------------------- *)

let pdeg (#p:int{EU.is_prime p}) (fbar: polynomial (fp p)) : nat
  = let d = deg fbar in if d >= 0 then d else 0

(* the monic monomial  x^k  in  (fp p)[x]. *)
let mono_x (p:int{EU.is_prime p}) (k:nat) : polynomial (fp p)
  = monomial #(fp p) (fp_one p) k

(* ---------------------------------------------------------------- *)
(*  1.  The Frobenius matrix  Q - I  as a row-list.                  *)
(*                                                                   *)
(*  Row i (i = 0 .. n-1, n = deg fbar) is the length-n coefficient   *)
(*  vector of  ((x^i)^p mod fbar) - x^i.                             *)
(* ---------------------------------------------------------------- *)

(* coefficient vector [coeff g i; ...; coeff g (i+n-1)]. *)
let rec vec_of (#p:int{EU.is_prime p}) (g: polynomial (fp p)) (i:nat) (n:nat)
  : Tot (NS.vector p) (decreases n)
  = if n = 0 then [] else coeff g i :: vec_of g (i ++ 1) (n - 1)

(* row i of Q - I. *)
let berlekamp_row (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (i:nat)
  : NS.vector p
  = let n = pdeg fbar in
    let qi = poly_rem (poly_power (mono_x p i) (p <: nat)) fbar in
    vec_of (qi -- (mono_x p i)) 0 n

let rec rows_from (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (i:nat) (cnt:nat)
  : Tot (list (NS.vector p)) (decreases cnt)
  = if cnt = 0 then []
    else berlekamp_row p fbar i :: rows_from p fbar (i ++ 1) (cnt - 1)

let berlekamp_matrix (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  : list (NS.vector p)
  = rows_from p fbar 0 (pdeg fbar)

(* ---------------------------------------------------------------- *)
(*  1'.  The TRANSPOSE  (Q - I)^T  as a row-list  (build by columns). *)
(*                                                                   *)
(*  CONVENTION.  berlekamp_matrix has ROW i = the Frobenius image    *)
(*  frob_x i.  Feeding that to  NS.mat_vec_mul  (which dots each row  *)
(*  with v) computes the RIGHT null space, which is NOT the          *)
(*  Berlekamp subalgebra (= the LEFT null space of Q - I).  The      *)
(*  matrix that represents  h |-> frob h  under mat_vec_mul is the   *)
(*  TRANSPOSE:  row k of berlekamp_matrix_T is                       *)
(*     [ coeff (frob_x 0) k ; ... ; coeff (frob_x (n-1)) k ].        *)
(*  berlekamp_kernel is driven by this transpose so that the null    *)
(*  space genuinely equals the Berlekamp algebra.                    *)
(* ---------------------------------------------------------------- *)

let mT_entry (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (i k:nat) : fp p
  = NS.get (berlekamp_row p fbar i) k

let rec mT_row (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (k:nat) (i cnt:nat)
  : Tot (NS.vector p) (decreases cnt)
  = if cnt = 0 then [] else mT_entry p fbar i k :: mT_row p fbar k (i ++ 1) (cnt - 1)

let rec mT_rows (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (k cnt:nat)
  : Tot (list (NS.vector p)) (decreases cnt)
  = if cnt = 0 then []
    else mT_row p fbar k 0 (pdeg fbar) :: mT_rows p fbar (k ++ 1) (cnt - 1)

let berlekamp_matrix_T (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  : list (NS.vector p)
  = mT_rows p fbar 0 (pdeg fbar)

(* ---------------- structural lemmas for mT_row / mT_rows ---------------- *)

let rec mT_row_length (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (k i cnt:nat)
  : Lemma (ensures L.length (mT_row p fbar k i cnt) == cnt) (decreases cnt)
  = if cnt = 0 then () else mT_row_length p fbar k (i ++ 1) (cnt - 1)

let rec mT_row_index (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (k i cnt a:nat)
  : Lemma (requires a < cnt)
          (ensures  (mT_row_length p fbar k i cnt;
                     L.index (mT_row p fbar k i cnt) a == mT_entry p fbar (i ++ a) k))
          (decreases cnt)
  = mT_row_length p fbar k i cnt;
    if a = 0 then ()
    else (mT_row_length p fbar k (i ++ 1) (cnt - 1);
          mT_row_index p fbar k (i ++ 1) (cnt - 1) (a - 1))

let rec mT_rows_length (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (k cnt:nat)
  : Lemma (ensures L.length (mT_rows p fbar k cnt) == cnt) (decreases cnt)
  = if cnt = 0 then () else mT_rows_length p fbar (k ++ 1) (cnt - 1)

let rec mT_rows_index (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (k cnt a:nat)
  : Lemma (requires a < cnt)
          (ensures  (mT_rows_length p fbar k cnt;
                     L.index (mT_rows p fbar k cnt) a == mT_row p fbar (k ++ a) 0 (pdeg fbar)))
          (decreases cnt)
  = mT_rows_length p fbar k cnt;
    if a = 0 then ()
    else (mT_rows_length p fbar (k ++ 1) (cnt - 1);
          mT_rows_index p fbar (k ++ 1) (cnt - 1) (a - 1))

(* every row of the transpose has length n = pdeg fbar. *)
let rec mT_rows_all_len (p:int{EU.is_prime p}) (fbar: polynomial (fp p)) (k cnt:nat)
  : Lemma (ensures NS.all_len (pdeg fbar) (mT_rows p fbar k cnt)) (decreases cnt)
  = if cnt = 0 then ()
    else (mT_row_length p fbar k 0 (pdeg fbar);
          mT_rows_all_len p fbar (k ++ 1) (cnt - 1))

let berlekamp_matrix_T_all_len (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  : Lemma (NS.all_len (pdeg fbar) (berlekamp_matrix_T p fbar))
  = mT_rows_all_len p fbar 0 (pdeg fbar)

let berlekamp_matrix_T_length (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  : Lemma (L.length (berlekamp_matrix_T p fbar) == pdeg fbar)
          [SMTPat (berlekamp_matrix_T p fbar)]
  = mT_rows_length p fbar 0 (pdeg fbar)

(* ---------------------------------------------------------------- *)
(*  2.  DECIDABLE Berlekamp membership  (the verified trust cap).    *)
(*                                                                   *)
(*  berlekamp_mem_check fbar h  =  (h^p - h) mod fbar == 0,          *)
(*  which certifies  cong fbar (h^p) h.                             *)
(* ---------------------------------------------------------------- *)

let berlekamp_mem_check (p:int{EU.is_prime p}) (fbar h: polynomial (fp p)) : bool
  = Nil? (poly_rem ((poly_power h (p <: nat)) -- h) fbar)

(* remainder-zero certifies the congruence. *)
let berlekamp_mem_check_sound (p:int{EU.is_prime p}) (fbar h: polynomial (fp p))
  : Lemma (requires berlekamp_mem_check p fbar h)
          (ensures  CM.cong #(polynomial (fp p)) fbar (poly_power h (p <: nat)) h)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let d : polynomial (fp p) = (poly_power h (p <: nat)) -- h in
    let q = poly_div d fbar in
    let r = poly_rem d fbar in
    assert (d = ((fbar * q) + r));                 (* poly_rem correctness *)
    CM.cong_of_divmod #(polynomial (fp p)) d fbar q r;   (* cong fbar d r *)
    (* r == poly_zero because Nil? r *)
    assert (r == poly_zero #(fp p));
    (* cong fbar d poly_zero  =  fbar | (d + (- poly_zero)) ; reduce to fbar | d *)
    CM.cong_reveal #(polynomial (fp p)) fbar d (poly_zero #(fp p));
    H.neg_zero #(polynomial (fp p)) ();            (* poly_zero = - poly_zero *)
    reflexivity d;
    add_congruence d (- (poly_zero #(fp p))) d (poly_zero #(fp p));
    H.x_plus_zero d;                                (* d + poly_zero = d *)
    transitivity (d + (- (poly_zero #(fp p)))) (d + (poly_zero #(fp p))) d;
    divides_congruence_right #(polynomial (fp p)) fbar
                             (d + (- (poly_zero #(fp p)))) d;
    CM.cong_reveal #(polynomial (fp p)) fbar (poly_power h (p <: nat)) h

(* ---------------------------------------------------------------- *)
(*  3.  The Berlekamp kernel:  null-space basis vectors read back    *)
(*      as polynomials, FILTERED by the certified membership test.   *)
(* ---------------------------------------------------------------- *)

let berlekamp_kernel (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  : list (polynomial (fp p))
  = let n = pdeg fbar in
    let cands = NS.null_space_basis #p n (berlekamp_matrix_T p fbar) in
    L.filter (berlekamp_mem_check p fbar) (L.map (trim #(fp p)) cands)

(* every kernel element is certified. *)
let berlekamp_kernel_certified (p:int{EU.is_prime p}) (fbar h: polynomial (fp p))
  : Lemma (requires L.memP h (berlekamp_kernel p fbar))
          (ensures  CM.cong #(polynomial (fp p)) fbar (poly_power h (p <: nat)) h)
  = let n = pdeg fbar in
    let mapped = L.map (trim #(fp p))
                   (NS.null_space_basis #p n (berlekamp_matrix_T p fbar)) in
    L.mem_filter (berlekamp_mem_check p fbar) mapped h;
    berlekamp_mem_check_sound p fbar h

(* ---------------------------------------------------------------- *)
(*  4.  The refinement loop.                                         *)
(*                                                                   *)
(*  refine1 h g  =  the NONCONSTANT  gcd(g, h - c),  c ∈ fp_enum.    *)
(*  refine_list h  refines every current factor;                     *)
(*  berlekamp_factor  folds the refinement over the kernel.          *)
(* ---------------------------------------------------------------- *)

let is_nonconst (#t:Type) {| cr: commutative_ring t |} (d: polynomial t) : bool
  = deg d >= 1

let refine1 (p:int{EU.is_prime p}) (h g: polynomial (fp p))
  : list (polynomial (fp p))
  = L.filter (is_nonconst #(fp p))
      (BK.berlekamp_factors #(fp p) g h (fp_enum p))

let refine_list (p:int{EU.is_prime p}) (h: polynomial (fp p))
  (gs: list (polynomial (fp p))) : list (polynomial (fp p))
  = L.concatMap (refine1 p h) gs

(* one fold step:  refine the whole current factor list by kernel elt h. *)
let refine_step (p:int{EU.is_prime p})
  (gs: list (polynomial (fp p))) (h: polynomial (fp p))
  : list (polynomial (fp p))
  = refine_list p h gs

let berlekamp_factor (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1})
  : list (polynomial (fp p))
  = L.fold_left (refine_step p) [fbar] (berlekamp_kernel p fbar)

(* ================================================================ *)
(*  5.  SOUNDNESS building blocks (generic).                        *)
(* ================================================================ *)

(* index-form  deg >= 0  entails  memP-form  deg >= 0. *)
let rec deg_all_memP (#t:Type) {| cr: commutative_ring t |} (l: list (polynomial t))
  : Lemma (requires (forall (k:nat). k < L.length l ==> deg (L.index l k) >= 0))
          (ensures  (forall (d: polynomial t). L.memP d l ==> deg d >= 0))
          (decreases l)
  = match l with
    | [] -> ()
    | h :: tl ->
        assert (deg h >= 0);                                (* index 0 *)
        assert (forall (k:nat). k < L.length tl ==>
                  L.index tl k == L.index (h :: tl) (k ++ 1));
        deg_all_memP tl

(* a degree-0 (unit) factor is absorbed up to associate:
   x * y  and  y  divide each other. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let deg0_mul_associate (#t:Type) {| f: field t |} (x y: polynomial t)
  : Lemma (requires deg x == 0)
          (ensures  divides #(polynomial t) (x * y) y /\
                    divides #(polynomial t) y (x * y))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* y | x*y *)
    mul_commutativity x y;                                  (* x*y ~ y*x *)
    divides_intro #(polynomial t) y (y * x) x;              (* y | y*x *)
    divides_congruence_right #(polynomial t) y (y * x) (x * y);
    (* x*y | y *)
    GC.degree_zero_is_singleton x;                          (* x == [poly_lc x], lc <> zero *)
    let c : t = poly_lc x in
    GC.singleton_inv_mul_singleton c;                       (* [inv c] * [c] = poly_one *)
    let u : polynomial t = [inv c] in
    assert (x == [c]);
    assert ((u * x) = (poly_one #t));                       (* u*x = u*[c] = poly_one *)
    SF.poly_mul_left_congruence (u * x) (poly_one #t) y;    (* (u*x)*y ~ poly_one*y *)
    mul_commutativity (poly_one #t) y;                      (* poly_one*y ~ y*poly_one *)
    poly_mul_one y;                                         (* y*poly_one ~ y *)
    poly_eq_transitivity (poly_one #t * y) (y * poly_one #t) y;
    poly_eq_transitivity ((u * x) * y) (poly_one #t * y) y; (* (u*x)*y ~ y *)
    mul_associativity u x y;                                (* (u*x)*y ~ u*(x*y) *)
    poly_eq_symmetry ((u * x) * y) (u * (x * y));
    poly_eq_transitivity (u * (x * y)) ((u * x) * y) y;     (* u*(x*y) ~ y *)
    mul_commutativity u (x * y);                            (* u*(x*y) ~ (x*y)*u *)
    poly_eq_symmetry (u * (x * y)) ((x * y) * u);
    poly_eq_transitivity ((x * y) * u) (u * (x * y)) y;     (* (x*y)*u ~ y *)
    poly_eq_symmetry ((x * y) * u) y;                       (* y ~ (x*y)*u *)
    divides_intro #(polynomial t) (x * y) y u
#pop-options

(* dropping the degree-0 factors of a product preserves its associate class. *)
#push-options "--z3rlimit 40 --fuel 2 --ifuel 1"
let rec prod_drop_units (#t:Type) {| f: field t |} (l: list (polynomial t))
  : Lemma (requires (forall (d: polynomial t). L.memP d l ==> deg d >= 0))
          (ensures  divides #(polynomial t) (PR.poly_prod l)
                            (PR.poly_prod (L.filter (is_nonconst #t) l)) /\
                    divides #(polynomial t) (PR.poly_prod (L.filter (is_nonconst #t) l))
                            (PR.poly_prod l))
          (decreases l)
  = H.elim_equatable_laws (polynomial t) ();
    match l with
    | [] ->
        divides_refl #(polynomial t) (poly_one #t)
    | x :: xs ->
        assert (deg x >= 0);
        prod_drop_units xs;
        let px  = PR.poly_prod xs in
        let pfx = PR.poly_prod (L.filter (is_nonconst #t) xs) in
        if is_nonconst #t x then begin
          (* filter (x::xs) = x :: filter xs *)
          IR.divides_mul_both_sides #t px pfx x;                (* x*px | x*pfx *)
          IR.divides_mul_both_sides #t pfx px x                 (* x*pfx | x*px *)
        end else begin
          (* deg x == 0 : x is a unit, filter (x::xs) = filter xs *)
          deg0_mul_associate x px;                           (* x*px ~ px *)
          divides_trans #(polynomial t) (x * px) px pfx;     (* x*px | pfx *)
          divides_trans #(polynomial t) pfx px (x * px)      (* pfx | x*px *)
        end
#pop-options

(* ================================================================ *)
(*  6.  refine1 soundness  (the single-split heart).                *)
(*                                                                   *)
(*    refine1 h g  =  the NONCONSTANT  gcd(g, h - c),  c ∈ fp_enum.  *)
(* ================================================================ *)

(* every split factor of g divides g  (memP form). *)
let refine1_bf_divides (p:int{EU.is_prime p}) (h g d: polynomial (fp p))
  : Lemma (requires L.memP d (BK.berlekamp_factors #(fp p) g h (fp_enum p)))
          (ensures  divides #(polynomial (fp p)) d g)
  = let cs = fp_enum p in
    BK.berlekamp_factors_reveal #(fp p) g h cs;
    L.memP_map_elim (fun (c:fp p) -> BK.berlekamp_split #(fp p) g h c) d cs;
    eliminate exists (c:fp p).
                L.memP c cs /\ (BK.berlekamp_split #(fp p) g h c) == d
    returns divides #(polynomial (fp p)) d g
    with _. BK.berlekamp_split_divides_f #(fp p) g h c

(* every split factor of g has deg >= 0  (memP form). *)
let refine1_bf_deg (p:int{EU.is_prime p}) (h g: polynomial (fp p))
  : Lemma (requires deg g >= 0)
          (ensures  (forall (d: polynomial (fp p)).
                       L.memP d (BK.berlekamp_factors #(fp p) g h (fp_enum p)) ==>
                       deg d >= 0))
  = let cs = fp_enum p in
    let bf = BK.berlekamp_factors #(fp p) g h cs in
    let dk (k:nat{k < L.length bf}) : Lemma (deg (L.index bf k) >= 0)
      = BK.berlekamp_factors_have_degree #(fp p) g h cs k in
    Classical.forall_intro dk;
    deg_all_memP #(fp p) bf

(* each output factor divides g. *)
let refine1_divides (p:int{EU.is_prime p}) (h g d: polynomial (fp p))
  : Lemma (requires L.memP d (refine1 p h g))
          (ensures  divides #(polynomial (fp p)) d g)
  = L.mem_filter (is_nonconst #(fp p))
                 (BK.berlekamp_factors #(fp p) g h (fp_enum p)) d;
    refine1_bf_divides p h g d

(* each output factor has deg >= 1. *)
let refine1_deg (p:int{EU.is_prime p}) (h g d: polynomial (fp p))
  : Lemma (requires L.memP d (refine1 p h g))
          (ensures  deg d >= 1)
  = L.mem_filter (is_nonconst #(fp p))
                 (BK.berlekamp_factors #(fp p) g h (fp_enum p)) d

(* PRODUCT PRESERVATION:  for a certified kernel element h  (h^p ≡ h
   mod g),  the product of the nonconstant splits is an associate of g. *)
#push-options "--z3rlimit 40"
let refine1_product (p:int{EU.is_prime p}) (h g: polynomial (fp p))
  : Lemma (requires deg g >= 0 /\
                    CM.cong #(polynomial (fp p)) g (poly_power h (p <: nat)) h)
          (ensures  divides #(polynomial (fp p)) g (PR.poly_prod (refine1 p h g)) /\
                    divides #(polynomial (fp p)) (PR.poly_prod (refine1 p h g)) g)
  = let cs = fp_enum p in
    let bf = BK.berlekamp_factors #(fp p) g h cs in
    (* g ~ poly_prod bf  (reverse split theorem) *)
    BK.berlekamp_reverse_associates p g h;
    (* poly_prod bf ~ poly_prod (filter nonconst bf) = poly_prod (refine1) *)
    refine1_bf_deg p h g;
    prod_drop_units #(fp p) bf;
    divides_trans #(polynomial (fp p)) g (PR.poly_prod bf) (PR.poly_prod (refine1 p h g));
    divides_trans #(polynomial (fp p)) (PR.poly_prod (refine1 p h g)) (PR.poly_prod bf) g
#pop-options

(* ================================================================ *)
(*  7.  COMPLETENESS — the pigeonhole reduction.                    *)
(*                                                                   *)
(*  Structural core (durable, generic): a coprime divisor g of a     *)
(*  product of irreducibles is  poly_const c * masked_prod is mask,  *)
(*  i.e. g is (a unit multiple of) a SUBSET PRODUCT of the           *)
(*  irreducible factors.  This is the linchpin of the pigeonhole     *)
(*  argument "r coprime factors of a squarefree poly with exactly r  *)
(*  irreducible factors ⟹ each factor is a single irreducible".      *)
(* ================================================================ *)

let coprime_factor_is_subset_product (#t:Type) {| f: field t |}
  (irs: list (polynomial t)) (g: polynomial t)
  : Lemma (requires SP.all_irreducible irs /\
                    divides #(polynomial t) g (PR.poly_prod irs))
          (ensures  exists (c: t) (mask: list bool).
                       L.length mask == L.length irs /\
                       not (c = zero) /\
                       (g = ((poly_const c) * (SP.masked_prod irs mask))))
  = SP.divisor_of_irreducible_prod irs g

(* ================================================================ *)
(*  8.  berlekamp_factor SOUNDNESS  (loop invariant, memP form).    *)
(*                                                                   *)
(*  Every factor the loop outputs is a NONCONSTANT (deg >= 1)        *)
(*  DIVISOR of fbar.  Proved by a fold invariant over the kernel:    *)
(*    - refine1 only produces nonconstant factors of its input;      *)
(*    - each such factor divides the input, which divides fbar.      *)
(*  (The two harder clauses — product = fbar and pairwise coprime —  *)
(*   compose across concatMap/fold; see report / refine1_product for *)
(*   the single-step product-preservation.)                         *)
(* ================================================================ *)

(* one refinement step preserves "nonconstant divisor of fbar". *)
let refine_list_preserves (p:int{EU.is_prime p})
  (fbar h: polynomial (fp p)) (gs: list (polynomial (fp p)))
  : Lemma (requires (forall (d: polynomial (fp p)). L.memP d gs ==>
                       deg d >= 1 /\ divides #(polynomial (fp p)) d fbar))
          (ensures  (forall (d: polynomial (fp p)). L.memP d (refine_list p h gs) ==>
                       deg d >= 1 /\ divides #(polynomial (fp p)) d fbar))
  = let step (d: polynomial (fp p))
      : Lemma (requires L.memP d (refine_list p h gs))
              (ensures  deg d >= 1 /\ divides #(polynomial (fp p)) d fbar)
      = BDC.concatMap_mem_elim (refine1 p h) gs d;
        eliminate exists (g: polynomial (fp p)).
                    L.memP g gs /\ L.memP d (refine1 p h g)
        returns deg d >= 1 /\ divides #(polynomial (fp p)) d fbar
        with _.
        begin
          refine1_deg p h g d;                              (* deg d >= 1 *)
          refine1_divides p h g d;                          (* d | g *)
          divides_trans #(polynomial (fp p)) d g fbar       (* g | fbar (hyp) *)
        end
    in
    Classical.forall_intro (Classical.move_requires step)

(* the fold preserves the invariant. *)
let rec fold_refine_inv (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  (gs: list (polynomial (fp p))) (ks: list (polynomial (fp p)))
  : Lemma (requires (forall (d: polynomial (fp p)). L.memP d gs ==>
                       deg d >= 1 /\ divides #(polynomial (fp p)) d fbar))
          (ensures  (forall (d: polynomial (fp p)).
                       L.memP d (L.fold_left (refine_step p) gs ks) ==>
                       deg d >= 1 /\ divides #(polynomial (fp p)) d fbar))
          (decreases ks)
  = match ks with
    | [] -> ()
    | h :: rest ->
        refine_list_preserves p fbar h gs;
        fold_refine_inv p fbar (refine_step p gs h) rest

(* SOUNDNESS (partial):  every output factor is a nonconstant divisor of fbar. *)
#push-options "--fuel 2 --ifuel 2"
let berlekamp_factor_sound (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1}) (d: polynomial (fp p))
  : Lemma (requires L.memP d (berlekamp_factor p fbar))
          (ensures  deg d >= 1 /\ divides #(polynomial (fp p)) d fbar)
  = let base_pf (d0: polynomial (fp p))
      : Lemma (requires L.memP d0 [fbar])
              (ensures  deg d0 >= 1 /\ divides #(polynomial (fp p)) d0 fbar)
      = assert (d0 == fbar);                          (* memP d0 [fbar] *)
        divides_refl #(polynomial (fp p)) fbar
    in
    Classical.forall_intro (Classical.move_requires base_pf);
    fold_refine_inv p fbar [fbar] (berlekamp_kernel p fbar)
#pop-options
