module Core.Factor.BerlekampComplete2

(* ================================================================ *)
(*  C5 · PIECE 1 — the BERLEKAMP COMPLETENESS PIGEONHOLE.            *)
(*                                                                   *)
(*  Durable, generic MATH over any {| field t |}:                   *)
(*                                                                   *)
(*  If `fs` is a list of pairwise-coprime factors, each of degree    *)
(*  >= 1, whose product is (an associate of) a product `irs` of      *)
(*  irreducibles, and  |fs| == |irs|  (the number of distinct        *)
(*  irreducible factors), then EVERY element of `fs` is irreducible.  *)
(*                                                                   *)
(*  Route (the mask pigeonhole):                                     *)
(*   - each fs_i divides ∏irs, so (SubsetProd.divisor_of_irreducible_*)
(*     prod)  fs_i = poly_const c_i * masked_prod irs mask_i.        *)
(*   - deg fs_i >= 1  ⟹  mask_i has a TRUE bit  (nonempty).          *)
(*   - pairwise-coprimality  ⟹  the masks are DISJOINT (a shared     *)
(*     kept index k gives irs_k | gcd(fs_i,fs_j), contra coprime).   *)
(*   - the owner map  i ↦ (a chosen true bit of mask_i)  is thus     *)
(*     an INJECTION  fin r -> fin r,  hence (FinInjSurj) SURJECTIVE, *)
(*     forcing each mask_i to a SINGLETON.                           *)
(*   - fs_i = poly_const c_i * irs_{k}  is an associate of the        *)
(*     irreducible irs_k, hence irreducible.                         *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module H   = Core.Algebra.Helpers
module IR  = Core.Polynomial.Irreducible
module SP  = Core.Polynomial.SubsetProd
module PR  = Core.Polynomial.Roots
module BC  = Core.Modular.PrimeField.BerlekampComplete
module FIS = Core.Factor.FinInjSurj
module ID  = FStar.IndefiniteDescription

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.GCD
open Core.Polynomial.Unique

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  A.  masked_prod structural helpers.                             *)
(* ================================================================ *)

(* an all-false mask collapses the masked product to poly_one. *)
let rec masked_prod_all_false (#t:Type) {| f: field t |}
  (hs: list (polynomial t)) (mask: list bool)
  : Lemma (requires (forall (a:nat). a < L.length mask ==> L.index mask a == false))
          (ensures  SP.masked_prod hs mask == poly_one #t)
          (decreases hs)
  = match hs, mask with
    | h :: rest, b :: m' ->
        assert (L.index mask 0 == false);              (* b == false *)
        assert (forall (a:nat). a < L.length m' ==>
                  L.index m' a == L.index mask (a ++ 1));
        masked_prod_all_false rest m';
        SP.masked_prod_cons_false h rest m'
    | [], _ -> SP.masked_prod_nil #t mask
    | h :: rest, [] -> SP.masked_prod_mask_nil (h :: rest)

(* a kept index divides the masked product. *)
let rec masked_prod_kept_index_divides (#t:Type) {| f: field t |}
  (hs: list (polynomial t)) (mask: list bool) (k:nat)
  : Lemma (requires k < L.length hs /\ k < L.length mask /\ L.index mask k == true)
          (ensures  divides #(polynomial t) (L.index hs k) (SP.masked_prod hs mask))
          (decreases hs)
  = H.elim_equatable_laws (polynomial t) ();
    match hs, mask with
    | h :: rest, b :: m' ->
        let mp = SP.masked_prod rest m' in
        if k = 0 then begin
          SP.masked_prod_cons_true h rest m';          (* masked == h * mp *)
          divides_intro #(polynomial t) (L.index hs 0) (h * mp) mp
        end else begin
          masked_prod_kept_index_divides rest m' (k - 1);  (* rest[k-1] | mp *)
          if b then begin
            SP.masked_prod_cons_true h rest m';        (* masked == h * mp *)
            divides_mul_left #(polynomial t) (L.index rest (k - 1)) h mp
          end else
            SP.masked_prod_cons_false h rest m'        (* masked == mp *)
        end
    | _ -> ()

(* a mask whose only true bit is k collapses to  hs_k  (up to associate). *)
let rec masked_prod_singleton_eq (#t:Type) {| f: field t |}
  (hs: list (polynomial t)) (mask: list bool) (k:nat)
  : Lemma (requires k < L.length hs /\ k < L.length mask /\
                    L.index mask k == true /\
                    (forall (a:nat). a < L.length mask /\ a <> k ==> L.index mask a == false))
          (ensures  (SP.masked_prod hs mask) = (L.index hs k))
          (decreases hs)
  = H.elim_equatable_laws (polynomial t) ();
    match hs, mask with
    | h :: rest, b :: m' ->
        if k = 0 then begin
          SP.masked_prod_cons_true h rest m';          (* masked == h * mp *)
          assert (forall (a:nat). a < L.length m' ==>
                    L.index m' a == L.index mask (a ++ 1));
          masked_prod_all_false rest m';               (* mp == poly_one *)
          poly_mul_one h                               (* h * poly_one = h == hs_0 *)
        end else begin
          assert (L.index mask 0 == false);            (* b == false *)
          SP.masked_prod_cons_false h rest m';         (* masked == mp *)
          assert (L.index m' (k - 1) == L.index mask k);
          assert (forall (a:nat). a < L.length m' /\ a <> k - 1 ==>
                    L.index m' a == L.index mask (a ++ 1));
          masked_prod_singleton_eq rest m' (k - 1)
        end
    | _ -> ()

(* ================================================================ *)
(*  B.  a masked product with NO true bit is a unit — so a factor    *)
(*      of degree >= 1 forces its mask to be nonempty.               *)
(* ================================================================ *)

let mask_has_true (#t:Type) {| f: field t |}
  (irs: list (polynomial t)) (mask: list bool) (c: t) (g: polynomial t)
  : Lemma (requires not (c = zero) /\ (g = (poly_const c * SP.masked_prod irs mask)) /\
                    deg g >= 1)
          (ensures  (exists (a:nat). a < L.length mask /\ L.index mask a == true))
  = H.elim_equatable_laws (polynomial t) ();
    let no_true () : Lemma (requires (forall (a:nat). a < L.length mask ==>
                                        L.index mask a == false))
                           (ensures  False)
      = masked_prod_all_false irs mask;                (* masked_prod == poly_one *)
        mul_congruence (poly_const c) (SP.masked_prod irs mask)
                       (poly_const c) (poly_one #t);   (* g's rhs = poly_const c * poly_one *)
        poly_mul_one (poly_const c);                   (* poly_const c * poly_one = poly_const c *)
        poly_eq_transitivity g (poly_const c * SP.masked_prod irs mask)
                             (poly_const c * poly_one #t);
        poly_eq_transitivity g (poly_const c * poly_one #t) (poly_const c);
        poly_const_deg c;                              (* deg (poly_const c) == 0 *)
        degree_well_defined g (poly_const c)           (* deg g == 0 : contra deg g >= 1 *)
    in
    Classical.move_requires no_true ()

(* ================================================================ *)
(*  C.  small structural helpers.                                    *)
(* ================================================================ *)

(* an irreducible polynomial has degree >= 1. *)
let irr_deg1 (#t:Type) {| f: field t |} (q: polynomial t)
  : Lemma (requires IR.poly_irreducible q) (ensures deg q >= 1) = ()

(* ================================================================ *)
(*  D.  THE PIGEONHOLE THEOREM.                                       *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let pigeonhole_all_irreducible (#t:Type) {| f: field t |}
  (fs irs: list (polynomial t))
  : Lemma (requires
             IR.pairwise_coprime fs /\
             (forall (i:nat). i < L.length fs ==> deg (L.index fs i) >= 1) /\
             SP.all_irreducible irs /\
             divides #(polynomial t) (PR.poly_prod fs) (PR.poly_prod irs) /\
             L.length fs == L.length irs)
          (ensures  SP.all_irreducible fs)
  = H.elim_equatable_laws (polynomial t) ();
    let r : nat = L.length fs in
    (* --- per-index subset-product existence --------------------- *)
    let decomp_exists (i:nat{i < r})
      : Lemma (exists (pr:(t & list bool)).
                 L.length (snd pr) == r /\ not (fst pr = zero) /\
                 (L.index fs i = (poly_const (fst pr) * SP.masked_prod irs (snd pr))))
      = BC.poly_prod_index_divides fs i;               (* fs_i | ∏fs *)
        divides_trans #(polynomial t)
          (L.index fs i) (PR.poly_prod fs) (PR.poly_prod irs);  (* fs_i | ∏irs *)
        SP.divisor_of_irreducible_prod irs (L.index fs i);
        eliminate exists (c:t) (mask:list bool).
                    L.length mask == L.length irs /\ not (c = zero) /\
                    (L.index fs i = (poly_const c * SP.masked_prod irs mask))
        returns (exists (pr:(t & list bool)).
                   L.length (snd pr) == r /\ not (fst pr = zero) /\
                   (L.index fs i = (poly_const (fst pr) * SP.masked_prod irs (snd pr))))
        with _. introduce exists (pr:(t & list bool)).
                            L.length (snd pr) == r /\ not (fst pr = zero) /\
                            (L.index fs i = (poly_const (fst pr) * SP.masked_prod irs (snd pr)))
                with (c, mask) and ()
    in
    let decomp (i:nat{i < r})
      : GTot (pr:(t & list bool){
                L.length (snd pr) == r /\ not (fst pr = zero) /\
                (L.index fs i = (poly_const (fst pr) * SP.masked_prod irs (snd pr)))})
      = decomp_exists i;
        ID.indefinite_description_ghost (t & list bool)
          (fun pr -> L.length (snd pr) == r /\ not (fst pr = zero) /\
                     (L.index fs i = (poly_const (fst pr) * SP.masked_prod irs (snd pr))))
    in
    let cc (i:nat{i < r}) : GTot t = fst (decomp i) in
    let mm (i:nat{i < r}) : GTot (list bool) = snd (decomp i) in
    (* --- DISJOINTNESS of the masks ------------------------------ *)
    let disjoint (i:nat{i < r}) (j:nat{j < r}) (k:nat{k < r})
      : Lemma (requires i <> j /\ L.index (mm i) k == true /\ L.index (mm j) k == true)
              (ensures  False)
      = let qk = L.index irs k in
        SP.all_irreducible_elim irs;
        L.lemma_index_memP irs k;                      (* IR.poly_irreducible qk *)
        irr_deg1 qk;                                   (* deg qk >= 1 *)
        (* qk | fs_i *)
        masked_prod_kept_index_divides irs (mm i) k;
        divides_mul_left #(polynomial t) qk (poly_const (cc i)) (SP.masked_prod irs (mm i));
        poly_eq_symmetry (L.index fs i) (poly_const (cc i) * SP.masked_prod irs (mm i));
        divides_congruence_right #(polynomial t) qk
          (poly_const (cc i) * SP.masked_prod irs (mm i)) (L.index fs i);
        (* qk | fs_j *)
        masked_prod_kept_index_divides irs (mm j) k;
        divides_mul_left #(polynomial t) qk (poly_const (cc j)) (SP.masked_prod irs (mm j));
        poly_eq_symmetry (L.index fs j) (poly_const (cc j) * SP.masked_prod irs (mm j));
        divides_congruence_right #(polynomial t) qk
          (poly_const (cc j) * SP.masked_prod irs (mm j)) (L.index fs j);
        (* qk | gcd(fs_i,fs_j) ; coprime ⟹ deg gcd = 0 ; contra deg qk >= 1 *)
        let gi = L.index fs i in
        let gj = L.index fs j in
        IR.pairwise_coprime_elim fs;                   (* coprime gi gj *)
        gcd_is_maximal gi gj qk;                       (* qk | poly_gcd gi gj *)
        coprime_reveal gi gj;                          (* deg (poly_gcd gi gj) == 0 *)
        IR.divides_degree_le qk (poly_gcd gi gj)
    in
    (* --- NONEMPTY: each mask has a true bit; pick one ----------- *)
    let chosen_exists (i:nat{i < r})
      : Lemma (exists (a:nat). a < r /\ L.index (mm i) a == true)
      = mask_has_true irs (mm i) (cc i) (L.index fs i)
    in
    let chosen (i:nat{i < r}) : GTot (a:nat{a < r /\ L.index (mm i) a == true})
      = chosen_exists i;
        ID.indefinite_description_ghost (a:nat{a < r})
          (fun a -> L.index (mm i) a == true)
    in
    (* chosen is INJECTIVE (disjointness). *)
    let chosen_inj (a:nat{a < r}) (b:nat{b < r})
      : Lemma (requires chosen a == chosen b) (ensures a == b)
      = if a = b then ()
        else disjoint a b (chosen a)
    in
    (* --- per-index IRREDUCIBILITY ------------------------------- *)
    let irr_at (i:nat{i < r}) : Lemma (IR.poly_irreducible (L.index fs i))
      = let k0 = chosen i in                           (* mm i true at k0 *)
        (* singleton: every true bit of (mm i) equals k0 (via surjectivity) *)
        let uniq (a:nat) : Lemma (a < r /\ L.index (mm i) a == true ==> a == k0)
          = let step () : Lemma (requires a < r /\ L.index (mm i) a == true)
                                 (ensures  a == k0)
              = FIS.fin_inj_surj r chosen chosen_inj a;
                eliminate exists (i':nat). i' < r /\ chosen i' == a
                returns a == k0
                with _.
                  if i' = i then ()                    (* chosen i == a == k0 *)
                  else disjoint i i' a                 (* both true at a : ⊥ *)
            in
            Classical.move_requires step ()
        in
        Classical.forall_intro uniq;
        (* mm i is the singleton mask at k0 *)
        masked_prod_singleton_eq irs (mm i) k0;        (* masked_prod irs (mm i) = irs_{k0} *)
        let qk = L.index irs k0 in
        SP.all_irreducible_elim irs;
        L.lemma_index_memP irs k0;                     (* IR.poly_irreducible qk *)
        poly_const_deg (cc i);                         (* deg (poly_const (cc i)) == 0 *)
        (* fs_i = poly_const c * masked = poly_const c * qk = qk * poly_const c *)
        mul_congruence (poly_const (cc i)) (SP.masked_prod irs (mm i)) (poly_const (cc i)) qk;
        poly_eq_transitivity (L.index fs i)
          (poly_const (cc i) * SP.masked_prod irs (mm i))
          (poly_const (cc i) * qk);
        mul_commutativity (poly_const (cc i)) qk;      (* poly_const c * qk = qk * poly_const c *)
        poly_eq_transitivity (L.index fs i)
          (poly_const (cc i) * qk) (qk * poly_const (cc i));
        BC.irreducible_associate qk (poly_const (cc i)) (L.index fs i)
    in
    (* --- assemble all_irreducible fs ---------------------------- *)
    let pir (h: polynomial t{L.memP h fs}) : Lemma (IR.poly_irreducible h)
      = let k = L.index_of fs h in
        irr_at k
    in
    SP.all_irreducible_intro fs pir
#pop-options
