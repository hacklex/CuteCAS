module Core.Modular.PrimeField.BerlekampDimCount

(* ================================================================ *)
(*  #29 STAGE C4:  the explicit Berlekamp cardinality  |B(f)| = p^r. *)
(*                                                                   *)
(*  For  f = poly_prod fs  with  fs = [f_0; ...; f_{r-1}]  pairwise  *)
(*  coprime irreducible factors over  fp p  (each deg >= 1),  the    *)
(*  Berlekamp set                                                    *)
(*     B(f) = { h : deg h < deg f  /\  h^p ≡ h  (mod f) }             *)
(*  is FINITE with exactly  p^r  elements.  Concretely we exhibit a   *)
(*  list  bs  with  no_repeats_p bs,  |bs| = p^r,  and                *)
(*     memP h bs  <==>  is_berlekamp p f h.                           *)
(*                                                                   *)
(*  Ingredients (all from STAGE C, module BerlekampDim):             *)
(*   - crt_const_witness : every constant r-tuple has a fixed witness *)
(*   - realizes_tuple / crt_const_inj / comp_tuple_unique            *)
(*   - berlekamp_structure : is_berlekamp <=> constant-mod-every-factor*)
(*  New here:                                                         *)
(*   - enum_tuples : the Cartesian power  (fp p)^r  as a list        *)
(*     (+ length = p^r, distinct, membership characterization)       *)
(*   - berlekamp_reduce : reduce the witness mod f (SURJECTIVITY)     *)
(*   - extract_tuple : recover the constant tuple of any h in B(f)    *)
(*   - berlekamp_count : the capstone assembly.                       *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module EU  = Core.NumberTheory
module CRT = Core.Polynomial.CRTMulti
module IR  = Core.Polynomial.Irreducible
module ID  = FStar.IndefiniteDescription

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Algebra.CongruenceMod
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.Roots
open Core.Modular.PrimeField
open Core.Modular.PrimeField.Berlekamp
open Core.Modular.PrimeField.BerlekampDim

#set-options "--fuel 1 --ifuel 1 --z3rlimit 10"

(* ================================================================ *)
(*  0.  A small nat exponent.                                         *)
(* ================================================================ *)

let rec pow (base:int{base > 1}) (n:nat) : Tot (r:int{r >= 1}) (decreases n)
  = if n = 0 then 1 else base `Prims.op_Star` pow base (n - 1)

let pow_succ (base:int{base > 1}) (n:nat{n >= 1})
  : Lemma (pow base n == base `Prims.op_Star` pow base (n - 1)) = ()

(* ================================================================ *)
(*  1.  poly_eq  ==>  propositional  ==   (canonical trimmed reps).   *)
(* ================================================================ *)

let poly_eq_prop (p:int{EU.is_prime p}) (a b: polynomial (fp p))
  : Lemma (requires poly_eq #(fp p) a b) (ensures a == b)
  = poly_eq_length #(fp p) a b;
    let ipf (i:nat) : Lemma (i < L.length a ==> L.index a i == L.index b i)
      = if i < L.length a then poly_eq_means_equal_coeffs #(fp p) a b i
    in
    Classical.forall_intro ipf;
    L.index_extensionality a b

(* ================================================================ *)
(*  2.  Cartesian-power enumeration  enum_tuples p r  =  (fp p)^r.    *)
(*      (Pure list lemmas: length p^r, distinct, len_r, membership.)  *)
(* ================================================================ *)

let lcons (#a:Type) (c:a) (t: list a) : list a = c :: t
let cons_block (#a:Type) (c:a) (ts: list (list a)) : list (list a) = L.map (lcons c) ts

(* NAMED block function so enum_tuples and its lemmas share ONE symbol
   (avoids inline-lambda unification failures). *)
let block_of (#a:Type) (prev: list (list a)) (c: a) : list (list a) = cons_block c prev

let block_of_unfold (#a:Type) (prev: list (list a)) (c: a)
  : Lemma (block_of prev c == L.map (lcons c) prev) = ()

let rec map_length_lemma (#a #b:Type) (f: a -> b) (l: list a)
  : Lemma (ensures L.length (L.map f l) == L.length l) (decreases l)
  = match l with | [] -> () | _ :: tl -> map_length_lemma f tl

(* length of concatMap of cons-blocks: |prev| * |cs|  (no forall / trigger). *)
let rec concat_blocks_length (#a:Type) (prev: list (list a)) (cs: list a)
  : Lemma (ensures L.length (L.concatMap (block_of prev) cs)
                   == L.length prev `Prims.op_Star` L.length cs)
          (decreases cs)
  = match cs with
    | [] -> ()
    | c :: tl ->
        concat_blocks_length prev tl;
        block_of_unfold prev c;
        map_length_lemma (lcons c) prev;
        L.append_length (block_of prev c) (L.concatMap (block_of prev) tl)

let rec mem_concatMap (#a #b: Type) (f: a -> list b) (y: a) (xs: list a) (x: b)
  : Lemma (requires L.memP y xs /\ L.memP x (f y))
          (ensures L.memP x (L.concatMap f xs))
  = match xs with
    | [] -> ()
    | h :: tl ->
        L.append_memP (f h) (L.concatMap f tl) x;
        let aux () : Lemma (requires L.memP y tl) (ensures L.memP x (L.concatMap f tl))
          = mem_concatMap f y tl x in
        Classical.move_requires aux ()

let rec concatMap_mem_elim (#a #b: Type) (f: a -> list b) (xs: list a) (x: b)
  : Lemma (requires L.memP x (L.concatMap f xs))
          (ensures exists (y:a). L.memP y xs /\ L.memP x (f y))
          (decreases xs)
  = match xs with
    | [] -> ()
    | h :: tl ->
        L.append_memP (f h) (L.concatMap f tl) x;
        eliminate (L.memP x (f h)) \/ (L.memP x (L.concatMap f tl))
        returns exists (y:a). L.memP y xs /\ L.memP x (f y)
        with _l. ()
        and  _r. concatMap_mem_elim f tl x

(* no_repeats through an injective map (injectivity as a per-pair proof-fn). *)
let rec no_repeats_map_inj (#a #b:Type) (g: a -> b) (l: list a)
  (inj: (x:a) -> (y:a) -> Lemma (requires L.memP x l /\ L.memP y l /\ g x == g y)
                                (ensures x == y))
  : Lemma (requires L.no_repeats_p l) (ensures L.no_repeats_p (L.map g l))
  = match l with
    | [] -> ()
    | x0 :: rest ->
        let inj' (x:a) (y:a)
          : Lemma (requires L.memP x rest /\ L.memP y rest /\ g x == g y) (ensures x == y)
          = inj x y in
        no_repeats_map_inj g rest inj';
        let contra () : Lemma (requires L.memP (g x0) (L.map g rest)) (ensures False)
          = L.memP_map_elim g (g x0) rest;
            eliminate exists (y:a). L.memP y rest /\ g y == g x0
            returns False
            with _pf.
              ( inj x0 y;
                assert (L.memP x0 rest) )
        in
        Classical.move_requires contra ()

let no_repeats_cons_block (#a:Type) (c:a) (ts: list (list a))
  : Lemma (requires L.no_repeats_p ts) (ensures L.no_repeats_p (cons_block c ts))
  = let inj (x y: list a)
      : Lemma (requires L.memP x ts /\ L.memP y ts /\ lcons c x == lcons c y) (ensures x == y)
      = () in
    no_repeats_map_inj (lcons c) ts inj

(* every element of a cons-block starts with the block head. *)
let block_mem_head (#a:Type) (c:a) (prev: list (list a)) (x: list a)
  : Lemma (requires L.memP x (block_of prev c)) (ensures Cons? x /\ L.hd x == c)
  = block_of_unfold prev c;
    L.memP_map_elim (lcons c) x prev;
    eliminate exists (t: list a). L.memP t prev /\ lcons c t == x
    returns Cons? x /\ L.hd x == c
    with _pf. ()

(* distinctness of the concatMap of cons-blocks over distinct heads. *)
let rec concat_blocks_distinct (#a:Type) (prev: list (list a)) (cs: list a)
  : Lemma (requires L.no_repeats_p prev /\ L.no_repeats_p cs)
          (ensures  L.no_repeats_p (L.concatMap (block_of prev) cs))
          (decreases cs)
  = match cs with
    | [] -> ()
    | c0 :: tl ->
        concat_blocks_distinct prev tl;
        no_repeats_cons_block c0 prev;
        let dpf (x: list a)
          : Lemma (requires L.memP x (block_of prev c0))
                  (ensures ~ (L.memP x (L.concatMap (block_of prev) tl)))
          = block_mem_head c0 prev x;
            let contra () : Lemma (requires L.memP x (L.concatMap (block_of prev) tl))
                                  (ensures False)
              = concatMap_mem_elim (block_of prev) tl x;
                eliminate exists (c': a). L.memP c' tl /\ L.memP x (block_of prev c')
                returns False
                with _pf.
                  ( block_mem_head c' prev x;
                    assert (L.memP c0 tl) )
            in Classical.move_requires contra ()
        in
        Classical.forall_intro (Classical.move_requires dpf);
        L.no_repeats_p_append_intro (block_of prev c0) (L.concatMap (block_of prev) tl)

let rec enum_tuples (p:int{p > 1}) (r:nat) : Tot (list (list (fp p))) (decreases r)
  = if r = 0 then [ [] ]
    else L.concatMap (block_of #(fp p) (enum_tuples p (r - 1))) (fp_enum p)

let enum_tuples_succ (p:int{p > 1}) (r:nat{r >= 1})
  : Lemma (enum_tuples p r ==
           L.concatMap (block_of #(fp p) (enum_tuples p (r - 1))) (fp_enum p))
  = ()

#push-options "--fuel 2 --ifuel 2"
let rec enum_tuples_len_r (p:int{p > 1}) (r:nat) (cs: list (fp p))
  : Lemma (requires L.memP cs (enum_tuples p r)) (ensures L.length cs == r) (decreases r)
  = if r = 0 then (assert (cs == []))
    else begin
      let prev = enum_tuples p (r - 1) in
      enum_tuples_succ p r;
      concatMap_mem_elim (block_of #(fp p) prev) (fp_enum p) cs;
      eliminate exists (c: fp p). L.memP c (fp_enum p) /\ L.memP cs (block_of #(fp p) prev c)
      returns L.length cs == r
      with _pf.
        ( block_of_unfold #(fp p) prev c;
          L.memP_map_elim (lcons c) cs prev;
          eliminate exists (t: list (fp p)). L.memP t prev /\ lcons c t == cs
          returns L.length cs == r
          with _pf2.
            ( enum_tuples_len_r p (r - 1) t ) )
    end
#pop-options

#push-options "--fuel 2 --ifuel 1"
let rec enum_tuples_length (p:int{p > 1}) (r:nat)
  : Lemma (ensures L.length (enum_tuples p r) == pow p r) (decreases r)
  = if r = 0 then ()
    else begin
      let prev = enum_tuples p (r - 1) in
      enum_tuples_length p (r - 1);
      concat_blocks_length #(fp p) prev (fp_enum p);
      enum_tuples_succ p r;
      assert (L.length (enum_tuples p r) ==
              L.length prev `Prims.op_Star` L.length (fp_enum p));
      fp_enum_length p;
      pow_succ p r
    end
#pop-options

let rec enum_tuples_mem (p:int{p > 1}) (r:nat) (cs: list (fp p))
  : Lemma (requires L.length cs == r) (ensures L.memP cs (enum_tuples p r)) (decreases r)
  = if r = 0 then ()
    else begin
      match cs with
      | c0 :: rest ->
          let prev = enum_tuples p (r - 1) in
          enum_tuples_mem p (r - 1) rest;
          fp_enum_complete p c0;
          L.mem_memP c0 (fp_enum p);
          L.memP_map_intro (lcons c0) rest prev;
          block_of_unfold #(fp p) prev c0;
          assert (L.memP cs (block_of #(fp p) prev c0));
          enum_tuples_succ p r;
          mem_concatMap (block_of #(fp p) prev) c0 (fp_enum p) cs
    end

(* fp_enum p has no repeats:  the elements 0..p-1 are pairwise distinct. *)
let rec fp_enum_from_norepeats (p:int{EU.is_prime p}) (lo:nat{lo <= p})
  : Lemma (ensures L.no_repeats_p (fp_enum_from p lo)) (decreases (p - lo))
  = if lo = p then ()
    else begin
      fp_enum_from_norepeats p (lo ++ 1);
      let tail = fp_enum_from p (lo ++ 1) in
      let c0 : fp p = lo in
      let contra () : Lemma (requires L.memP c0 tail) (ensures False)
        = L.mem_memP c0 tail;
          fp_enum_from_mem p (lo ++ 1) c0
      in Classical.move_requires contra ();
      L.no_repeats_p_cons c0 tail
    end

let fp_enum_norepeats (p:int{EU.is_prime p})
  : Lemma (L.no_repeats_p (fp_enum p))
  = fp_enum_from_norepeats p 0

#push-options "--fuel 2 --ifuel 2"
let rec enum_tuples_distinct (p:int{EU.is_prime p}) (r:nat)
  : Lemma (ensures L.no_repeats_p (enum_tuples p r)) (decreases r)
  = if r = 0 then ()
    else begin
      let prev = enum_tuples p (r - 1) in
      enum_tuples_distinct p (r - 1);
      fp_enum_norepeats p;
      concat_blocks_distinct #(fp p) prev (fp_enum p);
      enum_tuples_succ p r;
      assert (L.no_repeats_p (L.concatMap (block_of #(fp p) prev) (fp_enum p)))
    end
#pop-options

(* ================================================================ *)
(*  3.  REDUCTION.  From a fixed (unreduced) witness w for a tuple   *)
(*      cs to the reduced residue  h = w mod f  in  B(f).            *)
(*      Gives SURJECTIVITY of  cs |-> h  onto  B(f).                 *)
(* ================================================================ *)

let berlekamp_reduce (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (cs: list (fp p))
  : Pure (polynomial (fp p))
      (requires IR.pairwise_coprime fs /\ all_irreducible p fs /\
                L.length cs == L.length fs)
      (ensures  fun h -> realizes_tuple p fs h cs /\
                         is_berlekamp p (poly_prod fs) h)
  = let f : polynomial (fp p) = poly_prod fs in
    let w = crt_const_witness p fs cs in
    irred_gives_deg_ge1 p fs;
    CRT.deg_prod_nonneg fs;                          (* deg f >= 0 *)
    let q = poly_div w f in
    let h = poly_rem w f in                          (* w = f*q + h, deg h < deg f *)
    cong_of_divmod #(polynomial (fp p)) w f q h;     (* cong f w h, i.e. f | (w -- h) *)
    realizes_tuple_elim p fs w cs;
    let rpf (i:nat{i < L.length fs /\ i < L.length cs})
      : Lemma (divides #(polynomial (fp p)) (L.index fs i)
                       (h -- (poly_const #(fp p) (L.index cs i))))
      = let ci : polynomial (fp p) = poly_const #(fp p) (L.index cs i) in
        realizes_tuple_elim p fs w cs;               (* f_i | (w -- ci) *)
        CRT.prod_factor_divides fs i;                (* f_i | f *)
        divides_trans (L.index fs i) f (w -- h);     (* f_i | (w -- h) *)
        divides_sub (L.index fs i) (w -- ci) (w -- h);
        sub_from_common w ci h;                      (* (w--ci)--(w--h) = h -- ci *)
        divides_congruence_right (L.index fs i) ((w -- ci) -- (w -- h)) (h -- ci)
    in
    realizes_tuple_intro p fs h cs rpf;
    realizes_gives_comp_const p fs h cs;             (* all_comp_const p fs h *)
    c3 p fs h;                                        (* cong f (h^p) h *)
    h

(* Total wrapper so we can  L.map  it over the enumeration (the two
   structural side-conditions travel as squash arguments; the length
   guard picks the reduced witness on well-formed tuples). *)
let bwitness (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (_: squash (IR.pairwise_coprime fs)) (_: squash (all_irreducible p fs))
  (cs: list (fp p))
  : polynomial (fp p)
  = if L.length cs = L.length fs then berlekamp_reduce p fs cs
    else poly_zero #(fp p)

let bwitness_reduce (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (s1: squash (IR.pairwise_coprime fs)) (s2: squash (all_irreducible p fs))
  (cs: list (fp p))
  : Lemma (requires L.length cs == L.length fs)
          (ensures  bwitness p fs s1 s2 cs == berlekamp_reduce p fs cs)
  = ()

(* ================================================================ *)
(*  4.  TUPLE UNIQUENESS.  Two constant tuples realized by the SAME  *)
(*      residue are equal  (list index-extensionality of the         *)
(*      per-factor uniqueness  comp_tuple_unique).                    *)
(* ================================================================ *)

let tuple_ext (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p)) (cs cs': list (fp p))
  : Lemma (requires all_irreducible p fs /\
                    realizes_tuple p fs h cs /\ realizes_tuple p fs h cs' /\
                    L.length cs == L.length fs /\ L.length cs' == L.length fs)
          (ensures  cs == cs')
  = realizes_tuple_elim p fs h cs;
    realizes_tuple_elim p fs h cs';
    all_irreducible_elim p fs;
    let ipf (i:nat) : Lemma (i < L.length cs ==> L.index cs i == L.index cs' i)
      = if i < L.length cs then
          comp_tuple_unique p (L.index fs i) h (L.index cs i) (L.index cs' i)
    in
    Classical.forall_intro ipf;
    L.index_extensionality cs cs'

(* ================================================================ *)
(*  5.  EXTRACTION.  Every  h  in  B(f)  determines its constant      *)
(*      tuple  cs  (ghost, via indefinite description on each         *)
(*      per-factor kernel witness).                                   *)
(* ================================================================ *)

let extract_const (p:int{EU.is_prime p}) (q h: polynomial (fp p))
  : Ghost (fp p)
      (requires kernel_is_const_shifted p q h)
      (ensures  fun c -> divides #(polynomial (fp p)) q (h -- (poly_const #(fp p) c)))
  = kernel_is_const_shifted_elim p q h;
    ID.indefinite_description_ghost (fp p)
      (fun c -> divides #(polynomial (fp p)) q (h -- (poly_const #(fp p) c)))

let all_comp_const_head (p:int{EU.is_prime p}) (q0: polynomial (fp p))
  (rest: list (polynomial (fp p))) (h: polynomial (fp p))
  : Lemma (requires all_comp_const p (q0 :: rest) h)
          (ensures  kernel_is_const_shifted p q0 h)
  = all_comp_const_elim p (q0 :: rest) h;
    assert (L.index (q0 :: rest) 0 == q0)

let all_comp_const_tail (p:int{EU.is_prime p}) (q0: polynomial (fp p))
  (rest: list (polynomial (fp p))) (h: polynomial (fp p))
  : Lemma (requires all_comp_const p (q0 :: rest) h)
          (ensures  all_comp_const p rest h)
  = all_comp_const_elim p (q0 :: rest) h;
    let pf (i:nat{i < L.length rest})
      : Lemma (kernel_is_const_shifted p (L.index rest i) h)
      = all_comp_const_elim p (q0 :: rest) h;
        assert (L.index (q0 :: rest) (i ++ 1) == L.index rest i)
    in
    all_comp_const_intro p rest h pf

let rec extract_tuple (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p))
  : Ghost (list (fp p))
      (requires all_comp_const p fs h)
      (ensures  fun cs -> L.length cs == L.length fs /\ realizes_tuple p fs h cs)
      (decreases fs)
  = match fs with
    | [] ->
        realizes_tuple_intro p [] h [] (fun i -> ());
        []
    | q0 :: rest ->
        all_comp_const_head p q0 rest h;
        all_comp_const_tail p q0 rest h;
        let c0 = extract_const p q0 h in
        let cs' = extract_tuple p rest h in
        realizes_tuple_elim p rest h cs';
        let rpf (i:nat{i < L.length (q0 :: rest) /\ i < L.length (c0 :: cs')})
          : Lemma (divides #(polynomial (fp p)) (L.index (q0 :: rest) i)
                          (h -- (poly_const #(fp p) (L.index (c0 :: cs') i))))
          = if i = 0 then ()
            else begin
              realizes_tuple_elim p rest h cs';
              assert (L.index (q0 :: rest) i == L.index rest (i - 1));
              assert (L.index (c0 :: cs') i == L.index cs' (i - 1))
            end
        in
        realizes_tuple_intro p (q0 :: rest) h (c0 :: cs') rpf;
        c0 :: cs'

(* ================================================================ *)
(*  6.  THE CAPSTONE:  |B(f)| = p^r.                                  *)
(* ================================================================ *)

let berlekamp_count (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  : Lemma (requires IR.pairwise_coprime fs /\ all_irreducible p fs)
          (ensures  exists (bs: list (polynomial (fp p))).
                       L.no_repeats_p bs /\
                       L.length bs == pow p (L.length fs) /\
                       (forall (h: polynomial (fp p)).
                          L.memP h bs <==> is_berlekamp p (poly_prod fs) h))
  = let r : nat = L.length fs in
    let s1 : squash (IR.pairwise_coprime fs) = () in
    let s2 : squash (all_irreducible p fs) = () in
    let g : (list (fp p) -> polynomial (fp p)) = bwitness p fs s1 s2 in
    let tuples = enum_tuples p r in
    let bs = L.map g tuples in
    (* length *)
    enum_tuples_length p r;
    map_length_lemma g tuples;                       (* |bs| == |tuples| == p^r *)
    (* distinctness: g injective on the (length-r) enumerated tuples. *)
    enum_tuples_distinct p r;
    let inj (cs cs': list (fp p))
      : Lemma (requires L.memP cs tuples /\ L.memP cs' tuples /\ g cs == g cs')
              (ensures  cs == cs')
      = enum_tuples_len_r p r cs;
        enum_tuples_len_r p r cs';
        bwitness_reduce p fs s1 s2 cs;
        bwitness_reduce p fs s1 s2 cs';
        let h1 = berlekamp_reduce p fs cs in         (* realizes p fs h1 cs *)
        let h2 = berlekamp_reduce p fs cs' in        (* realizes p fs h2 cs' ; h1 == h2 *)
        tuple_ext p fs h1 cs cs'
    in
    no_repeats_map_inj g tuples inj;                 (* no_repeats_p bs *)
    (* membership characterization *)
    let memchar (h: polynomial (fp p))
      : Lemma (L.memP h bs <==> is_berlekamp p (poly_prod fs) h)
      = introduce L.memP h bs ==> is_berlekamp p (poly_prod fs) h
        with _pf.
          ( L.memP_map_elim g h tuples;
            eliminate exists (cs: list (fp p)). L.memP cs tuples /\ g cs == h
            returns is_berlekamp p (poly_prod fs) h
            with _p2.
              ( enum_tuples_len_r p r cs;
                bwitness_reduce p fs s1 s2 cs;
                let h1 = berlekamp_reduce p fs cs in (* is_berlekamp p f h1 ; g cs == h1 == h *)
                () ) );
        introduce is_berlekamp p (poly_prod fs) h ==> L.memP h bs
        with _pf.
          ( berlekamp_structure p fs h;              (* deg h < deg f /\ all_comp_const p fs h *)
            let cs = extract_tuple p fs h in          (* ghost: |cs| == r /\ realizes p fs h cs *)
            enum_tuples_mem p r cs;                   (* memP cs tuples *)
            bwitness_reduce p fs s1 s2 cs;            (* g cs == berlekamp_reduce p fs cs *)
            let h1 = berlekamp_reduce p fs cs in      (* realizes p fs h1 cs ; deg h1 < deg f *)
            crt_const_inj p fs cs h h1;               (* h = h1  (poly_eq) *)
            poly_eq_prop p h h1;                      (* h == h1 ;  g cs == h1 == h *)
            L.memP_map_intro g cs tuples )            (* memP (g cs) bs *)
    in
    Classical.forall_intro memchar;
    introduce exists (bs0: list (polynomial (fp p))).
                L.no_repeats_p bs0 /\
                L.length bs0 == pow p (L.length fs) /\
                (forall (h: polynomial (fp p)).
                   L.memP h bs0 <==> is_berlekamp p (poly_prod fs) h)
    with bs and ()
