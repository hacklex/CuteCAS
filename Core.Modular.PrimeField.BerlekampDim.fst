module Core.Modular.PrimeField.BerlekampDim

(* ================================================================ *)
(*  #29 STAGE C: the Berlekamp structure theorem.                    *)
(*                                                                   *)
(*  For  f = poly_prod fs  with  fs = [f_0; ...; f_{r-1}]  a list of  *)
(*  DISTINCT irreducible factors over  fp p  (pairwise coprime, each  *)
(*  of degree >= 1), the Berlekamp set                               *)
(*     B(f) = { h : deg h < deg f  /\  h^p ≡ h  (mod f) }             *)
(*  decomposes componentwise: a residue is Frobenius-fixed mod f iff  *)
(*  it is fixed modulo every factor f_i, iff modulo each f_i it is    *)
(*  congruent to a constant of  fp p.  Hence  B(f)  is in bijection   *)
(*  with r-tuples of constants  (fp p)^r,  and  |B(f)| = p^r.         *)
(*                                                                   *)
(*  C1  congruence decomposition   (CRT-split the divisibility)      *)
(*  C2  per-component <=> constant  (Frobenius fixed = a constant)   *)
(*  C3  structure theorem          (assemble C1+C2)                  *)
(*  + CRT bijection scaffolding (inj/surj) toward the p^r count.     *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module IR  = Core.Polynomial.Irreducible
module CRT = Core.Polynomial.CRTMulti

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Algebra.CongruenceMod
open Core.Tactics.CanonRing
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Roots
open Core.Modular.PrimeField
open Core.Modular.PrimeField.Berlekamp
module EU  = Core.NumberTheory

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  Opaque list-predicates (no raw quantifiers in business lemmas).  *)
(* ================================================================ *)

(* -- every factor is irreducible. *)
[@@"opaque_to_smt"]
let all_irreducible (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  : prop = forall (i:nat). i < L.length fs ==> IR.poly_irreducible #(fp p) (L.index fs i)

let all_irreducible_elim (p:int{EU.is_prime p})
  (fs: list (polynomial (fp p)){all_irreducible p fs})
  : Lemma (forall (i:nat). i < L.length fs ==> IR.poly_irreducible #(fp p) (L.index fs i))
  = reveal_opaque (`%all_irreducible) (all_irreducible p fs)

let all_irreducible_proof (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  = (i:nat{i < L.length fs}) -> Lemma (IR.poly_irreducible #(fp p) (L.index fs i))

let all_irreducible_intro (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (proof: all_irreducible_proof p fs)
  : Lemma (all_irreducible p fs)
  = reveal_opaque (`%all_irreducible) (all_irreducible p fs);
    let aux (i:nat) : Lemma (i < L.length fs ==> IR.poly_irreducible #(fp p) (L.index fs i))
      = if i < L.length fs then proof i else ()
    in
    Classical.forall_intro aux

(* -- h is Frobenius-fixed modulo every factor. *)
[@@"opaque_to_smt"]
let all_comp_fixed (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p))
  : prop = forall (i:nat). i < L.length fs ==>
             cong #(polynomial (fp p)) (L.index fs i)
                  (poly_power #(fp p) h (p <: nat)) h

let all_comp_fixed_elim (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p){all_comp_fixed p fs h})
  : Lemma (forall (i:nat). i < L.length fs ==>
             cong #(polynomial (fp p)) (L.index fs i)
                  (poly_power #(fp p) h (p <: nat)) h)
  = reveal_opaque (`%all_comp_fixed) (all_comp_fixed p fs h)

let all_comp_fixed_proof (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p))
  = (i:nat{i < L.length fs})
  -> Lemma (cong #(polynomial (fp p)) (L.index fs i)
                 (poly_power #(fp p) h (p <: nat)) h)

let all_comp_fixed_intro (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p)) (proof: all_comp_fixed_proof p fs h)
  : Lemma (all_comp_fixed p fs h)
  = reveal_opaque (`%all_comp_fixed) (all_comp_fixed p fs h);
    let aux (i:nat) : Lemma (i < L.length fs ==>
                cong #(polynomial (fp p)) (L.index fs i)
                     (poly_power #(fp p) h (p <: nat)) h)
      = if i < L.length fs then proof i else ()
    in
    Classical.forall_intro aux

(* -- modulo every factor, h is congruent to some constant. *)
[@@"opaque_to_smt"]
let all_comp_const (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p))
  : prop = forall (i:nat). i < L.length fs ==>
             kernel_is_const_shifted p (L.index fs i) h

let all_comp_const_elim (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p){all_comp_const p fs h})
  : Lemma (forall (i:nat). i < L.length fs ==>
             kernel_is_const_shifted p (L.index fs i) h)
  = reveal_opaque (`%all_comp_const) (all_comp_const p fs h)

let all_comp_const_proof (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p))
  = (i:nat{i < L.length fs})
  -> Lemma (kernel_is_const_shifted p (L.index fs i) h)

let all_comp_const_intro (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p)) (proof: all_comp_const_proof p fs h)
  : Lemma (all_comp_const p fs h)
  = reveal_opaque (`%all_comp_const) (all_comp_const p fs h);
    let aux (i:nat) : Lemma (i < L.length fs ==>
                kernel_is_const_shifted p (L.index fs i) h)
      = if i < L.length fs then proof i else ()
    in
    Classical.forall_intro aux

(* all_irreducible ==> all_deg_ge1 (CRT's degree predicate): irreducibles
   have degree >= 1 by definition. *)
let irred_gives_deg_ge1 (p:int{EU.is_prime p})
  (fs: list (polynomial (fp p)){all_irreducible p fs})
  : Lemma (CRT.all_deg_ge1 fs)
  = let dpf (k:nat{k < L.length fs}) : Lemma (deg (L.index fs k) >= 1)
      = all_irreducible_elim p fs
    in
    CRT.all_deg_ge1_intro fs dpf

(* ================================================================ *)
(*  C1.  CONGRUENCE DECOMPOSITION.                                   *)
(*    f = poly_prod fs, pairwise coprime  ==>                        *)
(*    ( f | (h^p -- h) )  <==>  ( all f_i | (h^p -- h) ).            *)
(* ================================================================ *)

(* forward:  divides through each factor via  f_i | f | (h^p -- h). *)
let c1_fwd (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p))
  : Lemma (requires cong #(polynomial (fp p)) (poly_prod fs)
                         (poly_power #(fp p) h (p <: nat)) h)
          (ensures  all_comp_fixed p fs h)
  = let cpf (i:nat{i < L.length fs})
      : Lemma (cong #(polynomial (fp p)) (L.index fs i)
                    (poly_power #(fp p) h (p <: nat)) h)
      = CRT.prod_factor_divides fs i;               (* f_i | poly_prod fs *)
        divides_trans (L.index fs i) (poly_prod fs)
          ((poly_power #(fp p) h (p <: nat)) + (- h))
    in
    all_comp_fixed_intro p fs h cpf

(* backward:  pairwise-coprime factors dividing g  ==>  their product does. *)
let c1_bwd (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p))
  : Lemma (requires IR.pairwise_coprime fs /\ all_irreducible p fs /\
                    all_comp_fixed p fs h)
          (ensures  cong #(polynomial (fp p)) (poly_prod fs)
                         (poly_power #(fp p) h (p <: nat)) h)
  = let g : polynomial (fp p) = (poly_power #(fp p) h (p <: nat)) + (- h) in
    all_comp_fixed_elim p fs h;                     (* forall i. f_i | g *)
    irred_gives_deg_ge1 p fs;
    CRT.all_deg_ge1_elim fs;                        (* forall k. deg f_k >= 1 *)
    IR.pairwise_coprime_elim fs;                   (* pairwise coprime *)
    IR.pairwise_coprime_divides fs g;               (* flat_product fs | g *)
    CRT.flat_eq_prod fs                             (* poly_prod fs | g *)

let c1 (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p))
  : Lemma (requires IR.pairwise_coprime fs /\ all_irreducible p fs)
          (ensures  cong #(polynomial (fp p)) (poly_prod fs)
                         (poly_power #(fp p) h (p <: nat)) h
                    <==> all_comp_fixed p fs h)
  = introduce cong #(polynomial (fp p)) (poly_prod fs)
                   (poly_power #(fp p) h (p <: nat)) h
              ==> all_comp_fixed p fs h
    with _pf. c1_fwd p fs h;
    introduce all_comp_fixed p fs h
              ==> cong #(polynomial (fp p)) (poly_prod fs)
                       (poly_power #(fp p) h (p <: nat)) h
    with _pf. c1_bwd p fs h

(* ================================================================ *)
(*  C2.  PER-COMPONENT  <=>  CONSTANT.                              *)
(*    For irreducible f_i:                                          *)
(*      f_i | (h^p -- h)  <==>  exists c. f_i | (h -- [c]).         *)
(*    This is exactly Berlekamp.kernel_factor_iff (the LHS is       *)
(*    cong f_i (h^p) h, the RHS is kernel_is_const_shifted).        *)
(* ================================================================ *)

(* lift the componentwise iff to the whole factor list. *)
let c2 (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p))
  : Lemma (requires all_irreducible p fs)
          (ensures  all_comp_fixed p fs h <==> all_comp_const p fs h)
  = introduce all_comp_fixed p fs h ==> all_comp_const p fs h
    with _pf.
      begin
        all_comp_fixed_elim p fs h;
        let cpf (i:nat{i < L.length fs})
          : Lemma (kernel_is_const_shifted p (L.index fs i) h)
          = all_irreducible_elim p fs;
            all_comp_fixed_elim p fs h;
            kernel_factor_iff p (L.index fs i) h
        in
        all_comp_const_intro p fs h cpf
      end;
    introduce all_comp_const p fs h ==> all_comp_fixed p fs h
    with _pf.
      begin
        all_comp_const_elim p fs h;
        let fpf (i:nat{i < L.length fs})
          : Lemma (cong #(polynomial (fp p)) (L.index fs i)
                        (poly_power #(fp p) h (p <: nat)) h)
          = all_irreducible_elim p fs;
            all_comp_const_elim p fs h;
            kernel_factor_iff p (L.index fs i) h
        in
        all_comp_fixed_intro p fs h fpf
      end

(* ================================================================ *)
(*  C3.  STRUCTURE THEOREM.                                          *)
(*    h  is Frobenius-fixed mod  f = poly_prod fs  IFF  modulo each  *)
(*    factor f_i it is congruent to a constant of fp p.  (No degree  *)
(*    hypothesis on h — this is the pure structural equivalence.)    *)
(* ================================================================ *)

let c3 (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p))
  : Lemma (requires IR.pairwise_coprime fs /\ all_irreducible p fs)
          (ensures  cong #(polynomial (fp p)) (poly_prod fs)
                         (poly_power #(fp p) h (p <: nat)) h
                    <==> all_comp_const p fs h)
  = c1 p fs h;
    c2 p fs h

(* the Berlekamp set  B(f) = { h : deg h < deg f  /\  h^p ≡ h  (mod f) }. *)
let is_berlekamp (p:int{EU.is_prime p}) (f h: polynomial (fp p)) : prop =
  deg h < deg f /\
  cong #(polynomial (fp p)) f (poly_power #(fp p) h (p <: nat)) h

(* degree-qualified structure theorem: membership in B(f) is exactly a bounded
   degree together with "congruent to a constant modulo every factor". *)
let berlekamp_structure (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (h: polynomial (fp p))
  : Lemma (requires IR.pairwise_coprime fs /\ all_irreducible p fs)
          (ensures  is_berlekamp p (poly_prod fs) h
                    <==> (deg h < deg (poly_prod fs) /\ all_comp_const p fs h))
  = c3 p fs h

(* ================================================================ *)
(*  CRT bijection scaffolding:  B(f)  <->  (fp p)^r.                 *)
(*  A constant tuple  cs : list (fp p)  of length r determines a     *)
(*  residue vector  [ [cs_0]; ...; [cs_{r-1}] ]  of constant polys.  *)
(* ================================================================ *)

(* (x -- z) -- (y -- z) = x -- y, over any commutative ring. *)
let sub_pair_cancel (#a:Type) {| cr: commutative_ring a |} (x y z: a)
  : Lemma ((x -- z) -- (y -- z) = x -- y)
  = assert ((x -- z) -- (y -- z) = x -- y) by (canon_ring ())

(* index commutes with map. *)
let rec index_map (#a #b:Type) (g: a -> b) (l: list a) (k:nat)
  : Lemma (requires k < L.length l)
          (ensures  L.index (L.map g l) k == g (L.index l k))
          (decreases l)
  = match l with
    | x :: xs -> if k = 0 then () else index_map g xs (k - 1)

(* -- w realizes the constant tuple cs:  f_i | (w -- [cs_i])  for all i. *)
[@@"opaque_to_smt"]
let realizes_tuple (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (w: polynomial (fp p)) (cs: list (fp p))
  : prop = L.length cs == L.length fs /\
           (forall (i:nat). i < L.length fs ==>
              divides #(polynomial (fp p)) (L.index fs i)
                      (w -- (poly_const #(fp p) (L.index cs i))))

let realizes_tuple_elim (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (w: polynomial (fp p)) (cs: list (fp p){realizes_tuple p fs w cs})
  : Lemma (L.length cs == L.length fs /\
           (forall (i:nat). i < L.length fs ==>
              divides #(polynomial (fp p)) (L.index fs i)
                      (w -- (poly_const #(fp p) (L.index cs i)))))
  = reveal_opaque (`%realizes_tuple) (realizes_tuple p fs w cs)

let realizes_tuple_proof (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (w: polynomial (fp p)) (cs: list (fp p))
  = (i:nat{i < L.length fs /\ i < L.length cs})
  -> Lemma (divides #(polynomial (fp p)) (L.index fs i)
                    (w -- (poly_const #(fp p) (L.index cs i))))

let realizes_tuple_intro (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (w: polynomial (fp p)) (cs: list (fp p))
  (proof: realizes_tuple_proof p fs w cs)
  : Lemma (requires L.length cs == L.length fs)
          (ensures  realizes_tuple p fs w cs)
  = reveal_opaque (`%realizes_tuple) (realizes_tuple p fs w cs);
    let aux (i:nat) : Lemma (i < L.length fs ==>
                divides #(polynomial (fp p)) (L.index fs i)
                        (w -- (poly_const #(fp p) (L.index cs i))))
      = if i < L.length fs then proof i else ()
    in
    Classical.forall_intro aux

(* realizing a constant tuple  ==>  fixed modulo every factor. *)
let realizes_gives_comp_const (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (w: polynomial (fp p)) (cs: list (fp p){realizes_tuple p fs w cs})
  : Lemma (all_comp_const p fs w)
  = let cpf (i:nat{i < L.length fs})
      : Lemma (kernel_is_const_shifted p (L.index fs i) w)
      = realizes_tuple_elim p fs w cs;
        kernel_is_const_shifted_intro p (L.index fs i) w (L.index cs i)
    in
    all_comp_const_intro p fs w cpf

(* ---------------------------------------------------------------- *)
(*  INJECTIVITY:  two residues (both reduced mod f) that realize the *)
(*  SAME constant tuple are equal.  (Uniqueness half of the count.)  *)
(* ---------------------------------------------------------------- *)

let crt_const_inj (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (cs: list (fp p)) (a b: polynomial (fp p))
  : Lemma (requires IR.pairwise_coprime fs /\ all_irreducible p fs /\
                    realizes_tuple p fs a cs /\ realizes_tuple p fs b cs /\
                    deg a < deg (poly_prod fs) /\ deg b < deg (poly_prod fs))
          (ensures  a = b)
  = irred_gives_deg_ge1 p fs;
    realizes_tuple_elim p fs a cs;
    realizes_tuple_elim p fs b cs;
    let cong_pf (k:nat{k < L.length fs})
      : Lemma (divides #(polynomial (fp p)) (L.index fs k) (a -- b))
      = let ck : polynomial (fp p) = poly_const #(fp p) (L.index cs k) in
        realizes_tuple_elim p fs a cs;
        realizes_tuple_elim p fs b cs;
        divides_sub (L.index fs k) (a -- ck) (b -- ck);
        sub_pair_cancel a b ck;
        divides_congruence_right (L.index fs k) ((a -- ck) -- (b -- ck)) (a -- b)
    in
    CRT.crt_multi_inj fs a b cong_pf

(* ---------------------------------------------------------------- *)
(*  SURJECTIVITY:  every constant tuple is realized by a witness      *)
(*  which is Frobenius-fixed modulo  f = poly_prod fs.  (Existence    *)
(*  half of the count; the witness is the CRT recombination.)         *)
(* ---------------------------------------------------------------- *)

let crt_const_witness (p:int{EU.is_prime p}) (fs: list (polynomial (fp p)))
  (cs: list (fp p))
  : Pure (polynomial (fp p))
         (requires IR.pairwise_coprime fs /\ all_irreducible p fs /\
                   L.length cs == L.length fs)
         (ensures  fun w -> realizes_tuple p fs w cs /\
                    cong #(polynomial (fp p)) (poly_prod fs)
                         (poly_power #(fp p) w (p <: nat)) w)
  = let rs : list (polynomial (fp p)) = L.map (poly_const #(fp p)) cs in
    (* L.length rs == L.length cs  by map_lemma's SMTPat. *)
    let cop_pf (i:nat{i < L.length fs}) (j:nat{j < L.length fs /\ j <> i})
      : Lemma (coprime #(fp p) (L.index fs i) (L.index fs j))
      = IR.pairwise_coprime_elim fs
    in
    let deg_pf (k:nat{k < L.length fs}) : Lemma (deg (L.index fs k) >= 1)
      = all_irreducible_elim p fs
    in
    let w = CRT.crt_multi_witness fs rs cop_pf deg_pf in
    (* w realizes cs:  all_cong_vec fs w rs, and rs_i = [cs_i]. *)
    CRT.all_cong_vec_elim fs w rs;
    let rpf (i:nat{i < L.length fs /\ i < L.length cs})
      : Lemma (divides #(polynomial (fp p)) (L.index fs i)
                       (w -- (poly_const #(fp p) (L.index cs i))))
      = CRT.all_cong_vec_elim fs w rs;
        index_map (poly_const #(fp p)) cs i
    in
    realizes_tuple_intro p fs w cs rpf;
    (* fixed modulo every factor, hence modulo f by C3. *)
    realizes_gives_comp_const p fs w cs;
    c3 p fs w;
    w

(* ---------------------------------------------------------------- *)
(*  UNIQUENESS of the per-factor constant:  modulo an irreducible    *)
(*  (degree >= 1) factor, a residue determines its constant.  This   *)
(*  is what makes distinct constant tuples give distinct classes —   *)
(*  the second half of the  B(f) <-> (fp p)^r  bijection.            *)
(* ---------------------------------------------------------------- *)

(* (x -- u) -- (x -- v) = v -- u, over any commutative ring. *)
let sub_from_common (#a:Type) {| cr: commutative_ring a |} (x u v: a)
  : Lemma ((x -- u) -- (x -- v) = v -- u)
  = assert ((x -- u) -- (x -- v) = v -- u) by (canon_ring ())

let comp_tuple_unique (p:int{EU.is_prime p}) (q h: polynomial (fp p)) (c c': fp p)
  : Lemma (requires deg #(fp p) q >= 1 /\
                    divides #(polynomial (fp p)) q (h -- (poly_const #(fp p) c)) /\
                    divides #(polynomial (fp p)) q (h -- (poly_const #(fp p) c')))
          (ensures  c = c')
  = if c = c' then ()
    else begin
      let cc  : polynomial (fp p) = poly_const #(fp p) c in
      let cc' : polynomial (fp p) = poly_const #(fp p) c' in
      divides_sub q (h -- cc) (h -- cc');              (* q | (h--cc)--(h--cc') *)
      sub_from_common h cc cc';                        (* (h--cc)--(h--cc') = cc'--cc *)
      divides_congruence_right q ((h -- cc) -- (h -- cc')) (cc' -- cc);
      nonunit_not_div_const_diff p q c' c              (* ~(q | cc'--cc), contradiction *)
    end
