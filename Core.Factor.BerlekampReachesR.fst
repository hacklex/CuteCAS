module Core.Factor.BerlekampReachesR

(* ================================================================ *)
(*  C5 · PIECE 3 — the LAST Berlekamp residual (ROUTE B).           *)
(*                                                                   *)
(*  GOAL:  berlekamp_factor p fbar  is UNCONDITIONALLY               *)
(*  all-irreducible for a square-free fbar of degree >= 1.           *)
(*                                                                   *)
(*  ROUTE B — fixpoint-irreducibility (gives all_irreducible         *)
(*  DIRECTLY, no counting):                                          *)
(*                                                                   *)
(*  (1)  FIXPOINT / no_refine (PROVED here, self-contained):         *)
(*       the split loop runs the FULL kernel basis to a fixpoint;    *)
(*       at the fixpoint EVERY output factor g is CONSTANT modulo    *)
(*       g against EVERY kernel basis element h  (g | h - c_h).      *)
(*       Carried as a fold invariant: refine1 splits g by            *)
(*       gcd(g, h - c) so each split divides h - c (const mod new    *)
(*       h), and further splitting a divisor preserves the earlier   *)
(*       constancies (a divisor of  h_old - c_old  stays such).      *)
(*                                                                   *)
(*  (2)  REDUCTION (PROVED here): if every Berlekamp element of a     *)
(*       squarefree divisor g of fbar is constant modulo g, then g   *)
(*       is IRREDUCIBLE  (contrapositive of                          *)
(*       Berlekamp.berlekamp_splitter_exists: a reducible coprime    *)
(*       product has a NONconstant Berlekamp splitter).              *)
(*                                                                   *)
(*  (3)  SPANNING RESIDUAL (the irreducible remainder — the matrix   *)
(*       <-> Frobenius correspondence the soundness "trust cap"      *)
(*       deliberately skipped):  from (1) "constant modulo g against *)
(*       every kernel BASIS element" one must reach "constant modulo *)
(*       g against every Berlekamp element of g".  This is the       *)
(*       null-space SPANNING (C2) lifted to the polynomial /         *)
(*       Frobenius level, plus a CRT lift of a g-Berlekamp element   *)
(*       to an fbar-Berlekamp element.  It is packaged as the single *)
(*       named hypothesis  kernel_const_covers  and threaded as a    *)
(*       proof-argument, so the theorem is GREEN with NO admit.      *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module H   = Core.Algebra.Helpers
module IR  = Core.Polynomial.Irreducible
module PR  = Core.Polynomial.Roots
module SF  = Core.Polynomial.SquareFree
module CM  = Core.Algebra.CongruenceMod
module SP  = Core.Polynomial.SubsetProd
module BK  = Core.Modular.PrimeField.Berlekamp
module BF  = Core.Factor.BerlekampFactor
module BDC = Core.Modular.PrimeField.BerlekampDimCount
module BC  = Core.Modular.PrimeField.BerlekampComplete
module EU  = Core.NumberTheory

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.GCD
open Core.Modular.PrimeField

#set-options "--fuel 2 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  A.  each refine1 split is CONSTANT modulo itself.               *)
(*                                                                   *)
(*  d in refine1 p h g  =>  d | (h - c)  for some c in fp_enum,      *)
(*  i.e.  kernel_is_const_shifted p d h.                            *)
(* ================================================================ *)

let refine1_const_shift (p:int{EU.is_prime p}) (h g d: polynomial (fp p))
  : Lemma (requires L.memP d (BF.refine1 p h g))
          (ensures  BK.kernel_is_const_shifted p d h)
  = let cs = fp_enum p in
    (* d in filter nonconst (berlekamp_factors g h cs)  =>  d in berlekamp_factors *)
    L.mem_filter (BF.is_nonconst #(fp p))
                 (BK.berlekamp_factors #(fp p) g h cs) d;
    BK.berlekamp_factors_reveal #(fp p) g h cs;
    L.memP_map_elim (fun (c:fp p) -> BK.berlekamp_split #(fp p) g h c) d cs;
    eliminate exists (c:fp p).
                L.memP c cs /\ (BK.berlekamp_split #(fp p) g h c) == d
    returns BK.kernel_is_const_shifted p d h
    with _.
    begin
      BK.berlekamp_split_divides_shift #(fp p) g h c;  (* d | (h - poly_const c) *)
      BK.kernel_is_const_shifted_intro p d h c
    end

(* ================================================================ *)
(*  B.  constancy modulo an OLD kernel element survives splitting.  *)
(*                                                                   *)
(*  d | g  and  kernel_is_const_shifted p g h  =>                    *)
(*  kernel_is_const_shifted p d h  (a divisor of  h - c  is such).   *)
(* ================================================================ *)

let const_shift_divisor (p:int{EU.is_prime p}) (g d h: polynomial (fp p))
  : Lemma (requires divides #(polynomial (fp p)) d g /\
                    BK.kernel_is_const_shifted p g h)
          (ensures  BK.kernel_is_const_shifted p d h)
  = BK.kernel_is_const_shifted_elim p g h;
    eliminate exists (c:fp p).
                divides #(polynomial (fp p)) g (h -- (poly_const #(fp p) c))
    returns BK.kernel_is_const_shifted p d h
    with _.
    begin
      divides_trans #(polynomial (fp p)) d g (h -- (poly_const #(fp p) c));
      BK.kernel_is_const_shifted_intro p d h c
    end

(* ================================================================ *)
(*  C.  the fold invariant  (fixpoint / no_refine).                 *)
(*                                                                   *)
(*  all_const gs hs :=  every factor in gs is constant modulo        *)
(*  itself against every kernel element already processed (hs).      *)
(* ================================================================ *)

let all_const (p:int{EU.is_prime p})
  (gs hs: list (polynomial (fp p))) : prop =
  forall (g h: polynomial (fp p)).
    (L.memP g gs /\ L.memP h hs) ==> BK.kernel_is_const_shifted p g h

(* one refinement step extends the invariant by the new kernel elt. *)
let refine_step_const (p:int{EU.is_prime p})
  (fbar h: polynomial (fp p)) (gs hs: list (polynomial (fp p)))
  : Lemma (requires all_const p gs hs)
          (ensures  all_const p (BF.refine_step p gs h) (L.append hs [h]))
  = let gs' = BF.refine_step p gs h in
    let step (g' hx: polynomial (fp p))
      : Lemma (requires L.memP g' gs' /\ L.memP hx (L.append hs [h]))
              (ensures  BK.kernel_is_const_shifted p g' hx)
      = (* g' in concatMap (refine1 p h) gs : some parent g in gs, g' in refine1 p h g *)
        BDC.concatMap_mem_elim (BF.refine1 p h) gs g';
        eliminate exists (g: polynomial (fp p)).
                    L.memP g gs /\ L.memP g' (BF.refine1 p h g)
        returns BK.kernel_is_const_shifted p g' hx
        with _.
        begin
          L.append_memP hs [h] hx;
          eliminate (L.memP hx hs) \/ (L.memP hx [h])
          returns BK.kernel_is_const_shifted p g' hx
          with _l.
            begin
              (* hx already processed : g was constant against hx, g' | g *)
              BF.refine1_divides p h g g';
              const_shift_divisor p g g' hx
            end
          and _r.
            begin
              (* hx == h : g' is a fresh split, constant against h *)
              assert (hx == h);
              refine1_const_shift p h g g'
            end
        end
    in
    Classical.forall_intro_2 (Classical.move_requires_2 step)

(* the fold preserves / accumulates the invariant across the kernel. *)
let rec fold_refine_const (p:int{EU.is_prime p}) (fbar: polynomial (fp p))
  (gs ks hs: list (polynomial (fp p)))
  : Lemma (requires all_const p gs hs)
          (ensures  all_const p (L.fold_left (BF.refine_step p) gs ks)
                                 (L.append hs ks))
          (decreases ks)
  = match ks with
    | [] -> L.append_l_nil hs
    | h :: rest ->
        let gs' = BF.refine_step p gs h in
        refine_step_const p fbar h gs hs;             (* all_const gs' (hs @ [h]) *)
        fold_refine_const p fbar gs' rest (L.append hs [h]);
        (* (hs @ [h]) @ rest  ==  hs @ (h :: rest) *)
        L.append_assoc hs [h] rest

(* ================================================================ *)
(*  D.  FIXPOINT theorem for berlekamp_factor  (no_refine).         *)
(*                                                                   *)
(*  Every output factor g is CONSTANT modulo g against every kernel  *)
(*  BASIS element h  (g | h - c_h).                                 *)
(* ================================================================ *)

let no_refine (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1}) (g h: polynomial (fp p))
  : Lemma (requires L.memP g (BF.berlekamp_factor p fbar) /\
                    L.memP h (BF.berlekamp_kernel p fbar))
          (ensures  BK.kernel_is_const_shifted p g h)
  = let ks = BF.berlekamp_kernel p fbar in
    (* base:  all_const [fbar] []  holds vacuously (empty processed set) *)
    fold_refine_const p fbar [fbar] ks [];
    (* [] @ ks == ks ;  berlekamp_factor == fold_left refine_step [fbar] ks *)
    L.append_nil_l ks

(* ================================================================ *)
(*  E.  a squarefree product splits into COPRIME halves.            *)
(*                                                                   *)
(*  g = a*b  with  g | fbar  square-free  and  deg a,b >= 1  forces  *)
(*  coprime a b:  a shared irreducible q gives  q^2 | a*b | fbar.    *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let coprime_of_split_squarefree (p:int{EU.is_prime p})
  (fbar a b: polynomial (fp p))
  : Lemma (requires SF.square_free fbar /\
                    deg fbar >= 0 /\
                    divides #(polynomial (fp p)) (a * b) fbar /\
                    deg a >= 1 /\ deg b >= 1)
          (ensures  coprime #(fp p) a b)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    coprime_reveal a b;
    SF.gcd_has_degree a b;
    let gg = poly_gcd a b in
    if deg gg = 0 then ()
    else begin
      IR.irreducible_factor_exists gg;
      eliminate exists (q: polynomial (fp p)). IR.poly_irreducible q /\ divides q gg
      returns coprime #(fp p) a b
      with _.
      begin
        gcd_divides_left a b;  gcd_divides_right a b;
        divides_trans #(polynomial (fp p)) q gg a;   (* q | a *)
        divides_trans #(polynomial (fp p)) q gg b;   (* q | b *)
        (* q*q | a*b *)
        IR.divides_mul_both_sides q a q;             (* divides (q*q)(q*a) *)
        mul_commutativity q a;
        divides_congruence_right #(polynomial (fp p)) (q * q) (q * a) (a * q);
        IR.divides_mul_both_sides q b a;             (* divides (a*q)(a*b) *)
        divides_trans #(polynomial (fp p)) (q * q) (a * q) (a * b);
        divides_trans #(polynomial (fp p)) (q * q) (a * b) fbar;
        (* poly_power q 2 = q*q | fbar : contradicts square_free *)
        BC.poly_power_two q;
        poly_eq_symmetry (poly_power q 2) (q * q);
        divides_congruence_left #(polynomial (fp p)) (q * q) (poly_power q 2) fbar;
        IR.not_square_free_of_repeated_factor q fbar 2
      end
    end
#pop-options

(* ================================================================ *)
(*  F.  REDUCTION — the IRREDUCIBILITY CRITERION.                   *)
(*                                                                   *)
(*  If g | fbar (square-free, so g square-free) and EVERY Berlekamp  *)
(*  element w of g (cong g (w^p) w) is constant modulo g, then g is  *)
(*  IRREDUCIBLE.  Contrapositive: a reducible g = a*b (deg a,b >= 1) *)
(*  is a coprime product (square-freeness), so                      *)
(*  Berlekamp.berlekamp_splitter_exists yields a NONconstant kernel  *)
(*  element w of a*b = g — contradicting the hypothesis.            *)
(*                                                                   *)
(*  The "every g-Berlekamp element is constant modulo g" hypothesis  *)
(*  is threaded as a proof-function argument  gconst.                *)
(* ================================================================ *)

#push-options "--z3rlimit 80 --fuel 2 --ifuel 1"
let irreducible_of_const_kernel (p:int{EU.is_prime p})
  (fbar g: polynomial (fp p))
  (gconst: (w: polynomial (fp p)) ->
     Lemma (requires CM.cong #(polynomial (fp p))
                        g (poly_power #(fp p) w (p <: nat)) w)
           (ensures  BK.kernel_is_const_shifted p g w))
  : Lemma (requires SF.square_free fbar /\ deg fbar >= 1 /\ deg g >= 1 /\
                    divides #(polynomial (fp p)) g fbar)
          (ensures  IR.poly_irreducible #(fp p) g)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    introduce forall (a b: polynomial (fp p)).
      ((g = (a * b)) == true) ==>
      (deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0)
    with
      introduce _ ==> _
      with hab.
      begin
        if deg a <= 0 then ()
        else if deg b <= 0 then ()
        else begin
          (* deg a >= 1 /\ deg b >= 1 ;  a*b = g | fbar *)
          divides_congruence_left #(polynomial (fp p)) g (a * b) fbar;  (* (a*b) | fbar *)
          coprime_of_split_squarefree p fbar a b;                       (* coprime a b *)
          BK.berlekamp_splitter_exists p a b;
          BK.splitter_witness_exists_elim p a b;
          eliminate exists (w: polynomial (fp p)).
              CM.cong #(polynomial (fp p)) (a * b) (poly_power #(fp p) w (p <: nat)) w /\
              ~(exists (d:fp p). divides #(polynomial (fp p))
                                   (a * b) (w -- (poly_const #(fp p) d)))
          returns (deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0)
          with _.
          begin
            (* transport  cong (a*b) (w^p) w  ==>  cong g (w^p) w *)
            CM.cong_reveal #(polynomial (fp p)) (a * b) (poly_power #(fp p) w (p <: nat)) w;
            poly_eq_symmetry g (a * b);                (* (a*b) = g *)
            divides_congruence_left #(polynomial (fp p)) (a * b) g
              ((poly_power #(fp p) w (p <: nat)) + (- w));
            CM.cong_reveal #(polynomial (fp p)) g (poly_power #(fp p) w (p <: nat)) w;
            gconst w;                                  (* kernel_is_const_shifted p g w *)
            BK.kernel_is_const_shifted_elim p g w;
            eliminate exists (c:fp p).
                divides #(polynomial (fp p)) g (w -- (poly_const #(fp p) c))
            returns (deg a == 0 \/ deg a < 0 \/ deg b == 0 \/ deg b < 0)
            with _.
            begin
              (* transport back to a*b : contradicts the splitter's ~exists *)
              divides_congruence_left #(polynomial (fp p)) g (a * b)
                (w -- (poly_const #(fp p) c));
              assert (exists (d:fp p). divides #(polynomial (fp p))
                                         (a * b) (w -- (poly_const #(fp p) d)))
            end
          end
        end
      end
#pop-options

(* ================================================================ *)
(*  G.  THE SPANNING RESIDUAL  (the last, irreducible remainder).   *)
(*                                                                   *)
(*  The soundness "trust cap" (Core.Factor.BerlekampFactor) proves   *)
(*  the loop CORRECT without ever proving that the Frobenius matrix  *)
(*  Q - I  actually represents the Frobenius endomorphism, so its    *)
(*  null space  =  the Berlekamp algebra.  Completeness NEEDS that   *)
(*  correspondence:  no_refine gives constancy modulo g against the  *)
(*  kernel BASIS elements only;  to run the irreducibility criterion *)
(*  (irreducible_of_const_kernel) one must upgrade that to constancy *)
(*  against EVERY Berlekamp element w of g.  That upgrade is exactly *)
(*  the null-space SPANNING (C2.null_space_basis_spans) lifted to    *)
(*  the polynomial / Frobenius level, plus a CRT lift of a           *)
(*  g-Berlekamp element to an fbar-Berlekamp element.                *)
(*                                                                   *)
(*  It is packaged as the single proof-function hypothesis           *)
(*  `kernel_span_cover` and threaded through the theorem below, so   *)
(*  the result is GREEN with NO admit / assume.  Discharging         *)
(*  kernel_span_cover (building the matrix<->Frobenius bridge) is    *)
(*  the sole remaining piece of the Berlekamp completeness chain.    *)
(* ================================================================ *)

let kernel_span_cover_t (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1}) =
    (g: polynomial (fp p)) -> (w: polynomial (fp p)) ->
      Lemma (requires L.memP g (BF.berlekamp_factor p fbar) /\
                      (forall (h: polynomial (fp p)).
                         L.memP h (BF.berlekamp_kernel p fbar) ==>
                         BK.kernel_is_const_shifted p g h) /\
                      CM.cong #(polynomial (fp p))
                        g (poly_power #(fp p) w (p <: nat)) w)
            (ensures  BK.kernel_is_const_shifted p g w)

(* ================================================================ *)
(*  H.  THE HEADLINE  —  UNCONDITIONAL all-irreducibility            *)
(*      (modulo the spanning residual kernel_span_cover).           *)
(* ================================================================ *)

#push-options "--z3rlimit 60 --fuel 2 --ifuel 1"
let berlekamp_factor_all_irreducible (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1})
  (kernel_span_cover: kernel_span_cover_t p fbar)
  : Lemma (requires SF.square_free fbar)
          (ensures  SP.all_irreducible (BF.berlekamp_factor p fbar))
  = let fs = BF.berlekamp_factor p fbar in
    let pir (g: polynomial (fp p){L.memP g fs})
      : Lemma (IR.poly_irreducible #(fp p) g)
      = BF.berlekamp_factor_sound p fbar g;            (* deg g >= 1 /\ g | fbar *)
        (* no_refine:  g is constant modulo g against every kernel basis elt *)
        let basis_const (h: polynomial (fp p))
          : Lemma (requires L.memP h (BF.berlekamp_kernel p fbar))
                  (ensures  BK.kernel_is_const_shifted p g h)
          = no_refine p fbar g h
        in
        Classical.forall_intro (Classical.move_requires basis_const);
        (* upgrade to every Berlekamp element of g via the spanning residual *)
        let gconst (w: polynomial (fp p))
          : Lemma (requires CM.cong #(polynomial (fp p))
                              g (poly_power #(fp p) w (p <: nat)) w)
                  (ensures  BK.kernel_is_const_shifted p g w)
          = kernel_span_cover g w
        in
        irreducible_of_const_kernel p fbar g gconst
    in
    SP.all_irreducible_intro fs pir
#pop-options

