module Core.AlgebraicConstant.EmbedHom

(*
   §E splitting-field bridge: ext_embed_poly is a RING HOMOMORPHISM.

   ext_embed_poly : polynomial t -> polynomial (algebraic r)   (coeff-wise via ac_const)

   Deliverables:
     - ext_embed_poly_add a b : ext_embed (a + b) ~ ext_embed a + ext_embed b
     - ext_embed_poly_mul a b : ext_embed (a * b) ~ ext_embed a * ext_embed b
   (the +,* on the RHS being poly_add / poly_mul at the extension ring acr r).
*)

module L  = FStar.List.Tot
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Algebra.CongruenceMod
open Core.Polynomial
open Core.Polynomial.Coeff
open Core.Polynomial.Eval
open Core.Polynomial.Irreducible
open Core.FinSum
open Core.AlgebraicConstant
open Core.AlgebraicConstant.Root
open Core.AlgebraicConstant.Eval

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ================================================================ *)
(*  0.  ac_const is a ring homomorphism (proved via ac_rep + the     *)
(*      poly_const ring-hom facts in Core.Polynomial).               *)
(* ================================================================ *)

(* ac_const respects the base equatable equality. *)
let ac_const_congr (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                   (x y: t)
  : Lemma (requires x = y)
          (ensures ac_embed r x = ac_embed r y)
  = poly_const_congr x y;                   (* poly_const x ~ poly_const y *)
    poly_eq_implies_ac_eq (ac_embed r x) (ac_embed r y)

(* ac_const (x + y)  ~  ac_add (ac_const x) (ac_const y). *)
let ac_const_add (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                 (x y: t)
  : Lemma (ac_embed r (x + y) = ac_const x + ac_const y)
  = let a : algebraic r = ac_const (x + y) in
    let b : algebraic r = (ac_const x) + (ac_const y) in
    (* a.ac_rep == poly_const (x + y) *)
    (* b.ac_rep == (ac_const x).ac_rep + (ac_const y).ac_rep == poly_const x + poly_const y *)
    ac_add_rep (ac_embed r x) (ac_embed r y);
    poly_const_add x y;                     (* poly_const (x+y) ~ poly_const x + poly_const y *)
    (* a.ac_rep = poly_const (x+y) ; b.ac_rep == poly_const x + poly_const y *)
    poly_eq_implies_ac_eq a b

(* neg (x -- y) ~ y -- x  in any commutative ring. *)
private let cr_neg_sub_swap_E
    (#u:Type) {| cr: commutative_ring u |} (x y: u)
  : Lemma (eq (- (x + (- y))) (y + (- x)))
  = assert (eq (- (x + (- y))) (y + (- x)))
      by Core.Tactics.CanonRing.canon_ring ()

(* ac_const (x * y)  ~  ac_mul (ac_const x) (ac_const y).
   ac_mul reduces, so reason mod r:
     poly_const(x*y) = poly_const x * poly_const y ~ class_of(poly_const x * poly_const y). *)
let ac_const_mul (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                 (x y: t)
  : Lemma (ac_eq (ac_const (x * y))
                          ((ac_const #_ #_ #r x) * (ac_const #_ #_ #r y)))
  = let a : algebraic r = ac_const (x * y) in
    let b : algebraic r = (ac_const x) * (ac_const y) in
    (* b <: polynomial t == class_of (poly_const x * poly_const y) *)
    ac_mul_rep (ac_const #_ #_ #r x) (ac_const #_ #_ #r y);
    let q : polynomial t = (ac_const #_ #_ #r x)
                                    * (ac_const #_ #_ #r y) in
    (* (a <: polynomial t) == poly_const (x*y).  poly_const(x*y) ~ q. *)
    poly_const_mul x y;                     (* poly_eq (poly_const (x*y)) q *)
    cong_of_eq r a q;     (* cong r a q  (= r `divides` (a -- q)) *)
    (* q ~ class_of q == b *)
    class_of_mod #_ #_ #r q;                       (* r | (class_of q -- q) *)
    (* flip to r | (q -- class_of q) *)
    divides_neg r ((class_of r q) -- q);
    cr_neg_sub_swap_E (class_of r q) q;
    divides_congruence_right r
      (- ((class_of r q) -- q))
      (q -- (class_of r q));
    (* chain: r | (a -- q), r | (q -- b)  ==>  r | (a -- b) *)
    cong_trans r a q b;
    ac_eq_divides a b

(* ac_const (zero<:t)  ~  ac_zero  (= zero of the extension ring). *)
let ac_const_zero (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r}) ()
  : Lemma (ac_eq (ac_const #_ #_ #r (zero <: t)) (ac_zero #_ #_ #r))
  = (* (ac_const zero <: polynomial t) == poly_const zero ~ poly_zero ; r | poly_zero ;
       hence r | poly_const zero ; hence ac_eq (ac_const zero) ac_zero. *)
    assert ((ac_const #_ #_ #r (zero <: t) <: polynomial t) == poly_const (zero <: t))
      by (FStar.Tactics.norm [delta_only [`%ac_const]; iota; zeta]; FStar.Tactics.trefl ());
    H.elim_equatable_laws (polynomial t) ();
    poly_const_zero #t ();                          (* poly_eq (poly_const zero) poly_zero *)
    divides_zero r;                                 (* r | poly_zero *)
    divides_congruence_right r (poly_zero #t) (poly_const (zero <: t));
    ac_eq_zero_iff_divides (ac_const #_ #_ #r (zero <: t))

(* ================================================================ *)
(*  1.  Additivity:  ext_embed (a + b) ~ ext_embed a + ext_embed b.  *)
(* ================================================================ *)

let ext_embed_poly_add (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                       (a b: polynomial t)
  : Lemma (
             (ext_embed_poly #_ #_ #r (a + b))
             =
             ((ext_embed_poly #_ #_ #r a) + (ext_embed_poly #_ #_ #r b)))
  = ac_elim_equatable_laws r;
    H.trans_for_calc (algebraic r) ();
    let lhs : polynomial (algebraic r) = ext_embed_poly (a + b) in
    let ea  : polynomial (algebraic r) = ext_embed_poly a in
    let eb  : polynomial (algebraic r) = ext_embed_poly b in
    let rhs : polynomial (algebraic r) = ea + eb in
    let aux (k:nat) : Lemma (coeff lhs k = coeff rhs k) =
      (* LHS: coeff lhs k ~ ac_const (coeff (a+b) k) *)
      embed_coeff #_ #_ #r (a + b) k;
      (* coeff (a+b) k == coeff a k + coeff b k *)
      poly_add_coeff a b k;
      (* ac_const (coeff a k + coeff b k) ~ ac_add (ac_const (coeff a k)) (ac_const (coeff b k)) *)
      ac_const_add #_ #_ #r (coeff a k) (coeff b k);
      (* RHS: coeff rhs k == coeff ea k + coeff eb k (poly_add_coeff over acr) *)
      poly_add_coeff ea eb k;
      (* coeff ea k ~ ac_const (coeff a k) ; coeff eb k ~ ac_const (coeff b k) *)
      embed_coeff #_ #_ #r a k;
      embed_coeff #_ #_ #r b k;
      add_congruence
        (coeff ea k) (coeff eb k)
        (ac_const #_ #_ #r (coeff a k)) (ac_const #_ #_ #r (coeff b k));
      (* assemble:
           coeff lhs k ~ ac_const (coeff a k + coeff b k)
                       ~ ac_const (coeff a k) + ac_const (coeff b k)
                       ~ coeff ea k + coeff eb k
                       == coeff rhs k *)
      let la : algebraic r = ac_const (coeff a k) in
      let lb : algebraic r = ac_const (coeff b k) in
      let cea : algebraic r = coeff ea k in
      let ceb : algebraic r = coeff eb k in
      (* coeff(a+b)k = coeff a k + coeff b k (base =) ==> ac_const congruence *)
      ac_const_congr #_ #_ #r (coeff (a + b) k) (coeff a k + coeff b k);
      (* chain on the extension ring:
           coeff lhs k ~ ac_const(coeff(a+b)k)
                       ~ ac_const(coeff a k + coeff b k)
                       ~ la + lb
                       ~ cea + ceb
                       == coeff rhs k *)
      transitivity
        (coeff lhs k)
        (ac_const (coeff (a + b) k))
        (ac_const (coeff a k + coeff b k));
      transitivity
        (coeff lhs k)
        (ac_const (coeff a k + coeff b k))
        (la + lb);
      transitivity
        (coeff lhs k)
        (la + lb)
        (cea + ceb)
    in
    poly_eq_by_coeff lhs rhs aux

(* ================================================================ *)
(*  2.  Multiplicativity.                                            *)
(* ================================================================ *)

(* Named summand: ac_const composed with a base-ring-valued sequence.
   Used to push ac_const through sum_range without an inline lambda. *)
let ac_const_comp (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                  (g: nat -> t) (i: nat) : algebraic r
  = ac_const (g i)

(* ac_const pushes through sum_range additively:
     ac_const (sum_range g lo hi)  ~  sum_range (ac_const_comp g) lo hi. *)
let rec ac_const_sum_push (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                          (g: nat -> t) (lo hi: nat)
  : Lemma (ensures ac_eq
             (ac_const (sum_range g lo hi))
             (sum_range (ac_const_comp #_ #_ #r g) lo hi))
          (decreases (hi - lo))
  = ac_elim_equatable_laws r;
    let gc : (nat -> algebraic r) = ac_const_comp g in
    if lo >= hi then begin
      (* both sums are zero; ac_const (zero<:t) ~ ac_zero == zero(acr). *)
      sum_range_empty g lo hi;             (* sum g lo hi == zero<:t *)
      sum_range_empty gc lo hi;               (* sum gc lo hi == zero(acr) *)
      ac_const_zero #_ #_ #r ();              (* ac_const zero ~ ac_zero *)
      (* ac_zero == zero(acr) by reveal; rewrite the goal's RHS to ac_zero. *)
      ()
    end else begin
      (* unfold both sums on the left. *)
      sum_range_unfold_left g lo hi;
        (* sum g lo hi == g lo + sum g (lo+1) hi   [base ring] *)
      sum_range_unfold_left gc lo hi;
        (* sum gc lo hi == gc lo + sum gc (lo+1) hi   [acr] *)
      (* IH *)
      ac_const_sum_push #_ #_ #r g (lo ++ 1) hi;
        (* ac_const (sum g (lo+1) hi) ~ sum gc (lo+1) hi *)
      (* ac_const (g lo + sum g (lo+1) hi) ~ ac_const (g lo) + ac_const (sum g (lo+1) hi) *)
      ac_const_add #_ #_ #r (g lo) (sum_range g (lo ++ 1) hi);
      (* combine: ac_const (g lo) + ac_const (sum ..) ~ gc lo + sum gc (lo+1) hi
         note gc lo == ac_const (g lo) by reduction. *)
      add_congruence
        (ac_const (g lo)) (ac_const (sum_range g (lo ++ 1) hi))
        (gc lo) (sum_range gc (lo ++ 1) hi);
      (* assemble the chain over acr:
           ac_const (sum g lo hi)
             == ac_const (g lo + sum g (lo+1) hi)
             ~  ac_const (g lo) + ac_const (sum g (lo+1) hi)
             ~  gc lo + sum gc (lo+1) hi
             == sum gc lo hi                                                 *)
      transitivity
        (ac_const (sum_range g lo hi))
        (ac_const (g lo) + ac_const (sum_range g (lo ++ 1) hi))
        (gc lo + sum_range gc (lo ++ 1) hi)
    end

(* the embedded polynomial is no longer than the base polynomial
   (trim_length_le is Core.Polynomial's). *)
let embed_len_le (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                         (a: polynomial t)
  : Lemma (L.length (ext_embed_poly #_ #_ #r a) <= L.length a)
  = L.map_lemma (ac_const #_ #_ #r) a;          (* length (map g a) == length a *)
    trim_length_le (L.map (ac_const #_ #_ #r) a)

(* out of range, the embedded coeff is exactly the extension zero. *)
private let embed_coeff_high (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                            (a: polynomial t) (i: nat)
  : Lemma (requires i >= L.length (ext_embed_poly #_ #_ #r a))
          (ensures  coeff (ext_embed_poly #_ #_ #r a) i
                    == (zero <: algebraic r))
  = ()

(* per-term bridge:
     ac_const (coeff a i * coeff b (k-i))  ~  coeff(embed a) i * coeff(embed b)(k-i). *)
let mul_term_bridge (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                    (a b: polynomial t) (k i: nat)
  : Lemma (ac_eq
             (ac_const #_ #_ #r (coeff a i * coeff b (k - i)))
             (mul
                (coeff (ext_embed_poly #_ #_ #r a) i)
                (coeff (ext_embed_poly #_ #_ #r b) (k - i))))
  = ac_elim_equatable_laws r;
    let j : int = k - i in
    let ca : t = coeff a i in
    let cb : t = coeff b j in
    let cea : algebraic r = coeff (ext_embed_poly a) i in
    let ceb : algebraic r = coeff (ext_embed_poly b) j in
    (* ac_const (ca * cb) ~ ac_const ca * ac_const cb *)
    ac_const_mul #_ #_ #r ca cb;
    (* coeff (embed a) i ~ ac_const ca *)
    embed_coeff #_ #_ #r a i;
    (* coeff (embed b) j ~ ac_const cb : nat index uses embed_coeff;
       negative index: both coeff(embed b) j and cb are ring zeros, ac_const zero ~ ac_zero. *)
    if j >= 0 then
      embed_coeff #_ #_ #r b j
    else begin
      (* cb == zero<:t ; ceb == zero(acr) ; ac_const zero ~ ac_zero == zero(acr) *)
      ac_const_zero #_ #_ #r ()                      (* ac_const (zero<:t) ~ ac_zero ;
                                                        symmetry via ac_elim_equatable_laws *)
    end;
    (* ac_const ca * ac_const cb ~ cea * ceb (symmetry via ac_elim_equatable_laws) *)
    mul_congruence
      (ac_const #_ #_ #r ca) (ac_const #_ #_ #r cb) cea ceb;
    transitivity
      (ac_const #_ #_ #r (ca * cb))
      (((ac_const #_ #_ #r ca) * (ac_const #_ #_ #r cb)))
      ((cea * ceb))

(* Named base convolution term:  conv_base a b k i = coeff a i * coeff b (k - i). *)
let conv_base (#t:Type) {| f: field t |} (a b: polynomial t) (k i: nat) : t
  = coeff a i * coeff b (k - i)

(* For an index past len(embed a), the embedded convolution term is the extension zero. *)
let conv_tail_zero (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                   (a b: polynomial t) (k i: nat)
  : Lemma (requires i >= L.length (ext_embed_poly #_ #_ #r a))
          (ensures ac_eq
                     (ac_const_comp #_ #_ #r (conv_base a b k) i)
                     (zero <: algebraic r))
  = ac_elim_equatable_laws r;
    let j : int = k - i in
    let cea : algebraic r = coeff (ext_embed_poly a) i in
    let ceb : algebraic r = coeff (ext_embed_poly b) j in
    (* ac_const_comp (conv_base a b k) i == ac_const (coeff a i * coeff b (k-i)) *)
    (* per-term bridge: that ~ cea * ceb *)
    mul_term_bridge #_ #_ #r a b k i;
    (* cea == zero(acr) since i is out of range of (embed a). *)
    embed_coeff_high #_ #_ #r a i;                  (* cea == zero(acr) *)
    (* zero(acr) * ceb ~ zero(acr) *)
    H.zero_mul_x ceb;   (* zero * ceb ~ zero *)
    (* cea * ceb == zero(acr) * ceb ~ zero(acr) ; chain with per-term bridge. *)
    transitivity
      (ac_const #_ #_ #r (conv_base a b k i))
      ((cea * ceb))
      (zero <: algebraic r)

(* Range bridge: the embedded convolution sum over the (possibly shorter) embedded
   range equals the sum over the full base range — the extra terms vanish. *)
let conv_range_bridge (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                      (a b: polynomial t) (k: nat)
  : Lemma (ac_eq
             (sum_range
                (ac_const_comp #_ #_ #r (conv_base a b k)) 0 (L.length a))
             (sum_range
                (ac_const_comp #_ #_ #r (conv_base a b k)) 0
                (L.length (ext_embed_poly #_ #_ #r a))))
  = ac_elim_equatable_laws r;
    let gc : (nat -> algebraic r) = ac_const_comp (conv_base a b k) in
    let le : nat = L.length (ext_embed_poly #_ #_ #r a) in
    let la : nat = L.length a in
    embed_len_le #_ #_ #r a;                         (* le <= la *)
    (* sum gc 0 la = sum gc 0 le + sum gc le la *)
    sum_range_split gc 0 le la;
    (* the tail sum gc le la ~ zero(acr) *)
    sum_range_all_zero gc le la
      (fun (i:nat{le <= i /\ i < la}) -> conv_tail_zero #_ #_ #r a b k i);
    (* sum gc 0 le + sum gc le la ~ sum gc 0 le + zero ~ sum gc 0 le *)
    add_congruence
      (sum_range gc 0 le)
      (sum_range gc le la)
      (sum_range gc 0 le)
      (zero <: algebraic r);
    H.x_plus_zero (sum_range gc 0 le);
    (* chain:
         sum gc 0 la == sum gc 0 le + sum gc le la
                      ~ sum gc 0 le + zero
                      ~ sum gc 0 le                                             *)
    transitivity
      (sum_range gc 0 la)
      (sum_range gc 0 le + sum_range gc le la)
      (sum_range gc 0 le + (zero <: algebraic r));
    transitivity
      (sum_range gc 0 la)
      (sum_range gc 0 le + (zero <: algebraic r))
      (sum_range gc 0 le)

#push-options "--z3rlimit 80"
let ext_embed_poly_mul (#t:Type) {| f: field t |} (#r: polynomial t {proper_extension r})
                       (a b: polynomial t)
  : Lemma (
             (ext_embed_poly #_ #_ #r (a * b))
             =
             ((ext_embed_poly #_ #_ #r a) * (ext_embed_poly #_ #_ #r b)))
  = ac_elim_equatable_laws r;
    H.trans_for_calc (algebraic r) ();
    let ea  : polynomial (algebraic r) = ext_embed_poly a in
    let eb  : polynomial (algebraic r) = ext_embed_poly b in
    let lhs : polynomial (algebraic r) = ext_embed_poly (a * b) in
    let rhs : polynomial (algebraic r) = ea * eb in
    let aux (k:nat) : Lemma (coeff lhs k = coeff rhs k) =
      let gb : (nat -> t) = conv_base a b k in
      let gc : (nat -> algebraic r) = ac_const_comp gb in
      (* LHS: coeff lhs k ~ ac_const (coeff (a*b) k) *)
      embed_coeff #_ #_ #r (a * b) k;
      (* coeff (a*b) k = sum_range gb 0 (len a) *)
      coeff_poly_mul_named a b k gb
        (fun (i:nat) -> reflexivity (conv_base a b k i));
      (* ac_const (coeff (a*b) k) ~ ac_const (sum_range gb 0 (len a)) *)
      ac_const_congr #_ #_ #r (coeff (a * b) k)
                              (sum_range gb 0 (L.length a));
      (* ac_const (sum_range gb 0 (len a)) ~ sum_range gc 0 (len a) *)
      ac_const_sum_push #_ #_ #r gb 0 (L.length a);
      (* sum_range gc 0 (len a) ~ sum_range gc 0 (len ea) *)
      conv_range_bridge #_ #_ #r a b k;
      (* RHS: coeff rhs k = sum_range gc 0 (len ea) *)
      coeff_poly_mul_named ea eb k gc
        (fun (i:nat) -> mul_term_bridge #_ #_ #r a b k i);
      (* assemble the chain over acr:
           coeff lhs k ~ ac_const (coeff (a*b) k)
                       ~ ac_const (sum_range gb 0 (len a))
                       ~ sum_range gc 0 (len a)
                       ~ sum_range gc 0 (len ea)
                       == coeff rhs k                                             *)
      transitivity
        (coeff lhs k)
        (ac_const (coeff (a * b) k))
        (ac_const (sum_range gb 0 (L.length a)));
      transitivity
        (coeff lhs k)
        (ac_const (sum_range gb 0 (L.length a)))
        (sum_range gc 0 (L.length a));
      transitivity
        (coeff lhs k)
        (sum_range gc 0 (L.length a))
        (sum_range gc 0 (L.length ea))
    in
    poly_eq_by_coeff lhs rhs aux
#pop-options
