module Core.Fractions.DerivativeSum

(*
   Rational-derivative SUM RULE (additivity of D over fraction addition):

     D(x + y)  =  D(x) + D(y)

   for rational functions x, y over a field t, where D = `rational_deriv`
   (the quotient-rule derivative) and `+` is `fraction_add`.

   Strategy:  write x = a/b, y = c/d.  Both sides become explicit fractions
   whose numerators/denominators are polynomial ring expressions.  The
   fraction equality reduces (via `fraction_eq_reveal`) to a single
   cross-multiplied polynomial identity.  We first expand the derivatives
   that appear inside the numerator of the LHS (N' and D') into ring
   expressions in the 8 atoms {a,b,c,d,a',b',c',d'} using `poly_deriv_add`
   and `poly_deriv_mul`, rewrite by congruence, and then discharge the
   resulting pure ring identity with `CR.canon_ring ()`.

   NO admit / assume / sorry in the final version.
*)

module H  = Core.Algebra.Helpers
module CR = Core.Tactics.CanonRing

open Core.Algebra
open Core.Algebra.Notation
open Core.Polynomial
open Core.Polynomial.Derivative
open Core.Fractions
open Core.Fractions.Derivative

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* ================================================================ *)
(*  Pure generic-ring cross-product identity (GOAL-X).               *)
(*                                                                   *)
(*  Atoms: a b c d  (the four polynomials) and their derivatives     *)
(*  a' b' c' d'.  All eight are opaque to `canon_ring`.              *)
(*                                                                   *)
(*  num(LHS) (expanded)                                              *)
(*    = ((a'*d + a*d' + b'*c + b*c') * (b*d))                        *)
(*        -- ((a*d + b*c) * (b'*d + b*d'))                           *)
(*  den(RHS) = (b*b)*(d*d)                                           *)
(*  den(LHS) = (b*d)*(b*d)                                           *)
(*  num(RHS) = ((a'*b -- a*b')*(d*d)) + ((b*b)*(c'*d -- c*d'))       *)
(*                                                                   *)
(*  GOAL-X:  num(LHS) * den(RHS)  =  den(LHS) * num(RHS).            *)
(* ================================================================ *)
#push-options "--z3rlimit 120"
private let cross_id (#r:Type) {| cr: commutative_ring r |}
  (a b c d a' b' c' d': r)
  : Lemma (
      ((((a' * d + a * d' + b' * c + b * c') * (b * d))
          -- ((a * d + b * c) * (b' * d + b * d')))
        * ((b * b) * (d * d)))
      = (((b * d) * (b * d))
         * (((a' * b -- a * b') * (d * d)) + ((b * b) * (c' * d -- c * d')))))
  = assert (
      ((((a' * d + a * d' + b' * c + b * c') * (b * d))
          -- ((a * d + b * c) * (b' * d + b * d')))
        * ((b * b) * (d * d)))
      = (((b * d) * (b * d))
         * (((a' * b -- a * b') * (d * d)) + ((b * b) * (c' * d -- c * d')))))
      by (CR.canon_ring ())
#pop-options

(* ================================================================ *)
(*  Main lemma: additivity of the rational derivative.               *)
(* ================================================================ *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 1"
let rational_deriv_add (#t:Type) {| f: field t |} (x y: rational_function f)
  : Lemma (
      rational_deriv (fraction_add x y)
      = fraction_add
          (rational_deriv x) (rational_deriv y))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* the four polynomials *)
    let a : polynomial t = Fraction?.num x in
    let b : polynomial t = Fraction?.den x in
    let c : polynomial t = Fraction?.num y in
    let d : polynomial t = Fraction?.den y in
    let a' = poly_deriv a in
    let b' = poly_deriv b in
    let c' = poly_deriv c in
    let d' = poly_deriv d in

    (* ---- LHS side ---- *)
    let sum = fraction_add x y in
    fraction_add_reveal x y;
    (* N = num(sum) = a*d + b*c ; D = den(sum) = b*d *)
    let bigN : polynomial t = Fraction?.num sum in
    let bigD : polynomial t = Fraction?.den sum in
    rational_deriv_reveal sum;
    (* num(LHS) = N' -- N*D' ; den(LHS) = D*D, where N' = poly_deriv N,
       D' = poly_deriv D.  Here num(LHS) = N'*D -- N*D'. *)
    let lhs = rational_deriv sum in
    let bigNp = poly_deriv bigN in
    let bigDp = poly_deriv bigD in

    (* ---- RHS side ---- *)
    let dx = rational_deriv x in
    let dy = rational_deriv y in
    rational_deriv_reveal x;   (* num(dx) = a'*b -- a*b' ; den(dx) = b*b *)
    rational_deriv_reveal y;   (* num(dy) = c'*d -- c*d' ; den(dy) = d*d *)
    fraction_add_reveal dx dy;
    let rhs = fraction_add dx dy in
    (* num(rhs) = (a'b--ab')*(d*d) + (b*b)*(c'd--cd') ; den(rhs) = (b*b)*(d*d) *)

    (* ---- expand the derivatives that sit inside num(LHS) ---- *)
    (* N = a*d + b*c, so N' ~ (a*d)' + (b*c)' ~ (a'*d + a*d') + (b'*c + b*c') *)
    poly_deriv_add (a * d) (b * c);
    poly_deriv_mul a d;
    poly_deriv_mul b c;
    (* bigNp = poly_deriv (a*d + b*c)
              ~ poly_deriv (a*d) + poly_deriv (b*c)
              ~ (a'*d + a*d') + (b'*c + b*c') *)
    poly_add_congruence
      (poly_deriv (a * d)) (poly_deriv (b * c))
      ((a' * d) + (a * d')) ((b' * c) + (b * c'));
    (* D = b*d, so D' ~ b'*d + b*d' *)
    poly_deriv_mul b d;
    (* bigDp ~ b'*d + b*d' *)

    let expNp : polynomial t = ((a' * d) + (a * d')) + ((b' * c) + (b * c')) in
    let expDp : polynomial t = (b' * d) + (b * d') in

    (* num(LHS) = bigNp * bigD -- bigN * bigDp.
       Rewrite by congruence to  expNp * bigD -- bigN * expDp. *)
    let numL : polynomial t = (bigNp * bigD) -- (bigN * bigDp) in
    poly_mul_congruence bigNp bigD expNp bigD;       (* bigNp*bigD ~ expNp*bigD *)
    poly_mul_congruence bigN bigDp bigN expDp;        (* bigN*bigDp ~ bigN*expDp *)
    poly_neg_congruence (bigN * bigDp) (bigN * expDp);
    poly_add_congruence
      (bigNp * bigD) (- (bigN * bigDp))
      (expNp * bigD) (- (bigN * expDp));
    let numLexp : polynomial t = (expNp * bigD) -- (bigN * expDp) in
    (* numL ~ numLexp *)

    (* Now bigN = a*d + b*c and bigD = b*d definitionally (from
       fraction_add_reveal == equalities), so numLexp is, up to the
       opaque atoms, exactly the LHS-numerator of cross_id with
         expNp = a'*d + a*d' + b'*c + b*c'  (associated as above).
       cross_id uses left-nested sum  a'*d + a*d' + b'*c + b*c'
       = ((a'*d + a*d') + b'*c) + b*c, but `+` parses left-assoc, so
       cross_id's atom is (((a'*d + a*d') + b'*c) + b*c'); our expNp is
       ((a'*d + a*d') + (b'*c + b*c')).  Bridge them by associativity. *)
    let cid_Np : polynomial t = a' * d + a * d' + b' * c + b * c' in
    (* cid_Np == (((a'*d + a*d') + b'*c) + b*c')  by left-assoc parsing *)
    poly_add_associativity ((a' * d) + (a * d')) (b' * c) (b * c');
    (* (((a'*d+a*d')+b'*c)+b*c') ~ ((a'*d+a*d')+(b'*c+b*c')) = expNp *)
    (* expNp ~ cid_Np  ... actually we want cid_Np ~ expNp; assoc gives
       (X+Y)+Z ~ X+(Y+Z) i.e. cid_Np ~ expNp. *)
    poly_mul_congruence expNp bigD cid_Np bigD;       (* expNp*bigD ~ cid_Np*bigD *)
    poly_add_congruence
      (expNp * bigD) (- (bigN * expDp))
      (cid_Np * bigD) (- (bigN * expDp));
    let numLcid : polynomial t = (cid_Np * bigD) -- (bigN * expDp) in
    (* numLexp ~ numLcid *)
    (* numL ~ numLcid *)

    (* The pure ring identity in the 8 atoms. *)
    cross_id a b c d a' b' c' d';
    (* cross_id LHS-num == numLcid (definitionally, since bigN==a*d+b*c,
       bigD==b*d, expDp==b'*d+b*d').  cross_id states:
         numLcid * ((b*b)*(d*d))  =  ((b*d)*(b*d)) * num(rhs)
       which is exactly  numL * den(rhs)  ~  den(LHS) * num(rhs)
       after the numL ~ numLcid rewrite on the left factor. *)

    (* den(LHS) = bigD * bigD ; we need numL * den(rhs) = den(LHS) * num(rhs).
       fraction_eq_reveal reduces (lhs = rhs) to
         num(lhs)*den(rhs) = den(lhs)*num(rhs). *)
    let denR : polynomial t = (b * b) * (d * d) in
    let numR : polynomial t = ((a' * b -- a * b') * (d * d))
                              + ((b * b) * (c' * d -- c * d')) in
    (* numL * denR ~ numLcid * denR   (left congruence) *)
    poly_mul_congruence numL denR numLcid denR;
    (* numLcid * denR = den(LHS) * numR  is cross_id (an `=`, i.e. poly_eq). *)

    (* Bridge the published fraction `=` to the cross product. *)
    fraction_eq_reveal lhs rhs
#pop-options

(* ================================================================ *)
(*  Pure generic-ring identity for the CONGRUENCE (well-definedness) *)
(*  argument.                                                        *)
(*                                                                   *)
(*  Atoms a b c d a' b' c' d'.  With                                 *)
(*    E    = (a'*d + a*d') -- (b'*c + b*c')   (DREL ~ 0)            *)
(*    R    = (a*d) -- (b*c)                    (REL  ~ 0)            *)
(*    Fcof = -(b'*d + b*d')                                          *)
(*  the cross-product difference factors as                         *)
(*    (a'*b -- a*b')*(d*d)                                           *)
(*      = (b*b)*(c'*d -- c*d')   +   ( (b*d)*E  +  R*Fcof )          *)
(*  certified by `canon_ring`.                                       *)
(* ================================================================ *)
#push-options "--z3rlimit 120"
private let cross_id_cong (#r:Type) {| cr: commutative_ring r |}
  (a b c d a' b' c' d': r)
  : Lemma (
      ((a' * b -- a * b') * (d * d))
      = (((b * b) * (c' * d -- c * d'))
         + (((b * d) * (((a' * d + a * d') -- (b' * c + b * c'))))
            + (((a * d) -- (b * c)) * (- ((b' * d) + (b * d')))))))
  = assert (
      ((a' * b -- a * b') * (d * d))
      = (((b * b) * (c' * d -- c * d'))
         + (((b * d) * (((a' * d + a * d') -- (b' * c + b * c'))))
            + (((a * d) -- (b * c)) * (- ((b' * d) + (b * d')))))))
      by (CR.canon_ring ())
#pop-options

(* ================================================================ *)
(*  Main lemma: well-definedness of the rational derivative.         *)
(*  Equal fractions have equal derivatives.                          *)
(* ================================================================ *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 1"
let rational_deriv_cong (#t:Type) {| f: field t |} (x y: rational_function f)
  : Lemma (requires x = y)
          (ensures rational_deriv x = rational_deriv y)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* x = a/b, y = c/d *)
    let a : polynomial t = Fraction?.num x in
    let b : polynomial t = Fraction?.den x in
    let c : polynomial t = Fraction?.num y in
    let d : polynomial t = Fraction?.den y in
    let a' = poly_deriv a in
    let b' = poly_deriv b in
    let c' = poly_deriv c in
    let d' = poly_deriv d in

    (* ---- REL: from x = y, cross-multiplication gives a*d ~ b*c ---- *)
    fraction_eq_reveal x y;
    (* (x = y) <==> (num x * den y = den x * num y), i.e. a*d = b*c *)
    (* so REL: poly_eq (a*d) (b*c) *)

    (* ---- DREL: differentiate REL ---- *)
    poly_deriv_congruence (a * d) (b * c);
    (* poly_deriv (a*d) ~ poly_deriv (b*c) *)
    poly_deriv_mul a d;     (* poly_deriv (a*d) ~ a'*d + a*d' *)
    poly_deriv_mul b c;     (* poly_deriv (b*c) ~ b'*c + b*c' *)
    (* (a'*d + a*d') ~ poly_deriv (a*d) ~ poly_deriv (b*c) ~ (b'*c + b*c') *)
    (* DREL: poly_eq ((a'*d + a*d')) ((b'*c + b*c')) *)

    (* ---- abbreviations matching cross_id_cong ---- *)
    let bigE : polynomial t = ((a' * d) + (a * d')) -- ((b' * c) + (b * c')) in
    let bigR : polynomial t = (a * d) -- (b * c) in
    let fcof : polynomial t = - ((b' * d) + (b * d')) in
    let correction : polynomial t = ((b * d) * bigE) + (bigR * fcof) in

    let pzero : polynomial t = zero in
    (* ---- bigE = pzero  (from DREL) ---- *)
    H.sub_self_zero ((a' * d) + (a * d')) ((b' * c) + (b * c'));
    (* bigE = pzero *)
    (* ---- bigR = pzero  (from REL) ---- *)
    H.sub_self_zero (a * d) (b * c);
    (* bigR = pzero *)

    (* ---- (b*d)*bigE = pzero ---- *)
    poly_mul_congruence (b * d) bigE (b * d) pzero;
    H.x_mul_zero (b * d);
    (* ---- bigR*fcof = pzero ---- *)
    poly_mul_congruence bigR fcof pzero fcof;
    H.zero_mul_x fcof;
    (* ---- correction = pzero ---- *)
    poly_add_congruence
      ((b * d) * bigE) (bigR * fcof)
      pzero pzero;
    H.x_plus_zero pzero;
    (* correction = pzero *)

    (* ---- target ring identity (canon_ring): LHS_term = RHS_term + correction *)
    let lhsTerm : polynomial t = (a' * b -- a * b') * (d * d) in
    let rhsTerm : polynomial t = (b * b) * (c' * d -- c * d') in
    cross_id_cong a b c d a' b' c' d';
    (* lhsTerm = rhsTerm + correction *)

    (* ---- rhsTerm + correction ~ rhsTerm + pzero ~ rhsTerm ---- *)
    poly_add_congruence
      rhsTerm correction
      rhsTerm pzero;
    H.x_plus_zero rhsTerm;
    (* lhsTerm ~ rhsTerm + correction ~ rhsTerm  *)
    (* GOAL: poly_eq lhsTerm rhsTerm, i.e.
       (a'*b -- a*b')*(d*d) = (b*b)*(c'*d -- c*d') *)

    (* ---- package back to rational_deriv x = rational_deriv y ---- *)
    rational_deriv_reveal x;   (* num(Dx) = a'*b -- a*b' ; den(Dx) = b*b *)
    rational_deriv_reveal y;   (* num(Dy) = c'*d -- c*d' ; den(Dy) = d*d *)
    fraction_eq_reveal
      (rational_deriv x) (rational_deriv y)
#pop-options

(* ================================================================ *)
(*  Pure generic-ring cross-product identity for the PRODUCT rule.   *)
(*                                                                   *)
(*  x = a/b, y = c/d.   xy = (a*c)/(b*d).                            *)
(*                                                                   *)
(*  num(LHS) (expanded, N'=a'c+ac', D'=b'd+bd')                      *)
(*    = ((a'*c + a*c') * (b*d)) -- ((a*c) * (b'*d + b*d'))           *)
(*  den(LHS) = (b*d)*(b*d)                                           *)
(*  num(RHS) = (((a'*b -- a*b')*c) * (b*(d*d)))                      *)
(*             + (((b*b)*d) * (a*(c'*d -- c*d')))                    *)
(*  den(RHS) = ((b*b)*d) * (b*(d*d))                                 *)
(*                                                                   *)
(*  GOAL-X:  num(LHS) * den(RHS)  =  den(LHS) * num(RHS).            *)
(* ================================================================ *)
#push-options "--z3rlimit 300 --fuel 2 --ifuel 1"
private let cross_id_mul (#r:Type) {| cr: commutative_ring r |}
  (a b c d a' b' c' d': r)
  : Lemma (
      ((((a' * c + a * c') * (b * d)) -- ((a * c) * (b' * d + b * d')))
        * (((b * b) * d) * (b * (d * d))))
      = (((b * d) * (b * d))
         * (((((a' * b -- a * b') * c) * (b * (d * d))))
            + ((((b * b) * d) * (a * (c' * d -- c * d')))))))
  = assert (
      ((((a' * c + a * c') * (b * d)) -- ((a * c) * (b' * d + b * d')))
        * (((b * b) * d) * (b * (d * d))))
      = (((b * d) * (b * d))
         * (((((a' * b -- a * b') * c) * (b * (d * d))))
            + ((((b * b) * d) * (a * (c' * d -- c * d')))))))
      by (CR.canon_ring ())
#pop-options

(* ================================================================ *)
(*  Main lemma: Leibniz product rule for the rational derivative.    *)
(* ================================================================ *)
#push-options "--z3rlimit 120 --fuel 2 --ifuel 1"
let rational_deriv_mul (#t:Type) {| f: field t |} (x y: rational_function f)
  : Lemma (
      rational_deriv (fraction_mul x y)
      = fraction_add
          (fraction_mul (rational_deriv x) y)
          (fraction_mul x (rational_deriv y)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* the four polynomials *)
    let a : polynomial t = Fraction?.num x in
    let b : polynomial t = Fraction?.den x in
    let c : polynomial t = Fraction?.num y in
    let d : polynomial t = Fraction?.den y in
    let a' = poly_deriv a in
    let b' = poly_deriv b in
    let c' = poly_deriv c in
    let d' = poly_deriv d in

    (* ---- LHS side ---- *)
    let prod = fraction_mul x y in
    fraction_mul_reveal x y;
    (* N = num(prod) = a*c ; D = den(prod) = b*d *)
    let bigN : polynomial t = Fraction?.num prod in
    let bigD : polynomial t = Fraction?.den prod in
    rational_deriv_reveal prod;
    (* num(LHS) = N'*D -- N*D' ; den(LHS) = D*D, where N' = poly_deriv N,
       D' = poly_deriv D. *)
    let lhs = rational_deriv prod in
    let bigNp = poly_deriv bigN in
    let bigDp = poly_deriv bigD in

    (* ---- RHS side ---- *)
    let dx = rational_deriv x in
    let dy = rational_deriv y in
    rational_deriv_reveal x;   (* num(dx) = a'*b -- a*b' ; den(dx) = b*b *)
    rational_deriv_reveal y;   (* num(dy) = c'*d -- c*d' ; den(dy) = d*d *)
    fraction_mul_reveal dx y;
    (* num(dx*y) = (a'*b -- a*b')*c ; den(dx*y) = (b*b)*d *)
    fraction_mul_reveal x dy;
    (* num(x*dy) = a*(c'*d -- c*d') ; den(x*dy) = b*(d*d) *)
    let dxy = fraction_mul dx y in
    let xdy = fraction_mul x dy in
    fraction_add_reveal dxy xdy;
    let rhs = fraction_add dxy xdy in
    (* num(rhs) = ((a'b--ab')*c)*(b*(d*d)) + ((b*b)*d)*(a*(c'd--cd')) ;
       den(rhs) = ((b*b)*d)*(b*(d*d)) *)

    (* ---- expand the derivatives that sit inside num(LHS) ---- *)
    (* N = a*c, so N' ~ a'*c + a*c' *)
    poly_deriv_mul a c;
    (* bigNp ~ a'*c + a*c' *)
    (* D = b*d, so D' ~ b'*d + b*d' *)
    poly_deriv_mul b d;
    (* bigDp ~ b'*d + b*d' *)

    let expNp : polynomial t = (a' * c) + (a * c') in
    let expDp : polynomial t = (b' * d) + (b * d') in

    (* num(LHS) = bigNp * bigD -- bigN * bigDp.
       Rewrite by congruence to  expNp * bigD -- bigN * expDp. *)
    let numL : polynomial t = (bigNp * bigD) -- (bigN * bigDp) in
    poly_mul_congruence bigNp bigD expNp bigD;       (* bigNp*bigD ~ expNp*bigD *)
    poly_mul_congruence bigN bigDp bigN expDp;        (* bigN*bigDp ~ bigN*expDp *)
    poly_neg_congruence (bigN * bigDp) (bigN * expDp);
    poly_add_congruence
      (bigNp * bigD) (- (bigN * bigDp))
      (expNp * bigD) (- (bigN * expDp));
    let numLexp : polynomial t = (expNp * bigD) -- (bigN * expDp) in
    (* numL ~ numLexp *)

    (* bigN = a*c and bigD = b*d definitionally (from fraction_mul_reveal ==
       equalities), so numLexp is, up to the opaque atoms, exactly the
       LHS-numerator of cross_id_mul. *)
    (* The pure ring identity in the 8 atoms. *)
    cross_id_mul a b c d a' b' c' d';
    (* cross_id_mul LHS-num == numLexp (definitionally: bigN==a*c, bigD==b*d,
       expNp==a'*c+a*c', expDp==b'*d+b*d').  cross_id_mul states:
         numLexp * den(rhs)  =  ((b*d)*(b*d)) * num(rhs)
       which is exactly  numL * den(rhs)  ~  den(LHS) * num(rhs)
       after the numL ~ numLexp rewrite on the left factor. *)

    (* den(LHS) = bigD * bigD ; we need numL * den(rhs) = den(LHS) * num(rhs).
       fraction_eq_reveal reduces (lhs = rhs) to
         num(lhs)*den(rhs) = den(lhs)*num(rhs). *)
    let denR : polynomial t = ((b * b) * d) * (b * (d * d)) in
    let numR : polynomial t = (((a' * b -- a * b') * c) * (b * (d * d)))
                              + (((b * b) * d) * (a * (c' * d -- c * d'))) in
    (* numL * denR ~ numLexp * denR   (left congruence) *)
    poly_mul_congruence numL denR numLexp denR;
    (* numLexp * denR = den(LHS) * numR  is cross_id_mul (an `=`, i.e. poly_eq). *)

    (* Bridge the published fraction `=` to the cross product. *)
    fraction_eq_reveal lhs rhs
#pop-options
