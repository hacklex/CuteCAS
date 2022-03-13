module Polynomials.Monomial

open FStar.Seq.Base
open AlgebraTypes
open Polynomials.Definition
open Polynomials.Equivalence
open Polynomials.Addition

private let stream_of_zeros #c (#r: commutative_ring c) (n: pos) 
  : (f:noncompact_poly_over_ring r{noncompact_poly_eq f empty}) = 
  let result = create n r.addition.neutral in
  zero_equals_self r; 
  poly_of_zeros_equals_empty #c #r result;
  result  
 
let monomial #c (r: commutative_ring c) (a:c) (degree: nat) 
  : Tot(z:noncompact_poly_over_ring r{
                                       is_nonempty z /\ (last z == a) /\ 
                                       noncompact_poly_eq (liat z) empty /\
                                       (nth z degree == a) /\
                                       (forall (i: nat{i<degree}). (nth z i == r.addition.neutral)) /\
                                       r.eq (last z) a
                                     }) (decreases degree) = 
  equals_self r a;   
  if degree=0 then create 1 a
  else (stream_of_zeros #c #r (degree)) $+ a 

let nth_of_monomial #c (r: commutative_ring c) (a:c) (deg: nat)
  : Lemma (forall (i: nat). (nth (monomial r a deg) i == (if (i=deg) then a else r.addition.neutral))) = ()

let monomial_length_is_deg #c (r: commutative_ring c) (a:c) (deg: nat) : Lemma (length (monomial r a deg) = (1+deg)) = ()

let monomial_leading_coefficient_is_a #c (r: commutative_ring c) (a:c) (deg: nat)
  : Lemma (nth (monomial r a deg) deg == a) = ()
  
let monomial_other_coefficients_are_zeros #c (r: commutative_ring c) (a:c) (deg: nat) (i: nat{i<>deg})
  : Lemma (nth (monomial r a deg) i == r.addition.neutral) = ()

let monomial_equality_lemma #c (r: commutative_ring c) (a:c) (b:c{r.eq a b}) (degree: nat)
  : Lemma (ensures ncpoly_eq (monomial r a degree) (monomial r b degree)) (decreases degree) 
  = if degree > 0 then eq_of_snoc (stream_of_zeros #c #r degree) a b  

let monomial_zero_lemma #c (r: commutative_ring c) (a:c{r.eq a r.addition.neutral}) (degree: nat)
  : Lemma (monomial r a degree `ncpoly_eq` empty) = poly_eq_from_nth_eq (monomial r a degree) empty
