module FStar.Algebra.Classes.Fractions

open FStar.Algebra.Classes.Equatable
open FStar.Algebra.Classes.Grouplikes
open FStar.Algebra.Classes.Ringlikes

module TC = FStar.Tactics.Typeclasses

//instance semiring_of_integral_domain t {| d: integral_domain t |} = d.commutative_ring.ring.semiring

//instance has_one_of_id t {| d: integral_domain t |} = d.commutative_ring.mul_comm_monoid.mul_monoid 
instance eq_of_id t {| d: integral_domain t |} : equatable t 
  = d.commutative_ring.ring.semiring.add_comm_monoid.add_monoid.add_semigroup.has_add.eq 

instance has_zero_of_id t {| d: integral_domain t |} = d.commutative_ring.ring.semiring.add_comm_monoid.add_monoid.has_zero

instance has_one_of_id t {| d: integral_domain t |} = d.commutative_ring.mul_comm_monoid.mul_monoid.has_one

type nonzero_of #t (d: integral_domain t) = x:t{x<>zero}

type fraction #t (d: integral_domain t) = 
  | Fraction : (num:t) -> (den: nonzero_of d) -> fraction #t d

let ( / ) (#t:Type) {| d: integral_domain t |} (x:t) (y:nonzero_of d) : fraction d =
  Fraction x y
 
let fraction_one t {| d: integral_domain t |} =    
  let one:t = one in
  symmetry zero one;
  one/one

let dec (x: pos) : p:nat{p<<x} = (x - 1) <: int

instance eq_of_nat : equatable nat = {
  eq = int_equatable.eq;
  reflexivity = (fun _ -> ());
  symmetry = (fun _ _ -> ());
  transitivity = (fun _ _ _ -> ());
}

private let rec coerce_pos #t (r: semiring t) (x:nat) : t =
  let one:t = one in
  let zero:t = zero in
  let o,l : t&t = zero, one in
  if x `int_equatable.eq` 0 then o
  else l + coerce_pos r (dec x)

let ( |- ) #t (r: semiring t) (n: nat) : t = 
  coerce_pos r n

let product_of_denominators_is_valid_denominator #t {| d: integral_domain t |} (x y: fraction d)
  : Lemma (x.den * y.den <> (zero <: t)) = Classical.move_requires_2 (d.domain.domain_law) x.den y.den

let semiring_coerce_one #t (r: semiring t) : Lemma ( (r |- 1) = one ) = 
  let one : t = one in
  assert ((r|-1) == one + zero);
  right_add_identity one 

let fraction_eq #t {| d: integral_domain t |} (x y: fraction d) : bool =
  (x.num * y.den) = (x.den * y.num)

private let fraction_eq_symmetry_aux #t (d: integral_domain t) (x y: fraction d)
  : Lemma (fraction_eq x y ==> fraction_eq y x) = 
  mul_commutativity y.num x.den;
  mul_commutativity x.num y.den;
  symmetry (x.den*y.num) (x.num*y.den);
  if fraction_eq x y then
  trans_lemma [ y.num*x.den;
                x.den*y.num;
                x.num*y.den;
                y.den*x.num ]

let fraction_eq_is_symmetric #t (d:integral_domain t) (x y: fraction d)
  : Lemma (fraction_eq x y <==> fraction_eq y x) = 
  fraction_eq_symmetry_aux d x y;
  fraction_eq_symmetry_aux d y x 

let fraction_eq_is_reflexive #t (d:integral_domain t) (x: fraction d)
  : Lemma (fraction_eq x x) = mul_commutativity x.num x.den
 
let fraction_eq_is_transitive #t (dom:integral_domain t) (x y z: fraction dom)
  : Lemma (requires fraction_eq x y /\ fraction_eq y z) (ensures fraction_eq x z) = 
  let (=) = (eq_of_id t).eq in
  Classical.forall_intro (eq_of_id t).reflexivity;
  Classical.forall_intro_3 (Classical.move_requires_3 (eq_of_id t).transitivity);
  Classical.forall_intro_2 (eq_of_id t).symmetry; 
  let mul_congruence_3 (x y z:t) 
    : Lemma (requires x=y) (ensures (x*z = y*z) /\ (z*x = z*y)) 
    = mul_congruence x z y z; mul_congruence z x z y in
  let (a,b,c,d,e,f) : (t & t & t & t & t & t) = (x.num, x.den, y.num, y.den, z.num, z.den) in
  mul_congruence_3 (c*f) (d*e) (a*d);
  mul_congruence_3 (a*d) (b*c) (d*e);
  assert ((b*c)*(d*e) = (a*d)*(d*e)); 
  calc (=) {
    (b*c)*(d*e); = { mul_associativity (b*c) d e }
    ((b*c)*d)*e; = { mul_associativity b c d;
                     mul_congruence_3 ((b*c)*d) (b*(c*d)) e }
    (b*(c*d))*e; = { mul_commutativity c d; 
                     mul_congruence_3 (c*d) (d*c) b;
                     mul_congruence_3 (b*(c*d)) (b*(d*c)) e }
    (b*(d*c))*e;
  };
  calc (=) {
    (a*d)*(c*f); = { mul_associativity a d (c*f);
                     mul_associativity d c f;
                     mul_congruence_3 (d*(c*f)) ((d*c)*f) a }
    a*((d*c)*f);
  };
  
  admit();
  () 
