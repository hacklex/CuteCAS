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

instance equatable_of_nonzeros t (d: integral_domain t) : equatable (nonzero_of d) = {
  eq = (eq_of_id t #d).eq;
  reflexivity = (eq_of_id t #d).reflexivity;
  symmetry = (eq_of_id t #d).symmetry;
  transitivity = (eq_of_id t #d).transitivity
}

instance has_mul t (d: integral_domain t) : has_mul (nonzero_of d) = {
  eq = equatable_of_nonzeros t d;
  mul = (fun (x y: nonzero_of d) -> (
    Classical.move_requires_2 domain_law (x <: t) (y <: t);
    d.commutative_ring.ring.semiring.mul_monoid.mul_semigroup.has_mul.mul x y
  ));
  congruence = d.commutative_ring.ring.semiring.mul_monoid.mul_semigroup.has_mul.congruence
}

let ( / ) (#t:Type) {| d: integral_domain t |} (x:t) (y:t) 
  : Pure (fraction d) (requires y <> zero) (ensures fun _ -> True) =
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

let fraction_eq_from_num_den #t {| d: integral_domain t |} (x y: fraction d) 
  : Lemma (requires ((eq_of_id t).eq x.den y.den) /\ (x.num = y.num)) (ensures fraction_eq x y) = 
  let a,b,c,d : t&t&t&t = x.num, x.den, y.num, y.den in
  symmetry b d; 
  mul_congruence a d c b;
  mul_commutativity c b;
  transitivity (a*d) (c*b) (b*c)

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


/// This lemma proves that for any three fractions x,y,z,
///        if x=y && y=z then x=z,
///          where (=) is the fraction_eq function
///
/// -- or, if we speak in terms of parent domain,
///       if (x.num*y.den = x.den*y.num) and
///          (y.num*z.den = y.den*z.num),
///       then (x.num*z.den = x.den*z.num),
/// (=) being the parent domain equivalence relation
let fraction_eq_is_transitive #t (dom:integral_domain t) (x y z: fraction dom)
  : Lemma (requires fraction_eq x y /\ fraction_eq y z) (ensures fraction_eq x z) = 
  
  let (=) = (eq_of_id t).eq in // extracted for performance reasons
  
  Classical.forall_intro (eq_of_id t).reflexivity; // these decrease verbosity
  Classical.forall_intro_2 (eq_of_id t).symmetry; 
  // transitivity lemma is ill-suited for forall 
  // (often we still need to call trans_lemma manually) --
  // but this invocation is required by the calc block below.
  Classical.forall_intro_3 (Classical.move_requires_3 (eq_of_id t).transitivity);
  let mul_congruence_3 (x y z:t) 
    : Lemma (requires x=y) (ensures (x*z = y*z) /\ (z*x = z*y)) 
    = mul_congruence x z y z; mul_congruence z x z y in
  let (a,b,c,d,e,f) : (t & t & t & t & t & t) // type ascription to fix typeclass resolution issue
    = (x.num, x.den, y.num, y.den, z.num, z.den) in  

  // in these terms, we're proving that (ad=bc && cf=de ==> af=be)

  let zero : t = zero in // added this to eliminate type ascriptions 
  mul_congruence_3 (c*f) (d*e) (a*d);
  mul_congruence_3 (a*d) (b*c) (d*e);
  assert ((b*c)*(d*e) = (a*d)*(c*f));  
  calc (=) { // this should be an assert (f = g) by ([assoc; congr; comm]) or something of the sort
    (b*c)*(d*e); = { mul_associativity (b*c) d e }
    ((b*c)*d)*e; = { mul_associativity b c d;
                     mul_congruence_3 ((b*c)*d) (b*(c*d)) e }
    (b*(c*d))*e; = { mul_commutativity b (c*d); 
                     mul_congruence_3 (b*(c*d)) ((c*d)*b) e;
                     mul_associativity (c*d) b e }
    (c*d)*(b*e);
  }; // this as well could probably be simplified to an *assertion by* couple of tactic calls
  calc (=) {
    (a*d)*(c*f); = { mul_associativity a d (c*f);
                     mul_associativity d c f;
                     mul_congruence_3 (d*(c*f)) ((d*c)*f) a }
    a*((d*c)*f); = { mul_commutativity d c;
                     mul_congruence_3 (d*c) (c*d) f;
                     mul_congruence_3 ((d*c)*f) ((c*d)*f) a;
                     mul_commutativity a ((c*d)*f);
                     mul_associativity (c*d) f a;
                     mul_commutativity f a;
                     mul_congruence_3 (f*a) (a*f) (c*d) }
    (c*d)*(a*f);     
  };
  //This one already feels like a tactic call :)
  trans_lemma [ (c*d)*(a*f); (a*d)*(c*f); (b*c)*(d*e); (c*d)*(b*e) ];
  assert ((c*d)*(a*f) = (c*d)*(b*e));
  if (c*d <> zero) then
  left_cancellation (c*d) (a*f) (b*e) 
  else begin
    domain_law c d; //cd=0 ==> c=0 since d is denominator and hence <> 0
    absorption c f; //cf=0
    transitivity (d*e) (c*f) zero; //de=cf=0
    domain_law d e; //e=0 since d can't be 0
    absorption c b; //c=0 ==> b*c=0
    transitivity (a*d) (b*c) zero; //ad=0
    domain_law a d; //same reasoning for a=0
    absorption a f; //then af=0
    absorption e b; //also be=0
    transitivity (a*f) zero (b*e); //0=0=0 :)
    () 
  end

instance fraction_equatable t (d: integral_domain t) : equatable (fraction d) = {
  eq = fraction_eq #t #d;
  reflexivity = fraction_eq_is_reflexive d;
  symmetry = fraction_eq_is_symmetric d;
  transitivity = fraction_eq_is_transitive d
}

let fraction_add #t {| dom: integral_domain t |} (x y: fraction dom) : fraction dom = 
  let a,b,c,d : t&t&t&t = x.num, x.den,y.num,y.den in
  product_of_denominators_is_valid_denominator x y;
  (a*d+b*c)/(b*d <: t)

let fraction_add_is_commutative #t {| d: integral_domain t |} (x y: fraction d) 
  : Lemma (fraction_add x y = fraction_add y x) =
  let a,b,c,d : t&t&t&t = x.num, x.den,y.num,y.den in 
  let eq : equatable t = TC.solve in
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  
  assert ((fraction_add x y).num == a*d + b*c);
  reflexivity (fraction_add x y).num;
  reflexivity (fraction_add y x).num;
  reflexivity (b*d);
  reflexivity (d*b);
  assert ((fraction_add x y).num = a*d + b*c);
  assert ((fraction_add y x).num = c*b + d*a);
  calc (=) {
    a*d + b*c; = { add_commutativity (a*d) (b*c) }
    b*c + a*d; = { mul_commutativity b c;
                   mul_commutativity a d;
                   add_congruence (b*c) (a*d) (c*b) (d*a) }
    c*b + d*a;
  };
  mul_commutativity b d;  
  fraction_eq_from_num_den (fraction_add x y) (fraction_add y x)

let fraction_add_is_associative #t {| d: integral_domain t |} (x y z: fraction d) 
  : Lemma (fraction_add (fraction_add x y) z `fraction_eq` fraction_add x (fraction_add y z)) =
  admit()
