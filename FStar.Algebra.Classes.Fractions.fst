module FStar.Algebra.Classes.Fractions

open FStar.Algebra.Classes.Equatable
open FStar.Algebra.Classes.Grouplikes
open FStar.Algebra.Classes.Ringlikes

module TC = FStar.Tactics.Typeclasses 

//instance semiring_of_integral_domain t {| d: integral_domain t |} 
//  = d.commutative_ring.ring.semiring

//instance has_one_of_id t {| d: integral_domain t |} = d.commutative_ring.mul_comm_monoid.mul_monoid 
instance eq_of_id t {| d: integral_domain t |} : equatable t 
  = d.commutative_ring.ring.semiring.add_comm_monoid.add_monoid.add_semigroup.has_add.eq 

instance has_zero_of_id t {| d: integral_domain t |} = d.commutative_ring.ring.semiring.add_comm_monoid.add_monoid.has_zero

instance has_one_of_id t {| d: integral_domain t |} = d.commutative_ring.mul_comm_monoid.mul_monoid.has_one

type nonzero_of #t (d: integral_domain t) = x:t{x<>zero}

type fraction #t (d: integral_domain t) = 
  | Fraction : (num:t) -> (den: nonzero_of d) -> fraction #t d

instance equatable_of_nonzeros t (d: integral_domain t) : equatable (nonzero_of d) = {
  ( = ) = (eq_of_id t #d).op_Equals;
  reflexivity = (eq_of_id t #d).reflexivity;
  symmetry = (eq_of_id t #d).symmetry;
  transitivity = (eq_of_id t #d).transitivity
}

// (Removed an experimental `has_mul (nonzero_of d)` instance: it had stale
// field names, an unrefined return type, and is not needed by the fraction
// development below — products of nonzero elements are handled directly via
// `domain_law`/`product_of_denominators_is_valid_denominator`.)

let ( / ) (#t:Type) {| d: integral_domain t |} (x:t) (y:t) 
  : Pure (fraction d) (requires y <> zero) (ensures fun _ -> True) =
  Fraction x y
 
let fraction_one t {| d: integral_domain t |} =    
  let one:t = one in
  symmetry zero one;
  one/one

let dec (x: pos) : p:nat{p<<x} = (x - 1) <: int

instance eq_of_nat : equatable nat = {
  ( = ) = int_equatable.op_Equals;
  reflexivity = (fun _ -> ());
  symmetry = (fun _ _ -> ());
  transitivity = (fun _ _ _ -> ());
}

private let rec coerce_pos #t (r: semiring t) (x:nat) : t =
  let one:t = one in
  let zero:t = zero in
  let o,l : t&t = zero, one in
  if x `int_equatable.op_Equals` 0 then o
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
  : Lemma (requires ((eq_of_id t).op_Equals x.den y.den) /\ (x.num = y.num)) (ensures fraction_eq x y) = 
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
  
  let (=) = (eq_of_id t).op_Equals in // extracted for performance reasons
  
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
  ( = ) = fraction_eq #t #d;
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

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"
let fraction_add_is_associative #t {| dom: integral_domain t |} (x y z: fraction dom)
  : Lemma (fraction_add (fraction_add x y) z `fraction_eq` fraction_add x (fraction_add y z)) =
  let a,b,c,d,e,f : t&t&t&t&t&t = x.num, x.den, y.num, y.den, z.num, z.den in
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  product_of_denominators_is_valid_denominator x y;
  product_of_denominators_is_valid_denominator y z;
  let xy = fraction_add x y in
  let yz = fraction_add y z in
  product_of_denominators_is_valid_denominator xy z;
  product_of_denominators_is_valid_denominator x yz;
  let lhs = fraction_add xy z in
  let rhs = fraction_add x yz in
  // lhs.num = (a*d+b*c)*f + (b*d)*e   ;   lhs.den = (b*d)*f
  // rhs.num = a*(d*f) + b*(c*f+d*e)   ;   rhs.den = b*(d*f)
  calc (=) {
    (a*d+b*c)*f + (b*d)*e;
    = { right_distributivity (a*d) (b*c) f;
        add_congruence ((a*d+b*c)*f) ((b*d)*e) ((a*d)*f + (b*c)*f) ((b*d)*e) }
    ((a*d)*f + (b*c)*f) + (b*d)*e;
    = { mul_associativity a d f;
        mul_associativity b c f;
        add_congruence ((a*d)*f) ((b*c)*f) (a*(d*f)) (b*(c*f));
        mul_associativity b d e;
        add_congruence ((a*d)*f + (b*c)*f) ((b*d)*e)
                       (a*(d*f) + b*(c*f))   (b*(d*e)) }
    (a*(d*f) + b*(c*f)) + b*(d*e);
    = { add_associativity (a*(d*f)) (b*(c*f)) (b*(d*e)) }
    a*(d*f) + (b*(c*f) + b*(d*e));
    = { left_distributivity b (c*f) (d*e);
        add_congruence (a*(d*f)) (b*(c*f) + b*(d*e))
                       (a*(d*f)) (b*(c*f + d*e)) }
    a*(d*f) + b*(c*f + d*e);
  };
  // Denominator: (b*d)*f = b*(d*f)
  mul_associativity b d f;
  fraction_eq_from_num_den lhs rhs
#pop-options

// ============================================================
// Phase A — Additive commutative group on (fraction d)
// ============================================================

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

/// Helper: (a*b)*(c*d) = (a*c)*(b*d). Used pervasively below.
let mul_middle_swap #t {| d: integral_domain t |} (a b c e: t)
  : Lemma ((a*b)*(c*e) = (a*c)*(b*e)) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  calc (=) {
    (a*b)*(c*e);
    = { mul_associativity a b (c*e) }
    a*(b*(c*e));
    = { mul_associativity b c e;
        mul_congruence a (b*(c*e)) a ((b*c)*e) }
    a*((b*c)*e);
    = { mul_commutativity b c;
        mul_congruence (b*c) e (c*b) e;
        mul_congruence a ((b*c)*e) a ((c*b)*e) }
    a*((c*b)*e);
    = { mul_associativity c b e;
        mul_congruence a ((c*b)*e) a (c*(b*e)) }
    a*(c*(b*e));
    = { mul_associativity a c (b*e) }
    (a*c)*(b*e);
  }

#pop-options

#push-options "--z3rlimit 5 --fuel 2 --ifuel 2"
/// Left congruence: x1 = x2 ==> x1 + y = x2 + y.
let fraction_add_left_congruence #t {| dom: integral_domain t |} (x1 x2 y: fraction dom)
  : Lemma (requires fraction_eq x1 x2)
          (ensures  fraction_eq (fraction_add x1 y) (fraction_add x2 y)) =
  let a,b,e,f,c,d : t&t&t&t&t&t = x1.num, x1.den, x2.num, x2.den, y.num, y.den in
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  product_of_denominators_is_valid_denominator x1 y;
  product_of_denominators_is_valid_denominator x2 y;
  // Given fraction_eq x1 x2:  a*f = b*e.   Need: (a*d+b*c)*(f*d) = (b*d)*(e*d+f*c).
  // Step 1: (a*d)*(f*d) = (b*d)*(e*d)
  mul_middle_swap a d f d;                        // (a*d)*(f*d) = (a*f)*(d*d)
  mul_congruence (a*f) (d*d) (b*e) (d*d);          // (a*f)*(d*d) = (b*e)*(d*d)
  mul_middle_swap b e d d;                         // (b*e)*(d*d) = (b*d)*(e*d)
  transitivity ((a*d)*(f*d)) ((a*f)*(d*d)) ((b*e)*(d*d));
  transitivity ((a*d)*(f*d)) ((b*e)*(d*d)) ((b*d)*(e*d));
  assert ((a*d)*(f*d) = (b*d)*(e*d));
  // Step 2: (b*c)*(f*d) = (b*d)*(f*c)
  mul_middle_swap b c f d;                         // (b*c)*(f*d) = (b*f)*(c*d)
  mul_middle_swap b d f c;                         // (b*d)*(f*c) = (b*f)*(d*c)
  mul_commutativity c d;
  mul_congruence (b*f) (c*d) (b*f) (d*c);           // (b*f)*(c*d) = (b*f)*(d*c)
  symmetry ((b*d)*(f*c)) ((b*f)*(d*c));            // (b*f)*(d*c) = (b*d)*(f*c)
  transitivity ((b*c)*(f*d)) ((b*f)*(c*d)) ((b*f)*(d*c));
  transitivity ((b*c)*(f*d)) ((b*f)*(d*c)) ((b*d)*(f*c));
  assert ((b*c)*(f*d) = (b*d)*(f*c));
  // Combine via add_congruence
  add_congruence ((a*d)*(f*d)) ((b*c)*(f*d)) ((b*d)*(e*d)) ((b*d)*(f*c));
  assert ((a*d)*(f*d) + (b*c)*(f*d) = (b*d)*(e*d) + (b*d)*(f*c));
  // Wrap with distributivities
  right_distributivity (a*d) (b*c) (f*d);          // (a*d+b*c)*(f*d) = (a*d)*(f*d) + (b*c)*(f*d)
  left_distributivity  (b*d) (e*d) (f*c);          // (b*d)*(e*d+f*c) = (b*d)*(e*d) + (b*d)*(f*c)
  transitivity ((a*d+b*c)*(f*d)) ((a*d)*(f*d) + (b*c)*(f*d)) ((b*d)*(e*d) + (b*d)*(f*c));
  symmetry ((b*d)*(e*d+f*c)) ((b*d)*(e*d) + (b*d)*(f*c));
  transitivity ((a*d+b*c)*(f*d)) ((b*d)*(e*d) + (b*d)*(f*c)) ((b*d)*(e*d+f*c))

#pop-options

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

/// Right congruence follows from left + commutativity.
let fraction_add_right_congruence #t {| dom: integral_domain t |} (x y1 y2: fraction dom)
  : Lemma (requires fraction_eq y1 y2)
          (ensures  fraction_eq (fraction_add x y1) (fraction_add x y2)) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  // add x y1 = add y1 x = add y2 x = add x y2
  fraction_add_is_commutative x y1;
  fraction_add_left_congruence y1 y2 x;
  fraction_add_is_commutative y2 x;
  let eqf : equatable (fraction dom) = TC.solve in
  eqf.transitivity (fraction_add x y1) (fraction_add y1 x) (fraction_add y2 x);
  eqf.transitivity (fraction_add x y1) (fraction_add y2 x) (fraction_add x y2)

/// Full congruence: x1 = x2 /\ y1 = y2 ==> x1+y1 = x2+y2.
let fraction_add_congruence #t {| dom: integral_domain t |} (x1 y1 x2 y2: fraction dom)
  : Lemma (requires fraction_eq x1 x2 /\ fraction_eq y1 y2)
          (ensures  fraction_eq (fraction_add x1 y1) (fraction_add x2 y2)) =
  fraction_add_left_congruence  x1 x2 y1;        // x1+y1 = x2+y1
  fraction_add_right_congruence x2 y1 y2;        // x2+y1 = x2+y2
  let eqf : equatable (fraction dom) = TC.solve in
  eqf.transitivity (fraction_add x1 y1) (fraction_add x2 y1) (fraction_add x2 y2)

#pop-options

instance fraction_has_add t (d: integral_domain t) : has_add (fraction d) = {
  ( + ) = fraction_add;
  eq = fraction_equatable t d;
  congruence = fraction_add_congruence;
}

let fraction_zero #t {| d: integral_domain t |} : fraction d =
  // Need one <> zero. Provided by zero_ne_one_semiring (parent of domain).
  let one : t = one in
  let zero : t = zero in
  symmetry zero one;             // gets one <> zero from zero <> one
  (zero / one)

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

let fraction_add_left_identity #t {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_add fraction_zero x = x) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let zero : t = zero in
  let one  : t = one  in
  let a : t = x.num in
  let b : t = x.den in
  product_of_denominators_is_valid_denominator (fraction_zero #t #d) x;
  let lhs = fraction_add (fraction_zero #t #d) x in
  // lhs.num = zero*b + one*a   ;   lhs.den = one*b
  // want lhs = x, i.e. lhs.num * x.den = lhs.den * x.num
  // (zero*b + one*a) * b = (one*b) * a
  absorption zero b;                    // zero*b = zero (left absorber)
  left_mul_identity a;                  // one*a = a
  add_congruence (zero*b) (one*a) zero a;
  left_add_identity a;
  transitivity (zero*b + one*a) (zero + a) a;   // lhs.num = a
  left_mul_identity b;                  // one*b = b
  mul_congruence (zero*b + one*a) b a b;
  mul_congruence (one*b) a b a;
  mul_commutativity b a;
  transitivity ((one*b)*a) (b*a) (a*b);
  transitivity ((zero*b + one*a)*b) (a*b) ((one*b)*a)

let fraction_add_right_identity #t {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_add x fraction_zero = x) =
  fraction_add_is_commutative x (fraction_zero #t #d);
  fraction_add_left_identity x;
  let eqf : equatable (fraction d) = TC.solve in
  eqf.transitivity (fraction_add x fraction_zero) (fraction_add (fraction_zero #t #d) x) x

#pop-options

instance fraction_has_zero t (d: integral_domain t) : has_zero (fraction d) = {
  zero = fraction_zero;
  eq = fraction_equatable t d;
}

instance fraction_add_semigroup t (d: integral_domain t) : add_semigroup (fraction d) = {
  has_add = fraction_has_add t d;
  associativity = fraction_add_is_associative;
}

instance fraction_add_monoid t (d: integral_domain t) : add_monoid (fraction d) = {
  has_zero      = fraction_has_zero t d;
  add_semigroup = fraction_add_semigroup t d;
  left_add_identity  = fraction_add_left_identity;
  right_add_identity = fraction_add_right_identity;
}

instance fraction_add_comm_magma t (d: integral_domain t) : add_comm_magma (fraction d) = {
  has_add = fraction_has_add t d;
  add_commutativity = fraction_add_is_commutative;
}

instance fraction_add_comm_semigroup t (d: integral_domain t) : add_comm_semigroup (fraction d) = {
  add_semigroup  = fraction_add_semigroup t d;
  add_comm_magma = fraction_add_comm_magma t d;
}

instance fraction_add_comm_monoid t (d: integral_domain t) : add_comm_monoid (fraction d) = {
  add_monoid         = fraction_add_monoid t d;
  add_comm_semigroup = fraction_add_comm_semigroup t d;
}

let fraction_neg #t {| d: integral_domain t |} (x: fraction d) : fraction d =
  let a : t = x.num in
  let b : t = x.den in
  Fraction (-a) b

let fraction_sub #t {| d: integral_domain t |} (x y: fraction d) : fraction d =
  fraction_add x (fraction_neg y)

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

let fraction_negation #t {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_add x (fraction_neg x) = fraction_zero #t #d
        /\ fraction_add (fraction_neg x) x = fraction_zero #t #d) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let a : t = x.num in
  let b : t = x.den in
  let zero : t = zero in
  let one : t = one in
  product_of_denominators_is_valid_denominator x (fraction_neg x);
  product_of_denominators_is_valid_denominator (fraction_neg x) x;
  // (1) x + (-x) = 0/1
  // lhs.num = a*b + b*(-a); lhs.den = b*b. fraction_zero = 0/1.
  // need: (a*b + b*(-a)) * 1 = (b*b) * 0
  // RHS = 0 (absorption); LHS reduces to 0 via -.
  ring_neg_xy_is_x_times_neg_y b a;        // -(b*a) = b*(-a)
  symmetry (-(b*a)) (b*(-a));               // b*(-a) = -(b*a)
  mul_commutativity b a;                     // b*a = a*b
  equal_elements_have_equal_inverses (b*a) (a*b);  // -(b*a) = -(a*b)
  transitivity (b*(-a)) (-(b*a)) (-(a*b));
  add_congruence (a*b) (b*(-a)) (a*b) (-(a*b));
  negation (a*b);                            // a*b + -(a*b) = 0
  transitivity (a*b + b*(-a)) (a*b + -(a*b)) zero;
  // now (a*b + b*(-a)) = 0
  // RHS side: (b*b) * 0 = 0
  absorption zero (b*b);                     // 0*(b*b) = 0 /\ (b*b)*0 = 0
  // also need: lhs.num * fraction_zero.den = lhs.den * fraction_zero.num
  // lhs.num * 1 = (a*b + b*(-a)) * 1
  // lhs.den * 0 = (b*b) * 0 = 0
  right_mul_identity (a*b + b*(-a));         // (a*b+b*(-a)) * 1 = (a*b+b*(-a))
  transitivity ((a*b + b*(-a))*one) (a*b + b*(-a)) zero;
  symmetry ((b*b)*zero) zero;
  transitivity ((a*b + b*(-a))*one) zero ((b*b)*zero);
  // proves (lhs.num)*1 = (lhs.den)*0, i.e. fraction_eq lhs fraction_zero
  // (2) by commutativity
  fraction_add_is_commutative (fraction_neg x) x;
  let eqf : equatable (fraction d) = TC.solve in
  eqf.transitivity (fraction_add (fraction_neg x) x) (fraction_add x (fraction_neg x)) (fraction_zero #t #d)

let fraction_subtraction_definition #t {| d: integral_domain t |} (x y: fraction d)
  : Lemma (fraction_sub x y = fraction_add x (fraction_neg y)) =
  let eqf : equatable (fraction d) = TC.solve in
  eqf.reflexivity (fraction_add x (fraction_neg y))

#pop-options

instance fraction_has_neg t (d: integral_domain t) : has_neg (fraction d) = {
  op_Minus = fraction_neg;
}

instance fraction_has_sub t (d: integral_domain t) : has_sub (fraction d) = {
  op_Subtraction = fraction_sub;
}

instance fraction_add_group t (d: integral_domain t) : add_group (fraction d) = {
  add_monoid = fraction_add_monoid t d;
  has_neg    = fraction_has_neg t d;
  has_sub    = fraction_has_sub t d;
  subtraction_definition = fraction_subtraction_definition;
  negation = fraction_negation;
}

instance fraction_add_comm_group t (d: integral_domain t) : add_comm_group (fraction d) = {
  add_group       = fraction_add_group t d;
  add_comm_monoid = fraction_add_comm_monoid t d;
}

// ============================================================
// Phase B — Commutative ring on (fraction d)
// ============================================================

let fraction_mul #t {| d: integral_domain t |} (x y: fraction d) : fraction d =
  let a,b,c,e : t&t&t&t = x.num, x.den, y.num, y.den in
  product_of_denominators_is_valid_denominator x y;
  (a*c) / (b*e <: t)

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

/// Multiplication congruence.
let fraction_mul_congruence #t {| dom: integral_domain t |} (x1 y1 x2 y2: fraction dom)
  : Lemma (requires fraction_eq x1 x2 /\ fraction_eq y1 y2)
          (ensures  fraction_eq (fraction_mul x1 y1) (fraction_mul x2 y2)) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let a,b,e,f : t&t&t&t = x1.num, x1.den, x2.num, x2.den in
  let c,d,g,h : t&t&t&t = y1.num, y1.den, y2.num, y2.den in
  // given: a*f = b*e ;  c*h = d*g
  // need:  (a*c)*(f*h) = (b*d)*(e*g)
  mul_middle_swap a c f h;                  // (a*c)*(f*h) = (a*f)*(c*h)
  mul_congruence (a*f) (c*h) (b*e) (d*g);    // (a*f)*(c*h) = (b*e)*(d*g)
  mul_middle_swap b e d g;                   // (b*e)*(d*g) = (b*d)*(e*g)
  transitivity ((a*c)*(f*h)) ((a*f)*(c*h)) ((b*e)*(d*g));
  transitivity ((a*c)*(f*h)) ((b*e)*(d*g)) ((b*d)*(e*g))

let fraction_mul_is_associative #t {| dom: integral_domain t |} (x y z: fraction dom)
  : Lemma (fraction_mul (fraction_mul x y) z = fraction_mul x (fraction_mul y z)) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let a,b,c,d,e,f : t&t&t&t&t&t = x.num, x.den, y.num, y.den, z.num, z.den in
  // lhs.num = (a*c)*e ; lhs.den = (b*d)*f
  // rhs.num = a*(c*e) ; rhs.den = b*(d*f)
  mul_associativity a c e;
  mul_associativity b d f;
  fraction_eq_from_num_den (fraction_mul (fraction_mul x y) z) (fraction_mul x (fraction_mul y z))

let fraction_mul_is_commutative #t {| dom: integral_domain t |} (x y: fraction dom)
  : Lemma (fraction_mul x y = fraction_mul y x) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let a,b,c,d : t&t&t&t = x.num, x.den, y.num, y.den in
  mul_commutativity a c;     // a*c = c*a
  mul_commutativity b d;     // b*d = d*b
  fraction_eq_from_num_den (fraction_mul x y) (fraction_mul y x)

#pop-options

let fraction_one' #t {| d: integral_domain t |} : fraction d =
  let one : t = one in
  let zero : t = zero in
  symmetry zero one;
  (one / one)

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

let fraction_mul_left_identity #t {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_mul fraction_one' x = x) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let one : t = one in
  let a : t = x.num in
  let b : t = x.den in
  // (1*a) * b = (1*b) * a
  left_mul_identity a;             // 1*a = a
  left_mul_identity b;             // 1*b = b
  mul_commutativity a b;           // a*b = b*a
  mul_congruence (one*a) b a b;
  mul_congruence (one*b) a b a;
  transitivity ((one*a)*b) (a*b) (b*a);
  symmetry ((one*b)*a) (b*a);
  transitivity ((one*a)*b) (b*a) ((one*b)*a)

let fraction_mul_right_identity #t {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_mul x fraction_one' = x) =
  fraction_mul_is_commutative x (fraction_one' #t #d);
  fraction_mul_left_identity x;
  let eqf : equatable (fraction d) = TC.solve in
  eqf.transitivity (fraction_mul x fraction_one') (fraction_mul (fraction_one' #t #d) x) x

let fraction_mul_left_absorption #t {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_mul fraction_zero x = fraction_zero #t #d) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let zero : t = zero in
  let one : t = one in
  let a : t = x.num in
  let b : t = x.den in
  // lhs = (0*a)/(1*b) ; fraction_zero = 0/1
  // fraction_eq: (0*a)*1 = (1*b)*0
  // RHS = 0 (absorption); LHS reduces: 0*a = 0 (absorption), then 0*1 = 0 (absorption)
  absorption zero a;                   // 0*a = 0
  absorption zero one;                 // 0*1 = 0
  mul_congruence (zero*a) one zero one;
  transitivity ((zero*a)*one) (zero*one) zero;
  absorption zero (one*b);             // 0*(1*b) = 0 = (1*b)*0
  symmetry ((one*b)*zero) zero;
  transitivity ((zero*a)*one) zero ((one*b)*zero)

let fraction_mul_right_absorption #t {| d: integral_domain t |} (x: fraction d)
  : Lemma (fraction_mul x fraction_zero = fraction_zero #t #d) =
  fraction_mul_is_commutative x (fraction_zero #t #d);
  fraction_mul_left_absorption x;
  let eqf : equatable (fraction d) = TC.solve in
  eqf.transitivity (fraction_mul x fraction_zero) (fraction_mul (fraction_zero #t #d) x) (fraction_zero #t #d)

#pop-options

/// Helper: a*x = b*y when both reduce to the same products. Generic 4-leaf swap-and-rearrange.
let mul_4_rearrange #t {| d: integral_domain t |} (a b c e f g: t)
  : Lemma ((a*b)*(c*(e*f)) = (a*c)*((b*e)*f) /\
           (a*b)*(c*(e*f)) = a*((b*c)*(e*f)) /\
           (a*b)*(c*(e*f)) = c*((a*b)*(e*f)))
  =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  // (a*b)*(c*(e*f)) = (a*c)*(b*(e*f)) [mul_middle_swap a b c (e*f)]
  // (a*c)*(b*(e*f)) = (a*c)*((b*e)*f) [assoc inside]
  mul_middle_swap a b c (e*f);
  mul_associativity b e f;
  mul_congruence (a*c) (b*(e*f)) (a*c) ((b*e)*f);
  transitivity ((a*b)*(c*(e*f))) ((a*c)*(b*(e*f))) ((a*c)*((b*e)*f));
  // (a*b)*(c*(e*f)) = a*((b*c)*(e*f)): use assoc twice
  mul_associativity a b (c*(e*f));            // (a*b)*(c*(e*f)) = a*(b*(c*(e*f)))
  mul_associativity b c (e*f);                 // b*(c*(e*f)) = (b*c)*(e*f)
  mul_congruence a (b*(c*(e*f))) a ((b*c)*(e*f));
  transitivity ((a*b)*(c*(e*f))) (a*(b*(c*(e*f)))) (a*((b*c)*(e*f)));
  // (a*b)*(c*(e*f)) = c*((a*b)*(e*f)): swap a*b with c
  mul_middle_swap a b c (e*f);                  // (a*b)*(c*(e*f)) = (a*c)*(b*(e*f))
  mul_commutativity (a*b) c;                    // (a*b)*c = c*(a*b)
  // also need to reassemble: (a*b)*(c*(e*f)) -- use mul_associativity:
  // (a*b)*(c*(e*f)) = ((a*b)*c)*(e*f) = (c*(a*b))*(e*f) = c*((a*b)*(e*f))
  mul_associativity (a*b) c (e*f);             // (a*b)*(c*(e*f)) = ((a*b)*c)*(e*f)
  mul_congruence ((a*b)*c) (e*f) (c*(a*b)) (e*f);
  mul_associativity c (a*b) (e*f);             // (c*(a*b))*(e*f) = c*((a*b)*(e*f))
  transitivity ((a*b)*c*(e*f)) (((a*b)*c)*(e*f)) ((c*(a*b))*(e*f));
  transitivity ((a*b)*(c*(e*f))) (((a*b)*c)*(e*f)) ((c*(a*b))*(e*f));
  transitivity ((a*b)*(c*(e*f))) ((c*(a*b))*(e*f)) (c*((a*b)*(e*f)))

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

/// Left distributivity for fractions.  x * (y + z) = x*y + x*z.
let fraction_left_distributivity #t {| dom: integral_domain t |} (x y z: fraction dom)
  : Lemma (fraction_mul x (fraction_add y z) = fraction_add (fraction_mul x y) (fraction_mul x z)) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let a,b,c,d,e,f : t&t&t&t&t&t = x.num, x.den, y.num, y.den, z.num, z.den in
  // k_ = c*f + d*e
  let k_ : t = c*f + d*e in
  // LHS = (a*k_)/(b*(d*f))
  // RHS-num = (a*c)*(b*f) + (b*d)*(a*e)
  // RHS-den = (b*d)*(b*f)
  // Need cross-mul: (a*k_) * ((b*d)*(b*f)) = (b*(d*f)) * ((a*c)*(b*f) + (b*d)*(a*e))
  // Step A: show (a*c)*(b*f) = (a*b)*(c*f)
  mul_middle_swap a c b f;
  // Step B: show (b*d)*(a*e) = (a*b)*(d*e)
  mul_middle_swap b d a e;          // (b*d)*(a*e) = (b*a)*(d*e)
  mul_commutativity b a;             // b*a = a*b
  mul_congruence (b*a) (d*e) (a*b) (d*e);
  transitivity ((b*d)*(a*e)) ((b*a)*(d*e)) ((a*b)*(d*e));
  // So RHS-num = (a*b)*(c*f) + (a*b)*(d*e)
  add_congruence ((a*c)*(b*f)) ((b*d)*(a*e)) ((a*b)*(c*f)) ((a*b)*(d*e));
  // Now ((a*b)*(c*f) + (a*b)*(d*e)) = (a*b)*(c*f+d*e) = (a*b)*k_
  left_distributivity (a*b) (c*f) (d*e);
  symmetry ((a*b)*k_) ((a*b)*(c*f) + (a*b)*(d*e));
  transitivity ((a*c)*(b*f) + (b*d)*(a*e)) ((a*b)*(c*f) + (a*b)*(d*e)) ((a*b)*k_);
  // RHS = (b*(d*f)) * ((a*b)*k_)  [now apply congruence]
  mul_congruence (b*(d*f)) ((a*c)*(b*f) + (b*d)*(a*e)) (b*(d*f)) ((a*b)*k_);
  // Now we have RHS' = (b*(d*f)) * ((a*b)*k_). 
  // Step C: show LHS = (a*k_) * ((b*d)*(b*f)) equals RHS' = (b*(d*f)) * ((a*b)*k_).
  // First rearrange (b*d)*(b*f) = b*(b*(d*f)) so LHS = (a*k_)*(b*(b*(d*f))).
  mul_middle_swap b d b f;                     // (b*d)*(b*f) = (b*b)*(d*f)
  mul_associativity b b (d*f);                 // (b*b)*(d*f) = b*(b*(d*f))
  transitivity ((b*d)*(b*f)) ((b*b)*(d*f)) (b*(b*(d*f)));
  mul_congruence (a*k_) ((b*d)*(b*f)) (a*k_) (b*(b*(d*f)));
  // LHS = (a*k_)*(b*(b*(d*f)))
  // Use mul_middle_swap a k_ b (b*(d*f)) to get  (a*k_)*(b*(b*(d*f))) = (a*b)*(k_*(b*(d*f)))
  mul_middle_swap a k_ b (b*(d*f));
  // (a*b)*(k_*(b*(d*f))) = (a*b)*((b*(d*f))*k_) by commutativity inside
  mul_commutativity k_ (b*(d*f));
  mul_congruence (a*b) (k_*(b*(d*f))) (a*b) ((b*(d*f))*k_);
  transitivity ((a*k_)*(b*(b*(d*f)))) ((a*b)*(k_*(b*(d*f)))) ((a*b)*((b*(d*f))*k_));
  // (a*b)*((b*(d*f))*k_) = (b*(d*f))*((a*b)*k_)  by mul_middle_swap a b (b*(d*f)) k_ + comm
  // Actually: (a*b)*(R*k_) where R = b*(d*f). Want = R*((a*b)*k_).
  // mul_associativity a b (R*k_): (a*b)*(R*k_) = a*(b*(R*k_))   -- not helpful directly
  // Use: (a*b)*(R*k_) = (R*k_)*(a*b) by comm; then = R*(k_*(a*b)) by assoc; then = R*((a*b)*k_) by comm inside
  mul_commutativity (a*b) ((b*(d*f))*k_);
  mul_associativity (b*(d*f)) k_ (a*b);
  mul_commutativity k_ (a*b);
  mul_congruence (b*(d*f)) (k_*(a*b)) (b*(d*f)) ((a*b)*k_);
  transitivity (((b*(d*f))*k_)*(a*b)) ((b*(d*f))*(k_*(a*b))) ((b*(d*f))*((a*b)*k_));
  transitivity ((a*b)*((b*(d*f))*k_)) (((b*(d*f))*k_)*(a*b)) ((b*(d*f))*((a*b)*k_));
  // Chain LHS to (b*(d*f))*((a*b)*k_)
  transitivity ((a*k_)*((b*d)*(b*f))) ((a*k_)*(b*(b*(d*f)))) ((a*b)*(k_*(b*(d*f))));
  transitivity ((a*k_)*((b*d)*(b*f))) ((a*b)*(k_*(b*(d*f)))) ((a*b)*((b*(d*f))*k_));
  transitivity ((a*k_)*((b*d)*(b*f))) ((a*b)*((b*(d*f))*k_)) ((b*(d*f))*((a*b)*k_));
  // Now combine: LHS = (b*(d*f))*((a*b)*k_) and (b*(d*f))*((a*c)*(b*f)+(b*d)*(a*e)) = (b*(d*f))*((a*b)*k_)
  symmetry ((b*(d*f))*((a*c)*(b*f) + (b*d)*(a*e))) ((b*(d*f))*((a*b)*k_));
  transitivity ((a*k_)*((b*d)*(b*f))) ((b*(d*f))*((a*b)*k_)) ((b*(d*f))*((a*c)*(b*f) + (b*d)*(a*e)))

#pop-options

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

/// Right distributivity follows from left + commutativity.
let fraction_right_distributivity #t {| dom: integral_domain t |} (x y z: fraction dom)
  : Lemma (fraction_mul (fraction_add x y) z = fraction_add (fraction_mul x z) (fraction_mul y z)) =
  let eqf : equatable (fraction dom) = TC.solve in
  Classical.forall_intro eqf.reflexivity;
  Classical.forall_intro_2 eqf.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eqf.transitivity);
  // (x+y)*z = z*(x+y) = z*x + z*y = x*z + y*z
  fraction_mul_is_commutative (fraction_add x y) z;
  fraction_left_distributivity z x y;
  fraction_mul_is_commutative z x;
  fraction_mul_is_commutative z y;
  fraction_add_congruence (fraction_mul z x) (fraction_mul z y)
                          (fraction_mul x z) (fraction_mul y z);
  eqf.transitivity (fraction_mul (fraction_add x y) z)
                   (fraction_mul z (fraction_add x y))
                   (fraction_add (fraction_mul z x) (fraction_mul z y));
  eqf.transitivity (fraction_mul (fraction_add x y) z)
                   (fraction_add (fraction_mul z x) (fraction_mul z y))
                   (fraction_add (fraction_mul x z) (fraction_mul y z))

let fraction_zero_ne_one #t {| dom: integral_domain t |}
  : Lemma (fraction_zero #t #dom <> fraction_one' #t #dom) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  let zero : t = zero in
  let one : t = one in
  // fraction_zero = 0/1, fraction_one' = 1/1
  // fraction_eq: 0*1 = 1*1 ?  0*1 = 0 (absorption), 1*1 = 1 (left_mul_identity)
  // So zero <> one means fraction_zero <> fraction_one'.
  absorption zero one;             // 0*1 = 0
  left_mul_identity one;            // 1*1 = 1
  // Suppose fraction_zero = fraction_one'. Then 0*1 = 1*1, so 0 = 1, contradiction.
  let aux () : Lemma (requires fraction_zero #t #dom = fraction_one' #t #dom) (ensures False) =
    eq.symmetry (zero*one) zero;
    eq.transitivity zero (zero*one) (one*one);
    eq.transitivity zero (one*one) one
  in
  Classical.move_requires aux ()

let fraction_domain_law #t {| dom: integral_domain t |} (x y: fraction dom)
  : Lemma (requires fraction_mul x y = fraction_zero #t #dom)
          (ensures  (x = fraction_zero #t #dom) \/ (y = fraction_zero #t #dom)) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let zero : t = zero in
  let one : t = one in
  let a : t = x.num in
  let b : t = x.den in
  let c : t = y.num in
  let e : t = y.den in
  // fraction_mul x y = (a*c)/(b*e), fraction_zero = 0/1
  // fraction_eq: (a*c) * 1 = (b*e) * 0
  // RHS = 0; right_mul_identity gives (a*c)*1 = a*c.
  // So a*c = 0, hence (by domain_law) a=0 or c=0.
  right_mul_identity (a*c);                  // (a*c)*1 = a*c
  absorption zero (b*e);                     // 0*(b*e) = 0 /\ (b*e)*0 = 0
  // a*c = (a*c)*1 = (b*e)*0 = 0
  eq.transitivity (a*c) ((a*c)*one) ((b*e)*zero);
  eq.transitivity (a*c) ((b*e)*zero) zero;
  assert (a*c = zero);
  domain_law a c;                            // a=0 or c=0
  // If a=0: prove x = fraction_zero. fraction_eq: a*1 = b*0. a=0 ==> a*1 = 0 = b*0.
  // If c=0: prove y = fraction_zero. analogous.
  let if_a_zero () : Lemma (requires a = zero) (ensures x = fraction_zero #t #dom) =
    right_mul_identity a;                     // a*1 = a
    eq.transitivity (a*one) a zero;            // a*1 = 0
    absorption zero b;                         // b*0 = 0
    eq.symmetry (b*zero) zero;
    eq.transitivity (a*one) zero (b*zero)
  in
  let if_c_zero () : Lemma (requires c = zero) (ensures y = fraction_zero #t #dom) =
    right_mul_identity c;
    eq.transitivity (c*one) c zero;
    absorption zero e;
    eq.symmetry (e*zero) zero;
    eq.transitivity (c*one) zero (e*zero)
  in
  Classical.move_requires if_a_zero ();
  Classical.move_requires if_c_zero ()

#pop-options

// ============================================================
// Phase B instance assembly
// ============================================================

instance fraction_has_mul t (d: integral_domain t) : has_mul (fraction d) = {
  ( * ) = fraction_mul;
  eq = fraction_equatable t d;
  congruence = fraction_mul_congruence;
}

instance fraction_has_one t (d: integral_domain t) : has_one (fraction d) = {
  one = fraction_one';
  eq = fraction_equatable t d;
}

instance fraction_mul_semigroup t (d: integral_domain t) : mul_semigroup (fraction d) = {
  has_mul = fraction_has_mul t d;
  associativity = fraction_mul_is_associative;
}

instance fraction_mul_comm_magma t (d: integral_domain t) : mul_comm_magma (fraction d) = {
  has_mul = fraction_has_mul t d;
  mul_commutativity = fraction_mul_is_commutative;
}

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

/// Direction (=>): if `dvd_bool x y` says yes, exhibit a witness c with y = c*x.
let fraction_dvd_witness #t {| dom: integral_domain t |} (x y: fraction dom)
  : Pure (fraction dom)
         (requires (x.num = (zero <: t) ==> y.num = (zero <: t)))
         (ensures fun c -> fraction_mul c x `fraction_eq` y) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let zero : t = zero in
  let a : t = x.num in
  let b : t = x.den in
  let p : t = y.num in
  let q : t = y.den in
  if a = zero then begin
    // c = fraction_zero. c*x = (0*a)/(1*b). y has y.num = 0.
    let c = fraction_zero #t #dom in
    let one : t = one in
    // Need: fraction_mul c x `fraction_eq` y
    // (0*a)*q = (1*b)*p
    // LHS: 0*a = 0 (absorption), so (0*a)*q = 0*q = 0
    // RHS: p = 0, so (1*b)*p = (1*b)*0 = 0
    absorption zero a;             // 0*a = 0
    absorption zero q;             // 0*q = 0
    mul_congruence (zero*a) q zero q;
    eq.transitivity ((zero*a)*q) (zero*q) zero;
    absorption zero (one*b);        // (1*b)*0 = 0
    eq.symmetry ((one*b)*zero) zero;
    eq.transitivity ((zero*a)*q) zero ((one*b)*zero);
    // Now need ((1*b)*0) = ((1*b)*p) — use p = 0
    mul_congruence (one*b) zero (one*b) p;
    eq.transitivity ((zero*a)*q) ((one*b)*zero) ((one*b)*p);
    c
  end else begin
    // x.num <> 0. c = (p*b) / (q*a).
    // Need q*a <> 0: q <> 0, a <> 0, integral domain.
    Classical.move_requires_2 dom.domain.domain_law q a;
    let c : fraction dom = (p*b) / (q*a <: t) in
    // c*x = ((p*b)*a) / ((q*a)*b).  fraction_eq with y means:
    //   ((p*b)*a) * q = ((q*a)*b) * p
    // Both sides should equal a*b*p*q by commutativity.
    // LHS = (p*b)*a*q   — use mul_middle_swap p b a q first?
    // Plan: ((p*b)*a)*q = p*(b*a)*q = p*(a*b)*q = a*b*p*q  -- but easier:
    // mul_middle_swap (p*b) a q' ... ok let me just compute.
    // LHS = ((p*b)*a) * q
    //     = (p*b)*(a*q)   by mul_associativity
    //     = (p*a)*(b*q)   by mul_middle_swap p b a q
    // RHS = ((q*a)*b) * p
    //     = (q*a)*(b*p)   by mul_associativity
    //     = (q*b)*(a*p)   by mul_middle_swap q a b p
    //     = (a*p)*(q*b)   by mul_commutativity? no, by ... hmm
    // Aim: a clean equality.
    // Both sides = a*p*b*q in some order.
    mul_associativity (p*b) a q;       // ((p*b)*a)*q = (p*b)*(a*q)
    mul_middle_swap p b a q;            // (p*b)*(a*q) = (p*a)*(b*q)
    eq.transitivity (((p*b)*a)*q) ((p*b)*(a*q)) ((p*a)*(b*q));
    mul_associativity (q*a) b p;        // ((q*a)*b)*p = (q*a)*(b*p)
    mul_middle_swap q a b p;             // (q*a)*(b*p) = (q*b)*(a*p)
    eq.transitivity (((q*a)*b)*p) ((q*a)*(b*p)) ((q*b)*(a*p));
    // Need (p*a)*(b*q) = (q*b)*(a*p). Both = pabq in some perm.
    mul_commutativity p a;               // p*a = a*p
    mul_commutativity b q;               // b*q = q*b
    mul_congruence (p*a) (b*q) (a*p) (q*b);  // (p*a)*(b*q) = (a*p)*(q*b)
    mul_commutativity (a*p) (q*b);       // (a*p)*(q*b) = (q*b)*(a*p)
    eq.transitivity ((p*a)*(b*q)) ((a*p)*(q*b)) ((q*b)*(a*p));
    eq.transitivity (((p*b)*a)*q) ((p*a)*(b*q)) ((q*b)*(a*p));
    eq.symmetry (((q*a)*b)*p) ((q*b)*(a*p));
    eq.transitivity (((p*b)*a)*q) ((q*b)*(a*p)) (((q*a)*b)*p);
    c
  end

#pop-options

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

/// Direction (<=): if y = c*x for some c, then `x.num = 0 ==> y.num = 0`.
let fraction_dvd_implies_bool #t {| dom: integral_domain t |} (x y: fraction dom) (c: fraction dom)
  : Lemma (requires fraction_mul c x `fraction_eq` y)
          (ensures  x.num = (zero <: t) ==> y.num = (zero <: t)) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let zero : t = zero in
  let a : t = x.num in
  let b : t = x.den in
  let p : t = y.num in
  let q : t = y.den in
  let r : t = c.num in
  let s : t = c.den in
  // fraction_mul c x = (r*a)/(s*b). fraction_eq with y: (r*a)*q = (s*b)*p.
  // Suppose a = 0. Then r*a = 0 (absorption), so (r*a)*q = 0*q = 0.
  // Hence (s*b)*p = 0. s,b nonzero, integral domain ==> p = 0.
  let aux () : Lemma (requires a = zero) (ensures p = zero) =
    absorption zero a;              // 0*a = 0 ; so a*x = 0*x but here r*a = r*0 = ?
    mul_congruence r a r zero;       // r*a = r*0
    absorption zero r;               // r*0 = 0
    eq.transitivity (r*a) (r*zero) zero;
    mul_congruence (r*a) q zero q;
    absorption zero q;
    eq.transitivity ((r*a)*q) (zero*q) zero;
    // (s*b)*p = (r*a)*q = 0
    eq.symmetry ((r*a)*q) ((s*b)*p);
    eq.transitivity ((s*b)*p) ((r*a)*q) zero;
    // s*b <> 0 since s<>0 and b<>0
    Classical.move_requires_2 dom.domain.domain_law s b;
    assert (s*b <> zero);
    // From (s*b)*p = 0 and s*b <> 0, conclude p = 0
    absorption zero (s*b);            // (s*b)*0 = 0
    eq.symmetry ((s*b)*zero) zero;
    eq.transitivity ((s*b)*p) zero ((s*b)*zero);
    left_cancellation (s*b) p zero
  in
  Classical.move_requires aux ()

#pop-options

/// Now the bool function with refinement matching `mul_comm_semigroup`'s `dvd`.
let fraction_dvd #t (dom: integral_domain t) (x y: fraction dom)
  : (b:bool { b <==> (exists (c: fraction dom). y `fraction_eq` (c `fraction_mul` x)) }) =
  let eq : equatable t = TC.solve in
  let zero : t = zero in
  let p : bool = if x.num = zero then y.num = zero else true in
  // Prove forward direction: p ==> ∃c. y = c*x
  let forward () : Lemma (requires p) (ensures exists (c: fraction dom). y `fraction_eq` (c `fraction_mul` x)) =
    let eqf : equatable (fraction dom) = TC.solve in
    let c = fraction_dvd_witness x y in
    eqf.symmetry (fraction_mul c x) y;
    assert (y `fraction_eq` (c `fraction_mul` x))
  in
  // Reverse: ∃c. y = c*x ==> p
  let reverse () : Lemma (requires (exists (c: fraction dom). y `fraction_eq` (c `fraction_mul` x))) (ensures p) =
    eliminate exists (c: fraction dom). y `fraction_eq` (c `fraction_mul` x)
    returns p with _.
    begin
      let eqf : equatable (fraction dom) = TC.solve in
      eqf.symmetry y (c `fraction_mul` x);
      fraction_dvd_implies_bool x y c
    end
  in
  Classical.move_requires forward ();
  Classical.move_requires reverse ();
  p

instance fraction_mul_comm_semigroup t (d: integral_domain t) : mul_comm_semigroup (fraction d) = {
  mul_semigroup  = fraction_mul_semigroup t d;
  mul_comm_magma = fraction_mul_comm_magma t d;
  dvd            = fraction_dvd d;
}

instance fraction_mul_monoid t (d: integral_domain t) : mul_monoid (fraction d) = {
  has_one        = fraction_has_one t d;
  mul_semigroup  = fraction_mul_semigroup t d;
  left_mul_identity  = fraction_mul_left_identity;
  right_mul_identity = fraction_mul_right_identity;
}

instance fraction_mul_comm_monoid t (d: integral_domain t) : mul_comm_monoid (fraction d) = {
  mul_monoid         = fraction_mul_monoid t d;
  mul_comm_semigroup = fraction_mul_comm_semigroup t d;
}

instance fraction_semiring t (d: integral_domain t) : semiring (fraction d) = {
  add_comm_monoid      = fraction_add_comm_monoid t d;
  mul_monoid           = fraction_mul_monoid t d;
  left_absorption      = fraction_mul_left_absorption;
  right_absorption     = fraction_mul_right_absorption;
  left_distributivity  = fraction_left_distributivity;
  right_distributivity = fraction_right_distributivity;
}

instance fraction_ring t (d: integral_domain t) : ring (fraction d) = {
  semiring       = fraction_semiring t d;
  add_comm_group = fraction_add_comm_group t d;
}

instance fraction_zero_ne_one_semiring t (d: integral_domain t) : zero_ne_one_semiring (fraction d) = {
  semiring = (fraction_zero_ne_one #t #d; fraction_semiring t d);
}

instance fraction_domain t (d: integral_domain t) : domain (fraction d) = {
  ring                 = fraction_ring t d;
  zero_ne_one_semiring = fraction_zero_ne_one_semiring t d;
  domain_law           = fraction_domain_law;
}

instance fraction_commutative_ring t (d: integral_domain t) : commutative_ring (fraction d) = {
  ring            = fraction_ring t d;
  mul_comm_monoid = fraction_mul_comm_monoid t d;
}

instance fraction_integral_domain t (d: integral_domain t) : integral_domain (fraction d) = {
  commutative_ring = fraction_commutative_ring t d;
  domain           = fraction_domain t d;
}

// ============================================================
// Phase C: field on (fraction d)
// ============================================================

#push-options "--z3rlimit 5 --fuel 1 --ifuel 1"

/// `x = fraction_zero` iff its numerator is zero in t.
let fraction_eq_zero_iff_num_zero #t {| dom: integral_domain t |} (x: fraction dom)
  : Lemma (fraction_eq x (fraction_zero #t #dom) <==> (x.num = (zero <: t))) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  Classical.forall_intro_3 (Classical.move_requires_3 eq.transitivity);
  let zero : t = zero in
  let one : t = one in
  let a : t = x.num in
  let b : t = x.den in
  // fraction_eq x fraction_zero = (a * 1 = b * 0)
  right_mul_identity a;        // a*1 = a
  absorption zero b;            // b*0 = 0 /\ 0*b = 0
  // a*1 = b*0  <==>  a = 0
  let fwd () : Lemma (requires fraction_eq x (fraction_zero #t #dom)) (ensures a = zero) =
    // a*1 = b*0, a*1 = a, b*0 = 0, so a = 0
    eq.symmetry (a*one) a;
    eq.transitivity a (a*one) (b*zero);
    eq.transitivity a (b*zero) zero
  in
  let bwd () : Lemma (requires a = zero) (ensures fraction_eq x (fraction_zero #t #dom)) =
    // want a*1 = b*0. a*1 = a = 0 = b*0.
    eq.transitivity (a*one) a zero;
    eq.symmetry (b*zero) zero;
    eq.transitivity (a*one) zero (b*zero)
  in
  Classical.move_requires fwd ();
  Classical.move_requires bwd ()

/// Inversion: swap num and den. Requires `x` not equivalent to `fraction_zero`.
let fraction_inv #t {| dom: integral_domain t |} (x: fraction dom{ x <> fraction_zero #t #dom })
  : fraction dom =
  fraction_eq_zero_iff_num_zero x;
  // Now we know x.num <> zero
  let a : t = x.num in
  let b : t = x.den in
  // a <> zero, so it's a valid denominator
  Fraction b a

/// inv x * x = one (= fraction_one').
let fraction_inv_left #t {| dom: integral_domain t |} (x: fraction dom{ x <> fraction_zero #t #dom })
  : Lemma (fraction_mul (fraction_inv x) x = fraction_one' #t #dom) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  let a : t = x.num in
  let b : t = x.den in
  // inv x = b/a; x = a/b. Product = (b*a)/(a*b). fraction_one' = 1/1.
  // fraction_eq: (b*a) * 1 = (a*b) * 1  <==>  by right_mul_identity twice, b*a = a*b, which is mul_commutativity.
  right_mul_identity (b*a);
  right_mul_identity (a*b);
  mul_commutativity b a;
  eq.transitivity ((b*a)*one) (b*a) (a*b);
  eq.symmetry ((a*b)*one) (a*b);
  eq.transitivity ((b*a)*one) (a*b) ((a*b)*one)

/// x * inv x = one.
let fraction_inv_right #t {| dom: integral_domain t |} (x: fraction dom{ x <> fraction_zero #t #dom })
  : Lemma (fraction_mul x (fraction_inv x) = fraction_one' #t #dom) =
  let eq : equatable t = TC.solve in
  Classical.forall_intro eq.reflexivity;
  Classical.forall_intro_2 eq.symmetry;
  let a : t = x.num in
  let b : t = x.den in
  // x * inv x = (a*b)/(b*a). fraction_one' = 1/1.
  right_mul_identity (a*b);
  right_mul_identity (b*a);
  mul_commutativity a b;
  eq.transitivity ((a*b)*one) (a*b) (b*a);
  eq.symmetry ((b*a)*one) (b*a);
  eq.transitivity ((a*b)*one) (b*a) ((b*a)*one)

/// Packaged inv with the postcondition required by `division_ring.inv`.
let fraction_inv_spec #t {| dom: integral_domain t |}
  (x: fraction dom{ x <> fraction_zero #t #dom })
  : (x': fraction dom { (fraction_mul x' x = fraction_one' #t #dom)
                      /\ (fraction_mul x x' = fraction_one' #t #dom) }) =
  fraction_inv_left x;
  fraction_inv_right x;
  fraction_inv x

#pop-options

instance fraction_division_ring t (d: integral_domain t) : division_ring (fraction d) = {
  domain = fraction_domain t d;
  inv    = fraction_inv_spec;
}

instance fraction_field t (d: integral_domain t) : field (fraction d) = {
  division_ring    = fraction_division_ring t d;
  commutative_ring = fraction_commutative_ring t d;
}
