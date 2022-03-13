module Fractions.Definition

open AlgebraTypes

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"

let is_valid_denominator_of (#a:Type) (d: integral_domain a) (x: a) = 
  is_unit_normal d.multiplication.op d.unit_part_of x /\ ~(is_zero_of d x)

type valid_denominator_of (#a:Type) (d: integral_domain a) = (t: a{is_valid_denominator_of d t})

let one_is_valid_denominator (#a:Type) (d: integral_domain a) : Lemma (is_valid_denominator_of d d.multiplication.neutral) = 
  reveal_opaque (`%is_neutral_invariant) (is_neutral_invariant #a #d.eq);   
  neutral_equivalent_is_neutral d.multiplication.op d.multiplication.neutral (d.unit_part_of d.multiplication.neutral); 
  absorber_nonequal_is_nonabsorber d.multiplication.op d.addition.neutral d.multiplication.neutral 
 
let normal_part_of_non_absorber_is_valid_denominator (#a:Type) (#d: integral_domain a) 
                                                     (x: non_absorber_of d.multiplication.op) 
  : Lemma (is_valid_denominator_of d (d.normal_part_of x)) = normal_part_of_nonabsorber_is_nonabsorber x
  
/// We construct fractions in such a way that denominators are always unit normal.
/// To better understand the notion of x=u(x)n(x), see Algorithms for Computer Algebra,
/// by Geddes, Czapor & Labahn, somewhere around paragraph 2.3 Divisibility and
/// factorization in integral domains
let denominator_is_unit_normal (#a: Type) (#d: integral_domain a) (x: valid_denominator_of d)
  : Lemma (is_unit_normal d.multiplication.op d.unit_part_of x) = ()

/// Fraction denominators are nonzero by definition
/// Zero is always the absorber of domain's multiplication
/// Or, equivalently, the domain addition's neutral element
let denominator_is_nonzero (#a:Type) (d: integral_domain a) (x:a{is_valid_denominator_of d x})
  : Lemma (~(is_absorber_of x d.multiplication.op)) = ()

/// We construct the fractions without much sophistication
type fraction (#a:Type) (d: integral_domain a) = 
 | Fraction : (num: a) -> (den: valid_denominator_of d) -> fraction d

/// This one is still actually used in several places.
/// Basically it's a shorthand to the AlgebraTypes library lemma.
/// Note how this one is proved automatically, but proving the post-condition
/// where the callers called this is a pain.
let product_of_denominators_is_denominator (#a:Type) (#d: integral_domain a) (x y: fraction d)
  : Lemma (is_valid_denominator_of d (d.multiplication.op x.den y.den)) = 
  reveal_opaque (`%has_no_absorber_divisors) (has_no_absorber_divisors #a #d.eq);   
  product_of_unit_normals_is_normal d.unit_part_of x.den y.den

#pop-options
