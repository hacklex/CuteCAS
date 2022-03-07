module Polynomials.Definition
 
open AlgebraTypes
  
open FStar.Seq
open FStar.Seq.Base
open FStar.Seq.Properties

/// This module contains the basic definitions for polynomials over general commutative rings

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"

/// Boolean checks whether a seq is empty (we base polynomials on seqs)
let is_empty #c (l: seq c) : bool = length l = 0
let is_nonempty #c (l: seq c) : bool = length l > 0

/// Polynomial type alias
/// Noncompact stays for "allow trailing zeros", i.e. 0x^2+2x+3 is a noncompact poly
/// that is equivalent to 2x+3.
type noncompact_poly_over_ring #c (r: ring #c) = seq c

/// A boolean check that a ring element is equal to ring zero
let is_zero #a (r: commutative_ring #a) (x:a) : bool = r.eq r.addition.neutral x

/// Basic operations for seq construction
let cons #c (#r: commutative_ring #c) (head: c) (tail: noncompact_poly_over_ring r) : noncompact_poly_over_ring r = cons head tail
let snoc #c (#r: commutative_ring #c) (liat: noncompact_poly_over_ring r) (last: c) : noncompact_poly_over_ring r = snoc liat last

/// Shortcuts to cons, snoc and append
let (+$) #c (#r: commutative_ring #c) (h: c) (t: noncompact_poly_over_ring r) 
  : (z: noncompact_poly_over_ring r{ length z > 0 /\ tail z == t /\ head z == h }) = lemma_eq_elim t (tail (cons h t)); cons h t
let ($+) #c (#r: commutative_ring #c) (liat: noncompact_poly_over_ring r) (last: c) 
  : (z: noncompact_poly_over_ring r { length z > 0 /\ slice z 0 (length z - 1) == liat /\ Seq.Properties.last z == last }) 
  = lemma_eq_elim liat (slice (snoc liat last) 0 ((length (snoc liat last)) - 1)); snoc liat last
let ($$) #c (#r: commutative_ring #c) (p q: noncompact_poly_over_ring r) : (z:noncompact_poly_over_ring r{ z == append p q }) = append p q

/// Tail that also returns empty seq when given an empty seq 
let tail #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) 
  : (z:noncompact_poly_over_ring r{
      ((is_empty p) <==> (p == z)) /\ 
      ((is_nonempty p) ==> (p == (head p +$ z)))
    })
  = if is_nonempty p then tail p else p

/// (liat x) is exactly (reverse (tail (reverse x))).
/// You'll be surprised with how fast you grow addicted to the name.
#push-options "--ifuel 1 --fuel 1 --z3rlimit 10"
let liat #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) 
  : (z:noncompact_poly_over_ring r{
      ((is_empty p) <==> (p == z)) /\ 
      ((is_nonempty p) ==> (p == (z $+ last p)))
    })
  = if length p < 1 then (lemma_eq_elim p empty; empty) else slice p 0 (length p - 1)
#pop-options

/// Additional refinements added to make some proofs simpler
let head #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r{is_nonempty p}) : (z:c {p == z +$ tail p}) = head p
/// for compact polys, we'd want to call last coefficient leading, but with noncompact polys,
/// such a name would be rather misleading...
let last #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r{is_nonempty p}) : (z:c {p == liat p $+ z}) = last p

let starts_with #c (#r: commutative_ring #c) 
                (poly: noncompact_poly_over_ring r) 
                (subpoly: noncompact_poly_over_ring r{length subpoly<=length poly}) 
  = slice poly 0 (length subpoly) == subpoly

let nth #c (#r: commutative_ring #c) (p: noncompact_poly_over_ring r) (n: nat) 
  : (t:c{((n>=length p) ==> (t==r.addition.neutral)) /\ ((n<length p) ==> (t==index p n))}) = 
  if n >= length p then r.addition.neutral else index p n

let max (x y: nat) : (t:nat{ t >= x /\ t >= y /\ (if x>y then t=x else t=y) }) = if x>y then x else y
