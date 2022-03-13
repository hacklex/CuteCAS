module RefinementEquality

module P = FStar.PropositionalExtensionality
open FStar.Tactics

/// An example by Nikhil Swamy, showing how one
/// asserts refinement equality on arbitrary types
///
/// Note: this trick uses an axiom.

let prop_ext #a (p q:a -> prop) (v:a)
  : Lemma (requires (forall x. p x <==> q x))
          (ensures p v == q v)
  = P.apply (p v) (q v)

let refinement_equality (a:Type) (p q:a -> prop)
  : Lemma
    (requires forall x. p x <==> q x)
    (ensures (x:a { p x } == x:a { q x }))
  = assert (x:a { p x } == x:a { q x })
        by (pointwise
             (fun _ ->
               try mapply (quote (prop_ext #a p q))
               with _ -> trefl());
            trefl())

let less_than (k:int) = z:int{z < k}
let not_greater_than (x:int) = t:int{t<=x}
let lem (k:int)
  : Lemma (less_than k == not_greater_than (k - 1))
  = assert (less_than k == not_greater_than (k - 1))
        by (norm [delta_only [`%less_than; `%not_greater_than]];
            mapply (`refinement_equality))
