module FStar.Algebra.Setoid

module TC = FStar.Tactics.Typeclasses
module P = FStar.PropositionalExtensionality

open FStar.Tactics

class equivalence_relation a = {
  eq : a -> a -> bool;
  reflexivity : (x:a -> Lemma (eq x x));
  symmetry: (x:a -> y:a -> Lemma (x `eq` y <==> y `eq` x));
  transitivity: (x:a -> y:a -> z:a -> Lemma (((eq x y) /\ (eq y z)) ==> eq x z));  
} 

type indicator a = a -> bool

private let eqclass_indicator #a {| equivalence_relation a |} (x:a) (y:a) = eq x y

let make_eqclass #a {| equivalence_relation a |} (sample:a) : indicator a = eqclass_indicator sample

let (!) #a {| equivalence_relation a |} x : indicator a = make_eqclass x

class has_mul t {| equivalence_relation t |} = {
  mul: t -> t -> t;
  congruence: (x:t) -> (y:t) -> (z:t) -> (w:t) 
    -> Lemma (requires eq x z /\ eq y w) (ensures eq (mul x y) (mul z w))  
}

let ec_eq #t {| equivalence_relation t |} #x (f: indicator t{f == !x}) #y (g: indicator t{g == !y})
  = eq x y

let try_compare #a {| equivalence_relation a |} (x y:a) (op: a->a->a) = 
  ec_eq !x !y


let is_reflexive #a (f: bool_func a) = forall (x:a). f a a

type setoid #a {| equivalence_relation a |} (x:a) = z:a{eq z x}

let ( ! ) #a {| eq: equivalence_relation a |} (x:a) = setoid x
 
noeq type magma a {| equivalence_relation a |} = {
  op: a -> a -> a;
  congruence: (x:a) -> (y:a) -> (z:a) -> (w: a) 
    -> Lemma (requires eq x z /\ eq y w) (ensures eq (op x y) (op z w))
}
 

let op #a {| equivalence_relation a |} (m: magma a) (#x #y: a) (p:Type{p == !x}) (q:Type{q == !y})
  = !(m.op x y) 

let op_congruence #a {| equivalence_relation a |} 
  (m: magma a) 
  (x y:a) 
  : Lemma (ensures !(x `m.op` y) == op m !x !y ) = ()
 

open FStar.Tactics

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

let eq_lemma #a {| equivalence_relation a |} (x y: a)
  : Lemma (requires eq x y) (ensures !x == !y) = 
  let equality (z:a) : Lemma (eq z x == eq z y) = 
      transitivity z x y;
      symmetry y x;
      transitivity z y x in
  Classical.forall_intro equality;
  let f1 (p:a) : prop = eq p x == true in
  let f2 (p:a) : prop = eq p y == true in  
  assert_norm (setoid x == z:a{f1 z});
  assert_norm (setoid y == z:a{f2 z});
  refinement_equality a f1 f2 
  
