module AlgebraTypeClasses

open FStar.Tactics.Typeclasses

type unary_op (#a: Type) = a -> a
type binary_op (#a: Type) = a -> a -> a

class semigroup (#a: Type) = {
  neutral: a;
  op: binary_op #a;
  inverse: unary_op #a;
  associativity_lemma: (x: a) -> (y: a) -> (z: a) -> Lemma (op (op x y) z == op x (op y z));
}

class monoid (#a : Type) = {
  neutral: a;
  op: binary_op #a;
  inverse: unary_op #a;
  associativity_lemma: (x: a) -> (y: a) -> (z: a) -> Lemma (op (op x y) z == op x (op y z));
}
