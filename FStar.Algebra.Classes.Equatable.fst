module FStar.Algebra.Classes.Equatable
 
module TC = FStar.Tactics.Typeclasses

class equatable (t:Type) = {
  eq: t -> t -> bool;
  reflexivity : (x:t -> Lemma (eq x x));
  symmetry: (x:t -> y:t -> Lemma (requires eq x y) 
                               (ensures eq y x));
  transitivity: (x:t -> y:t -> z:t -> Lemma (requires eq x y /\ eq y z) 
                                         (ensures eq x z));
} 

instance default_equatable (t:eqtype) : equatable t = {
  eq = (=);
  reflexivity = (fun _ -> ());
  symmetry = (fun _ _ -> ());
  transitivity = (fun _ _ _ -> ())  
}

let ( = ) (#t:Type) {|h: equatable t|} = h.eq

private let z = 4 = 5

private let _ = assert (not z)

private let zs = "hello" = "world"

private let _ =  assert (not zs)

private type fraction (t:Type) = 
  | Fraction : (num: t) -> (den: t) -> fraction t

private assume val is_zero (#t:Type) (f: fraction t) : bool

private assume val sub (#t:Type) (a b: fraction t) : fraction t

private instance fraction_equatable (t:Type) : equatable (fraction t) = {
  eq = (fun a b -> is_zero (sub a b));
  reflexivity = (fun _ -> admit());
  symmetry = (fun _ _ -> admit());
  transitivity = (fun _ _ _ -> admit())
}

private let trivial (t:Type) (f g: fraction t) : Lemma (f = g <==> g = f) = 
  let aux1 (p q: fraction t) : Lemma (requires p=q) (ensures q=p)
    = symmetry p q in
  FStar.Classical.forall_intro_2 (Classical.move_requires_2 aux1)

private let equality_lemma (#t:eqtype) (x y: t)
  : Lemma (requires x=y) (ensures x == y) = ()

[@@expect_failure]
private let failing_equality_lemma (#t:Type) {| equatable t |} (x y: t) 
  : Lemma (requires x=y) (ensures x == y) = ()
