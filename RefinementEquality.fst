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


let eq_fun (t1 t2:Type) (r1:t1 -> Type) (r2:t2 -> Type)
           (f1:(x:t1 -> r1 x))
           (f2:(x:t2 -> r2 x))
           (teq:squash (t1 == t2))
           (req:squash (forall (x:t1).  r1 x == r2 x))
           (feq:(x:t1 -> Lemma (f1 x == f2 x)))
  : Tot (squash ((fun (x:t1) -> f1 x) == (fun (x:t2) -> f2 x)))
    by (split ();
          smt(); //the first goal is about the well-typedness of the goal itself; SMT can do that
          l_to_r [quote teq; quote feq]) //rewrite the lambda terms with teq and feq
  = ()

let true_prop #a (x:a)  = true

let type_with_prop (t:Type) (p: t -> Type0) = z:t{p z}

let equality_of_types (t: Type) (p1 p2: t -> Type0) (proof: squash(p1 == p2))
  : Lemma (type_with_prop t p1 == type_with_prop t p2) = ()

type option_val =
  | Bool of bool
  | String of string
  | Path of string
  | Int of int
  | List of list option_val
  | Unset


let as_bool = function
  | Bool b -> b
  | String z -> z = ""
  | _ -> false

let auxie (t: Type) (p: t->Type0) (proof: squash (forall (x:t). p x)) 
  : Lemma (t == (z:t{p z})) =
  assert ((z:t{p z}) == t) by (

    l_to_r [quote proof]

  );  
  ()


let eq_of_null_refine (t: Type) : Lemma (t == (x:t{true_prop x})) by ( smt(); l_to_r [quote t  ] )  = ()

let eq_for_type_with_no_ref 
           (t1 t2:Type) 
           (r1:t1 -> Type) (r2:t2 -> Type)
           (type_1: (z:Type{z==(x:t1{r1 x})}))
           (type_2: (z:Type{z==(x:t2{r2 x})}))
           (teq:squash (t1 == t2))
           (req:squash (forall (x:t1).  r1 x == r2 x))
           (feq:squash ((forall (x:t2).  r1 x) /\ (forall (x:t1). r2 x) ))
           
  : Tot (squash (type_1 == type_2)) by
  (
    split();
    smt(); 
    l_to_r [quote teq; quote req; quote feq] 
  ) = 
  ()
