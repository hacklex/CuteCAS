module FStar.Seq.Extras
 
open FStar.Seq.Permutation
open FStar.Seq
open FStar.Calc

(* An abstract predicate defining when an index_fun is a permutation *)
val is_permutation' (#a:Type) (eq: FStar.Algebra.CommMonoid.Equiv.equiv a) (s0:seq a) (s1:seq a) (f:index_fun s0) : prop

(* A seqperm is an index_fun that is also a permutation *)
let seqperm' (#a:Type) (eq:FStar.Algebra.CommMonoid.Equiv.equiv a) (s0:seq a) (s1:seq a) =
  f:index_fun s0 { is_permutation' eq s0 s1 f }
  
val reveal_is_permutation' (#a:Type) (eq:FStar.Algebra.CommMonoid.Equiv.equiv a) (s0 s1:seq a) (f:index_fun s0)
  : Lemma (is_permutation' eq s0 s1 f <==>
           (* lengths of the sequences are the same *)
           Seq.length s0 == Seq.length s1 /\
           (* f is injective *)
           (forall x y. {:pattern f x; f y}
             x <> y ==> f x <> f y) /\
           (* and f relates equal items in s0 and s1 *)
           (forall (i:nat{i < Seq.length s0}).{:pattern (Seq.index s1 (f i))}
              Seq.index s0 i `eq.eq` Seq.index s1 (f i)))

(* And, finally, if s0 and s1 are permutations,
   then folding m over them is identical *)
val foldm_snoc_perm (#a:_) (#eq:_)
               (m:FStar.Algebra.CommMonoid.Equiv.cm a eq)
               (s0:seq a)
               (s1:seq a)
               (p:seqperm' eq s0 s1)
  : Lemma
    (ensures eq.eq (foldm_snoc m s0) (foldm_snoc m s1))
