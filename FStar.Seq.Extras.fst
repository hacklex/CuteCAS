module FStar.Seq.Extras

open FStar.Seq.Permutation
open FStar.Seq
open FStar.Calc

private module CE = FStar.Algebra.CommMonoid.Equiv

[@@"opaque_to_smt"]
let is_permutation' (#a:Type) (eq: FStar.Algebra.CommMonoid.Equiv.equiv a) (s0:seq a) (s1:seq a) (f:index_fun s0) =
  Seq.length s0 == Seq.length s1 /\
  (forall x y. // {:pattern f x; f y}
  x <> y ==> f x <> f y) /\
  (forall (i:nat{i < Seq.length s0}). // {:pattern (Seq.index s1 (f i))}
      Seq.index s0 i `eq.eq` Seq.index s1 (f i))


let reveal_is_permutation' #a eq (s0 s1:seq a) (f:index_fun s0)
  = reveal_opaque (`%is_permutation') (is_permutation' eq s0 s1 f)

let reveal_is_permutation_nopats' (#a:Type) (eq:FStar.Algebra.CommMonoid.Equiv.equiv a) (s0 s1:seq a) (f:index_fun s0)
  : Lemma (is_permutation' eq s0 s1 f <==>

           Seq.length s0 == Seq.length s1 /\

           (forall x y. x <> y ==> f x <> f y) /\

           (forall (i:nat{i < Seq.length s0}).
              Seq.index s0 i `eq.eq` Seq.index s1 (f i)))
   = reveal_is_permutation' eq s0 s1 f

let seqperm_len' #a #eq (s0 s1:seq a)
                   (p:seqperm' eq s0 s1)
  : Lemma
    (ensures Seq.length s0 == Seq.length s1)

  = reveal_is_permutation' eq s0 s1 p

let remove_i #a (s:seq a) (i:nat{i < Seq.length s})
  : a & seq a
  = let s0, s1 = Seq.split s i in
    Seq.head s1, Seq.append s0 (Seq.tail s1)

#push-options "--using_facts_from '* -FStar.Seq.Properties.slice_slice'"
let shift_perm2' #a #eq
               (s0 s1:seq a)
               (_:squash (Seq.length s0 == Seq.length s1 /\ Seq.length s0 > 0))
               (p:seqperm' eq s0 s1)
  : Tot (seqperm' eq (fst (Seq.un_snoc s0))
                 (snd (remove_i s1 (p (Seq.length s0 - 1)))))
  = reveal_is_permutation' eq s0 s1 p;
    let s0', last = Seq.un_snoc s0 in
    let n = Seq.length s0' in
    let p' (i:nat{ i < n })
        : j:nat{ j < n }
       = if p i < p n then p i else p i - 1
    in
    let _, s1' = remove_i s1 (p n) in
    reveal_is_permutation_nopats' eq s0' s1' p';
    p'
#pop-options


let shift_perm2 #a #eq
               (s0 s1:seq a)
               (_:squash (Seq.length s0 == Seq.length s1 /\ Seq.length s0 > 0))
               (p:seqperm' eq s0 s1)
  : Pure (seqperm' eq (fst (Seq.un_snoc s0))
                      (snd (remove_i s1 (p (Seq.length s0 - 1)))))
         (requires True)
         (ensures fun _ -> let n = Seq.length s0 - 1 in
                        Seq.index s1 (p n) `eq.eq`
                        Seq.index s0 n)
  = FStar.Algebra.CommMonoid.Equiv.elim_eq_laws eq;
    reveal_is_permutation' eq s0 s1 p;
    shift_perm2' s0 s1 () p


let eq2_eq #a (eq:FStar.Algebra.CommMonoid.Equiv.equiv a) (x y:a)
  : Lemma (requires x == y)
          (ensures x `eq.eq` y)
  = eq.reflexivity x


let elim_monoid_laws #a #eq (m:FStar.Algebra.CommMonoid.Equiv.cm a eq)
  : Lemma (
          (forall x y. {:pattern m.mult x y}  eq.eq (m.mult x y) (m.mult y x)) /\
          (forall x y z.{:pattern (m.mult x (m.mult y z))} eq.eq (m.mult x (m.mult y z)) (m.mult (m.mult x y) z)) /\
          (forall x.{:pattern (m.mult x m.unit)} eq.eq (m.mult x m.unit) x)
    )
  = introduce forall x y. eq.eq (m.mult x y) (m.mult y x)
    with ( m.commutativity x y );

    introduce forall x y z. eq.eq (m.mult x (m.mult y z)) (m.mult (m.mult x y) z)
    with ( m.associativity x y z;
           eq.symmetry (m.mult (m.mult x y) z) (m.mult x (m.mult y z)) );

    introduce forall x. eq.eq (m.mult x m.unit) x
    with ( FStar.Algebra.CommMonoid.Equiv.right_identity eq m x )

let rec foldm_snoc_unit_seq (#a:Type) (#eq:FStar.Algebra.CommMonoid.Equiv.equiv a) (m:FStar.Algebra.CommMonoid.Equiv.cm a eq) (s:Seq.seq a)
  : Lemma (requires Seq.equal s (Seq.create (Seq.length s) m.unit))
          (ensures eq.eq (foldm_snoc m s) m.unit)
          (decreases Seq.length s)
  = FStar.Algebra.CommMonoid.Equiv.elim_eq_laws eq;
    elim_monoid_laws m;
    if Seq.length s = 0
    then ()
    else let s_tl, _ = un_snoc s in
         foldm_snoc_unit_seq m s_tl

let x_yz_to_y_xz #a #eq (m:FStar.Algebra.CommMonoid.Equiv.cm a eq) (x y z:a)
  : Lemma ((x `m.mult` (y `m.mult` z))
             `eq.eq`
           (y `m.mult` (x `m.mult` z)))
  = FStar.Algebra.CommMonoid.Equiv.elim_eq_laws eq;
    elim_monoid_laws m;  
    calc (eq.eq) {
      x `m.mult` (y `m.mult` z);
      (eq.eq) { m.commutativity x (y `m.mult` z) }
      (y `m.mult` z) `m.mult` x;
      (eq.eq) { m.associativity y z x }
      y `m.mult` (z `m.mult` x);
      (eq.eq) { m.congruence y (z `m.mult` x) y (x `m.mult` z) }
      y `m.mult` (x `m.mult` z);
    }
    
#push-options "--fuel 0"
let foldm_snoc3 #a #eq (m:FStar.Algebra.CommMonoid.Equiv.cm a eq) (s1:seq a) (x:a) (s2:seq a)
  : Lemma (eq.eq (foldm_snoc m (Seq.append s1 (Seq.cons x s2)))
                 (m.mult x (foldm_snoc m (Seq.append s1 s2))))
  = FStar.Algebra.CommMonoid.Equiv.elim_eq_laws eq;
    elim_monoid_laws m;
    calc (eq.eq)
    {
      foldm_snoc m (Seq.append s1 (Seq.cons x s2));
      (eq.eq) { foldm_snoc_append m s1 (Seq.cons x s2) }
      m.mult (foldm_snoc m s1) (foldm_snoc m (Seq.cons x s2));
      (eq.eq) { foldm_snoc_append m (Seq.create 1 x) s2;
                m.congruence (foldm_snoc m s1)
                             (foldm_snoc m (Seq.cons x s2))
                             (foldm_snoc m s1)
                             (m.mult (foldm_snoc m (Seq.create 1 x)) (foldm_snoc m s2)) }
      m.mult (foldm_snoc m s1) (m.mult (foldm_snoc m (Seq.create 1 x)) (foldm_snoc m s2));
      (eq.eq) { foldm_snoc_singleton m x;
                m.congruence (foldm_snoc m (Seq.create 1 x))
                             (foldm_snoc m s2)
                             x
                             (foldm_snoc m s2);
                m.congruence (foldm_snoc m s1)
                             (m.mult (foldm_snoc m (Seq.create 1 x)) (foldm_snoc m s2))
                             (foldm_snoc m s1)
                             (m.mult x (foldm_snoc m s2)) }
      m.mult (foldm_snoc m s1) (m.mult x (foldm_snoc m s2));
      (eq.eq) { x_yz_to_y_xz m (foldm_snoc m s1) x (foldm_snoc m s2) }
      m.mult x (m.mult (foldm_snoc m s1) (foldm_snoc m s2));
      (eq.eq) { foldm_snoc_append m s1 s2;
                m.congruence x
                             (m.mult (foldm_snoc m s1) (foldm_snoc m s2))
                             x
                             (foldm_snoc m (Seq.append s1 s2)) }
      m.mult x (foldm_snoc m (Seq.append s1 s2));
    }
#pop-options


(* The sequence indexing lemmas make this quite fiddly *)
#push-options "--z3rlimit_factor 2 --fuel 1 --ifuel 0"
let rec foldm_snoc_perm #a #eq m s0 s1 p
  : Lemma
    (ensures eq.eq (foldm_snoc m s0) (foldm_snoc m s1))
    (decreases (Seq.length s0))
  = //for getting calc chain to compose
    FStar.Algebra.CommMonoid.Equiv.elim_eq_laws eq;
    seqperm_len' s0 s1 p;
    if Seq.length s0 = 0 then (
      assert (Seq.equal s0 s1);
      eq2_eq eq (foldm_snoc m s0) (foldm_snoc m s1)
    )
    else (
      let n0 = Seq.length s0 - 1 in
      let prefix, last = Seq.un_snoc s0 in
      let prefix', suffix' = Seq.split s1 (p n0) in
      let last', suffix' = Seq.head suffix', Seq.tail suffix' in
      let s1' = snd (remove_i s1 (p n0)) in
      let p' : seqperm' eq prefix s1' = shift_perm2 s0 s1 () p in
      assert (last `eq.eq` last');
      calc
      (eq.eq)
      {
        foldm_snoc m s1;
        (eq.eq) { assert (s1 `Seq.equal` Seq.append prefix' (Seq.cons last' suffix'));
                  eq2_eq eq (foldm_snoc m s1)
                            (foldm_snoc m (Seq.append prefix' (Seq.cons last' suffix'))) }
        foldm_snoc m (Seq.append prefix' (Seq.cons last' suffix'));
        (eq.eq) { foldm_snoc3 m prefix' last' suffix' }
        m.mult last' (foldm_snoc m (append prefix' suffix'));
        (eq.eq) { assert (Seq.equal (append prefix' suffix') s1');
                  eq2_eq eq (m.mult last' (foldm_snoc m (append prefix' suffix')))
                            (m.mult last' (foldm_snoc m s1')) }
        m.mult last' (foldm_snoc m s1');
        (eq.eq) { foldm_snoc_perm m prefix s1' p';
                  eq.symmetry (foldm_snoc m prefix) (foldm_snoc m s1');
                  eq.reflexivity last';
                  m.congruence last'
                               (foldm_snoc m s1')
                               last'
                               (foldm_snoc m prefix) }
        m.mult last' (foldm_snoc m prefix);
        (eq.eq) { m.congruence last' (foldm_snoc m prefix) last (foldm_snoc m prefix) }
        // eq (m.mult last' (foldm_snoc m prefix))
                            //  (foldm_snoc m s0) }
        foldm_snoc m s0;
      };
      eq.symmetry (foldm_snoc m s1) (foldm_snoc m s0))
#pop-options
