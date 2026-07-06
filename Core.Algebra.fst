module Core.Algebra

(*
   Diamond-free foundational algebra tower for CuteCAS.

   Design principles (see core/AGENTS.md §1):
   - Bundle fields tagged [@@@TC.no_method] so TC search never goes
     through them; resolution flows through explicit top-level
     `instance` declarations only.
   - Forest invariant: exactly one declared instance per ordered
     (Source, Target) class pair. Multi-step climbs compose
     automatically; skip-level instances are forbidden.
   - Marker classes (mul_is_commutative, mul_is_group) take the
     underlying structure as an explicit dependent param so coherence
     is statically forced.
   - Plain `instance` only; no `unfold instance` on records.
*)

module TC = FStar.Tactics.Typeclasses

(* ---------------------------------------------------------------- *)
(* equatable                                                        *)
(* ---------------------------------------------------------------- *)

class equatable (t:Type) = {
  eq:           t -> t -> bool;
  reflexivity:  (x:t) -> Lemma (eq x x);
  symmetry:     (x:t) -> (y:t) -> Lemma (eq x y <==> eq y x);
  transitivity: (x:t) -> (y:t) -> (z:t) ->
                Lemma (requires eq x y /\ eq y z) (ensures eq x z);
} 

instance default_equatable (t:eqtype) : equatable t = {
  eq = Prims.op_Equality;
  reflexivity = (fun _ -> ());
  symmetry = (fun _ _ -> ());
  transitivity = (fun _ _ _ -> ())
}

(* ---------------------------------------------------------------- *)
(* add_comm_group                                                   *)
(* ---------------------------------------------------------------- *)

class add_comm_group (t:Type) = {
  [@@@TC.no_method] acg_eq: equatable t;
  zero: t;
  add:  t -> t -> t;
  add_congruence:    (a:t) -> (b:t) -> (x:t) -> (y:t) ->
                     Lemma (requires eq a x /\ eq b y)
                           (ensures  add a b `eq` add x y);
  add_commutativity: (a:t) -> (b:t) ->
                     Lemma (add a b `eq` add b a);
  add_associativity: (a:t) -> (b:t) -> (c:t) ->
                     Lemma ((add (add a b) c) `eq` (add a (add b c)));
  add_zero:          (x:t) ->
                     Lemma ((eq (add x zero) x) /\ (eq (add zero x) x));
  neg:  t -> t;
  neg_congruence:    (a:t) -> (b:t) ->
                     Lemma (requires eq a b) (ensures eq (neg a) (neg b));
  add_negation:      (x:t) ->
                     Lemma ((eq (add (neg x) x) zero) /\
                            (eq (add x (neg x)) zero));
}

unfold instance eq_of_acg (t:Type) {| acg: add_comm_group t |} : equatable t = acg.acg_eq

(* Infix operators ( + ), ( * ), ( - ), ( ~- ) and prefix `neg`/`mul`
   notation live in `Core.Algebra.Notation` — NOT here. Opening
   `Core.Algebra` gives you the classes and instances; opening
   `Core.Algebra.Notation` additionally gives the overloaded operators.
   Files that use plain integer arithmetic in refinement types or
   `decreases` clauses (e.g. fin-n indices `i + 1 < n`) should only
   open `Core.Algebra`, so Prims arithmetic is used for those. *)

(* Note: we deliberately do NOT define ( - ) and ( ~- ) at module level —
   they collide with Prims integer arithmetic used in decreases clauses,
   list indices, etc. Use `neg x` and `add x (neg y)` (or write a per-module
   `let ( - ) x y = x + neg y` if the operator notation is needed locally). *)

(* ---------------------------------------------------------------- *)
(* op_group                                                         *)
(*   abstract multiplicative-style group; mostly here for           *)
(*   completeness — the proof tower uses ring/skewfield directly.   *)
(* ---------------------------------------------------------------- *)

class op_group (t:Type) = {
  [@@@TC.no_method] og_eq: equatable t;
  neutral: t;
  op:      t -> t -> t;
  op_congruence: (a:t) -> (b:t) -> (x:t) -> (y:t) ->
                 Lemma (requires eq a x /\ eq b y)
                       (ensures  eq (op a b) (op x y));
  op_associativity: (a:t) -> (b:t) -> (c:t) ->
                    Lemma (eq (op (op a b) c) (op a (op b c)));
  neutral_lemma:    (x:t) ->
                    Lemma ((eq (op x neutral) x) /\ (eq (op neutral x) x));
  inv_op:           t -> t;
  inv_op_congr:     (a:t) -> (b:t) ->
                    Lemma (requires eq a b) (ensures eq (inv_op a) (inv_op b));
  op_inversion:     (x:t) ->
                    Lemma ((eq (op (inv_op x) x) neutral) /\
                           (eq (op x (inv_op x)) neutral));
}

(* ---------------------------------------------------------------- *)
(* ring                                                             *)
(* ---------------------------------------------------------------- *)

class ring (t:Type) = {
  [@@@TC.no_method] r_add: add_comm_group t;
  one: t;
  mul: t -> t -> t;
  mul_congruence:       (a:t) -> (b:t) -> (x:t) -> (y:t) ->
                        Lemma (requires eq a x /\ eq b y)
                              (ensures  eq (mul a b) (mul x y));
  mul_associativity:    (a:t) -> (b:t) -> (c:t) ->
                        Lemma (eq (mul (mul a b) c) (mul a (mul b c)));
  mul_one:              (x:t) ->
                        Lemma ((eq (mul x one) x) /\ (eq (mul one x) x));
  left_distributivity:  (x:t) -> (y:t) -> (z:t) ->
                        Lemma (eq (mul x (add y z)) (add (mul x y) (mul x z)));
  right_distributivity: (x:t) -> (y:t) -> (z:t) ->
                        Lemma (eq (mul (add y z) x) (add (mul y x) (mul z x)));
}

unfold instance acg_of_r (t:Type) {| r: ring t |} : add_comm_group t = r.r_add

(* `( * )` lives in Core.Algebra.Notation — see comment near the top. *)

(* ---------------------------------------------------------------- *)
(* Marker class: ring + commutative multiplication                  *)
(* ---------------------------------------------------------------- *)

class mul_is_commutative (t:Type) {| r: ring t |} = {
  mul_commutativity: (x:t) -> (y:t) ->
                     Lemma (eq (mul x y) (mul y x));
}

(* ---------------------------------------------------------------- *)
(* nonzero predicate, used by the multiplicative-inverse marker     *)
(* ---------------------------------------------------------------- *)

unfold let is_nonzero (#t:Type) {| add_comm_group t |} (x:t) : bool =
  not (eq x zero)

class mul_is_group (t:Type) {| r: ring t |} = {
  inv:               (x:t) -> Pure t (requires is_nonzero x)
                                     (ensures fun y -> is_nonzero y);
  inv_congr:         (a: t) -> (b: t) ->
                     Lemma (requires is_nonzero a /\ is_nonzero b /\ eq a b)
                           (ensures  eq (inv a) (inv b));
  inversion_lemma:   (x: t) ->
                     Lemma (requires is_nonzero x)
                           (ensures (eq (mul x (inv x)) one) /\
                                    (eq (mul (inv x) x) one));
}

(* ---------------------------------------------------------------- *)
(* domain                                                           *)
(* ---------------------------------------------------------------- *)

class domain (t:Type) = {
  [@@@TC.no_method] d_r: ring t;
  domain_law: (x:t) -> (y:t) ->
              Lemma ((eq (mul x y) zero) <==>
                     ((eq x zero) \/ (eq y zero)));
}

unfold instance r_of_d (t:Type) {| d: domain t |} : ring t = d.d_r

(* Contrapositive of `domain_law`: in a domain, the product of two
   nonzero elements is nonzero. *)
let domain_nonzero_mul_nonzero (#t:Type) {| d: domain t |}
                               (x y: t)
  : Lemma (requires is_nonzero x /\ is_nonzero y)
          (ensures  is_nonzero (mul x y))
  = d.domain_law x y

(* ---------------------------------------------------------------- *)
(* skewfield                                                        *)
(* ---------------------------------------------------------------- *)

(* A skewfield is a ring where nonzero elements form a multiplicative
   group.  The domain law (no zero divisors) follows from the existence
   of inverses: if a·b = 0 and a ≠ 0 then b = inv(a)·(a·b) = inv(a)·0 = 0.
   We derive the domain instance rather than storing it redundantly. *)

class skewfield (t:Type) = {
  [@@@TC.no_method] sf_r:   ring t;
  [@@@TC.no_method] sf_mig: mul_is_group t #sf_r;
}

unfold instance mig_of_sf (t:Type) {| sf: skewfield t |} : mul_is_group t = sf.sf_mig

unfold instance r_of_sf (t:Type) {| sf: skewfield t |} : ring t = sf.sf_r

private let zero_mul_z (#t:Type) {|r: ring t|} (z: t) : Lemma (eq (mul zero z) zero)
  = 
  Classical.forall_intro #t reflexivity;
  Classical.forall_intro_2 #t symmetry; 
  Classical.forall_intro_3 #t (Classical.move_requires_3 transitivity);  
  let (+), ( * ), op_Minus = add, mul, neg in  
  add_zero #t zero;
  mul_congruence zero z (zero + zero) z;
  right_distributivity z zero zero;
  add_congruence (zero*z) (-(zero*z)) ((zero*z)+(zero*z)) (-(zero*z));
  add_negation (zero*z);
  add_associativity (zero*z) (zero*z) (-(zero*z));
  add_congruence (zero*z) (zero*z + (-(zero*z))) (zero*z) zero;
  add_zero (zero*z)

private let z_mul_zero (#t:Type) {|r: ring t|} (z: t) : Lemma (eq (mul z zero) zero)
  = 
  Classical.forall_intro #t reflexivity;
  Classical.forall_intro_2 #t symmetry; 
  Classical.forall_intro_3 #t (Classical.move_requires_3 transitivity);
  let (+), ( * ), op_Minus = add, mul, neg in
  add_zero #t zero;
  mul_congruence z zero z (zero + zero);
  left_distributivity z zero zero;
  add_congruence (z*zero) (-(z*zero)) ((z*zero)+(z*zero)) (-(z*zero));
  add_negation (z*zero);
  add_associativity (z*zero) (z*zero) (-(z*zero));
  add_congruence (z*zero) (z*zero + (-(z*zero))) (z*zero) zero;
  add_zero (z*zero)

private let mul_zero (#t:Type) {|r: ring t|} (z: t) : Lemma (eq (mul z zero) zero /\ eq (mul zero z) zero)
  = z_mul_zero z; zero_mul_z z

(* Proof that mul_is_group implies the no-zero-divisors law.
   Self-contained: uses only ring/equatable axiom fields directly. *)
private let mul_is_group_means_domain (#t:Type) (#r: ring t) (mig: mul_is_group t #r) (x y: t)
  : Lemma ((eq (mul x y) zero) <==> ((eq x zero) \/ (eq y zero))) =   
  Classical.forall_intro #t reflexivity;
  Classical.forall_intro_2 #t symmetry; 
  Classical.forall_intro_3 #t (Classical.move_requires_3 transitivity);
(* Step 2: backward direction — x=0 ∨ y=0 → xy=0 *)
  let backward () : Lemma (requires (eq x zero) \/ (eq y zero))
                          (ensures eq (mul x y) zero) =
    mul_zero x;
    mul_zero y;
    if (eq x zero) 
    then mul_congruence x y zero y 
    else mul_congruence x y x zero
  in
  (* Step 3: forward direction — xy=0 ∧ x≠0 → y=0 *)
  let forward () : Lemma (requires eq (mul x y) zero)
                          (ensures (eq x zero) \/ (eq y zero)) =
    if not (eq x (zero <: t)) then (
      mig.inversion_lemma x;
      let ix = mig.inv x in
      mul_associativity ix x y;
      mul_congruence (mul ix x) y one y;
      mul_one y;
      mul_congruence ix (mul x y) ix (zero <: t);
      z_mul_zero ix
    ) else ()
  in
  Classical.move_requires backward ();
  Classical.move_requires forward ()

unfold instance d_of_sf (t:Type) {| sf: skewfield t |} : domain t = {
  d_r = sf.sf_r;
  domain_law = mul_is_group_means_domain sf.sf_mig;
}

(* ---------------------------------------------------------------- *)
(* commutative_ring                                                 *)
(* ---------------------------------------------------------------- *)

class commutative_ring (t:Type) = {
  [@@@TC.no_method] cr_r:   ring t;
  [@@@TC.no_method] cr_mic: mul_is_commutative t #cr_r;
}

unfold instance r_of_cr (t:Type) {| cr: commutative_ring t |} : ring t = cr.cr_r

unfold instance mic_of_cr (t:Type) {| cr: commutative_ring t |}
  : mul_is_commutative t #(r_of_cr t) = cr.cr_mic

(* ---------------------------------------------------------------- *)
(* integral_domain                                                  *)
(* ---------------------------------------------------------------- *)

class integral_domain (t:Type) = {
  [@@@TC.no_method] id_d:   domain t;
  [@@@TC.no_method] id_mic: mul_is_commutative t #id_d.d_r;
  (* Classical theory: every integral domain has 1 ≠ 0. Baking this
     in (rather than as a separate marker class) since we never
     construct non-commutative domains or "trivial" rings as ID
     instances. Any field requires this too.

     The axiom shape is factored into the helper `one_ne_zero_axiom`
     so we can write it with bare names — the helper takes the domain
     as an explicit instance and resolves `eq`/`one`/`zero` cleanly. *)
  [@@@TC.no_method] id_one_ne_zero: squash(not(one `eq` zero #t));
}

unfold instance d_of_id (t:Type) {| id: integral_domain t |} : domain t = id.id_d

unfold instance cr_of_id (t:Type) {| id: integral_domain t |} : commutative_ring t = {
  cr_r   = id.id_d.d_r;
  cr_mic = id.id_mic;
}

(* ---------------------------------------------------------------- *)
(* field                                                            *)
(* ---------------------------------------------------------------- *)

class field (t:Type) = {
  [@@@TC.no_method] f_sf:  skewfield t;
  [@@@TC.no_method] f_mic: mul_is_commutative t #f_sf.sf_r; 
  [@@@TC.no_method] f_one_ne_zero: squash (not (one `eq` zero #t)); 
}


unfold instance sf_of_f (t:Type) {| f: field t |} : skewfield t = f.f_sf


instance id_of_f (t:Type) {| f: field t |} : integral_domain t = {
  id_d           = d_of_sf t;
  id_mic         = f.f_mic;
  id_one_ne_zero = f.f_one_ne_zero;
}

(* Note: field → commutative_ring composes uniquely via
   id_of_f ∘ cr_of_id. We deliberately do NOT declare a direct
   `cr_of_f` shortcut — that would create a diamond. *)
