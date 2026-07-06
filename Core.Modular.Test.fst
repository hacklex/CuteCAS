module Core.Modular.Test

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

class mul_is_commutative (t:Type) {| r: ring t |} = {
  mul_commutativity: (x:t) -> (y:t) ->
                     Lemma (eq (mul x y) (mul y x));
}

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

class domain (t:Type) = {
  [@@@TC.no_method] d_r: ring t;
  domain_law: (x:t) -> (y:t) ->
              Lemma ((eq (mul x y) zero) <==>
                     ((eq x zero) \/ (eq y zero)));
}

unfold instance r_of_d (t:Type) {| d: domain t |} : ring t = d.d_r

let domain_nonzero_mul_nonzero (#t:Type) {| d: domain t |}
                               (x y: t)
  : Lemma (requires is_nonzero x /\ is_nonzero y)
          (ensures  is_nonzero (mul x y))
  = d.domain_law x y

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

class commutative_ring (t:Type) = {
  [@@@TC.no_method] cr_r:   ring t;
  [@@@TC.no_method] cr_mic: mul_is_commutative t #cr_r;
}

unfold instance r_of_cr (t:Type) {| cr: commutative_ring t |} : ring t = cr.cr_r

unfold instance mic_of_cr (t:Type) {| cr: commutative_ring t |}
  : mul_is_commutative t #(r_of_cr t) = cr.cr_mic

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

let fin (n: pos) = x:nat{x < n}

open FStar.Math.Fermat
open FStar.Math.Euclid
open FStar.Math.Lemmas
open FStar.List.Tot

module TC = FStar.Tactics.Typeclasses

let residue (n: pos {n > 1}) = fin n

let prime_residue (n: pos {n>1 /\ is_prime n}) = fin n

let residue_add (#p:int{p > 1}) (a b: residue p) : residue p =
  lemma_mod_lt (a + b) p; (a + b) % p

let residue_add_associativity (#p:int{p > 1}) (a b c: residue p)
  : Lemma (residue_add (residue_add a b) c == residue_add a (residue_add b c))
  = (* ((a+b)%p + c)%p = (a+b+c)%p = (a + (b+c)%p)%p *)
    lemma_mod_add_distr c (a + b) p;          (* (c + (a+b)%p)%p = (c+a+b)%p *)
    lemma_mod_add_distr a (b + c) p           (* (a + (b+c)%p)%p = (a+b+c)%p *)

let residue_mul (#p:int{p > 1}) (a b: residue p) : residue p =
  lemma_mod_lt (a * b) p; (a * b) % p

let residue_neg (#n:int{n > 1}) (a: residue n) : residue n =
  lemma_mod_lt (n - a) n; (n - a) % n

let residue_add_negation (#p:int{p > 1}) (x: residue p)
  : Lemma (residue_add (residue_neg x) x == 0 /\ residue_add x (residue_neg x) == 0)
  = (* ((p-x)%p + x) % p = (p-x+x)%p = p%p = 0 *)
    lemma_mod_add_distr x (p - x) p;          (* (x + (p-x)%p)%p = (x+p-x)%p = p%p *)
    lemma_mod_add_distr x ((p - x)) p;
    cancel_mul_mod 1 p;                        (* (1*p)%p = 0 *)
    assert ((x + (p - x)) == 1 * p)

let residue_mul_associativity (#p:int{p > 1}) (a b c: residue p)
  : Lemma (residue_mul (residue_mul a b) c == residue_mul a (residue_mul b c))
  = (* ((a*b)%p * c)%p = (a*b*c)%p = (a * (b*c)%p)%p *)
    lemma_mod_mul_distr_l (a * b) c p;        (* ((a*b)%p * c)%p = (a*b*c)%p *)
    lemma_mod_mul_distr_r a (b * c) p;        (* (a * (b*c)%p)%p = (a*b*c)%p *)
    assert (residue_mul (residue_mul a b) c == residue_mul a (residue_mul b c))

let residue_left_distributivity (#p:int{p > 1}) (x y z: residue p)
  : Lemma (residue_mul x (residue_add y z) == residue_add (residue_mul x y) (residue_mul x z))
  = (* x * ((y+z)%p) % p = (x*(y+z))%p = (x*y + x*z)%p
       = ((x*y)%p + (x*z)%p)%p *)
    lemma_mod_mul_distr_r x (y + z) p;
    modulo_distributivity (x * y) (x * z) p   (* (x*y + x*z)%p = ((x*y)%p + (x*z)%p)%p *)

let residue_right_distributivity (#p:int{p > 1}) (x y z: residue p)
  : Lemma (residue_mul (residue_add y z) x == residue_add (residue_mul y x) (residue_mul z x))
  = lemma_mod_mul_distr_l (y + z) x p;  
    modulo_distributivity (y * x) (z * x) p

unfold instance rr (n: pos{n>1}) : ring (residue n) = {
  r_add = {
      acg_eq = default_equatable (residue n);
      zero = 0;
      add = residue_add;
      add_commutativity = (fun _ _ -> ());
      add_associativity = residue_add_associativity;
      add_zero = (fun _ -> ());
      neg = residue_neg;
      add_negation = (residue_add_negation);
      add_congruence = (fun _ _ _ _ -> ());
      neg_congruence = (fun _ _ -> ())
    };
    one = 1;
    mul = residue_mul;
    mul_associativity = residue_mul_associativity;
    mul_one = (fun _ -> ());
    left_distributivity = residue_left_distributivity;
    right_distributivity = residue_right_distributivity;
    mul_congruence = (fun _ _ _ _ -> ())
}

unfold instance residue_ring (n: pos{n>1}) : commutative_ring (residue n) = {
  cr_r = rr n;
  cr_mic = { 
    mul_commutativity = (fun _ _ -> ())
  }
}


(* For 0 < a < p with p prime, bezout_prime gives (r,s) with
   r*p + s*a = 1.  Normalize s into [0,p) to get the inverse. *)
let residue_inv (#p:int{is_prime p}) (a: residue p {a <> 0}) : residue p =
  let (r, s) = bezout_prime p a in
  lemma_mod_lt s p; (((s % p) + p) % p)

(* The Bezout coefficient s satisfies (s * a) % p = 1. *)
let residue_bezout_sa_mod (#p:int{is_prime p}) (a: residue p {a <> 0})
  : Lemma (let (r, s) = bezout_prime p a in (s * a) % p == 1)
  = let (r, s) = bezout_prime p a in
    lemma_mod_plus 1 (- r) p

(* (inv a * a) % p = 1 and (a * inv a) % p = 1 *)
let residue_inv_correct (#p:int{is_prime p}) (a: residue p {a <> 0})
  : Lemma (residue_mul (residue_inv a) a == 1 /\ residue_mul a (residue_inv a) == 1)
  = let (r, s) = bezout_prime p a in
    let ia = residue_inv a in
    residue_bezout_sa_mod a;
    lemma_mod_mul_distr_l ((s % p) + p) a p;
    lemma_mod_mul_distr_l s a p 

let residue_inv_nonzero (#p:pos{is_prime p}) (a: residue p {a <> 0})
  : Lemma (residue_inv a <> 0) = residue_inv_correct a

(* ---------------------------------------------------------------- *)
(*  mul_is_group / skewfield / field assembly                        *)
(* ---------------------------------------------------------------- *)

(* `is_nonzero x` for the residue ring unfolds to `not (eq x zero)`, i.e.
   `not (x = 0)`, i.e. `x <> 0`.

   Wrap inv at the bare element type so the lambda binder is not refined
   by the `<> 0` preconditions of residue_inv / residue_inv_nonzero (which would
   leak into the instance-argument subtyping check on `residue_ring p`). *)
let residue_inv_member (p:int{is_prime p}) (x: residue p)
  : Pure (residue p) (requires x <> 0) (ensures fun y -> y <> 0)
  = residue_inv_nonzero x; residue_inv x

unfold instance residue_mig (p:int{is_prime p})
  : mul_is_group (residue p) #(r_of_cr (residue p) #(residue_ring p)) = {
    inv             = residue_inv_member p;
    inv_congr       = (fun _ _ -> ());
    inversion_lemma = (fun (x: residue p) -> residue_inv_correct x);
  }


let residue_skewfield (p:int{is_prime p}) : skewfield (residue p) = {
  sf_r   = rr p;
  sf_mig = residue_mig p;
}

let residue_one_ne_zero (p:int{is_prime p})
  : Lemma (not (1 = 0))
  = ()

unfold instance residue_field (p:int{is_prime p}) : field (prime_residue p) =
  {
    f_sf          = residue_skewfield p;
    f_mic         = (residue_ring p).cr_mic;
    f_one_ne_zero = ();
  }

let test_inverse #t {|field t|} (x: t{is_nonzero x}) = inv x

let solve_mig #t {|field t|} : mul_is_group t = TC.solve 

let test_inverse2 (#p: int{is_prime p}) (x: prime_residue p{x <> 0}) = test_inverse x

let nonzero_mod_means_not_divides (x: nat) (m: pos)
   : Lemma (requires x % m > 0) (ensures ~(divides m x)) = ()

let rec any_under_x_divides_n (n: pos) (x: pos) : Pure bool 
  (requires x < n) 
  (ensures fun d -> d <==> exists (y:pos{y<=x /\ y>1}). divides y n) 
  = 
    if x < 2 then false else
    if any_under_x_divides_n n (x-1) then true
    else begin
      divides_mod |> Classical.move_requires_2 |> Classical.forall_intro_2;
      mod_divides |> Classical.move_requires_2 |> Classical.forall_intro_2;  
      n % x = 0
    end  

let prime_bool (n:pos) : (x:bool{x <==> is_prime n}) =
  //divides_mod |> Classical.move_requires_2 |> Classical.forall_intro_2;
  //mod_divides |> Classical.move_requires_2 |> Classical.forall_intro_2;  
  divides_opp |> Classical.move_requires_2 |> Classical.forall_intro_2;  
  if n < 2 then false 
  else begin 
    if any_under_x_divides_n n (n-1) then false
    else begin 
      let aux (y: int{y<(-1) /\ y > -n}) : Lemma (~(divides y n)) =         
        assert (~(divides (-y) n)) in      
      let wat (x:int) 
        : Lemma (requires x `divides` n) 
                (ensures x = 1 \/ x = -1 \/ x = n \/ x = -n) =         
          if x > -n && x < (-1) then aux x        
      in wat |> Classical.move_requires |> Classical.forall_intro;      
      true
    end
  end

let test_lemmas (#n:pos{n>1}) (x: residue n{x <> 0}) =      
   if (is_prime n /\ (x > 0)) then begin     
      inversion_lemma x;
      assert (inv x `mul` x == 1);
      (inv x) <: residue n
    end 
    else (0 <: residue n)

let test_inverse3 (#p: int{is_prime p}) (x: prime_residue p{x <> 0}) = inv x
