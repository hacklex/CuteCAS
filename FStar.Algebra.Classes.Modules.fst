module FStar.Algebra.Classes.Modules

module TC = FStar.Tactics.Typeclasses

open FStar.Algebra.Classes.Equatable
open FStar.Algebra.Classes.Grouplikes
open FStar.Algebra.Classes.Ringlikes

(* This is the current best attempt at speeding up stateless (and thus cacheless) typeclass resolution *)
instance he_temp t (g: add_comm_group t) : equatable t = g.add_group.add_monoid.add_semigroup.has_add.eq
instance ha_temp t (g:add_comm_group t) : has_add t = g.add_group.add_monoid.add_semigroup.has_add
instance hn_temp t (g: add_comm_group t) : has_neg t = g.add_group.has_neg
instance hm_temp t (g: add_comm_group t) : add_monoid t = g.add_group.add_monoid

(* Left module. In general, ring is not required to be commutative.
   This is what would be left of a vector space if the scalar field 
   is no longer a field, but only a ring. *)
class left_module (vector: Type) 
                  (scalar: Type) 
                  (r: ring scalar) 
                  (cm: add_comm_group vector) = {
  s_mul_v: (x:scalar) -> (y: vector) -> vector;
  left_module_congruence : (x:scalar) -> (y:vector) -> (z:vector) -> Lemma (requires y=z) (ensures s_mul_v x y = s_mul_v x z);
  ssv_associativity: (x: scalar) -> (y: scalar) -> (z: vector) -> Lemma (s_mul_v x (s_mul_v y z) = s_mul_v (x*y) z); 
  svv_distributivity: (x: scalar) -> (y: vector) -> (z: vector) -> Lemma (s_mul_v x (y + z) = s_mul_v x y + s_mul_v x z); 
  ssv_distributivity: (x: scalar) -> (y: scalar) -> (z: vector) -> Lemma (s_mul_v (x + y) z = s_mul_v x z + s_mul_v y z); 
}

(* S-multiplication currently can't smoothly override * operator
   in F*, because implementing heterogenous multiplication would
   spell type resolution troubles.  *)
let ( ^* ) #v #s {| r: ring s |} {| cm: add_comm_group v |} {| lm: left_module v s r cm |} (x:s) (y:v)
  : v = lm.s_mul_v x y

(* Right module class mirrors the left one *)
class right_module (vector: Type) 
                  (scalar: Type) 
                  (r: ring scalar) 
                  (cm: add_comm_group vector) = {
  v_mul_s: (x:vector) -> (y: scalar) -> vector;
  right_module_congruence : (x:vector) -> (y:vector) -> (z:scalar) -> Lemma (requires x=y) (ensures v_mul_s x z = v_mul_s y z);
  vss_associativity: (x: vector) -> (y: scalar) -> (z: scalar) -> Lemma (v_mul_s (v_mul_s x y) z = v_mul_s x (y*z));
  vss_distributivity: (x: vector) -> (y: scalar) -> (z: scalar) -> Lemma (v_mul_s x (y + z) = v_mul_s x y + v_mul_s x z); 
  vvs_distributivity: (x: vector) -> (y: vector) -> (z: scalar) -> Lemma (v_mul_s (x + y) z = v_mul_s x z + v_mul_s y z);   
}

(* Similar operator is defined for right module *)
let ( *^ ) #v #s {| r: ring s |} {| cm: add_comm_group v |} {| rm: right_module v s r cm |} (x:v) (y:s)
  : v = rm.v_mul_s x y

(* we can't use the name "module" because it is a keyword *)
class full_module (vector scalar: Type) (r: ring scalar) (cm: add_comm_group vector) = {
  [@@@TC.no_method] left_module: left_module vector scalar r cm; 
  [@@@TC.no_method] right_module: right_module vector scalar r cm; 
  module_commutativity: (x:vector) -> (y: scalar) -> Lemma ((x *^ y) = (y ^* x));  
}

(* An R,S-bimodule is built from an abelian group, two rings and a compatibility axiom *)
class bimodule (lscalar: Type) (vector: Type) (rscalar: Type) (r: ring lscalar) (g: add_comm_group vector) (s: ring rscalar) = {
  [@@@TC.no_method] left_module: left_module vector lscalar r g; 
  [@@@TC.no_method] right_module: right_module vector rscalar s g; 
  bimodule_axiom: (a: lscalar) -> (x:vector) -> (b: rscalar) -> Lemma ((a ^* (x *^ b)) = ((a ^* x) *^ b));  
}

(* building integer-related typeclasses *)
instance int_add_comm_monoid : add_comm_monoid int = {
  add_monoid = { 
    has_zero = { eq = int_equatable; zero = 0 };
    add_semigroup = { has_add = int_add; associativity = (fun _ _ _ -> ()) };
    left_add_identity = (fun _ -> ());
    right_add_identity = (fun _ -> ());
  };
  add_comm_semigroup = {
    add_comm_magma = { has_add = int_add; add_commutativity = (fun _ _ -> ()) };
    add_semigroup = { has_add = int_add; associativity = (fun _ _ _ -> ()) };
  }
}

instance int_semiring : semiring int = {
  add_comm_monoid = int_add_comm_monoid;
  mul_monoid = {
    has_one = { eq = int_equatable; one = 1 };
    mul_semigroup = { has_mul = int_mul; associativity = (fun _ _ _ -> ()) };
    left_mul_identity = (fun _ -> ());
    right_mul_identity = (fun _ -> ());
  };
  left_absorption = (fun _ -> ());
  left_distributivity = (fun _ _ _ -> ());
  right_distributivity = (fun _ _ _ -> ());
  right_absorption = (fun _ -> ());
}

instance int_ring : ring int = {
  semiring = int_semiring;
  add_comm_group = { 
    add_comm_monoid = int_semiring.add_comm_monoid;
    add_group = {
      add_monoid = int_semiring.add_comm_monoid.add_monoid;
      has_neg = { neg = op_Minus };
      has_sub = { sub = op_Subtraction };
      subtraction_definition = (fun _ _ -> ());
      negation = (fun _ -> ())
    }    
  }
}

open FStar.Math.Fermat
open FStar.Math.Lemmas

instance int_commutative_ring : commutative_ring int = {
  ring = int_ring;
  mul_comm_monoid = {
    mul_monoid = int_ring.semiring.mul_monoid;
    mul_comm_semigroup = {
      mul_semigroup = int_semiring.mul_monoid.mul_semigroup;
      mul_comm_magma = {
        has_mul = int_mul;
        mul_commutativity = (fun _ _ -> ())
      };
      dvd = (fun x y -> if x=0 then (y=0) else (
        if y=0 then true else begin
          Classical.move_requires_2 (Math.Euclid.mod_divides) y x;
          Classical.move_requires_2 (Math.Euclid.divides_mod) y x;
          (y % x) = 0
        end
      ))
    };
  }
}

instance int_domain : domain int = {
  ring = int_ring;
  zero_ne_one_semiring = { semiring = int_semiring };
  domain_law = (fun _ _ -> ())
}

instance int_integral_domain : integral_domain int = {
  commutative_ring = int_commutative_ring;
  domain = int_domain
}

(* From here, we work our way towards showing that any abelian group forms a int-module *)

(* s-multiplication is a function (int * t) -> t *)
let rec zmul #t {| g: add_comm_group t |} (a: int) (x:t) : Tot t (decreases abs a) = 
  if a = 0 then zero
  else if a > 0 then x + (zmul (a-1) x)
  else (-x) + (zmul (a+1) x)

(* x=y ==> ax=ay *)
let rec zmul_congruence #t {| g: add_comm_group t |} (a:int) (x y:t) 
  : Lemma (requires x = y) (ensures zmul a x = zmul a y) (decreases abs a) = 
  if a = 0 then reflexivity (zmul a x) 
  else if a > 0 then begin
    zmul_congruence (a-1) x y;
    add_congruence x (zmul (a-1) x) y (zmul (a-1) y)
  end 
  else begin    
    zmul_congruence (a+1) x y;
    equal_elements_have_equal_inverses x y;
    add_congruence (-x) (zmul (a+1) x) (-y) (zmul (a+1) y)
  end

(* a*zero = zero (zero is the group neutral, a is an integer) *)
let rec zmul_zero #t {| g: add_comm_group t |} (a:int) (x:t) 
  : Lemma (requires x = zero) (ensures zmul a x = zero) (decreases abs a) = 
  if a = 0 then begin
    reflexivity (zmul a x);
    symmetry (zmul a x) zero 
  end
  else if a > 0 then begin 
    zmul_zero (a-1) x;
    left_add_identity (zmul (a-1) x);
    reflexivity (zmul (a-1) x);
    add_congruence x (zmul (a-1) x) zero (zmul (a-1) x);
    trans_lemma [ zmul a x; zero + (zmul (a-1) x); zmul (a-1) x; zero ]
  end
  else begin
    let zero : t = zero in
    Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry;
    zmul_zero (a+1) x;
    left_add_identity (zmul (a+1) x);
    reflexivity (zmul (a+1) x);
    equal_elements_have_equal_inverses x zero;
    zero_equals_minus_zero #t #g.add_group;
    transitivity (-x) (-zero) zero;
    add_congruence (-x) (zmul (a+1) x) zero (zmul (a+1) x);
    trans_lemma [ zmul a x; zero + (zmul (a+1) x); zmul (a+1) x; zero ];
    ()
  end  

(* Auxiliary lemmas *)
let zmul_dec #t {| g: add_comm_group t |} (a: int) (x:t)
  : Lemma (ensures zmul a x = x + zmul (a-1) x) = 
  let zero : t = zero in
  Classical.forall_intro g.add_group.add_monoid.add_semigroup.has_add.eq.reflexivity;
  Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry; 
  if a > 0 then reflexivity (zmul a x)
  else if a = 0 then begin
    add_associativity x (-x) zero;
    negation x;
    add_congruence (x + -x) zero zero zero;
    left_add_identity zero;
    trans_lemma [ zmul a x; 
                  zero + zero; 
                  (x + -x) + zero; 
                  x + (-x + zero); 
                  x + zmul (a-1) x ]
  end else begin
    add_associativity x (-x) (zmul a x);
    negation x;
    add_congruence (x + -x) (zmul a x) zero (zmul a x);
    left_add_identity (zmul a x); 
    trans_lemma [ zmul a x;
                  zero + zmul a x;
                  (x + -x) + zmul a x;
                  x + zmul (a-1) x ]
  end

let zmul_inc #t {| g: add_comm_group t |} (a: int) (x:t)
  : Lemma (ensures zmul (a+1) x = x + zmul a x) = 
  Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry; 
  zmul_dec (a+1) x

let rec zmul_neg #t {| g: add_comm_group t |} (a: int) (x:t)
  : Lemma (ensures zmul (-a) x = zmul a (-x)) (decreases abs a) =
  Classical.forall_intro g.add_group.add_monoid.add_semigroup.has_add.eq.reflexivity;
  Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry;  
  if a=0 then reflexivity (zmul a x)
  else if a>0 then begin
    zmul_neg (a-1) x;
    zmul_inc (-a) x;
    transitivity_for_calc_proofs t;    
    negation x;
    add_congruence (-x) (zmul (a-1) (-x)) (-x) (x + zmul (-a) x);
    calc (=) {
      zmul a (-x);            = {}
      -x + (x + zmul (-a) x); = { add_associativity (-x) x (zmul (-a) x) }
      (-x + x) + zmul (-a) x; = { add_congruence (-x + x) (zmul (-a) x) zero (zmul (-a) x) }
      zero + zmul (-a) x;     = { left_add_identity (zmul (-a) x) }
      zmul (-a) x;
    }
  end else begin
    zmul_neg (a+1) x;
    zmul_inc (-a) x;
    zmul_inc a (-x);
    transitivity_for_calc_proofs t;    
    negation x;
    add_congruence x (zmul (-a-1) x) x (zmul (a+1) (-x));
    calc (=){
      zmul (-a) x; = {}
      x + zmul (a+1) (-x); = { add_congruence x (zmul (a+1) (-x)) x (-x + zmul a (-x)) }
      x + (-x + zmul a (-x)); = { add_associativity x (-x) (zmul a (-x)) }
      (x + -x) + zmul a (-x); = { add_congruence (x + -x) (zmul a (-x)) zero (zmul a (-x)) }
      zero + zmul a (-x); = { left_add_identity (zmul a (-x)) }
      zmul a (-x);
    };
    ()
  end

private let rec neg_zmul_nat #t {| g: add_comm_group t |} (a: int) (x:t)
  : Lemma (requires a>=0) 
          (ensures (-(zmul a x) = zmul (-a) x) /\ (-(zmul a x) = zmul a (-x)))
          (decreases abs a)  = 
  Classical.forall_intro g.add_group.add_monoid.add_semigroup.has_add.eq.reflexivity;
  Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry;  
  if a=0 then zero_equals_minus_zero #t #g.add_group
  else begin
    neg_zmul_nat (a-1) x;
    zmul_dec a x;
    neg_of_sum x (zmul (a-1) x);
    add_commutativity (zmul (a-1) x) (-x);
    transitivity_for_calc_proofs t;
    add_congruence (-(zmul (a-1) x)) (-x) (zmul (-(a-1)) x) (-x);
    assert (( -(zmul (a-1) x) + -x) = (zmul (-(a-1)) x + -x));
    calc (=) {
      -(zmul a x); = {}
      -(x + zmul (a-1) x); = {}
      -(x + zmul (a-1) x); = {}
      ( (-(zmul (a-1) x)) + -x); 
    };
    assert ((-(zmul a x)) = ( (-(zmul (a-1) x)) + -x));
    transitivity (-(zmul a x)) 
                 ((-(zmul (a-1) x)) + -x)
                 (zmul (-(a-1)) x + -x);
    calc (=) {
      -(zmul a x); = {}
      (zmul (-(a-1)) x + -x); = { zmul_neg (a-1) x;
                                  add_congruence (zmul (-(a-1)) x) (-x) (zmul (a-1) (-x)) (-x) }
      zmul (a-1) (-x) + (-x); = { add_commutativity (zmul (a-1) (-x)) (-x) }
      (-x) + zmul (a-1) (-x); = { zmul_dec a (-x) }
      zmul a (-x);
    };
    assert (-(zmul a x) = zmul a (-x));
    zmul_neg a x;
    ()    
  end

let neg_zmul #t {| g: add_comm_group t |} (a: int) (x:t)
  : Lemma (ensures (-(zmul a x) = zmul (-a) x) && (-(zmul a x) = zmul a (-x))) 
          (decreases abs a) = 
  Classical.forall_intro g.add_group.add_monoid.add_semigroup.has_add.eq.reflexivity;
  Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry;  
  if a>=0 then neg_zmul_nat a x
  else begin
    assert (a<0);
    transitivity_for_calc_proofs t;
    calc (=) {
      -(zmul a x);       = { zmul_neg (-a) x;
                             equal_elements_have_equal_inverses (zmul a x) (zmul (-a) (-x)) }
      -(zmul (-a) (-x)); = { neg_zmul_nat (-a) (-x) }
      zmul a (-x);       
    };
    zmul_neg a x
  end

(* (scalar+scalar)*vector distributivity *)
let rec zmul_ssv_distr #t {| g: add_comm_group t |} (a b:int) (x:t) 
  : Lemma (ensures zmul (a+b) x = zmul a x + zmul b x) (decreases abs a) = 
  Classical.forall_intro g.add_group.add_monoid.add_semigroup.has_add.eq.reflexivity;
  Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry; 
  if a = 0 then begin
    left_add_identity (zmul b x);
    symmetry (zmul a x + zmul b x) (zmul b x)
  end else if a > 0 then begin
    zmul_ssv_distr (a-1) b x;    
    zmul_dec a x;
    zmul_dec (a+b) x;
    add_congruence x (zmul (a-1+b) x) x (zmul (a-1) x + zmul b x);
    add_associativity x (zmul (a-1) x) (zmul b x);
    trans_lemma [ zmul (a+b) x;
                  x + (zmul (a-1+b) x);
                  x + (zmul (a-1) x + zmul b x);
                  (x + zmul (a-1) x) + zmul b x ]
  end else begin
    zmul_ssv_distr (a+1) b x;    
    assert (zmul (a+1+b) x = zmul (a+1) x + zmul b x);
    zmul_inc (a+b) x;
    zmul_inc a x;
    assert (zmul (a+1+b) x = x + zmul (a+b) x);
    assert (zmul (a+1) x = x + zmul a x);
    add_congruence (zmul (a+1) x) (zmul b x) (x + zmul a x) (zmul b x); 
    add_associativity x (zmul a x) (zmul b x);
    trans_lemma [ (x + zmul (a+b) x);
                  (zmul (a+1+b) x);
                  (zmul (a+1) x + zmul b x);
                  (x + zmul a x) + zmul b x; 
                  x + (zmul a x + zmul b x) ];
    group_cancellation_left x (zmul (a+b) x) (zmul a x + zmul b x)
  end

(* scalar*(vector+vector) distributivity aux *)
private let rec zmul_svv_distr_nat #t {| g: add_comm_group t |} (a:int) (x y:t)
  : Lemma (requires a>=0) (ensures zmul a (x+y) = zmul a x + zmul a y) (decreases a) =
  Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry; 
  Classical.forall_intro g.add_group.add_monoid.add_semigroup.has_add.eq.reflexivity;
  if a = 0 then right_add_identity (zero <: t) 
  else begin
    assert (a>0);
    zmul_svv_distr_nat (a-1) x y;
    assert (zmul (a-1) (x+y) = zmul (a-1) x + zmul (a-1) y);
    zmul_dec a (x+y);
    zmul_dec a x;
    zmul_dec a y; 
    transitivity_for_calc_proofs t; 
    calc (=) {
      zmul a (x+y); == {}
      (x+y) + zmul (a-1) (x+y); = { add_congruence (x+y) (zmul (a-1) (x+y)) (x+y) (zmul (a-1) x + zmul (a-1) y) } 
      (x+y) + (zmul (a-1) x + zmul (a-1) y); = { add_commutativity (zmul (a-1) x) (zmul (a-1) y); 
                                                 add_congruence (x+y) (zmul (a-1) x + zmul (a-1) y) (x+y) (zmul (a-1) y + zmul (a-1) x)
                                               }
      (x+y) + (zmul (a-1) y + zmul (a-1) x); = { add_associativity x y (zmul (a-1) y + zmul (a-1) x)  }
      x + (y + (zmul (a-1) y + zmul (a-1) x)); = { add_associativity y (zmul (a-1) y) (zmul (a-1) x);
                                                   add_congruence x (y + (zmul (a-1) y + zmul (a-1) x)) x ((y + zmul (a-1) y) + zmul (a-1) x) }
      x + ((y + zmul (a-1) y) + zmul (a-1) x); = { add_congruence (y + zmul (a-1) y) (zmul (a-1) x) (zmul a y) (zmul (a-1) x);
                                                   add_congruence x ((y + zmul (a-1) y) + zmul (a-1) x) x (zmul a y + zmul (a-1) x)
                                                 }
      x + (zmul a y + zmul (a-1) x); = { add_commutativity (zmul a y) (zmul (a-1) x);
                                         add_congruence x (zmul a y + zmul (a-1) x) x (zmul (a-1) x + zmul a y);
                                         add_associativity x (zmul (a-1) x) (zmul a y);
                                         add_congruence (x + zmul (a-1) x) (zmul a y) (zmul a x) (zmul a y) }
      zmul a x + zmul a y;
    }
  end

let zmul_neg_neg #t {| g: add_comm_group t |} (a:int) (x:t) 
  : Lemma (ensures zmul (-a) (-x) = zmul a x) = 
  zmul_neg (-a) x;
  symmetry (zmul (-a) (-x)) (zmul a x)

(* scalar*(vector+vector) distributivity, final form :) *)
let zmul_svv_distr #t {| g: add_comm_group t |} (a:int) (x y:t) 
  : Lemma (ensures zmul a (x+y) = zmul a x + zmul a y) =
  Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry; 
  Classical.forall_intro g.add_group.add_monoid.add_semigroup.has_add.eq.reflexivity;
  if a>=0 then zmul_svv_distr_nat a x y else begin
    transitivity_for_calc_proofs t;
    calc (=) { 
      zmul a (x+y); = { zmul_neg_neg a (x+y) }
      zmul (-a) (-(x+y)); = { neg_of_sum x y;
                              zmul_congruence (-a) (-(x+y)) (-y + -x) }
      zmul (-a) (-y + -x); = { zmul_svv_distr_nat (-a) (-y) (-x) }
      zmul (-a) (-y) + zmul (-a) (-x); = { zmul_neg_neg a y;
                                           zmul_neg_neg a x;
                                           add_congruence (zmul (-a) (-y)) (zmul (-a) (-x)) (zmul a y) (zmul a x); 
                                           add_commutativity (zmul a y) (zmul a x) }
      zmul a x + zmul a y;
    }
  end


let rec zmul_ssv_assoc_nat #t {| g: add_comm_group t |} (a b:int) (x:t)
  : Lemma (requires b>=0) (ensures zmul (a*b) x = zmul b (zmul a x)) (decreases abs b + abs a) = 
  let m (p:int) (q:t) = zmul p q in
  Classical.forall_intro g.add_group.add_monoid.add_semigroup.has_add.eq.reflexivity;
  Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry;
  if b=0 then zmul_zero a (zmul b x)
  else begin
    transitivity_for_calc_proofs t;
    zmul_ssv_assoc_nat a (b-1) x;
    assert (a*b = (a+ (b-1)*a));
    zmul_ssv_distr a ((b-1)*a) x;
    assert (zmul (a*b) x = zmul a x + zmul ((b-1)*a) x);
    add_congruence (zmul a x) (zmul ((b-1)*a) x) (zmul a x) (zmul (b-1) (zmul a x));
    assert (zmul (a*b) x = zmul a x + zmul (b-1) (zmul a x));
    zmul_dec b (zmul a x);    
    assert (zmul b (zmul a x) = zmul a x + zmul (b-1) (zmul a x));
    assert (zmul (a*b) x = zmul b (zmul a x))
  end 

let zmul_ssv_assoc_neg #t {| g: add_comm_group t |} (a b:int) (x:t)
  : Lemma (requires b<0) (ensures zmul (a*b) x = zmul b (zmul a x)) (decreases abs b) =   
  let m (p:int) (q:t) = zmul p q in
  Classical.forall_intro g.add_group.add_monoid.add_semigroup.has_add.eq.reflexivity;
  Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry;
  transitivity_for_calc_proofs t;  
  zmul_ssv_assoc_nat (-a) (-b) x;
  zmul_neg_neg (-b) (zmul (-a) x);
  neg_zmul (-a) x;
  zmul_congruence b (-(zmul (-a) x)) (zmul a x)

(* Associativity for (scalar * scalar * vector) *)
let zmul_ssv_assoc  #t {| g: add_comm_group t |} (a b:int) (x:t)
  : Lemma (ensures zmul (a*b) x = zmul b (zmul a x) /\ zmul (a*b) x = zmul a (zmul b x)) = 
  if b>=0 then zmul_ssv_assoc_nat a b x else zmul_ssv_assoc_neg a b x;
  if a>=0 then zmul_ssv_assoc_nat b a x else zmul_ssv_assoc_neg b a x
  
(* Note how one symmetry call solves the issue with the right_module mirrored declaration *)
instance z_module (vector: Type) (g: add_comm_group vector) 
  : full_module vector int int_ring g =  
  Classical.forall_intro_2 g.add_group.add_monoid.add_semigroup.has_add.eq.symmetry;  
  {
    left_module = {
      s_mul_v = (fun (s:int) (v:vector) -> zmul s v);
      left_module_congruence = (fun a x y -> zmul_congruence a x y);
      ssv_associativity = (fun a b x -> zmul_ssv_assoc a b x);
      svv_distributivity = (fun a x y -> zmul_svv_distr a x y);
      ssv_distributivity = (fun a b x -> zmul_ssv_distr a b x);
    };
    right_module = {
      v_mul_s = (fun (v:vector) (s:int) -> zmul s v);
      right_module_congruence = (fun x y a -> zmul_congruence a x y);
      vss_associativity = (fun x a b -> zmul_ssv_assoc a b x);
      vvs_distributivity = (fun x y a -> zmul_svv_distr a x y);
      vss_distributivity = (fun x a b -> zmul_ssv_distr a b x);      
    };
    module_commutativity = (fun x s -> reflexivity (zmul s x))
  }
