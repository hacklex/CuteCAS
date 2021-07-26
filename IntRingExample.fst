module IntRingExample

open AlgebraTypes
open FStar.Mul

#push-options "--ifuel 0 --fuel 0 --z3rlimit 1"

type neg = x:int{x<0}

private let prod_minus_lemma (p q: int) : Lemma ((-p)*q = -(p*q)) = ()
private let minus_prod_lemma (p q: int) : Lemma (p*(-q) = -(p*q)) = ()

private let plus_plus_lemma   (x: pos) (y: pos) : Lemma (x*y > 0) = ()
private let plus_minus_lemma  (p: neg) (q: pos) : Lemma (p*q < 0) = ()
private let minus_minus_lemma (p: neg) (q: neg) : Lemma (p*q > 0) = ()

private let minus_minus_eq_plus_plus (p q: int) : Lemma (p*q = (-p)*(-q)) = ()
private let minus_minus_is_plus (p: int) : Lemma (-(-p) = p) = () 

private let int_add : commutative_group #int = { op = (+); eq = (=); inv = op_Minus; neutral = 0 }
private let int_mul : commutative_monoid #int = { op = op_Multiply; eq = (=); inv = (fun x -> x); neutral = 1 }

private let int_mul_distributivity() : Lemma (is_fully_distributive op_Multiply (+) (=)) = ()
private let is_int_absorber x = is_absorber_of x op_Multiply (=)

private type int_absorber = absorber_of op_Multiply (=)
private type int_nonabsorber = non_absorber_of op_Multiply (=)

private let int_absorber_means_zero (p: int_absorber) : Lemma (p=0) = ()
private let int_absorber_iff_zero (p: int) : Lemma (is_int_absorber p <==> (p=0)) = ()

private let int_absorber_iff_zero_forall () : Lemma (forall (p: int). is_int_absorber p <==> (p=0)) = FStar.Classical.forall_intro int_absorber_iff_zero
private let int_nonabsorber_iff_nonzero (p: int) : Lemma (~(is_int_absorber p) <==>  p<>0) = ()
private let int_nonabsorber_iff_nonzero_forall () : Lemma (forall (x: int). (x<>0) <==> (~(is_absorber_of x op_Multiply (=)))) =
  FStar.Classical.forall_intro int_nonabsorber_iff_nonzero
  
private let abs (x: int): (t:int{(x>=0 /\ t==x) \/ (x<0 /\ t==(-x))}) = FStar.Math.Lib.abs x
private let abs_of_nonzero_is_positive_lemma (p: nonzero) : Lemma (abs p > 0) = ()
private let pos_product_is_not_less_than_factors_lemma (p: pos) (q: pos) : Lemma (p * q >= p) = FStar.Math.Lemmas.lemma_mult_le_left p 1 q

let ring_of_integers_is_domain (p q: int) : Lemma (p*q=0 <==> p=0 || q=0) = ()
let int_mul_has_no_absorber_divisors () : Lemma(has_no_absorber_divisors op_Multiply (=)) = ()
 
let one_is_unit() : Lemma (is_unit 1 op_Multiply (=)) = ()
let minus_one_is_unit() : Lemma (is_unit (-1) op_Multiply (=)) = ()

let int_unit_part (x: int) : (t: units_of int_mul.op (=){ if x<0 then t=(-1) else t=1 }) = if x<0 then (-1) else 1
let pos_unit_part_is_one (x: pos) : Lemma (int_unit_part x = 1) = ()
let neg_unit_part_is_minus_one (x: neg) : Lemma (int_unit_part x = (-1)) = ()
let int_unit_part_distributes_over_mul () : Lemma (unary_over_nonzeros_distributes_over int_unit_part op_Multiply (=)) = ()
  
let int_normal_part (x: int) : unit_normals_of op_Multiply (=) int_unit_part = abs x

let int_abs_spec : nat_function_defined_on_non_absorbers op_Multiply (=) = fun x -> if x=0 then None else Some (abs x)

let some_lemma (p: nonzero) : Lemma (int_abs_spec p <> None) = ()
let some_value (p: nonzero) : pos = Some?.v (int_abs_spec p)
let some_value_abs (a: nonzero) : Lemma (some_value a = abs a) = ()
let some_value_is_nonzero (a: nonzero) : Lemma (some_value a <> 0) = ()

let abs_lemma (p: pos) : Lemma (p = abs p) = ()
let abs_neg_lemma (p: neg) :Lemma ((-p) = abs p) = ()
let prod_abs_is_abs_prod (p q: nonzero) : Lemma ((abs p) * (abs q) = (abs (p*q))) = FStar.Math.Lib.abs_mul_lemma p q
 
let some_value_l (a: nonzero) (b: nonzero) : Lemma (some_value (a*b) >= some_value a) = 
  pos_product_is_not_less_than_factors_lemma (some_value a) (some_value b)
 
let nonabs_prod_is_nonabs (x y: (non_absorber_of op_Multiply (=))) : Lemma (~(is_absorber_of (x * y) op_Multiply (=))) = ()  

let euc_property (x y: non_absorber_of op_Multiply (=)) = Some?.v (int_abs_spec (nonabs_prod_is_nonabs x y; x * y)) >= Some?.v (int_abs_spec x)

let int_abs_q_l (x y: (non_absorber_of op_Multiply (=))) : Lemma (euc_property x y) = some_value_l x y

let int_abs_lemma() : Lemma(forall (x y: non_absorber_of op_Multiply (=)). euc_property x y) = FStar.Classical.forall_intro_2 int_abs_q_l

let int_norm : nat_function_defined_on_non_absorbers op_Multiply (=) = int_abs_spec

#push-options "--z3rlimit 5"
let int_def_lemma (x y: non_absorber_of op_Multiply (=)) 
  : Lemma (euclidean_norm_property (=) op_Multiply x y int_abs_spec) = 
  some_value_l x y;
  int_abs_q_l x y; 
  assert (euclidean_norm_property (=) op_Multiply x y int_abs_spec)
#pop-options
let int_def_forall_lemma () : Lemma (euclidean_norm_forall_property (=) op_Multiply int_abs_spec) = FStar.Classical.forall_intro_2 int_def_lemma

let int_unit_part_is_valid () : Lemma (is_unit_part_function int_unit_part) = 
  assert (is_idempotent int_unit_part (=));
  assert (yields_units int_unit_part op_Multiply (=)); 
  int_unit_part_distributes_over_mul()


let un_distr_lemma (x: int) (y: int) : Lemma ((int_normal_part x) * (int_normal_part y) = (int_normal_part (x*y)))
  = Math.Lib.abs_mul_lemma x y

let int_normal_part_is_valid() : Lemma (is_normal_part_function #int #op_Multiply #(=) int_unit_part int_normal_part) = 
  assert (is_idempotent int_normal_part (=));
  assert (yields_unit_normals op_Multiply (=) int_unit_part int_normal_part);
  Classical.forall_intro_2 un_distr_lemma;
  assert (unary_distributes_over int_normal_part op_Multiply (=))

let int_upart : unit_part_function op_Multiply (=) = int_unit_part_is_valid(); int_unit_part
let int_npart : normal_part_function int_upart = int_normal_part_is_valid(); int_normal_part 

#push-options "--z3rlimit 2" 
let int_integral_domain : integral_domain #int = 
assert (is_fully_distributive op_Multiply (+) (=));
assert (has_no_absorber_divisors op_Multiply (=));
{
  eq = (=);
  addition = int_add; 
  multiplication = int_mul; 
  unit_part_of = int_upart; 
  normal_part_of = int_npart;
  euclidean_norm = int_abs_spec;  
}
#pop-options

let int_euclidean_domain : euclidean_domain #int = 
  int_def_forall_lemma();
  int_integral_domain


  
