module AbstractAlgebra

open FStar.Math.Lemmas

type positive_int = x:int {x>0 \/ x==0}
type euclidean_norm_value = option positive_int

let is_euclidean_norm (#a: Type) (zero: a) (f: a -> euclidean_norm_value) = 
  forall (q: a). ((f q)==None) <==> (q==zero) 

type euclidean_norm (#a: Type) (zero: a) = f:(a -> euclidean_norm_value){ is_euclidean_norm zero f }

type binary_op (a:Type) = a -> a -> a
type unary_op (a:Type) = a -> a
type predicate (a:Type) = a -> bool

noeq
type semigroup_like (#a: Type) = {  
  neutral: a;
  op : binary_op a;
  inverse : unary_op a;
}

let associative (#a:Type) (op:binary_op a) =
  forall (x y z:a). (x `op` y) `op` z == x `op` (y `op` z)
let commutative (#a:Type) (op:binary_op a) =
  forall (x y:a). x `op` y == y `op` x
let left_id_of (#a:Type) (u:a) (op:binary_op a) =
  forall (x:a). u `op` x == x
let right_id_of (#a:Type) (u:a) (op:binary_op a) =
  forall (x:a). x `op` u == x
let neutral_of (#a:Type) (u:a) (op:binary_op a) =
  (left_id_of u op) /\ (right_id_of u op)
let inverse_of (#a:Type) (u:a) (zero:a) (op:binary_op a) (inverse: unary_op a) = 
  forall (x:a). (x == zero) \/ (( x `op` (inverse x) == u) /\ ((inverse x) `op` x == u))
let distributive_left (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) =
  forall (x y z:a). x `op_mul` (y `op_add` z) == (x `op_mul` y) `op_add` (x `op_mul` z)
let distributive_right (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) =
  forall (x y z:a). (x `op_add` y) `op_mul` z == (x `op_mul` z) `op_add` (y `op_mul` z)
let fully_distributive (#a:Type) (op_mul:binary_op a) (op_add:binary_op a) =
  (distributive_left op_mul op_add) /\ (distributive_right op_mul op_add) 
let no_zero_divisors (#a:Type) (zero:a) (op_mul: binary_op a) =
  forall (x y:a). (x `op_mul` y == zero) ==> (x == zero) \/ (y == zero)
let divides (#a:Type) (op_mul: binary_op a) (x: a) (y: a) = 
  exists (z: a). z `op_mul` y == x

let inst_divides (#a:Type) (op_mul: binary_op a) (x: a) (y: a) (z:a)
  : Lemma (requires z `op_mul` y == x)
          (ensures divides op_mul x y)
  = ()
let inst_divides_2 (#a:Type) (op_mul: binary_op a) (x: a) (y: a) (z:a)
  : Lemma (requires z `op_mul` y == x)
          (ensures divides op_mul x y)
  = FStar.Classical.exists_intro (fun z -> z `op_mul` y == x) z



let is_unit (#a: Type) (u: a) (one: a) (op_mul: binary_op a) = exists (v: a). (((u `op_mul` v) == one) /\ ((v `op_mul` u) == one))
let is_zero (#a: Type) (z: a) (op_mul: binary_op a) = forall (x: a). (x `op_mul` z) == z /\ (z `op_mul` x) == z 
let are_associated (#a: Type) (p: a) (q: a) (op_mul: binary_op a) = (divides op_mul p q) /\ (divides op_mul q p) 
let is_irreducible (#a: Type) (x: a) (one: a) (op_mul: binary_op a) = (~(is_unit x one op_mul)) /\
  (forall (p q: a). (q `op_mul` p == x) ==> ((are_associated p x op_mul) /\ (is_unit q one op_mul)) \/ ((are_associated q x op_mul) /\ (is_unit p one op_mul)))
let is_prime (#a: Type) (p: a) (one: a) (op_mul: binary_op a) = (~(is_unit p one op_mul)) /\
  (forall (m n: a). (divides op_mul (m `op_mul` n) p) ==> ((divides op_mul m p) \/ (divides op_mul n p)))
  

let factorization_is_unique (#a: Type) (op_mul: binary_op a) =
  forall (x y z w : a). ((x `op_mul` y) == (z `op_mul` w)) ==> (divides op_mul w x) \/ (divides op_mul w y)  



type semigroup (#a: Type) = x:semigroup_like #a {associative x.op}
type commutative_semigroup (#a: Type) = x:semigroup #a {commutative x.op}
type monoid (#a: Type) = x:semigroup #a {neutral_of x.neutral x.op}
type commutative_monoid (#a: Type) = x:monoid #a {commutative x.op}
type group (#a: Type) = x:monoid #a {inverse_of x.neutral x.neutral x.op x.inverse}
type commutative_group (#a: Type) = x:group #a {commutative x.op}

noeq
type ring_like (#a: Type) = {
  addition: commutative_group #a;
  multiplication: p:semigroup #a { fully_distributive p.op addition.op };
  euclidean_norm: a -> euclidean_norm_value
}
let trivial_euclidean_norm (#a: Type) (zeroEl: a) (x: a) = match x with | zeroEl -> None | _ -> Some(0)

type ring (#a: Type) = x:ring_like #a { neutral_of x.multiplication.neutral x.multiplication.op } 
type commutative_ring (#a: Type) = x:ring #a { commutative x.multiplication.op }
type domain (#a: Type) = x:ring #a { no_zero_divisors x.addition.neutral x.multiplication.op }
type integral_domain (#a: Type) = x:domain #a { commutative x.multiplication.op }


let is_ideal (#a: Type) (r: ring #a) (condition: predicate a) = //soon to be renamed to 'is_nonzero_ideal'
  (condition r.addition.neutral)
  /\ (exists (inst : a). (condition inst) /\ ~(inst == r.addition.neutral)) 
  /\ ( forall (x : a). (condition x) ==> (condition (r.addition.inverse x))) 
  /\ ( forall (x y: a). (condition x) ==> (condition (r.multiplication.op x y)))
  /\ ( forall (x y: a). ((condition x) /\ (condition y)) ==> (condition (r.addition.op x y)))

type ideal_predicate (#a:Type) (r: ring #a) = pred : (predicate a){is_ideal r pred}
  
let ideal_negate_lemma (#a: Type) (r: ring #a) (condition: (predicate a){is_ideal r condition}) (element: a{condition element}) : Lemma  
  (ensures (condition (r.addition.inverse element))) = ()

let ideal_sum_part_lemma (#a: Type) (r: ring #a) (pred: ideal_predicate r) (x: a) (y: a) (sum: a)  
  : Lemma 
    (requires ((sum == (r.addition.op x y)) /\ pred sum /\ pred x))
    (ensures (pred y)) = ()
 
let ideal_is_principal (#a: Type) (r: ring #a) (condition: predicate a) (element: a) = 
  (is_ideal r condition) /\ (forall (x : a). (condition x) ==> (exists (y: a). (r.multiplication.op element y) == x)      )

let is_principal_ideal (#a: Type) (r: ring #a) (condition: predicate a) = 
  (is_ideal r condition) /\ (exists (generator: a). ((condition generator) /\ (ideal_is_principal r condition generator)))

type principal_ideal_domain (#a: Type) = x:integral_domain #a { forall (pred: predicate a). (is_ideal x pred) ==> (is_principal_ideal x pred) }

type unique_factorization_domain (#a: Type) = x:integral_domain #a { factorization_is_unique x.multiplication.op }
type euclidean_domain (#a: Type) = x:unique_factorization_domain #a { is_euclidean_norm x.addition.neutral x.euclidean_norm }
type field (#a: Type) = x:euclidean_domain #a { inverse_of x.multiplication.neutral x.addition.neutral x.multiplication.op x.multiplication.inverse }

let string_cat (a: string) (b: string) = String.concat a [b]
let string_cat_monoid : semigroup_like = { neutral = ""; op = string_cat; inverse = fun x -> x }

let int_add (a: int) (b: int) = a+b
let int_mul (a: int) (b: int) = op_Multiply a b
let int_inverse (a: int) = 0-a

let fd_mul_add : squash (fully_distributive int_mul int_add) = assert (fully_distributive int_mul int_add)
let integers_have_no_zero_divisors : squash (no_zero_divisors 0 int_mul) = assert (no_zero_divisors 0 int_mul)
let integers_abs : (a: int) -> euclidean_norm_value = fun a -> if a<>0 then Some (if a<0 then -a else a) else None
let integers_add : commutative_group = { neutral = 0; op = int_add; inverse=int_inverse }
let integers_multiply = { neutral = 1; op = int_mul; inverse=int_inverse }

let integers_domain : integral_domain = { addition = integers_add; multiplication = integers_multiply; euclidean_norm = integers_abs  }
let z_ring : ring #int = integers_domain

let div_rem (x:int{x>=0}) (y:int{y>0}) : ( pair: ( (a: int{a>=0})*(b:int{b>=0/\b<y }) ) {  x=(( (fst pair)  `op_Multiply` y)+(snd pair))   })  = (x/y , x%y) 

let div_rem_existence (modulo: int{modulo > 0}) (element: int{element>=modulo}) : Lemma
  (ensures (exists (p q: int). element=((p `op_Multiply` modulo)+q))) 
  = 
    let (p,q) = (div_rem element modulo) in
    let _ = (assert ( element = ((p `op_Multiply` modulo)+q))) in
    ()


let any_nat_subset_has_minimum (pred: predicate int) (any_positive: pos)
  : Lemma    
    (requires (pred any_positive))
    (ensures (exists (q: pos{pred q}). (forall (s: pos). (pred s) ==> (s >= q)) ))
  = 
    let p = any_positive in    
    let rec min_val (n: nat{n<=p}) (cur_min: pos{(pred cur_min)/\(cur_min>=n) /\ (forall (s:pos). s > n /\ s < cur_min ==> not (pred s))}) 
      : (q:pos{(pred q)/\(q<=cur_min) /\ (forall (s:pos). s < q ==> not (pred s))}) =
        if (n=0) then cur_min
        else if (pred n) 
        then min_val (n-1) n 
        else min_val (n-1) cur_min 
    in      
    let mv = (min_val p p) in
    () //www


let any_int_subset_has_minimum_positive (pred: predicate int) 
  : Lemma    
    (requires (exists (any_positive: int{any_positive>0}). (pred any_positive)))
    (ensures (exists (q: int{pred q /\ q>0}). (forall (s: pos). (pred s) ==> (s >= q)) ))
  = 
    assert (exists (p: int{(p>0) && (pred p)}). p>0); 
    let p = FStar.IndefiniteDescription.indefinite_description_ghost (x:int{(x>0) && (pred x)}) (fun x -> true) in
    
    let rec min_val (n: int{n<=p /\ n>=0}) (cur_min: int{(pred cur_min)/\(cur_min>=n)/\(cur_min>0) /\ (forall (s:int). s > n /\ s < cur_min ==> not (pred s))}) 
      : (q:int{(q>0)/\(pred q)/\(q<=cur_min) /\ (forall (s:int{s>0}). s < q ==> not (pred s))}) =
        if (n=0) then cur_min
        else (
              assert((n-1)>=0);              
              let ntot : (x:int{x>=0 /\ x<=p}) = (n-1) in
              let _ = assert(n>0) in
              let _ = assert(n<=p) in
              
              if (pred n) 
              then min_val ntot n 
              else min_val ntot cur_min)
    in      
    let mv = (min_val p p) in
    ()
 

let any_nat_subset_has_minimum2 (pred: predicate int) 
  : Lemma    
    (requires (exists (any_positive: pos). (pred any_positive)))
    (ensures (exists (q: pos{pred q}). (forall (s: pos). (pred s) ==> (s >= q)) ))
  = 
    assert (exists (p: pos{pred p}). p>0); 
    let p = FStar.IndefiniteDescription.indefinite_description_ghost (x:pos{pred x}) (fun p -> true) in

    let rec min_val (n: nat{n<=p}) (cur_min: pos{(pred cur_min)/\(cur_min>=n) /\ (forall (s:pos). s > n /\ s < cur_min ==> not (pred s))}) 
      : (q:pos{(pred q)/\(q<=cur_min) /\ (forall (s:pos). s < q ==> not (pred s))}) =
        if (n=0) then cur_min
        else if (pred n) 
        then min_val (n-1) n 
        else min_val (n-1) cur_min 
    in      
    let mv = (min_val p p) in
    ()
    
let even : predicate int = fun x -> x % 2 = 0
 
let even_negation_holds (x: int)
  : Lemma 
    (requires (even x))
    (ensures (even (int_inverse x)))
  = 
    assert (even x);
    assert ((x%2)=0);
    let mx = ((-1) `op_Multiply` x) in
    assert ((mx%2)=0);
    assert (even mx);
    ()
    
let all_z_ideals_are_principal : squash ( (forall (p: predicate int). ( (is_ideal integers_domain p) ==> (is_principal_ideal integers_domain p) ) ) ) =
  let aux (int_pred: predicate int)
    : Lemma
      (requires (is_ideal integers_domain int_pred))
      (ensures (is_principal_ideal integers_domain int_pred))
      [SMTPat (is_ideal integers_domain int_pred)] //this tells F* to automatically apply lemma for any `int_pred` for which `is_ideal integers_domain int_pred` is derivable
    =

      let pos_log (x:int) = (int_pred x) /\ (x>0) in
      let pos_mem (x: int) = (int_pred x) && (x>0) in 
      let positive_member (x : int) = (int_pred x) && (x > 0) in            
      let any_nonzero_member (x: int) = (int_pred x) /\ ~(x==0) in
        
      assert (exists (x: int). (any_nonzero_member x)); 
      let existing_nonzero : (x:int{x<>0})  = FStar.IndefiniteDescription.indefinite_description_ghost int (fun x -> ( (any_nonzero_member x) )) in

      
      let existing_pos : (f: int{int_pred f /\ f>0}) = if existing_nonzero < 0 then (integers_domain.multiplication.op (-1) existing_nonzero) else existing_nonzero in
      assert (any_nonzero_member existing_pos);      
      assert (existing_pos > 0);      
      assert (positive_member existing_pos);      
      assert (exists (positive: int). (pos_log positive));       
      assert (is_ideal integers_domain int_pred);  
      let existing_positive = FStar.IndefiniteDescription.indefinite_description_ghost int (fun x -> (pos_log x)) in      
      assert (existing_positive > 0);
      assert (int_pred existing_positive);      
      assert (exists (any_positive: int{any_positive>0}). (int_pred any_positive));
      (any_int_subset_has_minimum_positive (fun (x:int) -> int_pred x) );
      //I'm not sure how you intend to prove this assertion      
      assert (exists (min_positive: int{pos_mem min_positive}). ((forall (y: int{y>0}). (pos_mem y) ==> (y >= min_positive)) ) );   
      
      //But, if you do, you get get your hands on the min_positive witness by using this library function
      let min_positive =
        FStar.IndefiniteDescription.indefinite_description_ghost
          (x:int{pos_mem x})
          (fun (min_positive : int{pos_mem min_positive}) -> ( (forall (y: int). (pos_mem y) ==> (y >= min_positive)) ))
      in      
      
      let pos_divided_by_min_pos(element: int{element>0}) : Lemma
        (requires (int_pred element))
        (ensures (divides integers_domain.multiplication.op element min_positive)) 
        =
          assert (forall (p: int{p>=0 /\ p<min_positive}). (int_pred p) ==> p=0);          
          assert (element > 0);
          assert (int_pred element);            
          assert (pos_log element);
          assert (min_positive > 0);
          assert (element >= min_positive);       
          let _ = div_rem_existence min_positive element in     
          let (q,r) = div_rem element min_positive in
          assert (q>=0);
          assert (r>=0);
          assert ( ((q `op_Multiply` min_positive)+r) = element);
          assert ( (q `op_Multiply` min_positive)=(integers_domain.multiplication.op q min_positive));
          assert (int_pred min_positive);
          let incomplete_product = (integers_domain.multiplication.op min_positive q) in
            
          assert (int_pred integers_domain.addition.neutral);
          let _ = assert (is_ideal integers_domain int_pred) in 
          assert (forall (x y: int). (int_pred x) ==> (int_pred (integers_domain.multiplication.op x y)));
          admit();
          admit();
          assert (int_pred min_positive);
          assert (int_pred incomplete_product);
          admit();
          assert (int_pred (incomplete_product+r));
          assert (element = (incomplete_product+r));
          admit();
          assert (int_pred (r));
          assert ((r < min_positive) /\ (r >= 0)); //first by definition of /, second by definition of %           
           


          assert (r == 0); // the only valid value for r after dividing by min_positive is 0
          assert (element == (q `op_Multiply` min_positive));          
          () in 

 
      //assert ( forall (x y: int). int_pred x /\ int_pred y ==> int_pred (integers_domain.multiplication.op (-1) y) );

      admit();
      let this_one_is_principal : squash (ideal_is_principal z_ring int_pred min_positive) = 
          let divided_by_min_positive (element: int) : Lemma 
            (requires (int_pred element))
            (ensures (exists (t:int). element == ( t `op_Multiply` min_positive))) =
              

          () in 

          let any_ideal_elem_is_generated_by_min_positive : squash ( forall (w: int). (int_pred w) ==> (exists (t: int). ( w == ( t `op_Multiply` min_positive) ) ) ) =
            //if w=0, then t=0, probably auto-proven anyway
            assert (exists (z: int). (pos_log z) );
            let z = FStar.IndefiniteDescription.indefinite_description_ghost int (fun z -> pos_log z) in
            assert (z >= min_positive);
            let q = (z / min_positive) in
            let r = (z % min_positive) in //z = min_positive*q + r
            assert ((r < min_positive) /\ (r >= 0)); //first by definition of /, second by definition of %
            
            assert (r == 0); // the only valid value for r after dividing by min_positive is 0
            admit();
            assert (z == (q `op_Multiply` min_positive))
          in
          admit ()
      in
      ()
  in
  ()



let even_is_preserved = assert ( forall (x y: int). (((x+y)%2) = (((x%2)+(y%2))%2)) )

let even_zero_p = assert (forall (x y: int). (((x%2)=0) /\ ((y%2)=0)) ==> (((x+y)%2)=0) )

let even_has_nonzeros () : Lemma (ensures (exists (two: int). (even two)/\~(two==0)))
  = assert ((even 2) /\ ~(2==0)) 

let even_contains_zero () : Lemma (ensures (even z_ring.addition.neutral)) = ()

let even_contains_neg (x: int) : Lemma 
  (requires (even x)) 
  (ensures (even (z_ring.addition.inverse x))) 
  [SMTPat((z_ring.addition.inverse x))]
  = 
    let _ = even_negation_holds x in
    assert ((-x)=(z_ring.addition.inverse x));
  ()

let even_preserves_under_add (x y: int) 
  : Lemma
    (requires ((even x) /\ (even y)))
    (ensures even (x+y))
    [SMTPat((z_ring.addition.op x y))]
  = 
    assert (even x);
    assert ((y%2)=0);
    FStar.Math.Lemmas.lemma_mod_add_distr x y 2;
    assert (((x+y)%2)=0);
    assert_norm (z_ring.addition.op x y == x+y)    

let even_preserves_under_mul (x y: int)
  : Lemma
    (requires even x)
    (ensures even (z_ring.multiplication.op x y))
    [SMTPat ((z_ring.multiplication.op x y))] //hint to tell Z3 how to instantiate x,y
  = let open FStar.Mul in
    assert ((x % 2) = 0);
    FStar.Math.Lemmas.lemma_mod_mul_distr_l x y 2;    
    assert ((x * y) % 2 = 0);
    assert_norm (z_ring.multiplication.op x y == x * y) //tells F* to prove this by just reduction
 
let even_is_ideal = assert (is_ideal z_ring even) 
 
