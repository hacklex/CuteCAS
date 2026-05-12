module PigeonPrinciple
 
open FStar.IntegerIntervals 

open FStar.Seq

open AlgebraTypes
  
let rec contains_eq #a (eq: equivalence_relation a) (s: seq a) (x:a) : Tot bool (decreases length s)
  = if length s < 1 then false
    else eq (index s 0) x || contains_eq eq (slice s 1 (length s)) x

let pred_contains_eq #a (eq: equivalence_relation a) (s: seq a) (x:a) 
  = exists (i:under (length s)). eq x (index s i)

let tail_contains_eq #a (eq: equivalence_relation a) (s:seq a) 
                        (x:a { contains_eq eq s x /\ ~(eq x (head s)) })
  : Lemma (contains_eq eq (tail s) x) 
  = symm_lemma eq x (head s)
  
let tail_pred_contains_eq #a (eq: equivalence_relation a) (s:seq a) 
                        (x:a { pred_contains_eq eq s x /\ ~(eq x (head s)) })
  : Lemma (pred_contains_eq eq (tail s) x) 
  = 
  assert (length s > 0);
  let t = tail s in 
  assert (forall (i: under (length t)). index s (i+1) == index t i);
  eliminate exists (i: under (length s)). eq x (index s i)
  returns exists (k: under (length t)). eq x (index t k) with _.
  begin
    assert (i>0);
    assert (eq x (index s i));
    assert (index s i == index t (i-1))
  end 
  
let rec pred_contains_eq_means_contains_eq #a (eq: equivalence_relation a) (s: seq a) (x:a) 
  : Lemma (requires pred_contains_eq eq s x)
          (ensures contains_eq eq s x)
          (decreases length s) =
  symm_lemma eq x (index s 0);  
  if not(eq x (head s)) then begin
    tail_pred_contains_eq eq s x;
    pred_contains_eq_means_contains_eq eq (tail s) x
  end


let rec find (#a: Type) (s: seq a) (p: (a -> bool)) (i: under (length s))
    : Pure (option (under (length s)))
      (requires True) 
      (ensures fun x -> match x with 
                     | None -> (forall (k: nat{i <= k /\ k < length s}). p (index s k) == false)
                     | Some j -> i <= j /\ p (index s j))
      (decreases length s - i) =
  if p (index s i) then Some i 
  else if i + 1 < length s 
       then find #a s p (i + 1) 
       else None

let items_of #a (eq: equivalence_relation a) (s: seq a) = x:a { contains_eq eq s x } 
 

let rec index_eq #a (eq:equivalence_relation a) (s: seq a) (x:a { contains_eq eq s x })
  : Tot (i: nat { (i < length s) /\ 
                (x `eq` index s i) /\ 
                (forall (j: under i). not (x `eq` index s j)) }) 
        (decreases length s) 
  = if length s = 1 then begin
      symm_lemma eq x (head s);
      0
    end
    else if x `eq` index s 0 then 0 
         else begin
           tail_contains_eq eq s x; 
           let ieq = index_eq eq (tail s) x in 
           let aux (i: under (1 + ieq)) 
             : Lemma (not (x `eq` index s i)) 
             = if i > 0 
               then assert (index (tail s) (i-1) == index s i) 
           in Classical.forall_intro aux;
           1 + ieq
         end  

let co_means_pco #a  (eq: equivalence_relation a) (s: seq a) (x:a) 
  : Lemma (requires contains_eq eq s x)
          (ensures pred_contains_eq eq s x)
          =  
          reveal_opaque (`%is_symmetric) (is_symmetric eq); 
          assert (eq x (index s (index_eq eq s x)))

let rec pigeonhole #a (eq: equivalence_relation a) 
                      (all: seq a{length all > 0}) 
                      (s: seq (items_of eq all))
  : Pure (under (length s) * under (length s))
         (requires length s > length all)
         (ensures (fun (i1,i2) -> i1<i2 /\ (index s i1 `eq` index s i2)))
         (decreases length all) = 
  reveal_opaque (`%is_symmetric) (is_symmetric eq); 
  Classical.forall_intro_2
    (Classical.move_requires_2 (pred_contains_eq_means_contains_eq #a eq));       
  if length all = 1 
  then (trans_lemma eq (index s 0) (index all 0) (index s 1); (0,1))
  else begin
    let k0 = index s 0 in
    match find s (fun k -> eq k k0) 1 with
    | Some i -> symm_lemma eq (index s 0) (index s i);
               0,i
    | None ->
      let index_of_k0 = index_eq eq all k0 in //we carefully carve k0 from all
      let all_no_k0 = append (slice all 0 (index_of_k0)) (slice all (index_of_k0+1) (length all)) in
      let aux (x:items_of eq all{not (eq x k0)}) : Lemma (pred_contains_eq eq all_no_k0 x) = 
        let ieq = index_eq eq all x in 
        if ieq < index_of_k0 then begin 
          assert (index all ieq == index all_no_k0 ieq);
           
          ()
        end
        else begin   
          reveal_opaque (`%is_transitive) (is_transitive eq);
          reveal_opaque (`%is_symmetric) (is_symmetric eq); 
          symm_lemma eq (index all ieq) (index all_no_k0 (ieq-1));
          assert (index all ieq == index all_no_k0 (ieq-1)) ;
           
          ()
        end 
      in Classical.forall_intro aux; 

      let reduced_t = init #(items_of eq all_no_k0)
                           (length s - 1) 
                           (fun i -> index s (i+1))
      in
      let i1, i2 = pigeonhole eq all_no_k0 reduced_t in
      (i1+1, i2+1)
  end

let is_finite_carrier_for #a (carrier: seq a) (r: ring a) = no_duplicates r.eq carrier /\ (forall (x:a). contains_eq r.eq carrier x)

let finite_carrier_for #a (r: ring a) = s:seq a { s `is_finite_carrier_for` r }

let is_finite_ring #a (r: ring a) = exists (s: seq a). s `is_finite_carrier_for` r

let finite_ring #a (carrier: seq a) = z: ring a { carrier `is_finite_carrier_for` z }

let index_in_finite_ring #a (carrier: seq a) (fr: finite_ring carrier) (x:a) 
  : under (length carrier)
  = index_eq fr.eq carrier x

let one_of #a (r: ring a) = r.multiplication.neutral

let equal_indices_mean_equals #a (carrier: seq a) (fr: finite_ring carrier) (x y: a)
  : Lemma (requires index_in_finite_ring carrier fr x == index_in_finite_ring carrier fr y)
          (ensures fr.eq x y) = 
  let x_in_c = index carrier (index_eq fr.eq carrier x) in    
  let y_in_c = index carrier (index_eq fr.eq carrier y) in
  trans_lemma fr.eq x y_in_c y

let equal_means_equal_indices #a (carrier: seq a) (fr: finite_ring carrier) (x y: a)
  : Lemma (requires fr.eq x y)
          (ensures index_in_finite_ring carrier fr x == index_in_finite_ring carrier fr y) =
  reveal_opaque (`%no_duplicates) (no_duplicates #a fr.eq carrier);
  let i = index_in_finite_ring carrier fr x in
  let j = index_in_finite_ring carrier fr y in
  let x_in_c = index carrier i in
  let y_in_c = index carrier j in
  symm_lemma fr.eq x_in_c x;
  symm_lemma fr.eq y_in_c y;
  trans_lemma_4 fr.eq x_in_c x y y_in_c 

let nonzero_of #a (r: ring a) = x:a{not(r.eq x r.addition.neutral)}

let is_nilpotent #a (r: ring a) (x:nonzero_of r) 
  = exists (n: pos). pow r.multiplication x n `r.eq` r.addition.neutral 

let no_nilpotents #a (r: ring a) = forall (x:nonzero_of r). ~ (is_nilpotent r x)

let no_nilpotents_exist_form_check #a (r: ring a)
  : Lemma (requires no_nilpotents r)
          (ensures ~(exists (x: nonzero_of r). is_nilpotent r x)) = ()

open FStar.FunctionalExtensionality

let carrier_superset_has_duplicates #a (carrier: seq a{length carrier > 0}) (fr: finite_ring carrier) (superset: seq a)
  : Lemma (requires length superset > length carrier)
          (ensures ~(no_duplicates fr.eq superset))
          = 
  reveal_opaque (`%no_duplicates) (no_duplicates #a fr.eq carrier);
  let ac : z:seq a { length z > 0 } = carrier in

  assert (for_all (fun x -> contains_eq fr.eq carrier x) ac);
  let all : items_of fr.eq carrier = ac in

  admit();          
  ()


let get_no_nilpotents_ring_loop_size #a 
  (carrier: seq a) 
  (fr: finite_ring carrier) 
  (x:a) 
  (h: pos)
 : k:pos { pow fr.multiplication x h `fr.eq` pow fr.multiplication x (h+k) } = 
 
 
 
 admit();
 1
          
 
