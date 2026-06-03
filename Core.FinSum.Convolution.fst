module Core.FinSum.Convolution

(* Public FinSum convolution (Cauchy product):
     (Σ_{i<m} f i)·(Σ_{j<n} g j) = Σ_{k<m+n} Σ_{i≤k} f i · g(k−i)
   for f,g supported on [0,m),[0,n).  Proof: pad each inner conv to the
   square [0,m+n)², rectangular sum_swap, then collapse via sum_range_shift
   and the support hypotheses. *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.FinSum

(* conv_term f g k i = f i * g (k-i)   (guarded so it is total in i) *)
let conv_term (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k i: nat) : t
  = if i <= k then f i * g (k - i) else zero

(* the k-th convolution coefficient: Σ_{i≤k} f i * g(k-i) *)
let conv_sum (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k: nat) : t
  = sum_range #t #(cr.cr_r.r_add) (conv_term f g k) 0 (Prims.op_Addition k 1)

(* beyond i=k the term vanishes *)
let conv_term_zero_high (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k i: nat)
  : Lemma (requires i > k) (ensures conv_term f g k i = (zero <: t))
  = H.elim_equatable_laws t ();
    reflexivity (zero <: t)

(* padding: summing conv_term up to any N >= k+1 gives the same conv_sum *)
let conv_extend (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (k n: nat)
  : Lemma (requires n >= Prims.op_Addition k 1)
          (ensures sum_range (conv_term f g k) 0 n = conv_sum f g k)
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let cf = conv_term f g k in
    sum_range_split cf 0 (Prims.op_Addition k 1) n;
    sum_range_all_zero cf (Prims.op_Addition k 1) n
      (fun (i: nat{Prims.op_Addition k 1 <= i /\ i < n}) -> conv_term_zero_high f g k i);
    H.x_plus_zero (sum_range cf 0 (Prims.op_Addition k 1));
    add_congruence (sum_range cf 0 (Prims.op_Addition k 1)) (sum_range cf (Prims.op_Addition k 1) n)
                   (sum_range cf 0 (Prims.op_Addition k 1)) (zero <: t);
    transitivity (sum_range cf 0 n)
                 (sum_range cf 0 (Prims.op_Addition k 1) + sum_range cf (Prims.op_Addition k 1) n)
                 (sum_range cf 0 (Prims.op_Addition k 1) + (zero <: t));
    transitivity (sum_range cf 0 n)
                 (sum_range cf 0 (Prims.op_Addition k 1) + (zero <: t))
                 (sum_range cf 0 (Prims.op_Addition k 1))

(* inner collapse: Σ_{k<n} conv_term f g k i = f i * Σ_{j<n-i} g j   (i <= n) *)
let inner_collapse (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (i n: nat)
  : Lemma (requires i <= n)
          (ensures sum_range (fun (k:nat) -> conv_term f g k i) 0 n
                 = f i * sum_range g 0 (Prims.op_Subtraction n i))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let ni : nat = Prims.op_Subtraction n i in
    let cfun : nat -> t = fun (k:nat) -> conv_term f g k i in
    let gshift : nat -> t = fun (k:nat) -> if i <= k then g (Prims.op_Subtraction k i) else (zero <: t) in
    let pm : nat -> t = pointwise_mul (const (f i)) gshift in
    let gsh2 : nat -> t = fun (j:nat) -> gshift (Prims.op_Addition j i) in
    (* split; lower part vanishes *)
    sum_range_split cfun 0 i n;
    sum_range_all_zero cfun 0 i (fun (k:nat{0 <= k /\ k < i}) -> conv_term_zero_high f g k i);
    (* upper part: cfun = pm on [i,n);  Σ pm = f i * Σ gshift *)
    sum_range_congruence cfun pm i n
      (fun (k:nat{i <= k /\ k < n}) -> reflexivity (f i * g (Prims.op_Subtraction k i)));
    sum_range_mul_left (f i) gshift i n;
    (* Σ_in gshift = Σ_0^ni g *)
    sum_range_shift gshift i 0 ni;
    sum_range_congruence gsh2 g 0 ni
      (fun (j:nat{0 <= j /\ j < ni}) -> reflexivity (g j));
    mul_congruence (f i) (sum_range gshift i n) (f i) (sum_range g 0 ni);
    (* assemble *)
    add_congruence (sum_range cfun 0 i) (sum_range cfun i n) (zero <: t) (sum_range cfun i n);
    H.zero_plus_x (sum_range cfun i n);
    transitivity (sum_range cfun 0 n)
                 (sum_range cfun 0 i + sum_range cfun i n)
                 ((zero <: t) + sum_range cfun i n);
    transitivity (sum_range cfun 0 n) (sum_range cfun i n) (f i * sum_range g 0 ni)

(* THE LEMMA: (Σ_{i<m} f)·(Σ_{j<n} g) = Σ_{k<m+n} conv_sum f g k *)
let sum_range_convolution (#t:Type) {| cr: commutative_ring t |} (f g: nat -> t) (m n: nat)
  (hf: (i:nat{i >= m}) -> Lemma (f i = (zero <: t)))
  (hg: (j:nat{j >= n}) -> Lemma (g j = (zero <: t)))
  : Lemma (sum_range f 0 m * sum_range g 0 n
         = sum_range (conv_sum f g) 0 (Prims.op_Addition m n))
  = H.elim_equatable_laws t ();
    H.trans_for_calc t ();
    let nn : nat = Prims.op_Addition m n in
    let ct2 : nat -> nat -> t = conv_term f g in
    let cg : t = sum_range g 0 n in
    let h : nat -> t = fun (i:nat) -> if i < nn then f i * sum_range g 0 (Prims.op_Subtraction nn i) else (zero <: t) in
    (* g support extension: for i<m, Σ g 0 (nn-i) = Σ g 0 n *)
    let gsupp (i:nat{i < m}) : Lemma (sum_range g 0 (Prims.op_Subtraction nn i) = cg) =
      sum_range_split g 0 n (Prims.op_Subtraction nn i);
      sum_range_all_zero g n (Prims.op_Subtraction nn i)
        (fun (j:nat{n <= j /\ j < Prims.op_Subtraction nn i}) -> hg j);
      H.x_plus_zero cg;
      add_congruence cg (sum_range g n (Prims.op_Subtraction nn i)) cg (zero <: t);
      transitivity (sum_range g 0 (Prims.op_Subtraction nn i))
                   (cg + sum_range g n (Prims.op_Subtraction nn i)) (cg + (zero <: t));
      transitivity (sum_range g 0 (Prims.op_Subtraction nn i)) (cg + (zero <: t)) cg
    in
    (* each outer term collapses: sum_range_on (swap_args ct2) 0 nn i = h i *)
    let outer_cb (i:nat{0 <= i /\ i < nn}) : Lemma (sum_range_on (swap_args ct2) 0 nn i = h i) =
      sum_range_congruence (swap_args ct2 i) (fun (k:nat) -> conv_term f g k i) 0 nn
        (fun (k:nat{0 <= k /\ k < nn}) -> reflexivity (conv_term f g k i));
      inner_collapse f g i nn;
      transitivity (sum_range (swap_args ct2 i) 0 nn)
                   (sum_range (fun (k:nat) -> conv_term f g k i) 0 nn)
                   (f i * sum_range g 0 (Prims.op_Subtraction nn i))
    in
    (* Step 1: RHS = Σ_k Σ_i ct2 k i  (square) *)
    sum_range_congruence (conv_sum f g) (sum_range_on ct2 0 nn) 0 nn
      (fun (k:nat{0 <= k /\ k < nn}) ->
         conv_extend f g k nn;
         symmetry (sum_range (conv_term f g k) 0 nn) (conv_sum f g k));
    (* Step 2: swap *)
    sum_swap ct2 0 nn 0 nn;
    (* Step 3: collapse outer terms to h *)
    sum_range_congruence (sum_range_on (swap_args ct2) 0 nn) h 0 nn outer_cb;
    (* Σ_{i<nn} h = Σ_{i<m} h + Σ_{m<=i<nn} h ; second is 0 *)
    sum_range_split h 0 m nn;
    sum_range_all_zero h m nn
      (fun (i:nat{m <= i /\ i < nn}) ->
         hf i;
         reflexivity (sum_range g 0 (Prims.op_Subtraction nn i));
         mul_congruence (f i) (sum_range g 0 (Prims.op_Subtraction nn i))
                        (zero <: t) (sum_range g 0 (Prims.op_Subtraction nn i));
         H.zero_mul_x (sum_range g 0 (Prims.op_Subtraction nn i));
         transitivity (f i * sum_range g 0 (Prims.op_Subtraction nn i))
                      ((zero <: t) * sum_range g 0 (Prims.op_Subtraction nn i)) (zero <: t));
    (* Σ_{i<m} h = (Σ_{i<m} f)·cg *)
    sum_range_congruence h (pointwise_mul f (const cg)) 0 m
      (fun (i:nat{0 <= i /\ i < m}) ->
         gsupp i;
         reflexivity (f i);
         mul_congruence (f i) (sum_range g 0 (Prims.op_Subtraction nn i)) (f i) cg);
    sum_range_mul_right f cg 0 m;
    (* assemble *)
    symmetry (sum_range f 0 m * cg) (sum_range (pointwise_mul f (const cg)) 0 m);
    transitivity (sum_range h 0 m) (sum_range (pointwise_mul f (const cg)) 0 m) (sum_range f 0 m * cg);
    H.x_plus_zero (sum_range h 0 m);
    add_congruence (sum_range h 0 m) (sum_range h m nn) (sum_range h 0 m) (zero <: t);
    transitivity (sum_range h 0 nn) (sum_range h 0 m + sum_range h m nn) (sum_range h 0 m + (zero <: t));
    transitivity (sum_range h 0 nn) (sum_range h 0 m + (zero <: t)) (sum_range h 0 m);
    transitivity (sum_range h 0 nn) (sum_range h 0 m) (sum_range f 0 m * cg);
    (* chain RHS(square)=swap=Σh=LHS ; then symmetry *)
    transitivity (sum_range (conv_sum f g) 0 nn)
                 (sum_range (sum_range_on ct2 0 nn) 0 nn)
                 (sum_range (sum_range_on (swap_args ct2) 0 nn) 0 nn);
    transitivity (sum_range (conv_sum f g) 0 nn)
                 (sum_range (sum_range_on (swap_args ct2) 0 nn) 0 nn)
                 (sum_range h 0 nn);
    transitivity (sum_range (conv_sum f g) 0 nn) (sum_range h 0 nn) (sum_range f 0 m * cg);
    symmetry (sum_range (conv_sum f g) 0 nn) (sum_range f 0 m * cg)
