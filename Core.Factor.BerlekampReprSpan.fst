module Core.Factor.BerlekampReprSpan

(* ================================================================ *)
(*  B.3 const-shift closure + poly_of_vec linearity + the RAW-vector *)
(*  B.1/B.2 bridge + candidate-in-kernel + span.  Representation     *)
(*  (sections 0-4) lives in Core.Factor.BerlekampRepr.               *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L   = FStar.List.Tot
module NS  = Core.LinearAlgebra.FpNullSpace
module BF  = Core.Factor.BerlekampFactor
module FM  = Core.Factor.FrobeniusMatrix
module BC3 = Core.Factor.BerlekampComplete3
module CM  = Core.Algebra.CongruenceMod
module CS  = Core.Polynomial.Coeff
module IR  = Core.Polynomial.Irreducible
module H   = Core.Algebra.Helpers
module EU  = Core.NumberTheory

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Polynomial
open Core.Polynomial.Div
open Core.FinSum
open Core.Algebra.Combinators
open Core.Modular.PrimeField
open Core.Tactics.CanonRing
open Core.Factor.BerlekampRepr

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  5.  B.3 — const-shift closure + poly_of_vec linearity bridges.  *)
(* ================================================================ *)

module BK = Core.Modular.PrimeField.Berlekamp

(* const-shift respects poly_eq of the argument. *)
let const_shift_congr (p:int{EU.is_prime p}) (g x x': polynomial (fp p))
  : Lemma (requires x = x' /\ BK.kernel_is_const_shifted p g x)
          (ensures  BK.kernel_is_const_shifted p g x')
  = H.elim_equatable_laws (polynomial (fp p)) ();
    BK.kernel_is_const_shifted_elim p g x;
    eliminate exists (c:fp p). divides #(polynomial (fp p)) g (x -- (poly_const #(fp p) c))
    returns BK.kernel_is_const_shifted p g x'
    with _.
    begin
      sub_congruence #(polynomial (fp p)) x (poly_const #(fp p) c) x' (poly_const #(fp p) c);
      divides_congruence_right #(polynomial (fp p)) g
        (x -- (poly_const #(fp p) c)) (x' -- (poly_const #(fp p) c));
      BK.kernel_is_const_shifted_intro p g x' c
    end

(* zero is const-shifted. *)
let const_shift_zero (p:int{EU.is_prime p}) (g: polynomial (fp p))
  : Lemma (BK.kernel_is_const_shifted p g (poly_zero #(fp p)))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    poly_const_zero #(fp p) ();                        (* poly_const (fp_zero) = poly_zero *)
    poly_eq_symmetry (poly_const #(fp p) (fp_zero p)) (poly_zero #(fp p));
    H.sub_self_zero (poly_zero #(fp p)) (poly_const #(fp p) (fp_zero p));  (* zero -- poly_const 0 = zero *)
    divides_zero #(polynomial (fp p)) g;
    poly_eq_symmetry ((poly_zero #(fp p)) -- (poly_const #(fp p) (fp_zero p))) (poly_zero #(fp p));
    divides_congruence_right #(polynomial (fp p)) g
      (poly_zero #(fp p)) ((poly_zero #(fp p)) -- (poly_const #(fp p) (fp_zero p)));
    BK.kernel_is_const_shifted_intro p g (poly_zero #(fp p)) (fp_zero p)

(* pure poly_eq bridges for const_shift_add / const_shift_scale, isolated at fuel 0. *)
private
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let const_add_bridge (#p:int{EU.is_prime p}) (a b pca pcb pcab : polynomial (fp p))
  : Lemma (requires pcab = (pca + pcb))
          (ensures  ((a -- pca) + (b -- pcb)) = ((a + b) -- pcab))
  = ring_2x2_sub #(polynomial (fp p)) a pca b pcb;             (* (a--pca)+(b--pcb) = (a+b)--(pca+pcb) *)
    poly_eq_symmetry pcab (pca + pcb);                          (* pca+pcb = pcab *)
    poly_eq_reflexivity (a + b);
    sub_congruence #(polynomial (fp p)) (a + b) (pca + pcb) (a + b) pcab;
    poly_eq_transitivity ((a -- pca) + (b -- pcb)) ((a + b) -- (pca + pcb)) ((a + b) -- pcab)
#pop-options

private
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let const_scale_bridge (#p:int{EU.is_prime p}) (ps a pca psca : polynomial (fp p))
  : Lemma (requires psca = (ps * pca))
          (ensures  (ps * (a -- pca)) = ((ps * a) -- psca))
  = mul_sub_left #(polynomial (fp p)) ps a pca;               (* ps*(a--pca) = (ps*a)--(ps*pca) *)
    poly_eq_symmetry psca (ps * pca);                          (* ps*pca = psca *)
    poly_eq_reflexivity (ps * a);
    sub_congruence #(polynomial (fp p)) (ps * a) (ps * pca) (ps * a) psca;
    poly_eq_transitivity (ps * (a -- pca)) ((ps * a) -- (ps * pca)) ((ps * a) -- psca)
#pop-options

(* const-shift is closed under +. *)
let const_shift_add (p:int{EU.is_prime p}) (g a b: polynomial (fp p))
  : Lemma (requires BK.kernel_is_const_shifted p g a /\ BK.kernel_is_const_shifted p g b)
          (ensures  BK.kernel_is_const_shifted p g (a + b))
  = BK.kernel_is_const_shifted_elim p g a;
    BK.kernel_is_const_shifted_elim p g b;
    eliminate exists (ca:fp p). divides #(polynomial (fp p)) g (a -- (poly_const #(fp p) ca))
    returns BK.kernel_is_const_shifted p g (a + b)
    with _.
    eliminate exists (cb:fp p). divides #(polynomial (fp p)) g (b -- (poly_const #(fp p) cb))
    returns BK.kernel_is_const_shifted p g (a + b)
    with _.
    begin
      let pca = poly_const #(fp p) ca in
      let pcb = poly_const #(fp p) cb in
      divides_add #(polynomial (fp p)) g (a -- pca) (b -- pcb);   (* g | ((a--pca)+(b--pcb)) *)
      poly_const_add #(fp p) ca cb;                              (* poly_const(ca+cb) = pca+pcb *)
      const_add_bridge #p a b pca pcb (poly_const #(fp p) (ca + cb));
      divides_congruence_right #(polynomial (fp p)) g
        ((a -- pca) + (b -- pcb)) ((a + b) -- (poly_const #(fp p) (ca + cb)));
      BK.kernel_is_const_shifted_intro p g (a + b) (ca + cb)
    end

(* const-shift is closed under multiplication by a constant polynomial. *)
let const_shift_scale (p:int{EU.is_prime p}) (g: polynomial (fp p))
  (s: fp p) (a: polynomial (fp p))
  : Lemma (requires BK.kernel_is_const_shifted p g a)
          (ensures  BK.kernel_is_const_shifted p g ((poly_const #(fp p) s) * a))
  = BK.kernel_is_const_shifted_elim p g a;
    eliminate exists (ca:fp p). divides #(polynomial (fp p)) g (a -- (poly_const #(fp p) ca))
    returns BK.kernel_is_const_shifted p g ((poly_const #(fp p) s) * a)
    with _.
    begin
      let pca = poly_const #(fp p) ca in
      let ps  = poly_const #(fp p) s in
      divides_mul_left #(polynomial (fp p)) g ps (a -- pca);     (* g | ps * (a -- pca) *)
      poly_const_mul #(fp p) s ca;                              (* poly_const(s*ca) = ps*pca *)
      const_scale_bridge #p ps a pca (poly_const #(fp p) (s * ca));
      divides_congruence_right #(polynomial (fp p)) g
        (ps * (a -- pca)) ((ps * a) -- (poly_const #(fp p) (s * ca)));
      BK.kernel_is_const_shifted_intro p g ((poly_const #(fp p) s) * a) (s * ca)
    end

(* ---- poly_of_vec linearity ---- *)

let poly_of_vec_zeros (p:int{EU.is_prime p}) (cols:nat)
  : Lemma (FM.poly_of_vec (NS.zeros #p cols) = (poly_zero #(fp p)))
  = H.elim_equatable_laws (fp p) ();
    poly_eq_by_coeff #(fp p) (FM.poly_of_vec (NS.zeros #p cols)) (poly_zero #(fp p))
      (fun (j:nat) ->
        FM.poly_of_vec_coeff (NS.zeros #p cols) j;
        NS.get_zeros #p cols j)

let poly_of_vec_zip_add (p:int{EU.is_prime p}) (a b: NS.vector p)
  : Lemma (requires L.length a == L.length b)
          (ensures  FM.poly_of_vec (NS.zip_add a b) = ((FM.poly_of_vec a) + (FM.poly_of_vec b)))
  = H.elim_equatable_laws (fp p) ();
    NS.zip_add_length a b;
    poly_eq_by_coeff #(fp p) (FM.poly_of_vec (NS.zip_add a b))
      ((FM.poly_of_vec a) + (FM.poly_of_vec b))
      (fun (j:nat) ->
        FM.poly_of_vec_coeff (NS.zip_add a b) j;
        FM.poly_of_vec_coeff a j;
        FM.poly_of_vec_coeff b j;
        poly_add_coeff (FM.poly_of_vec a) (FM.poly_of_vec b) j;
        if j < L.length a then NS.get_zip_add a b j
        else fp_add_zero (fp_zero p))

let poly_of_vec_vscale (p:int{EU.is_prime p}) (c: fp p) (r: NS.vector p)
  : Lemma (FM.poly_of_vec (NS.vscale c r) = ((poly_const #(fp p) c) * (FM.poly_of_vec r)))
  = H.elim_equatable_laws (fp p) ();
    NS.vscale_length c r;
    poly_eq_by_coeff #(fp p) (FM.poly_of_vec (NS.vscale c r))
      ((poly_const #(fp p) c) * (FM.poly_of_vec r))
      (fun (j:nat) ->
        FM.poly_of_vec_coeff (NS.vscale c r) j;
        FM.poly_of_vec_coeff r j;
        monomial_mul_coeff #(fp p) c 0 (FM.poly_of_vec r) j;
        if j < L.length r then NS.get_vscale c r j
        else NS.fp_mul_zero #p c)

(* the poly of a linear combination is const-shifted, given each basis
   candidate poly is const-shifted. *)
let rec comb_const_shift (p:int{EU.is_prime p}) (g: polynomial (fp p))
  (cols:nat) (pivots: list (nat & NS.vector p)) (src: NS.vector p) (frees: list nat)
  (basis_pf: (f:nat) -> Lemma (requires L.memP f frees)
               (ensures  BK.kernel_is_const_shifted p g
                           (FM.poly_of_vec (NS.build_vec cols pivots f))))
  : Lemma (ensures BK.kernel_is_const_shifted p g
                     (FM.poly_of_vec (NS.comb_of cols pivots src frees)))
          (decreases frees)
  = match frees with
    | [] ->
        poly_of_vec_zeros p cols;                    (* poly_of_vec (zeros cols) = poly_zero *)
        const_shift_zero p g;
        const_shift_congr p g (poly_zero #(fp p)) (FM.poly_of_vec (NS.comb_of cols pivots src frees))
    | f :: fs ->
        let bvf = NS.build_vec cols pivots f in
        let sb  = NS.scaled_basis cols pivots src f in    (* = vscale (get src f) bvf *)
        let cf  = NS.comb_of cols pivots src fs in
        let basis_pf2 (x:nat) : Lemma (requires L.memP x fs)
              (ensures BK.kernel_is_const_shifted p g (FM.poly_of_vec (NS.build_vec cols pivots x)))
          = basis_pf x in
        comb_const_shift p g cols pivots src fs basis_pf2;   (* const_shift (poly_of_vec cf) *)
        NS.build_vec_length cols pivots f;
        basis_pf f;                                          (* const_shift (poly_of_vec bvf) *)
        const_shift_scale p g (NS.get src f) (FM.poly_of_vec bvf);
        poly_of_vec_vscale p (NS.get src f) bvf;             (* poly_of_vec sb = ps * poly_of_vec bvf *)
        poly_eq_symmetry (FM.poly_of_vec sb)
          ((poly_const #(fp p) (NS.get src f)) * (FM.poly_of_vec bvf));
        const_shift_congr p g ((poly_const #(fp p) (NS.get src f)) * (FM.poly_of_vec bvf))
          (FM.poly_of_vec sb);                               (* const_shift (poly_of_vec sb) *)
        NS.vscale_length (NS.get src f) bvf;
        NS.comb_of_length cols pivots src fs;
        poly_of_vec_zip_add p sb cf;
        const_shift_add p g (FM.poly_of_vec sb) (FM.poly_of_vec cf);
        poly_eq_symmetry (FM.poly_of_vec (NS.zip_add sb cf))
          ((FM.poly_of_vec sb) + (FM.poly_of_vec cf));
        const_shift_congr p g ((FM.poly_of_vec sb) + (FM.poly_of_vec cf))
          (FM.poly_of_vec (NS.comb_of cols pivots src frees))

(* ================================================================ *)
(*  6.  B.4 helpers — mem_check completeness, round trips, transport.*)
(* ================================================================ *)

(* pure poly_eq bridge  x = (d+r)  ==>  x -- d = r , isolated at fuel 0. *)
private
#push-options "--fuel 0 --ifuel 0 --z3rlimit 20"
let sub_cancel_bridge (#p:int{EU.is_prime p}) (x d r : polynomial (fp p))
  : Lemma (requires x = (d + r))
          (ensures  (x -- d) = r)
  = add_sub_cancel #(polynomial (fp p)) d r;                (* (d+r)--d = r *)
    poly_eq_reflexivity d;
    sub_congruence #(polynomial (fp p)) x d (d + r) d;       (* x--d = (d+r)--d *)
    poly_eq_transitivity (x -- d) ((d + r) -- d) r
#pop-options

(* a Berlekamp poly passes the decidable membership filter. *)
let mem_check_complete (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (h: polynomial (fp p))
  : Lemma (requires CM.cong #(polynomial (fp p)) fbar (poly_power #(fp p) h (p <: nat)) h)
          (ensures  BF.berlekamp_mem_check p fbar h)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let x  = (poly_power #(fp p) h (p <: nat)) -- h in
    let r  = poly_rem x fbar in
    let dv = fst (poly_divmod #(fp p) x fbar) in
    (* x = fbar*dv + r *)
    assert (x = ((fbar * dv) + r));
    CM.cong_reveal #(polynomial (fp p)) fbar (poly_power #(fp p) h (p <: nat)) h;  (* fbar | x *)
    divides_intro #(polynomial (fp p)) fbar (fbar * dv) dv;                        (* fbar | fbar*dv *)
    divides_sub #(polynomial (fp p)) fbar x (fbar * dv);                           (* fbar | (x -- fbar*dv) *)
    sub_cancel_bridge #p x (fbar * dv) r;                                          (* x -- fbar*dv = r *)
    divides_congruence_right #(polynomial (fp p)) fbar (x -- (fbar * dv)) r;       (* fbar | r *)
    (* deg r < deg fbar ; if deg r >= 0 => deg fbar <= deg r, contradiction => length r = 0 *)
    if deg r >= 0 then IR.divides_degree_le #(fp p) fbar r

(* the vector round trip:  vec_of_poly n (poly_of_vec v) = v  for length-n v. *)
let vec_round_trip (p:int{EU.is_prime p}) (v: NS.vector p) (n:nat)
  : Lemma (requires L.length v == n)
          (ensures  FM.vec_of_poly n (FM.poly_of_vec v) == v)
  = FM.vec_of_poly_length #p n (FM.poly_of_vec v);
    introduce forall (j:nat). j < L.length (FM.vec_of_poly n (FM.poly_of_vec v)) ==>
                NS.get (FM.vec_of_poly n (FM.poly_of_vec v)) j == NS.get v j
    with (introduce _ ==> _ with _hj.
      (FM.vec_of_poly_get #p n (FM.poly_of_vec v) j;
       FM.poly_of_vec_coeff v j));
    NS.vec_ext (FM.vec_of_poly n (FM.poly_of_vec v)) v

(* const-shift transports across a congruence g | (w - w'). *)
let const_shift_cong (p:int{EU.is_prime p}) (g w w': polynomial (fp p))
  : Lemma (requires divides #(polynomial (fp p)) g (w -- w') /\
                    BK.kernel_is_const_shifted p g w')
          (ensures  BK.kernel_is_const_shifted p g w)
  = H.elim_equatable_laws (polynomial (fp p)) ();
    BK.kernel_is_const_shifted_elim p g w';
    eliminate exists (c:fp p). divides #(polynomial (fp p)) g (w' -- (poly_const #(fp p) c))
    returns BK.kernel_is_const_shifted p g w
    with _.
    begin
      let pc = poly_const #(fp p) c in
      divides_add #(polynomial (fp p)) g (w -- w') (w' -- pc);       (* g | ((w--w') + (w'--pc)) *)
      sub_chain #(polynomial (fp p)) w w' pc;
      divides_congruence_right #(polynomial (fp p)) g ((w -- w') + (w' -- pc)) (w -- pc);
      BK.kernel_is_const_shifted_intro p g w c
    end

(* ================================================================ *)
(*  7.  RAW-VECTOR B.1 / B.2 bridge  (kernel membership stated over  *)
(*      raw null-space vectors, at the coefficient/get level, so the *)
(*      composition mat_vec_mul(T)(vec_of_poly (poly_of_vec _)) never *)
(*      forms as an SMT blob).  Then candidate-in-kernel + span.     *)
(* ================================================================ *)

(* dot of two equal-length raw vectors as a pointwise-product sum. *)
let rec dot_get_sum (p:int{EU.is_prime p}) (r v: NS.vector p)
  : Lemma (requires L.length r == L.length v)
          (ensures NS.dot r v
                   = sum_range #(fp p) (fun (i:nat) -> fp_mul (NS.get r i) (NS.get v i))
                                       0 (L.length r))
          (decreases r)
  = H.elim_equatable_laws (fp p) ();
    let f (i:nat) : fp p = fp_mul (NS.get r i) (NS.get v i) in
    match r, v with
    | [], [] -> sum_range_empty f 0 (L.length r)
    | a :: r', b :: v' ->
        dot_get_sum p r' v';
        let g (j:nat) : fp p = fp_mul (NS.get r' j) (NS.get v' j) in
        sum_range_shift f 1 0 (L.length r');
        sum_range_congruence #(fp p) (fun (j:nat) -> f (j ++ 1)) g 0 (L.length r')
          (fun (j:nat{0 <= j /\ j < L.length r'}) -> reflexivity (f (j ++ 1)));
        sum_range_unfold_left f 0 (L.length r);
        reflexivity (f 0)

(* the mT-row * coefficient sum equals  coeff (frob h) k  (the tail of B.1). *)
let sum_mT_coeff_eq (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (h: polynomial (fp p)) (k:nat)
  : Lemma (requires deg h < BF.pdeg fbar /\ k < BF.pdeg fbar)
          (ensures  sum_range #(fp p)
                      (fun (i:nat) -> (BF.mT_entry p fbar i k) * (coeff h i)) 0 (BF.pdeg fbar)
                    == coeff (FM.frob p fbar h) k)
  = H.elim_equatable_laws (fp p) ();
    let n : nat = BF.pdeg fbar in
    frob_eq_sum p fbar h n;                        (* frob h = S *)
    coeff_S p fbar h k n;                          (* coeff S k = sum gk 0 n *)
    poly_eq_means_equal_coeffs #(fp p) (FM.frob p fbar h) (sum_range (pterm p fbar h) 0 n) k;
    sum_range_congruence #(fp p)
      (fun (i:nat) -> (BF.mT_entry p fbar i k) * (coeff h i)) (gk p fbar h k) 0 n
      (fun (i:nat{0 <= i /\ i < n}) ->
        H.elim_equatable_laws (fp p) ();
        mT_entry_is_coeff p fbar i k;
        fp_mul_commutativity (BF.mT_entry p fbar i k) (coeff h i))

(* RAW B.1 at get level:  (mat_vec_mul T v)[k] = coeff (frob (poly_of_vec v)) k. *)
let mvm_get_raw (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (v: NS.vector p) (k:nat)
  : Lemma (requires L.length v == BF.pdeg fbar /\ k < BF.pdeg fbar)
          (ensures  NS.get (NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) v) k
                    == coeff (FM.frob p fbar (FM.poly_of_vec v)) k)
  = H.elim_equatable_laws (fp p) ();
    let n  : nat = BF.pdeg fbar in
    let hf : polynomial (fp p) = FM.poly_of_vec v in
    trim_length_le v;                              (* deg hf < n *)
    BF.berlekamp_matrix_T_length p fbar;
    mvm_get p (BF.berlekamp_matrix_T p fbar) v k;  (* get(mvm) k == dot (index T k) v *)
    BF.mT_rows_length p fbar 0 n;
    BF.mT_rows_index p fbar 0 n k;                 (* index T k == mT_row k 0 n *)
    BF.mT_row_length p fbar k 0 n;                 (* length (mT_row k 0 n) == n *)
    dot_get_sum p (BF.mT_row p fbar k 0 n) v;      (* dot = sum (fun i -> fp_mul (get(mT_row) i)(get v i)) 0 n *)
    sum_range_congruence #(fp p)
      (fun (i:nat) -> fp_mul (NS.get (BF.mT_row p fbar k 0 n) i) (NS.get v i))
      (fun (i:nat) -> (BF.mT_entry p fbar i k) * (coeff hf i)) 0 n
      (fun (i:nat{0 <= i /\ i < n}) ->
        H.elim_equatable_laws (fp p) ();
        BF.mT_row_length p fbar k 0 n;
        BF.mT_row_index p fbar k 0 n i;            (* get(mT_row) i == mT_entry i k *)
        FM.poly_of_vec_coeff v i;                  (* coeff hf i == get v i *)
        reflexivity (fp_mul (NS.get (BF.mT_row p fbar k 0 n) i) (NS.get v i)));
    sum_mT_coeff_eq p fbar hf k                    (* sum (mT_entry*coeff hf) == coeff (frob hf) k *)

(* RAW B.1 :  mat_vec_mul T v = vec_of_poly n (frob (poly_of_vec v)). *)
let berlekamp_matrix_represents_raw (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (v: NS.vector p)
  : Lemma (requires L.length v == BF.pdeg fbar)
          (ensures  NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) v
                    == FM.vec_of_poly (BF.pdeg fbar) (FM.frob p fbar (FM.poly_of_vec v)))
  = let n  : nat = BF.pdeg fbar in
    let hf : polynomial (fp p) = FM.poly_of_vec v in
    let lhs = NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) v in
    let rhs = FM.vec_of_poly n (FM.frob p fbar hf) in
    NS.mat_vec_mul_length (BF.berlekamp_matrix_T p fbar) v;
    BF.berlekamp_matrix_T_length p fbar;
    FM.vec_of_poly_length #p n (FM.frob p fbar hf);
    introduce forall (j:nat). j < L.length lhs ==> NS.get lhs j == NS.get rhs j
    with (introduce _ ==> _ with _hj.
      (mvm_get_raw p fbar v j;
       FM.vec_of_poly_get #p n (FM.frob p fbar hf) j));
    NS.vec_ext lhs rhs

(* RAW B.2 :  null space membership of v  <==>  Berlekamp congruence of poly_of_vec v. *)
let in_kernel_iff_berlekamp_raw (p:int{EU.is_prime p})
  (fbar: polynomial (fp p){deg fbar >= 1}) (v: NS.vector p)
  : Lemma (requires L.length v == BF.pdeg fbar)
          (ensures  (NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) v == NS.zeros (BF.pdeg fbar))
                    <==> CM.cong #(polynomial (fp p)) fbar
                           (poly_power #(fp p) (FM.poly_of_vec v) (p <: nat)) (FM.poly_of_vec v))
  = let n  : nat = BF.pdeg fbar in
    let hf : polynomial (fp p) = FM.poly_of_vec v in
    trim_length_le v;                              (* deg hf < n *)
    berlekamp_matrix_represents_raw p fbar v;      (* mvm T v == vec_of_poly n (frob hf) *)
    let hph = poly_power #(fp p) hf (p <: nat) in
    introduce CM.cong #(polynomial (fp p)) fbar hph hf ==>
              (NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) v == NS.zeros n)
    with _.
      (berlekamp_implies_frob_zero p fbar hf;
       vec_of_poly_of_zero p (FM.frob p fbar hf) n);
    introduce (NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) v == NS.zeros n) ==>
              CM.cong #(polynomial (fp p)) fbar hph hf
    with _.
      (let r = poly_rem hph fbar in
       poly_sub_degree_bound r hf n;               (* deg (frob hf) < n *)
       vec_zeros_gives_poly_zero p (FM.frob p fbar hf) n;
       frob_zero_implies_berlekamp p fbar hf)

(* a length-n null-space vector has a certified-Berlekamp poly.  Uses the
   RAW iff so the mat_vec_mul(T)(vec_of_poly(poly_of_vec _)) blob never forms. *)
#push-options "--z3rlimit 30 --fuel 1 --ifuel 0"
let bvf_certified (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (bvf: NS.vector p)
  : Lemma (requires L.length bvf == BF.pdeg fbar /\
                    NS.mat_vec_mul (BF.berlekamp_matrix_T p fbar) bvf
                      == NS.zeros (BF.pdeg fbar))
          (ensures  BF.berlekamp_mem_check p fbar (FM.poly_of_vec bvf))
  = let hf = FM.poly_of_vec bvf in
    in_kernel_iff_berlekamp_raw p fbar bvf;        (* => cong fbar (hf^p) hf *)
    mem_check_complete p fbar hf
#pop-options

(* every null-space candidate poly is an element of berlekamp_kernel. *)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"
let candidate_poly_in_kernel (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (f:nat)
  : Lemma (requires L.memP f (NS.tag_frees 0
                     (NS.classify (BF.pdeg fbar) (BF.berlekamp_matrix_T p fbar) 0)))
          (ensures  L.memP (FM.poly_of_vec (NS.build_vec (BF.pdeg fbar)
                       (NS.tag_pivots 0 (NS.classify (BF.pdeg fbar)
                          (BF.berlekamp_matrix_T p fbar) 0)) f))
                     (BF.berlekamp_kernel p fbar))
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let n = BF.pdeg fbar in
    let m = BF.berlekamp_matrix_T p fbar in
    let tags = NS.classify n m 0 in
    let pivots = NS.tag_pivots 0 tags in
    let frees = NS.tag_frees 0 tags in
    let bvf = NS.build_vec n pivots f in
    let hf = FM.poly_of_vec bvf in
    BF.berlekamp_matrix_T_all_len p fbar;
    L.memP_map_intro (NS.build_vec n pivots) f frees;         (* bvf in candidates *)
    NS.candidate_in_kernel n m bvf;                            (* in_kernel_bool m bvf *)
    L.mem_filter (NS.in_kernel_bool m) (NS.null_space_candidates n m) bvf;  (* bvf in nsb *)
    NS.build_vec_length n pivots f;                            (* length bvf = n *)
    NS.null_space_basis_in_kernel_zeros n m bvf;              (* mvm m bvf == zeros (length m) *)
    NS.mat_vec_mul_length m bvf;
    BF.berlekamp_matrix_T_length p fbar;                      (* length m = n *)
    bvf_certified p fbar bvf;                                 (* mem_check p fbar hf *)
    L.memP_map_intro (trim #(fp p)) bvf (NS.null_space_basis n m);          (* hf in map trim nsb *)
    L.mem_filter (BF.berlekamp_mem_check p fbar)
                 (L.map (trim #(fp p)) (NS.null_space_basis n m)) hf
#pop-options

(* every Berlekamp element of fbar (deg < n) is const-shifted mod g. *)
#push-options "--z3rlimit 40 --fuel 1 --ifuel 0 --split_queries always"
let span_const_shift (p:int{EU.is_prime p}) (fbar: polynomial (fp p){deg fbar >= 1})
  (g w': polynomial (fp p))
  : Lemma (requires (forall (hh: polynomial (fp p)).
                        L.memP hh (BF.berlekamp_kernel p fbar) ==>
                        BK.kernel_is_const_shifted p g hh) /\
                    CM.cong #(polynomial (fp p)) fbar (poly_power #(fp p) w' (p <: nat)) w' /\
                    deg w' < BF.pdeg fbar)
          (ensures  BK.kernel_is_const_shifted p g w')
  = H.elim_equatable_laws (polynomial (fp p)) ();
    let n = BF.pdeg fbar in
    let m = BF.berlekamp_matrix_T p fbar in
    let vec = FM.vec_of_poly n w' in
    BF.berlekamp_matrix_T_all_len p fbar;
    FM.vec_of_poly_length #p n w';
    BF.berlekamp_matrix_T_length p fbar;
    NS.mat_vec_mul_length m vec;
    in_kernel_iff_berlekamp p fbar w';                        (* mvm m vec == zeros n *)
    assert (NS.mat_vec_mul m vec == NS.zeros (L.length m));
    NS.null_space_basis_spans n m vec;                        (* vec == comb_of n pivots vec frees *)
    let tags = NS.classify n m 0 in
    let pivots = NS.tag_pivots 0 tags in
    let frees = NS.tag_frees 0 tags in
    let basis_pf (f:nat) : Lemma (requires L.memP f frees)
          (ensures BK.kernel_is_const_shifted p g (FM.poly_of_vec (NS.build_vec n pivots f)))
      = candidate_poly_in_kernel p fbar f
    in
    comb_const_shift p g n pivots vec frees basis_pf;         (* const_shift (poly_of_vec (comb_of)) *)
    FM.round_trip #p n w';                                    (* poly_of_vec vec = w' *)
    const_shift_congr p g (FM.poly_of_vec (NS.comb_of n pivots vec frees)) w'
#pop-options
