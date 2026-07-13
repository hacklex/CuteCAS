module Core.Factor.Gauss

(* ================================================================ *)
(*  C3 · Gauss's lemma for ℤ[z].                                     *)
(*                                                                   *)
(*  primitive_mul_primitive : product of two primitive integer       *)
(*     polynomials is primitive.                                     *)
(*  content_mul             : content is multiplicative.             *)
(*                                                                   *)
(*  Elementary (no mod-p poly ring): the classic first-non-π-        *)
(*  divisible-coefficient argument + Euclid's lemma.                 *)
(*                                                                   *)
(*  Built on FStar.Math.Euclid (divides / is_gcd / is_prime /        *)
(*  euclid_prime), Core.Factor.Content (int_content / is_primitive / *)
(*  content_list_maximal / content_divides_coeff), Core.Polynomial   *)
(*  (coeff / deg_mul), Core.Polynomial.Coeff (coeff_poly_mul_named), *)
(*  Core.FinSum (sum_range).                                         *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module E  = Core.NumberTheory
module ML = FStar.Math.Lemmas
module CF = Core.Polynomial.Coeff
module R  = Core.Polynomial.Roots
module HT = Core.Polynomial.Height

open Core.Algebra
open Core.Algebra.Int
open Core.Algebra.Notation
open Core.Algebra.Combinators
open Core.Polynomial
open Core.FinSum
open Core.Factor.Content

#set-options "--fuel 1 --ifuel 1 --z3rlimit 20"

(* ================================================================ *)
(*  1.  Prime-factor existence:  n > 1  ⇒  some prime divides n.     *)
(* ================================================================ *)

let rec exists_prime_divisor (n:int)
  : Lemma (requires n > 1)
          (ensures  exists (pi:int). E.is_prime pi /\ E.divides pi n)
          (decreases n)
  = eliminate (E.is_prime n) \/ (~(E.is_prime n))
    returns (exists (pi:int). E.is_prime pi /\ E.divides pi n)
    with _hp. ( E.divides_reflexive n;
                introduce exists (pi:int). E.is_prime pi /\ E.divides pi n
                with n and () )
    and _hc. begin
      (* ~is_prime n  and  n > 1  ⇒  a proper divisor exists *)
      E.not_prime_elim n;                            (* reveal negated primality forall *)
      assert (exists (d:int). E.divides d n /\
                              ~(d = 1 \/ d = (-1) \/ d = n \/ d = (- n)));
      eliminate exists (d:int). E.divides d n /\
                                ~(d = 1 \/ d = (-1) \/ d = n \/ d = (- n))
      returns (exists (pi:int). E.is_prime pi /\ E.divides pi n)
      with _hd. begin
        let ad : int = if d >= 0 then d else - d in
        (* d <> 0 : else n = q*0 = 0, contradicting n > 1 *)
        assert (d <> 0);
        if d >= 0 then () else E.divides_opp d n;      (* divides ad n *)
        assert (E.divides ad n);
        assert (ad > 1);
        (* ad < n : ad | n, n > 0, ad > 0 ⇒ n >= ad; and ad <> n *)
        eliminate exists (qq:int). n = qq * ad
        returns (ad < n)
        with _hq. ( assert (qq >= 1);
                    ML.lemma_mult_le_right ad 1 qq;     (* 1*ad <= qq*ad = n *)
                    assert (n >= ad) );
        exists_prime_divisor ad;
        eliminate exists (pi:int). E.is_prime pi /\ E.divides pi ad
        returns (exists (pi:int). E.is_prime pi /\ E.divides pi n)
        with _hpi. ( E.divides_transitive pi ad n;
                     introduce exists (pi2:int). E.is_prime pi2 /\ E.divides pi2 n
                     with pi and () )
      end
    end

(* ================================================================ *)
(*  2.  Least index i with a decidable predicate f i = true, given   *)
(*      a witness.                                                    *)
(* ================================================================ *)

let rec find_least (f: nat -> bool) (i n j: nat)
  : Pure nat
      (requires i <= j /\ j < n /\ f j)
      (ensures  fun r -> i <= r /\ r < n /\ f r /\
                      (forall (a:nat). i <= a /\ a < r ==> f a = false))
      (decreases (n - i))
  = if f i then i
    else find_least f (i ++ 1) n j

(* ================================================================ *)
(*  3.  Divisibility through finite sums (over ℤ).                    *)
(* ================================================================ *)

let rec sum_range_divides (d: int) (g: nat -> int) (lo hi: nat)
  (pf: (a:nat{lo <= a /\ a < hi}) -> Lemma (E.divides d (g a)))
  : Lemma (ensures E.divides d (sum_range g lo hi)) (decreases hi - lo)
  = if lo >= hi then (sum_range_empty g lo hi; E.divides_0 d)
    else begin
      sum_range_unfold_left g lo hi;               (* sum = g lo + sum (lo+1) hi *)
      pf lo;
      let pf' (a:nat{(lo ++ 1) <= a /\ a < hi}) : Lemma (E.divides d (g a)) = pf a in
      sum_range_divides d g (lo ++ 1) hi pf';
      E.divides_plus (g lo) (sum_range g (lo ++ 1) hi) d
    end

(* Pull out one index i0 whose complement terms are all divisible. *)
let sum_range_pull (d: int) (g: nat -> int) (lo hi i0: nat)
  (pf: (a:nat{lo <= a /\ a < hi /\ a <> i0}) -> Lemma (E.divides d (g a)))
  : Lemma (requires lo <= i0 /\ i0 < hi /\ E.divides d (sum_range g lo hi))
          (ensures  E.divides d (g i0))
  = sum_range_split g lo i0 hi;                    (* S = A + R,   R = sum i0 hi *)
    sum_range_unfold_left g i0 hi;                 (* R = g i0 + B *)
    let pfA (a:nat{lo <= a /\ a < i0}) : Lemma (E.divides d (g a)) = pf a in
    sum_range_divides d g lo i0 pfA;               (* d | A *)
    let pfB (a:nat{(i0 ++ 1) <= a /\ a < hi}) : Lemma (E.divides d (g a)) = pf a in
    sum_range_divides d g (i0 ++ 1) hi pfB;        (* d | B *)
    let bigS = sum_range g lo hi in
    let aA   = sum_range g lo i0 in
    let bB   = sum_range g (i0 ++ 1) hi in
    E.divides_sub bigS aA d;                        (* d | (S - A) *)
    E.divides_sub (bigS - aA) bB d;                 (* d | (S - A - B) *)
    assert (bigS - aA - bB == g i0)

(* ================================================================ *)
(*  4.  Small ℤ-divisibility bridges between the `divides` relation  *)
(*      and the `%` form (used with the decidable predicate).        *)
(* ================================================================ *)

unfold let bad (p: polynomial int) (pi:int{pi <> 0}) (a: nat) : bool = coeff p a % pi <> 0

(* ~divides ⇒ bad is true. *)
let notdiv_bad (p: polynomial int) (pi:int{pi <> 0}) (a: nat)
  : Lemma (requires ~(E.divides pi (coeff p a))) (ensures bad p pi a)
  = if coeff p a % pi = 0 then E.mod_divides (coeff p a) pi else ()

(* bad = false ⇒ divides. *)
let notbad_div (p: polynomial int) (pi:int{pi <> 0}) (a: nat)
  : Lemma (requires bad p pi a = false) (ensures E.divides pi (coeff p a))
  = E.mod_divides (coeff p a) pi

(* ================================================================ *)
(*  5.  Existence of a coefficient not divisible by a prime π,        *)
(*      for a primitive polynomial.                                  *)
(* ================================================================ *)

(* If π divides every coefficient of a primitive p, then π | 1 : absurd. *)
let all_div_absurd (p: polynomial int) (pi: int)
  (pf: (i:nat{i < L.length p}) -> Lemma (E.divides pi (coeff p i)))
  : Lemma (requires is_primitive p /\ E.is_prime pi) (ensures False)
  = let pf' (i:nat{i < L.length p}) : Lemma (E.divides pi (L.index p i)) =
      pf i;
      assert (coeff p i == L.index p i)
    in
    content_list_maximal p pi pf';                 (* divides pi (content_list p) *)
    assert (content_list p == 1);                  (* is_primitive p *)
    E.is_prime_gt1 pi;                             (* expose 1 < pi (is_prime opaque) *)
    E.divides_1 pi                                 (* pi = 1 \/ pi = -1 : absurd *)

let exists_bad_index (p: polynomial int) (pi: int)
  : Lemma (requires is_primitive p /\ E.is_prime pi)
          (ensures  exists (i:nat). i < L.length p /\ ~(E.divides pi (coeff p i)))
  = let goal = exists (i:nat). i < L.length p /\ ~(E.divides pi (coeff p i)) in
    introduce ~goal ==> False
    with _hng. begin
      let pf (i:nat{i < L.length p}) : Lemma (E.divides pi (coeff p i)) =
        assert (E.divides pi (coeff p i))          (* from ~goal at index i *)
      in
      all_div_absurd p pi pf
    end

(* ================================================================ *)
(*  6.  The convolution term and the core Gauss contradiction.       *)
(* ================================================================ *)

unfold let term (p q: polynomial int) (k: nat) (i: nat) : int = coeff p i * coeff q (k - i)

let gauss_prime_contra (p q: polynomial int) (pi: int)
  : Lemma (requires is_primitive p /\ is_primitive q /\ E.is_prime pi
                    /\ E.divides pi (int_content (p * q)))
          (ensures False)
  = E.is_prime_gt1 pi;                              (* expose 1 < pi (is_prime opaque) *)
    assert (pi <> 0);
    exists_bad_index p pi;
    exists_bad_index q pi;
    eliminate exists (wp:nat). wp < L.length p /\ ~(E.divides pi (coeff p wp))
    returns False
    with _hwp.
    eliminate exists (wq:nat). wq < L.length q /\ ~(E.divides pi (coeff q wq))
    returns False
    with _hwq. begin
      notdiv_bad p pi wp;
      notdiv_bad q pi wq;
      let i0 = find_least (bad p pi) 0 (L.length p) wp in
      let j0 = find_least (bad q pi) 0 (L.length q) wq in
      let k : nat = i0 ++ j0 in
      (* coeff (p*q) k = sum_range (term p q k) 0 (len p) *)
      CF.coeff_poly_mul_named p q k (term p q k) (fun (i:nat) -> ());
      (* π | coeff (p*q) k *)
      content_divides_coeff (p * q) k;
      E.divides_transitive pi (int_content (p * q)) (coeff (p * q) k);
      (* per-index divisibility of the complement terms *)
      let pf_term (a:nat{0 <= a /\ a < L.length p /\ a <> i0})
        : Lemma (E.divides pi (term p q k a)) =
        let m : int = k - a in
        if a < i0 then begin
          assert (bad p pi a = false);              (* minimality of i0 at a < i0 *)
          notbad_div p pi a;                        (* π | coeff p a *)
          E.divides_mult_right (coeff q m) (coeff p a) pi;
          mul_commutativity (coeff q m) (coeff p a); (* term a == coeff q m * coeff p a *)
          assert (term p q k a == coeff q m * coeff p a)
        end else begin
          assert (a > i0);
          assert (m < j0);
          if m >= 0 then begin
            assert (bad q pi m = false);            (* minimality of j0 at m < j0 *)
            notbad_div q pi m                        (* π | coeff q m *)
          end else
            E.divides_0 pi;                          (* coeff q m = 0 *)
          E.divides_mult_right (coeff p a) (coeff q m) pi
        end
      in
      sum_range_pull pi (term p q k) 0 (L.length p) i0 pf_term;
      (* π | (coeff p i0 * coeff q j0) *)
      assert (term p q k i0 == coeff p i0 * coeff q j0);
      E.divides_mod (coeff p i0 * coeff q j0) pi;    (* product % pi = 0 *)
      E.euclid_prime pi (coeff p i0) (coeff q j0);   (* one factor % pi = 0 *)
      assert (bad p pi i0);                          (* coeff p i0 % pi <> 0 *)
      assert (bad q pi j0)                           (* coeff q j0 % pi <> 0 *)
    end

(* ================================================================ *)
(*  7.  Gauss's lemma:  primitive * primitive = primitive.           *)
(* ================================================================ *)

(* is_primitive p  ⇒  p is a nonempty list (deg >= 0). *)
let primitive_nonempty (p: polynomial int)
  : Lemma (requires is_primitive p) (ensures Cons? p /\ deg p >= 0)
  = match p with
    | []     -> ()                                  (* int_content [] = 0 <> 1 *)
    | _ :: _ -> ()

let primitive_mul_primitive (p q: polynomial int)
  : Lemma (requires is_primitive p /\ is_primitive q)
          (ensures  is_primitive (p * q))
  = if int_content (p * q) = 1 then ()
    else begin
      primitive_nonempty p;
      primitive_nonempty q;
      deg_mul p q;                                  (* deg (poly_mul p q) = deg p + deg q *)
      assert ((p * q) == poly_mul p q);
      assert (deg (p * q) >= 0);
      content_pos (p * q);                          (* content (p*q) > 0 *)
      int_content_nonneg (p * q);
      exists_prime_divisor (int_content (p * q));
      eliminate exists (pi:int). E.is_prime pi /\ E.divides pi (int_content (p * q))
      returns is_primitive (p * q)
      with _hpi. gauss_prime_contra p q pi
    end

(* ================================================================ *)
(*  8.  gcd scaling (localised 2-element Bézout) → content scaling.  *)
(* ================================================================ *)

(* gcd is insensitive to the sign of its second argument. *)
let gcd2_neg_right (a b: int) : Lemma (gcd2 a b == gcd2 a (- b))
  = let g  = gcd2 a b in
    let g' = gcd2 a (- b) in
    gcd2_nonneg a b;   gcd2_nonneg a (- b);
    gcd2_div_left a b;    gcd2_div_right a b;              (* g | a,  g | b  *)
    E.divides_minus g b;                                   (* g | (-b) *)
    gcd2_maximal a (- b) g;                                (* g | g' *)
    gcd2_div_left a (- b);   gcd2_div_right a (- b);       (* g' | a,  g' | (-b) *)
    E.divides_minus g' (- b);                              (* g' | b *)
    gcd2_maximal a b g';                                   (* g' | g *)
    E.divide_antisym g g'                                  (* g = g' \/ g = -g', both >= 0 *)

(* Bézout coefficients for any gcd (from the extended Euclid result). *)
let bezout_of_gcd (a b d: int)
  : Ghost (int & int) (requires E.is_gcd a b d)
                      (ensures fun rs -> (fst rs) * a + (snd rs) * b == d)
  = let (r, s, d0) = E.euclid_gcd a b in
    E.is_gcd_unique a b d0 d;
    assert (d0 = d \/ d0 = - d);
    if d0 = d then begin
      assert (r * a + s * b == d);
      (r, s)
    end else begin
      assert (d0 == - d);
      ML.neg_mul_left r a;                          (* -(r*a) = (-r)*a *)
      ML.neg_mul_left s b;                          (* -(s*b) = (-s)*b *)
      assert ((- r) * a + (- s) * b == d);
      (- r, - s)
    end

(* c·(r·a) = r·(c·a) : a nonlinear rearrangement fed to Z3. *)
let mul3_swap (c r a: int) : Lemma (c * (r * a) == r * (c * a))
  = ML.paren_mul_right c r a;
    ML.swap_mul c r;
    ML.paren_mul_right r c a

(* v = ±w with v >= 0  ⇒  v = |w| = |c|·g  (w = c·g, g >= 0). *)
let abs_finish (v c g: int)
  : Lemma (requires (v = c * g \/ v = - (c * g)) /\ v >= 0 /\ g >= 0)
          (ensures  v == HT.iabs c * g)
  = HT.iabs_mul c g

(* the is_gcd for the scaled pair, from the Bézout combination. *)
let gcd_scale_isgcd (c a b: int)
  : Lemma (requires E.is_gcd a b (gcd2 a b))
          (ensures  E.is_gcd (c * a) (c * b) (c * gcd2 a b))
  = let g = gcd2 a b in
    divides_scale c g a;                                   (* (c*g) | (c*a) *)
    divides_scale c g b;                                   (* (c*g) | (c*b) *)
    let (r, s) = bezout_of_gcd a b g in                    (* r*a + s*b = g *)
    ML.distributivity_add_right c (r * a) (s * b);
    mul3_swap c r a;   mul3_swap c s b;
    assert (c * g == r * (c * a) + s * (c * b));
    introduce forall (x:int).
        (E.divides x (c * a) /\ E.divides x (c * b)) ==> E.divides x (c * g)
    with (introduce _ ==> _ with _h.
      ( E.divides_mult_right r (c * a) x;
        E.divides_mult_right s (c * b) x;
        E.divides_plus (r * (c * a)) (s * (c * b)) x ))

(* gcd of scaled arguments = |scalar| · gcd. *)
let gcd2_scale (c a b: int)
  : Lemma (gcd2 (c * a) (c * b) == HT.iabs c * gcd2 a b)
  = gcd2_is_gcd a b;   gcd2_nonneg a b;
    gcd_scale_isgcd c a b;                                 (* is_gcd (c*a)(c*b)(c*gcd2 a b) *)
    gcd2_is_gcd (c * a) (c * b);   gcd2_nonneg (c * a) (c * b);
    E.is_gcd_unique (c * a) (c * b) (gcd2 (c * a) (c * b)) (c * gcd2 a b);
    assert (gcd2 (c * a) (c * b) = c * gcd2 a b \/ gcd2 (c * a) (c * b) = - (c * gcd2 a b));
    abs_finish (gcd2 (c * a) (c * b)) c (gcd2 a b)

(* content of the pointwise-scaled coefficient list. *)
let rec content_list_scale (c: int) (l: list int)
  : Lemma (ensures content_list (L.map (fun (x:int) -> c * x) l)
                   == HT.iabs c * content_list l)
          (decreases l)
  = match l with
    | []      -> ()
    | x :: tl ->
      content_list_scale c tl;                             (* IH on the tail *)
      gcd2_scale c x (content_list tl);
      gcd2_neg_right (c * x) (c * content_list tl)

(* ================================================================ *)
(*  9.  Content multiplicativity — divisibility direction.          *)
(*      content(p)·content(q) | content(p·q).                        *)
(* ================================================================ *)

let mul4_rearrange (a b c d: int) : Lemma ((a * b) * (c * d) == (a * c) * (b * d))
  = ML.paren_mul_right a b (c * d);                        (* (a*b)*(c*d) = a*(b*(c*d)) *)
    ML.paren_mul_right b c d;   ML.swap_mul b c;   ML.paren_mul_right c b d;
    ML.paren_mul_right a c (b * d)

let divides_mul_both (m n x y: int)
  : Lemma (requires E.divides m x /\ E.divides n y)
          (ensures  E.divides (m * n) (x * y))
  = eliminate exists (qx:int). x == qx * m
    returns E.divides (m * n) (x * y)
    with _.
    eliminate exists (qy:int). y == qy * n
    returns E.divides (m * n) (x * y)
    with _.
    begin
      mul4_rearrange qx m qy n;                            (* (qx*m)*(qy*n) = (qx*qy)*(m*n) *)
      introduce exists (qq:int). x * y == qq * (m * n)
      with (qx * qy) and ()
    end

let content_divides_mul (p q: polynomial int)
  : Lemma (E.divides (int_content p * int_content q) (int_content (p * q)))
  = let cp = int_content p in
    let cq = int_content q in
    let pq : polynomial int = p * q in
    let pf (k:nat{k < L.length pq}) : Lemma (E.divides (cp * cq) (L.index pq k)) =
      CF.coeff_poly_mul_named p q k (term p q k) (fun (i:nat) -> ());
      let pterm (a:nat{0 <= a /\ a < L.length p})
        : Lemma (E.divides (cp * cq) (term p q k a)) =
        content_divides_coeff p a;                         (* cp | coeff p a *)
        if k - a >= 0 then content_divides_coeff q (k - a) (* cq | coeff q (k-a) *)
        else E.divides_0 cq;                               (* coeff q (k-a) = 0 *)
        divides_mul_both cp cq (coeff p a) (coeff q (k - a))
      in
      sum_range_divides (cp * cq) (term p q k) 0 (L.length p) pterm;
      assert (coeff pq k == L.index pq k)
    in
    content_list_maximal pq (cp * cq) pf

(* ================================================================ *)
(* 10.  Content multiplicativity — full equality.                   *)
(* ================================================================ *)

(* index of a mapped list. *)
let rec idx_map (g: int -> int) (l: list int) (i:nat{i < L.length l})
  : Lemma (ensures (L.map_lemma g l; L.index (L.map g l) i == g (L.index l i)))
          (decreases i)
  = L.map_lemma g l;
    if i = 0 then () else idx_map g (L.tl l) (i - 1)

(* poly_eq to a scaled poly gives the scaled coefficient identity. *)
let coeff_p_scaled (p pp: polynomial int) (c: int) (a: nat)
  : Lemma (requires poly_eq p (R.poly_scale c pp))
          (ensures  (coeff p a <: int) == c * (coeff pp a <: int))
  = poly_eq_means_equal_coeffs p (R.poly_scale c pp) a;
    HT.coeff_scale c pp a

(* scaling by a nonzero integer preserves length. *)
let poly_scale_length (c: int) (r: polynomial int)
  : Lemma (requires c <> 0 /\ Cons? r)
          (ensures  L.length (R.poly_scale c r) == L.length r)
  = let s  = R.poly_scale c r in
    let nr = L.length r in
    HT.coeff_scale c r (nr - 1);                  (* coeff s (nr-1) == c * coeff r (nr-1) *)
    last_eq_index r (nr - 1);                     (* L.last r == coeff r (nr-1) *)
    assert (L.last r <> (0 <: int));              (* is_trimmed r *)
    assert (coeff s (nr - 1) <> 0);               (* c<>0, integral domain *)
    assert (L.length s >= nr);                    (* nonzero coeff at nr-1 *)
    if L.length s > nr then begin
      let ns = L.length s in
      HT.coeff_scale c r (ns - 1);                (* coeff s (ns-1) == c * coeff r (ns-1) *)
      last_eq_index s (ns - 1);                   (* L.last s == coeff s (ns-1) *)
      assert (L.last s <> (0 <: int));            (* is_trimmed s *)
      assert (coeff r (ns - 1) == 0);             (* ns-1 >= nr *)
      assert (coeff s (ns - 1) == 0)              (* contradiction *)
    end

(* convolution-factoring: coeff (p*q) k = (cp·cq)·coeff (pp*pq) k. *)
let conv_factor (p q pp pq: polynomial int) (cp cq: int) (k: nat)
  : Lemma (requires poly_eq p (R.poly_scale cp pp) /\ poly_eq q (R.poly_scale cq pq)
                    /\ L.length p == L.length pp)
          (ensures  (coeff (p * q) k <: int) == (cp * cq) * (coeff (pp * pq) k <: int))
  = CF.coeff_poly_mul_named pp pq k (term pp pq k) (fun (i:nat) -> ());
    let body : nat -> int = pointwise_mul (const (cp * cq)) (term pp pq k) in
    CF.coeff_poly_mul_named p q k body (fun (a:nat) ->
      coeff_p_scaled p pp cp a;
      (if k - a >= 0 then coeff_p_scaled q pq cq (k - a) else ());
      mul4_rearrange cp (coeff pp a) cq (coeff pq (k - a)));
    sum_range_mul_left (cp * cq) (term pp pq k) 0 (L.length p)

(* reverse divisibility:  content(p·q) | content(p)·content(q).       *)
let content_mul_divides_rev (p q: polynomial int)
  : Lemma (requires ~(p == []) /\ ~(q == []))
          (ensures  E.divides (int_content (p * q)) (int_content p * int_content q))
  = let cp   = int_content p in
    let cq   = int_content q in
    let prod = p * q in
    let pp   = primitive_part p in
    let ppq  = primitive_part q in
    content_pos p;   content_pos q;                         (* cp>0, cq>0 *)
    content_times_primitive p;   content_times_primitive q; (* poly_eq p (scale cp pp) etc *)
    primitive_part_is_primitive p;   primitive_part_is_primitive q;
    primitive_nonempty pp;   primitive_nonempty ppq;        (* pp, ppq nonempty *)
    poly_scale_length cp pp;   poly_eq_length p (R.poly_scale cp pp);   (* length p = length pp *)
    poly_scale_length cq ppq;  poly_eq_length q (R.poly_scale cq ppq);  (* (unused, symmetry) *)
    primitive_mul_primitive pp ppq;                         (* int_content (pp*ppq) = 1 *)
    let m0 : polynomial int = pp * ppq in
    let m = L.map (fun (x:int) -> (cp * cq) * x) m0 in
    content_list_scale (cp * cq) m0;                        (* content_list m = |cp*cq| * 1 *)
    L.map_lemma (fun (x:int) -> (cp * cq) * x) m0;          (* length m = length m0 *)
    assert (content_list m == cp * cq);
    let pfrev (j:nat{j < L.length m}) : Lemma (E.divides (int_content prod) (L.index m j)) =
      idx_map (fun (x:int) -> (cp * cq) * x) m0 j;          (* index m j = (cp*cq)*index m0 j *)
      conv_factor p q pp ppq cp cq j;                       (* coeff prod j = (cp*cq)*coeff m0 j *)
      content_divides_coeff prod j;                         (* content prod | coeff prod j *)
      assert ((L.index m j <: int) == (coeff prod j <: int))
    in
    content_list_maximal m (int_content prod) pfrev         (* content prod | content_list m = cp*cq *)

let nonempty_of_content (p: polynomial int)
  : Lemma (requires int_content p <> 0) (ensures ~(p == []))
  = match p with [] -> () | _ :: _ -> ()

let content_mul (p q: polynomial int)
  : Lemma (int_content (p * q) == int_content p * int_content q)
  = let cp = int_content p in
    let cq = int_content q in
    int_content_nonneg p;   int_content_nonneg q;   int_content_nonneg (p * q);
    content_divides_mul p q;                                (* (cp*cq) | content(p*q) *)
    if cp = 0 || cq = 0 then
      assert (int_content (p * q) == 0)                     (* 0 | content ⇒ content = 0 = cp*cq *)
    else begin
      nonempty_of_content p;   nonempty_of_content q;       (* p, q nonempty *)
      content_mul_divides_rev p q;                          (* content(p*q) | (cp*cq) *)
      E.divide_antisym (cp * cq) (int_content (p * q))       (* nonneg ⇒ equal *)
    end
