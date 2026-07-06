module Core.Polynomial.CRT

(* ================================================================ *)
(*  Chinese Remainder Theorem for two coprime polynomial moduli.    *)
(*                                                                   *)
(*  For coprime f, g over a field, the reduction map                *)
(*    phi : t[x]/(f*g)  ->  t[x]/(f) x t[x]/(g)                      *)
(*    phi([a]) = ([a mod f], [a mod g])                             *)
(*  is a ring isomorphism.  At the divisibility level this is:       *)
(*                                                                   *)
(*  - INJECTIVITY / kernel:                                          *)
(*      coprime f g  /\  f | a  /\  g | a   ==>  (f*g) | a           *)
(*    (so a == 0 in t[x]/(fg) iff its images vanish in both          *)
(*     factors -- the kernel of phi is trivial).                     *)
(*                                                                   *)
(*  - SURJECTIVITY:                                                  *)
(*      for any targets b, c there is a with                         *)
(*        f | (a - b)   and   g | (a - c)                            *)
(*    i.e. [a] maps to ([b],[c]); via Bezout u*f + v*g ~ 1,          *)
(*        a = b*(v*g) + c*(u*f).                                     *)
(*                                                                   *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module L  = FStar.List.Tot
module TC = FStar.Tactics.Typeclasses
module H  = Core.Algebra.Helpers
module PR = Core.Polynomial.Roots
module SF = Core.Polynomial.SquareFree

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Tactics.CanonRing
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
open Core.Polynomial.Irreducible
open Core.Polynomial.PartialFraction

#set-options "--fuel 1 --ifuel 1 --z3rlimit 60"

(* Ring identities are proved over an ABSTRACT commutative_ring p
   (canon_ring reflects cleanly on a variable instance; it does NOT
   reduce the concrete polynomial_commutative_ring projections), then
   instantiated at p = polynomial t with the resolved instance. *)

let abstract_mul_assoc_swap (#p:Type) {| pr: commutative_ring p |} (g f m: p)
  : Lemma (g * (f * m) = (f * g) * m)
  = assert (g * (f * m) = (f * g) * m) by (canon_ring ())

(* with  S = bl*mf + br*mg :  [c*(bl*mf) + b*(br*mg)] - b*S = (c-b)*bl*mf. *)
let abstract_surj_identity (#p:Type) {| pr: commutative_ring p |}
  (b c bl br mf mg: p)
  : Lemma ((c * (bl * mf) + b * (br * mg)) + (- (b * (bl * mf + br * mg)))
           = ((c + (- b)) * bl) * mf)
  = assert ((c * (bl * mf) + b * (br * mg)) + (- (b * (bl * mf + br * mg)))
            = ((c + (- b)) * bl) * mf) by (canon_ring ())

(* Fully abstract CRT surjectivity over ANY commutative ring:
   given a Bezout identity  bl*mf + br*mg = one,  the witness
     w = c*(bl*mf) + b*(br*mg)
   satisfies  mf | (w - b).   (Proved entirely with abstract ring ops
   so it transports verbatim to the polynomial ring.) *)
#push-options "--z3rlimit 100"
let abstract_crt_surj (#p:Type) {| pr: commutative_ring p |}
  (mf mg bl br b c: p)
  : Lemma (requires (bl * mf + br * mg) = one)
          (ensures  divides mf
                      ((c * (bl * mf) + b * (br * mg)) + (- b)))
  = H.elim_equatable_laws p ();
    H.trans_for_calc p ();
    let w = c * (bl * mf) + b * (br * mg) in
    let s = bl * mf + br * mg in
    (* mf | (c-b)*bl*mf  =  w - b*s  (abstract_surj_identity) *)
    abstract_surj_identity b c bl br mf mg;             (* w + neg(b*s) = ((c-b)*bl)*mf *)
    divides_refl mf;
    divides_mul_left mf ((c + (- b)) * bl) mf;          (* mf | ((c-b)*bl)*mf *)

    divides_congruence_right mf (((c + (- b)) * bl) * mf) (w + (- (b * s)));  (* mf | w - b*s *)
    (* b*s = b*one = b ; so  w + neg(b*s) = w + neg b *)

    mul_congruence b s b one;                       (* b*s = b*one *)
    H.x_mul_one b;                                         (* b*one = b *)
    transitivity (b * s) (b * one) b;               (* b*s = b *)
    neg_congruence (b * s) b;                              (* neg(b*s) = neg b *)

    add_congruence w (- (b * s)) w (- b);              (* w + neg(b*s) = w + neg b *)
    divides_congruence_right mf (w + (- (b * s))) (w + (- b))  (* mf | w + neg b *)
#pop-options

(* Polynomial ring rearrangement:  g*(f*m) ~ (f*g)*m. *)
let mul_assoc_swap (#t:Type) {| cr: commutative_ring t |} (g f m: polynomial t)
  : Lemma ((g * (f * m)) = ((f * g) * m))
  = abstract_mul_assoc_swap g f m

(* ================================================================ *)
(*  Injectivity / trivial kernel:                                    *)
(*    coprime f g  /\  f | a  /\  g | a   ==>  (f*g) | a.            *)
(* ================================================================ *)

let crt_inj (#t:Type) {| f: field t |} (mf mg a: polynomial t)
  : Lemma (requires deg mf >= 0 /\ coprime mf mg /\
                    divides mf a /\
                    divides mg a)
          (ensures  divides (mf * mg) a)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    (* g | a : a ~ g * k *)
    eliminate exists (k: polynomial t). (a = (mg * k))
    returns divides (mf * mg) a
    with _hk.
    begin
      (* f | a and a ~ g*k  ==>  f | (g*k) ~ (k*g) ==> f | (k*g) *)
      divides_congruence_right mf a (mg * k);  (* f | g*k *)
      poly_mul_commutativity mg k;                                          (* g*k ~ k*g *)
      divides_congruence_right mf (mg * k) (k * mg);  (* f | k*g *)
      euclid_lemma mf mg k;                                           (* f | k *)
      (* f | k : k ~ f * m *)
      eliminate exists (m: polynomial t). (k = (mf * m))
      returns divides (mf * mg) a
      with _hm.
      begin
        (* a ~ g*k ~ g*(f*m) ~ (f*g)*m *)

        poly_mul_congruence mg k mg (mf * m);                        (* g*k ~ g*(f*m) *)
        transitivity a (mg * k) (mg * (mf * m));       (* a ~ g*(f*m) *)
        (* g*(f*m) ~ (f*g)*m *)
        mul_assoc_swap mg mf m;
        transitivity a (mg * (mf * m)) ((mf * mg) * m);
        divides_intro (mf * mg) a m
      end
    end

(* ================================================================ *)
(*  Surjectivity:  for coprime f, g and any targets b, c there is    *)
(*  a single  a = c*(bl*mf) + b*(br*mg)  (bl,br the Bezout cofactors) *)
(*  with  f | (a - b)  and  g | (a - c).  I.e. phi([a]) = ([b],[c]). *)
(* ================================================================ *)

(* The explicit CRT witness. *)
unfold let crt_witness (#t:Type) {| f: field t |} (mf mg b c: polynomial t)
  : Pure (polynomial t)
         (requires deg mf >= 0 /\ coprime mf mg)
         (ensures fun _ -> True)
  = let bl = bezout_left  mf mg in
    let br = bezout_right mf mg in
    (c * (bl * mf)) + (b * (br * mg))

(* Bridge: in the polynomial commutative ring, the Bezout sum equals
   the ring `one`  (poly_eq ... poly_one  and  poly_one == one). *)
let bezout_sum_is_one (#t:Type) {| f: field t |} (mf mg: polynomial t)
  : Lemma (requires deg mf >= 0 /\ coprime mf mg)
          (ensures  (let bl = bezout_left  mf mg in
                     let br = bezout_right mf mg in
                     ((bl * mf) + (br * mg))
                       = one))
  = H.elim_equatable_laws (polynomial t) ();
    bezout_identity mf mg                  (* poly_eq (bl*mf+br*mg) poly_one; poly_one == one *)

#push-options "--z3rlimit 100"
let crt_surj_f (#t:Type) {| f: field t |} (mf mg b c: polynomial t)
  : Lemma (requires deg mf >= 0 /\ coprime mf mg)
          (ensures  divides mf
                      ((crt_witness mf mg b c) -- b))
  = H.elim_equatable_laws (polynomial t) ();
    let bl = bezout_left  mf mg in
    let br = bezout_right mf mg in
    let a  = crt_witness mf mg b c in
    bezout_sum_is_one mf mg;               (* (bl*mf + br*mg) = one *)
    abstract_crt_surj mf mg bl br b c;  (* mf | (w + neg b) *)
    (* w + neg b == a -- b *)
    assert (a == (c * (bl * mf)) + (b * (br * mg)))
#pop-options

(* abstract add-commutativity (for transporting the g-witness). *)
let abstract_add_comm (#p:Type) {| pr: commutative_ring p |} (x y: p)
  : Lemma (x + y = y + x)
  = assert (x + y = y + x) by (canon_ring ())

(* Symmetric statement for the second modulus. *)
#push-options "--z3rlimit 120"
let crt_surj_g (#t:Type) {| f: field t |} (mf mg b c: polynomial t)
  : Lemma (requires deg mf >= 0 /\ deg mg >= 0 /\ coprime mf mg)
          (ensures  divides mg
                      ((crt_witness mf mg b c) -- c))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    let bl = bezout_left  mf mg in
    let br = bezout_right mf mg in
    let a  = crt_witness mf mg b c in
    (* Bezout for the swapped order:  br*mg + bl*mf = one. *)
    bezout_sum_is_one mf mg;                          (* bl*mf + br*mg = one *)
    abstract_add_comm (bl * mf) (br * mg);  (* bl*mf+br*mg = br*mg+bl*mf *)
    symmetry ((bl * mf) + (br * mg))
             ((br * mg) + (bl * mf));  (* br*mg+bl*mf = bl*mf+br*mg *)
    transitivity ((br * mg) + (bl * mf))
                 ((bl * mf) + (br * mg))
                 one;                     (* br*mg + bl*mf = one *)
    (* abstract surjectivity with roles (mg, mf, br, bl, c, b):
         w' = b*(br*mg) + c*(bl*mf),   mg | (w' + neg c). *)
    abstract_crt_surj mg mf br bl c b;
    let w' = (b * (br * mg)) + (c * (bl * mf)) in
    (* w' = a  (add-commutativity) ;  hence  mg | (a + neg c) = poly_sub a c. *)
    abstract_add_comm (b * (br * mg)) (c * (bl * mf));
    assert (a == (c * (bl * mf)) + (b * (br * mg)));
    (* w' = a *)

    poly_add_congruence w' (- c) a (- c);     (* w' + neg c ~ a + neg c *)
    divides_congruence_right mg
      (w' + (- c)) (a + (- c)) (* mg | a + neg c;  a -- c == a + neg c *)
#pop-options

(* ===== merged from Core.Polynomial.CoprimeProduct - coprime-product divisibility (CRT engine) ===== *)

#set-options "--fuel 1 --ifuel 1 --z3rlimit 40"

(* ---------------------------------------------------------------- *)
(*  L1.  a|m and b|n  ==>  (a*b)|(m*n).   [pure commutative_ring]    *)
(* ---------------------------------------------------------------- *)
let divides_mul_pair (#t:Type) {| cr: commutative_ring t |} (a b m n: t)
  : Lemma (requires divides a m /\ divides b n)
          (ensures  divides (a * b) (m * n))
  = eliminate exists (k:t). eq m (a * k)
    returns divides (a * b) (m * n)
    with hk.
    eliminate exists (j:t). eq n (b * j)
    returns divides (a * b) (m * n)
    with hj.
    begin
      mul_congruence m n (a * k) (b * j);
      assert (eq ((a * k) * (b * j)) ((a * b) * (k * j))) by canon_ring ();
      transitivity (m * n) ((a * k) * (b * j)) ((a * b) * (k * j));
      divides_intro (a * b) (m * n) (k * j)
    end

(* ---------------------------------------------------------------- *)
(*  L2.  coprime m n, a|m, b|n  ==>  coprime a b.                    *)
(* ---------------------------------------------------------------- *)
let coprime_both_divisors (#t:Type) {| f: field t |} (a b m n: polynomial t)
  : Lemma (requires coprime m n /\ divides a m /\ divides b n /\
                    deg a >= 0 /\ deg b >= 0)
          (ensures  coprime a b)
  = coprime_divisor m n a;       (* coprime a n *)
    coprime_of_divisor a n b     (* coprime a b *)

(* ---------------------------------------------------------------- *)
(*  L3.  a|ff, b|ff, coprime a b  ==>  (a*b)|ff.   [via euclid]      *)
(* ---------------------------------------------------------------- *)
let pcd2 (#t:Type) {| f: field t |} (a b ff: polynomial t)
  : Lemma (requires divides a ff /\ divides b ff /\ coprime a b /\
                    deg a >= 0 /\ deg b >= 0)
          (ensures  divides (a * b) ff)
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    coprime_symmetric a b;                   (* coprime b a *)
    eliminate exists (k: polynomial t). eq ff (a * k)
    returns divides (a * b) ff
    with hk.
    begin
      (* b | ff, ff ~ a*k ~ k*a  →  b | k*a *)
      divides_congruence_right b ff (a * k);
      mul_commutativity a k;
      divides_congruence_right b (a * k) (k * a);
      (* coprime b a ∧ b | (k*a)  →  b | k *)
      euclid_lemma b a k;
      eliminate exists (j: polynomial t). eq k (b * j)
      returns divides (a * b) ff
      with hj.
      begin
        (* ff ~ a*k ~ a*(b*j) ~ (a*b)*j *)

        mul_congruence a k a (b * j);
        transitivity ff (a * k) (a * (b * j));
        mul_associativity a b j;

        transitivity ff (a * (b * j)) ((a * b) * j);
        divides_intro (a * b) ff j
      end
    end

(* ---------------------------------------------------------------- *)
(*  L4 (crux).  Divisor splitting along a coprime product:           *)
(*     g | m*n   ==>   g | gcd(g,m) * gcd(g,n).                       *)
(*                                                                   *)
(*  Bezout for each gcd:  s*g + t*m ~ gcd(g,m),  s'*g + t'*n ~ gcd(g,n).  *)
(*  Their product expands into 4 terms; three carry a factor g, and  *)
(*  the fourth is (t*t')*(m*n) which g divides by hypothesis.        *)
(* ---------------------------------------------------------------- *)

(* abstract: (s*g+t*m)*(s'*g+t'*n) = g*(...) + (t*t')*(m*n). *)
let abstract_split_identity (#p:Type) {| pr: commutative_ring p |}
  (s t s' t' g m n: p)
  : Lemma ((s * g + t * m) * (s' * g + t' * n)
           = g * (s * (s' * g) + s * (t' * n) + t * (s' * m)) + (t * t') * (m * n))
  = assert ((s * g + t * m) * (s' * g + t' * n)
            = g * (s * (s' * g) + s * (t' * n) + t * (s' * m)) + (t * t') * (m * n))
      by canon_ring ()

let divisor_splits (#t:Type) {| f: field t |} (g m n: polynomial t)
  : Lemma (requires divides g (m * n))
          (ensures  divides g ((poly_gcd g m) * (poly_gcd g n)))
  = H.elim_equatable_laws (polynomial t) ();
    H.trans_for_calc (polynomial t) ();
    ext_gcd_correct g m; ext_gcd_is_gcd g m;
    ext_gcd_correct g n; ext_gcd_is_gcd g n;
    let (s,  tt,  gv ) = poly_ext_gcd g m in   (* s*g + tt*m ~ gv ~ gcd(g,m) *)
    let (s', tt', gv') = poly_ext_gcd g n in   (* s'*g + tt'*n ~ gv' ~ gcd(g,n) *)
    let gm = poly_gcd g m in
    let gn = poly_gcd g n in
    (* lhs := the product of the two Bezout sums *)
    let lhs = (s * g + tt * m) * (s' * g + tt' * n) in
    let xmid = s * (s' * g) + s * (tt' * n) + tt * (s' * m) in
    let rhs  = g * xmid + (tt * tt') * (m * n) in
    abstract_split_identity s tt s' tt' g m n;  (* lhs = rhs *)
    (* g | rhs *)
    divides_refl g;
    divides_mul_right g g xmid;                 (* g | g*xmid *)
    divides_mul_left  g (tt * tt') (m * n);     (* g | (tt*tt')*(m*n) *)
    divides_add g (g * xmid) ((tt * tt') * (m * n));  (* g | rhs *)
    (* g | lhs  (rhs = lhs) *)

    divides_congruence_right g rhs lhs;          (* g | lhs *)
    (* lhs ~ gv*gv' ~ gm*gn *)
    mul_congruence (s * g + tt * m) (s' * g + tt' * n) gv gv';         (* lhs = gv*gv' *)
    mul_congruence gv gv' gm gn;                                       (* gv*gv' = gm*gn *)
    transitivity lhs (gv * gv') (gm * gn);                            (* lhs = gm*gn *)
    divides_congruence_right g lhs (gm * gn)     (* g | gm*gn *)

(* ---------------------------------------------------------------- *)
(*  L5.  Two-factor distribution, "B" direction (UNCONDITIONAL):     *)
(*     gcd(f, m*n)  |  gcd(f,m) * gcd(f,n).                           *)
(* ---------------------------------------------------------------- *)
let gcd_mn_divides_prod (#t:Type) {| f: field t |} (ff m n: polynomial t)
  : Lemma (divides (poly_gcd ff (m * n))
                   ((poly_gcd ff m) * (poly_gcd ff n)))
  = let g = poly_gcd ff (m * n) in
    gcd_divides_left  ff (m * n);             (* g | ff *)
    gcd_divides_right ff (m * n);             (* g | m*n *)
    divisor_splits g m n;                            (* g | gcd(g,m)*gcd(g,n) *)
    gcd_divides_left  g m;                           (* gcd(g,m) | g *)
    gcd_divides_right g m;                           (* gcd(g,m) | m *)
    divides_trans (poly_gcd g m) g ff;   (* gcd(g,m) | ff *)
    gcd_is_maximal ff m (poly_gcd g m);        (* gcd(g,m) | gcd(ff,m) *)
    gcd_divides_left  g n;
    gcd_divides_right g n;
    divides_trans (poly_gcd g n) g ff;
    gcd_is_maximal ff n (poly_gcd g n);
    divides_mul_pair
      (poly_gcd g m) (poly_gcd g n)
      (poly_gcd ff m) (poly_gcd ff n);
    divides_trans g
      ((poly_gcd g m) * (poly_gcd g n))
      ((poly_gcd ff m) * (poly_gcd ff n))

(* ---------------------------------------------------------------- *)
(*  L6.  Two-factor distribution, "A" direction (needs coprimality): *)
(*     coprime m n  ==>  gcd(f,m) * gcd(f,n)  |  gcd(f, m*n).         *)
(* ---------------------------------------------------------------- *)
let prod_divides_gcd_mn (#t:Type) {| f: field t |} (ff m n: polynomial t)
  : Lemma (requires coprime m n /\ deg ff >= 0)
          (ensures  divides ((poly_gcd ff m) * (poly_gcd ff n))
                            (poly_gcd ff (m * n)))
  = let a = poly_gcd ff m in
    let b = poly_gcd ff n in
    gcd_divides_left  ff m;   (* a | ff *)
    gcd_divides_right ff m;   (* a | m *)
    gcd_divides_left  ff n;   (* b | ff *)
    gcd_divides_right ff n;   (* b | n *)
    SF.gcd_has_degree ff m;   (* Some? deg a *)
    SF.gcd_has_degree ff n;   (* Some? deg b *)
    coprime_both_divisors a b m n;            (* coprime a b *)
    pcd2 a b ff;                              (* a*b | ff *)
    divides_mul_pair a b m n; (* a*b | m*n *)
    gcd_is_maximal ff (m * n) (a * b)  (* a*b | gcd(ff,m*n) *)

(* ---------------------------------------------------------------- *)
(*  L7.  List form of L5 (UNCONDITIONAL):                            *)
(*     gcd(f, prod ms)  |  prod_i gcd(f, ms_i).                      *)
(*  Pure induction on the list using gcd_mn_divides_prod.            *)
(* ---------------------------------------------------------------- *)
let rec gcd_prod_divides_prod_gcd (#t:Type) {| f: field t |}
  (ff: polynomial t) (ms: list (polynomial t))
  : Lemma (ensures divides (poly_gcd ff (PR.poly_prod ms))
                           (PR.poly_prod (L.map (fun m -> poly_gcd ff m) ms)))
          (decreases ms)
  = match ms with
    | [] ->
      (* poly_prod [] == poly_one ; map _ [] == [] ; gcd(ff,1) | 1 *)
      gcd_divides_right ff (poly_one #t)
    | x :: rest ->
      let pr = PR.poly_prod rest in
      let q  = PR.poly_prod (L.map (fun m -> poly_gcd ff m) rest) in
      gcd_mn_divides_prod ff x pr;            (* gcd(ff,x*pr) | gcd(ff,x)*gcd(ff,pr) *)
      gcd_prod_divides_prod_gcd ff rest;      (* IH: gcd(ff,pr) | q *)
      divides_refl (poly_gcd ff x);
      divides_mul_pair
        (poly_gcd ff x) (poly_gcd ff pr)
        (poly_gcd ff x) q;                    (* gcd(ff,x)*gcd(ff,pr) | gcd(ff,x)*q *)
      divides_trans
        (poly_gcd ff (x * pr))
        ((poly_gcd ff x) * (poly_gcd ff pr))
        ((poly_gcd ff x) * q)

(* ---------------------------------------------------------------- *)
(*  L8 (capstone, direction B).  f | prod ms  ==>  f | prod gcd.     *)
(*     f | prod ms  ==>  f | gcd(f, prod ms)  (gcd_is_maximal+refl)  *)
(*                    |  prod_i gcd(f, ms_i)   (L7).                  *)
(* ---------------------------------------------------------------- *)
let f_divides_prod_gcd (#t:Type) {| f: field t |}
  (ff: polynomial t) (ms: list (polynomial t))
  : Lemma (requires divides ff (PR.poly_prod ms))
          (ensures  divides ff (PR.poly_prod (L.map (fun m -> poly_gcd ff m) ms)))
  = divides_refl ff;
    gcd_is_maximal ff (PR.poly_prod ms) ff;     (* ff | gcd(ff, prod ms) *)
    gcd_prod_divides_prod_gcd ff ms;            (* gcd(ff, prod ms) | prod gcd *)
    divides_trans ff
      (poly_gcd ff (PR.poly_prod ms))
      (PR.poly_prod (L.map (fun m -> poly_gcd ff m) ms))

(* ---------------------------------------------------------------- *)
(*  L9.  poly_prod respects pointwise poly_eq of equal-length lists. *)
(* ---------------------------------------------------------------- *)
(* pointwise-equality witness: a proof that xs and ys agree at every in-range
   index, supplied as a per-index lemma argument rather than a `forall`
   precondition (no quantifier lands in the caller's SMT context). *)
let pointwise_eq_proof (#t:Type) {| cr: commutative_ring t |} (xs ys: list (polynomial t))
  = (i:nat{i < L.length xs /\ i < L.length ys}) -> Lemma ((L.index xs i) = (L.index ys i))

let rec poly_prod_congr (#t:Type) {| cr: commutative_ring t |}
  (xs ys: list (polynomial t))
  (proof: pointwise_eq_proof xs ys)
  : Lemma (requires L.length xs == L.length ys)
          (ensures  ((PR.poly_prod xs) = (PR.poly_prod ys)))
          (decreases xs)
  = H.elim_equatable_laws (polynomial t) ();
    match xs, ys with
    | [], [] -> reflexivity (PR.poly_prod xs)
    | x :: xs', y :: ys' ->
      proof 0;                                 (* x = y *)
      let tail (i:nat{i < L.length xs'})
        : Lemma ((L.index xs' i) = (L.index ys' i))
        = assert (L.index xs (i ++ 1) == L.index xs' i);
          assert (L.index ys (i ++ 1) == L.index ys' i);
          proof (i ++ 1)
      in
      poly_prod_congr xs' ys' tail;
      poly_mul_congruence x (PR.poly_prod xs') y (PR.poly_prod ys')

(* ---------------------------------------------------------------- *)
(*  L10.  a coprime to each ms_i  ==>  a coprime to (prod ms).       *)
(*  (public poly_prod analogue of Irreducible.coprime_flat_product.) *)
(* ---------------------------------------------------------------- *)
(* ---------------------------------------------------------------- *)
(*  "a is coprime to every element of ds" as an OPAQUE proposition,   *)
(*  with elim / proof-as-argument / intro.  Hides the `forall` so it  *)
(*  never lands in a consumer's SMT context.                          *)
(* ---------------------------------------------------------------- *)
[@@"opaque_to_smt"]
let coprime_with_all (#t:Type) {| f: field t |} (a: polynomial t) (ds: list (polynomial t))
  : prop = forall (k:nat). k < L.length ds ==> coprime a (L.index ds k)

let coprime_with_all_elim (#t:Type) {| f: field t |} (a: polynomial t)
  (ds: list (polynomial t){coprime_with_all a ds})
  : Lemma (forall (k:nat). k < L.length ds ==> coprime a (L.index ds k))
  = reveal_opaque (`%coprime_with_all) (coprime_with_all a ds)

let coprime_with_all_proof (#t:Type) {| f: field t |} (a: polynomial t) (ds: list (polynomial t))
  = (k:nat{k < L.length ds}) -> Lemma (coprime a (L.index ds k))

let coprime_with_all_intro (#t:Type) {| f: field t |} (a: polynomial t) (ds: list (polynomial t))
  (proof: coprime_with_all_proof a ds)
  : Lemma (coprime_with_all a ds)
  = reveal_opaque (`%coprime_with_all) (coprime_with_all a ds);
    let aux (k:nat) : Lemma (k < L.length ds ==> coprime a (L.index ds k))
      = if k < L.length ds then proof k else ()
    in
    Classical.forall_intro aux

#push-options "--z3rlimit 50 --fuel 3 --ifuel 2"
let rec coprime_to_prod (#t:Type) {| f: field t |}
  (a: polynomial t) (ds: list (polynomial t))
  : Lemma (requires deg a >= 0 /\ coprime_with_all a ds)
          (ensures  coprime a (PR.poly_prod ds))
          (decreases ds)
  = coprime_with_all_elim a ds;
    match ds with
    | [] ->
        coprime_reveal a (poly_one #t);
        SF.gcd_has_degree a (poly_one #t);
        gcd_divides_right a (poly_one #t);
        divides_degree_le (poly_gcd a (poly_one #t)) (poly_one #t)
    | d :: rest ->
        assert (L.index (d :: rest) 0 == d);           (* coprime a d (elim @0) *)
        let proof_rest (k:nat{k < L.length rest})
          : Lemma (coprime a (L.index rest k))
          = assert (L.index (d :: rest) (k ++ 1) == L.index rest k)
        in
        coprime_with_all_intro a rest proof_rest;
        coprime_to_prod a rest;
        coprime_mul_right a d (PR.poly_prod rest)
#pop-options
