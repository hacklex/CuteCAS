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

open Core.Algebra
open Core.Algebra.Notation
open Core.Algebra.Divisibility
open Core.Tactics.CanonRing
open Core.Polynomial
open Core.Polynomial.Div
open Core.Polynomial.GCD
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
  : Lemma ((c * (bl * mf) + b * (br * mg)) + neg (b * (bl * mf + br * mg))
           = ((c + neg b) * bl) * mf)
  = assert ((c * (bl * mf) + b * (br * mg)) + neg (b * (bl * mf + br * mg))
            = ((c + neg b) * bl) * mf) by (canon_ring ())

(* Fully abstract CRT surjectivity over ANY commutative ring:
   given a Bezout identity  bl*mf + br*mg = one,  the witness
     w = c*(bl*mf) + b*(br*mg)
   satisfies  mf | (w - b).   (Proved entirely with abstract ring ops
   so it transports verbatim to the polynomial ring.) *)
#push-options "--z3rlimit 100"
let abstract_crt_surj (#p:Type) {| pr: commutative_ring p |}
  (mf mg bl br b c: p)
  : Lemma (requires (bl * mf + br * mg) = (one <: p))
          (ensures  divides mf
                      ((c * (bl * mf) + b * (br * mg)) + neg b))
  = H.elim_equatable_laws p ();
    H.trans_for_calc p ();
    let w = c * (bl * mf) + b * (br * mg) in
    let s = bl * mf + br * mg in
    (* mf | (c-b)*bl*mf  =  w - b*s  (abstract_surj_identity) *)
    abstract_surj_identity #p b c bl br mf mg;             (* w + neg(b*s) = ((c-b)*bl)*mf *)
    divides_refl #p mf;
    divides_mul_left #p mf ((c + neg b) * bl) mf;          (* mf | ((c-b)*bl)*mf *)
    symmetry (w + neg (b * s)) (((c + neg b) * bl) * mf);
    divides_congruence_right #p mf (((c + neg b) * bl) * mf) (w + neg (b * s));  (* mf | w - b*s *)
    (* b*s = b*one = b ; so  w + neg(b*s) = w + neg b *)
    reflexivity b;
    mul_congruence b s b (one <: p);                       (* b*s = b*one *)
    H.x_mul_one b;                                         (* b*one = b *)
    transitivity (b * s) (b * (one <: p)) b;               (* b*s = b *)
    neg_congruence (b * s) b;                              (* neg(b*s) = neg b *)
    reflexivity w;
    add_congruence w (neg (b * s)) w (neg b);              (* w + neg(b*s) = w + neg b *)
    divides_congruence_right #p mf (w + neg (b * s)) (w + neg b)  (* mf | w + neg b *)
#pop-options

(* Polynomial ring rearrangement:  g*(f*m) ~ (f*g)*m. *)
let mul_assoc_swap (#t:Type) {| cr: commutative_ring t |} (g f m: polynomial t)
  : Lemma (poly_eq (poly_mul g (poly_mul f m)) (poly_mul (poly_mul f g) m))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    abstract_mul_assoc_swap #(polynomial t) #cr_p g f m

(* ================================================================ *)
(*  Injectivity / trivial kernel:                                    *)
(*    coprime f g  /\  f | a  /\  g | a   ==>  (f*g) | a.            *)
(* ================================================================ *)

let crt_inj (#t:Type) {| f: field t |} (mf mg a: polynomial t)
  : Lemma (requires Some? (poly_deg mf) /\ coprime mf mg /\
                    (let cr_p : commutative_ring (polynomial t) = TC.solve in
                     divides #(polynomial t) #cr_p mf a /\
                     divides #(polynomial t) #cr_p mg a))
          (ensures  (let cr_p : commutative_ring (polynomial t) = TC.solve in
                     divides #(polynomial t) #cr_p (poly_mul mf mg) a))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    H.trans_for_calc (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    (* g | a : a ~ g * k *)
    eliminate exists (k: polynomial t). poly_eq a (poly_mul mg k)
    returns divides #(polynomial t) #cr_p (poly_mul mf mg) a
    with _hk.
    begin
      (* f | a and a ~ g*k  ==>  f | (g*k) ~ (k*g) ==> f | (k*g) *)
      divides_congruence_right #(polynomial t) #cr_p mf a (poly_mul mg k);  (* f | g*k *)
      poly_mul_commutativity mg k;                                          (* g*k ~ k*g *)
      divides_congruence_right #(polynomial t) #cr_p mf (poly_mul mg k) (poly_mul k mg);  (* f | k*g *)
      euclid_lemma #t #f mf mg k;                                           (* f | k *)
      (* f | k : k ~ f * m *)
      eliminate exists (m: polynomial t). poly_eq k (poly_mul mf m)
      returns divides #(polynomial t) #cr_p (poly_mul mf mg) a
      with _hm.
      begin
        (* a ~ g*k ~ g*(f*m) ~ (f*g)*m *)
        reflexivity #(polynomial t) #(cr_p.cr_r.r_add.acg_eq) mg;
        poly_mul_congruence mg k mg (poly_mul mf m);                        (* g*k ~ g*(f*m) *)
        transitivity a (poly_mul mg k) (poly_mul mg (poly_mul mf m));       (* a ~ g*(f*m) *)
        (* g*(f*m) ~ (f*g)*m *)
        mul_assoc_swap #t mg mf m;
        transitivity a (poly_mul mg (poly_mul mf m)) (poly_mul (poly_mul mf mg) m);
        divides_intro #(polynomial t) #cr_p (poly_mul mf mg) a m
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
         (requires Some? (poly_deg mf) /\ coprime #t #f mf mg)
         (ensures fun _ -> True)
  = let bl = bezout_left  #t #f mf mg in
    let br = bezout_right #t #f mf mg in
    poly_add (poly_mul c (poly_mul bl mf)) (poly_mul b (poly_mul br mg))

(* Bridge: in the polynomial commutative ring, the Bezout sum equals
   the ring `one`  (poly_eq ... poly_one  and  poly_one == one). *)
let bezout_sum_is_one (#t:Type) {| f: field t |} (mf mg: polynomial t)
  : Lemma (requires Some? (poly_deg mf) /\ coprime #t #f mf mg)
          (ensures  (let cr_p : commutative_ring (polynomial t) = TC.solve in
                     let bl = bezout_left  #t #f mf mg in
                     let br = bezout_right #t #f mf mg in
                     (poly_add (poly_mul bl mf) (poly_mul br mg))
                       = (one <: polynomial t)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    bezout_identity #t #f mf mg                  (* poly_eq (bl*mf+br*mg) poly_one; poly_one == one *)

#push-options "--z3rlimit 100"
let crt_surj_f (#t:Type) {| f: field t |} (mf mg b c: polynomial t)
  : Lemma (requires Some? (poly_deg mf) /\ coprime #t #f mf mg)
          (ensures  (let cr_p : commutative_ring (polynomial t) = TC.solve in
                     divides #(polynomial t) #cr_p mf
                       (poly_sub (crt_witness #t #f mf mg b c) b)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    let bl = bezout_left  #t #f mf mg in
    let br = bezout_right #t #f mf mg in
    let a  = crt_witness #t #f mf mg b c in
    bezout_sum_is_one #t #f mf mg;               (* (bl*mf + br*mg) = one *)
    abstract_crt_surj #(polynomial t) #cr_p mf mg bl br b c;  (* mf | (w + neg b) *)
    (* w + neg b == poly_sub a b *)
    poly_sub_reveal a b;
    assert (a == poly_add (poly_mul c (poly_mul bl mf)) (poly_mul b (poly_mul br mg)))
#pop-options

(* abstract add-commutativity (for transporting the g-witness). *)
let abstract_add_comm (#p:Type) {| pr: commutative_ring p |} (x y: p)
  : Lemma (x + y = y + x)
  = assert (x + y = y + x) by (canon_ring ())

(* Symmetric statement for the second modulus. *)
#push-options "--z3rlimit 120"
let crt_surj_g (#t:Type) {| f: field t |} (mf mg b c: polynomial t)
  : Lemma (requires Some? (poly_deg mf) /\ Some? (poly_deg mg) /\ coprime #t #f mf mg)
          (ensures  (let cr_p : commutative_ring (polynomial t) = TC.solve in
                     divides #(polynomial t) #cr_p mg
                       (poly_sub (crt_witness #t #f mf mg b c) c)))
  = let cr_p : commutative_ring (polynomial t) = TC.solve in
    H.elim_equatable_laws (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    H.trans_for_calc (polynomial t) #(cr_p.cr_r.r_add.acg_eq) ();
    let bl = bezout_left  #t #f mf mg in
    let br = bezout_right #t #f mf mg in
    let a  = crt_witness #t #f mf mg b c in
    (* Bezout for the swapped order:  br*mg + bl*mf = one. *)
    bezout_sum_is_one #t #f mf mg;                          (* bl*mf + br*mg = one *)
    abstract_add_comm #(polynomial t) #cr_p (poly_mul bl mf) (poly_mul br mg);  (* bl*mf+br*mg = br*mg+bl*mf *)
    symmetry (poly_add (poly_mul bl mf) (poly_mul br mg))
             (poly_add (poly_mul br mg) (poly_mul bl mf));  (* br*mg+bl*mf = bl*mf+br*mg *)
    transitivity (poly_add (poly_mul br mg) (poly_mul bl mf))
                 (poly_add (poly_mul bl mf) (poly_mul br mg))
                 (one <: polynomial t);                     (* br*mg + bl*mf = one *)
    (* abstract surjectivity with roles (mg, mf, br, bl, c, b):
         w' = b*(br*mg) + c*(bl*mf),   mg | (w' + neg c). *)
    abstract_crt_surj #(polynomial t) #cr_p mg mf br bl c b;
    let w' = poly_add (poly_mul b (poly_mul br mg)) (poly_mul c (poly_mul bl mf)) in
    (* w' = a  (add-commutativity) ;  hence  mg | (a + neg c) = poly_sub a c. *)
    abstract_add_comm #(polynomial t) #cr_p (poly_mul b (poly_mul br mg)) (poly_mul c (poly_mul bl mf));
    assert (a == poly_add (poly_mul c (poly_mul bl mf)) (poly_mul b (poly_mul br mg)));
    (* w' = a *)
    reflexivity #(polynomial t) #(cr_p.cr_r.r_add.acg_eq) (poly_neg c);
    poly_add_congruence w' (poly_neg c) a (poly_neg c);     (* w' + neg c ~ a + neg c *)
    divides_congruence_right #(polynomial t) #cr_p mg
      (poly_add w' (poly_neg c)) (poly_add a (poly_neg c)); (* mg | a + neg c *)
    poly_sub_reveal a c                                     (* poly_sub a c == a + neg c *)
#pop-options
