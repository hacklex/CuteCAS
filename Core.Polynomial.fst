module Core.Polynomial

(*  Design probe for the new polynomial typeclass architecture.

    Goals (per user direction):
      - Class-based, no internal-record slop in public lemma signatures.
      - Characterizing (definitional) facts go INSIDE the class as fields.
      - Corollary lemmas live OUTSIDE, taking the minimal class
        constraints (coefficient cr/id/f + polynomial pcr/pid/pf).
      - Public statements use infix notation (`=`, `+`, `*`, `-`).
      - Independent of the legacy Core.Polynomial.* tower.
*)

module TC = FStar.Tactics.Typeclasses
module L = FStar.List.Tot
module H = Core.Algebra.Helpers

open Core.Algebra
open Core.Algebra.Notation

let is_trimmed (#t:Type) {| cr: commutative_ring t |} (p: list t) : bool 
  = (L.length p = 0) || (L.last p <> zero)

(* ---------------------------------------------------------------- *)
(*  The polynomial carrier                                          *)
(* ---------------------------------------------------------------- *)

type polynomial (t:Type) {| cr: commutative_ring t |} = (p:list t{is_trimmed p})

(* Trimming *)

let rec trim #t {| cr: commutative_ring t |} (p: list t) : polynomial t =
  if L.length p = 0 then []
  else begin
    let head = L.hd p in
    let tail = trim (L.tl p) in
    if L.length tail > 0 then (head :: tail) 
    else (if head = zero then [] else [head])    
  end

private let rec trim_idempotence (#t:Type) {| cr: commutative_ring t |} (p: list t)
  : Lemma (trim (trim p) == trim p)
          [SMTPat (trim (trim p))]
  = if L.length p > 0 then trim_idempotence (L.tl p) 
 
private let rec trim_poly_does_nothing (#t:Type) {| cr: commutative_ring t |} (p: list t)
  : Lemma (requires is_trimmed p) (ensures trim p == p)
          (decreases L.length p)
  = if L.length p > 0 then trim_poly_does_nothing (L.tl p)

private let rec trimmed_tail_is_trimmed (#t:Type) {| cr: commutative_ring t |} (p: list t)
  : Lemma (requires is_trimmed p /\ L.length p > 0) (ensures is_trimmed (L.tl p))
          (decreases L.length p)
  = match p with
    | [] -> ()
    | a :: p' ->
        if L.length p' > 0 then trimmed_tail_is_trimmed p'
        else add_zero a; reflexivity a

private unfold let const_coeff (#t:Type) {| cr: commutative_ring t |} (p: list t)
  = if L.length p > 0 then L.hd p else (zero <: t)

unfold let (@) (#t:Type) {| cr: commutative_ring t |} (x:t) (y: polynomial t) : polynomial t = 
    match x, y with
    | _, [] -> if x = zero then [] else [x]
    | h, t -> h :: t
 
private unfold let concat_coeff (#t:Type) {| cr: commutative_ring t |} (x:t) (p: polynomial t)
  : Lemma (const_coeff (x @ p) = x)
  = symmetry x zero;
    reflexivity x; 
    if L.length p = 0 && x = zero then assert_norm(const_coeff (x @ p) == zero)
    else if L.length p = 0 && x <> zero then assert_norm(const_coeff (x @ p) == x)
    
(* ---------------------------------------------------------------- *)
(*  Layer 1: polynomial_commutative_ring                            *)
(*    Requires: commutative_ring t                                  *)
(*    Provides: commutative_ring (polynomial cr) +                  *)
(*              characterizing equations for poly_add/poly_neg/     *)
(*              poly_mul/poly_one/lc/deg.                           *)
(* ---------------------------------------------------------------- *)

class polynomial_commutative_ring (t: Type) {| cr: commutative_ring t |} = {
  [@@@TC.no_method] pcr: commutative_ring (polynomial t);

  (*  ----- Additive layer ----- *)

  (*  Zero of the polynomial-ring is the empty list.               *)
  [@@@TC.no_method] poly_zero_reveal:
    squash (zero #(polynomial t) == []);

  (*  ----- Multiplicative layer ----- *)

  (*  Polynomial-ring one is the singleton list `[one]`.          *)
  [@@@TC.no_method] poly_one_reveal:
    squash ((one #t = zero #t && one #(polynomial t) == []) 
         || (one #t <> zero #t) && one #(polynomial t) == [one #t]);

  (*  Multiplying by zero on either side yields zero polynomial.        *)
  [@@@TC.no_method] poly_mul_zero: (q: polynomial t) ->
                 Lemma ((zero #(polynomial t)) * q == (zero #(polynomial t)) /\
                        q * (zero #(polynomial t)) == (zero #(polynomial t)));

  (*  ----- Degree + leading coefficient ----- *)

  lc:  polynomial t -> t;
  deg: polynomial t -> option nat;

  [@@@TC.no_method] deg_zero_is_none: squash (deg zero == None);

  [@@@TC.no_method] deg_reveal:
    (a: t) -> (p: polynomial t) ->
    Lemma (deg (a @ p) ==
           (match deg p with
            | Some k -> Some (succ k)
            | None   -> if a = zero then None else Some 0));

  [@@@TC.no_method] lc_reveal:
    (p: polynomial t) ->
    Lemma ((None? (deg p) /\ lc p == zero) \/ (Some? (deg p) /\ lc p == L.last p))
}

(*  Unfold-instance bridge: opening `polynomial_commutative_ring t`
    delivers `commutative_ring (polynomial cr)` to TC search.       *)
unfold instance cr_of_pcr (#t: Type) 
    {| cr: commutative_ring t |}
    {| pcrc: polynomial_commutative_ring t |}
  : commutative_ring (polynomial t) = pcrc.pcr

(* ---------------------------------------------------------------- *)
(*  Layer 2: polynomial_integral_domain                             *)
(*    Requires: integral_domain t                                   *)
(*    Provides: integral_domain (polynomial id) +                   *)
(*              polynomial_commutative_ring t #(cr_of_id t).        *)
(* ---------------------------------------------------------------- *)

class polynomial_integral_domain (t: Type) {| id: integral_domain t |}
                                           {| pcrc: polynomial_commutative_ring t |}
                                = {
  [@@@TC.no_method] pid:  integral_domain (polynomial t);
  [@@@TC.no_method] pid_pcrc_coherence: squash (cr_of_id (polynomial t) == pcrc.pcr);
 
  (*  Cons-mul: standard convolution shape.
        (a :: p) * q == (a@zero) * q + (zero@(p * q))
      Requires integral_domain coefficients to be a valid characterizing
      equation (over general rings the recursive structure can collapse
      via zero-divisor coincidences).                                  *)
  [@@@TC.no_method] poly_mul_cons_reveal:
    (a: t) -> (p: polynomial t) -> (q: polynomial t) ->
    Lemma ((a @ p) * q = (a @ zero) * q + (zero @ (p * q)));
}

unfold instance id_of_pid
    (#t: Type) {| id: integral_domain t |}
    {| pcrc: polynomial_commutative_ring t |}
    {| pidc: polynomial_integral_domain t |}
  : integral_domain (polynomial t) = pidc.pid

(* ---------------------------------------------------------------- *)
(*  Layer 3: polynomial_euclidean_domain                            *)
(*    Requires: field t                                             *)
(*    Provides: Euclidean division on polynomial (cr_of_id t).      *)
(* ---------------------------------------------------------------- *)

class polynomial_euclidean_domain (t: Type) {| f: field t |}
                                            {| pcrc: polynomial_commutative_ring t |}
                                            {| pidc: polynomial_integral_domain t |}
                                  = {
  (*  Euclidean division: (q, r) = divmod p d.
      Spec: p = d * q + r  /\  (r = 0  \/  deg r < deg d).           *)
  divmod:
    (p: polynomial t) ->
    (d: polynomial t { not (d = zero) }) ->
    polynomial t & polynomial t;

  divmod_lemma:
    (p: polynomial t) ->
    (d: polynomial t { not (d = zero) }) ->
    Lemma (let q, r = divmod p d in
           p = d * q + r);

  divmod_degree:
    (p: polynomial t) ->
    (d: polynomial t { not (d = zero) }) ->
    Lemma (let _, r = divmod p d in
           r = zero \/
           (Some? (deg r) /\ Some? (deg d) /\
            Some?.v (deg r) < Some?.v (deg d)));
}

(* ================================================================ *)
(*  Implementation: ported from legacy Core.Polynomial              *)
(* ================================================================ *)

(* From now, we start constructing the poly operations. Those should NOT use {| polynomial_commutative_ring |},
   because they will be used to finally construct one *)

(* coeff — out-of-bounds reads (including negative indices) return ring zero *)
let coeff (#t:Type) {| cr: commutative_ring t |} (p: polynomial t) (i: int)
  : (c:t{(i < 0 ==> c == (zero <: t)) /\
         (i >= 0 /\ i >= L.length p ==> c == (zero <: t)) /\
         (i >= 0 /\ i <  L.length p ==> c == L.index p i)})
  = if i < 0 then (zero <: t)
    else if i < L.length p then L.index p i
    else (zero <: t)

(* poly_zero — canonical empty list at type polynomial t *)
unfold let poly_zero (#t:Type) {| cr: commutative_ring t |} : polynomial t = []

(* ---------------- Equality ---------------- *)

let rec poly_eq (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) : bool =
   match p, q with
    | [], [] -> true
    | a::p', b::q' -> a = b && poly_eq p' q'
    | _, _ -> false

let rec poly_eq_reflexivity (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (poly_eq p p)
  = if L.length p > 0 then (poly_eq_reflexivity #t #cr (L.tl p); reflexivity (L.hd p))  

let rec poly_eq_symmetry (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma (poly_eq p q <==> poly_eq q p)
  = match p, q with
    | [], _            -> ()
    | _ :: _, []       -> ()
    | a :: p', b :: q' -> symmetry a b; poly_eq_symmetry #t #cr p' q'

let rec poly_eq_transitivity #t {| cr: commutative_ring t |} (p q r: polynomial t)
  : Lemma (requires poly_eq p q /\ poly_eq q r) (ensures poly_eq p r)
          (decreases %[L.length p; L.length q; L.length r])
  = match p, q, r with
    | [], [], [] -> ()
    | _ :: _, _ :: _, _ :: _ ->
        symmetry (L.hd p) (L.hd q);
        transitivity (L.hd p) (L.hd q) (L.hd r);
        poly_eq_transitivity #t #cr (L.tl p) (L.tl q) (L.tl r)

private let rec poly_eq_means_length_eq (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma (requires poly_eq p q) (ensures L.length p = L.length q)
          (decreases L.length p)
  = match p, q with
    | [], [] -> ()
    | a::p', b::q' -> poly_eq_means_length_eq #t #cr p' q'
    | _, _ -> ()
 
private let const_coeff_is_coeff_at_zero (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (const_coeff p == coeff p 0)
  = match p with
    | [] -> ()
    | a :: _ -> reflexivity a

let rec poly_eq_means_equal_coeffs (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) (i: nat)
  : Lemma (requires poly_eq p q) (ensures coeff p i = coeff q i)
          (decreases i)
  = poly_eq_means_length_eq #t #cr p q;
    reflexivity (coeff p i);
    if i > 0  && i < L.length p 
    then poly_eq_means_equal_coeffs (L.tl p) (L.tl q) (i - 1) 

let rec coeff_at_tail #t {| cr: commutative_ring t |} (p: polynomial t {L.length p > 0}) (i: pos)
  : Lemma (ensures coeff p i = coeff (L.tl p) (i - 1))
          (decreases L.length p) = 
    reflexivity (coeff p i);
    if (L.length p > 1 && i > 1) 
    then coeff_at_tail #t #cr (L.tl p) (i - 1)
  
let rec last_eq_index #t (l: list t) (i: nat {i < L.length l}) 
  : Lemma (requires L.length l > 0 /\ i = (L.length l - 1))
          (ensures L.last l == L.index l ((L.length l) - 1)) =  
  assert (L.index l 0 == L.hd l);
  if i > 0 then begin
    last_eq_index #t (L.tl l) (i - 1);
    assert (L.index l i == L.index (L.tl l) (i - 1))
  end


let rec equal_coeffs_means_poly_eq (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) 
  : Lemma (requires (forall j. coeff p j = coeff q j))
          (ensures poly_eq p q)
          (decreases L.length p)
  = match p, q with
    | [], [] -> ()
    | a::p', b::q' ->
        reflexivity a;
        assert (coeff p 0 = coeff q 0);
        let aux (i:nat) : Lemma (ensures ((coeff #t #cr p' i) = (coeff #t #cr q' i))) =            
          assert (coeff p' i == coeff p (succ i));
          assert (coeff q' i == coeff q (succ i));               
          reflexivity (coeff p' i) in
        Classical.forall_intro aux;
        equal_coeffs_means_poly_eq #t #cr p' q';        
        ()
    | nonzero_poly, [] -> last_eq_index #t nonzero_poly ((L.length nonzero_poly) - 1)
    | [], nonzero_poly ->
      last_eq_index #t nonzero_poly ((L.length nonzero_poly) - 1);
      symmetry (zero <: t) (coeff nonzero_poly ((L.length nonzero_poly) - 1))
        
let rec poly_eq_length #t {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma (requires poly_eq p q) (ensures L.length p = L.length q) =
  match p, q with
  | [], [] -> ()
  | a::p', b::q' -> poly_eq_length p' q'
  | _, _ -> ()

private let poly_eq_nil_l_compute
  (#t:Type) {| cr: commutative_ring t |} (q: polynomial t)
  : Lemma (poly_eq #t #cr [] q <==> (q == []))
  = ()

private let poly_eq_nil_r_compute
  (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (poly_eq #t #cr p [] <==> (p == []))
  = match p with | [] -> () | _ :: _ -> ()

(* The polynomial zero is uniquely characterized: anything poly_eq to it
   IS it (propositionally). This subsumes the older nil-compute lemmas. *)
let poly_zero_is_unique (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (poly_eq p (poly_zero #t) <==> (p == (poly_zero #t)))
  = match p with | [] -> () | _ :: _ -> ()

private let zero_is_unique (#t:Type) {| cr: commutative_ring t |} (z: polynomial t)
  : Lemma (requires poly_eq z poly_zero) (ensures z == ([] <: polynomial t)) = ()

private let zero_eq_self_in_cr (#t:Type) {| cr: commutative_ring t |}
  : Lemma ((zero <: t) = (zero <: t))
  = reflexivity (zero <: t)

private let eq_zero_eq_zero_imp_eq (#t:Type) {| cr: commutative_ring t |} (a b: t)
  : Lemma (requires a = (zero <: t) /\ b = (zero <: t)) (ensures a = b)
  = symmetry b (zero <: t);
    transitivity a (zero <: t) b

private let eq_zero_neq_zero_imp_neq (#t:Type) {| cr: commutative_ring t |} (a b: t)
  : Lemma (requires a = (zero <: t) /\ ~ (b = (zero <: t))) (ensures ~ (a = b))
  = let contra (_: unit) : Lemma (requires a = b) (ensures False) =
        symmetry a b;
        transitivity b a (zero <: t)
    in Classical.move_requires contra ()

let poly_eq_cons_cons_compute
  (#t:Type) {| cr: commutative_ring t |}
  (a: t) (p': polynomial t) (b: t) (q': polynomial t)
  : Lemma (poly_eq (a @ p') (b @ q') == ((a = b) && poly_eq p' q'))
  = match p', q' with
    | [], [] ->
        if a = (zero <: t) then begin
          if b = (zero <: t) then begin
            (* a@[]=[], b@[]=[], LHS=true; need a=b *)
            symmetry b (zero <: t);
            transitivity a (zero <: t) b
          end else begin
            (* a@[]=[], b@[]=[b], LHS=poly_eq [] [b] = false; need ~(a=b) *)
            let contra (_:unit) : Lemma (requires a = b) (ensures False) =
              symmetry a b;
              transitivity b a (zero <: t)
            in Classical.move_requires contra ()
          end
        end else begin
          if b = (zero <: t) then begin
            (* a@[]=[a], b@[]=[], LHS=poly_eq [a] [] = false; need ~(a=b) *)
            let contra (_:unit) : Lemma (requires a = b) (ensures False) =
              transitivity a b (zero <: t)
            in Classical.move_requires contra ()
          end else ()
        end
    | [], _ :: _ -> ()
    | _ :: _, [] -> ()
    | _ :: _, _ :: _ -> ()

let polynomial_equatable (#t:Type) (cr: commutative_ring t) : equatable (polynomial t #cr) = {
  eq = poly_eq;
  reflexivity = poly_eq_reflexivity;
  symmetry = poly_eq_symmetry;
  transitivity = poly_eq_transitivity;
}

(* ---------------- Addition ---------------- *)

private let rec poly_add_untrimmed (#t:Type) {| cr: commutative_ring t |} (p q: list t) : list t =
  match p, q with
  | [], _            -> q
  | _, []            -> p
  | a :: p', b :: q' -> (a + b) :: poly_add_untrimmed p' q'
 
private let poly_add_zero_untrimmed #t {| cr: commutative_ring t |} (p: list t)
  : Lemma (ensures poly_add_untrimmed p [] == p)
          (decreases L.length p) = ()

(* ================================================================ *)
(*  Private raw (untrimmed) layer                                    *)
(*  All facts here are proven on raw `list t` values.  The trimmed   *)
(*  layer below bridges via `trim`.                                  *)
(* ================================================================ *)

private let rec raw_all_zero #t {| cr: commutative_ring t |} (p: list t) : bool =
  match p with
  | []      -> true
  | a :: p' -> ((a <: t) = (zero <: t)) && raw_all_zero p'

private let rec raw_poly_eq #t {| cr: commutative_ring t |} (p q: list t) : bool =
  match p, q with
  | [], _              -> raw_all_zero q
  | _, []              -> raw_all_zero p
  | a :: p', b :: q'   -> ((a <: t) = (b <: t)) && raw_poly_eq p' q'

(* Refl/Sym/Trans for raw_poly_eq (legacy proofs) *)

private let rec raw_poly_eq_refl #t {| cr: commutative_ring t |} (p: list t)
  : Lemma (raw_poly_eq p p)
  = match p with
    | []      -> ()
    | a :: p' -> reflexivity a; raw_poly_eq_refl #t #cr p'

private let rec raw_poly_eq_sym #t {| cr: commutative_ring t |} (p q: list t)
  : Lemma (raw_poly_eq p q <==> raw_poly_eq q p)
  = match p, q with
    | [], _            -> ()
    | _ :: _, []       -> ()
    | a :: p', b :: q' -> symmetry a b; raw_poly_eq_sym #t #cr p' q'

private let rec raw_poly_eq_trans_lhs_empty #t {| cr: commutative_ring t |}
                                            (q r: list t)
  : Lemma (requires raw_all_zero q /\ raw_poly_eq q r) (ensures raw_all_zero r)
          (decreases %[L.length q; L.length r])
  = match q, r with
    | [], _       -> ()
    | _ :: _, []  -> ()
    | b :: q', c :: r' ->
        symmetry b c;
        transitivity c b (zero <: t);
        raw_poly_eq_trans_lhs_empty #t #cr q' r'

private let rec raw_poly_eq_trans_rhs_empty #t {| cr: commutative_ring t |}
                                            (p q: list t)
  : Lemma (requires raw_poly_eq p q /\ raw_all_zero q) (ensures raw_all_zero p)
          (decreases %[L.length p; L.length q])
  = match p, q with
    | _, []       -> ()
    | [], _       -> ()
    | a :: p', b :: q' ->
        transitivity a b (zero <: t);
        raw_poly_eq_trans_rhs_empty #t #cr p' q'

private let rec raw_poly_eq_trans_mid_empty #t {| cr: commutative_ring t |}
                                            (p r: list t)
  : Lemma (requires raw_all_zero p /\ raw_all_zero r) (ensures raw_poly_eq p r)
          (decreases %[L.length p; L.length r])
  = match p, r with
    | [], _      -> ()
    | _ :: _, [] -> ()
    | a :: p', c :: r' ->
        symmetry c (zero <: t);
        transitivity a (zero <: t) c;
        raw_poly_eq_trans_mid_empty #t #cr p' r'

private let rec raw_poly_eq_trans #t {| cr: commutative_ring t |} (p q r: list t)
  : Lemma (requires raw_poly_eq p q /\ raw_poly_eq q r) (ensures raw_poly_eq p r)
          (decreases %[L.length p; L.length q; L.length r])
  = match p, q, r with
    | [], _, _ ->
        raw_poly_eq_trans_lhs_empty q r
    | _ :: _, [], _ ->
        raw_poly_eq_trans_rhs_empty p q;
        raw_poly_eq_trans_mid_empty p r
    | _ :: _, _ :: _, [] ->
        raw_poly_eq_trans_rhs_empty p q;
        raw_poly_eq_trans_mid_empty p r
    | a :: p', b :: q', c :: r' ->
        transitivity a b c;
        raw_poly_eq_trans #t #cr p' q' r'

(* ------------------ Raw coefficient + raw poly_add facts ------------ *)

private let raw_coeff #t {| cr: commutative_ring t |} (p: list t) (i: nat) : t
  = if i < L.length p then L.index p i else (zero <: t)

private let rec raw_all_zero_means_zero_coeffs #t {| cr: commutative_ring t |}
                                               (p: list t) (i: nat)
  : Lemma (requires raw_all_zero p) (ensures raw_coeff p i = (zero <: t))
          (decreases L.length p)
  = match p with
    | []      -> reflexivity (zero <: t)
    | a :: p' ->
        if i = 0 then ()
        else raw_all_zero_means_zero_coeffs p' (i-1)

private let rec raw_poly_eq_means_coeff_eq #t {| cr: commutative_ring t |}
                                          (p q: list t) (i: nat)
  : Lemma (requires raw_poly_eq p q) (ensures raw_coeff p i = raw_coeff q i)
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ ->
        raw_all_zero_means_zero_coeffs q i;
        symmetry (raw_coeff q i) (zero <: t)
    | _ :: _, [] ->
        raw_all_zero_means_zero_coeffs p i
    | a :: p', b :: q' ->
        if i = 0 then ()
        else raw_poly_eq_means_coeff_eq p' q' (i-1)

(* poly_add_untrimmed coefficient law *)

private let rec raw_add_coeff #t {| cr: commutative_ring t |}
                              (p q: list t) (i: nat)
  : Lemma (ensures raw_coeff (poly_add_untrimmed p q) i =
                   (raw_coeff p i) + (raw_coeff q i))
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ ->
        let v : t = raw_coeff q i in
        add_zero v;
        add_commutativity v (zero <: t);
        symmetry (v + (zero <: t)) v;
        transitivity v (v + (zero <: t)) ((zero <: t) + v);
        symmetry v ((zero <: t) + v)
    | _ :: _, [] ->
        let v : t = raw_coeff p i in
        add_zero v;
        symmetry (v + (zero <: t)) v
    | a :: p', b :: q' ->
        if i = 0 then reflexivity (a + b)
        else begin
          raw_add_coeff p' q' (i-1)
        end

(* Bare facts about + and neg on coefficients *)

private let coef_add_zero_l #t {| cr: commutative_ring t |} (a: t)
  : Lemma ((zero <: t) + a = a)
  = add_commutativity (zero <: t) a;
    add_zero a;
    transitivity ((zero <: t) + a) (a + (zero <: t)) a

private let coef_add_zero_r #t {| cr: commutative_ring t |} (a: t)
  : Lemma (a + (zero <: t) = a)
  = add_zero a

private let coef_add_cong_aux #t {| cr: commutative_ring t |} (a b x y: t)
  : Lemma (requires a = x /\ b = y) (ensures (a + b) = (x + y))
  = add_congruence a b x y

(* ------------- Raw additive lemmas: legacy proofs adopted ------------- *)

private let rec raw_add_left_all_zero #t {| cr: commutative_ring t |}
                                      (p q: list t)
  : Lemma (requires raw_all_zero p)
          (ensures raw_poly_eq (poly_add_untrimmed p q) q)
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _           -> raw_poly_eq_refl q
    | _ :: _, []      -> ()
    | a :: p', b :: q' ->
        reflexivity b;
        add_congruence a b (zero <: t) b;
        coef_add_zero_l b;
        transitivity (a + b) ((zero <: t) + b) b;
        raw_add_left_all_zero p' q'

private let rec raw_add_right_all_zero #t {| cr: commutative_ring t |}
                                       (p q: list t)
  : Lemma (requires raw_all_zero q)
          (ensures raw_poly_eq (poly_add_untrimmed p q) p)
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _           -> raw_poly_eq_refl ([] <: list t); raw_poly_eq_sym q ([] <: list t)
    | _ :: _, []      -> raw_poly_eq_refl p
    | a :: p', b :: q' ->
        reflexivity a;
        add_congruence a b a (zero <: t);
        coef_add_zero_r a;
        transitivity (a + b) (a + (zero <: t)) a;
        raw_add_right_all_zero p' q'

private let rec raw_add_left_cong #t {| cr: commutative_ring t |}
                                  (p1 p2 q: list t)
  : Lemma (requires raw_poly_eq p1 p2)
          (ensures raw_poly_eq (poly_add_untrimmed p1 q) (poly_add_untrimmed p2 q))
          (decreases %[L.length p1; L.length p2; L.length q])
  = match p1, p2, q with
    | [], _, _ ->
        raw_add_left_all_zero p2 q;
        raw_poly_eq_sym (poly_add_untrimmed p2 q) q
    | _ :: _, [], _ ->
        raw_add_left_all_zero p1 q
    | a :: p1', b :: p2', [] ->
        raw_poly_eq_refl (poly_add_untrimmed (a :: p1') ([] <: list t))
    | a :: p1', b :: p2', c :: q' ->
        reflexivity c;
        add_congruence a c b c;
        raw_add_left_cong p1' p2' q'

private let rec raw_add_right_cong #t {| cr: commutative_ring t |}
                                   (p q1 q2: list t)
  : Lemma (requires raw_poly_eq q1 q2)
          (ensures raw_poly_eq (poly_add_untrimmed p q1) (poly_add_untrimmed p q2))
          (decreases %[L.length p; L.length q1; L.length q2])
  = match p, q1, q2 with
    | [], _, _ -> ()
    | _ :: _, [], _ ->
        raw_add_right_all_zero p q2;
        raw_poly_eq_sym (poly_add_untrimmed p q2) p
    | _ :: _, _ :: _, [] ->
        raw_add_right_all_zero p q1
    | a :: p', b :: q1', c :: q2' ->
        reflexivity a;
        add_congruence a b a c;
        raw_add_right_cong p' q1' q2'

private let raw_add_cong #t {| cr: commutative_ring t |}
                         (p1 q1 p2 q2: list t)
  : Lemma (requires raw_poly_eq p1 p2 /\ raw_poly_eq q1 q2)
          (ensures raw_poly_eq (poly_add_untrimmed p1 q1) (poly_add_untrimmed p2 q2))
  = raw_add_left_cong  p1 p2 q1;
    raw_add_right_cong p2 q1 q2;
    raw_poly_eq_trans (poly_add_untrimmed p1 q1) (poly_add_untrimmed p2 q1) (poly_add_untrimmed p2 q2)

private let rec raw_add_comm #t {| cr: commutative_ring t |} (p q: list t)
  : Lemma (ensures raw_poly_eq (poly_add_untrimmed p q) (poly_add_untrimmed q p))
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ ->
        raw_add_right_all_zero q p;
        raw_poly_eq_sym (poly_add_untrimmed q p) p
    | _ :: _, [] ->
        raw_add_right_all_zero p q
    | a :: p', b :: q' ->
        add_commutativity a b;
        raw_add_comm p' q'

private let rec raw_add_assoc #t {| cr: commutative_ring t |} (p q r: list t)
  : Lemma (ensures raw_poly_eq (poly_add_untrimmed (poly_add_untrimmed p q) r)
                               (poly_add_untrimmed p (poly_add_untrimmed q r)))
          (decreases %[L.length p; L.length q; L.length r])
  = match p, q, r with
    | [], _, _ ->
        raw_poly_eq_refl (poly_add_untrimmed q r)
    | _ :: _, [], _ ->
        raw_poly_eq_refl (poly_add_untrimmed p r)
    | _ :: _, _ :: _, [] ->
        raw_poly_eq_refl (poly_add_untrimmed p q)
    | a :: p', b :: q', c :: r' ->
        add_associativity a b c;
        raw_add_assoc p' q' r'

(* ----------------- Raw neg ----------------- *)

private let rec raw_poly_neg #t {| cr: commutative_ring t |} (p: list t) : list t =
  match p with
  | []      -> []
  | a :: p' -> (-a) :: raw_poly_neg p'

private let rec raw_neg_all_zero #t {| cr: commutative_ring t |} (p: list t)
  : Lemma (requires raw_all_zero p) (ensures raw_all_zero (raw_poly_neg p))
          (decreases L.length p)
  = match p with
    | []      -> ()
    | a :: p' ->
        H.neg_zero #t ();
        symmetry (zero <: t) (-(zero <: t));
        neg_congruence a (zero <: t);
        transitivity (-a) (-(zero <: t)) (zero <: t);
        raw_neg_all_zero p'

private let rec raw_neg_cong #t {| cr: commutative_ring t |} (p q: list t)
  : Lemma (requires raw_poly_eq p q) (ensures raw_poly_eq (raw_poly_neg p) (raw_poly_neg q))
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ -> raw_neg_all_zero q
    | _ :: _, [] -> raw_neg_all_zero p
    | a :: p', b :: q' ->
        neg_congruence a b;
        raw_neg_cong p' q'

private let rec raw_add_neg_r #t {| cr: commutative_ring t |} (p: list t)
  : Lemma (ensures raw_poly_eq (poly_add_untrimmed p (raw_poly_neg p)) [])
          (decreases L.length p)
  = match p with
    | []      -> ()
    | a :: p' ->
        add_negation a;
        raw_add_neg_r p'

private let rec raw_add_neg_l #t {| cr: commutative_ring t |} (p: list t)
  : Lemma (ensures raw_poly_eq (poly_add_untrimmed (raw_poly_neg p) p) [])
          (decreases L.length p)
  = match p with
    | []      -> ()
    | a :: p' ->
        add_negation a;
        raw_add_neg_l p'

(* ================================================================ *)
(*  Trim bridge: trim is coefficient-preserving                      *)
(* ================================================================ *)

private let rec trim_raw_eq #t {| cr: commutative_ring t |} (p: list t)
  : Lemma (ensures raw_poly_eq p (trim p))
          (decreases L.length p)
  = match p with
    | []      -> ()
    | a :: p' ->
        trim_raw_eq p';
        let t' = trim p' in
        if L.length t' > 0 then reflexivity a
        else if a = (zero <: t) then ()
        else reflexivity a

private let coeff_in_raw_eq #t {| cr: commutative_ring t |}
                            (p: polynomial t) (i: nat)
  : Lemma (ensures coeff p i == raw_coeff p i) = ()

private let trim_preserves_coeff #t {| cr: commutative_ring t |}
                                 (p: list t) (i: nat)
  : Lemma (ensures raw_coeff (trim p) i = raw_coeff p i)
  = trim_raw_eq p;
    raw_poly_eq_means_coeff_eq p (trim p) i;
    symmetry (raw_coeff p i) (raw_coeff (trim p) i)

(* Bridge: raw_poly_eq a b implies coefficient agreement implies poly_eq (strict)
   on the trimmed forms. *)

private let raw_eq_means_trim_coeff_eq #t {| cr: commutative_ring t |}
                                       (a b: list t) (i: nat)
  : Lemma (requires raw_poly_eq a b)
          (ensures coeff (trim a) i = coeff (trim b) i)
  = raw_poly_eq_means_coeff_eq a b i;
    trim_preserves_coeff a i;
    trim_preserves_coeff b i;
    coeff_in_raw_eq (trim a) i;
    coeff_in_raw_eq (trim b) i;
    let ca = raw_coeff (trim a) i in
    let cb = raw_coeff (trim b) i in
    let ra = raw_coeff a i in
    let rb = raw_coeff b i in
    (* ca = ra, ra = rb, cb = rb *)
    symmetry cb rb;            (* rb = cb *)
    transitivity ca ra rb;     (* ca = rb *)
    transitivity ca rb cb      (* ca = cb *)

private let raw_eq_means_trim_poly_eq #t {| cr: commutative_ring t |}
                                      (a b: list t)
  : Lemma (requires raw_poly_eq a b)
          (ensures poly_eq (trim a) (trim b))
  = let aux (i: nat) : Lemma (coeff (trim a) i = coeff (trim b) i)
      = raw_eq_means_trim_coeff_eq a b i in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (trim a) (trim b)

(* trim of a trimmed polynomial is itself; lift to polynomial type *)
private let raw_eq_means_poly_eq_for_trimmed #t {| cr: commutative_ring t |}
                                             (p q: polynomial t)
  : Lemma (requires raw_poly_eq p q) (ensures poly_eq p q)
  = trim_poly_does_nothing p;
    trim_poly_does_nothing q;
    raw_eq_means_trim_poly_eq p q

let poly_add (#t:Type) {| cr: commutative_ring t |} (p q: polynomial t) 
  : polynomial t = trim (poly_add_untrimmed p q)
 
let rec poly_add_coeff #t {| cr: commutative_ring t |} (p q: polynomial t) (i: nat)
  : Lemma (ensures coeff (poly_add p q) i = (coeff p i) + (coeff q i))
          (decreases i)
          [SMTPat (coeff (poly_add p q) i)]
  = trim_preserves_coeff (poly_add_untrimmed p q) i;
    raw_add_coeff p q i;
    coeff_in_raw_eq (poly_add p q) i;
    coeff_in_raw_eq p i;
    coeff_in_raw_eq q i;
    let c = raw_coeff (poly_add_untrimmed p q) i in
    let lhs = raw_coeff (trim (poly_add_untrimmed p q)) i in
    let rhs = (raw_coeff p i) + (raw_coeff q i) in
    (* lhs = c (trim_preserves), c = rhs (raw_add_coeff). So lhs = rhs by transitivity. *)
    transitivity lhs c rhs

private let poly_add_nil_l_compute (#t:Type) {| cr: commutative_ring t |} (q: polynomial t)
  : Lemma (poly_add ([] <: polynomial t) q == q)
          [SMTPat (poly_add ([] <: polynomial t) q)]
  = trim_poly_does_nothing q

private let poly_add_nil_r_compute (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (poly_add p ([] <: polynomial t) == p)
          [SMTPat (poly_add p ([] <: polynomial t))]
  = trim_poly_does_nothing p

private let neg_nonzero_is_nonzero (#t:Type) {| cr: commutative_ring t |} (a: t)
  : Lemma (requires a <> zero) (ensures -a <> zero)
  = let contra x : Lemma (requires (x <> zero #t) /\ (-x = zero #t)) (ensures False) =       
      reflexivity x;
      add_congruence x (-x) x zero;
      add_zero x;
      add_negation x;
      symmetry (x + zero) (x + (-x));
      transitivity (x+zero) (x + (-x)) zero;      
      symmetry (x + zero) x;
      transitivity x (x + zero) zero
      in Classical.move_requires contra a      

let rec poly_neg (#t:Type) {| cr: commutative_ring t |} (p: polynomial t) 
  : Tot (polynomial t) (decreases L.length p) =
  match p with
  | [] -> []
  | a :: p' -> 
    trimmed_tail_is_trimmed p;
    (-a) @ poly_neg p'

let poly_neg_zero (#t:Type) {| cr: commutative_ring t |} 
  : Lemma (poly_neg ([] <: polynomial t) == ([] <: polynomial t))
  = ()

let poly_neg_reveal (#t:Type) {| cr: commutative_ring t |}
                          (a: t) (p': polynomial t)
  : Lemma (poly_neg (a @ p') == ((-a) @ poly_neg p'))
          [SMTPat (poly_neg (a @ p'))]
  = match p' with
    | []     ->
        if a = zero then begin
          H.neg_zero #t ();
          symmetry (zero <: t) (-(zero <: t));
          neg_congruence a (zero <: t);
          transitivity (-a) (-(zero <: t)) (zero <: t)
        end else neg_nonzero_is_nonzero a
    | _ :: _ -> ()


(* private helpers: bare facts about + and neg on coefficients *)
private let coef_neg_zero (#t:Type) {| cr: commutative_ring t |}
  : Lemma ((-(zero <: t)) = (zero <: t))
  = H.neg_zero #t ();
    symmetry (zero <: t) (-(zero <: t))

private let coef_add_cong (#t:Type) {| cr: commutative_ring t |}
                          (a b x y: t)
  : Lemma (requires a = x /\ b = y)
          (ensures  (a + b) = (x + y))
  = add_congruence a b x y

(* poly_add: all_zero on one side gives equality *)

(* Trim-bridge for poly_neg: since p is trimmed and -x <> 0 when x <> 0,
   poly_neg p = raw_poly_neg p as a list. *)
private let rec poly_neg_eq_raw #t {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (ensures poly_neg p == raw_poly_neg p)
          (decreases L.length p)
  = match p with
    | []      -> ()
    | a :: p' ->
        trimmed_tail_is_trimmed p;
        poly_neg_eq_raw p';
        match p' with
        | []     -> neg_nonzero_is_nonzero a
        | _ :: _ -> ()

private let rec raw_neg_coeff #t {| cr: commutative_ring t |}
                              (p: list t) (i: nat)
  : Lemma (ensures raw_coeff (raw_poly_neg p) i = (- (raw_coeff p i)))
          (decreases L.length p)
  = match p with
    | []      ->
        H.neg_zero #t ();
        symmetry (zero <: t) (-(zero <: t))
    | a :: p' ->
        if i = 0 then reflexivity (-a)
        else raw_neg_coeff p' (i-1)

let poly_neg_coeff #t {| cr: commutative_ring t |}
                                 (p: polynomial t) (i: nat)
  : Lemma (ensures coeff (poly_neg p) i = (- (coeff p i)))
  = poly_neg_eq_raw p;
    raw_neg_coeff p i;
    coeff_in_raw_eq (poly_neg p) i;
    coeff_in_raw_eq p i

private let rec poly_add_right_zero (#t:Type) {| cr: commutative_ring t |}  
                           (p: polynomial t)
  : Lemma (ensures poly_eq (poly_add p ([] <: polynomial t)) p)
          (decreases L.length p)
  = poly_add_zero_untrimmed p;
    trim_poly_does_nothing p;
    poly_eq_reflexivity p

private let rec poly_add_left_zero (#t:Type) {| cr: commutative_ring t |}
                                (p: polynomial t)
  : Lemma (ensures poly_eq (poly_add ([] <: polynomial t) p) p)
          (decreases L.length p)
  = trim_poly_does_nothing p;
    poly_eq_reflexivity p

(* congruence *)

private let rec poly_add_left_congruence (#t:Type) {| cr: commutative_ring t |}
                                 (p1 p2 q: polynomial t)
  : Lemma (requires poly_eq p1 p2)
          (ensures  poly_eq (poly_add p1 q) (poly_add p2 q))
  = let aux (i: nat) : Lemma (coeff (poly_add p1 q) i = coeff (poly_add p2 q) i) =
      poly_eq_means_equal_coeffs p1 p2 i;
      poly_add_coeff p1 q i;
      poly_add_coeff p2 q i;
      reflexivity (coeff q i);
      add_congruence (coeff p1 i) (coeff q i) (coeff p2 i) (coeff q i);
      symmetry (coeff (poly_add p2 q) i) ((coeff p2 i) + (coeff q i));
      transitivity (coeff (poly_add p1 q) i) ((coeff p1 i) + (coeff q i)) ((coeff p2 i) + (coeff q i));
      transitivity (coeff (poly_add p1 q) i) ((coeff p2 i) + (coeff q i)) (coeff (poly_add p2 q) i)
    in Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_add p1 q) (poly_add p2 q)

private let rec poly_add_right_congruence (#t:Type) {| cr: commutative_ring t |}
                                  (p q1 q2: polynomial t)
  : Lemma (requires poly_eq q1 q2)
          (ensures  poly_eq (poly_add p q1) (poly_add p q2))
  = let aux (i: nat) : Lemma (coeff (poly_add p q1) i = coeff (poly_add p q2) i) =
      poly_eq_means_equal_coeffs q1 q2 i;
      poly_add_coeff p q1 i;
      poly_add_coeff p q2 i;
      reflexivity (coeff p i);
      add_congruence (coeff p i) (coeff q1 i) (coeff p i) (coeff q2 i);
      symmetry (coeff (poly_add p q2) i) ((coeff p i) + (coeff q2 i));
      transitivity (coeff (poly_add p q1) i) ((coeff p i) + (coeff q1 i)) ((coeff p i) + (coeff q2 i));
      transitivity (coeff (poly_add p q1) i) ((coeff p i) + (coeff q2 i)) (coeff (poly_add p q2) i)
    in Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_add p q1) (poly_add p q2)

let poly_add_congruence (#t:Type) {| cr: commutative_ring t |}
                        (p1 q1 p2 q2: polynomial t)
  : Lemma (requires poly_eq p1 p2 /\ poly_eq q1 q2)
          (ensures  poly_eq (poly_add p1 q1) (poly_add p2 q2))
  = poly_add_left_congruence  p1 p2 q1;
    poly_add_right_congruence p2 q1 q2;
    poly_eq_transitivity (poly_add p1 q1) (poly_add p2 q1) (poly_add p2 q2)

let rec poly_add_commutativity (#t:Type) {| cr: commutative_ring t |}
                             (p q: polynomial t)
  : Lemma (poly_eq (poly_add p q) (poly_add q p))
  = let aux (i: nat) : Lemma (coeff (poly_add p q) i = coeff (poly_add q p) i) =
      poly_add_coeff p q i;
      poly_add_coeff q p i;
      add_commutativity (coeff p i) (coeff q i);
      symmetry (coeff (poly_add q p) i) ((coeff q i) + (coeff p i));
      transitivity (coeff (poly_add p q) i) ((coeff p i) + (coeff q i)) ((coeff q i) + (coeff p i));
      transitivity (coeff (poly_add p q) i) ((coeff q i) + (coeff p i)) (coeff (poly_add q p) i)
    in Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_add p q) (poly_add q p)

let rec poly_add_associativity (#t:Type) {| cr: commutative_ring t |}
                             (p q r: polynomial t)
  : Lemma (poly_eq (poly_add (poly_add p q) r) (poly_add p (poly_add q r)))
  = let lhs = poly_add (poly_add p q) r in
    let rhs = poly_add p (poly_add q r) in
    let aux (i: nat) : Lemma (coeff lhs i = coeff rhs i) =
      poly_add_coeff (poly_add p q) r i;
      poly_add_coeff p q i;
      poly_add_coeff p (poly_add q r) i;
      poly_add_coeff q r i;
      reflexivity (coeff r i);
      reflexivity (coeff p i);
      add_congruence (coeff (poly_add p q) i) (coeff r i) ((coeff p i) + (coeff q i)) (coeff r i);
      add_congruence (coeff p i) (coeff (poly_add q r) i) (coeff p i) ((coeff q i) + (coeff r i));
      add_associativity (coeff p i) (coeff q i) (coeff r i);
      let a = coeff p i in let b = coeff q i in let c = coeff r i in
      (* coeff lhs i = (coeff (p+q) i) + c = (a+b) + c
         coeff rhs i = a + (coeff (q+r) i) = a + (b+c) *)
      transitivity (coeff lhs i) ((coeff (poly_add p q) i) + c) ((a + b) + c);
      symmetry (coeff rhs i) (a + (coeff (poly_add q r) i));
      symmetry (a + (coeff (poly_add q r) i)) (a + (b + c));
      transitivity (a + (b + c)) (a + (coeff (poly_add q r) i)) (coeff rhs i);
      transitivity ((a + b) + c) (a + (b + c)) (coeff rhs i);
      transitivity (coeff lhs i) ((a + b) + c) (coeff rhs i)
    in Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs

let poly_add_zero (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (poly_eq (poly_add p (poly_zero #t)) p /\ poly_eq (poly_add (poly_zero #t) p) p)
  = poly_add_right_zero p;
    poly_add_left_zero p

(* negation *)

let rec poly_neg_congruence (#t:Type) {| cr: commutative_ring t |}
                            (p q: polynomial t)
  : Lemma (requires poly_eq p q) (ensures poly_eq (poly_neg p) (poly_neg q))
  = let aux (i: nat) : Lemma (coeff (poly_neg p) i = coeff (poly_neg q) i) =
      poly_eq_means_equal_coeffs p q i;
      poly_neg_coeff p i;
      poly_neg_coeff q i;
      neg_congruence (coeff p i) (coeff q i);
      symmetry (coeff (poly_neg q) i) (- (coeff q i));
      transitivity (coeff (poly_neg p) i) (- (coeff p i)) (- (coeff q i));
      transitivity (coeff (poly_neg p) i) (- (coeff q i)) (coeff (poly_neg q) i)
    in Classical.forall_intro aux;
    equal_coeffs_means_poly_eq (poly_neg p) (poly_neg q)

private let rec poly_add_negation_r (#t:Type) {| cr: commutative_ring t |}
                            (p: polynomial t)
  : Lemma (ensures poly_eq (poly_add p (poly_neg p)) (poly_zero #t))
          (decreases L.length p)
  = let lhs = poly_add p (poly_neg p) in
    let aux (i: nat) : Lemma (coeff lhs i = coeff (poly_zero #t) i) =
      poly_add_coeff p (poly_neg p) i;
      poly_neg_coeff p i;
      reflexivity (coeff p i);
      add_congruence (coeff p i) (coeff (poly_neg p) i) (coeff p i) (- (coeff p i));
      add_negation (coeff p i);
      transitivity (coeff lhs i) ((coeff p i) + (coeff (poly_neg p) i)) ((coeff p i) + (- (coeff p i)));
      transitivity (coeff lhs i) ((coeff p i) + (- (coeff p i))) (zero <: t);
      reflexivity (coeff (poly_zero #t) i);
      symmetry (coeff (poly_zero #t) i) (zero <: t);
      transitivity (coeff lhs i) (zero <: t) (coeff (poly_zero #t) i)
    in Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs (poly_zero #t)

private let rec poly_add_negation_l (#t:Type) {| cr: commutative_ring t |}
                            (p: polynomial t)
  : Lemma (ensures poly_eq (poly_add (poly_neg p) p) (poly_zero #t))
          (decreases L.length p)
  = poly_add_negation_r p;
    poly_add_commutativity (poly_neg p) p;
    poly_eq_transitivity (poly_add (poly_neg p) p) (poly_add p (poly_neg p)) (poly_zero #t)

let poly_add_negation (#t:Type) {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (poly_eq (poly_add (poly_neg p) p) (poly_zero #t) /\
           poly_eq (poly_add p (poly_neg p)) (poly_zero #t))
  = poly_add_negation_l p;
    poly_add_negation_r p

(* add_comm_group instance *)

let polynomial_acg (#t:Type) (cr: commutative_ring t) : add_comm_group (polynomial t #cr) = {
  acg_eq = polynomial_equatable cr;
  zero = poly_zero #t;
  add = poly_add;
  add_congruence = poly_add_congruence;
  add_commutativity = poly_add_commutativity;
  add_associativity = poly_add_associativity;
  add_zero = poly_add_zero;
  neg = poly_neg;
  neg_congruence = poly_neg_congruence;
  add_negation = poly_add_negation;
}


(* ---------------- Reveal lemmas for the polynomial_acg instance ---------------- *)

let polynomial_equatable_eq_reveal
  (#t:Type) (cr: commutative_ring t) (p q: polynomial t #cr)
  : Lemma ((polynomial_equatable cr).eq p q == poly_eq p q)
  = ()

let polynomial_acg_eq_reveal
  (#t:Type) (cr: commutative_ring t) (p q: polynomial t #cr)
  : Lemma ((polynomial_acg cr).acg_eq.eq p q == poly_eq p q)
  = ()

let polynomial_acg_add_reveal
  (#t:Type) (cr: commutative_ring t) (p q: polynomial t #cr)
  : Lemma ((polynomial_acg cr).add p q == poly_add p q)
  = ()

let polynomial_acg_zero_reveal
  (#t:Type) (cr: commutative_ring t)
  : Lemma ((polynomial_acg cr).zero == ([] <: polynomial t #cr))
  = ()

let polynomial_acg_neg_reveal
  (#t:Type) (cr: commutative_ring t) (p: polynomial t #cr)
  : Lemma ((polynomial_acg cr).neg p == poly_neg p)
  = ()

let poly_lc #t {| cr: commutative_ring t |} (p: polynomial t) 
  : t = if L.length p > 0 then L.last p else zero

let poly_deg #t {| cr: commutative_ring t |} (p: polynomial t) : option nat =
  if L.length p > 0 then Some (L.length p - 1) else None

(* ---------------- Multiplication: raw layer ---------------- *)

private let rec raw_scalar_mul #t {| cr: commutative_ring t |} (a: t) (q: list t) : list t =
  match q with
  | []      -> []
  | b :: q' -> (a * b) :: raw_scalar_mul a q'

private let rec raw_poly_mul #t {| cr: commutative_ring t |} (p q: list t) : list t =
  match p with
  | []      -> []
  | a :: p' ->
      poly_add_untrimmed (raw_scalar_mul a q) ((zero <: t) :: raw_poly_mul p' q)
(* ================================================================ *)
(*  Raw multiplicative layer: lemmas adopted from legacy proofs     *)
(*  (private; not exported).                                         *)
(* ================================================================ *)

private let rec raw_scalar_mul_kills_all_zero (#t:Type) {| cr: commutative_ring t |}
                                              (a: t) (q: list t)
  : Lemma (requires raw_all_zero q) (ensures raw_all_zero (raw_scalar_mul a q))
          (decreases L.length q)
  = match q with
    | []      -> ()
    | b :: q' ->
        reflexivity a;
        mul_congruence a b a (zero <: t);
        H.x_mul_zero a;
        transitivity (a * b) (a * (zero <: t)) (zero <: t);
        raw_scalar_mul_kills_all_zero a q'

private let rec raw_scalar_mul_zero_factor (#t:Type) {| cr: commutative_ring t |}
                                           (a: t) (q: list t)
  : Lemma (requires a = (zero <: t)) (ensures raw_all_zero (raw_scalar_mul a q))
          (decreases L.length q)
  = match q with
    | []      -> ()
    | b :: q' ->
        reflexivity b;
        mul_congruence a b (zero <: t) b;
        H.zero_mul_x b;
        transitivity (a * b) ((zero <: t) * b) (zero <: t);
        raw_scalar_mul_zero_factor a q'

private let rec raw_scalar_mul_right_cong (#t:Type) {| cr: commutative_ring t |}
                                          (a: t) (q1 q2: list t)
  : Lemma (requires raw_poly_eq q1 q2)
          (ensures  raw_poly_eq (raw_scalar_mul a q1) (raw_scalar_mul a q2))
          (decreases %[L.length q1; L.length q2])
  = match q1, q2 with
    | [], _  -> raw_scalar_mul_kills_all_zero a q2
    | _, []  -> raw_scalar_mul_kills_all_zero a q1
    | b1 :: q1', b2 :: q2' ->
        reflexivity a;
        mul_congruence a b1 a b2;
        raw_scalar_mul_right_cong a q1' q2'

private let rec raw_scalar_mul_left_cong (#t:Type) {| cr: commutative_ring t |}
                                         (a1 a2: t) (q: list t)
  : Lemma (requires a1 = a2)
          (ensures  raw_poly_eq (raw_scalar_mul a1 q) (raw_scalar_mul a2 q))
          (decreases L.length q)
  = match q with
    | []      -> ()
    | b :: q' ->
        reflexivity b;
        mul_congruence a1 b a2 b;
        raw_scalar_mul_left_cong a1 a2 q'

private let raw_scalar_mul_cong #t {| cr: commutative_ring t |}
                                (a b: t) (p q: list t)
  : Lemma (requires a = b /\ raw_poly_eq p q)
          (ensures raw_poly_eq (raw_scalar_mul a p) (raw_scalar_mul b q))
  = raw_scalar_mul_left_cong a b p;
    raw_scalar_mul_right_cong b p q;
    raw_poly_eq_trans (raw_scalar_mul a p) (raw_scalar_mul b p) (raw_scalar_mul b q)

private let rec raw_add_two_all_zero (#t:Type) {| cr: commutative_ring t |}
                                     (p q: list t)
  : Lemma (requires raw_all_zero p /\ raw_all_zero q)
          (ensures  raw_all_zero (poly_add_untrimmed p q))
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _ -> ()
    | _, [] -> ()
    | a :: p', b :: q' ->
        add_congruence a b (zero <: t) (zero <: t);
        add_zero (zero <: t);
        transitivity (a + b) ((zero <: t) + (zero <: t)) (zero <: t);
        raw_add_two_all_zero p' q'

private let rec raw_mul_left_all_zero (#t:Type) {| cr: commutative_ring t |}
                                      (p q: list t)
  : Lemma (requires raw_all_zero p) (ensures raw_all_zero (raw_poly_mul p q))
          (decreases L.length p)
  = match p with
    | []      -> ()
    | a :: p' ->
        raw_scalar_mul_zero_factor a q;
        raw_mul_left_all_zero p' q;
        reflexivity (zero <: t);
        let s = raw_scalar_mul a q in
        let r = (zero <: t) :: raw_poly_mul p' q in
        raw_add_two_all_zero s r

private let rec raw_mul_right_cong (#t:Type) {| cr: commutative_ring t |}
                                   (p q1 q2: list t)
  : Lemma (requires raw_poly_eq q1 q2)
          (ensures  raw_poly_eq (raw_poly_mul p q1) (raw_poly_mul p q2))
          (decreases L.length p)
  = match p with
    | []      -> ()
    | a :: p' ->
        raw_scalar_mul_right_cong a q1 q2;
        raw_mul_right_cong p' q1 q2;
        reflexivity (zero <: t);
        raw_add_cong
          (raw_scalar_mul a q1) ((zero <: t) :: raw_poly_mul p' q1)
          (raw_scalar_mul a q2) ((zero <: t) :: raw_poly_mul p' q2)

private let rec raw_mul_left_cong (#t:Type) {| cr: commutative_ring t |}
                                  (p1 p2 q: list t)
  : Lemma (requires raw_poly_eq p1 p2)
          (ensures  raw_poly_eq (raw_poly_mul p1 q) (raw_poly_mul p2 q))
          (decreases %[L.length p1; L.length p2])
  = match p1, p2 with
    | [], _ ->
        raw_mul_left_all_zero p2 q
    | _ :: _, [] ->
        raw_mul_left_all_zero p1 q
    | a :: p1', b :: p2' ->
        raw_scalar_mul_left_cong a b q;
        raw_mul_left_cong p1' p2' q;
        reflexivity (zero <: t);
        raw_add_cong
          (raw_scalar_mul a q) ((zero <: t) :: raw_poly_mul p1' q)
          (raw_scalar_mul b q) ((zero <: t) :: raw_poly_mul p2' q)

private let raw_mul_cong (#t:Type) {| cr: commutative_ring t |}
                         (p1 q1 p2 q2: list t)
  : Lemma (requires raw_poly_eq p1 p2 /\ raw_poly_eq q1 q2)
          (ensures  raw_poly_eq (raw_poly_mul p1 q1) (raw_poly_mul p2 q2))
  = raw_mul_left_cong  p1 p2 q1;
    raw_mul_right_cong p2 q1 q2;
    raw_poly_eq_trans (raw_poly_mul p1 q1) (raw_poly_mul p2 q1) (raw_poly_mul p2 q2)

private let rec raw_scalar_mul_one_left (#t:Type) {| cr: commutative_ring t |}
                                        (q: list t)
  : Lemma (ensures raw_poly_eq (raw_scalar_mul (one <: t) q) q)
          (decreases L.length q)
  = match q with
    | []      -> ()
    | b :: q' ->
        H.one_mul_x b;
        raw_scalar_mul_one_left q'

private let raw_mul_one_left (#t:Type) {| cr: commutative_ring t |}
                             (q: list t)
  : Lemma (raw_poly_eq (raw_poly_mul [ (one <: t) ] q) q)
  = raw_scalar_mul_one_left q;
    reflexivity (zero <: t);
    let r : list t = [ (zero <: t) ] in
    assert (raw_all_zero r);
    raw_add_right_all_zero (raw_scalar_mul (one <: t) q) r;
    raw_poly_eq_trans
      (raw_poly_mul [ (one <: t) ] q)
      (raw_scalar_mul (one <: t) q)
      q

private let rec raw_mul_one_right (#t:Type) {| cr: commutative_ring t |}
                                  (p: list t)
  : Lemma (ensures raw_poly_eq (raw_poly_mul p [ (one <: t) ]) p)
          (decreases L.length p)
  = match p with
    | []      -> ()
    | a :: p' ->
        H.x_mul_one a;
        H.x_plus_zero (a * (one <: t));
        transitivity ((a * (one <: t)) + (zero <: t)) (a * (one <: t)) a;
        raw_mul_one_right p'

private let rec raw_scalar_mul_distrib_right (#t:Type) {| cr: commutative_ring t |}
                                             (a: t) (q1 q2: list t)
  : Lemma (ensures raw_poly_eq (raw_scalar_mul a (poly_add_untrimmed q1 q2))
                               (poly_add_untrimmed (raw_scalar_mul a q1) (raw_scalar_mul a q2)))
          (decreases %[L.length q1; L.length q2])
  = match q1, q2 with
    | [], _ ->
        raw_poly_eq_refl (raw_scalar_mul a q2)
    | _, [] ->
        raw_poly_eq_refl (raw_scalar_mul a q1)
    | b1 :: q1', b2 :: q2' ->
        left_distributivity a b1 b2;
        raw_scalar_mul_distrib_right a q1' q2'

#push-options "--z3rlimit 40"
private let rec raw_scalar_mul_distrib_left (#t:Type) {| cr: commutative_ring t |}
                                            (a b: t) (q: list t)
  : Lemma (ensures raw_poly_eq (raw_scalar_mul (add a b) q)
                               (poly_add_untrimmed (raw_scalar_mul a q) (raw_scalar_mul b q)))
          (decreases L.length q)
  = match q with
    | [] -> ()
    | c :: q' ->
        right_distributivity c a b;
        raw_scalar_mul_distrib_left #t #cr a b q'
#pop-options

private let raw_cons_zero_add (#t:Type) {| cr: commutative_ring t |}
                              (q1 q2: list t)
  : Lemma (raw_poly_eq ((zero <: t) :: poly_add_untrimmed q1 q2)
                       (poly_add_untrimmed ((zero <: t) :: q1) ((zero <: t) :: q2)))
  = add_zero (zero <: t);
    symmetry ((zero <: t) + (zero <: t)) (zero <: t);
    raw_poly_eq_refl (poly_add_untrimmed q1 q2)

#push-options "--z3rlimit 40"
private let raw_add_swap_4 (#t:Type) {| cr: commutative_ring t |}
                           (a b c d: list t)
  : Lemma (raw_poly_eq (poly_add_untrimmed (poly_add_untrimmed a b) (poly_add_untrimmed c d))
                       (poly_add_untrimmed (poly_add_untrimmed a c) (poly_add_untrimmed b d)))
  = let bc  = poly_add_untrimmed b c in
    let cb  = poly_add_untrimmed c b in
    let cd  = poly_add_untrimmed c d in
    let bd  = poly_add_untrimmed b d in
    let ac  = poly_add_untrimmed a c in
    let s1 = poly_add_untrimmed (poly_add_untrimmed a b) cd in
    let s2 = poly_add_untrimmed a (poly_add_untrimmed b cd) in
    let s3 = poly_add_untrimmed a (poly_add_untrimmed bc d) in
    let s4 = poly_add_untrimmed a (poly_add_untrimmed cb d) in
    let s5 = poly_add_untrimmed a (poly_add_untrimmed c bd) in
    let s6 = poly_add_untrimmed ac bd in
    raw_add_assoc a b cd;
    raw_add_assoc b c d;
    raw_poly_eq_sym (poly_add_untrimmed bc d) (poly_add_untrimmed b cd);
    raw_poly_eq_refl a;
    raw_add_cong a (poly_add_untrimmed b cd) a (poly_add_untrimmed bc d);
    raw_add_comm b c;
    raw_poly_eq_refl d;
    raw_add_cong bc d cb d;
    raw_poly_eq_refl a;
    raw_add_cong a (poly_add_untrimmed bc d) a (poly_add_untrimmed cb d);
    raw_add_assoc c b d;
    raw_poly_eq_refl a;
    raw_add_cong a (poly_add_untrimmed cb d) a (poly_add_untrimmed c bd);
    raw_add_assoc a c bd;
    raw_poly_eq_sym (poly_add_untrimmed ac bd) (poly_add_untrimmed a (poly_add_untrimmed c bd));
    raw_poly_eq_trans s1 s2 s3;
    raw_poly_eq_trans s1 s3 s4;
    raw_poly_eq_trans s1 s4 s5;
    raw_poly_eq_trans s1 s5 s6
#pop-options

#push-options "--z3rlimit 50"
private let rec raw_mul_right_distrib (#t:Type) {| cr: commutative_ring t |}
                                      (p q1 q2: list t)
  : Lemma (ensures raw_poly_eq (raw_poly_mul p (poly_add_untrimmed q1 q2))
                               (poly_add_untrimmed (raw_poly_mul p q1) (raw_poly_mul p q2)))
          (decreases L.length p)
  = match p with
    | []      ->
        raw_poly_eq_refl ([] <: list t)
    | a :: p' ->
        let za = raw_scalar_mul a (poly_add_untrimmed q1 q2) in
        let z1 = raw_scalar_mul a q1 in
        let z2 = raw_scalar_mul a q2 in
        let m1 = raw_poly_mul p' q1 in
        let m2 = raw_poly_mul p' q2 in
        let mc = raw_poly_mul p' (poly_add_untrimmed q1 q2) in
        let zr = (zero <: t) in
        raw_scalar_mul_distrib_right a q1 q2;
        raw_mul_right_distrib p' q1 q2;
        reflexivity zr;
        raw_cons_zero_add m1 m2;
        let lhs0 = poly_add_untrimmed za (zr :: mc) in
        let mid1 = poly_add_untrimmed (poly_add_untrimmed z1 z2) (zr :: mc) in
        let mid2 = poly_add_untrimmed (poly_add_untrimmed z1 z2) (zr :: (poly_add_untrimmed m1 m2)) in
        let mid3 = poly_add_untrimmed (poly_add_untrimmed z1 z2) (poly_add_untrimmed (zr :: m1) (zr :: m2)) in
        let rhs0 = poly_add_untrimmed (poly_add_untrimmed z1 (zr :: m1)) (poly_add_untrimmed z2 (zr :: m2)) in
        raw_poly_eq_refl (zr :: mc);
        raw_add_cong za (zr :: mc) (poly_add_untrimmed z1 z2) (zr :: mc);
        raw_poly_eq_refl (poly_add_untrimmed z1 z2);
        reflexivity zr;
        raw_add_cong (poly_add_untrimmed z1 z2) (zr :: mc) (poly_add_untrimmed z1 z2) (zr :: (poly_add_untrimmed m1 m2));
        raw_add_cong (poly_add_untrimmed z1 z2) (zr :: (poly_add_untrimmed m1 m2))
                     (poly_add_untrimmed z1 z2) (poly_add_untrimmed (zr :: m1) (zr :: m2));
        raw_add_swap_4 z1 z2 (zr :: m1) (zr :: m2);
        raw_poly_eq_trans lhs0 mid1 mid2;
        raw_poly_eq_trans lhs0 mid2 mid3;
        raw_poly_eq_trans lhs0 mid3 rhs0
#pop-options

#push-options "--z3rlimit 60"
private let rec raw_mul_left_distrib (#t:Type) {| cr: commutative_ring t |}
                                     (p1 p2 q: list t)
  : Lemma (ensures raw_poly_eq (raw_poly_mul (poly_add_untrimmed p1 p2) q)
                               (poly_add_untrimmed (raw_poly_mul p1 q) (raw_poly_mul p2 q)))
          (decreases %[L.length p1; L.length p2])
  = match p1, p2 with
    | [], _ ->
        raw_poly_eq_refl (raw_poly_mul p2 q)
    | _, [] ->
        raw_poly_eq_refl (raw_poly_mul p1 q)
    | a :: p1', b :: p2' ->
        let zr = (zero <: t) in
        let ab = add a b in
        let sab = raw_scalar_mul ab q in
        let sa  = raw_scalar_mul a q in
        let sb  = raw_scalar_mul b q in
        let m12 = raw_poly_mul (poly_add_untrimmed p1' p2') q in
        let m1  = raw_poly_mul p1' q in
        let m2  = raw_poly_mul p2' q in
        raw_scalar_mul_distrib_left a b q;
        raw_mul_left_distrib p1' p2' q;
        raw_cons_zero_add m1 m2;
        reflexivity zr;
        let lhs0 = poly_add_untrimmed sab (zr :: m12) in
        let mid1 = poly_add_untrimmed (poly_add_untrimmed sa sb) (zr :: m12) in
        let mid2 = poly_add_untrimmed (poly_add_untrimmed sa sb) (zr :: (poly_add_untrimmed m1 m2)) in
        let mid3 = poly_add_untrimmed (poly_add_untrimmed sa sb) (poly_add_untrimmed (zr :: m1) (zr :: m2)) in
        let rhs0 = poly_add_untrimmed (poly_add_untrimmed sa (zr :: m1)) (poly_add_untrimmed sb (zr :: m2)) in
        raw_poly_eq_refl (zr :: m12);
        raw_add_cong sab (zr :: m12) (poly_add_untrimmed sa sb) (zr :: m12);
        raw_poly_eq_refl (poly_add_untrimmed sa sb);
        raw_add_cong (poly_add_untrimmed sa sb) (zr :: m12)
                     (poly_add_untrimmed sa sb) (zr :: (poly_add_untrimmed m1 m2));
        raw_add_cong (poly_add_untrimmed sa sb) (zr :: (poly_add_untrimmed m1 m2))
                     (poly_add_untrimmed sa sb) (poly_add_untrimmed (zr :: m1) (zr :: m2));
        raw_add_swap_4 sa sb (zr :: m1) (zr :: m2);
        raw_poly_eq_trans lhs0 mid1 mid2;
        raw_poly_eq_trans lhs0 mid2 mid3;
        raw_poly_eq_trans lhs0 mid3 rhs0
#pop-options

private let rec raw_scalar_mul_assoc (#t:Type) {| cr: commutative_ring t |}
                                     (a b: t) (r: list t)
  : Lemma (ensures raw_poly_eq (raw_scalar_mul a (raw_scalar_mul b r))
                               (raw_scalar_mul (a * b) r))
          (decreases L.length r)
  = match r with
    | []      -> raw_poly_eq_refl ([] <: list t)
    | c :: r' ->
        mul_associativity a b c;
        symmetry (mul (mul a b) c) (mul a (mul b c));
        raw_scalar_mul_assoc a b r'

private let raw_mul_singleton (#t:Type) {| cr: commutative_ring t |}
                              (a: t) (q: list t)
  : Lemma (raw_poly_eq (raw_poly_mul (a :: ([] <: list t)) q) (raw_scalar_mul a q))
  = let r : list t = [ (zero <: t) ] in
    reflexivity (zero <: t);
    assert (raw_all_zero r);
    raw_add_right_all_zero (raw_scalar_mul a q) r

private let raw_scalar_mul_cons_zero (#t:Type) {| cr: commutative_ring t |}
                                     (a: t) (q: list t)
  : Lemma (raw_poly_eq (raw_scalar_mul a ((zero <: t) :: q))
                       ((zero <: t) :: raw_scalar_mul a q))
  = H.x_mul_zero a;
    raw_poly_eq_refl (raw_scalar_mul a q)

private let raw_mul_cons_zero_left (#t:Type) {| cr: commutative_ring t |}
                                   (p q: list t)
  : Lemma (raw_poly_eq (raw_poly_mul ((zero <: t) :: p) q)
                       ((zero <: t) :: raw_poly_mul p q))
  = reflexivity (zero <: t);
    raw_scalar_mul_zero_factor (zero <: t) q;
    raw_add_left_all_zero (raw_scalar_mul (zero <: t) q)
                          ((zero <: t) :: raw_poly_mul p q)

#push-options "--z3rlimit 60"
private let rec raw_scalar_mul_over_mul (#t:Type) {| cr: commutative_ring t |}
                                        (a: t) (q r: list t)
  : Lemma (ensures raw_poly_eq (raw_scalar_mul a (raw_poly_mul q r))
                               (raw_poly_mul (raw_scalar_mul a q) r))
          (decreases L.length q)
  = match q with
    | []      -> raw_poly_eq_refl ([] <: list t)
    | b :: q' ->
        let zr = (zero <: t) in
        let sa_b_r  = raw_scalar_mul a (raw_scalar_mul b r) in
        let ab_r    = raw_scalar_mul (a * b) r in
        let pmq'r   = raw_poly_mul q' r in
        let sa_pmq'r = raw_scalar_mul a pmq'r in
        let pm_saq'_r = raw_poly_mul (raw_scalar_mul a q') r in
        raw_scalar_mul_distrib_right a (raw_scalar_mul b r) (zr :: pmq'r);
        raw_scalar_mul_cons_zero a pmq'r;
        raw_scalar_mul_over_mul a q' r;
        reflexivity zr;
        raw_scalar_mul_assoc a b r;
        let lhs0 = raw_scalar_mul a (raw_poly_mul (b :: q') r) in
        let mid1 = poly_add_untrimmed sa_b_r (raw_scalar_mul a (zr :: pmq'r)) in
        let mid2 = poly_add_untrimmed sa_b_r (zr :: sa_pmq'r) in
        let mid3 = poly_add_untrimmed sa_b_r (zr :: pm_saq'_r) in
        let mid4 = poly_add_untrimmed ab_r (zr :: pm_saq'_r) in
        raw_poly_eq_refl sa_b_r;
        raw_add_cong sa_b_r (raw_scalar_mul a (zr :: pmq'r)) sa_b_r (zr :: sa_pmq'r);
        raw_add_cong sa_b_r (zr :: sa_pmq'r) sa_b_r (zr :: pm_saq'_r);
        raw_poly_eq_refl (zr :: pm_saq'_r);
        raw_add_cong sa_b_r (zr :: pm_saq'_r) ab_r (zr :: pm_saq'_r);
        raw_poly_eq_trans lhs0 mid1 mid2;
        raw_poly_eq_trans lhs0 mid2 mid3;
        raw_poly_eq_trans lhs0 mid3 mid4
#pop-options

#push-options "--z3rlimit 80"
private let rec raw_mul_assoc (#t:Type) {| cr: commutative_ring t |}
                              (p q r: list t)
  : Lemma (ensures raw_poly_eq (raw_poly_mul (raw_poly_mul p q) r)
                               (raw_poly_mul p (raw_poly_mul q r)))
          (decreases L.length p)
  = match p with
    | []      -> raw_poly_eq_refl ([] <: list t)
    | a :: p' ->
        let zr = (zero <: t) in
        let saq    = raw_scalar_mul a q in
        let pmp'q  = raw_poly_mul p' q in
        let pmqr   = raw_poly_mul q r in
        let pmp'qr = raw_poly_mul p' pmqr in
        let pm_pmp'q_r = raw_poly_mul pmp'q r in
        raw_mul_left_distrib saq (zr :: pmp'q) r;
        raw_scalar_mul_over_mul a q r;
        raw_poly_eq_sym (raw_scalar_mul a pmqr) (raw_poly_mul saq r);
        raw_mul_cons_zero_left pmp'q r;
        raw_mul_assoc p' q r;
        reflexivity zr;
        let lhs0 = raw_poly_mul (raw_poly_mul (a :: p') q) r in
        let mid1 = poly_add_untrimmed (raw_poly_mul saq r)
                                      (raw_poly_mul (zr :: pmp'q) r) in
        let mid2 = poly_add_untrimmed (raw_scalar_mul a pmqr)
                                      (raw_poly_mul (zr :: pmp'q) r) in
        let mid3 = poly_add_untrimmed (raw_scalar_mul a pmqr) (zr :: pm_pmp'q_r) in
        let mid4 = poly_add_untrimmed (raw_scalar_mul a pmqr) (zr :: pmp'qr) in
        raw_poly_eq_refl (raw_poly_mul (zr :: pmp'q) r);
        raw_add_cong (raw_poly_mul saq r) (raw_poly_mul (zr :: pmp'q) r)
                     (raw_scalar_mul a pmqr) (raw_poly_mul (zr :: pmp'q) r);
        raw_poly_eq_refl (raw_scalar_mul a pmqr);
        raw_add_cong (raw_scalar_mul a pmqr) (raw_poly_mul (zr :: pmp'q) r)
                     (raw_scalar_mul a pmqr) (zr :: pm_pmp'q_r);
        raw_add_cong (raw_scalar_mul a pmqr) (zr :: pm_pmp'q_r)
                     (raw_scalar_mul a pmqr) (zr :: pmp'qr);
        raw_poly_eq_trans lhs0 mid1 mid2;
        raw_poly_eq_trans lhs0 mid2 mid3;
        raw_poly_eq_trans lhs0 mid3 mid4
#pop-options

private let rec raw_mul_right_nil (#t:Type) {| cr: commutative_ring t |}
                                  (p: list t)
  : Lemma (ensures raw_all_zero (raw_poly_mul p ([] <: list t)))
          (decreases L.length p)
  = match p with
    | []      -> ()
    | _ :: p' ->
        raw_mul_right_nil p';
        reflexivity (zero <: t)

#push-options "--z3rlimit 60"
private let raw_add_swap_middle (#t:Type) {| cr: commutative_ring t |}
                                (a b z: list t)
  : Lemma (raw_poly_eq (poly_add_untrimmed a (poly_add_untrimmed b z))
                       (poly_add_untrimmed b (poly_add_untrimmed a z)))
  = raw_add_assoc a b z;
    raw_add_comm a b;
    raw_poly_eq_refl z;
    raw_add_cong (poly_add_untrimmed a b) z (poly_add_untrimmed b a) z;
    raw_add_assoc b a z;
    let lhs = poly_add_untrimmed a (poly_add_untrimmed b z) in
    let m1  = poly_add_untrimmed (poly_add_untrimmed a b) z in
    let m2  = poly_add_untrimmed (poly_add_untrimmed b a) z in
    let rhs = poly_add_untrimmed b (poly_add_untrimmed a z) in
    raw_poly_eq_sym m1 lhs;
    raw_poly_eq_trans lhs m1 m2;
    raw_poly_eq_trans lhs m2 rhs
#pop-options

#push-options "--z3rlimit 80"
private let rec raw_mul_right_cons (#t:Type) {| cr: commutative_ring t |}
                                   (p: list t) (a: t) (q': list t)
  : Lemma (ensures raw_poly_eq (raw_poly_mul p (a :: q'))
                               (poly_add_untrimmed (raw_scalar_mul a p)
                                                   ((zero <: t) :: raw_poly_mul p q')))
          (decreases L.length p)
  = match p with
    | []      -> reflexivity (zero <: t)
    | b :: p' ->
        raw_mul_right_cons p' a q';
        let smbq = raw_scalar_mul b q' in
        let pmp'q  = raw_poly_mul p' q' in
        let smap'  = raw_scalar_mul a p' in
        let zr : t = zero in
        let pmp'aq = raw_poly_mul p' (a :: q') in
        let zpmpq : list t = zr :: pmp'q in
        let lhs_tail = poly_add_untrimmed smbq pmp'aq in
        let mid1 = poly_add_untrimmed smbq (poly_add_untrimmed smap' zpmpq) in
        let mid2 = poly_add_untrimmed smap' (poly_add_untrimmed smbq zpmpq) in
        raw_poly_eq_refl smbq;
        raw_add_cong smbq pmp'aq smbq (poly_add_untrimmed smap' zpmpq);
        raw_add_swap_middle smbq smap' zpmpq;
        raw_poly_eq_trans lhs_tail mid1 mid2;
        mul_commutativity b a;
        reflexivity (zero <: t);
        add_congruence (b * a) (zero <: t) (a * b) (zero <: t);
        assert ((b * a) + (zero <: t) = (a * b) + (zero <: t))
#pop-options

#push-options "--z3rlimit 80"
private let rec raw_mul_comm (#t:Type) {| cr: commutative_ring t |}
                             (p q: list t)
  : Lemma (ensures raw_poly_eq (raw_poly_mul p q) (raw_poly_mul q p))
          (decreases L.length p)
  = match p with
    | [] -> raw_mul_right_nil q
    | a :: p' ->
        raw_mul_comm p' q;
        let smaq  = raw_scalar_mul a q in
        let zr : t = zero in
        let pmp'q = raw_poly_mul p' q in
        let pmqp' = raw_poly_mul q p' in
        let zpmpq : list t = zr :: pmp'q in
        let zpmqp : list t = zr :: pmqp' in
        reflexivity zr;
        raw_poly_eq_refl smaq;
        assert (raw_poly_eq zpmpq zpmqp);
        raw_add_cong smaq zpmpq smaq zpmqp;
        let lhs = poly_add_untrimmed smaq zpmpq in
        let mid = poly_add_untrimmed smaq zpmqp in
        raw_mul_right_cons q a p';
        let rhs = raw_poly_mul q (a :: p') in
        raw_poly_eq_sym rhs mid;
        raw_poly_eq_trans lhs mid rhs
#pop-options

private let rec poly_eq_implies_raw_poly_eq #t {| cr: commutative_ring t |}
                                            (p q: polynomial t)
  : Lemma (requires poly_eq p q) (ensures raw_poly_eq p q)
          (decreases L.length p)
  = match p, q with
    | [], [] -> ()
    | a :: p', b :: q' -> poly_eq_implies_raw_poly_eq p' q'

let poly_mul #t {| cr: commutative_ring t |} (p q: polynomial t) : polynomial t =
  trim (raw_poly_mul p q)

(* ================================================================ *)
(*  Trimmed multiplicative laws: bridge raw_* into the public layer *)
(* ================================================================ *)

let poly_mul_congruence #t {| cr: commutative_ring t |} (p1 q1 p2 q2: polynomial t)
  : Lemma (requires poly_eq p1 p2 /\ poly_eq q1 q2)
          (ensures  poly_eq (poly_mul p1 q1) (poly_mul p2 q2))
  = poly_eq_implies_raw_poly_eq p1 p2;
    poly_eq_implies_raw_poly_eq q1 q2;
    raw_mul_cong p1 q1 p2 q2;
    raw_eq_means_trim_poly_eq (raw_poly_mul p1 q1) (raw_poly_mul p2 q2)

#push-options "--z3rlimit 40"
let poly_mul_associativity #t {| cr: commutative_ring t |} (p q r: polynomial t)
  : Lemma (poly_eq (poly_mul (poly_mul p q) r) (poly_mul p (poly_mul q r)))
  = let mpq : list t = raw_poly_mul p q in
    let mqr : list t = raw_poly_mul q r in
    let lhs1 : list t = raw_poly_mul (trim mpq) r in
    let lhs2 : list t = raw_poly_mul mpq r in
    let rhs2 : list t = raw_poly_mul p mqr in
    let rhs1 : list t = raw_poly_mul p (trim mqr) in
    trim_raw_eq mpq;
    raw_poly_eq_sym mpq (trim mpq);
    raw_mul_left_cong (trim mpq) mpq r;
    raw_mul_assoc p q r;
    raw_poly_eq_trans lhs1 lhs2 rhs2;
    trim_raw_eq mqr;
    raw_mul_right_cong p mqr (trim mqr);
    raw_poly_eq_sym mqr (trim mqr);
    raw_mul_right_cong p mqr (trim mqr);
    raw_poly_eq_trans lhs1 rhs2 rhs1;
    raw_eq_means_trim_poly_eq lhs1 rhs1
#pop-options

let poly_mul_commutativity #t {| cr: commutative_ring t |} (p q: polynomial t)
  : Lemma (poly_eq (poly_mul p q) (poly_mul q p))
  = raw_mul_comm p q;
    raw_eq_means_trim_poly_eq (raw_poly_mul p q) (raw_poly_mul q p)

let poly_one #t {| cr: commutative_ring t |} : polynomial t =
  if one = zero #t then [] else
  [one #t]

(* Trivial-ring case (eq one zero) is handled by deriving p == [] from
   is_trimmed: in a trivial ring every element is propositionally zero,
   so any nonempty trimmed p contradicts is_trimmed. *)
let poly_mul_one #t {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (poly_eq (poly_mul p (poly_one #t)) p /\ poly_eq (poly_mul (poly_one #t) p) p)
  = if one = zero #t then begin
      match p with
      | [] -> poly_eq_reflexivity #t (poly_zero #t)
      | _ :: _ ->
          let a = L.last p in
          H.x_mul_one a;
          symmetry (a * one) a;
          reflexivity a;
          mul_congruence a one a (zero <: t);
          transitivity a (a * one) (a * (zero <: t));
          H.x_mul_zero a;
          transitivity a (a * (zero <: t)) (zero <: t)
    end else begin
      raw_mul_one_right p;
      raw_eq_means_trim_poly_eq (raw_poly_mul p [one #t]) p;
      trim_poly_does_nothing p;
      raw_mul_one_left p;
      raw_eq_means_trim_poly_eq (raw_poly_mul [one #t] p) p
    end

let poly_left_distributivity #t {| cr: commutative_ring t |} (p q r: polynomial t)
  : Lemma (poly_eq (poly_mul p (poly_add q r)) (poly_add (poly_mul p q) (poly_mul p r)))
  = let qr_raw : list t = poly_add_untrimmed q r in
    let mqr_raw : list t = raw_poly_mul p qr_raw in
    let m_trimmed_qr : list t = raw_poly_mul p (trim qr_raw) in
    let mq : list t = raw_poly_mul p q in
    let mr : list t = raw_poly_mul p r in
    let sum_raw : list t = poly_add_untrimmed mq mr in
    let sum_via_trims : list t = poly_add_untrimmed (trim mq) (trim mr) in
    trim_raw_eq qr_raw;
    raw_poly_eq_sym qr_raw (trim qr_raw);
    raw_mul_right_cong p qr_raw (trim qr_raw);
    raw_poly_eq_sym (raw_poly_mul p (trim qr_raw)) mqr_raw;
    raw_mul_right_distrib p q r;
    raw_poly_eq_trans m_trimmed_qr mqr_raw sum_raw;
    trim_raw_eq mq;
    trim_raw_eq mr;
    raw_add_cong mq mr (trim mq) (trim mr);
    raw_poly_eq_trans m_trimmed_qr sum_raw sum_via_trims;
    raw_eq_means_trim_poly_eq m_trimmed_qr sum_via_trims

let poly_right_distributivity #t {| cr: commutative_ring t |} (x y z: polynomial t)
  : Lemma (poly_eq (poly_mul (poly_add y z) x) (poly_add (poly_mul y x) (poly_mul z x)))
  = let yz_raw : list t = poly_add_untrimmed y z in
    let m_yz_x_raw : list t = raw_poly_mul yz_raw x in
    let m_trimmed_yzx : list t = raw_poly_mul (trim yz_raw) x in
    let my : list t = raw_poly_mul y x in
    let mz : list t = raw_poly_mul z x in
    let sum_raw : list t = poly_add_untrimmed my mz in
    let sum_via_trims : list t = poly_add_untrimmed (trim my) (trim mz) in
    trim_raw_eq yz_raw;
    raw_poly_eq_sym yz_raw (trim yz_raw);
    raw_mul_left_cong (trim yz_raw) yz_raw x;
    raw_poly_eq_sym (raw_poly_mul (trim yz_raw) x) m_yz_x_raw;
    raw_mul_left_distrib y z x;
    raw_poly_eq_trans m_trimmed_yzx m_yz_x_raw sum_raw;
    trim_raw_eq my;
    trim_raw_eq mz;
    raw_add_cong my mz (trim my) (trim mz);
    raw_poly_eq_trans m_trimmed_yzx sum_raw sum_via_trims;
    raw_eq_means_trim_poly_eq m_trimmed_yzx sum_via_trims

(* Placeholder: _poly_mul_zero_both lives just before the instance,
   after raw_mul_right_nil_all_zero / raw_all_zero_trim_nil are in scope. *)

let poly_deg_zero_is_none #t {| cr: commutative_ring t |} : squash (poly_deg (poly_zero #t) == None) = ()

let poly_deg_reveal #t {| cr: commutative_ring t |} (a: t) (p: polynomial t)
  : Lemma (poly_deg (a @ p) ==
           (match poly_deg p with
            | Some k -> Some (succ k)
            | None   -> if a = zero then None else Some 0)) = ()

let poly_lc_reveal #t {| cr: commutative_ring t |} (p: polynomial t) 
  : Lemma ((None? (poly_deg p) /\ poly_lc p == zero) \/ (Some? (poly_deg p) /\ poly_lc p == L.last p)) = ()


(* ================================================================ *)
(*  Layer 2 prerequisites: leading-coefficient theorem,             *)
(*  domain law, integral-domain helpers                             *)
(* ================================================================ *)

private let rec last_eq_index_simple #t (l: list t)
  : Lemma (requires L.length l > 0)
          (ensures  L.last l == L.index l (L.length l - 1))
          (decreases L.length l)
  = if L.length l > 1 then last_eq_index_simple (L.tl l)

private let rec raw_scalar_mul_length #t {| cr: commutative_ring t |}
                                      (a: t) (q: list t)
  : Lemma (ensures L.length (raw_scalar_mul a q) == L.length q)
          (decreases L.length q)
  = match q with
    | []      -> ()
    | _ :: q' -> raw_scalar_mul_length a q'

private let rec raw_scalar_mul_index #t {| cr: commutative_ring t |}
                                     (a: t) (q: list t) (i: nat)
  : Lemma (requires i < L.length q)
          (ensures  L.length (raw_scalar_mul a q) == L.length q /\
                    L.index (raw_scalar_mul a q) i == a * L.index q i)
          (decreases L.length q)
  = raw_scalar_mul_length a q;
    match q with
    | _ :: q' -> if i = 0 then () else raw_scalar_mul_index a q' (i - 1)

private let rec poly_add_untrimmed_length #t {| cr: commutative_ring t |}
                                          (p q: list t)
  : Lemma (ensures L.length (poly_add_untrimmed p q)
                   = (if L.length p > L.length q then L.length p else L.length q))
          (decreases %[L.length p; L.length q])
  = match p, q with
    | [], _              -> ()
    | _ :: _, []         -> ()
    | _ :: p', _ :: q'   -> poly_add_untrimmed_length p' q'

private let rec raw_mul_length #t {| cr: commutative_ring t |} (p q: list t)
  : Lemma (requires Cons? p /\ Cons? q)
          (ensures  L.length (raw_poly_mul p q) = L.length p + L.length q - 1)
          (decreases L.length p)
  = match p with
    | [_] ->
        let a = L.hd p in
        raw_scalar_mul_length a q;
        poly_add_untrimmed_length (raw_scalar_mul a q) ((zero <: t) :: [])
    | a :: p' ->
        raw_mul_length p' q;
        raw_scalar_mul_length a q;
        poly_add_untrimmed_length (raw_scalar_mul a q)
                                  ((zero <: t) :: raw_poly_mul p' q)

private let nonzero_under_eq #t {| add_comm_group t |} (x y: t)
  : Lemma (requires x = y /\ not (eq y zero)) (ensures not (eq x zero))
  = symmetry x y;
    Classical.move_requires (transitivity y x) (zero <: t)

#push-options "--z3rlimit 100"
private let rec raw_mul_last_index #t {| cr: commutative_ring t |}
                                   (p q: polynomial t)
  : Lemma (requires Cons? p /\ Cons? q)
          (ensures L.length (raw_poly_mul p q) = L.length p + L.length q - 1 /\
                   raw_coeff (raw_poly_mul p q) (L.length p + L.length q - 2)
                   = (L.last p) * (L.last q))
          (decreases L.length p) =
  raw_mul_length p q;
  let m = L.length q in
  let s = raw_scalar_mul (L.hd p) q in
  raw_scalar_mul_length (L.hd p) q;
  let r = raw_poly_mul p q in
  match p with
  | a :: [] ->
      let z1 : list t = (zero <: t) :: [] in
      let idx : nat = m - 1 in
      raw_add_coeff s z1 idx;
      raw_scalar_mul_index a q idx;
      last_eq_index_simple q;
      assert (raw_coeff s idx == a * L.last q);
      assert (raw_coeff z1 idx == (zero <: t));
      let v : t = a * L.last q in
      assert (L.last p == a);
      assert (v == (L.last p) * (L.last q));
      assert (raw_coeff r idx = (raw_coeff s idx) + (raw_coeff z1 idx));
      assert (raw_coeff r idx = v + (zero <: t));
      coef_add_zero_r v;
      transitivity (raw_coeff r idx) (v + (zero <: t)) v
  | a :: (b :: p'') ->
      let p' : list t = b :: p'' in
      assert (L.last p' == L.last p);
      assert (is_trimmed p');
      raw_mul_last_index p' q;
      raw_mul_length p' q;
      let n' = L.length p' in
      let idx : nat = n' + m - 1 in
      let r' = raw_poly_mul p' q in
      let u : list t = (zero <: t) :: r' in
      raw_add_coeff s u idx;
      assert (idx >= L.length s);
      assert (raw_coeff s idx == (zero <: t));
      assert (L.length r' = n' + m - 1);
      assert (idx < L.length u);
      assert (L.index u idx == L.index r' (idx - 1));
      assert (raw_coeff u idx == raw_coeff r' (idx - 1));
      let v : t = (L.last p') * (L.last q) in
      assert (raw_coeff r' (idx - 1) = v);
      reflexivity (raw_coeff r' (idx - 1));
      assert (raw_coeff u idx = raw_coeff r' (idx - 1));
      transitivity (raw_coeff u idx) (raw_coeff r' (idx - 1)) v;
      assert (raw_coeff u idx = v);
      assert (raw_coeff r idx = (raw_coeff s idx) + (raw_coeff u idx));
      assert (raw_coeff r idx = (zero <: t) + (raw_coeff u idx));
      coef_add_zero_l (raw_coeff u idx);
      transitivity (raw_coeff r idx) ((zero <: t) + (raw_coeff u idx)) (raw_coeff u idx);
      transitivity (raw_coeff r idx) (raw_coeff u idx) v;
      assert (v == (L.last p) * (L.last q))
#pop-options

private let rec raw_mul_right_nil_all_zero #t {| cr: commutative_ring t |}
                                           (p: list t)
  : Lemma (ensures raw_all_zero (raw_poly_mul p []))
          (decreases L.length p)
  = match p with
    | []      -> ()
    | _ :: p' ->
        raw_mul_right_nil_all_zero p';
        reflexivity (zero <: t)

private let rec raw_all_zero_trim_nil #t {| cr: commutative_ring t |}
                                      (p: list t)
  : Lemma (requires raw_all_zero p) (ensures trim p == [])
          (decreases L.length p)
  = match p with
    | []      -> ()
    | _ :: p' -> raw_all_zero_trim_nil p'

#push-options "--z3rlimit 80"
private let poly_mul_nonzero_in_id #t {| id: integral_domain t |}
                                   (p q: polynomial t)
  : Lemma (requires Cons? p /\ Cons? q)
          (ensures  Cons? (poly_mul p q) /\
                    L.length (poly_mul p q) =
                      Prims.op_Subtraction (Prims.op_Addition (L.length p) (L.length q)) 1)
  = raw_mul_last_index p q;
    let n = L.length p in
    let m = L.length q in
    let r = raw_poly_mul p q in
    let idx : nat = n + m - 2 in
    let lp = L.last p in
    let lq = L.last q in
    let lpq : t = lp * lq in
    assert (L.length r = n + m - 1);
    assert (raw_coeff r idx = lpq);
    assert (is_trimmed p);
    assert (is_trimmed q);
    assert (lp <> zero);
    assert (lq <> zero);
    assert (not (eq lp (zero <: t)));
    assert (not (eq lq (zero <: t)));
    domain_nonzero_mul_nonzero #t #(d_of_id t) lp lq;
    assert (not (eq lpq (zero <: t)));
    last_eq_index_simple r;
    assert (L.length r - 1 = idx);
    assert (L.last r == L.index r idx);
    assert (idx < L.length r);
    assert (L.index r idx == raw_coeff r idx);
    assert (L.last r == raw_coeff r idx);
    assert (L.last r = lpq);
    nonzero_under_eq (L.last r) lpq;
    assert (L.last r <> zero);
    assert (is_trimmed r);
    trim_poly_does_nothing r;
    assert (poly_mul p q == r)
#pop-options

private let poly_eq_nil_iff_nil #t {| cr: commutative_ring t |} (p: polynomial t)
  : Lemma (poly_eq p (poly_zero #t) <==> Nil? p)
  = match p with
    | [] -> ()
    | _ :: _ -> ()

#push-options "--z3rlimit 80"
let poly_domain_law #t {| id: integral_domain t |}
                    (p q: polynomial t)
  : Lemma ((poly_eq (poly_mul p q) (poly_zero #t)) <==>
           (poly_eq p (poly_zero #t) \/ poly_eq q (poly_zero #t)))
  = poly_eq_nil_iff_nil (poly_mul p q);
    poly_eq_nil_iff_nil p;
    poly_eq_nil_iff_nil q;
    (if Cons? p && Cons? q then poly_mul_nonzero_in_id p q);
    (match p, q with
     | [], _ ->
         assert (poly_mul p q == [])
     | _ :: _, [] ->
         raw_mul_right_nil_all_zero p;
         raw_all_zero_trim_nil (raw_poly_mul p [])
     | _ :: _, _ :: _ -> ())
#pop-options

(* ----------------------------------------------------------------
   Public degree-of-product lemma.

   In an integral_domain coefficient ring, multiplying two nonzero
   polynomials yields a nonzero polynomial whose degree is the sum
   of the degrees. Used by Core.Polynomial.Unique.
   ---------------------------------------------------------------- *)
#push-options "--z3rlimit 80 --fuel 2 --ifuel 2"
let poly_deg_mul #t {| id: integral_domain t |}
                 (p q: polynomial t)
  : Lemma (requires Some? (poly_deg p) /\ Some? (poly_deg q))
          (ensures  Some? (poly_deg (poly_mul p q)) /\
                    Some?.v (poly_deg (poly_mul p q)) ==
                    Prims.op_Addition (Some?.v (poly_deg p)) (Some?.v (poly_deg q)))
  = assert (Cons? p);
    assert (Cons? q);
    raw_mul_length p q;
    poly_mul_nonzero_in_id p q;
    assert (L.length (poly_mul p q) = Prims.op_Subtraction (Prims.op_Addition (L.length p) (L.length q)) 1)
#pop-options

(* ================================================================ *)
(*  poly_mul_cons_reveal: characterizing equation for *               *)
(*  Required by polynomial_integral_domain instance.                *)
(* ================================================================ *)

private let rec trim_nil_means_all_zero #t {| cr: commutative_ring t |}
                                       (p: list t)
  : Lemma (requires trim p == []) (ensures raw_all_zero p)
          (decreases L.length p)
  = match p with
    | []      -> ()
    | a :: p' ->
        trim_nil_means_all_zero p';
        ()

private let raw_coeff_singleton_zero_pmcr #t {| cr: commutative_ring t |} (i: nat)
  : Lemma (raw_coeff ([(zero <: t)] <: list t) i == (zero <: t))
  = if i = 0 then () else ()

private let rec raw_coeff_scalar_mul #t {| cr: commutative_ring t |}
                                     (a: t) (q: list t) (i: nat)
  : Lemma (ensures raw_coeff (raw_scalar_mul a q) i = a * (raw_coeff q i))
          (decreases q)
  = match q with
    | []      ->
        H.x_mul_zero a;
        symmetry (a * (zero <: t)) (zero <: t)
    | _ :: q' ->
        if i = 0 then reflexivity (a * (raw_coeff q 0))
        else raw_coeff_scalar_mul a q' (i - 1)

#push-options "--z3rlimit 60"
private let a_zero_coeff_pmcr #t {| cr: commutative_ring t |}
                              (a: t) (q: polynomial t) (i: nat)
  : Lemma (coeff (poly_mul (a @ poly_zero) q) i = raw_coeff (raw_scalar_mul a q) i)
  = let s : polynomial t = poly_mul (a @ poly_zero) q in
    let xi : t = raw_coeff (raw_scalar_mul a q) i in
    let azp : polynomial t = a @ poly_zero in
    let l_raw : list t = raw_poly_mul azp q in
    coeff_in_raw_eq s i;
    trim_preserves_coeff l_raw i;
    if a = (zero <: t) then begin
      assert (azp == ([] <: polynomial t));
      assert (l_raw == ([] <: list t));
      raw_scalar_mul_zero_factor a q;
      raw_all_zero_means_zero_coeffs (raw_scalar_mul a q) i;
      symmetry xi (zero <: t);
      reflexivity (coeff s i);
      transitivity (coeff s i) (zero <: t) xi
    end else begin
      assert (azp == ([a] <: polynomial t));
      assert (l_raw ==
        poly_add_untrimmed (raw_scalar_mul a q) ((zero <: t) :: ([] <: list t)));
      raw_add_coeff (raw_scalar_mul a q) [(zero <: t)] i;
      raw_coeff_singleton_zero_pmcr #t #cr i;
      let zi : t = raw_coeff [(zero <: t)] i in
      add_zero xi;
      reflexivity (coeff s i);
      transitivity (raw_coeff l_raw i) (xi + zi) xi;
      transitivity (coeff s i) (raw_coeff l_raw i) xi
    end
#pop-options

(* Public coefficient law for poly_mul (a @ poly_zero) — the "scalar mul"
   case.  coeff (poly_mul [a] q) i = a * coeff q i  (smart-cons makes
   a @ poly_zero == [] when a = zero, in which case both sides are zero). *)
#push-options "--z3rlimit 40"
let poly_mul_singleton_coeff #t {| cr: commutative_ring t |}
                             (a: t) (q: polynomial t) (i: nat)
  : Lemma (coeff (poly_mul (a @ poly_zero) q) i = a * (coeff q i))
  = a_zero_coeff_pmcr a q i;
    raw_coeff_scalar_mul a q i;
    coeff_in_raw_eq q i;
    reflexivity a;
    reflexivity (raw_coeff q i);
    mul_congruence a (raw_coeff q i) a (coeff q i);
    transitivity (raw_coeff (raw_scalar_mul a q) i)
                 (a * (raw_coeff q i))
                 (a * (coeff q i));
    transitivity (coeff (poly_mul (a @ poly_zero) q) i)
                 (raw_coeff (raw_scalar_mul a q) i)
                 (a * (coeff q i))
#pop-options

#push-options "--z3rlimit 60"
private let zero_pq_coeff_pmcr #t {| cr: commutative_ring t |}
                               (p q: polynomial t) (i: nat)
  : Lemma (coeff ((zero <: t) @ (poly_mul p q)) i =
           raw_coeff ((zero <: t) :: raw_poly_mul p q) i)
  = let pq : polynomial t = poly_mul p q in
    let lhs_poly : polynomial t = (zero <: t) @ pq in
    let yi : t = raw_coeff ((zero <: t) :: raw_poly_mul p q) i in
    reflexivity (zero <: t);
    coeff_in_raw_eq lhs_poly i;
    match pq with
    | [] ->
        assert (lhs_poly == ([] <: polynomial t));
        trim_nil_means_all_zero (raw_poly_mul p q);
        if i = 0 then begin
          reflexivity (zero <: t);
          symmetry yi (zero <: t);
          transitivity (coeff lhs_poly i) (zero <: t) yi
        end else begin
          raw_all_zero_means_zero_coeffs (raw_poly_mul p q) (i - 1);
          assert (yi == raw_coeff (raw_poly_mul p q) (i - 1));
          symmetry yi (zero <: t);
          transitivity (coeff lhs_poly i) (zero <: t) yi
        end
    | _ :: _ ->
        assert (lhs_poly == ((zero <: t) :: pq));
        if i = 0 then begin
          reflexivity (zero <: t);
          symmetry yi (zero <: t);
          transitivity (coeff lhs_poly i) (zero <: t) yi
        end else begin
          coeff_in_raw_eq pq (i - 1);
          trim_preserves_coeff (raw_poly_mul p q) (i - 1);
          reflexivity yi
        end
#pop-options

#push-options "--z3rlimit 60"
private let lhs_coeff_pmcr #t {| cr: commutative_ring t |}
                          (a: t) (p q: polynomial t) (i: nat)
  : Lemma (coeff (poly_mul (a @ p) q) i =
           (raw_coeff (raw_scalar_mul a q) i) +
           (raw_coeff ((zero <: t) :: raw_poly_mul p q) i))
  = let s : polynomial t = poly_mul (a @ p) q in
    let xi : t = raw_coeff (raw_scalar_mul a q) i in
    let yi : t = raw_coeff ((zero <: t) :: raw_poly_mul p q) i in
    let ap : polynomial t = a @ p in
    let l_raw : list t = raw_poly_mul ap q in
    coeff_in_raw_eq s i;
    trim_preserves_coeff l_raw i;
    match p with
    | [] ->
        if a = (zero <: t) then begin
          assert (ap == ([] <: polynomial t));
          assert (l_raw == ([] <: list t));
          raw_scalar_mul_zero_factor a q;
          raw_all_zero_means_zero_coeffs (raw_scalar_mul a q) i;
          raw_coeff_singleton_zero_pmcr #t #cr i;
          assert (yi == (zero <: t));
          add_congruence xi yi (zero <: t) (zero <: t);
          add_zero (zero <: t);
          transitivity (xi + yi) ((zero <: t) + (zero <: t)) (zero <: t);
          symmetry (xi + yi) (zero <: t);
          reflexivity (coeff s i);
          transitivity (coeff s i) (zero <: t) (xi + yi)
        end else begin
          assert (ap == ([a] <: polynomial t));
          assert (l_raw == poly_add_untrimmed (raw_scalar_mul a q) [(zero <: t)]);
          raw_add_coeff (raw_scalar_mul a q) [(zero <: t)] i;
          raw_coeff_singleton_zero_pmcr #t #cr i;
          assert (yi == raw_coeff [(zero <: t)] i);
          assert (yi == (zero <: t));
          reflexivity (xi + yi);
          transitivity (coeff s i) (raw_coeff l_raw i) (xi + yi)
        end
    | _ :: _ ->
        assert (ap == (a :: p));
        assert (l_raw == poly_add_untrimmed (raw_scalar_mul a q) ((zero <: t) :: raw_poly_mul p q));
        raw_add_coeff (raw_scalar_mul a q) ((zero <: t) :: raw_poly_mul p q) i;
        transitivity (coeff s i) (raw_coeff l_raw i) (xi + yi)
#pop-options

#push-options "--z3rlimit 80"
let poly_mul_reveal #t {| cr: commutative_ring t |}
                               (a: t) (p q: polynomial t)
  : Lemma (poly_eq (poly_mul (a @ p) q)
                   (poly_add (poly_mul (a @ poly_zero) q)
                             ((zero <: t) @ (poly_mul p q))))
  = let lhs : polynomial t = poly_mul (a @ p) q in
    let s1  : polynomial t = poly_mul (a @ poly_zero) q in
    let s2  : polynomial t = (zero <: t) @ (poly_mul p q) in
    let rhs : polynomial t = poly_add s1 s2 in
    let aux (i: nat) : Lemma (coeff lhs i = coeff rhs i) =
      poly_add_coeff s1 s2 i;
      a_zero_coeff_pmcr a q i;
      zero_pq_coeff_pmcr p q i;
      lhs_coeff_pmcr a p q i;
      let xi : t = raw_coeff (raw_scalar_mul a q) i in
      let yi : t = raw_coeff ((zero <: t) :: raw_poly_mul p q) i in
      add_congruence (coeff s1 i) (coeff s2 i) xi yi;
      symmetry (coeff rhs i) ((coeff s1 i) + (coeff s2 i));
      transitivity (coeff rhs i) ((coeff s1 i) + (coeff s2 i)) (xi + yi);
      symmetry (coeff rhs i) (xi + yi);
      transitivity (coeff lhs i) (xi + yi) (coeff rhs i)
    in
    Classical.forall_intro aux;
    equal_coeffs_means_poly_eq lhs rhs
#pop-options
private let _poly_mul_zero_both #t {| cr: commutative_ring t |} (q: polynomial t)
  : Lemma (poly_mul (poly_zero #t) q == poly_zero #t /\
           poly_mul q (poly_zero #t) == poly_zero #t)
  = raw_mul_right_nil_all_zero q;
    raw_all_zero_trim_nil (raw_poly_mul q [])

instance polynomial_commutative_ring_instance #t {| cr: commutative_ring t |} : polynomial_commutative_ring t = {
  pcr = {
    cr_r = {
      r_add = {
        acg_eq = polynomial_equatable cr;
        zero = poly_zero #t;
        add = poly_add;
        add_congruence = poly_add_congruence;
        add_commutativity = poly_add_commutativity;
        add_associativity = poly_add_associativity;
        add_zero = poly_add_zero;
        neg = poly_neg;
        neg_congruence = poly_neg_congruence;
        add_negation = poly_add_negation;
      };
      one = poly_one;
      mul = poly_mul;
      mul_congruence = poly_mul_congruence;
      mul_associativity = poly_mul_associativity;
      mul_one = poly_mul_one;
      left_distributivity = poly_left_distributivity;
      right_distributivity = poly_right_distributivity;
    };
    cr_mic = {
        mul_commutativity = poly_mul_commutativity
    }
  };
  poly_zero_reveal = ();
  poly_one_reveal = ();
  poly_mul_zero = _poly_mul_zero_both;
  lc = poly_lc;
  deg = poly_deg;
  deg_zero_is_none = poly_deg_zero_is_none;
  deg_reveal = poly_deg_reveal;
  lc_reveal = poly_lc_reveal;
}

(* ================================================================ *)
(*  polynomial_integral_domain instance                              *)
(* ================================================================ *)

let polynomial_one_ne_zero #t {| id: integral_domain t |}
  : Lemma (not (poly_eq (poly_one #t) (poly_zero #t)))
  = let h : squash(not(one `eq` zero #t)) = id.id_one_ne_zero in
    assert (not (one #t = zero #t));
    assert (poly_one #t == [one #t]);
    ()

instance polynomial_integral_domain_instance
    #t {| id: integral_domain t |}
  : polynomial_integral_domain t #id
       #(polynomial_commutative_ring_instance #t #(cr_of_id t)) =
  let d_inst : domain (polynomial t) = {
    d_r = (polynomial_commutative_ring_instance #t #(cr_of_id t)).pcr.cr_r;
    domain_law = poly_domain_law;
  } in
  polynomial_one_ne_zero #t #id;
  let id_inst : integral_domain (polynomial t) = {
    id_d = d_inst;
    id_mic = (polynomial_commutative_ring_instance #t #(cr_of_id t)).pcr.cr_mic;
    id_one_ne_zero = ();
  } in
  {
    pid = id_inst;
    pid_pcrc_coherence = ();
    poly_mul_cons_reveal = poly_mul_reveal;
  }