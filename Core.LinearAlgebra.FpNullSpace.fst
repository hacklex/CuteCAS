module Core.LinearAlgebra.FpNullSpace

(* ================================================================ *)
(*  Executable Gaussian elimination + null-space basis over the     *)
(*  finite prime field  fp p  (Core.Modular.PrimeField).            *)
(*                                                                   *)
(*  Representation: a matrix is a `list (list (fp p))` — a list of   *)
(*  rows, each row a `list (fp p)`.  All functions are Tot and       *)
(*  extraction-ready.  Field arithmetic goes through the concrete    *)
(*  fp operations (fp_add / fp_mul / fp_neg / fp_inv), which ARE the *)
(*  operations of the `fp_field p` instance; because `fp p` uses     *)
(*  `default_equatable`, field equality coincides with structural    *)
(*  `==`, so proofs are stated with `==`.                            *)
(*                                                                   *)
(*  Load-bearing correctness (for Berlekamp / S5):                   *)
(*    null_space_basis_in_kernel — every returned basis vector v     *)
(*    satisfies m . v = 0  (mat_vec_mul m v is the zero vector).     *)
(*  This is guaranteed by a verified per-vector kernel check baked   *)
(*  into null_space_basis (a "trust cap"), so (a) holds              *)
(*  UNCONDITIONALLY, independent of the RREF structural invariants.  *)
(* ================================================================ *)

module L = FStar.List.Tot
open Core.NumberTheory
open FStar.Math.Lemmas
open Core.Modular.PrimeField

(* ---------------------------------------------------------------- *)
(*  Vectors and the dot product                                     *)
(* ---------------------------------------------------------------- *)

let vector (p:int{p > 1}) = list (fp p)

(* dot r v = sum_k r_k * v_k  (stops at the shorter list; for equal
   lengths this is the honest inner product). *)
let rec dot (#p:int{p > 1}) (r v: vector p) : Tot (fp p) (decreases r) =
  match r, v with
  | a :: r', b :: v' -> fp_add (fp_mul a b) (dot r' v')
  | _ -> fp_zero p

let rec mat_vec_mul (#p:int{p > 1}) (m: list (vector p)) (v: vector p)
  : Tot (vector p) (decreases m) =
  match m with
  | [] -> []
  | row :: m' -> dot row v :: mat_vec_mul m' v

let rec is_zero_vec (#p:int{p > 1}) (w: vector p) : Tot bool (decreases w) =
  match w with
  | [] -> true
  | x :: w' -> (x = fp_zero p) && is_zero_vec w'

(* ---------------------------------------------------------------- *)
(*  fp arithmetic helper lemmas (all `==`, over p > 1)              *)
(* ---------------------------------------------------------------- *)

let fp_mul_zero (#p:int{p > 1}) (c: fp p)
  : Lemma (fp_mul c (fp_zero p) == fp_zero p /\ fp_mul (fp_zero p) c == fp_zero p)
  = assert (c * (fp_zero p) == 0);
    assert ((fp_zero p) * c == 0);
    small_mod 0 p

(* 2x2 additive regrouping: (w+x)+(y+z) = (w+y)+(x+z). *)
let fp_add_2x2 (#p:int{p > 1}) (w x y z: fp p)
  : Lemma (fp_add (fp_add w x) (fp_add y z) == fp_add (fp_add w y) (fp_add x z))
  = modulo_distributivity (w + x) (y + z) p;
    modulo_distributivity (w + y) (x + z) p

(* ---------------------------------------------------------------- *)
(*  Vector operations                                               *)
(* ---------------------------------------------------------------- *)

(* scale a whole vector by c *)
let rec vscale (#p:int{p > 1}) (c: fp p) (r: vector p) : Tot (vector p) (decreases r) =
  match r with
  | [] -> []
  | a :: r' -> fp_mul c a :: vscale c r'

(* pointwise sum (aligned for equal length) *)
let rec zip_add (#p:int{p > 1}) (a b: vector p) : Tot (vector p) (decreases a) =
  match a, b with
  | x :: a', y :: b' -> fp_add x y :: zip_add a' b'
  | [], _ -> b
  | _, [] -> a

(* a + c*b   (row-axpy) *)
let vaxpy (#p:int{p > 1}) (c: fp p) (b a: vector p) : vector p =
  zip_add a (vscale c b)

let rec vscale_length (#p:int{p > 1}) (c: fp p) (r: vector p)
  : Lemma (ensures L.length (vscale c r) == L.length r) (decreases r)
  = match r with [] -> () | _ :: r' -> vscale_length c r'

let rec zip_add_length (#p:int{p > 1}) (a b: vector p)
  : Lemma (requires L.length a == L.length b)
          (ensures L.length (zip_add a b) == L.length a)
          (decreases a)
  = match a, b with
    | _ :: a', _ :: b' -> zip_add_length a' b'
    | _ -> ()

let vaxpy_length (#p:int{p > 1}) (c: fp p) (b a: vector p)
  : Lemma (requires L.length a == L.length b)
          (ensures L.length (vaxpy c b a) == L.length a)
  = vscale_length c b; zip_add_length a (vscale c b)

(* ---------------------------------------------------------------- *)
(*  dot identities (the linearity spine)                            *)
(* ---------------------------------------------------------------- *)

(* dot (c .* r) v = c * dot r v *)
let rec dot_scale (#p:int{p > 1}) (c: fp p) (r v: vector p)
  : Lemma (ensures dot (vscale c r) v == fp_mul c (dot r v)) (decreases r)
  = match r, v with
    | a :: r', b :: v' ->
        dot_scale c r' v';
        // head: fp_mul (fp_mul c a) b = fp_mul c (fp_mul a b)
        fp_mul_associativity c a b;
        // dot (vscale c r) v = fp_add (fp_mul (fp_mul c a) b) (fp_mul c (dot r' v'))
        // want fp_mul c (fp_add (fp_mul a b) (dot r' v'))
        fp_left_distributivity c (fp_mul a b) (dot r' v')
    | _ ->
        // r = [] or v = []: both sides are c * 0
        fp_mul_zero c

(* dot (a + b) v = dot a v + dot b v  (aligned) *)
let rec dot_add (#p:int{p > 1}) (a b v: vector p)
  : Lemma (requires L.length a == L.length b)
          (ensures dot (zip_add a b) v == fp_add (dot a v) (dot b v))
          (decreases a)
  = match a, b with
    | x :: a', y :: b' ->
        (match v with
         | z :: v' ->
             dot_add a' b' v';
             // head fp_mul (fp_add x y) z = fp_add (fp_mul x z) (fp_mul y z)
             fp_right_distributivity z x y;
             // dot(zip_add a b) v = fp_add (fp_add (fp_mul x z) (fp_mul y z))
             //                             (fp_add (dot a' v') (dot b' v'))
             // want fp_add (fp_add (fp_mul x z) (dot a' v'))
             //             (fp_add (fp_mul y z) (dot b' v'))
             fp_add_2x2 (fp_mul x z) (fp_mul y z) (dot a' v') (dot b' v')
         | [] ->
             // dot everything with [] is 0; 0 + 0 = 0
             fp_add_zero (fp_zero p))
    | _ ->
        // equal length so both empty
        fp_add_zero (fp_zero p)

(* a + c*b linearity *)
let dot_axpy (#p:int{p > 1}) (c: fp p) (b a v: vector p)
  : Lemma (requires L.length a == L.length b)
          (ensures dot (vaxpy c b a) v == fp_add (dot a v) (fp_mul c (dot b v)))
  = vscale_length c b;
    dot_add a (vscale c b) v;
    dot_scale c b v

(* ---------------------------------------------------------------- *)
(*  Indexed helpers (all Tot, total, guarded)                       *)
(* ---------------------------------------------------------------- *)

let get (#p:int{p > 1}) (r: vector p) (i:nat) : fp p =
  if i < L.length r then L.index r i else fp_zero p

let rec set_idx (#p:int{p > 1}) (l: vector p) (i:nat) (x: fp p)
  : Tot (vector p) (decreases l) =
  match l with
  | [] -> []
  | h :: t -> if i = 0 then x :: t else h :: set_idx t (i - 1) x

let rec zeros (#p:int{p > 1}) (n:nat) : Tot (vector p) (decreases n) =
  if n = 0 then [] else fp_zero p :: zeros #p (n - 1)

(* ---------------------------------------------------------------- *)
(*  Gaussian elimination to row-echelon form                        *)
(* ---------------------------------------------------------------- *)

(* pull out the first row with a nonzero entry in column c. *)
let rec extract_pivot (#p:int{p > 1}) (c:nat) (rows: list (vector p))
  : Tot (option (vector p & list (vector p))) (decreases rows) =
  match rows with
  | [] -> None
  | r :: rest ->
    if get r c <> fp_zero p then Some (r, rest)
    else (match extract_pivot c rest with
          | None -> None
          | Some (pr, others) -> Some (pr, r :: others))

(* the extracted pivot row has a nonzero entry in column c. *)
let rec extract_pivot_nonzero (#p:int{p > 1}) (c:nat) (rows: list (vector p))
  : Lemma (ensures (match extract_pivot c rows with
                    | None -> True
                    | Some (pr, _) -> get pr c <> fp_zero p))
          (decreases rows) =
  match rows with
  | [] -> ()
  | r :: rest -> if get r c <> fp_zero p then () else extract_pivot_nonzero c rest

(* Column classification.  `classify cols rows c` produces exactly one
   tag per column c, c+1, ..., cols-1 (so the position in the output is
   the column index).  A column is a pivot column (carrying the
   normalized pivot row) or a free column.  In the pivot branch the
   pivot column is cleared in all rows below before recursing. *)
type coltag (p:int{p > 1}) =
  | CPivot : vector p -> coltag p
  | CFree  : coltag p

(* eliminate column c from row r using normalized pivot row pr1
   (whose entry at c is 1): r := r - r[c] * pr1. *)
let elim_step (#p:int{p > 1}) (c:nat) (pr1 r: vector p) : vector p =
  vaxpy (fp_neg (get r c)) pr1 r

(* ---------------------------------------------------------------- *)
(*  Row-operation kernel-preservation spine.  These say the          *)
(*  elementary operations do not change the solution set  m.v = 0:   *)
(*   - scaling a row that already dots to 0 keeps it dotting to 0;   *)
(*   - an elimination step (r := r - r[c].pr1) with a pivot row that  *)
(*     dots to 0 leaves EVERY continuing row's dot with v unchanged.  *)
(*  Hence a full elimination pass preserves the kernel.              *)
(* ---------------------------------------------------------------- *)

let dot_vscale_zero (#p:int{p > 1}) (c: fp p) (r v: vector p)
  : Lemma (requires dot r v == fp_zero p) (ensures dot (vscale c r) v == fp_zero p)
  = dot_scale c r v; fp_mul_zero c

let dot_elim_step_preserves (#p:int{p > 1}) (col:nat) (pr1 r v: vector p)
  : Lemma (requires dot pr1 v == fp_zero p /\ L.length r == L.length pr1)
          (ensures  dot (elim_step col pr1 r) v == dot r v)
  = dot_axpy (fp_neg (get r col)) pr1 r v;
    fp_mul_zero (fp_neg (get r col));
    fp_add_zero (dot r v)

(* an elimination step preserves the whole vector m.v of remaining rows *)
let rec mat_vec_mul_elim (#p:int{p > 1}) (col:nat) (pr1 v: vector p)
                         (rest: list (vector p))
  : Lemma (requires dot pr1 v == fp_zero p /\
                    L.for_all (fun (r: vector p) -> L.length r = L.length pr1) rest)
          (ensures  mat_vec_mul (L.map (elim_step col pr1) rest) v
                    == mat_vec_mul rest v)
          (decreases rest)
  = match rest with
    | [] -> ()
    | r :: t ->
        dot_elim_step_preserves col pr1 r v;
        mat_vec_mul_elim col pr1 v t

let rec classify (#p:int{is_prime p}) (cols:nat) (rows: list (vector p)) (c:nat{c <= cols})
  : Tot (r: list (coltag p){L.length r == cols - c}) (decreases (cols - c)) =
  if c = cols then []
  else (match extract_pivot c rows with
        | None -> CFree :: classify cols rows (c + 1)
        | Some (pr, rest) ->
            extract_pivot_nonzero c rows;
            let pr1 = vscale (fp_inv (get pr c)) pr in
            CPivot pr1 :: classify cols (L.map (elim_step c pr1) rest) (c + 1))

(* recover (column, pivot-row) pairs and free columns from the tags; the
   accumulator `start` is the column index of the head tag. *)
let rec tag_pivots (#p:int{p > 1}) (start:nat) (tags: list (coltag p))
  : Tot (list (nat & vector p)) (decreases tags) =
  match tags with
  | [] -> []
  | CPivot pr :: t -> (start, pr) :: tag_pivots (start + 1) t
  | CFree :: t -> tag_pivots (start + 1) t

let rec tag_frees (#p:int{p > 1}) (start:nat) (tags: list (coltag p))
  : Tot (list nat) (decreases tags) =
  match tags with
  | [] -> []
  | CPivot _ :: t -> tag_frees (start + 1) t
  | CFree :: t -> start :: tag_frees (start + 1) t

(* ---------------------------------------------------------------- *)
(*  Null-space basis: free-variable construction                    *)
(* ---------------------------------------------------------------- *)

(* one back-substitution step: solve the pivot variable at column
   (fst pcpr) from the current partial solution v. *)
let bstep (#p:int{p > 1}) (pcpr: nat & vector p) (v: vector p) : vector p =
  set_idx v (fst pcpr) (fp_neg (dot (snd pcpr) v))

(* build the free-variable basis vector for free column f by
   back-substitution over the echelon pivots (fold_right processes the
   deepest / largest-column pivot first). *)
let build_vec (#p:int{p > 1}) (cols:nat) (pivots: list (nat & vector p)) (f:nat)
  : vector p =
  L.fold_right bstep pivots (set_idx (zeros cols) f (fp_one p))

let null_space_candidates (#p:int{is_prime p}) (cols:nat) (m: list (vector p))
  : list (vector p) =
  let tags = classify cols m 0 in
  L.map (build_vec cols (tag_pivots 0 tags)) (tag_frees 0 tags)

let in_kernel_bool (#p:int{p > 1}) (m: list (vector p)) (v: vector p) : bool =
  is_zero_vec (mat_vec_mul m v)

(* The exported null-space basis.  The kernel check is a verified trust
   cap: every returned vector is GUARANTEED to lie in the kernel of m,
   independent of the RREF structural invariants. *)
let null_space_basis (#p:int{is_prime p}) (cols:nat) (m: list (vector p))
  : list (vector p) =
  L.filter (in_kernel_bool m) (null_space_candidates cols m)

(* ---------------------------------------------------------------- *)
(*  (a) CORRECTNESS: every basis vector is in the kernel of m        *)
(* ---------------------------------------------------------------- *)

let null_space_basis_in_kernel (#p:int{is_prime p}) (cols:nat)
                               (m: list (vector p)) (v: vector p)
  : Lemma (requires L.memP v (null_space_basis cols m))
          (ensures  is_zero_vec (mat_vec_mul m v))
  = L.mem_filter (in_kernel_bool m) (null_space_candidates cols m) v

let rec mat_vec_mul_length (#p:int{p > 1}) (m: list (vector p)) (v: vector p)
  : Lemma (ensures L.length (mat_vec_mul m v) == L.length m) (decreases m)
  = match m with [] -> () | _ :: m' -> mat_vec_mul_length m' v

let rec is_zero_vec_eq_zeros (#p:int{p > 1}) (w: vector p)
  : Lemma (requires is_zero_vec w) (ensures w == zeros (L.length w)) (decreases w)
  = match w with
    | [] -> ()
    | _ :: w' -> is_zero_vec_eq_zeros w'

(* (a) in the `mat_vec_mul m v == 0-vector` form S5 will consume. *)
let null_space_basis_in_kernel_zeros (#p:int{is_prime p}) (cols:nat)
                                     (m: list (vector p)) (v: vector p)
  : Lemma (requires L.memP v (null_space_basis cols m))
          (ensures  mat_vec_mul m v == zeros (L.length m))
  = null_space_basis_in_kernel cols m v;
    is_zero_vec_eq_zeros (mat_vec_mul m v);
    mat_vec_mul_length m v

(* ---------------------------------------------------------------- *)
(*  (b) DIMENSION: |candidates| == #cols - rank   (rank = #pivots)   *)
(* ---------------------------------------------------------------- *)

let rec tag_count (#p:int{p > 1}) (start:nat) (tags: list (coltag p))
  : Lemma (ensures L.length (tag_pivots start tags) + L.length (tag_frees start tags)
                   == L.length tags)
          (decreases tags)
  = match tags with
    | [] -> ()
    | CPivot _ :: t -> tag_count (start + 1) t
    | CFree :: t -> tag_count (start + 1) t

(* rank = number of pivot columns produced by the elimination. *)
let rank (#p:int{is_prime p}) (cols:nat) (m: list (vector p)) : nat =
  L.length (tag_pivots 0 (classify cols m 0))

let null_space_candidates_length (#p:int{is_prime p}) (cols:nat) (m: list (vector p))
  : Lemma (rank cols m <= cols /\
           L.length (null_space_candidates cols m) == cols - rank cols m)
  = let tags = classify cols m 0 in
    tag_count 0 tags;
    L.map_lemma (build_vec cols (tag_pivots 0 tags)) (tag_frees 0 tags)

(* ---------------------------------------------------------------- *)
(*  (b) INDEPENDENCE: the free-coordinate submatrix is the identity  *)
(*  i.e. the basis vector for free column f evaluates to 1 at f and   *)
(*  0 at every other free column g.  This certifies that the returned *)
(*  family of candidate vectors is linearly independent.             *)
(* ---------------------------------------------------------------- *)

let rec set_idx_length (#p:int{p > 1}) (l: vector p) (i:nat) (x: fp p)
  : Lemma (ensures L.length (set_idx l i x) == L.length l) (decreases l)
  = match l with [] -> () | _ :: t -> if i = 0 then () else set_idx_length t (i - 1) x

let rec zeros_length (#p:int{p > 1}) (n:nat)
  : Lemma (ensures L.length (zeros #p n) == n) (decreases n)
  = if n = 0 then () else zeros_length #p (n - 1)

let rec get_set_idx_same (#p:int{p > 1}) (l: vector p) (i:nat) (x: fp p)
  : Lemma (requires i < L.length l) (ensures get (set_idx l i x) i == x) (decreases l)
  = match l with
    | h :: t -> if i = 0 then () else (set_idx_length t (i - 1) x; get_set_idx_same t (i - 1) x)
    | [] -> ()

let rec get_set_idx_other (#p:int{p > 1}) (l: vector p) (i:nat) (x: fp p) (k:nat)
  : Lemma (requires k <> i) (ensures get (set_idx l i x) k == get l k) (decreases l)
  = match l with
    | [] -> ()
    | h :: t ->
        if i = 0 then ()
        else if k = 0 then ()
        else (set_idx_length t (i - 1) x; get_set_idx_other t (i - 1) x (k - 1))

let rec get_zeros (#p:int{p > 1}) (n:nat) (g:nat)
  : Lemma (ensures get (zeros #p n) g == fp_zero p) (decreases n)
  = if n = 0 then () else if g = 0 then () else get_zeros #p (n - 1) (g - 1)

(* free/pivot column-index bounds (implication form for free reuse) *)
let rec tag_frees_lb (#p:int{p > 1}) (start:nat) (tags: list (coltag p)) (g:nat)
  : Lemma (ensures L.mem g (tag_frees start tags) ==> g >= start) (decreases tags)
  = match tags with
    | [] -> ()
    | CPivot _ :: t -> tag_frees_lb (start + 1) t g
    | CFree :: t -> tag_frees_lb (start + 1) t g

let rec tag_frees_ub (#p:int{p > 1}) (start:nat) (tags: list (coltag p)) (g:nat)
  : Lemma (ensures L.mem g (tag_frees start tags) ==> g < start + L.length tags) (decreases tags)
  = match tags with
    | [] -> ()
    | CPivot _ :: t -> tag_frees_ub (start + 1) t g
    | CFree :: t -> tag_frees_ub (start + 1) t g

let rec tag_pivots_lb (#p:int{p > 1}) (start:nat) (tags: list (coltag p)) (pc:nat)
  : Lemma (ensures L.mem pc (L.map fst (tag_pivots start tags)) ==> pc >= start)
          (decreases tags)
  = match tags with
    | [] -> ()
    | CFree :: t -> tag_pivots_lb (start + 1) t pc
    | CPivot _ :: t -> tag_pivots_lb (start + 1) t pc

(* free columns are disjoint from pivot columns *)
let rec free_not_pivot (#p:int{p > 1}) (start:nat) (tags: list (coltag p)) (g:nat)
  : Lemma (requires L.mem g (tag_frees start tags))
          (ensures  ~(L.mem g (L.map fst (tag_pivots start tags))))
          (decreases tags)
  = match tags with
    | [] -> ()
    | CPivot _ :: t ->
        tag_frees_lb (start + 1) t g;      (* g >= start+1 > start *)
        free_not_pivot (start + 1) t g
    | CFree :: t ->
        if g = start then tag_pivots_lb (start + 1) t g   (* pivots >= start+1 > g *)
        else free_not_pivot (start + 1) t g

(* the back-substitution fold never touches a free (non-pivot) column *)
let rec fold_get_free (#p:int{p > 1}) (pivots: list (nat & vector p)) (v0: vector p) (g:nat)
  : Lemma (requires ~(L.mem g (L.map fst pivots)))
          (ensures  get (L.fold_right bstep pivots v0) g == get v0 g)
          (decreases pivots)
  = match pivots with
    | [] -> ()
    | ph :: pt ->
        fold_get_free pt v0 g;
        get_set_idx_other (L.fold_right bstep pt v0) (fst ph)
          (fp_neg (dot (snd ph) (L.fold_right bstep pt v0))) g

(* value of the free-column basis vector at any free column *)
let build_vec_free (#p:int{p > 1}) (cols:nat) (pivots: list (nat & vector p)) (f g:nat)
  : Lemma (requires ~(L.mem g (L.map fst pivots)) /\ f < cols)
          (ensures  get (build_vec cols pivots f) g
                    == (if g = f then fp_one p else fp_zero p))
  = let v0 = set_idx (zeros #p cols) f (fp_one p) in
    fold_get_free pivots v0 g;
    zeros_length #p cols;
    if g = f then get_set_idx_same (zeros #p cols) f (fp_one p)
    else (get_set_idx_other (zeros #p cols) f (fp_one p) g; get_zeros #p cols g)

(* INDEPENDENCE CERTIFICATE: the basis vector for free column f is 1 at f
   and 0 at every other free column g.  (Free-coordinate projection of the
   candidate family is the identity, hence the family is independent.) *)
let candidate_free_identity (#p:int{is_prime p}) (cols:nat) (m: list (vector p)) (f g:nat)
  : Lemma (requires (let tags = classify cols m 0 in
                     L.mem f (tag_frees 0 tags) /\ L.mem g (tag_frees 0 tags)))
          (ensures  (let tags = classify cols m 0 in
                     get (build_vec cols (tag_pivots 0 tags) f) g
                     == (if g = f then fp_one p else fp_zero p)))
  = let tags = classify cols m 0 in
    tag_frees_ub 0 tags f;
    free_not_pivot 0 tags g;
    build_vec_free cols (tag_pivots 0 tags) f g

(* ================================================================ *)
(*  EXACT NULLITY / back-substitution identity  (R2 gap C2)          *)
(*  Every free-variable candidate genuinely satisfies  m . v = 0.    *)
(* ================================================================ *)

(* ---------------------------------------------------------------- *)
(*  get through the coordinatewise vector operations                 *)
(* ---------------------------------------------------------------- *)

let get_cons (#p:int{p > 1}) (b: fp p) (t: vector p) (i:nat)
  : Lemma (requires i > 0) (ensures get (b :: t) i == get t (i - 1))
  = ()

let rec get_vscale (#p:int{p > 1}) (c: fp p) (r: vector p) (i:nat)
  : Lemma (requires i < L.length r)
          (ensures get (vscale c r) i == fp_mul c (get r i))
          (decreases r)
  = match r with
    | a :: r' ->
        vscale_length c r;
        if i = 0 then () else (vscale_length c r'; get_vscale c r' (i - 1))
    | [] -> ()

let rec get_zip_add (#p:int{p > 1}) (a b: vector p) (i:nat)
  : Lemma (requires L.length a == L.length b /\ i < L.length a)
          (ensures get (zip_add a b) i == fp_add (get a i) (get b i))
          (decreases a)
  = match a, b with
    | x :: a', y :: b' ->
        zip_add_length a b;
        if i = 0 then () else (zip_add_length a' b'; get_zip_add a' b' (i - 1))
    | _ -> ()

(* ---------------------------------------------------------------- *)
(*  single-coordinate update inside a dot product                    *)
(* ---------------------------------------------------------------- *)

(* if the row is 0 at column i, updating v[i] leaves the dot unchanged *)
let rec dot_set_idx_zero (#p:int{p > 1}) (pr v: vector p) (i:nat) (x: fp p)
  : Lemma (requires get pr i == fp_zero p)
          (ensures dot pr (set_idx v i x) == dot pr v)
          (decreases pr)
  = match pr, v with
    | b :: pr', a :: v' ->
        if i = 0 then (fp_mul_zero b)
        else (get_cons b pr' i; dot_set_idx_zero pr' v' (i - 1) x)
    | _ -> ()

(* if v is 0 at column i, updating v[i]:=x adds pr[i]*x to the dot *)
let rec dot_set_idx_vzero (#p:int{p > 1}) (pr v: vector p) (i:nat) (x: fp p)
  : Lemma (requires get v i == fp_zero p /\ i < L.length v /\ i < L.length pr)
          (ensures dot pr (set_idx v i x)
                   == fp_add (dot pr v) (fp_mul (get pr i) x))
          (decreases pr)
  = match pr, v with
    | b :: pr', a :: v' ->
        if i = 0 then
          (fp_mul_zero b;
           fp_add_zero (dot pr' v');
           fp_add_commutativity (fp_mul b x) (dot pr' v'))
        else
          (get_cons b pr' i; get_cons a v' i;
           dot_set_idx_vzero pr' v' (i - 1) x;
           fp_add_associativity (fp_mul b a) (dot pr' v') (fp_mul (get pr i) x))
    | _ -> ()

(* ---------------------------------------------------------------- *)
(*  a row that is zero on all its coordinates dots to zero           *)
(* ---------------------------------------------------------------- *)

let rec dot_zeros (#p:int{p > 1}) (n:nat) (v: vector p)
  : Lemma (ensures dot (zeros #p n) v == fp_zero p) (decreases n)
  = if n = 0 then ()
    else match v with
      | b :: v' -> fp_mul_zero b; fp_add_zero (fp_zero p); dot_zeros #p (n - 1) v'
      | [] -> ()

let get_shift (#p:int{p > 1}) (a: fp p) (r': vector p) (k:nat)
  : Lemma (get (a :: r') (k + 1) == get r' k)
  = get_cons a r' (k + 1)

let rec zeroed_imp_eq_zeros (#p:int{p > 1}) (r: vector p)
  : Lemma (requires (forall (k:nat). k < L.length r ==> get r k == fp_zero p))
          (ensures r == zeros #p (L.length r))
          (decreases r)
  = match r with
    | [] -> ()
    | a :: r' ->
        introduce forall (k:nat). k < L.length r' ==> get r' k == fp_zero p
        with (get_shift a r' k);
        zeroed_imp_eq_zeros r'

let dot_all_zero (#p:int{p > 1}) (r v: vector p)
  : Lemma (requires (forall (k:nat). k < L.length r ==> get r k == fp_zero p))
          (ensures dot r v == fp_zero p)
  = zeroed_imp_eq_zeros r; dot_zeros #p (L.length r) v

(* ---------------------------------------------------------------- *)
(*  length of the back-substitution fold                             *)
(* ---------------------------------------------------------------- *)

let bstep_length (#p:int{p > 1}) (pcpr: nat & vector p) (v: vector p)
  : Lemma (L.length (bstep pcpr v) == L.length v)
  = set_idx_length v (fst pcpr) (fp_neg (dot (snd pcpr) v))

let rec fold_bstep_length (#p:int{p > 1}) (pvs: list (nat & vector p)) (v0: vector p)
  : Lemma (ensures L.length (L.fold_right bstep pvs v0) == L.length v0) (decreases pvs)
  = match pvs with
    | [] -> ()
    | h :: t -> fold_bstep_length t v0; bstep_length h (L.fold_right bstep t v0)

(* ---------------------------------------------------------------- *)
(*  Well-formedness predicates for the working row set and pivots    *)
(* ---------------------------------------------------------------- *)

(* a row is zero on all columns strictly below c *)
let row_zeroed_before (#p:int{p > 1}) (c:nat) (r: vector p) : prop =
  forall (k:nat). k < c ==> get r k == fp_zero p

let rec all_len (#p:int{p > 1}) (cols:nat) (rows: list (vector p)) : prop =
  match rows with [] -> True | r :: t -> L.length r == cols /\ all_len cols t

let rec all_zeroed (#p:int{p > 1}) (c:nat) (rows: list (vector p)) : prop =
  match rows with [] -> True | r :: t -> row_zeroed_before c r /\ all_zeroed c t

(* the list of echelon pivots is forward-echelon: strictly increasing
   pivot columns, each pivot row normalized (1 at its column) and zero
   on all earlier columns. *)
let rec pivots_wf (#p:int{p > 1}) (cols:nat) (start:nat) (pvs: list (nat & vector p))
  : Tot prop (decreases pvs) =
  match pvs with
  | [] -> True
  | (pc, pr) :: t ->
      start <= pc /\ pc < cols /\ L.length pr == cols /\
      get pr pc == fp_one p /\
      (forall (k:nat). k < pc ==> get pr k == fp_zero p) /\
      pivots_wf cols (pc + 1) t

(* v dots to zero against every pivot row *)
let rec pivots_kill (#p:int{p > 1}) (v: vector p) (pvs: list (nat & vector p)) : prop =
  match pvs with
  | [] -> True
  | (pc, pr) :: t -> dot pr v == fp_zero p /\ pivots_kill v t

(* membership extractors *)
let rec all_len_mem (#p:int{p > 1}) (cols:nat) (rows: list (vector p)) (r: vector p)
  : Lemma (requires all_len cols rows /\ L.memP r rows)
          (ensures L.length r == cols) (decreases rows)
  = match rows with
    | [] -> ()
    | r0 :: t -> if r = r0 then () else all_len_mem cols t r

let rec all_zeroed_mem (#p:int{p > 1}) (c:nat) (rows: list (vector p)) (r: vector p)
  : Lemma (requires all_zeroed c rows /\ L.memP r rows)
          (ensures row_zeroed_before c r) (decreases rows)
  = match rows with
    | [] -> ()
    | r0 :: t -> if r = r0 then () else all_zeroed_mem c t r

let rec all_zeroed_zero (#p:int{p > 1}) (rows: list (vector p))
  : Lemma (ensures all_zeroed 0 rows) (decreases rows)
  = match rows with [] -> () | _ :: t -> all_zeroed_zero t

let rec all_zeroed_succ (#p:int{p > 1}) (c:nat) (rows: list (vector p))
  : Lemma (requires all_zeroed c rows /\
                    (forall (r: vector p). L.memP r rows ==> get r c == fp_zero p))
          (ensures all_zeroed (c + 1) rows) (decreases rows)
  = match rows with
    | [] -> ()
    | r0 :: t -> all_zeroed_succ c t

let pivots_wf_relax (#p:int{p > 1}) (cols s1 s2:nat) (pvs: list (nat & vector p))
  : Lemma (requires pivots_wf cols s1 pvs /\ s2 <= s1)
          (ensures pivots_wf cols s2 pvs) (decreases pvs)
  = match pvs with [] -> () | (pc, pr) :: t -> ()

(* the head pivot column does not occur among the tail pivot columns *)
let rec pivots_wf_head_notin (#p:int{p > 1}) (cols pc:nat) (t: list (nat & vector p))
  : Lemma (requires pivots_wf cols (pc + 1) t)
          (ensures ~(L.mem pc (L.map fst t))) (decreases t)
  = match t with
    | [] -> ()
    | (pc2, pr2) :: t2 ->
        pivots_wf_relax cols (pc2 + 1) (pc + 1) t2;
        pivots_wf_head_notin cols pc t2

(* every tail pivot row is zero at a column strictly below its start *)
let rec pivots_wf_zero_below (#p:int{p > 1}) (cols s pc:nat) (t: list (nat & vector p))
                             (pc':nat) (pr': vector p)
  : Lemma (requires pivots_wf cols s t /\ pc < s /\ L.memP (pc', pr') t)
          (ensures get pr' pc == fp_zero p) (decreases t)
  = match t with
    | [] -> ()
    | (pc2, pr2) :: t2 ->
        if (pc2, pr2) = (pc', pr') then ()
        else (pivots_wf_relax cols (pc2 + 1) s t2;
              pivots_wf_zero_below cols s pc t2 pc' pr')

(* setting a below-start column preserves that v kills every tail pivot *)
let rec pivots_kill_set_idx (#p:int{p > 1}) (cols s pc:nat) (t: list (nat & vector p))
                            (w': vector p) (x: fp p)
  : Lemma (requires pivots_wf cols s t /\ pc < s /\ pivots_kill w' t)
          (ensures pivots_kill (set_idx w' pc x) t) (decreases t)
  = match t with
    | [] -> ()
    | (pc2, pr2) :: t2 ->
        pivots_wf_zero_below cols s pc t pc2 pr2;
        dot_set_idx_zero pr2 w' pc x;
        pivots_wf_relax cols (pc2 + 1) s t2;
        pivots_kill_set_idx cols s pc t2 w' x

(* ---------------------------------------------------------------- *)
(*  extract_pivot: structural facts under the working invariant      *)
(* ---------------------------------------------------------------- *)

let rec extract_pivot_some (#p:int{p > 1}) (cols c:nat) (rows: list (vector p))
                           (pr: vector p) (rest: list (vector p))
  : Lemma (requires extract_pivot c rows == Some (pr, rest) /\
                    all_len cols rows /\ all_zeroed c rows)
          (ensures L.length pr == cols /\ row_zeroed_before c pr /\
                   all_len cols rest /\ all_zeroed c rest /\
                   (forall (r: vector p). L.memP r rows ==> (r == pr \/ L.memP r rest)))
          (decreases rows)
  = match rows with
    | [] -> ()
    | r0 :: tl ->
        if get r0 c <> fp_zero p then ()
        else (match extract_pivot c tl with
              | None -> ()
              | Some (pr', others) -> extract_pivot_some cols c tl pr' others)

let rec extract_pivot_none_zero (#p:int{p > 1}) (c:nat) (rows: list (vector p)) (r: vector p)
  : Lemma (requires extract_pivot c rows == None /\ L.memP r rows)
          (ensures get r c == fp_zero p) (decreases rows)
  = match rows with
    | [] -> ()
    | r0 :: tl ->
        if get r0 c <> fp_zero p then ()
        else (match extract_pivot c tl with
              | Some _ -> ()
              | None -> if r = r0 then () else extract_pivot_none_zero c tl r)

(* ---------------------------------------------------------------- *)
(*  field cancellation and pivot normalization                       *)
(* ---------------------------------------------------------------- *)

let cancel_inv_mul (#p:int{is_prime p}) (a b: fp p)
  : Lemma (requires a <> fp_zero p /\ fp_mul (fp_inv a) b == fp_zero p)
          (ensures b == fp_zero p)
  = fp_inv_correct a;
    fp_mul_associativity a (fp_inv a) b;
    fp_mul_one b;
    fp_mul_zero a

let pivot_norm_zeroed (#p:int{is_prime p}) (cols c:nat) (pr: vector p)
  : Lemma (requires L.length pr == cols /\ c < cols /\ get pr c <> fp_zero p /\
                    row_zeroed_before c pr)
          (ensures (let pr1 = vscale (fp_inv (get pr c)) pr in
                    L.length pr1 == cols /\ get pr1 c == fp_one p /\ row_zeroed_before c pr1))
  = let ci = fp_inv (get pr c) in
    vscale_length ci pr;
    get_vscale ci pr c;
    fp_inv_correct (get pr c);
    introduce forall (k:nat). k < c ==> get (vscale ci pr) k == fp_zero p
    with (introduce _ ==> _ with _hk. (get_vscale ci pr k; fp_mul_zero ci))

(* ---------------------------------------------------------------- *)
(*  elimination step zeroes columns 0..c                             *)
(* ---------------------------------------------------------------- *)

let elim_zeroes (#p:int{p > 1}) (cols c:nat) (pr1 r: vector p) (k:nat)
  : Lemma (requires L.length r == cols /\ L.length pr1 == cols /\ c < cols /\ k < c + 1 /\
                    row_zeroed_before c pr1 /\ get pr1 c == fp_one p /\ row_zeroed_before c r)
          (ensures get (elim_step c pr1 r) k == fp_zero p)
  = vscale_length (fp_neg (get r c)) pr1;
    get_zip_add r (vscale (fp_neg (get r c)) pr1) k;
    get_vscale (fp_neg (get r c)) pr1 k;
    if k < c then (fp_mul_zero (fp_neg (get r c)); fp_add_zero (fp_zero p))
    else (fp_mul_one (fp_neg (get r c)); fp_add_negation (get r c))

let rec map_elim_len (#p:int{p > 1}) (cols c:nat) (pr1: vector p) (rest: list (vector p))
  : Lemma (requires all_len cols rest /\ L.length pr1 == cols)
          (ensures all_len cols (L.map (elim_step c pr1) rest)) (decreases rest)
  = match rest with
    | [] -> ()
    | r :: t ->
        vaxpy_length (fp_neg (get r c)) pr1 r;
        map_elim_len cols c pr1 t

let rec map_elim_zeroed (#p:int{p > 1}) (cols c:nat) (pr1: vector p) (rest: list (vector p))
  : Lemma (requires all_len cols rest /\ L.length pr1 == cols /\ c < cols /\
                    row_zeroed_before c pr1 /\ get pr1 c == fp_one p /\ all_zeroed c rest)
          (ensures all_zeroed (c + 1) (L.map (elim_step c pr1) rest)) (decreases rest)
  = match rest with
    | [] -> ()
    | r :: t ->
        introduce forall (k:nat). k < c + 1 ==> get (elim_step c pr1 r) k == fp_zero p
        with (introduce _ ==> _ with _hk. elim_zeroes cols c pr1 r k);
        map_elim_zeroed cols c pr1 t

(* ---------------------------------------------------------------- *)
(*  RREF structural invariant:  classify produces a well-formed      *)
(*  forward-echelon pivot list.                                      *)
(* ---------------------------------------------------------------- *)

let rec classify_pivots_wf (#p:int{is_prime p}) (cols:nat) (rows: list (vector p)) (c:nat{c <= cols})
  : Lemma (requires all_len cols rows /\ all_zeroed c rows)
          (ensures pivots_wf cols c (tag_pivots c (classify cols rows c)))
          (decreases (cols - c))
  = if c = cols then ()
    else match extract_pivot c rows with
      | None ->
          introduce forall (r: vector p). L.memP r rows ==> get r c == fp_zero p
          with (introduce _ ==> _ with _m. extract_pivot_none_zero c rows r);
          all_zeroed_succ c rows;
          classify_pivots_wf cols rows (c + 1);
          pivots_wf_relax cols (c + 1) c (tag_pivots (c + 1) (classify cols rows (c + 1)))
      | Some (pr, rest) ->
          extract_pivot_nonzero c rows;
          extract_pivot_some cols c rows pr rest;
          pivot_norm_zeroed cols c pr;
          let pr1 = vscale (fp_inv (get pr c)) pr in
          map_elim_len cols c pr1 rest;
          map_elim_zeroed cols c pr1 rest;
          classify_pivots_wf cols (L.map (elim_step c pr1) rest) (c + 1)

(* ---------------------------------------------------------------- *)
(*  Kernel-preservation:  if v kills every echelon pivot row, then v *)
(*  kills every ORIGINAL row of the working set.                     *)
(* ---------------------------------------------------------------- *)

let rec classify_rows_zero (#p:int{is_prime p}) (cols:nat) (rows: list (vector p))
                           (c:nat{c <= cols}) (v: vector p)
  : Lemma (requires all_len cols rows /\ all_zeroed c rows /\
                    pivots_kill v (tag_pivots c (classify cols rows c)))
          (ensures (forall (r: vector p). L.memP r rows ==> dot r v == fp_zero p))
          (decreases (cols - c))
  = if c = cols then
      (introduce forall (r: vector p). L.memP r rows ==> dot r v == fp_zero p
       with (introduce _ ==> _ with _mem.
             (all_len_mem cols rows r; all_zeroed_mem cols rows r; dot_all_zero r v)))
    else match extract_pivot c rows with
      | None ->
          introduce forall (r: vector p). L.memP r rows ==> get r c == fp_zero p
          with (introduce _ ==> _ with _m. extract_pivot_none_zero c rows r);
          all_zeroed_succ c rows;
          classify_rows_zero cols rows (c + 1) v
      | Some (pr, rest) ->
          extract_pivot_nonzero c rows;
          extract_pivot_some cols c rows pr rest;
          pivot_norm_zeroed cols c pr;
          let pr1 = vscale (fp_inv (get pr c)) pr in
          (* dot pr1 v == 0 is the head of the pivots_kill hypothesis *)
          assert (dot pr1 v == fp_zero p);
          (* hence dot pr v == 0 *)
          dot_scale (fp_inv (get pr c)) pr v;
          cancel_inv_mul (get pr c) (dot pr v);
          map_elim_len cols c pr1 rest;
          map_elim_zeroed cols c pr1 rest;
          classify_rows_zero cols (L.map (elim_step c pr1) rest) (c + 1) v;
          introduce forall (r: vector p). L.memP r rows ==> dot r v == fp_zero p
          with (introduce _ ==> _ with _mem.
                (if r = pr then ()
                 else (all_len_mem cols rest r;
                       L.memP_map_intro (elim_step c pr1) r rest;
                       dot_elim_step_preserves c pr1 r v)))

(* ---------------------------------------------------------------- *)
(*  BACK-SUBSTITUTION IDENTITY:  the fold builds a vector that kills  *)
(*  every echelon pivot row.                                         *)
(* ---------------------------------------------------------------- *)

let rec fold_kills_pivots (#p:int{p > 1}) (cols start:nat) (pvs: list (nat & vector p))
                          (v0: vector p)
  : Lemma (requires pivots_wf cols start pvs /\ L.length v0 == cols /\
                    (forall (pc:nat). L.mem pc (L.map fst pvs) ==> get v0 pc == fp_zero p))
          (ensures L.length (L.fold_right bstep pvs v0) == cols /\
                   pivots_kill (L.fold_right bstep pvs v0) pvs)
          (decreases pvs)
  = match pvs with
    | [] -> ()
    | (pc, pr) :: t ->
        fold_kills_pivots cols (pc + 1) t v0;
        let w' = L.fold_right bstep t v0 in
        pivots_wf_head_notin cols pc t;
        fold_get_free t v0 pc;
        (* dot pr w == 0 where w = set_idx w' pc (- dot pr w') *)
        dot_set_idx_vzero pr w' pc (fp_neg (dot pr w'));
        fp_mul_one (fp_neg (dot pr w'));
        fp_add_negation (dot pr w');
        (* v kills all the tail pivots too *)
        pivots_kill_set_idx cols (pc + 1) pc t w' (fp_neg (dot pr w'));
        bstep_length (pc, pr) w'

(* the free-variable init vector is zero at every pivot column *)
let build_init_zero_at_pivots (#p:int{is_prime p}) (cols:nat) (tags: list (coltag p)) (f:nat)
  : Lemma (requires L.mem f (tag_frees 0 tags))
          (ensures (let v0 = set_idx (zeros #p cols) f (fp_one p) in
                    L.length v0 == cols /\
                    (forall (pc:nat). L.mem pc (L.map fst (tag_pivots 0 tags))
                                      ==> get v0 pc == fp_zero p)))
  = zeros_length #p cols;
    set_idx_length (zeros #p cols) f (fp_one p);
    free_not_pivot 0 tags f;
    introduce forall (pc:nat). L.mem pc (L.map fst (tag_pivots 0 tags))
                               ==> get (set_idx (zeros #p cols) f (fp_one p)) pc == fp_zero p
    with (introduce _ ==> _ with _mp.
          (get_set_idx_other (zeros #p cols) f (fp_one p) pc; get_zeros #p cols pc))

(* pointwise-zero dot products give a zero matrix-vector product *)
let rec dots_zero_imp_zerovec (#p:int{p > 1}) (m: list (vector p)) (v: vector p)
  : Lemma (requires (forall (r: vector p). L.memP r m ==> dot r v == fp_zero p))
          (ensures is_zero_vec (mat_vec_mul m v)) (decreases m)
  = match m with
    | [] -> ()
    | _ :: t -> dots_zero_imp_zerovec t v

let rec filter_all_length (#a:Type) (pred: a -> bool) (l: list a)
  : Lemma (requires (forall (x:a). L.memP x l ==> pred x))
          (ensures L.length (L.filter pred l) == L.length l) (decreases l)
  = match l with
    | [] -> ()
    | _ :: t -> filter_all_length pred t

(* ================================================================ *)
(*  DELIVERABLE 1 — EXACT NULLITY                                    *)
(* ================================================================ *)

(* each free-variable candidate genuinely satisfies  m . v = 0 *)
let back_substitution_identity (#p:int{is_prime p}) (cols:nat) (m: list (vector p)) (f:nat)
  : Lemma (requires all_len cols m /\ L.mem f (tag_frees 0 (classify cols m 0)))
          (ensures is_zero_vec
                     (mat_vec_mul m (build_vec cols (tag_pivots 0 (classify cols m 0)) f)))
  = let tags = classify cols m 0 in
    let pivots = tag_pivots 0 tags in
    let v0 = set_idx (zeros #p cols) f (fp_one p) in
    let v = build_vec cols pivots f in
    all_zeroed_zero m;
    classify_pivots_wf cols m 0;
    build_init_zero_at_pivots cols tags f;
    fold_kills_pivots cols 0 pivots v0;
    classify_rows_zero cols m 0 v;
    dots_zero_imp_zerovec m v

(* every candidate lies in the kernel: the filter drops nothing *)
let candidate_in_kernel (#p:int{is_prime p}) (cols:nat) (m: list (vector p)) (v: vector p)
  : Lemma (requires all_len cols m /\ L.memP v (null_space_candidates cols m))
          (ensures in_kernel_bool m v)
  = let tags = classify cols m 0 in
    let pivots = tag_pivots 0 tags in
    L.memP_map_elim (build_vec cols pivots) v (tag_frees 0 tags);
    eliminate exists (f:nat). L.memP f (tag_frees 0 tags) /\ build_vec cols pivots f == v
    returns in_kernel_bool m v
    with pf.
      back_substitution_identity cols m f

(* EXACT NULLITY:  |null_space_basis| == cols - rank  (the filter is
   the identity because every candidate is in the kernel). *)
let null_space_basis_length_exact (#p:int{is_prime p}) (cols:nat) (m: list (vector p))
  : Lemma (requires all_len cols m)
          (ensures L.length (null_space_basis cols m) == cols - rank cols m)
  = let cands = null_space_candidates cols m in
    null_space_candidates_length cols m;
    introduce forall (v: vector p). L.memP v cands ==> in_kernel_bool m v
    with (introduce _ ==> _ with _mv. candidate_in_kernel cols m v);
    filter_all_length (in_kernel_bool m) cands

(* ================================================================ *)
(*  DELIVERABLE 2 — SPANNING (kernel vector determined by frees)     *)
(* ================================================================ *)

(* extracted rows are still members of the original working set *)
let rec extract_pivot_mem_orig (#p:int{p > 1}) (c:nat) (rows: list (vector p))
                               (pr: vector p) (rest: list (vector p)) (r: vector p)
  : Lemma (requires extract_pivot c rows == Some (pr, rest) /\ (r == pr \/ L.memP r rest))
          (ensures L.memP r rows) (decreases rows)
  = match rows with
    | [] -> ()
    | r0 :: tl ->
        if get r0 c <> fp_zero p then ()
        else (match extract_pivot c tl with
              | None -> ()
              | Some (pr', others) ->
                  if r = r0 then ()
                  else extract_pivot_mem_orig c tl pr' others r)

let rec extract_pivot_len (#p:int{p > 1}) (cols c:nat) (rows: list (vector p))
                          (pr: vector p) (rest: list (vector p))
  : Lemma (requires extract_pivot c rows == Some (pr, rest) /\ all_len cols rows)
          (ensures L.length pr == cols /\ all_len cols rest) (decreases rows)
  = match rows with
    | [] -> ()
    | r0 :: tl ->
        if get r0 c <> fp_zero p then ()
        else (match extract_pivot c tl with
              | None -> ()
              | Some (pr', others) -> extract_pivot_len cols c tl pr' others)

(* FORWARD kernel direction: if v kills every original row of m, it kills
   every echelon pivot row (the row operations preserve the dot). *)
let rec classify_pivots_killed (#p:int{is_prime p}) (cols:nat) (rows: list (vector p))
                               (c:nat{c <= cols}) (w: vector p)
  : Lemma (requires all_len cols rows /\
                    (forall (r: vector p). L.memP r rows ==> dot r w == fp_zero p))
          (ensures pivots_kill w (tag_pivots c (classify cols rows c)))
          (decreases (cols - c))
  = if c = cols then ()
    else match extract_pivot c rows with
      | None -> classify_pivots_killed cols rows (c + 1) w
      | Some (pr, rest) ->
          extract_pivot_nonzero c rows;
          extract_pivot_len cols c rows pr rest;
          let pr1 = vscale (fp_inv (get pr c)) pr in
          vscale_length (fp_inv (get pr c)) pr;
          (* dot pr1 w == 0 *)
          extract_pivot_mem_orig c rows pr rest pr;
          dot_scale (fp_inv (get pr c)) pr w;
          fp_mul_zero (fp_inv (get pr c));
          assert (dot pr1 w == fp_zero p);
          map_elim_len cols c pr1 rest;
          (* every eliminated row still dots to 0 *)
          introduce forall (r': vector p).
                      L.memP r' (L.map (elim_step c pr1) rest) ==> dot r' w == fp_zero p
          with (introduce _ ==> _ with _m'.
                (L.memP_map_elim (elim_step c pr1) r' rest;
                 eliminate exists (r: vector p). L.memP r rest /\ elim_step c pr1 r == r'
                 returns dot r' w == fp_zero p
                 with _pf.
                   (extract_pivot_mem_orig c rows pr rest r;
                    all_len_mem cols rest r;
                    dot_elim_step_preserves c pr1 r w)));
          classify_pivots_killed cols (L.map (elim_step c pr1) rest) (c + 1) w

(* dot of a row with a vector that is zero everywhere: zero. *)
let rec dot_second_zeros (#p:int{p > 1}) (r: vector p) (n:nat)
  : Lemma (ensures dot r (zeros #p n) == fp_zero p) (decreases r)
  = match r with
    | [] -> ()
    | b :: r' ->
        if n = 0 then ()
        else (fp_mul_zero b; fp_add_zero (fp_zero p); dot_second_zeros r' (n - 1))

(* a normalized pivot row isolates its own pivot coordinate: if v is zero on
   every column strictly above pc, then  dot pr v == v[pc]. *)
let rec dot_pivot_isolate (#p:int{p > 1}) (pr w: vector p) (pc:nat)
  : Lemma (requires get pr pc == fp_one p /\
                    (forall (k:nat). k < pc ==> get pr k == fp_zero p) /\
                    (forall (k:nat). k > pc ==> get w k == fp_zero p))
          (ensures dot pr w == get w pc) (decreases pr)
  = match pr, w with
    | b :: pr', a :: w' ->
        if pc = 0 then
          (introduce forall (k:nat). k < L.length w' ==> get w' k == fp_zero p
           with (introduce _ ==> _ with _hk. get_shift a w' k);
           zeroed_imp_eq_zeros w';
           dot_second_zeros pr' (L.length w');
           fp_mul_one a;
           fp_add_zero a)
        else
          (get_cons b pr' pc;
           introduce forall (k:nat). k < pc - 1 ==> get pr' k == fp_zero p
           with (introduce _ ==> _ with _hk. get_shift b pr' k);
           introduce forall (k:nat). k > pc - 1 ==> get w' k == fp_zero p
           with (introduce _ ==> _ with _hk. get_shift a w' k);
           get_shift a w' (pc - 1);
           fp_mul_zero a;
           fp_add_zero (dot pr' w');
           dot_pivot_isolate pr' w' (pc - 1))
    | _ -> ()

(* membership extractors for the pivot list *)
let rec pivots_wf_mem (#p:int{p > 1}) (cols s:nat) (pvs: list (nat & vector p))
                      (pc:nat) (pr: vector p)
  : Lemma (requires pivots_wf cols s pvs /\ L.memP (pc, pr) pvs)
          (ensures s <= pc /\ pc < cols /\ L.length pr == cols /\
                   get pr pc == fp_one p /\ (forall (k:nat). k < pc ==> get pr k == fp_zero p))
          (decreases pvs)
  = match pvs with
    | [] -> ()
    | (pc2, pr2) :: t ->
        if (pc2, pr2) = (pc, pr) then ()
        else pivots_wf_mem cols (pc2 + 1) t pc pr

let rec pivots_kill_mem (#p:int{p > 1}) (w: vector p) (pvs: list (nat & vector p))
                        (pc:nat) (pr: vector p)
  : Lemma (requires pivots_kill w pvs /\ L.memP (pc, pr) pvs)
          (ensures dot pr w == fp_zero p) (decreases pvs)
  = match pvs with
    | [] -> ()
    | (pc2, pr2) :: t ->
        if (pc2, pr2) = (pc, pr) then () else pivots_kill_mem w t pc pr

(* DOWNWARD elimination: a kernel vector that is zero on all non-pivot
   columns is zero at every column (each pivot coord is forced by the pivot
   rows dotting to zero, processing the largest pivot column first). *)
let rec forces_zero_at (#p:int{is_prime p}) (cols:nat) (pivots: list (nat & vector p))
                       (w: vector p) (j:nat)
  : Lemma (requires pivots_wf cols 0 pivots /\ pivots_kill w pivots /\ L.length w == cols /\
                    (forall (g:nat). g < cols /\ ~(L.mem g (L.map fst pivots))
                                     ==> get w g == fp_zero p))
          (ensures get w j == fp_zero p)
          (decreases (if j < cols then cols - j else 0))
  = if j >= cols then ()
    else if not (L.mem j (L.map fst pivots)) then ()
    else
      (L.memP_map_elim fst j pivots;
       eliminate exists (x: nat & vector p). L.memP x pivots /\ fst x == j
       returns get w j == fp_zero p
       with _pf.
         (let pr = snd x in
          assert (x == (j, pr));
          pivots_wf_mem cols 0 pivots j pr;
          pivots_kill_mem w pivots j pr;
          introduce forall (k:nat). k > j ==> get w k == fp_zero p
          with (introduce _ ==> _ with _hk.
                (if k < cols then forces_zero_at cols pivots w k else ()));
          dot_pivot_isolate pr w j))

(* SPANNING core: a kernel vector is uniquely determined by its free
   coordinates — if they all vanish, the whole vector vanishes. *)
let kernel_zero_frees_imp_zero (#p:int{is_prime p}) (cols:nat) (m: list (vector p)) (w: vector p)
  : Lemma (requires all_len cols m /\ L.length w == cols /\
                    (forall (r: vector p). L.memP r m ==> dot r w == fp_zero p) /\
                    (forall (g:nat). g < cols /\
                       ~(L.mem g (L.map fst (tag_pivots 0 (classify cols m 0))))
                       ==> get w g == fp_zero p))
          (ensures w == zeros #p cols)
  = let pivots = tag_pivots 0 (classify cols m 0) in
    all_zeroed_zero m;
    classify_pivots_wf cols m 0;
    classify_pivots_killed cols m 0 w;
    introduce forall (j:nat). j < L.length w ==> get w j == fp_zero p
    with (introduce _ ==> _ with _hj. forces_zero_at cols pivots w j);
    zeroed_imp_eq_zeros w

(* ---------------------------------------------------------------- *)
(*  fp additive-inverse facts (for the linear-combination packaging) *)
(* ---------------------------------------------------------------- *)

let fp_neg_zero (#p:int{p > 1}) : Lemma (fp_neg (fp_zero p) == fp_zero p)
  = cancel_mul_mod 1 p

let fp_neg_unique (#p:int{p > 1}) (a b: fp p)
  : Lemma (requires fp_add a b == fp_zero p) (ensures b == fp_neg a)
  = fp_add_zero b;
    fp_add_negation a;
    fp_add_associativity b a (fp_neg a);
    fp_add_commutativity a b;
    fp_add_zero (fp_neg a)

let fp_neg_mul (#p:int{p > 1}) (a b: fp p)
  : Lemma (fp_mul (fp_neg a) b == fp_neg (fp_mul a b))
  = fp_right_distributivity b a (fp_neg a);
    fp_add_negation a;
    fp_mul_zero b;
    fp_neg_unique (fp_mul a b) (fp_mul (fp_neg a) b)

let fp_neg_add (#p:int{p > 1}) (x y: fp p)
  : Lemma (fp_neg (fp_add x y) == fp_add (fp_neg x) (fp_neg y))
  = fp_add_2x2 x y (fp_neg x) (fp_neg y);
    fp_add_negation x; fp_add_negation y; fp_add_zero (fp_zero p);
    fp_neg_unique (fp_add x y) (fp_add (fp_neg x) (fp_neg y))

let rec dot_sym (#p:int{p > 1}) (a b: vector p)
  : Lemma (ensures dot a b == dot b a) (decreases a)
  = match a, b with
    | a0 :: a', b0 :: b' -> fp_mul_commutativity a0 b0; dot_sym a' b'
    | _ -> ()

(* ---------------------------------------------------------------- *)
(*  vector difference and extensionality                             *)
(* ---------------------------------------------------------------- *)

let rec vsub (#p:int{p > 1}) (a b: vector p) : Tot (vector p) (decreases a) =
  match a, b with
  | a0 :: a', b0 :: b' -> fp_add a0 (fp_neg b0) :: vsub a' b'
  | [], _ -> []
  | _, [] -> a

let rec vsub_length (#p:int{p > 1}) (a b: vector p)
  : Lemma (requires L.length a == L.length b)
          (ensures L.length (vsub a b) == L.length a) (decreases a)
  = match a, b with
    | _ :: a', _ :: b' -> vsub_length a' b'
    | _ -> ()

let rec get_vsub (#p:int{p > 1}) (a b: vector p) (j:nat)
  : Lemma (requires L.length a == L.length b /\ j < L.length a)
          (ensures get (vsub a b) j == fp_add (get a j) (fp_neg (get b j)))
          (decreases a)
  = match a, b with
    | a0 :: a', b0 :: b' ->
        vsub_length a b;
        if j = 0 then () else (vsub_length a' b'; get_vsub a' b' (j - 1))
    | _ -> ()

let rec dot_vsub_first (#p:int{p > 1}) (a b r: vector p)
  : Lemma (requires L.length a == L.length b)
          (ensures dot (vsub a b) r == fp_add (dot a r) (fp_neg (dot b r)))
          (decreases a)
  = match a, b with
    | a0 :: a', b0 :: b' ->
        (match r with
         | r0 :: r' ->
             dot_vsub_first a' b' r';
             fp_right_distributivity r0 a0 (fp_neg b0);
             fp_neg_mul b0 r0;
             fp_add_2x2 (fp_mul a0 r0) (fp_neg (fp_mul b0 r0))
                        (dot a' r') (fp_neg (dot b' r'));
             fp_neg_add (fp_mul b0 r0) (dot b' r')
         | [] -> fp_neg_zero #p; fp_add_zero (fp_zero p))
    | [], _ -> fp_neg_zero #p; fp_add_zero (fp_zero p)
    | _, [] -> ()

let rec vec_ext (#p:int{p > 1}) (a b: vector p)
  : Lemma (requires L.length a == L.length b /\
                    (forall (j:nat). j < L.length a ==> get a j == get b j))
          (ensures a == b) (decreases a)
  = match a, b with
    | a0 :: a', b0 :: b' ->
        introduce forall (j:nat). j < L.length a' ==> get a' j == get b' j
        with (introduce _ ==> _ with _hj. (get_shift a0 a' j; get_shift b0 b' j));
        vec_ext a' b'
    | _ -> ()

let fp_sub_zero_eq (#p:int{p > 1}) (a b: fp p)
  : Lemma (requires fp_add a (fp_neg b) == fp_zero p) (ensures a == b)
  = fp_add_commutativity a (fp_neg b);
    fp_neg_unique (fp_neg b) a;
    fp_add_negation b;
    fp_neg_unique (fp_neg b) b

(* ---------------------------------------------------------------- *)
(*  The linear combination  sum_f  v[f] . (candidate for f)          *)
(* ---------------------------------------------------------------- *)

let build_vec_length (#p:int{p > 1}) (cols:nat) (pivots: list (nat & vector p)) (f:nat)
  : Lemma (L.length (build_vec cols pivots f) == cols)
  = zeros_length #p cols;
    set_idx_length (zeros #p cols) f (fp_one p);
    fold_bstep_length pivots (set_idx (zeros #p cols) f (fp_one p))

let scaled_basis (#p:int{p > 1}) (cols:nat) (pivots: list (nat & vector p))
                 (src: vector p) (f:nat) : vector p =
  vscale (get src f) (build_vec cols pivots f)

let rec comb_of (#p:int{p > 1}) (cols:nat) (pivots: list (nat & vector p))
                (src: vector p) (frees: list nat) : Tot (vector p) (decreases frees) =
  match frees with
  | [] -> zeros #p cols
  | f :: fs -> zip_add (scaled_basis cols pivots src f) (comb_of cols pivots src fs)

let rec comb_of_length (#p:int{p > 1}) (cols:nat) (pivots: list (nat & vector p))
                       (src: vector p) (frees: list nat)
  : Lemma (ensures L.length (comb_of cols pivots src frees) == cols) (decreases frees)
  = match frees with
    | [] -> zeros_length #p cols
    | f :: fs ->
        comb_of_length cols pivots src fs;
        build_vec_length cols pivots f;
        vscale_length (get src f) (build_vec cols pivots f);
        zip_add_length (scaled_basis cols pivots src f) (comb_of cols pivots src fs)

(* an entry of a zero matrix-vector product dots to zero *)
let rec mvm_zero_dot (#p:int{p > 1}) (m: list (vector p)) (v: vector p) (r: vector p)
  : Lemma (requires mat_vec_mul m v == zeros #p (L.length m) /\ L.memP r m)
          (ensures dot r v == fp_zero p) (decreases m)
  = match m with
    | [] -> ()
    | r0 :: t -> if r = r0 then () else mvm_zero_dot t v r

(* the combination lies in the kernel of every row that kills the basis *)
let rec dot_comb_zero (#p:int{p > 1}) (cols:nat) (pivots: list (nat & vector p))
                      (src r: vector p) (frees: list nat)
  : Lemma (requires (forall (f:nat). L.memP f frees ==>
                       dot r (build_vec cols pivots f) == fp_zero p))
          (ensures dot r (comb_of cols pivots src frees) == fp_zero p) (decreases frees)
  = match frees with
    | [] -> dot_sym r (zeros #p cols); dot_zeros #p cols r
    | f :: fs ->
        dot_comb_zero cols pivots src r fs;
        comb_of_length cols pivots src fs;
        build_vec_length cols pivots f;
        vscale_length (get src f) (build_vec cols pivots f);
        dot_add (scaled_basis cols pivots src f) (comb_of cols pivots src fs) r;
        dot_scale (get src f) (build_vec cols pivots f) r;
        dot_sym r (zip_add (scaled_basis cols pivots src f) (comb_of cols pivots src fs));
        dot_sym r (build_vec cols pivots f);
        dot_sym r (comb_of cols pivots src fs);
        fp_mul_zero (get src f);
        fp_add_zero (fp_zero p)

(* free columns of the tag list have no repeats *)
let rec tag_frees_norepeats (#p:int{p > 1}) (start:nat) (tags: list (coltag p))
  : Lemma (ensures L.noRepeats (tag_frees start tags)) (decreases tags)
  = match tags with
    | [] -> ()
    | CPivot _ :: t -> tag_frees_norepeats (start + 1) t
    | CFree :: t -> tag_frees_lb (start + 1) t start; tag_frees_norepeats (start + 1) t

(* every column in range is either a pivot column or a free column *)
let rec tag_covers (#p:int{p > 1}) (start:nat) (tags: list (coltag p)) (g:nat)
  : Lemma (requires start <= g /\ g < start + L.length tags)
          (ensures L.mem g (L.map fst (tag_pivots start tags)) \/
                   L.mem g (tag_frees start tags)) (decreases tags)
  = match tags with
    | [] -> ()
    | CPivot _ :: t -> if g = start then () else tag_covers (start + 1) t g
    | CFree :: t -> if g = start then () else tag_covers (start + 1) t g

(* value of a single scaled basis vector at a non-pivot column *)
#push-options "--fuel 0 --ifuel 1"
let get_scaled_basis (#p:int{p > 1}) (cols:nat) (pivots: list (nat & vector p))
                     (src: vector p) (f g:nat)
  : Lemma (requires ~(L.mem g (L.map fst pivots)) /\ f < cols /\ g < cols)
          (ensures get (scaled_basis cols pivots src f) g
                   == (if g = f then get src f else fp_zero p))
  = build_vec_length cols pivots f;
    vscale_length (get src f) (build_vec cols pivots f);
    get_vscale (get src f) (build_vec cols pivots f) g;
    build_vec_free cols pivots f g;
    if g = f then fp_mul_one (get src f) else fp_mul_zero (get src f)
#pop-options

(* value of the combination at a non-pivot column *)
#push-options "--fuel 1 --ifuel 1"
let rec get_comb (#p:int{p > 1}) (cols:nat) (pivots: list (nat & vector p))
                 (src: vector p) (frees: list nat) (g:nat)
  : Lemma (requires ~(L.mem g (L.map fst pivots)) /\ g < cols /\ L.noRepeats frees /\
                    (forall (f:nat). L.memP f frees ==>
                       ~(L.mem f (L.map fst pivots)) /\ f < cols))
          (ensures get (comb_of cols pivots src frees) g
                   == (if L.mem g frees then get src g else fp_zero p))
          (decreases frees)
  = match frees with
    | [] -> get_zeros #p cols g
    | f :: fs ->
        get_comb cols pivots src fs g;
        comb_of_length cols pivots src fs;
        build_vec_length cols pivots f;
        vscale_length (get src f) (build_vec cols pivots f);
        get_zip_add (scaled_basis cols pivots src f) (comb_of cols pivots src fs) g;
        get_scaled_basis cols pivots src f g;
        (* get (comb_of (f::fs)) g == fp_add (get A g) (get B g), with
           get A g pinned above and get B g pinned by the IH. *)
        if g = f then fp_add_zero (get src f)                 (* B g == 0, A g == src f == src g *)
        else if L.mem g fs then fp_add_zero (get src g)       (* A g == 0, B g == src g *)
        else fp_add_zero (fp_zero p)                          (* A g == 0, B g == 0 *)
#pop-options

(* SPANNING:  every kernel vector v is the linear combination of the
   candidate null-space basis vectors with coefficients its own free
   coordinates:  v == sum_{f free}  v[f] . (candidate for f). *)
let null_space_basis_spans (#p:int{is_prime p}) (cols:nat) (m: list (vector p)) (v: vector p)
  : Lemma (requires all_len cols m /\ L.length v == cols /\
                    mat_vec_mul m v == zeros #p (L.length m))
          (ensures (let pivots = tag_pivots 0 (classify cols m 0) in
                    v == comb_of cols pivots v (tag_frees 0 (classify cols m 0))))
  = let tags = classify cols m 0 in
    let pivots = tag_pivots 0 tags in
    let frees = tag_frees 0 tags in
    let comb = comb_of cols pivots v frees in
    let diff = vsub v comb in
    comb_of_length cols pivots v frees;
    vsub_length v comb;
    tag_frees_norepeats 0 tags;
    (* the free columns are well-formed (non-pivot, in range) *)
    introduce forall (f:nat). L.memP f frees ==>
                ~(L.mem f (L.map fst pivots)) /\ f < cols
    with (introduce _ ==> _ with _mf. (free_not_pivot 0 tags f; tag_frees_ub 0 tags f));
    (* diff lies in the kernel of m *)
    introduce forall (r: vector p). L.memP r m ==> dot r diff == fp_zero p
    with (introduce _ ==> _ with _mr.
          (all_len_mem cols m r;
           mvm_zero_dot m v r;
           introduce forall (f:nat). L.memP f frees ==>
                       dot r (build_vec cols pivots f) == fp_zero p
           with (introduce _ ==> _ with _mf.
                 (L.memP_map_intro (build_vec cols pivots) f frees;
                  candidate_in_kernel cols m (build_vec cols pivots f);
                  is_zero_vec_eq_zeros (mat_vec_mul m (build_vec cols pivots f));
                  mat_vec_mul_length m (build_vec cols pivots f);
                  mvm_zero_dot m (build_vec cols pivots f) r));
           dot_comb_zero cols pivots v r frees;
           dot_sym r diff;
           dot_vsub_first v comb r;
           dot_sym v r;
           dot_sym comb r;
           fp_neg_zero #p;
           fp_add_zero (fp_zero p)));
    (* diff is zero at every non-pivot column *)
    introduce forall (g:nat). g < cols /\ ~(L.mem g (L.map fst pivots)) ==> get diff g == fp_zero p
    with (introduce _ ==> _ with _hg.
          (tag_covers 0 tags g;
           get_comb cols pivots v frees g;
           get_vsub v comb g;
           fp_add_negation (get v g)));
    kernel_zero_frees_imp_zero cols m diff;
    (* diff == zeros  ==>  v == comb, pointwise *)
    introduce forall (j:nat). j < L.length v ==> get v j == get comb j
    with (introduce _ ==> _ with _hj.
          (get_vsub v comb j; get_zeros #p cols j; fp_sub_zero_eq (get v j) (get comb j)));
    vec_ext v comb
