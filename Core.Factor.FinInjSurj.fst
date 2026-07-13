module Core.Factor.FinInjSurj

(* ================================================================ *)
(*  DURABLE finite pigeonhole:                                       *)
(*  an INJECTIVE function  f : fin r -> fin r  is SURJECTIVE.         *)
(*                                                                   *)
(*  This is the combinatorial core of the Berlekamp completeness     *)
(*  pigeonhole: r nonempty pairwise-disjoint blocks that cover a      *)
(*  size-r set are each singletons (a surjective owner-map on r       *)
(*  points is injective, so preimages are singletons).               *)
(*                                                                   *)
(*  Proved by compression + FStar.Fin.pigeonhole.                    *)
(*  NO admit / assume / sorry.                                       *)
(* ================================================================ *)

module S = FStar.Seq
module F = FStar.Fin

#set-options "--fuel 0 --ifuel 1 --z3rlimit 20"

(* An injective  f : {0..r-1} -> {0..r-1}  hits every  v < r.
   `f` is ghost (typical callers pick it by indefinite description). *)
let fin_inj_surj (r:nat)
  (f: (i:nat{i < r}) -> GTot (j:nat{j < r}))
  (finj: (a:nat{a < r}) -> (b:nat{b < r})
         -> Lemma (requires f a == f b) (ensures a == b))
  (v:nat{v < r})
  : Lemma (exists (i:nat). i < r /\ f i == v)
  = let contra () : Lemma (requires (forall (i:nat). i < r ==> f i =!= v))
                          (ensures  False)
      = if r = 1 then
          (* f 0 : {0} so f 0 == 0 == v, contradicting f 0 =!= v *)
          assert (f 0 == 0)
        else begin
          let n : pos = r - 1 in
          (* compress the image  {0..r-1} \ {v}  into  {0..r-2}. *)
          let cf (i:nat{i < r}) : GTot (F.under n)
            = let fi = f i in if fi < v then fi else fi - 1 in
          let s : S.seq (F.under n) = S.init_ghost r cf in
          S.lemma_init_ghost_len r cf;                 (* length s == r == n+1 > n *)
          let ip = F.pigeonhole #n s in
          let i1 = fst ip in
          let i2 = snd ip in
          (* i1 < i2 < r ; s[i1] == s[i2] ; init_ghost_index_ SMTPat gives s[k]==cf k *)
          S.init_ghost_index_ r cf i1;
          S.init_ghost_index_ r cf i2;
          assert (cf i1 == cf i2);
          assert (f i1 == f i2);                       (* compression is injective *)
          finj i1 i2                                   (* i1 == i2 : contra i1 < i2 *)
        end
    in
    Classical.move_requires contra ()
