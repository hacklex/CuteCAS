module FMap

open FStar.List

let rec has_key #a (z: list (nat*a)) (k:nat)
  = match z with
  | [] -> false
  | h::t -> fst h = k || has_key t k

let rec is_fmap (#a: eqtype) (z: list (nat*a)) = 
  match z with
  | [] -> true
  | h::t -> not(has_key t (fst h)) && is_fmap t

type fmap (a:eqtype) = z: list (nat * a) { is_fmap z }

let test_map : fmap int = 
  [ (3,5); (5, 7); (6, 7); (13, 8)]

let rec ( @> ) (#a:eqtype) (map: fmap a) (k: nat) 
  : Pure a (requires has_key map k) (ensures fun _ -> True)
  = match map with 
  | h::t -> if (fst h = k) then snd h else t @> k

let _ = assert (test_map @> 5 = 7)

let rec set (#a:eqtype) (z: fmap a) (i: nat) (v: a)
  : Pure (fmap a) (requires True) (ensures fun m -> (has_key m i) /\ 
                                              (m @> i = v) /\
                                              (forall (n:nat{n<>i}). has_key z n == has_key m n))
  = match z with
  | [] -> [(i,v)]
  | h::t -> if fst h = i then (i,v)::t
          else h::set t i v 

let upd = set test_map 5 2

let _ = assert (upd @> 5 = 2)
let _ = assert (upd @> 6 = 7)

let rec set_all (#a: eqtype) (z: fmap a) (indices: list nat) (v:a)
  : Tot (fmap a) (decreases length indices)
  = match indices with
  | [] -> z
  | h::t -> set_all (set z h v) t v

let update_2 = set_all upd [1;3;4] (-1)

let _ = assert (update_2 @> 1 = -1)
let _ = assert (update_2 @> 3 = -1)
let _ = assert (update_2 @> 4 = -1)

