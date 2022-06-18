module FStar.Dictionary

open FStar.List

type simple_map tkey tvalue = 
  | 





let after (#k:eqtype) (p:k) = z:k{p<<z}

type ordered (tkey:eqtype) (tvalue:Type) = 
  | Item: x:tkey ->
          v: tvalue -> 
          next:(ordered (after x) tvalue) -> 
          ordered tkey tvalue
  | Nul: ordered tkey tvalue

let rec len_of (#k:eqtype) #v (d: ordered k v) 
  : Tot nat (decreases d) = 
  match d with 
  | Nul -> 0
  | Item _ _ tail -> 1 + len_of tail

let sub_len_lemma (#k:eqtype) #v (d: ordered k v{len_of d > 0}) 
  : Lemma (Item?.next d << d) = ()

let rec last_key_of (#k:eqtype) #v (d: ordered k v) : Tot (option k) (decreases len_of d) = 
  match d with 
  | Nul -> None
  | Item dx _ dn -> match dn with
    | Nul -> Some dx
    | Item _ _ t -> match (last_key_of t) with
                   | None -> Some dx
                   | Some v -> Some v

let last_of_is_nonempty (#k:eqtype) #v (d: ordered k v{len_of d > 0}) 
  : Lemma (ensures last_key_of d =!= None) (decreases len_of d) = ()

let last_of_nonempty (#k:eqtype) #v (d: ordered k v{len_of d > 0}) 
  : Tot k (decreases len_of d) = 
  Some?.v (last_key_of d)

let rec except_last (#k:eqtype) (#v:Type) (d: ordered k v) : Tot (ordered k v) (decreases len_of d)
  = match d with
  | Nul -> Nul
  | Item key value next -> match next with 
                          | Nul -> Nul
                          | Item _ _ n -> Item key value (except_last next)

let rec except_last_len (#k:eqtype) #v (d: ordered k v) 
  : Lemma (requires len_of d > 0) 
          (ensures len_of (except_last d) < len_of d) 
          (decreases len_of d) =
  match d with 
  | Item key value next -> match next with 
                          | Nul -> ()
                          | Item _ _ n -> except_last_len next

let rec has_key (#k:eqtype) (#v:Type) (key:k) (d: ordered k v) : Tot bool (decreases len_of d) =    
  if (len_of d = 0) then false else begin
    let lk = Some?.v (last_key_of d) in
    if lk=key then true
    else begin
      except_last_len d;
      has_key key (except_last d)
    end
  end



type atom (tkey:eqtype) (tvalue:Type) = {
  key : tkey; value: tvalue
}

type cell (tkey:eqtype) (tvalue:Type) = {
  this: atom tkey tvalue;
  left: cell tkey tvalue;
  right: cell tkey tvalue;
}

type dic_entry (tkey:eqtype) (tvalue:Type) = 
{
  key: tkey;
  value: tvalue
}

let mkentry (#tkey:eqtype) #tvalue (k:tkey) (v:tvalue) : dic_entry tkey tvalue = { key = k; value = v }

type dic (tkey:eqtype) (tvalue:Type) = 
  | Kvp: this : dic_entry tkey tvalue -> next: dic tkey tvalue -> dic tkey tvalue
  | Nul: dic tkey tvalue

let rec is_valid_dic (tkey:eqtype) (tvalue:Type) (d:dic tkey tvalue) =
  match d with
  | Nul -> True
  | Kvp t n -> match n with
              | Nul -> True
              | Kvp t2 n2 -> t.key << t2.key /\ is_valid_dic tkey tvalue n

type dictionary (k: eqtype) v = (z:dic k v { is_valid_dic k v z })

let test_dic : dic nat nat = 
  Kvp (mkentry 1 1) (Kvp (mkentry 0 2) Nul) 

let rec contains_key (#k:eqtype) #v (d: dictionary k v) (key:k) : bool = 
  match d with
  | Nul -> false
  | Kvp t n -> t.key = key || contains_key n key

let rec dic_add (#k:eqtype) (#v:Type) (d: dictionary k v) 
                (key:k{not(contains_key d key)}) (value:v)
                : dictionary k v = 
  match d with
  | Nul -> Kvp (mkentry key value) Nul
  | Kvp t n -> if key << t.key then Kvp (mkentry key value) d
              else Kvp t (dic_add n key value)
  
            

