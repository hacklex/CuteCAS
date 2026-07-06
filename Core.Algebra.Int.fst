module Core.Algebra.Int

(*
   add_comm_group / ring / commutative_ring instances for `int`.

   Provided so that Notation-open files can use overloaded operators
   (`( + )`, `( * )`, unary `( ~- )`, binary `( -- )`) on int values
   without the typeclass resolution failing.

   All proofs are trivial — int arithmetic is built into Prims and
   F*/SMT discharges every algebraic law automatically.

   The bodies of the field functions use explicit `Prims.op_*` so we
   don't loop through Notation's overloaded operators.
*)

open Core.Algebra

instance int_acg : add_comm_group int = {
  acg_eq            = default_equatable int;
  zero              = 0;
  add               = Prims.op_Addition;
  add_congruence    = (fun _ _ _ _ -> ());
  add_commutativity = (fun _ _ -> ());
  add_associativity = (fun _ _ _ -> ());
  add_zero          = (fun _ -> ());
  neg               = Prims.op_Minus;
  neg_congruence    = (fun _ _ -> ());
  add_negation      = (fun _ -> ());
}

instance int_ring : ring int = {
  r_add                = int_acg;
  one                  = 1;
  mul                  = (fun (x y: int) -> Prims.op_Star x y);
  mul_congruence       = (fun _ _ _ _ -> ());
  mul_associativity    = (fun _ _ _ -> ());
  mul_one              = (fun _ -> ());
  left_distributivity  = (fun _ _ _ -> ());
  right_distributivity = (fun _ _ _ -> ());
}

instance int_mic : mul_is_commutative int #int_ring = {
  mul_commutativity = (fun _ _ -> ());
}

instance int_cr : commutative_ring int = {
  cr_r   = int_ring;
  cr_mic = int_mic;
}

(* ---------------------------------------------------------------- *)
(* domain / integral_domain instances for `int`.                    *)
(*                                                                  *)
(* Over `int` the class `eq` is `Prims.op_Equality`, `mul` is       *)
(* `Prims.op_Star` and `zero`/`one` are `0`/`1`, so the            *)
(* no-zero-divisors law `x*y = 0 <==> x = 0 \/ y = 0` and the      *)
(* nontriviality `1 <> 0` are native integer facts, discharged by  *)
(* `()`. We reuse `int_ring` (hence `int_mic` resolves) and do NOT *)
(* rebuild any ring structure.                                     *)
(* ---------------------------------------------------------------- *)

instance int_domain : domain int = {
  d_r        = int_ring;
  domain_law = (fun _ _ -> ());
}

instance int_id : integral_domain int = {
  id_d           = int_domain;
  id_mic         = int_mic;
  id_one_ne_zero = ();
}
