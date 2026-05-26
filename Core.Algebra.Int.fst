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
  add               = (fun x y -> Prims.op_Addition x y);
  add_congruence    = (fun _ _ _ _ -> ());
  add_commutativity = (fun _ _ -> ());
  add_associativity = (fun _ _ _ -> ());
  add_zero          = (fun _ -> ());
  neg               = (fun x -> Prims.op_Minus x);
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
