(* Generic ABT interface. Unsafe because there is no arity check, and because
 * one could switch which operator functions one is using and get undesired
 * behavior. *)
signature ABT =
sig
  type 'oper t

  datatype ('t, 'oper) view
    = Var of Variable.t
    | VarBinding of Variable.t * 't
    | SymBinding of Symbol.t * 't
    | Oper of 'oper * 't list

  exception Malformed

  type 'a var_binding_modifier = Variable.t -> int -> 'a -> 'a
  type 'a sym_binding_modifier = Symbol.t -> int -> 'a -> 'a

  val bind_var : 'oper var_binding_modifier -> 'oper t var_binding_modifier
  val unbind_var : 'oper var_binding_modifier -> 'oper t var_binding_modifier
  val bind_sym : 'oper sym_binding_modifier -> 'oper t sym_binding_modifier
  val unbind_sym : 'oper sym_binding_modifier -> 'oper t sym_binding_modifier
  val into : 'oper var_binding_modifier
             -> 'oper sym_binding_modifier
             -> ('oper t, 'oper) view
             -> 'oper t
  val out : 'oper var_binding_modifier
            -> 'oper sym_binding_modifier
            -> 'oper t
            -> ('oper t, 'oper) view
  val aequiv : ('oper * 'oper -> bool) -> 'oper t * 'oper t -> bool
  val toString : ('oper -> string) -> 'oper t -> string
  val map : ('a -> 'b) -> ('a, 'oper) view -> ('b, 'oper) view
end
