(* Generic ABT interface. Unsafe because there is no arity check, and because
 * one could switch which operator functions one is using and get undesired
 * behavior. *)
signature ABT =
sig
  type 'oper t

  datatype ('t, 'oper) view
    = Var of Temp.t
    | Binding of Temp.t * 't
    | Oper of 'oper

  exception Malformed

  type 'a binding_modifier = Temp.t -> int -> 'a -> 'a

  val bind : 'oper binding_modifier -> 'oper t binding_modifier
  val unbind : 'oper binding_modifier -> 'oper t binding_modifier
  val into : 'oper binding_modifier -> ('oper t, 'oper) view -> 'oper t
  val out : 'oper binding_modifier -> 'oper t -> ('oper t, 'oper) view
  val aequiv : ('oper * 'oper -> bool) -> 'oper t * 'oper t -> bool
  val toString : ('oper -> string) -> 'oper t -> string
  val map : ('a -> 'b) -> ('a, 'oper) view -> ('b, 'oper) view
end
