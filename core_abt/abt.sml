structure Abt :> ABT = struct
  datatype 'oper t
    = FV of Temp.t
    | BV of int
    | ABS of 'oper t
    | OPER of 'oper

  datatype 'oper view
    = Var of Temp.t
    | Binding of Temp.t * 'oper t
    | Oper of 'oper

  type 'a binding_modifier = Temp.t -> int -> 'a -> 'a

  exception Malformed

  fun bind bind_oper x i t =
      case t of
        FV y => if Temp.equal (x, y) then BV i else FV y
      | ABS t => ABS (bind bind_oper x (i + 1) t)
      | BV n => BV n
      | OPER f => OPER (bind_oper x i f)

  fun unbind unbind_oper x i t =
      case t of
        BV j => if i = j then FV x else BV j
      | ABS t => ABS (unbind unbind_oper x (i + 1) t)
      | FV x => FV x
      | OPER f => OPER (unbind_oper x i f)

  fun into bind_oper v =
      case v of
        Var x => FV x
      | Binding (x, t) => ABS (bind bind_oper x 0 t)
      | Oper f => OPER f

  fun out unbind_oper t =
      case t of
        BV _ => raise Fail "Internal Abbot Error"
      | FV x => Var x
      | OPER f => Oper f
      | ABS t =>
        let val x = Temp.new "x"
        in Binding (x, unbind unbind_oper x 0 t)
        end
end
