structure Abt :> ABT = struct
  datatype ('t, 'oper) view
    = Var of Variable.t
    | Binding of Variable.t * 't
    | Oper of 'oper

  datatype 'oper t
    = FV of Variable.t
    | BV of int
    | ABS of 'oper t
    | OPER of 'oper

  type 'a binding_modifier = Variable.t -> int -> 'a -> 'a

  exception Malformed

  fun aequiv _ (FV x, FV y) = Variable.equal (x, y)
    | aequiv _ (BV n, BV m) = (n = m)
    | aequiv aequiv_oper (ABS t, ABS t') = aequiv aequiv_oper (t, t')
    | aequiv aequiv_oper (OPER f, OPER f') = aequiv_oper (f, f')
    | aequiv _ (_, _) = false

  fun bind bind_oper x i t =
      case t of
        FV y => if Variable.equal (x, y) then BV i else FV y
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

  exception Assertion_failure_name

  fun out unbind_oper t =
      case t of
        BV _ => raise Assertion_failure_name
      | FV x => Var x
      | OPER f => Oper f
      | ABS t =>
        let val x = Variable.new "x"
        in Binding (x, unbind unbind_oper x 0 t)
        end

  fun toString operToString e = (* ??? *)
      case out (fn _ => fn _ => fn f => f) e of
        Var x => Variable.toString x
      | Oper f => operToString f
      | Binding (x, e) =>
        (Variable.toString x) ^ ". " ^ (toString operToString e)
  and toStrings _ [] = ""
    | toStrings operToString [e] = toString operToString e
    | toStrings operToString (e :: es) =
      (toString operToString e) ^ ", " ^ (toStrings operToString es)

  fun map f v = (* use oper map ??? *)
      case v of
        Var x => Var x
      | Binding (x, t) => Binding (x, f t)
      | Oper h => Oper h
end
