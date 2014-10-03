structure Abt :> ABT = struct
  datatype ('t, 'oper) view
    = Var of Variable.t
    | VarBinding of Variable.t * 't
    | SymBinding of Symbol.t * 't
    | Oper of 'oper * 't list

  datatype 'oper t
    = FV of Variable.t
    | BV of int
    | AVB of 'oper t
    | ASB of 'oper t
    | OPER of 'oper * 'oper t list

  type 'a var_binding_modifier = Variable.t -> int -> 'a -> 'a
  type 'a sym_binding_modifier = Symbol.t -> int -> 'a -> 'a

  exception Malformed

  fun aequiv _ (FV x, FV y) = Variable.equal (x, y)
    | aequiv _ (BV n, BV m) = (n = m)
    | aequiv aequiv_oper (AVB t, AVB t') = aequiv aequiv_oper (t, t')
    | aequiv aequiv_oper (ASB t, ASB t') = aequiv aequiv_oper (t, t')
    | aequiv aequiv_oper (OPER (f, ts), OPER (f', ts')) =
      aequiv_oper (f, f') andalso List_Util.zipTest (aequiv aequiv_oper) ts ts'
    | aequiv _ (_, _) = false

  fun bind_var bind_var_oper x i t =
      case t of
        FV y => if Variable.equal (x, y) then BV i else FV y
      | AVB t => AVB (bind_var bind_var_oper x (i + 1) t)
      | ASB t => ASB (bind_var bind_var_oper x i t)
      | BV n => BV n
      | OPER (f, ts) =>
        OPER (bind_var_oper x i f, List.map (bind_var bind_var_oper x i) ts)

  fun unbind_var unbind_var_oper x i t =
      case t of
        BV j => if i = j then FV x else BV j
      | AVB t => AVB (unbind_var unbind_var_oper x (i + 1) t)
      | ASB t => ASB (unbind_var unbind_var_oper x i t)
      | FV x => FV x
      | OPER (f, ts) =>
        OPER (unbind_var_oper x i f, List.map (unbind_var unbind_var_oper x i) ts)

  fun bind_sym bind_sym_oper a i t =
      case t of
        FV x => FV x
      | AVB t => AVB (bind_sym bind_sym_oper a i t)
      | ASB t => ASB (bind_sym bind_sym_oper a (i + 1) t)
      | BV n => BV n
      | OPER (f, ts) =>
        OPER (bind_sym_oper a i f, List.map (bind_sym bind_sym_oper a i) ts)

  fun unbind_sym unbind_sym_oper a i t =
      case t of
        BV n => BV n
      | AVB t => AVB (unbind_sym unbind_sym_oper a i t)
      | ASB t => ASB (unbind_sym unbind_sym_oper a (i + 1) t)
      | FV x => FV x
      | OPER (f, ts) =>
        OPER (unbind_sym_oper a i f, List.map (unbind_sym unbind_sym_oper a i) ts)

  fun into bind_var_oper bind_sym_oper v =
      case v of
        Var x => FV x
      | VarBinding (x, t) => AVB (bind_var bind_var_oper x 0 t)
      | SymBinding (a, t) => ASB (bind_sym bind_sym_oper a 0 t)
      | Oper (f, es) => OPER (f, es)

  exception Assertion_failure_name

  fun out unbind_var_oper unbind_sym_oper t =
      case t of
        BV _ => raise Assertion_failure_name
      | FV x => Var x
      | OPER (f, ts) => Oper (f, ts)
      | AVB t =>
        let val x = Variable.new "x"
        in VarBinding (x, unbind_var unbind_var_oper x 0 t)
        end
      | ASB t =>
        let val a = Symbol.new "a"
        in SymBinding (a, unbind_sym unbind_sym_oper a 0 t)
        end

  fun toString operToString e = (* ??? *)
      case out (fn _ => fn _ => fn f => f) (fn _ => fn _ => fn f => f) e of
        Var x => Variable.toString x
      | Oper (f, []) => operToString f
      | Oper (f, es) =>
        (operToString f) ^ "(" ^ (toStrings operToString es) ^ ")"
      | VarBinding (x, e) =>
        (Variable.toString x) ^ ". " ^ (toString operToString e)
      | SymBinding (a, e) =>
        (Symbol.toString a) ^ ". " ^ (toString operToString e)
  and toStrings _ [] = ""
    | toStrings operToString [e] = toString operToString e
    | toStrings operToString (e :: es) =
      (toString operToString e) ^ ", " ^ (toStrings operToString es)

  fun map f v =
      case v of
        Var x => Var x
      | VarBinding (x, t) => VarBinding (x, f t)
      | SymBinding (a, t) => SymBinding (a, f t)
      | Oper (h, ts) => Oper (h, List.map f ts)
end
