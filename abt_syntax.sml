structure AbbotSyntax = struct
  datatype arity
    = Param of string (* paramaterized arity *)
    | Use of string (* sort, symbol, or constant mappable use *)
    | Binding of string (* sort or symbol binding *)
    | Prod of arity list
    | App of string * arity list
    | Dot of arity * arity (* Binds bindings on the left in the right. *)

  type oper = string * arity option
end
