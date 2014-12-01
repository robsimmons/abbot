structure SmlSyntax = struct
  (* allow functors that are pos in some args and negative in others??? *)
  datatype binding
    = BindingVar of string (* sort, symbol, or constant iterable *)
    | ProdBinding of binding list
    | AppBinding of string * binding list

  datatype arity
    = ArityVar of string (* sort, symbol, or constant mappable *)
    | ProdArity of arity list
    | AppArity of string * arity list
    | BindingArity of binding * arity

  type oper = string * arity option

  datatype ast_arity
    = Param of string
    | ProdAstArity of ast_arity list
    | AppAstArity of string * ast_arity list

  type ast_oper = string * ast_arity option
end
