structure Syntax = struct
  type oper = {
    name : string,
    arity : (string list * string) list
  }
end
