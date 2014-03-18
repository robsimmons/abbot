(* Signatures for variables *)

signature EXP_VAR = 
sig
   type expVar
   type t = expVar
   val newvar: string -> expVar
   val equal: (expVar * expVar) -> bool
   val compare: (expVar * expVar) -> order
   val toString: expVar -> string
   val hash: expVar -> int
end


(* Implementation of normal sorts *)

signature EXP = 
sig
   type exp (* = Exp.t *)
   type expVar (* = Exp.Var.t *)
   type t = exp
   
   structure Var: EXP_VAR where type expVar = expVar
   datatype expView = datatype AbbotImpl.Exp.expView
   (* datatype 'exp expView
    *  = Var of Exp.Var.t
    *  | Lam
    *  | Ap of 'exp * 'exp   *)
   
   val Var' : expVar -> exp
   val Lam': exp
   val Ap': exp * exp -> exp
   
   val into:  exp expView -> exp
   val out: exp -> exp expView
   val aequiv: exp * exp -> bool
   val toString: exp -> string
   val subst: exp -> expVar -> exp -> exp
   val fmap: ('exp1 -> 'exp2)
          -> 'exp1 expView -> 'exp2 expView
end
structure Exp: EXP
      where type exp = AbbotImpl.exp
      where type expVar = AbbotImpl.ExpVar.expVar
      = AbbotImpl.Exp
      
(* Intentionally shadow internals *)
structure AbbotImpl = struct end
