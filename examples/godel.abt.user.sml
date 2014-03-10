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

signature TP = 
sig
   type tp (* = Tp.t *)
   type t = tp
   
   datatype tpView = datatype AbbotImpl.Tp.tpView
   (* datatype 'tp tpView
    *  = Nat
    *  | Arr of 'tp * 'tp   *)
   
   val Nat': tp
   val Arr': tp * tp -> tp
   
   val into:  tp tpView -> tp
   val out: tp -> tp tpView
   val aequiv: tp * tp -> bool
   val toString: tp -> string
end
structure Tp: TP
      where type tp = AbbotImpl.tp
      = AbbotImpl.TpImpl
      
signature EXP = 
sig
   type exp (* = Exp.t *)
   type expVar (* = Exp.Var.t *)
   type t = exp
   
   structure Var: EXP_VAR where type expVar = expVar
   datatype expView = datatype AbbotImpl.Exp.expView
   (* datatype 'exp expView
    *  = Var of Exp.Var.t
    *  | Z
    *  | S of 'exp
    *  | Rec of 'exp * 'exp * (Exp.Var.t * Exp.Var.t * 'exp)
    *  | Lam of Tp.t * (Exp.Var.t * 'exp)
    *  | Ap of 'exp * 'exp   *)
   
   val Var' : expVar -> exp
   val Z': exp
   val S': exp -> exp
   val Rec': exp * exp * (expVar * expVar * exp) -> exp
   val Lam': Tp.tp * (expVar * exp) -> exp
   val Ap': exp * exp -> exp
   
   val into:  exp expView -> exp
   val out: exp -> exp expView
   val aequiv: exp * exp -> bool
   val toString: exp -> string
   val subst: exp -> expVar -> exp -> exp
   val freevars: exp -> expVar list
end
structure Exp: EXP
      where type exp = AbbotImpl.exp
      where type expVar = AbbotImpl.ExpVar.expVar
      = AbbotImpl.ExpImpl
      
(* Intentionally shadow internals *)
structure AbbotImpl = struct end
