(* Signatures for variables *)

signature TP_VAR = 
sig
   type tpVar
   type t = tpVar
   val newvar: string -> tpVar
   val equal: (tpVar * tpVar) -> bool
   val compare: (tpVar * tpVar) -> order
   val toString: tpVar -> string
   val hash: tpVar -> int
end

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
   type tpVar (* = Tp.Var.t *)
   type t = tp
   
   structure Var: TP_VAR where type tpVar = tpVar
   datatype tpView = datatype AbbotImpl.Tp.tpView
   (* datatype 'tp tpView
    *  = Var of Tp.Var.t
    *  | All of (Tp.Var.t * 'tp)
    *  | Arr of 'tp * 'tp   *)
   
   val Var' : tpVar -> tp
   val All': (tpVar * tp) -> tp
   val Arr': tp * tp -> tp
   
   val into:  tp tpView -> tp
   val out: tp -> tp tpView
   val aequiv: tp * tp -> bool
   val toString: tp -> string
   val subst: tp -> tpVar -> tp -> tp
   val fmap: ('tp1 -> 'tp2)
          -> 'tp1 tpView -> 'tp2 tpView
end
structure Tp: TP
      where type tp = AbbotImpl.tp
      where type tpVar = AbbotImpl.TpVar.tpVar
      = AbbotImpl.Tp
      
signature EXP = 
sig
   type exp (* = Exp.t *)
   type expVar (* = Exp.Var.t *)
   type t = exp
   
   structure Var: EXP_VAR where type expVar = expVar
   datatype expView = datatype AbbotImpl.Exp.expView
   (* datatype 'exp expView
    *  = Var of Exp.Var.t
    *  | Lam of Tp.t * (Exp.Var.t * 'exp)
    *  | App of 'exp * 'exp
    *  | TLam of (Tp.Var.t * 'exp)
    *  | TApp of 'exp * Tp.t   *)
   
   val Var' : expVar -> exp
   val Lam': Tp.tp * (expVar * exp) -> exp
   val App': exp * exp -> exp
   val TLam': (Tp.Var.tpVar * exp) -> exp
   val TApp': exp * Tp.tp -> exp
   
   val into:  exp expView -> exp
   val out: exp -> exp expView
   val aequiv: exp * exp -> bool
   val toString: exp -> string
   val subst: exp -> expVar -> exp -> exp
   val substTp: Tp.tp -> Tp.Var.tpVar -> exp -> exp
   val fmap: ('exp1 -> 'exp2)
          -> 'exp1 expView -> 'exp2 expView
end
structure Exp: EXP
      where type exp = AbbotImpl.exp
      where type expVar = AbbotImpl.ExpVar.expVar
      = AbbotImpl.Exp
      
(* Intentionally shadow internals *)
structure AbbotImpl = struct end
