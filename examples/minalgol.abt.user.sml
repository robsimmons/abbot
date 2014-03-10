(* Implementation of symbol sorts *)

signature ASSIGN = 
sig
   type assign = AbbotImpl.Assign.assign
   type t = assign
   val newsym: string -> assign
   val equal: (assign * assign) -> bool
   val compare: (assign * assign) -> order
   val toString: assign -> string
   val hash: assign -> int
end
structure Assign:> ASSIGN = AbbotImpl.Assign


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

signature SIDE = 
sig
   type side (* = Side.t *)
   type t = side
   
   datatype sideView = datatype AbbotImpl.Side.sideView
   (* datatype 'side sideView
    *  = L
    *  | R   *)
   
   val L': side
   val R': side
   
   val into:  side sideView -> side
   val out: side -> side sideView
   val aequiv: side * side -> bool
   val toString: side -> string
end
structure Side: SIDE
      where type side = AbbotImpl.side
      = AbbotImpl.SideImpl
      
signature TP = 
sig
   type tp (* = Tp.t *)
   type t = tp
   
   datatype tpView = datatype AbbotImpl.Tp.tpView
   (* datatype 'tp tpView
    *  = Nat
    *  | Parr of 'tp * 'tp
    *  | Unit
    *  | Prod of 'tp * 'tp
    *  | Void
    *  | Sum of 'tp * 'tp
    *  | Cmd of 'tp   *)
   
   val Nat': tp
   val Parr': tp * tp -> tp
   val Unit': tp
   val Prod': tp * tp -> tp
   val Void': tp
   val Sum': tp * tp -> tp
   val Cmd': tp -> tp
   
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
   type cmd (* = Cmd.t *)
   type t = exp
   
   structure Var: EXP_VAR where type expVar = expVar
   datatype expView = datatype AbbotImpl.Exp.expView
   (* datatype ('exp, 'cmd) expView
    *  = Var of Exp.Var.t
    *  | Z
    *  | S of 'exp
    *  | Ifz of Tp.t * (Exp.Var.t * 'exp)
    *  | Lam of Tp.t * (Exp.Var.t * 'exp)
    *  | Ap of 'exp * 'exp
    *  | Let of 'exp * (Exp.Var.t * 'exp)
    *  | Fix of Tp.t * (Exp.Var.t * 'exp)
    *  | Triv
    *  | Pair of 'exp * 'exp
    *  | Pr of Side.t * 'exp
    *  | Abort of Tp.t * 'exp
    *  | In of Tp.t * Tp.t * Side.t * 'exp
    *  | Case of 'exp * (Exp.Var.t * 'exp) * (Exp.Var.t * 'exp)
    *  | Cmd of 'cmd   *)
   
   val Var' : expVar -> exp
   val Z': exp
   val S': exp -> exp
   val Ifz': Tp.tp * (expVar * exp) -> exp
   val Lam': Tp.tp * (expVar * exp) -> exp
   val Ap': exp * exp -> exp
   val Let': exp * (expVar * exp) -> exp
   val Fix': Tp.tp * (expVar * exp) -> exp
   val Triv': exp
   val Pair': exp * exp -> exp
   val Pr': Side.side * exp -> exp
   val Abort': Tp.tp * exp -> exp
   val In': Tp.tp * Tp.tp * Side.side * exp -> exp
   val Case': exp * (expVar * exp) * (expVar * exp) -> exp
   val Cmd': cmd -> exp
   
   val into:  (exp, cmd) expView -> exp
   val out: exp -> (exp, cmd) expView
   val aequiv: exp * exp -> bool
   val toString: exp -> string
   val subst: exp -> expVar -> exp -> exp
   val freevars: exp -> expVar list
   val freeAssign: exp -> Assign.assign list
end
structure Exp: EXP
      where type exp = AbbotImpl.exp
      where type expVar = AbbotImpl.ExpVar.expVar
      where type cmd = AbbotImpl.cmd
      = AbbotImpl.ExpImpl
      
signature CMD = 
sig
   type exp (* = Exp.t *)
   type expVar (* = Exp.Var.t *)
   type cmd (* = Cmd.t *)
   type t = cmd
   
   datatype cmdView = datatype AbbotImpl.Cmd.cmdView
   (* datatype ('exp, 'cmd) cmdView
    *  = Ret of 'exp
    *  | Bnd of 'exp * (Exp.Var.t * 'cmd)
    *  | Dcl of 'exp * (Assign.t * 'cmd)
    *  | Get of Assign.t
    *  | Set of Assign.t * 'exp   *)
   
   val Ret': exp -> cmd
   val Bnd': exp * (expVar * cmd) -> cmd
   val Dcl': exp * (Assign.assign * cmd) -> cmd
   val Get': Assign.assign -> cmd
   val Set': Assign.assign * exp -> cmd
   
   val into:  (exp, cmd) cmdView -> cmd
   val out: cmd -> (exp, cmd) cmdView
   val aequiv: cmd * cmd -> bool
   val toString: cmd -> string
   val substExp: exp -> expVar -> cmd -> cmd
   val freeExpVars: cmd -> expVar list
   val freeAssign: cmd -> Assign.assign list
end
structure Cmd: CMD
      where type exp = AbbotImpl.exp
      where type expVar = AbbotImpl.ExpVar.expVar
      where type cmd = AbbotImpl.cmd
      = AbbotImpl.CmdImpl
      
(* Intentionally shadow internals *)
structure AbbotImpl = struct end
