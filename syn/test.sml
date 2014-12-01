structure Assign = Temp ()

structure SideOps = struct
  datatype side_oper
    = L
    | R
  withtype side = side_oper Abt.t
  fun side_oper_bind _ _ _ = raise Fail ""
  fun side_oper_unbind _ _ _ = raise Fail ""
  fun side_oper_aequiv _ = raise Fail ""
  fun side_oper_toString _ = raise Fail ""
end

structure Side = struct
  type side = SideOps.side
  type t = side
end

structure TpOps = struct
  datatype tp_oper
    = Nat
    | Parr (* 0, 0 *)
    | Prod (* 0, 0 *)
    | Void
    | Sum (* 0, 0 *)
    | Cmd (* 0 *)
  withtype tp = tp_oper Abt.t
  fun tp_oper_bind _ _ _ = raise Fail ""
  fun tp_oper_unbind _ _ _ = raise Fail ""
  fun tp_oper_aequiv _ = raise Fail ""
  fun tp_oper_toString _ = raise Fail ""
end

structure Tp = struct
  type tp = TpOps.tp
  type t = tp
end

structure ExpCmdOps = struct
  datatype exp_oper
    = Z
    | S (* 0 *)
    | Ifz (* 0, 0, 1 *)
    | Lam of Tp.t (* 1 *)
    | Ap (* 0, 0 *)
    | Let (* 0, 1 *)
    | Fix of Tp.t (* 1 *)
    | Pair (* 1, 1 *)
    | Pr of Side.t (* 0 *)
    | Abort of Tp.t (* 0 *)
    | In of Tp.t * Tp.t * Side.t (* 0 *)
    | Case (* 0, 1, 1 *)
    | Cmd of cmd
  and cmd_oper
    = Bnd of exp (* 1 *)
    | Ret of exp
    | Dcl of Assign.t * exp (* 1 *)
    | Get of Assign.t
    | Set of Assign.t * exp
  withtype exp = exp_oper Abt.t
  and cmd = cmd_oper Abt.t

  fun exp_oper_bind x i t =
      case t of
          Z => Z
        | S => S
        | Ifz => Ifz
        | Lam tp => Lam (Abt.bind TpOps.tp_oper_bind x i tp)
        | Ap => Ap
        | Let => Let
        | Fix tp => Fix (Abt.bind TpOps.tp_oper_bind x i tp)
        | Pair => Pair
        | Pr side => Pr (Abt.bind SideOps.side_oper_bind x i side)
        | Abort tp => Abort (Abt.bind TpOps.tp_oper_bind x i tp)
        | In (tp1, tp2, side) =>
          In (Abt.bind TpOps.tp_oper_bind x i tp1,
              Abt.bind TpOps.tp_oper_bind x i tp2,
              Abt.bind SideOps.side_oper_bind x i side)
        | Case => Case
        | Cmd cmd => Cmd (Abt.bind cmd_oper_bind x i cmd)
  and cmd_oper_bind _ _ _ = raise Fail ""
  fun exp_oper_unbind _ _ _ = raise Fail ""
  and cmd_oper_unbind _ _ _ = raise Fail ""
  fun exp_oper_aequiv _ = raise Fail ""
  and cmd_oper_aequiv _ _ _ = raise Fail ""
  fun exp_oper_toString _ = raise Fail ""
  and cmd_oper_toString _ _ _ = raise Fail ""
end

structure Exp (* : EXP*) = struct
  type exp = ExpCmdOps.exp
  type cmd = ExpCmdOps.cmd
  type t = exp

  structure Var = Variable

  type expVar = Var.t

  datatype ('exp, 'cmd) view
    = Var of expVar
    | Z
    | S of 'exp
    | Ifz of 'exp * 'exp * (expVar * 'exp)
    | Lam of Tp.t * (expVar * 'exp)
    | Ap of 'exp * 'exp
    | Let of 'exp * (expVar * 'exp)
    | Fix of Tp.t * (expVar * 'exp)
    | Pair of 'exp * 'exp
    | Pr of Side.t * 'exp
    | Abort of Tp.t * 'exp
    | In of Tp.t * Tp.t * Side.t * 'exp
    | Case of 'exp * (expVar * 'exp) * (expVar * 'exp)
    | Cmd of 'cmd

  fun Binding' exp = Abt.into ExpCmdOps.exp_oper_bind (Abt.Binding exp)

  fun view_in v =
      case v of
          Var x => Abt.Var x
        | Z => Abt.Oper (ExpCmdOps.Z, [])
        | S exp => Abt.Oper (ExpCmdOps.S, [exp])
        | Ifz (exp1, exp2, exp3) =>
          Abt.Oper (ExpCmdOps.Ifz, [exp1, exp2, Binding' exp3])
        | Lam (tp, exp) =>
          Abt.Oper (ExpCmdOps.Lam tp, [Binding' exp])
        | Ap (exp1, exp2) =>
          Abt.Oper (ExpCmdOps.Ap, [exp1, exp2])
        | Let (exp1, exp2) =>
          Abt.Oper (ExpCmdOps.Let, [exp1, Binding' exp2])
        | Fix (tp, exp) =>
          Abt.Oper (ExpCmdOps.Fix tp, [Binding' exp])
        | Pair (exp1, exp2) =>
          Abt.Oper (ExpCmdOps.Pair, [exp1, exp2])
        | Pr (side, exp) =>
          Abt.Oper (ExpCmdOps.Pr side, [exp])
        | Abort (tp, exp) =>
          Abt.Oper (ExpCmdOps.Abort tp, [exp])
        | In (tp1, tp2, side, exp) =>
          Abt.Oper (ExpCmdOps.In (tp1, tp2, side), [exp])
        | Case (exp1, exp2, exp3) =>
          Abt.Oper (ExpCmdOps.Case, [exp1, Binding' exp2, Binding' exp3])
        | Cmd cmd =>
          Abt.Oper (ExpCmdOps.Cmd cmd, [])

  fun view_out v =
      case v of
          Abt.Var x => Var x
        | Abt.Oper (ExpCmdOps.Z, []) => Z
        | Abt.Oper (ExpCmdOps.S, [exp]) => S exp
        | Abt.Oper (ExpCmdOps.Ifz, [exp1, exp2, exp3]) =>
          let val Abt.Binding exp3' = Abt.out ExpCmdOps.exp_oper_unbind exp3
          in Ifz (exp1, exp2, exp3')
          end
        | Abt.Oper (ExpCmdOps.Lam tp, [exp]) =>
          let val Abt.Binding exp' = Abt.out ExpCmdOps.exp_oper_unbind exp
          in Lam (tp, exp')
          end
        | Abt.Oper (ExpCmdOps.Ap, [exp1, exp2]) =>
          Ap (exp1, exp2)
        | Abt.Oper (ExpCmdOps.Let, [exp1, exp2]) =>
          let val Abt.Binding exp2' = Abt.out ExpCmdOps.exp_oper_unbind exp2
          in Let (exp1, exp2')
          end
        | Abt.Oper (ExpCmdOps.Fix tp, [exp]) =>
          let val Abt.Binding exp' = Abt.out ExpCmdOps.exp_oper_unbind exp
          in Fix (tp, exp')
          end
        | Abt.Oper (ExpCmdOps.Pair, [exp1, exp2]) =>
          Pair (exp1, exp2)
        | Abt.Oper (ExpCmdOps.Pr side, [exp]) =>
          Pr (side, exp)
        | Abt.Oper (ExpCmdOps.Abort tp, [exp]) =>
          Abort (tp, exp)
        | Abt.Oper (ExpCmdOps.In (tp1, tp2, side), [exp]) =>
          In (tp1, tp2, side, exp)
        | Abt.Oper (ExpCmdOps.Case, [exp1, exp2, exp3]) =>
          let
            val Abt.Binding exp2' = Abt.out ExpCmdOps.exp_oper_unbind exp2
            val Abt.Binding exp3' = Abt.out ExpCmdOps.exp_oper_unbind exp3
          in Case (exp1, exp2', exp3')
          end
        | Abt.Oper (ExpCmdOps.Cmd cmd, []) =>
          Cmd cmd

  val into = Abt.into ExpCmdOps.exp_oper_bind o view_in
  val out = view_out o Abt.out ExpCmdOps.exp_oper_unbind
  fun aequiv (l, r) = Abt.aequiv ExpCmdOps.exp_oper_aequiv (l, r)
  fun toString t = Abt.toString ExpCmdOps.exp_oper_toString t
  fun map f = view_out o Abt.map f o view_in

  val Var' = into o Var
  val Z' = into Z
  val S' = into o S
  val Ifz' = into o Ifz
  val Lam' = into o Lam
  val Ap' = into o Ap
  val Let' = into o Let
  val Fix' = into o Fix
  val Pair' = into o Pair
  val Pr' = into o Pr
  val Abort' = into o Abort
  val In' = into o In
  val Case' = into o Case
  val Cmd' = into o Cmd
end
