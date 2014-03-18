structure AbbotImpl = 
struct
   (* All symbols *)
   structure Assign = 
   struct
      datatype assign = Sym of string * int
      type t = assign
      val counter = ref 0
      val default = ("default", 0)
      fun hash (Sym (_, id)) = id
      fun newsym s = Sym (s, (counter := !counter + 1; !counter))
      fun equal (Sym (_, x), Sym (_, y)) = x = y
      fun compare (Sym (_, x), Sym (_, y)) = Int.compare (x, y)
      fun toString (Sym (s, id)) = s ^ "@" ^ Int.toString id
      fun toUserString (Sym (s, id)) = s
   end
   type assign = Assign.assign
   
   datatype 'a maybe_symbol
    = bound_symbol of IntInf.int 
    | free_symbol of 'a
   
   fun unbind_assign_assign n newfree x =
       case x of
          free_symbol _ => x
        | bound_symbol m => 
          if m < n then x else free_symbol newfree
   
   fun bind_assign_assign n oldfree x = 
       case x of
          free_symbol freesym =>
          if Assign.equal (oldfree, freesym)
          then bound_symbol n else x
        | bound_symbol _ => x
   
   fun out_assign (bound_symbol _) = 
       raise Fail "Invariant: exposed bvar"
     | out_assign (free_symbol x) = x
   
   fun into_assign x = free_symbol x
   
   fun aequiv_assign (x, y) = 
      case (x, y) of
         (free_symbol x, free_symbol y) => Assign.equal (x, y)
       | (bound_symbol x, bound_symbol y) => x = y
       | _ => false
   
   (* All variables *)
   structure ExpVar = 
   struct
      datatype expVar = Var of string * int
      type t = expVar
      val counter = ref 0
      val default = ("default", 0)
      fun hash (Var (_, id)) = id
      fun newvar s = Var (s, (counter := !counter + 1; !counter))
      fun equal (Var (_, x), Var (_, y)) = x = y
      fun compare (Var (_, x), Var (_, y)) = Int.compare (x, y)
      fun toString (Var (s, id)) = s ^ "@" ^ Int.toString id
      fun toUserString (Var (s, id)) = s
   end
   
   (* Implementation of recursive block: side *)
   
   structure Side =
   struct
      datatype 'side sideView
       = L
       | R
   end
   
   (* Naive and minimal implementation *)
   local
      datatype side
       = Impl_Side_L
       | Impl_Side_R
      
   in
      type side = side
      
      fun out_side x = 
         case x of
            Impl_Side_L =>
            Side.L
          | Impl_Side_R =>
            Side.R
      
      fun into_side x = 
         case x of
            Side.L =>
            Impl_Side_L
          | Side.R =>
            Impl_Side_R
      
      fun aequiv_side (x, y) = 
         case (x, y) of
            (Impl_Side_L, Impl_Side_L) => true
          | (Impl_Side_R, Impl_Side_R) => true
          | _ => false
         
   end
   
   (* Derived functions *)
   fun toString_side x = 
      case out_side x of
         Side.L =>
         "L"
       | Side.R =>
         "R"
   
   
   (* Implementation of recursive block: tp *)
   
   structure Tp =
   struct
      datatype 'tp tpView
       = Nat
       | Parr of 'tp * 'tp
       | Unit
       | Prod of 'tp * 'tp
       | Void
       | Sum of 'tp * 'tp
       | Cmd of 'tp
   end
   
   (* Naive and minimal implementation *)
   local
      datatype tp
       = Impl_Tp_Nat
       | Impl_Tp_Parr of tp * tp
       | Impl_Tp_Unit
       | Impl_Tp_Prod of tp * tp
       | Impl_Tp_Void
       | Impl_Tp_Sum of tp * tp
       | Impl_Tp_Cmd of tp
      
   in
      type tp = tp
      
      fun out_tp x = 
         case x of
            Impl_Tp_Nat =>
            Tp.Nat
          | Impl_Tp_Parr (tp1, tp2) =>
            Tp.Parr (tp1, tp2)
          | Impl_Tp_Unit =>
            Tp.Unit
          | Impl_Tp_Prod (tp1, tp2) =>
            Tp.Prod (tp1, tp2)
          | Impl_Tp_Void =>
            Tp.Void
          | Impl_Tp_Sum (tp1, tp2) =>
            Tp.Sum (tp1, tp2)
          | Impl_Tp_Cmd tp1 =>
            Tp.Cmd tp1
      
      fun into_tp x = 
         case x of
            Tp.Nat =>
            Impl_Tp_Nat
          | Tp.Parr (tp1, tp2) =>
            Impl_Tp_Parr (tp1, tp2)
          | Tp.Unit =>
            Impl_Tp_Unit
          | Tp.Prod (tp1, tp2) =>
            Impl_Tp_Prod (tp1, tp2)
          | Tp.Void =>
            Impl_Tp_Void
          | Tp.Sum (tp1, tp2) =>
            Impl_Tp_Sum (tp1, tp2)
          | Tp.Cmd tp1 =>
            Impl_Tp_Cmd tp1
      
      fun aequiv_tp (x, y) = 
         case (x, y) of
            (Impl_Tp_Nat, Impl_Tp_Nat) => true
          | (Impl_Tp_Parr x, Impl_Tp_Parr y) =>
            aequiv_tp (#1 x, #1 y) andalso
            aequiv_tp (#2 x, #2 y)
          | (Impl_Tp_Unit, Impl_Tp_Unit) => true
          | (Impl_Tp_Prod x, Impl_Tp_Prod y) =>
            aequiv_tp (#1 x, #1 y) andalso
            aequiv_tp (#2 x, #2 y)
          | (Impl_Tp_Void, Impl_Tp_Void) => true
          | (Impl_Tp_Sum x, Impl_Tp_Sum y) =>
            aequiv_tp (#1 x, #1 y) andalso
            aequiv_tp (#2 x, #2 y)
          | (Impl_Tp_Cmd x, Impl_Tp_Cmd y) => aequiv_tp (x, y)
          | _ => false
         
   end
   
   (* Derived functions *)
   fun toString_tp x = 
      case out_tp x of
         Tp.Nat =>
         "Nat"
       | Tp.Parr (tp1, tp2) =>
         "Parr("^toString_tp tp1^", "^toString_tp tp2^")"
       | Tp.Unit =>
         "Unit"
       | Tp.Prod (tp1, tp2) =>
         "Prod("^toString_tp tp1^", "^toString_tp tp2^")"
       | Tp.Void =>
         "Void"
       | Tp.Sum (tp1, tp2) =>
         "Sum("^toString_tp tp1^", "^toString_tp tp2^")"
       | Tp.Cmd tp1 =>
         "Cmd("^toString_tp tp1^")"
   
   
   (* Implementation of recursive block: exp, cmd *)
   
   structure Exp =
   struct
      datatype ('exp, 'cmd) expView
       = Var of ExpVar.t
       | Z
       | S of 'exp
       | Ifz of 'exp * 'exp * (ExpVar.t * 'exp)
       | Lam of tp * (ExpVar.t * 'exp)
       | Ap of 'exp * 'exp
       | Let of 'exp * (ExpVar.t * 'exp)
       | Fix of tp * (ExpVar.t * 'exp)
       | Triv
       | Pair of 'exp * 'exp
       | Pr of side * 'exp
       | Abort of tp * 'exp
       | In of tp * tp * side * 'exp
       | Case of 'exp * (ExpVar.t * 'exp) * (ExpVar.t * 'exp)
       | Cmd of 'cmd
   end
   
   structure Cmd =
   struct
      datatype ('exp, 'cmd) cmdView
       = Ret of 'exp
       | Bnd of 'exp * (ExpVar.t * 'cmd)
       | Dcl of 'exp * (assign * 'cmd)
       | Get of assign
       | Set of assign * 'exp
   end
   
   (* Naive and minimal implementation *)
   local
      datatype exp
       = Impl_Exp_BoundVar of IntInf.int
       | Impl_Exp_Var of ExpVar.t
       | Impl_Exp_Z
       | Impl_Exp_S of exp
       | Impl_Exp_Ifz of exp * exp * (string * exp)
       | Impl_Exp_Lam of tp * (string * exp)
       | Impl_Exp_Ap of exp * exp
       | Impl_Exp_Let of exp * (string * exp)
       | Impl_Exp_Fix of tp * (string * exp)
       | Impl_Exp_Triv
       | Impl_Exp_Pair of exp * exp
       | Impl_Exp_Pr of side * exp
       | Impl_Exp_Abort of tp * exp
       | Impl_Exp_In of tp * tp * side * exp
       | Impl_Exp_Case of exp * (string * exp) * (string * exp)
       | Impl_Exp_Cmd of cmd
      
      and cmd
       = Impl_Cmd_Ret of exp
       | Impl_Cmd_Bnd of exp * (string * cmd)
       | Impl_Cmd_Dcl of exp * (string * cmd)
       | Impl_Cmd_Get of assign maybe_symbol
       | Impl_Cmd_Set of assign maybe_symbol * exp
      
   in
      type exp = exp
      type cmd = cmd
      
      fun unbind_exp_exp n newfree x = 
         case x of
            Impl_Exp_Z =>
            Impl_Exp_Z
          | Impl_Exp_S exp1 =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
            in
               Impl_Exp_S exp1
            end
          | Impl_Exp_Ifz (exp1, exp2, (exp3, exp4)) =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
               val exp2 = unbind_exp_exp n newfree exp2
               val exp4 = unbind_exp_exp (n+1) newfree exp4
            in
               Impl_Exp_Ifz (exp1, exp2, (exp3, exp4))
            end
          | Impl_Exp_Lam (tp1, (exp2, exp3)) =>
            let
               val exp3 = unbind_exp_exp (n+1) newfree exp3
            in
               Impl_Exp_Lam (tp1, (exp2, exp3))
            end
          | Impl_Exp_Ap (exp1, exp2) =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
               val exp2 = unbind_exp_exp n newfree exp2
            in
               Impl_Exp_Ap (exp1, exp2)
            end
          | Impl_Exp_Let (exp1, (exp2, exp3)) =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
               val exp3 = unbind_exp_exp (n+1) newfree exp3
            in
               Impl_Exp_Let (exp1, (exp2, exp3))
            end
          | Impl_Exp_Fix (tp1, (exp2, exp3)) =>
            let
               val exp3 = unbind_exp_exp (n+1) newfree exp3
            in
               Impl_Exp_Fix (tp1, (exp2, exp3))
            end
          | Impl_Exp_Triv =>
            Impl_Exp_Triv
          | Impl_Exp_Pair (exp1, exp2) =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
               val exp2 = unbind_exp_exp n newfree exp2
            in
               Impl_Exp_Pair (exp1, exp2)
            end
          | Impl_Exp_Pr (side1, exp2) =>
            let
               val exp2 = unbind_exp_exp n newfree exp2
            in
               Impl_Exp_Pr (side1, exp2)
            end
          | Impl_Exp_Abort (tp1, exp2) =>
            let
               val exp2 = unbind_exp_exp n newfree exp2
            in
               Impl_Exp_Abort (tp1, exp2)
            end
          | Impl_Exp_In (tp1, tp2, side3, exp4) =>
            let
               val exp4 = unbind_exp_exp n newfree exp4
            in
               Impl_Exp_In (tp1, tp2, side3, exp4)
            end
          | Impl_Exp_Case (exp1, (exp2, exp3), (exp4, exp5)) =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
               val exp3 = unbind_exp_exp (n+1) newfree exp3
               val exp5 = unbind_exp_exp (n+1) newfree exp5
            in
               Impl_Exp_Case (exp1, (exp2, exp3), (exp4, exp5))
            end
          | Impl_Exp_Cmd cmd1 =>
            let
               val cmd1 = unbind_exp_cmd n newfree cmd1
            in
               Impl_Exp_Cmd cmd1
            end
          | Impl_Exp_Var x1 =>
            x
          | Impl_Exp_BoundVar n1 =>
            if n1 < n then x
            else Impl_Exp_Var newfree
      
      and unbind_exp_cmd n newfree x = 
         case x of
            Impl_Cmd_Ret exp1 =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
            in
               Impl_Cmd_Ret exp1
            end
          | Impl_Cmd_Bnd (exp1, (exp2, cmd3)) =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
               val cmd3 = unbind_exp_cmd (n+1) newfree cmd3
            in
               Impl_Cmd_Bnd (exp1, (exp2, cmd3))
            end
          | Impl_Cmd_Dcl (exp1, (assign2, cmd3)) =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
               val cmd3 = unbind_exp_cmd (n+1) newfree cmd3
            in
               Impl_Cmd_Dcl (exp1, (assign2, cmd3))
            end
          | Impl_Cmd_Get assign1 =>
            Impl_Cmd_Get assign1
          | Impl_Cmd_Set (assign1, exp2) =>
            let
               val exp2 = unbind_exp_exp n newfree exp2
            in
               Impl_Cmd_Set (assign1, exp2)
            end
      
      fun unbind_assign_exp n newfree x = 
         case x of
            Impl_Exp_Z =>
            Impl_Exp_Z
          | Impl_Exp_S exp1 =>
            let
               val exp1 = unbind_assign_exp n newfree exp1
            in
               Impl_Exp_S exp1
            end
          | Impl_Exp_Ifz (exp1, exp2, (exp3, exp4)) =>
            let
               val exp1 = unbind_assign_exp n newfree exp1
               val exp2 = unbind_assign_exp n newfree exp2
               val exp4 = unbind_assign_exp (n+1) newfree exp4
            in
               Impl_Exp_Ifz (exp1, exp2, (exp3, exp4))
            end
          | Impl_Exp_Lam (tp1, (exp2, exp3)) =>
            let
               val exp3 = unbind_assign_exp (n+1) newfree exp3
            in
               Impl_Exp_Lam (tp1, (exp2, exp3))
            end
          | Impl_Exp_Ap (exp1, exp2) =>
            let
               val exp1 = unbind_assign_exp n newfree exp1
               val exp2 = unbind_assign_exp n newfree exp2
            in
               Impl_Exp_Ap (exp1, exp2)
            end
          | Impl_Exp_Let (exp1, (exp2, exp3)) =>
            let
               val exp1 = unbind_assign_exp n newfree exp1
               val exp3 = unbind_assign_exp (n+1) newfree exp3
            in
               Impl_Exp_Let (exp1, (exp2, exp3))
            end
          | Impl_Exp_Fix (tp1, (exp2, exp3)) =>
            let
               val exp3 = unbind_assign_exp (n+1) newfree exp3
            in
               Impl_Exp_Fix (tp1, (exp2, exp3))
            end
          | Impl_Exp_Triv =>
            Impl_Exp_Triv
          | Impl_Exp_Pair (exp1, exp2) =>
            let
               val exp1 = unbind_assign_exp n newfree exp1
               val exp2 = unbind_assign_exp n newfree exp2
            in
               Impl_Exp_Pair (exp1, exp2)
            end
          | Impl_Exp_Pr (side1, exp2) =>
            let
               val exp2 = unbind_assign_exp n newfree exp2
            in
               Impl_Exp_Pr (side1, exp2)
            end
          | Impl_Exp_Abort (tp1, exp2) =>
            let
               val exp2 = unbind_assign_exp n newfree exp2
            in
               Impl_Exp_Abort (tp1, exp2)
            end
          | Impl_Exp_In (tp1, tp2, side3, exp4) =>
            let
               val exp4 = unbind_assign_exp n newfree exp4
            in
               Impl_Exp_In (tp1, tp2, side3, exp4)
            end
          | Impl_Exp_Case (exp1, (exp2, exp3), (exp4, exp5)) =>
            let
               val exp1 = unbind_assign_exp n newfree exp1
               val exp3 = unbind_assign_exp (n+1) newfree exp3
               val exp5 = unbind_assign_exp (n+1) newfree exp5
            in
               Impl_Exp_Case (exp1, (exp2, exp3), (exp4, exp5))
            end
          | Impl_Exp_Cmd cmd1 =>
            let
               val cmd1 = unbind_assign_cmd n newfree cmd1
            in
               Impl_Exp_Cmd cmd1
            end
          | Impl_Exp_Var x1 =>
            x
          | Impl_Exp_BoundVar n1 =>
            x
      
      and unbind_assign_cmd n newfree x = 
         case x of
            Impl_Cmd_Ret exp1 =>
            let
               val exp1 = unbind_assign_exp n newfree exp1
            in
               Impl_Cmd_Ret exp1
            end
          | Impl_Cmd_Bnd (exp1, (exp2, cmd3)) =>
            let
               val exp1 = unbind_assign_exp n newfree exp1
               val cmd3 = unbind_assign_cmd (n+1) newfree cmd3
            in
               Impl_Cmd_Bnd (exp1, (exp2, cmd3))
            end
          | Impl_Cmd_Dcl (exp1, (assign2, cmd3)) =>
            let
               val exp1 = unbind_assign_exp n newfree exp1
               val cmd3 = unbind_assign_cmd (n+1) newfree cmd3
            in
               Impl_Cmd_Dcl (exp1, (assign2, cmd3))
            end
          | Impl_Cmd_Get assign1 =>
            let
               val assign1 = unbind_assign_assign n newfree assign1
            in
               Impl_Cmd_Get assign1
            end
          | Impl_Cmd_Set (assign1, exp2) =>
            let
               val assign1 = unbind_assign_assign n newfree assign1
               val exp2 = unbind_assign_exp n newfree exp2
            in
               Impl_Cmd_Set (assign1, exp2)
            end
      
      fun out_exp x = 
         case x of
            Impl_Exp_Z =>
            Exp.Z
          | Impl_Exp_S exp1 =>
            Exp.S exp1
          | Impl_Exp_Ifz (exp1, exp2, (exp3, exp4)) =>
            let
               val exp3 = ExpVar.newvar exp3
               val exp4 = unbind_exp_exp 0 exp3 exp4
            in
               Exp.Ifz (exp1, exp2, (exp3, exp4))
            end
          | Impl_Exp_Lam (tp1, (exp2, exp3)) =>
            let
               val exp2 = ExpVar.newvar exp2
               val exp3 = unbind_exp_exp 0 exp2 exp3
            in
               Exp.Lam (tp1, (exp2, exp3))
            end
          | Impl_Exp_Ap (exp1, exp2) =>
            Exp.Ap (exp1, exp2)
          | Impl_Exp_Let (exp1, (exp2, exp3)) =>
            let
               val exp2 = ExpVar.newvar exp2
               val exp3 = unbind_exp_exp 0 exp2 exp3
            in
               Exp.Let (exp1, (exp2, exp3))
            end
          | Impl_Exp_Fix (tp1, (exp2, exp3)) =>
            let
               val exp2 = ExpVar.newvar exp2
               val exp3 = unbind_exp_exp 0 exp2 exp3
            in
               Exp.Fix (tp1, (exp2, exp3))
            end
          | Impl_Exp_Triv =>
            Exp.Triv
          | Impl_Exp_Pair (exp1, exp2) =>
            Exp.Pair (exp1, exp2)
          | Impl_Exp_Pr (side1, exp2) =>
            Exp.Pr (side1, exp2)
          | Impl_Exp_Abort (tp1, exp2) =>
            Exp.Abort (tp1, exp2)
          | Impl_Exp_In (tp1, tp2, side3, exp4) =>
            Exp.In (tp1, tp2, side3, exp4)
          | Impl_Exp_Case (exp1, (exp2, exp3), (exp4, exp5)) =>
            let
               val exp2 = ExpVar.newvar exp2
               val exp3 = unbind_exp_exp 0 exp2 exp3
               val exp4 = ExpVar.newvar exp4
               val exp5 = unbind_exp_exp 0 exp4 exp5
            in
               Exp.Case (exp1, (exp2, exp3), (exp4, exp5))
            end
          | Impl_Exp_Cmd cmd1 =>
            Exp.Cmd cmd1
          | Impl_Exp_Var x1 =>
            Exp.Var x1
          | Impl_Exp_BoundVar n1 =>
            raise Fail "Invariant: exposed bvar"
      
      and out_cmd x = 
         case x of
            Impl_Cmd_Ret exp1 =>
            Cmd.Ret exp1
          | Impl_Cmd_Bnd (exp1, (exp2, cmd3)) =>
            let
               val exp2 = ExpVar.newvar exp2
               val cmd3 = unbind_exp_cmd 0 exp2 cmd3
            in
               Cmd.Bnd (exp1, (exp2, cmd3))
            end
          | Impl_Cmd_Dcl (exp1, (assign2, cmd3)) =>
            let
               val assign2 = Assign.newsym assign2
               val cmd3 = unbind_assign_cmd 0 assign2 cmd3
            in
               Cmd.Dcl (exp1, (assign2, cmd3))
            end
          | Impl_Cmd_Get assign1 =>
            let
               val assign1 = out_assign assign1
            in
               Cmd.Get assign1
            end
          | Impl_Cmd_Set (assign1, exp2) =>
            let
               val assign1 = out_assign assign1
            in
               Cmd.Set (assign1, exp2)
            end
      
      fun bind_exp_exp n oldfree x = 
         case x of
            Impl_Exp_Z =>
            Impl_Exp_Z
          | Impl_Exp_S exp1 =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
            in
               Impl_Exp_S exp1
            end
          | Impl_Exp_Ifz (exp1, exp2, (exp3, exp4)) =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
               val exp2 = bind_exp_exp n oldfree exp2
               val exp4 = bind_exp_exp (n+1) oldfree exp4
            in
               Impl_Exp_Ifz (exp1, exp2, (exp3, exp4))
            end
          | Impl_Exp_Lam (tp1, (exp2, exp3)) =>
            let
               val exp3 = bind_exp_exp (n+1) oldfree exp3
            in
               Impl_Exp_Lam (tp1, (exp2, exp3))
            end
          | Impl_Exp_Ap (exp1, exp2) =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
               val exp2 = bind_exp_exp n oldfree exp2
            in
               Impl_Exp_Ap (exp1, exp2)
            end
          | Impl_Exp_Let (exp1, (exp2, exp3)) =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
               val exp3 = bind_exp_exp (n+1) oldfree exp3
            in
               Impl_Exp_Let (exp1, (exp2, exp3))
            end
          | Impl_Exp_Fix (tp1, (exp2, exp3)) =>
            let
               val exp3 = bind_exp_exp (n+1) oldfree exp3
            in
               Impl_Exp_Fix (tp1, (exp2, exp3))
            end
          | Impl_Exp_Triv =>
            Impl_Exp_Triv
          | Impl_Exp_Pair (exp1, exp2) =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
               val exp2 = bind_exp_exp n oldfree exp2
            in
               Impl_Exp_Pair (exp1, exp2)
            end
          | Impl_Exp_Pr (side1, exp2) =>
            let
               val exp2 = bind_exp_exp n oldfree exp2
            in
               Impl_Exp_Pr (side1, exp2)
            end
          | Impl_Exp_Abort (tp1, exp2) =>
            let
               val exp2 = bind_exp_exp n oldfree exp2
            in
               Impl_Exp_Abort (tp1, exp2)
            end
          | Impl_Exp_In (tp1, tp2, side3, exp4) =>
            let
               val exp4 = bind_exp_exp n oldfree exp4
            in
               Impl_Exp_In (tp1, tp2, side3, exp4)
            end
          | Impl_Exp_Case (exp1, (exp2, exp3), (exp4, exp5)) =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
               val exp3 = bind_exp_exp (n+1) oldfree exp3
               val exp5 = bind_exp_exp (n+1) oldfree exp5
            in
               Impl_Exp_Case (exp1, (exp2, exp3), (exp4, exp5))
            end
          | Impl_Exp_Cmd cmd1 =>
            let
               val cmd1 = bind_exp_cmd n oldfree cmd1
            in
               Impl_Exp_Cmd cmd1
            end
          | Impl_Exp_Var x1 =>
            if ExpVar.equal (oldfree, x1) then Impl_Exp_BoundVar n else x
          | Impl_Exp_BoundVar n1 =>
            x
      
      and bind_exp_cmd n oldfree x = 
         case x of
            Impl_Cmd_Ret exp1 =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
            in
               Impl_Cmd_Ret exp1
            end
          | Impl_Cmd_Bnd (exp1, (exp2, cmd3)) =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
               val cmd3 = bind_exp_cmd (n+1) oldfree cmd3
            in
               Impl_Cmd_Bnd (exp1, (exp2, cmd3))
            end
          | Impl_Cmd_Dcl (exp1, (assign2, cmd3)) =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
               val cmd3 = bind_exp_cmd (n+1) oldfree cmd3
            in
               Impl_Cmd_Dcl (exp1, (assign2, cmd3))
            end
          | Impl_Cmd_Get assign1 =>
            Impl_Cmd_Get assign1
          | Impl_Cmd_Set (assign1, exp2) =>
            let
               val exp2 = bind_exp_exp n oldfree exp2
            in
               Impl_Cmd_Set (assign1, exp2)
            end
      
      fun bind_assign_exp n oldfree x = 
         case x of
            Impl_Exp_Z =>
            Impl_Exp_Z
          | Impl_Exp_S exp1 =>
            let
               val exp1 = bind_assign_exp n oldfree exp1
            in
               Impl_Exp_S exp1
            end
          | Impl_Exp_Ifz (exp1, exp2, (exp3, exp4)) =>
            let
               val exp1 = bind_assign_exp n oldfree exp1
               val exp2 = bind_assign_exp n oldfree exp2
               val exp4 = bind_assign_exp (n+1) oldfree exp4
            in
               Impl_Exp_Ifz (exp1, exp2, (exp3, exp4))
            end
          | Impl_Exp_Lam (tp1, (exp2, exp3)) =>
            let
               val exp3 = bind_assign_exp (n+1) oldfree exp3
            in
               Impl_Exp_Lam (tp1, (exp2, exp3))
            end
          | Impl_Exp_Ap (exp1, exp2) =>
            let
               val exp1 = bind_assign_exp n oldfree exp1
               val exp2 = bind_assign_exp n oldfree exp2
            in
               Impl_Exp_Ap (exp1, exp2)
            end
          | Impl_Exp_Let (exp1, (exp2, exp3)) =>
            let
               val exp1 = bind_assign_exp n oldfree exp1
               val exp3 = bind_assign_exp (n+1) oldfree exp3
            in
               Impl_Exp_Let (exp1, (exp2, exp3))
            end
          | Impl_Exp_Fix (tp1, (exp2, exp3)) =>
            let
               val exp3 = bind_assign_exp (n+1) oldfree exp3
            in
               Impl_Exp_Fix (tp1, (exp2, exp3))
            end
          | Impl_Exp_Triv =>
            Impl_Exp_Triv
          | Impl_Exp_Pair (exp1, exp2) =>
            let
               val exp1 = bind_assign_exp n oldfree exp1
               val exp2 = bind_assign_exp n oldfree exp2
            in
               Impl_Exp_Pair (exp1, exp2)
            end
          | Impl_Exp_Pr (side1, exp2) =>
            let
               val exp2 = bind_assign_exp n oldfree exp2
            in
               Impl_Exp_Pr (side1, exp2)
            end
          | Impl_Exp_Abort (tp1, exp2) =>
            let
               val exp2 = bind_assign_exp n oldfree exp2
            in
               Impl_Exp_Abort (tp1, exp2)
            end
          | Impl_Exp_In (tp1, tp2, side3, exp4) =>
            let
               val exp4 = bind_assign_exp n oldfree exp4
            in
               Impl_Exp_In (tp1, tp2, side3, exp4)
            end
          | Impl_Exp_Case (exp1, (exp2, exp3), (exp4, exp5)) =>
            let
               val exp1 = bind_assign_exp n oldfree exp1
               val exp3 = bind_assign_exp (n+1) oldfree exp3
               val exp5 = bind_assign_exp (n+1) oldfree exp5
            in
               Impl_Exp_Case (exp1, (exp2, exp3), (exp4, exp5))
            end
          | Impl_Exp_Cmd cmd1 =>
            let
               val cmd1 = bind_assign_cmd n oldfree cmd1
            in
               Impl_Exp_Cmd cmd1
            end
          | Impl_Exp_Var x1 =>
            x
          | Impl_Exp_BoundVar n1 =>
            x
      
      and bind_assign_cmd n oldfree x = 
         case x of
            Impl_Cmd_Ret exp1 =>
            let
               val exp1 = bind_assign_exp n oldfree exp1
            in
               Impl_Cmd_Ret exp1
            end
          | Impl_Cmd_Bnd (exp1, (exp2, cmd3)) =>
            let
               val exp1 = bind_assign_exp n oldfree exp1
               val cmd3 = bind_assign_cmd (n+1) oldfree cmd3
            in
               Impl_Cmd_Bnd (exp1, (exp2, cmd3))
            end
          | Impl_Cmd_Dcl (exp1, (assign2, cmd3)) =>
            let
               val exp1 = bind_assign_exp n oldfree exp1
               val cmd3 = bind_assign_cmd (n+1) oldfree cmd3
            in
               Impl_Cmd_Dcl (exp1, (assign2, cmd3))
            end
          | Impl_Cmd_Get assign1 =>
            let
               val assign1 = bind_assign_assign n oldfree assign1
            in
               Impl_Cmd_Get assign1
            end
          | Impl_Cmd_Set (assign1, exp2) =>
            let
               val assign1 = bind_assign_assign n oldfree assign1
               val exp2 = bind_assign_exp n oldfree exp2
            in
               Impl_Cmd_Set (assign1, exp2)
            end
      
      fun into_exp x = 
         case x of
            Exp.Z =>
            Impl_Exp_Z
          | Exp.S exp1 =>
            Impl_Exp_S exp1
          | Exp.Ifz (exp1, exp2, (exp3, exp4)) =>
            let
               val exp4 = bind_exp_exp 0 exp3 exp4
               val exp3 = ExpVar.toUserString exp3
            in
               Impl_Exp_Ifz (exp1, exp2, (exp3, exp4))
            end
          | Exp.Lam (tp1, (exp2, exp3)) =>
            let
               val exp3 = bind_exp_exp 0 exp2 exp3
               val exp2 = ExpVar.toUserString exp2
            in
               Impl_Exp_Lam (tp1, (exp2, exp3))
            end
          | Exp.Ap (exp1, exp2) =>
            Impl_Exp_Ap (exp1, exp2)
          | Exp.Let (exp1, (exp2, exp3)) =>
            let
               val exp3 = bind_exp_exp 0 exp2 exp3
               val exp2 = ExpVar.toUserString exp2
            in
               Impl_Exp_Let (exp1, (exp2, exp3))
            end
          | Exp.Fix (tp1, (exp2, exp3)) =>
            let
               val exp3 = bind_exp_exp 0 exp2 exp3
               val exp2 = ExpVar.toUserString exp2
            in
               Impl_Exp_Fix (tp1, (exp2, exp3))
            end
          | Exp.Triv =>
            Impl_Exp_Triv
          | Exp.Pair (exp1, exp2) =>
            Impl_Exp_Pair (exp1, exp2)
          | Exp.Pr (side1, exp2) =>
            Impl_Exp_Pr (side1, exp2)
          | Exp.Abort (tp1, exp2) =>
            Impl_Exp_Abort (tp1, exp2)
          | Exp.In (tp1, tp2, side3, exp4) =>
            Impl_Exp_In (tp1, tp2, side3, exp4)
          | Exp.Case (exp1, (exp2, exp3), (exp4, exp5)) =>
            let
               val exp3 = bind_exp_exp 0 exp2 exp3
               val exp2 = ExpVar.toUserString exp2
               val exp5 = bind_exp_exp 0 exp4 exp5
               val exp4 = ExpVar.toUserString exp4
            in
               Impl_Exp_Case (exp1, (exp2, exp3), (exp4, exp5))
            end
          | Exp.Cmd cmd1 =>
            Impl_Exp_Cmd cmd1
          | Exp.Var x1 =>
            Impl_Exp_Var x1
      
      and into_cmd x = 
         case x of
            Cmd.Ret exp1 =>
            Impl_Cmd_Ret exp1
          | Cmd.Bnd (exp1, (exp2, cmd3)) =>
            let
               val cmd3 = bind_exp_cmd 0 exp2 cmd3
               val exp2 = ExpVar.toUserString exp2
            in
               Impl_Cmd_Bnd (exp1, (exp2, cmd3))
            end
          | Cmd.Dcl (exp1, (assign2, cmd3)) =>
            let
               val cmd3 = bind_assign_cmd 0 assign2 cmd3
               val assign2 = Assign.toUserString assign2
            in
               Impl_Cmd_Dcl (exp1, (assign2, cmd3))
            end
          | Cmd.Get assign1 =>
            let
               val assign1 = into_assign assign1
            in
               Impl_Cmd_Get assign1
            end
          | Cmd.Set (assign1, exp2) =>
            let
               val assign1 = into_assign assign1
            in
               Impl_Cmd_Set (assign1, exp2)
            end
      
      fun aequiv_exp (x, y) = 
         case (x, y) of
            (Impl_Exp_Z, Impl_Exp_Z) => true
          | (Impl_Exp_S x, Impl_Exp_S y) => aequiv_exp (x, y)
          | (Impl_Exp_Ifz x, Impl_Exp_Ifz y) =>
            aequiv_exp (#1 x, #1 y) andalso
            aequiv_exp (#2 x, #2 y) andalso
            aequiv_exp (#2 (#3 x), #2 (#3 y))
          | (Impl_Exp_Lam x, Impl_Exp_Lam y) =>
            aequiv_tp (#1 x, #1 y) andalso
            aequiv_exp (#2 (#2 x), #2 (#2 y))
          | (Impl_Exp_Ap x, Impl_Exp_Ap y) =>
            aequiv_exp (#1 x, #1 y) andalso
            aequiv_exp (#2 x, #2 y)
          | (Impl_Exp_Let x, Impl_Exp_Let y) =>
            aequiv_exp (#1 x, #1 y) andalso
            aequiv_exp (#2 (#2 x), #2 (#2 y))
          | (Impl_Exp_Fix x, Impl_Exp_Fix y) =>
            aequiv_tp (#1 x, #1 y) andalso
            aequiv_exp (#2 (#2 x), #2 (#2 y))
          | (Impl_Exp_Triv, Impl_Exp_Triv) => true
          | (Impl_Exp_Pair x, Impl_Exp_Pair y) =>
            aequiv_exp (#1 x, #1 y) andalso
            aequiv_exp (#2 x, #2 y)
          | (Impl_Exp_Pr x, Impl_Exp_Pr y) =>
            aequiv_side (#1 x, #1 y) andalso
            aequiv_exp (#2 x, #2 y)
          | (Impl_Exp_Abort x, Impl_Exp_Abort y) =>
            aequiv_tp (#1 x, #1 y) andalso
            aequiv_exp (#2 x, #2 y)
          | (Impl_Exp_In x, Impl_Exp_In y) =>
            aequiv_tp (#1 x, #1 y) andalso
            aequiv_tp (#2 x, #2 y) andalso
            aequiv_side (#3 x, #3 y) andalso
            aequiv_exp (#4 x, #4 y)
          | (Impl_Exp_Case x, Impl_Exp_Case y) =>
            aequiv_exp (#1 x, #1 y) andalso
            aequiv_exp (#2 (#2 x), #2 (#2 y)) andalso
            aequiv_exp (#2 (#3 x), #2 (#3 y))
          | (Impl_Exp_Cmd x, Impl_Exp_Cmd y) => aequiv_cmd (x, y)
          | (Impl_Exp_BoundVar x, Impl_Exp_BoundVar y) => x = y
          | (Impl_Exp_Var x, Impl_Exp_Var y) => ExpVar.equal (x, y)
          | _ => false
         
      and aequiv_cmd (x, y) = 
         case (x, y) of
            (Impl_Cmd_Ret x, Impl_Cmd_Ret y) => aequiv_exp (x, y)
          | (Impl_Cmd_Bnd x, Impl_Cmd_Bnd y) =>
            aequiv_exp (#1 x, #1 y) andalso
            aequiv_cmd (#2 (#2 x), #2 (#2 y))
          | (Impl_Cmd_Dcl x, Impl_Cmd_Dcl y) =>
            aequiv_exp (#1 x, #1 y) andalso
            aequiv_cmd (#2 (#2 x), #2 (#2 y))
          | (Impl_Cmd_Get x, Impl_Cmd_Get y) => aequiv_assign (x, y)
          | (Impl_Cmd_Set x, Impl_Cmd_Set y) =>
            aequiv_assign (#1 x, #1 y) andalso
            aequiv_exp (#2 x, #2 y)
          | _ => false
         
      val free_exp_exp = fn _ => raise Fail "Unimpl"
      val free_exp_cmd = fn _ => raise Fail "Unimpl"
      val free_assign_exp = fn _ => raise Fail "Unimpl"
      val free_assign_cmd = fn _ => raise Fail "Unimpl"
   end
   
   (* Derived functions *)
   fun subst_exp_exp t x s = 
      case out_exp s of
         Exp.Z =>
         into_exp (Exp.Z)
       | Exp.S exp1 =>
         let
            val exp1 = subst_exp_exp t x exp1
         in
            into_exp (Exp.S exp1)
         end
       | Exp.Ifz (exp1, exp2, (exp3, exp4)) =>
         let
            val exp1 = subst_exp_exp t x exp1
            val exp2 = subst_exp_exp t x exp2
            val exp4 = subst_exp_exp t x exp4
         in
            into_exp (Exp.Ifz (exp1, exp2, (exp3, exp4)))
         end
       | Exp.Lam (tp1, (exp2, exp3)) =>
         let
            val exp3 = subst_exp_exp t x exp3
         in
            into_exp (Exp.Lam (tp1, (exp2, exp3)))
         end
       | Exp.Ap (exp1, exp2) =>
         let
            val exp1 = subst_exp_exp t x exp1
            val exp2 = subst_exp_exp t x exp2
         in
            into_exp (Exp.Ap (exp1, exp2))
         end
       | Exp.Let (exp1, (exp2, exp3)) =>
         let
            val exp1 = subst_exp_exp t x exp1
            val exp3 = subst_exp_exp t x exp3
         in
            into_exp (Exp.Let (exp1, (exp2, exp3)))
         end
       | Exp.Fix (tp1, (exp2, exp3)) =>
         let
            val exp3 = subst_exp_exp t x exp3
         in
            into_exp (Exp.Fix (tp1, (exp2, exp3)))
         end
       | Exp.Triv =>
         into_exp (Exp.Triv)
       | Exp.Pair (exp1, exp2) =>
         let
            val exp1 = subst_exp_exp t x exp1
            val exp2 = subst_exp_exp t x exp2
         in
            into_exp (Exp.Pair (exp1, exp2))
         end
       | Exp.Pr (side1, exp2) =>
         let
            val exp2 = subst_exp_exp t x exp2
         in
            into_exp (Exp.Pr (side1, exp2))
         end
       | Exp.Abort (tp1, exp2) =>
         let
            val exp2 = subst_exp_exp t x exp2
         in
            into_exp (Exp.Abort (tp1, exp2))
         end
       | Exp.In (tp1, tp2, side3, exp4) =>
         let
            val exp4 = subst_exp_exp t x exp4
         in
            into_exp (Exp.In (tp1, tp2, side3, exp4))
         end
       | Exp.Case (exp1, (exp2, exp3), (exp4, exp5)) =>
         let
            val exp1 = subst_exp_exp t x exp1
            val exp3 = subst_exp_exp t x exp3
            val exp5 = subst_exp_exp t x exp5
         in
            into_exp (Exp.Case (exp1, (exp2, exp3), (exp4, exp5)))
         end
       | Exp.Cmd cmd1 =>
         let
            val cmd1 = subst_exp_cmd t x cmd1
         in
            into_exp (Exp.Cmd cmd1)
         end
       | Exp.Var x1 =>
         if ExpVar.equal (x, x1)
         then t else s
   
   and subst_exp_cmd t x s = 
      case out_cmd s of
         Cmd.Ret exp1 =>
         let
            val exp1 = subst_exp_exp t x exp1
         in
            into_cmd (Cmd.Ret exp1)
         end
       | Cmd.Bnd (exp1, (exp2, cmd3)) =>
         let
            val exp1 = subst_exp_exp t x exp1
            val cmd3 = subst_exp_cmd t x cmd3
         in
            into_cmd (Cmd.Bnd (exp1, (exp2, cmd3)))
         end
       | Cmd.Dcl (exp1, (assign2, cmd3)) =>
         let
            val exp1 = subst_exp_exp t x exp1
            val cmd3 = subst_exp_cmd t x cmd3
         in
            into_cmd (Cmd.Dcl (exp1, (assign2, cmd3)))
         end
       | Cmd.Get assign1 =>
         into_cmd (Cmd.Get assign1)
       | Cmd.Set (assign1, exp2) =>
         let
            val exp2 = subst_exp_exp t x exp2
         in
            into_cmd (Cmd.Set (assign1, exp2))
         end
   
   fun toString_exp x = 
      case out_exp x of
         Exp.Z =>
         "Z"
       | Exp.S exp1 =>
         "S("^toString_exp exp1^")"
       | Exp.Ifz (exp1, exp2, (exp3, exp4)) =>
         "Ifz("^toString_exp exp1^", "^toString_exp exp2^", "^ExpVar.toString exp3^"."^toString_exp exp4^")"
       | Exp.Lam (tp1, (exp2, exp3)) =>
         "Lam("^toString_tp tp1^", "^ExpVar.toString exp2^"."^toString_exp exp3^")"
       | Exp.Ap (exp1, exp2) =>
         "Ap("^toString_exp exp1^", "^toString_exp exp2^")"
       | Exp.Let (exp1, (exp2, exp3)) =>
         "Let("^toString_exp exp1^", "^ExpVar.toString exp2^"."^toString_exp exp3^")"
       | Exp.Fix (tp1, (exp2, exp3)) =>
         "Fix("^toString_tp tp1^", "^ExpVar.toString exp2^"."^toString_exp exp3^")"
       | Exp.Triv =>
         "Triv"
       | Exp.Pair (exp1, exp2) =>
         "Pair("^toString_exp exp1^", "^toString_exp exp2^")"
       | Exp.Pr (side1, exp2) =>
         "Pr("^toString_side side1^", "^toString_exp exp2^")"
       | Exp.Abort (tp1, exp2) =>
         "Abort("^toString_tp tp1^", "^toString_exp exp2^")"
       | Exp.In (tp1, tp2, side3, exp4) =>
         "In("^toString_tp tp1^", "^toString_tp tp2^", "^toString_side side3^", "^toString_exp exp4^")"
       | Exp.Case (exp1, (exp2, exp3), (exp4, exp5)) =>
         "Case("^toString_exp exp1^", "^ExpVar.toString exp2^"."^toString_exp exp3^", "^ExpVar.toString exp4^"."^toString_exp exp5^")"
       | Exp.Cmd cmd1 =>
         "Cmd("^toString_cmd cmd1^")"
       | Exp.Var x1 =>
         ExpVar.toString x1
   
   and toString_cmd x = 
      case out_cmd x of
         Cmd.Ret exp1 =>
         "Ret("^toString_exp exp1^")"
       | Cmd.Bnd (exp1, (exp2, cmd3)) =>
         "Bnd("^toString_exp exp1^", "^ExpVar.toString exp2^"."^toString_cmd cmd3^")"
       | Cmd.Dcl (exp1, (assign2, cmd3)) =>
         "Dcl("^toString_exp exp1^", "^Assign.toString assign2^"."^toString_cmd cmd3^")"
       | Cmd.Get assign1 =>
         "Get("^Assign.toString assign1^")"
       | Cmd.Set (assign1, exp2) =>
         "Set("^Assign.toString assign1^", "^toString_exp exp2^")"
   
   
   (* Rebind structs with full contents *)
   structure Side =
   struct
      type t = side
      type side = side
      open Side
      
      fun fmap f_side x = 
         case x of
            Side.L =>
            Side.L
          | Side.R =>
            Side.R
      
      val into = into_side
      val out = out_side
      val aequiv = aequiv_side
      val toString = toString_side
      val L' = into Side.L
      val R' = into Side.R
   end
   
   structure Tp =
   struct
      type t = tp
      type tp = tp
      open Tp
      
      fun fmap f_tp x = 
         case x of
            Tp.Nat =>
            Tp.Nat
          | Tp.Parr (tp1, tp2) =>
            let
               val tp1 = f_tp tp1
               val tp2 = f_tp tp2
            in
               Tp.Parr (tp1, tp2)
            end
          | Tp.Unit =>
            Tp.Unit
          | Tp.Prod (tp1, tp2) =>
            let
               val tp1 = f_tp tp1
               val tp2 = f_tp tp2
            in
               Tp.Prod (tp1, tp2)
            end
          | Tp.Void =>
            Tp.Void
          | Tp.Sum (tp1, tp2) =>
            let
               val tp1 = f_tp tp1
               val tp2 = f_tp tp2
            in
               Tp.Sum (tp1, tp2)
            end
          | Tp.Cmd tp1 =>
            let
               val tp1 = f_tp tp1
            in
               Tp.Cmd tp1
            end
      
      val into = into_tp
      val out = out_tp
      val aequiv = aequiv_tp
      val toString = toString_tp
      val Nat' = into Tp.Nat
      val Parr' = fn x => into (Parr x)
      val Unit' = into Tp.Unit
      val Prod' = fn x => into (Prod x)
      val Void' = into Tp.Void
      val Sum' = fn x => into (Sum x)
      val Cmd' = fn x => into (Cmd x)
   end
   
   structure Exp =
   struct
      type t = exp
      type exp = exp
      type cmd = cmd
      type expVar = ExpVar.t
      open Exp
      
      fun fmap f_exp f_cmd x = 
         case x of
            Exp.Z =>
            Exp.Z
          | Exp.S exp1 =>
            let
               val exp1 = f_exp exp1
            in
               Exp.S exp1
            end
          | Exp.Ifz (exp1, exp2, (exp3, exp4)) =>
            let
               val exp1 = f_exp exp1
               val exp2 = f_exp exp2
               val exp4 = f_exp exp4
            in
               Exp.Ifz (exp1, exp2, (exp3, exp4))
            end
          | Exp.Lam (tp1, (exp2, exp3)) =>
            let
               val exp3 = f_exp exp3
            in
               Exp.Lam (tp1, (exp2, exp3))
            end
          | Exp.Ap (exp1, exp2) =>
            let
               val exp1 = f_exp exp1
               val exp2 = f_exp exp2
            in
               Exp.Ap (exp1, exp2)
            end
          | Exp.Let (exp1, (exp2, exp3)) =>
            let
               val exp1 = f_exp exp1
               val exp3 = f_exp exp3
            in
               Exp.Let (exp1, (exp2, exp3))
            end
          | Exp.Fix (tp1, (exp2, exp3)) =>
            let
               val exp3 = f_exp exp3
            in
               Exp.Fix (tp1, (exp2, exp3))
            end
          | Exp.Triv =>
            Exp.Triv
          | Exp.Pair (exp1, exp2) =>
            let
               val exp1 = f_exp exp1
               val exp2 = f_exp exp2
            in
               Exp.Pair (exp1, exp2)
            end
          | Exp.Pr (side1, exp2) =>
            let
               val exp2 = f_exp exp2
            in
               Exp.Pr (side1, exp2)
            end
          | Exp.Abort (tp1, exp2) =>
            let
               val exp2 = f_exp exp2
            in
               Exp.Abort (tp1, exp2)
            end
          | Exp.In (tp1, tp2, side3, exp4) =>
            let
               val exp4 = f_exp exp4
            in
               Exp.In (tp1, tp2, side3, exp4)
            end
          | Exp.Case (exp1, (exp2, exp3), (exp4, exp5)) =>
            let
               val exp1 = f_exp exp1
               val exp3 = f_exp exp3
               val exp5 = f_exp exp5
            in
               Exp.Case (exp1, (exp2, exp3), (exp4, exp5))
            end
          | Exp.Cmd cmd1 =>
            let
               val cmd1 = f_cmd cmd1
            in
               Exp.Cmd cmd1
            end
          | Exp.Var x1 =>
            Exp.Var x1
      
      val into = into_exp
      val out = out_exp
      structure Var = ExpVar
      val Var' = fn x => into (Var x)
      val aequiv = aequiv_exp
      val toString = toString_exp
      val subst = subst_exp_exp
      val freevars = free_exp_exp
      val freeAssign = free_assign_exp
      val Z' = into Exp.Z
      val S' = fn x => into (S x)
      val Ifz' = fn x => into (Ifz x)
      val Lam' = fn x => into (Lam x)
      val Ap' = fn x => into (Ap x)
      val Let' = fn x => into (Let x)
      val Fix' = fn x => into (Fix x)
      val Triv' = into Exp.Triv
      val Pair' = fn x => into (Pair x)
      val Pr' = fn x => into (Pr x)
      val Abort' = fn x => into (Abort x)
      val In' = fn x => into (In x)
      val Case' = fn x => into (Case x)
      val Cmd' = fn x => into (Cmd x)
   end
   
   structure Cmd =
   struct
      type t = cmd
      type exp = exp
      type cmd = cmd
      type expVar = ExpVar.t
      open Cmd
      
      fun fmap f_exp f_cmd x = 
         case x of
            Cmd.Ret exp1 =>
            let
               val exp1 = f_exp exp1
            in
               Cmd.Ret exp1
            end
          | Cmd.Bnd (exp1, (exp2, cmd3)) =>
            let
               val exp1 = f_exp exp1
               val cmd3 = f_cmd cmd3
            in
               Cmd.Bnd (exp1, (exp2, cmd3))
            end
          | Cmd.Dcl (exp1, (assign2, cmd3)) =>
            let
               val exp1 = f_exp exp1
               val cmd3 = f_cmd cmd3
            in
               Cmd.Dcl (exp1, (assign2, cmd3))
            end
          | Cmd.Get assign1 =>
            Cmd.Get assign1
          | Cmd.Set (assign1, exp2) =>
            let
               val exp2 = f_exp exp2
            in
               Cmd.Set (assign1, exp2)
            end
      
      val into = into_cmd
      val out = out_cmd
      val aequiv = aequiv_cmd
      val toString = toString_cmd
      val substExp = subst_exp_cmd
      val freeExpVars = free_exp_cmd
      val freeAssign = free_assign_cmd
      val Ret' = fn x => into (Ret x)
      val Bnd' = fn x => into (Bnd x)
      val Dcl' = fn x => into (Dcl x)
      val Get' = fn x => into (Get x)
      val Set' = fn x => into (Set x)
   end
   
end
