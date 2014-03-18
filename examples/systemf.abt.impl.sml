structure AbbotImpl = 
struct
   (* All symbols *)
   datatype 'a maybe_symbol
    = bound_symbol of IntInf.int 
    | free_symbol of 'a
   
   (* All variables *)
   structure TpVar = 
   struct
      datatype tpVar = Var of string * int
      type t = tpVar
      val counter = ref 0
      val default = ("default", 0)
      fun hash (Var (_, id)) = id
      fun newvar s = Var (s, (counter := !counter + 1; !counter))
      fun equal (Var (_, x), Var (_, y)) = x = y
      fun compare (Var (_, x), Var (_, y)) = Int.compare (x, y)
      fun toString (Var (s, id)) = s ^ "@" ^ Int.toString id
      fun toUserString (Var (s, id)) = s
   end
   
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
   
   (* Implementation of recursive block: tp *)
   
   structure Tp =
   struct
      datatype 'tp tpView
       = Var of TpVar.t
       | All of (TpVar.t * 'tp)
       | Arr of 'tp * 'tp
   end
   
   (* Naive and minimal implementation *)
   local
      datatype tp
       = Impl_Tp_BoundVar of IntInf.int
       | Impl_Tp_Var of TpVar.t
       | Impl_Tp_All of (string * tp)
       | Impl_Tp_Arr of tp * tp
      
   in
      type tp = tp
      
      fun unbind_tp_tp n newfree x = 
         case x of
            Impl_Tp_All (tp1, tp2) =>
            let
               val tp2 = unbind_tp_tp (n+1) newfree tp2
            in
               Impl_Tp_All (tp1, tp2)
            end
          | Impl_Tp_Arr (tp1, tp2) =>
            let
               val tp1 = unbind_tp_tp n newfree tp1
               val tp2 = unbind_tp_tp n newfree tp2
            in
               Impl_Tp_Arr (tp1, tp2)
            end
          | Impl_Tp_Var x1 =>
            x
          | Impl_Tp_BoundVar n1 =>
            if n1 < n then x
            else Impl_Tp_Var newfree
      
      fun out_tp x = 
         case x of
            Impl_Tp_All (tp1, tp2) =>
            let
               val tp1 = TpVar.newvar tp1
               val tp2 = unbind_tp_tp 0 tp1 tp2
            in
               Tp.All (tp1, tp2)
            end
          | Impl_Tp_Arr (tp1, tp2) =>
            Tp.Arr (tp1, tp2)
          | Impl_Tp_Var x1 =>
            Tp.Var x1
          | Impl_Tp_BoundVar n1 =>
            raise Fail "Invariant: exposed bvar"
      
      fun bind_tp_tp n oldfree x = 
         case x of
            Impl_Tp_All (tp1, tp2) =>
            let
               val tp2 = bind_tp_tp (n+1) oldfree tp2
            in
               Impl_Tp_All (tp1, tp2)
            end
          | Impl_Tp_Arr (tp1, tp2) =>
            let
               val tp1 = bind_tp_tp n oldfree tp1
               val tp2 = bind_tp_tp n oldfree tp2
            in
               Impl_Tp_Arr (tp1, tp2)
            end
          | Impl_Tp_Var x1 =>
            if TpVar.equal (oldfree, x1) then Impl_Tp_BoundVar n else x
          | Impl_Tp_BoundVar n1 =>
            x
      
      fun into_tp x = 
         case x of
            Tp.All (tp1, tp2) =>
            let
               val tp2 = bind_tp_tp 0 tp1 tp2
               val tp1 = TpVar.toUserString tp1
            in
               Impl_Tp_All (tp1, tp2)
            end
          | Tp.Arr (tp1, tp2) =>
            Impl_Tp_Arr (tp1, tp2)
          | Tp.Var x1 =>
            Impl_Tp_Var x1
      
      fun aequiv_tp (x, y) = 
         case (x, y) of
            (Impl_Tp_All x, Impl_Tp_All y) => aequiv_tp (#2 x, #2 y)
          | (Impl_Tp_Arr x, Impl_Tp_Arr y) =>
            aequiv_tp (#1 x, #1 y) andalso
            aequiv_tp (#2 x, #2 y)
          | (Impl_Tp_BoundVar x, Impl_Tp_BoundVar y) => x = y
          | (Impl_Tp_Var x, Impl_Tp_Var y) => TpVar.equal (x, y)
          | _ => false
         
      val free_tp_tp = fn _ => raise Fail "Unimpl"
   end
   
   (* Derived functions *)
   fun subst_tp_tp t x s = 
      case out_tp s of
         Tp.All (tp1, tp2) =>
         let
            val tp2 = subst_tp_tp t x tp2
         in
            into_tp (Tp.All (tp1, tp2))
         end
       | Tp.Arr (tp1, tp2) =>
         let
            val tp1 = subst_tp_tp t x tp1
            val tp2 = subst_tp_tp t x tp2
         in
            into_tp (Tp.Arr (tp1, tp2))
         end
       | Tp.Var x1 =>
         if TpVar.equal (x, x1)
         then t else s
   
   fun toString_tp x = 
      case out_tp x of
         Tp.All (tp1, tp2) =>
         "All("^TpVar.toString tp1^"."^toString_tp tp2^")"
       | Tp.Arr (tp1, tp2) =>
         "Arr("^toString_tp tp1^", "^toString_tp tp2^")"
       | Tp.Var x1 =>
         TpVar.toString x1
   
   
   (* Implementation of recursive block: exp *)
   
   structure Exp =
   struct
      datatype 'exp expView
       = Var of ExpVar.t
       | Lam of tp * (ExpVar.t * 'exp)
       | App of 'exp * 'exp
       | TLam of (TpVar.t * 'exp)
       | TApp of 'exp * tp
   end
   
   (* Naive and minimal implementation *)
   local
      datatype exp
       = Impl_Exp_BoundVar of IntInf.int
       | Impl_Exp_Var of ExpVar.t
       | Impl_Exp_Lam of tp * (string * exp)
       | Impl_Exp_App of exp * exp
       | Impl_Exp_TLam of (string * exp)
       | Impl_Exp_TApp of exp * tp
      
   in
      type exp = exp
      
      fun unbind_tp_exp n newfree x = 
         case x of
            Impl_Exp_Lam (tp1, (exp2, exp3)) =>
            let
               val tp1 = unbind_tp_tp n newfree tp1
               val exp3 = unbind_tp_exp (n+1) newfree exp3
            in
               Impl_Exp_Lam (tp1, (exp2, exp3))
            end
          | Impl_Exp_App (exp1, exp2) =>
            let
               val exp1 = unbind_tp_exp n newfree exp1
               val exp2 = unbind_tp_exp n newfree exp2
            in
               Impl_Exp_App (exp1, exp2)
            end
          | Impl_Exp_TLam (tp1, exp2) =>
            let
               val exp2 = unbind_tp_exp (n+1) newfree exp2
            in
               Impl_Exp_TLam (tp1, exp2)
            end
          | Impl_Exp_TApp (exp1, tp2) =>
            let
               val exp1 = unbind_tp_exp n newfree exp1
               val tp2 = unbind_tp_tp n newfree tp2
            in
               Impl_Exp_TApp (exp1, tp2)
            end
          | Impl_Exp_Var x1 =>
            x
          | Impl_Exp_BoundVar n1 =>
            x
      
      fun unbind_exp_exp n newfree x = 
         case x of
            Impl_Exp_Lam (tp1, (exp2, exp3)) =>
            let
               val exp3 = unbind_exp_exp (n+1) newfree exp3
            in
               Impl_Exp_Lam (tp1, (exp2, exp3))
            end
          | Impl_Exp_App (exp1, exp2) =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
               val exp2 = unbind_exp_exp n newfree exp2
            in
               Impl_Exp_App (exp1, exp2)
            end
          | Impl_Exp_TLam (tp1, exp2) =>
            let
               val exp2 = unbind_exp_exp (n+1) newfree exp2
            in
               Impl_Exp_TLam (tp1, exp2)
            end
          | Impl_Exp_TApp (exp1, tp2) =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
            in
               Impl_Exp_TApp (exp1, tp2)
            end
          | Impl_Exp_Var x1 =>
            x
          | Impl_Exp_BoundVar n1 =>
            if n1 < n then x
            else Impl_Exp_Var newfree
      
      fun out_exp x = 
         case x of
            Impl_Exp_Lam (tp1, (exp2, exp3)) =>
            let
               val exp2 = ExpVar.newvar exp2
               val exp3 = unbind_exp_exp 0 exp2 exp3
            in
               Exp.Lam (tp1, (exp2, exp3))
            end
          | Impl_Exp_App (exp1, exp2) =>
            Exp.App (exp1, exp2)
          | Impl_Exp_TLam (tp1, exp2) =>
            let
               val tp1 = TpVar.newvar tp1
               val exp2 = unbind_tp_exp 0 tp1 exp2
            in
               Exp.TLam (tp1, exp2)
            end
          | Impl_Exp_TApp (exp1, tp2) =>
            Exp.TApp (exp1, tp2)
          | Impl_Exp_Var x1 =>
            Exp.Var x1
          | Impl_Exp_BoundVar n1 =>
            raise Fail "Invariant: exposed bvar"
      
      fun bind_tp_exp n oldfree x = 
         case x of
            Impl_Exp_Lam (tp1, (exp2, exp3)) =>
            let
               val tp1 = bind_tp_tp n oldfree tp1
               val exp3 = bind_tp_exp (n+1) oldfree exp3
            in
               Impl_Exp_Lam (tp1, (exp2, exp3))
            end
          | Impl_Exp_App (exp1, exp2) =>
            let
               val exp1 = bind_tp_exp n oldfree exp1
               val exp2 = bind_tp_exp n oldfree exp2
            in
               Impl_Exp_App (exp1, exp2)
            end
          | Impl_Exp_TLam (tp1, exp2) =>
            let
               val exp2 = bind_tp_exp (n+1) oldfree exp2
            in
               Impl_Exp_TLam (tp1, exp2)
            end
          | Impl_Exp_TApp (exp1, tp2) =>
            let
               val exp1 = bind_tp_exp n oldfree exp1
               val tp2 = bind_tp_tp n oldfree tp2
            in
               Impl_Exp_TApp (exp1, tp2)
            end
          | Impl_Exp_Var x1 =>
            x
          | Impl_Exp_BoundVar n1 =>
            x
      
      fun bind_exp_exp n oldfree x = 
         case x of
            Impl_Exp_Lam (tp1, (exp2, exp3)) =>
            let
               val exp3 = bind_exp_exp (n+1) oldfree exp3
            in
               Impl_Exp_Lam (tp1, (exp2, exp3))
            end
          | Impl_Exp_App (exp1, exp2) =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
               val exp2 = bind_exp_exp n oldfree exp2
            in
               Impl_Exp_App (exp1, exp2)
            end
          | Impl_Exp_TLam (tp1, exp2) =>
            let
               val exp2 = bind_exp_exp (n+1) oldfree exp2
            in
               Impl_Exp_TLam (tp1, exp2)
            end
          | Impl_Exp_TApp (exp1, tp2) =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
            in
               Impl_Exp_TApp (exp1, tp2)
            end
          | Impl_Exp_Var x1 =>
            if ExpVar.equal (oldfree, x1) then Impl_Exp_BoundVar n else x
          | Impl_Exp_BoundVar n1 =>
            x
      
      fun into_exp x = 
         case x of
            Exp.Lam (tp1, (exp2, exp3)) =>
            let
               val exp3 = bind_exp_exp 0 exp2 exp3
               val exp2 = ExpVar.toUserString exp2
            in
               Impl_Exp_Lam (tp1, (exp2, exp3))
            end
          | Exp.App (exp1, exp2) =>
            Impl_Exp_App (exp1, exp2)
          | Exp.TLam (tp1, exp2) =>
            let
               val exp2 = bind_tp_exp 0 tp1 exp2
               val tp1 = TpVar.toUserString tp1
            in
               Impl_Exp_TLam (tp1, exp2)
            end
          | Exp.TApp (exp1, tp2) =>
            Impl_Exp_TApp (exp1, tp2)
          | Exp.Var x1 =>
            Impl_Exp_Var x1
      
      fun aequiv_exp (x, y) = 
         case (x, y) of
            (Impl_Exp_Lam x, Impl_Exp_Lam y) =>
            aequiv_tp (#1 x, #1 y) andalso
            aequiv_exp (#2 (#2 x), #2 (#2 y))
          | (Impl_Exp_App x, Impl_Exp_App y) =>
            aequiv_exp (#1 x, #1 y) andalso
            aequiv_exp (#2 x, #2 y)
          | (Impl_Exp_TLam x, Impl_Exp_TLam y) => aequiv_exp (#2 x, #2 y)
          | (Impl_Exp_TApp x, Impl_Exp_TApp y) =>
            aequiv_exp (#1 x, #1 y) andalso
            aequiv_tp (#2 x, #2 y)
          | (Impl_Exp_BoundVar x, Impl_Exp_BoundVar y) => x = y
          | (Impl_Exp_Var x, Impl_Exp_Var y) => ExpVar.equal (x, y)
          | _ => false
         
      val free_tp_exp = fn _ => raise Fail "Unimpl"
      val free_exp_exp = fn _ => raise Fail "Unimpl"
   end
   
   (* Derived functions *)
   fun subst_tp_exp t x s = 
      case out_exp s of
         Exp.Lam (tp1, (exp2, exp3)) =>
         let
            val tp1 = subst_tp_tp t x tp1
            val exp3 = subst_tp_exp t x exp3
         in
            into_exp (Exp.Lam (tp1, (exp2, exp3)))
         end
       | Exp.App (exp1, exp2) =>
         let
            val exp1 = subst_tp_exp t x exp1
            val exp2 = subst_tp_exp t x exp2
         in
            into_exp (Exp.App (exp1, exp2))
         end
       | Exp.TLam (tp1, exp2) =>
         let
            val exp2 = subst_tp_exp t x exp2
         in
            into_exp (Exp.TLam (tp1, exp2))
         end
       | Exp.TApp (exp1, tp2) =>
         let
            val exp1 = subst_tp_exp t x exp1
            val tp2 = subst_tp_tp t x tp2
         in
            into_exp (Exp.TApp (exp1, tp2))
         end
       | Exp.Var x1 =>
         s
   
   fun subst_exp_exp t x s = 
      case out_exp s of
         Exp.Lam (tp1, (exp2, exp3)) =>
         let
            val exp3 = subst_exp_exp t x exp3
         in
            into_exp (Exp.Lam (tp1, (exp2, exp3)))
         end
       | Exp.App (exp1, exp2) =>
         let
            val exp1 = subst_exp_exp t x exp1
            val exp2 = subst_exp_exp t x exp2
         in
            into_exp (Exp.App (exp1, exp2))
         end
       | Exp.TLam (tp1, exp2) =>
         let
            val exp2 = subst_exp_exp t x exp2
         in
            into_exp (Exp.TLam (tp1, exp2))
         end
       | Exp.TApp (exp1, tp2) =>
         let
            val exp1 = subst_exp_exp t x exp1
         in
            into_exp (Exp.TApp (exp1, tp2))
         end
       | Exp.Var x1 =>
         if ExpVar.equal (x, x1)
         then t else s
   
   fun toString_exp x = 
      case out_exp x of
         Exp.Lam (tp1, (exp2, exp3)) =>
         "Lam("^toString_tp tp1^", "^ExpVar.toString exp2^"."^toString_exp exp3^")"
       | Exp.App (exp1, exp2) =>
         "App("^toString_exp exp1^", "^toString_exp exp2^")"
       | Exp.TLam (tp1, exp2) =>
         "TLam("^TpVar.toString tp1^"."^toString_exp exp2^")"
       | Exp.TApp (exp1, tp2) =>
         "TApp("^toString_exp exp1^", "^toString_tp tp2^")"
       | Exp.Var x1 =>
         ExpVar.toString x1
   
   
   (* Rebind structs with full contents *)
   structure Tp =
   struct
      type t = tp
      type tp = tp
      type tpVar = TpVar.t
      open Tp
      
      fun fmap f_tp x = 
         case x of
            Tp.All (tp1, tp2) =>
            let
               val tp2 = f_tp tp2
            in
               Tp.All (tp1, tp2)
            end
          | Tp.Arr (tp1, tp2) =>
            let
               val tp1 = f_tp tp1
               val tp2 = f_tp tp2
            in
               Tp.Arr (tp1, tp2)
            end
          | Tp.Var x1 =>
            Tp.Var x1
      
      val into = into_tp
      val out = out_tp
      structure Var = TpVar
      val Var' = fn x => into (Var x)
      val aequiv = aequiv_tp
      val toString = toString_tp
      val subst = subst_tp_tp
      val freevars = free_tp_tp
      val All' = fn x => into (All x)
      val Arr' = fn x => into (Arr x)
   end
   
   structure Exp =
   struct
      type t = exp
      type exp = exp
      type expVar = ExpVar.t
      open Exp
      
      fun fmap f_exp x = 
         case x of
            Exp.Lam (tp1, (exp2, exp3)) =>
            let
               val exp3 = f_exp exp3
            in
               Exp.Lam (tp1, (exp2, exp3))
            end
          | Exp.App (exp1, exp2) =>
            let
               val exp1 = f_exp exp1
               val exp2 = f_exp exp2
            in
               Exp.App (exp1, exp2)
            end
          | Exp.TLam (tp1, exp2) =>
            let
               val exp2 = f_exp exp2
            in
               Exp.TLam (tp1, exp2)
            end
          | Exp.TApp (exp1, tp2) =>
            let
               val exp1 = f_exp exp1
            in
               Exp.TApp (exp1, tp2)
            end
          | Exp.Var x1 =>
            Exp.Var x1
      
      val into = into_exp
      val out = out_exp
      structure Var = ExpVar
      val Var' = fn x => into (Var x)
      val aequiv = aequiv_exp
      val toString = toString_exp
      val substTp = subst_tp_exp
      val subst = subst_exp_exp
      val freeTpVars = free_tp_exp
      val freevars = free_exp_exp
      val Lam' = fn x => into (Lam x)
      val App' = fn x => into (App x)
      val TLam' = fn x => into (TLam x)
      val TApp' = fn x => into (TApp x)
   end
   
end
