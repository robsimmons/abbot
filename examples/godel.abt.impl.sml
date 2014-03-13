structure AbbotImpl = 
struct
   (* All symbols *)
   datatype 'a maybe_symbol
    = bound_symbol of IntInf.int 
    | free_symbol of 'a
   
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
   
   (* Implementation of recursive block: tp *)
   
   structure Tp =
   struct
      datatype 'tp tpView
       = Nat
       | Arr of 'tp * 'tp
      
      val fmap = fn _ => raise Fail "Unimpl"
   end
   
   (* Naive and minimal implementation *)
   local
      datatype tp
       = Impl_Tp_Nat
       | Impl_Tp_Arr of tp * tp
      
   in
      type tp = tp
      
      fun out_tp x = 
         case x of
            Impl_Tp_Nat =>
            Tp.Nat
          | Impl_Tp_Arr (tp1, tp2) =>
            Tp.Arr (tp1, tp2)
      
      fun into_tp x = 
         case x of
            Tp.Nat =>
            Impl_Tp_Nat
          | Tp.Arr (tp1, tp2) =>
            Impl_Tp_Arr (tp1, tp2)
      
      fun aequiv_tp (x, y) = 
         case (x, y) of
            (Impl_Tp_Nat, Impl_Tp_Nat) => true
          | (Impl_Tp_Arr x, Impl_Tp_Arr y) =>
            aequiv_tp (#1 x, #1 y) andalso
            aequiv_tp (#2 x, #2 y)
          | _ => false
         
   end
   
   (* Derived functions *)
   fun toString_tp x = 
      case out_tp x of
         Tp.Nat =>
         "Nat"
       | Tp.Arr (tp1, tp2) =>
         "Arr("^toString_tp tp1^", "^toString_tp tp2^")"
   
   
   (* Implementation of recursive block: exp *)
   
   structure Exp =
   struct
      datatype 'exp expView
       = Var of ExpVar.t
       | Z
       | S of 'exp
       | Rec of 'exp * 'exp * (ExpVar.t * ExpVar.t * 'exp)
       | Lam of tp * (ExpVar.t * 'exp)
       | Ap of 'exp * 'exp
      
      val fmap = fn _ => raise Fail "Unimpl"
   end
   
   (* Naive and minimal implementation *)
   local
      datatype exp
       = Impl_Exp_BoundVar of IntInf.int
       | Impl_Exp_Var of ExpVar.t
       | Impl_Exp_Z
       | Impl_Exp_S of exp
       | Impl_Exp_Rec of exp * exp * (string * string * exp)
       | Impl_Exp_Lam of tp * (string * exp)
       | Impl_Exp_Ap of exp * exp
      
   in
      type exp = exp
      
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
          | Impl_Exp_Rec (exp1, exp2, (exp3, exp4, exp5)) =>
            let
               val exp1 = unbind_exp_exp n newfree exp1
               val exp2 = unbind_exp_exp n newfree exp2
               val exp5 = unbind_exp_exp (n+2) newfree exp5
            in
               Impl_Exp_Rec (exp1, exp2, (exp3, exp4, exp5))
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
          | Impl_Exp_Var x1 =>
            x
          | Impl_Exp_BoundVar n1 =>
            if n1 < n then x
            else Impl_Exp_Var newfree
      
      fun out_exp x = 
         case x of
            Impl_Exp_Z =>
            Exp.Z
          | Impl_Exp_S exp1 =>
            Exp.S exp1
          | Impl_Exp_Rec (exp1, exp2, (exp3, exp4, exp5)) =>
            let
               val exp3 = ExpVar.newvar exp3
               val exp5 = unbind_exp_exp 1 exp3 exp5
               val exp4 = ExpVar.newvar exp4
               val exp5 = unbind_exp_exp 0 exp4 exp5
            in
               Exp.Rec (exp1, exp2, (exp3, exp4, exp5))
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
          | Impl_Exp_Var x1 =>
            Exp.Var x1
          | Impl_Exp_BoundVar n1 =>
            raise Fail "Invariant: exposed bvar"
      
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
          | Impl_Exp_Rec (exp1, exp2, (exp3, exp4, exp5)) =>
            let
               val exp1 = bind_exp_exp n oldfree exp1
               val exp2 = bind_exp_exp n oldfree exp2
               val exp5 = bind_exp_exp (n+2) oldfree exp5
            in
               Impl_Exp_Rec (exp1, exp2, (exp3, exp4, exp5))
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
          | Impl_Exp_Var x1 =>
            if ExpVar.equal (oldfree, x1) then Impl_Exp_BoundVar n else x
          | Impl_Exp_BoundVar n1 =>
            x
      
      fun into_exp x = 
         case x of
            Exp.Z =>
            Impl_Exp_Z
          | Exp.S exp1 =>
            Impl_Exp_S exp1
          | Exp.Rec (exp1, exp2, (exp3, exp4, exp5)) =>
            let
               val exp5 = bind_exp_exp 1 exp3 exp5
               val exp3 = ExpVar.toUserString exp3
               val exp5 = bind_exp_exp 0 exp4 exp5
               val exp4 = ExpVar.toUserString exp4
            in
               Impl_Exp_Rec (exp1, exp2, (exp3, exp4, exp5))
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
          | Exp.Var x1 =>
            Impl_Exp_Var x1
      
      fun aequiv_exp (x, y) = 
         case (x, y) of
            (Impl_Exp_Z, Impl_Exp_Z) => true
          | (Impl_Exp_S x, Impl_Exp_S y) => aequiv_exp (x, y)
          | (Impl_Exp_Rec x, Impl_Exp_Rec y) =>
            aequiv_exp (#1 x, #1 y) andalso
            aequiv_exp (#2 x, #2 y) andalso
            aequiv_exp (#3 (#3 x), #3 (#3 y))
          | (Impl_Exp_Lam x, Impl_Exp_Lam y) =>
            aequiv_tp (#1 x, #1 y) andalso
            aequiv_exp (#2 (#2 x), #2 (#2 y))
          | (Impl_Exp_Ap x, Impl_Exp_Ap y) =>
            aequiv_exp (#1 x, #1 y) andalso
            aequiv_exp (#2 x, #2 y)
          | (Impl_Exp_BoundVar x, Impl_Exp_BoundVar y) => x = y
          | (Impl_Exp_Var x, Impl_Exp_Var y) => ExpVar.equal (x, y)
          | _ => false
         
      val free_exp_exp = fn _ => raise Fail "Unimpl"
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
       | Exp.Rec (exp1, exp2, (exp3, exp4, exp5)) =>
         let
            val exp1 = subst_exp_exp t x exp1
            val exp2 = subst_exp_exp t x exp2
            val exp5 = subst_exp_exp t x exp5
         in
            into_exp (Exp.Rec (exp1, exp2, (exp3, exp4, exp5)))
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
       | Exp.Var x1 =>
         if ExpVar.equal (x, x1)
         then t else s
   
   fun toString_exp x = 
      case out_exp x of
         Exp.Z =>
         "Z"
       | Exp.S exp1 =>
         "S("^toString_exp exp1^")"
       | Exp.Rec (exp1, exp2, (exp3, exp4, exp5)) =>
         "Rec("^toString_exp exp1^", "^toString_exp exp2^", "^ExpVar.toString exp3^"."^ExpVar.toString exp4^"."^toString_exp exp5^")"
       | Exp.Lam (tp1, (exp2, exp3)) =>
         "Lam("^toString_tp tp1^", "^ExpVar.toString exp2^"."^toString_exp exp3^")"
       | Exp.Ap (exp1, exp2) =>
         "Ap("^toString_exp exp1^", "^toString_exp exp2^")"
       | Exp.Var x1 =>
         ExpVar.toString x1
   
   
   (* Rebind structs with full contents *)
   structure Tp =
   struct
      type t = tp
      type tp = tp
      open Tp
      val into = into_tp
      val out = out_tp
      val aequiv = aequiv_tp
      val toString = toString_tp
      val Nat' = into Tp.Nat
      val Arr' = fn x => into (Arr x)
   end
   
   structure Exp =
   struct
      type t = exp
      type exp = exp
      type expVar = ExpVar.t
      open Exp
      val into = into_exp
      val out = out_exp
      structure Var = ExpVar
      val Var' = fn x => into (Var x)
      val aequiv = aequiv_exp
      val toString = toString_exp
      val subst = subst_exp_exp
      val freevars = free_exp_exp
      val Z' = into Exp.Z
      val S' = fn x => into (S x)
      val Rec' = fn x => into (Rec x)
      val Lam' = fn x => into (Lam x)
      val Ap' = fn x => into (Ap x)
   end
   
end
