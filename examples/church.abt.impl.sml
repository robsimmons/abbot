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
   
   (* Implementation of recursive block: exp *)
   
   structure Exp =
   struct
      datatype 'exp expView
       = Var of ExpVar.t
       | Lam
       | Ap of 'exp * 'exp
   end
   
   (* Naive and minimal implementation *)
   local
      datatype exp
       = Impl_Exp_BoundVar of IntInf.int
       | Impl_Exp_Var of ExpVar.t
       | Impl_Exp_Lam
       | Impl_Exp_Ap of exp * exp
      
   in
      type exp = exp
      
      fun unbind_exp_exp n newfree x = 
         case x of
            Impl_Exp_Lam =>
            Impl_Exp_Lam
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
            Impl_Exp_Lam =>
            Exp.Lam
          | Impl_Exp_Ap (exp1, exp2) =>
            Exp.Ap (exp1, exp2)
          | Impl_Exp_Var x1 =>
            Exp.Var x1
          | Impl_Exp_BoundVar n1 =>
            raise Fail "Invariant: exposed bvar"
      
      fun bind_exp_exp n oldfree x = 
         case x of
            Impl_Exp_Lam =>
            Impl_Exp_Lam
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
            Exp.Lam =>
            Impl_Exp_Lam
          | Exp.Ap (exp1, exp2) =>
            Impl_Exp_Ap (exp1, exp2)
          | Exp.Var x1 =>
            Impl_Exp_Var x1
      
      fun aequiv_exp (x, y) = 
         case (x, y) of
            (Impl_Exp_Lam, Impl_Exp_Lam) => true
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
         Exp.Lam =>
         into_exp (Exp.Lam)
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
         Exp.Lam =>
         "Lam"
       | Exp.Ap (exp1, exp2) =>
         "Ap("^toString_exp exp1^", "^toString_exp exp2^")"
       | Exp.Var x1 =>
         ExpVar.toString x1
   
   
   (* Rebind structs with full contents *)
   structure Exp =
   struct
      type t = exp
      type exp = exp
      type expVar = ExpVar.t
      open Exp
      
      fun fmap f_exp x = 
         case x of
            Exp.Lam =>
            Exp.Lam
          | Exp.Ap (exp1, exp2) =>
            let
               val exp1 = f_exp exp1
               val exp2 = f_exp exp2
            in
               Exp.Ap (exp1, exp2)
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
      val Lam' = into Exp.Lam
      val Ap' = fn x => into (Ap x)
   end
   
end
