Abbot
=====

Abbot is a tool for the automatic generation of implementations for abstract binding trees with the locally nameless representation. Abstract syntax trees are quite natural to express as Standard ML datatypes, but the abstract binding trees described in Harper's _Practical Foundations of Programming Languages_ are trickier due to the necessity of alpha-equivalence and avoiding variable capture.

A reasonable implementation strategy for abstract binding trees keeps ABTs as an abstract type; whenever a bound variable is exposed, it is given a globally fresh name that ensures its uniqueness. Such an implementation avoids many potential errors that can happen because of shadowing. However, implementing this interface for each language that we might be interested in would be tedious and error-prone in the extreme.

ABTs as a library
-----------------

One solution, which has been used successfully for large projects like Tom Murphy's ML5/pgh compiler, is to implement a library for ABTs, a functor parameterized by a set of _operators_. An ABT in the library implementation is either:

```
A variable 
  - view: ` x
  - constructor: `` x
  
An abstract binding site
  - view: \ (x,t)
  - constructor: \\ (x,t)
  
An operator and a list of sub-abts
  - view: oper $ [t1,...,tn]
  - constructor: oper $$ [t1,...,tn]
```

Each operator has an arity, which determines both the number of subexpressions and the location of abstract binding sites. In the untyped lambda calculus, there is one operator `Lam` with one subexpression that binds one variable, and another `Ap` with two subexpressions that bind no variables. Small-step evaluation for the untyped lambda calculus looks like this:

```
fun trystep exp = 
   (case out exp of 
       ` x => raise Malformed
     | \ (x, exp) => raise Malformed
     | Lam $ [exp'] => VAL
     | Ap $ [exp1, exp2] =>
       (case trystep exp1 of 
           STEPS exp1' => STEPS (Ap $$ [exp1', exp2])
         | VAL =>
           (case trystep exp2 of 
               STEPS exp2' => STEPS (Ap $$ [exp1, exp2'])
             | VAL => 
               (case out exp1 of 
                   Lam $ [exp1'] => 
                   (case out exp1' of
                       \ (x, exp0) => subst exp2 x exp0
                     | _ => raise Malformed) 
                 | _ => raise Malformed))))
```

ABTs with Abbot
---------------

Abbot takes a code generation approach to ABT specification. Instead of the operators and the corresponding information about their arities being passed to a functor, we can specify 

```
abt exp = Lam (exp.exp) | Ap (exp, exp)
```

Abbot takes this specification and compiles it into Standard ML signature specific to that abstract binding tree spec:

```
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
   datatype 'exp expView
    = Var of Exp.Var.t
    | Lam
    | Ap of 'exp * 'exp  
   
   val Var' : expVar -> exp
   val Lam': exp
   val Ap': exp * exp -> exp
   
   val into:  exp expView -> exp
   val out: exp -> exp expView
   val aequiv: exp * exp -> bool
   val toString: exp -> string
   val subst: exp -> expVar -> exp -> exp
end
structure Exp: EXP
```

Code using Abbot-generated signatures looks about the same, but makes better use of Standard ML's type system to ensure correctness; instead of using operators and the infixed `$` constructor, our views are normal-looking SML datatypes. 

One significant difference from using Abbot is that binding sites are now automatically exposed along with the constructor they are attached to. This makes the reduction step in our example a little more concise.

```
fun trystep exp = 
   (case out exp of 
       Var _ => raise Malformed
     | Lam (x, exp') => VAL
     | Ap (exp1, exp2) =>
       (case trystep exp1 of 
           STEPS exp1' => STEPS (Ap' (exp1', exp2))
         | VAL =>
           (case trystep exp2 of 
               STEPS exp2' => STEPS (Ap' (exp1, exp2'))
             | VAL => 
               (case out exp1 of 
                   Lam (x, exp0) => subst exp2 x exp0
                 | _ => raise Malformed))))
```

The pretty concrete syntax for Abbot isn't connected to a frontend yet; the SML representation of a few datatypes is in analysis.sml, and the output of Abbot can be seen in the examples directory.
