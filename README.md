abbot
=====

Abbot is a tool for the automatic generation of implementations for abstract binding trees with the locally nameless representation. Abstract syntax trees are quite natural to express as Standard ML datatypes, but the abstract binding trees described in Harper's _Practical Foundations of Programming Languages_ are tricker due to the necessity of alpha-equivalence and avoiding variable capture.

A reasonable implementation strategy for abstract binding trees keeps ABTs as an abstract type; whenever a bound variable is exposed, it is given a globally fresh name that ensures its uniqueness. Such an implementation avoids many potential errors that can happen because of shadowing. However, implementing this interface for each language that we might be interested in would be tedious and error-prone in the extreme.

One solution, which has been used successfully for large projects like Tom Murphy's ML5/pgh compiler, is to implement a library for ABTs, a functor parameterized by a set of _operators_. An ABT is either a variable (constructor ``x`, destructor ``x). 

```
fun trystep exp = 
   case out exp of 
      Lam $ [exp'] => VAL
    | Ap $ [exp1, exp2] =>
      (case trystep exp1 of 
          STEPS exp1' => STEPS (Ap' $$ [exp1', exp2])
        | VAL =>
          (case trystep exp2 of 
              STEPS exp2' => STEPS (Ap' $$ [exp1', exp2])
            | VAL => 
              (case out exp1 of 
                  Lam $ [exp1'] => 
                  (case out exp1' of
                      \ (x, exp0) => 
                    | _ => raise Malformed) 
                | _ => raise Malformed)))
```

Lam $ [exp1'] => 

(case out exp1' of

Lam $ [exp1'] => 

(case out exp1 of 

VAL => 

(case trystep exp2 of 
      (case out 
```
