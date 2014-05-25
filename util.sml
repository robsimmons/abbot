(* Generally useful utilities, primarily used for emitting code *)

signature UTIL =
sig
    datatype ('a, 'b) sum = L of 'a | R of 'b

    (* Stateful; set or unset the indent *)
    val emit: string list -> unit
    val incr: unit -> unit
    val decr: unit -> unit
    val flush: unit -> unit

    (* Write: output to a particular stream *)
    val write: TextIO.outstream -> (unit -> unit) -> unit

    (* Annotate a listwith ints *)
    val mapi: (int * 'a -> 'b) -> 'a list -> 'b list
    val intify: 'a list -> (int * 'a) list

    (* Application utility functions *)
    val transSuper: (* Analogy: String.translate *)
        (unit -> 'c list)                             (* There are no items *)
        -> ('a -> 'c list)                            (* There is one item *)
        -> ('a -> 'c list) * ('a -> 'c list) * ('a -> 'c list) (* F,M,L *)
        -> 'a list                                    (* List *)
        -> 'c list

    val appSuper:
        (unit -> unit)                                (* There are no items *)
        -> ('a -> unit)                               (* There is one item *)
        -> ('a -> unit) * ('a -> unit) * ('a -> unit) (* First, middle, last *)
        -> 'a list                                    (* List *)
        -> unit

    val transFirst:
        (unit -> 'c list)
        -> ('pre * 'a -> 'c list)
        -> ('pre * 'pre)
        -> 'a list
        -> 'c list

    val appFirst:
        (unit -> unit)       (* Function if there are no items *)
        -> ('a * 'b -> unit) (* Function for each item *)
        -> ('a * 'a)         (* Data for first item, data for other items *)
        -> 'b list           (* List of items *)
        -> unit
end

structure Util:> UTIL =
struct

datatype ('a, 'b) sum = L of 'a | R of 'b

fun mapi' f n [] alloc = rev alloc
  | mapi' f n (x :: xs) alloc = mapi' f (n+1) xs (f (n, x) :: alloc)

fun mapi f xs = mapi' f 0 xs []

fun intify xs = mapi (fn x => x) xs

fun transSuper none one (first, middle, last) xs =
    let
        fun loop [ x ] accum = List.concat (rev (last x :: accum))
          | loop (x :: xs) accum = loop xs (middle x :: accum)
    in case xs of
           [] => none ()
         | [ x ] => one x
         | x :: xs => loop xs [first x]
    end

fun appSuper none one (first: 'a -> unit, middle: 'a -> unit, last) xs: unit =
    let
        (*[ val loop: ('a conslist) -> unit ]*)
        fun loop [ x ] = last x
          | loop (x :: (xs as _ :: _)) = (middle x; loop xs)
    in case xs of
           [] => none ()
         | [ x ] => one x
         | x :: (xs as _ :: _) => (first x; loop xs)
    end

fun transFirst none some (first, rest) =
    let
        fun first' x = some (first, x)
        fun rest' x = some (rest, x)
    in
        transSuper none first' (first', rest', rest')
    end

fun appFirst none some (first, rest) =
    let
        fun first' x = some (first, x)
        fun rest' x = some (rest, x)
    in
        appSuper none first' (first', rest', rest')
    end


local
    val outstream: TextIO.outstream option ref =
        (ref NONE (*[ <: TextIO.outstream option ref ]*))
    val ind = ref ""
in
fun emit1 s =
    let val s' = !ind ^ s ^ "\n"
    in case !outstream of
           NONE => print s'
         | SOME stream => TextIO.output (stream, s')
    end

val emit = app emit1

fun flush () =
    case !outstream of
        NONE => TextIO.flushOut TextIO.stdOut
      | SOME s => TextIO.flushOut s

fun incr () = ind := !ind ^ "   "

fun decr () =
    case !ind of
        "" => raise Fail "Unbalanced increment/decrement"
      | s => ind := String.extract (!ind, 3, NONE)

fun write stream (f: unit -> unit) =
    case !outstream of
        NONE =>
        let in
            ( outstream := SOME stream
            ; f ()
            ; outstream := NONE)
            handle exn => (outstream := NONE; raise exn)
        end
      | SOME _ => raise Fail "Nested calls to write"
end

end
