structure StudentTestSuite =
struct

  (* * * Result * * *)
  (* A result specifies the output produced by the run of a function: a value
   * or a raised exception. *)
  structure Result =
  struct

    datatype 'a result = Exn of exn
                       | Value of 'a

    fun compare cmp (x, y) =
      case (x, y) of
        (Exn x', Exn y') => exnName x' = exnName y'
      | (Value x', Value y') => cmp (x', y')
      | _ => false

    fun toStr aToStr r =
      case r of
        Exn e => "Exn " ^ exnName e
      | Value a => aToStr a

    fun run (f : 'a -> 'b) (input : 'a) : 'b result =
      Value (f input)
        handle e => Exn e

  end


  (* * * Checkers * * *)
  (* A checker is essentially a function to test, f, along with a function,
   * ver, which checks whether the given output is correct with regards to
   * the given input.
   *
   * We can generalize testing against fixed output, or a reference solution
   * to tetsing against a checker. *)
  structure Checker =
  struct

    type ('a, 'b) checker = ('a -> 'b) * (('a * 'b Result.result) -> bool)

    datatype ('a, 'b) correctness = Correct
                         | Incorrect of ('a * 'b)

    fun fromRefsol (f, fRef, cmp) : ('a, 'b) checker =
      let
        fun ver (input, result) =
          Result.compare cmp (result, Result.run fRef input)
      in
        (f, ver)
      end

    fun fromOutput (f, cmp) : (('a * 'b Result.result), 'b) checker =
      let
        fun f' (input, _) =
          f input
        fun ver ((input, desired), result) =
          Result.compare cmp (result, desired)
      in
        (f', ver)
      end

    fun fromVerifier (f, ver) : ('a,'b) checker = (f, ver)

    fun check (f, ver) input =
      let
        val got = Result.run f input
      in
        if ver (input, got) then Correct else Incorrect (input, got)
      end

  end


  (* * * Loggers * * *)
  structure Logger =
  struct
    
    type ('a,'b) logger = ('a -> string) * ('b -> string)

    fun log (iToS, oToS) correctness =
      case correctness of
        Checker.Correct => print "Test passed.\n"
      | Checker.Incorrect (inp, out) =>
          print ("Test failed on input " ^ iToS inp ^ "; got " ^
                 Result.toStr oToS out ^ ".\n")

    fun create (iToS : 'a -> string, oToS : 'b -> string) : ('a, 'b) logger =
      (iToS, oToS)

  end


  (* * * Tester * * *)
  structure Tester =
  struct

    fun test checker logger input =
      let
        val _ = Logger.log logger (Checker.check checker input)
      in
        ()
      end

    fun testGroup checker logger inputList =
      let
        val _ = List.map (test checker logger) inputList
      in
        ()
      end

  end

end
