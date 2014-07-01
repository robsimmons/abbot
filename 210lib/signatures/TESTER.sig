signature TESTER =
sig
  exception FailInputOutputFileFormat

  (* testFromRef: tests a function, f, from a reference solution on a given set of test cases
   * testFromRef then runs each case with both functions then uses the comparison function given
   * to determine if the solutions are equivalent. If the comparison function returns true the
   * tester will add (NONE, "test passed") to the list of results otherwise it will add the expected
   * output and a string indictating what was returned and what should be returned.
   *)
  val testFromRef:    ('a -> string)      (* input to string *)
                   -> ('b -> string)      (* output to string *)
                   -> ('b * 'b -> bool)   (* compare outputs *)
                   -> ('a -> 'b)          (* function to test *)
                   -> ('a -> 'b)          (* reference solution *)
                   -> 'a list             (* test cases *)
                   -> (('b option * string) list)


  (* Calls testFromRef after loading the file name if there is a problem
   * with the formating of the file FailInputOutputFileFormat will be raised
   *)
  val testFromRefFile :    ('a -> string) * (string -> 'a option)  (* input to string / from string *)
                        -> ('b -> string)                   (* output to string *)
                        -> ('b * 'b -> bool)                (* compare outputs *)
                        -> ('a -> 'b)                       (* function to test *)
                        -> ('a -> 'b)                       (* reference solution *)
                        -> string                           (* file name *)
                        -> ('b option * string) list

  (* testFromOutput: tests a function, f, from a given set of test cases and their expected solutions
   * testFromRef then runs each case with both functions then uses the comparison function given
   * to determine if the solution is equivalent to the expected output. If the comparison function
   * returns true the tester will add (NONE, "test passed") to the list of results otherwise it
   * will add the expected output and a string indictating what was returned and what should be
   * returned.
   *)
  val testFromOutput:    ('a -> string)                   (* input to string *)
                      -> ('b -> string)                   (* output to string *)
                      -> ('b * 'b -> bool)                (* compare outputs *)
                      -> ('a -> 'b)                       (* function to test *)
                      -> ('a * 'b) list                   (* test cases / expected outputs *)
                      -> (('b option * string) list)


  (* Calls testFromOutput after loading the file names if there is a problem
   * with the formating of the file FailInputOutputFileFormat will be raised
   *)
  val testFromOutputFile :    ('a -> string) * (string -> 'a option) (* input to string / from string *)
                           -> ('b -> string) * (string -> 'b option) (* output to string / from string *)
                           -> ('b * 'b -> bool)               (* compare outputs *)
                           -> ('a -> 'b)                      (* function to test *)
                           -> string * string                 (* inputs file name / outputs file name *)
                           -> ('b option * string) list
end
