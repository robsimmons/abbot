signature ANALYSIS = sig
  val sorts : Syntax.oper list StringTable.table
  val symbs : string list
  val issrt : string -> bool
  val issym : string -> bool
  val binds : string -> string -> bool
  val varin : string -> string list
  val symin : string -> string list
  val mutual : string -> string list
  val mutualwith : string -> string -> bool
end
