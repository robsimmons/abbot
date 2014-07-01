signature PRIMITIVES =
sig
  val par  : (unit -> 'a) * (unit -> 'b) -> ('a * 'b)
  val par3 : (unit -> 'a) * (unit -> 'b) * (unit -> 'c) -> ('a * 'b * 'c)
  val parTab : int * (int -> 'a) -> (int -> 'a)
end
