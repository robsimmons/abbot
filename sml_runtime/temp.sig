signature TEMP = sig
  type t

  (* Creates a new, globally unique temp. *)
  val create : string -> t

  (* Provides the string used to create the temp. *)
  val name : t -> string

  val eq : t * t -> bool
  val compare : t * t -> order
  val hash : t -> word
end
