open! Core

type t

val apply : t -> Internal_var.t -> Internal_var.t

val bind : Temp.t -> t
val bind' : Temp.t list -> t

val unbind : t -> Temp.t -> t
val unbind' : t -> Temp.t list -> t

val ident : t

val compose : t -> t -> t
