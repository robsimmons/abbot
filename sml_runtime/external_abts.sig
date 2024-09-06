signature EXTERNAL_ABT_0 = sig
    type t

    val apply_renaming : Renaming.t -> 'acc -> t -> 'acc * t
    val subst : 'subst -> t -> t
end

signature EXTERNAL_ABT_1 = sig
    type 'a t

    val apply_renaming
        : (Renaming.t -> 'acc -> 'a1 -> 'acc * 'a2) -> Renaming.t -> 'acc -> 'a1 t -> 'acc * 'a2 t

    val subst : ('subst -> 'a -> 'a) -> 'subst -> 'a t -> 'a t
end

signature EXTERNAL_ABTS = sig
    structure Unit : EXTERNAL_ABT_0 where type t = unit
    structure Bool : EXTERNAL_ABT_0 where type t = bool
    structure Int : EXTERNAL_ABT_0 where type t = int
    structure Char : EXTERNAL_ABT_0 where type t = char
    structure String : EXTERNAL_ABT_0 where type t = string

    structure Option : EXTERNAL_ABT_1 where type 'a t = 'a option
    structure List : EXTERNAL_ABT_1 where type 'a t = 'a list
end
