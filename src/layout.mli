open! Core

(** A [Layout.t] is an abstract representation of how to lay out some code. It is designed to
    encourage the user to a limited set of well-structured, nice-looking choices.

    The primary guiding principle is that one should never add line breaks to a syntactic node
    without also splitting all syntatic nodes that contain it. *)
type t

(** [atom ?magnet_left ?magnet_right string] creates an atomic [t], which is layed out as [string]
    and can never be split.

    [string] should not contain line breaks. If it does [to_string] will likely behave badly.

    [magnet_left] and [magnet_right] default to [false], and can be set to true to cause this atom
    to be placed right next to the atom to its left or right (respectively) when it is on the same
    line as that atom. This is useful for things like parentheses, which can be distinguished from
    the atom they are next to without whitespace. *)
val atom
  :  ?magnet_left:bool
  -> ?magnet_right:bool
  -> string
  -> t

module Indentation : sig
  type t =
    | Indent
    | No_indent
end

(** [list elts] creates a [t] that place all of [elts] on a single line if there is enough space,
    and will otherwise place each on separate lines. In the case where the [elts] are placed on
    separate lines, they will be indented according to the provided indentation.

    Raises if [elts] is empty. *)
val list : (Indentation.t * t) list -> t

(** [always_split_list elts] is like [list elts], except that it always puts things on separate
    lines. This will necessarily cause any outer list to be split as well.

    Raises if [elts] is empty. *)
val always_split_list : (Indentation.t * t) list -> t

(** [if_fits_on_line ~then_ ~else_] behaves like [then_] if [then_] fits on a single line, and
    [else_] otherwise. This is for the rare cases where the actual set of tokens you want to emit
    depends on the layout. *)
val if_fits_on_line : then_:t -> else_:t -> t

(** [to_string config t ~max_line_length] converts a [t] to a string, attempting to limit line
    lengths to less than [max_line_length].

    Note that it is possible to exceed [max_line_length] if splitting the string maximally and
    respecting indentation still results lines that are too wide. For example, if there is a single
    atom that is longer than [max_line_length], this will occur. *)
val to_string
  :  ?spaces_to_indent:int (* defaults to [2]. *)
  -> t
  -> max_line_length:int
  -> string
