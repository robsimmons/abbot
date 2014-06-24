structure Emit :> sig
  val emit : AbstractSML.toplevel_defn list -> unit
end = struct
  open Util
  infixr 0 >>
  open AbstractSML

  fun foldlSuper first middle start l =
      let
        fun foldl' acc l =
            case l of
                [] => acc
              | x::xs => foldl' (middle (x, acc)) xs
      in
        case l of
            [] => start
          | x::xs => foldl' (first (x, start)) xs
      end

  datatype indent
    = None
    | Incr
    | Decr

  datatype emittable
    = String of string
    | Newline of indent

  fun type_args_to_string args =
      case args of
          [] => ""
        | [arg] => arg ^ " "
        | _ => "(" ^ String.concatWith ", " args ^ ") "

  fun precedence TYPE =
      case TYPE of
          (TypeVar _ | ModProj _ | Prod [] | Prod [_]) => 0
        | App _ => 1
        | Prod _ => 2
        | Arrow _ => 3

  fun emit_type TYPE acc =
      case TYPE of
          TypeVar name => String name :: acc
        | Arrow (TYPE1, TYPE2) =>
          if precedence TYPE1 > 2
          then
            emit_type TYPE2
              (String ") -> " :: emit_type TYPE1 (String "(" :: acc))
          else
            emit_type TYPE2 (String " -> " :: emit_type TYPE1 acc)
        | Prod TYPES =>
          foldlSuper
            (fn (TYPE, acc) =>
                if precedence TYPE > 1
                then String ")" :: emit_type TYPE (String "(" :: acc)
                else emit_type TYPE acc)
            (fn (TYPE, acc) =>
                if precedence TYPE > 1
                then String ")" :: emit_type TYPE (String " * (" :: acc)
                else emit_type TYPE (String " * " :: acc))
            acc
            TYPES
        | App (args, func) =>
          let
            fun emit_args args acc =
                case args of
                    [] => acc
                  | [arg] =>
                    if precedence arg > 0
                    then String ") " :: emit_type arg (String "(" :: acc)
                    else String " " :: emit_type arg acc
                  | arg::args =>
                    String ") "
                    :: List.foldl
                         (fn (arg, acc) => emit_type arg (String ", " :: acc))
                         (emit_type arg (String "(" :: acc))
                         args
          in
            emit_type func (emit_args args acc)
          end
        | ModProj (mod_name, TYPE) =>
          emit_type TYPE (String (mod_name ^ ".") :: acc)

  fun emit_datatype name args branches acc =
      Newline Decr
      :: foldlSuper
           (fn ((cons_name, type_opt), acc) =>
               case type_opt of
                   NONE => String cons_name :: acc
                 | SOME TYPE =>
                   emit_type TYPE (String (cons_name ^ " of ") :: acc))
           (fn ((cons_name, type_opt), acc) =>
               case type_opt of
                   NONE => String ("| " ^ cons_name) :: Newline None :: acc
                 | SOME TYPE =>
                   emit_type TYPE
                     (String ("| " ^ cons_name ^ " of ") :: Newline None :: acc))
           (String "= "
            :: Newline Incr
            :: String ("datatype " ^ type_args_to_string args ^ name)
            :: acc)
           branches

  fun emit_exp EXP acc =
      case EXP of
          ExpVar name => String name :: acc

  fun emit_decl (name, d) acc =
      case d of
          StructureDecl SIG =>
          emit_sig SIG (String ("structure " ^ name ^ " : ") :: acc)
        | DatatypeDecl (args, branches) =>
          emit_datatype name args branches acc
        | TypeDecl (args, type_opt) =>
          (case type_opt of
               NONE =>
               String ("type " ^ type_args_to_string args ^ name)
               :: acc
             | SOME TYPE =>
               emit_type TYPE
                 (String ("type " ^ type_args_to_string args ^ name ^ " = ")
                  :: acc))
        | ValDecl TYPE =>
          emit_type TYPE (String ("val " ^ name ^ " : ") :: acc)
        | SharingDecl (TYPE1, TYPE2) =>
          emit_type TYPE2
            (String " = " :: emit_type TYPE1 (String "sharing type " :: acc))

  and emit_sig SIG acc =
      case SIG of
          SigVar sig_name =>
          String sig_name :: acc
        | SigBody decls =>
          String "end"
          :: Newline Decr
          :: foldlSuper
               (fn (decl, acc) => emit_decl decl acc)
               (fn (decl, acc) =>
                   emit_decl decl (Newline None :: Newline None :: acc))
               (Newline Incr :: String "sig" :: acc)
               decls

  fun emit_defn (name, d) acc =
      case d of
          StructureDefn (sig_opt, STRUCT) =>
          emit_structure_defn name sig_opt STRUCT acc
        | DatatypeDefn (args, branches) =>
          emit_datatype name args branches acc
        | TypeDefn (args, TYPE) =>
          emit_type TYPE
            (String ("type " ^ type_args_to_string args ^ name ^ " = ")
             :: acc)
        | ValDefn (type_opt, EXP) =>
          (case type_opt of
               NONE => emit_exp EXP (String ("val " ^ name ^ " = ") :: acc)
             | SOME TYPE =>
               emit_exp EXP
                 (String " = "
                  :: emit_type TYPE
                       (String ("val " ^ name ^ " : ") :: acc)))
        | FunDefn (args, type_opt, EXP) => raise Fail "Unimpl???"

  and emit_structure_defn name sig_opt STRUCT acc =
      case sig_opt of
          NONE =>
          emit_struct STRUCT (String ("structure " ^ name ^ " = ") :: acc)
        | SOME SIG =>
          emit_struct STRUCT
            (String " = "
             :: emit_sig SIG
                  (String ("structure " ^ name ^ " :> ") :: acc))

  and emit_struct STRUCT acc =
      let
        fun peel_names STRUCT =
            case STRUCT of
                StructVar struct_name => ([struct_name], NONE)
              | StructBody decls => ([], SOME decls)
              | StructApp (fname, STRUCT') =>
                let val (names, body_opt) = peel_names STRUCT'
                in (fname::names, body_opt)
                end

        val (names, body_opt) = peel_names STRUCT

        val end_text = String.concatWith ")" (List.map (fn _ => "") names)
      in
        case body_opt of
            NONE => String (String.concatWith " (" names ^ end_text) :: acc
          | SOME body =>
            String "end"
            :: Newline Decr
            :: foldlSuper
                 (fn (defn, acc) => emit_defn defn acc)
                 (fn (defn, acc) =>
                     emit_defn defn (Newline None :: Newline None :: acc))
                 (case names of
                    [] => Newline Incr :: String "struct" :: acc
                  | _ =>
                    Newline Incr
                    :: String (String.concatWith " (" names ^ " (struct")
                    :: acc)
                 body
      end

  fun emit_toplevel_defn (name, tld) acc =
      case tld of
          TLSignature SIG =>
          emit_sig SIG (String ("signature " ^ name ^ " = ") :: acc)
        | TLStructure (sig_opt, STRUCT) =>
          emit_structure_defn name sig_opt STRUCT acc
        | TLFunctor (arg_name, arg_sig, sig_opt, STRUCT) =>
          let
            val start_text =
                "functor " ^ name ^ " (" ^ arg_name ^ " : "
            val with_arg =
                String ") " :: emit_sig arg_sig (String start_text :: acc)
          in
            case sig_opt of
                NONE =>
                emit_struct STRUCT (String "= " :: with_arg)
              | SOME SIG =>
                emit_struct STRUCT
                  (String " = "
                   :: emit_sig SIG (String ":> " :: with_arg))
          end

  fun peel_strings e acc =
      case e of
          String s :: e' => peel_strings e' (s :: acc)
        | _ => (acc, e)

  fun flatten e =
      case e of
          [] => ()
        | String s :: e' =>
          let val (ss, e'') = peel_strings e []
          in emit [String.concat (List.rev ss)] >> flatten e''
          end
        | Newline None :: Newline None :: Newline None :: e' =>
          flatten (Newline None :: Newline None :: e')
        | Newline None :: Newline None :: e' =>
          flatten (Newline None :: String "" :: Newline None :: e')
        | Newline None :: e' =>
          flatten e'
        | Newline Incr :: e' =>
          incr () >> flatten e'
        | Newline Decr :: e' =>
          decr () >> flatten e'

  fun emit defns =
      let
        val emittable =
            foldlSuper
              (fn (defn, acc) => emit_toplevel_defn defn acc)
              (fn (defn, acc) =>
                  emit_toplevel_defn defn (Newline None :: Newline None :: acc))
              []
              defns
      in
        flatten (List.rev emittable)
      end
end
