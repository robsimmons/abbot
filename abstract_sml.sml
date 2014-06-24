structure AbstractSML =
struct
  datatype TYPE
    = TypeVar of string
    | Arrow of TYPE * TYPE
    | Prod of TYPE list
    | App of TYPE list * TYPE
    | ModProj of string * TYPE

  type data_cases = (string * TYPE option) list

  datatype EXP
    = ExpVar of string

  datatype SIG
    = SigVar of string
    | SigBody of decl list
    | WhereType of SIG * TYPE * TYPE

  and decl_rhs
    = StructureDecl of SIG
    | DatatypeDecl of string list * data_cases
    | TypeDecl of string list * TYPE option
    | ValDecl of TYPE
    | SharingDecl of TYPE * TYPE

  withtype decl = string * decl_rhs

  datatype STRUCT
    = StructVar of string
    | StructBody of defn list
    | StructApp of string * STRUCT

  and defn_rhs
    = StructureDefn of SIG option * STRUCT
    | DatatypeDefn of string list * data_cases
    | TypeDefn of string list * TYPE
    | ValDefn of TYPE option * EXP
    | FunDefn of (string * TYPE option) list * TYPE option * EXP

  withtype defn = string * defn_rhs

  datatype toplevel_defn_rhs
    = TLSignature of SIG
    | TLStructure of SIG option * STRUCT
    | TLFunctor of string * SIG * SIG option * STRUCT

  type toplevel_defn = string * toplevel_defn_rhs
end
