structure AbstractSML =
struct
  datatype TYPE
    = TypeVar of string
    | Arrow of TYPE * TYPE
    | Prod of TYPE list
    | App of {func : TYPE, arg : TYPE}
    | ModProj of string * TYPE

  type data_cases = (string * TYPE option) list

  datatype EXP
    = ExpVar of string

  datatype SIG
    = SigVar of string
    | SigBody of decl list

  and decl_rhs
    = StructureDecl of SIG
    | DatatypeDecl of data_cases
    | TypeDecl of TYPE option
    | ValDecl of TYPE
    | SharingDecl of TYPE * TYPE

  withtype decl = string * decl_rhs

  datatype STRUCT
    = StructVar of string
    | StructBody of defn list
    | StructApp of string * STRUCT

  and defn_rhs
    = StructureDefn of SIG option * STRUCT
    | DatatypeDefn of data_cases
    | TypeDefn of TYPE
    | ValDefn of TYPE option * EXP
    | FunDefn of (string * TYPE option) list * TYPE option * EXP

  withtype defn = string * defn_rhs

  datatype toplevel_defn_rhs
    = TLSignature of SIG
    | TLStructure of SIG option * STRUCT
    | TLFunctor of string * SIG * SIG option * STRUCT

  type toplevel_defn = string * toplevel_defn_rhs
end
