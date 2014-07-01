structure AbstractSML =
struct
  datatype TYPE
    = TypeVar of string
    | Arrow of TYPE * TYPE
    | Prod of TYPE list
    | App of TYPE list * TYPE
    | ModProj of string * TYPE

  type data_cases = (string * TYPE option) list

  datatype PAT
    = Wild
    | VarPat of string
    | TuplePat of PAT list
    | InjPat of string * PAT

  datatype EXP
    = ExpVar of string
    | TupleExp of EXP list
    | CaseExp of EXP * (PAT * EXP) list
    | SeqExp of EXP list

  datatype SIG
    = SigVar of string
    | SigBody of decl list
    | WhereType of SIG * TYPE * TYPE

  and decl
    = BlankDecl
    | StructureDecl of string * SIG
    | DatatypeDecl of string * string list * data_cases
    | TypeDecl of string * string list * TYPE option
    | ValDecl of string * TYPE
    | SharingDecl of TYPE * TYPE

  datatype STRUCT
    = StructVar of string
    | StructBody of defn list
    | StructApp of string * STRUCT

  and defn
    = BlankDefn
    | StructureDefn of string * SIG option * STRUCT
    | DatatypeDefn of string * string list * data_cases
    | TypeDefn of string * string list * TYPE
    | ValDefn of PAT * EXP
    | FunDefn of string * PAT list * TYPE option * EXP

  datatype toplevel_defn
    = TLSignature of string * SIG
    | TLStructure of string * SIG option * STRUCT
    | TLFunctor of string * string * SIG * SIG option * STRUCT
end
