structure SMLSyntax =
struct
  datatype TYPE
    = TypeVar of string
    | Arrow of TYPE * TYPE
    | Prod of TYPE list
    | App of TYPE list * TYPE
    | ModProj of string * TYPE

  type data_cases = (string * TYPE option) list

  datatype SIG
    = SigVar of string
    | SigBody of decl list
    | WhereType of SIG * TYPE * TYPE

  and decl
    = BlankDecl
    | StructureDecl of string * SIG
    | TypeDecls of
      {datatypes : (string * string list * data_cases) list,
       aliases : (string * string list * TYPE option) list}
    | ValDecl of string * TYPE
    | SharingDecl of TYPE * TYPE

  datatype PAT
    = Wild
    | VarPat of string
    | TuplePat of PAT list
    | InjPat of string * PAT
    | ListPat of PAT list
    | AscribedPat of PAT * TYPE
    | ConsPat of PAT * PAT

  datatype EXP
    = ExpVar of string
    | TupleExp of EXP list
    | CaseExp of EXP * (PAT * EXP) list
    | SeqExp of EXP list
    | StringExp of string
    | ListExp of EXP list
    | LetExp of defn list * EXP
    | LamExp of (PAT * EXP) list

  and STRUCT
    = StructVar of string
    | StructBody of defn list
    | StructApp of string * STRUCT

  and defn
    = BlankDefn
    | StructureDefn of string * SIG option * STRUCT
    | TypeDefns of
      {datatypes : (string * string list * data_cases) list,
       aliases : (string * string list * TYPE) list}
    | ValDefn of PAT * EXP
    | FunDefn of (string * PAT list * TYPE option * EXP) list
    | OpenDefn of STRUCT

  datatype toplevel_defn
    = TLSignature of string * SIG
    | TLStructure of string * SIG option * STRUCT
    | TLFunctor of string * decl list * SIG option * STRUCT
end
