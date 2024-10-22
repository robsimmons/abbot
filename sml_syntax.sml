structure SmlSyntax =
struct

  datatype BASETYPE 
    = Str 
    | Bool
    | Int 
    | Char
    
  datatype TYPE
    = TypeVar of string
    | ArrowType of TYPE * TYPE
    | ProdType of TYPE list
    | AppType of TYPE list * TYPE
    | ModProjType of STRUCT * string
    | BaseType of BASETYPE

  and SIG
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

  and PAT
    = Wild
    | VarPat of string
    | TuplePat of PAT list
    | InjPat of string * PAT
    | ListPat of PAT list
    | AscribedPat of PAT * TYPE
    | ConsPat of PAT * PAT

  and EXP
    = ExpVar of string
    | TupleExp of EXP list
    | CaseExp of EXP * (PAT * EXP) list
    | SeqExp of EXP list
    | IntExp of int
    | StringExp of string
    | ListExp of EXP list
    | LetExp of defn list * EXP
    | LamExp of (PAT * EXP) list
    | IfExp of EXP * EXP * EXP
    | BoolAnd

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
    | FunDefns of (string * PAT list * TYPE option * EXP) list
    | OpenDefn of STRUCT
    | DatatypeCopy of string * TYPE

  withtype data_cases = (string * TYPE option) list

  datatype toplevel_defn
    = TLSignature of string * SIG
    | TLStructure of string * SIG option * STRUCT
    | TLFunctor of string * decl list * SIG option * STRUCT
end
