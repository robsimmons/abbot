%{
  open Core
  open Parse_tree
%}

%type <Parse_tree.Defn.t list> all_defns
%type <Parse_tree.Defn.t> defn

%start all_defns
%token SORT ABT EQUAL BAR LPAREN RPAREN SYMBOL DOT STAR OF BINDING QUOTE COMMA EOF
%token <string> Name NAME

%right DOT

%%

all_defns: defns EOF { $1 }

defns:
  | /* empty */ { [] }
  | defn defns { $1 :: $2 }

defn:
  | ABT args Name { { name = $3; args = $2; body = External_abt } }
  | ABT args Name EQUAL constructors { { name = $3; args = $2; body = Internal_abt $5 } }
  | SYMBOL args Name { { name = $3; args = $2; body = Symbol } }
  | SORT args Name EQUAL constructors { { name = $3; args = $2; body = Sort $5 } }

arg_name:
  QUOTE Name { $2 }

args:
  | /* empty */ { [] }
  | arg_name { [$1] }
  | LPAREN arg_list RPAREN { $2 }

arg_list:
  | arg_name { [$1] }
  | arg_name COMMA arg_list { $1 :: $3 }

constructors:
  | /* empty */ { [] }
  | non_empty_constructors { $1 }
  | BAR non_empty_constructors { $2 }

non_empty_constructors:
  | constructor { [$1] }
  | constructor BAR non_empty_constructors { $1 :: $3 }

constructor:
  | NAME { ($1, None) }
  | NAME OF abt { ($1, Some $3) }

abt:
  | simple_abt { $1 }
  | product { Abt.Prod $1 }
  | abt DOT abt { Abt.Bind ($1, $3) }

simple_abt:
  | Name { Abt.Use ($1, []) }
  | arg_name { Abt.Arg_use $1 }
  | simple_abt Name { Abt.Use ($2, [$1]) }
  | LPAREN comma_separated_abts RPAREN Name { Abt.Use ($4, $2) }
  | Name BINDING { Abt.Binding $1 }
  | LPAREN abt RPAREN { $2 }

comma_separated_abts:
  | abt COMMA abt { [ $1; $3 ] }
  | abt COMMA comma_separated_abts { $1 :: $3 }

product:
  | simple_abt STAR simple_abt { [$1; $3] }
  | simple_abt STAR product { $1 :: $3 }
