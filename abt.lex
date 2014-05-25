type lexresult = Token.t

open Token

fun eof () = EOF
%%
alpha=[A-Za-z];
ws = [\ \t\n];
%%

{ws}+ => (lex ());
"abt" => (ABT);
"=" => (EQUAL);
"|" => (BAR);
"(" => (LPAREN);
")" => (RPAREN);
"," => (COMMA);
"symbol" => (SYMBOL);
"." => (DOT);
{alpha}+ => (Name yytext);
