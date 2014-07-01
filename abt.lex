structure Tokens = Tokens

type pos = int
type svalue = Tokens.svalue
type ('a,'b) token = ('a,'b) Tokens.token
type lexresult= (svalue,pos) token

val pos = ref 0
val eof = fn () => Tokens.EOF (!pos,!pos)

exception Illegal_character of pos

val commentLevel = ref 0
fun enterComment () = commentLevel := !commentLevel + 1
fun exitComment () = (commentLevel := !commentLevel - 1; !commentLevel = 0)

val thestring: string list ref = ref []
fun addString s = thestring := s :: !thestring
fun addSpecialChar s =
   case Char.fromCString s of
      NONE => raise Fail ("Not a legitimate character escape: '" ^ s ^ "'")
    | SOME c => thestring := Char.toString c :: !thestring
fun convertString (): string =
     (String.concat (rev (!thestring))) before thestring := []
fun initString () = thestring := []

%%
%full
%header (functor Abt_LexFun(structure Tokens: Abt_TOKENS));
%s STRING COMMENT;

alpha=[A-Za-z];
digit=[0-9];
any = [a-zA-Z0-9'_];

ws = [\ \t\011\012\r];

%%

<INITIAL> \n       => (pos := (!pos) + 1; lex());
<INITIAL> {ws}+    => (lex());

<INITIAL> "("      => (Tokens.LPAREN (!pos, !pos));
<INITIAL> ")"      => (Tokens.RPAREN (!pos, !pos));

<INITIAL> "="      => (Tokens.EQUAL (!pos, !pos));
<INITIAL> "|"      => (Tokens.BAR (!pos, !pos));
<INITIAL> ","      => (Tokens.COMMA (!pos, !pos));
<INITIAL> "."      => (Tokens.DOT (!pos, !pos));

<INITIAL> "abt"  => (Tokens.ABT (!pos, !pos));
<INITIAL> "symbol"  => (Tokens.SYMBOL (!pos, !pos));

<INITIAL> {alpha}{any}* => (Tokens.Name (yytext, !pos, !pos));
<INITIAL> "(*"     => (YYBEGIN COMMENT; enterComment (); lex ());
<INITIAL> .        => (raise Fail ("Unexpected character '"^
                                   String.toCString yytext^"'"));

<COMMENT> "(*"     => (enterComment (); lex ());
<COMMENT> "*)"     => (if exitComment () then YYBEGIN INITIAL else (); lex ());
<COMMENT> \n       => (lex ());
<COMMENT> .        => (lex ());
