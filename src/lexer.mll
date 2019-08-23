{
open! Core
open Parser
}

let whitespace = [' ' '\t']
let printing = ['!'-'~']
let newline = '\r' | '\n' | "\r\n"
let digit = ['0'-'9']
let lower = ['a'-'z']
let upper = ['A'-'Z']
let alpha = ['a'-'z' 'A'-'Z']
let alphanum = ['0'-'9' 'a'-'z' 'A'-'Z']
let ident_char = (alphanum|'_')

rule token = parse
  | whitespace+ {
      token lexbuf
    }
  | newline {
      Lexing.new_line lexbuf;
      token lexbuf
    }
  | "(" {
      LPAREN
    }
  | ")" {
      RPAREN
    }
  | "=" {
      EQUAL
    }
  | "|" {
      BAR
    }
  | "." {
      DOT
    }
  | "*" {
      STAR
    }
  | "'" {
      QUOTE
    }
  | "," {
      COMMA
    }
  | "of" {
      OF
    }
  | "sort" {
      SORT
    }
  | "abt" {
      ABT
    }
  | "symbol" {
      SYMBOL
    }
  | "binding" {
      BINDING
    }
  | "(*" {
      comment 1 lexbuf; token lexbuf
    }
  | lower(ident_char)* as name {
      Name name
    }
  | upper(ident_char)* as name {
      NAME name
    }
  | eof {
      EOF
    }
  | _ {
      failwithf
        !"Illegal character at %{Source_code_position}"
        (Lexing.lexeme_start_p lexbuf)
        ()
    }

and comment depth = parse
  | "(*" {
      comment (depth + 1) lexbuf
    }
  | "*)" {
      if Int.equal depth 1
      then ()
      else comment (depth - 1) lexbuf
    }
  | (printing|whitespace) {
      comment depth lexbuf
    }
  | newline {
      Lexing.new_line lexbuf;
      comment depth lexbuf
    }
  | eof {
      failwithf
        !"EOF before end of comment at %{Source_code_position}"
        (Lexing.lexeme_start_p lexbuf)
        ()
    }
  | _ {
      failwithf
        !"Illegal character in comment at %{Source_code_position}"
        (Lexing.lexeme_start_p lexbuf)
        ()
    }

{
}
