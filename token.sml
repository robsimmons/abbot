structure Token = struct
  datatype t = EOF | ABT | EQUAL | BAR | LPAREN | RPAREN | COMMA | SYMBOL | DOT | Name of string
end
