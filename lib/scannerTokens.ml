type token =
(* Keywords and base types *)
| IF | ELSE
| FOR | WHILE
| TINT | TCHAR | TVOID | TBOOL
| RETURN | NULL

(* Operators *)
| ADDR_OF | ASSIGN
| PLUS | MINUS | TIMES | DIV | MOD
| EQ | NEQ | LEQ | LS | GR | GEQ
| AND | OR | NOT

(* Identifiers and Values *)
| IDENT of string
| INT of int
| CHAR of char
| BOOL of bool

(* Other Symbols *)
| SEMICOLON | COMMA
| LPAREN | RPAREN
| LSQR_BRACKET | RSQR_BRACKET
| LBRACE | RBRACE
| EOF
[@@deriving show]