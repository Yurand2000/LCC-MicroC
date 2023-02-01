(** List of tokens generated from the Tokenizer *)

type token =
(* Keywords and base types *)
| IF | ELSE
| FOR | WHILE | DO
| TINT | TFLOAT | TCHAR | TVOID | TBOOL
| RETURN | NULL
| STRUCT | SIZEOF

(* Mathematical Operators *)
| PLUS | MINUS | TIMES | DIV | MOD
| INCREMENT | DECREMENT

(* Comparison operators *)
| EQ | NEQ | LEQ | LS | GR | GEQ

(* Logic Operators *)
| AND | OR | NOT

(* Bitwise operators *)
| BIT_AND | BIT_OR | BIT_NOT | BIT_XOR
| SHIFT_LEFT | SHIFT_RIGHT

(* Assignment Operators*)
| ASSIGN
| ASSIGN_PLUS | ASSIGN_MINUS | ASSIGN_TIMES
| ASSIGN_DIV | ASSIGN_MOD
| ASSIGN_BIT_AND | ASSIGN_BIT_OR
| ASSIGN_BIT_XOR
| ASSIGN_SHIFT_LEFT | ASSIGN_SHIFT_RIGHT

(* Identifiers and Values *)
| IDENT of string
| INT of int
| FLOAT of float
| CHAR of char
| STRING of string
| BOOL of bool

(* Parenthesis *)
| LPAREN | RPAREN
| LSQR_BRACKET | RSQR_BRACKET
| LBRACE | RBRACE

(* Other Symbols *)
| SEMICOLON | COMMA | DOT | ARROW
| EOF

[@@deriving show]