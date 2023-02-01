(** Parser *)

(** Syntax error with position and error message *)
exception Syntax_error of Location.lexeme_pos * string

(** Main parse function which takes the tokenizer main function, a Lexing.lexbuf and parses it, returning the AST of the program. *)
val parse : (Lexing.lexbuf -> ScannerTokens.token) -> Lexing.lexbuf -> Ast.program
