(** Scanner/Tokenizer *)

(** Lexical error with position and description *)
exception Lexing_error of Location.lexeme_pos * string

(** Main function which retrieves the next token from a Lexing.lexbuf *)
val next_token : Lexing.lexbuf -> ScannerTokens.token
