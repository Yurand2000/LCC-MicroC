exception Syntax_error of Location.lexeme_pos * string

val parse : (Lexing.lexbuf -> ScannerTokens.token) -> Lexing.lexbuf -> Ast.program
