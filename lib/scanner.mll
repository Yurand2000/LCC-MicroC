{
    open ScannerTokens
    open String
    open Location

    (* Auxiliary definitions *)
    exception Lexing_error of Location.lexeme_pos * string

}

(* Regular Expressions *)
let letters = ['a'-'z'] | ['A' - 'Z']
let digits = ['0'-'9']
let hex_digits = digits | ['a' - 'f'] | ['A' - 'F']
let special_chars = "\\'" | "\\b" | "\\f" | "\\t" | "\\\\" | "\\r" | "\\n"
let chars = [^ '\'' '\b' '\t' '\\' '\r' '\n' ]
let whitespace = ' ' | '\t' | '\n' | '\r'

let ident = ('_' | letters )('_' | letters | digits)*
let integer = digits+ | ("0x" | "0X") hex_digits+
let char = '\'' chars '\''
let bool = "true" | "false"
let operators = '&' | '+' | '-' | '*' | '/' | '%' | '=' | "==" | "!=" | "<=" | '<' | '>' | ">=" | "&&" | "||" | '!'

(* Scanner specification *)
rule next_token = parse
    (* Whitespaces -> Do Nothing *)
    | whitespace { next_token lexbuf }

    (* Keywords *)
    | "if" { IF }
    | "else" { ELSE }
    | "for" { FOR }
    | "while" { WHILE }

    | "int" { TINT }
    | "char" { TCHAR }
    | "void" { TVOID }
    | "bool" { TBOOL }

    | "return" { RETURN }
    | "NULL" { NULL }

    (* Operators *)
    | '&' { ADDR_OF }
    | '+' { PLUS }
    | '-' { MINUS }
    | '*' { TIMES }
    | '/' { DIV }
    | '%' { MOD }
    | '=' { ASSIGN }
    | "==" { EQ }
    | "!=" { NEQ }
    | "<=" { LEQ }
    | '<' { LS }
    | '>' { GR }
    | ">=" { GEQ }
    | "&&" { AND }
    | "||" { OR }
    | '!' { NOT }

    (* Identifiers and Values *)
    | ident as str { IDENT str }
    | integer as str 
        {
            INT (int_of_string str)
        }

    | '\'' chars as str '\''
        {
            let pos = to_lexeme_position lexbuf in
            let character =
                if length str == 1 then get str 0
                else raise (Lexing_error (pos, "Error in parsing \'char\'."))
            in
            CHAR character
        }
    | '\'' '\'' '\'' { CHAR '\'' }
    | '\'' "\b" '\'' { CHAR '\b' }
    | '\'' "\\f" '\'' { CHAR '\x0C' }
    | '\'' "\t" '\'' { CHAR '\t' }
    | '\'' "\\" '\'' { CHAR '\\' }
    | '\'' "\r" '\'' { CHAR '\r' }
    | '\'' "\n" '\'' { CHAR '\n' }
    
    | bool as str { BOOL (equal str "true") }
        
    (* Other Symbols *)
    | ';' { SEMICOLON }
    | '(' { LPAREN }
    | ')' { RPAREN }
    | '[' { LSQR_BRACKET }
    | ']' { RSQR_BRACKET }
    | '{' { LBRACE }
    | '}' { RBRACE }
    | eof { EOF }

    (* Comments *)
    | "//" { single_line_comment lexbuf }
    | "/*" { multi_line_comment lexbuf }

    (* Unknown Token *)
    | _ { raise (Lexing_error (to_lexeme_position lexbuf, "Syntax Error. ")) }

and single_line_comment = parse
    | '\n' { next_token lexbuf }
    | _ { single_line_comment lexbuf }
and multi_line_comment = parse
    | "*/" { next_token lexbuf }
    | _ { multi_line_comment lexbuf }