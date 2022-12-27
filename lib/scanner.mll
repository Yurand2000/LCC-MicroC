{
    open ScannerTokens
    open String
    open Location

    (* Auxiliary definitions *)
    exception Lexing_error of Location.lexeme_pos * string
}

(* Generic Regular Expressions *)
let letters = ['a'-'z'] | ['A' - 'Z']
let zero = '0'
let octal_digits = ['0'-'7']
let octal_digits_non_zero = ['1'-'7']
let digits = octal_digits | ['8'-'9']
let digits_non_zero = octal_digits_non_zero | ['8'-'9']
let hex_digits = digits | ['a' - 'f'] | ['A' - 'F']
let hex_digits_non_zero = digits_non_zero | ['a' - 'f'] | ['A' - 'F']
let special_chars = "\\'" | "\\b" | "\\f" | "\\t" | "\\\\" | "\\r" | "\\n"
let chars = [^ '\'' '\b' '\t' '\\' '\r' '\n' ]
let str_special_chars = "\\\"" | "\\b" | "\\f" | "\\t" | "\\\\" | "\\r" | "\\n"
let str_chars = [^ '\"' '\b' '\t' '\\' '\r' '\n' ]
let whitespace = ' ' | '\t' | '\n' | '\r'

(* Identifier Regular Expression *)
let ident = ('_' | letters )('_' | letters | digits)*
let sign = '+' | '-'
let octal_number_prefix = zero
let hex_number_prefix = ("0x" | "0X")

(* Integer Regular Expression *)
let octal_integer = octal_digits_non_zero octal_digits* | zero
let decimal_integer = digits_non_zero digits* | zero
let hex_integer = hex_digits_non_zero hex_digits* | zero
let integer =
      decimal_integer
    | octal_number_prefix octal_integer
    | hex_number_prefix hex_integer

(* Float Regular Expression *)
let decimal_significand =
      decimal_integer
    | (decimal_integer '.' digits*)
    | ('.' digits+)

let hex_significand =
      hex_integer
    | (hex_integer '.' hex_digits*)
    | ('.' hex_digits+)

let significand =
      decimal_significand
    | hex_number_prefix hex_significand

let exponent =
      ( 'e' | 'E' ) sign? decimal_integer
    | ( 'p' | 'P' ) sign? hex_integer

let float = significand exponent? ('f' | 'F')

(* Other Types *)
let char = '\'' chars '\''
let bool = "true" | "false"

(* Scanner specification *)
rule next_token = parse
    (* Whitespaces -> Do Nothing *)
    | whitespace { next_token lexbuf }

    (* Keywords *)
    | "if" { IF }
    | "else" { ELSE }
    | "for" { FOR }
    | "while" { WHILE }
    | "do" { DO }

    | "int" { TINT }
    | "float" { TFLOAT }
    | "char" { TCHAR }
    | "void" { TVOID }
    | "bool" { TBOOL }

    | "return" { RETURN }
    | "NULL" { NULL }
    | "struct" { STRUCT }
    | "sizeof" { SIZEOF }

    (* Operators *)
    | '=' { ASSIGN }
    | '+' { PLUS }
    | '-' { MINUS }
    | '*' { TIMES }
    | '/' { DIV }
    | '%' { MOD }
    | "++" { INCREMENT }
    | "--" { DECREMENT }

    | "==" { EQ }
    | "!=" { NEQ }
    | "<=" { LEQ }
    | '<' { LS }
    | '>' { GR }
    | ">=" { GEQ }
    | "&&" { AND }
    | "||" { OR }
    | '!' { NOT }

    | '&' { BIT_AND }
    | '|' { BIT_OR }
    | '~' { BIT_NOT }
    | '^' { BIT_XOR }
    | "<<" { SHIFT_LEFT }
    | ">>" { SHIFT_RIGHT }

    | "+=" { ASSIGN_PLUS }
    | "-=" { ASSIGN_MINUS }
    | "*=" { ASSIGN_TIMES }
    | "/=" { ASSIGN_DIV }
    | "%=" { ASSIGN_MOD }
    | "&=" { ASSIGN_BIT_AND }
    | "|=" { ASSIGN_BIT_OR }
    | "^=" { ASSIGN_BIT_XOR }
    | "<<=" { ASSIGN_SHIFT_LEFT }
    | ">>=" { ASSIGN_SHIFT_RIGHT }

    (* Identifiers and Values *)
    | integer as str 
        {
            INT (int_of_string str)
        }
    | float as str 
        {
            FLOAT (float_of_string str)
        }
    | '\"' (str_chars | str_special_chars) as str '\"'
        {
            STRING str
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
    
    | "true" { BOOL (true) }
    | "false" { BOOL (false) }
    
    | ident as str { IDENT str }
        
    (* Other Symbols *)
    | ';' { SEMICOLON }
    | ',' { COMMA }
    | '.' { DOT }
    | "->" { ARROW }
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