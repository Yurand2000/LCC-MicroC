{
    open ScannerTokens
    open String
    open Location

    (* Auxiliary definitions *)
    exception Lexing_error of Location.lexeme_pos * string
}

(* Generic Regular Expressions *)
let whitespace = ' ' | '\t' | '\r'
let letters = ['a'-'z'] | ['A' - 'Z']
let digits = ['0'-'9']

(* Identifier expression *)
let ident = ('_' | letters)('_' | letters | digits)*

(* Character expressions *)
let special_chars = "\\'" | "\\b" | "\\f" | "\\t" | "\\\\" | "\\r" | "\\n"
let chars = [^ '\'' '\b' '\t' '\\' '\r' '\n' ]

(* Characters for string literals *)
let str_special_chars = "\\\"" | "\\b" | "\\f" | "\\t" | "\\\\" | "\\r" | "\\n"
let str_chars = [^ '\"' '\b' '\t' '\\' '\r' '\n' ]

(* Expressions for Numbers *)
let octal_number_prefix = '0'
let octal_digits = ['0'-'7']
let octal_digits_non_zero = ['1'-'7']

let dec_digits = octal_digits | ['8'-'9']
let dec_digits_non_zero = octal_digits_non_zero | ['8'-'9']

let hex_number_prefix = ("0x" | "0X")
let hex_digits = dec_digits | ['a' - 'f'] | ['A' - 'F']
let hex_digits_non_zero = dec_digits_non_zero | ['a' - 'f'] | ['A' - 'F']

(* Integer Regular Expression *)
let zero = '0'
let octal_integer = octal_digits_non_zero octal_digits* | zero
let decimal_integer = dec_digits_non_zero dec_digits* | zero
let hex_integer = hex_digits_non_zero hex_digits* | zero
let integer =
      decimal_integer
    | octal_number_prefix octal_integer
    | hex_number_prefix hex_integer

(* Float Regular Expression *)
(* Adaptation from https://en.cppreference.com/w/c/language/floating_constant *)
let sign = '+' | '-'
let decimal_significand =
      decimal_integer
    | (decimal_integer '.' dec_digits*)
    | ('.' dec_digits+)
let decimal_exponent =
    ( 'e' | 'E' ) sign? decimal_integer

let hex_significand =
      hex_integer
    | (hex_integer '.' hex_digits*)
    | ('.' hex_digits+)
let hex_exponent =
    ( 'p' | 'P' ) sign? hex_integer

let float = 
      decimal_significand decimal_exponent? 
    | hex_number_prefix hex_significand hex_exponent?

let float_end_marker = ('f' | 'F')

(* Scanner specification *)
rule next_token = parse
    (* Whitespaces -> Skip Character *)
    | whitespace { next_token lexbuf }
    | '\n' { Lexing.new_line lexbuf; next_token lexbuf }

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

    | '=' { ASSIGN }
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

    (* Integer and Float literals *)
    | integer as str  { INT (int_of_string str) }
    | float as str float_end_marker { FLOAT (float_of_string str) }

    (* String literals *)
    | '\"' ((str_chars | str_special_chars)* as str) '\"' { STRING str }

    (* Char literals *)
    | '\'' chars as str '\''
        {
            let pos = to_lexeme_position lexbuf in
            let character =
                if length str == 1 then get str 0
                else raise (Lexing_error (pos, "Error in parsing \'char\'."))
            in
            CHAR character
        }

    (* Escaped Characters literals *)
    | '\'' '\'' '\'' { CHAR '\'' }
    | '\'' "\b" '\'' { CHAR '\b' }
    | '\'' "\\f" '\'' { CHAR '\x0C' }
    | '\'' "\t" '\'' { CHAR '\t' }
    | '\'' "\\" '\'' { CHAR '\\' }
    | '\'' "\r" '\'' { CHAR '\r' }
    | '\'' "\n" '\'' { CHAR '\n' }
    
    (* Boolean literals *)
    | "true" { BOOL (true) }
    | "false" { BOOL (false) }
    
    (* Itentifiers *)
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

    (* Unknown Tokens *)
    | _ as char { raise (Lexing_error (to_lexeme_position lexbuf, "Syntax Error, found symbol(s): \"" ^ (String.make 1 char) ^ "\".")) }

(* Single-line comment scanner *)
and single_line_comment = parse
    | '\n' { Lexing.new_line lexbuf; next_token lexbuf }
    | _ { single_line_comment lexbuf }

(* Multi-line comment scanner *)
and multi_line_comment = parse
    | "*/" { next_token lexbuf }
    | '\n' { Lexing.new_line lexbuf; multi_line_comment lexbuf }
    | _ { multi_line_comment lexbuf }