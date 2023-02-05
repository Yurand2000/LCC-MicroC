(** Abstract Syntax Tree *)

(** Binary Operators *)
type binop =
  | Add (** Addition *)
  | Sub (** Subtraction *)
  | Mult (** Multiplication *)
  | Div (** Division *)
  | Mod (** Modulo operator *)
  | Bit_And (** Bitwise And *)
  | Bit_Or (** Bitwise Or *)
  | Bit_Xor (** Bitwise Xor *)
  | Shift_Left (** Shift Left *)
  | Shift_Right (** (Arithmetic) Shift Right *)
  | Equal (** Equality *)
  | Neq (** Non-Equality *)
  | Less (** Less then *)
  | Leq (** Less or equal then *)
  | Greater (** Greater then *)
  | Geq (** Greater of equal then *)
  | And (** Logical and *)
  | Or (** Logical or *)
[@@deriving show]

(** Unary Operators *)
type uop =
  | Pos (** Unary positive *)
  | Neg (** Unary negation *)
  | Bit_Not (** Bitwise Not *)
  | Not (** Boolean Not *)
[@@deriving show]

(** Identifier *)
type identifier = string [@@deriving show]

(** Annotated Node with code location *)
type 'a annotated_node = {
  loc : Location.code_pos; [@opaque]
  node : 'a;
}
[@@deriving show]

(** Type representation *)
type typ =
  | TypI (** Type int *)
  | TypF (** Type float *)
  | TypB (** Type bool *)
  | TypC (** Type char *)
  | TypA of typ * int option (** Array type *)
  | TypP of typ (** Pointer type  *)
  | TypS of identifier (** Struct type *)
  | TypV (** Type void  *)
[@@deriving show]

and expr = expr_node annotated_node

(** Expressions *)
and expr_node =
  | Access of access (** Variable access ([x] or [*p] or [a[e]]) *)
  | Assign of access * expr (** Variable assignment ([x = e] or [*p = e] or [a[e] = e]) *)
  | Addr of access (** Address of variable ([&x] or [&*p] or [&a[e]]) *)
  | ILiteral of int (** Integer literal *)
  | FLiteral of float (** Float literal *)
  | CLiteral of char (** Char literal *)
  | BLiteral of bool (** Bool literal *)
  | SLiteral of string (** String literal *)
  | UnaryOp of uop * expr (** Unary primitive operator *)
  | BinaryOp of binop * expr * expr (** Binary primitive operator *)
  | CommaOp of expr * expr (** Comma operator *)
  | Call of identifier * expr list (** Function call [fn(args)] *)
  | SizeOf of typ (** SizeOf operator *)
  | Cast of typ * expr (** Type cast (type)expression *)
[@@deriving show]

and access = access_node annotated_node

(** Access expressions *)
and access_node =
  | AccVar of identifier (** Variable access *)
  | AccDeref of expr (** Pointer dereferencing ( [*p] ) *)
  | AccIndex of access * expr (** Array/Pointer indexing ( [a[e]] ) *)
  | AccStruct of access * identifier (** Struct Dot and Arrow access ( [a.b] or [p->b] ) *)
[@@deriving show]

and stmt = stmt_node annotated_node

(** Statements *)
and stmt_node =
  | If of expr * stmt * stmt (** Conditional *)
  | While of expr * stmt (** While loop *)
  | Expr of expr (** Expression statement ( [e;] ) *)
  | Return of expr option (** Return statement *)
  | Block of stmtordec list (** Block: grouping and scope *)
[@@deriving show]

and stmtordec = stmtordec_node annotated_node

(** Statements and declarations inside blocks *)
and stmtordec_node =
  | Dec of typ * identifier (** Local variable declaration *)
  | Stmt of stmt (** Statement *)
[@@deriving show]

(** Function Declaration and Definition (return type, function name, formal parameters and body) *)
type fun_decl = {
  typ : typ;
  fname : string;
  formals : (typ * identifier) list;
  body : stmt;
}
[@@deriving show]

type topdecl = topdecl_node annotated_node

(** Top Declarations: Functions, Global variables and Struct Types *)
and topdecl_node =
  | Fundecl of fun_decl
  | Vardec of typ * identifier * expr option
  | StructDecl of identifier * (typ * identifier) list
[@@deriving show]

(** The whole program *)
type program = Prog of topdecl list [@@deriving show]
