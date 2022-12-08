/*
* MicroC Parser specification
*/

%{
  open Ast

  type variable_description = 
  | Id of string
  | Ptr of variable_description
  | Array of variable_description
  | ArrayNum of variable_description * int

  let annotate node lstart lend = {
    node = node;
    loc = Location.to_code_position (lstart, lend);
  }

  exception ErrorMsg of string

  let raise_error msg = 
    raise (ErrorMsg msg)

%}

/* ------------------------------------------ */
/* Tokens declarations */
/* Keywods and base types */
%token IF ELSE FOR WHILE RETURN
%token NULL TINT TCHAR TVOID TBOOL

/* Operators */
%token ADDR_OF ASSIGN
%token PLUS MINUS TIMES "*" DIV MOD
%token EQ NEQ LEQ LS GR GEQ
%token AND OR NOT

/* Identifiers and Const Values */
%token <string> IDENT
%token <int> INT
%token <char> CHAR
%token <bool> BOOL

/* Other Symbols */
%token SEMICOLON COMMA
%token LPAREN RPAREN
%token LSQR_BRACKET RSQR_BRACKET
%token LBRACE RBRACE
%token EOF

/* ------------------------------------------ */
/* Precedence and associativity specification */
//%left COMMA
%right ASSIGN
%left OR
%left AND
%left EQ NEQ
%left GR GEQ LS LEQ
%left PLUS MINUS
%left TIMES DIV MOD
%right NOT ADDR_OF DEFER UPLUS UMINUS
%left LSQR_BRACKET /*LPAREN*/

/* ------------------------------------------ */
/* Starting symbol */

%start program
%type <Ast.program> program    /* the parser returns a Ast.program value */

%%

/* Grammar specification */
/* returns a node of type: program */
let program :=
| decl = topdecl; prog = program;
  {
    match prog with
    | Prog decls -> Prog( decl :: decls )
  }
| EOF; { Prog([]) }
| error; { raise_error "Program Error" }

/* returns a node of type: topdecl */
let topdecl :=
| (t, id) = vardecl; SEMICOLON; { annotate (Vardec (t, id)) $startpos $endpos }
| f_decl = fundecl; { annotate (Fundecl f_decl) $startpos $endpos }

/* returns: typ * identifier */
let vardecl :=
| t = typ; desc = vardesc;
  {
    let rec build_vardecl t desc =
      match desc with
      | Id id -> (t, id)
      | Ptr decl -> build_vardecl (TypP t) decl
      | Array decl -> build_vardecl (TypA (t, None)) decl
      | ArrayNum (decl, size) -> build_vardecl (TypA (t, Some size)) decl
    in
    build_vardecl t desc
  }

/* returns: variable_description (local definition, not from ast.ml) */
let vardesc :=
| id = IDENT; { Id id }
| "*"; desc = vardesc; { Ptr desc }
| LPAREN; desc = vardesc; RPAREN; { desc }
| desc = vardesc; LSQR_BRACKET; RSQR_BRACKET; { Array desc }
| desc = vardesc; LSQR_BRACKET; size = INT; RSQR_BRACKET; { ArrayNum (desc, size) }

/* returns: fun_decl */
let fundecl :=
| t = typ; fname = IDENT; LPAREN; args = funargs; RPAREN; body = block;
  {
    {
      typ = t;
      fname = fname;
      formals = args;
      body = body;
    }
  }

/* returns: (typ * identifier) list */
let funargs :=
| { [] }
| decl = vardecl; { [decl] }
| decl = vardecl; COMMA; args = funargs; { decl :: args }

/* returns a node of type: stmt */
let block :=
| LBRACE; block = block_inner?; RBRACE;
  {
    let block = match block with
      | Some stmts -> stmts
      | None -> []
      in
    annotate (Block block) $startpos $endpos
  }

/* returns: stmtordec list */
let block_inner :=
| stmt_decl = stmt_or_decl; { [ stmt_decl ] }
| stmt_decl = stmt_or_decl; block = block_inner; { stmt_decl :: block }

/* returns a node of type: stmtordec */
let stmt_or_decl :=
| stmt = stmt;
  { annotate (Stmt stmt) $startpos $endpos }
| (t, desc) = vardecl;
  { annotate (Dec (t, desc)) $startpos $endpos }

/* returns a node of type: typ */
let typ :=
| TINT; { TypI }
| TCHAR; { TypC }
| TVOID; { TypV }
| TBOOL; { TypB }

/* returns a node of type: stmt */
let single_line_stmt :=
| RETURN; e = expr?; SEMICOLON; { annotate (Return e) $startpos $endpos }
| e = expr; SEMICOLON; { annotate (Expr e) $startpos $endpos }
| SEMICOLON; { annotate (Block []) $startpos $endpos }

/* returns a node of type: stmt */
let stmt :=
| stmt = single_line_stmt; { Printf.printf("single"); stmt }
| stmt = block; { stmt }
| WHILE; g = if_guard; body = stmt;
  {
    annotate (While (g, body)) $startpos $endpos
  }
| FOR; LPAREN; init = expr?; SEMICOLON; guard = expr?; SEMICOLON; incr = expr?; RPAREN; body = stmt;
  {
    let init = match init with
      | Some e -> annotate (Expr e) $startpos $endpos
      | None -> annotate (Block []) $startpos $endpos
      in
    let guard = match guard with
      | Some e -> e
      | None -> annotate (BLiteral true) $startpos $endpos
      in
    let body = match incr with
      | Some e -> 
        let incr = annotate (Expr e) $startpos $endpos in
        annotate (Block [
          annotate (Stmt body) $startpos $endpos;
          annotate (Stmt incr) $startpos $endpos
        ]) $startpos $endpos
      | None -> body
      in
    annotate (Block [
      annotate (Stmt init) $startpos $endpos;
      annotate (Stmt 
        ( annotate (While (guard, body)) $startpos $endpos )
      ) $startpos $endpos
    ]) $startpos $endpos
  }
| i_stmt = if_stmt; { i_stmt }

/* returns a node of type: stmt */
let if_stmt :=
| IF; g = if_guard; b = if_body;
  {
    let empty_block = annotate (Block []) $startpos $endpos in
    annotate (If (g, b, empty_block)) $startpos $endpos
  }
| IF; g = if_guard; then_b = if_body; ELSE; else_b = if_body;
  {
    annotate (If (g, then_b, else_b)) $startpos $endpos
  }
| IF; g = if_guard; then_b = if_body; ELSE; elif_b = if_stmt;
  {
    annotate (If (g, then_b, elif_b)) $startpos $endpos
  }

/* returns a node of type: expr */
let if_guard :=
| LPAREN; e = expr; RPAREN; { e }

/* returns a node of type: stmt */
let if_body :=
| stmt = single_line_stmt; { stmt }
| stmt = block; { stmt }

/* returns a node of type: expr */
let expr :=
| e = rexpr; { e }
| e = lexpr; { annotate (Access e) $startpos $endpos }

/* returns a node of type: access */
let lexpr :=
| id = IDENT; { annotate (AccVar id) $startpos $endpos }
| LPAREN; e = lexpr; RPAREN; { e }
| "*"; e = lexpr;
  {
    let e = annotate (Access e) $startpos $endpos in
    annotate (AccDeref e) $startpos $endpos
  } %prec DEFER
| "*"; e = aexpr; { annotate (AccDeref e) $startpos $endpos } /*%prec DEFER*/
| e = lexpr; LSQR_BRACKET; index = expr; RSQR_BRACKET;
  { annotate (AccIndex (e, index)) $startpos $endpos }

/* returns a node of type: expr */
let rexpr :=
| e = aexpr; { e }
| fun_id = IDENT; LPAREN; args = fun_args; RPAREN; { annotate (Call (fun_id, args)) $startpos $endpos }
| l = lexpr; ASSIGN; r = expr; { annotate (Assign (l, r)) $startpos $endpos }

| PLUS; e = expr; { e } %prec UPLUS
| MINUS; e = expr; { annotate (UnaryOp (Neg, e)) $startpos $endpos } %prec UMINUS
| l = expr; PLUS; r = expr; { annotate (BinaryOp (Add, l, r)) $startpos $endpos }
| l = expr; MINUS; r = expr; { annotate (BinaryOp (Sub, l, r)) $startpos $endpos }
| l = expr; TIMES; r = expr; { annotate (BinaryOp (Mult, l, r)) $startpos $endpos }
| l = expr; DIV; r = expr; { annotate (BinaryOp (Div, l, r)) $startpos $endpos }
| l = expr; MOD; r = expr; { annotate (BinaryOp (Mod, l, r)) $startpos $endpos }

| l = expr; AND; r = expr; { annotate (BinaryOp (And, l, r)) $startpos $endpos }
| l = expr; OR; r = expr; { annotate (BinaryOp (Or, l, r)) $startpos $endpos }
| NOT; e = expr; { annotate (UnaryOp (Not, e)) $startpos $endpos }

| l = expr; LS; r = expr; { annotate (BinaryOp (Less, l, r)) $startpos $endpos }
| l = expr; GR; r = expr; { annotate (BinaryOp (Greater, l, r)) $startpos $endpos }
| l = expr; LEQ; r = expr; { annotate (BinaryOp (Leq, l, r)) $startpos $endpos }
| l = expr; GEQ; r = expr; { annotate (BinaryOp (Geq, l, r)) $startpos $endpos }
| l = expr; EQ; r = expr; { annotate (BinaryOp (Equal, l, r)) $startpos $endpos }
| l = expr; NEQ; r = expr; { annotate (BinaryOp (Neq, l, r)) $startpos $endpos }

/* returns: expr list */
let fun_args :=
| { [] }
| e = expr; { [ e ] }
| e = expr; COMMA; exprs = fun_args; { e :: exprs }

/* returns a node of type: expr */
let aexpr :=
| ival = INT; { annotate (ILiteral ival) $startpos $endpos }
| cval = CHAR; { annotate (CLiteral cval) $startpos $endpos }
| bval = BOOL; { annotate (BLiteral bval) $startpos $endpos }
| NULL; { annotate (ILiteral 0) $startpos $endpos }
| LPAREN; e = rexpr; RPAREN; { e }
| ADDR_OF; e = lexpr; { annotate (Addr e) $startpos $endpos }