/*
* MicroC Parser specification
*/

%{
  open Ast
  open List

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

  let rec build_vardecl t desc =
    match desc with
    | Id id -> (t, id)
    | Ptr decl -> build_vardecl (TypP t) decl
    | Array decl -> build_vardecl (TypA (t, None)) decl
    | ArrayNum (decl, size) -> build_vardecl (TypA (t, Some size)) decl

  let unOp op e startpos endpos =
    annotate (UnaryOp (op, e)) startpos endpos
  let binOp op l r startpos endpos = 
    annotate (BinaryOp (op, l, r)) startpos endpos

  let access l startpos endpos =
    annotate (Access l) startpos endpos
  let assign l r startpos endpos =
    annotate (Assign (l, r)) startpos endpos
  let assignBinOp l r op startpos endpos =
    let lvalue = access l startpos endpos in
    let op = binOp op lvalue r startpos endpos in
    assign l op startpos endpos
%}

/* ------------------------------------------ */
/* Tokens declarations */
/* Keywods and base types */
%token IF ELSE FOR WHILE DO RETURN
%token NULL TINT TCHAR TVOID TBOOL TFLOAT
%token STRUCT SIZEOF

/* Operators */
%token PLUS MINUS TIMES "*" DIV MOD
%token INCREMENT DECREMENT
%token EQ NEQ LEQ LS GR GEQ
%token AND OR NOT
%token BIT_AND "&" BIT_OR BIT_XOR BIT_NOT
%token SHIFT_LEFT SHIFT_RIGHT

%token ASSIGN
%token ASSIGN_PLUS ASSIGN_MINUS ASSIGN_TIMES
%token ASSIGN_DIV ASSIGN_MOD
%token ASSIGN_BIT_AND ASSIGN_BIT_OR
%token ASSIGN_BIT_XOR
%token ASSIGN_SHIFT_LEFT ASSIGN_SHIFT_RIGHT

/* Identifiers and Const Values */
%token <string> IDENT
%token <int> INT
%token <char> CHAR
%token <bool> BOOL
%token <float> FLOAT
%token <string> STRING

/* Other Symbols */
%token SEMICOLON COMMA DOT ARROW
%token LPAREN RPAREN
%token LSQR_BRACKET RSQR_BRACKET
%token LBRACE RBRACE
%token EOF

/* ------------------------------------------ */
/* Precedence and associativity specification */
%left COMMA
%right ASSIGN ASSIGN_PLUS ASSIGN_MINUS ASSIGN_TIMES ASSIGN_DIV ASSIGN_MOD ASSIGN_SHIFT_LEFT ASSIGN_SHIFT_RIGHT ASSIGN_BIT_AND ASSIGN_BIT_XOR ASSIGN_BIT_OR
%left OR
%left AND
%left BIT_OR
%left BIT_XOR
%left BIT_AND
%left EQ NEQ
%left GR GEQ LS LEQ
%left SHIFT_LEFT SHIFT_RIGHT
%left PLUS MINUS
%left TIMES DIV MOD
%right PRE_INCR_DECR UPLUS UMINUS NOT BIT_NOT DEFER ADDR_OF SIZEOF
%left POST_INCR_DECR FN_CALL ARRAY_SUBSCRIPT STRUCT_ACCESS

%left DOT ARROW
%left INCREMENT DECREMENT
%left LPAREN RPAREN LSQR_BRACKET RSQR_BRACKET LBRACE RBRACE

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
    | Prog decls -> Prog( decl @ decls )
  }
| EOF; { Prog([]) }
| error; { raise_error "Program Error" }

/* returns: topdecl list */
let topdecl :=
| v_decls = vardecl; SEMICOLON;
  {
    let vardecl_builder vardesc =
      let (typ, desc, expr) = vardesc in
      annotate (Vardec (typ, desc, expr)) $startpos $endpos
    in
    List.map vardecl_builder v_decls
  }
| f_decl = fundecl; { [annotate (Fundecl f_decl) $startpos $endpos] }
| s_decl = structdecl;
  {
    let (name, fields) = s_decl in
    [ annotate (StructDecl (name, fields)) $startpos $endpos ]
  }

/* returns: identifier * (typ * identifier) list */
let structdecl :=
| STRUCT; name = IDENT; SEMICOLON; { (name, []) }
| STRUCT; name = IDENT; LBRACE; fields = structFields; RBRACE; SEMICOLON; { (name, fields) }

/* returns: (typ * identifier) list */
let structFields :=
| fields = structField; SEMICOLON; { fields }
| fields = structField; SEMICOLON; other_fields = structFields; { fields @ other_fields }

/* returns: (typ * identifier) list */
let structField :=
| t = typ; descs = structFieldDeclMulti; { List.map (build_vardecl t) descs }

/* returns: variable_description list */
let structFieldDeclMulti :=
| desc = vardesc; { [desc] }
| desc = vardesc; COMMA; descs = structFieldDeclMulti; { desc :: descs }

/* returns: (typ * identifier * expr option) list */
let vardecl :=
| t = typ; descs = vardecl_multi;
  {
    let vardecl_builder vardesc =
      let (desc, expr) = vardesc in
      let (typ, desc) = build_vardecl t desc in
      (typ, desc, expr)
    in
    List.map vardecl_builder descs
  }

/* returns: (variable_description * expr option) list */
let vardecl_multi :=
| desc = vardesc; { [(desc, None)] }
| desc = vardesc; ASSIGN; e = expr_no_comma; { [(desc, Some(e))] }
| desc = vardesc; COMMA; other = vardecl_multi; { (desc, None) :: other }
| desc = vardesc; ASSIGN; e = expr_no_comma; COMMA; other = vardecl_multi; { (desc, Some(e)) :: other }


/* returns: variable_description (local definition, not from ast.ml) */
let vardesc :=
| id = IDENT; { Id id }
| "*"; desc = vardesc; { Ptr desc }
| LPAREN; desc = vardesc; RPAREN; { desc }
| desc = vardesc; LSQR_BRACKET; RSQR_BRACKET; { Array desc }
| desc = vardesc; LSQR_BRACKET; size = INT; RSQR_BRACKET; { ArrayNum (desc, size) }

/* returns: fun_decl */
let fundecl :=
| t = typ; fname = IDENT; LPAREN; args = funargs; RPAREN; SEMICOLON;
  {
    {
      typ = t;
      fname = fname;
      formals = args;
      body = { annotate (Block []) $startpos $endpos };
    }
  }
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
| decl = funarg; { [decl] }
| decl = funarg; COMMA; args = funargs; { decl :: args }

/* returns: typ * identifier */
let funarg :=
| t = typ; desc = vardesc; { build_vardecl t desc }

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
| stmt = stmt; block = block_inner?;
  {
    let stmt = annotate (Stmt stmt) $startpos $endpos in
    match block with
      | Some(block) -> stmt :: block
      | None -> stmt :: []
  }
| vardescs = vardecl; SEMICOLON; block = block_inner?;
  {
    let stmt_builder vardesc =
      let (typ, desc, expr) = vardesc in
      let declaration = annotate (Dec (typ, desc)) $startpos $endpos in
      match expr with
        | Some(expr) ->
          let access = annotate (AccVar desc) $startpos $endpos in
          let assign = annotate (Assign (access, expr)) $startpos $endpos in
          let stmt = annotate (Expr assign) $startpos $endpos in
          declaration :: (annotate (Stmt stmt) $startpos $endpos) :: []
        | None -> declaration :: []
    in
    let rec build vardescs =
      match vardescs with
        | [] -> []
        | hd::tl -> (stmt_builder hd) @ (build tl)
    in
    let new_stmts = build vardescs in
    match block with
      | Some(block) -> new_stmts @ block
      | None -> new_stmts
  }

/* returns a node of type: typ */
let typ :=
| TINT; { TypI }
| TCHAR; { TypC }
| TFLOAT; { TypF }
| TVOID; { TypV }
| TBOOL; { TypB }
| STRUCT; struct_name = IDENT; { TypS struct_name }

/* returns a node of type: typ */
let adv_typ :=
| t = typ; { t }
| "*"; t = adv_typ; { TypP t }
| t = adv_typ; LSQR_BRACKET; i = INT?; RSQR_BRACKET; { TypA (t, i) }

/* returns a node of type: stmt */
let single_line_stmt :=
| RETURN; e = expr?; SEMICOLON; { annotate (Return e) $startpos $endpos }
| e = expr; SEMICOLON; { annotate (Expr e) $startpos $endpos }
| SEMICOLON; { annotate (Block []) $startpos $endpos }

/* returns a node of type: stmt */
let stmt :=
| stmt = single_line_stmt; { stmt }
| stmt = block; { stmt }
| WHILE; guard = if_guard; body = stmt;
  {
    annotate (While (guard, body)) $startpos $endpos
  }
| DO; body = stmt; WHILE; guard = if_guard; SEMICOLON;
  {
    annotate (Block [
      annotate (Stmt body) $startpos $endpos;
      annotate (Stmt 
        ( annotate (While (guard, body)) $startpos $endpos )
      ) $startpos $endpos
    ]) $startpos $endpos
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

let expr :=
| e = rexpr; { e }
| e = lexpr; { annotate (Access e) $startpos $endpos }

/* returns a node of type: expr */
let expr_no_comma :=
| e = rexpr_no_comma; { e }
| e = lexpr; { annotate (Access e) $startpos $endpos }
| LPAREN; e1 = expr; COMMA; e2 = expr; RPAREN; { annotate (CommaOp (e1, e2)) $startpos $endpos }

/* returns a node of type: access */
let lexpr :=
| id = IDENT; { annotate (AccVar id) $startpos $endpos }
| LPAREN; e = lexpr; RPAREN; { e }

| "*"; e = lexpr;
  {
    let e = annotate (Access e) $startpos $endpos in
    annotate (AccDeref e) $startpos $endpos
  } %prec DEFER /* Deferencing */

| e = lexpr; LSQR_BRACKET; index = expr; RSQR_BRACKET; { annotate (AccIndex (e, index)) $startpos $endpos }
  %prec ARRAY_SUBSCRIPT /* Array Access */

| str = lexpr; DOT; field = IDENT; { annotate (AccDot (str, field)) $startpos $endpos }
  %prec STRUCT_ACCESS /* Struct access */

| e = lexpr; ARROW; field = IDENT;
  {
    let e = annotate (Access e) $startpos $endpos in
    annotate (AccArrow (e, field)) $startpos $endpos
  } %prec STRUCT_ACCESS /* Struct deref access */

/* returns a node of type: expr */
let rexpr_no_comma :=
| e = aexpr; { e }
| fun_id = IDENT; LPAREN; args = fun_args; RPAREN; { annotate (Call (fun_id, args)) $startpos $endpos } %prec FN_CALL /* Function Call*/
| l = lexpr; ASSIGN; r = expr_no_comma; { assign l r $startpos $endpos } /* Assignment operator */
| l = lexpr; ASSIGN_PLUS; r = expr_no_comma; { assignBinOp l r Add $startpos $endpos }
| l = lexpr; ASSIGN_MINUS; r = expr_no_comma; { assignBinOp l r Sub $startpos $endpos }
| l = lexpr; ASSIGN_TIMES; r = expr_no_comma; { assignBinOp l r Mult $startpos $endpos }
| l = lexpr; ASSIGN_DIV; r = expr_no_comma; { assignBinOp l r Div $startpos $endpos }
| l = lexpr; ASSIGN_MOD; r = expr_no_comma; { assignBinOp l r Mod $startpos $endpos }
| l = lexpr; ASSIGN_BIT_AND; r = expr_no_comma; { assignBinOp l r Bit_And $startpos $endpos }
| l = lexpr; ASSIGN_BIT_OR; r = expr_no_comma; { assignBinOp l r Bit_Or $startpos $endpos }
| l = lexpr; ASSIGN_BIT_XOR; r = expr_no_comma; { assignBinOp l r Bit_Xor $startpos $endpos }
| l = lexpr; ASSIGN_SHIFT_LEFT; r = expr_no_comma; { assignBinOp l r Shift_Left $startpos $endpos }
| l = lexpr; ASSIGN_SHIFT_RIGHT; r = expr_no_comma; { assignBinOp l r Shift_Right $startpos $endpos }

| PLUS; e = expr_no_comma; { e } %prec UPLUS
| MINUS; e = expr_no_comma; { unOp Neg e $startpos $endpos } %prec UMINUS
| l = expr_no_comma; PLUS; r = expr_no_comma; { binOp Add l r $startpos $endpos }
| l = expr_no_comma; MINUS; r = expr_no_comma; { binOp Sub l r $startpos $endpos }
| l = expr_no_comma; TIMES; r = expr_no_comma; { binOp Mult l r $startpos $endpos }
| l = expr_no_comma; DIV; r = expr_no_comma; { binOp Div l r $startpos $endpos }
| l = expr_no_comma; MOD; r = expr_no_comma; { binOp Mod l r $startpos $endpos }

| l = expr_no_comma; AND; r = expr_no_comma; { binOp And l r $startpos $endpos }
| l = expr_no_comma; OR; r = expr_no_comma; { binOp Or l r $startpos $endpos }
| NOT; e = expr_no_comma; { unOp Not e $startpos $endpos }

| l = expr_no_comma; LS; r = expr_no_comma; { binOp Less l r $startpos $endpos }
| l = expr_no_comma; GR; r = expr_no_comma; { binOp Greater l r $startpos $endpos }
| l = expr_no_comma; LEQ; r = expr_no_comma; { binOp Leq l r $startpos $endpos }
| l = expr_no_comma; GEQ; r = expr_no_comma; { binOp Geq l r $startpos $endpos }
| l = expr_no_comma; EQ; r = expr_no_comma; { binOp Equal l r $startpos $endpos }
| l = expr_no_comma; NEQ; r = expr_no_comma; { binOp Neq l r $startpos $endpos }

| l = expr_no_comma; BIT_AND; r = expr_no_comma; { binOp Bit_And l r $startpos $endpos }
| l = expr_no_comma; BIT_OR; r = expr_no_comma; { binOp Bit_Or l r $startpos $endpos }
| BIT_NOT; e = expr_no_comma; { unOp Bit_Not e $startpos $endpos }
| l = expr_no_comma; BIT_XOR; r = expr_no_comma; { binOp Bit_Xor l r $startpos $endpos }
| l = expr_no_comma; SHIFT_LEFT; r = expr_no_comma; { binOp Shift_Left l r $startpos $endpos }
| l = expr_no_comma; SHIFT_RIGHT; r = expr_no_comma; { binOp Shift_Right l r $startpos $endpos }

| INCREMENT; e = expr_no_comma; { unOp Pre_Incr e $startpos $endpos } %prec PRE_INCR_DECR
| DECREMENT; e = expr_no_comma; { unOp Pre_Decr e $startpos $endpos } %prec PRE_INCR_DECR
| e = expr_no_comma; INCREMENT; { unOp Post_Incr e $startpos $endpos } %prec POST_INCR_DECR
| e = expr_no_comma; DECREMENT; { unOp Post_Decr e $startpos $endpos } %prec POST_INCR_DECR

| SIZEOF; t = adv_typ; { annotate (SizeOf t) $startpos $endpos }

/* returns a node of type: expr */
let rexpr :=
| e = aexpr; { e }
| fun_id = IDENT; LPAREN; args = fun_args; RPAREN; { annotate (Call (fun_id, args)) $startpos $endpos } %prec FN_CALL /* Function Call*/
| l = lexpr; ASSIGN; r = expr; { assign l r $startpos $endpos } /* Assignment operator */
| l = lexpr; ASSIGN_PLUS; r = expr; { assignBinOp l r Add $startpos $endpos }
| l = lexpr; ASSIGN_MINUS; r = expr; { assignBinOp l r Sub $startpos $endpos }
| l = lexpr; ASSIGN_TIMES; r = expr; { assignBinOp l r Mult $startpos $endpos }
| l = lexpr; ASSIGN_DIV; r = expr; { assignBinOp l r Div $startpos $endpos }
| l = lexpr; ASSIGN_MOD; r = expr; { assignBinOp l r Mod $startpos $endpos }
| l = lexpr; ASSIGN_BIT_AND; r = expr; { assignBinOp l r Bit_And $startpos $endpos }
| l = lexpr; ASSIGN_BIT_OR; r = expr; { assignBinOp l r Bit_Or $startpos $endpos }
| l = lexpr; ASSIGN_BIT_XOR; r = expr; { assignBinOp l r Bit_Xor $startpos $endpos }
| l = lexpr; ASSIGN_SHIFT_LEFT; r = expr; { assignBinOp l r Shift_Left $startpos $endpos }
| l = lexpr; ASSIGN_SHIFT_RIGHT; r = expr; { assignBinOp l r Shift_Right $startpos $endpos }

| PLUS; e = expr; { e } %prec UPLUS
| MINUS; e = expr; { unOp Neg e $startpos $endpos } %prec UMINUS
| l = expr; PLUS; r = expr; { binOp Add l r $startpos $endpos }
| l = expr; MINUS; r = expr; { binOp Sub l r $startpos $endpos }
| l = expr; TIMES; r = expr; { binOp Mult l r $startpos $endpos }
| l = expr; DIV; r = expr; { binOp Div l r $startpos $endpos }
| l = expr; MOD; r = expr; { binOp Mod l r $startpos $endpos }

| l = expr; AND; r = expr; { binOp And l r $startpos $endpos }
| l = expr; OR; r = expr; { binOp Or l r $startpos $endpos }
| NOT; e = expr; { unOp Not e $startpos $endpos }

| l = expr; LS; r = expr; { binOp Less l r $startpos $endpos }
| l = expr; GR; r = expr; { binOp Greater l r $startpos $endpos }
| l = expr; LEQ; r = expr; { binOp Leq l r $startpos $endpos }
| l = expr; GEQ; r = expr; { binOp Geq l r $startpos $endpos }
| l = expr; EQ; r = expr; { binOp Equal l r $startpos $endpos }
| l = expr; NEQ; r = expr; { binOp Neq l r $startpos $endpos }

| l = expr; BIT_AND; r = expr; { binOp Bit_And l r $startpos $endpos }
| l = expr; BIT_OR; r = expr; { binOp Bit_Or l r $startpos $endpos }
| BIT_NOT; e = expr; { unOp Bit_Not e $startpos $endpos }
| l = expr; BIT_XOR; r = expr; { binOp Bit_Xor l r $startpos $endpos }
| l = expr; SHIFT_LEFT; r = expr; { binOp Shift_Left l r $startpos $endpos }
| l = expr; SHIFT_RIGHT; r = expr; { binOp Shift_Right l r $startpos $endpos }

| INCREMENT; e = expr; { unOp Pre_Incr e $startpos $endpos } %prec PRE_INCR_DECR
| DECREMENT; e = expr; { unOp Pre_Decr e $startpos $endpos } %prec PRE_INCR_DECR
| e = expr; INCREMENT; { unOp Post_Incr e $startpos $endpos } %prec POST_INCR_DECR
| e = expr; DECREMENT; { unOp Post_Decr e $startpos $endpos } %prec POST_INCR_DECR

| SIZEOF; t = adv_typ; { annotate (SizeOf t) $startpos $endpos }

/* returns: expr list */
let fun_args :=
| { [] }
| e = expr_no_comma; { [ e ] }
| e = expr_no_comma; COMMA; exprs = fun_args; { e :: exprs }

/* returns a node of type: expr */
let aexpr :=
| ival = INT; { annotate (ILiteral ival) $startpos $endpos }
| cval = CHAR; { annotate (CLiteral cval) $startpos $endpos }
| bval = BOOL; { annotate (BLiteral bval) $startpos $endpos }
| fval = FLOAT; { annotate (FLiteral fval) $startpos $endpos }
| sval = STRING; { annotate (SLiteral sval) $startpos $endpos }
| NULL; { annotate (ILiteral 0) $startpos $endpos }
| LPAREN; e = rexpr; RPAREN; { e }
| "&"; e = lexpr; { annotate (Addr e) $startpos $endpos } %prec ADDR_OF
