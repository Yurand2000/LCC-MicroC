/*
* MicroC Parser specification
*/

%{
  open Ast
  open List

  (* Auxiliary function to create annotated nodes *)
  let annotate node (lstart, lend) = {
    node = node;
    loc = Location.to_code_position (lstart, lend);
  }

  (* Empty Block *)
  let empty_block loc = annotate (Block []) loc

  (* Auxiliary type for Variable Declarators in multi declaration lines *)
  (* From https://en.cppreference.com/w/c/language/declarations *)
  type variable_declarator =
  | Id of string
  | Ptr of variable_declarator
  | Array of variable_declarator
  | ArrayNum of variable_declarator * int

  (* Type and Variable Declarator to (type * identifier) pair *)
  let rec to_typ_id typ desc =
    match desc with
    | Id id -> (typ, id)
    | Ptr decl -> to_typ_id (TypP typ) decl
    | Array decl -> to_typ_id (TypA (typ, None)) decl
    | ArrayNum (decl, size) -> to_typ_id (TypA (typ, Some size)) decl

  (* Given a local variable declaration, generates the nodes to declare and optionally initialize the variable. *)
  (* returns: stmtordec list*)
  let local_vardecl_builder (decl, expr) =
    let ((typ, desc), decl_loc) = decl in
    let variable_declaration = annotate (Dec (typ, desc)) decl_loc in
    let initializer_expr = Option.map (
        fun (expr, expr_loc) -> 
        let loc = (fst(decl_loc), snd(expr_loc)) in
        let access = annotate (AccVar desc) decl_loc in
        let assign = annotate (Assign (access, expr)) loc in
        let stmt = annotate (Expr assign) loc in
        annotate (Stmt stmt) loc
      ) expr
    in
    variable_declaration :: (Option.to_list initializer_expr)

  (* Operator expressions builders *)
  let unOp op e loc =
    annotate (UnaryOp (op, e)) loc
  let binOp op l r loc =
    annotate (BinaryOp (op, l, r)) loc

  (* Access and assign expressions builders *)
  let access l loc =
    annotate (Access l) loc
  let assign l r loc =
    annotate (Assign (l, r)) loc
  let assignBinOp l r op loc =
    let lvalue = access l loc in
    let op = binOp op lvalue r loc in
    assign l op loc
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
%token SEMICOLON ";" COMMA "," DOT "." ARROW "->"
%token LPAREN "(" RPAREN ")"
%token LSQR_BRACKET "[" RSQR_BRACKET "]"
%token LBRACE "{" RBRACE "}"
%token EOF

/* ------------------------------------------ */
/* Precedence and associativity specification */
/* Adapted from https://en.cppreference.com/w/c/language/operator_precedence */
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
%right PRE_INCR_DECR UPLUS UMINUS NOT BIT_NOT DEREF ADDR_OF SIZEOF
%left POST_INCR_DECR FN_CALL ARRAY_SUBSCRIPT STRUCT_ACCESS

%left DOT ARROW
%left INCREMENT DECREMENT
%left LPAREN RPAREN LSQR_BRACKET RSQR_BRACKET LBRACE RBRACE

/* ------------------------------------------ */
/* Starting symbol */

%start program
%type <Ast.program> program    /* the parser returns a Ast.program value */

%%

/* ------------------------------------------ */
/* Grammar specification */
/* Program, returns a node of type: program */
let program :=
  | decls = flatten(list(topdecl)); EOF; { Prog(decls) }

/* Top declaration, returns: topdecl list */
let topdecl :=
  // Global variable(s) declaration(s)
  | v_decls = var_definition; SEMICOLON;
    {
      let builder (decl, expr) =
        let ((typ, desc), decl_loc) = decl in
        match expr with
        | Some(expr, expr_loc) -> annotate (Vardec (typ, desc, Some(expr))) (fst(decl_loc), snd(expr_loc))
        | None -> annotate (Vardec (typ, desc, None)) decl_loc
      in
      List.map builder v_decls
    }

  // Function definition
  | f_decl = fundecl;
    { [ annotate (Fundecl f_decl) $loc ] }

  // Struct declaration
  | s_decl = struct_declaration;
    {
      let (id, fields) = s_decl in
      [ annotate (StructDecl(id, fields)) $loc ]
    }

/* ------------------------------------------ */
/* Struct declaration, returns: identifier * (typ * identifier) list */
let struct_declaration :=
  | STRUCT; name = IDENT; "{"; fields = flatten(nonempty_list(struct_field_definition)); "}";
  { (name, fields) }
let struct_field_definition := // Struct field, returns: (typ * identifier) list
  | typ = typ; descs = separated_nonempty_list(COMMA, var_declarator); SEMICOLON;
  { List.map (to_typ_id typ) descs }

/* ------------------------------------------ */
/* Variable declaration and definition, for both global and local variables. */
/* returns: ( ((typ * identifier) * location) * ((expr * location) option) ) list */
let var_definition :=
  | typ = typ; descs = separated_nonempty_list(COMMA, var_declaration_or_definition);
    {
      let builder (desc, expr) =
        let (desc, desc_loc) = desc in
        let (typ, desc) = to_typ_id typ desc in
        ( ((typ, desc), desc_loc), expr )
      in
      List.map builder descs
    }
let var_declaration_or_definition := // returns: (variable_declarator * location) * ((expr * location) option)
  | desc = var_declarator; { ( (desc, $loc(desc)), None ) }
  | desc = var_declarator; ASSIGN; e = expr_nc; { ( (desc, $loc(desc)), Some(e, $loc(e)) ) }

/* ------------------------------------------ */
/* Variable Declarator (as seen in a multi line definition/declaration), returns: variable_declarator */
let var_declarator :=
  | "*"; desc = var_declarator; { Ptr desc } //Pointer
  | desc = var_declarator_noptr; { desc } //Non-Pointer Declaration
let var_declarator_noptr :=
  | id = IDENT; { Id id } //Identifier
  | "("; desc = var_declarator; ")"; { desc }
  | desc = var_declarator_noptr; "["; "]"; { Array desc } //Array (without size)
  | desc = var_declarator_noptr; "["; size = INT; "]"; { ArrayNum (desc, size) } //Array (with size)

/* ------------------------------------------ */
/* Function declaration, returns: fun_decl */
let fundecl :=
  | ret_typ = typ; fname = var_declarator; "("; args = separated_list(COMMA, funarg); ")"; body = block;
    {
      let (ret_typ, fname) = to_typ_id ret_typ fname in
      { typ = ret_typ; fname = fname; formals = args; body = Some(body); }
    }
  | ret_typ = typ; fname = var_declarator; "("; args = separated_list(COMMA, funarg); ")"; SEMICOLON;
    {
      let (ret_typ, fname) = to_typ_id ret_typ fname in
      { typ = ret_typ; fname = fname; formals = args; body = None; }
    } 
let funarg := // returns: typ * identifier
  | typ = typ; desc = var_declarator; { to_typ_id typ desc }

/* ------------------------------------------ */
/* Types, without pointers and arrays, returns a node of type: typ */
let typ :=
  | TINT; { TypI }
  | TCHAR; { TypC }
  | TFLOAT; { TypF }
  | TVOID; { TypV }
  | TBOOL; { TypB }
  | STRUCT; struct_name = IDENT; { TypS struct_name }
let cast_typ := // pointers
  | t = typ; { t }
  | t = cast_typ; "*"; { TypP t } //Pointer of type
let sizeof_typ := // pointers and arrays
  | t = typ; { t }
  | t = sizeof_typ; "*"; { TypP t } //Pointer of type
  | t = sizeof_typ; "["; i = INT; "]"; { TypA (t, Some(i)) } //Array of type

/* ------------------------------------------ */
/* Single Line Statement, returns a node of type: stmt */
/* These are the statements that can be used inside if, while and for bodies without opening a scope. */
let single_line_stmt :=
  | RETURN; e = expr?; SEMICOLON; { annotate (Return e) $loc } //Return expression
  | e = expr; SEMICOLON; { annotate (Expr e) $loc } //Generic expression

/* Block, returns a node of type: stmt */
let block :=
  | "{"; block = flatten(list(stmt_or_decl)); "}";
    { annotate (Block block) $loc }
let stmt_or_decl := // Block statement or declaration, returns: stmtordec list
  | stmt = stmt;
    { [ annotate (Stmt stmt) $loc ] }
  | var_definitions = var_definition; SEMICOLON;
    { List.flatten (List.map local_vardecl_builder var_definitions) }

/* Statements, returns a node of type: stmt */
let stmt :=
  | stmt = single_line_stmt; { stmt }
  | stmt = block; { stmt }
  | if_stmt = if_stmt; { if_stmt } //If statements
  | while_stmt = while_stmt; { while_stmt } //While and Do While statements
  | for_stmt = for_stmt; { for_stmt; } //For statements

/* ------------------------------------------ */
/* If statement, returns a node of type: stmt */
let if_stmt :=
  | IF; g = if_guard; b = if_body; //If then
    {
      let empty_block = (empty_block ($endpos, $endpos)) in
      annotate (If (g, b, empty_block)) $loc
    }
  | IF; g = if_guard; then_b = if_body; ELSE; else_b = if_body; //If then else
    {
      annotate (If (g, then_b, else_b)) $loc
    }
  | IF; g = if_guard; then_b = if_body; ELSE; elif_b = if_stmt; //If then else if
    {
      annotate (If (g, then_b, elif_b)) $loc
    }
let if_guard :=
  | "("; e = expr; ")"; { e }
let if_body :=
  | stmt = single_line_stmt; { stmt }
  | stmt = block; { stmt }

/* ------------------------------------------ */
/* While statements, returns a node of type: stmt */
let while_stmt :=
  // While statement
  | WHILE; guard = if_guard; body = stmt;
    { annotate (While (guard, body)) $loc }
  // Do While statement
  // A DoWhile statement is compiled as a while statement, where the guard is computed as the
  // last command in the while body, outside of its scope, and the initial value of the guard is true.
  // The names introduced in the while's body scope cannot be used in the guard.
  | DO; body = stmt; WHILE; guard = if_guard; SEMICOLON;
  {
    let guard_var_name = "0_do_while_guard" in (* names starting with digits cannot conflict with any variable name *)
    let bool_true = annotate (BLiteral true) $loc(guard) in
    let guard_access = annotate (AccVar guard_var_name) $loc(guard) in
    let guard_expr = annotate (Access guard_access) $loc(guard) in
    let guard_init = annotate (Assign(guard_access, bool_true)) $loc(guard) in
    let guard_init = annotate (Expr guard_init) $loc(guard) in

    let guard_assign = annotate (Assign(guard_access, guard)) $loc(guard) in
    let guard_assign = annotate (Expr guard_assign) $loc(guard) in
    let while_body =
      annotate (Block [
        annotate (Stmt body) $loc(body);
        annotate (Stmt guard_assign) $loc(guard)
      ]) $loc
    in
    let while_stmt = annotate (While (guard_expr, while_body)) $loc in
    annotate (Block [
      annotate (Dec(TypB, guard_var_name)) $loc(guard);
      annotate (Stmt guard_init) $loc(guard);
      annotate (Stmt while_stmt) $loc(body)
    ]) $loc
  }

/* ------------------------------------------ */
/* For statement, returns a node of type: stmt */
/* A for statement is translated as a while statement, where the initialization is executed before the loop.
 * The increment expression is executed after the while body executed, outside of its scope. */
let for_stmt :=
  | FOR; "("; init = for_init; SEMICOLON; guard = for_guard; SEMICOLON; incr = expr?; ")"; body = stmt;
    {
      let body = 
        match incr with
        | Some e ->
          let incr = annotate (Expr e) $loc(incr) in
          let incr = annotate (Stmt incr) $loc(incr) in
          let body = annotate (Stmt body) $loc(body) in
          annotate (Block [ body; incr ]) $loc(body)
        | None -> body
      in
      let while_stmt = annotate (While (guard, body)) $loc in
      let while_stmt = annotate (Stmt while_stmt) $loc in
      annotate (Block (List.append init [while_stmt])) $loc
    }
let for_init := // returns a list of stmtordecl nodes
  | { [] }
  | vardecl = var_definition;
    { List.concat (List.map local_vardecl_builder vardecl) }
  | expr = expr;
    {
      let expr = annotate (Expr expr) $loc in
      [ annotate (Stmt expr) $loc ]
    }
let for_guard := // returns a node of type: expr
  | { annotate (BLiteral true) $loc }
  | guard = expr; { guard }

/* ------------------------------------------ */
/* Expression with comma operator, returns a node of type: expr */
let expr :=
  | e = rexpr(expr); { e } //RExpression
  | e = lexpr; { annotate (Access e) $loc } //Access to a LExpression
  | e1 = expr; COMMA; e2 = expr; { annotate (CommaOp (e1, e2)) $loc } //Comma Operator

/* Expression without comma operator (used for function call arguments), returns a node of type: expr */
let expr_nc :=
  | e = rexpr(expr_nc); { e } //RExpression
  | e = lexpr; { annotate (Access e) $loc } //Access to a LExpression
  | "("; e1 = expr; COMMA; e2 = expr; ")"; { annotate (CommaOp (e1, e2)) $loc } //Comma Operator only if between parenthesis

/* LExpression, returns a node of type: access */
let lexpr :=
  | "("; e = lexpr; ")"; { e }//Parenthesis
  | id = IDENT; { annotate (AccVar id) $loc } //Identifier access

  // Dereferencing
  | "*"; e = lexpr;
    {
      let e = annotate (Access e) $loc in
      annotate (AccDeref e) $loc
    } %prec DEREF
  | "*"; e = aexpr;
    {
      annotate (AccDeref e) $loc
    } %prec DEREF
  
  // Array/Pointer Access
  | e = lexpr; "["; index = expr; "]";
    {
      annotate (AccIndex (e, index)) $loc
    } %prec ARRAY_SUBSCRIPT
  | e = aexpr; "["; index = expr; "]";
    {
      let p = annotate (AccDeref e) $loc in
      annotate (AccIndex (p, index)) $loc
    } %prec ARRAY_SUBSCRIPT
 
  // Struct Access
  | e = lexpr; DOT; field = IDENT;
    {
      annotate (AccStruct (e, field)) $loc
    } %prec STRUCT_ACCESS

  // Struct Dereferencing Access
  | e = lexpr; ARROW; field = IDENT;
    {
      let e = annotate (Access e) $loc in
      let p = annotate (AccDeref e) $loc in
      annotate (AccStruct (p, field)) $loc
    } %prec STRUCT_ACCESS
  | e = aexpr; ARROW; field = IDENT;
    {
      let p = annotate (AccDeref e) $loc in
      annotate (AccStruct (p, field)) $loc
    } %prec STRUCT_ACCESS

/* RExpression, parametrized on the expression nonterminal symbol, returns a node of type: expr */
/* The parametrization is needed to identify the two cases where Comma Operators may occur:
 * comma operators occur differently inside any command than inside function calls arguments. */
let rexpr(expr_sym) :=
  | e = aexpr; { e } //AExpression is RExpression

  //Function call
  | fun_id = IDENT; "("; args = separated_list(COMMA, expr_nc); ")";
    {
      annotate (Call (fun_id, args)) $loc
    } %prec FN_CALL

  // Assignment operators
  | l = lexpr; ASSIGN; r = expr_sym; { assign l r $loc }
  | l = lexpr; ASSIGN_PLUS; r = expr_sym; { assignBinOp l r Add $loc }
  | l = lexpr; ASSIGN_MINUS; r = expr_sym; { assignBinOp l r Sub $loc }
  | l = lexpr; ASSIGN_TIMES; r = expr_sym; { assignBinOp l r Mult $loc }
  | l = lexpr; ASSIGN_DIV; r = expr_sym; { assignBinOp l r Div $loc }
  | l = lexpr; ASSIGN_MOD; r = expr_sym; { assignBinOp l r Mod $loc }
  | l = lexpr; ASSIGN_BIT_AND; r = expr_sym; { assignBinOp l r Bit_And $loc }
  | l = lexpr; ASSIGN_BIT_OR; r = expr_sym; { assignBinOp l r Bit_Or $loc }
  | l = lexpr; ASSIGN_BIT_XOR; r = expr_sym; { assignBinOp l r Bit_Xor $loc }
  | l = lexpr; ASSIGN_SHIFT_LEFT; r = expr_sym; { assignBinOp l r Shift_Left $loc }
  | l = lexpr; ASSIGN_SHIFT_RIGHT; r = expr_sym; { assignBinOp l r Shift_Right $loc }

  //Arithmetic Operators
  | PLUS; e = expr_sym; { e } %prec UPLUS
  | MINUS; e = expr_sym; { unOp Neg e $loc } %prec UMINUS
  | l = expr_sym; PLUS; r = expr_sym; { binOp Add l r $loc }
  | l = expr_sym; MINUS; r = expr_sym; { binOp Sub l r $loc }
  | l = expr_sym; TIMES; r = expr_sym; { binOp Mult l r $loc }
  | l = expr_sym; DIV; r = expr_sym; { binOp Div l r $loc }
  | l = expr_sym; MOD; r = expr_sym; { binOp Mod l r $loc }

  //Logic Operators
  | l = expr_sym; AND; r = expr_sym; { binOp And l r $loc }
  | l = expr_sym; OR; r = expr_sym; { binOp Or l r $loc }
  | NOT; e = expr_sym; { unOp Not e $loc }

  //Comparison Operators
  | l = expr_sym; LS; r = expr_sym; { binOp Less l r $loc }
  | l = expr_sym; GR; r = expr_sym; { binOp Greater l r $loc }
  | l = expr_sym; LEQ; r = expr_sym; { binOp Leq l r $loc }
  | l = expr_sym; GEQ; r = expr_sym; { binOp Geq l r $loc }
  | l = expr_sym; EQ; r = expr_sym; { binOp Equal l r $loc }
  | l = expr_sym; NEQ; r = expr_sym; { binOp Neq l r $loc }

  //Bitwise Operators
  | l = expr_sym; BIT_AND; r = expr_sym; { binOp Bit_And l r $loc }
  | l = expr_sym; BIT_OR; r = expr_sym; { binOp Bit_Or l r $loc }
  | BIT_NOT; e = expr_sym; { unOp Bit_Not e $loc }
  | l = expr_sym; BIT_XOR; r = expr_sym; { binOp Bit_Xor l r $loc }
  | l = expr_sym; SHIFT_LEFT; r = expr_sym; { binOp Shift_Left l r $loc }
  | l = expr_sym; SHIFT_RIGHT; r = expr_sym; { binOp Shift_Right l r $loc }

  //Prefix increment / decrement
  | INCREMENT; e = lexpr;
    {
      let one_expr = annotate (ILiteral 1) $loc in
      assignBinOp e one_expr Add $loc
    } %prec PRE_INCR_DECR
  | DECREMENT; e = lexpr;
    {
      let one_expr = annotate (ILiteral 1) $loc in
      assignBinOp e one_expr Sub $loc
    } %prec PRE_INCR_DECR

  //Postfix increment / decrement
  | e = lexpr; INCREMENT;
    {
      let one_expr = annotate (ILiteral 1) $loc in
      let incr = assignBinOp e one_expr Add $loc in
      binOp Sub incr one_expr $loc
    } %prec POST_INCR_DECR
  | e = lexpr; DECREMENT;
    {
      let one_expr = annotate (ILiteral 1) $loc in
      let decr = assignBinOp e one_expr Sub $loc in
      binOp Add decr one_expr $loc
    } %prec POST_INCR_DECR

  //SizeOf operator
  | SIZEOF; "("; t = sizeof_typ; ")"; { annotate (SizeOf t) $loc }
  | "("; t = cast_typ; ")"; expr = expr_sym; { annotate (Cast (t, expr)) $loc }

/* ------------------------------------------ */
/* AExpression, returns a node of type: expr */
let aexpr :=
  | ival = INT; { annotate (ILiteral ival) $loc }
  | cval = CHAR; { annotate (CLiteral cval) $loc }
  | bval = BOOL; { annotate (BLiteral bval) $loc }
  | fval = FLOAT; { annotate (FLiteral fval) $loc }
  | sval = STRING; { annotate (SLiteral sval) $loc }
  | NULL; { annotate (ILiteral 0) $loc }
  | "("; e = rexpr(expr); ")"; { e }
  | "&"; e = lexpr; { annotate (Addr e) $loc } %prec ADDR_OF
