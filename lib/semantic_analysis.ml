exception Semantic_error of Location.code_pos * string

open Ast
open Symbol_table

type typ =
    | Int | Float | Bool | Char | Void | Ptr of typ | Array of typ
    | Funct of Ast.identifier | Struct of Ast.identifier
type symbol =
    | StructDef of (typ * Ast.identifier) list
    | FunDef of typ * (typ) list
    | VarDef of typ

let rec is_type_valid typ env =
    match typ with
    | Funct(id) -> Option.is_some (lookup_opt id env)
    | Struct(id) -> Option.is_some (lookup_opt id env)
    | Ptr(typ) -> is_type_valid typ env
    | Array(typ) -> is_type_valid typ env
    | _ -> true

let rec ast_type_to_typ typ =
    match typ with
    | TypI -> Int
    | TypF -> Float
    | TypB -> Bool
    | TypC -> Char
    | TypA(typ, _) -> (Array (ast_type_to_typ typ))
    | TypP(typ) -> (Ptr (ast_type_to_typ typ))
    | TypS(id) -> (Struct id)
    | TypV -> Void

let lookup_fn_def env id =
    match lookup_opt id env with
    | Some(FunDef(ret_typ, arg_def_types)) -> (ret_typ, arg_def_types)
    | Some(_) -> failwith "Is not a function"
    | None -> failwith "Function not defined"
and lookup_var_type env id =
    match lookup_opt id env with
    | Some(VarDef(typ)) -> typ
    | Some(_) -> failwith "Is not a variable"
    | None -> failwith "Variable not defined"
and lookup_struct_def env id =
    match lookup_opt id env with
    | Some(StructDef(fields)) -> fields
    | Some(_) -> failwith "Is not a struct"
    | None -> failwith "Struct not defined"

(* Type Check expression: Ast.expr *)
let rec tc_expr env expr =
    match expr.node with
    | Access(access) -> tc_access env access
    | Assign(access, expr) -> (
        let (env, expr_type) = tc_expr env expr in
        let (env, access_type) = tc_access env access in
        match (expr_type = access_type) with
        | true -> (env, expr_type)
        | false -> failwith "Cannot assign expression to a variable of different type"
    )
    | Addr(access) ->
        let (env, access_type) = tc_access env access in
        (env, Ptr access_type)
    | ILiteral(_) -> (env, Int)
    | FLiteral(_) -> (env, Float)
    | CLiteral(_) -> (env, Char)
    | BLiteral(_) -> (env, Bool)
    | SLiteral(_) -> (env, Ptr Char)
    | UnaryOp(op, expr) -> tc_un_op env op expr
    | BinaryOp(op, lexpr, rexpr) -> tc_bin_op env op lexpr rexpr
    | CommaOp(lexpr, rexpr) -> 
        let (lenv, _) = tc_expr env lexpr in
        tc_expr lenv rexpr
    | Call(id, args) -> tc_fn_call env id args
    | SizeOf(_) -> (env, Int)
    
(* Type Check access expression: Ast.access *)
and tc_access env access =
    match access.node with
    | AccVar(id) -> (env, lookup_var_type env id)
    | AccDeref(expr) -> (
        let (env, expr_type) = tc_expr env expr in
        match expr_type with
        | Ptr(typ) -> (env, typ)
        | _ -> failwith "Deferencing requested on non pointer type"
    )
    | AccIndex(access, expr) -> (
        let (env, access_type) = tc_access env access in
        let (env, expr_type) = tc_expr env expr in
        match (access_type, expr_type) with
        | (Array(typ), Int) -> (env, typ)
        | (Array(_), _) -> failwith "Array access index is not an integer"
        | _ -> failwith "Array access requested on non array type"
    )
    | AccDot(access, field) -> (
        let (env, access_type) = tc_access env access in
        match access_type with
        | Struct(str_id) -> (env, search_field_in_struct env str_id field)
        | _ -> failwith "Dot operator requested on non struct type"
    )
    | AccArrow(expr, field) -> (
        let (env, expr_type) = tc_expr env expr in
        match expr_type with
        | Ptr(Struct(str_id)) -> (env, search_field_in_struct env str_id field)
        | _ -> failwith "Arrow operator requested on non ptr to struct type"
    )
and search_field_in_struct env str_id field =
    let fields = lookup_struct_def env str_id in
    let field_has_name name (_, id) = (id = name) in
    match List.find_opt (field_has_name field) fields with
    | Some((typ, _)) -> typ
    | None -> failwith "The struct definition does not contain the required field"

(* Type Check function call expression *)
and tc_fn_call env fn args =
    let (ret_typ, arg_def_types) = lookup_fn_def env fn in
    let (env, arg_types) = tc_fn_args env args in
    match List.equal (=) arg_def_types arg_types with
    | true -> (env, ret_typ)
    | false -> failwith "Function argument types do not match"
and tc_fn_args env args =
    List.fold_left_map tc_expr env args

(* Type Check unary operation expression *)
and tc_un_op env op expr =
    let (env, expr_type) = tc_expr env expr in
    match op with
    | Pos | Neg ->
        let res = match expr_type with
        | Int | Float | Char | Ptr(_) -> (env, expr_type)
        | _ -> failwith "Unary operator cannot be applied to the expression of type"
        in res
    | Bit_Not -> (
        match expr_type with
        | Int | Char -> (env, expr_type)
        | _ -> failwith "Unary operator cannot be applied to the expression of type"
    )
    | Not ->
        let res = match expr_type with
        | Bool -> (env, expr_type)
        | _ -> failwith "Unary operator cannot be applied to the expression of type"
        in res

(* Type Check binary operation expression *)
and tc_bin_op env op lexpr rexpr =
    let (env, ltype) = tc_expr env lexpr in
    let (env, rtype) = tc_expr env rexpr in
    match op with
    | Add -> (
        match (ltype, rtype) with
        | (Int, Int) | (Float, Float) | (Char, Char) -> (env, ltype)
        | (Ptr(_), Int) -> (env, ltype)
        | (Int, Ptr(_)) -> (env, rtype)
        | _ -> failwith "Binary operator cannot be applied to the expression of type"
    )
    | Sub -> (
        match (ltype, rtype) with
        | (Int, Int) | (Float, Float) | (Char, Char) -> (env, ltype)
        | (Ptr(_), Int) -> (env, ltype)
        | (Ptr(ltyp), Ptr(rtyp)) -> (
            match (ltyp = rtyp) with
            | true -> (env, ltype)
            | false -> failwith "Binary subtraction ptrs must have equal type"
        )
        | _ -> failwith "Binary operator cannot be applied to the expression of type"
    )
    | Mult | Div -> (
        match (ltype, rtype) with
        | (Int, Int) | (Float, Float) | (Char, Char) -> (env, ltype)
        | _ -> failwith "Binary operator cannot be applied to the expression of type"
    )
    | Mod -> (
        match (ltype, rtype) with
        | (Int, Int) | (Char, Char) -> (env, ltype)
        | _ -> failwith "Binary operator cannot be applied to the expression of type"
    )
    | Bit_And | Bit_Or | Bit_Xor
    | Shift_Left | Shift_Right -> (
        match (ltype, rtype) with
        | (Int, Int) | (Char, Char) -> (env, ltype)
        | _ -> failwith "Binary operator cannot be applied to the expression of type"
    )
    | And | Or -> (
        match (ltype, rtype) with
        | (Bool, Bool) -> (env, ltype)
        | _ -> failwith "Binary operator cannot be applied to the expression of type"
    )
    | Equal | Neq
    | Less | Leq
    | Greater | Geq -> (
        match (ltype, rtype) with
        | (Bool, Bool) | (Int, Int) | (Char, Char) | (Float, Float)
        | (Ptr(_), Int) | (Int, Ptr(_)) -> (env, Bool)
        | (Ptr(ltyp), Ptr(rtyp)) -> (
            match (ltyp = rtyp) with
            | true -> (env, Bool)
            | false -> failwith "Binary comparison between ptrs must have equal type"
        )
        | _ -> failwith "Binary operator cannot be applied to the expression of type"
    )

(* Type Check statement or declaration node: Ast.stmtordecl *)
let rec tc_stmt_or_decl env stmt_or_decl =
    match stmt_or_decl.node with
    | Dec(typ, id) -> tc_local_decl env (typ, id)
    | Stmt(stmt) -> tc_stmt env stmt

(* Type Check statement nodes: Ast.stmt *)
and tc_stmt env stmt =
    match stmt.node with
    | If(guard, then_stmt, else_stmt) -> env (* TEMPORARY *)
    | While(guard, stmt) -> env (* TEMPORARY *)
    | Expr(expr) -> env (* TEMPORARY *)
    | Return(expr) -> env (* TEMPORARY *)
    | Block(stmts) -> env (* TEMPORARY *)

(* Type Check local variable declaration: Ast.stmtordecl -> Dec of Ast.typ * Ast.identifier *)
and tc_local_decl env (typ, id) =
    let type_id = ast_type_to_typ typ in
    add_entry id (VarDef type_id) env



(* Type Check whole program declaration: Ast.program *)
let rec tc_program program = 
    let tc_topdecl env decl =
        match decl.node with
        | Fundecl(decl) ->
            let fun_decl = (decl.fname, decl.typ, decl.formals, decl.body) in
            tc_func_def env fun_decl
        | Vardec(typ, id, expr) ->
            tc_var_decl env (typ, id, expr)
        | StructDecl(id, fields) ->
            tc_struct_def env (id, fields)
    in
    (* Program declarations must be reordered to remove the definitions without body *)
    failwith "FIX THIS ISSUE FIRST"
    (* match program with
    | Prog(decls) -> List.fold_left tc_topdecl make_default_env decls *)

(* Type Check variable declaration: Ast.typ * Ast.identifier * Ast.expr option *)
and tc_var_decl env (typ, id, expr) =
    let type_id = ast_type_to_typ typ in
    let tc = match expr with
        | Some(expr) -> snd (tc_expr env expr) = type_id
        | None -> true
    in
    match tc with
        | true -> add_entry id (VarDef type_id) env
        | false -> failwith "Initializer expression does not match variable type"

(* Type Check struct declaration: Ast.identifier * (Ast.typ * Ast.identifier) list *)
and tc_struct_def env (id, fields) =
    let tc_struct_field_def env (fields, is_valid) (typ, id) =
        match is_valid with
        | true ->
            let type_id = ast_type_to_typ typ in
            let res = match is_type_valid type_id env with
            | true -> ( (type_id, id) :: fields, true )
            | false -> (fields, false)
            in res
        | false -> (fields, false)
    in
    match fields with
    | [] -> add_entry id (StructDef []) env
    | _ -> 
        let (fields, is_valid) = List.fold_left (tc_struct_field_def env) ([], true) fields in
        match is_valid with
        | true -> add_entry id (StructDef fields) env
        | false -> failwith "Generic Error"

(* Type Check function declaration: { typ : Ast.typ; fname : string; formals : (Ast.typ * Ast.identifier) list; body : Ast.stmt; } *)
and tc_func_def env (id, ret_typ, formals, body) =
    let tc_func_ret_type env ret_typ =
        let type_id = ast_type_to_typ ret_typ in
        (type_id, is_type_valid type_id env)
    in
    let tc_func_param_def env (formals, is_valid) (typ, id) =
        match is_valid with
        | true ->
            let type_id = ast_type_to_typ typ in
            let res = match is_type_valid type_id env with
            | true -> ( (type_id, id) :: formals, true )
            | false -> (formals, false)
            in res
        | false -> (formals, false)
    in
    let (ret_typ, is_valid) = tc_func_ret_type env ret_typ in
    let (formals, is_valid) = List.fold_left (tc_func_param_def env) ([], is_valid) formals in
    let formal_types = List.map (fun (typ, _) -> typ) formals in
    match is_valid with
    | true -> add_entry id (FunDef (ret_typ, formal_types)) env
    | false -> failwith "Generic Error"

and make_default_env =
    empty_table |>
    add_entry "print" ( FunDef (Void, [Int]) ) |>
    add_entry "getint" ( FunDef (Int, []) )

(* Type Check whole program declaration: Ast.program *)
let type_check program = 
    let _ = tc_program program in
    program