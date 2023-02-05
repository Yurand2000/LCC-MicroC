exception Semantic_error of Location.code_pos * string

open Ast
open Symbol_table
open Sa_local_types
open Sa_environment
open Sa_const_expr_solver

let fmt = Printf.sprintf

(* Helper type to indicate if all the paths in a statement subtree return. *)
type returns = | Returns | NoReturn

(* ************************************************* *)
(* Type Check whole program declaration: Ast.program *)
let rec type_check program =
    let env = tc_program program in
    tc_main_defined program env |>
    solve_const_expressions

(* Check if a correctly defined main function is available. *)
and tc_main_defined program env =
    match lookup_opt "main" env with
    | Some(FunDef(ret_typ, arg_def_types)) -> (
        match (ret_typ, arg_def_types) with
        | (Int, [])
        | (Void, []) -> program
        | (Int, _::_)
        | (Void, _::_) -> raise_error "Main function must have no formal parameters. " None
        | (_, _) -> raise_error "Main function return type must be void or int. " None
    )
    | _ -> raise_error "Main function is not defined. " None

(* Type Check whole program declaration: Ast.program *)
and tc_program program =
    let split_topdecls (vlist, slist, flist) topdecl =
        let loc = topdecl.loc in
        match topdecl.node with
        | Fundecl(decl) -> ( vlist, slist, (decl, loc) :: flist )
        | Vardec(typ, id, expr) -> ( (typ, id, expr, loc) :: vlist, slist, flist )
        | StructDecl(id, fields) -> ( vlist, (id, fields, loc) :: slist, flist )
    in
    match program with
    | Prog(decls) ->
        let (vars, structs, functs) = List.fold_left split_topdecls ([], [], []) decls in
        let env = make_default_env empty_table in
        let env = process_struct_defs env structs in
        let env = process_function_defs env functs in
        let env = process_global_variable_defs env vars in
        let _ = process_function_bodies env functs in env

(* Type Check struct declaration: Ast.identifier * (Ast.typ * Ast.identifier) list *)
and tc_struct_def env (id, fields) loc =
    let tc_struct_field_def env (typ, id) =
        let typ = ast_type_to_typ typ in
        if (is_valid_type typ env) && (is_valid_variable_type typ env) then
            (typ, id)
        else
            raise_error "Struct field type is not valid. " (Some loc)
    in
    let fields = List.map (tc_struct_field_def env) fields in
    add_entry id (StructDef fields) env

(* When processing struct definitions, there might be some recursive definitions.
 * If a struct definition type check fails it may be run again after checking all the others, recursively until a fix point is reached.
 * Reached a fix point either no definitions can be resolved, and so there are some recursive definitions,
 * or all have been resolved and the type checking can continue. *)
and process_struct_defs env defs =
    let process_struct (env, unused) (id, fields, loc) =
        try
            (tc_struct_def env (id, fields) loc, unused)
        with | Semantic_error(_) ->
            (env, (id, fields, loc) :: unused)
    in
    let rec process_defs prec_defs_size env defs =
        let defs_size = Some (List.length defs) in
        match (defs_size, prec_defs_size = defs_size) with
        | (Some(0), _) -> env
        | (_, true) -> raise_error "Some struct definitions are recursive. " None
        | (_, false) -> (
            let (env, unused) = List.fold_left process_struct (env, []) defs in
            process_defs defs_size env unused
        )
    in
    process_defs None env defs

(* Type Check function declaration: { typ : Ast.typ; fname : string; formals : (Ast.typ * Ast.identifier) list; body : Ast.stmt; } *)
and tc_func_decl env (id, ret_typ, formals) loc =
    let ret_typ = tc_func_ret_type env id ret_typ loc in
    let formals = List.map (fun x -> tc_func_param_def env id x loc) formals in
    add_entry id (FunDef (ret_typ, formals)) env
and tc_func_ret_type env fn ret_typ loc =
    let ret_typ = ast_type_to_typ ret_typ in
    if (is_valid_type ret_typ env) && (is_valid_return_type ret_typ env) then
        ret_typ
    else
        raise_error (fmt "Function '%s' return type '%s' is invalid" fn (show_typ ret_typ)) (Some loc)
and tc_func_param_def env fn (typ, id) loc =
    let typ = ast_type_to_typ typ in
    if (is_valid_type typ env) && (is_valid_parameter_type typ env) then
        (typ, id)
    else
        raise_error (fmt "Function '%s' formal parameter '%s' type '%s' is invalid. " fn id (show_typ typ)) (Some loc)

and process_function_defs env defs =
    let process_function env ({typ=ret_typ; fname=id; formals=formals; body=_}, loc) =
        tc_func_decl env (id, ret_typ, formals) loc
    in
    List.fold_left process_function env defs

(* Type Check function body: { typ : Ast.typ; fname : string; formals : (Ast.typ * Ast.identifier) list; body : Ast.stmt; } *)
and tc_func_body env (id, body) loc =
    let add_formals_to_env env (typ, id) = add_entry id (VarDef(typ)) env in

    let (ret_typ, arg_defs) = lookup_function_def env id (Some(loc)) in
    let env = begin_block env in
    let env = List.fold_left add_formals_to_env env arg_defs in
    let returns =
        match body.node with
        | Block(stmts) -> tc_block_stmt env stmts ret_typ
        | _ -> tc_stmt env body ret_typ
    in
    match (ret_typ, returns) with
    | (_, Returns) | (Void, _) -> ()
    | _ -> raise_error (fmt "Function '%s' is missing some return expression. " id) (Some loc)

and process_function_bodies env defs =
    let process_function env ({typ=_; fname=id; formals=_; body=body}, loc) =
        tc_func_body env (id, body) loc
    in
    List.iter (process_function env) defs

(* Type Check variable declaration: Ast.typ * Ast.identifier * Ast.expr option *)
and tc_var_decl env (var_typ, id, expr) loc =
    let var_typ = ast_type_to_typ var_typ in
    if (is_valid_type var_typ env && is_valid_variable_type var_typ env) then
        match Option.map (tc_const_expr env) expr with
        | None ->
            add_entry id (VarDef var_typ) env
        | Some(expr_typ) when are_types_equal var_typ expr_typ ->
            add_entry id (VarDef var_typ) env
        | Some(expr_typ) ->
            raise_error (fmt (
                "Initializer expression for global variable does not match variable type. "
                ^^ "The variable type is '%s' and the expression type is '%s'.") (show_typ var_typ) (show_typ expr_typ)
            ) (Some loc)
    else
        raise_error (fmt "Invalid type '%s' for global variable '%s'." (show_typ var_typ) id) (Some loc)

and process_global_variable_defs env defs =
    let process_variable env (typ, id, expr, loc) =
        tc_var_decl env (typ, id, expr) loc
    in
    List.fold_left process_variable env defs

(* ************************************************* *)
(* Type Check statement nodes: Ast.stmt *)
and tc_stmt env stmt ret_typ =
    let loc = stmt.loc in
    match stmt.node with
    | If(guard, then_stmt, else_stmt) -> (
        let guard_typ = tc_expr env guard in
        match guard_typ with
        | Bool -> (
            let then_returns = tc_stmt env then_stmt ret_typ in
            let else_returns = tc_stmt env else_stmt ret_typ in
            match (then_returns, else_returns) with
            | (Returns, Returns) -> Returns
            | _ -> NoReturn
        )
        | typ -> raise_error (fmt "If guard expression type must be a boolean. The expression type is: '%s'." (show_typ typ)) (Some loc)
    )
    | While(guard, stmt) -> (
        let guard_typ = tc_expr env guard in
        match guard_typ with
        | Bool ->
            let _ = tc_stmt env stmt ret_typ in NoReturn
        | typ -> raise_error (fmt "While guard expression type must be a boolean. The expression type is: '%s'." (show_typ typ)) (Some loc)
    )
    | Expr(expr) ->
        let _ = tc_expr env expr in NoReturn
    | Return(expr) -> (
        match expr with
        | Some(expr) -> (
            let expr_typ = tc_expr env expr in
            match can_be_implicitly_casted ret_typ expr_typ with
            | true -> Returns
            | false -> raise_error (fmt ("Return expression type must match the function return type. "
                ^^ "The exprected return type is '%s' and the expression type is: '%s'.") (show_typ ret_typ) (show_typ expr_typ)) (Some loc)
        )
        | None -> (
            match ret_typ with
            | Void -> Returns
            | _ -> raise_error (fmt ("Return expression type must match the function return type. "
                ^^ "The exprected return type is '%s' and the expression type is: '%s'.") (show_typ ret_typ) (show_typ Void)) (Some loc)
        )
    )
    | Block(stmts) -> (
        let env = begin_block env in
        tc_block_stmt env stmts ret_typ
    )
and tc_block_stmt env stmts ret_typ =
    let check_stmt (env, returns) stmt =
        let loc = stmt.loc in
        match returns with
        | Returns -> raise_error "Dead code detected: return expression cannot be followed by any command. " (Some loc)
        | NoReturn -> tc_stmt_or_decl env stmt ret_typ
    in
    let (_, returns) = List.fold_left check_stmt (env, NoReturn) stmts in returns

(* Type Check statement or declaration node: Ast.stmtordecl *)
and tc_stmt_or_decl env stmt_or_decl ret_typ =
    match stmt_or_decl.node with
    | Dec(typ, id) -> tc_local_decl env (typ, id) stmt_or_decl.loc
    | Stmt(stmt) -> (env, tc_stmt env stmt ret_typ)

(* Type Check local variable declaration: Ast.stmtordecl -> Dec of Ast.typ * Ast.identifier *)
and tc_local_decl env (var_typ, id) loc =
    let var_typ = ast_type_to_typ var_typ in
    if (is_valid_type var_typ env && is_valid_variable_type var_typ env) then
        (add_entry id (VarDef var_typ) env, NoReturn)
    else
        raise_error (fmt "Invalid type '%s' for local variable '%s'." (show_typ var_typ) id ) (Some loc)

(* ************************************************* *)
(* Type Check expression: Ast.expr *)
and tc_expr env expr =
    let loc = expr.loc in
    match expr.node with
    | ILiteral(_) | FLiteral(_) | CLiteral(_)
    | BLiteral(_) | SLiteral(_) | SizeOf(_) ->
        tc_const_expr env expr
    | Access(access) -> tc_access env access
    | Assign(access, expr) -> (
        let access_type = tc_access env access in
        if is_valid_lexpr_type access_type env then
            let expr_type = tc_expr env expr in
            match (can_be_implicitly_casted access_type expr_type) with
            | true -> access_type
            | false -> raise_error (fmt "Cannot assign expression of type '%s' to a variable of type '%s'."
                (show_typ expr_type) (show_typ access_type)) (Some expr.loc)
        else 
            raise_error (fmt "Variables of type '%s' are not assignable." (show_typ access_type)) (Some expr.loc)
    )
    | Addr(access) ->
        (Ptr (tc_access env access))
    | UnaryOp(op, expr) -> tc_unary_op env tc_expr op expr loc
    | BinaryOp(op, lexpr, rexpr) -> tc_binary_op env tc_expr op lexpr rexpr loc
    | CommaOp(lexpr, rexpr) ->
        let _ = tc_expr env lexpr in
        tc_expr env rexpr
    | Call(id, args) -> tc_function_call env id args loc
    | Cast(typ, expr) -> tc_cast_expr env typ expr loc

(* Type Check expression as const expression: Ast.expr *)
and tc_const_expr env expr =
    let loc = expr.loc in
    match expr.node with
    | ILiteral(value) -> (
        match is_int_literal_valid value with
        | true -> Int
        | false -> raise_error "Integer literal is out of range." (Some loc)
    )
    | FLiteral(_) -> Float
    | CLiteral(_) -> Char
    | BLiteral(_) -> Bool
    | SLiteral(_) -> Ptr Char
    | SizeOf(_) -> Int
    | UnaryOp(op, expr) -> tc_unary_op env tc_const_expr op expr loc
    | BinaryOp(op, lexpr, rexpr) -> tc_binary_op env tc_const_expr op lexpr rexpr loc
    | _ -> raise_error "Given expression of type cannot be const evaluated." (Some loc)
and is_int_literal_valid value =
    (value <= 2147483647) && (value >= -2147483648)

(* Type Check access expression: Ast.access *)
and tc_access env access =
    let loc = access.loc in
    match access.node with
    | AccVar(id) ->
        lookup_var_type env id (Some loc)
    | AccDeref(expr) -> (
        match tc_expr env expr with
        | Ptr(typ) -> typ
        | typ -> raise_error (fmt "Deferencing requires a pointer type. The expression type is: '%s'." (show_typ typ)) (Some loc)
    )
    | AccIndex(access, expr) -> (
        match (tc_access env access, tc_expr env expr) with
        | (Ptr(Void), Int) -> raise_error "Void pointer cannot be array accessed." (Some loc)
        | (Array(typ, _), Int) | (Ptr(typ), Int) -> typ
        | (Array(_), typ) -> raise_error (fmt "Array access index is not an integer. The index expression type is: '%s'." (show_typ typ)) (Some loc)
        | (typ, _) -> raise_error (fmt "Array access requires an array or pointer type. The expression type is: '%s'." (show_typ typ))  (Some loc)
    )
    | AccStruct(access, field) -> (
        match tc_access env access with
        | Struct(str_id) -> search_field_in_struct env str_id field loc
        | typ -> raise_error (fmt "Dot operator requires a struct type. The expression type is: '%s'." (show_typ typ)) (Some loc)
    )
and search_field_in_struct env str_id field loc =
    let fields = lookup_struct_def env str_id (Some(loc)) in
    let field_has_name name (_, id) = (id = name) in
    match List.find_opt (field_has_name field) fields with
    | Some((typ, _)) -> typ
    | None -> raise_error (fmt "The struct '%s' does not contain the field '%s'." str_id field) (Some loc)

(* Type Check function call expression *)
and tc_function_call env fn args loc =
    let (ret_typ, arg_defs) = lookup_function_def env fn (Some(loc)) in
    let arg_types = tc_function_args env args in
    let check_function_args argnum (def_type, _) arg_type =
        if can_be_implicitly_casted def_type arg_type then
            argnum + 1
        else
            raise_error (fmt ("Call of fn '%s', argument #%d types do not match and the provided argument cannot be implicitly casted"
                ^^ ": definition type is '%s', argument type is '%s'.") fn argnum (show_typ def_type) (show_typ arg_type)) (Some loc)
    in
    if (List.length arg_defs) = (List.length arg_types) then
        let _ = List.fold_left2 check_function_args 0 arg_defs arg_types in
        ret_typ
    else
        raise_error (fmt "Call of fn '%s', number of provided arguments does not match the number of formal parameters." fn) (Some loc)
and tc_function_args env args =
    List.map (tc_expr env) args

(* Type Check cast expression *)
and tc_cast_expr env typ expr loc =
    let expr_type = tc_expr env expr in
    let cast_type = ast_type_to_typ typ in
    match (cast_type, expr_type) with
    | (Int, Float) | (Float, Int)
    | (Int, Ptr(_)) | (Ptr(_), Int)
    | (Ptr(_), Ptr(Void)) | (Ptr(Void), Ptr(_)) ->
        cast_type
    | (Ptr(ctyp), Array(atyp, _)) when are_types_equal ctyp atyp ->
        cast_type
    | (ctyp, typ) when are_types_equal ctyp typ ->
        cast_type
    | _ -> raise_error (fmt "Cast of expression of type '%s' to type '%s' cannot be performed. " (show_typ expr_type) (show_typ cast_type)) (Some loc)

(* Type Check unary operation expression *)
and tc_unary_op env tc_fn op expr loc =
    let expr_type = tc_fn env expr in
    let raise_un_op_error () = raise_error (fmt "Unary operator '%s' cannot be applied to the expression of type '%s'."
        (Ast.show_uop op) (show_typ expr_type)) (Some loc)
    in
    match op with
    | Pos | Neg -> (
        match expr_type with
        | Int | Float | Char -> expr_type
        | _ -> raise_un_op_error ()
    )
    | Bit_Not -> (
        match expr_type with
        | Int | Char -> expr_type
        | _ -> raise_un_op_error ()
    )
    | Not -> (
        match expr_type with
        | Bool -> expr_type
        | _ -> raise_un_op_error ()
    )

(* Type Check binary operation expression *)
and tc_binary_op env tc_fn op lexpr rexpr loc =
    let ltype = tc_fn env lexpr in
    let rtype = tc_fn env rexpr in
    let raise_bin_op_error () = raise_error (fmt "Binary operator '%s' cannot be applied to expressions of type '%s' and '%s'."
        (Ast.show_binop op) (show_typ ltype) (show_typ rtype) ) (Some loc)
    in
    match op with
    | Add -> (
        match (ltype, rtype) with
        | (Int, Int) | (Float, Float) | (Char, Char) -> ltype
        | (Ptr(_), Int) -> ltype
        | (Int, Ptr(_)) -> rtype
        | _ -> raise_bin_op_error ()
    )
    | Sub -> (
        match (ltype, rtype) with
        | (Int, Int) | (Float, Float) | (Char, Char) -> ltype
        | (Ptr(_), Int) -> ltype
        | (Ptr(ltyp), Ptr(rtyp)) -> (
            match (are_types_equal ltyp rtyp) with
            | true -> ltype
            | false -> raise_error (fmt ("Binary subtraction between pointers must have equal types."
                ^^ " The two pointers have types '%s' and '%s'. ") (show_typ ltype) (show_typ rtype)) (Some loc)
        )
        | _ -> raise_bin_op_error ()
    )
    | Mult | Div -> (
        match (ltype, rtype) with
        | (Int, Int) | (Float, Float) -> ltype
        | _ -> raise_bin_op_error ()
    )
    | Mod -> (
        match (ltype, rtype) with
        | (Int, Int) -> ltype
        | _ -> raise_bin_op_error ()
    )
    | Bit_And | Bit_Or | Bit_Xor
    | Shift_Left | Shift_Right -> (
        match (ltype, rtype) with
        | (Int, Int) -> ltype
        | _ -> raise_bin_op_error ()
    )
    | And | Or -> (
        match (ltype, rtype) with
        | (Bool, Bool) -> ltype
        | _ -> raise_bin_op_error ()
    )
    | Equal | Neq -> (
        match (ltype, rtype) with
        | (Bool, Bool) | (Int, Int) | (Char, Char) | (Float, Float)
        | (Ptr(_), Int) | (Int, Ptr(_)) -> Bool
        | (Ptr(ltyp), Ptr(rtyp)) -> (
            match (are_types_equal ltyp rtyp) with
            | true -> Bool
            | false -> raise_error (fmt ("Binary comparison between pointers must have equal types."
                ^^ " The two pointers have types '%s' and '%s'. ") (show_typ ltype) (show_typ rtype)) (Some loc)
        )
        | _ -> raise_bin_op_error ()
    )
    | Less | Leq
    | Greater | Geq -> (
        match (ltype, rtype) with
        | (Int, Int) | (Char, Char) | (Float, Float)
        | (Ptr(_), Int) | (Int, Ptr(_)) -> Bool
        | (Ptr(ltyp), Ptr(rtyp)) -> (
            match (are_types_equal ltyp rtyp) with
            | true -> Bool
            | false -> raise_error (fmt ("Binary comparison between pointers must have equal types."
                ^^ " The two pointers have types '%s' and '%s'. ") (show_typ ltype) (show_typ rtype)) (Some loc)
        )
        | _ -> raise_bin_op_error ()
    )