exception Semantic_error of Location.code_pos * string

open Ast
open Symbol_table

type typ =
    | Int | Float | Bool | Char | Void | Ptr of typ | Array of typ * int option
    | Struct of Ast.identifier

let rec show_typ typ =
    match typ with
    | Int -> "int"
    | Float -> "float"
    | Bool -> "bool"
    | Char -> "char"
    | Void -> "void"
    | Ptr(typ) -> "(* " ^ show_typ typ ^ ")"
    | Array(typ, _) -> "(" ^ show_typ typ ^ "[])"
    | Struct(id) -> "(struct " ^ id ^ ")"

type symbol =
    | StructDef of (typ * Ast.identifier) list
    | FunDef of typ * (typ * Ast.identifier) list
    | VarDef of typ

let rec is_valid_type typ env =
    match typ with
    | Struct(id) -> Option.is_some (lookup_opt id env)
    | Ptr(typ) -> is_valid_type typ env
    | Array(typ, size) ->
        (Option.fold ~none:true ~some:(fun s -> s > 0) size) &&
        (is_valid_type typ env)
    | _ -> true
and is_valid_variable_type typ _env =
    match typ with
    | Void -> false
    | Array(typ, size) -> (
        (Option.fold ~none:true ~some:(fun s -> s > 0) size) &&
        (is_valid_variable_type typ _env)
    )
    | Ptr(typ) -> is_valid_parameter_type typ _env
    | _ -> true
and is_valid_return_type typ _env =
    match typ with
    | Array(_) -> false
    | Ptr(typ) -> is_valid_parameter_type typ _env
    | _ -> true
and is_valid_parameter_type typ _env =
    match typ with
    | Void -> false
    | Array(typ, size) -> (
        match Option.is_none size with
        | true -> is_valid_parameter_type typ _env
        | false -> false
    )
    | Ptr(typ) -> is_valid_parameter_type typ _env
    | _ -> true
and is_valid_lexpr_type typ _env =
    match typ with
    | Void | Array(_) | Struct(_) -> false
    | _ -> true
and are_types_equal ltyp rtyp =
    match (ltyp, rtyp) with
    | (Array(ltyp, _), Array(rtyp, _)) -> are_types_equal ltyp rtyp
    | _ -> ltyp = rtyp

let rec ast_type_to_typ typ =
    match typ with
    | TypI -> Int
    | TypF -> Float
    | TypB -> Bool
    | TypC -> Char
    | TypA(typ, size) -> (Array((ast_type_to_typ typ), size))
    | TypP(typ) -> (Ptr (ast_type_to_typ typ))
    | TypS(id) -> (Struct id)
    | TypV -> Void

let rec lookup_fn_def env id loc =
    let loc = loc_optional_param loc in
    match lookup_opt id env with
    | Some(FunDef(ret_typ, arg_defs)) -> (ret_typ, arg_defs)
    | Some(_) -> raise (Semantic_error(loc, "Identifier \"" ^ id ^ "\" is not a function."))
    | None -> raise (Semantic_error(loc, "Function \"" ^ id ^ "\" is not defined."))
and lookup_var_type env id loc =
    let loc = loc_optional_param loc in
    match lookup_opt id env with
    | Some(VarDef(typ)) -> typ
    | Some(_) -> raise (Semantic_error(loc, "Identifier \"" ^ id ^ "\" is not a variable."))
    | None -> raise (Semantic_error(loc, "Variable \"" ^ id ^ "\" is not defined."))
and lookup_struct_def env id loc =
    let loc = loc_optional_param loc in
    match lookup_opt id env with
    | Some(StructDef(fields)) -> fields
    | Some(_) -> raise (Semantic_error(loc, "Identifier \"" ^ id ^ "\" is not a struct."))
    | None -> raise (Semantic_error(loc, "Struct \"" ^ id ^ "\" is not defined."))
and loc_optional_param loc =
    Option.value loc ~default:Location.dummy_code_pos

(* Type Check expression: Ast.expr *)
let rec tc_expr env expr =
    let loc = expr.loc in
    match expr.node with
    | Access(access) -> tc_access env access
    | Assign(access, expr) -> (
        let (env, access_type) = tc_access env access in
        match is_valid_lexpr_type access_type env with
        | true -> (
            let (env, expr_type) = tc_expr env expr in
            match (are_types_equal expr_type access_type) with
            | true -> (env, expr_type)
            | false -> raise (Semantic_error(expr.loc,
                "Cannot assign expression of type \"" ^ show_typ expr_type
                ^ "\" to a variable of type \"" ^ show_typ access_type ^ "\"."))
        )
        | false -> raise (Semantic_error(expr.loc,
                "Variables of type \"" ^ show_typ access_type ^ "\" are not assignable."))
    )
    | Addr(access) ->
        let (env, access_type) = tc_access env access in
        (env, Ptr access_type)
    | UnaryOp(op, expr) -> tc_un_op env tc_expr op expr loc
    | BinaryOp(op, lexpr, rexpr) -> tc_bin_op env tc_expr op lexpr rexpr loc
    | CommaOp(lexpr, rexpr) -> 
        let (lenv, _) = tc_expr env lexpr in
        tc_expr lenv rexpr
    | Call(id, args) -> tc_fn_call env id args loc
    | Cast(_, _) -> raise (Semantic_error(loc, "Type cast not implemented."))
    | ILiteral(_) | FLiteral(_) | CLiteral(_)
    | BLiteral(_) | SLiteral(_) | SizeOf(_) | SizeOfExpr(_) ->
        tc_const_expr env expr
and tc_const_expr env expr =
    let loc = expr.loc in
    match expr.node with
    | ILiteral(value) -> (
        match is_int_literal_valid value with
        | true -> (env, Int)
        | false -> raise (Semantic_error(loc,"Integer literal is out of range."))
    )
    | FLiteral(_) -> (env, Float)
    | CLiteral(_) -> (env, Char)
    | BLiteral(_) -> (env, Bool)
    | SLiteral(_) -> (env, Ptr Char)
    | SizeOf(_) -> (env, Int)
    | SizeOfExpr(_) -> (env, Int)
    | Access(access) -> tc_const_access env access
    | Addr(access) -> tc_const_access env access
    | UnaryOp(op, expr) -> tc_un_op env tc_const_expr op expr loc
    | BinaryOp(op, lexpr, rexpr) -> tc_bin_op env tc_const_expr op lexpr rexpr loc
    | _ -> raise (Semantic_error(loc, "Given expression of type cannot be const evaluated."))
and is_int_literal_valid value =
    (value <= 2147483647) && (value >= -2147483648)
    
(* Type Check access expression: Ast.access *)
and tc_access env access =
    let loc = access.loc in
    match access.node with
    | AccVar(id) -> (env, lookup_var_type env id (Some(loc)))
    | AccDeref(expr) -> (
        let (env, expr_type) = tc_expr env expr in
        match expr_type with
        | Ptr(typ) -> (env, typ)
        | typ -> raise (Semantic_error(loc, "Deferencing requires a pointer type. "
            ^ "The expression type is: \"" ^ show_typ typ ^ "\"."))
    )
    | AccIndex(access, expr) -> (
        let (env, access_type) = tc_access env access in
        let (env, expr_type) = tc_expr env expr in
        match (access_type, expr_type) with
        | (Array(typ, _), Int) -> (env, typ)
        | (Array(_), typ) -> raise (Semantic_error(loc, "Array access index is not an integer. "
            ^ "The index expression type is: \"" ^ show_typ typ ^ "\"."))
        | (typ, _) -> raise (Semantic_error(loc, "Array access requires an array type. "
        ^ "The expression type is: \"" ^ show_typ typ ^ "\"."))
    )
    | AccDot(access, field) -> (
        let (env, access_type) = tc_access env access in
        match access_type with
        | Struct(str_id) -> (env, search_field_in_struct env str_id field loc)
        | typ -> raise (Semantic_error(loc, "Dot operator requires a struct type. "
        ^ "The expression type is: \"" ^ show_typ typ ^ "\"."))
    )
    | AccArrow(expr, field) -> (
        let (env, expr_type) = tc_expr env expr in
        match expr_type with
        | Ptr(Struct(str_id)) -> (env, search_field_in_struct env str_id field loc)
        | typ -> raise (Semantic_error(loc, "Arrow operator requires a pointer to struct type"
        ^ "The expression type is: \"" ^ show_typ typ ^ "\"."))
    )
and tc_const_access env access =
    let loc = access.loc in
    match access.node with
    | AccVar(id) -> (env, lookup_var_type env id (Some(loc)))
    | AccDeref(expr) -> (
        match expr.node with
        | Addr(access) -> tc_const_access env access
        | _ -> raise (Semantic_error(expr.loc, "Given access expression cannot be const evaluated."))
    )
    | _ -> raise (Semantic_error(loc, "Given access expression cannot be const evaluated."))
and search_field_in_struct env str_id field loc =
    let fields = lookup_struct_def env str_id (Some(loc)) in
    let field_has_name name (_, id) = (id = name) in
    match List.find_opt (field_has_name field) fields with
    | Some((typ, _)) -> typ
    | None -> raise (Semantic_error(loc, "The struct \"" ^ str_id ^
        "\" does not contain the field \"" ^ field ^ "\".")) 

(* Type Check function call expression *)
and tc_fn_call env fn args loc =
    let (ret_typ, arg_defs) = lookup_fn_def env fn (Some(loc)) in
    let (env, arg_types) = tc_fn_args env args in
    let tc_fn_args argnum (def_type, _) arg_type =
        match are_types_equal def_type arg_type with
        | true -> argnum + 1
        | false -> raise (Semantic_error(loc,
            "Call of fn \"" ^ fn ^ "\", argument #" ^ string_of_int argnum ^ " types do not match: definition type is \""
            ^ show_typ def_type ^ "\", argument type is \"" ^ show_typ arg_type ^ "\""))
    in
    match (List.length arg_defs) = (List.length arg_types) with
    | true -> (
        let _ = List.fold_left2 tc_fn_args 0 arg_defs arg_types in
        (env, ret_typ)
    )
    | false -> raise (Semantic_error(loc,
        "Call of fn \"" ^ fn ^ "\", number of provided arguments does not match the number of formal parameters."))
and tc_fn_args env args =
    List.fold_left_map tc_expr env args

(* Type Check unary operation expression *)
and tc_un_op env tc_fn op expr loc =
    let (env, expr_type) = tc_fn env expr in
    match op with
    | Pos | Neg -> (
        match expr_type with
        | Int | Float | Char -> (env, expr_type)
        | _ -> raise_un_op_error loc op expr_type
    )
    | Bit_Not -> (
        match expr_type with
        | Int | Char -> (env, expr_type)
        | _ -> raise_un_op_error loc op expr_type
    )
    | Not -> (
        match expr_type with
        | Bool -> (env, expr_type)
        | _ -> raise_un_op_error loc op expr_type
    )
and raise_un_op_error loc op typ =
    raise (Semantic_error(loc, "Unary operator \"" ^ Ast.show_uop op ^
        "\"cannot be applied to the expression of type \"" ^ show_typ typ ^ "\".")) 

(* Type Check binary operation expression *)
and tc_bin_op env tc_fn op lexpr rexpr loc =
    let (env, ltype) = tc_fn env lexpr in
    let (env, rtype) = tc_fn env rexpr in
    match op with
    | Add -> (
        match (ltype, rtype) with
        | (Int, Int) | (Float, Float) | (Char, Char) -> (env, ltype)
        | (Ptr(_), Int) -> (env, ltype)
        | (Int, Ptr(_)) -> (env, rtype)
        | _ -> raise_bin_op_error loc op ltype rtype
    )
    | Sub -> (
        match (ltype, rtype) with
        | (Int, Int) | (Float, Float) | (Char, Char) -> (env, ltype)
        | (Ptr(_), Int) -> (env, ltype)
        | (Ptr(ltyp), Ptr(rtyp)) -> (
            match (are_types_equal ltyp rtyp) with
            | true -> (env, ltype)
            | false -> raise (Semantic_error(loc, "Binary subtraction between pointers must have are_types_equal types. " ^
                "The two pointers have types \"" ^ show_typ ltype ^ "\" and \"" ^ show_typ rtype ^ "\"."))
        )
        | _ -> raise_bin_op_error loc op ltype rtype
    )
    | Mult | Div -> (
        match (ltype, rtype) with
        | (Int, Int) | (Float, Float) -> (env, ltype)
        | _ -> raise_bin_op_error loc op ltype rtype
    )
    | Mod -> (
        match (ltype, rtype) with
        | (Int, Int) -> (env, ltype)
        | _ -> raise_bin_op_error loc op ltype rtype
    )
    | Bit_And | Bit_Or | Bit_Xor
    | Shift_Left | Shift_Right -> (
        match (ltype, rtype) with
        | (Int, Int) -> (env, ltype)
        | _ -> raise_bin_op_error loc op ltype rtype
    )
    | And | Or -> (
        match (ltype, rtype) with
        | (Bool, Bool) -> (env, ltype)
        | _ -> raise_bin_op_error loc op ltype rtype
    )
    | Equal | Neq
    | Less | Leq
    | Greater | Geq -> (
        match (ltype, rtype) with
        | (Bool, Bool) | (Int, Int) | (Char, Char) | (Float, Float)
        | (Ptr(_), Int) | (Int, Ptr(_)) -> (env, Bool)
        | (Ptr(ltyp), Ptr(rtyp)) -> (
            match (are_types_equal ltyp rtyp) with
            | true -> (env, Bool)
            | false -> raise (Semantic_error(loc, "Binary comparison between pointers must have are_types_equal types. " ^
                "The two pointers have types \"" ^ show_typ ltype ^ "\" and \"" ^ show_typ rtype ^ "\"."))            
        )
        | _ -> raise_bin_op_error loc op ltype rtype
    )
and raise_bin_op_error loc op ltyp rtyp =
    raise (Semantic_error(loc, "Binary operator \"" ^ Ast.show_binop op ^
        "\"cannot be applied to expressions of type \"" ^ show_typ ltyp ^ "\" and \"" ^ show_typ rtyp ^ "\".")) 

(* Type Check statement or declaration node: Ast.stmtordecl *)
let rec tc_stmt_or_decl env stmt_or_decl ret_typ =
    match stmt_or_decl.node with
    | Dec(typ, id) -> tc_local_decl env (typ, id) stmt_or_decl.loc
    | Stmt(stmt) -> tc_stmt env stmt ret_typ

(* Type Check statement nodes: Ast.stmt *)
and tc_stmt env stmt ret_typ =
    let loc = stmt.loc in
    match stmt.node with
    | If(guard, then_stmt, else_stmt) -> (
        let (env, guard_typ) = tc_expr env guard in
        match guard_typ with
        | Bool -> (
            let env = begin_block env in
            let (env, then_returns) = tc_stmt env then_stmt ret_typ in
            let env = end_block env in

            let env = begin_block env in
            let (env, else_returns) = tc_stmt env else_stmt ret_typ in
            let env = end_block env in

            match (then_returns, else_returns) with
            | (false, _) | (_, false) -> (env, false)
            | _ -> (env, true)
        )
        | typ -> raise (Semantic_error(loc, "If guard expression type must be a boolean. "
            ^ "The expression type is: \"" ^ show_typ typ ^ "\".")) 
    )
    | While(guard, stmt) -> (
        let (env, guard_typ) = tc_expr env guard in
        match guard_typ with
        | Bool -> 
            let env = begin_block env in
            let (env, _) = tc_stmt env stmt ret_typ in
            (end_block env, false)
        | typ -> raise (Semantic_error(loc, "While guard expression type must be a boolean. "
            ^ "The expression type is: \"" ^ show_typ typ ^ "\"."))
    )
    | Expr(expr) ->
        let (env, _) = tc_expr env expr in
        (env, false)
    | Return(expr) -> (
        match expr with
        | Some(expr) -> (
            let (env, expr_typ) = tc_expr env expr in
            match are_types_equal expr_typ ret_typ with
            | true -> (env, true)
            | false -> raise (Semantic_error(loc, "Return expression type must match the function return type. "
                ^ "The exprected return type is \"" ^ show_typ ret_typ ^ "\" and the expression type is: \"" ^ show_typ expr_typ ^ "\"."))
        )
        | None -> (
            match ret_typ with
            | Void -> (env, true)
            | _ -> raise (Semantic_error(loc, "Return expression type must match the function return type. "
                ^ "The exprected return type is \"" ^ show_typ ret_typ ^ "\" and the expression type is: \"" ^ show_typ Void ^ "\"."))
        )
    )
    | Block(stmts) -> (
        let env = begin_block env in
        let (env, returns) = tc_block_stmt env stmts ret_typ in
        (end_block env, returns)
    )
and tc_block_stmt env stmts ret_typ =
    let check_stmt (env, returns) stmt =
        let loc = stmt.loc in
        match returns with
        | true -> raise (Semantic_error(loc, "Dead code detected: return expression cannot be followed by any command. "))
        | false -> tc_stmt_or_decl env stmt ret_typ
    in
    List.fold_left check_stmt (env, false) stmts

(* Type Check local variable declaration: Ast.stmtordecl -> Dec of Ast.typ * Ast.identifier *)
and tc_local_decl env (var_typ, id) loc =
    let var_typ = ast_type_to_typ var_typ in
    match (is_valid_type var_typ env, is_valid_variable_type var_typ env) with
    | (false, _) | (_, false) ->
        raise (Semantic_error(loc, "Invalid type \"" ^ show_typ var_typ ^ "\" for local variable \"" ^ id ^ "\". "))
    | (true, true) -> (add_entry id (VarDef var_typ) env, false)

(* Type Check whole program declaration: Ast.program *)
let rec tc_program program = 
    let split_topdecls (vlist, slist, flist) topdecl =
        let loc = topdecl.loc in
        match topdecl.node with
        | Fundecl({ typ=ret_typ; fname=id; formals=formals; body=body; }) ->
            ( vlist, slist, (id, ret_typ, formals, body, loc) :: flist )
        | Vardec(typ, id, expr) ->
            ( (typ, id, expr, loc) :: vlist, slist, flist )
        | StructDecl(id, fields) ->
            ( vlist, (id, fields, loc) :: slist, flist )
    in
    match program with
    | Prog(decls) ->
        let (vars, structs, functs) = List.fold_left split_topdecls ([], [], []) decls in
        let env = make_default_env in
        let env = process_struct_defs env structs in
        let env = process_function_defs env functs in
        let env = process_global_variable_defs env vars in
        process_function_bodies env functs

and make_default_env =
    empty_table |>
    add_entry "print" ( FunDef (Void, [(Int, "value")]) ) |>
    add_entry "getint" ( FunDef (Int, []) )

and process_struct_defs env defs =
    let is_struct_valid env (_, fields, _) =
        let check_type env is_valid (typ, _) =
            let typ = ast_type_to_typ typ in
            match is_valid with
            | false -> false
            | true ->
                (is_valid_type typ env) &&
                (is_valid_variable_type typ env)
        in
        List.fold_left (check_type env) true fields
    in
    let rec process_defs prec_defs_size env defs =
        let defs_size = List.length defs in
        match (defs_size, prec_defs_size = defs_size) with
        | (0, _) -> env
        | (_, true) -> raise (Semantic_error(Location.dummy_code_pos, "Some struct definitions are recursive. ")) 
        | (_, false) -> (
            let (usable, unusable) = List.partition (is_struct_valid env) defs in
            let type_check_struct env def =
                let (id, fields, loc) = def in
                tc_struct_def env (id, fields) loc
            in
            let env = List.fold_left type_check_struct env usable in
            process_defs defs_size env unusable
        )
    in
    process_defs (-1) env defs
(* Type Check struct declaration: Ast.identifier * (Ast.typ * Ast.identifier) list *)
and tc_struct_def env (id, fields) loc =
    let tc_struct_field_def env (fields, is_valid) (typ, id) =
        match is_valid with
        | true -> (
            let typ = ast_type_to_typ typ in
            match (is_valid_type typ env) && (is_valid_variable_type typ env) with
            | true -> ( (typ, id) :: fields, true )
            | false -> (fields, false)
        )
        | false -> (fields, false)
    in
    let (fields, is_valid) = List.fold_left (tc_struct_field_def env) ([], true) fields in
    match is_valid with
    | true -> add_entry id (StructDef fields) env
    | false -> raise (Semantic_error(loc, "Struct field type is not valid. "))

and process_function_defs env defs =
    let process_function env (id, ret_typ, formals, _, loc) =
        tc_func_def env (id, ret_typ, formals) loc
    in
    List.fold_left process_function env defs
    
(* Type Check function declaration: { typ : Ast.typ; fname : string; formals : (Ast.typ * Ast.identifier) list; body : Ast.stmt; } *)
and tc_func_def env (id, ret_typ, formals) loc =
    let tc_func_ret_type env ret_typ =
        let typ = ast_type_to_typ ret_typ in
        (typ, (is_valid_type typ env) && (is_valid_return_type typ env))
    in
    let tc_func_param_def env (typ, id) (formals, is_valid) =
        match is_valid with
        | true ->
            let typ = ast_type_to_typ typ in
            let res = match (is_valid_type typ env) && (is_valid_parameter_type typ env) with
            | true -> ( (typ, id) :: formals, true )
            | false -> (formals, false)
            in res
        | false -> (formals, false)
    in
    let (ret_typ, is_valid) = tc_func_ret_type env ret_typ in
    let (formals, is_valid) = List.fold_right (tc_func_param_def env) formals ([], is_valid) in
    match is_valid with
    | true -> add_entry id (FunDef (ret_typ, formals)) env
    | false -> raise (Semantic_error(loc, "Function \"" ^ id ^ "\" formal parameters are incorrect. ")) 

and process_function_bodies env defs =
    let process_function env (id, _, _, body, loc) =
        tc_func_body env (id, body) loc
    in
    List.fold_left process_function env defs

(* Type Check function body: { typ : Ast.typ; fname : string; formals : (Ast.typ * Ast.identifier) list; body : Ast.stmt; } *)
and tc_func_body env (id, body) loc =
    let add_formals_to_env env (typ, id) =
        add_entry id (VarDef(typ)) env
    in
    let (ret_typ, arg_defs) = lookup_fn_def env id (Some(loc)) in

    let env = begin_block env in
    let env = List.fold_left add_formals_to_env env arg_defs in
    let (env, returns) = 
        match body.node with
        | Block(stmts) -> tc_block_stmt env stmts ret_typ
        | _ -> tc_stmt env body ret_typ
    in
    let env = end_block env in
    match (ret_typ, returns) with
    | (_, true) | (Void, _) -> env
    | _ -> raise (Semantic_error(loc, "Function \"" ^ id ^ "\" is missing some return expression. ")) 

and process_global_variable_defs env defs =
    let process_variable env (typ, id, expr, loc) =
        tc_var_decl env (typ, id, expr) loc
    in
    List.fold_left process_variable env defs

(* Type Check variable declaration: Ast.typ * Ast.identifier * Ast.expr option *)
and tc_var_decl env (var_typ, id, expr) loc =
    let var_typ = ast_type_to_typ var_typ in
    match (is_valid_type var_typ env, is_valid_variable_type var_typ env) with
    | (false, _) | (_, false) ->
        raise (Semantic_error(loc, "Invalid type \"" ^ show_typ var_typ ^ "\" for global variable \"" ^ id ^ "\". "))
    | (true, true) -> (
        match expr with
        | Some(expr) -> (
            let (env, expr_typ) = tc_const_expr env expr in
            match are_types_equal expr_typ var_typ with
            | true -> add_entry id (VarDef var_typ) env
            | false -> raise (Semantic_error(loc, "Initializer expression for global variable does not match variable type. "
                ^ "The variable type is \"" ^ show_typ var_typ ^ "\" and the expression type is \"" ^ show_typ expr_typ ^ "\"." ))
        )
        | None -> add_entry id (VarDef var_typ) env
    )
    

(* Type Check whole program declaration: Ast.program *)
let type_check program = 
    let env = tc_program program in
    match lookup_opt "main" env with
    | Some(FunDef(ret_typ, arg_def_types)) -> (
        let _ = match ret_typ with
            | Int | Void -> true
            | _ -> raise (Semantic_error(Location.dummy_code_pos, "Main function return type must be void or int. "))
        in
        let _ = match arg_def_types with
            | [] -> true
            | _ -> raise (Semantic_error(Location.dummy_code_pos, "Main function has no formal parameters. "))
        in
        program
    )
    | _ -> raise (Semantic_error(Location.dummy_code_pos, "Main function is not defined. "))