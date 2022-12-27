exception Semantic_error of Location.code_pos * string

open Ast
open Symbol_table

type typ =
    | Int | Float | Bool | Char | Void | Ptr of typ | Array of typ
    (* | Funct of Ast.identifier *)
    | Struct of Ast.identifier

let rec show_typ typ =
    match typ with
    | Int -> "int"
    | Float -> "float"
    | Bool -> "bool"
    | Char -> "char"
    | Void -> "void"
    | Ptr(typ) -> "(* " ^ show_typ typ ^ ")"
    | Array(typ) -> "(" ^ show_typ typ ^ "[])"
    | Struct(id) -> "(struct " ^ id ^ ")"

type symbol =
    | StructDef of (typ * Ast.identifier) list
    | FunDef of typ * (typ) list
    | VarDef of typ

let rec is_type_valid typ env =
    match typ with
    (* | Funct(id) -> Option.is_some (lookup_opt id env) *)
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
    | None -> raise (Semantic_error(Location.dummy_code_pos, "Function " ^ id ^ " not defined"))
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
    let loc = expr.loc in
    match expr.node with
    | Access(access) -> tc_access env access
    | Assign(access, expr) -> (
        let (env, expr_type) = tc_expr env expr in
        let (env, access_type) = tc_access env access in
        match (expr_type = access_type) with
        | true -> (env, expr_type)
        | false -> raise (Semantic_error(expr.loc,
            "Cannot assign expression of type \"" ^ show_typ expr_type
            ^ "\" to a variable of type \"" ^ show_typ expr_type ^ "\"")
        )
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
    | Call(id, args) -> tc_fn_call env id args loc
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
and tc_fn_call env fn args loc =
    let (ret_typ, arg_def_types) = lookup_fn_def env fn in
    let (env, arg_types) = tc_fn_args env args in
    let tc_fn_args argnum def_type arg_type =
        match def_type = arg_type with
        | true -> argnum + 1
        | false -> raise (Semantic_error(loc,
            "Call of fn \"" ^ fn ^ "\", argument #" ^ string_of_int argnum ^ " types do not match: definition type is \""
            ^ show_typ def_type ^ "\", argument type is \"" ^ show_typ arg_type ^ "\""))
    in
    let _ = List.fold_left2 tc_fn_args 0 arg_def_types arg_types in
    (env, ret_typ)
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
    | If(guard, then_stmt, else_stmt) -> (
        let (env, guard_typ) = tc_expr env guard in
        match guard_typ with
        | Bool ->
            let (env, _) = tc_stmt env then_stmt in
            let (env, _) = tc_stmt env else_stmt in
            (env, Void)
        | _ -> failwith "If guard expression type must be a boolean"
    )
    | While(guard, stmt) -> (
        let (env, guard_typ) = tc_expr env guard in
        match guard_typ with
        | Bool -> 
            let (env, _) = tc_stmt env stmt in
            (env, Void)
        | _ -> failwith "While guard expression type must be a boolean"
    )
    | Expr(expr) ->
        let (env, _) = tc_expr env expr in
        (env, Void)
    | Return(expr) -> (
        match expr with
        | Some(expr) -> tc_expr env expr
        | None -> (env, Void)
    )
    | Block(stmts) -> (
        let check_stmt (env, ret_typ) stmt =
            match ret_typ with
            | Void -> tc_stmt_or_decl env stmt
            | _ -> failwith "Return statement must be the last command in a block with a return statement."
        in
        let env = begin_block env in
        let (env, typ) = List.fold_left check_stmt (env, Void) stmts in
        (end_block env, typ)
    )

(* Type Check local variable declaration: Ast.stmtordecl -> Dec of Ast.typ * Ast.identifier *)
and tc_local_decl env (typ, id) =
    let type_id = ast_type_to_typ typ in
    (add_entry id (VarDef type_id) env, Void)

(* Type Check whole program declaration: Ast.program *)
let rec tc_program program = 
    let tc_topdecl env decl =
        let loc = decl.loc in
        match decl.node with
        | Fundecl(decl) ->
            let fun_decl = (decl.fname, decl.typ, decl.formals, decl.body) in
            tc_func_def env fun_decl loc
        | Vardec(typ, id, expr) ->
            tc_var_decl env (typ, id, expr) loc
        | StructDecl(id, fields) ->
            tc_struct_def env (id, fields) loc
    in
    match program with
    | Prog(decls) ->
        let decls = remove_forward_declarations decls in
        List.fold_left tc_topdecl make_default_env decls

and remove_forward_declarations decls =
    let rec fix_decls decls new_decls =
        match decls with
        | [] -> new_decls
        | hd::tl -> (
            let new_decls = match hd.node with
            | Vardec(_, _, _) -> hd :: new_decls
            | StructDecl(id, fields) -> (
                let rec lookup_decl id new_decls accum =
                    match new_decls with
                    | [] -> (List.rev accum, None, [])
                    | hd::tl -> (
                        match hd.node with
                        | StructDecl(str_id, _) -> (
                            match id = str_id with
                            | true -> (List.rev accum, Some(hd), tl)
                            | false -> lookup_decl id tl (hd::accum)
                        )
                        | _ -> lookup_decl id tl (hd::accum)
                    )
                in
                let (prec, def, next) = lookup_decl id new_decls [] in
                let def = match def with Some({ node = node; _ }) -> Some(node) | None -> None in
                match (def, fields) with
                | (Some(StructDecl(_, [])), _::_) -> prec @ ( hd :: next )
                | (None, _) -> hd :: prec
                | (Some(_), _) -> failwith "Struct already defined"
            )
            | Fundecl(decl) -> (
                let {typ = ret_typ; fname = fname; formals = formals; body = body } = decl in
                let rec lookup_decl id new_decls accum =
                    match new_decls with
                    | [] -> (List.rev accum, None, [])
                    | hd::tl -> (
                        match hd.node with
                        | Fundecl({ fname = fname; _ }) -> (
                            match id = fname with
                            | true -> (List.rev accum, Some(hd), tl)
                            | false -> lookup_decl id tl (hd::accum)
                        )
                        | _ -> lookup_decl id tl (hd::accum)
                    )
                in
                let formals_match formals def_formals =
                    let formal_match valid l r =
                        match valid with
                        | true -> l = r
                        | false -> false
                    in
                    List.fold_left2 formal_match true formals def_formals
                in 
                let (prec, def, next) = lookup_decl fname new_decls [] in
                let def = match def with Some({ node = node; _ }) -> Some(node) | None -> None in
                match def with
                | Some(Fundecl({typ = def_ret_typ; fname=fname; formals = def_formals; body = def_body; })) -> (
                    match (ret_typ = def_ret_typ, formals_match formals def_formals, body.node, def_body.node) with
                    | ( true, true, Block(_::_), Block([]) ) -> prec @ ( hd :: next )
                    | ( true, true, Block([]), Block([]) ) -> failwith "Function already declared"
                    | ( true, true, _, _ ) -> failwith "Function already defined"
                    | ( false, _, _, _ ) -> raise (Semantic_error(Location.dummy_code_pos,
                            "Function \"" ^ fname ^ "\" return types do not match: declared fn is \""
                            ^ Ast.show_typ def_ret_typ ^ "\" defined fn is \"" ^ Ast.show_typ ret_typ ^ "\"")
                        )
                    | ( _, false, _, _ ) -> failwith "Function parameters do not match"
                )
                | (Some(_)) -> failwith "Error not expected"
                | None -> hd :: prec
            )
            in
            fix_decls tl new_decls
        )
    in
    List.rev (fix_decls decls [])

(* Type Check variable declaration: Ast.typ * Ast.identifier * Ast.expr option *)
and tc_var_decl env (typ, id, expr) _loc =
    let type_id = ast_type_to_typ typ in
    let tc = match expr with
        | Some(expr) -> snd (tc_expr env expr) = type_id
        | None -> true
    in
    match tc with
        | true -> add_entry id (VarDef type_id) env
        | false -> failwith "Initializer expression does not match variable type"

(* Type Check struct declaration: Ast.identifier * (Ast.typ * Ast.identifier) list *)
and tc_struct_def env (id, fields) _loc =
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
and tc_func_def env (id, ret_typ, formals, body) loc =
    let tc_func_ret_type env ret_typ =
        let type_id = ast_type_to_typ ret_typ in
        (type_id, is_type_valid type_id env)
    in
    let tc_func_param_def env (typ, id) (formals, is_valid) =
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
    let (formals, is_valid) = List.fold_right (tc_func_param_def env) formals ([], is_valid) in
    let formal_types = List.map (fun (typ, _) -> typ) formals in
    match is_valid with
    | true -> (
        let add_formals_to_env env (typ, id) =
            add_entry id (VarDef(typ)) env
        in
        let env = add_entry id (FunDef (ret_typ, formal_types)) env in
        let env = begin_block env in
        let env = List.fold_left add_formals_to_env env formals in
        let (env, block_ret_typ) = (tc_stmt env body) in
        let env = end_block env in
        match ret_typ = block_ret_typ with
        | true -> env
        | false -> raise (Semantic_error(loc,
            "Function \"" ^ id ^ "\" return type \"" ^ show_typ ret_typ ^ "\" does not match block return type \""
            ^ show_typ block_ret_typ ^ "\""))
    )
    | false -> failwith "Function formal parameters are incorrect"

and make_default_env =
    empty_table |>
    add_entry "print" ( FunDef (Void, [Int]) ) |>
    add_entry "getint" ( FunDef (Int, []) )

(* Type Check whole program declaration: Ast.program *)
let type_check program = 
    let env = tc_program program in
    match lookup_opt "main" env with
    | Some(FunDef(ret_typ, arg_def_types)) -> (
        let _ = match ret_typ with
            | Int | Void -> true
            | _ -> failwith "Main function return type must be void or int"
        in
        let _ = match arg_def_types with
            | [] -> true
            | _ -> failwith "Main function has no formal parameters"
        in
        program
    )
    | _ -> failwith "Main function is not defined"