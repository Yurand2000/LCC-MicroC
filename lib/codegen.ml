open Ast
open Symbol_table
open Cg_local_types
open Cg_environment
open Cg_helper_fns
open Cg_exceptions

(* Exceptions *)
exception Unexpected_error = Cg_exceptions.Unexpected_error

(* Main Function *)
let rec to_llvm_module ast =
    let ctx = Llvm.global_context () in
    let md = Llvm.create_module ctx "module" in
    let env =
        (empty_table, empty_table) |>
        cg_types_env (ctx, md) |>
        cg_runtime_env (ctx, md)
    in
    let _ = match ast with | Prog(decls) -> (
        let (structs, vars, functs) = split_topdecls decls in
        let env = List.fold_left (cg_struct_decl (ctx, md)) env structs in
        let _ = List.map (cg_struct_def (ctx, md) env) structs in
        let env = List.fold_left (cg_fun_decl (ctx, md)) env functs in
        let env = List.fold_left (cg_global_var (ctx, md)) env vars in
        List.filter (fun { typ=_; fname=_; formals=_; body=body; } -> Option.is_some body ) functs |>
        List.map (cg_fun_def (ctx, md) env)
    ) in
    md

and split_topdecls topdecls =
    let split_decls (structs, vars, functs) topdecl =
        match topdecl.node with
        | Fundecl(fun_decl) -> (structs, vars, fun_decl :: functs)
        | Vardec(typ, id, expr) -> (structs, (typ, id, expr) :: vars, functs)
        | StructDecl(id, fields) -> ((id, fields) :: structs, vars, functs)
    in
    List.fold_left split_decls ([],[],[]) topdecls

(* Generate code for Variable definition *)
and cg_global_var (ctx, md) (typs, env) (typ, id, expr) =
    match expr with
    | Some(expr) -> (
        let (expr, typ) = cg_const_expr (ctx, md) (typs, env) expr in
        let var = Llvm.define_global id expr md in
        let env = add_global_entry id (var, Ptr(typ)) env in
        (typs, env)
    )
    | None -> (
        let typ = get_local_typ typ in
        let default = cg_default_value typs typ in
        let var = Llvm.define_global id default md in
        let env = add_global_entry id (var, Ptr(typ)) env in
        (typs, env)
    )

(* Generate code for Struct declaration *)
and cg_struct_decl (ctx, _md) (typs, env) (id, fields) =
    (* Declare struct llvm type *)
    let struct_type = Llvm.named_struct_type ctx id in

    (* Build field table for struct *)
    let add_field (fields, curr_index) (typ, id) =
        (add_entry id (curr_index, get_local_typ typ) fields, curr_index + 1)
    in
    let (fields, _) = List.fold_left add_field (empty_table, 0) fields in

    (add_entry id (struct_type, fields) typs, env)

(* Generate code for Struct definition *)
and cg_struct_def (_ctx, _md) (typs, _env) (id, fields) =
    let struct_type = lookup_type id typs in
    let field_types = List.map (fun (typ, _id) -> get_local_typ typ |> get_llvm_type typs) fields in
    let _ = Llvm.struct_set_body struct_type (Array.of_list field_types) false in
    ()

(* Generate code for Function declaration *)
and cg_fun_decl (_ctx, md) (typs, env) { typ=ret_typ; fname=fn_name; formals=formals; body=body; } =
    (* Convert Ast types to local types *)
    let ret_typ = get_local_typ ret_typ in
    let formals = List.map (fun (t, _) -> get_local_typ t) formals in
    let fn_type = Fun (ret_typ, formals) in

    (* Add function to the environment *)
    match body with
    | Some(_) -> (typs, define_llvm_fn (_ctx, md) (typs, env) fn_name fn_type)
    | None -> (typs, declare_llvm_fn (_ctx, md) (typs, env) fn_name fn_type)

(* Generate code for Function definition *)
and cg_fun_def (ctx, md) (typs, env) { typ=_; fname=id; formals=formals; body=body; } =
    let body = match body with
    | Some(body) -> body
    | None -> raise_error "Cannot create body of an external function declaration" Location.dummy_code_pos
    in

    (* Convert Ast types to local types *)
    let formals = List.map (fun (t, id) -> (get_local_typ t, id)) formals in

    (* Lookup declared function from the environment *)
    let fn = Llvm.lookup_function id md in
    let fn = match fn with
        | Some(fn) -> fn
        | None -> raise_error "Function definition not found" Location.dummy_code_pos
    in

    (* Create function entry basic block *)
    let entry_bb = Llvm.entry_block fn in
    let bld = Llvm.builder_at_end ctx entry_bb in

    (* Create function environment *)
    let env = begin_block env in
    let params = Array.to_list (Llvm.params fn) in
    let add_local_params_to_env env (typ, id) llvalue =
        let lltype = get_llvm_type typs typ in
        let param = Llvm.build_alloca lltype id bld in
        let _ = Llvm.build_store llvalue param bld in
        add_entry id (param, Ptr(typ)) env
    in
    let env = List.fold_left2 add_local_params_to_env env formals params in

    (* Build function body *)
    let _ = cg_stmt (ctx, md, bld) (typs, env) body in
    let _ = if Bool.not (is_return_present body) then
        let _ = Llvm.build_ret_void bld in ()
    in
    ()

(* Generate code for Statements *)
and cg_stmt (ctx, md, bld) (typs, env) stmt =
    match stmt.node with
    | If(guard_expr, then_stmts, else_stmts) ->
        cg_if_stmt (ctx, md, bld) (typs, env) guard_expr then_stmts else_stmts
    | While(guard_expr, stmts) ->
        cg_while_stmt (ctx, md, bld) (typs, env) guard_expr stmts
    | Expr(expr) ->
        let _ = cg_expr (ctx, md, bld) (typs, env) expr in ()
    | Return(Some(expr)) ->
        let (expr, _) = cg_expr (ctx, md, bld) (typs, env) expr in
        let _ = Llvm.build_ret expr bld in ()
    | Return(None) ->
        let _ = Llvm.build_ret_void bld in ()
    | Block(stmts) ->
        let build_stmt (ctx, md, bld) typs env stmt_or_decl =
            cg_stmt_or_dec (ctx, md, bld) (typs, env) stmt_or_decl
        in
        let _ = List.fold_left (build_stmt (ctx, md, bld) typs) (begin_block env) stmts in
        ()

(* Code for Statement Or Declarations, they may update the local environment *)
and cg_stmt_or_dec (ctx, md, bld) (typs, env) stmt_or_dec =
    match stmt_or_dec.node with
    | Dec(typ, id) -> (
        let typ = get_local_typ typ  in
        let lltype = get_llvm_type typs typ in
        let var = Llvm.build_alloca lltype id bld in
        add_entry id (var, Ptr(typ)) env
    )
    | Stmt(stmt) ->
        let _ = cg_stmt (ctx, md, bld) (typs, env) stmt in
        env

(* Code generation for If statements *)
and cg_if_stmt (ctx, md, bld) (typs, env) guard then_stmt else_stmt =
    (* Build then and else basic blocks *)
    let fn = Llvm.block_parent (Llvm.insertion_block bld) in
    let then_bb = Llvm.append_block ctx "if_then" fn in
    let else_bb = Llvm.append_block ctx "if_else" fn in

    (* Build continue block if needed *)
    let then_returns = is_return_present then_stmt in
    let else_returns = is_return_present else_stmt in
    let cnt_bb = match (then_returns, else_returns) with
        | (true, true) -> then_bb
        | _ -> Llvm.append_block ctx "if_cnt" fn
    in

    (* Evaluate guard and build branch instruction *)
    let (guard, _) = cg_expr (ctx, md, bld) (typs, env) guard in
    let _ = Llvm.build_cond_br guard then_bb else_bb bld in

    (* Build then and else branches *)
    let _ = Llvm.position_at_end then_bb bld in
    let _ = cg_stmt (ctx, md, bld) (typs, env) then_stmt in
    let _ = if Bool.not (is_return_present then_stmt) then
        let _ = Llvm.build_br cnt_bb bld in ()
    in

    let _ = Llvm.position_at_end else_bb bld in
    let _ = cg_stmt (ctx, md, bld) (typs, env) else_stmt in
    let _ = if Bool.not (is_return_present else_stmt) then
        let _ = Llvm.build_br cnt_bb bld in ()
    in

    let _ = Llvm.position_at_end cnt_bb bld in
    ()

(* Code generation for While statements *)
and cg_while_stmt (ctx, md, bld) (typs, env) guard body =
    (* Build guard, loop and continue basic blocks *)
    let fn = Llvm.block_parent (Llvm.insertion_block bld) in
    let guard_bb = Llvm.append_block ctx "while_guard" fn in
    let loop_bb = Llvm.append_block ctx "while_loop" fn in
    let cnt_bb = Llvm.append_block ctx "while_cnt" fn in

    (* Jump to guard basic block *)
    let _ = Llvm.build_br guard_bb bld in

    (* Evaluate guard and do conditional jump *)
    let _ = Llvm.position_at_end guard_bb bld in
    let (guard, _) = cg_expr (ctx, md, bld) (typs, env) guard in
    let _ = Llvm.build_cond_br guard loop_bb cnt_bb bld in

    (* Build loop branch *)
    let _ = Llvm.position_at_end loop_bb bld in
    let _ = cg_stmt (ctx, md, bld) (typs, env) body in
    let _ = match is_return_present body with
        | true -> ()
        | false -> let _ = Llvm.build_br guard_bb bld in ()
    in

    (* Move builder to continue branch *)
    let _ = Llvm.position_at_end cnt_bb bld in
    ()

(* Check if all paths lead to a return statement *)
and is_return_present stmt =
    let rec is_return_in_stmt stmt =
        match stmt.node with
        | If(_, then_stmt, else_stmt) ->
            (is_return_in_stmt then_stmt) && (is_return_in_stmt else_stmt)
        | While(_) -> false
        | Expr(_) -> false
        | Return(_) -> true
        | Block(stmts) -> (
            let is_return_in_block previous stmt_or_dec =
                match previous with
                | true -> raise_error "Found statement after return expression." stmt.loc
                | false -> is_return_in_stmt_or_dec stmt_or_dec
            in
            List.fold_left is_return_in_block false stmts
        )
    and is_return_in_stmt_or_dec stmt_or_dec =
        match stmt_or_dec.node with
        | Dec(_) -> false
        | Stmt(stmt) -> is_return_in_stmt stmt
    in
    is_return_in_stmt stmt

(* Codegen Expressions *)
and cg_expr (ctx, md, bld) (typs, env) expr =
    let loc = expr.loc in
    match expr.node with
    | ILiteral(_) | FLiteral(_) | CLiteral(_)
    | BLiteral(_) | SLiteral(_) | SizeOf(_) ->
        cg_literals (ctx, md) typs expr
    | Access(access) -> (
        let (addr, addr_typ) = cg_access (ctx, md, bld) (typs, env) access in
        match addr_typ with
        | Ptr(Array(_)) -> (addr, addr_typ)
        | Ptr(typ) -> (Llvm.build_load addr "load" bld, typ)
        | _ -> raise_error "Access address is not a pointer" expr.loc
    )
    | Assign(access, expr) -> (
        let (expr, expr_typ) = cg_expr (ctx, md, bld) (typs, env) expr in
        let (addr, access_typ) = cg_access (ctx, md, bld) (typs, env) access in
        let access_typ = match access_typ with
            | Ptr(typ) -> typ
            | _ -> raise_error "Access didn't return a pointer" loc
        in
        let (expr, expr_typ) = cg_implicit_cast_expr (ctx, md, bld) (typs, env) access_typ (expr, expr_typ) loc in
        let _ = Llvm.build_store expr addr bld in
        (expr, expr_typ)
    )
    | Addr(access) -> cg_access (ctx, md, bld) (typs, env) access

    | UnaryOp(op, expr) -> cg_un_op (ctx, md, bld) (typs, env) op expr loc
    | BinaryOp(op, lexpr, rexpr) -> cg_bin_op (ctx, md, bld) (typs, env) op lexpr rexpr loc
    | CommaOp(lexpr, rexpr) ->
        let _ = cg_expr (ctx, md, bld) (typs, env) lexpr in
        cg_expr (ctx, md, bld) (typs, env) rexpr
    | Call(id, args) -> cg_fn_call (ctx, md, bld) (typs, env) id args loc
    | Cast(typ, expr) -> cg_cast_expr (ctx, md, bld) (typs, env) typ expr loc

(* Access Expressions, returns address of the access expression *)
and cg_access (ctx, md, bld) (typs, env) access =
    match access.node with
    | AccVar(id) -> lookup id env
    | AccDeref(expr) -> cg_expr (ctx, md, bld) (typs, env) expr
    | AccIndex(access, index_expr) -> (
        let (index, _) = cg_expr (ctx, md, bld) (typs, env) index_expr in
        let (addr, addr_typ) = (cg_access (ctx, md, bld) (typs, env) access) in
        match addr_typ with
        | Ptr(Array(data_typ, _)) ->
            (Llvm.build_gep addr [| const_zero typs; index |] "array_access" bld, Ptr(data_typ))
        | Ptr(Ptr(data_typ)) ->
            let addr = Llvm.build_load addr "deref" bld in
            (Llvm.build_gep addr [| index |] "array_access" bld, Ptr(data_typ))
        | Ptr(data_typ) ->
            (Llvm.build_gep addr [| index |] "array_access" bld, Ptr(data_typ))
        | _ ->
            raise_error ("Pointer or array pointer expected, found: " ^ show_typ addr_typ) access.loc
    )
    | AccStruct(access, field_id) -> (
        let (addr, addr_typ) = cg_access (ctx, md, bld) (typs, env) access in
        match addr_typ with
        | Ptr(Struct(struct_id)) -> cg_struct_access (ctx, md, bld) typs addr struct_id field_id
        | _ -> raise_error ("Access address is not a pointer to struct, found: " ^ show_typ addr_typ) access.loc
    )
and cg_struct_access (_ctx, _md, bld) typs addr struct_id field_id =
    let (field_index, field_typ) = lookup_struct_field struct_id field_id typs in
    let addr = Llvm.build_struct_gep addr field_index "struct_access" bld in
    (addr, Ptr(field_typ))

(* Codegen Constant Expressions *)
and cg_const_expr (ctx, md) (typs, _) expr =
    match expr.node with
    | ILiteral(_) | FLiteral(_) | CLiteral(_)
    | BLiteral(_) | SLiteral(_) | SizeOf(_) ->
        cg_literals (ctx, md) typs expr
    | Access(_) | Addr(_) | Assign(_, _) | Call(_, _) | Cast(_, _) ->
        raise_error "This expression cannot be const evaluated" expr.loc
    | UnaryOp(_, _) | BinaryOp(_, _, _) | CommaOp(_, _) ->
        raise_error "This expression must be const evaluated before code generation" expr.loc

(* Literal Expressions *)
and cg_literals (ctx, md) typs expr =
    match expr.node with
    | ILiteral(value) -> (Llvm.const_int (get_llvm_int typs) value, Int)
    | FLiteral(value) -> (Llvm.const_float (get_llvm_float typs) value, Float)
    | CLiteral(value) -> (Llvm.const_int (get_llvm_char typs) (Char.code value), Char)
    | BLiteral(value) -> (Llvm.const_int (get_llvm_bool typs) (Bool.to_int value), Bool)
    | SLiteral(value) -> make_string_literal (ctx, md) typs value
    | SizeOf(typ) ->
        let lltype = get_llvm_type typs (get_local_typ typ) in
        (get_size_of_type typs lltype, Int)
    | _ ->
        raise_error "Literal evaluation unexpected error" expr.loc

(* String literals are saved as constant global variables with special names,
   and a pointer to these variables is returned.
   This function allocates only one variable for each same string literal generated. *)
and make_string_literal (ctx, md) typs string_literal =
    let global_const_name = "0SL[" ^ Int.to_string (Hashtbl.hash string_literal) ^ "]" in
    let gvar =
        match Llvm.lookup_global global_const_name md with
        | Some(gvar) -> gvar
        | None -> (
            let string_literal = Llvm.const_stringz ctx string_literal in
            let gvar = Llvm.define_global global_const_name string_literal md in
            let _ = Llvm.set_global_constant true gvar in
            gvar
        )
    in
    let string_pointer = Llvm.const_gep gvar [|const_zero typs; const_zero typs|] in
    (string_pointer, Ptr Char)

(* Codegen Function call Expressions *)
and cg_fn_call (ctx, md, bld) (typs, env) id args loc =
    let (fn, fun_typ) = lookup id env in
    let (ret_typ, arg_typs) =
        match fun_typ with
        | Fun((ret_typ, arg_typs)) -> (ret_typ, arg_typs)
        | _ -> raise_error "The type of the given function is not a function" loc
    in
    let args_implicit_cast (llvalue, expr_type) arg_type =
        fst (cg_implicit_cast_expr (ctx, md, bld) (typs, env) arg_type (llvalue, expr_type) loc)
    in
    let args = List.map (cg_expr (ctx, md, bld) (typs, env)) args in
    let args = List.map2 args_implicit_cast args arg_typs in
    match ret_typ with
    | Void -> (Llvm.build_call fn (Array.of_list args) "" bld, ret_typ)
    | _ -> (Llvm.build_call fn (Array.of_list args) "fn_call" bld, ret_typ)

(* Codegen Cast expression *)
and cg_cast_expr (ctx, md, bld) (typs, env) _cast_type _expr loc =
    let (expr, expr_type) = cg_expr (ctx, md, bld) (typs, env) _expr in
    let cast_type = get_local_typ _cast_type in
    match (cast_type, expr_type) with
    | (Int, Float) ->
        (Llvm.build_fptosi expr (get_llvm_type typs cast_type) "cast" bld, cast_type)
    | (Float, Int) ->
        (Llvm.build_sitofp expr (get_llvm_type typs cast_type) "cast" bld, cast_type)
    | (Int, Ptr(_)) ->
        (Llvm.build_ptrtoint expr (get_llvm_type typs cast_type) "cast" bld, cast_type)
    | (Ptr(_), Int) ->
        (Llvm.build_inttoptr expr (get_llvm_type typs cast_type) "cast" bld, cast_type)
    | (Ptr(_), Ptr(Void)) ->
        (Llvm.build_pointercast expr (get_llvm_type typs cast_type) "cast" bld, cast_type)

    (* Implicit casts *)
    | _ -> cg_implicit_cast_expr (ctx, md, bld) (typs, env) cast_type (expr, expr_type) loc

(* Codegen implicit cast *)
and cg_implicit_cast_expr (_ctx, _md, bld) (typs, _env) cast_type (expr, expr_type) loc =
    match (cast_type, expr_type) with
    | (Ptr(Void), Ptr(_)) ->
        (Llvm.build_pointercast expr (get_llvm_type typs cast_type) "implicit_cast" bld, cast_type)
    | (Ptr(ctyp), Ptr(Array(atyp, _))) when ctyp = atyp ->
        (Llvm.build_pointercast expr (get_llvm_type typs cast_type) "implicit_cast" bld, cast_type)
    | _ when cast_type = expr_type ->
        (expr, expr_type)
    | _ ->
        raise_error ("Unexpected implicit cast operation: " ^ show_typ expr_type ^ " to " ^ show_typ cast_type) loc

(* Codegen Unary Operator Expressions *)
and cg_un_op (ctx, md, bld) (typs, env) op expr loc =
    let (expr, typ) = cg_expr (ctx, md, bld) (typs, env) expr in
    match op with
    | Pos -> (expr, typ)
    | Neg -> (
        match typ with
        | Int | Char -> (Llvm.build_neg expr "negate" bld, typ)
        | Float -> (Llvm.build_fneg expr "negate" bld, typ)
        | _ -> raise_error "Unary operation \'Neg\' error" loc
    )
    | Bit_Not | Not -> (
        match typ with
        | Int | Bool | Char -> (Llvm.build_not expr "not" bld, typ)
        | _ -> raise_error "Unary operation \'Bit Not | Not\' error" loc
    )

(* Codegen Binary Operator Expressions *)
and cg_bin_op (ctx, md, bld) (typs, env) op lexpr rexpr loc =
    let (lexpr, ltype) = cg_expr (ctx, md, bld) (typs, env) lexpr in
    let (rexpr, rtype) = cg_expr (ctx, md, bld) (typs, env) rexpr in
    match op with
    | Add -> (
        match (ltype, rtype) with
        | (Int, Int) | (Char, Char) -> (Llvm.build_add lexpr rexpr "add" bld, ltype)
        | (Float, Float) -> (Llvm.build_fadd lexpr rexpr "add" bld, ltype)
        | (Ptr(_), Int) -> (Llvm.build_gep lexpr [|rexpr|] "add" bld, ltype)
        | (Int, Ptr(_)) -> (Llvm.build_gep rexpr [|lexpr|] "add" bld, rtype)
        | _ -> raise_error "Binary Operation \'Add\' error" loc
    )
    | Sub -> (
        match (ltype, rtype) with
        | (Int, Int) | (Char, Char) -> (Llvm.build_sub lexpr rexpr "sub" bld, ltype)
        | (Float, Float) -> (Llvm.build_fsub lexpr rexpr "sub" bld, ltype)
        | (Ptr(_), Int) ->
            let negated = Llvm.build_neg rexpr "negate" bld in
            (Llvm.build_gep lexpr [|negated|] "sub" bld, ltype)
        | (Ptr(_), Ptr(_)) ->
            let ptr_to_int = Llvm.build_ptrtoint rexpr (get_llvm_int typs) "ptr_to_int" bld in
            let negated = Llvm.build_neg ptr_to_int "negate" bld in
            (Llvm.build_gep lexpr [|negated|] "sub" bld, ltype)
        | _ -> raise_error "Binary Operation \'Sub\' error" loc
    )
    | Mult -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_mul lexpr rexpr "mul" bld, ltype)
        | (Float, Float) -> (Llvm.build_fmul lexpr rexpr "mul" bld, ltype)
        | _ -> raise_error "Binary Operation \'Mult\' error" loc
    )
    | Div -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_sdiv lexpr rexpr "div" bld, ltype)
        | (Float, Float) -> (Llvm.build_fdiv lexpr rexpr "div" bld, ltype)
        | _ -> raise_error "Binary Operation \'Div\' error" loc
    )
    | Mod -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_srem lexpr rexpr "mod" bld, ltype)
        | _ -> raise_error "Binary Operation \'Mod\' error" loc
    )
    | Bit_And | And -> (
        match (ltype, rtype) with
        | (Int, Int) | (Bool, Bool) -> (Llvm.build_and lexpr rexpr "and" bld, ltype)
        | _ -> raise_error "Binary Operation \'Bit And | And\' error" loc
    )
    | Bit_Or | Or -> (
        match (ltype, rtype) with
        | (Int, Int) | (Bool, Bool) -> (Llvm.build_or lexpr rexpr "or" bld, ltype)
        | _ -> raise_error "Binary Operation \'Bit Or | Or\' error" loc
    )
    | Bit_Xor -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_xor lexpr rexpr "xor" bld, ltype)
        | _ -> raise_error "Binary Operation \'Bit Xor\' error" loc
    )
    | Shift_Left -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_shl lexpr rexpr "shift_left" bld, ltype)
        | _ -> raise_error "Binary Operation \'Shift Left\' error" loc
    )
    | Shift_Right -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_ashr lexpr rexpr "shift_right" bld, ltype)
        | _ -> raise_error "Binary Operation \'Shift Right\' error" loc
    )
    | Equal | Neq
    | Less | Leq
    | Greater | Geq -> (
        match (ltype, rtype) with
        | (Bool, Bool) | (Int, Int) | (Char, Char) ->
            (Llvm.build_icmp (get_icmp_typ op) lexpr rexpr "cmp" bld, Bool)
        | (Float, Float) ->
            (Llvm.build_fcmp (get_fcmp_typ op) lexpr rexpr "cmp" bld, Bool)
        | (Ptr(_), Int) ->
            let ptr_to_int = Llvm.build_ptrtoint lexpr (get_llvm_int typs) "ptr_to_int" bld in
            (Llvm.build_icmp (get_icmp_typ op) ptr_to_int rexpr "cmp" bld, Bool)
        | (Int, Ptr(_)) ->
            let ptr_to_int = Llvm.build_ptrtoint rexpr (get_llvm_int typs) "ptr_to_int" bld in
            (Llvm.build_icmp (get_icmp_typ op) lexpr ptr_to_int "cmp" bld, Bool)
        | (Ptr(_), Ptr(_)) ->
            let lptr_to_int = Llvm.build_ptrtoint lexpr (get_llvm_int typs) "lptr_to_int" bld in
            let rptr_to_int = Llvm.build_ptrtoint rexpr (get_llvm_int typs) "rptr_to_int" bld in
            (Llvm.build_icmp (get_icmp_typ op) lptr_to_int rptr_to_int "cmp" bld, Bool)
        | _ -> raise_error "Binary Operation \'comparison\' error" loc
    )
and get_icmp_typ op =
    match op with
    | Equal -> Llvm.Icmp.Eq
    | Neq -> Llvm.Icmp.Ne
    | Less -> Llvm.Icmp.Slt
    | Leq -> Llvm.Icmp.Sle
    | Greater -> Llvm.Icmp.Sgt
    | Geq -> Llvm.Icmp.Sge
    | _ -> raise_error "Unexpected error" Location.dummy_code_pos
and get_fcmp_typ op =
    match op with
    | Equal -> Llvm.Fcmp.Ueq
    | Neq -> Llvm.Fcmp.Une
    | Less -> Llvm.Fcmp.Ult
    | Leq -> Llvm.Fcmp.Ule
    | Greater -> Llvm.Fcmp.Ugt
    | Geq -> Llvm.Fcmp.Uge
    | _ -> raise_error "Unexpected error" Location.dummy_code_pos