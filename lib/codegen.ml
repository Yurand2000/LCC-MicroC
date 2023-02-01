(*
let to_llvm_module _ =
    failwith "Not Implemented"
*)

open Ast
open Symbol_table

(* Exceptions *)
exception Unexpected_error of Location.code_pos * string
let sem_error msg loc = (Unexpected_error (loc, "Semantic Analysis should have failed at this point: " ^ msg))

(* Debug
let print _msg = ()
    (* Printf.eprintf "** %s\n" _msg; Stdlib.flush stderr; *) *)

(* let print_lltype msg lltype =
    Printf.eprintf "*** %s : %s\n" msg (Llvm.string_of_lltype lltype);
    Stdlib.flush stderr; () *)

(* let print_llvalue msg llvalue =
    let lltype = Llvm.type_of llvalue in
    Printf.eprintf "**** %s : %s\n" msg (Llvm.string_of_lltype lltype);
    Stdlib.flush stderr; () *)

(* Local Types *)
type typ =
    | Int | Float | Bool | Char | Void | Ptr of typ
    | Struct of Ast.identifier
    | Array of typ * int list (* Size of each dimension *)
    | ArrayRef of typ * int (* Dimensions *)
[@@deriving show]

(* Ast.typ to Local types *)
let rec get_local_typ typ =
    match typ with
    | TypI -> Int
    | TypF -> Float
    | TypB -> Bool
    | TypC -> Char
    | TypA(_, size) -> (
        match size with
        | Some(_) -> 
            let (typ, sizes) = get_array_size typ in
            Array(typ, sizes)
        | None -> 
            let (typ, dimentions) = get_array_dims typ in
            ArrayRef(typ, dimentions)
    )
    | TypP(typ) -> Ptr(get_local_typ typ)
    | TypS(id) -> Struct(id)
    | TypV -> Void
and get_array_size typ =
    match typ with
    | TypA(typ, Some(size)) -> (
        let (typ, sizes) = get_array_size typ in
        (typ, size :: sizes)
    )
    | TypA(_, None) -> raise (sem_error "Zero-Sized array" Location.dummy_code_pos)
    | _ -> (get_local_typ typ, [])
and get_array_dims typ =
    match typ with
    | TypA(typ, _) ->
        let (typ, inner_dimentions) = get_array_dims typ in
        (typ, inner_dimentions + 1)
    | _ -> (get_local_typ typ, 0)

(* Types to Llvm types *)
let rec get_llvm_type typs typ =
    match typ with
    | Int -> lookup_type "@i32" typs
    | Float -> lookup_type "@f32" typs
    | Bool -> lookup_type "@bool" typs
    | Char -> lookup_type "@i8" typs
    | Void -> lookup_type "@void" typs
    | Struct(id) -> lookup_type id typs
    | Ptr(typ) -> Llvm.pointer_type (get_llvm_type typs typ)
    | Array(typ, sizes) ->
        get_array_type typs typ sizes
    | ArrayRef(typ, dims) ->
        let sizes = List.init dims (fun _ -> 0) in
        Llvm.pointer_type (get_array_type typs typ sizes)
and get_llvm_int typs = get_llvm_type typs Int
and get_llvm_float typs = get_llvm_type typs Float
and get_llvm_bool typs = get_llvm_type typs Bool
and get_llvm_char typs = get_llvm_type typs Char
and get_llvm_void typs = get_llvm_type typs Void
and get_array_type typs typ sizes =
    let lltype = get_llvm_type typs typ in
    let array_of_size lltype size =
        Llvm.array_type lltype size
    in
    List.fold_left array_of_size lltype sizes
and lookup_type id typs =
    fst (lookup id typs)
and lookup_struct_fields struct_id typs =
    to_alist (snd (lookup struct_id typs))
and lookup_struct_field struct_id field_id typs =
    let fields = snd (lookup struct_id typs) in
    let (field_index, field_typ) = lookup field_id fields in
    (field_index, field_typ)

(* Constants *)
let const_zero typs = Llvm.const_int (get_llvm_int typs) 0
let const_one typs = Llvm.const_int (get_llvm_int typs) 1
let null_ptr typ = Llvm.const_null (Llvm.pointer_type typ)

(* SizeOf type *)
let get_size_of_type typs typ =
    let ptr = Llvm.const_gep (null_ptr typ) [|const_one typs|] in
    Llvm.const_ptrtoint ptr (get_llvm_int typs)

(* Main Function *)
let rec to_llvm_module ast =
    let ctx = Llvm.global_context () in
    let md = Llvm.create_module ctx "module" in
    let env = (empty_table, empty_table) in
    let env = cg_types_env (ctx, md) env in
    let env = cg_runtime_env (ctx, md) env in
    
    let _ = match ast with | Prog(decls) -> (
        let (structs, vars, functs) = reorder_topdecls decls in
        let env = List.fold_left (cg_struct_decl (ctx, md)) env structs in
        let env = List.fold_left (cg_struct_def (ctx, md)) env structs in
        let env = List.fold_left (cg_fun_decl (ctx, md)) env functs in
        let env = List.fold_left (cg_global_var (ctx, md)) env vars in
        List.fold_left (cg_fun_def (ctx, md)) env functs
    ) in
    md

and reorder_topdecls topdecls =
    let split_topdecls (structs, vars, functs) topdecl =
        match topdecl.node with
        | Fundecl(fun_decl) -> (structs, vars, fun_decl :: functs)
        | Vardec(typ, id, expr) -> (structs, (typ, id, expr) :: vars, functs)
        | StructDecl(id, fields) -> ((id, fields) :: structs, vars, functs)
    in
    List.fold_left split_topdecls ([],[],[]) topdecls

and cg_types_env (ctx, _md) (typs, env) =
    let typs = add_entry "@i32" (Llvm.i32_type ctx, empty_table) typs in
    let typs = add_entry "@f32" (Llvm.float_type ctx, empty_table) typs in
    let typs = add_entry "@bool" (Llvm.i1_type ctx, empty_table) typs in
    let typs = add_entry "@char" (Llvm.i8_type ctx, empty_table) typs in
    let typs = add_entry "@void" (Llvm.void_type ctx, empty_table) typs in
    (typs, env)

and cg_runtime_env (_ctx, md) (typs, env) =
    let print_fn = Llvm.declare_function "print" (Llvm.function_type (get_llvm_void typs) [|get_llvm_int typs|]) md in
    let env = add_entry "print" (print_fn, Void) env in
    let getint_fn = Llvm.declare_function "getint" (Llvm.function_type (get_llvm_int typs) [||]) md in
    let env = add_entry "getint" (getint_fn, Int) env in
    (typs, env)

(* Generate code for Variable definition *)
and cg_global_var (ctx, md) (typs, env) (typ, id, expr) =
    match expr with
    | Some(expr) -> (
        let (expr, typ) = cg_const_expr ctx (typs, env) expr in
        let var = Llvm.define_global id expr md in
        let env = add_entry id (var, Ptr(typ)) env in
        (typs, env)
    )
    | None -> (
        let typ = get_local_typ typ in
        let default = cg_default_value typs typ in
        let var = Llvm.define_global id default md in
        let _ = Llvm.set_externally_initialized false var in
        let env = add_entry id (var, Ptr(typ)) env in
        (typs, env)
    )
and cg_default_value typs typ =
    match typ with
    | Int -> Llvm.const_int (get_llvm_int typs) 0
    | Float -> Llvm.const_float (get_llvm_float typs) 0.0
    | Bool -> Llvm.const_int (get_llvm_bool typs) 0
    | Char -> Llvm.const_int (get_llvm_char typs) 0
    | Void -> raise (sem_error "Void cannot have values." Location.dummy_code_pos)
    | Struct(id) -> (
        let lltype = lookup_type id typs in
        let fields = lookup_struct_fields id typs in
        let initialize_field (_, (curr_index, typ)) =
            (curr_index, cg_default_value typs typ)
        in
        let sort_fields (lindex, _) (rindex, _) =
            Stdlib.compare lindex rindex
        in
        let fields = List.map initialize_field fields in
        let fields = List.sort sort_fields fields in
        let fields = List.map snd fields in
        Llvm.const_named_struct lltype (Array.of_list fields)
    )
    | Ptr(_) -> Llvm.const_pointer_null (get_llvm_type typs typ)
    | Array(inner_typ, sizes) ->
        let lltype = get_llvm_type typs inner_typ in
        let llvalue = cg_default_value typs inner_typ in
        let make_def_array size (value, typ) =
            let array_type = Llvm.array_type typ size in
            let array_values = List.init size (fun _ -> value) in
            (Llvm.const_array typ (Array.of_list array_values), array_type)
        in
        fst (List.fold_right make_def_array sizes (llvalue, lltype))
    | ArrayRef(_) ->
        Llvm.const_pointer_null (get_llvm_type typs typ)

(* Generate code for Struct declaration *)
and cg_struct_decl (ctx, _md) (typs, env) (id, fields) =
    let fields = List.map (fun (typ, id) -> (get_local_typ typ, id)) fields in

    (* Declare struct llvm type *)
    let struct_type = Llvm.named_struct_type ctx id in

    (* Build field table for struct *)
    let add_field (fields, curr_index) (typ, id) =
        (add_entry id (curr_index, typ) fields, curr_index + 1)
    in
    let (fields, _) = List.fold_left add_field (empty_table, 0) fields in

    (add_entry id (struct_type, fields) typs, env)

(* Generate code for Struct definition *)
and cg_struct_def (_ctx, _md) (typs, env) (id, fields) =
    let fields = List.map (fun (typ, id) -> (get_local_typ typ, id)) fields in

    (* Build struct llvm type *)
    let field_types = List.map (fun (typ, _) -> get_llvm_type typs typ) fields in
    let struct_type = lookup_type id typs in
    let _ = Llvm.struct_set_body struct_type (Array.of_list field_types) false in
    (typs, env)

(* Generate code for Function declaration *)
and cg_fun_decl (_ctx, md) (typs, env) { typ=ret_typ; fname=id; formals=formals; body=_; } =
    (* Convert Ast types to local types *)
    let ret_typ = get_local_typ ret_typ in
    let formals = List.map (fun (t, id) -> (get_local_typ t, id)) formals in

    (* Add function to the environment *)
    let ll_ret_typ = get_llvm_type typs ret_typ in
    let ll_arg_typs = List.map (fun (t, _) -> get_llvm_type typs t) formals in
    let fn = Llvm.define_function id (Llvm.function_type ll_ret_typ (Array.of_list ll_arg_typs)) md in
    (typs, add_entry id (fn, ret_typ) env)

(* Generate code for Function definition *)
and cg_fun_def (ctx, md) (typs, env) { typ=_; fname=id; formals=formals; body=body; } =
    (* Convert Ast types to local types *)
    let formals = List.map (fun (t, id) -> (get_local_typ t, id)) formals in

    (* Lookup declared function from the environment *)
    let fn = Llvm.lookup_function id md in
    let fn = match fn with
        | Some(fn) -> fn
        | None -> raise (sem_error "Function definition not found" Location.dummy_code_pos)
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
    let env = cg_stmt (ctx, bld) (typs, env) body in 
    let _ = if Bool.not (is_return_present body) then
        let _ = Llvm.build_ret_void bld in ()
    in  
    (typs, end_block env)

(* Generate code for Statements *)
and cg_stmt (ctx, bld) (typs, env) stmt =
    match stmt.node with
    | If(guard_expr, then_stmts, else_stmts) ->
        cg_if_stmt (ctx, bld) (typs, env) guard_expr then_stmts else_stmts
    | While(guard_expr, stmts) ->
        cg_while_stmt (ctx, bld) (typs, env) guard_expr stmts
    | Expr(expr) ->
        let _ = cg_expr (ctx, bld) (typs, env) expr in
        env
    | Return(expr) -> (
        match expr with
        | Some(expr) -> (
            let (expr, _) = cg_expr (ctx, bld) (typs, env) expr in
            let _ = Llvm.build_ret expr bld in
            env
        )
        | None ->
            let _ = Llvm.build_ret_void bld in
            env
    )
    | Block(stmts) -> (
        let build_stmt (ctx, bld) typs env stmt_or_decl =
            cg_stmt_or_dec (ctx, bld) (typs, env) stmt_or_decl
        in
        let env = begin_block env in
        let env = List.fold_left (build_stmt (ctx, bld) typs) env stmts in
        end_block env
    )
and cg_stmt_or_dec (ctx, bld) (typs, env) stmt_or_dec = (* Code for Statement Or Declarations *)
    match stmt_or_dec.node with
    | Dec(typ, id) -> (
        let typ = get_local_typ typ in
        let lltype = get_llvm_type typs typ in
        let var = Llvm.build_alloca lltype id bld in
        add_entry id (var, Ptr(typ)) env
    )
    | Stmt(stmt) -> cg_stmt (ctx, bld) (typs, env) stmt

and cg_if_stmt (ctx, bld) (typs, env) guard then_stmt else_stmt = (* Code generation for If statements *)
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
    let (guard, _) = cg_expr (ctx, bld) (typs, env) guard in
    let _ = Llvm.build_cond_br guard then_bb else_bb bld in

    (* Build then and else branches *)
    let _ = Llvm.position_at_end then_bb bld in
    let env = cg_stmt (ctx, bld) (typs, env) then_stmt in
    let _ = if Bool.not (is_return_present then_stmt) then
        let _ = Llvm.build_br cnt_bb bld in ()
    in

    let _ = Llvm.position_at_end else_bb bld in
    let env = cg_stmt (ctx, bld) (typs, env) else_stmt in
    let _ = if Bool.not (is_return_present else_stmt) then
        let _ = Llvm.build_br cnt_bb bld in ()
    in

    let _ = Llvm.position_at_end cnt_bb bld in
    env
and cg_while_stmt (ctx, bld) (typs, env) guard body = (* Code generation for While statements *)
    (* Build guard, loop and continue basic blocks *)
    let fn = Llvm.block_parent (Llvm.insertion_block bld) in
    let guard_bb = Llvm.append_block ctx "while_guard" fn in
    let loop_bb = Llvm.append_block ctx "while_loop" fn in
    let cnt_bb = Llvm.append_block ctx "while_cnt" fn in

    (* Jump to guard basic block *)
    let _ = Llvm.build_br guard_bb bld in

    (* Evaluate guard and do conditional jump *)
    let _ = Llvm.position_at_end guard_bb bld in
    let (guard, _) = cg_expr (ctx, bld) (typs, env) guard in
    let _ = Llvm.build_cond_br guard loop_bb cnt_bb bld in

    (* Build loop branch *)
    let _ = Llvm.position_at_end loop_bb bld in
    let env = cg_stmt (ctx, bld) (typs, env) body in
    let _ = match is_return_present body with
        | true -> ()
        | false -> let _ = Llvm.build_br guard_bb bld in ()
    in

    (* Move builder to continue branch *)
    let _ = Llvm.position_at_end cnt_bb bld in
    env
and is_return_present stmt = (* Check if all paths lead to a return statement *)
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
                | true -> raise (sem_error "Found statement after return expression." stmt.loc)
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

(* Generate code for Expressions *)
and cg_expr (ctx, bld) (typs, env) expr = (* Expressions *)
    let loc = expr.loc in
    match expr.node with
    | ILiteral(_) | FLiteral(_) | CLiteral(_)
    | BLiteral(_) | SLiteral(_) | SizeOf(_) ->
        cg_literals ctx typs expr

    | Access(access) -> (
        let (addr, addr_typ) = cg_access (ctx, bld) (typs, env) access in
        match addr_typ with
        | Ptr(Array(_)) -> (addr, addr_typ)
        | Ptr(typ) -> (Llvm.build_load addr "load" bld, typ)
        | _ -> raise (sem_error "Access address is not a pointer" expr.loc)
    )
    | Assign(access, expr) -> (
        let (expr, expr_typ) = cg_expr (ctx, bld) (typs, env) expr in
        let (addr, _) = cg_access (ctx, bld) (typs, env) access in
        let _ = Llvm.build_store expr addr bld in
        (expr, expr_typ)
    )
    | Addr(access) ->
        cg_access (ctx, bld) (typs, env) access
    | UnaryOp(op, expr) ->
        cg_un_op (ctx, bld) (typs, env) op expr loc
    | BinaryOp(op, lexpr, rexpr) ->
        cg_bin_op (ctx, bld) (typs, env) op lexpr rexpr loc

    | CommaOp(lexpr, rexpr) ->
        let _ = cg_expr (ctx, bld) (typs, env) lexpr in
        cg_expr (ctx, bld) (typs, env) rexpr

    | Call(id, args) ->
        cg_fn_call (ctx, bld) (typs, env) id args

    | Cast(_, _) -> raise (sem_error "Type cast not implemented." loc)

and cg_access (ctx, bld) (typs, env) access = (* Access Expressions, returns address of variable *)
    match access.node with
    | AccVar(id) ->
        lookup id env
    | AccDeref(expr) -> (
        cg_expr (ctx, bld) (typs, env) expr
    )
    | AccIndex(access, expr) -> (
        let (addr, data_typ, indices) = cg_array_access (ctx, bld) (typs, env) access expr in
        (Llvm.build_gep addr (Array.of_list (const_zero typs :: indices)) "array_access" bld, Ptr(data_typ))
    )
    | AccDot(access, field_id) -> (
        let (addr, addr_typ) = cg_access (ctx, bld) (typs, env) access in
        match addr_typ with
        | Ptr(Struct(struct_id)) -> cg_struct_access (ctx, bld) typs addr struct_id field_id
        | _ -> raise (sem_error "Access address is not a pointer to struct" access.loc)
    )
    | AccArrow(expr, field_id) -> (
        let (addr, addr_typ) = cg_expr (ctx, bld) (typs, env) expr in
        match addr_typ with
        | Ptr(Struct(struct_id)) -> cg_struct_access (ctx, bld) typs addr struct_id field_id
        | _ -> raise (sem_error "Access address is not a pointer to struct" access.loc)
    )
and _cg_address_of (ctx, bld) (var, typ) =
    (Llvm.build_gep var [|const_zero ctx|] "addr_of" bld, Ptr(typ))
and cg_struct_access (_ctx, bld) typs addr struct_id field_id =
    let (field_index, field_typ) = lookup_struct_field struct_id field_id typs in
    let addr = Llvm.build_struct_gep addr field_index "struct_access" bld in
    (addr, Ptr(field_typ))
and cg_array_access (ctx, bld) (typs, env) access expr =
    let (index, _) = cg_expr (ctx, bld) (typs, env) expr in
    match access.node with
    | AccIndex(access, expr) -> (
        let (addr, data_typ, indices) = cg_array_access (ctx, bld) (typs, env) access expr in
        (addr, data_typ, index :: indices)
    )
    | _ -> (
        let (addr, addr_typ) = (cg_access (ctx, bld) (typs, env) access) in
        match addr_typ with
        | Ptr(Array(typ, _)) -> (addr, typ, [ index ])
        | Ptr(ArrayRef(typ, _)) -> (
            let addr = Llvm.build_load addr "deref" bld in
            (addr, typ, [ index ])
        )
        | _ -> raise (sem_error ("Array pointer expected, found: " ^ show_typ addr_typ) access.loc)        
    )

and cg_const_expr ctx (typs, env) expr = (* Constant Expressions *)
    match expr.node with
    | ILiteral(_) | FLiteral(_) | CLiteral(_)
    | BLiteral(_) | SLiteral(_) | SizeOf(_) ->
        cg_literals ctx typs expr
    | Access(access) ->
        cg_const_access ctx (typs, env) access
    | Addr(access) ->
        let (access, access_typ) = cg_const_access ctx (typs, env) access in
        cg_const_address_of typs (access, access_typ)
    | Assign(_, _) | Call(_, _) | Cast(_, _) ->
        raise (sem_error "This expression cannot be const evaluated" expr.loc)
    | UnaryOp(_, _) | BinaryOp(_, _, _) | CommaOp(_, _) ->
        raise (sem_error "This expression must be const evaluated before code generation" expr.loc)
and cg_const_access ctx (_typs, env) access = (* Constant Access Expressions *)
    match access.node with
    | AccVar(id) -> lookup id env
    | AccDeref(expr) -> (
        match expr.node with
        | Addr(access) -> cg_const_access ctx (_typs, env) access
        | _ -> raise (sem_error "This const access expression cannot be evaluated" access.loc)
    )
    | _ -> raise (sem_error "This const access expression cannot be evaluated" access.loc)
and cg_const_address_of typs (var, typ) =
    (Llvm.const_gep var [|const_zero typs|], Ptr(typ))

and cg_literals ctx typs expr = (* Literal Expressions *)
    match expr.node with
    | ILiteral(value) -> (Llvm.const_int (get_llvm_int typs) value, Int)
    | FLiteral(value) -> (Llvm.const_float (get_llvm_float typs) value, Float)
    | CLiteral(value) -> (Llvm.const_int (get_llvm_char typs) (Char.code value), Char)
    | BLiteral(value) -> (Llvm.const_int (get_llvm_bool typs) (Bool.to_int value), Bool)
    | SLiteral(value) -> (Llvm.const_stringz ctx value, Ptr(Char))
    | SizeOf(typ) ->
        let lltype = get_llvm_type typs (get_local_typ typ) in
        (get_size_of_type typs lltype, Int)
    | _ ->
        raise (sem_error "Literal evaluation unexpected error" expr.loc)

and cg_fn_call (ctx, bld) (typs, env) id args = (* Function call Expressions*)
    let (fn, ret_typ) = lookup id env in
    let array_ptrs_conversion (llvalue, typ) =
        match typ with
        | Ptr(Array(typ, sizes)) ->
            let typ = ArrayRef(typ, List.length sizes) in
            let lltype = get_llvm_type typs typ in
            let llvalue = Llvm.build_bitcast llvalue lltype "bitcast" bld in
            (llvalue, typ)
        | _ -> (llvalue, typ)
    in
    let args = List.map (cg_expr (ctx, bld) (typs, env)) args in
    let args = List.map (fun expr -> fst (array_ptrs_conversion expr)) args in
    match ret_typ with
    | Void -> (Llvm.build_call fn (Array.of_list args) "" bld, ret_typ)
    | _ -> (Llvm.build_call fn (Array.of_list args) "fn_call" bld, ret_typ)

and cg_un_op (ctx, bld) (typs, env) op expr loc =  (* Unary Operator Expressions *)
    let (expr, typ) = cg_expr (ctx, bld) (typs, env) expr in
    match op with
    | Pos -> (expr, typ)
    | Neg -> (
        match typ with
        | Int | Bool | Char -> (Llvm.build_neg expr "negate" bld, typ)
        | Float -> (Llvm.build_fneg expr "negate" bld, typ)
        | _ -> raise (sem_error "Unary operation \'Neg\' error" loc)
    )
    | Bit_Not | Not -> (
        match typ with
        | Int | Bool | Char -> (Llvm.build_not expr "not" bld, typ)
        | _ -> raise (sem_error "Unary operation \'Bit Not | Not\' error" loc)
    )

and cg_bin_op (ctx, bld) (typs, env) op lexpr rexpr loc = (* Binary Operator Expressions *)
    let (lexpr, ltype) = cg_expr (ctx, bld) (typs, env) lexpr in
    let (rexpr, rtype) = cg_expr (ctx, bld) (typs, env) rexpr in
    match op with
    | Add -> (
        match (ltype, rtype) with
        | (Int, Int) | (Char, Char) -> (Llvm.build_add lexpr rexpr "add" bld, ltype)
        | (Float, Float) -> (Llvm.build_fadd lexpr rexpr "add" bld, ltype)
        | (Ptr(_), Int) -> (Llvm.build_gep lexpr [|rexpr|] "add" bld, ltype)
        | (Int, Ptr(_)) -> (Llvm.build_gep rexpr [|lexpr|] "add" bld, rtype)
        | _ -> raise (sem_error "Binary Operation \'Add\' error" loc)
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
        | _ -> raise (sem_error "Binary Operation \'Sub\' error" loc)
    )
    | Mult -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_mul lexpr rexpr "mul" bld, ltype)
        | (Float, Float) -> (Llvm.build_fmul lexpr rexpr "mul" bld, ltype)
        | _ -> raise (sem_error "Binary Operation \'Mult\' error" loc)
    )
    | Div -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_sdiv lexpr rexpr "div" bld, ltype)
        | (Float, Float) -> (Llvm.build_fdiv lexpr rexpr "div" bld, ltype)
        | _ -> raise (sem_error "Binary Operation \'Div\' error" loc)
    )
    | Mod -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_srem lexpr rexpr "mod" bld, ltype)
        | _ -> raise (sem_error "Binary Operation \'Mod\' error" loc)
    )
    | Bit_And | And -> (
        match (ltype, rtype) with
        | (Int, Int) | (Bool, Bool) -> (Llvm.build_and lexpr rexpr "and" bld, ltype)
        | _ -> raise (sem_error "Binary Operation \'Bit And | And\' error" loc)
    )
    | Bit_Or | Or -> (
        match (ltype, rtype) with
        | (Int, Int) | (Bool, Bool) -> (Llvm.build_or lexpr rexpr "or" bld, ltype)
        | _ -> raise (sem_error "Binary Operation \'Bit Or | Or\' error" loc)
    )
    | Bit_Xor -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_xor lexpr rexpr "xor" bld, ltype)
        | _ -> raise (sem_error "Binary Operation \'Bit Xor\' error" loc)
    )
    | Shift_Left -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_shl lexpr rexpr "shift_left" bld, ltype)
        | _ -> raise (sem_error "Binary Operation \'Shift Left\' error" loc)
    )
    | Shift_Right -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_ashr lexpr rexpr "shift_right" bld, ltype)
        | _ -> raise (sem_error "Binary Operation \'Shift Right\' error" loc)
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
        | _ -> raise (sem_error "Binary Operation \'comparison\' error" loc)
    )
and get_icmp_typ op =
    match op with
    | Equal -> Llvm.Icmp.Eq
    | Neq -> Llvm.Icmp.Ne
    | Less -> Llvm.Icmp.Slt
    | Leq -> Llvm.Icmp.Sle
    | Greater -> Llvm.Icmp.Sgt
    | Geq -> Llvm.Icmp.Sge
    | _ -> raise (sem_error "Unexpected error" Location.dummy_code_pos)
and get_fcmp_typ op =
    match op with
    | Equal -> Llvm.Fcmp.Ueq
    | Neq -> Llvm.Fcmp.Une
    | Less -> Llvm.Fcmp.Ult
    | Leq -> Llvm.Fcmp.Ule
    | Greater -> Llvm.Fcmp.Ugt
    | Geq -> Llvm.Fcmp.Uge
    | _ -> raise (sem_error "Unexpected error" Location.dummy_code_pos)