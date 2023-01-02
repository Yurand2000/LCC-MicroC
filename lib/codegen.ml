(*
let to_llvm_module _ =
    failwith "Not Implemented"
*)

open Ast
open Symbol_table

(* Exceptions *)
exception Unexpected_error of string
let sem_error = (Unexpected_error "Semantic Analysis should have failed at this point.")

(* LLVM types *)
let void_type ctx = Llvm.void_type ctx
let int_type ctx = Llvm.i32_type ctx
let bool_type ctx = Llvm.i1_type ctx
let char_type ctx = Llvm.i8_type ctx
let float_type ctx = Llvm.float_type ctx
let pointer_type ctx typ = Llvm.pointer_type (typ ctx)
let function_type ctx ret_typ arg_types =
    let arg_types = List.map (fun x -> x ctx) arg_types in
    Llvm.function_type (ret_typ ctx) (Array.of_list arg_types)

(* Constants *)
let const_zero ctx = Llvm.const_int (int_type ctx) 0
let const_one ctx = Llvm.const_int (int_type ctx) 1
let null_ptr ctx typ = Llvm.const_null (pointer_type ctx typ)

(* SizeOf type *)
let get_type_size ctx typ =
    let ptr = Llvm.const_gep (null_ptr ctx typ) [|const_one ctx|] in
    Llvm.const_ptrtoint ptr (int_type ctx)

(* Local Types *)
type typ =
    | Int | Float | Bool | Char | Void | Ptr of typ
    | Struct of Ast.identifier
    | Array of typ * int list (* Size of each dimension *)
    | ArrayRef of typ * int (* Dimensions *)

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
    | TypA(_, None) -> raise sem_error
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
    | Int -> int_type
    | Float -> float_type
    | Bool -> bool_type
    | Char -> char_type
    | Array(typ, sizes) ->
        get_array_type typs typ sizes
    | ArrayRef(typ, dims) ->
        let sizes = List.init dims (fun _ -> 0) in
        get_array_type typs typ sizes
    | Ptr(typ) -> fun ctx -> pointer_type ctx (get_llvm_type typs typ)
    | Struct(id) -> lookup_type id typs
    | Void -> void_type
and get_array_type typs typ sizes =
    let ll_typ = get_llvm_type typs typ in
    let fn ll_typ size ctx = Llvm.array_type (ll_typ ctx) size in
    List.fold_left fn ll_typ sizes
and get_size_of_type ctx typs typ =
    get_type_size ctx (get_llvm_type typs typ)
and lookup_type id typs =
    fst (lookup id typs)
and lookup_struct_field struct_id field_id typs =
    let fields = snd (lookup struct_id typs) in
    let (field_index, field_typ) = lookup field_id fields in
    (field_index, field_typ)

(* Main Function *)
let rec to_llvm_module ast =
    let ctx = Llvm.global_context () in
    let md = Llvm.create_module ctx "module" in
    let (typs, env) = cg_runtime_env (ctx, md) (empty_table, empty_table) in
    let _ = match ast with | Prog(decls) -> (
        List.fold_left (cg_topdecl (ctx, md)) (typs, env) decls
    ) in
    md

and cg_runtime_env (ctx, md) (typs, env) =
    let print_fn = Llvm.declare_function "print" (function_type ctx void_type [int_type]) md in
    let env = add_entry "print" (print_fn, Void) env in
    let getint_fn = Llvm.declare_function "getint" (function_type ctx int_type []) md in
    let env = add_entry "getint" (getint_fn, Int) env in
    (typs, env)

(* Generate code for Top Declarations *)
and cg_topdecl ctx env decl =
    match decl.node with
    | Fundecl(fun_decl) -> cg_fun_def ctx env fun_decl
    | Vardec(typ, id, expr) -> cg_global_var ctx env (typ, id, expr)
    | StructDecl(id, fields) -> cg_struct_def ctx env (id, fields)

(* Generate code for Variable definition *)
and cg_global_var (ctx, md) (typs, env) (typ, id, expr) =
    match expr with
    | Some(expr) -> (
        let (expr, typ) = cg_const_expr ctx (typs, env) expr in
        let var = Llvm.define_global id expr md in
        let env = add_entry id (var, typ) env in
        (typs, env)
    )
    | None -> (
        let typ = get_local_typ typ in
        let ll_typ = get_llvm_type typs typ in
        let var = Llvm.declare_global (ll_typ ctx) id md in
        let env = add_entry id (var, typ) env in
        (typs, env)
    )

(* Generate code for Struct definition *)
and cg_struct_def (ctx, _md) (typs, env) (id, fields) =
    let fields = List.map (fun (typ, id) -> (get_local_typ typ, id)) fields in

    (* Build struct llvm type *)
    let field_types = List.map (fun (typ, _) -> (get_llvm_type typs typ) ctx) fields in
    let struct_type = (fun ctx -> Llvm.named_struct_type ctx id) in
    let _ = Llvm.struct_set_body (struct_type ctx) (Array.of_list field_types) false in

    (* Build field table for struct *)
    let add_field (fields, curr_index) (typ, id) =
        (add_entry id (curr_index, typ) fields, curr_index + 1)
    in
    let (fields, _) = List.fold_left add_field (empty_table, 0) fields in

    (add_entry id (struct_type, fields) typs, env)

(* Generate code for Function definition *)
and cg_fun_def (ctx, md) (typs, env) { typ=ret_typ; fname=id; formals=formals; body=body; } =
    let ret_typ = get_local_typ ret_typ in
    let ll_ret_typ = get_llvm_type typs ret_typ in
    let ll_arg_typs = List.map (fun (t, _) -> get_llvm_type typs (get_local_typ t)) formals in
    let fn = Llvm.define_function id (function_type ctx ll_ret_typ ll_arg_typs) md in
    let env = add_entry id (fn, ret_typ) env in (* Add function in the environment *)

    let entry_bb = Llvm.entry_block fn in
    let bld = Llvm.builder_at_end ctx entry_bb in
    (typs, cg_stmt (ctx, bld) (typs, env) body)

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
        match typ with
        | Struct(id) -> (
            let ll_typ = lookup_type id typs in
            let var = Llvm.build_alloca (ll_typ ctx) id bld in
            add_entry id (var, typ) env
        )
        | _ -> (
            let ll_typ = get_llvm_type typs typ in
            let var = Llvm.build_alloca (ll_typ ctx) id bld in
            add_entry id (var, typ) env
        )
    )
    | Stmt(stmt) -> cg_stmt (ctx, bld) (typs, env) stmt

and cg_if_stmt (ctx, bld) (typs, env) guard then_stmt else_stmt = (* Code generation for If statements *)
    (* Build then and else basic blocks *)
    let fn = Llvm.block_parent (Llvm.insertion_block bld) in
    let then_bb = Llvm.append_block ctx "if_then" fn in
    let else_bb = Llvm.append_block ctx "if_else" fn in

    (* Evaluate guard and build branch instruction *)
    let (guard, _) = cg_expr (ctx, bld) (typs, env) guard in
    let _ = Llvm.build_cond_br guard then_bb else_bb bld in

    (* Build then and else branches *)
    let _ = Llvm.position_at_end then_bb bld in
    let env = cg_stmt (ctx, bld) (typs, env) then_stmt in
    let _ = Llvm.position_at_end else_bb bld in
    let env = cg_stmt (ctx, bld) (typs, env) else_stmt in

    (* Build branches to continue block if needed *)
    let tbranch_returns = is_return_present then_stmt in
    let ebranch_returns = is_return_present else_stmt in
    match (tbranch_returns, ebranch_returns) with
    | (true, true) -> env
    | _ -> (
        let cnt_bb = Llvm.append_block ctx "if_cnt" fn in
        let _ = if Bool.not tbranch_returns then (
            let _ = Llvm.position_at_end then_bb bld in
            let _ = Llvm.build_br cnt_bb bld in ()
        ) else () in
        let _ = if Bool.not ebranch_returns then (
            let _ = Llvm.position_at_end else_bb bld in
            let _ = Llvm.build_br cnt_bb bld in ()
        ) else () in
        let _ = Llvm.position_at_end cnt_bb bld in
        env
    )
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
                previous && (is_return_in_stmt_or_dec stmt_or_dec)
            in
            match stmts with
            | [] -> false
            | _ -> List.fold_left is_return_in_block true stmts
        )
    and is_return_in_stmt_or_dec stmt_or_dec =
        match stmt_or_dec.node with
        | Dec(_) -> false
        | Stmt(stmt) -> is_return_in_stmt stmt
    in
    is_return_in_stmt stmt

(* Generate code for Expressions *)
and cg_expr (ctx, bld) (typs, env) expr = (* Expressions *)
    match expr.node with
    | ILiteral(_) | FLiteral(_) | CLiteral(_)
    | BLiteral(_) | SLiteral(_) | SizeOf(_) ->
        cg_literals ctx typs expr

    | Access(access) -> (
        let (addr, addr_typ) = cg_access (ctx, bld) (typs, env) access in
        match addr_typ with
        | Ptr(typ) -> (Llvm.build_load addr "load" bld, typ)
        | _ -> raise sem_error
    )
    | Assign(access, expr) -> (
        let (expr, expr_typ) = cg_expr (ctx, bld) (typs, env) expr in
        let (addr, _) = cg_access (ctx, bld) (typs, env) access in
        let _ = Llvm.build_store addr expr bld in
        (expr, expr_typ)
    )
    | Addr(access) ->
        cg_access (ctx, bld) (typs, env) access

    | UnaryOp(op, expr) ->
        cg_un_op (ctx, bld) (typs, env) op expr
    | BinaryOp(op, lexpr, rexpr) ->
        cg_bin_op (ctx, bld) (typs, env) op lexpr rexpr

    | CommaOp(lexpr, rexpr) ->
        let _ = cg_expr (ctx, bld) (typs, env) lexpr in
        cg_expr (ctx, bld) (typs, env) rexpr

    | Call(id, args) ->
        let (fn, ret_typ) = lookup id env in
        let args = List.map (fun expr -> fst (cg_expr (ctx, bld) (typs, env) expr)) args in
        match ret_typ with
        | Void -> (Llvm.build_call fn (Array.of_list args) "" bld, ret_typ)
        | _ -> (Llvm.build_call fn (Array.of_list args) "fn_call" bld, ret_typ)
and cg_access (ctx, bld) (typs, env) access = (* Access Expressions, returns address of variable *)
    match access.node with
    | AccVar(id) ->
        let (var, typ) = lookup id env in
        cg_address_of (ctx, bld) (var, typ)
    | AccDeref(expr) -> (
        cg_expr (ctx, bld) (typs, env) expr
    )
    | AccIndex(access, expr) -> (
        let (addr, data_typ, indices) = cg_array_access (ctx, bld) (typs, env) access expr in
        (Llvm.build_gep addr (Array.of_list (const_zero ctx :: indices)) "array_access" bld, Ptr(data_typ))
    )
    | AccDot(access, field_id) -> (
        let (addr, addr_typ) = cg_access (ctx, bld) (typs, env) access in
        match addr_typ with
        | Struct(struct_id) -> cg_struct_access (ctx, bld) typs addr struct_id field_id
        | _ -> raise sem_error
    )
    | AccArrow(expr, field_id) -> (
        let (addr, addr_typ) = cg_expr (ctx, bld) (typs, env) expr in
        match addr_typ with
        | Ptr(Struct(struct_id)) -> cg_struct_access (ctx, bld) typs addr struct_id field_id
        | _ -> raise sem_error
    )
and cg_address_of (ctx, bld) (var, typ) =
    (Llvm.build_gep var [|const_zero ctx|] "addr_of" bld, Ptr(typ))
and cg_struct_access (_ctx, bld) typs addr struct_id field_id =
    let (field_index, field_typ) = lookup_struct_field struct_id field_id typs in
    let addr = Llvm.build_struct_gep addr field_index "struct_access" bld in
    (addr, field_typ)
and cg_array_access (ctx, bld) (typs, env) access expr =
    let (index, _) = cg_expr (ctx, bld) (typs, env) expr in
    match access.node with
    | AccIndex(access, expr) -> (
        let (addr, data_typ, indices) = cg_array_access (ctx, bld) (typs, env) access expr in
        (addr, data_typ, index :: indices)
    )
    | _ -> (
        let (addr, addr_typ) = cg_access (ctx, bld) (typs, env) access in
        match addr_typ with
        | Array(typ, _) -> (addr, typ, [ index ])
        | _ -> raise sem_error
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
        cg_const_address_of ctx (access, access_typ)
    | _ -> raise sem_error
and cg_const_access ctx (_typs, env) access = (* Constant Access Expressions *)
    match access.node with
    | AccVar(id) -> lookup id env
    | AccDeref(expr) -> (
        match expr.node with
        | Addr(access) -> cg_const_access ctx (_typs, env) access
        | _ -> raise sem_error
    )
    | _ -> raise sem_error
and cg_const_address_of ctx (var, typ) =
    (Llvm.const_gep var [|const_zero ctx|], Ptr(typ))

and cg_literals ctx typs expr = (* Literal Expressions *)
    match expr.node with
    | ILiteral(value) -> (Llvm.const_int (int_type ctx) value, Int)
    | FLiteral(value) -> (Llvm.const_float (float_type ctx) value, Float)
    | CLiteral(value) -> (Llvm.const_int (char_type ctx) (Char.code value), Char)
    | BLiteral(value) -> (Llvm.const_int (bool_type ctx) (Bool.to_int value), Bool)
    | SLiteral(value) -> (Llvm.const_stringz ctx value, Ptr(Char))
    | SizeOf(typ) -> (get_size_of_type ctx typs (get_local_typ typ), Int)
    | _ -> raise sem_error

and cg_un_op (ctx, bld) (typs, env) op expr =  (* Unary Operator Expressions *)
    let (expr, typ) = cg_expr (ctx, bld) (typs, env) expr in
    match op with
    | Pos -> (expr, typ)
    | Neg -> (
        match typ with
        | Int | Bool | Char -> (Llvm.build_neg expr "negate" bld, typ)
        | Float -> (Llvm.build_fneg expr "negate" bld, typ)
        | _ -> raise sem_error
    )
    | Bit_Not | Not -> (
        match typ with
        | Int | Bool | Char -> (Llvm.build_not expr "not" bld, typ)
        | _ -> raise sem_error
    )

and cg_bin_op (ctx, bld) (typs, env) op lexpr rexpr = (* Binary Operator Expressions *)
    let (lexpr, ltype) = cg_expr (ctx, bld) (typs, env) lexpr in
    let (rexpr, rtype) = cg_expr (ctx, bld) (typs, env) rexpr in
    match op with
    | Add -> (
        match (ltype, rtype) with
        | (Int, Int) | (Char, Char) -> (Llvm.build_add lexpr rexpr "add" bld, ltype)
        | (Float, Float) -> (Llvm.build_fadd lexpr rexpr "add" bld, ltype)
        | (Ptr(_), Int) -> (Llvm.build_gep lexpr [|rexpr|] "add" bld, ltype)
        | (Int, Ptr(_)) -> (Llvm.build_gep rexpr [|lexpr|] "add" bld, rtype)
        | _ -> raise sem_error
    )
    | Sub -> (
        match (ltype, rtype) with
        | (Int, Int) | (Char, Char) -> (Llvm.build_sub lexpr rexpr "sub" bld, ltype)
        | (Float, Float) -> (Llvm.build_fsub lexpr rexpr "sub" bld, ltype)
        | (Ptr(_), Int) ->
            let negated = Llvm.build_neg rexpr "negate" bld in
            (Llvm.build_gep lexpr [|negated|] "sub" bld, ltype)
        | (Ptr(_), Ptr(_)) ->
            let ptr_to_int = Llvm.build_ptrtoint rexpr (int_type ctx) "ptr_to_int" bld in
            let negated = Llvm.build_neg ptr_to_int "negate" bld in
            (Llvm.build_gep lexpr [|negated|] "sub" bld, ltype)
        | _ -> raise sem_error
    )
    | Mult -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_mul lexpr rexpr "mul" bld, ltype)
        | (Float, Float) -> (Llvm.build_fmul lexpr rexpr "mul" bld, ltype)
        | _ -> raise sem_error
    )
    | Div -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_sdiv lexpr rexpr "div" bld, ltype)
        | (Float, Float) -> (Llvm.build_fdiv lexpr rexpr "div" bld, ltype)
        | _ -> raise sem_error
    )
    | Mod -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_srem lexpr rexpr "mod" bld, ltype)
        | _ -> raise sem_error
    )
    | Bit_And | And -> (
        match (ltype, rtype) with
        | (Int, Int) | (Bool, Bool) -> (Llvm.build_and lexpr rexpr "and" bld, ltype)
        | _ -> raise sem_error
    )
    | Bit_Or | Or -> (
        match (ltype, rtype) with
        | (Int, Int) | (Bool, Bool) -> (Llvm.build_or lexpr rexpr "or" bld, ltype)
        | _ -> raise sem_error
    )
    | Bit_Xor -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_xor lexpr rexpr "xor" bld, ltype)
        | _ -> raise sem_error
    )
    | Shift_Left -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_shl lexpr rexpr "shift_left" bld, ltype)
        | _ -> raise sem_error
    )
    | Shift_Right -> (
        match (ltype, rtype) with
        | (Int, Int) -> (Llvm.build_ashr lexpr rexpr "shift_right" bld, ltype)
        | _ -> raise sem_error
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
            let ptr_to_int = Llvm.build_ptrtoint lexpr (int_type ctx) "ptr_to_int" bld in
            (Llvm.build_icmp (get_icmp_typ op) ptr_to_int rexpr "cmp" bld, Bool)
        | (Int, Ptr(_)) ->
            let ptr_to_int = Llvm.build_ptrtoint rexpr (int_type ctx) "ptr_to_int" bld in
            (Llvm.build_icmp (get_icmp_typ op) lexpr ptr_to_int "cmp" bld, Bool)
        | (Ptr(_), Ptr(_)) ->
            let lptr_to_int = Llvm.build_ptrtoint lexpr (int_type ctx) "lptr_to_int" bld in
            let rptr_to_int = Llvm.build_ptrtoint rexpr (int_type ctx) "rptr_to_int" bld in
            (Llvm.build_icmp (get_icmp_typ op) lptr_to_int rptr_to_int "cmp" bld, Bool)
        | _ -> raise sem_error
    )
and get_icmp_typ op =
    match op with
    | Equal -> Llvm.Icmp.Eq
    | Neq -> Llvm.Icmp.Ne
    | Less -> Llvm.Icmp.Slt
    | Leq -> Llvm.Icmp.Sle
    | Greater -> Llvm.Icmp.Sgt
    | Geq -> Llvm.Icmp.Sge
    | _ -> raise sem_error
and get_fcmp_typ op =
    match op with
    | Equal -> Llvm.Fcmp.Ueq
    | Neq -> Llvm.Fcmp.Une
    | Less -> Llvm.Fcmp.Ult
    | Leq -> Llvm.Fcmp.Ule
    | Greater -> Llvm.Fcmp.Ugt
    | Geq -> Llvm.Fcmp.Uge
    | _ -> raise sem_error