(*
let to_llvm_module _ =
    failwith "Not Implemented"
*)

open Ast
open Symbol_table

(* Global Context *)
let ctx = Llvm.global_context ()

(* LLVM types *)
let void_type = Llvm.void_type ctx
let int_type = Llvm.i32_type ctx
let bool_type = Llvm.i1_type ctx
let char_type = Llvm.i8_type ctx
let float_type = Llvm.float_type ctx
let pointer_type typ = Llvm.pointer_type typ
let array_type typ size = Llvm.array_type typ size

(* Constants *)
let const_zero = Llvm.const_int int_type 0
let const_one = Llvm.const_int int_type 1
let null_ptr typ = Llvm.const_null (Llvm.pointer_type typ)

(* SizeOf type *)
let get_type_size typ =
    let ptr = Llvm.const_gep (null_ptr typ) [|const_one|] in
    Llvm.const_ptrtoint ptr int_type

(* Local Types *)
type typ =
    | Int | Float | Bool | Char | Void | Ptr of typ
    | Array of typ * int option | Struct of Ast.identifier

(* Ast.typ to Local types *)
let rec get_local_typ typ =
    match typ with
    | TypI -> Int
    | TypF -> Float
    | TypB -> Bool
    | TypC -> Char
    | TypA(typ, size) -> Array(get_local_typ typ, size)
    | TypP(typ) -> Ptr(get_local_typ typ)
    | TypS(id) -> Struct(id)
    | TypV -> Void

(* Types to Llvm types *)
let rec get_llvm_type typ =
    match typ with
    | Int -> int_type
    | Float -> float_type
    | Bool -> bool_type
    | Char -> char_type
    | Array(typ, size) -> failwith "Not implemented"
    | Ptr(typ) -> pointer_type (get_llvm_type typ)
    | Struct(id) -> failwith "Not implemented"
    | Void -> void_type
and get_size_of_type typ =
    get_type_size (get_llvm_type typ)

(* Other *)
exception Unexpected_error of string
let sem_error = (Unexpected_error "Semantic Analysis should have failed.")

(* Main Function *)
let rec to_llvm_module ast =
    let md = Llvm.create_module ctx "module" in
    let env = empty_table in
    let _ = match ast with | Prog(decls) -> (
        List.fold_left (cg_topdecl (ctx, md)) env decls
    ) in
    md

(* Generate code for Top Declarations *)
and cg_topdecl ctx_mod env decl =
    match decl.node with
    | Fundecl(fun_decl) -> cg_fun_def ctx_mod env fun_decl
    | Vardec(typ, id, expr) -> cg_global_var ctx_mod env (typ, id, expr)
    | StructDecl(id, fields) -> cg_struct_def ctx_mod env (id, fields)

(* Generate code for Variable definition *)
and cg_global_var (ctx, md) env (typ, id, expr) =
    failwith "Not implemented"

(* Generate code for Struct definition *)
and cg_struct_def (ctx, md) env (id, fields) =
    failwith "Not implemented"

(* Generate code for Function definition *)
and cg_fun_def (ctx, md) env { typ=ret_typ; fname=id; formals=formals; body=body; } =
    failwith "Not implemented"

(* Generate code for Statements *)
let rec cg_stmt (ctx, env, bld) stmt =
    match stmt.node with
    | If(guard_expr, then_stmts, else_stmts) ->
        cg_if_stmt (ctx, env, bld) guard_expr then_stmts else_stmts
    | While(guard_expr, stmts) ->
        cg_while_stmt (ctx, env, bld) guard_expr stmts
    | Expr(expr) ->
        let _ = cg_expr (ctx, env, bld) expr in
        env
    | Return(expr) -> (
        match expr with
        | Some(expr) -> (
            let (expr, _) = cg_expr (ctx, env, bld) expr in
            let _ = Llvm.build_ret expr bld in
            env
        )
        | None ->
            let _ = Llvm.build_ret_void bld in
            env
    )
    | Block(stmts) -> (
        let build_stmt ctx bld env stmt_or_decl =
            cg_stmt_or_dec (ctx, env, bld) stmt_or_decl
        in
        let env = begin_block env in
        let env = List.fold_left (build_stmt ctx bld) env stmts in
        end_block env
    )
and cg_stmt_or_dec (ctx, env, bld) stmt_or_dec = (* Code for Statement Or Declarations *)
    match stmt_or_dec.node with
    | Dec(typ, id) -> (
        let typ = get_local_typ typ in
        match typ with
        | Array(typ, Some(size)) -> (
            let size = Llvm.const_int int_type size in
            let var = Llvm.build_array_alloca (get_llvm_type typ) size id bld in
            add_entry id (var, typ) env
        )
        | Array(typ, None) -> raise sem_error
        | Struct(id) -> failwith "Not implemented"
        | _ -> (
            let var = Llvm.build_alloca (get_llvm_type typ) id bld in
            add_entry id (var, typ) env
        )
    )
    | Stmt(stmt) ->
        cg_stmt (ctx, env, bld) stmt
and cg_if_stmt (ctx, env, bld) guard then_stmt else_stmt = (* Code generation for If statements *)
    (* Build then and else basic blocks *)
    let fn = Llvm.block_parent (Llvm.insertion_block bld) in
    let then_bb = Llvm.append_block ctx "if_then" fn in
    let else_bb = Llvm.append_block ctx "if_else" fn in

    (* Evaluate guard and build branch instruction *)
    let (guard, _) = cg_expr (ctx, env, bld) guard in
    let _ = Llvm.build_cond_br guard then_bb else_bb bld in

    (* Build then and else branches *)
    let _ = Llvm.position_at_end then_bb bld in
    let env = cg_stmt (ctx, env, bld) then_stmt in
    let _ = Llvm.position_at_end else_bb bld in
    let env = cg_stmt (ctx, env, bld) else_stmt in

    (* Build branches to continue block if needed *)
    let tbranch_returns = is_return_present then_stmt in
    let ebranch_returns = is_return_present else_stmt in
    match (tbranch_returns, ebranch_returns) with
    | (true, true) -> env
    | _ -> (
        let cnt_bb = Llvm.append_block ctx "if_cnt" fn in
        let _ = if tbranch_returns then (
            let _ = Llvm.position_at_end then_bb bld in
            let _ = Llvm.build_br cnt_bb bld in ()
        ) else () in
        let _ = if ebranch_returns then (
            let _ = Llvm.position_at_end else_bb bld in
            let _ = Llvm.build_br cnt_bb bld in ()
        ) else () in
        let _ = Llvm.position_at_end cnt_bb bld in
        env
    )
and cg_while_stmt (ctx, env, bld) guard body = (* Code generation for While statements *)
    (* Build guard, loop and continue basic blocks *)
    let fn = Llvm.block_parent (Llvm.insertion_block bld) in
    let guard_bb = Llvm.append_block ctx "while_guard" fn in
    let loop_bb = Llvm.append_block ctx "while_loop" fn in
    let cnt_bb = Llvm.append_block ctx "while_cnt" fn in

    (* Jump to guard basic block *)
    let _ = Llvm.build_br guard_bb bld in

    (* Evaluate guard and do conditional jump *)
    let _ = Llvm.position_at_end guard_bb bld in
    let (guard, _) = cg_expr (ctx, env, bld) guard in
    let _ = Llvm.build_cond_br guard loop_bb cnt_bb bld in

    (* Build loop branch *)
    let _ = Llvm.position_at_end loop_bb bld in
    let env = cg_stmt (ctx, env, bld) body in
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
        | While(_, body) -> false
        | Expr(_) -> false
        | Return(_) -> true
        | Block(stmts) -> (
            let is_return_in_block previous stmt_or_dec =
                previous && (is_return_in_stmt_or_dec stmt_or_dec)
            in
            List.fold_left is_return_in_block true stmts
        )
    and is_return_in_stmt_or_dec stmt_or_dec =
        match stmt_or_dec.node with
        | Dec(_) -> false
        | Stmt(stmt) -> is_return_in_stmt stmt
    in
    is_return_in_stmt stmt

(* Generate code for Expressions *)
and cg_expr (ctx, env, bld) expr = (* Expressions *)
    match expr.node with
    | ILiteral(_) | FLiteral(_) | CLiteral(_)
    | BLiteral(_) | SLiteral(_) | SizeOf(_) ->
        cg_literals ctx expr
    | Access(access) -> cg_access (ctx, env, bld) access
    | Assign(access, expr) ->
        let (access, access_typ) = cg_access (ctx, env, bld) access in
        let (addr, _) = cg_address_of (ctx, env, bld) (access, access_typ) in
        let (expr, expr_typ) = cg_expr (ctx, env, bld) expr in
        let _ = Llvm.build_store addr expr bld in
        (access, access_typ)
    | Addr(access) ->
        let (access, access_typ) = cg_access (ctx, env, bld) access in
        cg_address_of (ctx, env, bld) (access, access_typ)
    | UnaryOp(op, expr) -> cg_un_op (ctx, env, bld) op expr
    | BinaryOp(op, lexpr, rexpr) -> cg_bin_op (ctx, env, bld) op lexpr rexpr
    | CommaOp(lexpr, rexpr) ->
        let _ = cg_expr (ctx, env, bld) lexpr in
        cg_expr (ctx, env, bld) rexpr
    | Call(id, args) ->
        let (fn, ret_typ) = lookup id env in
        let args = List.map (cg_expr (ctx, env, bld)) args in
        let args = Array.of_list (List.map fst args) in
        (Llvm.build_call fn args "fn_call" bld, ret_typ)
and cg_access (ctx, env, bld) access = (* Access Expressions *)
    match access.node with
    | AccVar(id) ->
        let (var, typ) = lookup id env in
        let (addr, _) = cg_address_of (ctx, env, bld) (var, typ) in
        (Llvm.build_load addr "load" bld, typ)
    | AccDeref(expr) -> (
        let (expr, expr_typ) = cg_expr (ctx, env, bld) expr in
        match expr_typ with
        | Ptr(typ) -> (Llvm.build_load expr "deref_load" bld, typ)
        | _ -> raise sem_error
    )
    | AccIndex(access, expr) -> (
        let (access, access_typ) = cg_access (ctx, env, bld) access in
        let (expr, expr_typ) = cg_expr (ctx, env, bld) expr in
        let (addr, _) = cg_address_of (ctx, env, bld) (access, access_typ) in
        match access_typ with
        | Array(typ, _) -> (Llvm.build_gep addr [|const_zero; expr|] "array_access" bld, typ)
        | _ -> raise sem_error
    )
    | AccDot(access, id) -> failwith "Not implemented"
    | AccArrow(expr, id) -> failwith "Not implemented"
and cg_address_of (ctx, env, bld) (var, typ) =
    (Llvm.build_gep var [|const_zero|] "addr_of" bld, Ptr(typ))

and cg_const_expr (ctx, env) expr = (* Constant Expressions *)
    match expr.node with
    | ILiteral(_) | FLiteral(_) | CLiteral(_)
    | BLiteral(_) | SLiteral(_) | SizeOf(_) ->
        cg_literals ctx expr
    | Access(access) ->
        cg_const_access (ctx, env) access
    | Addr(access) ->
        let (access, access_typ) = cg_const_access (ctx, env) access in
        (Llvm.const_gep access [|const_zero|], Ptr(access_typ))
    | _ -> raise sem_error
and cg_const_access (ctx, env) access = (* Constant Access Expressions *)
    match access.node with
    | AccVar(id) -> lookup id env
    | AccDeref(expr) -> (
            match expr.node with
            | Addr(access) -> cg_const_access (ctx, env) access
            | _ -> raise sem_error
    )
    | _ -> raise sem_error

and cg_literals ctx expr = (* Literal Expressions *)
    match expr.node with
    | ILiteral(value) -> (Llvm.const_int int_type value, Int)
    | FLiteral(value) -> (Llvm.const_float float_type value, Float)
    | CLiteral(value) -> (Llvm.const_int char_type (Char.code value), Char)
    | BLiteral(value) -> (Llvm.const_int bool_type (Bool.to_int value), Bool)
    | SLiteral(value) -> (Llvm.const_stringz ctx value, Ptr(Char))
    | SizeOf(typ) -> (get_size_of_type (get_local_typ typ), Int)
    | _ -> raise sem_error

and cg_un_op (ctx, env, bld) op expr =  (* Unary Operator Expressions *)
    let (expr, typ) = cg_expr (ctx, env, bld) expr in
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

and cg_bin_op (ctx, env, bld) op lexpr rexpr = (* Binary Operator Expressions *)
    let (lexpr, ltype) = cg_expr (ctx, env, bld) lexpr in
    let (rexpr, rtype) = cg_expr (ctx, env, bld) rexpr in
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
            let ptr_to_int = Llvm.build_ptrtoint rexpr int_type "ptr_to_int" bld in
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
            let ptr_to_int = Llvm.build_ptrtoint lexpr int_type "ptr_to_int" bld in
            (Llvm.build_icmp (get_icmp_typ op) ptr_to_int rexpr "cmp" bld, Bool)
        | (Int, Ptr(_)) ->
            let ptr_to_int = Llvm.build_ptrtoint rexpr int_type "ptr_to_int" bld in
            (Llvm.build_icmp (get_icmp_typ op) lexpr ptr_to_int "cmp" bld, Bool)
        | (Ptr(_), Ptr(_)) ->
            let lptr_to_int = Llvm.build_ptrtoint lexpr int_type "lptr_to_int" bld in
            let rptr_to_int = Llvm.build_ptrtoint rexpr int_type "rptr_to_int" bld in
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