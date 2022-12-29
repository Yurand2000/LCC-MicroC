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

(* Ast.typ to Llvm types *)
let rec get_llvm_type typ =
    match typ with
    | TypI -> int_type
    | TypF -> float_type
    | TypB -> bool_type
    | TypC -> char_type
    | TypA(typ, size) -> failwith "Not implemented"
    | TypP(typ) -> pointer_type (get_llvm_type typ)
    | TypS(id) -> failwith "Not implemented"
    | TypV -> void_type
and get_size_of_type typ =
    get_type_size (get_llvm_type typ)

(* Other *)
let sem_error = Unexpected_error "Semantic Analysis should have failed."

let rec to_llvm_module ast =
    let md = Llvm.create_module ctx "module" in
    let env = empty_table in
    let _ = match ast with | Prog(decls) -> (
        List.fold_left (cg_topdecl (ctx, md)) env decls
    ) in
    md

type typ =
    | Int | Float | Bool | Char | Void | Ptr of typ | Array of typ * int option
    | Struct of Ast.identifier

and cg_topdecl ctx_mod env decl =
    match decl.node with
    | Fundecl(fun_decl) -> cg_fun_def ctx_mod env fun_decl
    | Vardec(typ, id, expr) -> cg_global_var ctx_mod env (typ, id, expr)
    | StructDecl(id, fields) -> cg_struct_def ctx_mod env (id, fields)

and cg_global_var (ctx, md) env (typ, id, expr) =
    failwith "Not implemented"

and cg_struct_def (ctx, md) env (id, fields) =
    failwith "Not implemented"

and cg_fun_def (ctx, md) env { typ=ret_typ; fname=id; formals=formals; body=body; } =
    failwith "Not implemented"

let cg_expr (ctx, env, bld) expr =
    match expr.node with
    | ILiteral(_) | FLiteral(_) | CLiteral(_) 
    | BLiteral(_) | SLiteral(_) | SizeOf(_) -> 
        cg_literals ctx expr
    | Access(access) -> failwith "Not implemented"
    | Assign(access, expr) -> failwith "Not implemented"
    | Addr(access) -> failwith "Not implemented"
    | UnaryOp(op, expr) -> cg_un_op (ctx, env, bld) op expr
    | BinaryOp(op, lexpr, rexpr) -> cg_bin_op (ctx, env, bld) op lexpr rexpr
    | CommaOp(lexpr, rexpr) -> failwith "Not implemented"
    | Call(id, args) -> failwith "Not implemented"

and cg_const_expr (ctx, env) expr =
    match expr.node with
    | ILiteral(_) | FLiteral(_) | CLiteral(_) 
    | BLiteral(_) | SLiteral(_) | SizeOf(_) -> 
        cg_literals ctx expr
    | Access(access) ->
        cg_const_access ctx access
    | Addr(access) -> 
        let access = cg_const_access (ctx, env) access in
        Llvm.const_gep access [|const_zero|]
    | _ -> raise sem_error
and cg_const_access (ctx, env) access =
    match access.node with
    | AccVar(id) -> lookup id env
    | AccDeref(expr) -> (
            match expr.node with
            | Addr(access) -> cg_const_access env access
            | _ -> raise sem_error
    )
    | _ -> raise sem_error

and cg_literals ctx expr =
    match expr.node with
    | ILiteral(value) -> (Llvm.const_int int_type value, Int)
    | FLiteral(value) -> (Llvm.const_float float_type value, Float)
    | CLiteral(value) -> (Llvm.const_int char_type (Char.code value), Char)
    | BLiteral(value) -> (Llvm.const_int bool_type (Bool.to_int value), Bool)
    | SLiteral(value) -> (Llvm.const_stringz ctx value, Ptr(Char))
    | SizeOf(typ) -> (Llvm.const_int int_type (get_size_of_type typ), Int)
    | _ -> raise sem_error

and cg_un_op (ctx, env, bld) op expr =
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

and cg_bin_op (ctx, env, bld) op lexpr rexpr =
    let (lexpr, ltyp) = cg_expr (ctx, env, bld) lexpr in
    let (rexpr, rtyp) = cg_expr (ctx, env, bld) rexpr in
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
        | (Int, Int) -> (Llvm.build_ashl lexpr rexpr "shift_right" bld, ltype)
        | _ -> raise sem_error
    )
    | Equal | Neq
    | Less | Leq
    | Greater | Geq -> (
        let icmp_typ = 
        in
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