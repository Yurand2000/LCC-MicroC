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

(* Type Check expression: Ast.expr *)
let tc_expr env expr typ =
    env

(* Type Check variable declaration: Ast.typ * Ast.identifier * Ast.expr option *)
let tc_var_decl env (typ, id, expr) =
    let type_id = ast_type_to_typ typ in
    let env = match expr with
        | Some(expr) -> tc_expr env expr type_id
        | None -> env
    in
    add_entry id (VarDef type_id) env

(* Type Check struct declaration: Ast.identifier * (Ast.typ * Ast.identifier) list *)
let tc_struct_def env (id, fields) =
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
        | true -> update_entry id (StructDef fields) env
        | false -> failwith "Generic Error"

(* Type Check function declaration: { typ : Ast.typ; fname : string; formals : (Ast.typ * Ast.identifier) list; body : Ast.stmt; } *)
let tc_func_def env (id, ret_typ, formals, body) =
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
    | true -> update_entry id (FunDef (ret_typ, formal_types)) env
    | false -> failwith "Generic Error"

let make_default_env =
    empty_table |>
    add_entry "print" ( FunDef (Void, [Int]) ) |>
    add_entry "getint" ( FunDef (Int, []) )

(* Type Check whole program declaration: Ast.program *)
let tc_program program = 
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

(* Type Check whole program declaration: Ast.program *)
let type_check program = 
    let _ = tc_program program in
    program