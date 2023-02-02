open Symbol_table
open Sa_local_types

(* Type of data used in the environment table. *)
type symbol =
    | StructDef of (typ * Ast.identifier) list
    | FunDef of typ * (typ * Ast.identifier) list
    | VarDef of typ

(* Lookup for specific definitions from the environment: Functions, Variables and Structs *)
let lookup_function_def env id loc =
    match lookup_opt id env with
    | Some(FunDef(ret_typ, arg_defs)) -> (ret_typ, arg_defs)
    | Some(_) -> raise_error ("Identifier \"" ^ id ^ "\" is not a function.") loc
    | None -> raise_error ("Function \"" ^ id ^ "\" is not defined.") loc

let lookup_var_type env id loc =
    match lookup_opt id env with
    | Some(VarDef(typ)) -> typ
    | Some(_) -> raise_error ("Identifier \"" ^ id ^ "\" is not a variable.") loc
    | None -> raise_error ("Variable \"" ^ id ^ "\" is not defined.") loc

let lookup_struct_def env id loc =
    match lookup_opt id env with
    | Some(StructDef(fields)) -> fields
    | Some(_) -> raise_error ("Identifier \"" ^ id ^ "\" is not a struct.") loc
    | None -> raise_error ("Struct \"" ^ id ^ "\" is not defined.") loc

(* Builds the default environment available to all the programs. *)
let make_default_env env =
    env |>
    add_entry "print" ( FunDef (Void, [(Int, "value")]) ) |>
    add_entry "getint" ( FunDef (Int, []) ) |>
    add_entry "print_string" ( FunDef (Void, [(Ptr Char, "string")]) ) |>
    add_entry "mem_alloc" ( FunDef (Ptr Void, [(Int, "size")]) ) |>
    add_entry "mem_free" ( FunDef (Void, [(Ptr Void, "ptr")]) )