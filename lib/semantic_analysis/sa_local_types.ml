exception Semantic_error of Location.code_pos * string

open Ast
open Symbol_table

(* Helper exception function *)
let raise_error msg loc =
    raise (Semantic_error(Option.value loc ~default:Location.dummy_code_pos, msg))

(* Local types used for Semantic Analysis *)
type typ =
    | Int | Float | Bool | Char | Void
    | Ptr of typ | Array of typ * int option
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

(* Trivial conversion from types defined in the AST to the local types. *)
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

(* Type checks for various situations. *)
(* Asserts that the type has been defined in the environment and that array sizes are meaningful. *)
let rec is_valid_type typ env =
    match typ with
    | Struct(id) -> Option.is_some (lookup_opt id env)
    | Ptr(typ) -> is_valid_type typ env
    | Array(typ, size) ->
            (Option.fold ~none:true ~some:(fun s -> s > 0) size) &&
            (is_valid_type typ env) && (Bool.not (is_array_type typ env))
    | _ -> true

and is_array_type typ _env =
    match typ with
    | Array(_) -> true
    | _ -> false

(* Asserts that the type can be used as variable type. *)
and is_valid_variable_type typ _env =
    match typ with
    | Void -> false
    | Array(typ, size) -> (
            (Option.fold ~none:false ~some:(fun s -> s > 0) size) &&
            (is_valid_variable_type typ _env)
    )
    | Ptr(Void) -> true
    | Ptr(typ) -> is_valid_parameter_type typ _env
    | _ -> true

(* Asserts that the type can be used in return types of functions. *)
and is_valid_return_type typ _env =
    match typ with
    | Array(_) -> false
    | Ptr(Void) -> true
    | Ptr(typ) -> is_valid_parameter_type typ _env
    | _ -> true

(* Asserts that the type can be used as a parameter in a function. *)
and is_valid_parameter_type typ _env =
    match typ with
    | Void -> false
    | Array(typ, size) -> (
            match size with
            | None -> is_valid_parameter_type typ _env
            | Some(_) -> false
    )
    | Ptr(Void) -> true
    | Ptr(typ) -> is_valid_parameter_type typ _env
    | _ -> true

(* Asserts that the type can be used as a left expression. *)
and is_valid_lexpr_type typ _env =
    match typ with
    | Void | Array(_) -> false
    | _ -> true

(* Are two types equal? *)
and are_types_equal ltyp rtyp =
    match (ltyp, rtyp) with
    | (Array(ltyp, _), Array(rtyp, _)) -> ltyp = rtyp
    | _ -> ltyp = rtyp

(* Can a type be implicitly casted to another type? (typ is casted to ctyp) *)
and can_be_implicitly_casted ctyp typ =
    match (ctyp, typ) with
    | (Ptr(Void), Ptr(_)) -> true
    | (Ptr(ctyp), Array(atyp, _)) when can_be_implicitly_casted ctyp atyp -> true
    | (Array(ctyp, _), Ptr(atyp)) when can_be_implicitly_casted ctyp atyp -> true
    | _ -> are_types_equal ctyp typ