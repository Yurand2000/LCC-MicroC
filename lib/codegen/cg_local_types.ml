exception Unexpected_error of Location.code_pos * string

open Ast
open Symbol_table

(* Helper exception function *)
let raise_error msg loc = raise (Unexpected_error (loc, "Semantic Analysis should have failed at this point: " ^ msg))

(* Local types used for code generation *)
type typ =
    | Int | Float | Bool | Char | Void | Ptr of typ
    | Struct of Ast.identifier
    | Array of typ * int list (* Size of each dimension *)
    | ArrayRef of typ * int (* Dimensions *)
    | Fun of typ * typ list (* Function type *)
[@@deriving show]

(* Ast.typ to local types *)
let rec get_local_typ typ =
    match typ with
    | TypI -> Int
    | TypF -> Float
    | TypB -> Bool
    | TypC -> Char
    | TypA(_, Some(_)) -> 
        let (typ, sizes) = get_array_size typ in
        Array(typ, sizes)
    | TypA(_, None) ->
        let (typ, dimentions) = get_array_dims typ in
        ArrayRef(typ, dimentions)
    | TypP(typ) -> Ptr(get_local_typ typ)
    | TypS(id) -> Struct(id)
    | TypV -> Void
and get_array_size typ =
    match typ with
    | TypA(typ, Some(size)) ->
        let (typ, sizes) = get_array_size typ in
        (typ, size :: sizes)
    | TypA(_, None) -> raise_error "Zero-Sized array" Location.dummy_code_pos
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
        get_llvm_array_type typs typ sizes
    | ArrayRef(typ, dims) ->
        let sizes = List.init dims (fun _ -> 0) in
        Llvm.pointer_type (get_llvm_array_type typs typ sizes)
    | Fun(ret_typ, arg_typs) ->
        let arg_typs = List.map (get_llvm_type typs) arg_typs in
        Llvm.function_type (get_llvm_type typs ret_typ) (Array.of_list arg_typs)
and get_llvm_int typs = get_llvm_type typs Int
and get_llvm_float typs = get_llvm_type typs Float
and get_llvm_bool typs = get_llvm_type typs Bool
and get_llvm_char typs = get_llvm_type typs Char
and get_llvm_void typs = get_llvm_type typs Void
and get_llvm_array_type typs typ sizes =
    let lltype = get_llvm_type typs typ in
    let array_of_size lltype size =
        Llvm.array_type lltype size
    in
    List.fold_left array_of_size lltype sizes

(* Looks up for a given type given a type alias, used to get struct types. *)
and lookup_type id typs =
    fst (lookup id typs)

(* This function gets the struct fields of a struct type. *)
and lookup_struct_fields struct_id typs =
    to_alist (snd (lookup struct_id typs))
and lookup_struct_field struct_id field_id typs =
    let fields = snd (lookup struct_id typs) in
    let (field_index, field_typ) = lookup field_id fields in
    (field_index, field_typ)