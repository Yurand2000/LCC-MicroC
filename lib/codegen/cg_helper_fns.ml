open Symbol_table
open Cg_local_types

(* Constants *)
let const_zero typs = Llvm.const_int (get_llvm_int typs) 0
let const_one typs = Llvm.const_int (get_llvm_int typs) 1
let null_ptr typ = Llvm.const_null (Llvm.pointer_type typ)

(* SizeOf type *)
let get_size_of_type typs typ =
    let ptr = Llvm.const_gep (null_ptr typ) [|const_one typs|] in
    Llvm.const_ptrtoint ptr (get_llvm_int typs)

(* Codegen LLVM function declaration *)
let declare_llvm_fn (_ctx, md) (typs, env) fn_name fn_type =
    let fn_lltyp = get_llvm_type typs fn_type in
    let fn_decl = Llvm.declare_function fn_name fn_lltyp md in
    add_entry fn_name (fn_decl, fn_type) env

(* Codegen LLVM function definition *)
let define_llvm_fn (_ctx, md) (typs, env) fn_name fn_type =
    let fn_lltyp = get_llvm_type typs fn_type in
    let fn_decl = Llvm.define_function fn_name fn_lltyp md in
    add_entry fn_name (fn_decl, fn_type) env

(* Codegen default value for a given type *)
let rec cg_default_value typs typ =
    match typ with
    | Int -> Llvm.const_int (get_llvm_int typs) 0
    | Float -> Llvm.const_float (get_llvm_float typs) 0.0
    | Bool -> Llvm.const_int (get_llvm_bool typs) 0
    | Char -> Llvm.const_int (get_llvm_char typs) 0
    | Void -> raise_error "Void cannot have values." Location.dummy_code_pos
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
    | Fun(_) ->
        raise_error "No default value for function types" Location.dummy_code_pos