open Symbol_table
open Cg_local_types
open Cg_helper_fns

(* Builds the types environment available to all the programs. *)
let cg_types_env (ctx, _md) (typs, env) =
    let typs = 
        add_entry "@i32" (Llvm.i32_type ctx, empty_table) typs |>
        add_entry "@f32" (Llvm.float_type ctx, empty_table) |>
        add_entry "@bool" (Llvm.i1_type ctx, empty_table) |>
        add_entry "@char" (Llvm.i8_type ctx, empty_table) |>
        add_entry "@void" (Llvm.void_type ctx, empty_table)
    in
    (typs, env)

(* Builds the default environment available to all the programs. *)
let cg_runtime_env (_ctx, md) (typs, env) =
    let declare_fn fn_name fn_type env =
        declare_llvm_fn (_ctx, md) (typs, env) fn_name fn_type
    in
    let env =
        declare_fn "print" (Fun (Void, [Int])) env |>
        declare_fn "getint" (Fun (Int, [])) |>
        declare_fn "print_string" (Fun (Void, [Ptr Char])) |>
        declare_fn "mem_alloc" (Fun (Ptr Void, [Int])) |>
        declare_fn "mem_free" (Fun (Void, [Ptr Void]))
    in
    (typs, env)