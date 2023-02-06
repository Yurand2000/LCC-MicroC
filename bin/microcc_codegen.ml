open Microc
open Microcc_utilities

(* Parse buffer and return an Ast.program *)
let rec parse buffer =
    Parsing.parse Scanner.next_token buffer

(* Type Check an Ast.program *)
and type_check ast =
    Semantic_analysis.type_check ast

(* Check if a valid main is defined in the given Ast.program *)
and is_main_defined ast =
    Semantic_analysis.type_check_main_defined ast

(* Compile a given Ast.program into an Llvm.llmodule *)
and compile_file ast optimize verify_module =
    let llmodule = Codegen.to_llvm_module ast in
    let optimize = if optimize then Optimizer.optimize_module else Fun.id in

    if verify_module then
        Llvm_analysis.assert_valid_module llmodule;
    optimize llmodule

(* Compile a set of files into a list of Llvm.llmodule(s) *)
and compile_files files optimize verify_module =
    let parse_and_type_check filename =
        try
            let ast = make_buffer filename |> parse |> type_check in
            (filename, ast)
        with
        | Scanner.Lexing_error (pos, msg) | Parsing.Syntax_error (pos, msg) ->
            handle_syntatic_error filename pos msg; failwith ""
        | Semantic_analysis.Semantic_error (pos, msg) ->
            handle_semantic_error filename pos msg; failwith ""
    in
    let is_main_defined is_defined (_, ast) =
        try
            let _ = is_main_defined ast in true
        with Semantic_analysis.Semantic_error (_) ->
            is_defined || false
    in
    let compile (filename, ast) =
        try
            (filename, compile_file ast optimize verify_module)
        with
        | Codegen.Unexpected_error (pos, msg) ->
            handle_codegen_error filename pos msg; failwith ""
    in
    let asts = List.map parse_and_type_check files in
    let main_defined = List.fold_left is_main_defined false asts in
    if Bool.not main_defined then
        failwith "Main function not defined or not correctly defined.";
    List.map compile asts

(* Generate object files for the current architecture *)
and make_output_files llmodules output_dir =
    Llvm_all_backends.initialize ();
    let machine_target_triple = Llvm_target.Target.default_triple () in
    let machine_target = Llvm_target.Target.by_triple machine_target_triple in
    let generator =
        Llvm_target.TargetMachine.create
        ~triple:machine_target_triple
        ~cpu:"generic"
        machine_target
    in
    let data_layout = Llvm_target.TargetMachine.data_layout generator in
    let data_layout = Llvm_target.DataLayout.as_string data_layout in
    let set_data_layouts (_, llmodule) = 
        Llvm.set_data_layout data_layout llmodule;
        Llvm.set_target_triple machine_target_triple llmodule;
    in
    let output_object_files (filename, llmodule) =
        let out_file = Filename.remove_extension filename in
        let out_file = (Filename.basename out_file) ^ ".o" in
        let out_file = Filename.concat output_dir out_file in
        let file_type = Llvm_target.CodeGenFileType.ObjectFile in
        Llvm_target.TargetMachine.emit_to_file
            llmodule file_type out_file generator;
        out_file
    in
    List.iter set_data_layouts llmodules;
    List.map output_object_files llmodules

(* Try linking the object files with clang *)
and try_linking object_files rt_support output_file =
    let _ =
        Filename.quote_command "clang" (object_files @ [rt_support; "-o"; output_file]) |>
        Sys.command
    in
    ()