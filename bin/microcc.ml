open Microc

(* Utility functions *)
let rec load_file filename =
    let ic = open_in filename in
    let n = in_channel_length ic in
    let s = Bytes.create n in
    really_input ic s 0 n;
    close_in ic;
    Bytes.to_string s
and make_buffer filename =
    let source = load_file filename in
    Lexing.from_string ~with_positions:true source

(* Compilation passes *)
and parse buffer =
    Parsing.parse Scanner.next_token buffer
and type_check buffer =
    let ast = parse buffer in
    Semantic_analysis.type_check ast
and compile_file buffer optimize verify_module =
    let ast = type_check buffer in
    let llmodule = Codegen.to_llvm_module ast in
    let optimize =
        match optimize with
        | true -> Optimizer.optimize_module
        | false -> Fun.id
    in
    if verify_module then Llvm_analysis.assert_valid_module llmodule;
    optimize llmodule
and compile_files files optimize verify_module =
    let compile filename =
        let buffer = make_buffer filename in
        try
            let llmodule = compile_file buffer optimize verify_module in
            (filename, llmodule)
        with
        | Scanner.Lexing_error (pos, msg) | Parsing.Syntax_error (pos, msg) ->
            handle_syntatic_error filename pos msg; failwith ""
        | Semantic_analysis.Semantic_error (pos, msg) ->
            handle_semantic_error filename pos msg; failwith ""
    in
    List.map compile files
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
and try_linking object_files rt_support output_file =
    let linker_command =
        Filename.quote_command "clang" (object_files @ [rt_support; "-o"; output_file])
    in
    let _ = Sys.command linker_command in
    ()

(* Single step compilation, for debug purposes *)
and run_scanner buffer =
    let scan buffer =
        let rec scan_tr buffer acc =
            match Scanner.next_token buffer with
            | Microc.ScannerTokens.EOF -> Microc.ScannerTokens.EOF :: acc
            | token -> scan_tr buffer (token :: acc)
        in
        List.rev (scan_tr buffer [])
    in
    let print_tokens tokens =
        let print_token acc token =
            acc ^ "\n" ^ (Microc.ScannerTokens.show_token token)
        in
        List.fold_left print_token "" tokens;
    in
    let tokens = scan buffer in
    Printf.printf "Scanning succeded!\n\n%s\n" (print_tokens tokens)
and run_parser buffer =
    let ast = parse buffer in
    Printf.printf "Parsing succeded!\n\n%s\n" (Ast.show_program ast)
and run_type_checker buffer =
    let ast = type_check buffer in
    Printf.printf "Type Checking succeded!\n\n%s\n" (Ast.show_program ast)
and dump_llvm_ir buffer optimize verify_module  =
    let llmodule = compile_file buffer optimize verify_module in
    Printf.printf "Compilation succeded!\n\n%s\n" (Llvm.string_of_llmodule llmodule)
and dump_llvm_bitcode buffer outputfile optimize verify_module  =
    let llmodule = compile_file buffer optimize verify_module in
    assert (Llvm_bitwriter.write_bitcode_file llmodule outputfile)

(* Displaying of syntatic and semantic errors *)
and handle_syntatic_error source lexeme_pos msg =
    let lines = String.split_on_char '\n' source in
    let line = List.nth lines (lexeme_pos.Location.line - 1) in
    let prefix = String.make (lexeme_pos.Location.start_column - 1) ' ' in
    let middle =
        String.make
            (lexeme_pos.Location.end_column - lexeme_pos.Location.start_column + 1)
            '^'
    in
    Printf.eprintf "\n*** Error at line %d.\n%s\n%s%s\n*** %s\n\n"
        lexeme_pos.Location.line line prefix middle msg

and handle_semantic_error source code_pos msg =
    let lines =
        String.split_on_char '\n' source
        |> List.filteri (fun line _ ->
                     code_pos.Location.start_line - 1 <= line
                     && line <= code_pos.Location.end_line - 1)
    in
    let length = List.length lines in
    if length = 1 then
        let line = List.hd lines in
        let prefix = String.make (code_pos.Location.start_column - 1) ' ' in
        let middle =
            String.make
                (code_pos.Location.end_column - code_pos.Location.start_column + 1)
                '^'
        in
        Printf.eprintf "\n*** Error at line %d.\n%s\n%s%s\n*** %s\n\n"
            code_pos.Location.start_line line prefix middle msg
    else
        let text = lines |> List.filteri (fun i _ -> i < 5) |> String.concat "\n" in
        Printf.eprintf "\n*** Error at lines %d-%d.\n%s\n*** %s\n\n"
            code_pos.Location.start_line
            (code_pos.Location.start_line + 5)
            text msg

(* Main Function *)
type action = Scan | Parse | Type_check | Dump_llvm_ir | Dump_llvm_bitcode | Compile

let () =
    try
        let action = ref Compile in
        let input_files = ref [] in
        let output_file = ref "" in
        let rt_support = ref "" in
        let output_dir = ref "." in
        let optimize = ref false in
        let verify = ref false in
        let link = ref false in
        let spec_list =
            [
                ( "-s", Arg.Unit (fun () -> action := Scan), "Scan and print tokens (onlt first file)");
                ( "-p", Arg.Unit (fun () -> action := Parse), "Parse and print AST (onlt first file)");
                ( "-t", Arg.Unit (fun () -> action := Type_check),
                    "Type checks and print the result (onlt first file)" );
                ( "-d", Arg.Unit (fun () -> action := Dump_llvm_ir),
                    "Compile and print the generated LLVM IR to stdout, in readable format (onlt first file)" );
                ( "-g", Arg.String (fun output -> action := Dump_llvm_bitcode; output_file := output),
                    "Compile and save the generated LLVM IR to output file, in bitcode format (onlt first file)" );
                ( "-dir", Arg.Set_string output_dir,
                    "Output directory (used for generating object files." );
                ( "-o", Arg.String (fun output -> link := true; output_file := output),
                    "Generate executable from object files (uses clang linker if available on the system otherwise fails)" );
                ( "-rt", Arg.Set_string rt_support,
                    "Runtime support for executable generation" );
                ( "-O", Arg.Set optimize,
                    "Optimize the generated LLVM IR (default: false)" );
                ( "-verify", Arg.Set verify,
                    "Verify the generated LLVM module (default: false)" );
            ]
        in
        let usage =
            Printf.sprintf "Usage:\t%s%s%s" Sys.argv.(0)
            "\n **   Debug mode: [-s | -p | -t | -d | -g <output>] [-O] [-verify] <file1>"
            "\n ** Compile mode: [-dir <output_directory>] [-rt <runtime_support>] [-o <output>] [-O] [-verify] <file1> [<file2>] ... \n" 
        in
        let anon_files filename = input_files := filename :: !input_files in
        let () = Arg.parse spec_list anon_files usage in
        match !input_files with
        | [] -> Arg.usage spec_list usage;
        | _ -> (
            match !action with
            | Compile -> (
                try
                    let output_file =
                        match !output_file with
                        |    "" -> "a.out"
                        | _ -> !output_file
                    in
                    let llmodules = compile_files !input_files !optimize !verify in
                    let object_files = make_output_files llmodules !output_dir in
                    if !link then
                        try_linking object_files !rt_support output_file;
                with
                | Failure(_) -> ignore(exit 1);
            )
            | _ -> (
                let source = List.hd !input_files in
                try
                    let output_file =
                        match !output_file with
                        |    "" -> "a.bc"
                        | _ -> !output_file
                    in
                    let buffer = make_buffer source in
                    match !action with
                    | Scan -> run_scanner buffer
                    | Parse -> run_parser buffer
                    | Type_check -> run_type_checker buffer
                    | Dump_llvm_ir -> dump_llvm_ir buffer !optimize !verify
                    | Dump_llvm_bitcode -> dump_llvm_bitcode buffer output_file !optimize !verify
                    | _ -> failwith "Unexpected Error"
                with
                | Scanner.Lexing_error (pos, msg) | Parsing.Syntax_error (pos, msg) ->
                    handle_syntatic_error source pos msg; ignore(exit 1);
                | Semantic_analysis.Semantic_error (pos, msg) ->
                    handle_semantic_error source pos msg; ignore(exit 1);

                if List.length !input_files > 1 then
                    Printf.printf "*** Warning! Only the first file is used for this option\n\n";
            )
        )
    with
        Sys_error msg -> Printf.eprintf "*** Error %s ***\n" msg