open Microc
open Microcc_utilities
open Microcc_codegen
open Microcc_single_step

(* Main Function *)
type action = Scan | Parse | Type_check | Dump_llvm_ir | Dump_llvm_bitcode | Compile

let () =
    try
        let action = ref Compile in
        let input_files = ref [] in
        let output_file = ref "" in
        let rt_support = ref "" in
        let output_dir = ref "." in
        let tc_main_defined = ref true in
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
                ( "-no_tc_main", Arg.Unit (fun () -> tc_main_defined := false),
                    "Skip control for definition of the main function. Only used for single step compilation. (default: true)" );
            ]
        in
        let usage =
            Printf.sprintf "Usage:\t%s%s%s" Sys.argv.(0)
            "\n **   Debug mode: [-s | -p | -t | -d | -g <output>] [-no_tc_main] [-O] [-verify] <file1>"
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
                        | "" -> "a.out"
                        | _ -> !output_file
                    in
                    let llmodules = compile_files !input_files !link !optimize !verify in
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
                    | Type_check -> run_type_checker buffer !tc_main_defined
                    | Dump_llvm_ir -> dump_llvm_ir buffer !tc_main_defined !optimize !verify
                    | Dump_llvm_bitcode -> dump_llvm_bitcode buffer output_file !tc_main_defined !optimize !verify
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