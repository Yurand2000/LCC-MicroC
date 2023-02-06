open Microc
open Microcc_codegen

(* Single step compilation, for debug purposes *)
(* Scanner only *)
let run_scanner buffer =
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

(* Scanner and parser only *)
let run_parser buffer =
    let ast = parse buffer in
    Printf.printf "Parsing succeded!\n\n%s\n" (Ast.show_program ast)

(* Type Checking *)
let run_type_checker buffer tc_main_defined =
    let ast = buffer |> parse |> type_check |> type_check in
    let ast = if tc_main_defined then is_main_defined ast else ast in
    Printf.printf "Type Checking succeded!\n\n%s\n" (Ast.show_program ast)

(* Compile and Dump LLVM IR (readable) to stdout *)
let dump_llvm_ir buffer tc_main_defined optimize verify_module  =
    let ast = buffer |> parse |> type_check in
    let ast = if tc_main_defined then is_main_defined ast else ast in
    let llmodule = compile_file ast optimize verify_module in
    Printf.printf "Compilation succeded!\n\n%s\n" (Llvm.string_of_llmodule llmodule)

(* Compile and Dump LLVM IR (bytecode) to file *)
let dump_llvm_bitcode buffer outputfile tc_main_defined optimize verify_module  =
    let ast = buffer |> parse |> type_check in
    let ast = if tc_main_defined then is_main_defined ast else ast in
    let llmodule = compile_file ast optimize verify_module in
    assert (Llvm_bitwriter.write_bitcode_file llmodule outputfile)