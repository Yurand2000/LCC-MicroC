open Microc

let read_args =
  let usage_msg = "-dir <test files directory> -ext <test files extension>" in
  let input_dir = ref "" in
  let ext = ref "" in
  let speclist = 
    [
      ("-dir", Arg.Set_string input_dir, "Directory with test files");
      ("-ext", Arg.Set_string ext, "code files extension");
    ]
  in
  let _ = Arg.parse speclist (fun _ -> ()) usage_msg in
  (!input_dir, !ext)

let rec main () =
  let (input_dir, ext) = read_args in
  let _ = if Sys.file_exists input_dir then () else failwith ("\"" ^ input_dir ^ "\" does not exist!") in
  let test_files = match (Sys.is_directory input_dir) with
    | true -> Array.to_list (Sys.readdir input_dir)
    | false -> failwith ("\"" ^ input_dir ^ "\" is not a directory!")
  in
  let (successes, fails, other) = get_files test_files ext in
  let successes = List.map (fun fname -> input_dir ^ "/" ^ fname) successes in
  let fails = List.map (fun fname -> input_dir ^ "/" ^ fname) fails in
  let (successes, fails) = (load_files successes, load_files fails) in
  List.iter (test_input_file true) successes;
  List.iter (test_input_file false) fails;
  let other = List.length other in
  match other > 0 with
    | true -> 
      print_long_line ();
      Printf.eprintf "*** Warning: %d tests files are not run because it is unknown if they are success or fail tests." other
    | false -> ()

and get_files files ext =
  let has_ext ext file_name =
    String.ends_with ~suffix:ext file_name
  in
  let is_success_test file_name =
    String.starts_with ~prefix:"test-" file_name
  in
  let is_failure_test file_name =
    String.starts_with ~prefix:"fail-" file_name
  in
  let valid_files = List.filter (has_ext ext) files in
  let (success, other) = List.partition is_success_test valid_files in
  let (failures, other) = List.partition is_failure_test other in
  (success, failures, other)

and load_files files =
  List.map load_file files

and load_file file =
  let ic = open_in file in
  let n = in_channel_length ic in
  let s = Bytes.create n in
  really_input ic s 0 n;
  close_in ic;
  (file, Bytes.to_string s)

and test_input_file is_success_test (fname, source)  =
  let lexbuf = Lexing.from_string ~with_positions:true source in 
  try
    let _ =
      lexbuf |>
      Parsing.parse Scanner.next_token |>
      Semantic_analysis.type_check
    in
    match is_success_test with
    | true ->  ()
    | false -> 
      print_long_line ();
      Printf.eprintf "Test \"%s\" failed, failure expected but was not found.\n\n" fname
  with 
  | Scanner.Lexing_error (pos, msg)
  | Parsing.Syntax_error (pos, msg) -> (
    match is_success_test with
    | true -> handle_syntatic_error fname source pos msg
    | false -> ()
  )
  | Semantic_analysis.Semantic_error (pos, msg) -> (
    match is_success_test with
    | true -> handle_semantic_error fname source pos msg
    | false -> ()
  )
  | Symbol_table.DuplicateEntry (entry) -> (
    match is_success_test with
    | true -> 
      print_long_line ();
      Printf.eprintf "Test \"%s\" failed:\n*** Duplicate entry detected: %s\n\n" fname entry
    | false -> ()    
  )

and handle_syntatic_error fname source lexeme_pos msg = 
  let lines = String.split_on_char '\n' source in 
  let line = List.nth lines (lexeme_pos.Location.line - 1) in
  let prefix = String.make (lexeme_pos.Location.start_column - 1) ' ' in 
  let middle = String.make (lexeme_pos.Location.end_column - lexeme_pos.Location.start_column + 1) '^' in 
  print_long_line ();
  Printf.eprintf "Test \"%s\" failed:\n*** Error at line %d.\n%s\n%s%s\n*** %s\n\n"
    fname lexeme_pos.Location.line line prefix middle msg

and handle_semantic_error fname source code_pos msg = 
  let lines = 
    String.split_on_char '\n' source |>
    List.filteri (fun line _ -> 
      code_pos.Location.start_line-1 <= line && line <= code_pos.Location.end_line-1)  
  in
  let length = List.length lines in 
  if length = 1 then
    let line = List.hd lines in  
    let prefix = String.make (code_pos.Location.start_column - 1) ' ' in 
    let middle = String.make (code_pos.Location.end_column - code_pos.Location.start_column + 1) '^' in 
    print_long_line ();
    Printf.eprintf "Test \"%s\" failed:\n*** Error at line %d.\n%s\n%s%s\n*** %s\n\n"
      fname code_pos.Location.start_line line prefix middle msg
  else
    let text = 
      lines |>
      List.filteri (fun i _ -> i < 5) |>
      String.concat "\n" 
    in 
    print_long_line ();
    Printf.eprintf "Test \"%s\" failed:\n*** Error at lines %d-%d.\n%s\n*** %s\n\n"
      fname code_pos.Location.start_line (code_pos.Location.start_line + 5) text msg

and print_long_line () =
    Printf.eprintf "----------------------------------------------------------\n"

let () = main ()