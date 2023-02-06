(** Semantic Analyzer *)

(** Semantic error with position and error message *)
exception Semantic_error of Location.code_pos * string

(** Main semantic check function, which checks if the program is well formed.
    It additionally performs some const-expression simplifications. *)
val type_check : Ast.program -> Ast.program

(** This function checks if the provided program contains a valid main function. *)
val type_check_main_defined : Ast.program -> Ast.program
