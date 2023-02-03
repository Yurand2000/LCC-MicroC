(** Code generator *)

(** Code generation error with position and error message *)
exception Unexpected_error of Location.code_pos * string

(** Main code generation function, which converts a type checked program and converts it into an llvm module. *)
val to_llvm_module : Ast.program -> Llvm.llmodule
