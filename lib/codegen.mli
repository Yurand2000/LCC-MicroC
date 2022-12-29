exception Unexpected_error of string

val to_llvm_module : Ast.program -> Llvm.llmodule
