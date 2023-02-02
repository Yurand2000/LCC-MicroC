(** Const Expression Solver 
    
This function transforms a program by pre-computing any expression which
consists of only literal values and primitive operators, where possible.
*)

(** The transformation function *)
val solve_const_expressions : Ast.program -> Ast.program