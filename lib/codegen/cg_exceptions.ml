exception Unexpected_error of Location.code_pos * string

(* Helper exception function *)
let raise_error msg loc = raise (Unexpected_error (loc, "Semantic Analysis should have failed at this point: " ^ msg))