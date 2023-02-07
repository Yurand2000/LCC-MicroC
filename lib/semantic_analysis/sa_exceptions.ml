exception Semantic_error of Location.code_pos * string

(* Helper exception function *)
let raise_error msg loc =
  raise (Semantic_error(Option.value loc ~default:Location.dummy_code_pos, msg))