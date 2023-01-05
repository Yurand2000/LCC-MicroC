exception DuplicateEntry of Ast.identifier
exception EntryNotFound of Ast.identifier

type 'a t = ((Ast.identifier * 'a) list) list

let lookup_in_block block name =
    let is_same_name (id, _) = (name = id) in
    List.find_opt is_same_name block

let empty_table = [ [] ]

let begin_block env = [] :: env

let end_block env = 
    match env with
    | _::snd::tl -> snd::tl
    | _::_ -> failwith "Cannot remove global scope from environment table!"
    | [] -> failwith "Cannot close scope: environment table is empty!"

let add_entry id def env =
    let (hd, tl) = (List.hd env, List.tl env) in
    match lookup_in_block hd id with
        | Some(_) -> raise (DuplicateEntry id)
        | None -> ((id, def) :: hd) :: tl

let rec lookup_opt id env =
    match env with
    | [] -> None
    | hd::tl -> (
        match lookup_in_block hd id with
        | Some((_, value)) -> Some(value)
        | None -> lookup_opt id tl
    )

let lookup id env = 
    match lookup_opt id env with
    | Some(res) -> res
    | None -> raise (EntryNotFound id)

let of_alist list = 
    let add_to_env env (id, def) =
        add_entry id def env
    in
    List.fold_left add_to_env empty_table list

let to_alist table =
    List.flatten table
