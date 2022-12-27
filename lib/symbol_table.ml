exception DuplicateEntry of Ast.identifier

type 'a names = (Ast.identifier, 'a) Hashtbl.t

type 'a t = 
{
    global : 'a names;
    local: ('a names) list;
}

let empty_table = { global = Hashtbl.create 10; local = [] }

let begin_block env = { global = env.global; local = Hashtbl.create 10 :: env.local }

let end_block env = { global = env.global; local = List.tl env.local }

let update_entry id def env =
    let head = match env.local with
        | [] -> env.global
        | hd::_ -> hd
    in
    let _ = Hashtbl.add head id def in
    env

let add_entry id def env =
    let head = match env.local with
        | [] -> env.global
        | hd::_ -> hd
    in
    let _ = match Hashtbl.find_opt head id with
        | Some(_) -> raise (DuplicateEntry id)
        | None -> Hashtbl.add head id def
    in
    env

let lookup_opt id env = 
    let env_blocks = (List.rev (env.global :: List.rev env.local)) in
    let rec rec_lookup id blocks =
        match blocks with
        | [] -> None
        | hd::tl -> 
            match Hashtbl.find_opt hd id with
            | Some(res) -> Some(res)
            | None -> rec_lookup id tl
    in
    rec_lookup id env_blocks

let lookup id env = 
    match lookup_opt id env with
    | Some(res) -> res
    | None -> failwith "Entry not found"

let of_alist list = 
    let env = empty_table in
    let add_to_env (id, def) env =
        add_entry id def env
    in
    List.fold_right add_to_env list env