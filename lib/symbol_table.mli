(** Symbol Table *)

(** Duplicate entry exception, when inserting the same name in a scope. *)
exception DuplicateEntry of Ast.identifier

(** Entry not found exception, when looking up for a non defined name in the table. *)
exception EntryNotFound of Ast.identifier

(** Symbol Table definition. *)
type 'a t 

(** Empty table constructor. *)
val empty_table : 'a t 

(** Open new scope in the environment. *)
val begin_block : 'a t -> 'a t 

(** Close last scope in the environment.
    Closing the global scope will raise an exception. *)
val end_block : 'a t -> 'a t

(** Adds an entry to the most inner scope if there is no other
    definition with the same name, otherwise raises a DuplicateEntry exception *)
val add_entry : Ast.identifier -> 'a -> 'a t -> 'a t

(** Adds an entry to the global scope if there is no other
    definition with the same name, otherwise raises a DuplicateEntry exception *)
val add_global_entry : Ast.identifier -> 'a -> 'a t -> 'a t 

(** Lookup for definition in the symbol table, returning an option. *)
val lookup : Ast.identifier -> 'a t -> 'a

(** Lookup for definition in the symbol table, raising an EntryNotFound exception if not found. *)
val lookup_opt : Ast.identifier -> 'a t -> 'a option

(** Converts a list of pairs (identifier, value) into a symbol table with the global scope filled with these pairs. *)
val of_alist : (Ast.identifier * 'a) list -> 'a t 

(** Collects all the items in the various scopes and flattens them in a single list. *)
val to_alist : 'a t -> (Ast.identifier * 'a) list