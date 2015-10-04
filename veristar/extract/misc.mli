module StringSet : Set.S with type elt = string
module StringMap : Map.S with type key = string

val remove_duplicates : 'a list -> 'a list
val iter_pairs :  ('a * 'b -> unit) -> 'a list -> 'b list -> unit
val iter_pairwise : ('a * 'a -> unit) -> 'a list -> unit

(* generate fresh identifiers *)
type ident
val id_name : ident -> string
val id_stamp : ident -> int

module IdSet : Set.S with type elt = ident
module IdMap : Map.S with type key = ident
val init_gensym : unit -> unit
val gensym : ident -> ident
val gensym_garb: ident -> ident
val create_ident : string -> ident
val is_existential : ident -> bool
val is_garbage : ident -> bool
val un_existential : ident -> ident
val string_of_ident : ident -> string
val pp_ident : Format.formatter -> ident -> unit
