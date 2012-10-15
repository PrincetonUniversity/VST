open Misc
open Symbtree

type ip_description =
    {id: string; id_arg: ident list; cmp_arg: string list;
     guard: can_atom; newids: ident list; body: can_spred list}

val lookup_ip : string -> ip_description
val instance_ip : string * can_exp list * component list ->
  can_atom * can_exp list * can_spred list
