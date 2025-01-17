open Extra

type t

type loc_data =
  { loc_key   : int
  ; loc_file  : string
  ; loc_line1 : int
  ; loc_col1  : int
  ; loc_line2 : int
  ; loc_col2  : int }

module Pool :
  sig
    type t

    val make : unit -> t
    val iter : (loc_data -> unit) -> t -> unit
  end

val none : Pool.t -> t
val make : string -> int -> int -> int -> int -> Pool.t -> t
val get : t -> loc_data option

val pp_data : loc_data pp
val pp_loc : t pp

type 'a located = { elt : 'a ; loc : t }

val to_cerb_loc : t -> Cerb_location.t
