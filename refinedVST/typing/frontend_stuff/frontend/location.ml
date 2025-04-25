open Extra

type loc_data =
  { loc_key   : int
  ; loc_file  : string
  ; loc_line1 : int
  ; loc_col1  : int
  ; loc_line2 : int
  ; loc_col2  : int }

module Pool =
  struct
    type t =
      { htbl        : (int, loc_data) Hashtbl.t
      ; key_counter : int ref }

    let make : unit -> t = fun _ ->
      { htbl        = Hashtbl.create 97
      ; key_counter = ref (-1) }

    let fresh : (int -> loc_data option) -> t -> int = fun c pool ->
      let key = incr pool.key_counter; !(pool.key_counter) in
      Option.iter (fun data -> Hashtbl.add pool.htbl key data) (c key); key

    let get : t -> int -> loc_data option = fun pool key ->
      try Some(Hashtbl.find pool.htbl key) with Not_found -> None

    let iter : (loc_data -> unit) -> t -> unit = fun f pool ->
      Hashtbl.iter (fun _ data -> f data) pool.htbl
  end

type t = int * Pool.t

let none : Pool.t -> t = fun pool ->
  (Pool.fresh (fun _ -> None) pool, pool)

let make : string -> int -> int -> int -> int -> Pool.t -> t =
    fun f l1 c1 l2 c2 pool ->
  let data key =
    { loc_key = key; loc_file = f
    ; loc_line1 = l1+1 ; loc_col1 = c1
    ; loc_line2 = l2+1 ; loc_col2 = c2 }
  in
  (Pool.fresh (fun key -> Some(data key)) pool, pool)

let get : t -> loc_data option = fun (key, pool) ->
  Pool.get pool key

let pp_data : loc_data pp = fun ff data ->
  let (l1, c1) = (data.loc_line1, data.loc_col1) in
  let (l2, c2) = (data.loc_line2, data.loc_col2) in
  Format.fprintf ff "%s %i:%i" data.loc_file l1 c1;
  if l1 = l2 && c1 <> c2 then Format.fprintf ff "-%i" c2;
  if l1 <> l2 then Format.fprintf ff "-%i:%i" l2 c2

let pp_loc : t pp = fun ff (key, pool) ->
  match Pool.get pool key with
  | Some(d) -> pp_data ff d
  | None    -> Format.fprintf ff "unknown"

type 'a located = { elt : 'a ; loc : t }

let to_cerb_loc : t -> Cerb_location.t = fun (key, pool) ->
  match Pool.get pool key with
  | None    -> Cerb_location.unknown
  | Some(d) ->
  let pos_fname = d.loc_file in
  let {loc_line1=l1; loc_col1=c1; loc_line2=l2; loc_col2=c2; _} = d in
  let p1 = Lexing.{pos_fname; pos_lnum=l1; pos_bol=0; pos_cnum=c1} in
  let p2 = Lexing.{pos_fname; pos_lnum=l2; pos_bol=0; pos_cnum=c2} in
  Cerb_location.region (p1, p2) NoCursor
