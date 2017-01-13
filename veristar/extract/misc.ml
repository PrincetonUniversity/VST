module StringSet =
  Set.Make(struct
    type t = string
    let compare = compare
  end)

module StringMap =
  Map.Make(struct
    type t = string
    let compare = compare
  end)

let remove_duplicates l =
  let l2 = List.stable_sort compare l in
  let rec f = function
    | x::y::xs -> if x=y then f(y::xs) else x::(f(y::xs))
    | xs -> xs
  in f l2

let rec iter_pairs f l1 l2 =
  let g x1 = List.iter (fun x2 -> f (x1,x2)) l2
  in List.iter g l1

let rec iter_pairwise f = function
  | [] -> ()
  | x::l -> List.iter (function y -> f (x,y)) l;
            iter_pairwise f l

(* parameters for identifiers, in priority order: builtin compare used *)
type id_status = GARBAGE | RENAMED | ORIGINAL
type id_kind = EXISTENTIAL_VAR | NORMAL_VAR
type ident = {status:id_status; kind:id_kind; name:string; stamp:int}

let id_name (id : ident) = id.name
let id_stamp (id : ident) = id.stamp

module IdSet =
  Set.Make(struct
    type t = ident
    let compare = compare
  end)

module IdMap =
  Map.Make(struct
    type t = ident
    let compare = compare
  end)

let gensym_count = ref StringMap.empty
let init_gensym () = gensym_count := StringMap.empty


(* generate fresh identifiers *)
let gensym id =
  let count = try StringMap.find id.name !gensym_count
  with Not_found -> -1
  in
    gensym_count := StringMap.add id.name (count-1) !gensym_count;
    {id with status=RENAMED; stamp = count}

let gensym_garb id =
  {(gensym id) with status = GARBAGE}

let existential_name s = String.get s 0 = '_'

let un_EX s =
    try String.sub s 1 ((String.length s)- 1)
    with Not_found -> assert false

let is_existential id =
  id.kind = EXISTENTIAL_VAR

let is_garbage id =
  id.status = GARBAGE

let un_existential id =
  assert (id.kind = EXISTENTIAL_VAR);
  {id with kind = NORMAL_VAR}

let create_ident s =
  let (name,kind) = if existential_name s
  then (un_EX s, EXISTENTIAL_VAR)
  else (s,NORMAL_VAR) in
    {status=ORIGINAL; stamp=0; name=name; kind=kind}

let string_of_ident id =
  (if id.kind = EXISTENTIAL_VAR then "_" else "") ^
    (if id.status=GARBAGE then "" (* "%" *) else "") ^
    id.name ^
    (if id.stamp = 0 then "" else "_" ^ string_of_int (-1 - id.stamp))

let pp_ident f id = Format.fprintf f "%s" (string_of_ident id)
