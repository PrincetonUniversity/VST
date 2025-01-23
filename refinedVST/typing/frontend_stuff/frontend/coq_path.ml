open Extra

type member = string

let member_of_string : string -> member = fun s ->
  let invalid r =
    let f = "Name \"%s\" is invalid as a Coq path member: it " ^^ r ^^ "." in
    invalid_arg f s
  in
  (* Empty string is invalid. *)
  if String.length s = 0 then invalid "is empty";
  (* Only accept characters, digits and underscores. *)
  let check_char c =
    match c with
    | 'a'..'z' | 'A'..'Z' | '0'..'9' | '_' -> ()
    | _ when Char.printable_ascii c        ->
        invalid "contains '%c'" c;
    | _                                    ->
        invalid "uses non-printable ASCII characters" c;
  in
  String.iter check_char s;
  (* Should not start with a letter. *)
  match s.[0] with
  | 'a'..'z' | 'A'..'Z' -> s
  | c                   -> invalid "starts with '%c'" c

let fixup_string_member : string -> string option = fun s ->
  (* Remove non-ASCII characters. *)
  let s = Ubase.from_utf8 ~malformed:"" ~strip:"" s in
  (* Use underscores for invalid characters. *)
  let fn c =
    match c with
    | 'a'..'z' | 'A'..'Z' | '0'..'9' -> c
    | _                              -> '_'
  in
  let s = String.map fn s in
  (* Remove leading underscores. *)
  let s = String.trim_leading '_' s in
  (* Check non-empty. *)
  if String.length s = 0 then None else
  (* Check starts with letter. *)
  match s.[0] with
  | 'a'..'z' | 'A'..'Z' -> Some(s)
  | _                   -> None

type path = Path of member * member list
type t = path

let path_of_members : member list -> path = fun ms ->
  match ms with
  | []    -> invalid_arg "Coq_path.path_of_members requires a non-empty list."
  | m::ms -> Path(m, ms)

let path_of_string : string -> path = fun s ->
  let members = String.split_on_char '.' s in
  try
    match List.map member_of_string members with
    | m :: ms -> Path(m, ms)
    | []      -> invalid_arg "The empty module path is forbidden."
  with Invalid_argument(msg) ->
  invalid_arg "String \"%s\" is not a valid Coq module path.\n%s" s msg

let fixup_string_path : string -> string option = fun s ->
  let rec build ms acc =
    match (ms, acc) with
    | ([]     , []) -> None
    | ([]     , _ ) -> Some(String.concat "." (List.rev acc))
    | (m :: ms, _ ) ->
    match fixup_string_member m with
    | None    -> None
    | Some(m) -> build ms (m :: acc)
  in
  build (String.split_on_char '.' s) []

type suffix = member list

let append : t -> suffix -> t = fun (Path(m, ms)) suff -> Path(m, ms @ suff)

let to_string : path -> string = fun (Path(m, ms)) ->
  String.concat "." (m :: ms)

let pp : path pp = fun ff path ->
  Format.pp_print_string ff (to_string path)
