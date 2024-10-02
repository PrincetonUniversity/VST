(** Support for annotations in special comments. *)

type inlined_code =
  { ic_prelude : string list
  ; ic_section : string list
  ; ic_final   : string list }

type comment_annots =
  { ca_inlined       : inlined_code
  ; ca_requires      : string list
  ; ca_imports       : (string * string) list
  ; ca_proof_imports : (string * string) list
  ; ca_code_imports  : (string * string) list
  ; ca_context       : string list
  ; ca_typedefs      : Rc_annot.typedef list }

type annot_line =
  | AL_annot of string * string option
  | AL_comm  of string
  | AL_none

let read_line : string -> annot_line = fun s ->
  (* First try to read an annotation comment. *)
  let k_annot name n =
    let payload = String.trim (String.sub s n (String.length s - n)) in
    let payload = if payload = "" then None else Some(payload) in
    AL_annot(name, payload)
  in
  try Scanf.sscanf s "//@rc::%s%n" k_annot
  with End_of_file | Scanf.Scan_failure(_) ->
  (* Then try to read a comment. *)
  let k_comm n = AL_comm(String.sub s n (String.length s - n)) in
  try Scanf.sscanf s "//@%n" k_comm
  with End_of_file | Scanf.Scan_failure(_) ->
  (* Line has no special meaning. *)
  AL_none

type where = Default | CodeOnly | ProofsOnly

let read_import : string -> (string * string * where) option = fun s ->
  let k proof_only mod_name from = Some(from, mod_name, proof_only) in
  (* First try to read an import that is only for proofs. *)
  try Scanf.sscanf s "%s from %s (for proofs only) %!" (k ProofsOnly)
  with End_of_file | Scanf.Scan_failure(_) ->
  (* Then try to read an import that is only for the code. *)
  try Scanf.sscanf s "%s from %s (for code only) %!" (k CodeOnly)
  with End_of_file | Scanf.Scan_failure(_) ->
  (* Then try to read a general import. *)
  try Scanf.sscanf s "%s from %s %!" (k Default)
  with End_of_file | Scanf.Scan_failure(_) -> None

let read_typedef : string -> Rc_annot.typedef option = fun s ->
  let open Earley_core in
  let parse_string = Earley.parse_string Rc_annot.typedef Blanks.default in
  try Some(parse_string s) with Earley.Parse_error(_,_) -> None

let parse_annots : string list -> comment_annots = fun ls ->
  let error fmt =
    Panic.panic_no_pos ("Comment annotation error: " ^^ fmt ^^ ".")
  in
  let imports = ref [] in
  let requires = ref [] in
  let inlined = ref [] in
  let inlined_top = ref [] in
  let inlined_end = ref [] in
  let typedefs = ref [] in
  let context = ref [] in
  let read_block start_tag ls =
    let rec read_block acc ls =
      match ls with
      | AL_comm(s)            :: ls -> read_block (s :: acc) ls
      | AL_annot("end", None) :: ls -> (acc, ls)
      | AL_annot("end", _   ) :: ls ->
          error "[rc::end] does not expect a payload"
      | AL_annot(_    , _   ) :: ls ->
          error "unclosed [rc::%s] annotation" start_tag
      | AL_none               :: ls ->
          error "interrupted block"
      | []                          ->
          error "unclosed [rc::%s] annotation" start_tag
    in
    read_block [] ls
  in
  let rec loop ls =
    match ls with
    | []                  -> ()
    | AL_none       :: ls -> loop ls
    | AL_comm(_)    :: ls -> error "no block has been started"
    | AL_annot(n,p) :: ls ->
    let get_payload () =
      match p with Some(s) -> s | None ->
      error "annotation [rc::%s] expects a payload" n
    in
    let add_inlined r p ls =
      let (lines, ls) =
        match p with
        | Some(s) -> ([s], ls)
        | None    -> read_block n ls
      in
      r := lines @ !r; ls
    in
    match n with
    | "inlined"         -> loop (add_inlined inlined p ls)
    | "inlined_prelude" -> loop (add_inlined inlined_top p ls)
    | "inlined_final"   -> loop (add_inlined inlined_end p ls)
    | "end"     -> error "no block has been started"
    | "import"  ->
        begin
          match (read_import (get_payload ())) with
          | Some(i) -> imports := i :: !imports; loop ls
          | None    -> error "invalid [rc::%s] annotation" n
        end
    | "require" ->
        begin
          let s = String.trim (get_payload ()) in
          requires := s :: !requires; loop ls
        end
    | "typedef" ->
        begin
          match (read_typedef (get_payload ())) with
          | Some(t) -> typedefs := t :: !typedefs; loop ls
          | None    -> error ("invalid [rc::typedef] annotation")
        end
    | "context" ->
        begin
          context := get_payload () :: !context;
          loop ls
        end
    | _         ->
        error "unknown annotation [rc::%s]" n
  in
  loop (List.map read_line ls);
  let imports = List.rev !imports in
  let proof_imports = List.filter (fun (_,_,w) -> w = ProofsOnly) imports in
  let code_imports  = List.filter (fun (_,_,w) -> w = CodeOnly  ) imports in
  let imports       = List.filter (fun (_,_,w) -> w = Default   ) imports in
  let ic_prelude = List.rev !inlined_top in
  let ic_section = List.rev !inlined in
  let ic_final   = List.rev !inlined_end in
  { ca_inlined        = { ic_prelude ; ic_section ; ic_final }
  ; ca_proof_imports  = List.map (fun (f,m,_) -> (f,m)) proof_imports
  ; ca_code_imports   = List.map (fun (f,m,_) -> (f,m)) code_imports
  ; ca_imports        = List.map (fun (f,m,_) -> (f,m)) imports
  ; ca_requires       = List.rev !requires
  ; ca_context        = List.rev !context
  ; ca_typedefs       = List.rev !typedefs }
