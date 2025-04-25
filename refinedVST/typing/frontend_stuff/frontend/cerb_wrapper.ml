open Cerb_frontend
open Cerb_backend
open Pipeline

type cpp_config =
  { cpp_I        : string list
  ; cpp_include  : string list
  ; cpp_nostdinc : bool
  ; cpp_D        : string list }

let (>>=)  = Exception.except_bind
let return = Exception.except_return

let io : Pipeline.io_helpers =
  let pass_message = let ref = ref 0 in fun str ->
    Cerb_debug.print_success (Printf.sprintf "%i. %s" !ref str);
    incr ref; return ()
  in
  let set_progress _ = return () in
  let run_pp opts doc = run_pp opts doc; return () in
  let print_endline str = print_endline str; return () in
  let print_debug n mk_str = Cerb_debug.print_debug n [] mk_str; return () in
  let warn ?(always=false) mk_str = Cerb_debug.warn ~always [] mk_str; return () in
  {pass_message ; set_progress ; run_pp ; print_endline ; print_debug ; warn}

let impl_name =
  try Sys.getenv "IMPL_NAME" with Not_found ->
    "gcc_4.9.0_x86_64-apple-darwin10.8.0"

let set_cerb_conf () =
  let open Cerb_global in
  set_cerb_conf "RefinedC" false Random false Basic false false false false false

let frontend cpp_cmd filename =
  let conf =
    { debug_level = 0 ; pprints = [] ; astprints = [] ; ppflags = []
    ; typecheck_core = false ; rewrite_core = false
    ; sequentialise_core = false ; cpp_cmd ; cpp_stderr = true }
  in
  set_cerb_conf ();
  Ocaml_implementation.(set (HafniumImpl.impl));
  load_core_stdlib () >>= fun stdlib ->
  load_core_impl stdlib impl_name >>= fun impl ->
  c_frontend (conf, io) (stdlib, impl) ~filename

let run_cpp cpp_cmd filename =
  let conf =
    { debug_level = 0 ; pprints = [] ; astprints = [] ; ppflags = []
    ; typecheck_core = false ; rewrite_core = false
    ; sequentialise_core = false ; cpp_cmd ; cpp_stderr = true }
  in
  set_cerb_conf ();
  cpp (conf, io) ~filename

let cpp_cmd config =
  let stdinc =
    if config.cpp_nostdinc then []
    else [Filename.concat (Cerb_runtime.runtime ()) "libc/include"]
  in
  let cpp_I = List.map (fun dir -> "-I" ^ dir) (stdinc @ config.cpp_I) in
  let cpp_include =
    List.map  (fun file -> "-include " ^ file) config.cpp_include
  in
  let macros =
    ["__refinedc__"; "__cerb__"; "DEBUG"; "MAX_CPUS=4"; "MAX_VMS=2"; "HEAP_PAGES=10"]
    @ config.cpp_D
  in
  let cpp_D = List.map (fun mac -> "-D" ^ mac) macros in
  let opts = cpp_I @ cpp_include @ cpp_D in
  let cmd = "cc -E -C -Werror -nostdinc -undef " ^ String.concat " " opts in
  (* Printf.printf "CPP: %s\n%!" cmd; *) cmd

(* A couple of things that the frontend does not seem to check. *)
let source_file_check filename =
  if not (Sys.file_exists filename) then
    Panic.panic_no_pos "File [%s] does not exist." filename;
  if Sys.is_directory filename then
    Panic.panic_no_pos "A file was expected, [%s] is a directory." filename;
  if not (Filename.check_suffix filename ".c") then
    Panic.panic_no_pos "File [%s] does not have the [.c] extension." filename

let c_file_to_ail config fname =
  let open Exception in
  source_file_check fname;
  match frontend (cpp_cmd config) fname with
  | Result(_, (_, ast)) -> ast
  | Exception((loc,err))    ->
  match err with
  | CPP(_) -> Panic.panic_no_pos "Failed due to preprocessor error."
  | _      ->
  let err = Pp_errors.short_message err in
  let (_, pos) =
    try Cerb_location.head_pos_of_location loc with Invalid_argument(_) ->
      ("", "(Cerberus position bug)")
  in
  Panic.panic loc "Frontend error.\n%s\n\027[0m%s%!" err pos

let cpp_lines config fname =
  source_file_check fname;
  let str =
    match run_cpp (cpp_cmd config) fname with
    | Result(str)  -> str
    | Exception(_) -> Panic.panic_no_pos "Failed due to preprocessor error."
  in
  String.split_on_char '\n' str

let print_ail : Ail_to_coq.typed_ail -> unit = fun ast ->
  match io.run_pp None (Pp_ail_ast.pp_program true false ast) with
  | Result(_)            -> ()
  | Exception((loc,err)) ->
  match err with
  | CPP(_) -> Panic.panic_no_pos "Failed due to preprocessor error."
  | _      ->
  let err = Pp_errors.short_message err in
  let (_, pos) =
    try Cerb_location.head_pos_of_location loc with Invalid_argument(_) ->
      ("", "(Cerberus position bug)")
  in
  Panic.panic loc "Frontend error.\n%s\n\027[0m%s%!" err pos
