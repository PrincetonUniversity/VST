open Cmdliner
open Extra
open Panic.Simple
open Project
open Version

(* Standard file and directory names. *)

let rc_project_file   = "rc-project.toml"
let dune_proj_file    = "dune-project"
let coq_project_file  = "_CoqProject"
let rc_dir_name       = "proofs"

let code_file_name    = "generated_code.v"
let code_file_name_vst = "generated_code_vst.v"
let spec_file_name    = "generated_spec.v"
let spec_file_name_vst = "generated_spec_vst.v"
let proof_file_name   = Printf.sprintf "generated_proof_vst_%s.v"
(* let proof_file_name_vst = Printf.sprintf "generated_proof_%s_vst.v" *)
let proofs_file_name  = "proof_files"
(* let proofs_file_name_vst = "proof_files_vst" *)

(* Default Coq root prefix. *)

let default_coq_root_prefix = ["refinedc"; "project"]

(* The default Coq root is the above prefix followed by the project name. *)
let default_coq_root : Coq_path.member -> Coq_path.t =
  let default_coq_root_prefix =
    try List.map Coq_path.member_of_string default_coq_root_prefix
    with Invalid_argument(_) -> assert false (* Should never fail. *)
  in
  fun base -> Coq_path.path_of_members (default_coq_root_prefix @ [base])

(* RefinedC include directory (containing [refinedc.h]). *)
let refinedc_include : string option =
  try
    let opam_prefix = Sys.getenv "OPAM_SWITCH_PREFIX" in
    Some(Filename.concat opam_prefix "lib/refinedc/include")
  with Not_found -> None

(* The RefinedC tooling assumes a specific structure of the working directory.
   It is organized in a "RefinedC project", that can be set up with a provided
   command. Further actions maintain several invariants, like the existence of
   certain files.

   A RefinedC project, when it is initialized, contains the following files in
   its root directory:
    - [rc_project_file] containing certain project metadata,
    - [dune_proj_file] containing the build system setup for Coq,
    - [coq_project_file] containing editor setup for Coq.
   These files are generated, and should not be modified directly. These files
   all have special, reserved names, that should not be used for other files.

   When checking a C source file, say ["src/dir/file.c"], RefinedC creates the
   special directory ["src/dir/" ^ rc_dir_name] if it does not already exists,
   and it also creates a directory ["file"] inside it (having the same name as
   the C source file, without the extension). This directory then contains all
   the generated (Coq) files corresponding to ["src/dir/file.c"]. For example,
   it would contain the code file [code_file_name].

   When checking another file of the same directory, a similar directory (with
   the base name of the file) is created under the special RefinedC directory.
   For example, the project source tree may look like the following:
   [{|
     .
     ├── _CoqProject
     ├── dune-project
     ├── lib
     │   ├── proofs
     │   │   └── socket
     │   │       ├── generated_code.v
     │   │       └── generated_spec.v
     │   └── socket.c
     ├── rc-project.toml
     └── src
         ├── client
         │   ├── client.c
         │   ├── lib.c
         │   └── proofs
         │       ├── client
         │       │   ├── generated_code.v
         │       │   └── generated_spec.v
         │       └── lib
         │           ├── generated_code.v
         │           └── generated_spec.v
         └── server
             ├── proofs
             │   └── server
             │       ├── generated_code.v
             │       └── generated_spec.v
             └── server.c
   |}]
   The Coq qualification for each source file is determined by the Coq logical
   directory chosen at project creation (which defaults to something using the
   directory name if possible). Using the example above, and assuming that the
   Coq logical directory name of the project is ["refinedc.project.my_server"]
   then ["src/client/proofs/client/generated_code.v"] is mapped to module name
   ["refinedc.project.my_server.src.client.generated_code"] in Coq.

   A directory corresponding to the generated code of a C source file also has
   a ["dune"] file, that controls its building. It is automatically generated,
   and automatically updated in case of changes.

   The user can freely add Coq files (provided they do not have reserved names
   like [code_file_name], [spec_file_name] or [proof_file_name s] where [s] is
   a potential C function name) to directories corresponding to any C file.

   TODO Find a better way, with a specific directory?

   RefinedC relies on file [proofs_file_name], placed next to generated files,
   to identify the currently valid proof files. When the user removes or moves
   a function spec, a proof file may no longer correspond to anything. In that
   case it is deleted by RefinedC automatically upon generation. *)

(** Metadata associated to a C file. *)
type c_file_data = {
  orig_path : string; (** Path given by the user on the command line. *)
  file_path : string; (** Absolute, normalised file path. *)
  file_dir  : string; (** Directory holding the file. *)
  base_name : string; (** Base name of the file, without extension. *)
  root_dir  : string; (** Absolute path to the RefinedVST frontend root. *)
  vst_dir   : string; (** Absolute path to the VST project root. *)
  rel_path  : string list; (** Relative path to the parent directory. *)
  proj_cfg  : project_config; (** Associated project configuration. *)
}

(** [get_c_file_data path] computes various metadata for the C file pointed to
    by the given [path]. It includes, for instance, the path to the associated
    RefinedC project directory. In case of error a suitable message is printed
    and the program is terminated. *)
let get_c_file_data : string -> c_file_data = fun c_file ->
  (* Original file path. *)
  let orig_path = c_file in
  (* Absolute, normalised file path. *)
  let file_path =
    try Filename.realpath c_file with Invalid_argument(_) ->
      panic "File \"%s\" disappeared..." c_file
  in
  (* Directoru, base name and extension. *)
  let file_dir = Filename.dirname file_path in
  let base_name = Filename.basename file_path in
  let base_name = Filename.remove_extension base_name in
  (* Root directory and relative path. *)
  let (root_dir, rel_path) =
    let rec find acc dir =
      let rc_project = Filename.concat dir rc_project_file in
      if Sys.file_exists rc_project then (dir, acc) else
      let parent = Filename.dirname dir in
      if parent = dir then raise Not_found;
      find (Filename.basename dir :: acc) parent
    in
    try find [] file_dir with Not_found ->
      panic "No RefinedC project can be located for file \"%s\"." orig_path
  in
  let vst_dir =
    let rec find acc dir =
      let vst_project = Filename.concat dir coq_project_file in
      Printf.printf "try: %s\n" dir;
      if Sys.file_exists vst_project then dir else
      let parent = Filename.dirname dir in
      if parent = dir then raise Not_found;
      find (Filename.basename dir :: acc) parent
    in
    try find [] file_dir with Not_found ->
      panic "No RefinedC project can be located for file \"%s\"." orig_path
  in
  Printf.printf "root_dir: %s\n" root_dir;
  (* Reading the project configuration. *)
  let proj_cfg =
    let project_file = Filename.concat root_dir rc_project_file in
    try
      if Sys.is_directory project_file then
        panic "Invalid project file \"%s\" (directory)." project_file;
      read_project_file project_file
    with Sys_error(_) ->
      panic "Error while reading the project file \"%s\"." project_file
  in
  {orig_path; file_path; file_dir; base_name; root_dir; vst_dir; rel_path; proj_cfg}

(** Command line configuration for the ["check"] command. *)
type config =
  { cpp_config  : Cerb_wrapper.cpp_config
  ; no_locs     : bool
  ; no_analysis : bool
  ; no_build    : bool
  ; no_mem_cast : bool }

(** Entry point for the ["check"] command. *)
let run : config -> string -> unit = fun cfg c_file ->
  (* Set the printing flags. *)
  if cfg.no_locs then
    begin
      Coq_pp.print_expr_locs := false;
      Coq_pp.print_stmt_locs := false
    end;
  if cfg.no_mem_cast then
    begin
      Coq_pp.no_mem_cast := true
    end;
  (* Obtain the metadata for the input C file. *)
  let c_file = get_c_file_data c_file in
  (* Compute the base Coq logical path for the files. *)
  let path =
    let suffix =
      let suffix = c_file.rel_path @ [c_file.base_name] in
      try List.map Coq_path.member_of_string suffix
      with Invalid_argument(msg) ->
        panic "File \"%s\" does not correspond to a valid Coq module path.\n\
              The obtained module path segment is \"%s\".\n%s"
              c_file.orig_path (String.concat "." suffix) msg
    in
    Coq_path.append c_file.proj_cfg.project_coq_root suffix
  in
  (* Prepare the output folder if need be. *)
  let file_rc_dir = Filename.concat c_file.file_dir rc_dir_name in
  if not (Sys.file_exists file_rc_dir) then Unix.mkdir file_rc_dir 0o755;
  let output_dir = Filename.concat file_rc_dir c_file.base_name in
  if not (Sys.file_exists output_dir) then
    begin
      Unix.mkdir output_dir 0o755;
      (* Add the mapping to the Coq project file for editors. *)
      let dune_dir_path =
        let relative_path =
          Filename.relative_path c_file.root_dir c_file.file_dir
        in
        let path =
          if relative_path = Filename.current_dir_name then "_build/default"
          else Filename.concat "_build/default" relative_path
        in
        let path = Filename.concat path rc_dir_name in
        Filename.concat path c_file.base_name
      in
      let coq_proj_path = Filename.concat c_file.vst_dir coq_project_file in
      Printf.printf "coq_proj_path: %s\n" coq_proj_path;
      let new_line =
        Printf.sprintf "-Q %s %s" dune_dir_path (Coq_path.to_string path)
      in
      let lines = try read_file coq_proj_path with Sys_error(_) -> [] in
      if not (List.mem new_line lines) then
        append_file coq_proj_path [new_line]
    end;
  (* Paths to the output files. *)
  let code_file = Filename.concat output_dir code_file_name in
  let code_file_vst = Filename.concat output_dir code_file_name_vst in
  let spec_file = Filename.concat output_dir spec_file_name in
  let spec_file_vst = Filename.concat output_dir spec_file_name_vst in
  let proof_of_file id = Filename.concat output_dir (proof_file_name id) in
  (* let proof_of_file_vst id = Filename.concat output_dir (proof_file_name_vst id) in *)
  let proof_files_file = Filename.concat output_dir proofs_file_name in
  (* let proof_files_file_vst = Filename.concat output_dir proofs_file_name_vst in *)
  let dune_file = Filename.concat output_dir "dune" in
  (* Prepare the CPP configuration. *)
  let cpp_config =
    let cpp_I =
      let proj_include =
        let incl = c_file.proj_cfg.project_cpp_include in
        List.map (Filename.concat c_file.root_dir) incl
      in
      let cpp_include = cfg.cpp_config.cpp_I @ proj_include in
      match (refinedc_include, c_file.proj_cfg.project_cpp_with_rc) with
      | (_      , false) -> cpp_include
      | (Some(d), true ) -> d :: cpp_include
      | (None   , true ) ->
          panic "Unable to locate the RefinedC include directory."
    in
    {cfg.cpp_config with cpp_I}
  in
  (* Parse the comment annotations. *)
  let open Comment_annot in
  let ca =
    let lines = Cerb_wrapper.cpp_lines cpp_config c_file.file_path in
    parse_annots lines
  in
  let ctxt = List.map (fun s -> "Context " ^ s) ca.ca_context in
  (* Do the translation to Ail, analyse, and generate our AST. *)
  Sys.chdir c_file.root_dir; (* Move to the root to get relative paths. *)
  let c_file_rel = Filename.relative_path c_file.root_dir c_file.file_path in
  let ail_ast = Cerb_wrapper.c_file_to_ail cpp_config c_file_rel in
  if not cfg.no_analysis then Warn.warn_file ail_ast;
  let coq_ast = Ail_to_coq.translate c_file_rel ail_ast in
  (* Generate the code file. *)
  let open Coq_pp in
  let mode = Code(c_file.root_dir, ca.ca_code_imports) in
  write mode code_file coq_ast;
  let mode = CodeVST(c_file.root_dir, ca.ca_code_imports) in
  write mode code_file_vst coq_ast;
  (* Generate the spec file. *)
  let mode = Spec(path, ca.ca_imports, ca.ca_inlined, ca.ca_typedefs, ctxt) in
  write mode spec_file coq_ast;
  let mode = SpecVST(path, ca.ca_imports, ca.ca_inlined, ca.ca_typedefs, ctxt) in
  write mode spec_file_vst coq_ast;
  (* Compute the list of proof files to generate. *)
  let to_generate =
    let not_inlined (_, def_or_decl) =
      let open Coq_ast in
      match def_or_decl with
      | FDef(def) when is_inlined def -> false
      | _                             -> true
    in
    let fs = List.filter not_inlined coq_ast.functions in
    let files = List.map (fun (id, _) -> proof_of_file id) fs in
    List.sort_uniq String.compare files
  in
  (* Delete obsolete proof files. *)
  let already_generated =
    let files = try read_file proof_files_file with Sys_error(_) -> [] in
    List.map (Filename.concat output_dir) files
  in
  let delete_when_obsolete fname =
    if not (List.mem fname to_generate) then
      try Sys.remove fname with Sys_error(_) -> ()
  in
  List.iter delete_when_obsolete already_generated;
  (* Write the new list of proof files. *)
  write_file proof_files_file (List.map Filename.basename to_generate);
  (* Generate the proof files. *)
  let proof_imports = ca.ca_imports @ ca.ca_proof_imports in
  let write_proof (id, def_or_decl) =
    let open Coq_ast in
    match def_or_decl with
    | FDec(_)                       -> ()
    | FDef(def) when is_inlined def -> ()
    | FDef(def)                     ->
    let mode = Fprf(path, def, proof_imports, ctxt, proof_kind def) in
    write mode (proof_of_file id) coq_ast
  in
  List.iter write_proof coq_ast.functions;
  (* Generate the dune file. *)
  (* let theories =
    let default_theories = ["refinedc.typing"; "refinedc.typing.automation"; "caesium"; "lithium";
                            "iris"; "stdpp"; "Ltac2"; "RecordUpdate"] in
    let glob = List.map Coq_path.to_string c_file.proj_cfg.project_theories in
    let imports = ca.ca_imports @ ca.ca_proof_imports @ ca.ca_code_imports in
    let imports = List.sort_uniq Stdlib.compare imports in
    ignore imports; (* TODO some dependency analysis based on [imports]. *)
    let theories =
      let path = Coq_path.to_string path in
      List.filter (fun s -> s <> path) (ca.ca_requires @ glob @ default_theories)
    in
    List.sort_uniq String.compare theories
  in *)
  Printf.printf "theories: %s \n" dune_file;
  Printf.printf "vst_dir: %s\n" c_file.vst_dir;
  Printf.printf "spec: %s\n" spec_file_vst;
  Printf.printf "code: %s\n" code_file_vst;
  (* write_file dune_file [
    "; Generated by [refinedc], do not edit.";
    "(coq.theory";
    " (flags :standard -w -notation-incompatible-prefix \
                       -w -redundant-canonical-projection)";
    Printf.sprintf " (name %s)" (Coq_path.to_string path);
    Printf.sprintf " (theories %s))" (String.concat " " theories);
  ]; *)
  (* Run Coq type-checking. *)
  if not (cfg.no_build || c_file.proj_cfg.project_no_build) then
    begin
      Sys.chdir c_file.vst_dir;
      match Sys.command ("(set -x; make " ^ code_file_vst ^ "o)") with
      | 0           ->
          info "File \"%s\" successfully checked.\n%!" c_file.orig_path
      | i           ->
          panic "The call to [dune] returned with error code %i." i
      | exception _ ->
          panic "The call to [dune] failed for some reason."
    end;
  Printf.printf "done\n"

let cpp_I =
  let doc =
    "Add the directory $(docv) to the list of directories to be searched for \
     header files during preprocessing."
  in
  let i = Arg.(info ["I"] ~docv:"DIR" ~doc) in
  Arg.(value & opt_all dir [] & i)

let cpp_include =
  let doc =
    "Add an include for the file $(docv) at the beginning of the source file."
  in
  let i = Arg.(info ["include"] ~docv:"FILE" ~doc) in
  Arg.(value & opt_all file [] & i)


let cpp_nostdinc =
  let doc =
    "Do not search the standard system directories for header files. Only \
     the directories explicitly specified with $(b,-I) options are searched."
  in
  Arg.(value & flag & info ["nostdinc"] ~doc)

let cpp_D =
  let doc =
    "Do not search the standard system directories for header files. Only \
     the directories explicitly specified with $(b,-I) options are searched."
  in
  let i = Arg.(info ["D"] ~docv:"MACRODEF" ~doc) in
  Arg.(value & opt_all string [] & i)

let cpp_config =
  let build cpp_I cpp_include cpp_nostdinc cpp_D =
    Cerb_wrapper.{cpp_I; cpp_include; cpp_nostdinc; cpp_D}
  in
  Term.(const build $ cpp_I $ cpp_include $ cpp_nostdinc $ cpp_D)

let no_analysis =
  let doc =
    "Disable the extra analyses (and the corresponding warnings) that are \
     performed on the source code by default. There are two such analyses. \
     (1) A warning is issued when the address of a local variable whose \
     scope is not that of the function is taken. Indeed, if that happens \
     then variables can potentially escape their lifetime (which is only \
     active in the block they are defined in) since all local variable are \
     hoisted to the function scope by RefiendC. (2) A warning is issued when \
     there is potential non-determinism in evaluation of expressions. This \
     is a problem since C has a loose ordering of expression evaluation, \
     while RefiendC has a fixed left-to-right evaluation order. Note that \
     these two analyses are over-approximations."
  in
  Arg.(value & flag & info ["no-extra-analysis"] ~doc)

let no_locs =
  let doc =
    "Do not output any location information in the generated Coq files."
  in
  Arg.(value & flag & info ["no-locs"] ~doc)

let no_build =
  let doc =
    "Do not build Coq object files after generation."
  in
  Arg.(value & flag & info ["no-build"] ~doc)

let no_mem_cast =
  let doc =
    "Disable mem cast on loads from memory."
  in
  Arg.(value & flag & info ["no-mem-cast"] ~doc)

let opts : config Term.t =
  let build cpp_config no_analysis no_locs no_build no_mem_cast =
    { cpp_config ; no_analysis ; no_locs ; no_build ; no_mem_cast }
  in
  Term.(const build $ cpp_config $ no_analysis $ no_locs $ no_build $ no_mem_cast)

let c_file =
  let doc = "C language source file." in
  Arg.(required & pos 0 (some non_dir_file) None & info [] ~docv:"FILE" ~doc)

let check_cmd =
  let open Term in
  let term = const run $ opts $ c_file in
  let doc = "Run RefiendC on the given C file." in
  Cmd.(v (info "check" ~version ~doc) term)

(* Preprocessing command (useful for debugging). *)

let run_cpp config c_file =
  output_lines stdout (Cerb_wrapper.cpp_lines config c_file);
  flush stdout

let cpp_cmd =
  let doc = "Print the result of the Cerberus preprocessor to stdout." in
  Cmd.(v (info "cpp" ~version ~doc) Term.(const run_cpp $ cpp_config $ c_file))

(* Ail printing command (useful for debugging). *)

let run_ail config c_file =
  let ail_ast = Cerb_wrapper.c_file_to_ail config c_file in
  Cerb_wrapper.print_ail ail_ast

let ail_cmd =
  let doc = "Print the Cerberus Ail AST of the given C file to stdout." in
  Cmd.(v (info "ail" ~version ~doc) Term.(const run_ail $ cpp_config $ c_file))

(* Cleaning command. *)

let run_clean : bool -> string -> unit = fun soft c_file ->
  (* Obtain the metadata for the input C file. *)
  let c_file = get_c_file_data c_file in
  (* Compute the relevant directory and file paths. *)
  let rc_dir = Filename.concat c_file.file_dir rc_dir_name in
  let gen_dir = Filename.concat rc_dir c_file.base_name in
  let dune_file = Filename.concat gen_dir "dune" in
  let proofs_file = Filename.concat gen_dir proofs_file_name in
  let code_file = Filename.concat gen_dir code_file_name in
  let spec_file = Filename.concat gen_dir spec_file_name in
  let proof_files =
    let files = try read_file proofs_file with Sys_error(_) -> [] in
    List.map (Filename.concat gen_dir) files
  in
  (* Compute the list of files to delete, and delete them. *)
  let all = [code_file; spec_file; dune_file; proofs_file] @ proof_files in
  List.iter (fun f -> try Sys.remove f with Sys_error(_) -> ()) all;
  (* Check if the generated directories are empty and if so delete them. *)
  let all_dirs = [gen_dir; rc_dir] in
  let rmdir dir =
    let files = try Sys.readdir dir with Sys_error(_) -> [||] in
    if Array.length files = 0 then
      ignore (Sys.command (Printf.sprintf "rm -rf %s" dir))
  in
  List.iter rmdir all_dirs;
  (* Delete the Coq project mapping for the file. *)
  if not soft then
  (* Compute the base Coq logical path for the files. *)
  let path =
    let suffix =
      let suffix = c_file.rel_path @ [c_file.base_name] in
      try List.map Coq_path.member_of_string suffix
      with Invalid_argument(msg) ->
        panic "File \"%s\" does not correspond to a valid Coq module path.\n\
              The obtained module path segment is \"%s\".\n%s"
              c_file.orig_path (String.concat "." suffix) msg
    in
    Coq_path.append c_file.proj_cfg.project_coq_root suffix
  in
  let dune_dir_path =
    let rel_path = Filename.relative_path c_file.root_dir c_file.file_dir in
    let path = Filename.concat "_build/default" rel_path in
    let path = Filename.concat path rc_dir_name in
    Filename.concat path c_file.base_name
  in
  let coq_project_path = Filename.concat c_file.vst_dir coq_project_file in
  Printf.printf "coq_project_path: %s\n" coq_project_path;
  let line =
    let path = Coq_path.to_string path in
    Printf.sprintf "-Q %s %s" dune_dir_path path
  in
  let lines = try read_file coq_project_path with Sys_error(_) -> [] in
  if List.mem line lines then
    begin
      let new_lines = List.filter (fun s -> s <> line) lines in
      write_file coq_project_path new_lines
    end

let soft =
  let doc =
    "Do not remove the corresponding entry from the `_CoqProject' file."
  in
  Arg.(value & flag & info ["soft"] ~doc)

let clean_cmd =
  let doc = "Delete all the generated files for the given C source file." in
  Cmd.(v (info "clean" ~version ~doc) Term.(const run_clean $ soft $ c_file))

(* Project initialization command. *)

let init : string option -> unit = fun coq_path ->
  (* Read the current working directory. *)
  let wd =
    try Filename.realpath (Sys.getcwd ()) with Invalid_argument(_) ->
      panic "Error while reading the current working directory."
  in
  (* Files to generate. *)
  let rc_project_path = Filename.concat wd rc_project_file in
  let dune_project_path = Filename.concat wd dune_proj_file in
  let coq_project_path = Filename.concat wd coq_project_file in
  (* Check for an existing project. *)
  if Sys.file_exists rc_project_path then
    panic "A RefinedC project already exists here.";
  (* Check for conflicting project files in subdirectories. *)
  let file_check is_dir path =
    let dir = Filename.dirname path in
    let base = Filename.basename path in
    if base = rc_project_file then
      if is_dir then
        panic "Subdirectory \"%s\" uses a reserved name." path
      else
        panic "A RefinedC project exists in directory \"%s\"." dir
    else if base = dune_proj_file then
      if is_dir then
        panic "Subdirectory \"%s\" uses a reserved name." path
      else
        panic "A \"%s\" file exists in directory \"%s\"." dune_proj_file dir
    else if base = coq_project_file then
      if is_dir then
        panic "Subdirectory \"%s\" uses a reserved name." path
      else
        panic "A \"%s\" file exists in directory \"%s\"." dune_proj_file dir
    else if base = rc_dir_name then
      if is_dir then
        panic "Directory \"%s\" uses a reserved name." path
      else
        panic "File \"%s\" uses a reserved name." path
    else ()
  in
  Filename.iter_files ~ignored_dirs:[".git"; "_build"; "_opam"] wd file_check;
  (* Check for conflicting projects in parent directories. *)
  let rec check_parents dir =
    let check_dir dir =
      (* Avoid nested RefinedC projects for sanity. *)
      let file = Filename.concat dir rc_project_file in
      if Sys.file_exists file then begin
        if Sys.is_directory file then
          panic "Parent directory \"%s\" has a reserved name." file;
        panic "Nested under RefinedC project \"%s\"." file
      end;
      (* Avoid nested dune workspaces, leads to problems. *)
      let file = Filename.concat dir dune_proj_file in
      if Sys.file_exists file then begin
        if Sys.is_directory file then
          panic "Parent directory \"%s\" has a reserved name." file;
        panic "Nested under RefinedC project \"%s\"." file
      end
      (* Coq project files should be OK. *)
    in
    let parent = Filename.dirname dir in
    if parent <> dir then (check_dir parent; check_parents parent)
  in
  check_parents wd;
  (* Build the Coq root path, using a possible CLI argument. *)
  let coq_path =
    let parse_coq_path d =
      try Coq_path.path_of_string d with Invalid_argument(msg) ->
      let example =
        let d =
          match Coq_path.fixup_string_path d with Some(d) -> d | None ->
          String.concat "." (default_coq_root_prefix @ ["my_project"])
        in
        try Coq_path.path_of_string d with Invalid_argument(msg) ->
          assert false (* Cannot happen. *)
      in
      panic "%s\nRetry using option \"--coq-path=%a\" or similar."
        msg Coq_path.pp example
    in
    match coq_path with
    | Some(d) -> parse_coq_path d
    | None    ->
    let base =
      let base = Filename.basename wd in
      try Coq_path.member_of_string base with Invalid_argument(msg) ->
      let example =
        let base =
          match Coq_path.fixup_string_member base with
          | Some(id) -> id
          | None     -> "my_project"
        in
        try default_coq_root (Coq_path.member_of_string base)
        with Invalid_argument(_) -> assert false (* Cannot happen. *)
      in
      panic "Current directory name \"%s\" cannot be used to build a Coq \
            module path.\n%s\nRetry using option \"--coq-path=%a\" or \
            similar." base msg Coq_path.pp example
    in
    default_coq_root base
  in
  (* Now we are safe, generate the project files. *)
  write_project_file rc_project_path (default_project_config coq_path);
  write_file dune_project_path [
    "(lang dune 3.8)";
    "(using coq 0.8)";
    "; Generated by [refinedc], do not edit.";
  ];
  write_file coq_project_path [
    "# Generated by [refinedc], do not edit.";
    "-arg -w -arg -notation-incompatible-prefix";
    "-arg -w -arg -redundant-canonical-projection";
  ];
  (* Reporting. *)
  info "Initialized a RefinedC project in \"%s\".\n" wd;
  info "Using Coq root module path [%a].\n%!" Coq_path.pp coq_path

let coq_path =
  let doc =
    "Specify the Coq module path under which the created verification \
    project is to be placed. The argument is expected to be a dot-sperated \
    list of identifiers formed of letters and underscores (but not in first \
    position). If no explicit Coq directory is given then it defaults to \
    [refinedc.project.DIRNAME], where DIRNAME is the current directory name. \
    If DIRNAME is not a valid identifier then the command fails."
  in
  let i = Arg.(info ["coq-path"] ~docv:"COQDIR" ~doc) in
  Arg.(value & opt (some string) None & i)

let init_cmd =
  let doc = "Create a new RefinedC project in the current directory." in
  Cmd.(v (info "init" ~version ~doc) Term.(const init $ coq_path))

(* A few trivial commands. *)

let print_version () =
  info "RefinedC version: %s\nRelying on Cerberus version: %s\n%!"
    Version.version Cerb_frontend.Version.version

let version_cmd =
  let doc = "Show detailed version information for RefinedC." in
  Cmd.(v (info "version" ~version ~doc) Term.(const print_version $ const ()))

let help_cmd =
  let doc = "Show the main help page for RefinedC." in
  Cmd.(v (info "help" ~version ~doc) Term.(ret (const (`Help (`Pager, None)))))

let (default_cmd, default_info) =
  let doc = "RefinedC program verification framework." in
  Term.(ret (const (`Help(`Pager, None)))),
  Cmd.info "refinedc" ~version ~doc

(* Entry point. *)
let _ =
  let cmds =
    [ init_cmd ; cpp_cmd ; ail_cmd ; check_cmd ; clean_cmd
    ; help_cmd ; version_cmd ]
  in
  (* Term.(exit (eval_choice default_cmd cmds)) *)
  Stdlib.exit (Cmd.eval (Cmd.group default_info ~default:default_cmd cmds))
