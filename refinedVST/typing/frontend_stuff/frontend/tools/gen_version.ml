let version =
  (* Trick to check whether the watermark has been substituted. *)
  if "%%VERSION%%" <> "%%" ^ "VERSION%%" then "%%VERSION%%" else
  (* If not, we fallback to git version. *)
  let cmd = "git describe --dirty --always" in 
  let (oc, ic, ec) = Unix.open_process_full cmd (Unix.environment ()) in
  let version =
    try Printf.sprintf "dev-%s" (input_line oc)
    with End_of_file -> "unknown"
  in
  match Unix.close_process_full (oc, ic, ec) with
  | Unix.WEXITED(0) -> version
  | _               -> "unknown"

let _ =
  let line fmt = Printf.printf (fmt ^^ "\n%!") in
  line "(** Version informations. *)";
  line "";
  line "(** [version] gives a version description. *)";
  line "let version : string = \"%s\"" version
