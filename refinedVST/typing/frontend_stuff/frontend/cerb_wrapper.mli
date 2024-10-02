(** Preprocessor configuration. *)
type cpp_config =
  { cpp_I        : string list (** Directories in the search path.    *)
  ; cpp_include  : string list (** Add as includes in source file.    *)
  ; cpp_nostdinc : bool        (** Do not search standard lib C dirs. *)
  ; cpp_D        : string list (** Issue the given macro definition.  *) }

(** [c_file_to_ail config fname] uses Cerberus to preprocess, parse, elaborate
    and type-check the C source file [fname]. The given configuration [config]
    is used to alter the behaviour of the preprocessor. In case of an error, a
    message is displayed and the program exits with error code [-1]. *)
val c_file_to_ail : cpp_config -> string -> Ail_to_coq.typed_ail

(** [cpp_lines config fname] preprocesses the C file [fname] with Cerberus and
    returns the obtained list of lines. The configuration [config] can be used
    to alter the behaviour of the preprocessor. In case of an error, a message
    is displayed and the program exits with error code [-1]. *)
val cpp_lines : cpp_config -> string -> string list

(** [print_ail ast] outputs the given Ail [ast] to standard output. *)
val print_ail : Ail_to_coq.typed_ail -> unit
