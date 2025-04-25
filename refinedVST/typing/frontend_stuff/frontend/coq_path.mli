(** Management of Coq module paths.

    Coq modules path identifiers and file names are restricted to be valid Coq
    identifiers, with further restrictions (only ASCII letters, digits and the
    underscore symbol). This module provides types that encapsulate components
    of Coq module paths into abstract types, to enforces that they are valid.

    Useful links:
    - https://coq.inria.fr/refman/practical-tools/coq-commands.html
    - https://coq.inria.fr/refman/language/core/basic.html#lexical-conventions
*)

open Extra

(** Coq module path member. *)
type member

(** [member_of_string s] converts string [s] into a Coq module path member. If
    the given string does not correspond to a valid path member, the exception
    [Invalid_argument] is raised with an explanatory error message formed of a
    full sentence, to be displayed directly (and ideally on its own line). *)
val member_of_string : string -> member

(** [fixup_string_member s] tries to build a resonable (valid) Coq module path
    member name from the string [s]. This is done by replacing diacritic marks
    by corresponding ASCII sequences if applicable, and by using ['_'] instead
    of invalid characters like ['-']. If a result string is produced, applying
    the [member_of_string] function to it is guaranteed to succeed. *)
val fixup_string_member : string -> string option

(** Coq module path. *)
type path

(** Short synonym for [path]. *)
type t = path

(** [path_of_members ms] turns the (non-empty) list of members [ms] into a Coq
    module path. If [ms] is empty then [Invalid_argument] is raised. *)
val path_of_members : member list -> path

(** [path_of_string s] parses string [s] into a Coq module path. In case where
    [s] does not denote a valid module path, then exception [Invalid_argument]
    is raised with a full, explanatory error message. *)
val path_of_string : string -> path

(** [fixup_string_path s] is similar to [fixup_string_member] but for full Coq
    module paths. If a result string is produced, applying [path_of_string] to
    it it guaranteed to succeed (no exception is produced). *)
val fixup_string_path : string -> string option

(** Coq path suffix. *)
type suffix = member list

(** [append path suff] extends the Coq path [path] with suffix [suff]. *)
val append : t -> suffix -> t

(** [to_string path] converts the path [path] into a string directly usable as
    the Coq representation of the path. *)
val to_string : path -> string

(** [pp ff path] prints the string representation of [path] (as obtained using
    [to_string]) to the [ff] formatter. *)
val pp : path pp
