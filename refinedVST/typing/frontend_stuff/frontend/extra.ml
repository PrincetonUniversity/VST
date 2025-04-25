(** Standard library extension (mostly). *)

(** Short name for the type of a pretty-printing function. *)
type 'a pp = Format.formatter -> 'a -> unit

(** Short name for the type of an equality function. *)
type 'a eq = 'a -> 'a -> bool

(** Short name for the type of a comparison function. *)
type 'a cmp = 'a -> 'a -> int

module Int =
  struct
    type t = int
    let compare = (-)
  end

module Char =
  struct
    include Char

    let printable_ascii : char -> bool = fun c ->
      ' ' <= c && c <= '~'
  end

module Option =
  struct
    type 'a t = 'a option

    let map : ('a -> 'b) -> 'a t -> 'b t = fun f o ->
      match o with
      | None    -> None
      | Some(e) -> Some(f e)

    let map_default : ('a -> 'b) -> 'b -> 'a option -> 'b = fun f d o ->
      match o with
      | None    -> d
      | Some(e) -> f e

    let iter : ('a -> unit) -> 'a t -> unit = fun f o ->
      match o with
      | None    -> ()
      | Some(e) -> f e

    let get : 'a -> 'a option -> 'a = fun d o ->
      match o with
      | None    -> d
      | Some(e) -> e

    let equal : 'a eq -> 'a option eq = fun eq o1 o2 ->
      match (o1, o2) with
      | (None    , None    ) -> true
      | (Some(e1), Some(e2)) -> eq e1 e2
      | (_       , _       ) -> false

    let pp : 'a pp -> 'a option pp = fun pp_elt oc o ->
      match o with
      | None   -> ()
      | Some e -> pp_elt oc e
  end

module Filename =
  struct
    include Filename

    (** [realpath path] returns the absolute canonical path to file [path]. If
        [path] is invalid (i.e., it does not describe an existing file),  then
        the exception [Invalid_argument] is raised. *)
    external realpath : string -> string = "c_realpath"

    (** [iter_files ?ignored_dirs dir f] recursively traverses directory [dir]
        and calls function [f] on each file, using as first argument a boolean
        indicating whether the file is a directory, and as second arugment the
        full path to the file. The traversal ignores directories whose name is
        contained in [ignored_dirs], as well as their contents. *)
    let iter_files : ?ignored_dirs:string list -> string
        -> (bool -> string -> unit) -> unit = fun ?(ignored_dirs=[]) dir f ->
      let rec iter dirs =
        match dirs with
        | []                  -> ()
        | (dir, base) :: dirs ->
        let file = Filename.concat dir base in
        let is_dir = Sys.is_directory file in
        (* Ignore if necessary. *)
        match is_dir && List.mem base ignored_dirs with
        | true  -> iter dirs
        | false ->
        (* Run the action on the current file. *)
        f is_dir file;
        (* Compute remaining files. *)
        if is_dir then
          let files = Sys.readdir file in
          let fn name dirs = (file, name) :: dirs in
          iter (Array.fold_right fn files dirs)
        else
          iter dirs
      in
      iter [(Filename.dirname dir, Filename.basename dir)]

    (** [relative_path root file] computes a relative filepath for [file] with
        its origin at [root]. The exception [Invalid_argument] is raised if an
        error occurs. *)
    let relative_path : string -> string -> string = fun root file ->
      let root = realpath root in
      let file = realpath file in
      if root = file then "." else
      let root_len = String.length root in
      let full_len = String.length file in
      if root_len > full_len then
        invalid_arg "Extra.Filename.relative_path";
      let file_root = String.sub file 0 root_len in
      if file_root <> root then
        invalid_arg "Extra.Filename.relative_path";
      String.sub file (root_len + 1) (full_len - root_len - 1)
  end

module SMap = Map.Make(String)
module IMap = Map.Make(Int)

module List =
  struct
    include List

    (** [filter_map f l] applies function [f] to the elements of [l], and then
        filters out then [None]. *)
    let rec filter_map : ('a -> 'b option) -> 'a list -> 'b list = fun f l ->
      match l with
      | []     -> []
      | h :: t ->
          match f h with
          | Some(x) -> x :: filter_map f t
          | None    -> filter_map f t

    let find_index : ('a -> bool) -> 'a list -> int = fun p l ->
      let rec find i l =
        match l with
        | []     -> raise Not_found
        | x :: l -> if p x then i else find (i+1) l
      in
      find 0 l

    (** [dedup cmp l] filters out dupplicates from list [l] using the function
        [cmp] to compare elements. It is assumed to be a valid function to use
        in the instantiation of the [Set.Make] functor. *)
    let dedup : type a. (a -> a -> int) -> a list -> a list = fun cmp l ->
      let module S =
        Set.Make(struct
          type t = a
          let compare = cmp
        end)
      in
      let rec dedup elts l =
        match l with
        | []                       -> []
        | x :: l when S.mem x elts -> dedup elts l
        | x :: l                   -> x :: dedup (S.add x elts) l
      in
      dedup S.empty l
  end

module Buffer =
  struct
    include Buffer

    let add_full_channel : t -> in_channel -> unit = fun buf ic ->
      try
        while true do
          add_char buf (input_char ic)
        done
      with End_of_file -> ()

    let add_file : t -> string -> unit = fun buf fname ->
      let ic = open_in fname in
      add_full_channel buf ic;
      close_in ic

    let from_file : string -> t = fun fname ->
      let buf = create 4096 in
      add_file buf fname; buf

    let to_file : string -> t -> unit = fun fname buf ->
      let oc = open_out fname in
      output_buffer oc buf;
      close_out oc
  end

module String =
  struct
    include String

    let for_all : (char -> bool) -> string -> bool = fun p s ->
      try iter (fun c -> if not (p c) then raise Exit) s; true
      with Exit -> false

    let sub_from : string -> int -> string = fun s i ->
      sub s i (length s - i)

    let trim_leading : char -> string -> string = fun c s ->
      let len = length s in
      let index = ref 0 in
      while !index < len && s.[!index] = '_' do incr index done;
      sub_from s !index
  end

(** [outut_lines oc ls] prints the lines [ls] to the output channel [oc]. Note
    that a newline character is added at the end of each line. *)
let output_lines : out_channel -> string list -> unit = fun oc ls ->
  List.iter (Printf.fprintf oc "%s\n") ls

(** [write_file fname ls] writes the lines [ls] to file [fname]. All lines are
    terminated with a newline character. *)
let write_file : string -> string list -> unit = fun fname ls ->
  let oc = open_out fname in
  output_lines oc ls; close_out oc

(** [append_file fname ls] writes the lines [ls] at the end of file [fname]. A
    newline terminates each inserted lines. The file must exist. *)
let append_file : string -> string list -> unit = fun fname ls ->
  let oc = open_out_gen [Open_append] 0 fname in
  output_lines oc ls; close_out oc

(** [read_file fname] returns the list of the lines of file [fname]. Note that
    the trailing newlines are removed. *)
let read_file : string -> string list = fun fname ->
  let ic = open_in fname in
  let lines = ref [] in
  try
    while true do lines := input_line ic :: !lines done;
    assert false (* Unreachable. *)
  with End_of_file -> close_in ic; List.rev !lines

(** Short name for a standard formatter with continuation. *)
type ('a,'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** [invalid_arg fmt ...] raises [Invalid_argument] with the given message. It
    can be formed using the standard formatter syntax. *)
let invalid_arg : ('a, 'b) koutfmt -> 'a = fun fmt ->
  let cont _ = invalid_arg (Format.flush_str_formatter ()) in
  Format.kfprintf cont Format.str_formatter fmt
