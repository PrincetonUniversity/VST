(** Output and debugging utilities. *)

open Extra

type loc = Cerb_location.t

let pp_loc : loc pp = fun oc loc ->
  Format.pp_print_string oc (Cerb_location.location_to_string loc)

let pp_loc_opt : loc option pp = fun oc lopt ->
  Option.iter (Format.fprintf oc "[%a] " pp_loc) lopt

(** Short name for a standard formatter. *)
type 'a outfmt = ('a, Format.formatter, unit) format

(** Short name for a standard formatter with continuation. *)
type ('a, 'b) koutfmt = ('a, Format.formatter, unit, unit, unit, 'b) format6

(** Format transformers (colors). *)
let with_color k fmt = "\027[" ^^ k ^^ "m" ^^ fmt ^^ "\027[0m%!"

let red fmt = with_color "31" fmt
let gre fmt = with_color "32" fmt
let yel fmt = with_color "33" fmt
let blu fmt = with_color "34" fmt
let mag fmt = with_color "35" fmt
let cya fmt = with_color "36" fmt

let info : 'a outfmt -> 'a = Format.printf

(** [wrn loc_opt fmt] outputs a waning to [stderr] using [Format] format [fmt]
    and the correponding arguments. If [loc_opt] is [Some(loc)], then location
    [loc] is shown as a prefix of the warning. Note that a newline is added to
    the end of the message automatically, and that [stderr] is flushed. *)
let wrn : loc option -> 'a outfmt -> 'a = fun lopt fmt ->
  Format.eprintf (yel ("%a" ^^ fmt ^^ "\n")) pp_loc_opt lopt

(** [panic loc fmt] interrupts the program with [exit 1], after displaying the
    error message described by [Format] format [fmt].  Location [loc] is shown
    as a prefix of the error message,  and a newline is automatically inserted
    at its end ([stderr] is also flushed) *)
let panic : loc -> ('a, 'b) koutfmt -> 'a = fun loc fmt ->
  let fmt = red ("[%a] " ^^ fmt ^^ "\n") in
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter fmt pp_loc loc

(** [panic_no_pos fmt] is similar to [panic _ fmt], but has no location. *)
let panic_no_pos : ('a,'b) koutfmt -> 'a = fun fmt ->
  let fmt = red (fmt ^^ "\n") in
  Format.kfprintf (fun _ -> exit 1) Format.err_formatter fmt

(** Simpler interface for when there is no precise position. *)
module Simple =
  struct
    let panic : ('a,'b) koutfmt -> 'a = panic_no_pos
    let wrn   : 'a outfmt -> 'a = fun fmt -> wrn None fmt
    let info  : 'a outfmt -> 'a = info
  end
