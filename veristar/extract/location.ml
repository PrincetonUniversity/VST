open Lexing

type t_record = {file: string; line: int; start_char: int; end_char: int}
type t = t_record option

let none : t = None

let mkloc s e =
  Some{file = e.pos_fname; (* s.pos_fname might not be set *)
       line = s.pos_lnum;
       start_char = s.pos_cnum - s.pos_bol;
       end_char = e.pos_cnum - s.pos_bol}
    (* for end_char, subtracting e and s is intentional, to handle
       multiline locations *)

let symbol_loc () = mkloc (Parsing.symbol_start_pos()) (Parsing.symbol_end_pos())
let rhs_loc n = mkloc (Parsing.rhs_start_pos n) (Parsing.rhs_end_pos n)


let sprint loc = match loc with
  | Some{file=f; line=l; start_char=s; end_char=e} ->
      Format.sprintf "File \"%s\", line %i, characters %i-%i:@." f l s e
  | None -> ""

let print fmt loc = Format.pp_print_string fmt (sprint loc)

let lexbuf : Lexing.lexbuf option ref = ref None
