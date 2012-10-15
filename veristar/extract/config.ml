let formatter = ref Format.std_formatter
let columns = ref 72

let print_gc_stats = false

let repetitions = ref 1

let verbose1 = ref false
let verbose2 = ref false
let all_states = ref false
let show_induction = ref false

let inductive_preds = ref false

(* default component tags *)
let list_data_tag = "hd"
let list_link_tag = "tl"
let tree_data_tag = "d"
let tree_link_tags = "l", "r"
let dl_Llink_tag,dl_Rlink_tag = tree_link_tags (* the parser assumes this *)

(* command line arguments *)
let speclist = (*Arg.align*)
  [("-repetitions", Arg.Int (fun n -> repetitions := n), "    Verify a number of times repeatedly");
   ("-columns", Arg.Int (fun n -> columns := n), "        Format output for a number of columns");
   ("-verbose", Arg.Unit (fun () ->
                          verbose1 := true;
                          verbose2 := false;
			  all_states := false;
			  show_induction := false), "        Display additional internal information");
   ("-all_states", Arg.Unit (fun () -> all_states := true), "     Display intermediate states");
   ("-show_induction", Arg.Unit (fun () -> show_induction := true), " Indicate when induction is used during verification");
   ("-very_verbose", Arg.Unit (fun () ->
                            verbose1 := true;
                            verbose2 := true;
			    all_states := true;
                            show_induction := true), "   Display more additional internal information")]

let usage_msg =
  "Usage: " ^ Sys.argv.(0) ^
  " [-repetitions n] [-columns n] [([-verbose] [-all_states] [-show_induction]) | [-very_verbose]] <files>"
