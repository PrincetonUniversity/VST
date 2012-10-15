(* lexer *)
exception Illegal_character of char * Location.t
exception Unterminated_comment of Location.t

(* parser *)
exception Not_distinct of string * Location.t
exception Parameters_not_variables of Location.t
exception Parse_error of Location.t

(* vcgen *)
exception Vcgen_unknown_fun of string * Location.t
exception Vcgen_unknown_res of string * Location.t
exception Vcgen_wrong_arg_num of string * string list * Symbtree.can_exp list * Location.t
exception Vcgen_rsrc_not_distinct of string * Location.t
exception Vcgen_owned_not_disjoint of string * string * string * Location.t
exception Vcgen_owned_free_in_inv of string * string * string * Location.t
exception Vcgen_modify_spec of string * string * string * Location.t
exception Vcgen_var_race of string * string * string * Location.t
exception Vcgen_rsrc_init_race of string * string * Location.t
exception Vcgen_non_seq_initzer of string * Location.t
exception Vcgen_multiple_mains of Location.t * Location.t
exception Vcgen_multiple_inits of Location.t * Location.t
exception Vcgen_main_nonempty_req of Location.t
exception Vcgen_global_ref of string * string * Location.t
exception Vcgen_bound_globals of string * string * string * string * Location.t
exception Vcgen_param_locals of string * string * Location.t

(* symbolic execution *)
exception Symb_exe_entail of Symbtree.can_form * Symbtree.can_form * string * Location.t
exception Symb_exe_noframe of Symbtree.can_form * Symbtree.can_form * string * Location.t
exception Symb_exe_heap_error

(* reporting *)
let print loc =
  let fmt = !Config.formatter in
    Location.print fmt loc;
    Format.fprintf fmt

let sprint loc = "\n" ^ (Location.sprint loc)

let report ?(nonfatal_thunk = fun () -> assert false) thunk =
  try thunk () with
(* lexer *)
    | Illegal_character(c,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Syntax error: Illegal character (%s)@." (Char.escaped c)))
    | Unterminated_comment(loc) ->
	invalid_arg ((sprint loc) ^ (Format.sprintf "Syntax error: Unterminated comment@."))
(* parser *)
    | Not_distinct(s,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Syntax error: %s must be distinct@." s))
    | Parameters_not_variables(loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Syntax error: Reference parameters must be variables@."))
    | Parse_error(loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Parse error@."))
    | Parsetree.Undef_a_exp_of_p_exp(loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Unknown expression@."))
    | Parsetree.Undef_a_prop_of_p_exp(loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Unknown proposition@."))
    | Symbtree.Undef_prop_to_can_atom(s) ->
	invalid_arg("Syntax error: " ^ s ^ " not an atomic formula\n")
(* vcgen *)
    | Vcgen_unknown_fun (fid,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Function %s is not defined@." fid))
    | Vcgen_unknown_res (rid,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Resource %s is not defined@." rid))
    | Vcgen_wrong_arg_num (s,l1,l2,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Function call has %d %s arguments but %d expected@." (List.length l2) s (List.length l1)))
    | Vcgen_modify_spec (fid,id,fid',loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Function %s modifies %s which appears in the spec of %s@." fid id fid'))
    | Vcgen_var_race (fid,id,fid',loc) ->
      invalid_arg((sprint loc) ^ (Format.sprintf "RACE: function %s modifies %s which is accessed by %s@." fid id fid'))
    | Vcgen_rsrc_init_race (rid,id,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "RACE: resource initializer for %s modifies %s which appears in another resource@." rid id))
    | Vcgen_rsrc_not_distinct (rid,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Resource name %s is not unique@." rid))
    | Vcgen_owned_not_disjoint (id,rid,rid',loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Variable %s is protected by both resources %s and %s@." id rid rid'))
    | Vcgen_owned_free_in_inv (id,rid,rid',loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Variable %s appears in the invariant of %s but is protected by %s@." id rid rid'))
    | Vcgen_non_seq_initzer (rid,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Initializer of resource %s is not sequential@." rid))
    | Vcgen_multiple_mains (loc,loc') ->
	invalid_arg("\n" ^ (Location.sprint loc') ^ (Location.sprint loc) ^ (Format.sprintf "More than one main()@."))
    | Vcgen_multiple_inits (loc,loc') ->
	invalid_arg("\n" ^ (Location.sprint loc') ^ (Location.sprint loc) ^ (Format.sprintf "More than one init()@."))
    | Vcgen_main_nonempty_req (loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "main() requires nonempty resources@."))
    | Vcgen_global_ref (id,fid,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Global variable %s is (recusively) mentioned in %s and cannot be passed by reference@." id fid))
    | Vcgen_bound_globals (sx,x,sid,id,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Global variable %s cannot be a %s variable in %s %s@." x sx sid id))
    | Vcgen_param_locals (x,fid,loc) ->
	invalid_arg((sprint loc) ^ (Format.sprintf "Variable %s in function %s cannot be both a parameter and a local@." x fid))
(* symbolic execution *)
    | Symb_exe_entail (cf1,cf2,s,loc) ->
	print loc "ERROR invalid entailment: %s@.%a@." s Symbtree.pp_sp_entailment (cf1,cf2);
	nonfatal_thunk()
    | Symb_exe_noframe (cf1,cf2,s,loc) ->
	print loc "ERROR cannot find frame: %s@.%a@." s Symbtree.pp_sp_entailment (cf1,cf2);
	nonfatal_thunk()
    | Symb_exe_heap_error -> nonfatal_thunk()
