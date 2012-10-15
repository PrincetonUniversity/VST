type a_component = string

and a_expression =
  | Aexp_ident of string
  | Aexp_num of int
  | Aexp_uminus of a_expression
  | Aexp_infix of string * a_expression * a_expression
	  (* string is one of "+", "-", "*", "/", "%" *)

type dlink_kind = DL | XL

type a_space_pred =
  | Aspred_list of a_component * a_expression
  | Aspred_listseg of a_component * a_expression * a_expression
  | Aspred_dlseg of dlink_kind * a_component * a_expression * a_expression * a_component * a_expression * a_expression
  | Aspred_tree of a_component * a_component * a_expression
  | Aspred_empty
  | Aspred_pointsto of a_expression * (a_component * a_expression) list

type a_proposition =
  | Aprop_infix of string * a_expression * a_expression
	  (* string is one of "<", "<=", ">", ">=" *)
  | Aprop_equal of a_expression * a_expression
  | Aprop_not_equal of a_expression * a_expression
  | Aprop_false
  | Aprop_ifthenelse of a_proposition * a_proposition * a_proposition
  | Aprop_star of a_proposition * a_proposition
  | Aprop_spred of a_space_pred

type p_expression =
	{ pexp_desc: p_expression_desc;
	  pexp_loc: Location.t }

and p_expression_desc =
  | Pexp_ident of string
  | Pexp_num of int
  | Pexp_prefix of string * p_expression
      (* string is "+" or "-" *)
  | Pexp_infix of string * p_expression * p_expression
      (* string is one of "==", "!=", "^", "&&", "<", "<=", ">", ">=", "+", "-", "*", "/", "%" *)

type a_invariant = a_proposition option

type p_statement =
	{ pstm_desc: p_statement_desc;
	  pstm_loc: Location.t }

and p_statement_desc =
  | Pstm_assign of string * p_expression
  | Pstm_fldlookup of string * p_expression * a_component
  | Pstm_fldassign of p_expression * a_component * p_expression
  | Pstm_new of string
  | Pstm_dispose of p_expression
  | Pstm_block of p_statement list
  | Pstm_if of p_expression * p_statement * p_statement
  | Pstm_while of a_invariant * p_expression * p_statement
  | Pstm_withres of string * p_expression * p_statement
  | Pstm_fcall of string * actual_params
  | Pstm_parallel_fcall of string * actual_params * string * actual_params
and actual_params = string list * p_expression list

type p_item =
  | Pfundecl of string * (string list * string list) * a_invariant *
      string list * p_statement list * a_invariant * Location.t * Location.t
  | Presource of string * string list * a_proposition * Location.t

type p_program =
  | Pprogram of a_component list * p_item list

(* iter f s calls f on each statement in s *)
val iter : (Location.t -> p_statement_desc -> unit) -> p_statement list -> unit

(* pretty-print a_expression *)
val pp_a_exp : Format.formatter -> a_expression -> unit

(* pretty-print assertions *)
val pp_assert : Format.formatter -> a_proposition -> unit

(* the expression corresponding to nil *)
val aexp_nil : a_expression

(* the a_expression corresponding to a p_expression *)
val a_exp_of_p_exp : p_expression -> a_expression

(* raised when a_exp_of_p_exp is given an argument p_expression which does not
 * correspond to an a_expression *)
exception Undef_a_exp_of_p_exp of Location.t

(* the a_proposition corresponding to a p_expression *)
val a_prop_of_p_exp : p_expression -> a_proposition

(* raised when a_prop_of_p_exp is given an argument p_expression which does not
 * correspond to an a_proposition *)
exception Undef_a_prop_of_p_exp of Location.t
