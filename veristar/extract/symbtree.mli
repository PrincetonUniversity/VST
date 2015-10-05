open Misc
open Parsetree

type component = string

(* canonical expression *)
type can_exp =
  | Ce_num of int
  | Ce_ident of ident
  | Ce_xor of can_exp * can_exp

(* canonical atom: e1==e2 or e1!=e2 *)
type can_atom =
  | EQ of can_exp * can_exp
  | NEQ of can_exp * can_exp

type link_kind = SINGLE | DOUBLE | XOR

type can_spred =
  | Csp_listseg of link_kind * component * can_exp * can_exp * component * can_exp * can_exp
  | Csp_pointsto of can_exp * (component * can_exp) list
  | Csp_tree of component * component * can_exp
  | Csp_indpred of string * can_exp list * component list

type can_form = can_atom list * can_spred list

type can_prop =
  | Cp_base of can_form
  | Cp_ifthenelse of can_atom * can_prop * can_prop
  | Cp_star of can_prop * can_prop

type can_stmt =
  { can_st_desc: can_st_desc;
    can_st_loc: Location.t }

and can_cmd = can_stmt list

and can_st_desc =
  | Cst_ifthenelse of can_atom * can_cmd * can_cmd
  | Cst_assign of ident * can_exp
  | Cst_fldlookup of ident * can_exp * string
  | Cst_fldassign of can_exp * string * can_exp
  | Cst_new of ident
  | Cst_dispose of can_exp
  | Cst_fcall of IdSet.t * can_prop * can_prop * string
  | Cst_wand of can_prop

type can_entailment = can_prop * can_cmd * can_prop * string * Location.t

exception Inconsistent
exception Undef_prop_to_can_atom of string

(* conversion *)
val a_exp_to_can_exp : a_expression -> can_exp
val p_exp_to_can_exp : p_expression -> can_exp
val can_atom_to_can_prop: can_atom -> can_prop
val can_prop_empty : can_prop
val is_can_prop_empty : can_prop -> bool
val can_prop_star: can_prop -> can_prop -> can_prop
val and_cprop_catom : can_prop -> can_atom -> can_prop
val prop_to_can_atom : ?quiet:bool -> a_proposition -> can_atom
val prop_to_can_prop : a_proposition -> can_prop

(* misc ops *)
val mk_EQ : can_exp * can_exp -> can_atom
val mk_NEQ : can_exp * can_exp -> can_atom
val is_EQ: can_atom -> bool
val un_EQ: can_atom -> can_exp * can_exp
val un_NEQ: can_atom -> can_exp * can_exp
val is_uneq : can_atom list -> can_exp * can_exp -> bool
val neg_can_atom : can_atom -> can_atom
val eval_can_atom : can_atom -> bool
val can_spred_eq : can_spred * can_spred -> bool
val fv_norm_can_atom : can_atom -> IdSet.t
val fv_can_exp : can_exp -> IdSet.t
val fv_norm_can_prop : can_prop -> IdSet.t

(* substitutions *)
type subst
val mk_subst : (ident -> can_exp) -> (component->component) -> subst
val mk_subst_pairs : (ident * can_exp) list -> subst
val mk_single_subst : (ident * can_exp) -> subst
val mk_gensym_garb_subst : ident -> subst
val mk_gensym_subst_list : ident list -> subst
val mk_gensym_garb_subst_list : ident list -> subst
val sub_can_exp : subst -> can_exp -> can_exp
val sub_can_atom : subst -> can_atom -> can_atom
val sub_can_spred : subst -> can_spred -> can_spred
val sub_can_form : subst -> can_form -> can_form
val sub_can_prop : subst -> can_prop -> can_prop
val sub_idset : subst -> IdSet.t -> IdSet.t

(* equalities *)
type equalities
val empty_eq : equalities
val eq_add : equalities -> (can_exp * can_exp) -> equalities
val sub_equalities : subst -> equalities -> equalities
val eq_to_sub : equalities -> subst
val eq_to_can_prop : equalities -> can_prop

(* normalization *)
val normalize_can_exp : can_exp -> can_exp
val normalize_can_form : can_form -> can_form
val kill_garbage_vars : equalities * can_prop -> equalities * can_prop

(* constraints *)
type constr = (can_exp * can_exp) list * (can_exp * can_exp)
type constraints
val empty_constrs : constraints
val add_constr : constraints -> constr -> constraints
val simplify_constraints : can_atom list * constraints -> can_atom list * constraints
val solve_constraints : equalities -> can_atom list -> constraints -> equalities * can_atom list * constraints

(* existentials *)
val existential_id : can_exp -> bool
val ex_fv_can_prop : can_prop -> IdSet.t
val existentials_sub : IdSet.t -> subst

(* pretty printing *)
val pp_listsep : (Format.formatter -> 'a -> unit) ->
      string -> string -> Format.formatter -> 'a list -> unit
val pp_can_exp : Format.formatter -> can_exp -> unit
val pp_can_atom : Format.formatter -> can_atom -> unit
val pp_can_spred : Format.formatter -> can_spred -> unit
val pp_can_form : Format.formatter -> can_form -> unit
val pp_can_prop : Format.formatter -> can_prop -> unit
val pp_sp_entailment : Format.formatter -> can_form * can_form -> unit
val pp_can_entailment : Format.formatter -> can_form * can_form -> unit
val pp_pure_entailment : Format.formatter -> can_form * can_atom -> unit
val pp_spatial_list : Format.formatter -> can_spred list -> unit
val pp_entailment : Format.formatter -> can_entailment -> unit
val pp_inst : Format.formatter -> (ident * can_exp) list -> unit
val pp_constraints : Format.formatter -> (can_atom list * constraints) -> unit
