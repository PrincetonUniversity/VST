open Misc

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

and p_expression =
    { pexp_desc: p_expression_desc;
      pexp_loc: Location.t }

and p_expression_desc =
  | Pexp_ident of string
  | Pexp_num of int
  | Pexp_prefix of string * p_expression
  | Pexp_infix of string * p_expression * p_expression

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

type fun_item =
    { fid : string;
      param: string list * string list;
      locals: StringSet.t;
      mutable calls: StringSet.t;
      modif: StringSet.t;
      pre: a_invariant;
      body: p_statement list;
      post: a_invariant;
      post_loc: Location.t;
      fun_loc: Location.t }

type p_program =
  | Pprogram of a_component list * p_item list

(* iter f s calls f on each statement in s *)
let iter f =
  let rec loop = function
    | [] -> ()
    | {pstm_desc=stm; pstm_loc=loc} :: stms ->
	f loc stm;
	match stm with
	  | Pstm_block(stm_l) -> loop (stm_l @ stms)
	  | Pstm_if(_,s0,s1) -> loop (s0 :: s1 :: stms)
	  | Pstm_while(_,_,s) -> loop (s :: stms)
	  | Pstm_withres(_,_,s) -> loop (s :: stms)
	  | _ -> loop stms
  in loop

open Format

(* pretty-print assertions

   - precedences are integers from 0 to 8
   - parent_prec is the precedence of the parent node of the parsetree
   - parent_posn indicates the left (-1), only (0), or right (1) child of the
   parent node
   - prec is the precedence of the current node
   - assoc is the associativity of the current node: left (-1), non (0),
   right (1)
 *)

let check_parens parent_prec parent_posn prec assoc =
  parent_prec > prec
  or (parent_prec <= prec & parent_posn == -assoc & assoc != 0)

let rec pp_a_component parent_prec parent_posn f =
  function t -> fprintf f "%s" t

and pp_a_expression parent_prec parent_posn f =
  let ppae = pp_a_expression parent_prec 0
  in function
    | Aexp_ident i -> fprintf f "%s" i
    | Aexp_num n -> fprintf f "%d" n
    | Aexp_uminus e -> fprintf f "@[<hv 2>-%a@]" ppae e
    | Aexp_infix (o, e1, e2) ->
	fprintf f "@[<hv 2>%a@ %s %a@]" ppae e1 o ppae e2

let pp_string f s = fprintf f "%s" s

let pp_list pp f l = List.iter (fun x -> fprintf f " %a" pp x) l

let rec pp_listsep pp s f = function
  | [] -> ()
  | [x] -> fprintf f "%a" pp x
  | x::l -> fprintf f "%a%s%a" pp x s (pp_listsep pp s) l

and pp_a_proposition pprc ppsn f =
  let cp = check_parens pprc ppsn
  and ppae = pp_a_expression
  and ppap = pp_a_proposition
  and ppac = pp_a_component
  and ppace parent_prec parent_posn f (c,e) =
    fprintf f "%a:%a" (pp_a_component parent_prec parent_posn) c
      (pp_a_expression parent_prec parent_posn) e
  in function
    | Aprop_infix (o, e1, e2) ->
	if cp 5 (-1)
	then fprintf f "@[<hv 2>(%a@ %s %a)@]" (ppae 5 (-1)) e1 o (ppae 5 1) e2
	else fprintf f "@[<hv 2>%a@ %s %a@]" (ppae 5 (-1)) e1 o (ppae 5 1) e2
    | Aprop_equal (e1, e2) ->
	if cp 5 (-1)
	then fprintf f "@[<hv 2>(%a@ == %a)@]" (ppae 5 (-1)) e1 (ppae 5 1) e2
	else fprintf f "@[<hv 2>%a@ == %a@]" (ppae 5 (-1)) e1 (ppae 5 1) e2
    | Aprop_not_equal (e1, e2) ->
	if cp 5 (-1)
	then fprintf f "@[<hv 2>(%a@ != %a)@]" (ppae 5 (-1)) e1 (ppae 5 1) e2
	else fprintf f "@[<hv 2>%a@ != %a@]" (ppae 5 (-1)) e1 (ppae 5 1) e2
    | Aprop_false ->
	fprintf f "ff"
    | Aprop_ifthenelse (p,p1,p2) ->
	fprintf f "@[<hv 2>if %a@ then %a@ else %a]" (ppap 0 0) p (ppap 0 0) p1 (ppap 0 0) p2
    | Aprop_star (p1, p2) ->
	if cp 6 (-1)
	then fprintf f "@[<hv 2>(%a@ * %a)@]" (ppap 6 (-1)) p1 (ppap 6 (-1)) p2
	else fprintf f "@[<hv 2>%a@ * %a@]" (ppap 6 (-1)) p1 (ppap 6 (-1)) p2
    | Aprop_spred (Aspred_list (c,e)) ->
	fprintf f "@[<hv 2>list(%a;%a)@]"
	(ppac 0 (-1)) c (ppae 0 1) e
    | Aprop_spred (Aspred_listseg (c,e1,e2)) ->
	fprintf f "@[<hv 2>listseg(%a;@,%a,%a)@]" (ppac 0 0) c
	(ppae 0 0) e1 (ppae 0 0) e2
    | Aprop_spred (Aspred_dlseg (k,c1,e1,f1,c2,e2,f2)) ->
	fprintf f "@[<hv 2>%s(%a,%a;@,%a,%a,%a,%a)@]"
	 (if k=DL then "dlseg" else "xlseg")
	 (ppac 0 0) c1 (ppac 0 0) c2
	 (ppae 0 0) e1 (ppae 0 0) f1 (ppae 0 0) e2 (ppae 0 0) f2
    | Aprop_spred (Aspred_tree (c1,c2,e1)) ->
	fprintf f "@[<hv 2>tree(%a,@,%a;%a)@]" (ppac 0 0) c1
	(ppac 0 0) c2 (ppae 0 0) e1
    | Aprop_spred (Aspred_empty) ->
	fprintf f "empty"
    | Aprop_spred (Aspred_pointsto (e1, el)) ->
	if cp 7 (-1)
        then fprintf f "@[<hv 2>(%a@ |-> %a)@]" (ppae 7 (-1)) e1 (pp_listsep (ppace 7 1) ",") el
        else fprintf f "@[<hv 2>%a@ |-> %a@]" (ppae 7 (-1)) e1 (pp_listsep (ppace 7 1) ",") el

let pp_a_exp = pp_a_expression 0 0

let pp_assert = pp_a_proposition 0 0

let aexp_nil = Aexp_num 0

(* raised when a_exp_of_p_exp is given an argument p_expression which does not
 * correspond to an a_expression *)
exception Undef_a_exp_of_p_exp of Location.t

(* the a_expression corresponding to a p_expression *)
let rec a_exp_of_p_exp {pexp_desc = d; pexp_loc = l} =
  (match d with
     | Pexp_ident i -> Aexp_ident i

     | Pexp_num n -> Aexp_num n

     | Pexp_prefix ("+", e) -> a_exp_of_p_exp e
     | Pexp_prefix ("-", e) -> Aexp_uminus (a_exp_of_p_exp e)
     | Pexp_prefix _ -> assert false

     | Pexp_infix ("||", _, _)
     | Pexp_infix ("&&", _, _)
     | Pexp_infix ("==", _, _)
     | Pexp_infix ("!=", _, _)
     | Pexp_infix ("<", _, _)
     | Pexp_infix ("<=", _, _)
     | Pexp_infix (">", _, _)
     | Pexp_infix (">=", _, _) -> raise (Undef_a_exp_of_p_exp l)
     | Pexp_infix ("+", e1, e2) ->
	 Aexp_infix ("+", a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix ("-", e1, e2) ->
	 Aexp_infix ("-", a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix ("*", e1, e2) ->
	 Aexp_infix ("*", a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix ("/", e1, e2) ->
	 Aexp_infix ("/", a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix ("%", e1, e2) ->
	 Aexp_infix ("%", a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix ("^", e1, e2) ->
	 Aexp_infix ("^", a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix _ -> assert false)

(* raised when a_prop_of_p_exp is given an argument p_expression which does not
 * correspond to an a_proposition *)
exception Undef_a_prop_of_p_exp of Location.t

(* the a_proposition corresponding to a p_expression *)
let rec a_prop_of_p_exp {pexp_desc = d; pexp_loc = l} =
  (match d with
     | Pexp_ident _

     | Pexp_num _ -> raise (Undef_a_prop_of_p_exp l)

     | Pexp_prefix ("+", _)
     | Pexp_prefix ("-", _) -> raise (Undef_a_prop_of_p_exp l)
     | Pexp_prefix _ -> assert false

     | Pexp_infix ("&&", e1, e2) ->
	 Aprop_star (a_prop_of_p_exp e1, a_prop_of_p_exp e2)
     | Pexp_infix ("==", e1, e2) ->
	 Aprop_equal (a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix ("!=", e1, e2) ->
	 Aprop_not_equal (a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix ("<", e1, e2) ->
	 Aprop_infix ("<", a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix ("<=", e1, e2) ->
	 Aprop_infix ("<=", a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix (">", e1, e2) ->
	 Aprop_infix (">", a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix (">=", e1, e2) ->
	 Aprop_infix (">=", a_exp_of_p_exp e1, a_exp_of_p_exp e2)
     | Pexp_infix ("+", _, _)
     | Pexp_infix ("-", _, _)
     | Pexp_infix ("*", _, _)
     | Pexp_infix ("/", _, _)
     | Pexp_infix ("%", _, _) -> raise (Undef_a_prop_of_p_exp l)
     | Pexp_infix _ -> assert false)
