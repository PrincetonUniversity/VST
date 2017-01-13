
let debugging = ref false

(* pretty-print clauses *)

let rec pos2int = function
  | XH -> 1
  | XO(p) -> 2 * pos2int p
  | XI(p) -> 2 * pos2int p + 1

let pp_expr = function
  | Nil -> "nil"
  | Var(x) -> string_of_int x

let pp_atm = function
  | Eqv(t1, t2) -> pp_expr t1 ^ "=" ^ pp_expr t2

let pp_space_atm = function
  | Lseg(t1, t2) -> "lseg(" ^ pp_expr t1 ^ "," ^ pp_expr t2 ^ ")"
  | Next(t1, t2) -> "next(" ^ pp_expr t1 ^ "," ^ pp_expr t2 ^ ")"

let rec list2string f sep = function
  | [] -> ""
  | x :: [] -> f x
  | x :: y :: l' -> f x ^ sep ^ list2string f sep (y::l')

let pp_cls = function
  | PureClause([], [], _) -> "empty_clause"
  | PureClause([], pos, _) ->
      list2string pp_atm "," pos
  | PureClause(neg, [], _) ->
      list2string pp_atm "," neg ^ "==>empty"
  | PureClause(neg, pos, _) ->
      list2string pp_atm "," neg ^ "==>" ^
      list2string pp_atm "," pos
  | PosSpaceClause([], [], space) ->
      list2string pp_space_atm "*" space
  | PosSpaceClause([], pos, []) ->
      list2string pp_atm "," pos
  | PosSpaceClause([], pos, space) ->
      list2string pp_atm "," pos ^ "," ^ list2string pp_space_atm "*" space
  | PosSpaceClause(neg, [], space) ->
      list2string pp_atm "," neg ^ "==>" ^ list2string pp_space_atm "*" space
  | PosSpaceClause(neg, pos, space) ->
      list2string pp_atm "," neg ^ "==>" ^
      list2string pp_atm "," pos ^ "," ^ list2string pp_space_atm "*" space
  | NegSpaceClause([], [], pos) ->
      list2string pp_atm "," pos
  | NegSpaceClause([], space, []) ->
      list2string pp_space_atm "*" space ^ "==>empty"
  | NegSpaceClause([], space, pos) ->
      list2string pp_space_atm "*" space ^ "==>" ^
      list2string pp_atm "," pos
  | NegSpaceClause(neg, space, []) ->
      list2string pp_atm "," neg ^ "," ^ list2string pp_space_atm "*" space ^ "==>empty"
  | NegSpaceClause(neg, space, pos) ->
      list2string pp_atm "," neg ^ "," ^ list2string pp_space_atm "*" space ^ "==>" ^
      list2string pp_atm "," pos

let pp_ve = function
  | (v, e) -> string_of_int v ^ "=" ^ (pp_expr e)

let pp_mod r = list2string pp_ve "," r

let pp_ctype = function
  | CexpL -> "cexp_l"
  | CexpR -> "cexp_r"
  | CexpEf -> "cexp_ef"

(* end pretty-print *)

let print_spatial_model c r =
  if !debugging then
    (Printf.printf "== spatial model ==\n[%s]\n%s\n" (pp_mod r) (pp_cls c)) else ();
  flush_all (); c

(* print spatial model inside the prover's inner unfolding loop *)

let print_spatial_model2 c c' r =
  if !debugging then
    (Printf.printf "== spatial model (unfold loop) ==\n[%s]\n%s\n%s\n"
       (pp_mod r) (pp_cls c) (pp_cls c')) else ();
  flush_all (); c'

(* print pure clauses derived from the initial entailment *)

let print_new_pures_set s =
  if !debugging && List.length (M.elements s) > 0 then
    Printf.printf "== new pure clauses ==\n%s\n" (list2string pp_cls "\n" (M.elements s)) else ();
  flush_all (); s

(* print pure clauses derived during wellformedness inference *)

let print_wf_set s =
  if !debugging && List.length (M.elements s) > 0 then
    Printf.printf "== wellformedness clauses ==\n%s\n"
      (list2string pp_cls "\n" (M.elements s)) else ();
  flush_all (); s

(* print pure clauses derived during unfolding inference *)

let print_unfold_set s =
  if !debugging && List.length (M.elements s) > 0 then
    Printf.printf "== unfolding clauses ==\n%s\n"
      (list2string pp_cls "\n" (M.elements s)) else ();
  flush_all (); s

(* print pure clauses derived during pure reasoning *)

let print_inferred_list l =
  if !debugging && List.length l > 0 then
    Printf.printf "== inferred clauses ==\n%s\n" (list2string pp_cls "\n" l) else (); flush_all (); l

(* print pure clauses passed to superpose *)

let print_pures_list l =
  if !debugging && List.length l > 0 then
    Printf.printf "== initial pure clauses ==\n%s\n" (list2string pp_cls "\n" l) else (); flush_all (); l

let print_eqs_list l =
  if !debugging && List.length l > 0 then
    Printf.printf "== eqs ==\n%s\n" (list2string pp_cls "\n" l) else (); flush_all (); l

let print_ce_clause r c ct =
  if !debugging then
    (Printf.printf "== candidate model & c_example ==\n[%s]; %s; %s\n"
       (pp_mod r) (pp_cls c) (pp_ctype ct)) else ();
  flush_all (); ((r, c), ct)
