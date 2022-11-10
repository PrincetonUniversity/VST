(** * Define tactics which do a cbv reduction restricted to a tailored delta list and optionally to certain parts of a term *)

Require Import Ltac2.Ltac2.
Require Import Ltac2.Bool.
Require Import Ltac2.Printf.
(* This file contains symbol lists for delta reductions tailored for specific applications *)
Require Export VST.ltac2.cbv_symbol_lists_generated.
(* Ltac helper files *)
Require Export VST.ltac2.list_ex.
Require Export VST.ltac2.constr_ex.
Require Export VST.ltac2.control_ex.
Require Export VST.ltac2.message_ex.
Require Export VST.ltac2.print_ex.
(* Definition of EVar ... *)
Require compcert.cfrontend.Clight.
Require VST.veric.expr.

(** ** Ltac2 utilities *)

(** Get first and second of a pair *)

Ltac2 pair_first (x : 'a*'b) : 'a := let (a,b):=x in a.
Ltac2 pair_second (x : 'a*'b) : 'b := let (a,b):=x in b.

(** ** Functions to construct Std.red_flags records for specific purposes *)

Ltac2 redflags_full () :=
{
  (* beta: expand the application of an unfolded functions by substitution *)
  Std.rBeta := true;
  (* delta: true = expand all but rConst; false = expand only rConst *)
  Std.rDelta := true;
  (* Note: iota in tactics like cbv is a shorthand for match, fix and cofix *)
  (* iota-match: simplify matches by choosing a pattern *)
  Std.rMatch := true;
  (* iota-fix: simplify fixpoint expressions by expanding one level *)
  Std.rFix := true;
  (* iota-cofix: simplify cofixpoint expressions by expanding one level *)
  Std.rCofix := true;
  (* zeta: expand let expressions by substitution *)
  Std.rZeta := true;
  (* Symbols to expand or not to expand (depending on rDelta) *)
  Std.rConst := []
}.

Ltac2 redflags_delta_only (delta_symbols : Std.reference list) :=
{
  (* beta: expand the application of an unfolded functions by substitution *)
  Std.rBeta := true;
  (* delta: true = expand all but rConst; false = expand only rConst *)
  Std.rDelta := false;
  (* Note: iota in tactics like cbv is a shorthand for match, fix and cofix *)
  (* iota-match: simplify matches by choosing a pattern *)
  Std.rMatch := true;
  (* iota-fix: simplify fixpoint expressions by expanding one level *)
  Std.rFix := true;
  (* iota-cofix: simplify cofixpoint expressions by expanding one level *)
  Std.rCofix := true;
  (* zeta: expand let expressions by substitution *)
  Std.rZeta := true;
  (* Symbols to expand or not to expand (depending on rDelta) *)
  Std.rConst := delta_symbols
}.

(** ** Functions to CBV compute only under applications of a given head symbol *)

(** ** CBV under application of the given head term with limited recursion:
 - arguments and function terms in applications
 - bound terms of products and lambdas
 - bound terms and values of let in bindings
 - values of cast expressions
 - values or primitive projections
 - match expressions and match case functions in matches, but no match return types
fixpoints, types and native arrays are copied unchanged.
The function returns a pair with a bool, which indicates if the match term was found and cbv was called on a part of the term.
There is an extended recusion variant of the function below.
*)

Ltac2 rec eval_cbv_uao_lr (head : constr) (frf : constr -> Std.red_flags) (term : constr) : constr * bool :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App func args =>
      if Constr.equal head func
      then
        (Std.eval_cbv (frf term) term, true)
      else
        let (func_r, func_m) := eval_cbv_uao_lr head frf func in
        let args_e := Array.map (eval_cbv_uao_lr head frf) args in
        if func_m || (Array.exist pair_second args_e)
        then (Constr.Unsafe.make (Constr.Unsafe.App func_r (Array.map pair_first args_e)), true)
        else (term, false)

  | Constr.Unsafe.Prod binder bound =>
      let (bound_r, bound_m) := eval_cbv_uao_lr head frf bound in
      if bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.Prod binder bound_r), true)
      else (term, false)

  | Constr.Unsafe.Lambda binder bound =>
      let (bound_r, bound_m) := eval_cbv_uao_lr head frf bound in
      if bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.Lambda binder bound_r), true)
      else (term, false)

  | Constr.Unsafe.LetIn binder value bound =>
      let (value_r, value_m) := eval_cbv_uao_lr head frf value in
      let (bound_r, bound_m) := eval_cbv_uao_lr head frf bound in
      if value_m || bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.LetIn binder value_r bound_r), true)
      else (term, false)

  | Constr.Unsafe.Cast value cast type =>
      let (value_r, value_m) := eval_cbv_uao_lr head frf value in
      if value_m
      then (Constr.Unsafe.make (Constr.Unsafe.Cast value_r cast type), true)
      else (term, false)

  | Constr.Unsafe.Proj projection value =>
      let (value_r, value_m) := eval_cbv_uao_lr head frf value in
      if value_m
      then  (Constr.Unsafe.make (Constr.Unsafe.Proj projection value_r), true)
      else (term, false)

  | Constr.Unsafe.Case case_a constr_return case_b constr_match case_funcs =>
      let (match_r, match_m) := eval_cbv_uao_lr head frf constr_match in
      let case_funcs_e := Array.map (eval_cbv_uao_lr head frf) case_funcs in
      if match_m || (Array.exist pair_second case_funcs_e)
      then (Constr.Unsafe.make (Constr.Unsafe.Case case_a constr_return case_b match_r (Array.map pair_first case_funcs_e)), true)
      else (term, false)

  | _ => (term, false)
  end.

(** ** CBV under application of the given head term with almsot full recusion.
    The search does not recurse into types in binders, because with Coq 8.16 Ltac2 one cannot safely reconstruct the term (fixed in 8.17)
*)

Ltac2 rec eval_cbv_uao_afr (head : constr) (frf : constr -> Std.red_flags) (term : constr) : constr * bool :=
  match Constr.Unsafe.kind term with
  | Constr.Unsafe.App func args =>
      if Constr.equal head func
      then
        (Std.eval_cbv (frf term) term, true)
      else
        let (func_r, func_m) := eval_cbv_uao_afr head frf func in
        let args_e := Array.map (eval_cbv_uao_afr head frf) args in
        if func_m || (Array.exist pair_second args_e)
        then (Constr.Unsafe.make (Constr.Unsafe.App func_r (Array.map pair_first args_e)), true)
        else (term, false)

  | Constr.Unsafe.Prod binder bound =>
      let (bound_r, bound_m) := eval_cbv_uao_afr head frf bound in
      if bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.Prod binder bound_r), true)
      else (term, false)

  | Constr.Unsafe.Lambda binder bound =>
      let (bound_r, bound_m) := eval_cbv_uao_afr head frf bound in
      if bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.Lambda binder bound_r), true)
      else (term, false)

  | Constr.Unsafe.LetIn binder value bound =>
      let (value_r, value_m) := eval_cbv_uao_afr head frf value in
      let (bound_r, bound_m) := eval_cbv_uao_afr head frf bound in
      if value_m || bound_m
      then (Constr.Unsafe.make (Constr.Unsafe.LetIn binder value_r bound_r), true)
      else (term, false)

  | Constr.Unsafe.Cast value cast type =>
      let (value_r, value_m) := eval_cbv_uao_afr head frf value in
      let (type_r, type_m) := eval_cbv_uao_afr head frf type in
      if value_m || type_m
      then (Constr.Unsafe.make (Constr.Unsafe.Cast value_r cast type_r), true)
      else (term, false)

  | Constr.Unsafe.Proj projection value =>
      let (value_r, value_m) := eval_cbv_uao_afr head frf value in
      if value_m
      then  (Constr.Unsafe.make (Constr.Unsafe.Proj projection value_r), true)
      else (term, false)

  | Constr.Unsafe.Case case_a constr_return case_b constr_match case_funcs =>
      let (return_r, return_m) := eval_cbv_uao_afr head frf constr_return in
      let (match_r, match_m) := eval_cbv_uao_afr head frf constr_match in
      let case_funcs_e := Array.map (eval_cbv_uao_afr head frf) case_funcs in
      if return_m || match_m || (Array.exist pair_second case_funcs_e)
      then (Constr.Unsafe.make (Constr.Unsafe.Case case_a return_r case_b match_r (Array.map pair_first case_funcs_e)), true)
      else (term, false)

  | Constr.Unsafe.Fix int_arr int binder_arr constr_arr =>
      let constr_arr_e := Array.map (eval_cbv_uao_afr head frf) constr_arr in
      if (Array.exist pair_second constr_arr_e)
      then (Constr.Unsafe.make (Constr.Unsafe.Fix int_arr int binder_arr (Array.map pair_first constr_arr_e)), true)
      else (term, false)

  | Constr.Unsafe.CoFix int binder_arr constr_arr =>
      let constr_arr_e := Array.map (eval_cbv_uao_afr head frf) constr_arr in
      if (Array.exist pair_second constr_arr_e)
      then (Constr.Unsafe.make (Constr.Unsafe.CoFix int binder_arr (Array.map pair_first constr_arr_e)), true)
      else (term, false)

  | Constr.Unsafe.Array instance constr_arr constr_a constr_b =>
      let (constr_a_r, constr_a_m) := eval_cbv_uao_afr head frf constr_a in
      let (constr_b_r, constr_b_m) := eval_cbv_uao_afr head frf constr_b in
      let constr_arr_e := Array.map (eval_cbv_uao_afr head frf) constr_arr in
      if constr_a_m || constr_b_m || (Array.exist pair_second constr_arr_e)
      then (Constr.Unsafe.make (Constr.Unsafe.Array instance (Array.map pair_first constr_arr_e) constr_a_r constr_b_r), true)
      else (term, false)

  | _ => (term, false)
  end.

(** ** Functions to collect local symbol definitions in VST *)

Ltac2 reference_of_constr(ref : constr) : Std.reference :=
  match Constr.Unsafe.kind ref with
  | Constr.Unsafe.Var ident 
    => Std.VarRef ident
  | Constr.Unsafe.Constant constant instance 
    => Std.ConstRef constant
  | Constr.Unsafe.Ind inductive instance 
    => Std.IndRef inductive
  | Constr.Unsafe.Constructor constructor instance 
    => Std.ConstructRef constructor
  | _ => throw_invalid_argument "reference_of_constr: not a reference: %t" ref
  end.

Ltac2 vst_collect_local_ident_one (c : constr) (l : constr list) : constr list :=
match! c with
| compcert.cfrontend.Clight.Evar ?a ?b => constr_bag_add l a
| compcert.cfrontend.Clight.Etempvar ?a ?b => constr_bag_add l a
| VST.veric.expr.tc_initialized ?a ?b => constr_bag_add l a
| _ => l
end.

Ltac2 vst_collect_local_idents (c : constr) : constr list := fold_right_app vst_collect_local_ident_one c [].

Ltac2 vst_extend_delta_symbols (ds : Std.reference list) (c : constr) : Std.reference list :=
  let cl := vst_collect_local_idents c in
  let rl := List.map reference_of_constr cl in
  (* printf "vst_extend_delta_symbols: %a" (fun _ => list_to_message reference_to_message) rl; *)
  List.append rl ds.

(** ** Reduction tactics *)

(** Tactic for cbv reduction of the goal with
    - uao_lr: reduction only under applications of the given head symbol - with limited recursion into the term
    Usage: cbv_uao_lr_tac '@<head symbol>
    *)

Ltac2 cbv_uao_lr (head : constr) : unit :=
    let goal := Control.goal() in
    let (goal_r, goal_m) := eval_cbv_uao_lr head (fun _ => redflags_full ()) goal in
    change $goal_r.
  
(** Tactic for cbv reduction of the goal with
    - uao_afr: reduction only under applications of the given head symbol - with almost full recursion into the term
    Usage: cbv_uao_fr '@<head symbol>
    *)

Ltac2 cbv_uao_afr (head : constr) : unit :=
    let goal := Control.goal() in
    let (goal_r, goal_m) := eval_cbv_uao_afr head (fun _ => redflags_full ()) goal in
    change $goal_r.
  
(** Tactic for cbv reduction of the goal with
    - ds: delta expansion symbol list
    Usage: cbv_ds < delta symbol definition>
    *)

Ltac2 cbv_ds (delta_symbols : Std.reference list) : unit :=
    let goal := Control.goal() in
    let goal_r := Std.eval_cbv (redflags_delta_only delta_symbols) goal in
    change $goal_r.

(** Tactic for cbv reduction of the goal with
    - ds: delta expansion symbol list
    - uao_lr: reduction only under applications of the given head symbol - with limited recursion into the term
    - vstl: extend the delta reduction list with VST local symbols
    Usage: cbv_ds_uao_lr_vstl < delta symbol definition> '@<head symbol>
    *)

Ltac2 cbv_ds_uao_lr_vstl (delta_symbols : Std.reference list) (head : constr) : unit :=
    let goal := Control.goal() in
    (* printf "cbv_ds_uao_lr_vstl"; print_context (); *)
    let (goal_r, goal_m) := eval_cbv_uao_lr head (fun term => redflags_delta_only (vst_extend_delta_symbols delta_symbols term)) goal in
    change $goal_r.

(** Tactic for cbv reduction of the goal with
    - ds: delta expansion symbol list
    - uao_afr: reduction only under applications of the given head symbol - with almost full recursion into the term
    - vstl: extend the delta reduction list with VST local symbols
    Usage: cbv_ds_uao_afr_vstl < delta symbol definition> '@<head symbol>
    *)

Ltac2 cbv_ds_uao_afr_vstl (delta_symbols : Std.reference list) (head : constr) : unit :=
    let goal := Control.goal() in
    (* printf "cbv_ds_uao_afr_vstl"; print_context (); *)
    let (goal_r, goal_m) := eval_cbv_uao_afr head (fun term => redflags_delta_only (vst_extend_delta_symbols delta_symbols term)) goal in
    change $goal_r.

(** ** Special tactics for VST *)

(* Ltac simpl_msubst_denote_tc_assert := simpl VST.floyd.local2ptree_typecheck.msubst_denote_tc_assert. *)
Ltac simpl_msubst_denote_tc_assert := ltac2:(cbv_ds_uao_lr_vstl (reduction_symbol_list_msubst_denote_tc_assert ()) '@VST.floyd.local2ptree_typecheck.msubst_denote_tc_assert).

(** ** Tests *)

(* Test limited rewrite *)
Goal forall x, let f := (fun x => x+2*3) in (x + (f (2*3)) + (2*3) + 2*3+4*5*6 + x = x + 144).
cbv_uao_lr 'Nat.mul.
Abort.

(* Test compute intensive reduction *)
Require Import ZArith.
Goal (2^400 / 2^396 = 16)%Z.
Time cbv_ds (reduction_symbol_list_zarith ()).
Abort.
