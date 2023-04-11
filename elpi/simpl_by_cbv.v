(** * Define tactics which do a cbv reduction restricted to a tailored delta list and optionally to certain parts of a term *)

Require Import elpi.elpi.
(* This file contains symbol lists for delta reductions tailored for specific applications *)
Require Export VST.elpi.cbv_symbol_lists_generated.

(* This defines Evar Etempvar *)
Require Import compcert.cfrontend.Clight.

(** Elpi database with common definitions for advanced CBV style computation functions *)

Elpi Db restricted_cbv.db lp:{{
  %%% Simple utility predicates

  % Convert a constant to a reduction flag
  pred constant->redflag i:constant, o:coq.redflag.
  constant->redflag C (coq.redflags.const C).

  %%% VST specifi tactic: find local symbols - more specifically arguments to Evar or Etempvar - in a term
  %%% vst-extract-local-symbols input-term input-symbol-list extended-output-symbol-list

  pred vst-extract-local-symbols i:term, i:list constant, o:list constant.
  % type prod name -> term -> (term -> term) -> term.         % forall x : t,
  vst-extract-local-symbols (prod N S B) I O :- pi x\ decl x N S => vst-extract-local-symbols (B x) I O.
  % type let  name -> term -> term -> (term -> term) -> term. % let x : T := v in
  vst-extract-local-symbols (let N S _V B) I O :- pi x\ decl x N S => vst-extract-local-symbols (B x) I O.
  % type app   list term -> term.                   % app [hd|args]
  vst-extract-local-symbols {{Evar lp:{{global (const VN)}} lp:{{_VT}} }} I [VN|I].
  vst-extract-local-symbols {{Etempvar lp:{{global (const VN)}} lp:{{_VT}} }} I [VN|I].
  vst-extract-local-symbols (app L) I O :- std.fold L I vst-extract-local-symbols O.
  % Everything else we don't recurse into
  vst-extract-local-symbols _T I I.

  %%% VST specifi tactic: extend reduction flags by local symbol found in term,
  %%% vst-extend-reduction-by-local-symbols input-reduction input-term extended-reduction
  pred vst-extend-reduction-by-local-symbols i: coq.redflags, i:term, o:coq.redflags.
  vst-extend-reduction-by-local-symbols RF T RFX :-
    vst-extract-local-symbols T [] LLS,
    std.map LLS constant->redflag LLR,
    coq.redflags.add RF LLR RFX.

  %%% CBV under applications of a given term
  %%% cbv-under-application-of head-term reduction-flag-generation-function input-term output-term
  %%% Note: the reduction flags used in general depend on the term. E.g. one might want to search for additional local symbols in the term.

  pred cbv-under-application-of i:term, i:(term -> coq.redflags -> prop), i:term, o:term.
  % forall X : T, B
  cbv-under-application-of HT FRF (prod X T BI) (prod X T BO) :- pi x\ decl x X T => cbv-under-application-of HT FRF (BI x) (BO x).
  % let x : T := v in B
  cbv-under-application-of HT FRF (let X T V BI) (let X T V BO) :- pi x\ def x X T V => cbv-under-application-of HT FRF (BI x) (BO x).
  % application of HT
  cbv-under-application-of HT FRF ((app [ HT | _ ]) as TI) TO :-
    !,
    FRF TI RFX,
    @redflags! RFX => coq.reduction.cbv.norm TI TO.
  % any other application
  cbv-under-application-of HT FRF (app LI) (app LO) :- std.map LI (cbv-under-application-of HT FRF) LO.
  % Everything else we just copy
  cbv-under-application-of _ _ T T.

}}.

(** Tactic for cbv reduction of the goal with
    - nr: named reduction from the reduction database (=delta symbol list) 
    Usage: cbv_nr <reduction id>
    *)
Elpi Tactic cbv_nr.
Elpi Accumulate Db cbv_symbol_generated.db.
Elpi Accumulate Db restricted_cbv.db.
Elpi Accumulate lp:{{
  solve (goal _ _ GoalType _ [str ReductionId] as Goal) GoalReduced :-
    cbv-reduction ReductionId RF,
    @redflags! RF => coq.reduction.cbv.norm GoalType GoalTypeReduced,
    refine {{ _ : lp:{{GoalTypeReduced}} }} Goal GoalReduced % to leave a vmcast one needs to call ltac1
  .
}}.
Elpi Typecheck.
        
(** Tactic for cbv reduction of the goal with
    - nr: named reduction from the reduction database (=delta symbol list) 
    - vstl: extend the delta reduction list with VST local symbols
    Usage: cbv_nr_vstl <reduction id>
    *)
Elpi Tactic cbv_nr_vstl.
Elpi Accumulate Db cbv_symbol_generated.db.
Elpi Accumulate Db restricted_cbv.db.
Elpi Accumulate lp:{{
  solve (goal _ _ GoalType _ [str ReductionId] as Goal) GoalReduced :-
    cbv-reduction ReductionId RF,
    vst-extend-reduction-by-local-symbols RF GoalType RFX,
    @redflags! RFX => coq.reduction.cbv.norm GoalType GoalTypeReduced,
    refine {{ _ : lp:{{GoalTypeReduced}} }} Goal GoalReduced % to leave a vmcast one needs to call ltac1
  .
}}.
Elpi Typecheck.
    
(** Tactic for cbv reduction of the goal with
    - nr: named reduction from the reduction database (=delta symbol list) 
    - uao: reduction only under applications of the given head symbol
    - vstl: extend the delta reduction list with VST local symbols
    Usage: cbv_nr_uao_vstl <reduction id> <head symbol>
    *)
Elpi Tactic cbv_nr_uao_vstl.
Elpi Accumulate Db cbv_symbol_generated.db.
Elpi Accumulate Db restricted_cbv.db.
Elpi Accumulate lp:{{
  solve (goal _ _ GoalType _ [str ReductionId, trm HeadTerm] as Goal) GoalReduced :-
    cbv-reduction ReductionId RF,
    cbv-under-application-of HeadTerm (vst-extend-reduction-by-local-symbols RF) GoalType GoalTypeReduced,
    refine {{ _ : lp:{{GoalTypeReduced}} }} Goal GoalReduced % to leave a vmcast one needs to call ltac1
  .
}}.
Elpi Typecheck.

(** Ltac wrappers for the elpi tactics  for specific cases *)

(* Ltac simpl_msubst_denote_tc_assert := simpl VST.floyd.local2ptree_typecheck.msubst_denote_tc_assert. *)
Ltac simpl_msubst_denote_tc_assert := elpi cbv_nr_uao_vstl "msubst_denote_tc_assert" (@VST.floyd.local2ptree_typecheck.msubst_denote_tc_assert).
