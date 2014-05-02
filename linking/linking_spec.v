(* sepcomp imports *)

Require Import linking.sepcomp. Import SepComp. 
Require Import sepcomp.arguments.

Require Import linking.pos.
Require Import linking.core_semantics_lemmas.
Require Import linking.compcert_linking.
Require Import linking.rc_semantics.

(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import sepcomp.nucular_semantics.
Require Import compcert.common.Values.   

(* This file states the main linking simulation result.                   *)
(* Informally,                                                            *)
(*   - Assume a multi-module program with N translation units:            *)
(*                                                                        *)
(*       M_0, M_1, ..., M_{N-1}, and                                      *)
(*                                                                        *)
(*   - For each module M_i, we have an induced                            *)
(*       o Source effect semantics Source_i operating on source states    *)
(*         C_i of source language S_i                                     *)
(*       o Target effect semantics Target_i operating on target states    *)
(*         D_i of target language T_i                                     *)
(*     (Note that it's not required that S_i = S_j for i<>j.)             *)
(*                                                                        *)
(*   - Assume we also have, for each 0 <= i < N, a simulation relation    *)
(*     from S_i to T_i.                                                   *)
(*                                                                        *)
(* Then we can construct a simulation relation Sim between the source     *)
(* semantics                                                              *)
(*                                                                        *)
(*   Source_0 >< Source_1 >< ... >< Source_{N-1}                          *)
(*                                                                        *)
(* and target semantics                                                   *)
(*                                                                        *)
(*   Target_0 >< Target_1 >< ... >< Target_{N-1}                          *)
(*                                                                        *)
(* where >< denotes the semantic linking operation defined in             *)
(* compcert_linking.v.                                                    *)

Import Wholeprog_simulation.
Import SM_simulation.
Import Linker. 
Import Modsem.

Module Type LINKING_SIMULATION.

Axiom link : forall 
  (N : pos)
  (sems_S sems_T : 'I_N -> Modsem.t)
  (nucular_T : forall ix : 'I_N, Nuke_sem.t (sems_T ix).(sem))
  (plt : ident -> option 'I_N)
  (sims : forall ix : 'I_N, 
    let s := sems_S ix in
    let t := sems_T ix in
    SM_simulation_inject s.(sem) t.(sem) s.(ge) t.(ge))
  (ge_top : ge_ty)
  (domeq_S : forall ix : 'I_N, genvs_domain_eq ge_top (sems_S ix).(ge))
  (domeq_T : forall ix : 'I_N, genvs_domain_eq ge_top (sems_T ix).(ge)),
  let sems_S (ix : 'I_N) := 
    Modsem.mk (sems_S ix).(ge) (RC.effsem (sems_S ix).(sem)) in 
  let linker_S := effsem N sems_S plt in
  let linker_T := effsem N sems_T plt in forall
  (main : val), 
  Wholeprog_simulation linker_S linker_T ge_top ge_top main.

End LINKING_SIMULATION.

  
  


