Require Import sepcomp.mem_lemmas.
Require Import sepcomp.effect_simulations.
Require Import sepcomp.pos.
Require Import sepcomp.linking.

Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

Require Import compcert.common.AST.    (*for ident*)
Require Import compcert.common.Values.   
Require Import compcert.common.Globalenvs.   

(** * Linking simulation proof 

This file states and proves the main linking simulation result.

*)

Require Import sepcomp.wf_lemmas.

Section linkingSimulation.

Import SM_simulation.
Import Linker.
Import Static.

Arguments core_data {F1 V1 C1 F2 V2 C2 Sem1 Sem2 ge1 ge2} _ _.
Arguments core_ord  {F1 V1 C1 F2 V2 C2 Sem1 Sem2 ge1 ge2 entry_points} _ _ _.

Variable N : pos.
Variable (cores_S cores_T : 'I_N -> Static.t). 
Variable fun_tbl : ident -> option 'I_N.
Variable entry_points : seq (val*val*signature).
Variable (sims : forall i : 'I_N, 
  let s := cores_S i in
  let t := cores_T i in
  SM_simulation_inject s.(coreSem) t.(coreSem) s.(ge) t.(ge) entry_points).
Variable my_ge : ge_ty.
Variable my_ge_S : forall (i : 'I_N), genvs_domain_eq my_ge (cores_S i).(ge).
Variable my_ge_T : forall (i : 'I_N), genvs_domain_eq my_ge (cores_T i).(ge).

Let types := fun i : 'I_N => (sims i).(core_data entry_points).
Let ords : forall i : 'I_N, types i -> types i -> Prop 
  := fun i : 'I_N => (sims i).(core_ord).

Variable wf_ords : forall i : 'I_N, well_founded (ords i).

Let linker_S := effsem N cores_S fun_tbl.
Let linker_T := effsem N cores_T fun_tbl.

Let ord := @Lex.ord N types ords.

Lemma link : SM_simulation_inject linker_S linker_T my_ge my_ge entry_points.
Proof.

eapply Build_SM_simulation_inject
  with (core_data := Lex.t types)
       (core_ord  := ord).

(* well_founded ord *)
- by apply: Lex.wf_ord.

Admitted. (*WORK-IN-PROGRESS*)

End linkingSimulation.
