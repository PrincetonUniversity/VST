(* sepcomp imports *)

Require Import sepcomp. Import SepComp. 
Require Import arguments.

Require Import pos.
Require Import compcert_linking.
Require Import rc_semantics.

(* ssreflect *)

Require Import ssreflect ssrbool ssrfun seq eqtype fintype.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import nucular_semantics.
Require Import Values.   

(** * Forward Simulation is Compatible with Linking *)

(** This file states one of the primary linking results, essentially, 
    that simulation compatible with \mathcal{L}. *)

(** Informally, 
- Assume a multi-module program with N translation units:
        [M_0, M_1, ..., M_{N-1}], and 
- For each module [M_i], we have an induced 
    source effect semantics [Source_i]
        operating on source states [C_i] of source language [S_i] and 
    target effect semantics [Target_i] 
        operating on target states [D_i] of target language [T_i]
    (note that it's not required that [S_i = S_j] for [i<>j].)
- Assume we also have, for each [0 <= i < N], a simulation relation
       from [S_i] to [T_i]. *)

(** Then we can construct a simulation relation [Sim] between the source semantics 
- [Source_0 >< Source_1 >< ... >< Source_{N-1}] and target semantics 
- [Target_0 >< Target_1 >< ... >< Target_{N-1}] *)

(** where [><] denotes the semantic linking operation defined in 
  [linking/compcert_linking.v]. *)

(** For an explanation of [nucular_T] (a technical condition that happens to be
satisfied by all CompCert x86 Asm programs), see
[linking/CompositionalComplements.v] or footnote 5 on pg. 9 of the paper. *)

Import Wholeprog_sim.
Import SM_simulation.
Import Linker. 
Import Modsem.

Module Type LINKING_SIMULATION.

Axiom link : forall 
  (N : pos)
  (sems_S sems_T : 'I_N -> Modsem.t)
  (find_symbol_ST : 
     forall (i : 'I_N) id bf, 
     Genv.find_symbol (ge (sems_S i)) id = Some bf -> 
     Genv.find_symbol (ge (sems_T i)) id = Some bf)
  (rclosed_S : forall ix : 'I_N, RCSem.t (sems_S ix).(sem) (sems_S ix).(ge))
  (nucular_T : forall ix : 'I_N, Nuke_sem.t (sems_T ix).(sem))
  (plt : ident -> option 'I_N)
  (sims : forall ix : 'I_N, 
    let s := sems_S ix in
    let t := sems_T ix in
    SM_simulation_inject s.(sem) t.(sem) s.(ge) t.(ge))
  (ge_top : ge_ty)
  (domeq_S : forall ix : 'I_N, genvs_domain_eq ge_top (sems_S ix).(ge))
  (domeq_T : forall ix : 'I_N, genvs_domain_eq ge_top (sems_T ix).(ge))

  (*Four new assumptions*)
  (symbols_up_S: forall ix id b,
     Genv.find_symbol (ge (sems_S ix)) id = Some b ->
     Genv.find_symbol ge_top id = Some b) 
  (symbols_up_T: forall ix id b,
     Genv.find_symbol  (ge (sems_T ix)) id = Some b ->
     Genv.find_symbol ge_top id = Some b)
  (gvarinfos_S: forall ix b, gvars_included (Genv.find_var_info (ge (sems_S ix)) b)
                             (Genv.find_var_info ge_top b))
  (gvarinfos_T: forall ix b, gvars_included (Genv.find_var_info (ge (sems_T ix)) b)
                             (Genv.find_var_info ge_top b)),
  let linker_S := effsem N sems_S plt in
  let linker_T := effsem N sems_T plt in forall
  (main : val), 
  CompCert_wholeprog_sim linker_S linker_T ge_top ge_top main.

End LINKING_SIMULATION.

  
  


