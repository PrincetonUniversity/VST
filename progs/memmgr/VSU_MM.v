Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require Import VST.veric.initial_world.

Require Import malloc.
Require Import mmap0.
Require Import ASI_malloc.
Require Import ASI_mmap0.
Require Import VSU_malloc_definitions.
Require Import VSU_malloc.
Require Import VSU_mmap0.

Definition MM_VSU := privatizeExports (ltac:(linkVSUs MM0_VSU MF_VSU)) [_mmap0; _munmap].

(*
Definition mm_Exports:funspecs := Malloc_ASI (ForgetR R_APD) _malloc _free.
Goal (VSU_Exports MM_VSU) = mm_Exports. reflexivity. Qed.
Eval simpl in (VSU_GP MM_VSU).*)

Definition MM_R_VSU:= privatizeExports (ltac:(linkVSUs MM0_VSU MF_R_VSU)) [(*_mmap0;*) _munmap(*; _try_pre_fill*)].

(*Eval simpl in VSU_Imports MM_R_VSU. (* nil*)*)
(*Eval simpl in (VSU_Exports MM_R_VSU). *) (*mmap0, pre_fill, try_pre_fill, malloc, free*)

(*Print Assumptions MM_VSU.*)
Print Assumptions MM_R_VSU.
(* body_mmap0 and body_munmap are 'Parameters' in VSU_mmap0 - maybe turn them into imported specs that remain unresolved?*)