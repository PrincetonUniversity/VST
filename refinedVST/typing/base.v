From stdpp Require Import coPset.
From VST.lithium Require Export syntax definitions.
From compcert.cfrontend Require Export Ctypes.
From VST.sepcomp Require Export extspec.
Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.veric Require Export Clight_base expr valid_pointer Cop2 Clight_Cop2 val_lemmas res_predicates mpred seplog tycontext lifting mapsto_memory_block.
From VST.floyd Require Export functional_base base nested_field_lemmas.
From VST.veric Require Export lifting_expr.
From VST Require Export shared.dshare.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".

Class CoPsetFact (P : Prop) : Prop := copset_fact : P.
(* clear for performance reasons as there can be many hypothesis and they should not be needed for the goals which occur *)
Local Definition coPset_disjoint_empty_r := disjoint_empty_r (C:=coPset).
Local Definition coPset_disjoint_empty_l := disjoint_empty_l (C:=coPset).
Global Hint Extern 1 (CoPsetFact ?P) => (change P; clear; eauto using coPset_disjoint_empty_r, coPset_disjoint_empty_r with solve_ndisj) : typeclass_instances.
