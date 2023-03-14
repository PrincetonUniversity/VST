Require Export VST.veric.base.
Require Export VST.veric.res_predicates.

(* patch for compcert maps notation conflict *)
Global Notation "a ! b" := (Maps.PTree.get b a) (at level 1).

(* Module Mem : MEM := compcert.common.Memory.Mem. *)
Export Mem.
Open Scope Z.
