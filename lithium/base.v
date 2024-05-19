From VST.lithium Require Export syntax definitions.
From VST Require Export floyd.proofauto shared.dshare.

Class CoPsetFact (P : Prop) : Prop := copset_fact : P.
(* clear for performance reasons as there can be many hypothesis and they should not be needed for the goals which occur *)
Local Definition coPset_disjoint_empty_r := disjoint_empty_r (C:=coPset).
Local Definition coPset_disjoint_empty_l := disjoint_empty_l (C:=coPset).
Global Hint Extern 1 (CoPsetFact ?P) => (change P; clear; eauto using coPset_disjoint_empty_r, coPset_disjoint_empty_r with solve_ndisj) : typeclass_instances.
