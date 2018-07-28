Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Smallstep.

Require Export VST.sepcomp.semantics.

(* Extract a CoreSemantics from a part_semantics*)
Inductive step2corestep (sem:part_semantics):(state sem) -> mem -> (state sem) -> mem -> Prop :=
  coreify: forall s1 m1 t s2,
    step sem (set_mem s1 m1) t s2 ->
    Smallstep.at_external sem (set_mem s1 m1) = None ->
    step2corestep sem s1 m1 s2 (get_mem s2).
    
Program Definition sem2coresem (sem:part_semantics) corestep_not_halted : CoreSemantics _ _:=
  {|
    initial_core := fun _ m c m' f args => start_stack sem m c f args /\ get_mem c = m'
    ; at_external := fun s m => Smallstep.at_external sem (set_mem s m) 
    ; after_external := Smallstep.after_external sem
    ; halted:= final_state sem
    ; corestep := step2corestep sem
    ; corestep_not_halted:=corestep_not_halted
|}.
Next Obligation.
  inv H; auto.
Qed.
