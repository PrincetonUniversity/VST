Require Import compcert.lib.Coqlib.
Require Import compcert.common.Values.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Maps.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.Globalenvs.
Require Import compcert.cfrontend.Ctypes.
Require Import compcert.cfrontend.Cop.
Require Import compcert.cfrontend.Clight.

Require Import VST.veric.Clight_core.

Require Import VST.concurrency.compiler.self_simulation.
Require Import VST.veric.Clight_core.

Set Bullet Behavior "Strict Subproofs".

(* NOTE: Old proof is in Clight_self_simulation_proof*)

Section ClightSelfSim.
  

  Context (ge: genv).
  Lemma clight_self_simulation:
    self_simulation _ (cl_core_sem ge).
  Admitted.

End ClightSelfSim.
  
  
