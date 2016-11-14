Require Import compcert.lib.Axioms.
Require Import compcert.lib.Maps.

Require Import concurrency.sepcomp. Import SepComp.

Require Import concurrency.pos.
Require Import concurrency.scheduler.
Require Import concurrency.TheSchedule.
Require Import concurrency.konig.
Require Import concurrency.addressFiniteMap. (*The finite maps*)
Require Import concurrency.pos.
Require Import concurrency.lksize.
Require Import concurrency.permjoin_def.
Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.


Require Import Coq.ZArith.ZArith.

Require Import concurrency.permissions.
Require Import concurrency.threadPool.
 
Require Import compcert.common.Memory. (*for Mem.perm_order'' *)
Require Import concurrency.bounded_maps.


(*Semantics*)
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import sepcomp.event_semantics.
Require Import veric.Clight_sim.
Require Import concurrency.ClightSemantincsForMachines.


Lemma CLight_Deterministic: forall ge c m c1 m1 c2 m2,
    veric.Clight_new.cl_step ge c m c2 m2 ->
    veric.Clight_new.cl_step ge c m c1 m1 ->
    c1 = c2 /\ m1 = m2.
                
Admitted.

Lemma CLight_step_mem_bound: forall ge c m c' m',
    veric.Clight_new.cl_step ge c m c' m' ->
    bounded_maps.bounded_map (snd (getMaxPerm m)) ->
    bounded_maps.bounded_map (snd (getMaxPerm m')).
                
Admitted.
