Require Import compcert.common.Memory.


Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import concurrency.scheduler.
Require Import concurrency.concurrent_machine.
Require Import concurrency.juicy_machine. Import Concur.
Require Import concurrency.dry_machine. Import Concur.
(*Require Import concurrency.dry_machine_lemmas. *)
Require Import concurrency.lksize.
Require Import concurrency.permissions.

(*SSReflect*)
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Require Import concurrency.ssromega. (*omega in ssrnat *)

(*The simulations*)
Require Import sepcomp.wholeprog_simulations.

(*General erasure*)
Require Import concurrency.erasure_signature.
Require Import concurrency.erasure_proof.

From mathcomp.ssreflect Require Import ssreflect seq.

Import addressFiniteMap.

Module ErasureSafety (DecayingSEM: DecayingSemantics).

  Module ErasureProof := erasure_proof.Parching DecayingSEM.
  Module Erasure := ErasureFnctr ErasureProof.
  Import ErasureProof.
  Import Erasure.

  Parameters initU: DryMachine.Sch.
  Parameter init_rmap : JuicyMachine.SIG.ThreadPool.RES.res.
  Parameter init_pmap : DSEM.perm_map.
  Parameter init_rmap_perm:  match_rmap_perm init_rmap init_pmap.

  Definition local_erasure:= erasure initU init_rmap init_pmap init_rmap_perm.
  Definition step_diagram:= ErasureProof.core_diagram.
  
  Lemma erasure_safety': forall n ge sch js ds m,
      ErasureProof.match_st js ds ->
      DSEM.invariant ds ->
    JuicyMachine.csafe ge (sch, nil, js) m n ->
    DryMachine.csafe ge (sch, nil, ds) m n.
  Proof.
    induction n.
    intros. constructor.
    intros. inversion H1.
    - (*Safe_0*) constructor.  
    - (*HaltedSafe*)
      simpl. unfold DryMachine.halted; simpl.
      unfold JuicyMachine.halted in H2; simpl in H2.
      destruct (SCH.schedPeek sch); inversion H; auto.
    - { simpl in Hstep.
        unfold JuicyMachine.MachStep in Hstep; simpl in Hstep.
        assert (step_diagram:=step_diagram).
        specialize (step_diagram m initU sch sch (Some init_rmap) (Some init_pmap)).
        specialize (step_diagram ds js tp' m').
        unfold corestep in step_diagram; simpl in step_diagram.
        unfold JuicyMachine.MachStep in step_diagram; simpl in step_diagram.
        eapply step_diagram in Hstep; try eassumption.
        destruct Hstep as [ds' [dinv' [MATCH' stp']]].
        econstructor 3; eauto. }
    - { simpl in Hstep.
        unfold JuicyMachine.MachStep in Hstep; simpl in Hstep.
        assert (step_diagram:=step_diagram).
        specialize (step_diagram m initU sch (SCH.schedSkip sch) (Some init_rmap) (Some init_pmap)).
        specialize (step_diagram ds js tp' m').
        unfold corestep in step_diagram; simpl in step_diagram.
        unfold JuicyMachine.MachStep in step_diagram; simpl in step_diagram.
        eapply step_diagram in Hstep; try eassumption.
        destruct Hstep as [ds' [dinv' [MATCH' stp']]].
        econstructor 4; eauto. }
Qed.
        

  Theorem erasure_safety: forall ge cd j js ds m n,
      Erasure.match_state cd j js m ds m ->
    JuicyMachine.csafe ge js m n ->
    DryMachine.csafe ge ds m n.
  Proof.
    intros ? ? ? ? ? ? ? MATCH jsafe.
    inversion MATCH. subst.
    eapply erasure_safety'; eauto.
  Qed.
    
End ErasureSafety. 