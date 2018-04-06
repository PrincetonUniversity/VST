Require Import compcert.common.Memory.


Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.

(*IM using proof irrelevance!*)
Require Import ProofIrrelevance.

(* The concurrent machinery*)
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.juicy_machine. Import Concur.
Require Import VST.concurrency.HybridMachine. Import Concur.
(*Require Import VST.concurrency.HybridMachine_lemmas. *)
Require Import VST.concurrency.lksize.
Require Import VST.concurrency.permissions.

(*SSReflect*)
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat eqtype seq.
Require Import Coq.ZArith.ZArith.
Require Import PreOmega.
Require Import VST.concurrency.ssromega. (*omega in ssrnat *)

(*The simulations*)
Require Import VST.sepcomp.wholeprog_simulations.

(*General erasure*)
Require Import VST.concurrency.erasure_signature.
Require Import VST.concurrency.erasure_proof.

From mathcomp.ssreflect Require Import ssreflect seq.

Import addressFiniteMap.

Set Bullet Behavior "Strict Subproofs".

Module ErasureSafety.

  Module ErasureProof := erasure_proof.Parching.
  Module Erasure := ErasureFnctr ErasureProof.
  Import ErasureProof.
  Import Erasure.

  Parameters initU: DryMachine.Sch.
  Parameter init_rmap : JuicyMachine.SIG.ThreadPool.RES.res.
  Parameter init_pmap : DryMachine.SIG.ThreadPool.RES.res.
  Parameter init_rmap_perm:  match_rmap_perm init_rmap init_pmap.

  (*Definition local_erasure:= erasure initU init_rmap init_pmap init_rmap_perm.*)
  Definition step_diagram:= ErasureProof.core_diagram.

  Notation jm_csafe := JuicyMachineModule.THE_JUICY_MACHINE.jm_csafe.

  Lemma erasure_safety': forall n ge sch js ds m,
      ErasureProof.match_st js ds ->
      DMS.invariant ds ->
    jm_csafe ge (sch, nil, js) m n ->
    DryMachine.csafe ge (sch, nil, ds) m n.
  Proof.
    induction n.
    intros. constructor.
    intros. inversion H1.
    - constructor; simpl. unfold DryMachine.halted; simpl.
      unfold JuicyMachine.halted in H2; simpl in H2.
      change JuicyMachineModule.THE_JUICY_MACHINE.SCH.schedPeek with
      DryMachineSource.THE_DRY_MACHINE_SOURCE.SCH.schedPeek in H2.
      destruct ( DryMachineSource.THE_DRY_MACHINE_SOURCE.SCH.schedPeek sch ) eqn:AA;
      inversion H; auto.
    - { simpl in Hstep.
        unfold JuicyMachine.MachStep in Hstep; simpl in Hstep.
        assert (step_diagram:=step_diagram).
        specialize (step_diagram m initU sch sch (Some init_rmap) (Some init_pmap)).
        specialize (step_diagram ds js tp' m').
        unfold corestep in step_diagram; simpl in step_diagram.
        unfold JuicyMachine.MachStep in step_diagram; simpl in step_diagram.
        eapply step_diagram in Hstep; try eassumption.
        destruct Hstep as [ds' [dinv' [MATCH' stp']]].
        destruct Hsafe as [[? Hphi] Hsafe].
        specialize (Hsafe _ Hphi nil) as (? & ? & ? & ? & Hr & ? & Hsafe).
        { eexists; simpl.
          erewrite <- ghost_core; apply join_comm, core_unit. }
        eapply MTCH_tp_update in MATCH'; eauto.
        eapply IHn in Hsafe; eauto.
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
        econstructor 4; eauto.
        intro U''; specialize (Hsafe U'').
        destruct Hsafe as [[? Hphi] Hsafe].
        specialize (Hsafe _ Hphi nil) as (? & ? & ? & ? & Hr & ? & Hsafe).
        { eexists; simpl.
          erewrite <- ghost_core; apply join_comm, core_unit. }
        eapply MTCH_tp_update in MATCH'; eauto. }
Qed.


  Theorem erasure_safety: forall ge cd j js ds m n,
      Erasure.match_state cd j js m ds m ->
    jm_csafe ge js m n ->
    DryMachine.csafe ge ds m n.
  Proof.
    intros ? ? ? ? ? ? ? MATCH jsafe.
    inversion MATCH. subst.
    eapply erasure_safety'; eauto.
  Qed.

  (*there is something weird about this theorem.*)
  (*The injection is trivial... but it shouldn't*)
  Theorem initial_safety:
    forall (U : DryMachine.Sch) (js : jstate)
      (vals : seq Values.val) m
      (rmap0 : rmap) (pmap : access_map * access_map) main genv h,
      match_rmap_perm rmap0 pmap ->
      no_locks_perm rmap0 ->
      initial_core (JMachineSem U (Some rmap0)) h genv
         m main vals = Some ((U, [::], js), None)  ->
      exists (ds : dstate),
        initial_core (DMachineSem U (Some pmap)) h genv
                     m main vals = Some ((U, [::], ds), None) /\
        DMS.invariant ds /\ match_st js ds.
  Proof.
    intros ? ? ? ? ? ? ? ? ? mtch_perms no_locks init.
    destruct (init_diagram (fun _ => None) U js vals m rmap0 pmap main genv h)
    as [ds [dinit [dinv MTCH]]]; eauto.
    unfold init_inj_ok; intros b b' ofs H. inversion H.
  Qed.

  (** *Lets proof that again with the new kind of safety*)
  Axiom assume: forall js ds, match_st js ds -> forall sch, JuicyMachine.valid (sch, nil, js) <-> DryMachine.valid (sch, nil, ds).
  Lemma new_erasure_safety'': forall n ge js ds m,
      ErasureProof.match_st js ds ->
      DMS.invariant ds ->
      (forall sch, JuicyMachine.valid (sch, nil, js) -> JuicyMachine.ksafe_new_step ge (sch, nil, js) m n) ->
      (forall sch, DryMachine.valid (sch, nil, ds) -> DryMachine.ksafe_new_step ge (sch, nil, ds) m n).
  Proof.
    induction n; [intros; constructor| ].
    move => ge js ds m MATCH INV H1 sch VAL. specialize (H1 sch).
    move: VAL (MATCH) => /assume /H1 HH /HH KSF.
    inversion KSF.
    rewrite /DryMachine.ksafe_new_step /DryMachine.mk_nstate /=.
    move: H0; rewrite /JuicyMachine.new_step /JuicyMachine.mk_ostate /= => H3.
    inversion H3.
    { (*Halted case*)
      destruct st as [[a b] c]; destruct st' as [[a' b'] c']; simpl in *.
      inversion H4; subst.
      apply: (safety.sft_step).
      - apply: DryMachine.halt_with_step=> //.
      - move => U'' nVAL.
        apply: IHn => //.
        + apply: (MATCH).
        + rewrite /JuicyMachine.ksafe_new_step /JuicyMachine.mk_nstate /=.
          move=>sch' /assume JVAL; move: (MATCH) => /JVAL DVAL.
          apply: H2.
          rewrite /JuicyMachine.new_valid /JuicyMachine.mk_ostate /=.
          move: DVAL MATCH => /assume KK /KK //.
    }
    { (* Step Case*)
      assert (step_diagram:=step_diagram).
      specialize (step_diagram m initU sch U' (Some init_rmap) (Some init_pmap)).
      specialize (step_diagram ds js).
      specialize (step_diagram (snd (fst st')) (snd st')).
      unfold JuicyMachine.MachStep in step_diagram; simpl in step_diagram.
      unfold JuicyMachineModule.THE_JUICY_MACHINE.JuicyMachine.MachStep in step_diagram; simpl in step_diagram.
      destruct st as [[a b] c]; destruct st' as [[a' b'] c']; simpl in *.
      inversion H4; subst.
      (*We need to talk about traces... until now... they are empty:*)
      assert (requirement:(a') = nil).
      { inversion H0; simpl in *; eauto. }

      rewrite requirement in H0.
      eapply step_diagram in H0 => //.
      destruct H0 as [ ds' [ Dinv' [ match' step']]].
      apply: (safety.sft_step).
        - by eapply (DryMachine.step_with_halt _ _ _ (DryMachine.mk_ostate (nil, ds', c') U')) => //.
        - (*rewrite /JuicyMachine.ksafe_new_step /JuicyMachine.mk_nstate /=.
          move=>sch' /assume /= JVAL'. move: (match') => /JVAL' JVAL.
          rewrite requirement in H2.*)
          move => U'' nVAL.
          apply: IHn => //.
          + exact match'.
          + rewrite /JuicyMachine.ksafe_new_step /JuicyMachine.mk_nstate /=.
          move=>sch' /assume JVAL; move: (match') => /JVAL DVAL.
          rewrite requirement in H2; apply: H2.
          rewrite /JuicyMachine.new_valid /JuicyMachine.mk_ostate /=.
          move: DVAL match' => /assume KK /KK //.
    }
  Qed.

  Lemma new_erasure_safety': forall n ge js ds m,
      (forall sch, JuicyMachine.valid (sch, nil, js)) ->
      ErasureProof.match_st js ds ->
      DMS.invariant ds ->
      (forall sch, JuicyMachine.ksafe_new_step ge (sch, nil, js) m n) ->
      forall sch, DryMachine.ksafe_new_step ge (sch, nil, ds) m n.
  Proof.
    move => n ge js ds m all_val MATCH dINV sch jKSF.
    apply: new_erasure_safety''=> //.
    - exact MATCH.
    - eapply assume. exact MATCH.
      apply: all_val.
  Qed.


 (* Theorem new_erasure_safety: forall ge cd j jtp dtp m n,
      (forall sch,  JuicyMachine.valid (sch, nil, jtp) ) ->
      forall sch, Erasure.match_state cd j (sch, nil, jtp) m (sch, nil, dtp) m ->
    JuicyMachine.csafe ge (sch, nil, jtp) m n ->
    DryMachine.csafe ge (sch, nil, dtp) m n.
  Proof.
    intros.
    eapply new_erasure_safety''.
    intros ? ? ? ? ? ? ? MATCH jsafe.
    inversion MATCH. subst.
    eapply erasure_safety'; eauto.
  Qed.*)


End ErasureSafety.
