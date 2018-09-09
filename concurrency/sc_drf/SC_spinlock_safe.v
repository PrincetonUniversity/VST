(** * Trace erasure preserves spinlock clean and well-synchronized*)
Require Import compcert.lib.Axioms.


Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.sc_drf.SC_erasure.
Require Import VST.concurrency.sc_drf.spinlocks.
Require Import VST.concurrency.sc_drf.executions.
Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module SpinLocksSC.

  Import CoreErasure.
  Import Executions SpinLocks SCErasure TraceErasure.
  Import event_semantics.
  Import Events.

    Open Scope nat.
    
    Lemma event_erasure_action:
      forall ev ev',
        event_erasure ev ev' ->
        action ev = action ev'.
    Proof.
      intros.
      inversion H; subst.
      inv H0; reflexivity.
      inv H. simpl.
      destruct ev0; reflexivity.
    Qed.

  Lemma memval_erasure_list_length:
    forall mval mval',
      ValErasure.memval_erasure_list mval mval' ->
      length mval = length mval'.
  Proof.
    intros. induction H;
              simpl; now eauto.
  Qed.

  Lemma event_erasure_location:
    forall ev ev',
      event_erasure ev ev' ->
      location ev = location ev'.
  Proof.
    intros. unfold location.
    inversion H; subst.
    inv H0; try (erewrite memval_erasure_list_length; eauto);
      reflexivity.
    inv H.
    destruct ev0; reflexivity.
  Qed.

  Lemma event_erasure_sameLocation:
    forall ev1 ev1' ev2 ev2',
      event_erasure ev1 ev1' ->
      event_erasure ev2 ev2' ->
      sameLocation ev1' ev2' ->
      sameLocation ev1 ev2.
  Proof.
    intros.
    unfold sameLocation in *.
    erewrite event_erasure_location by eauto.
    erewrite event_erasure_location with (ev := ev2) by eauto.
    now assumption.
  Qed.

  Lemma trace_erasure_nth:
    forall tr tr' i ev'
      (Herased: trace_erasure tr tr')
      (Hi: nth_error tr' i = Some ev'),
    exists ev, nth_error tr i = Some ev /\
          event_erasure ev ev'.
  Proof.
    intros.
    generalize dependent i.
    induction Herased; intros.
    - rewrite nth_error_nil in Hi. discriminate.
    - destruct i.
      + simpl in Hi. inv Hi.
        eexists; split; simpl; eauto.
      + simpl in Hi.
        eauto.
  Qed.

  Lemma trace_erasure_nth':
    forall tr tr' i ev
      (Herased: trace_erasure tr tr')
      (Hi: nth_error tr i = Some ev),
    exists ev', nth_error tr' i = Some ev' /\
           event_erasure ev ev'.
  Proof.
    intros.
    generalize dependent i.
    induction Herased; intros.
    - rewrite nth_error_nil in Hi. discriminate.
    - destruct i.
      + simpl in Hi. inv Hi.
        eexists; split; simpl; eauto.
      + simpl in Hi.
        eauto.
  Qed.

  Lemma trace_erasure_spinlock_clean:
    forall tr tr'
      (Herased: trace_erasure tr tr')
      (Hclean: spinlock_clean tr),
      spinlock_clean tr'.
  Proof.
    intros.
    intros i j evi' evj' Hij Hi' Hj' Hevi' H HsameLoc.
    eapply trace_erasure_nth in Hi'; eauto.
    eapply trace_erasure_nth in Hj'; eauto.
    destruct Hi' as [evi [Hi Herased_i]].
    destruct Hj' as [evj [Hj Herased_j]].
    pose proof (event_erasure_action Herased_i) as Hevi.
    rewrite Hevi' in Hevi.
    specialize (Hclean i j evi evj Hij Hi Hj Hevi).
    eapply event_erasure_sameLocation in HsameLoc; eauto.
    assert (H': (forall (u : nat) (evu : machine_event), i < u < j -> nth_error tr u = Some evu -> action evu <> Freelock \/ location evu <> location evi)).
    { intros u evu Horder Hu.
      eapply trace_erasure_nth' in Hu; eauto.
      destruct Hu as [evu' [Hu' Herased_u]].
      specialize (H _ _ Horder Hu').
      destruct H as [Hactionu' | Hlocu'].
      - left.
        intros Hactionu.
        pose proof (event_erasure_action Herased_u) as Hequ.
        rewrite Hequ in Hactionu.
        now auto.
      - right.
        intros Hloc.
        pose proof (event_erasure_location Herased_u) as Hequ.
        pose proof (event_erasure_location Herased_i) as Heqi.
        rewrite Hequ Heqi in Hloc.
        now auto.
    }
    pose proof (event_erasure_action Herased_j) as Heqj.
    rewrite <- Heqj.
    now auto.
  Qed.

  Lemma event_erasure_caction:
    forall ev ev',
      event_erasure ev ev' ->
      caction ev' -> caction ev.
  Proof.
    intros.
    destruct ev'; simpl in *;
      [destruct m | destruct s]; inv H; simpl;
        try inv H3; auto;
          destruct ev0; auto; simpl in *; discriminate.
  Qed.

  Lemma event_erasure_is_internal:
    forall ev ev',
      event_erasure ev ev' ->
      is_internal ev = is_internal ev'.
  Proof.
    intros.
    inversion H; reflexivity.
  Qed.

  Lemma event_erasure_is_external:
    forall ev ev',
      event_erasure ev ev' ->
      is_external ev = is_external ev'.
  Proof.
    intros.
    inversion H; reflexivity.
  Qed.

  Lemma event_erasure_thread_id:
    forall ev ev',
      event_erasure ev ev' ->
      thread_id ev = thread_id ev'.
  Proof.
    intros; inv H; reflexivity.
  Qed.

  Lemma event_erasure_competes:
    forall ev1 ev2 ev1' ev2'
      (Herasure1: event_erasure ev1 ev1')
      (Herasure2: event_erasure ev2 ev2'),
      competes ev1' ev2' ->
      competes ev1 ev2.
  Proof.
    intros.
    destruct H as (? & ? & ? & ? & ?).
    eapply event_erasure_sameLocation in H0; eauto.
    eapply event_erasure_caction in H1;
      eapply event_erasure_caction in H2; eauto.
    erewrite <- event_erasure_thread_id in H by eauto.
    erewrite <- event_erasure_thread_id with (ev' := ev2') in H by eauto.
    erewrite <- event_erasure_is_internal in H3 by eauto.
    erewrite <- event_erasure_is_internal with (ev' := ev2') in H3 by eauto.
    erewrite <- event_erasure_is_external in H3 by eauto.
    erewrite <- event_erasure_is_external with (ev' := ev2') in H3 by eauto.
    pose proof (event_erasure_action Herasure1) as Heq1.
    pose proof (event_erasure_action Herasure2) as Heq2.
    rewrite <- Heq1 in H3.
    rewrite <- Heq2 in H3.
    destruct H3.
    repeat split; auto.
  Qed.

  Lemma trace_erasure_spinlock_synchronized:
    forall tr tr'
      (Herased: trace_erasure tr tr')
      (Hsync: spinlock_synchronized tr),
      spinlock_synchronized tr'.
  Proof.
    intros.
    intros i j evi' evj' Hij Hi' Hj' Hcompetes'.
    eapply trace_erasure_nth in Hi'; eauto.
    eapply trace_erasure_nth in Hj'; eauto.
    destruct Hi' as [evi [Hi Herased_i]].
    destruct Hj' as [evj [Hj Herased_j]].
    pose proof (event_erasure_competes Herased_i Herased_j Hcompetes') as Hcompetes.
    destruct (Hsync _ _ _ _ Hij Hi Hj Hcompetes) as [[u [v [eu [ev [? [? [Hu [Hv [Hevu [Hevv Hloc]]]]]]]]]] |
                                                     [u [eu [? [Hu Hevu]]]]].
    - eapply trace_erasure_nth' in Hu; eauto.
      eapply trace_erasure_nth' in Hv; eauto.
      destruct Hu as [evu' [Hu' Herased_u]].
      destruct Hv as [evv' [Hv' Herased_v]].
      pose proof (event_erasure_action Herased_u) as Hequ.
      pose proof (event_erasure_action Herased_v) as Heqv.
      rewrite Hevu in Hequ.
      rewrite Hevv in Heqv.
      pose proof (event_erasure_location Herased_u) as Hlocu.
      pose proof (event_erasure_location Herased_v) as Hlocv.
      rewrite Hlocv Hlocu in Hloc.
      left.
      exists u, v, evu', evv'.
      repeat split; auto.
    - eapply trace_erasure_nth' in Hu; eauto.
      destruct Hu as [evu' [Hu' Herased_u]].
      pose proof (event_erasure_action Herased_u) as Hequ.
      rewrite Hevu in Hequ.
      right.
      do 2 eexists;
        repeat split; eauto.
  Qed.

End SpinLocksSC.
