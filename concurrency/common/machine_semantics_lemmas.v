Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.

Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import VST.msl.Extensionality.

Require Import VST.sepcomp.mem_lemmas.
Require Import VST.concurrency.common.core_semantics.

Require Import VST.concurrency.common.machine_semantics.

Require Import VST.msl.Coqlib2.

Section thread_stepN.
  Context {G TID SCH TR C M E res thread_type:Type}
          (Sem:@ConcurSemantics G TID SCH TR C M res (*thread_type*)) (ge:G).

  Fixpoint thread_stepN (n:nat) : SCH -> C -> M -> C -> M -> Prop :=
    match n with
      | O => fun U c m c' m' => (c,m) = ( c',m')
      | S k => fun U c1 m1 c3 m3 => exists c2, exists m2,
        @thread_step _ _ _ _ _ _ _ (*_*) Sem ge U c1 m1 c2 m2 /\
        thread_stepN k U c2 m2 c3 m3
    end.

  Lemma thread_stepN_add : forall n m U c1 m1 c3 m3,
    thread_stepN (n+m) U c1 m1 c3 m3 <->
    exists c2, exists m2,
      thread_stepN n U c1 m1 c2 m2 /\
      thread_stepN m U c2 m2 c3 m3.
  Proof.
    induction n; simpl; intuition.
    firstorder. firstorder.
    inv H. auto.
    decompose [ex and] H. clear H.
    destruct (IHn m U x x0 c3 m3).
    apply H in H2.
    decompose [ex and] H2. clear H2.
    repeat econstructor; eauto.
    decompose [ex and] H. clear H.
    exists x1. exists x2; split; auto.
    destruct (IHn m U x1 x2 c3 m3).
    eauto.
  Qed.

  Definition thread_step_plus U c m c' m' :=
    exists n, thread_stepN (S n) U c m c' m'.

  Definition thread_step_star U c m c' m' :=
    exists n, thread_stepN n U c m c' m'.

  Lemma thread_step_plus_star : forall U c1 c2 m1 m2,
    thread_step_plus U c1 m1 c2 m2 -> thread_step_star U c1 m1 c2 m2.
  Proof. intros. destruct H as [n1 H1]. eexists. apply H1. Qed.

  Lemma thread_step_plus_trans : forall U c1 c2 c3 m1 m2 m3,
    thread_step_plus U c1 m1 c2 m2 -> thread_step_plus U c2 m2 c3 m3 ->
    thread_step_plus U c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (thread_stepN_add (S n1) (S n2) U  c1 m1 c3 m3) as [_ H].
    eexists. apply H. exists c2. exists m2. split; assumption.
  Qed.

  Lemma thread_step_star_plus_trans : forall U c1 c2 c3 m1 m2 m3,
    thread_step_star U c1 m1 c2 m2 -> thread_step_plus U c2 m2 c3 m3 ->
    thread_step_plus U c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (thread_stepN_add n1 (S n2) U  c1 m1 c3 m3) as [_ H].
    rewrite <- plus_n_Sm in H.
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma thread_step_plus_star_trans: forall U c1 c2 c3 m1 m2 m3,
    thread_step_plus U c1 m1 c2 m2 -> thread_step_star U c2 m2 c3 m3 ->
    thread_step_plus U c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (thread_stepN_add (S n1) n2 U c1 m1 c3 m3) as [_ H].
    rewrite plus_Sn_m in H.
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma thread_step_star_trans: forall U c1 c2 c3 m1 m2 m3,
    thread_step_star U c1 m1 c2 m2 -> thread_step_star U c2 m2 c3 m3 ->
    thread_step_star U c1 m1 c3 m3.
  Proof. intros. destruct H as [n1 H1]. destruct H0 as [n2 H2].
    destruct (thread_stepN_add n1 n2 U c1 m1 c3 m3) as [_ H].
    eexists. apply H.  exists c2. exists m2.  split; assumption.
  Qed.

  Lemma thread_step_plus_one: forall U c m c' m',
    thread_step  Sem ge U c m c' m' -> thread_step_plus U c m c' m'.
  Proof. intros. unfold thread_step_plus, thread_stepN. simpl.
    exists O. exists c'. exists m'. eauto.
  Qed.

  Lemma thread_step_plus_two: forall U c m c' m' c'' m'',
    thread_step  Sem ge U c m c' m' -> thread_step  Sem ge U c' m' c'' m'' ->
    thread_step_plus U c m c'' m''.
  Proof. intros.
    exists (S O). exists c'. exists m'. split; trivial.
    exists c''. exists m''. split; trivial. reflexivity.
  Qed.

  Lemma thread_step_star_zero: forall U c m, thread_step_star U c m c m.
  Proof. intros. exists O. reflexivity. Qed.

  Lemma thread_step_star_one: forall U c m c' m',
    thread_step  Sem ge U c m c' m' -> thread_step_star U c m c' m'.
  Proof. intros.
    exists (S O). exists c'. exists m'. split; trivial. reflexivity.
  Qed.

  Lemma thread_step_plus_split: forall U c m c' m',
    thread_step_plus U c m c' m' ->
    exists c'', exists m'', thread_step  Sem ge U c m c'' m'' /\
      thread_step_star U  c'' m'' c' m'.
  Proof. intros.
    destruct H as [n [c2 [m2 [Hstep Hstar]]]]. simpl in*.
    exists c2. exists m2. split. assumption. exists n. assumption.
  Qed.

End thread_stepN.
