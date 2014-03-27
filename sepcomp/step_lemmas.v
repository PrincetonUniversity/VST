Require Import AST.
Require Import Coqlib.

Require Import sepcomp.extspec.
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.forward_simulations.

Section safety.
  Context {G C M D Z:Type}.
  Context (Hcore:CoreSemantics G C M).
  Variable (Hspec:external_specification M external_function Z).

  Variable ge : G.

  Fixpoint safeN (n:nat) (z:Z) (c:C) (m:M) : Prop :=
    match n with
    | O => True
    | S n' => 
       match at_external Hcore c, halted Hcore c with
       | None, None =>
           exists c', exists m',
             corestep Hcore ge c m c' m' /\
             safeN n' z c' m'
       | Some (e,sig,args), None =>
           exists x:ext_spec_type Hspec e,
             ext_spec_pre Hspec e x (sig_args sig) args z m /\
             (forall ret m' z',
               ext_spec_post Hspec e x (sig_res sig) ret z' m' ->
               exists c',
                 after_external Hcore ret c = Some c' /\
                 safeN n' z' c' m')
       | None, Some i => ext_spec_exit Hspec (Some i) z m
       | Some _, Some _ => False
       end
    end.

  Definition corestep_fun  :=
       forall ge m q m1 q1 m2 q2 ,
       corestep Hcore ge q m q1 m1 -> 
       corestep Hcore ge q m q2 m2 -> 
       (q1, m1) = (q2, m2).

  Lemma safe_corestep_forward:
     corestep_fun -> 
    forall c m c' m' n z,
    corestep Hcore ge c m c' m' -> safeN (S n) z c m -> safeN n z c' m'.
  Proof.
    simpl; intros.
    erewrite corestep_not_at_external in H1; eauto.
    erewrite corestep_not_halted in H1; eauto.
    destruct H1 as [c'' [m'' [? ?]]].
    assert ((c',m') = (c'',m'')).
    eapply H; eauto.
   inv H3; auto.
  Qed.

  Lemma safe_corestep_backward:
    forall c m c' m' n z,
    corestep Hcore ge c m c' m' -> safeN n z c' m' -> safeN (S n) z c m.
  Proof.
    simpl; intros.
    erewrite corestep_not_at_external; eauto.
    erewrite corestep_not_halted; eauto.
  Qed.

  Lemma safe_downward1 :
    forall n c m z,
      safeN (S n) z c m -> safeN n z c m.
  Proof.
    induction n; simpl; intros; auto.
    destruct (at_external Hcore c);
      destruct (halted Hcore c).
    destruct p; auto.
    destruct p. destruct p.
    destruct H as [x ?].
    exists x. 
    destruct H. split; auto.
    intros. specialize (H0 ret m' z' H1).
    destruct H0 as [c' [? ?]].
    exists c'; split; auto.
    auto.
    destruct H as [c' [m' [? ?]]].
    exists c'. exists m'; split; auto.
  Qed.

  Lemma safe_downward : 
    forall n n' c m z,
      le n' n ->
      safeN n z c m -> safeN n' z c m.
  Proof.
    do 6 intro. revert c m z. induction H; auto.
    intros. apply IHle. apply safe_downward1. auto.
  Qed.

  Lemma safe_corestepN_forward:
    corestep_fun -> 
    forall z c m c' m' n n0,
      corestepN Hcore ge n0 c m c' m' -> 
      safeN (n + S n0) z c m -> 
      safeN n z c' m'.
  Proof.
    intros.
    revert c m c' m' n H0 H1.
    induction n0; intros; auto.
    simpl in H0; inv H0.
    eapply safe_downward in H1; eauto. omega.
    simpl in H0. destruct H0 as [c2 [m2 [STEP STEPN]]].
    apply (IHn0 _ _ _ _ n STEPN). 
    assert (Heq: (n + S (S n0) = S (n + S n0))%nat) by omega.
    rewrite Heq in H1.
    eapply safe_corestep_forward in H1; eauto.
  Qed.

  Lemma safe_step'_back2 :
    forall
      {ora st m st' m' n},
      corestep Hcore ge st m st' m' ->
      safeN (n-1) ora st' m' ->
      safeN n ora st m.
  Proof.
    intros.
    destruct n.
    hnf. auto.
    simpl in H0.
    replace (n-0)%nat with n in H0.
    eapply safe_corestep_backward; eauto.
    omega.
  Qed.

  Lemma safe_corestepN_backward:
    forall z c m c' m' n n0,
      corestepN Hcore ge n0 c m c' m' -> 
      safeN (n - n0) z c' m' -> 
      safeN n z c m.
  Proof.
    simpl; intros.
    revert c m c' m' n H H0.
    induction n0; intros; auto.
    simpl in H; inv H.
    solve[assert (Heq: (n = n - 0)%nat) by omega; rewrite Heq; auto].
    simpl in H. destruct H as [c2 [m2 [STEP STEPN]]].
    assert (H: safeN (n - 1 - n0) z c' m'). 
    eapply safe_downward in H0; eauto. omega.
    specialize (IHn0 _ _ _ _ (n - 1)%nat STEPN H). 
    solve[eapply safe_step'_back2; eauto].
  Qed.
    
  Lemma convergent_controls_safe : 
    forall m q1 q2,
      (at_external Hcore q1 = at_external Hcore q2) ->
      (forall ret q', after_external Hcore ret q1 = Some q' ->
                      after_external Hcore ret q2 = Some q') ->
      (halted Hcore q1 = halted Hcore q2) ->
      (forall q' m', corestep Hcore ge q1 m q' m' -> corestep Hcore ge q2 m q' m') ->
      (forall n z, safeN n z q1 m -> safeN n z q2 m).
  Proof.
    intros. destruct n; simpl in *; auto.
    rewrite H in H3. rewrite H1 in H3.
    destruct (at_external Hcore q2);
      destruct (halted Hcore q2); auto.
    destruct p. destruct p.
    destruct H3 as [x ?].
    exists x. 
    destruct H3; split; auto.
    intros. specialize (H4 ret m' z' H5).
    destruct H4 as [c' [? ?]].
    exists c'; split; auto.
    destruct H3 as [c' [m' [? ?]]].
    exists c'. exists m'; split; auto.
  Qed.

  Lemma wlog_safeN_gt0 : forall
    n z q m,
    (lt 0 n -> safeN n z q m) -> 
    safeN n z q m.
  Proof.
    intros. destruct n.
    hnf. auto.
    apply H. omega.
  Qed.

End safety.
