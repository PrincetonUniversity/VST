Require Import Min.

Require Import msl.msl_standard.
Require Import Maps.
Require Import FuncListMachine.
Require Import lemmas.
Require Import hoare_total.

Open Scope pred.

Section estep.
  Variable X:Type.
  Variable x:X.

  Inductive estep : program X -> store -> list (instr X) -> store -> list (instr X) -> Prop :=

  | estep_assert : forall p r i stk (P:X),
    (*----------------------------------------------------*)
      estep p r ((instr_assert P ;; i) :: stk) r (i :: stk)

  | estep_getlabel: forall p r l v i stk,
    (*----------------------------------------------------*)
      estep p r ((instr_getlabel l v ;; i) :: stk) (r#v <- (value_label l)) (i :: stk)

  | estep_fetch_field_0: forall p r v1 v2 i a0 a1 stk,
      r#v1 = Some (value_cons a0 a1) ->
    (*----------------------------------------------------*)
      estep p r ((instr_fetch_field v1 0 v2 ;; i) :: stk) (r#v2 <- a0) (i :: stk)

  | estep_fetch_field_1: forall p r v1 v2 i a0 a1 stk,
      r#v1 = Some (value_cons a0 a1) ->
    (*----------------------------------------------------*)
      estep p r ((instr_fetch_field v1 1 v2 ;; i) :: stk) (r#v2 <- a1) (i :: stk)

  | estep_cons: forall p r v1 v2 v3 i a1 a2 stk,
      r#v1 = Some a1 ->
      r#v2 = Some a2 ->
    (*----------------------------------------------------*)
      estep p r ((instr_cons v1 v2 v3 ;; i) :: stk) (r#v3 <- (value_cons a1 a2)) (i :: stk)

  | estep_seq: forall p r i1 i2 i3 stk,
    (*----------------------------------------------------*)
      estep p r (((i1 ;; i2) ;; i3) :: stk) r ((i1 ;; i2 ;; i3) :: stk)

  | estep_if_nil1 : forall p r v i1 i2 i stk,
      r#v = Some (value_label (L 0)) ->
    (*----------------------------------------------------*)
      estep p r ((instr_if_nil v i1 i2 ;; i) :: stk) r ((i1 ;; i) :: stk)

  | estep_if_nil2 : forall p r v i1 i2 i a1 a2 stk,
      r#v = Some (value_cons a1 a2) ->
    (*----------------------------------------------------*)
      estep p r ((instr_if_nil v i1 i2 ;; i) :: stk) r ((i2 ;; i) :: stk)

  | estep_call : forall p r v l i i' stk,
      r#v = Some (value_label l) ->
      p#l = Some i' ->
    (*----------------------------------------------------*)
      estep p r ((instr_call v ;; i) :: stk) r ((i' ;; instr_assert x) :: i :: stk)

  | estep_return : forall p r stk i,
    (*----------------------------------------------------*)
      estep p r ((instr_return ;; i) :: stk) r stk.


  Inductive estepstar : program X -> store -> list (instr X) -> store -> list (instr X) ->  Prop :=
  | estepstar_O: forall p s i, estepstar p s i s i
  | estepstar_S: forall p s i s' i' s'' i'',
              estep p s i s' i' ->
              estepstar p s' i' s'' i'' ->
              estepstar p s i s'' i''.

  Definition eventually_ehalts (p:program X) (r:store) (s:list (instr X)) : Prop :=
    exists r', estepstar p r s r' nil.

  Definition erase_instr : instruction -> instr X :=
    fmap_instr (fun _ => x).

  Definition erase_prog := map_fmap _ _ erase_instr.

  Theorem erase_step : forall p p' n r r' s s',
    step (K.squash (n,p)) p' r s r' s' ->
    estep (erase_prog p) r (List.map erase_instr s) r' (List.map erase_instr s') /\
    exists n', p' = K.squash (n',p).
  Proof.
    intros.
    inv H; unfold erase_instr; simpl in *;
      try (split; econstructor; eauto; fail).
    split.
    eapply estep_call; eauto.
    unfold prog_lookup in H1.
    rewrite K.unsquash_squash in H1.
    simpl in H1.
    unfold KnotInput.fmap in H1.
    eapply fmap_eqn2 in H1.
    destruct H1 as [i'' [? ?]].
    unfold erase_prog.
    erewrite fmap_eqn.
    2: eauto.
    f_equal.
    subst i'.
    clear.
    unfold erase_instr.
    induction i''; simpl; congruence.
    hnf in H2.
    rewrite K.knot_age1 in H2.
    rewrite K.unsquash_squash in H2.
    destruct n; try discriminate.
    inv H2.
    exists n.
    apply K.unsquash_inj.
    repeat rewrite K.unsquash_squash.
    f_equal.
    rewrite K.fmap_fmap.
    change (S n) with (1 +n).
    rewrite <- K.approx_approx1.
    auto.
  Qed.

  Lemma erase_halt' : forall n p p' r r' s,
    stepstar (K.squash (n,p)) p' r s r' nil ->
    estepstar (erase_prog p) r (List.map erase_instr s) r' nil.
  Proof.
    intros.
    remember (K.squash (n,p)) as phat.
    remember (@nil instruction) as s'.
    revert Heqphat Heqs'.
    revert n.
    induction H; intros.
    subst i.
    simpl.
    econstructor.
    subst.
    apply erase_step in H.
    destruct H.
    destruct H1.
    subst p'.
    spec IHstepstar x0.
    spec IHstepstar; auto.
    spec IHstepstar; auto.
    eapply estepstar_S; eauto.
  Qed.

  Theorem erase_halt : forall p n r s,
    eventually_halts (K.squash (n,p)) r s ->
    eventually_ehalts (erase_prog p) r (List.map erase_instr s).
  Proof.
    intros. hnf in H. hnf.
    destruct H as [p' [r' ?]].
    exists r'.
    eapply erase_halt'; eauto.
  Qed.

  Theorem total_correctness_full_erasure : forall G psi l t c r n,
    verify_prog psi G ->
    G |-- funptr l unit t (fun _ => TT) (fun _ => TT) ->
    proj1_sig t r n ->
    psi#l = Some c ->
    eventually_ehalts (erase_prog psi) r ((erase_instr c ;; instr_assert x) :: nil).
  Proof.
    intros.
    generalize (verify_halts t G psi l H H0 r n c H1 H2).
    apply erase_halt.
  Qed.

End estep.
