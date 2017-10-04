Require Import msl.msl_standard.
Require Import Maps.
Require Import FuncListMachine.
Require Import lemmas.
Require Import hoare_total.

Section wp.
  Variable R:pred world.

  Fixpoint is_basic (i:instruction) : bool :=
    match i with
    | instr_call _ => false
    | instr_seq s1 s2 => andb (is_basic s1) (is_basic s2)
    | _ => true
    end.

  Fixpoint wp (x:nat) (i:instruction) (POST:pred world) { struct i } : pred world :=
    match i with
    | instr_return => R

    | instr_assert P => P && POST

    | instr_getlabel l v =>  box (setM v (value_label l)) POST

    | instr_fetch_field v1 0 v2 =>
        EX x1:value, EX x2:value,
          store_op(fun r => r#v1 = Some (value_cons x1 x2)) && box (setM v2 x1) POST

    | instr_fetch_field v1 1 v2 =>
        EX x1:value, EX x2:value,
          store_op (fun r => r#v1 = Some (value_cons x1 x2)) && box (setM v2 x2) POST

    | instr_cons v1 v2 v3 =>
      (EX x1:value, EX x2:value,
        store_op (fun r => r#v1 = Some x1 /\ r#v2 = Some x2) &&
          box (setM v3 (value_cons x1 x2)) POST)

    | instr_if_nil v s1 s2 =>

    EX val:value,
      store_op (fun r => r#v = Some val) &&
    (

      ((!!(val = value_label (L 0)) && wp x s1 POST))
      ||
      ((EX x1:value, (EX x2:value,
        !!(val = (value_cons x1 x2)))) && wp x s2 POST)
    )

    | instr_call v =>
      EX l:label, EX A:Type, EX t:termMeas, EX lP:(A->pred world), EX lQ:(A -> pred world), EX n':nat, EX a:A,
        store_op (fun r => r#v = Some (value_label l) /\ proj1_sig t r n' /\ n' < x) &&
        (world_op (funptr l A t lP lQ) (fun _ => True)) &&
        lP a && (closed (lQ a --> POST))

    | instr_seq s1 s2 =>
        if is_basic s1 then wp 0 s1 (wp x s2 POST) else
        if is_basic s2 then wp x s1 (wp 0 s2 POST) else
        EX n:nat, EX m:nat,
           wp n s1 (wp m s2 POST) && !!(n+m = x)

    | _ => FF
    end.
End wp.

Lemma hoare_wp : forall i x G R P Q,
  prog_op G && P |-- wp R x i Q ->
  hoare x G R P i Q.
Proof.
  induction i; simpl; intros.
  apply hoare_weaken_time with 0. omega.
  apply hoare_weaken_post with P.
  hnf; intros. spec H a. spec H; auto.
  destruct H; auto.
  apply hoare_assert; auto.
  intro a. spec H a. intuition.
  destruct H1; auto.

  apply hoare_weaken_time with 0. omega.
  eapply hoare_weaken_pre.
  2: eapply hoare_getlabel. auto.

  destruct n.
  apply hoare_weaken_time with 0. omega.
  eapply hoare_weaken_pre.
  apply H.
  apply hoare_ex_pre. intro x1.
  apply hoare_ex_pre. intro x2.
  apply hoare_step_fetch0.
  destruct n.
  apply hoare_weaken_time with 0. omega.
  eapply hoare_weaken_pre.
  apply H.
  apply hoare_ex_pre. intro x1.
  apply hoare_ex_pre. intro x2.
  apply hoare_step_fetch1.
  eapply hoare_weaken_pre.
  apply H. repeat intro. elim H4.

  apply hoare_weaken_time with 0. omega.
  eapply hoare_weaken_pre.
  apply H.
  apply hoare_ex_pre. intro x1.
  apply hoare_ex_pre. intro x2.
  apply hoare_cons.

  eapply hoare_weaken_pre.
  apply H.
  destruct (is_basic i1).
  change x with (0+x).
  apply hoare_seq with (wp R x i2 Q); auto.
  apply IHi1; auto. hnf; simpl; intuition.
  apply IHi2; auto. hnf; simpl; intuition.
  destruct (is_basic i2).
  pattern x at 1.
  replace x with (x+0) by omega.
  apply hoare_seq with (wp R 0 i2 Q); auto.
  apply IHi1; auto. hnf; simpl; intuition.
  apply IHi2; auto. hnf; simpl; intuition.
  apply hoare_ex_pre. intro n.
  apply hoare_ex_pre. intro m.
  eapply hoare_weaken_pre with
    (!!(n+m = x) && (wp R n i1 (wp R m i2 Q))).
  hnf; unfold andp; simpl; intuition.
  apply hoare_fact_pre. intro.
  subst x.
  apply hoare_seq with (wp R m i2 Q); auto.
  apply IHi1; auto. hnf; simpl; intuition.
  apply IHi2; auto. hnf; simpl; intuition.
  eapply hoare_weaken_pre.
  apply H.
  apply hoare_if.
  apply IHi1; auto. hnf; simpl; intuition.
  apply IHi2; auto. hnf; simpl; intuition.

  eapply hoare_weaken_pre.
  apply H.
  repeat (apply hoare_ex_pre; intro).
  match goal with
    [ |- hoare _ _ _ ?P _ _ ] =>
    apply hoare_weaken_pre with (!!(z4 < x) && P)
  end.
  hnf; intros. split; auto.
  destruct H0.
  destruct H1.
  destruct H1.
  destruct H1.
  hnf in H1.
  destruct a.
  hnf. intuition.
  destruct H0. auto.
  apply hoare_fact_pre; intro.
  destruct x. inv H0.
  eapply hoare_weaken_time.
  apply H0.
  eapply hoare_weaken_pre.
  2: eapply hoare_call'.
  hnf. intuition.
  do 6 econstructor.
  destruct H1.
  destruct H2.
  split; eauto.
  destruct H2.
  split; eauto.
  destruct H2.
  split; eauto.
  destruct a; simpl in *; intuition.

  apply hoare_weaken_time with 0. omega.
  eapply hoare_weaken_pre.
  apply H.
  apply hoare_weaken_post with FF.
  hnf; intros. destruct H0. elim H1.
  apply hoare_return.
Qed.
