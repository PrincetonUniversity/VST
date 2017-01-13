Require Import msl.msl_standard.
Require Import Maps.
Require Import FuncListMachine.
Require Import lemmas.
Require Import hoare_total.


(* rule for if in weakest precondition form *)
Lemma wp_if : forall t x v s1 s2 P1 P2 G R Q,
  let wp :=
    EX val:value,
      store_op (fun r => r#v = Some val) &&
    (

      ((!!(val = value_label (L 0)) && P1))
      ||
      ((EX x1:value, (EX x2:value,
        !!(val = (value_cons x1 x2)))) && P2)
    )
   in
  hoare t x G R P1 s1 Q ->
  hoare t x G R P2 s2 Q ->
  hoare t x G R wp (instr_if_nil v s1 s2) Q.
Proof.
  intros.
  apply hoare_if.
  unfold wp.
  hnf; intros.
  destruct H1 as [val [? ?]].
  destruct a as [p' [r t']].
  destruct H1 as [_ [? _]].
  destruct H2.
  destruct H2. simpl in H2.
  subst val.
  split; auto. hnf; auto.
  rewrite H1. split; auto.
  destruct H2.
  destruct H2 as [x1 [x2 ?]].
  simpl in H2.
  subst val.
  split; auto. hnf; auto.
  rewrite H1. auto.
  apply hoare_weaken_pre with P1; auto.
  unfold wp; hnf; intuition.
  destruct a as [? [? ?]].
  destruct H1.
  destruct H1.
  destruct H1.
  unfold store_op, world_op in *;
    simpl in *; intuition.
  rewrite H2 in H5.
  inv H5.
  destruct H3 as [? [? ?]]; discriminate.
  apply hoare_weaken_pre with P2; auto.
  unfold wp; hnf; intuition.
  destruct a as [? [? ?]].
  destruct H1.
  destruct H1.
  destruct H1.
  unfold store_op, world_op in *;
    simpl in *; intuition.
  subst x0.
  rewrite H2 in H5.
  destruct H5 as [? [? ?]]; discriminate.
Qed.

Section wp.
  Variable t:terminationMeasure.
  Variables G R:pred world.

  Fixpoint is_basic (i:instruction) : bool :=
    match i with
    | instr_call _ => false
    | instr_seq s1 s2 => andb (is_basic s1) (is_basic s2)
    | _ => true
    end.

  Fixpoint wp (x:nat) (i:instruction) (POST:pred world) { struct i } : pred world :=
    match i with
    | instr_return => R

    | instr_assert P => (G --> proj1_sig P) && POST

    | instr_getlabel l v =>  box (setM v (value_label l)) POST

    | instr_fetch_field v1 0 v2 =>
        EX x1:value, EX x2:value,
          store_op (fun r => r#v1 = Some (value_cons x1 x2)) && box (setM v2 x1) POST

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
      EX l:label, EX A:Type, EX lP:(A->pred world), EX lQ:(A -> pred world), EX n':nat, EX a:A,
        store_op (fun r => r#v = Some (value_label l) /\ t l r = Some n' /\ n' < x) &&
        (G --> funptr l A lP lQ) && lP a && (closed (lQ a --> POST))

    | instr_seq s1 s2 =>
        if is_basic s1 then wp 0 s1 (wp x s2 POST) else
        if is_basic s2 then wp x s1 (wp 0 s2 POST) else
        EX n:nat, EX m:nat,
           wp n s1 (wp m s2 POST) && !!(n+m = x)

    | _ => FF
    end.
End wp.

Lemma hoare_wp : forall i x t G R P Q,
  boxy K.expandM G ->
  P |-- wp t G R x i Q ->
  hoare t x G R P i Q.
Proof.
  induction i; simpl; intros.
  apply hoare_weaken_time with 0. omega.
  apply hoare_weaken_post with P.
  hnf; intros. spec H0 a; intuition. destruct H2; auto.
  apply hoare_assert; auto.
  intro a. spec H0 a. intuition.
  destruct H1. spec H0; auto.
  destruct H0. spec H0 a. spec H0; auto.

  apply hoare_weaken_time with 0. omega.
  eapply hoare_weaken_pre.
  2: eapply hoare_getlabel. auto.
  destruct n.

  apply hoare_weaken_time with 0. omega.
  eapply hoare_weaken_pre.
  apply H0.
  apply hoare_ex_pre. intro x1.
  apply hoare_ex_pre. intro x2.
  apply hoare_step_fetch0.
  destruct n.
  apply hoare_weaken_time with 0. omega.
  eapply hoare_weaken_pre.
  apply H0.
  apply hoare_ex_pre. intro x1.
  apply hoare_ex_pre. intro x2.
  apply hoare_step_fetch1.
  eapply hoare_weaken_pre.
  apply H0. repeat intro. elim H6.

  apply hoare_weaken_time with 0. omega.
  eapply hoare_weaken_pre.
  apply H0.
  apply hoare_ex_pre. intro x1.
  apply hoare_ex_pre. intro x2.
  apply hoare_cons.

  eapply hoare_weaken_pre.
  apply H0.
  destruct (is_basic i1).
  change x with (0+x).
  apply hoare_seq with (wp t G R x i2 Q); auto.
  destruct (is_basic i2).
  pattern x at 1.
  replace x with (x+0) by omega.
  apply hoare_seq with (wp t G R 0 i2 Q); auto.
  apply hoare_ex_pre. intro n.
  apply hoare_ex_pre. intro m.
  eapply hoare_weaken_pre with
    (!!(n+m = x) && (wp t G R n i1 (wp t G R m i2 Q))).
  hnf; unfold andp; simpl; intuition.
  apply hoare_fact_pre. intro.
  subst x.
  apply hoare_seq with (wp t G R m i2 Q); auto.

  eapply hoare_weaken_pre.
  apply H0.
  apply wp_if.
  apply IHi1; auto. hnf; auto.
  apply IHi2; auto. hnf; auto.

  eapply hoare_weaken_pre.
  apply H0.
  apply hoare_call.

  apply hoare_weaken_time with 0. omega.
  eapply hoare_weaken_pre.
  apply H0.
  apply hoare_weaken_post with FF.
  hnf; intros. elim H1.
  apply hoare_return.

  apply hoare_weaken_pre with FF; auto.
  repeat intro. elim H6.
Qed.

