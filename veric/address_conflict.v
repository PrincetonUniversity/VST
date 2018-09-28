(* This file is developed by Qinxiang Cao, Aquinas Hobor and Shengyi Wang in 2015. *)

Require Import VST.veric.base.
Require Import VST.veric.val_lemmas.
Require Import VST.veric.Memory.

Lemma range_overlap_spec: forall l1 n1 l2 n2,
  n1 > 0 ->
  n2 > 0 ->
  (range_overlap l1 n1 l2 n2 <-> adr_range l1 n1 l2 \/ adr_range l2 n2 l1).
Proof.
  intros.
  unfold range_overlap, adr_range.
  destruct l1, l2.
  split; intros.
  + destruct H1 as [[? ?] [[? ?] [? ?]]].
    subst.
    destruct (zle z z0); [left | right].
    - split; auto.
      omega.
    - split; auto.
      omega.
  + destruct H1 as [[? ?] | [? ?]].
    - exists (b0, z0). repeat split; auto; omega.
    - exists (b, z). repeat split; auto; omega.
Qed.

Lemma range_overlap_comm: forall l1 n1 l2 n2, range_overlap l1 n1 l2 n2 -> range_overlap l2 n2 l1 n1.
Proof.
  unfold range_overlap.
  intros.
  destruct H as [l ?].
  exists l.
  tauto.
Qed.

Lemma range_overlap_non_zero: forall l1 n1 l2 n2, range_overlap l1 n1 l2 n2 -> n1 > 0 /\ n2 > 0.
Proof.
  unfold range_overlap.
  intros.
  destruct H as [l [? ?]].
  apply adr_range_non_zero in H.
  apply adr_range_non_zero in H0.
  auto.
Qed.

Definition pointer_range_overlap p n p' n' :=
  exists l l', val2adr p l /\ val2adr p' l' /\ range_overlap l n l' n'.

Lemma pointer_range_overlap_dec: forall p1 n1 p2 n2, {pointer_range_overlap p1 n1 p2 n2} + {~ pointer_range_overlap p1 n1 p2 n2}.
Proof.
  unfold pointer_range_overlap.
  intros.
  destruct p1;
  try solve
   [right;
    intros [[? ?] [[? ?] [HH [_ _]]]];
    inversion HH].
  destruct p2;
  try solve
   [right;
    intros [[? ?] [[? ?] [_ [HH _]]]];
    inversion HH].
  destruct (zlt 0 n1); [| right; intros [[? ?] [[? ?] [_ [_ HH]]]]; apply range_overlap_non_zero in HH; omega].
  destruct (zlt 0 n2); [| right; intros [[? ?] [[? ?] [_ [_ HH]]]]; apply range_overlap_non_zero in HH; omega].
  destruct (eq_block b b0).
  (*destruct (Clight_lemmas.block_eq_dec b b0).*)
  + subst b0.
    unfold val2adr.
    forget (Ptrofs.unsigned i) as i1;
    forget (Ptrofs.unsigned i0) as i2;
    clear i i0.
    destruct (range_dec i1 i2 (i1 + n1)); [| destruct (range_dec i2 i1 (i2 + n2))].
    - left.
      exists (b, i1), (b, i2); repeat split; auto.
      apply range_overlap_spec; try omega.
      left; simpl; auto.
    - left.
      exists (b, i1), (b, i2); repeat split; auto.
      apply range_overlap_spec; try omega.
      right; simpl; auto.
    - right.
      intros [[? ?] [[? ?] [? [? HH]]]].
      inversion H; inversion H0; subst.
      apply range_overlap_spec in HH; [| omega | omega].
      simpl in HH; omega.
  + right.
    intros [[? ?] [[? ?] [? [? HH]]]].
    simpl in H, H0.
    inversion H; inversion H0; subst.
    apply range_overlap_spec in HH; [| omega | omega].
    simpl in HH.
    pose proof @eq_sym _ b0 b.
    tauto.
Qed.

Lemma pointer_range_overlap_refl: forall p n1 n2,
  isptr p ->
  n1 > 0 ->
  n2 > 0 ->
  pointer_range_overlap p n1 p n2.
Proof.
  intros.
  destruct p; try inversion H.
  exists (b, Ptrofs.unsigned i), (b, Ptrofs.unsigned i).
  repeat split; auto.
  apply range_overlap_spec; auto.
  left.
  simpl.
  split; auto; omega.
Qed.

Lemma pointer_range_overlap_comm: forall p1 n1 p2 n2,
  pointer_range_overlap p1 n1 p2 n2 <->
  pointer_range_overlap p2 n2 p1 n1.
Proof.
  cut (forall p1 n1 p2 n2,
         pointer_range_overlap p1 n1 p2 n2 ->
         pointer_range_overlap p2 n2 p1 n1). {
    intros.
    pose proof H p1 n1 p2 n2.
    pose proof H p2 n2 p1 n1.
    tauto.
  }
  unfold pointer_range_overlap.
  intros.
  destruct H as [l [l' [? [? ?]]]].
  exists l', l.
  repeat split; auto.
  apply range_overlap_comm.
  auto.
Qed.

Lemma pointer_range_overlap_non_zero: forall p1 n1 p2 n2,
  pointer_range_overlap p1 n1 p2 n2 -> n1 > 0 /\ n2 > 0.
Proof.
  intros.
  destruct H as [? [? [? [? ?]]]].
  eapply range_overlap_non_zero; eauto.
Qed.

Lemma pointer_range_overlap_isptr: forall p1 n1 p2 n2,
  pointer_range_overlap p1 n1 p2 n2 -> isptr p1 /\ isptr p2.
Proof.
  intros.
  destruct H as [? [? [? [? ?]]]].
  destruct p1, p2; try solve [inversion H | inversion H0].
  simpl; auto.
Qed.

