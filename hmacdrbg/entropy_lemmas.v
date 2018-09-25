Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import hmacdrbg.entropy.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import sha.ByteBitRelations.
Require Import sha.general_lemmas.

Fixpoint get_first_None (limit:nat) (s: ENTROPY.stream): nat :=
  match limit with
    | O => O (* bogus *)
    | S limit' =>
      match s O with
        | None => O
        | Some _ => S (get_first_None limit' (fun i => s (S i)))
      end
  end
.

Lemma get_bits_stream_success:
  forall k s b s',
    ENTROPY.success b s' = ENTROPY.get_bits k s ->
    s' = fun i => s (k + i)%nat.
Proof.
  intros k.
  destruct k as [|k'].
  {
    simpl. intros. inv H. extensionality i; reflexivity.
  }
  simpl.
  intros.
  destruct (ENTROPY.get_bits k' s); try solve [inversion H].
  destruct (s0 0%nat); try solve [inversion H].
  inv H.
  reflexivity.
Qed.

Lemma get_bits_stream_success_Some:
  forall k s b s',
    ENTROPY.success b s' = ENTROPY.get_bits k s ->
    (forall i, (i < k)%nat -> s i <> None).
Proof.
  intros k.
  induction k as [|k']; intros. omega.
  simpl in H.
  remember (ENTROPY.get_bits k' s) as get_bits_k'_s; destruct get_bits_k'_s; try solve [inversion H].
  remember (s0 0%nat) as s0_0; destruct s0_0; try solve [inversion H].
  inv H.
  pose proof Heqget_bits_k'_s as IHsimpl.
  pose proof (Heqget_bits_k'_s) as Hstream.
  apply get_bits_stream_success in Hstream; subst.
  destruct (le_lt_eq_dec i k'). omega.
  {
    (* i < k', use inductive case *)
    eapply IHk'; eassumption.
  }
  {
    (* i = k', use known info *)
    subst.
    replace (k' + 0)%nat with k' in Heqs0_0 by omega.
    intros contra; rewrite <- Heqs0_0 in contra; inversion contra.
  }
Qed.

Lemma get_first_None_limit:
  forall k s i,
    i = get_first_None k s ->
    (i <= k)%nat.
Proof.
  induction k as [|k']; intros. simpl in H. omega.
  simpl in H.
  remember (s O) as s_O; destruct s_O.
  destruct i as [|i']; try solve [omega].
  inversion H.
  pose proof (IHk' (fun i => s (S i)) i').
  subst; omega.
  subst; omega.
Qed.

(* TODO convert this to use get_first_None_limit *)
Lemma get_bits_stream_error:
  forall k s e s',
    ENTROPY.error e s' = ENTROPY.get_bits k s ->
    (exists i, (i < k)%nat /\ (forall i', s' i' = match Nat.compare i' i with
                                   | Lt => s i'
                                   | Eq | Gt => s (S i')
                                 end) /\ s i = None /\ (forall i', (i' < i)%nat -> s i' <> None)).
Proof.
  intros k.
  induction k as [|k']; intros. inversion H.
  simpl in H.
  remember (ENTROPY.get_bits k' s) as get_bits_k'_s; destruct get_bits_k'_s.
  {
    (* get_bits k' s = success *)
    pose proof (Heqget_bits_k'_s) as Hstream.
    apply get_bits_stream_success in Hstream; subst.
    replace (k' + 0)%nat with k' in H by omega.
    remember (s k') as s_k'; destruct s_k'; inv H.
    exists k'.
    repeat split; auto.
    intros.
    eapply get_bits_stream_success_Some; eassumption.
  }
  {
    (* get_bits k' s = error *)
    pose proof (IHk' s e0 s0 Heqget_bits_k'_s) as IHsimpl.
    destruct IHsimpl.
    destruct (le_lt_dec k' x).
    {
      (* x >= k' *)
      destruct H0. omega.
    }
    {
      exists x.
      inv H.
      destruct H0.
      split; auto.
    }
  }
Qed.

Lemma get_bits_length:
  forall k s b s',
    ENTROPY.success b s' = ENTROPY.get_bits k s ->
    length b = k.
Proof.
  intros k.
  induction k as [|k'].
  {
    intros.
    inv H.
    reflexivity.
  }
  intros until s'.
  simpl.
  intros H.
  remember (ENTROPY.get_bits k' s) as result.
  destruct result; [|inversion H].
  remember (s0 0%nat) as s0_0.
  destruct s0_0; try solve [inversion H].
  inv H.
  rewrite app_length.
  simpl. replace (length l + 1)%nat with (S (length l)) by omega.
  rewrite IHk' with (s':=s0) (s:=s); auto.
Qed.

Lemma get_bytes_length:
  forall k s b s',
    ENTROPY.success b s' = ENTROPY.get_bytes k s ->
    length b = k.
Proof.
  unfold ENTROPY.get_bytes; intros.
  remember (ENTROPY.get_bits (8 * k)%nat s) as get_bits_s.
  destruct get_bits_s; inv H.
  assert (length l = (8 * k)%nat) by (apply get_bits_length with (s:=s) (s':=s0); auto).
  apply bitsToBytes_len_gen.
  omega.
Qed.

Lemma get_bytes_Zlength:
  forall k s b s',
    k >= 0 ->
    ENTROPY.success b s' = ENTROPY.get_bytes (Z.to_nat k) s ->
    Zlength b = k.
Proof.
  intros.
  rewrite Zlength_correct.
  erewrite get_bytes_length.
  rewrite Z2Nat.id; [reflexivity | omega].
  eauto.
Qed.
