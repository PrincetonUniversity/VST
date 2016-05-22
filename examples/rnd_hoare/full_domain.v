Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import RndHoare.random_oracle.

Definition is_full_domain {ora: RandomOracle} (d: RandomVarDomain): Prop :=
  forall h, is_inf_history h ->
    exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ d h'.

Lemma unit_domain_full {ora: RandomOracle}: is_full_domain unit_space_domain.
Proof.
  hnf; intros.
  exists (fin_history nil).
  split.
  + left.
    (* TODO: pick out this proof. *)
    hnf; intros.
    left; simpl.
    destruct n; auto.
  + simpl.
    unfold Basics.compose.
    simpl; auto.
Qed.

Definition full_domain_same_covered {ora: RandomOracle}: forall (d1 d2: RandomVarDomain),
  is_full_domain d1 ->
  is_full_domain d2 ->
  same_covered_domain d1 d2.
Proof.
  unfold is_full_domain, same_covered_domain.
  firstorder.
Qed.

Definition contextual_consi {ora: RandomOracle} (d: RandomHistory -> Prop) (h: RandomHistory): Prop :=
  forall h', d h' -> conflict_history h h' -> False.

Definition nth_layer_pre_extension {ora: RandomOracle} (n: nat) (d: RandomHistory -> Prop): RandomHistory -> Prop :=
  fun h => d h \/ (is_n_history n h /\ contextual_consi d h).

Fixpoint n_layers_pre_extension {ora: RandomOracle} (n: nat) (d: RandomHistory -> Prop): RandomHistory -> Prop :=
  match n with
  | 0 => d
  | S n => nth_layer_pre_extension n (n_layers_pre_extension n d)
  end.

Definition finite_layers_pre_extension {ora: RandomOracle} (d: RandomHistory -> Prop): RandomHistory -> Prop :=
  fun h => exists n, n_layers_pre_extension n d h.

Definition max_pre_extension {ora: RandomOracle} (d: RandomHistory -> Prop): RandomHistory -> Prop :=
  fun h => finite_layers_pre_extension d h \/ contextual_consi (finite_layers_pre_extension d) h.

Definition nth_layer_covered {ora: RandomOracle} (n: nat) (d: RandomHistory -> Prop): Prop :=
  forall h, is_n_history n h -> contextual_consi d h -> d h.

Lemma fstn_history_coincide {ora: RandomOracle}: forall n h,
  history_coincide n h (fstn_history n h).
Proof.
  intros.
  intros m ?.
  rewrite fstn_history_Some by omega.
  auto.
Qed.

Lemma AUX_contextual_consi_Sn_n {ora: RandomOracle}: forall n h h1 h2 a1 a2,
  is_n_history (S n) h ->
  is_n_history (S n) h1 ->
  history_coincide n h1 h2 ->
  h1 n = Some a1 ->
  h2 n = Some a2 ->
  projT1 a1 = projT1 a2 ->
  conflict_history h h1 ->
  conflict_history h h2.
Proof.
  intros.
  destruct H5 as [m [? ?]].
  exists m.
  destruct (lt_eq_lt_dec m n) as [[?H | ?H] | ?H].
  + split.
    - apply (history_coincide_weaken m n h1 h2) in H1; [| omega].
      intros m0 HH; specialize (H1 m0 HH); specialize (H5 m0 HH); congruence.
    - rewrite <- (H1 m) by auto.
      auto.
  + subst m.
    split.
    - intros m0 HH; specialize (H1 m0 HH); specialize (H5 m0 HH); congruence.
    - rewrite H2 in H6; rewrite H3.
      rewrite <- H4; auto.
  + exfalso.
    rewrite (is_n_history_None (S n) m h) in H6 by (auto; omega).
    rewrite (is_n_history_None (S n) m h1) in H6 by (auto; omega).
    auto.
Qed.

Lemma contextual_consi_Sn_n {ora: RandomOracle}: forall (n: nat) (d: RandomHistory -> Prop) (h h0: RandomHistory),
  is_n_history (S n) h ->
  is_n_history (S n) h0 ->
  contextual_consi d h ->
  contextual_consi d h0 ->
  conflict_history h h0 ->
  contextual_consi d (fstn_history n h).
Proof.
  intros.
  hnf; intros.
  apply (H1 h' H4).
  destruct H5 as [m [? ?]].
  exists m.
  destruct (lt_eq_lt_dec n m) as [[?H | ?H] | ?H].
  + exfalso.
    specialize (H5 n H7).
    rewrite fstn_history_None in H5 by omega.
    symmetry in H5.
    rewrite fstn_history_None in H6 by omega.
    rewrite (history_sound1 h' n m) in H6 by (auto; omega).
    auto.
  + subst m.
    rewrite fstn_history_None in H6 by omega.
    destruct (h' n) eqn: ?H; try inversion H6; clear H6.
    assert (history_coincide n h h'); [| split; auto].
    - intros m ?H; specialize (H5 m H6).
      rewrite fstn_history_Some in H5 by omega; auto.
    - destruct (h n) eqn: ?H; auto.
      specialize (H2 h' H4).
      intro; apply H2; clear H2.
      apply conflict_history_sym in H3.
      apply (AUX_contextual_consi_Sn_n n h0 h h' r0 r); auto.
  + split.
    - intros m0 ?H; specialize (H5 m0 H8).
      rewrite fstn_history_Some in H5 by omega; auto.
    - rewrite fstn_history_Some in H6 by omega; auto.
Qed.

Lemma pre_extension_spec {ora: RandomOracle}: forall (n: nat) (d: RandomHistory -> Prop),
  (history_set_consi d /\ forall n', n' < n -> nth_layer_covered n' d) ->
  (history_set_consi (nth_layer_pre_extension n d) /\
   forall n', n' < S n -> nth_layer_covered n' (nth_layer_pre_extension n d)).
Proof.
  unfold history_set_consi, nth_layer_covered.
  intros.
  destruct H; split.
  + intros.
    destruct H2 as [? | [? ?]], H3 as [? | [? ?]].
    - apply (H h1 h2); auto.
    - apply (H4 h1); auto.
      apply conflict_history_sym; auto.
    - apply (H4 h2); auto.
    - destruct n.
      * apply (is_0_history_non_conflict h1 h2); auto.
      * assert (d (fstn_history n h1)).
        Focus 1. {
          apply (H0 n).
          + omega.
          + apply fstn_history_is_n_history with (S n); auto.
          + apply (contextual_consi_Sn_n n d h1 h2); auto.
        } Unfocus.
        apply (H4 _ H6).
        exists n.
        split; [apply fstn_history_coincide |].
        clear - H2.
        destruct H2.
        specialize (H0 n (le_n _)).
        destruct (h1 n); [| congruence].
        rewrite fstn_history_None by omega.
        auto.
  + intros.
    destruct (eq_nat_dec n' n).
    - subst n'.
      right.
      split; auto.
      intros h' ?.
      apply (H3 h').
      left; auto.
    - left.
      apply (H0 n'); [omega | auto |].
      intros h' ?.
      apply (H3 h').
      left; auto.
Qed.

