Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Import RndHoare.random_oracle.

Definition is_max_anti_chain {ora: RandomOracle} (d: HistoryAntiChain): Prop :=
  forall h, is_inf_history h ->
    exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ d h'.

Lemma unit_anti_chain_max {ora: RandomOracle}: is_max_anti_chain unit_space_anti_chain.
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

Definition max_anti_chain_same_covered {ora: RandomOracle}: forall (d1 d2: HistoryAntiChain),
  is_max_anti_chain d1 ->
  is_max_anti_chain d2 ->
  same_covered_anti_chain d1 d2.
Proof.
  unfold is_max_anti_chain, same_covered_anti_chain.
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
  fun h => finite_layers_pre_extension d h \/ (is_inf_history h /\ contextual_consi (finite_layers_pre_extension d) h).

Definition guarded_covered {ora: RandomOracle} (P: RandomHistory -> Prop) (d: RandomHistory -> Prop): Prop :=
  forall h, P h -> contextual_consi d h -> d h.

Definition nth_layer_covered {ora: RandomOracle} (n: nat) (d: RandomHistory -> Prop): Prop :=
  guarded_covered (is_n_history n) d.

Lemma contextual_consi_shorten {ora: RandomOracle}: forall (n: nat) (d: RandomHistory -> Prop) (h h0: RandomHistory),
  h n <> None ->
  h0 n <> None ->
  contextual_consi d h ->
  contextual_consi d h0 ->
  history_coincide n h h0 ->
  n_conflict_history n h h0 ->
  contextual_consi d (fstn_history n h).
Proof.
  intros.
  hnf; intros.
  apply (H1 h' H5).
  destruct H6 as [m [? ?]].
  exists m.
  destruct (lt_eq_lt_dec n m) as [[?H | ?H] | ?H].
  + exfalso.
    specialize (H6 n H8).
    rewrite fstn_history_None in H6 by omega.
    symmetry in H6.
    hnf in H7.
    rewrite fstn_history_None in H7 by omega.
    rewrite (history_sound1 h' n m) in H7 by (auto; omega).
    auto.
  + subst m.
    unfold n_conflict_history in H7 |- *.
    rewrite fstn_history_None in H7 by omega.
    destruct (h' n) eqn: ?H; try inversion H7; clear H7.
    assert (history_coincide n h h'); [| split; auto].
    - intros m ?H; specialize (H6 m H7).
      rewrite fstn_history_Some in H6 by omega; auto.
    - destruct (h n) eqn: ?H; auto.
      specialize (H2 h' H5).
      intro; apply H2; clear H2.
      exists n.
      apply history_coincide_sym in H3.
      split; [apply history_coincide_trans with h; auto |].
      clear - H8 H9 H10 H4.
      hnf in H4 |- *.
      rewrite H8. rewrite H9 in H4.
      rewrite <- H10; auto.
      destruct (h0 n); congruence.
  + split.
    - intros m0 ?H; specialize (H6 m0 H9).
      rewrite fstn_history_Some in H6 by omega; auto.
    - hnf in H7.
      rewrite fstn_history_Some in H7 by omega; auto.
Qed.

Lemma is_n_history_conflict {ora: RandomOracle}: forall n m h1 h2,
  is_n_history n h1 ->
  is_n_history n h2 ->
  n_conflict_history m h1 h2 ->
  m < n.
Proof.
  intros.
  destruct H as [? _], H0 as [? _].
  destruct (le_lt_dec n m); auto.
  exfalso.
  hnf in H1.
  rewrite (history_sound1 h1 n m l) in H1 by auto.
  rewrite (history_sound1 h2 n m l) in H1 by auto.
  auto.
Qed.

Lemma is_n_history_Some {ora: RandomOracle}: forall n m h, m < n -> is_n_history n h -> h m <> None.
Proof.
  intros.
  destruct H0.
  intro.
  apply (H1 m); auto.
Qed.

Lemma nth_layer_pre_extension_spec {ora: RandomOracle}: forall (n: nat) (d: RandomHistory -> Prop),
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
    - destruct H1 as [m [? ?]].
      pose proof is_n_history_conflict n m h1 h2 H2 H3 H6.
      assert (d (fstn_history m h1)).
      Focus 1. {
        apply (H0 m).
        + auto.
        + apply fstn_history_is_n_history with n; auto; omega.
        + apply (contextual_consi_shorten m d h1 h2); auto;
          apply is_n_history_Some with n; auto.
      } Unfocus.
      apply (H4 _ H8).
      exists m.
      split; [apply fstn_history_coincide |].
      clear - H2 H7.
      apply is_n_history_Some with (m0 := m) in H2; auto.
      hnf.
      rewrite fstn_history_None by omega.
      destruct (h1 m); auto; congruence.
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

Lemma n_layers_pre_extension_spec {ora: RandomOracle}: forall (n: nat) (d: RandomHistory -> Prop),
  history_set_consi d ->
  history_set_consi (n_layers_pre_extension n d) /\
  forall n', n' < n -> nth_layer_covered n' (n_layers_pre_extension n d).
Proof.
  intros.
  induction n; simpl.
  + split; auto.
    intros.
    omega.
  + apply nth_layer_pre_extension_spec; auto.
Qed.

Lemma fin_history_n_history {ora: RandomOracle}: forall h,
  is_fin_history h ->
  exists n, is_n_history n h.
Proof.
  intros.
  destruct H.
  pose proof dec_inh_nat_subset_has_unique_least_element (fun x => h x = None).
  simpl in H0.
  destruct H0.
  + clear.
    intros n; destruct (h n); [right | left]; congruence.
  + exists x; auto.
  + clear - H0.
    destruct H0 as [[? ?] _].
    exists x0; split; auto.
    intros x; specialize (H0 x).
    intros ? ?.
    apply H0 in H2; omega.
Qed.

Lemma n_layers_pre_extension_mono {ora: RandomOracle}: forall (n1 n2: nat) (d: RandomHistory -> Prop) h,
  n1 <= n2 ->
  (n_layers_pre_extension n1 d) h ->
  (n_layers_pre_extension n2 d) h.
Proof.
  intros.
  remember (n2 - n1) as del.
  assert (n2 = del + n1) by omega.
  subst n2.
  clear Heqdel H.
  revert n1 H0; induction del; intros.
  + auto.
  + simpl.
    left.
    apply IHdel; auto.
Qed.

Lemma n_layers_pre_extension_consi_mono {ora: RandomOracle}: forall (n1 n2: nat) (d: RandomHistory -> Prop) h,
  n1 <= n2 ->
  contextual_consi (n_layers_pre_extension n2 d) h ->
  contextual_consi (n_layers_pre_extension n1 d) h.
Proof.
  intros.
  hnf; intros.
  apply (H0 h'); auto.
  eapply n_layers_pre_extension_mono; eauto.
Qed.

Lemma finite_layers_pre_extension_spec {ora: RandomOracle}: forall (d: RandomHistory -> Prop),
  history_set_consi d ->
  history_set_consi (finite_layers_pre_extension d) /\
  guarded_covered is_fin_history (finite_layers_pre_extension d).
Proof.
  intros.
  split.
  + hnf; intros.
    destruct H1 as [n1 ?].
    destruct H2 as [n2 ?].
    apply (n_layers_pre_extension_mono n1 (max n1 n2) _ _ (Max.le_max_l _ _)) in H1.
    apply (n_layers_pre_extension_mono n2 (max n1 n2) _ _ (Max.le_max_r _ _)) in H2.
    apply n_layers_pre_extension_spec with (n := max n1 n2) in H.
    destruct H as [? _].
    apply (H h1 h2); auto.
  + hnf; intros.
    destruct (fin_history_n_history _ H0) as [n ?]; clear H0.
    apply n_layers_pre_extension_spec with (n0 := S n) in H.
    destruct H as [_ ?].
    exists (S n).
    apply (H n (le_n _ ) h); auto.

    clear - H1.
    hnf; intros.
    apply (H1 h'); auto.
    exists (S n); auto.
Qed.

Lemma max_pre_extension_spec {ora: RandomOracle}: forall (d: RandomHistory -> Prop),
  history_set_consi d ->
  history_set_consi (max_pre_extension d) /\
  guarded_covered is_inf_history (max_pre_extension d).
Proof.
  intros.
  apply finite_layers_pre_extension_spec in H.
  destruct H.
  split.
  + hnf; intros.
    destruct H2 as [? | [? ?]], H3 as [? | [? ?]].
    - apply (H h1 h2); auto.
    - apply (H4 h1); auto.
      apply conflict_history_sym; auto.
    - apply (H4 h2); auto.
    - destruct H1 as [n [? ?]].
      assert (finite_layers_pre_extension d (fstn_history n h1)).
      Focus 1. {
        apply H0.
        + exists n.
          apply fstn_history_None; omega.
        + apply (contextual_consi_shorten n _ h1 h2); auto;
          apply is_n_history_Some with n; auto.
      } Unfocus.
      apply (H4 _ H7).
      exists n.
      split; [apply fstn_history_coincide |].
      clear - H2.
      hnf.
      rewrite fstn_history_None by auto.
      specialize (H2 n).
      destruct (h1 n); auto; congruence.
  + hnf; intros.
    right.
    split; auto.
    hnf; intros.
    apply (H2 h'); auto.
    left; auto.
Qed.

Definition max_extension {ora: RandomOracle} (d: HistoryAntiChain): HistoryAntiChain.
  exists (max_pre_extension d).
  constructor.
  destruct d as [d H]; simpl.
  exact (proj1 (max_pre_extension_spec _ rand_consi)).
Defined.

Require Import Coq.Logic.Classical.

Lemma max_extension_full {ora: RandomOracle}: forall d, is_max_anti_chain (max_extension d).
Proof.
  intros.
  hnf; intros.
  destruct (classic (exists h', (max_extension d) h' /\ conflict_history h h')).
  + destruct H0 as [h' [? ?]].
    exists h'.
    split; auto.
    apply conflict_history_strict_conflict; auto.
    apply conflict_history_sym; auto.
  + exists h.
    pose proof max_pre_extension_spec d (@rand_consi _ _ (raw_anti_chain_legal d)).
    destruct H1 as [_ ?].
    specialize (H1 h H).
    split; [left; apply prefix_history_refl |].
    apply H1.
    hnf; intros.
    apply H0.
    exists h'.
    split; auto.
Qed.
