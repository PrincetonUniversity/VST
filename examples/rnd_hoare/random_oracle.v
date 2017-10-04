Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.
Require Export Coq.Logic.Classical.
Require Export Coq.Logic.FunctionalExtensionality.
Require Export Coq.Classes.Equivalence.
Require Export Coq.Classes.Morphisms.

Lemma nth_error_None_iff: forall {A} (l: list A) n, nth_error l n = None <-> n >= length l.
Proof.
  intros.
  revert n; induction l; intros; destruct n; simpl.
  + split; [intros _; omega | auto].
  + split; [intros _; omega | auto].
  + split; [intros; inversion H | omega].
  + rewrite IHl.
    omega.
Qed.

Class RandomOracle: Type := {
  ro_question: Type;
  ro_answer: ro_question -> Type;
  ro_default_question: ro_question;
  ro_default_answer: ro_answer ro_default_question
}.

Definition RandomQA {ora: RandomOracle}: Type := {q: ro_question & ro_answer q}.

Definition RandomHistory {ora: RandomOracle}: Type := {h: nat -> option RandomQA | forall x y, x < y -> h x = None -> h y = None}.

Definition history_get {ora: RandomOracle} (h: RandomHistory) (n: nat) := proj1_sig h n.

Coercion history_get: RandomHistory >-> Funclass.

Lemma history_sound1: forall {ora: RandomOracle} (h: RandomHistory) (x y: nat), x <= y -> h x = None -> h y = None.
Proof.
  intros ? [h ?] ? ? ?.
  destruct H; auto; simpl.
  apply (e x (S m)).
  omega.
Qed.

Lemma history_sound2: forall {ora: RandomOracle} (h: RandomHistory) (x y: nat), x <= y -> (exists a, h y = Some a) -> (exists a, h x = Some a).
Proof.
  intros.
  pose proof history_sound1 h x y H.
  destruct (h x), (h y), H0; eauto.
  specialize (H1 eq_refl).
  congruence.
Qed.

Lemma history_extensionality {ora: RandomOracle}: forall h1 h2: RandomHistory, (forall n, h1 n = h2 n) -> h1 = h2.
Proof.
  intros.
  destruct h1 as [h1 ?H], h2 as [h2 ?H]; simpl in *.
  assert (h1 = h2) by (extensionality n; auto).
  subst h2.
  assert (H0 = H1) by (apply proof_irrelevance).
  subst H1.
  auto.
Qed.

Tactic Notation "history_extensionality" ident(x) :=
  match goal with
    [ |- ?X = ?Y ] =>
     apply history_extensionality; intro x
  end.

Definition fin_history {ora: RandomOracle} (h: list RandomQA) : RandomHistory.
  exists (fun n => nth_error h n).
  intros.
  rewrite nth_error_None_iff in H0 |- *.
  omega.
Defined.

Definition inf_history {ora: RandomOracle} (h: nat -> RandomQA) : RandomHistory.
  exists (fun n => Some (h n)).
  intros.
  congruence.
Defined.

Definition fstn_history {ora: RandomOracle} (n: nat) (h: RandomHistory) : RandomHistory.
  exists (fun m => if le_lt_dec n m then None else h m).
  intros.
  destruct (le_lt_dec n x), (le_lt_dec n y); try congruence.
  + omega.
  + apply (history_sound1 h x y); auto; omega.
Defined.

Definition history_coincide {ora: RandomOracle} (n: nat) (h1 h2: RandomHistory): Prop :=
  forall m, m < n -> h1 m = h2 m.

(*
Definition history_cons {ora: RandomOracle} (h1: RandomHistory) (a: RandomQA) (h2: RandomHistory): Prop :=
  exists n,
    history_coincide n h1 h2 /\
    h1 n = None /\
    h2 n = Some a /\
    h2 (S n) = None.
*)

Definition history_app {ora: RandomOracle} (h1 h2 h: RandomHistory): Prop :=
  exists n,
    h1 n = None /\
    history_coincide n h1 h /\
    (forall m, h (m + n) = h2 m).

Definition is_fin_history {ora: RandomOracle} (h: RandomHistory): Prop :=
  exists n, h n = None.

Definition is_inf_history {ora: RandomOracle} (h: RandomHistory): Prop :=
  forall n, h n <> None.

Definition is_n_history {ora: RandomOracle} (n: nat) (h: RandomHistory): Prop :=
  h n = None /\ forall n', n' < n -> h n' <> None.

Definition is_at_least_n_history {ora: RandomOracle} (n: nat) (h: RandomHistory): Prop :=
  forall n', n' < n -> h n' <> None.

Lemma fin_history_fin {ora: RandomOracle}: forall l, is_fin_history (fin_history l).
Proof.
  intros.
  exists (length l).
  simpl.
  rewrite nth_error_None_iff; auto.
Qed.

Lemma inf_history_inf {ora: RandomOracle}: forall f, is_inf_history (inf_history f).
Proof.
  intros; hnf; intros.
  simpl.
  congruence.
Qed.

Definition prefix_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  forall n, h1 n = None \/ h1 n = h2 n.

Definition strict_prefix_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  prefix_history h1 h2 /\ exists n, h1 n <> h2 n.

Definition n_bounded_prefix_history {ora: RandomOracle} (m: nat) (h1 h2: RandomHistory): Prop :=
  forall n, (h1 n = None /\ h2 (n + m) = None) \/ h1 n = h2 n.

Definition n_conflict_history {ora: RandomOracle} (n: nat) (h1 h2: RandomHistory): Prop :=
  match h1 n, h2 n with
  | Some a1, Some a2 => projT1 a1 <> projT1 a2
  | Some _, None => True
  | None, Some _ => True
  | None, None => False
  end.

Definition conflict_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  exists n, history_coincide n h1 h2 /\ n_conflict_history n h1 h2.

Definition strict_conflict_history {ora: RandomOracle} (h1 h2: RandomHistory): Prop :=
  exists n,
    history_coincide n h1 h2 /\
    match h1 n, h2 n with
    | Some a1, Some a2 => projT1 a1 <> projT1 a2
    | _, _ => False
    end.

Lemma history_coincide_sym {ora: RandomOracle}: forall h1 h2 n,
  history_coincide n h1 h2 ->
  history_coincide n h2 h1.
Proof.
  intros.
  hnf; intros.
  specialize (H m H0); congruence.
Qed.

Lemma n_conflict_history_sym {ora: RandomOracle}: forall h1 h2 n,
  n_conflict_history n h1 h2 ->
  n_conflict_history n h2 h1.
Proof.
  intros.
  unfold n_conflict_history in *.
  destruct (h1 n), (h2 n); auto.
Qed.

Lemma conflict_history_sym {ora: RandomOracle}: forall h1 h2,
  conflict_history h1 h2 ->
  conflict_history h2 h1.
Proof.
  unfold conflict_history; intros.
  destruct H as [n [? ?]].
  exists n; split.
  + apply history_coincide_sym; auto.
  + hnf in H0 |- *; destruct (h1 n), (h2 n); auto.
Qed.

Lemma strict_conflict_history_sym {ora: RandomOracle}: forall h1 h2,
  strict_conflict_history h1 h2 ->
  strict_conflict_history h2 h1.
Proof.
  intros.
  destruct H as [n [? ?]].
  exists n; split; [apply history_coincide_sym; auto |].
  destruct (h1 n), (h2 n); auto.
Qed.

Lemma history_coincide_trans {ora: RandomOracle}: forall h1 h2 h3 n,
  history_coincide n h1 h2 ->
  history_coincide n h2 h3 ->
  history_coincide n h1 h3.
Proof.
  intros.
  hnf; intros.
  specialize (H m H1);
  specialize (H0 m H1); congruence.
Qed.

Lemma is_0_history_non_conflict {ora: RandomOracle}: forall h1 h2,
  is_n_history 0 h1 ->
  is_n_history 0 h2 ->
  conflict_history h1 h2 ->
  False.
Proof.
  intros.
  destruct H1 as [n [? ?]].
  destruct H as [? _], H0 as [? _].
  hnf in H2.
  rewrite (history_sound1 h1 0 n) in H2 by (auto; omega).
  rewrite (history_sound1 h2 0 n) in H2 by (auto; omega).
  auto.
Qed.

Lemma fstn_history_Some {ora: RandomOracle}: forall n m h, m < n -> (fstn_history n h) m = h m.
Proof.
  intros; simpl.
  destruct (le_lt_dec n m); auto; omega.
Qed.

Lemma fstn_history_None {ora: RandomOracle}: forall n m h, n <= m -> (fstn_history n h) m = None.
Proof.
  intros; simpl.
  destruct (le_lt_dec n m); auto; omega.
Qed.

Lemma history_coincide_weaken {ora: RandomOracle}: forall n m h1 h2,
  n <= m ->
  history_coincide m h1 h2 ->
  history_coincide n h1 h2.
Proof.
  intros.
  intros n0 ?.
  apply H0.
  omega.
Qed.

Lemma is_n_history_None {ora: RandomOracle}: forall n m h, n <= m -> is_n_history n h -> h m = None.
Proof.
  intros.
  destruct H0.
  apply (history_sound1 h n m); auto.
Qed.

Lemma fstn_history_is_n_history {ora: RandomOracle}: forall n m h,
  m <= n ->
  is_n_history n h ->
  is_n_history m (fstn_history m h).
Proof.
  intros.
  destruct H0.
  split.
  + rewrite fstn_history_None by auto; auto.
  + intros.
    rewrite fstn_history_Some by omega.
    apply H1; omega.
Qed.

Lemma fstn_history_coincide {ora: RandomOracle}: forall n h,
  history_coincide n h (fstn_history n h).
Proof.
  intros.
  intros m ?.
  rewrite fstn_history_Some by omega.
  auto.
Qed.

Lemma prefix_history_refl {ora: RandomOracle}: forall h, prefix_history h h.
Proof.
  intros.
  hnf; intros.
  right; auto.
Qed.

Lemma prefix_history_trans {ora: RandomOracle}: forall h1 h2 h3, prefix_history h1 h2 -> prefix_history h2 h3 -> prefix_history h1 h3.
Proof.
  intros.
  hnf in H, H0 |- *; intros.
  specialize (H n); specialize (H0 n).
  destruct H, H0.
  + left; auto.
  + left; auto.
  + left; congruence.
  + right; congruence.
Qed.

Lemma prefix_history_anti_sym {ora: RandomOracle}: forall h1 h2, prefix_history h1 h2 -> prefix_history h2 h1 -> h1 = h2.
Proof.
  intros.
  history_extensionality n.
  hnf; intros.
  specialize (H n); specialize (H0 n).
  destruct H, H0; congruence.
Qed.

Lemma prefix_history_comparable {ora: RandomOracle}: forall h1 h2 h, prefix_history h1 h -> prefix_history h2 h -> prefix_history h1 h2 \/ prefix_history h2 h1.
Proof.
  intros.
  destruct (classic (exists n, h1 n <> h2 n /\ h1 n <> None)); [right | left].
  + hnf; intros.
    destruct H1 as [m [? ?]].
    destruct (H0 n); [auto |].
    destruct (H n); [| right; congruence].
    assert (m < n).
    Focus 1. {
      destruct (le_dec n m); try omega.
      exfalso; apply H2.
      eapply history_sound1; eauto.
    } Unfocus.
    destruct (H m); [congruence |].
    destruct (H0 m); [| congruence].
    left.
    apply history_sound1 with m; auto. omega.
  + hnf; intros n.
    destruct (classic (h1 n = None)), (classic (h1 n = h2 n)); try tauto.
    exfalso.
    apply H1.
    eexists; eauto.
Qed.

Lemma conflict_history_strict_conflict {ora: RandomOracle}: forall h h',
  is_inf_history h ->
  conflict_history h' h ->
  prefix_history h' h \/ strict_conflict_history h' h.
Proof.
  intros.
  destruct H0 as [n [? ?]].
  hnf in H1.
  specialize (H n).
  destruct (h n) eqn:?H; [| congruence].
  destruct (h' n) eqn:?H.
  + right.
    exists n.
    split; auto.
    rewrite H2, H3; auto.
  + left.
    hnf; intros.
    destruct (le_lt_dec n n0).
    - left.
      apply (history_sound1 h' n n0); auto.
    - right.
      apply H0; auto.
Qed.

Lemma fstn_history_finite {ora: RandomOracle}: forall n h, is_fin_history (fstn_history n h).
Proof.
  intros.
  exists n.
  rewrite fstn_history_None; auto.
Qed.

Lemma fstn_history_prefix {ora: RandomOracle}: forall n h, prefix_history (fstn_history n h) h.
Proof.
  intros.
  hnf; intros m.
  destruct (le_dec n m).
  + rewrite fstn_history_None; auto.
  + rewrite fstn_history_Some; auto.
    omega.
Qed.

Lemma n_conflict_at_least_n_history1 {ora: RandomOracle}: forall n h1 h2,
  history_coincide n h1 h2 ->
  n_conflict_history n h1 h2 ->
  is_at_least_n_history n h1.
Proof.
  intros.
  intros m ? ?.
  pose proof H2.
  rewrite H in H2 by auto.
  unfold n_conflict_history in H0.
  rewrite (history_sound1 h1 m n) in H0 by (auto; omega).
  rewrite (history_sound1 h2 m n) in H0 by (auto; omega).
  auto.
Qed.

Lemma n_conflict_at_least_n_history2 {ora: RandomOracle}: forall n h1 h2,
  history_coincide n h1 h2 ->
  n_conflict_history n h1 h2 ->
  is_at_least_n_history n h2.
Proof.
  intros.
  intros m ? ?.
  pose proof H2.
  rewrite <- H in H2 by auto.
  unfold n_conflict_history in H0.
  rewrite (history_sound1 h1 m n) in H0 by (auto; omega).
  rewrite (history_sound1 h2 m n) in H0 by (auto; omega).
  auto.
Qed.

Lemma prefix_history_coincide {ora: RandomOracle}: forall n h1 h2,
  prefix_history h1 h2 ->
  is_at_least_n_history n h1 ->
  history_coincide n h1 h2.
Proof.
  intros.
  hnf; intros.
  specialize (H m).
  specialize (H0 m H1).
  tauto.
Qed.

Lemma is_at_least_n_history_fstn_history {ora: RandomOracle}: forall n m h, n <= m -> (is_at_least_n_history n (fstn_history m h) <-> is_at_least_n_history n h).
Proof.
  intros.
  split; intros; hnf; intros.
  + specialize (H0 n' H1).
    rewrite fstn_history_Some in H0 by omega.
    auto.
  + specialize (H0 n' H1).
    rewrite fstn_history_Some by omega.
    auto.
Qed.

Lemma n_conflict_proper_aux_right {ora: RandomOracle}: forall n h1 h2 h3,
  history_coincide (S n) h2 h3 ->
  (history_coincide n h1 h2 /\ n_conflict_history n h1 h2 <->
   history_coincide n h1 h3 /\ n_conflict_history n h1 h3).
Proof.
  intros.
  pose proof history_coincide_weaken n (S n) h2 h3 (le_n_Sn _) H.
  assert (history_coincide n h1 h2 <-> history_coincide n h1 h3).
  Focus 1. {
    split; intros; [apply history_coincide_trans with h2 | apply history_coincide_trans with h3]; auto.
    apply history_coincide_sym; auto.
  } Unfocus.
  assert (n_conflict_history n h1 h2 <-> n_conflict_history n h1 h3).
  Focus 1. {
    unfold n_conflict_history.
    specialize (H n (le_refl _)).
    rewrite H; reflexivity.
  } Unfocus.
  tauto.
Qed.

Lemma n_conflict_proper_aux_left {ora: RandomOracle}: forall n h1 h2 h3,
  history_coincide (S n) h2 h3 ->
  (history_coincide n h2 h1 /\ n_conflict_history n h2 h1 <->
   history_coincide n h3 h1 /\ n_conflict_history n h3 h1).
Proof.
  intros.
  pose proof n_conflict_proper_aux_right n h1 h2 h3 H.
  pose proof history_coincide_sym h1 h2 n.
  pose proof history_coincide_sym h2 h1 n.
  pose proof history_coincide_sym h1 h3 n.
  pose proof history_coincide_sym h3 h1 n.
  pose proof n_conflict_history_sym h1 h2 n.
  pose proof n_conflict_history_sym h2 h1 n.
  pose proof n_conflict_history_sym h1 h3 n.
  pose proof n_conflict_history_sym h3 h1 n.
  tauto.
Qed.

Lemma n_conflict_proper_aux {ora: RandomOracle}: forall n l1 l2 r1 r2,
  history_coincide (S n) l1 l2 ->
  history_coincide (S n) r1 r2 ->
  (history_coincide n l1 r1 /\ n_conflict_history n l1 r1 <->
   history_coincide n l2 r2 /\ n_conflict_history n l2 r2).
Proof.
  intros.
  rewrite (n_conflict_proper_aux_left n r1 l1 l2 H).
  apply n_conflict_proper_aux_right; auto.
Qed.

Lemma squeeze_history_coincide {ora: RandomOracle}: forall n h1 h2,
  prefix_history (fstn_history n h1) h2 ->
  prefix_history h2 h1 ->
  history_coincide n h1 h2.
Proof.
  intros.
  hnf; intros.
  specialize (H m).
  specialize (H0 m).
  rewrite fstn_history_Some in H by auto.
  destruct H, H0; congruence.
Qed.


Lemma strict_conflict_prefix_conflict_left {ora: RandomOracle}: forall h h1 h2,
  strict_conflict_history h2 h ->
  prefix_history h1 h2 ->
  conflict_history h1 h.
Proof.
  intros.
  destruct H as [n [? ?]].
  destruct (h1 n) eqn:?H.
  + exists n.
    split.
    - apply history_coincide_trans with h2; auto.
      hnf; intros.
      specialize (H0 m).
      destruct H0; auto.
      apply (history_sound1 h1 m n) in H0; [| omega].
      congruence.
    - unfold n_conflict_history.
      specialize (H0 n).
      destruct H0; [congruence |].
      rewrite H2 in H0 |- *.
      rewrite <- H0 in H1.
      destruct (h n); auto.
  + pose proof dec_inh_nat_subset_has_unique_least_element (fun n => h1 n = None) (fun n => classic (_ n)) (ex_intro _ n H2).
    destruct H3 as [m [[? ?] _]].
    exists m.
    split.
    - apply history_coincide_trans with h2; [| apply history_coincide_weaken with n; auto].
      hnf; intros.
      specialize (H0 m0); specialize (H4 m0).
      destruct H0; auto.
      apply H4 in H0.
      omega.
    - unfold n_conflict_history.
      rewrite H3.
      specialize (H4 _ H2).
      destruct (h m) eqn:?H; auto.
      apply (history_sound1 h m n H4) in H5.
      rewrite H5 in H1; destruct (h2 n); auto.
Qed.

Lemma strict_conflict_prefix_conflict_right {ora: RandomOracle}: forall h h1 h2,
  strict_conflict_history h h2 ->
  prefix_history h1 h2 ->
  conflict_history h h1.
Proof.
  intros.
  apply strict_conflict_history_sym in H.
  apply conflict_history_sym.
  eapply strict_conflict_prefix_conflict_left; eauto.
Qed.

Lemma strict_conflict_prefix_left {ora: RandomOracle}: forall h h1 h2,
  strict_conflict_history h2 h ->
  prefix_history h1 h2 ->
  prefix_history h1 h \/ strict_conflict_history h1 h.
Proof.
  intros.
  destruct H as [n [? ?]].
  destruct (h1 n) eqn:?H; [right | left].
  + exists n.
    split.
    - apply history_coincide_trans with h2; auto.
      hnf; intros.
      specialize (H0 m).
      destruct H0; auto.
      apply (history_sound1 h1 m n) in H0; [| omega].
      congruence.
    - unfold n_conflict_history.
      specialize (H0 n).
      destruct H0; [congruence |].
      rewrite H2 in H0 |- *.
      rewrite <- H0 in H1.
      destruct (h n); auto.
  + pose proof dec_inh_nat_subset_has_unique_least_element (fun n => h1 n = None) (fun n => classic (_ n)) (ex_intro _ n H2).
    destruct H3 as [m [[? ?] _]].
    hnf; intros.
    destruct (le_dec m n0).
    - left; apply (history_sound1 h1 m n0 l); auto.
    - right.
      assert (h1 n0 <> None) by (destruct (h1 n0) eqn:?H; [| specialize (H4 _ H5)]; congruence).
      specialize (H0 n0); destruct H0; [congruence |].
      rewrite H0.
      apply H.
      destruct (le_dec n n0); [| omega].
      exfalso.
      apply H5.
      apply (history_sound1 h1 n n0 l); auto.
Qed.

Lemma strict_conflict_prefix_right {ora: RandomOracle}: forall h h1 h2,
  strict_conflict_history h h2 ->
  prefix_history h1 h2 ->
  prefix_history h1 h \/ strict_conflict_history h h1.
Proof.
  intros.
  apply strict_conflict_history_sym in H.
  pose proof (strict_conflict_prefix_left _ _ _ H H0).
  destruct H1; auto.
  apply strict_conflict_history_sym in H1; auto.
Qed.

(* TODO: put this in lib *)
Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.

Definition history_set_consi {ora: RandomOracle} (P: RandomHistory -> Prop) : Prop :=
  forall h1 h2,
    conflict_history h1 h2 ->
    P h1 ->
    P h2 ->
    False.

Class LegalHistoryAntiChain {ora: RandomOracle} (d: RandomHistory -> Prop) : Prop := {
  rand_consi: history_set_consi d
}.

Record HistoryAntiChain {ora: RandomOracle}: Type := {
  raw_anti_chain: RandomHistory -> Prop;
  raw_anti_chain_legal: LegalHistoryAntiChain raw_anti_chain
}.

Definition in_anti_chain {ora: RandomOracle} (d: HistoryAntiChain) (h: RandomHistory): Prop := raw_anti_chain d h.

Coercion in_anti_chain: HistoryAntiChain >-> Funclass.

Definition history_in_anti_chain{ora: RandomOracle} (d: HistoryAntiChain) : Type := {h: RandomHistory | d h}.

Coercion history_in_anti_chain: HistoryAntiChain >-> Sortclass.

Definition history_in_anti_chain_history {ora: RandomOracle} (d: HistoryAntiChain) : history_in_anti_chain d -> RandomHistory := @proj1_sig _ _.

Coercion history_in_anti_chain_history: history_in_anti_chain >-> RandomHistory.

Lemma LegalHistoryAntiChain_Included {ora: RandomOracle}: forall (d1 d2: RandomHistory -> Prop), (forall h, d1 h -> d2 h) -> LegalHistoryAntiChain d2 -> LegalHistoryAntiChain d1.
Proof.
  intros.
  destruct H0 as [?H].
  constructor.
  hnf; intros.
  specialize (H0 h1 h2).
  auto.
Qed.

(*
Definition join {ora: RandomOracle} {A: Type} (v1 v2 v: RandomVariable A): Prop :=
  forall h, (v1 h = None /\ v2 h = v h) \/ (v2 h = None /\ v1 h = v h).

Definition Forall_RandomHistory {ora: RandomOracle} {A: Type} (P: A -> Prop) (v: RandomVariable A): Prop :=
  forall h,
    match v h with
    | None => True
    | Some a => P a
    end.
*)

Definition singleton_history_anti_chain {ora: RandomOracle} (h: RandomHistory): HistoryAntiChain.
  exists (fun h' => forall n, h n = h' n).
  constructor.
  hnf; intros; simpl in *.
  destruct H as [n [? ?]].
  specialize (H0 n).
  specialize (H1 n).
  hnf in H2.
  destruct (h n); rewrite <- H0, <- H1 in H2; auto.
Defined.

Definition unit_space_anti_chain {ora: RandomOracle}: HistoryAntiChain := singleton_history_anti_chain (fin_history nil).

Definition filter_anti_chain {ora: RandomOracle} (filter: RandomHistory -> Prop) (d: HistoryAntiChain): HistoryAntiChain.
  exists (fun h => d h /\ filter h).
  constructor.
  destruct d as [d [H]].
  hnf; simpl; intros.
  apply (H h1 h2 H0); tauto.
Defined.

Definition covered_by {ora: RandomOracle} (h: RandomHistory) (d: HistoryAntiChain): Prop :=
  exists h', prefix_history h' h /\ d h'.

Definition n_bounded_covered_by {ora: RandomOracle} (n: nat) (h: RandomHistory) (d: HistoryAntiChain): Prop :=
  exists h', n_bounded_prefix_history n h' h -> d h'.

Definition future_anti_chain {ora: RandomOracle} (present future: HistoryAntiChain): Prop :=
  forall h, future h -> covered_by h present.

Definition n_bounded_future_anti_chain {ora: RandomOracle} (n: nat) (present future: HistoryAntiChain): Prop :=
  forall h, future h -> n_bounded_covered_by n h present.

Definition bounded_future_anti_chain {ora: RandomOracle} (present future: HistoryAntiChain): Prop :=
  exists n, n_bounded_future_anti_chain n present future.

Definition same_covered_anti_chain {ora: RandomOracle} (d1 d2: HistoryAntiChain): Prop :=
  forall h, is_inf_history h ->
    ((exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ d1 h') <->
     (exists h', (prefix_history h' h \/ strict_conflict_history h' h) /\ d2 h')).

Lemma anti_chain_not_comparable {ora: RandomOracle}: forall (d: HistoryAntiChain) h1 h2,
  d h1 ->
  d h2 ->
  prefix_history h1 h2 ->
  h1 = h2.
Proof.
  intros.
  pose proof (fun HH  => @rand_consi _ _ (raw_anti_chain_legal d) h1 h2 HH H H0).
  clear H H0.
  destruct (classic (exists n, h1 n <> h2 n)).
  + pose proof dec_inh_nat_subset_has_unique_least_element (fun n => h1 n <> h2 n) (fun n => classic (_ n)) H.
    hnf in H0.
    destruct H0 as [n [[? ?] _]].
    exfalso; apply H2; clear H2.
    exists n; split.
    - hnf; intros.
      specialize (H3 m).
      destruct (classic (h1 m = h2 m)); auto.
      apply H3 in H4; omega.
    - destruct (H1 n); [| congruence].
      unfold n_conflict_history.
      rewrite H2.
      destruct (h2 n); auto; congruence.
  + history_extensionality n.
    destruct (classic (h1 n = h2 n)); auto; exfalso.
    apply H; exists n; auto.
Qed.

Instance same_covered_eq {ora: RandomOracle}: Equivalence same_covered_anti_chain.
Proof.
  constructor.
  + hnf; intros.
    hnf; intros.
    reflexivity.
  + hnf; intros.
    unfold same_covered_anti_chain in *; intros.
    specialize (H h H0); tauto.
  + hnf; intros.
    unfold same_covered_anti_chain in *; intros.
    specialize (H h H1); specialize (H0 h H1); tauto.
Qed.

Lemma future_anti_chain_refl {ora: RandomOracle}: forall d,
  future_anti_chain d d.
Proof.
  intros.
  unfold future_anti_chain.
  intros.
  exists h.
  split; auto.
  apply prefix_history_refl.
Qed.

Lemma future_anti_chain_trans {ora: RandomOracle}: forall d1 d2 d3,
  future_anti_chain d1 d2 ->
  future_anti_chain d2 d3 ->
  future_anti_chain d1 d3.
Proof.
  unfold future_anti_chain.
  intros.
  rename h into h3.
  destruct (H0 h3 H1) as [h2 [? ?]].
  destruct (H h2 H3) as [h1 [? ?]].
  exists h1.
  split; auto.
  apply prefix_history_trans with h2; auto.
Qed.

Lemma proj_in_anti_chain_unique {ora: RandomOracle}: forall (d: HistoryAntiChain) h1 h2 h3,
  prefix_history h1 h3 ->
  prefix_history h2 h3 ->
  covered_by h2 d ->
  d h1 ->
  prefix_history h1 h2.
Proof.
  intros.
  pose proof prefix_history_comparable _ _ _ H H0.
  destruct H3; auto.
  destruct H1 as [h1' [? ?]].
  pose proof prefix_history_trans _ _ _ H1 H3.
  pose proof anti_chain_not_comparable _ _ _ H4 H2 H5.
  rewrite <- H6; auto.
Qed.

Lemma same_covered_future_anti_chain_spec {ora: RandomOracle}: forall d1 d2,
  same_covered_anti_chain d1 d2 ->
  future_anti_chain d1 d2 ->
  forall h1, d1 h1 -> exists h2, prefix_history h1 h2 /\ d2 h2.
Proof.
  intros.
  set (h := inf_history (fun n => match h1 n with Some qa => qa | None => existT _ ro_default_question ro_default_answer end)).
  pose proof proj1 (H h (inf_history_inf _)).
  assert (prefix_history h1 h).
  Focus 1. {
    hnf; intros.
    subst h; simpl.
    destruct (h1 n); auto.
  } Unfocus.
  assert (exists h' : RandomHistory, (prefix_history h' h \/ strict_conflict_history h' h) /\ d1 h').
  + clear H2.
    exists h1.
    split; [left |]; auto.
  + specialize (H2 H4); clear H4.
    destruct H2 as [h2 [? ?]].
    exists h2; split; [| auto].
    destruct (H0 h2 H4) as [h1' [? ?]].
    destruct H2.
    - apply (proj_in_anti_chain_unique d1 h1 h2 h); auto.
    - pose proof strict_conflict_prefix_right h2 h1 h H2 H3.
      destruct H7; auto.
      pose proof strict_conflict_prefix_conflict_left h1 h1' h2 H7 H5.
      pose proof @rand_consi _ _ (raw_anti_chain_legal d1) _ _ H8 H6 H1.
      inversion  H9.
Qed.

Require RndHoare.axiom. Import RndHoare.axiom.NatChoice.

Fixpoint app_fin_inf {ora: RandomOracle} (l: list RandomQA) (f: nat -> RandomQA) :=
  match l with
  | nil => f
  | qa :: l0 => fun n =>
                match n with
                | 0 => qa
                | S m => app_fin_inf l0 f m
                end
  end.

Lemma app_fin_inf_list {ora: RandomOracle}: forall l h m, m < length l -> Some (app_fin_inf l h m) = nth_error l m.
Proof.
  intros.
  revert l H; induction m; intros; simpl.
  + destruct l; [simpl in H; omega |].
    simpl; auto.
  + destruct l; [simpl in H; omega |].
    simpl.
    apply IHm.
    simpl in H; omega.
Qed.

Lemma app_fin_inf_fun {ora: RandomOracle}: forall l h m, length l <= m -> app_fin_inf l h m = h (m - length l).
Proof.
  intros.
  revert m H; induction l; intros; simpl.
  + f_equal; omega.
  + destruct m; [simpl in H; omega |].
    rewrite IHl by (simpl in H; omega).
    f_equal.
Qed.

(* These three lemmas are copied from veric/assert_lemmas.v and veric/initial_world.v *)
Lemma nth_error_in_bounds: forall {A} (l: list A) i, (O <= i < length l)%nat
  -> exists x, nth_error l i = value x.
Proof.
intros until i; intros H.
revert i l H.
induction i; destruct l; intros; simpl in *;
  try solve [eauto | omega].
apply IHi; omega.
Qed.

Lemma nth_error_app: forall {T} (al bl : list T) (j: nat),
     nth_error (al++bl) (length al + j) = nth_error bl j.
Proof.
 intros. induction al; simpl; auto.
Qed.

Lemma nth_error_app1: forall {T} (al bl : list T) (j: nat),
     (j < length al)%nat ->
     nth_error (al++bl) j = nth_error al j.
Proof.
  intros. revert al H; induction j; destruct al; simpl; intros; auto; try omega.
   apply IHj. omega.
Qed.

Lemma length_firstn_list_from_fun: forall {A} (f: nat -> A) n, length (fisrtn_list_from_fun f n) = n.
Proof.
  intros.
  induction n; simpl; auto.
  rewrite app_length, IHn.
  simpl.
  omega.
Qed.

Lemma nth_error_firstn_list_from_fun: forall {A} (f: nat -> A) n m, m < n -> nth_error (fisrtn_list_from_fun f n) m = Some (f m).
Proof.
  intros.
  revert m H; induction n; intros; simpl.
  + omega.
  + destruct (le_dec n m).
    - assert (n = m) by omega; subst.
      replace m with (length (fisrtn_list_from_fun f m) + 0) at 3 by (rewrite length_firstn_list_from_fun; omega).
      rewrite nth_error_app.
      simpl; auto.
    - rewrite nth_error_app1 by (rewrite length_firstn_list_from_fun; omega).
      apply IHn; omega.
Qed.

Lemma fstn_app_inf_fin {ora: RandomOracle}: forall l h n,
  n >= length l ->
  fstn_history n (inf_history (app_fin_inf l h)) = fin_history (l ++ fisrtn_list_from_fun h (n - length l)).
Proof.
  intros.
  history_extensionality m.
  destruct (le_dec n m).
  + rewrite fstn_history_None by auto.
    simpl.
    symmetry.
    apply nth_error_None_iff.
    rewrite app_length.
    rewrite length_firstn_list_from_fun.
    omega.
  + rewrite fstn_history_Some by omega.
    simpl.
    destruct (le_dec (length l) m).
    - rewrite app_fin_inf_fun by auto.
      replace m with (length l + (m - length l)) at 2 by omega.
      rewrite nth_error_app.
      rewrite nth_error_firstn_list_from_fun by omega.
      auto.
    - rewrite nth_error_app1 by omega.
      rewrite app_fin_inf_list by omega.
      auto.
Qed.

Lemma inf_history_construction {ora: RandomOracle}: forall (P: RandomHistory -> Prop) (init: list RandomQA),
  P (fin_history init) ->
  (forall l, P (fin_history l) -> exists qa, P (fin_history (l ++ qa :: nil))) ->
  exists h, is_inf_history h /\ forall n, n >= length init -> P (fstn_history n h).
Proof.
  intros.
  pose (Q := fun l => P (fin_history (init ++ l))).
  destruct (nat_stepwise_choice Q) as [h ?].
  + hnf.
    rewrite app_nil_r; auto.
  + subst Q; simpl; intros.
    specialize (H0 _ H1).
    destruct H0 as [qa ?]; exists qa.
    rewrite app_assoc.
    auto.
  + exists (inf_history (app_fin_inf init h)).
    split; [apply inf_history_inf |].
    intros.
    specialize (H1 (n - length init)).
    unfold Q in H1.
    rewrite fstn_app_inf_fin by auto.
    auto.
Qed.
