Require Import Coq.omega.Omega.
Require Import Coq.Lists.List.

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

