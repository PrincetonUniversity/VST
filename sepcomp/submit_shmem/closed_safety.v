Require Import sepcomp.compcert. Import CompcertLibraries.

Require Import sepcomp.core_semantics.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section closed_safety.

Variable (G C D Z M : Type).

Variable sem : CoreSemantics G C M.

Variable ge : G.

Fixpoint safeN (n : nat) (c : C) (m : M) : Prop :=
  match n with
    | O => True
    | S n' =>
      match halted sem c with
        | None =>
          exists c', exists m',
            corestep sem ge c m c' m' /\
            safeN n' c' m'
        | Some i => True
      end
  end.

Lemma safe_downward1 n c m : safeN (S n) c m -> safeN n c m.
Proof.
revert c m; induction n; simpl; intros; auto.
destruct (halted sem c); auto.
destruct H as [c' [m' [? ?]]].
exists c', m'; split; auto.
Qed.

Lemma safe_downward (n n' : nat) c m :
  le n' n -> safeN n c m -> safeN n' c m.
Proof.
do 2 intro. revert c m H0. induction H; auto.
intros. apply IHle. apply safe_downward1. auto.
Qed.

Lemma safe_corestep_forward c m c' m' n :
  corestep_fun sem ->
  corestep sem ge c m c' m' -> safeN (S n) c m ->
  safeN n c' m'.
Proof.
simpl; intros.
erewrite corestep_not_halted in H1; eauto.
destruct H1 as [c'' [m'' [? ?]]].
assert ((c',m') = (c'',m'')).
destruct (H _ _ _ _ _ _ _ H0 H1).
subst; auto.
inv H3; auto.
Qed.

Lemma safe_corestepN_forward c m c' m' n n0 :
  corestep_fun sem ->
  corestepN sem ge n0 c m c' m' ->
  safeN (n + S n0) c m -> safeN n c' m'.
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

Lemma safe_corestep_backward c m c' m' n :
  corestep sem ge c m c' m' ->
  safeN (n - 1) c' m' ->
  safeN n c m.
Proof.
simpl; intros.
induction n; simpl; auto.
erewrite corestep_not_halted; eauto.
exists c', m'; split; auto.
assert (Heq: (n = S n - 1)%nat) by omega.
rewrite Heq; auto.
Qed.

Lemma safe_corestepN_backward c m c' m' n n0 :
  corestepN sem ge n0 c m c' m' ->
  safeN (n - n0) c' m' ->
  safeN n c m.
Proof.
simpl; intros.
revert c m c' m' n H H0.
induction n0; intros; auto.
simpl in H; inv H.
solve[assert (Heq: (n = n - 0)%nat) by omega; rewrite Heq; auto].
simpl in H. destruct H as [c2 [m2 [STEP STEPN]]].
assert (H: safeN (n - 1 - n0) c' m').
eapply safe_downward in H0; eauto. omega.
specialize (IHn0 _ _ _ _ (n - 1)%nat STEPN H).
eapply safe_corestep_backward; eauto.
Qed.

End closed_safety.
