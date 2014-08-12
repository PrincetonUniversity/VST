Require Import compcert. Import CompcertLibraries.

Require Import core_semantics.
Require Import core_semantics_lemmas.

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
          (exists c', exists m', corestep sem ge c m c' m') /\
          (forall c' m', corestep sem ge c m c' m' -> safeN n' c' m') 
        | Some i => True
      end
  end.

Lemma safe_downward1 n c m : safeN (S n) c m -> safeN n c m.
Proof.
revert c m; induction n; simpl; intros; auto.
destruct (halted sem c); auto.
destruct H as [H H0].
destruct H as [c' [m' H2]].
split. exists c', m'; auto.
intros c'' m'' H3. 
specialize (H0 _ _ H3). destruct n; auto.
Qed.

Lemma safe_downward (n n' : nat) c m :
  le n' n -> safeN n c m -> safeN n' c m.
Proof.
do 2 intro. revert c m H0. induction H; auto.
intros. apply IHle. apply safe_downward1. auto.
Qed.

Lemma safe_corestep_forward c m c' m' n :
  corestep sem ge c m c' m' -> safeN (S n) c m -> 
  safeN n c' m'.
Proof.
simpl; intros. 
generalize H as H'; intro.
eapply corestep_not_halted in H; rewrite H in H0.
destruct H0 as [H1 H2]. clear H H1.
apply H2; auto.
Qed.

Lemma safe_corestepN_forward c m c' m' n n0 :
  corestepN sem ge n0 c m c' m' -> 
  safeN (n + S n0) c m -> safeN n c' m'.
Proof.
intros.
revert c m c' m' n H H0.
induction n0; intros; auto.
simpl in H; inv H.
eapply safe_downward in H0; eauto. omega.
simpl in H. destruct H as [c2 [m2 [STEP STEPN]]].
eapply IHn0; eauto.
assert (Heq: (n + S (S n0) = S (n + S n0))%nat) by omega.
rewrite Heq in H0.
eapply safe_corestep_forward in H0; eauto.
Qed.

Lemma corestep_star_fun : 
  corestep_fun sem -> 
  forall c m c' m' c'' m'' n,
  corestepN sem ge n c m c' m' -> 
  corestepN sem ge n c m c'' m'' -> 
  c'=c'' /\ m'=m''.
Proof.
intro FUN. intros. revert c m H H0. induction n; auto.
simpl. intros ? ?. inversion 1; subst. inversion 1; subst. 
split; auto.
simpl.
intros c m H H2.
destruct H as [c2 [m2 [STEP STEPN]]].
destruct H2 as [c2' [m2' [STEP' STEPN']]].
assert (c2 = c2' /\ m2 = m2').
  unfold corestep_fun in FUN. eapply FUN; eauto.
inv H.
eapply IHn; eauto.
Qed.

End closed_safety.
