Require Import Coq.Lists.List.
Require Import Coq.omega.Omega.

Fixpoint delete_nth {A} (n: nat) (xs: list A) {struct n} : list A :=
 match n, xs with
 | O, y::ys => ys
 | S n', y::ys =>y :: delete_nth n' ys
 | _ , _ => nil
 end.

Inductive find_nth_preds_rec {A: Type} (pred: A -> Prop): nat -> list A -> option (nat * A) -> Prop :=
| find_nth_preds_rec_cons_head: forall n R0 R, pred R0 -> find_nth_preds_rec pred n (R0 :: R) (Some (n, R0))
| find_nth_preds_rec_cons_tail: forall n R0 R R_res, find_nth_preds_rec pred (S n) R R_res -> find_nth_preds_rec pred n (R0 :: R) R_res
| find_nth_preds_rec_nil: forall n, find_nth_preds_rec pred n nil None.

Inductive find_nth_preds {A: Type} (pred: A -> Prop): list A -> option (nat * A) -> Prop :=
| find_nth_preds_constr: forall R R_res, find_nth_preds_rec pred 0 R R_res -> find_nth_preds pred R R_res.

Lemma find_nth_preds_Some: forall {A: Type} (pred: A -> Prop) R n R0, find_nth_preds pred R (Some (n, R0)) ->
  nth_error R n = Some R0 /\ pred R0.
Proof.
  intros.
  inversion H; subst; clear H.
  replace n with (n - 0)%nat by omega.
  assert ((n >= 0)%nat /\ nth_error R (n - 0) = Some R0 /\ pred R0); [| tauto].
  revert H0; generalize 0%nat as m; intros.
  remember (Some (n, R0)) as R_res eqn:?H in H0.
  induction H0.
  + inversion H; subst; clear H.
    replace (n - n)%nat with 0%nat by omega.
    simpl; auto.
  + apply IHfind_nth_preds_rec in H.
    destruct H as [? [? ?]].
    replace (n - n0)%nat with (S (n - S n0)) by omega.
    split; [omega |].
    simpl; auto.
  + inversion H.
Qed.

(* Current not used. *)
Lemma find_nth_preds_rec_S: forall {A: Type} (pred: A -> Prop) z R n Rn,
  find_nth_preds_rec pred z R (Some (n, Rn)) ->
  find_nth_preds_rec pred (S z) R (Some (S n, Rn)).
Proof.
  intros.
  remember (Some (n, Rn)) as Res eqn:?H.
  revert n Rn H0; induction H; intros.
  + inversion H0; subst; clear H0.
    eapply find_nth_preds_rec_cons_head; eauto.
  + subst R_res.
    apply find_nth_preds_rec_cons_tail; auto.
  + inversion H0.
Qed.

(* Current not used. *)
Lemma find_nth_preds_rec_delete_nth: forall {A: Type} (pred: A -> Prop) z m R Rn,
  (exists n, find_nth_preds_rec pred z (delete_nth m R) (Some (n, Rn))) ->
  (exists n, find_nth_preds_rec pred z R (Some (n, Rn))).
Proof.
  intros.
  revert z R H; induction m; intros; destruct R; auto.
  + simpl in *.
    destruct H as [n ?].
    eexists.
    eapply find_nth_preds_rec_cons_tail.
    apply find_nth_preds_rec_S.
    exact H.
  + simpl in *.
    destruct H as [n ?].
    inversion H; subst; clear H.
    - eexists; apply find_nth_preds_rec_cons_head; auto.
    - specialize (IHm (S z) _ (ex_intro _ _ H4)).
      clear n H4; destruct IHm as [n ?].
      exists n.
      apply find_nth_preds_rec_cons_tail; auto.
Qed.

(* Current not used. *)
Lemma find_nth_preds_delete_nth: forall {A: Type} (pred: A -> Prop) m R Rn,
  (exists n, find_nth_preds pred (delete_nth m R) (Some (n, Rn))) ->
  (exists n, find_nth_preds pred R (Some (n, Rn))).
Proof.
  intros ? ? ? ? ? [n ?].
  inversion H; subst; clear H.
  pose proof (ex_intro _ n H0): exists n, find_nth_preds_rec pred 0 (delete_nth m R) (Some (n, Rn)).
  apply find_nth_preds_rec_delete_nth in H.
  clear n H0.
  destruct H as [n ?].
  exists n.
  apply find_nth_preds_constr; auto.
Qed.

Ltac find_nth_rec tac :=
  first [ simple eapply find_nth_preds_rec_cons_head; tac
        | simple eapply find_nth_preds_rec_cons_tail; find_nth_rec tac
        | simple eapply find_nth_preds_rec_nil].

Ltac find_nth tac :=
  eapply find_nth_preds_constr; find_nth_rec tac.
(* The reason to use "eapply" instead of "simple eapply" is because "find_nth" may be buried in definitions. *)
