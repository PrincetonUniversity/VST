Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.

Local Open Scope logic.

Section RAMIFICATION.

Context {CS: compspecs}.
Context (Espec: OracleKind).

Lemma semax_ramification: forall Delta G L s L' G',
  closed_wrt_modvars s (L' -* G') ->
  G |-- L * (L' -* G') ->
  semax Delta L s (normal_ret_assert L') ->
    semax Delta G s (normal_ret_assert G').
Proof.
  intros.
  apply semax_pre_post with (P' := L * (L' -* G')) (R' := normal_ret_assert (L' * (L' -* G'))). 
  + intros.
    apply andp_left2; auto.
  + intros.
    apply andp_left2.
    unfold normal_ret_assert.
    apply andp_derives; [auto |].
    apply andp_derives; [auto |].
    rewrite sepcon_comm, wand_sepcon_adjoint; auto.
  + apply semax_frame with (F := L' -* G') in H1; [| auto].
    rewrite frame_normal in H1.
    auto.
Qed.

Lemma corable_local: forall P, corable (local P).
Proof.
  intros.
  simpl; intros.
  unfold local, lift1.
  apply corable_prop.
Qed.

Lemma semax_ramification_P: forall Delta G L s PureLocal PureFrame L' G',
  closed_wrt_modvars s (local PureFrame) ->
  closed_wrt_modvars s (L' -* G') ->
  G |-- local PureFrame && (L * (L' -* G')) ->
  semax Delta L s (normal_ret_assert (local PureLocal && L')) ->
  semax Delta G s (normal_ret_assert (local PureFrame && local PureLocal && G')).
Proof.
  intros.
  apply semax_pre_post with
    (P' := L * (local PureFrame && (L' -* G')))
    (R' := normal_ret_assert (local PureLocal && L' * (local PureFrame && (L' -* G')))). 
  + intros.
    apply andp_left2.
    rewrite corable_sepcon_andp1 by (apply corable_local).
    auto.
  + intros.
    apply andp_left2.
    unfold normal_ret_assert.
    apply andp_derives; [auto |].
    apply andp_derives; [auto |].
    rewrite corable_sepcon_andp1, corable_andp_sepcon1, <- andp_assoc by (apply corable_local).
    apply andp_derives; [auto |].
    rewrite sepcon_comm, wand_sepcon_adjoint; auto.
  + apply semax_frame with (F := local PureFrame && (L' -* G')) in H2; [| auto with closed].
    rewrite frame_normal in H2.
    auto.
Qed.

Lemma semax_ramification_Q: forall A Delta G L s L' G',
  (forall x, closed_wrt_modvars s (L' x -* G' x)) ->
  G |-- L * (ALL x: A, L' x -* G' x) ->
  semax Delta L s (normal_ret_assert (EX x: A, L' x)) ->
    semax Delta G s (normal_ret_assert (EX x: A, G' x)).
Proof.
  intros.
  apply semax_pre_post with
   (P' := L * (ALL x: A, L' x -* G' x))
   (R' := normal_ret_assert ((EX x: A, L' x) * (ALL x: A, L' x -* G' x))). 
  + intros.
    apply andp_left2; auto.
  + intros.
    apply andp_left2.
    unfold normal_ret_assert.
    apply andp_derives; [auto |].
    apply andp_derives; [auto |].
    rewrite exp_sepcon1.
    apply exp_left; intro x; apply (exp_right x).
    rewrite sepcon_comm, wand_sepcon_adjoint.
    apply (allp_left _ x); auto.
  + apply semax_frame with (F := (ALL  x : A , L' x -* G' x)) in H1; [| auto with closed].
    rewrite frame_normal in H1.
    auto.
Qed.

Lemma semax_ramification_PQ: forall A Delta G L s PureLocal PureFrame L' G',
  closed_wrt_modvars s (local PureFrame) ->
  (forall x, closed_wrt_modvars s (L' x -* G' x)) ->
  G |-- local PureFrame && (L * (ALL x: A, L' x -* G' x)) ->
  semax Delta L s (normal_ret_assert (EX x :A, local (PureLocal x) && L' x)) ->
  semax Delta G s (normal_ret_assert (local PureFrame && (EX x: A, local (PureLocal x) && G' x))).
Proof.
  intros.
  apply semax_pre_post with
    (P' := L * (local PureFrame && ALL x: A, (L' x -* G' x)))
    (R' := normal_ret_assert ((EX x: A, local (PureLocal x) && (L' x)) *
                              (local PureFrame && (ALL x: A, (L' x -* G' x))))). 
  + intros.
    apply andp_left2.
    rewrite corable_sepcon_andp1 by (apply corable_local).
    auto.
  + intros.
    apply andp_left2.
    unfold normal_ret_assert.
    apply andp_derives; [auto |].
    apply andp_derives; [auto |].
    rewrite exp_sepcon1, exp_andp2.
    apply exp_left; intro x; apply (exp_right x).
    rewrite corable_sepcon_andp1, corable_andp_sepcon1 by (apply corable_local).
    apply andp_derives; [auto |].
    apply andp_derives; [auto |].
    rewrite sepcon_comm, wand_sepcon_adjoint; auto.
    apply (allp_left _ x); auto.
  + apply semax_frame with (F := local PureFrame && (ALL x: A, L' x -* G' x)) in H2; [| auto with closed].
    rewrite frame_normal in H2.
    auto.
Qed.

End RAMIFICATION.
