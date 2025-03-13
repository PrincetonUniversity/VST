Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.res_predicates.
Require Import VST.veric.external_state.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.lifting_expr.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.

Section mpred.

Context `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty}.

Lemma closed_wrt_modvars_switch:
  forall a sl n F,
  closed_wrt_modvars(Σ:=Σ) (Sswitch a sl) F ->
  closed_wrt_modvars (seq_of_labeled_statement (select_switch n sl)) F.
Proof.
unfold closed_wrt_modvars, modifiedvars.
intros.
intros rho te' H0; apply H.
intros; specialize (H0 i).
destruct H0; auto;left.
clear - H0.
simpl in *.
forget idset0 as s.
assert (isSome (modifiedvars' (seq_of_labeled_statement sl) s !! i)). {
  unfold select_switch in *.
  destruct (select_switch_case n sl) eqn:?.
 *
  revert l Heqo s H0; induction sl; intros. inv Heqo.
  simpl. simpl in Heqo. destruct o. destruct (zeq z n).
  inv Heqo; subst. simpl in H0. auto.
  specialize (IHsl _ Heqo _ H0).
  rewrite modifiedvars'_union; right; auto.
  rewrite modifiedvars'_union; right; eauto.
 *
  revert sl Heqo s H0; induction sl; intros.
  simpl in *. auto.
  simpl in Heqo, H0|- *.
  destruct o.
  destruct (zeq z n). inv Heqo.
  rewrite modifiedvars'_union; right; eauto.
  simpl in H0. auto.
}
 clear - H.
 revert s H; induction sl; simpl; intros; auto.
 rewrite -> modifiedvars'_union in H|-*.
 destruct H;[left|right]; auto.
Qed.

Context {CS : compspecs}.

Lemma semax_switch:
  forall E Delta (Q: assert) a sl R
     (Ht : is_int_type (typeof a) = true)
     (Htc : Q ⊢ tc_expr Delta a)
     (Hcase : forall n,
     semax OK_spec E Delta (local (fun rho => eval_expr a rho = Vint n) ∧ Q)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)),
     semax OK_spec E Delta Q (Sswitch a sl) R.
Proof.
  intros.
  rewrite semax_unfold.
  intros; iIntros "??" (?? (TC' & ?)) "E ?".
  destruct HGG. assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  iApply wp_switch.
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  iApply (wp_tc_expr(CS := CS) with "E"); [done..|].
  iSplit; first by rewrite Htc.
  iIntros "E" (He).
  destruct (typeof a) eqn: Hty; try discriminate; rewrite /sem_switch_arg /=.
  destruct (eval_expr a rho) eqn: Ha; try contradiction.
  iExists _; iSplit; first done.
  specialize (Hcase i0); rewrite semax_unfold in Hcase.
  iApply wp_conseq; last (by iApply (Hcase _ Delta' with "[$] [$] [//] E"); try done;
    rewrite monPred_at_and /=; iFrame; auto); simpl; auto.
  iIntros "((% & F & ?) & ?)".
  rewrite monPred_at_pure embed_pure; iDestruct "F" as "[]".
Qed.

End mpred.
