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
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.lifting_expr.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.

Local Open Scope nat_scope.

Section extensions.
Context `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty} {CS: compspecs}.

Lemma tc_test_eq1:
  forall b i v m,
  mem_auth m ∗ denote_tc_test_eq (Vptr b i) v ⊢
  ⌜Mem.weak_valid_pointer m b (Ptrofs.unsigned i) = true⌝.
Proof.
intros; iIntros "[Hm H]".
destruct v; try done; simpl.
- iDestruct "H" as "[% H]".
  iApply (valid_pointer.weak_valid_pointer_dry with "[$Hm $H]").
- unfold test_eq_ptrs.
  destruct (sameblock (Vptr b i) (Vptr b0 i0)).
  + iDestruct "H" as "[H _]".
    iApply (valid_pointer.weak_valid_pointer_dry with "[$Hm $H]").
  + iDestruct "H" as "[H _]".
    iDestruct (valid_pointer.valid_pointer_dry with "[$Hm $H]") as %?; iPureIntro.
    apply valid_pointer_implies.
    rewrite Z.add_0_r // in H.
Qed.

Lemma semax_ifthenelse:
   forall E Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     semax OK_spec E Delta (P ∧ local (expr_true b)) c R ->
     semax OK_spec E Delta (P ∧ local (expr_false b)) d R ->
     semax OK_spec E Delta
              (▷ (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) ∧ P))
              (Sifthenelse b c d) R.
Proof.
  intros.
  rewrite !semax_unfold in H0, H1 |- *.
  intros; iIntros "E ? #?" (? (TC' & ?)) "P".
  rewrite monPred_at_later monPred_at_and.
  destruct HGG.
  iApply wp_if.
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; eauto).
  pose proof (typecheck_environ_sub _ _ TS _ TC') as TC.
  iDestruct (add_and _ (▷ ⌜_⌝) with "P") as "(P & >%HTCb)".
  { iIntros "(H & _) !>". iPoseProof (typecheck_expr_sound with "H") as "%"; done. }
  iApply (wp_tc_expr(CS := CS) with "E"); [done..|].
  iSplit.
  { rewrite /= denote_tc_assert_andp bi.and_elim_l bi.and_elim_r; auto. }
  iIntros "E" (?) "!>"; iSplit.
  { simpl.
    destruct (eval_expr b rho) eqn: Hb; try done.
    rewrite denote_tc_assert_andp /= !bi.and_elim_l.
    destruct (typeof b); try done.
    * by destruct f0.
    * rewrite denote_tc_assert_andp binop_lemmas2.denote_tc_assert_test_eq' /= bi.and_elim_r.
      unfold_lift; rewrite Hb /=.
      simple_if_tac; last by rewrite embed_pure; iDestruct "P" as "[]".
      by iDestruct "P" as "(_ & ?)".
    * rewrite embed_pure; iDestruct "P" as "[]".
    * rewrite embed_pure; iDestruct "P" as "[]". }
  simpl in HTCb; super_unfold_lift; rewrite /eval_unop /= in HTCb.
  destruct (bool_val (typeof b) (eval_expr b rho)) as [b'|] eqn: Hb; last done.
  iExists b'; iSplit; first done.
  rewrite bi.and_elim_r.
  destruct b'; [iApply (H0 _ Delta' with "E [$]") | iApply (H1 _ Delta' with "E [$]")]; eauto;
    rewrite monPred_at_and; (iSplit; first done); iPureIntro; by apply bool_val_strict.
Qed.

Lemma semax_seq:
  forall E Delta (R: ret_assert) P Q h t,
  semax OK_spec E Delta P h (overridePost Q R) ->
  semax OK_spec E Delta Q t R ->
  semax OK_spec E Delta P (Clight.Ssequence h t) R.
Proof.
  intros.
  rewrite !semax_unfold in H,H0|-*.
  intros.
  iIntros "E ? #B" (? (TC' & ?)) "P".
  iApply wp_seq.
  iApply wp_strong_mono.
  iSplitL ""; last by iApply (H with "E [$]").
  simpl.
  iSplit; last by auto.
  iIntros "((% & ? & % & E) & ?)".
  by iApply (H0 with "E [$]").
Qed.

Lemma semax_loop:
forall E Delta Q Q' incr body R,
     semax OK_spec E Delta Q body (loop1_ret_assert Q' R) ->
     semax OK_spec E Delta Q' incr (loop2_ret_assert Q R) ->
     semax OK_spec E Delta Q (Sloop body incr) R.
Proof.
  intros ?????? POST H H0.
  rewrite !semax_unfold in H H0 |- *.
  intros ?????.
  iLöb as "IH".
  iIntros "% E ? #B" (? (TC' & ?)) "Q".
  iApply wp_loop.
  iNext.
  iApply wp_strong_mono.
  iSplitL ""; last by iApply (H with "E [$]").
  simpl.
  iAssert ((∃ x0 : environ, ⎡ Q' x0 ⎤ ∗ <affine> ⌜typecheck_environ Delta' x0⌝ ∗
    curr_env psi x0) ∗ ⎡ funassert Delta' ⎤ ={E}=∗
   wp OK_spec psi E f incr
   (Clight_seplog.loop2_ret_assert
      (wp OK_spec psi E f (Sloop body incr)
         (Clight_seplog.frame_ret_assert (env_ret_assert Delta' psi POST)
            ⎡ funassert Delta' ⎤))
      (Clight_seplog.frame_ret_assert (env_ret_assert Delta' psi POST)
         ⎡ funassert Delta' ⎤)))%I as "?"; last auto.
  iIntros "((% & ? & % & E) & ?) !>".
  iApply wp_strong_mono.
  iSplitL ""; last by iApply (H0 with "E [$]").
  simpl; iSplit.
  - iIntros "((% & ? & % & E) & ?) !>".
    by iApply ("IH" with "E [$]").
  - iSplit; first auto.
    iSplit; last auto.
    iIntros "((% & F & ?) & ?)".
    rewrite monPred_at_pure embed_pure; iDestruct "F" as "[]".
Qed.

Lemma semax_break:
   forall E Delta Q,        semax OK_spec E Delta (RA_break Q) Sbreak Q.
Proof.
  intros.
  rewrite semax_unfold; intros.
  iIntros "???" (? (? & ?)) "?".
  iApply wp_break; by iFrame.
Qed.

Lemma semax_continue:
   forall E Delta Q,        semax OK_spec E Delta (RA_continue Q) Scontinue Q.
Proof.
  intros.
  rewrite semax_unfold; intros.
  iIntros "???" (? (? & ?)) "?".
  iApply wp_continue; by iFrame.
Qed.

End extensions.
