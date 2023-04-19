Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem (*VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops*).
Require Import VST.veric.res_predicates.
Require Import VST.veric.external_state.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_core.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.

Section mpred.

Context `{!heapGS Σ} {Espec: OracleKind} `{!externalGS OK_ty Σ}.

Lemma closed_wrt_modvars_switch:
  forall a sl n F,
  closed_wrt_modvars (Sswitch a sl) F ->
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
  revert l Heqo s H0; induction sl ;intros. inv Heqo.
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

Lemma tc_expr_sound {CS: compspecs}:
 forall Delta e rho, typecheck_environ Delta rho -> 
     tc_expr Delta e rho ⊢ ⌜tc_val (typeof e) (eval_expr e rho)⌝.
Proof.
  intros; eapply typecheck_expr_sound; eauto.
Qed.

Lemma switch_rguard:
 forall E
  (R : ret_assert)
  (psi : genv)
  (F : environ -> mpred)
  (f: function)
  (Delta' : tycontext)
  (k : cont),
 rguard Espec psi E Delta' f
        (frame_ret_assert R F) k ⊢
(rguard Espec psi E Delta' f
   (frame_ret_assert (switch_ret_assert R) F) 
   (Kswitch k)).
Proof.
  intros.
  unfold rguard.
  iIntros "#H" (????) "!>".
  pose (ek' := match ek with 
                    | EK_normal => EK_normal
                    | EK_break => EK_normal
                    | EK_continue => EK_continue
                    | EK_return => EK_return
                    end).
  pose (vl' := match ek with 
                    | EK_normal => None
                    | EK_break => None
                    | EK_continue => None
                    | EK_return => vl
                    end).
  iSpecialize ("H" $! ek' vl' tx vx).
  rewrite !proj_frame.
  iIntros "(? & (? & P) & ?)".
  destruct R, ek; subst ek' vl'; simpl proj_ret_assert; try (by iApply ("H" with "[$]")); iDestruct "P" as "(-> & ?)"; try done; by (iApply "H"; iFrame).
Qed.

Context {CS : compspecs}.

(*Lemma assert_safe_step_nostore:
  forall  psi f vx vx2 tx tx2 c1 k1 c2 k2 Delta e rho,
  (forall jm jm', age1 jm = Some jm' ->
    app_pred (tc_expr Delta e rho) (m_phi jm) ->
     cl_step psi (State f c1 k1 vx tx)
      (m_dry jm) (State f c2 k2 vx2 tx2) (m_dry jm)) ->
  assert_safe Espec psi f vx2 tx2 (Cont (Kseq c2 k2)) (construct_rho (filter_genv psi) vx2 tx2)
 && tc_expr Delta e rho
⊢ assert_safe Espec psi f vx tx (Cont (Kseq c1 k1)) (construct_rho (filter_genv psi) vx tx).
Proof.
intros. intros ? [Hw Hw'] ?? Hora ???; subst.
apply jm_fupd_intro'.
destruct (level (m_phi jm)) eqn:?; try lia. clear LW.
destruct (levelS_age1 _ _ Heqn) as [phi' Hage].
destruct (can_age1_juicy_mem _ _ Hage) as [jm' Hage'].
clear phi' Hage.
simpl.
econstructor 2 with (m' := jm').
econstructor.
rewrite <- (age_jm_dry Hage').
apply (H _ _ Hage'); auto.
split.
apply age1_resource_decay; assumption.
split; [apply age_level; assumption|].
apply age1_ghost_of, age_jm_phi; auto.
pose  proof (age_level _ _ Hage').
rewrite <- level_juice_level_phi in Heqn.
rewrite Heqn in H1.
inv H1. clear Heqn.
eapply pred_hereditary in Hw;
  [ | instantiate (1:= (m_phi jm')); apply age_jm_phi; auto].
apply assert_safe_jsafe; auto.
Qed.*)

Lemma semax_switch: 
  forall E Delta (Q: environ -> mpred) a sl R
     (Ht : is_int_type (typeof a) = true)
     (Htc : forall rho, Q rho ⊢ tc_expr Delta a rho)
     (Hcase : forall n,
     semax Espec E Delta (fun rho => ⌜eval_expr a rho = Vint n⌝ ∧ Q rho)
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)),
     semax Espec E Delta Q (Sswitch a sl) R.
Proof.
  intros.
  rewrite semax_unfold.
  iIntros (?????) "#Prog_OK".
  iIntros (???) "(%Hclosed & #rguard)".
  iIntros (??) "!> ((% & %) & (F & Q) & #?)".
  set (rho := construct_rho _ _ _).
  assert (typecheck_environ Delta rho) by (eapply typecheck_environ_sub; done).
  iAssert ⌜tc_val (typeof a) (eval_expr(CS := CS) a rho)⌝ as %?.
  { rewrite Htc tc_expr_sound //. }
  destruct (typeof a) eqn: Hta; try discriminate.
  destruct (eval_expr a rho) as [ | n | | | |] eqn:?;  try contradiction.
  specialize (Hcase n); rewrite semax_unfold in Hcase.
  iPoseProof (Hcase with "Prog_OK []") as "Hcase".
  { iIntros "!>"; iSplit; last by iApply switch_rguard.
    iPureIntro; eapply closed_wrt_modvars_switch with (n:= Int.unsigned n); eauto. }
  rewrite /guard' /_guard /assert_safe.
  iIntros (? _).
  iApply jsafe_step; rewrite /jstep_ex.
  iIntros (?) "(Hm & ?) !>".
  destruct HGG as [CSUB ?]; iDestruct (eval_expr_relate with "[$Hm Q]") as %?; first done.
  { subst rho; rewrite Htc tc_expr_cenv_sub //. }
  iExists _, _; iSplit.
  { iPureIntro; econstructor; try done.
    erewrite (eval_expr_cenv_sub_Vint CSUB) by done.
    rewrite Hta //. }
  iFrame.
  iApply ("Hcase" with "[-]"); last by iPureIntro.
  iFrame; auto.
Qed.

End mpred.
