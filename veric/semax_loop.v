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
Require Import VST.veric.semax_conseq.
Require Import VST.veric.Clight_lemmas.

Local Open Scope nat_scope.

Section extensions.
Context `{!heapGS Σ} {Espec: OracleKind} `{!externalGS OK_ty Σ} {CS: compspecs}.

Lemma tc_test_eq1:
  forall b i v m,
  mem_auth m ∗ denote_tc_test_eq (Vptr b i) v ⊢
  ⌜Mem.weak_valid_pointer m b (Ptrofs.unsigned i) = true⌝.
Proof.
intros; iIntros "[Hm H]".
destruct v; try done; simpl.
- iDestruct "H" as "[% H]".
  iApply (binop_lemmas4.weak_valid_pointer_dry with "[$Hm $H]").
- unfold test_eq_ptrs.
  destruct (sameblock (Vptr b i) (Vptr b0 i0)).
  + iDestruct "H" as "[H _]".
    iApply (binop_lemmas4.weak_valid_pointer_dry with "[$Hm $H]").
  + iDestruct "H" as "[H _]".
    iDestruct (binop_lemmas4.valid_pointer_dry with "[$Hm $H]") as %?; iPureIntro.
    apply valid_pointer_implies.
    rewrite Z.add_0_r // in H.
Qed.

Lemma semax_ifthenelse:
   forall E Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     semax Espec E Delta (P ∧ local (expr_true b)) c R ->
     semax Espec E Delta (P ∧ local (expr_false b)) d R ->
     semax Espec E Delta
              (▷ (tc_expr Delta (Eunop Cop.Onotbool b (Tint I32 Signed noattr)) ∧ P))
              (Sifthenelse b c d) R.
Proof.
  intros.
  rewrite !semax_unfold in H0, H1 |- *.
  intros.
  iIntros "#Prog_OK" (???) "[%Hclosed #rguard]".
  iPoseProof (H0 with "Prog_OK [rguard]") as "H0".
  { iIntros "!>"; iFrame "rguard"; iPureIntro.
    unfold closed_wrt_modvars, closed_wrt_vars in *; intros ?? Hi; apply Hclosed.
    intros i; specialize (Hi i); rewrite modifiedvars_Sifthenelse; tauto. }
  iPoseProof (H1 with "Prog_OK [rguard]") as "H1".
  { iIntros "!>"; iFrame "rguard"; iPureIntro.
    unfold closed_wrt_modvars, closed_wrt_vars in *; intros ?? Hi; apply Hclosed.
    intros i; specialize (Hi i); rewrite modifiedvars_Sifthenelse; tauto. }
  iIntros (tx vx) "!> H".
  iIntros (??).
  iApply jsafe_step.
  iIntros (m) "[Hm ?]".
  monPred.unseal.
  iDestruct "H" as "(%TC & (F & P) & fun)".
  unfold expr_true, expr_false, Cnot, lift1 in *.
  set (rho := construct_rho _ _ _) in *.
  assert (typecheck_environ Delta rho) as TYCON_ENV
    by (destruct TC as [TC' TC'']; eapply typecheck_environ_sub; eauto).
  rewrite (add_and (▷ _) (▷ _)); last by iIntros "[H _]"; iApply (typecheck_expr_sound with "H").
  iDestruct "P" as "[P >%HTCb]".
  assert (cenv_sub (@cenv_cs CS) psi) by (eapply cenv_sub_trans; destruct HGG; auto).
  iCombine "Hm P" as "H"; rewrite (add_and (mem_auth m ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & H & _)"; iApply (eval_expr_relate(CS := CS) with "[$Hm $H]").
  iDestruct "H" as "(H & >%Heval)".
  rewrite /tc_expr /typecheck_expr /= denote_tc_assert_andp; fold (typecheck_expr(CS := CS)).
  rewrite -assoc (bi.and_elim_r (denote_tc_assert _ _)).
  rewrite (add_and (mem_auth m ∗ _) (▷_)); last by iIntros "H"; iNext; iDestruct "H" as "(Hm & H & _)"; iApply (eval_expr_relate(CS := CS) with "[$Hm $H]").
  iDestruct "H" as "(H & >%Hb)".
  inv Heval.
  eapply eval_expr_fun in Hb; last done; subst.
  rewrite typecheck_expr_sound; last done.
  rewrite bi.later_and.
  iDestruct "H" as "(Hm & >%TC2 & P)"; simpl in HTCb.
  unfold liftx, lift, eval_unop in HTCb; simpl in HTCb.
  destruct (bool_val (typeof b) (eval_expr b rho)) as [b'|] eqn: Hb; [|contradiction].
  iAssert (▷assert_safe Espec psi E f vx tx (Cont (Kseq (if b' then c else d) k)) rho) with "[F P fun]" as "Hsafe".
  { iNext; destruct b'; [iApply "H0" | iApply "H1"]; (iSplit; first done); iFrame; iPureIntro; split; auto; split; auto;
      apply bool_val_strict; auto. }
  simpl in *; unfold Cop.sem_notbool in *.
  destruct (Cop.bool_val _ _ _) eqn: Hbool_val; inv H9.
  super_unfold_lift.
  iIntros "!>"; iExists _, _; iSplit.
  - iPureIntro; eapply step_ifthenelse; eauto.
  - iFrame; iNext.
    eapply bool_val_Cop in Hbool_val; eauto; subst.
    by iApply assert_safe_jsafe.
  - inv H4.
Qed.

(*Ltac inv_safe H :=
  inv H;
  try solve[match goal with
    | H : semantics.at_external _ _ _ = _ |- _ =>
      simpl in H; congruence
    | H : j_at_external _ _ _ = _ |- _ =>
      simpl in H; congruence
    | H : semantics.halted _ _ _ |- _ =>
      simpl in H; unfold cl_halted in H; contradiction
  end].*)

Lemma semax_seq:
  forall E Delta (R: ret_assert) P Q h t,
  semax Espec E Delta P h (overridePost Q R) ->
  semax Espec E Delta Q t R ->
  semax Espec E Delta P (Clight.Ssequence h t) R.
Proof.
  intros.
  rewrite !semax_unfold in H,H0|-*.
  intros.
  iIntros "#Prog_OK" (???) "[%Hclosed #rguard]".
  iPoseProof (H with "Prog_OK") as "H".
  iPoseProof (H0 with "Prog_OK [rguard]") as "H0".
  { iIntros "!>"; iFrame "rguard"; iPureIntro.
    unfold closed_wrt_modvars, closed_wrt_vars in *; intros ?? Hi; apply Hclosed.
    intros i; specialize (Hi i); rewrite modifiedvars_Ssequence; tauto. }
  iSpecialize ("H" $! (Kseq t k) F with "[H0]"); last by iApply (guard_safe_adj' with "H");
    intros; iIntros "H"; iApply (jsafe_local_step with "H"); constructor.
  iIntros "!>"; iSplit.
  { iPureIntro; unfold closed_wrt_modvars, closed_wrt_vars in *; intros ?? Hi; apply Hclosed.
    intros i; specialize (Hi i); rewrite modifiedvars_Ssequence; tauto. }
  iIntros (????) "!> H".
  rewrite proj_frame.
  destruct (eq_dec ek EK_normal).
  - subst; rewrite /proj_ret_assert.
    monPred.unseal; iDestruct "H" as "(% & (? & [% ?]) & ?)"; subst; destruct R; simpl.
    iApply "H0"; by iFrame.
  - replace (exit_cont ek vl (Kseq t k)) with (exit_cont ek vl k)
      by (destruct ek; simpl; congruence).
    iApply "rguard".
    monPred.unseal; rewrite (bi.sep_comm (F _)).
    destruct R, ek; simpl; monPred.unseal; rewrite ?pure_and_sep_assoc //.
Qed.

Lemma semax_loop:
forall E Delta Q Q' incr body R,
     semax Espec E Delta Q body (loop1_ret_assert Q' R) ->
     semax Espec E Delta Q' incr (loop2_ret_assert Q R) ->
     semax Espec E Delta Q (Sloop body incr) R.
Proof.
  intros ?????? POST H H0.
  rewrite semax_unfold.
  intros ?????.
  iLöb as "IH".
  iIntros "#Prog_OK" (???) "[%Hclosed #rguard]".
  iIntros (??) "!> H".
  iIntros (??).
  set (rho := construct_rho _ _ _).
  iApply jsafe_step; rewrite /jstep_ex.
  iIntros (?) "? !>".
  iExists (State f body (Kloop1 body incr k) vx tx), _; iSplit; first by iPureIntro; constructor.
  iFrame; iNext.
  iApply assert_safe_jsafe.
  rewrite semax_unfold in H.
  iApply (H with "Prog_OK"); last done.
  iIntros "!>"; iSplit.
  { iPureIntro; unfold closed_wrt_modvars, closed_wrt_vars in *; intros ?? Hi; apply Hclosed.
    intros i; specialize (Hi i); rewrite modifiedvars_Sloop; tauto. }
  iIntros (??).
  rewrite semax_unfold in H0.
  iPoseProof (H0 with "Prog_OK") as "H0".
  iSpecialize ("IH" with "Prog_OK").
  assert (closed_wrt_modvars incr F).
  { unfold closed_wrt_modvars, closed_wrt_vars in *; intros ?? Hi; apply Hclosed.
    intros i; specialize (Hi i); rewrite modifiedvars_Sloop; tauto. }
  iAssert (guard' Espec psi E Delta' f (F ∗ Q') (Kseq incr (Kloop2 body incr k))) as "#Hincr".
  { iApply "H0".
    iIntros "!>"; iSplit; first done.
    iIntros (ek2 vl2 tx2 vx2) "!>"; rewrite /loop2_ret_assert proj_frame.
    destruct ek2; simpl proj_ret_assert; simpl exit_cont; monPred.unseal.
    * iIntros "(% & (? & % & ?) & ?)"; subst.
      iApply ("IH" $! _ F); last by destruct POST; iFrame.
      iIntros "!>"; iSplit; done.
    * iIntros "(% & (? & % & ?) & ?)"; subst.
      destruct POST; iApply ("rguard" $! EK_normal None); simpl; monPred.unseal; by iFrame.
    * destruct POST; simpl.
      iIntros "(% & (? & % & []) & ?)".
    * destruct POST; simpl.
      iIntros "(% & (? & ?) & ?)".
      iApply ("rguard" $! EK_return); simpl; monPred.unseal; by iFrame. }
  iIntros (??) "!>".
  destruct ek.
  + rewrite proj_frame; simpl proj_ret_assert; monPred.unseal; iIntros "(% & (? & % & ?) & ?)"; subst.
    iApply (assert_safe_adj _ _ _ _ _ (Kseq incr (Kloop2 body incr k)) (Kseq _ _)); last by iApply "Hincr"; destruct POST; iFrame.
    intros ?????; iIntros "H"; iApply (jsafe_local_step with "H"); constructor; auto.
  + simpl proj_ret_assert; monPred.unseal; iIntros "(% & (% & ?) & ?)"; rewrite /loop1_ret_assert.
    destruct POST; iApply ("rguard" $! EK_normal None); simpl; monPred.unseal; by iFrame.
  + simpl exit_cont; simpl proj_ret_assert; monPred.unseal.
    iIntros "(% & (% & H) & ?)".
    iApply "Hincr".
    by destruct POST; simpl frame_ret_assert; monPred.unseal; iDestruct "H" as "[$ $]"; iFrame.
  + destruct POST; iApply ("rguard" $! EK_return); by iFrame.
Qed.

Lemma semax_break:
   forall E Delta Q,        semax Espec E Delta (RA_break Q) Sbreak Q.
Proof.
  intros.
  rewrite semax_unfold; intros.
  iIntros "#Prog_OK" (???) "[%Hclosed #rguard]".
  iIntros (??) "!> H".
  iSpecialize ("rguard" $! EK_break None tx vx with "[H]").
  { simpl.
    rewrite (bi.pure_True (None = None)) // bi.True_and; destruct Q; simpl.
    monPred.unseal; by rewrite (bi.sep_comm (RA_break _)). }
  iIntros (? H); iSpecialize ("rguard" $! _ H).
  simpl exit_cont; destruct (break_cont k) eqn: Hcont.
  { iMod "rguard" as "[]". }
  2: { exfalso; clear - Hcont. revert k c Hcont; induction k; simpl; intros; try discriminate. eauto. }
  destruct c; try iMod "rguard" as "[]".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] rguard"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iNext.
      iApply (convergent_controls_jsafe with "rguard"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iNext.
      iApply (convergent_controls_jsafe with "rguard"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iNext.
      iApply (convergent_controls_jsafe with "rguard"); simpl; try congruence.
      by inversion 1; constructor.
  - rename c into k'.
    iInduction k as [| s' | s1 s2 | s1 s2 | |] "IHk" forall (s k' Hcont); try discriminate.
    + iApply jsafe_local_step.
      { constructor. }
      by iApply ("IHk" with "[%] rguard").
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      iApply "rguard".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      iApply "rguard".
    + inv Hcont.
      iApply jsafe_local_step.
      { intros; apply step_skip_break_switch; auto. }
      iApply jsafe_local_step.
      { apply step_skip_seq. }
      iApply "rguard".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] rguard"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iApply "rguard".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iApply "rguard".
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iApply "rguard".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] rguard"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      iApply "rguard".
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      iApply "rguard".
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iApply jsafe_local_step.
      { apply step_skip_loop2. }
      iApply "rguard".
  - iInduction k as [| | | | |] "IHk"; try discriminate.
    + iApply jsafe_local_step; last by iApply ("IHk" with "[%] rguard"). constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop1. }
      iNext.
      iApply (convergent_controls_jsafe with "rguard"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { apply step_break_loop2. }
      iNext.
      iApply (convergent_controls_jsafe with "rguard"); simpl; try congruence.
      by inversion 1; constructor.
    + inv Hcont.
      iApply jsafe_local_step.
      { constructor; auto. }
      iNext.
      iApply (convergent_controls_jsafe with "rguard"); simpl; try congruence.
      by inversion 1; constructor.
Qed.

Lemma semax_continue:
   forall E Delta Q,        semax Espec E Delta (RA_continue Q) Scontinue Q.
Proof.
  intros.
  rewrite semax_unfold; intros.
  iIntros "#Prog_OK" (???) "[%Hclosed #rguard]".
  iSpecialize ("rguard" $! EK_continue None); simpl.
  iIntros (??) "!>".
  monPred.unseal; iIntros "(% & (? & ?) & ?)"; iSpecialize ("rguard" with "[-]").
  { destruct Q; simpl; monPred.unseal; by iFrame. }
  iIntros (? Heq); iSpecialize ("rguard" $! _ Heq).
  destruct (continue_cont k) eqn:Hcont; try iMod "rguard" as "[]".
  - rename c into k'.
    assert (exists s c, k' = Kseq s c) as (? & ? & Hcase).
    { induction k; inv Hcont; eauto. }
    rewrite Hcase.
    iInduction k as [| | | | |] "IHk" forall (k' Hcont Hcase); try discriminate.
    + iApply jsafe_local_step.
      { constructor. }
      iApply ("IHk" with "[%] [%] rguard"); eauto.
    + inv Hcont. inv H1.
      iApply jsafe_local_step.
      { intros; apply step_skip_or_continue_loop1; auto. }
      iApply "rguard".
    + iApply jsafe_local_step.
      { apply step_continue_switch. }
      iApply ("IHk" with "[%] [%] rguard"); eauto.
  - exfalso; clear - Hcont.
    revert c o Hcont; induction k; simpl; intros; try discriminate; eauto.
Qed.

End extensions.
