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
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.

(* This file contains two parts:
   1. Proof of semax_conseq.
   2. Deriving simpler and older version of consequence rules from semax_conseq.
   3. semax_extract_pre, and proof of semax_adapt_frame rules from semax_conseq, and 2 specializations of semax_adapt_frame. *)

(* Part 1: Proof of semax_conseq *)

Global Instance local_absorbing `{!heapGS Σ} l : Absorbing (local l).
Proof.
  rewrite /local; apply monPred_absorbing, _.
Qed.

Global Instance local_persistent `{!heapGS Σ} l : Persistent (local l).
Proof.
  rewrite /local; apply monPred_persistent, _.
Qed.

Section mpred.

Context `{!VSTGS OK_ty Σ} {OK_spec : ext_spec OK_ty}.

Lemma _guard_mono: forall ge E Delta f (P Q: assert) k,
  (P ⊢ Q) ->
  _guard OK_spec ge E Delta f Q k ⊢ _guard OK_spec ge E Delta f P k.
Proof.
  intros.
  apply _guard_mono; auto.
  intros; apply H.
Qed.

Lemma guard_mono: forall ge E Delta f (P Q: assert) k,
  (P ⊢ Q) ->
  guard' OK_spec ge E Delta f Q k ⊢ guard' OK_spec ge E Delta f P k.
Proof.
  intros.
  apply _guard_mono; auto.
Qed.

Lemma rguard_mono: forall ge E Delta f (P Q: ret_assert) k,
  (forall rk vl, proj_ret_assert P rk vl ⊢ proj_ret_assert Q rk vl) ->
  rguard OK_spec ge E Delta f Q k ⊢ rguard OK_spec ge E Delta f P k.
Proof.
  intros.
  unfold rguard.
  iIntros "H" (??).
  rewrite -_guard_mono; eauto.
Qed.

Definition fupd_ret_assert E (Q: ret_assert): ret_assert :=
          {| RA_normal := |={E}=> RA_normal Q;
             RA_break := |={E}=> RA_break Q;
             RA_continue := |={E}=> RA_continue Q;
             RA_return := fun v => RA_return Q v |}.
(* Asymmetric consequence: since there's no CompCert step that
   corresponds to RA_return, we can't do an update there. We could
   probably add a bupd if we really want to, but it may not be
   necessary. *)

Lemma fupd_fupd_andp_prop : forall E P (Q : assert), (|={E}=> (⌜P⌝ ∧ |={E}=> Q)) ⊣⊢ (|={E}=> (⌜P⌝ ∧ Q)).
Proof.
  intros; iSplit; iIntros "H".
  - iMod "H" as "[$ $]".
  - iMod "H" as "[$ $]"; done.
Qed.

Lemma proj_fupd_ret_assert: forall E Q ek vl,
  (|={E}=> proj_ret_assert (fupd_ret_assert E Q) ek vl) ⊣⊢ (|={E}=> proj_ret_assert Q ek vl).
Proof.
  intros.
  destruct ek; rewrite // /=; apply fupd_fupd_andp_prop.
Qed.

(* After deep embedded hoare logic (SL_as_Logic) is ported, maybe the frame does not need to be
   quantified in the semantic definition of semax. *)

Lemma assert_safe_fupd':
  forall gx vx tx E (P: assert) Delta f k rho,
    match k with Ret _ _ => False | _ => True end ->
    let PP1 := ⌜guard_environ Delta f rho⌝ in
    let PP2 := funassert Delta rho in
    (PP1 ∧ P rho ∗ PP2 -∗ assert_safe OK_spec gx E f vx tx k rho) ⊣⊢
    (PP1 ∧ (|={E}=> P rho) ∗ PP2 -∗ assert_safe OK_spec gx E f vx tx k rho).
Proof.
  intros.
  iSplit.
  * iIntros "H (% & P & ?)".
    iApply assert_safe_fupd; first done; iMod "P"; iApply "H"; auto.
    by iFrame.
  * iIntros "H (% & P & ?)"; iApply "H"; auto.
    by iFrame.
Qed.

Lemma _guard_fupd':
  forall ge E Delta (P: assert) f k,
    match k with Ret _ _ => False | _ => True end ->
    _guard OK_spec ge E Delta f P k ⊣⊢ _guard OK_spec ge E Delta f (|={E}=> P) k.
Proof.
  intros.
  unfold _guard.
  apply bi.forall_proper; intros ?.
  apply bi.forall_proper; intros ?.
  rewrite assert_safe_fupd'; auto.
  by monPred.unseal.
Qed.

Lemma guard_fupd':
  forall ge E Delta f (P: assert) k,
    guard' OK_spec ge E Delta f P k ⊣⊢ guard' OK_spec ge E Delta f (|={E}=> P) k.
Proof.
  intros.
  apply _guard_fupd'; auto.
Qed.

Lemma exit_cont_nonret : forall ek vl k, ek <> EK_return ->
  match exit_cont ek vl k with Ret _ _ => False | _ => True end.
Proof.
  destruct ek; try contradiction; intros; simpl.
  - destruct vl; auto.
  - induction k; simpl; auto.
  - induction k; simpl; auto.
Qed.

Lemma rguard_fupd':
  forall ge E Delta f (P: ret_assert) k,
    rguard OK_spec ge E Delta f P k ⊣⊢ rguard OK_spec ge E Delta f (fupd_ret_assert E P) k.
Proof.
  intros.
  unfold rguard.
  apply bi.forall_proper; intros ek.
  apply bi.forall_proper; intros vl.
  destruct (eq_dec ek EK_return); subst; auto.
  rewrite _guard_fupd'; [|apply exit_cont_nonret; auto].
  setoid_rewrite _guard_fupd' at 2; [|apply exit_cont_nonret; auto].
  iSplit; iApply _guard_mono; intros; rewrite proj_fupd_ret_assert; auto.
Qed.

Lemma assert_safe_fupd:
  forall gx vx tx rho E (F P: assert) Delta f k,
    match k with Ret _ _ => False | _ => True end ->
    let PP1 := ⌜guard_environ Delta f rho⌝ in
    let PP2 := funassert Delta rho in
    (PP1 ∧ (F ∗ P) rho ∗ PP2 -∗
    assert_safe OK_spec gx E f vx tx k rho) ⊣⊢
    (PP1 ∧ (F ∗ |={E}=> P) rho ∗ PP2 -∗
    assert_safe OK_spec gx E f vx tx k rho).
Proof.
  intros.
  iSplit.
  * iIntros "H (% & P & ?)".
    rewrite (assert_safe_fupd' _ _ _ _ (F ∗ P)); last done.
    iApply "H"; iFrame "%"; iFrame.
    monPred.unseal; by iDestruct "P" as "($ & >$)".
  * iIntros "H (% & P & ?)"; iApply "H"; iFrame.
    iFrame "%"; monPred.unseal; by iDestruct "P" as "($ & $)".
Qed.

Lemma _guard_fupd:
  forall ge E Delta f (F P: assert) k,
    match k with Ret _ _ => False | _ => True end ->
    _guard OK_spec ge E Delta f (F ∗ P) k ⊣⊢ _guard OK_spec ge E Delta f (F ∗ |={E}=> P) k.
Proof.
  intros.
  unfold _guard.
  apply bi.forall_proper; intros ?.
  apply bi.forall_proper; intros ?.
  rewrite assert_safe_fupd; auto.
Qed.

Lemma guard_fupd:
  forall ge E Delta f (F P: assert) k,
    guard' OK_spec ge E Delta f (F ∗ P) k ⊣⊢ guard' OK_spec ge E Delta f (F ∗ |={E}=> P) k.
Proof.
  intros.
  apply _guard_fupd; auto.
Qed.

Lemma fupd_fupd_frame_l : forall E (P Q : assert), (|={E}=> (P ∗ |={E}=> Q)) ⊣⊢ |={E}=> (P ∗ Q).
Proof.
  intros; iSplit.
  - by iIntros ">[$ >$]".
  - by iIntros ">[$ $]".
Qed.

Lemma proj_fupd_ret_assert_frame: forall E F Q ek vl,
  (|={E}=> (F ∗ proj_ret_assert (fupd_ret_assert E Q) ek vl)) ⊣⊢ |={E}=> (F ∗ proj_ret_assert Q ek vl).
Proof.
  intros.
  destruct ek; simpl; auto;
    rewrite -fupd_fupd_frame_l fupd_fupd_andp_prop fupd_fupd_frame_l; auto.
Qed.

Global Instance guard_proper ge E Delta f : Proper (equiv ==> eq ==> equiv) (_guard OK_spec ge E Delta f).
Proof.
  intros ????? ->; rewrite /_guard.
  do 7 f_equiv.
  by rewrite H.
Qed.

Global Instance guard'_proper ge E Delta f : Proper (equiv ==> eq ==> equiv) (guard' OK_spec ge E Delta f).
Proof.
  solve_proper.
Qed.

Global Instance rguard_proper ge E Delta f : Proper (equiv ==> eq ==> equiv) (rguard OK_spec ge E Delta f).
Proof.
  intros ????? ->; rewrite /rguard.
  do 3 f_equiv; intros ?.
  apply guard_proper; last done.
  destruct H as (? & ? & ? & ?).
  destruct a; simpl; last done; f_equiv; done.
Qed.

Global Instance frame_ret_assert_proper : Proper (equiv ==> equiv ==> equiv) frame_ret_assert.
Proof.
  intros [????] [????] (? & ? & ? & ?); repeat intro; simpl in *.
  split3; last split; simpl; intros; f_equiv; done.
Qed.

Global Instance semax_proper {CS} E Delta : Proper (equiv ==> eq ==> equiv ==> iff) (semax(CS := CS) OK_spec E Delta).
Proof.
  repeat intro; subst.
  rewrite !semax_unfold.
  split; intros.
  - iIntros "#B" (????) "(% & ?)".
    rewrite -H; iApply (H0 with "B [-]"); [done..|].
    iApply (bi.affinely_mono with "[$]").
    rewrite H1; iIntros "$"; done.
  - iIntros "#B" (????) "(% & ?)".
    rewrite H; iApply (H0 with "B [-]"); [done..|].
    iApply (bi.affinely_mono with "[$]").
    rewrite H1; iIntros "$"; done.
Qed.

Lemma guard_proj_frame : forall ge E Delta f P F ek vl k,
  _guard OK_spec ge E Delta f (proj_ret_assert (frame_ret_assert P F) ek vl) k ⊣⊢
  _guard OK_spec ge E Delta f (F ∗ proj_ret_assert P ek vl) k.
Proof.
  intros. rewrite proj_frame //.
Qed.

Lemma rguard_fupd:
  forall ge E Delta F f (P: ret_assert) k,
    rguard OK_spec ge E Delta f (frame_ret_assert P F) k ⊣⊢ rguard OK_spec ge E Delta f (frame_ret_assert (fupd_ret_assert E P) F) k.
Proof.
  intros.
  unfold rguard.
  apply bi.forall_proper; intros ek.
  apply bi.forall_proper; intros vl.
  rewrite !guard_proj_frame.
  destruct (eq_dec ek EK_return); [subst; auto|].
  rewrite _guard_fupd'; [|apply exit_cont_nonret; auto].
  setoid_rewrite _guard_fupd' at 2; [|apply exit_cont_nonret; auto].
  iSplit; iApply _guard_mono; intros; rewrite proj_fupd_ret_assert_frame; auto.
Qed.

Lemma _guard_allp_fun_id:
  forall ge E Delta' Delta f (F P: assert) k,
    tycontext_sub Delta Delta' ->
    _guard OK_spec ge E Delta' f (F ∗ P) k ⊣⊢ _guard OK_spec ge E Delta' f (F ∗ (<affine> allp_fun_id Delta ∗ P)) k.
Proof.
  intros.
  unfold _guard.
  do 7 f_equiv.
  iSplit.
  * rewrite {1}funassert_allp_fun_id_sub //.
    monPred.unseal; rewrite monPred_at_affinely.
    iIntros "(($ & $) & ($ & $))".
  * monPred.unseal.
    iIntros "(($ & _ & $) & $)".
Qed.

Lemma guard_allp_fun_id: forall ge E Delta' Delta f (F P: assert) k,
  tycontext_sub Delta Delta' ->
  guard' OK_spec ge E Delta' f (F ∗ P) k ⊣⊢ guard' OK_spec ge E Delta' f (F ∗ (<affine> allp_fun_id Delta ∗ P)) k.
Proof.
  intros.
  apply _guard_allp_fun_id; auto.
Qed.

Lemma rguard_allp_fun_id: forall ge E Delta' Delta f (F: assert) P k,
  tycontext_sub Delta Delta' ->
  rguard OK_spec ge E Delta' f (frame_ret_assert P F) k ⊣⊢ rguard OK_spec ge E Delta' f (frame_ret_assert (frame_ret_assert P (<affine> allp_fun_id Delta)) F) k.
Proof.
  intros.
  unfold rguard.
  apply bi.forall_proper; intros ek.
  apply bi.forall_proper; intros vl.
  rewrite !guard_proj_frame.
  rewrite _guard_allp_fun_id; eauto.
  apply guard_proper; auto.
  by intros; rewrite proj_frame.
Qed.

Lemma _guard_tc_environ:
  forall ge E Delta' Delta f (F P: assert) k,
    tycontext_sub Delta Delta' ->
    _guard OK_spec ge E Delta' f (F ∗ P) k ⊣⊢
    _guard OK_spec ge E Delta' f (F ∗ (local (typecheck_environ Delta) ∧ P)) k.
Proof.
  intros.
  unfold _guard.
  do 6 f_equiv.
  iSplit.
  * monPred.unseal; iIntros "(%Henv & ($ & $) & $)"; iPureIntro.
    split3; last done; auto.
    eapply typecheck_environ_sub; eauto.
    destruct Henv as [? _]; auto.
  * monPred.unseal; iIntros "($ & ($ & [_ $]) & $)".
Qed.

Lemma guard_tc_environ: forall ge E Delta' Delta f (F P: assert) k,
  tycontext_sub Delta Delta' ->
  guard' OK_spec ge E Delta' f (F ∗ P) k ⊣⊢ guard' OK_spec ge E Delta' f (F ∗ (local (typecheck_environ Delta) ∧ P)) k.
Proof.
  intros.
  apply _guard_tc_environ; auto.
Qed.

Lemma rguard_tc_environ: forall ge E Delta' Delta f (F: assert) P k,
  tycontext_sub Delta Delta' ->
  rguard OK_spec ge E Delta' f (frame_ret_assert P F) k ⊣⊢ rguard OK_spec ge E Delta' f (frame_ret_assert (conj_ret_assert P (local (typecheck_environ Delta))) F) k.
Proof.
  intros.
  unfold rguard.
  apply bi.forall_proper; intros ek.
  apply bi.forall_proper; intros vl.
  rewrite !guard_proj_frame _guard_tc_environ; eauto.
  apply guard_proper; auto.
  intros; by rewrite proj_conj.
Qed.

Lemma semax'_conseq {CS: compspecs}:
 forall E Delta P' (R': ret_assert) P c (R: ret_assert) ,
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
                   (|={E}=> P')) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_normal R') ⊢
                   (|={E}=> RA_normal R)) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_break R') ⊢
                   (|={E}=> RA_break R)) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_continue R') ⊢
                   (|={E}=> RA_continue R)) ->
   (forall vl, local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_return R' vl) ⊢
                   RA_return R vl) ->
   semax' OK_spec E Delta P' c R' ⊢ semax' OK_spec E Delta P c R.
Proof.
  intros.
  rewrite !semax_fold_unfold.
  iIntros "H" (??? [??]).
  iPoseProof ("H" with "[%]") as "H"; first done.
  iApply (bi.impl_mono with "H"); first done.
  iIntros "H" (????) "[(% & %) rguard]".
  iSpecialize ("H" with "[-]").
  + rewrite /bi_affinely; iSplit; first done; iSplit; first done.
    rewrite bi.and_elim_r.
    erewrite (rguard_allp_fun_id _ _ _ _ _ _ R') by eauto.
    erewrite (rguard_tc_environ _ _ _ _ _ _ (frame_ret_assert R' _)) by eauto.
    rewrite (rguard_fupd _ _ _ _ _ R).
    iApply (rguard_mono with "rguard").
    intros.
    rewrite proj_frame proj_conj !proj_frame.
    destruct rk; simpl;
         [rename H0 into Hx; pose (ek:=@RA_normal Σ)
         | rename H1 into Hx; pose (ek:=@RA_break Σ)
         | rename H2 into Hx ; pose (ek:=@RA_continue Σ)
         | apply bi.sep_mono, H3; auto]; clear H3.
    all: rewrite fupd_mask_mono // in Hx; rewrite -Hx; iIntros "($ & ? & $ & $ & $)"; auto.
  + erewrite (guard_allp_fun_id _ _ _ _ _ _ P) by eauto.
    erewrite (guard_tc_environ _ _ _ _ _ _ (<affine> allp_fun_id Delta ∗ P)) by eauto.
    rewrite (guard_fupd _ _ _ _ _ P').
    iApply (guard_mono with "H").
    rewrite -fupd_mask_mono //.
    by rewrite -H.
Qed.

Lemma semax_conseq {CS: compspecs}:
 forall E Delta P' (R': ret_assert) P c (R: ret_assert) ,
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
                   (|={E}=> P') ) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_normal R') ⊢
                   (|={E}=> RA_normal R)) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_break R') ⊢
                   (|={E}=> RA_break R)) ->
   (local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_continue R') ⊢
                   (|={E}=> RA_continue R)) ->
   (forall vl, local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ RA_return R' vl) ⊢
                   RA_return R vl) ->
   semax OK_spec E Delta P' c R' ->  semax OK_spec E Delta P c R.
Proof.
  intros.
  unfold semax; rewrite -semax'_conseq; eauto.
Qed.

(* Part 2: Deriving simpler and older version of consequence rules from semax_conseq. *)
Lemma semax'_post_fupd:
 forall {CS: compspecs} (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl, ek <> EK_return -> local (typecheck_environ Delta) ∧
                proj_ret_assert R' ek vl
         ⊢ |={E}=> proj_ret_assert R ek vl) ->
   (forall vl, local (typecheck_environ Delta) ∧
                RA_return R' vl
         ⊢ RA_return R vl) ->
   semax' OK_spec E Delta P c R' ⊢ semax' OK_spec E Delta P c R.
Proof.
intros.
apply semax'_conseq; [by iIntros "(_ & _ & $)" | .. | intros; rewrite -H0; iIntros "(? & _ & $)"; auto]; intros.
- specialize (H EK_normal None); simpl in H.
  rewrite (bi.pure_True (None = None)) in H; last done; rewrite !bi.True_and in H.
  rewrite -H; last done; iIntros "(? & _ & $)"; auto.
- specialize (H EK_break None); simpl in H.
  rewrite (bi.pure_True (None = None)) in H; last done; rewrite !bi.True_and in H.
  rewrite -H; last done; iIntros "(? & _ & $)"; auto.
- specialize (H EK_continue None); simpl in H.
  rewrite (bi.pure_True (None = None)) in H; last done; rewrite !bi.True_and in H.
  rewrite -H; last done; iIntros "(? & _ & $)"; auto.
Qed.

Lemma semax'_post:
 forall {CS: compspecs} (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl, local (typecheck_environ Delta) ∧
                proj_ret_assert R' ek vl
         ⊢ proj_ret_assert R ek vl) ->
   semax' OK_spec E Delta P c R' ⊢ semax' OK_spec E Delta P c R.
Proof.
intros.
apply semax'_post_fupd.
- by intros; iIntros "? !>"; iApply H.
- apply (H EK_return).
Qed.

Lemma semax'_pre_fupd:
 forall {CS: compspecs} (P' : assert) E Delta R (P : assert) c,
  (forall rho, typecheck_environ Delta rho -> P rho ⊢ |={E}=> (P' rho)) -> 
  semax' OK_spec E Delta P' c R ⊢ semax' OK_spec E Delta P c R.
Proof.
intros.
apply semax'_conseq; intros; [| by iIntros "(_ & _ & $)"..].
split => ?; monPred.unseal; iIntros "(% & _ & ?)"; iApply H; auto.
Qed.

Lemma semax'_pre:
 forall {CS: compspecs} (P': assert) E Delta R (P: assert) c,
  (forall rho, typecheck_environ Delta rho -> P rho ⊢ P' rho) ->
  semax' OK_spec E Delta P' c R ⊢ semax' OK_spec E Delta P c R.
Proof.
intros; apply semax'_pre_fupd.
by intros; iIntros "? !>"; iApply H.
Qed.

Lemma semax'_pre_post_fupd:
 forall
      {CS: compspecs} (P' : assert) (R': ret_assert) E Delta (R: ret_assert) (P: assert) c,
   (forall rho, typecheck_environ Delta rho -> P rho ⊢ |={E}=> (P' rho)) ->
   (forall ek vl, ek <> EK_return -> local (typecheck_environ Delta)
                       ∧  proj_ret_assert R ek vl
                    ⊢ |={E}=> proj_ret_assert R' ek vl) ->
   (forall vl, local (typecheck_environ Delta)
                       ∧  RA_return R vl
                    ⊢ RA_return R' vl) ->
   semax' OK_spec E Delta P' c R ⊢ semax' OK_spec E Delta P c R'.
Proof.
intros.
rewrite semax'_pre_fupd; eauto.
apply semax'_post_fupd; auto.
Qed.

Lemma semax'_pre_post:
 forall
      {CS: compspecs} (P': assert) (R': ret_assert) E Delta (R: ret_assert) (P: assert) c,
   (forall rho, typecheck_environ Delta rho -> P rho ⊢ P' rho) ->
   (forall ek vl, local (typecheck_environ Delta)
                       ∧  proj_ret_assert R ek vl
                    ⊢ proj_ret_assert R' ek vl) ->
   semax' OK_spec E Delta P' c R ⊢ semax' OK_spec E Delta P c R'.
Proof.
intros.
rewrite semax'_pre; eauto.
apply semax'_post; auto.
Qed.

Lemma semax_post'_fupd {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl, ek <> EK_return -> local (typecheck_environ Delta)
                      ∧  proj_ret_assert R' ek vl
                        ⊢ |={E}=> proj_ret_assert R ek vl) ->
   (forall vl, local (typecheck_environ Delta)
                      ∧  RA_return R' vl
                        ⊢ RA_return R vl) ->
   semax OK_spec E Delta P c R' ->  semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post_fupd; auto.
Qed.

Lemma semax_post_fupd {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (local (typecheck_environ Delta)
                      ∧  RA_normal R' ⊢ |={E}=> RA_normal R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_break R' ⊢ |={E}=> RA_break R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_continue R' ⊢ |={E}=> RA_continue R) ->
   (forall vl, local (typecheck_environ Delta)
                      ∧ RA_return R' vl ⊢ RA_return R vl) ->
   semax OK_spec E Delta P c R' ->  semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post_fupd; auto.
destruct ek; try contradiction; intros; simpl;
  iIntros "(? & -> & ?)"; rewrite -> bi.pure_True by done; rewrite bi.True_and; [rewrite -H | rewrite -H0 | rewrite -H1]; auto.
Qed.

Lemma semax_post' {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl, local (typecheck_environ Delta)
                      ∧  proj_ret_assert R' ek vl
                        ⊢ proj_ret_assert R ek vl) ->
   semax OK_spec E Delta P c R' ->  semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post; auto.
Qed.

Lemma semax_post {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (local (typecheck_environ Delta)
                      ∧  RA_normal R' ⊢ RA_normal R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_break R' ⊢ RA_break R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_continue R' ⊢ RA_continue R) ->
   (forall vl, local (typecheck_environ Delta)
                      ∧ RA_return R' vl ⊢ RA_return R vl) ->
   semax OK_spec E Delta P c R' ->  semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post; auto.
destruct ek; simpl; auto; intros;
  iIntros "(? & -> & ?)"; rewrite -> bi.pure_True by done; rewrite bi.True_and; [rewrite -H | rewrite -H0 | rewrite -H1]; auto.
Qed.

Lemma semax_pre_fupd {CS: compspecs} :
 forall P' E Delta P c R,
   (local (typecheck_environ Delta) ∧ P ⊢ |={E}=> P') ->
     semax OK_spec E Delta P' c R  -> semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_pre_fupd; auto.
intros; inversion H as [H']. revert H'; monPred.unseal; intros <-; auto.
Qed.

Lemma semax_pre {CS: compspecs} :
 forall P' E Delta P c R,
   (local (typecheck_environ Delta) ∧ P ⊢ P') ->
     semax OK_spec E Delta P' c R  -> semax OK_spec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_pre; auto.
intros; inversion H as [H']; revert H'; monPred.unseal; intros <-; auto.
Qed.

Lemma semax_pre_post_fupd {CS: compspecs}:
 forall P' (R': ret_assert) E Delta P c (R: ret_assert) ,
   (local (typecheck_environ Delta) ∧ P ⊢ |={E}=> P') ->
   (local (typecheck_environ Delta)
                      ∧  RA_normal R' ⊢ |={E}=> RA_normal R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_break R' ⊢ |={E}=> RA_break R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_continue R' ⊢ |={E}=> RA_continue R) ->
   (forall vl, local (typecheck_environ Delta)
                      ∧ RA_return R' vl ⊢ RA_return R vl) ->
   semax OK_spec E Delta P' c R' ->  semax OK_spec E Delta P c R.
Proof.
intros.
eapply semax_pre_fupd; eauto.
eapply semax_post_fupd; eauto.
Qed.

Lemma semax_pre_post {CS: compspecs}:
 forall P' (R': ret_assert) E Delta P c (R: ret_assert) ,
   (local (typecheck_environ Delta) ∧ P ⊢ P') ->
   (local (typecheck_environ Delta)
                      ∧  RA_normal R' ⊢ RA_normal R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_break R' ⊢ RA_break R) ->
   (local (typecheck_environ Delta)
                      ∧ RA_continue R' ⊢ RA_continue R) ->
   (forall vl, local (typecheck_environ Delta)
                      ∧ RA_return R' vl ⊢ RA_return R vl) ->
   semax OK_spec E Delta P' c R' ->  semax OK_spec E Delta P c R.
Proof.
intros.
eapply semax_pre; eauto.
eapply semax_post; eauto.
Qed.

Lemma semax_fupd_elim {CS: compspecs}:
 forall E Delta P c R,
  semax OK_spec E Delta P c R -> semax OK_spec E Delta (|={E}=> P) c R.
Proof.
intros; eapply semax_pre_fupd, H.
by intros; rewrite bi.and_elim_r.
Qed.

Lemma semax_skip {CS: compspecs}:
   forall E Delta P, semax OK_spec E Delta P Sskip (normal_ret_assert P).
Proof.
intros.
apply derives_skip.
intros.
rewrite /= bi.pure_True // left_id //.
Qed.

(*Taken from floyd.SeparationLogicFacts.v*)
Lemma semax_extract_prop:
  forall {CS: compspecs},
  forall E Delta (PP: Prop) (P:assert) c (Q:ret_assert),
           (PP -> semax OK_spec E Delta P c Q) ->
           semax OK_spec E Delta (⌜PP⌝ ∧ P) c Q.
Proof.
  intros.
  eapply semax_pre with (∃ H: PP, P).
  + intros; iIntros "(? & %HPP & ?)"; iExists HPP; auto.
  + apply extract_exists_pre, H.
Qed.

Lemma semax_adapt_frame {cs} E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
                   ∃ F: assert, (⌜closed_wrt_modvars c F⌝ ∧ |={E}=> (P' ∗ F) ∧
                         ⌜local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_normal (frame_ret_assert Q' F) ⊢ |={E}=> RA_normal Q⌝ ∧
                         ⌜local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_break (frame_ret_assert Q' F) ⊢ |={E}=> RA_break Q⌝ ∧
                         ⌜local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_continue (frame_ret_assert Q' F) ⊢ |={E}=> RA_continue Q⌝ ∧
                         ⌜forall vl, local (tc_environ Delta) ∧ <affine> allp_fun_id Delta ∗ RA_return (frame_ret_assert Q' F) vl ⊢ RA_return Q vl⌝))
   (SEM: semax(CS := cs) OK_spec E Delta P' c Q'):
   semax OK_spec E Delta P c Q.
Proof.
  intros.
  eapply semax_conseq; [| by intros; iIntros "(_ & _ & $)" .. |].
  { by intros; iIntros "? !>"; iApply (H with "[-]"). }
  apply extract_exists_pre. intros F. clear H.
  apply semax_extract_prop. intros.
  eapply semax_pre_fupd. 2:{ do 4 (apply semax_extract_prop; intros).
    eapply semax_conseq. 6:{ apply semax_frame. exact H. apply SEM. }
    2: { exact H0. }
    2: { exact H1. }
    2: { exact H2. }
    2: { exact H3. }
   intros; iIntros "(_ & _ & P) !>"; iApply "P". }
  intros. unfold local, liftx, lift1, tc_environ; simpl.
  by iIntros "[_ >[$ %]]"; iPureIntro; rewrite and_True.
Qed.

Lemma semax_adapt_frame' {cs} E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
                   ∃ F: assert, (⌜closed_wrt_modvars c F⌝ ∧ |={E}=> (P' ∗ F) ∧
                         ⌜RA_normal (frame_ret_assert Q' F) ⊢ |={E}=> RA_normal Q⌝ ∧
                         ⌜RA_break (frame_ret_assert Q' F) ⊢ |={E}=> RA_break Q⌝ ∧
                         ⌜RA_continue (frame_ret_assert Q' F) ⊢ |={E}=> RA_continue Q⌝ ∧
                         ⌜forall vl, RA_return (frame_ret_assert Q' F) vl ⊢ RA_return Q vl⌝))
   (SEM: semax(CS := cs) OK_spec E Delta P' c Q'):
   semax OK_spec E Delta P c Q.
Proof.
  intros. eapply semax_adapt_frame, SEM.
  intros. rewrite H.
  apply bi.exist_mono; intros.
  iIntros "[$ >[$ (% & % & % & %)]]"; iPureIntro; split; auto.
  split3; last split; intros; rewrite /bi_affinely bi.and_elim_r bi.and_elim_l left_id; auto.
Qed.

Lemma semax_adapt {cs} E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: local (typecheck_environ Delta) ∧ (<affine> allp_fun_id Delta ∗ P) ⊢
                   (|={E}=> P' ∧
                        ⌜RA_normal Q' ⊢ |={E}=> RA_normal Q⌝ ∧
                        ⌜RA_break Q' ⊢ |={E}=> RA_break Q⌝ ∧
                        ⌜RA_continue Q' ⊢ |={E}=> RA_continue Q⌝ ∧
                        ⌜forall vl, RA_return Q' vl ⊢ RA_return Q vl⌝))
   (SEM: semax(CS := cs) OK_spec E Delta P' c Q'):
   semax OK_spec E Delta P c Q.
Proof.
  intros. eapply semax_adapt_frame'; eauto. intros. rewrite H; iIntros "H"; iExists emp.
  iSplit.
  { iPureIntro; monPred.unseal; done. }
  iMod "H" as "($ & %NORM & %BREAK & %CONT & %RET)"; iPureIntro; split; auto.
  destruct Q'; simpl in *.
  split3; last split; intros; rewrite right_id; auto.
Qed.

End mpred.
