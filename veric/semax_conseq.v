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

Local Notation assert := (environ -> mpred).

Section mpred.

Context `{!heapGS Σ} {Espec : OracleKind} `{!externalGS OK_ty Σ}. (* consolidate *)

Lemma _guard_mono: forall ge E Delta f (P Q: assert) k,
  (forall rho, P rho ⊢ Q rho) ->
  _guard Espec ge E Delta f Q k ⊢ _guard Espec ge E Delta f P k.
Proof.
  intros.
  apply _guard_mono; auto.
Qed.

Lemma guard_mono: forall ge E Delta f (P Q: assert) k,
  (forall rho, P rho ⊢ Q rho) ->
  guard' Espec ge E Delta f Q k ⊢ guard' Espec ge E Delta f P k.
Proof.
  intros.
  apply guard_mono; auto.
Qed.

Lemma rguard_mono: forall ge E Delta f (P Q: ret_assert) k,
  (forall rk vl rho, proj_ret_assert P rk vl rho ⊢ proj_ret_assert Q rk vl rho) ->
  rguard Espec ge E Delta f Q k ⊢ rguard Espec ge E Delta f P k.
Proof.
  intros.
  unfold rguard.
  iIntros "H" (??).
  rewrite -_guard_mono; eauto.
Qed.

Definition fupd_ret_assert E (Q: ret_assert): ret_assert :=
          {| RA_normal := fun rho => |={E}=> (RA_normal Q rho);
             RA_break := fun rho => |={E}=> (RA_break Q rho);
             RA_continue := fun rho => |={E}=> (RA_continue Q rho);
             RA_return := fun v rho => RA_return Q v rho |}.
(* Asymmetric consequence: since there's no CompCert step that
   corresponds to RA_return, we can't do an update there. We could
   probably add a bupd if we really want to, but it may not be
   necessary. *)

Lemma fupd_fupd_andp_prop : forall E P (Q : mpred), (|={E}=> (⌜P⌝ ∧ |={E}=> Q)) ⊣⊢ (|={E}=> (⌜P⌝ ∧ Q)).
Proof.
  intros; iSplit; iIntros "H".
  - iMod "H" as "[$ $]".
  - iMod "H" as "[$ $]"; done.
Qed.

Lemma proj_fupd_ret_assert: forall E Q ek vl rho,
  (|={E}=> proj_ret_assert (fupd_ret_assert E Q) ek vl rho) ⊣⊢ (|={E}=> proj_ret_assert Q ek vl rho).
Proof.
  intros.
  destruct ek; simpl; auto; apply fupd_fupd_andp_prop.
Qed.

(* The following four lemmas are not now used. but after deep embedded hoare logic (SL_as_Logic) is
ported, the frame does not need to be quantified in the semantic definition of semax. Then,
these two lemmas can replace the other two afterwards. *)

Lemma assert_safe_fupd':
  forall gx vx tx rho E (P: environ -> mpred) Delta f k,
    match k with Ret _ _ => False | _ => True end ->
    let PP1 := ⌜guard_environ Delta f rho⌝ in
    let PP2 := funassert Delta rho in
    (PP1 ∧ P rho ∗ PP2 -∗ assert_safe Espec gx E f vx tx k rho) ⊣⊢
    (PP1 ∧ (|={E}=> P rho) ∗ PP2 -∗ assert_safe Espec gx E f vx tx k rho).
Proof.
  intros.
  iSplit.
  * iIntros "H (% & P & #?)".
    iApply assert_safe_fupd; iMod "P"; iApply "H"; auto.
  * iIntros "H (% & P & ?)"; iApply "H"; auto.
Qed.

Lemma _guard_fupd':
  forall ge E Delta (P: environ -> mpred) f k,
    match k with Ret _ _ => False | _ => True end ->
    _guard Espec ge E Delta f P k ⊣⊢ _guard Espec ge E Delta f (fun rho => |={E}=> (P rho)) k.
Proof.
  intros.
  unfold _guard.
  apply bi.forall_proper; intros ?.
  apply bi.forall_proper; intros ?.
  rewrite assert_safe_fupd'; auto.
Qed.

Lemma guard_fupd':
  forall ge E Delta f (P: environ -> mpred) k,
    guard' Espec ge E Delta f P k ⊣⊢ guard' Espec ge E Delta f (fun rho => |={E}=> (P rho)) k.
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
    rguard Espec ge E Delta f P k ⊣⊢ rguard Espec ge E Delta f (fupd_ret_assert E P) k.
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
  forall gx vx tx rho E (F P: environ -> mpred) Delta f k,
    match k with Ret _ _ => False | _ => True end ->
    let PP1 := ⌜guard_environ Delta f rho⌝ in
    let PP2 := funassert Delta rho in
    (PP1 ∧ (F rho ∗ P rho) ∗ PP2 -∗
    assert_safe Espec gx E f vx tx k rho) ⊣⊢
    (PP1 ∧ (F rho ∗ |={E}=> (P rho)) ∗ PP2 -∗
    assert_safe Espec gx E f vx tx k rho).
Proof.
  intros.
  iSplit.
  * iIntros "H (% & P & #?)".
    rewrite (assert_safe_fupd' _ _ _ _ _ (fun rho => F rho ∗ P rho)); last done.
    iPoseProof (fupd_frame_l with "P") as "P".
    iApply "H"; auto.
  * iIntros "H (% & (? & P) & ?)"; iApply "H"; iFrame; auto.
Qed.

Lemma _guard_fupd:
  forall ge E Delta f (F P: environ -> mpred) k,
    match k with Ret _ _ => False | _ => True end ->
    _guard Espec ge E Delta f (fun rho => F rho ∗ P rho) k ⊣⊢ _guard Espec ge E Delta f (fun rho => F rho ∗ |={E}=> (P rho)) k.
Proof.
  intros.
  unfold _guard.
  apply bi.forall_proper; intros ?.
  apply bi.forall_proper; intros ?.
  rewrite assert_safe_fupd; auto.
Qed.

Lemma guard_fupd:
  forall ge E Delta f (F P: environ -> mpred) k,
    guard' Espec ge E Delta f (fun rho => F rho ∗ P rho) k ⊣⊢ guard' Espec ge E Delta f (fun rho => F rho ∗ |={E}=> (P rho)) k.
Proof.
  intros.
  apply _guard_fupd; auto.
Qed.

Lemma fupd_fupd_frame_l : forall E (P Q : mpred), (|={E}=> (P ∗ |={E}=> Q)) ⊣⊢ |={E}=> (P ∗ Q).
Proof.
  intros; iSplit.
  - by iIntros ">[$ >$]".
  - by iIntros ">[$ $]".
Qed.

Lemma proj_fupd_ret_assert_frame: forall E F Q ek vl rho,
  (|={E}=> (F ∗ proj_ret_assert (fupd_ret_assert E Q) ek vl rho)) ⊣⊢ |={E}=> (F ∗ proj_ret_assert Q ek vl rho).
Proof.
  intros.
  destruct ek; simpl; auto;
    rewrite -fupd_fupd_frame_l fupd_fupd_andp_prop fupd_fupd_frame_l; auto.
Qed.

(* this would be unnecessary if assert worked properly *)
Global Instance guard_proper ge E Delta f : Proper ((fun a b => forall rho, a rho ⊣⊢ b rho) ==> eq ==> equiv) (_guard Espec ge E Delta f).
Proof.
  intros ????? ->; rewrite /_guard.
  do 7 f_equiv.
  by rewrite H.
Qed.

Lemma guard_proj_frame : forall ge E Delta f P F ek vl k,
  _guard Espec ge E Delta f (proj_ret_assert (frame_ret_assert P F) ek vl) k ⊣⊢
  _guard Espec ge E Delta f (fun rho => F rho ∗ proj_ret_assert P ek vl rho) k.
Proof.
  intros; apply guard_proper; last done.
  intros; by rewrite proj_frame.
Qed.

Lemma rguard_fupd:
  forall ge E Delta F f (P: ret_assert) k,
    rguard Espec ge E Delta f (frame_ret_assert P F) k ⊣⊢ rguard Espec ge E Delta f (frame_ret_assert (fupd_ret_assert E P) F) k.
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
  forall ge E Delta' Delta f (F P: environ -> mpred) k,
    tycontext_sub E Delta Delta' ->
    _guard Espec ge E Delta' f (fun rho => F rho ∗ P rho) k ⊣⊢ _guard Espec ge E Delta' f (fun rho => F rho ∗ (<affine> allp_fun_id E Delta rho ∗ P rho)) k.
Proof.
  intros.
  unfold _guard.
  do 7 f_equiv.
  iSplit.
  * iIntros "(($ & $) & #f)".
    by iPoseProof (funassert_allp_fun_id_sub with "f") as "$".
  * iIntros "(($ & _ & $) & $)".
Qed.

Lemma guard_allp_fun_id: forall ge E Delta' Delta f (F P: environ -> mpred) k,
  tycontext_sub E Delta Delta' ->
  guard' Espec ge E Delta' f (fun rho => F rho ∗ P rho) k ⊣⊢ guard' Espec ge E Delta' f (fun rho => F rho ∗ (<affine> allp_fun_id E Delta rho ∗ P rho)) k.
Proof.
  intros.
  apply _guard_allp_fun_id; auto.
Qed.

Lemma rguard_allp_fun_id: forall ge E Delta' Delta f (F: environ -> mpred) P k,
  tycontext_sub E Delta Delta' ->
  rguard Espec ge E Delta' f (frame_ret_assert P F) k ⊣⊢ rguard Espec ge E Delta' f (frame_ret_assert (frame_ret_assert P (fun rho => <affine> allp_fun_id E Delta rho)) F) k.
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
  forall ge E Delta' Delta f (F P: environ -> mpred) k,
    tycontext_sub E Delta Delta' ->
    _guard Espec ge E Delta' f (fun rho => F rho ∗ P rho) k ⊣⊢
    _guard Espec ge E Delta' f (fun rho => F rho ∗ (⌜typecheck_environ Delta rho⌝ ∧ P rho)) k.
Proof.
  intros.
  unfold _guard.
  do 6 f_equiv.
  iSplit.
  * iIntros "(%Henv & ($ & $) & $)"; iPureIntro.
    split3; auto; eapply typecheck_environ_sub; eauto.
    destruct Henv as [? _]; auto.
  * iIntros "($ & ($ & [_ $]) & $)".
Qed.

Lemma guard_tc_environ: forall ge E Delta' Delta f (F P: environ -> mpred) k,
  tycontext_sub E Delta Delta' ->
  guard' Espec ge E Delta' f (fun rho => F rho ∗ P rho) k ⊣⊢ guard' Espec ge E Delta' f (fun rho => F rho ∗ (⌜typecheck_environ Delta rho⌝ ∧ P rho)) k.
Proof.
  intros.
  apply _guard_tc_environ; auto.
Qed.

Lemma rguard_tc_environ: forall ge E Delta' Delta f (F: environ -> mpred) P k,
  tycontext_sub E Delta Delta' ->
  rguard Espec ge E Delta' f (frame_ret_assert P F) k ⊣⊢ rguard Espec ge E Delta' f (frame_ret_assert (conj_ret_assert P (fun rho => ⌜typecheck_environ Delta rho⌝)) F) k.
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
   (forall rho, ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ P rho) ⊢
                   (|={E}=> (P' rho)) ) ->
   (forall rho,  ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ RA_normal R' rho) ⊢
                   (|={E}=> (RA_normal R rho))) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ RA_break R' rho) ⊢
                   (|={E}=> (RA_break R rho))) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ RA_continue R' rho) ⊢
                   (|={E}=> (RA_continue R rho))) ->
   (forall vl rho, ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ RA_return R' vl rho) ⊢
                   (RA_return R vl rho)) ->
   semax' Espec E Delta P' c R' ⊢ semax' Espec E Delta P c R.
Proof.
  intros.
  rewrite !semax_fold_unfold.
  iIntros "H" (??? [??]).
  iPoseProof ("H" with "[%]") as "H"; first done.
  iApply (bi.impl_mono with "H"); first done.
  iIntros "H" (???) "[% rguard]".
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
         [rename H0 into Hx; pose (ek:=RA_normal)
         | rename H1 into Hx; pose (ek:=RA_break)
         | rename H2 into Hx ; pose (ek:=RA_continue)
         | apply bi.sep_mono, H3; auto]; clear H3.
    all: rewrite -Hx; iIntros "($ & $ & $ & $ & $)".
  + erewrite (guard_allp_fun_id _ _ _ _ _ _ P) by eauto.
    erewrite (guard_tc_environ _ _ _ _ _ _ (fun rho => <affine> allp_fun_id E Delta rho ∗ P rho)) by eauto.
    rewrite (guard_fupd _ _ _ _ _ P').
    iApply (guard_mono with "H").
    intros.
    by rewrite -H.
Qed.

Lemma semax_conseq {CS: compspecs}:
 forall E Delta P' (R': ret_assert) P c (R: ret_assert) ,
   (forall rho, ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ P rho) ⊢
                   (|={E}=> (P' rho)) ) ->
   (forall rho,  ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ RA_normal R' rho) ⊢
                   (|={E}=> (RA_normal R rho))) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ RA_break R' rho) ⊢
                   (|={E}=> (RA_break R rho))) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ RA_continue R' rho) ⊢
                   (|={E}=> (RA_continue R rho))) ->
   (forall vl rho, ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ RA_return R' vl rho) ⊢
                   (RA_return R vl rho)) ->
   semax Espec E Delta P' c R' ->  semax Espec E Delta P c R.
Proof.
  intros.
  unfold semax; rewrite -semax'_conseq; eauto.
Qed.

(* Part 2: Deriving simpler and older version of consequence rules from semax_conseq. *)
Lemma semax'_post_fupd:
 forall {CS: compspecs} (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl rho, ek <> EK_return -> ⌜typecheck_environ Delta rho⌝ ∧ 
                proj_ret_assert R' ek vl rho
         ⊢ |={E}=> (proj_ret_assert R ek vl rho)) ->
   (forall vl rho,  ⌜typecheck_environ Delta rho⌝ ∧
                RA_return R' vl rho 
         ⊢ RA_return R vl rho) ->
   semax' Espec E Delta P c R' ⊢ semax' Espec E Delta P c R.
Proof.
intros.
apply semax'_conseq; [by iIntros (?) "(_ & _ & $)" | .. | intros; rewrite -H0; iIntros "($ & _ & $)"]; intros.
- specialize (H EK_normal None rho); simpl in H.
  rewrite (bi.pure_True (None = None)) in H; last done; rewrite !bi.True_and in H.
  rewrite -H; last done; iIntros "($ & _ & $)".
- specialize (H EK_break None rho); simpl in H.
  rewrite (bi.pure_True (None = None)) in H; last done; rewrite !bi.True_and in H.
  rewrite -H; last done; iIntros "($ & _ & $)".
- specialize (H EK_continue None rho); simpl in H.
  rewrite (bi.pure_True (None = None)) in H; last done; rewrite !bi.True_and in H.
  rewrite -H; last done; iIntros "($ & _ & $)".
Qed.

Lemma semax'_post:
 forall {CS: compspecs} (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl rho,  ⌜typecheck_environ Delta rho⌝ ∧ 
                proj_ret_assert R' ek vl rho 
         ⊢ proj_ret_assert R ek vl rho) ->
   semax' Espec E Delta P c R' ⊢ semax' Espec E Delta P c R.
Proof.
intros.
apply semax'_post_fupd.
- by intros; iIntros "? !>"; iApply H.
- apply (H EK_return).
Qed.

Lemma semax'_pre_fupd:
 forall {CS: compspecs} P' E Delta R P c,
  (forall rho, typecheck_environ Delta rho -> P rho ⊢ |={E}=> (P' rho)) -> 
  semax' Espec E Delta P' c R ⊢ semax' Espec E Delta P c R.
Proof.
intros.
apply semax'_conseq; intros; [| by iIntros "(_ & _ & $)"..].
iIntros "(% & _ & ?)"; iApply H; auto.
Qed.

Lemma semax'_pre:
 forall {CS: compspecs} P' E Delta R P c,
  (forall rho, typecheck_environ Delta rho -> P rho ⊢ P' rho) ->
  semax' Espec E Delta P' c R ⊢ semax' Espec E Delta P c R.
Proof.
intros; apply semax'_pre_fupd.
by intros; iIntros "? !>"; iApply H.
Qed.

Lemma semax'_pre_post_fupd:
 forall
      {CS: compspecs} P' (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall rho, typecheck_environ Delta rho -> P rho ⊢ |={E}=> (P' rho)) ->
   (forall ek vl rho, ek <> EK_return -> ⌜typecheck_environ Delta rho⌝
                       ∧  proj_ret_assert R ek vl rho 
                    ⊢ |={E}=> (proj_ret_assert R' ek vl rho)) ->
   (forall vl rho, ⌜typecheck_environ Delta rho⌝ 
                       ∧  RA_return R vl rho 
                    ⊢ RA_return R' vl rho) ->
   semax' Espec E Delta P' c R ⊢ semax' Espec E Delta P c R'.
Proof.
intros.
rewrite semax'_pre_fupd; eauto.
apply semax'_post_fupd; auto.
Qed.

Lemma semax'_pre_post:
 forall
      {CS: compspecs} P' (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall rho, typecheck_environ Delta rho -> P rho ⊢ P' rho) ->
   (forall ek vl rho, ⌜typecheck_environ Delta rho⌝
                       ∧  proj_ret_assert R ek vl rho
                    ⊢ proj_ret_assert R' ek vl rho) ->
   semax' Espec E Delta P' c R ⊢ semax' Espec E Delta P c R'.
Proof.
intros.
rewrite semax'_pre; eauto.
apply semax'_post; auto.
Qed.

Lemma semax_post'_fupd {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl rho, ek <> EK_return -> ⌜typecheck_environ Delta rho⌝ 
                      ∧  proj_ret_assert R' ek vl rho
                        ⊢ |={E}=> (proj_ret_assert R ek vl rho)) ->
   (forall vl rho,  ⌜typecheck_environ Delta rho⌝ 
                      ∧  RA_return R' vl rho
                        ⊢ RA_return R vl rho) ->
   semax Espec E Delta P c R' ->  semax Espec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post_fupd; auto.
Qed.

Lemma semax_post_fupd {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall rho,  ⌜typecheck_environ Delta rho⌝
                      ∧  RA_normal R' rho ⊢ |={E}=> (RA_normal R rho)) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_break R' rho ⊢ |={E}=> (RA_break R rho)) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_continue R' rho ⊢ |={E}=> (RA_continue R rho)) ->
   (forall vl rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_return R' vl rho ⊢ RA_return R vl rho) ->
   semax Espec E Delta P c R' ->  semax Espec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post_fupd; auto.
destruct ek; try contradiction; intros; simpl;
  iIntros "(% & -> & ?)"; rewrite -> bi.pure_True by done; rewrite bi.True_and; [rewrite -H | rewrite -H0 | rewrite -H1]; auto.
Qed.

Lemma semax_post' {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall ek vl rho,  ⌜typecheck_environ Delta rho⌝ 
                      ∧  proj_ret_assert R' ek vl rho
                        ⊢ proj_ret_assert R ek vl rho) ->
   semax Espec E Delta P c R' ->  semax Espec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post; auto.
Qed.

Lemma semax_post {CS: compspecs}:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (forall rho,  ⌜typecheck_environ Delta rho⌝
                      ∧  RA_normal R' rho ⊢ RA_normal R rho) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_break R' rho ⊢ RA_break R rho) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_continue R' rho ⊢ RA_continue R rho) ->
   (forall vl rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_return R' vl rho ⊢ RA_return R vl rho) ->
   semax Espec E Delta P c R' ->  semax Espec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_post; auto.
destruct ek; simpl; auto; intros;
  iIntros "(% & -> & ?)"; rewrite -> bi.pure_True by done; rewrite bi.True_and; [rewrite -H | rewrite -H0 | rewrite -H1]; auto.
Qed.

Lemma semax_pre_fupd {CS: compspecs} :
 forall P' E Delta P c R,
   (forall rho, ⌜typecheck_environ Delta rho⌝ ∧  P rho ⊢ |={E}=> (P' rho)) ->
     semax Espec E Delta P' c R  -> semax Espec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_pre_fupd; auto.
intros; rewrite -H; auto.
Qed.

Lemma semax_pre {CS: compspecs} :
 forall P' E Delta P c R,
   (forall rho, ⌜typecheck_environ Delta rho⌝ ∧ P rho ⊢ P' rho) ->
     semax Espec E Delta P' c R  -> semax Espec E Delta P c R.
Proof.
unfold semax.
intros.
rewrite -semax'_pre; auto.
intros; rewrite -H; auto.
Qed.

Lemma semax_pre_post_fupd {CS: compspecs}:
 forall P' (R': ret_assert) E Delta P c (R: ret_assert) ,
   (forall rho,  ⌜typecheck_environ Delta rho⌝ ∧  P rho ⊢ |={E}=> P' rho) ->
   (forall rho,  ⌜typecheck_environ Delta rho⌝
                      ∧  RA_normal R' rho ⊢ |={E}=> (RA_normal R rho)) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_break R' rho ⊢ |={E}=> (RA_break R rho)) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_continue R' rho ⊢ |={E}=> (RA_continue R rho)) ->
   (forall vl rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_return R' vl rho ⊢ RA_return R vl rho) ->
   semax Espec E Delta P' c R' ->  semax Espec E Delta P c R.
Proof.
intros.
eapply semax_pre_fupd; eauto.
eapply semax_post_fupd; eauto.
Qed.

Lemma semax_pre_post {CS: compspecs}:
 forall P' (R': ret_assert) E Delta P c (R: ret_assert) ,
   (forall rho,  ⌜typecheck_environ Delta rho⌝ ∧ P rho ⊢ P' rho) ->
   (forall rho,  ⌜typecheck_environ Delta rho⌝
                      ∧  RA_normal R' rho ⊢ RA_normal R rho) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_break R' rho ⊢ RA_break R rho) ->
   (forall rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_continue R' rho ⊢ RA_continue R rho) ->
   (forall vl rho, ⌜typecheck_environ Delta rho⌝
                      ∧ RA_return R' vl rho ⊢ RA_return R vl rho) ->
   semax Espec E Delta P' c R' ->  semax Espec E Delta P c R.
Proof.
intros.
eapply semax_pre; eauto.
eapply semax_post; eauto.
Qed.

Lemma semax_fupd_elim {CS: compspecs}:
 forall E Delta P c R,
  semax Espec E Delta P c R -> semax Espec E Delta (fun rho => |={E}=> (P rho)) c R.
Proof.
intros; eapply semax_pre_fupd, H.
by intros; rewrite bi.and_elim_r.
Qed.

(*Lemma semax_skip {CS: compspecs}:
   forall E Delta P, semax Espec E Delta P Sskip (normal_ret_assert P).
Proof.
intros.
apply derives_skip.
intros.
simpl.
rewrite prop_true_andp by auto.
auto.
Qed.*)

(*Taken from floyd.SeparationLogicFacts.v*)
Lemma semax_extract_prop:
  forall {CS: compspecs},
  forall E Delta (PP: Prop) (P:assert) c (Q:ret_assert),
           (PP -> semax Espec E Delta P c Q) ->
           semax Espec E Delta (fun rho => ⌜PP⌝ ∧ P rho) c Q.
Proof.
  intros.
  eapply semax_pre with (fun rho => ∃ H: PP, P rho).
  + intros; iIntros "(% & %HPP & ?)"; iExists HPP; auto.
  + apply extract_exists_pre, H.
Qed.

Lemma semax_adapt_frame {cs} E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: forall rho,  ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ P rho) ⊢
                   ∃ F: assert, (⌜closed_wrt_modvars c F⌝ ∧ |={E}=> (P' rho ∗ F rho) ∧
                         ⌜forall rho, ((local (tc_environ Delta) rho) ∧ <affine> allp_fun_id E Delta rho ∗ RA_normal (frame_ret_assert Q' F) rho ⊢ |={E}=> RA_normal Q rho)⌝ ∧
                         ⌜forall rho, ((local (tc_environ Delta) rho) ∧ <affine> allp_fun_id E Delta rho ∗ RA_break (frame_ret_assert Q' F) rho ⊢ |={E}=> RA_break Q rho)⌝ ∧
                         ⌜forall rho, ((local (tc_environ Delta) rho) ∧ <affine> allp_fun_id E Delta rho ∗ RA_continue (frame_ret_assert Q' F) rho ⊢ |={E}=> RA_continue Q rho)⌝ ∧
                         ⌜forall vl rho, ((local (tc_environ Delta) rho) ∧ <affine> allp_fun_id E Delta rho ∗ RA_return (frame_ret_assert Q' F) vl rho ⊢ RA_return Q vl rho)⌝))
   (SEM: semax Espec E Delta P' c Q'):
   semax Espec E Delta P c Q.
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
   (H: forall rho,  ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ P rho) ⊢
                   ∃ F: assert, (⌜closed_wrt_modvars c F⌝ ∧ |={E}=> (P' rho ∗ F rho) ∧
                         ⌜forall rho, (RA_normal (frame_ret_assert Q' F) rho ⊢ |={E}=> RA_normal Q rho)⌝ ∧
                         ⌜forall rho, (RA_break (frame_ret_assert Q' F) rho ⊢ |={E}=> RA_break Q rho)⌝ ∧
                         ⌜forall rho, (RA_continue (frame_ret_assert Q' F) rho ⊢ |={E}=> RA_continue Q rho)⌝ ∧
                         ⌜forall vl rho, (RA_return (frame_ret_assert Q' F) vl rho ⊢ RA_return Q vl rho)⌝))
   (SEM: semax Espec E Delta P' c Q'):
   semax Espec E Delta P c Q.
Proof.
  intros. eapply semax_adapt_frame, SEM.
  intros. rewrite H.
  apply bi.exist_mono; intros.
  iIntros "[$ >[$ (% & % & % & %)]]"; iPureIntro; split; auto.
  split3; last split; intros; rewrite /bi_affinely bi.and_elim_r bi.and_elim_l left_id; auto.
Qed.

Lemma semax_adapt {cs} E Delta c (P P': assert) (Q Q' : ret_assert)
   (H: forall rho,  ⌜typecheck_environ Delta rho⌝ ∧ (<affine> allp_fun_id E Delta rho ∗ P rho) ⊢
                   (|={E}=> (P' rho) ∧
                        ⌜forall rho, RA_normal Q' rho ⊢ |={E}=> RA_normal Q rho⌝ ∧
                        ⌜forall rho, RA_break Q' rho ⊢ |={E}=> RA_break Q rho⌝ ∧
                        ⌜forall rho, RA_continue Q' rho ⊢ |={E}=> RA_continue Q rho⌝ ∧
                        ⌜forall vl rho, RA_return Q' vl rho ⊢ RA_return Q vl rho⌝))
   (SEM: semax Espec E Delta P' c Q'):
   semax Espec E Delta P c Q.
Proof.
  intros. eapply semax_adapt_frame'; eauto. intros. rewrite H; iIntros "H"; iExists (fun rho => emp).
  iSplit; first done.
  iMod "H" as "($ & %NORM & %BREAK & %CONT & %RET)"; iPureIntro; split; auto.
  destruct Q'; simpl in *.
  split3; last split; intros; rewrite right_id; auto.
Qed.

End mpred.
