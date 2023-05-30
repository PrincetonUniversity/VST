From compcert Require Export Clightdefs.
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Export VST.floyd.jmeq_lemmas.
Require Export VST.floyd.find_nth_tactic.
Require Export VST.veric.juicy_extspec.

Require Import VST.floyd.assert_lemmas.
Import LiftNotation.

Section mpred.

Context `{!heapGS Σ}.

(* Closed and subst. copied from closed_lemmas.v. *)

Lemma closed_wrt_subst:
  forall id e (P : assert), closed_wrt_vars (eq id) P -> assert_of (subst id e P) ⊣⊢ P.
Proof.
intros.
unfold subst, closed_wrt_vars in *.
split => rho /=.
symmetry.
apply H.
intros.
destruct (eq_dec id i); auto.
right.
rewrite Map.gso; auto.
Qed.

(* End of copied from closed_lemmas.v. *)

Lemma subst_self: forall {A: Type} (P: environ -> A) t id v Delta rho,
  (temp_types Delta) !! id = Some t ->
  tc_environ Delta rho ->
  v rho = eval_id id rho ->
  subst id v P rho = P rho.
Proof.
  intros.
  destruct H0 as [? _].
  specialize (H0 _ _ H).
  destruct H0 as [v' [? ?]].
  unfold subst.
  f_equal.
  unfold env_set, eval_id in *; destruct rho; simpl in *.
  f_equal.
  rewrite H1 H0.
  simpl.
  apply Map.ext; intros i.
  destruct (Pos.eq_dec id i).
  + subst.
    rewrite Map.gss; symmetry; auto.
  + rewrite -> Map.gso by auto.
    auto.
Qed.

Notation assert := (@assert Σ).

Definition obox (Delta: tycontext) (i: ident) (P: assert): assert :=
  ∀ v: _,
    match (temp_types Delta) !! i with
    | Some t => ⌜tc_val' t v⌝ → assert_of (subst i (`v) P)
    | _ => True
    end.

Definition odia (Delta: tycontext) (i: ident) (P: assert): assert :=
  ∃ v: _,
    match (temp_types Delta) !! i with
    | Some t => ⌜tc_val' t v⌝ ∧ assert_of (subst i (`v) P)
    | _ => False
    end.

Lemma obox_closed_wrt: forall Delta id P, closed_wrt_vars (eq id) (obox Delta id P).
Proof.
  intros.
  hnf; intros.
  unfold obox; simpl.
  monPred.unseal; simpl.
  f_equiv; intros ?.
  destruct ((temp_types Delta) !! id); auto.
  rewrite /monpred.monPred_defs.monPred_impl_def /=.
  assert ((Map.set id a (te_of rho)) = Map.set id a te') as Hrho.
  { apply Map.ext; intros j.
    destruct (ident_eq id j).
    + subst.
      rewrite !Map.gss; auto.
    + rewrite !Map.gso //.
      destruct (H j); [congruence |].
      auto. }
  iSplit; iIntros "H" (? <- ?); (iSpecialize ("H" with "[%] [%]"); [done.. |]);
    unfold_lift; rewrite /subst /env_set /= Hrho //.
Qed.

Lemma odia_closed_wrt: forall Delta id P, closed_wrt_vars (eq id) (odia Delta id P).
Proof.
  intros.
  hnf; intros.
  unfold odia; simpl.
  monPred.unseal; simpl.
  f_equiv; intros ?.
  destruct ((temp_types Delta) !! id); auto.
  simpl; f_equiv.
  rewrite /subst /env_set /=; f_equiv.
  f_equiv; apply Map.ext; intros j.
  destruct (ident_eq id j).
  + subst.
    rewrite !Map.gss; auto.
  + rewrite !Map.gso //.
    destruct (H j); [congruence |].
    auto.
Qed.

Lemma subst_obox: forall Delta id v (P: assert), assert_of (subst id (`v) (obox Delta id P)) ⊣⊢ obox Delta id P.
Proof.
  intros.
  apply closed_wrt_subst.
  apply obox_closed_wrt.
Qed.

Lemma subst_odia: forall Delta id v (P: assert), assert_of (subst id (`v) (odia Delta id P)) ⊣⊢ odia Delta id P.
Proof.
  intros.
  apply closed_wrt_subst.
  apply odia_closed_wrt.
Qed.

Definition temp_guard (Delta : tycontext) (i: ident): Prop :=
  (temp_types Delta) !! i <> None.

Lemma obox_closed: forall Delta i (P : assert), temp_guard Delta i -> closed_wrt_vars (eq i) P -> obox Delta i P ⊣⊢ P.
Proof.
  intros.
  unfold obox.
  hnf in H.
  destruct ((temp_types Delta) !! i); [| tauto].
  iSplit.
  + iIntros "H"; iSpecialize ("H" $! Vundef with "[%]"); first apply tc_val'_Vundef.
    rewrite closed_wrt_subst //.
  + iIntros "?" (??).
    rewrite closed_wrt_subst //.
Qed.

Lemma obox_odia: forall Delta i P, temp_guard Delta i -> obox Delta i (odia Delta i P) ⊣⊢ odia Delta i P.
Proof.
  intros.
  apply obox_closed; auto.
  apply odia_closed_wrt.
Qed.

Lemma obox_K: forall Delta i P Q, (P ⊢ Q) -> obox Delta i P ⊢ obox Delta i Q.
Proof.
  intros.
  rewrite /obox /subst.
  destruct ((temp_types Delta) !! i); auto.
  split => rho; monPred.unseal.
  iIntros "H" (????); rewrite -H; by iApply "H".
Qed.

Lemma obox_T: forall Delta i (P: assert),
  temp_guard Delta i ->
  local (tc_environ Delta) ∧ obox Delta i P ⊢ P.
Proof.
  intros.
  split => rho; rewrite /local /lift1 /obox /subst /env_set; monPred.unseal.
  iIntros "((%TC & _) & H)".
  unfold temp_guard, typecheck_temp_environ in *.
  specialize (TC i); destruct (temp_types Delta !! i); last done.
  edestruct TC as (? & ? & ?); first done.
  iSpecialize ("H" with "[%] [%]"); [done.. | simpl].
  destruct rho; rewrite Map.override_same //.
Qed.

Lemma odia_D: forall Delta i (P: assert),
  temp_guard Delta i ->
  local (tc_environ Delta) ∧ P ⊢ odia Delta i P.
Proof.
  intros.
  split => rho; rewrite /local /lift1 /odia /subst /env_set; monPred.unseal.
  iIntros "((%TC & _) & H)".
  unfold temp_guard, typecheck_temp_environ in *.
  specialize (TC i); destruct (temp_types Delta !! i); last done.
  edestruct TC as (? & ? & ?); first done.
  iExists _; iSplit; first done; simpl.
  destruct rho; rewrite Map.override_same //.
Qed.

Lemma odia_derives_EX_subst: forall Delta i P,
  odia Delta i P ⊢ ∃ v : val, assert_of (subst i (` v) P).
Proof.
  intros.
  unfold odia.
  apply bi.exist_mono; intros.
  iIntros "H"; destruct ((temp_types Delta) !! i); last done.
  rewrite bi.and_elim_r //.
Qed.

Lemma tc_environ_set: forall Delta i t x rho (TC : tc_environ Delta rho),
  temp_types Delta !! i = Some t -> tc_val' t x ->
  tc_environ Delta (mkEnviron (ge_of rho) (ve_of rho) (Map.set i ((` x) rho) (te_of rho))).
Proof.
  intros.
  destruct rho, TC as (TC & ? & ?); split3; auto; simpl in *.
  intros j tj Hj; destruct (TC j tj Hj) as (v & ? & ?).
  destruct (ident_eq i j).
  + subst; eexists; rewrite Map.gss.
    assert (tj = t) as -> by (rewrite Hj in H; inv H; done); eauto.
  + exists v.
    rewrite Map.gso //.
Qed.

Lemma obox_left2: forall Delta i P Q,
  temp_guard Delta i ->
  (local (tc_environ Delta) ∧ P ⊢ Q) ->  
  local (tc_environ Delta) ∧ obox Delta i P ⊢ obox Delta i Q.
Proof.
  intros ????? [H].
  split => ?; revert H; rewrite /local /lift1 /obox /subst /env_set; monPred.unseal; intros.
  iIntros "(%TC & H)".
  destruct (temp_types Delta !! i) eqn: Ht; last done.
  rewrite /monpred.monPred_defs.monPred_impl_def /=.
  iIntros (x rho -> ?); iApply H; iSplit; last by iApply "H".
  iPureIntro; eapply tc_environ_set; eauto.
Qed.

Lemma obox_left2': forall E Delta i P Q,
  temp_guard Delta i ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id E Delta ∗ P) ⊢ Q) ->
  local (tc_environ Delta) ∧ (<affine> allp_fun_id E Delta ∗ obox Delta i P) ⊢ obox Delta i Q.
Proof.
  intros ?????? [H].
  split => ?; revert H; rewrite /local /lift1 /obox /subst /env_set; monPred.unseal; intros.
  iIntros "(%TC & Ha & H)".
  destruct (temp_types Delta !! i) eqn: Ht; last done.
  rewrite /monpred.monPred_defs.monPred_impl_def /=.
  iIntros (x rho -> ?); iApply H; iSplit; last iSplitR "H"; last by iApply "H".
  - iPureIntro; eapply tc_environ_set; eauto.
  - rewrite !monPred_at_affinely //.
Qed.

Lemma obox_sepcon: forall Delta i P Q,
  obox Delta i P ∗ obox Delta i Q ⊢ obox Delta i (P ∗ Q).
Proof.
  intros.
  rewrite /obox.
  iIntros "(HP & HQ)" (?).
  destruct (temp_types Delta !! i); last done.
  iIntros (?); rewrite subst_sepcon; iSplitL "HP"; [iApply "HP" | iApply "HQ"]; done.
Qed.

Definition oboxopt Delta ret P :=
  match ret with
  | Some id => obox Delta id P
  | _ => P
  end.

Definition odiaopt Delta ret P :=
  match ret with
  | Some id => odia Delta id P
  | _ => P
  end.

Definition temp_guard_opt (Delta : tycontext) (i: option ident): Prop :=
  match i with
  | Some i => temp_guard Delta i
  | None => True
  end.

Lemma substopt_oboxopt: forall Delta id v (P: assert), assert_of (substopt id (`v) (oboxopt Delta id P)) ⊣⊢ oboxopt Delta id P.
Proof.
  intros.
  destruct id; [| done].
  apply subst_obox.
Qed.

Lemma oboxopt_closed: forall Delta i (P : assert),
  temp_guard_opt Delta i ->
  closed_wrt_vars (fun id => isSome ((match i with Some i' => insert_idset i' idset0 | None => idset0 end) !! id)) P ->
  oboxopt Delta i P ⊣⊢ P.
Proof.
  intros.
  destruct i; auto.
  simpl in H0 |- *.
  apply obox_closed; auto.
  replace (eq i) with ((fun id : ident => isSome ((insert_idset i idset0) !! id))); auto.
  extensionality id.
  unfold insert_idset.
  destruct (ident_eq id i).
  - subst.
    setoid_rewrite Maps.PTree.gss.
    simpl.
    apply prop_ext.
    tauto.
  - setoid_rewrite Maps.PTree.gso; last done.
    unfold idset0.
    rewrite Maps.PTree.gempty.
    simpl.
    assert (i <> id) by congruence.
    apply prop_ext.
    tauto.
Qed.

Lemma oboxopt_T: forall Delta i (P: assert),
  temp_guard_opt Delta i ->
  local (tc_environ Delta) ∧ oboxopt Delta i P ⊢ P.
Proof.
  intros.
  destruct i; [|rewrite /= bi.and_elim_r //].
  apply obox_T; auto.
Qed.

Lemma odiaopt_D: forall Delta i (P: assert),
  temp_guard_opt Delta i ->
  local (tc_environ Delta) ∧ P ⊢ odiaopt Delta i P.
Proof.
  intros.
  destruct i; [|rewrite /= bi.and_elim_r //].
  apply odia_D; auto.
Qed.

Lemma oboxopt_odiaopt: forall Delta i P, temp_guard_opt Delta i -> oboxopt Delta i (odiaopt Delta i P) ⊣⊢ odiaopt Delta i P.
Proof.
  intros.
  destruct i; auto.
  apply obox_odia; auto.
Qed.

Lemma oboxopt_K: forall Delta i P Q, (P ⊢ Q) -> oboxopt Delta i P ⊢ oboxopt Delta i Q.
Proof.
  intros.
  destruct i; last done.
  apply obox_K; auto.
Qed.

Lemma odiaopt_derives_EX_substopt: forall Delta i P,
  odiaopt Delta i P ⊢ ∃ v : val, assert_of (substopt i (` v) P).
Proof.
  intros.
  destruct i; [apply odia_derives_EX_subst |].
  split => rho; monPred.unseal.
  by iIntros "H"; iExists Vundef.
Qed.

Lemma oboxopt_left2: forall Delta i P Q,
  temp_guard_opt Delta i ->
  (local (tc_environ Delta) ∧ P ⊢ Q) ->  
  local (tc_environ Delta) ∧ oboxopt Delta i P ⊢ oboxopt Delta i Q.
Proof.
  intros.
  destruct i; [apply obox_left2; auto |].
  auto.
Qed.

Lemma oboxopt_left2': forall E Delta i P Q,
  temp_guard_opt Delta i ->
  (local (tc_environ Delta) ∧ (<affine> allp_fun_id E Delta ∗ P) ⊢ Q) ->  
  local (tc_environ Delta) ∧ (<affine> allp_fun_id E Delta ∗ oboxopt Delta i P) ⊢ oboxopt Delta i Q.
Proof.
  intros.
  destruct i; [apply obox_left2'; auto |].
  auto.
Qed.

Lemma oboxopt_sepcon: forall Delta i P Q,
  oboxopt Delta i P ∗ oboxopt Delta i Q ⊢ oboxopt Delta i (P ∗ Q).
Proof.
  intros.
  destruct i; last done.
  apply obox_sepcon.
Qed.

End mpred.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_conseq:
  forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS OK_ty Σ} {CS: compspecs} E (Delta: tycontext),
  forall P' (R': ret_assert) P c (R: ret_assert),
    (local (tc_environ Delta) ∧ (<affine> allp_fun_id E Delta ∗ P) ⊢ (|={E}=> P')) ->
    (local (tc_environ Delta) ∧ (<affine> allp_fun_id E Delta ∗ RA_normal R') ⊢ (|={E}=> RA_normal R)) ->
    (local (tc_environ Delta) ∧ (<affine> allp_fun_id E Delta ∗ RA_break R') ⊢ (|={E}=> RA_break R)) ->
    (local (tc_environ Delta) ∧ (<affine> allp_fun_id E Delta ∗ RA_continue R') ⊢ (|={E}=> RA_continue R)) ->
    (forall vl, local (tc_environ Delta) ∧ (<affine> allp_fun_id E Delta ∗ RA_return R' vl) ⊢ (RA_return R vl)) ->
   semax E Delta P' c R' -> semax E Delta P c R.

End CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE.

Module GenCConseqFacts
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CConseq: CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE with Module CSHL_Def := Def).

Import Def.
Import CConseq.

Section mpred.

Context `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs}.

Lemma semax_pre_post_indexed_fupd:
  forall E (Delta: tycontext),
 forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) ∧ P ⊢ (|={E}=> P')) ->
    (local (tc_environ Delta) ∧ RA_normal R' ⊢ (|={E}=> RA_normal R)) ->
    (local (tc_environ Delta) ∧ RA_break R' ⊢ (|={E}=> RA_break R)) ->
    (local (tc_environ Delta) ∧ RA_continue R' ⊢ (|={E}=> RA_continue R)) ->
    (forall vl, local (tc_environ Delta) ∧ RA_return R' vl ⊢ (RA_return R vl)) ->
   semax E Delta P' c R' -> semax E Delta P c R.
Proof.
  intros.
  eapply semax_conseq; [.. | exact H4]; intros; rewrite bi.affinely_elim_emp left_id //.
Qed.

Lemma semax_pre_post_fupd:
  forall E (Delta: tycontext),
 forall P' (R': ret_assert) P c (R: ret_assert) ,
    (local (tc_environ Delta) ∧ P ⊢ (|={E}=> P')) ->
    (local (tc_environ Delta) ∧ RA_normal R' ⊢ (|={E}=> RA_normal R)) ->
    (local (tc_environ Delta) ∧ RA_break R' ⊢ (|={E}=> RA_break R)) ->
    (local (tc_environ Delta) ∧ RA_continue R' ⊢ (|={E}=> RA_continue R)) ->
    (forall vl, local (tc_environ Delta) ∧ RA_return R' vl ⊢ (RA_return R vl)) ->
   semax E Delta P' c R' -> semax E Delta P c R.
Proof.
  intros.
  eapply semax_pre_post_indexed_fupd; [.. | exact H4]; try intros;
  try apply derives_fupd_derives_fupd; auto.
Qed.

Lemma semax_pre_indexed_fupd:
 forall P' E Delta P c R,
     (local (tc_environ Delta) ∧ P ⊢ (|={E}=> P')) ->
     semax E Delta P' c R  -> semax E Delta P c R.
Proof.
  intros; eapply semax_pre_post_indexed_fupd; eauto;
  intros; reduce2derives; done.
Qed.

Lemma semax_post_indexed_fupd:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (local (tc_environ Delta) ∧ RA_normal R' ⊢ (|={E}=> RA_normal R)) ->
   (local (tc_environ Delta) ∧ RA_break R' ⊢ (|={E}=> RA_break R)) ->
   (local (tc_environ Delta) ∧ RA_continue R' ⊢ (|={E}=> RA_continue R)) ->
   (forall vl, local (tc_environ Delta) ∧ RA_return R' vl ⊢ (RA_return R vl)) ->
   semax E Delta P c R' ->  semax E Delta P c R.
Proof.
  intros; eapply semax_pre_post_indexed_fupd; try eassumption.
  apply derives_fupd_refl.
Qed.

Lemma semax_post''_indexed_fupd: forall R' E Delta R P c,
           (local (tc_environ Delta) ∧ R' ⊢ (|={E}=> RA_normal R)) ->
      semax E Delta P c (normal_ret_assert R') ->
      semax E Delta P c R.
Proof.
 intros. eapply semax_post_indexed_fupd, H0; simpl; auto; intros; rewrite right_absorb; apply bi.False_elim.
Qed.

Lemma semax_pre_fupd:
 forall P' E Delta P c R,
     (local (tc_environ Delta) ∧ P ⊢ (|={E}=> P')) ->
     semax E Delta P' c R  -> semax E Delta P c R.
Proof.
intros; eapply semax_pre_post_fupd; eauto; intros; rewrite bi.and_elim_r //; apply fupd_intro.
Qed.

Lemma semax_post_fupd:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (local (tc_environ Delta) ∧ RA_normal R' ⊢ (|={E}=> RA_normal R)) ->
   (local (tc_environ Delta) ∧ RA_break R' ⊢ (|={E}=> RA_break R)) ->
   (local (tc_environ Delta) ∧ RA_continue R' ⊢ (|={E}=> RA_continue R)) ->
   (forall vl, local (tc_environ Delta) ∧ RA_return R' vl ⊢ (RA_return R vl)) ->
   semax E Delta P c R' ->  semax E Delta P c R.
Proof.
  intros; eapply semax_pre_post_fupd; try eassumption.
  apply derives_fupd_refl.
Qed.

Lemma semax_post'_fupd: forall R' E Delta R P c,
           (local (tc_environ Delta) ∧ R' ⊢ (|={E}=> R)) ->
      semax E Delta P c (normal_ret_assert R') ->
      semax E Delta P c (normal_ret_assert R).
Proof.
 intros. eapply semax_post_fupd; eauto; simpl; auto; intros; rewrite right_absorb //; apply fupd_intro.
Qed.

Lemma semax_post''_fupd: forall R' E Delta R P c,
           (local (tc_environ Delta) ∧ R' ⊢ (|={E}=> RA_normal R)) ->
      semax E Delta P c (normal_ret_assert R') ->
      semax E Delta P c R.
Proof.
 intros. eapply semax_post_fupd; eauto; simpl; auto; intros; rewrite right_absorb //; apply bi.False_elim.
Qed.

Lemma semax_pre_post'_fupd: forall P' R' E Delta R P c,
      (local (tc_environ Delta) ∧ P ⊢ (|={E}=> P')) ->
      (local (tc_environ Delta) ∧ R' ⊢ (|={E}=> R)) ->
      semax E Delta P' c (normal_ret_assert R') ->
      semax E Delta P c (normal_ret_assert R).
Proof.
 intros.
 eapply semax_pre_fupd; eauto.
 eapply semax_post'_fupd; eauto.
Qed.

Lemma semax_pre_post''_fupd: forall P' R' E Delta R P c,
      (local (tc_environ Delta) ∧ P ⊢ (|={E}=> P')) ->
      (local (tc_environ Delta) ∧ R' ⊢ (|={E}=> RA_normal R)) ->
      semax E Delta P' c (normal_ret_assert R') ->
      semax E Delta P c R.
Proof.
 intros.
 eapply semax_pre_fupd; eauto.
 eapply semax_post''_fupd; eauto.
Qed.

End mpred.

End GenCConseqFacts.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_pre_post : forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs},
 forall P' (R': ret_assert) E Delta P c (R: ret_assert) ,
    (local (tc_environ Delta) ∧ P ⊢ P') ->
    (local (tc_environ Delta) ∧ RA_normal R' ⊢ RA_normal R) ->
    (local (tc_environ Delta) ∧ RA_break R' ⊢ RA_break R) ->
    (local (tc_environ Delta) ∧ RA_continue R' ⊢ RA_continue R) ->
    (forall vl, local (tc_environ Delta) ∧ RA_return R' vl ⊢ RA_return R vl) ->
   semax E Delta P' c R' -> semax E Delta P c R.

End CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE.

Module GenConseq
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CConseq: CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE with Module CSHL_Def := Def): CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module CConseqFacts := GenCConseqFacts (Def) (CConseq).
Import CSHL_Def.
Import CConseq.
Import CConseqFacts.

Lemma semax_pre_post : forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs},
 forall P' (R': ret_assert) E Delta P c (R: ret_assert) ,
    (local (tc_environ Delta) ∧ P ⊢ P') ->
    (local (tc_environ Delta) ∧ RA_normal R' ⊢ RA_normal R) ->
    (local (tc_environ Delta) ∧ RA_break R' ⊢ RA_break R) ->
    (local (tc_environ Delta) ∧ RA_continue R' ⊢ RA_continue R) ->
    (forall vl, local (tc_environ Delta) ∧ RA_return R' vl ⊢ RA_return R vl) ->
   semax E Delta P' c R' -> semax E Delta P c R.
Proof.
  intros; eapply semax_pre_post_fupd, H4; eauto.
Qed.

End GenConseq.

Module GenConseqFacts
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def).

Import Def.
Import Conseq.

Section mpred.

Context `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs}.

(* Copied from canon.v *)

Lemma semax_pre: 
 forall P' E Delta P c R,
     (local (tc_environ Delta) ∧ P ⊢ P') ->
     semax E Delta P' c R  -> semax E Delta P c R.
Proof.
  intros; eapply semax_pre_post; eauto;
  intros; apply ENTAIL_refl.
Qed.

Lemma semax_pre_simple:
 forall P' E Delta P c R,
     (P ⊢ P') ->
     semax E Delta P' c R  -> semax E Delta P c R.
Proof.
intros; eapply semax_pre; [| eauto].
rewrite bi.and_elim_r //.
Qed.

Lemma semax_post:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (local (tc_environ Delta) ∧ RA_normal R' ⊢ RA_normal R) ->
   (local (tc_environ Delta) ∧ RA_break R' ⊢ RA_break R) ->
   (local (tc_environ Delta) ∧ RA_continue R' ⊢ RA_continue R) ->
   (forall vl, local (tc_environ Delta) ∧ RA_return R' vl ⊢ RA_return R vl) ->
   semax E Delta P c R' ->  semax E Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply ENTAIL_refl.
Qed.

Lemma semax_post_simple:
 forall (R': ret_assert) E Delta (R: ret_assert) P c,
   (RA_normal R' ⊢ RA_normal R) ->
   (RA_break R' ⊢ RA_break R) ->
   (RA_continue R' ⊢ RA_continue R) ->
   (forall vl, RA_return R' vl ⊢ RA_return R vl) ->
   semax E Delta P c R' ->  semax E Delta P c R.
Proof.
  intros; eapply semax_post; [.. | eauto]; intros; reduce2derives; auto.
Qed.

Lemma semax_post': forall R' E Delta R P c,
           (local (tc_environ Delta) ∧ R' ⊢ R) ->
      semax E Delta P c (normal_ret_assert R') ->
      semax E Delta P c (normal_ret_assert R).
Proof.
 intros. eapply semax_post; eauto; simpl; auto; intros; rewrite bi.and_elim_r //.
Qed.

Lemma semax_pre_post': forall P' R' E Delta R P c,
      (local (tc_environ Delta) ∧ P ⊢ P') ->
      (local (tc_environ Delta) ∧ R' ⊢ R) ->
      semax E Delta P' c (normal_ret_assert R') ->
      semax E Delta P c (normal_ret_assert R).
Proof. intros.
 eapply semax_pre; eauto.
 eapply semax_post'; eauto.
Qed.

(* Copied from canon.v end. *)

Lemma semax_post'': forall R' E Delta R P c,
           (local (tc_environ Delta) ∧ R' ⊢ RA_normal R) ->
      semax E Delta P c (normal_ret_assert R') ->
      semax E Delta P c R.
Proof.
 intros. eapply semax_post; eauto; simpl; auto; intros; rewrite bi.and_elim_r; apply bi.False_elim.
Qed.

Lemma semax_pre_post'': forall P' R' E Delta R P c,
      (local (tc_environ Delta) ∧ P ⊢ P') ->
      (local (tc_environ Delta) ∧ R' ⊢ RA_normal R) ->
      semax E Delta P' c (normal_ret_assert R') ->
      semax E Delta P c R.
Proof.
 intros.
 eapply semax_pre; eauto.
 eapply semax_post''; eauto.
Qed.

End mpred.

End GenConseqFacts.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_extract_exists:
  forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs},
  forall (A : Type)  (P : A -> assert) c E (Delta: tycontext) (R: ret_assert),
  (forall x, semax E Delta (P x) c R) ->
   semax E Delta (∃ x:A, P x) c R.

End CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION.

Module GenExtrFacts
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def).

Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.

Section mpred.

Context `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs}.

Lemma semax_extract_prop:
  forall E Delta (PP: Prop) P c Q,
           (PP -> semax E Delta P c Q) ->
           semax E Delta (⌜PP⌝ ∧ P) c Q.
Proof.
  intros.
  eapply semax_pre with (∃ H: PP, P).
  + iIntros "(_ & %HP & ?)".
    by iExists HP.
  + apply semax_extract_exists, H.
Qed.

Lemma semax_orp:
  forall E Delta P1 P2 c Q,
           semax E Delta P1 c Q ->
           semax E Delta P2 c Q ->
           semax E Delta (P1 ∨ P2) c Q.
Proof.
  intros.
  eapply semax_pre with (∃ b: bool, if b then P1 else P2).
  + by iIntros "(_ & [? | ?])"; [iExists true | iExists false].
  + apply semax_extract_exists.
    intros.
    destruct x; auto.
Qed.

End mpred.

End GenExtrFacts.

Module GenIExtrFacts
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CConseq: CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def).

Module Conseq := GenConseq (Def) (CConseq).
Module CConseqFacts := GenCConseqFacts (Def) (CConseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import CConseq.
Import CConseqFacts.
Import Extr.
Import ExtrFacts.

Lemma semax_extract_later_prop:
  forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs},
  forall E Delta (PP: Prop) P c Q,
           (PP -> semax E Delta P c Q) ->
           semax E Delta ((▷ ⌜PP⌝) ∧ P) c Q.
Proof.
  intros.
  apply semax_extract_prop in H.
  eapply semax_pre_post_indexed_fupd; [.. | exact H].
  + by iIntros "(_ & >$ & $)".
  + apply derives_fupd_refl.
  + apply derives_fupd_refl.
  + apply derives_fupd_refl.
  + intros; rewrite bi.and_elim_r //.
Qed.

End GenIExtrFacts.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_forward:
  forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
 forall e1 e2 sh P,
   writable_share sh ->
   semax E Delta
          (▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗ P)))
          (Sassign e1 e2)
          (normal_ret_assert
             (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) ∗ P)).

End CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext) e1 e2 P,
   semax E Delta
          (∃ sh: share, ⌜writable_share sh⌝ ∧ ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗ (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) -∗ P))))
          (Sassign e1 e2)
          (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD.

Module StoreF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (StoreF: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import StoreF.

Theorem semax_store_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext) e1 e2 P,
   semax E Delta
          (∃ sh: share, ⌜writable_share sh⌝ ∧ ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗ (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) -∗ P))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Proof.
  intros.
  eapply semax_post'; [.. | eapply (semax_extract_exists _ _ _ _ _ (normal_ret_assert P))].
  + rewrite bi.and_elim_r //.
  + intros sh.
    apply semax_extract_prop; intro SH.
    eapply semax_pre_post', semax_store_forward; eauto.
    * rewrite bi.and_elim_r; apply bi.later_mono; rewrite -!assoc //.
    * iIntros "(_ & ? & H)"; by iApply "H".
Qed.

End StoreF2B.

Module StoreB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (StoreB: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import StoreB.

Theorem semax_store_forward:
  forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext) e1 e2 sh P,
   writable_share sh ->
   semax E Delta
          (▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗ P)))
          (Sassign e1 e2)
          (normal_ret_assert
             (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) ∗ P)).
Proof.
  intros.
  eapply semax_pre; [| apply semax_store_backward].
  iIntros "(_ & H)"; iExists sh; iSplit; first done.
  iNext.
  iApply (bi.and_mono with "H"); first done.
  iIntros "($ & $) $".
Qed.

End StoreB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_union_hack_forward:
  forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
 forall (e1 e2 : expr) (t2: type) (ch ch' : memory_chunk) (sh : share) (P : assert),
       (numeric_type (typeof e1) && numeric_type t2)%bool = true ->
       access_mode (typeof e1) = By_value ch ->
       access_mode t2 = By_value ch' ->
       decode_encode_val_ok ch ch' ->
       writable_share sh ->
       semax E Delta
         (▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1))) ∧
              ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1))
                ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1)))
               ∗ P)))
         (Sassign e1 e2)
         (normal_ret_assert
            (∃ v':val,
              (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) ∧
              (assert_of ((` (mapsto sh t2)) (eval_lvalue e1) (`v')) ∗ P))).

End CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_union_hack_backward:
 forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext) e1 e2 P,
   semax E Delta
          (∃ (t2:type) (ch ch': memory_chunk) (sh: share),
             ⌜(numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh⌝ ∧
             ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1))) ∧
             ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1))
                      ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1))) ∗
              (∀ v': val,
                 assert_of (`(mapsto sh t2) (eval_lvalue e1) (`v')) -∗
                  (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) →
                      (  P)))))
          (Sassign e1 e2)
          (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD.

Module StoreUnionHackF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (StoreUnionHackF: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import StoreUnionHackF.

Theorem semax_store_union_hack_backward:
 forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext) e1 e2 P,
   semax E Delta
          (∃ (t2:type) (ch ch': memory_chunk) (sh: share),
             ⌜(numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh⌝ ∧
             ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1))) ∧
             ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1))
                      ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1))) ∗
              (∀ v': val,
                 assert_of (`(mapsto sh t2) (eval_lvalue e1) (`v')) -∗
                  (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) →
                      (  P)))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Proof.
  intros.
  eapply semax_post'; [.. | eapply (semax_extract_exists _ _ _ _ _ (normal_ret_assert P))];
    [rewrite bi.and_elim_r // | intro t2].
  eapply semax_post'; [.. | eapply (semax_extract_exists _ _ _ _ _ (normal_ret_assert P))];
    [rewrite bi.and_elim_r // | intro ch].
  eapply semax_post'; [.. | eapply (semax_extract_exists _ _ _ _ _ (normal_ret_assert P))];
    [rewrite bi.and_elim_r // | intro ch'].
  eapply semax_post'; [.. | eapply (semax_extract_exists _ _ _ _ _ (normal_ret_assert P))];
    [rewrite bi.and_elim_r // | intro sh].
  apply semax_extract_prop; intros [? [? [? [? SH]]]].
  eapply semax_post'; [.. | eapply semax_store_union_hack_forward; eauto].
  iIntros "(_ & % & ? & ? & H)".
  by iSpecialize ("H" with "[$]"); iApply "H".
Qed.

End StoreUnionHackF2B.

Module StoreUnionHackB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (StoreUnionHackB: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import StoreUnionHackB.

Theorem semax_store_union_hack_forward:
  forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
 forall (e1 e2 : expr) (t2: type) (ch ch' : memory_chunk) (sh : share) (P : assert),
       (numeric_type (typeof e1) && numeric_type t2)%bool = true ->
       access_mode (typeof e1) = By_value ch ->
       access_mode t2 = By_value ch' ->
       decode_encode_val_ok ch ch' ->
       writable_share sh ->
       semax E Delta
         (▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1))) ∧
              ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1))
                ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1)))
               ∗ P)))
         (Sassign e1 e2)
         (normal_ret_assert
            (∃ v':val,
              (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) ∧
              (assert_of ((` (mapsto sh t2)) (eval_lvalue e1) (`v')) ∗ P))).
Proof.
  intros.
  eapply semax_pre; [| apply semax_store_union_hack_backward].
  iIntros "(_ & H)"; iExists t2, ch, ch', sh.
  iSplit; first done.
  iNext.
  iApply (bi.and_mono with "H"); first done.
  iIntros "($ & $)"; eauto.
Qed.

End StoreUnionHackB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_SASSIGN_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_store_union_hack_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) e1 e2,
    semax E Delta
       ((∃ sh: share, ⌜writable_share sh⌝ ∧
             ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗
              (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) -∗ P))))
          ∨ (∃ (t2:type) (ch ch': memory_chunk) (sh: share),
             ⌜(numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh⌝ ∧
             ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) )
                      ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1))) ∗
              (∀ v': val,
                 assert_of (`(mapsto sh t2) (eval_lvalue e1) (`v')) -∗
                    (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) →
                      (P)))))
       )
        (Sassign e1 e2) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_SASSIGN_BACKWARD.

Module ToSassign
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (StoreB: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD with Module CSHL_Def := Def)
       (StoreUnionHackB: CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_SASSIGN_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).

Import Def.
Import Conseq.
Import ConseqFacts.
Import StoreB.
Import StoreUnionHackB.
Import ExtrFacts.

Theorem semax_store_store_union_hack_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) e1 e2,
    semax E Delta
       ((∃ sh: share, ⌜writable_share sh⌝ ∧
             ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗
              (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) -∗ P))))
          ∨ (∃ (t2:type) (ch ch': memory_chunk) (sh: share),
             ⌜(numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh⌝ ∧
             ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) )
                      ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1))) ∗
              (∀ v': val,
                 assert_of (`(mapsto sh t2) (eval_lvalue e1) (`v')) -∗
                    (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) →
                      (P)))))
       )
        (Sassign e1 e2) (normal_ret_assert P).
Proof.
  intros.
  apply semax_orp.
  + apply semax_store_backward.
  + apply semax_store_union_hack_backward.
Qed.

End ToSassign.

Module Sassign2Store
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sassign: CLIGHT_SEPARATION_HOARE_LOGIC_SASSIGN_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sassign.

Theorem semax_store_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext) e1 e2 P,
   semax E Delta
          (∃ sh: share, ⌜writable_share sh⌝ ∧ ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             (assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) ∗ (assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2)))) -∗ P))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_store_store_union_hack_backward].
  apply bi.or_intro_l.
Qed.

End Sassign2Store.

Module Sassign2StoreUnionHack
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sassign: CLIGHT_SEPARATION_HOARE_LOGIC_SASSIGN_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_STORE_UNION_HACK_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sassign.

Theorem semax_store_union_hack_backward:
 forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext) e1 e2 P,
   semax E Delta
          (∃ (t2:type) (ch ch': memory_chunk) (sh: share),
             ⌜(numeric_type (typeof e1) && numeric_type t2)%bool = true /\
                 access_mode (typeof e1) = By_value ch /\
                 access_mode t2 = By_value ch' /\
                 decode_encode_val_ok ch ch' /\
                 writable_share sh⌝ ∧
             ▷ ((tc_lvalue Delta e1 ∧ tc_expr Delta (Ecast e2 (typeof e1)))  ∧
             ((assert_of (`(mapsto_ sh (typeof e1)) (eval_lvalue e1))
                      ∧ assert_of (`(mapsto_ sh t2) (eval_lvalue e1))) ∗
              (∀ v': val,
                 assert_of (`(mapsto sh t2) (eval_lvalue e1) (`v')) -∗
                    (local  ((`decode_encode_val )
                         ((` force_val) ((`(sem_cast (typeof e2) (typeof e1))) (eval_expr e2))) (`ch) (`ch') (`v') )) →
                      (P)))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_store_store_union_hack_backward].
  apply bi.or_intro_r.
Qed.

End Sassign2StoreUnionHack.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_call_forward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
    forall A P Q x (F: assert) ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
           (retsig = Ctypes.Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  semax E Delta
          (((*▷*)((tc_expr Delta a) ∧ (tc_exprlist Delta argsig bl)))  ∧
         (assert_of (`(func_ptr E (mk_funspec  (argsig,retsig) cc A P Q)) (eval_expr a)) ∗
          (▷ (F ∗ assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
            (∃ old:val, assert_of (substopt ret (`old) F) ∗ maybe_retval (Q x) retsig ret)).

End CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_call_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
    forall ret a bl R,
  semax E Delta
         (∃ argsig: _, ∃ retsig: _, ∃ cc: _,
          ∃ A: _, ∃ P: _, ∃ Q: _, ∃ x: _,
         ⌜Cop.classify_fun (typeof a) =
             Cop.fun_case_f (typelist_of_type_list argsig) retsig cc /\
             (retsig = Ctypes.Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig⌝ ∧
          ((*▷*)((tc_expr Delta a) ∧ (tc_exprlist Delta argsig bl)))  ∧
         assert_of (`(func_ptr E (mk_funspec  (argsig,retsig) cc A P Q)) (eval_expr a)) ∗
          ▷(assert_of (fun rho => (P x (ge_of rho, eval_exprlist argsig bl rho))) ∗ oboxopt Delta ret (maybe_retval (Q x) retsig ret -∗ R)))
         (Scall ret a bl)
         (normal_ret_assert R).

End CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD.

Lemma fn_return_temp_guard : forall `{!heapGS Σ} Delta ret retsig, tc_fn_return Delta ret retsig ->
  temp_guard_opt Delta ret.
Proof.
  destruct ret; auto; simpl.
  rewrite /temp_guard.
  destruct (_ !! _); done.
Qed.

Module CallF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (CallF: CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import CallF.
  
Theorem semax_call_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
    forall ret a bl R,
  semax E Delta
         (∃ argsig: _, ∃ retsig: _, ∃ cc: _,
          ∃ A: _, ∃ P: _, ∃ Q: _, ∃ x: _,
         ⌜Cop.classify_fun (typeof a) =
             Cop.fun_case_f (typelist_of_type_list argsig) retsig cc /\
             (retsig = Ctypes.Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig⌝ ∧
          ((*▷*)((tc_expr Delta a) ∧ (tc_exprlist Delta argsig bl)))  ∧
         assert_of (`(func_ptr E (mk_funspec  (argsig,retsig) cc A P Q)) (eval_expr a)) ∗
          ▷(assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho)) ∗ oboxopt Delta ret (maybe_retval (Q x) retsig ret -∗ R)))
         (Scall ret a bl)
         (normal_ret_assert R).
Proof.
  intros.
  apply semax_extract_exists; intro argsig.
  apply semax_extract_exists; intro retsig.
  apply semax_extract_exists; intro cc.
  apply semax_extract_exists; intro A.
  apply semax_extract_exists; intro P.
  apply semax_extract_exists; intro Q.
  apply semax_extract_exists; intro x.
  apply semax_extract_prop; intros [? [? ?]].
  eapply semax_pre_post'; [.. | apply semax_call_forward; auto].
  + rewrite bi.and_elim_r; apply bi.and_mono; first done; apply bi.sep_mono; first done.
    apply bi.later_mono.
    rewrite comm //.
  + iIntros "(TC & % & H & ?)".
    rewrite substopt_oboxopt.
    iPoseProof (oboxopt_T with "[$TC $H]") as "H"; last by iApply "H".
    by eapply fn_return_temp_guard.
  + auto.
  + auto.
  + auto.
Qed.

End CallF2B.

Module CallB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (CallB: CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import CallB.
(*
Theorem semax_call_forward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
    forall A P Q ts x (F: assert) ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  semax E Delta
          ((▷((tc_expr Delta a) ∧ (tc_exprlist Delta (snd (split argsig)) bl)))  ∧
         (`(func_ptr E (mk_funspec  (argsig,retsig) cc A P Q)) (eval_expr a) ∧
          ▷(F ∗ `(P ts x: assert) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert
            (∃ old:val, substopt ret (`old) F ∗ maybe_retval (Q ts x) retsig ret)).
Proof.
  intros.
  eapply semax_pre; [| apply semax_call_backward].
  apply (exp_right argsig), (exp_right retsig), (exp_right cc), (exp_right A), (exp_right P), (exp_right Q), (exp_right NEP), (exp_right NEQ), (exp_right ts), (exp_right x).
  rewrite !andp_assoc.
  apply andp_right; [apply prop_right; auto |].
  apply andp_right; [solve_andp |].
  apply andp_right; [solve_andp |].
  rewrite andp_comm, imp_andp_adjoint.
  apply andp_left2.
  apply andp_left2.
  rewrite <- imp_andp_adjoint, andp_comm.
  apply later_left2.
  rewrite <- corable_andp_sepcon1 by (intro; apply corable_prop).
  rewrite sepcon_comm.
  apply sepcon_derives; auto.
  eapply derives_trans; [apply (odiaopt_D _ ret) |].
    1: destruct ret; hnf in H1 |- *; [destruct ((temp_types Delta) !! i) |]; auto; congruence.
  rewrite <- oboxopt_odiaopt.
    2: destruct ret; hnf in H1 |- *; [destruct ((temp_types Delta) !! i) |]; auto; congruence.
  apply oboxopt_K.
  rewrite <- wand_sepcon_adjoint.
  rewrite <- exp_sepcon1.
  apply sepcon_derives; auto.
  apply odiaopt_derives_∃_substopt.
Qed.
*)
Theorem semax_call_forward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
    forall A P Q x (F: assert) ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (typelist_of_type_list argsig) retsig cc ->
           (retsig = Ctypes.Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  semax E Delta
          (((*▷*)((tc_expr Delta a) ∧ (tc_exprlist Delta argsig bl)))  ∧
         (assert_of (`(func_ptr E (mk_funspec  (argsig,retsig) cc A P Q)) (eval_expr a)) ∗
          (▷ (F ∗ assert_of (fun rho => P x (ge_of rho, eval_exprlist argsig bl rho))))))
         (Scall ret a bl)
         (normal_ret_assert
            (∃ old:val, assert_of (substopt ret (`old) F) ∗ maybe_retval (Q x) retsig ret)).
Proof.
  intros.
  eapply semax_pre; [| apply semax_call_backward].
  iIntros "(#? & H)"; iExists argsig, retsig, cc, A, P, Q, x.
  iSplit; first done.
  iSplit; first by rewrite bi.and_elim_l.
  rewrite bi.and_elim_r; iDestruct "H" as "($ & H)".
  iNext; iDestruct "H" as "(F & $)".
  assert (temp_guard_opt Delta ret) by (eapply fn_return_temp_guard; done).
  iPoseProof (odiaopt_D _ ret F with "[$F]") as "H"; auto.
  rewrite -oboxopt_odiaopt //.
  iApply (oboxopt_K with "H").
  iIntros "? $".
  by iApply odiaopt_derives_EX_substopt.
Qed.

End CallB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_SET_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_set_forward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
    semax E Delta
        (▷ ( (tc_expr Delta e) ∧
             (tc_temp_id id (typeof e) Delta e) ∧
          P))
          (Sset id e)
        (normal_ret_assert
          (∃ old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) ∧
                            assert_of (subst id (`old) P))).

End CLIGHT_SEPARATION_HOARE_LOGIC_SET_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_set_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
    semax E Delta
        (▷ ( (tc_expr Delta e) ∧
             (tc_temp_id id (typeof e) Delta e) ∧
             assert_of (subst id (eval_expr e) P)))
          (Sset id e) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_load_forward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall  sh id P e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    (local (tc_environ Delta) ∧ P ⊢ <absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (` v2))) ->
    semax E Delta
       (▷ (tc_lvalue Delta e1 ∧
       ⌜tc_val (typeof e1) v2⌝ ∧
          P))
       (Sset id e1)
       (normal_ret_assert (∃ old:val, local (`eq (eval_id id) (` v2)) ∧
                                          (assert_of (subst id (`old) P)))).

End CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_load_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e1,
    semax E Delta
        (∃ sh: share, ∃ t2: type, ∃ v2: val,
              ⌜typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e1) t2 = true /\
                  readable_share sh⌝ ∧
         ▷ ((tc_lvalue Delta e1 ∧
              ⌜tc_val (typeof e1) v2⌝ ∧
              (<absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2)))) ∧
              assert_of (subst id (`v2) P)))
        (Sset id e1) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_cast_load_forward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall sh id P e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    (local (tc_environ Delta) ∧ P ⊢ <absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ->
    semax E Delta
       (▷ ( (tc_lvalue Delta e1) ∧
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) ∧
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (∃ old:val, local (`eq (eval_id id) (subst id (`old) (`(eval_cast (typeof e1) t1 v2)))) ∧
                                          (assert_of (subst id (`old) P)))).

End CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_cast_load_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
    semax E Delta
        (∃ sh: share, ∃ e1: expr, ∃ t1: type, ∃ v2: val,
              ⌜e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh⌝ ∧
         ▷ ( (tc_lvalue Delta e1) ∧
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) ∧
              (<absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ∧
              assert_of (subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P)))
        (Sset id e) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD.

Module LoadF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (LoadF: CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import LoadF.

Theorem semax_load_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e1,
    semax E Delta
        (∃ sh: share, ∃ t2: type, ∃ v2: val,
              ⌜typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e1) t2 = true /\
                  readable_share sh⌝ ∧
         ▷ ((tc_lvalue Delta e1 ∧
              ⌜tc_val (typeof e1) v2⌝ ∧
              (<absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2)))) ∧
              assert_of (subst id (`v2) P)))
        (Sset id e1) (normal_ret_assert P).
Proof.
  intros.
  apply semax_extract_exists; intro sh.
  apply semax_extract_exists; intro t2.
  apply semax_extract_exists; intro v2.
  apply semax_extract_prop; intros [? [? ?]].
  eapply semax_pre_post', semax_load_forward; eauto.
  + rewrite bi.and_elim_r -!assoc //.
  + split => rho; rewrite /subst; monPred.unseal.
    iIntros "(%TC & % & % & ?)"; super_unfold_lift; subst.
    rewrite bi.and_elim_r.
    unfold typeof_temp in H; destruct (_ !! _) eqn: Ht; last done.
    erewrite <- (subst_self P _ _ _ _ rho); try done.
    rewrite /subst env_set_env_set //.
  + rewrite bi.and_elim_r bi.and_elim_l //.
Qed.

End LoadF2B.

Module LoadB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (LoadB: CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import LoadB.

Theorem semax_load_forward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall  sh id P e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    (local (tc_environ Delta) ∧ P ⊢ <absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (` v2))) ->
    semax E Delta
       (▷ ( (tc_lvalue Delta e1) ∧
       ⌜tc_val (typeof e1) v2⌝ ∧
          P))
       (Sset id e1)
       (normal_ret_assert (∃ old:val, local (`eq (eval_id id) (` v2)) ∧
                                          (assert_of (subst id (`old) P)))).
Proof.
  intros.
  eapply semax_pre; [| apply semax_load_backward].
  iIntros "(#? & H)"; iExists sh, t2, v2.
  iSplit; first done.
  iNext.
  rewrite -!assoc; iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r.
  iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r.
  iSplit; first (iApply H2; iFrame; auto).
  iStopProof; split => rho; rewrite /subst /local; monPred.unseal.
  rewrite monPred_at_intuitionistically.
  iIntros "(% & ?)"; iExists (eval_id id rho).
  iSplit; first by iPureIntro; apply eval_id_same.
  unfold typeof_temp in H; destruct (_ !! _) eqn: Ht; last done.
  erewrite <- (subst_self P _ _ _ _ rho); try done.
  rewrite /subst env_set_env_set //.
Qed.

End LoadB2F.

Module CastLoadF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (CastLoadF: CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import CastLoadF.

Theorem semax_cast_load_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
    semax E Delta
        (∃ sh: share, ∃ e1: expr, ∃ t1: type, ∃ v2: val,
              ⌜e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh⌝ ∧
         ▷ ( (tc_lvalue Delta e1) ∧
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) ∧
              (<absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ∧
              assert_of (subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P)))
        (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  apply semax_extract_exists; intro sh.
  apply semax_extract_exists; intro e1.
  apply semax_extract_exists; intro t2.
  apply semax_extract_exists; intro v2.
  apply semax_extract_prop; intros [He [? [? ?]]].
  subst e.
  eapply semax_post'; [.. | eapply semax_cast_load_forward; eauto].
  + split => rho; rewrite /subst; monPred.unseal.
    iIntros "(%TC & % & % & ?)"; super_unfold_lift; subst.
    rewrite bi.and_elim_r.
    unfold typeof_temp in H; destruct (_ !! _) eqn: Ht; last done.
    erewrite <- (subst_self P _ _ _ _ rho); try done.
    rewrite /subst env_set_env_set H2 //.
  + rewrite bi.and_elim_r bi.and_elim_l //.
Qed.

End CastLoadF2B.

Module CastLoadB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (CastLoadB: CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import CastLoadB.

Theorem semax_cast_load_forward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall sh id P e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    (local (tc_environ Delta) ∧ P ⊢ <absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ->
    semax E Delta
       (▷ ( (tc_lvalue Delta e1) ∧
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) ∧
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (∃ old:val, local (`eq (eval_id id) (subst id (`old) (`(eval_cast (typeof e1) t1 v2)))) ∧
                                          (assert_of (subst id (`old) P)))).
Proof.
  intros.
  eapply semax_pre; [| apply semax_cast_load_backward].
  iIntros "(#? & ?)"; iExists sh, e1, t1, v2.
  iSplit; first done.
  iNext.
  iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r.
  iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r.
  iSplit; first by iApply H2; iFrame; auto.
  iStopProof; split => rho; rewrite /subst /local; monPred.unseal.
  rewrite monPred_at_intuitionistically.
  iIntros "(%TC & ?)"; super_unfold_lift; subst.
  iExists (eval_id id rho); iSplit; first by rewrite eval_id_same.
  rewrite env_set_env_set.
  unfold typeof_temp in H; destruct (_ !! _) eqn: Ht; last done.
  erewrite env_set_eval_id; done.
Qed.

End CastLoadB2F.

Lemma denote_tc_assert_False: forall `{!heapGS Σ} {CS: compspecs} X, assert_of (denote_tc_assert (tc_FF X)) ⊣⊢ False.
Proof.
  intros; split => rho; monPred.unseal; done.
Qed.

Module SetF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (SetF: CLIGHT_SEPARATION_HOARE_LOGIC_SET_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import SetF.

Theorem semax_set_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
    semax E Delta
        (▷ ( (tc_expr Delta e) ∧
             (tc_temp_id id (typeof e) Delta e) ∧
             assert_of (subst id (eval_expr e) P)))
          (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  apply semax_pre with (▷ (⌜exists t, ((temp_types Delta) !! id = Some t)⌝ ∧ (tc_expr Delta e ∧ tc_temp_id id (typeof e) Delta e ∧ assert_of (subst id (eval_expr e) P)))).
  { apply later_ENTAIL.
    iIntros "H"; iSplit; last rewrite bi.and_elim_r //.
    unfold tc_temp_id, typecheck_temp_id.
    destruct ((temp_types Delta) !! id); first eauto.
    rewrite denote_tc_assert_False; iDestruct "H" as "(_ & _ & [] & _)". }
  apply semax_pre with (▷ (tc_expr Delta e ∧ tc_temp_id id (typeof e) Delta e ∧ (⌜exists t, ((temp_types Delta) !! id = Some t)⌝ ∧ assert_of (subst id (eval_expr e) P)))).
  { apply later_ENTAIL.
    iIntros "(_ & $ & $)". }
  eapply semax_post'; [.. | eapply semax_set_forward; eauto].
  split => rho; rewrite /subst /local /lift1; monPred.unseal; unfold_lift.
  iIntros "(% & % & <- & (% & %) & P)".
  rewrite env_set_env_set; erewrite env_set_eval_id; done.
Qed.

End SetF2B.

Module SetB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (SetB: CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_SET_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import SetB.

Theorem semax_set_forward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
    semax E Delta
        (▷ ( (tc_expr Delta e) ∧
             (tc_temp_id id (typeof e) Delta e) ∧
          P))
          (Sset id e)
        (normal_ret_assert
          (∃ old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) ∧
                            assert_of (subst id (`old) P))).
Proof.
  intros.
  eapply semax_pre; [| apply semax_set_backward].
  apply later_ENTAIL.
  iIntros "(? & H)".
  iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r.
  iSplit; first rewrite bi.and_elim_l //.
  iStopProof.
  split => rho; rewrite /subst /local /lift1; monPred.unseal.
  rewrite monPred_at_affinely; iIntros "(% & H)".
  iExists (eval_id id rho); unfold_lift.
  rewrite env_set_env_set eval_id_same.
  rewrite /typecheck_temp_id.
  destruct (_ !! _) eqn: Ht; last by iDestruct "H" as "([] & _)".
  erewrite env_set_eval_id; try done.
  iDestruct "H" as "(_ & $)"; done.
Qed.

End SetB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_ptr_compare_forward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall P id cmp e1 e2 ty sh1 sh2,
    sh1 ≠ Share.bot -> sh2 ≠ Share.bot ->
   is_comparison cmp = true  ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   typecheck_tid_ptr_compare Delta id = true ->
   semax E Delta
        ( ▷ ( (tc_expr Delta e1) ∧
              (tc_expr Delta e2)  ∧

          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          (<absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1))) ∧
          (<absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2))) ∧
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (∃ old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) ∧
                       assert_of (subst id `(old) P))).

End CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_ptr_compare_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
   semax E Delta
        (∃ cmp: Cop.binary_operation, ∃ e1: expr, ∃ e2: expr,
         ∃ ty: type, ∃ sh1: share, ∃ sh2: share,
          ⌜e = Ebinop cmp e1 e2 ty /\
              sh1 ≠ Share.bot /\ sh2 ≠ Share.bot /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true⌝ ∧
            ( ▷ ( (tc_expr Delta e1) ∧
              (tc_expr Delta e2)  ∧
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          (<absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1))) ∧
          (<absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2))) ∧
          assert_of (subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))))
          (Sset id e)
        (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD.

Module PtrCmpF2B
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (PtrCmpF: CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_FORWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).
Import Def.
Import Conseq.
Import ConseqFacts.
Import Extr.
Import ExtrFacts.
Import PtrCmpF.

Theorem semax_ptr_compare_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
   semax E Delta
        (∃ cmp: Cop.binary_operation, ∃ e1: expr, ∃ e2: expr,
         ∃ ty: type, ∃ sh1: share, ∃ sh2: share,
          ⌜e = Ebinop cmp e1 e2 ty /\
              sh1 ≠ Share.bot /\ sh2 ≠ Share.bot /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true⌝ ∧
            ( ▷ ( (tc_expr Delta e1) ∧
              (tc_expr Delta e2)  ∧
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          (<absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1))) ∧
          (<absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2))) ∧
          assert_of (subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))))
          (Sset id e)
          (normal_ret_assert P).
Proof.
  intros.
  apply semax_extract_exists; intro cmp.
  apply semax_extract_exists; intro e1.
  apply semax_extract_exists; intro e2.
  apply semax_extract_exists; intro ty.
  apply semax_extract_exists; intro sh1.
  apply semax_extract_exists; intro sh2.
  apply semax_extract_prop; intros [He [? [? [? [? [? ?]]]]]].
  subst e.
  eapply semax_post'; [.. | eapply semax_ptr_compare_forward; eauto].
  split => rho; rewrite /local /subst /lift1; monPred.unseal; unfold_lift.
  iIntros "(% & % & <- & H)".
  rewrite env_set_env_set.
  unfold typecheck_tid_ptr_compare in *.
  destruct (_ !! _) eqn: Ht; last done.
  erewrite env_set_eval_id; done.
Qed.

End PtrCmpF2B.

Module PtrCmpB2F
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (PtrCmpB: CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_FORWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Import Def.
Import Conseq.
Import ConseqFacts.
Import PtrCmpB.

Theorem semax_ptr_compare_forward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall P id cmp e1 e2 ty sh1 sh2,
    sh1 ≠ Share.bot -> sh2 ≠ Share.bot ->
   is_comparison cmp = true  ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   typecheck_tid_ptr_compare Delta id = true ->
   semax E Delta
        ( ▷ ( (tc_expr Delta e1) ∧
              (tc_expr Delta e2)  ∧

          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          (<absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1))) ∧
          (<absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2))) ∧
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (∃ old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) ∧
                       assert_of (subst id `(old) P))).
Proof.
  intros.
  eapply semax_pre; [| apply semax_ptr_compare_backward].
  iIntros "(#? & H)"; iExists cmp, e1, e2, ty, sh1, sh2.
  iSplit; first by iPureIntro.
  iNext.
  repeat (iSplit; first rewrite bi.and_elim_l //; rewrite bi.and_elim_r).
  iStopProof.
  split => rho; rewrite /local /subst /lift1; monPred.unseal; unfold_lift.
  rewrite monPred_at_intuitionistically.
  iIntros "(% & H)".
  iExists (eval_id id rho).
  rewrite env_set_env_set eval_id_same.
  unfold typecheck_tid_ptr_compare in *.
  destruct (_ !! _) eqn: Ht; last done.
  erewrite env_set_eval_id; first iFrame; done.
Qed.

End PtrCmpB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_set_ptr_compare_load_cast_load_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
    semax E Delta
       ((((▷ ( (tc_expr Delta e) ∧
             (tc_temp_id id (typeof e) Delta e) ∧
             assert_of (subst id (eval_expr e) P))) ∨
        (∃ cmp: Cop.binary_operation, ∃ e1: expr, ∃ e2: expr,
         ∃ ty: type, ∃ sh1: share, ∃ sh2: share,
          ⌜e = Ebinop cmp e1 e2 ty /\
              sh1 ≠ Share.bot /\ sh2 ≠ Share.bot /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true⌝ ∧
            ( ▷ ( (tc_expr Delta e1) ∧
              (tc_expr Delta e2)  ∧
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          (<absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1))) ∧
          (<absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2))) ∧
          assert_of (subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))))) ∨
        (∃ sh: share, ∃ t2: type, ∃ v2: val,
              ⌜typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh⌝ ∧
         ▷ ((tc_lvalue Delta e ∧
              ⌜tc_val (typeof e) v2⌝ ∧
              (<absorb> assert_of (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2)))) ∧
              assert_of (subst id (`v2) P)))) ∨
        (∃ sh: share, ∃ e1: expr, ∃ t1: type, ∃ v2: val,
              ⌜e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh⌝ ∧
         ▷ (tc_lvalue Delta e1 ∧
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) ∧
              (<absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ∧
              assert_of (subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P))))
        (Sset id e) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD.

Module ToSset
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Extr: CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION with Module CSHL_Def := Def)
       (SetB: CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD with Module CSHL_Def := Def)
       (PtrCmpB: CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD with Module CSHL_Def := Def)
       (LoadB: CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD with Module CSHL_Def := Def)
       (CastLoadB: CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).
Module ExtrFacts := GenExtrFacts (Def) (Conseq) (Extr).

Import Def.
Import Conseq.
Import ConseqFacts.
Import SetB.
Import PtrCmpB.
Import LoadB.
Import CastLoadB.
Import ExtrFacts.

Theorem semax_set_ptr_compare_load_cast_load_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
    semax E Delta
       ((((▷ ( (tc_expr Delta e) ∧
             (tc_temp_id id (typeof e) Delta e) ∧
             assert_of (subst id (eval_expr e) P))) ∨
        (∃ cmp: Cop.binary_operation, ∃ e1: expr, ∃ e2: expr,
         ∃ ty: type, ∃ sh1: share, ∃ sh2: share,
          ⌜e = Ebinop cmp e1 e2 ty /\
              sh1 ≠ Share.bot /\ sh2 ≠ Share.bot /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true⌝ ∧
            ( ▷ ( (tc_expr Delta e1) ∧
              (tc_expr Delta e2)  ∧
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          (<absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1))) ∧
          (<absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2))) ∧
          assert_of (subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))))) ∨
        (∃ sh: share, ∃ t2: type, ∃ v2: val,
              ⌜typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh⌝ ∧
         ▷ ((tc_lvalue Delta e ∧
              ⌜tc_val (typeof e) v2⌝ ∧
              (<absorb> assert_of (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2)))) ∧
              assert_of (subst id (`v2) P)))) ∨
        (∃ sh: share, ∃ e1: expr, ∃ t1: type, ∃ v2: val,
              ⌜e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh⌝ ∧
         ▷ ( (tc_lvalue Delta e1) ∧
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) ∧
              (<absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ∧
              assert_of (subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P))))
        (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  apply semax_orp; [apply semax_orp; [apply semax_orp |] |].
  + apply semax_set_backward.
  + apply semax_ptr_compare_backward.
  + apply semax_load_backward.
  + apply semax_cast_load_backward.
Qed.

End ToSset.

Module Sset2Set
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sset: CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sset.

Theorem semax_set_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
    semax E Delta
        (▷ ( (tc_expr Delta e) ∧
             (tc_temp_id id (typeof e) Delta e) ∧
             assert_of (subst id (eval_expr e) P)))
          (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_set_ptr_compare_load_cast_load_backward].
  iIntros; iLeft; iLeft; iLeft; done.
Qed.

End Sset2Set.

Module Sset2PtrCmp
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sset: CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sset.

Theorem semax_ptr_compare_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
   semax E Delta
        (∃ cmp: Cop.binary_operation, ∃ e1: expr, ∃ e2: expr,
         ∃ ty: type, ∃ sh1: share, ∃ sh2: share,
          ⌜e = Ebinop cmp e1 e2 ty /\
              sh1 ≠ Share.bot /\ sh2 ≠ Share.bot /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true⌝ ∧
            ( ▷ ( (tc_expr Delta e1) ∧
              (tc_expr Delta e2)  ∧
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) ∧
          (<absorb> assert_of (`(mapsto_ sh1 (typeof e1)) (eval_expr e1))) ∧
          (<absorb> assert_of (`(mapsto_ sh2 (typeof e2)) (eval_expr e2))) ∧
          assert_of (subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))))
          (Sset id e)
        (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_set_ptr_compare_load_cast_load_backward].
  iIntros; iLeft; iLeft; iRight; done.
Qed.

End Sset2PtrCmp.

Module Sset2Load
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sset: CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sset.

Theorem semax_load_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e1,
    semax E Delta
        (∃ sh: share, ∃ t2: type, ∃ v2: val,
              ⌜typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e1) t2 = true /\
                  readable_share sh⌝ ∧
         ▷ ((tc_lvalue Delta e1 ∧
              ⌜tc_val (typeof e1) v2⌝ ∧
              (<absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2)))) ∧
              assert_of (subst id (`v2) P)))
        (Sset id e1) (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_set_ptr_compare_load_cast_load_backward].
  iIntros; iLeft; iRight; done.
Qed.

End Sset2Load.

Module Sset2CastLoad
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def)
       (Sset: CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD with Module CSHL_Def := Def):
       CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module ConseqFacts := GenConseqFacts (Def) (Conseq).

Import Def.
Import Conseq.
Import ConseqFacts.
Import Sset.

Theorem semax_cast_load_backward: forall `{!heapGS Σ} {Espec: OracleKind} `{!externalGS (@OK_ty Σ Espec) Σ} {CS: compspecs} E (Delta: tycontext),
  forall (P: assert) id e,
    semax E Delta
        (∃ sh: share, ∃ e1: expr, ∃ t1: type, ∃ v2: val,
              ⌜e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh⌝ ∧
         ▷ ( (tc_lvalue Delta e1) ∧
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) ∧
              (<absorb> assert_of (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2))) ∧
              assert_of (subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P)))
        (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_set_ptr_compare_load_cast_load_backward].
  iIntros; iRight; done.
Qed.

End Sset2CastLoad.
