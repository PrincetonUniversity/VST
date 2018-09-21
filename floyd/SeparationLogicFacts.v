From compcert Require Export Clightdefs.
Require Export VST.veric.SeparationLogic.
Require Export VST.msl.Extensionality.
Require Export compcert.lib.Coqlib.
Require Export VST.msl.Coqlib2 VST.veric.coqlib4 VST.floyd.coqlib3.
Require Export VST.floyd.jmeq_lemmas.
Require Export VST.floyd.find_nth_tactic.
Require Export VST.veric.juicy_extspec.
Require Import VST.veric.NullExtension.

Require Import VST.floyd.assert_lemmas.

Local Open Scope logic.

(* TODO: move it *)
Lemma exp_derives:
       forall {A: Type}  {NA: NatDed A} (B: Type) (P Q: B -> A),
               (forall x:B, P x |-- Q x) -> (exp P |-- exp Q).
Proof.
intros.
apply exp_left; intro x; apply exp_right with x; auto.
Qed.

(* Closed and subst. copied from closed_lemmas.v. *)

Lemma closed_wrt_subst:
  forall {A} id e (P: environ -> A), closed_wrt_vars (eq id) P -> subst id e P = P.
Proof.
intros.
unfold subst, closed_wrt_vars in *.
extensionality rho.
symmetry.
apply H.
intros.
destruct (eq_dec id i); auto.
right.
rewrite Map.gso; auto.
Qed.

(* End of copied from closed_lemmas.v. *)

Lemma subst_self: forall {A: Type} (P: environ -> A) t id v Delta rho,
  (temp_types Delta) ! id = Some t ->
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
  rewrite H1, H0.
  simpl.
  apply Map.ext; intros i.
  destruct (Pos.eq_dec id i).
  + subst.
    rewrite Map.gss; symmetry; auto.
  + rewrite Map.gso by auto.
    auto.
Qed.

Definition obox (Delta: tycontext) (i: ident) (P: environ -> mpred): environ -> mpred :=
  ALL v: _,
    match ((temp_types Delta) ! i) with
    | Some t => !! (tc_val' t v) --> subst i (`v) P
    | _ => TT
    end.

Definition odia (Delta: tycontext) (i: ident) (P: environ -> mpred): environ -> mpred :=
  EX v: _,
    match ((temp_types Delta) ! i) with
    | Some t => !! (tc_val' t v) && subst i (`v) P
    | _ => FF
    end.

Lemma obox_closed_wrt: forall Delta id P, closed_wrt_vars (eq id) (obox Delta id P).
Proof.
  intros.
  hnf; intros.
  unfold obox; simpl.
  apply allp_congr; intros.
  unfold subst.
  destruct ((temp_types Delta) ! id); auto.
  f_equal.
  f_equal.
  unfold_lift.
  unfold env_set.
  f_equal.
  simpl.
  apply Map.ext; intros j.
  destruct (ident_eq id j).
  + subst.
    rewrite !Map.gss; auto.
  + rewrite !Map.gso by congruence.
    destruct (H j); [congruence |].
    auto.
Qed.

Lemma odia_closed_wrt: forall Delta id P, closed_wrt_vars (eq id) (odia Delta id P).
Proof.
  intros.
  hnf; intros.
  unfold odia; simpl.
  apply exp_congr; intros.
  destruct ((temp_types Delta) ! id); auto.
  f_equal.
  unfold subst.
  simpl.
  f_equal.
  unfold_lift.
  unfold env_set.
  f_equal.
  simpl.
  apply Map.ext; intros j.
  destruct (ident_eq id j).
  + subst.
    rewrite !Map.gss; auto.
  + rewrite !Map.gso by congruence.
    destruct (H j); [congruence |].
    auto.
Qed.

Lemma subst_obox: forall Delta id v (P: environ -> mpred), subst id (`v) (obox Delta id P) = obox Delta id P.
Proof.
  intros.
  apply closed_wrt_subst.
  apply obox_closed_wrt.
Qed.

Lemma subst_odia: forall Delta id v (P: environ -> mpred), subst id (`v) (odia Delta id P) = odia Delta id P.
Proof.
  intros.
  apply closed_wrt_subst.
  apply odia_closed_wrt.
Qed.

Definition temp_guard (Delta : tycontext) (i: ident): Prop :=
  (temp_types Delta) ! i <> None.

Lemma obox_closed: forall Delta i P, temp_guard Delta i -> closed_wrt_vars (eq i) P -> obox Delta i P = P.
Proof.
  intros.
  unfold obox.
  hnf in H.
  destruct ((temp_types Delta) ! i); [| tauto].
  apply pred_ext.
  + apply (allp_left _ Vundef).
    rewrite closed_wrt_subst by auto.
    apply derives_refl'.
    apply prop_imp, tc_val'_Vundef.
  + apply allp_right; intros.
    rewrite closed_wrt_subst by auto.
    apply imp_right2.
Qed.

Lemma obox_odia: forall Delta i P, temp_guard Delta i -> obox Delta i (odia Delta i P) = odia Delta i P.
Proof.
  intros.
  apply obox_closed; auto.
  apply odia_closed_wrt.
Qed.

Lemma obox_K: forall Delta i P Q, P |-- Q -> obox Delta i P |-- obox Delta i Q.
Proof.
  intros.
  intro rho.
  unfold obox, subst.
  simpl; apply allp_derives; intros.
  destruct ((temp_types Delta) ! i); auto.
  apply imp_derives; auto.
Qed.

Lemma obox_T: forall Delta i (P: environ -> mpred),
  temp_guard Delta i ->
  local (tc_environ Delta) && obox Delta i P |-- P.
Proof.
  intros.
  intro rho; simpl.
  unfold local, lift1.
  normalize.
  destruct H0 as [? _].
  hnf in H, H0.
  specialize (H0 i).
  unfold obox; simpl.
  destruct ((temp_types Delta) ! i); [| tauto].
  specialize (H0 t eq_refl).
  destruct H0 as [v [? ?]].
  apply (allp_left _ v).
  rewrite prop_imp by auto.
  unfold subst.
  apply derives_refl'.
  f_equal.
  unfold_lift.
  destruct rho.
  unfold env_set; simpl in *.
  f_equal.
  apply Map.ext; intro j.
  destruct (ident_eq i j).
  + subst.
    rewrite Map.gss; auto.
  + rewrite Map.gso by auto.
    auto.
Qed.

Lemma odia_D: forall Delta i (P: environ -> mpred),
  temp_guard Delta i ->
  local (tc_environ Delta) && P |-- odia Delta i P.
Proof.
  intros.
  intro rho; simpl.
  unfold local, lift1.
  normalize.
  destruct H0 as [? _].
  hnf in H, H0.
  specialize (H0 i).
  unfold odia; simpl.
  destruct ((temp_types Delta) ! i); [| tauto].
  specialize (H0 t eq_refl).
  destruct H0 as [v [? ?]].
  apply (exp_right v).
  rewrite prop_true_andp by auto.
  unfold subst.
  apply derives_refl'.
  f_equal.
  unfold_lift.
  destruct rho.
  unfold env_set; simpl in *.
  f_equal.
  apply Map.ext; intro j.
  destruct (ident_eq i j).
  + subst.
    rewrite Map.gss; auto.
  + rewrite Map.gso by auto.
    auto.
Qed.

Lemma odia_derives_EX_subst: forall Delta i P,
  odia Delta i P |-- EX v : val, subst i (` v) P.
Proof.
  intros.
  unfold odia.
  apply exp_derives.
  intros v.
  destruct ((temp_types Delta) ! i); [| apply FF_left].
  apply andp_left2; auto.
Qed.

Lemma obox_left2: forall Delta i P Q,
  temp_guard Delta i ->
  local (tc_environ Delta) && P |-- Q ->  
  local (tc_environ Delta) && obox Delta i P |-- obox Delta i Q.
Proof.
  intros.
  unfold local, lift1 in *.
  intro rho; simpl.
  normalize.
  unfold obox; simpl.
  apply allp_derives; intros x.
  destruct ((temp_types Delta) ! i) eqn:?H; auto.
  rewrite <- imp_andp_adjoint.
  normalize.
  unfold TT; rewrite prop_imp by auto.
  unfold subst; unfold_lift.
  specialize (H0 (env_set rho i x)).
  simpl in H0.
  assert (tc_environ Delta (env_set rho i x)).
  {
    clear H0.
    destruct rho, H1 as [? [? ?]]; split; [| split]; simpl in *; auto.
    clear H1 H4.
    hnf in H0 |- *.
    intros j tj H1; specialize (H0 j tj H1).
    destruct H0 as [v [? ?]].
    destruct (ident_eq i j).
    + exists x.
      subst.
      rewrite H2 in H1; inv H1.
      rewrite Map.gss.
      split; auto.
    + exists v.
      rewrite Map.gso by auto.
      split; auto.
  }
  normalize in H0.
Qed.

Lemma obox_left2': forall Delta i P Q,
  temp_guard Delta i ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- Q ->  
  local (tc_environ Delta) && (allp_fun_id Delta && obox Delta i P) |-- obox Delta i Q.
Proof.
  intros.
  unfold local, lift1 in *.
  intro rho; simpl.
  normalize.
  unfold obox; simpl.
  apply allp_right; intros x.
  rewrite andp_comm; apply imp_andp_adjoint.
  apply (allp_left _ x).
  apply imp_andp_adjoint; rewrite andp_comm.
  destruct ((temp_types Delta) ! i) eqn:?H; [| apply prop_right; auto].
  rewrite <- imp_andp_adjoint.
  normalize.
  unfold TT; rewrite prop_imp by auto.
  unfold subst; unfold_lift.
  specialize (H0 (env_set rho i x)).
  simpl in H0.
  assert (tc_environ Delta (env_set rho i x)).
  {
    clear H0.
    destruct rho, H1 as [? [? ?]]; split; [| split]; simpl in *; auto.
    clear H1 H4.
    hnf in H0 |- *.
    intros j tj H1; specialize (H0 j tj H1).
    destruct H0 as [v [? ?]].
    destruct (ident_eq i j).
    + exists x.
      subst.
      rewrite H2 in H1; inv H1.
      rewrite Map.gss.
      split; auto.
    + exists v.
      rewrite Map.gso by auto.
      split; auto.
  }
  normalize in H0.
Qed.

Lemma obox_sepcon: forall Delta i P Q,
  obox Delta i P * obox Delta i Q |-- obox Delta i (P * Q).
Proof.
  intros.
  unfold obox.
  apply allp_right.
  intros v.
  apply wand_sepcon_adjoint.
  apply (allp_left _ v).
  apply wand_sepcon_adjoint.
  rewrite sepcon_comm.
  apply wand_sepcon_adjoint.
  apply (allp_left _ v).
  apply wand_sepcon_adjoint.
  rewrite sepcon_comm.
  destruct ((temp_types Delta) ! i); [| apply TT_right].
  apply imp_andp_adjoint.
  normalize.
  unfold TT.
  rewrite !prop_imp by auto.
  rewrite subst_sepcon.
  auto.
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

Lemma substopt_oboxopt: forall Delta id v (P: environ -> mpred), substopt id (`v) (oboxopt Delta id P) = oboxopt Delta id P.
Proof.
  intros.
  destruct id; [| auto].
  apply subst_obox.
Qed.

Lemma oboxopt_closed: forall Delta i P,
  temp_guard_opt Delta i ->
  closed_wrt_vars (fun id => isSome (match i with Some i' => insert_idset i' idset0 | None => idset0 end) ! id) P ->
  oboxopt Delta i P = P.
Proof.
  intros.
  destruct i.
  + simpl in H0 |- *.
    apply obox_closed; auto.
    replace (eq i) with ((fun id : ident => isSome (insert_idset i idset0) ! id)); auto.
    extensionality id.
    unfold insert_idset.
    destruct (ident_eq id i).
    - subst.
      rewrite PTree.gss.
      simpl.
      apply prop_ext.
      tauto.
    - rewrite PTree.gso by auto.
      unfold idset0.
      rewrite PTree.gempty.
      simpl.
      assert (i <> id) by congruence.
      apply prop_ext.
      tauto.
  + auto.
Qed.

Lemma oboxopt_T: forall Delta i (P: environ -> mpred),
  temp_guard_opt Delta i ->
  local (tc_environ Delta) && oboxopt Delta i P |-- P.
Proof.
  intros.
  destruct i; [| apply andp_left2, derives_refl].
  apply obox_T; auto.
Qed.

Lemma odiaopt_D: forall Delta i (P: environ -> mpred),
  temp_guard_opt Delta i ->
  local (tc_environ Delta) && P |-- odiaopt Delta i P.
Proof.
  intros.
  destruct i; [| apply andp_left2, derives_refl].
  apply odia_D; auto.
Qed.

Lemma oboxopt_odiaopt: forall Delta i P, temp_guard_opt Delta i -> oboxopt Delta i (odiaopt Delta i P) = odiaopt Delta i P.
Proof.
  intros.
  destruct i; auto.
  apply obox_odia; auto.
Qed.

Lemma oboxopt_K: forall Delta i P Q, P |-- Q -> oboxopt Delta i P |-- oboxopt Delta i Q.
Proof.
  intros.
  intro rho.
  destruct i; auto.
  apply obox_K; auto.
Qed.

Lemma odiaopt_derives_EX_substopt: forall Delta i P,
  odiaopt Delta i P |-- EX v : val, substopt i (` v) P.
Proof.
  intros.
  destruct i; [apply odia_derives_EX_subst |].
  simpl.
  intros; apply (exp_right Vundef); auto.
Qed.

Lemma oboxopt_left2: forall Delta i P Q,
  temp_guard_opt Delta i ->
  local (tc_environ Delta) && P |-- Q ->  
  local (tc_environ Delta) && oboxopt Delta i P |-- oboxopt Delta i Q.
Proof.
  intros.
  destruct i; [apply obox_left2; auto |].
  auto.
Qed.

Lemma oboxopt_left2': forall Delta i P Q,
  temp_guard_opt Delta i ->
  local (tc_environ Delta) && (allp_fun_id Delta && P) |-- Q ->  
  local (tc_environ Delta) && (allp_fun_id Delta && oboxopt Delta i P) |-- oboxopt Delta i Q.
Proof.
  intros.
  destruct i; [apply obox_left2'; auto |].
  auto.
Qed.

Lemma oboxopt_sepcon: forall Delta i P Q,
  oboxopt Delta i P * oboxopt Delta i Q |-- oboxopt Delta i (P * Q).
Proof.
  intros.
  destruct i.
  + apply obox_sepcon.
  + apply derives_refl.
Qed.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_conseq:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P' (R': ret_assert) P c (R: ret_assert) ,
    local (tc_environ Delta) && ((allp_fun_id Delta) && P) |-- |==> |> FF || P' ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_normal R') |-- |==> |> FF || RA_normal R ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_break R') |-- |==> |> FF || RA_break R ->
    local (tc_environ Delta) && ((allp_fun_id Delta) && RA_continue R') |-- |==> |> FF || RA_continue R ->
    (forall vl, local (tc_environ Delta) && ((allp_fun_id Delta) && RA_return R' vl) |-- |==> |> FF || RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.

End CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE.

Module GenCConseqFacts
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CConseq: CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE with Module CSHL_Def := Def).

Import Def.
Import CConseq.

Lemma semax_pre_post_indexed_bupd:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall P' (R': ret_assert) P c (R: ret_assert) ,
    local (tc_environ Delta) && P |-- |==> |> FF || P' ->
    local (tc_environ Delta) && RA_normal R' |-- |==> |> FF || RA_normal R ->
    local (tc_environ Delta) && RA_break R' |-- |==> |> FF || RA_break R ->
    local (tc_environ Delta) && RA_continue R' |-- |==> |> FF || RA_continue R ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- |==> |> FF || RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.
Proof.
  intros.
  eapply semax_conseq; [.. | exact H4]; try intros;
  match goal with
  | |- ?A && (_ && ?B) |-- _ => apply derives_trans with (A && B); [solve_andp | auto]
  end.
Qed.

Lemma semax_pre_post_bupd:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall P' (R': ret_assert) P c (R: ret_assert) ,
    local (tc_environ Delta) && P |-- |==> P' ->
    local (tc_environ Delta) && RA_normal R' |-- |==> RA_normal R ->
    local (tc_environ Delta) && RA_break R' |-- |==> RA_break R ->
    local (tc_environ Delta) && RA_continue R' |-- |==> RA_continue R ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- |==> RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.
Proof.
  intros.
  eapply semax_pre_post_indexed_bupd; [.. | exact H4]; try intros;
  try apply derives_bupd_derives_bupd0; auto.
Qed.

Lemma semax_pre_indexed_bupd:
 forall P' Espec {cs: compspecs} Delta P c R,
     local (tc_environ Delta) && P |-- |==> |> FF || P' ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof.
  intros; eapply semax_pre_post_indexed_bupd; eauto;
  intros; reduce2derives; apply derives_refl.
Qed.

Lemma semax_post_indexed_bupd:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   local (tc_environ Delta) && RA_normal R' |-- |==> |> FF || RA_normal R ->
   local (tc_environ Delta) && RA_break R' |-- |==> |> FF || RA_break R ->
   local (tc_environ Delta) && RA_continue R' |-- |==> |> FF || RA_continue R ->
   (forall vl, local (tc_environ Delta) && RA_return R' vl |-- |==> |> FF || RA_return R vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
  intros; eapply semax_pre_post_indexed_bupd; try eassumption.
  apply derives_bupd0_refl.
Qed.

Lemma semax_post''_indexed_bupd: forall R' Espec {cs: compspecs} Delta R P c,
           local (tc_environ Delta) && R' |-- |==> |> FF || RA_normal R ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Proof. intros. eapply semax_post_indexed_bupd; eauto.
 simpl RA_normal; auto.
 simpl RA_break; normalize.
 simpl RA_continue; normalize.
 intro vl; simpl RA_return; normalize.
Qed.

Lemma semax_pre_bupd:
 forall P' Espec {cs: compspecs} Delta P c R,
     local (tc_environ Delta) && P |-- |==> P' ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post_bupd; eauto;
intros; apply andp_left2, bupd_intro; auto.
Qed.

Lemma semax_post_bupd:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   local (tc_environ Delta) && RA_normal R' |-- |==> RA_normal R ->
   local (tc_environ Delta) && RA_break R' |-- |==> RA_break R ->
   local (tc_environ Delta) && RA_continue R' |-- |==> RA_continue R ->
   (forall vl, local (tc_environ Delta) && RA_return R' vl |-- |==> RA_return R vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
  intros; eapply semax_pre_post_bupd; try eassumption.
  apply derives_bupd_refl.
Qed.

Lemma semax_post'_bupd: forall R' Espec {cs: compspecs} Delta R P c,
           local (tc_environ Delta) && R' |-- |==> R ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Proof. intros. eapply semax_post_bupd; eauto.
 simpl RA_normal; auto.
 simpl RA_break; normalize.
 simpl RA_continue; normalize.
 intro vl; simpl RA_return; normalize.
Qed.

Lemma semax_post''_bupd: forall R' Espec {cs: compspecs} Delta R P c,
           local (tc_environ Delta) && R' |-- |==> RA_normal R ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Proof. intros. eapply semax_post_bupd; eauto.
 simpl RA_normal; auto.
 simpl RA_break; normalize.
 simpl RA_continue; normalize.
 intro vl; simpl RA_return; normalize.
Qed.

Lemma semax_pre_post'_bupd: forall P' R' Espec {cs: compspecs} Delta R P c,
      local (tc_environ Delta) && P |-- |==> P' ->
      local (tc_environ Delta) && R' |-- |==> R ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Proof. intros.
 eapply semax_pre_bupd; eauto.
 eapply semax_post'_bupd; eauto.
Qed.

Lemma semax_pre_post''_bupd: forall P' R' Espec {cs: compspecs} Delta R P c,
      local (tc_environ Delta) && P |-- |==> P' ->
      local (tc_environ Delta) && R' |-- |==> RA_normal R ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Proof. intros.
 eapply semax_pre_bupd; eauto.
 eapply semax_post''_bupd; eauto.
Qed.

End GenCConseqFacts.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_pre_post : forall {Espec: OracleKind}{CS: compspecs},
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- P') ->
    local (tc_environ Delta) && RA_normal R' |-- RA_normal R ->
    local (tc_environ Delta) && RA_break R' |-- RA_break R ->
    local (tc_environ Delta) && RA_continue R' |-- RA_continue R ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.

End CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE.

Module GenConseq
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (CConseq: CLIGHT_SEPARATION_HOARE_LOGIC_COMPLETE_CONSEQUENCE with Module CSHL_Def := Def): CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def.

Module CSHL_Def := Def.
Module CConseqFacts := GenCConseqFacts (Def) (CConseq).
Import CSHL_Def.
Import CConseq.
Import CConseqFacts.

Lemma semax_pre_post : forall {Espec: OracleKind}{CS: compspecs},
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
    (local (tc_environ Delta) && P |-- P') ->
    local (tc_environ Delta) && RA_normal R' |-- RA_normal R ->
    local (tc_environ Delta) && RA_break R' |-- RA_break R ->
    local (tc_environ Delta) && RA_continue R' |-- RA_continue R ->
    (forall vl, local (tc_environ Delta) && RA_return R' vl |-- RA_return R vl) ->
   @semax CS Espec Delta P' c R' -> @semax CS Espec Delta P c R.
Proof.
  intros; eapply semax_pre_post_bupd; eauto; intros; eapply derives_trans, bupd_intro; auto.
Qed.

End GenConseq.

Module GenConseqFacts
       (Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF)
       (Conseq: CLIGHT_SEPARATION_HOARE_LOGIC_CONSEQUENCE with Module CSHL_Def := Def).

Import Def.
Import Conseq.

(* Copied from canon.v *)

Lemma semax_pre: forall {Espec: OracleKind}{cs: compspecs},
 forall P' Delta P c R,
     local (tc_environ Delta) && P |-- P' ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof.
  intros; eapply semax_pre_post; eauto;
  intros; apply ENTAIL_refl.
Qed.

Lemma semax_pre_simple: forall {Espec: OracleKind}{cs: compspecs},
 forall P' Delta P c R,
     P |-- P' ->
     @semax cs Espec Delta P' c R  -> @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre; [| eauto].
apply andp_left2; auto.
Qed.

Lemma semax_post:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   local (tc_environ Delta) && RA_normal R' |-- RA_normal R ->
   local (tc_environ Delta) && RA_break R' |-- RA_break R ->
   local (tc_environ Delta) && RA_continue R' |-- RA_continue R ->
   (forall vl, local (tc_environ Delta) && RA_return R' vl |-- RA_return R vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
intros; eapply semax_pre_post; try eassumption.
apply ENTAIL_refl.
Qed.

Lemma semax_post_simple:
 forall (R': ret_assert) Espec {cs: compspecs} Delta (R: ret_assert) P c,
   RA_normal R' |-- RA_normal R ->
   RA_break R' |-- RA_break R ->
   RA_continue R' |-- RA_continue R ->
   (forall vl, RA_return R' vl |-- RA_return R vl) ->
   @semax cs Espec Delta P c R' ->  @semax cs Espec Delta P c R.
Proof.
  intros; eapply semax_post; [.. | eauto]; intros; reduce2derives; auto.
Qed.

Lemma semax_post': forall R' Espec {cs: compspecs} Delta R P c,
           local (tc_environ Delta) && R' |-- R ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Proof. intros. eapply semax_post; eauto.
 simpl RA_normal; auto.
 simpl RA_break; normalize.
 simpl RA_continue; normalize.
 intro vl; simpl RA_return; normalize.
Qed.

Lemma semax_pre_post': forall P' R' Espec {cs: compspecs} Delta R P c,
      local (tc_environ Delta) && P |-- P' ->
      local (tc_environ Delta) && R' |-- R ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c (normal_ret_assert R).
Proof. intros.
 eapply semax_pre; eauto.
 eapply semax_post'; eauto.
Qed.

(* Copied from canon.v end. *)

Lemma semax_post'': forall R' Espec {cs: compspecs} Delta R P c,
           local (tc_environ Delta) && R' |-- RA_normal R ->
      @semax cs Espec Delta P c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Proof. intros. eapply semax_post; eauto.
 simpl RA_normal; auto.
 simpl RA_break; normalize.
 simpl RA_continue; normalize.
 intro vl; simpl RA_return; normalize.
Qed.

Lemma semax_pre_post'': forall P' R' Espec {cs: compspecs} Delta R P c,
      local (tc_environ Delta) && P |-- P' ->
      local (tc_environ Delta) && R' |-- RA_normal R ->
      @semax cs Espec Delta P' c (normal_ret_assert R') ->
      @semax cs Espec Delta P c R.
Proof. intros.
 eapply semax_pre; eauto.
 eapply semax_post''; eauto.
Qed.

End GenConseqFacts.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_EXTRACTION.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_extract_exists:
  forall {CS: compspecs} {Espec: OracleKind},
  forall (A : Type)  (P : A -> environ->mpred) c (Delta: tycontext) (R: ret_assert),
  (forall x, @semax CS Espec Delta (P x) c R) ->
   @semax CS Espec Delta (EX x:A, P x) c R.

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

Lemma semax_extract_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta (!!PP && P) c Q.
Proof.
  intros.
  eapply semax_pre with (EX H: PP, P).
  + apply andp_left2.
    apply derives_extract_prop; intros.
    apply (exp_right H0), derives_refl.
  + apply semax_extract_exists, H.
Qed.

Lemma semax_orp:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta P1 P2 c Q,
           @semax CS Espec Delta P1 c Q ->
           @semax CS Espec Delta P2 c Q ->
           @semax CS Espec Delta (P1 || P2) c Q.
Proof.
  intros.
  eapply semax_pre with (EX b: bool, if b then P1 else P2).
  + apply andp_left2.
    apply orp_left.
    - apply (exp_right true), derives_refl.
    - apply (exp_right false), derives_refl.
  + apply semax_extract_exists.
    intros.
    destruct x; auto.
Qed.

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
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) P c Q,
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta ((|> !!PP) && P) c Q.
Proof.
  intros.
  apply semax_extract_prop in H.
  eapply semax_pre_post_indexed_bupd; [.. | exact H].
  + apply andp_left2.
    eapply derives_trans; [| apply bupd_intro].
    rewrite orp_comm, distrib_andp_orp.
    apply andp_right.
    - apply andp_left1.
      apply later_prop.
    - apply orp_right1.
      solve_andp.
  + apply derives_bupd0_refl.
  + apply derives_bupd0_refl.
  + apply derives_bupd0_refl.
  + intros; apply derives_bupd0_refl.
Qed.

End GenIExtrFacts.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_forward:
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall e1 e2 sh P,
   writable_share sh ->
   @semax CS Espec Delta
          (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P)))
          (Sassign e1 e2)
          (normal_ret_assert
             (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P)).

End CLIGHT_SEPARATION_HOARE_LOGIC_STORE_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_STORE_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_store_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
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
  
Theorem semax_store_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext) e1 e2 P,
   @semax CS Espec Delta
          (EX sh: share, !! writable_share sh && |> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             ((`(mapsto_ sh (typeof e1)) (eval_lvalue e1)) * (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) -* P))))
          (Sassign e1 e2)
          (normal_ret_assert P).
Proof.
  intros.
  eapply semax_post'; [.. | eapply (semax_extract_exists _ _ _ _ (normal_ret_assert P))].
  + apply andp_left2.
    change (RA_normal (existential_ret_assert (fun _ : share => normal_ret_assert P))) with (EX _: share, P).
    apply derives_refl.
  + intros sh.
    apply semax_extract_prop; intro SH.
    eapply semax_post'; [.. | eapply semax_store_forward; auto].
    apply andp_left2.
    apply modus_ponens_wand.
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
  forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
 forall e1 e2 sh P,
   writable_share sh ->
   @semax CS Espec Delta
          (|> ( (tc_lvalue Delta e1) &&  (tc_expr Delta (Ecast e2 (typeof e1)))  &&
             (`(mapsto_ sh (typeof e1)) (eval_lvalue e1) * P)))
          (Sassign e1 e2)
          (normal_ret_assert
             (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`force_val (`(sem_cast (typeof e2) (typeof e1)) (eval_expr e2))) * P)).
Proof.
  intros.
  eapply semax_pre; [| apply semax_store_backward].
  apply (exp_right sh).
  normalize.
  apply andp_left2.
  apply later_derives.
  apply andp_derives; auto.
  apply sepcon_derives; auto.
  apply wand_sepcon_adjoint.
  rewrite sepcon_comm.
  apply derives_refl.
Qed.

End StoreB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_call_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall A P Q NEP NEQ ts x (F: environ -> mpred) ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          ((|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         (`(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>(F * `(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert
            (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).

End CLIGHT_SEPARATION_HOARE_LOGIC_CALL_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_call_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall ret a bl R,
  @semax CS Espec Delta
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (type_of_params argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          (|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((`(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* R)))
         (Scall ret a bl)
         (normal_ret_assert R).

End CLIGHT_SEPARATION_HOARE_LOGIC_CALL_BACKWARD.

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
  
Theorem semax_call_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall ret a bl R,
  @semax CS Espec Delta
         (EX argsig: _, EX retsig: _, EX cc: _,
          EX A: _, EX P: _, EX Q: _, EX NEP: _, EX NEQ: _, EX ts: _, EX x: _,
         !! (Cop.classify_fun (typeof a) =
             Cop.fun_case_f (type_of_params argsig) retsig cc /\
             (retsig = Tvoid -> ret = None) /\
             tc_fn_return Delta ret retsig) &&
          (|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         `(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>((`(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl))) * oboxopt Delta ret (maybe_retval (Q ts x) retsig ret -* R)))
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
  apply semax_extract_exists; intro NEP.
  apply semax_extract_exists; intro NEQ.
  apply semax_extract_exists; intro ts.
  apply semax_extract_exists; intro x.
  rewrite !andp_assoc.
  apply semax_extract_prop; intros [? [? ?]].
  eapply semax_pre_post'; [.. | apply semax_call_forward; auto].
  + apply andp_left2.
    apply andp_derives; [apply derives_refl |].
    apply andp_derives; [apply derives_refl |].
    apply later_derives.
    rewrite sepcon_comm.
    apply derives_refl.
  + unfold RA_normal, normal_ret_assert.
    rewrite <- exp_sepcon1.
    rewrite <- corable_andp_sepcon1 by (intro; apply corable_prop).
    rewrite wand_sepcon_adjoint.
    rewrite exp_andp2; apply exp_left; intros old.
    rewrite substopt_oboxopt.
    apply oboxopt_T.
    destruct ret; hnf in H1 |- *; [destruct ((temp_types Delta) ! i) |]; auto; congruence.
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

Theorem semax_call_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
    forall A P Q NEP NEQ ts x (F: environ -> mpred) ret argsig retsig cc a bl,
           Cop.classify_fun (typeof a) =
           Cop.fun_case_f (type_of_params argsig) retsig cc ->
           (retsig = Tvoid -> ret = None) ->
          tc_fn_return Delta ret retsig ->
  @semax CS Espec Delta
          ((|>((tc_expr Delta a) && (tc_exprlist Delta (snd (split argsig)) bl)))  &&
         (`(func_ptr (mk_funspec  (argsig,retsig) cc A P Q NEP NEQ)) (eval_expr a) &&
          |>(F * `(P ts x: environ -> mpred) (make_args' (argsig,retsig) (eval_exprlist (snd (split argsig)) bl)))))
         (Scall ret a bl)
         (normal_ret_assert
            (EX old:val, substopt ret (`old) F * maybe_retval (Q ts x) retsig ret)).
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
    1: destruct ret; hnf in H1 |- *; [destruct ((temp_types Delta) ! i) |]; auto; congruence.
  rewrite <- oboxopt_odiaopt.
    2: destruct ret; hnf in H1 |- *; [destruct ((temp_types Delta) ! i) |]; auto; congruence.
  apply oboxopt_K.
  rewrite <- wand_sepcon_adjoint.
  rewrite <- exp_sepcon1.
  apply sepcon_derives; auto.
  apply odiaopt_derives_EX_substopt.
Qed.

End CallB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_SET_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_set_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
          P))
          (Sset id e)
        (normal_ret_assert
          (EX old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P)).

End CLIGHT_SEPARATION_HOARE_LOGIC_SET_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_set_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_SET_BACKWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_load_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall  sh id P e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (` v2) * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val (typeof e1) v2)) &&
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (` v2)) &&
                                          (subst id (`old) P))).

End CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e1,
    @semax CS Espec Delta
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e1) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val (typeof e1) v2)) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`v2) P))
        (Sset id e1) (normal_ret_assert P).

End CLIGHT_SEPARATION_HOARE_LOGIC_LOAD_BACKWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_cast_load_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall sh id P e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) (`(eval_cast (typeof e1) t1 v2)))) &&
                                          (subst id (`old) P))).

End CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_CAST_LOAD_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P))
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

Theorem semax_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e1,
    @semax CS Espec Delta
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e1) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val (typeof e1) v2)) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`v2) P))
        (Sset id e1) (normal_ret_assert P).
Proof.
  intros.
  apply semax_extract_exists; intro sh.
  apply semax_extract_exists; intro t2.
  apply semax_extract_exists; intro v2.
  apply semax_extract_prop; intros [? [? ?]].
  rewrite (andp_assoc _ _ (subst _ _ _)).
  eapply semax_post'; [.. | eapply semax_load_forward; eauto].
  + rewrite exp_andp2.
    apply exp_left; intros old.
    autorewrite with subst.
    apply derives_trans with (local (tc_environ Delta) && (local ((` eq) (eval_id id) (` v2))) && subst id (` v2) P); [solve_andp |].
    intro rho; unfold local, lift1; unfold_lift; simpl.
    unfold typeof_temp in H.
    destruct ((temp_types Delta) ! id) eqn:?H; inv H.
    normalize.
    erewrite subst_self by eauto; auto.
  + solve_andp.
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

Theorem semax_load_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall  sh id P e1 t2 (v2: val),
    typeof_temp Delta id = Some t2 ->
    is_neutral_cast (typeof e1) t2 = true ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (` v2) * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val (typeof e1) v2)) &&
          P))
       (Sset id e1)
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (` v2)) &&
                                          (subst id (`old) P))).
Proof.
  intros.
  eapply semax_pre; [| apply semax_load_backward].
  apply (exp_right sh).
  apply (exp_right t2).
  apply (exp_right v2).
  apply andp_right; [apply prop_right; auto |].
  apply later_ENTAIL.
  rewrite (andp_assoc _ _ (subst _ _ _)).
  apply andp_ENTAIL; [apply ENTAIL_refl |].
  apply andp_right; auto.
  rewrite subst_exp.
  intros rho.
  change (local (tc_environ Delta) rho && P rho
  |-- EX b : val,
       subst id (` v2) (local ((` eq) (eval_id id) (` v2)) && subst id (` b) P) rho).
  apply (exp_right (eval_id id rho)).
  autorewrite with subst.
  unfold local, lift1; unfold_lift; simpl.
  unfold typeof_temp in H.
  destruct ((temp_types Delta) ! id) eqn:?H; inv H.
  normalize.
  apply andp_right; [| erewrite subst_self by eauto; auto].
  apply prop_right.
  unfold subst.
  apply eval_id_same.
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

Theorem semax_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P))
        (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  apply semax_extract_exists; intro sh.
  apply semax_extract_exists; intro e1.
  apply semax_extract_exists; intro t2.
  apply semax_extract_exists; intro v2.
  apply semax_extract_prop; intros [He [? [? ?]]].
  subst e.
  rewrite (andp_assoc _ _ (subst _ _ _)).
  eapply semax_post'; [.. | eapply semax_cast_load_forward; eauto].
  + rewrite exp_andp2.
    apply exp_left; intros old.
    autorewrite with subst.
    apply derives_trans with (local (tc_environ Delta) && (local ((` eq) (eval_id id) (subst id (` old) ((` (eval_cast (typeof e1) t2)) (` v2))))) && subst id (`(force_val (sem_cast (typeof e1) t2 v2))) P); [solve_andp |].
    intro rho; unfold local, lift1; unfold_lift; simpl.
    unfold typeof_temp in H.
    destruct ((temp_types Delta) ! id) eqn:?H; inv H.
    normalize.
    erewrite subst_self by eauto; auto.
  + solve_andp.
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

Theorem semax_cast_load_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall sh id P e1 t1 (v2: val),
    typeof_temp Delta id = Some t1 ->
   cast_pointer_to_bool (typeof e1) t1 = false ->
    readable_share sh ->
    local (tc_environ Delta) && P |-- `(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT ->
    @semax CS Espec Delta
       (|> ( (tc_lvalue Delta e1) &&
       local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
          P))
       (Sset id (Ecast e1 t1))
       (normal_ret_assert (EX old:val, local (`eq (eval_id id) (subst id (`old) (`(eval_cast (typeof e1) t1 v2)))) &&
                                          (subst id (`old) P))).
Proof.
  intros.
  eapply semax_pre; [| apply semax_cast_load_backward].
  apply (exp_right sh).
  apply (exp_right e1).
  apply (exp_right t1).
  apply (exp_right v2).
  apply andp_right; [apply prop_right; auto |].
  apply later_ENTAIL.
  rewrite (andp_assoc _ _ (subst _ _ _)).
  apply andp_ENTAIL; [apply ENTAIL_refl |].
  apply andp_right; auto.
  rewrite subst_exp.
  intros rho.
  change (local (tc_environ Delta) rho && P rho
  |-- EX b : val,
       subst id (` (force_val (sem_cast (typeof e1) t1 v2))) (local ((` eq) (eval_id id) (subst id (` b) (` (eval_cast (typeof e1) t1 v2)))) && subst id (` b) P) rho).
  apply (exp_right (eval_id id rho)).
  autorewrite with subst.
  unfold local, lift1; unfold_lift; simpl.
  unfold typeof_temp in H.
  destruct ((temp_types Delta) ! id) eqn:?H; inv H.
  normalize.
  apply andp_right; [| erewrite subst_self by eauto; auto].
  apply prop_right.
  unfold subst.
  apply eval_id_same.
Qed.

End CastLoadB2F.

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

Theorem semax_set_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  apply semax_pre with (|> (!! (exists t, ((temp_types Delta) ! id = Some t)) && (tc_expr Delta e && tc_temp_id id (typeof e) Delta e && subst id (eval_expr e) P))).
  {
    apply later_ENTAIL.
    apply andp_right; [| solve_andp].
    unfold tc_temp_id, typecheck_temp_id.
    destruct ((temp_types Delta) ! id).
    + apply prop_right; eauto.
    + simpl denote_tc_assert.
      normalize.
  }
  apply semax_pre with (|> (tc_expr Delta e && tc_temp_id id (typeof e) Delta e && (!! (exists t, ((temp_types Delta) ! id = Some t)) && subst id (eval_expr e) P))).
  {
    apply later_ENTAIL.
    solve_andp.
  }
  eapply semax_post'; [.. | eapply semax_set_forward; eauto].
  rewrite exp_andp2.
  apply exp_left; intros old.
  autorewrite with subst.
  normalize.
  destruct H as [t ?].
  apply derives_trans with (local (tc_environ Delta) && (local ((` eq) (eval_id id) (subst id (` old) (eval_expr e)))) && subst id (` old) (subst id (eval_expr e) P)); [solve_andp |].
  set (v := `old).
  intro rho; unfold local, lift1; unfold_lift; simpl; subst v.
  normalize.
  rewrite resubst_full.
  erewrite subst_self; eauto.
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

Theorem semax_set_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
          P))
          (Sset id e)
        (normal_ret_assert
          (EX old:val, local (`eq (eval_id id) (subst id (`old) (eval_expr e))) &&
                            subst id (`old) P)).
Proof.
  intros.
  eapply semax_pre; [| apply semax_set_backward].
  apply later_ENTAIL.
  apply andp_right; [solve_andp |].
  rewrite subst_exp.
  intro rho.
  simpl.
  apply (exp_right (eval_id id rho)).
  unfold_lift; unfold local, lift1.
  simpl.
  unfold subst.
  normalize.
  rewrite !env_set_env_set.
  assert (tc_temp_id id (typeof e) Delta e rho |-- !! (env_set rho id (eval_id id rho) = rho)).
  + unfold tc_temp_id, typecheck_temp_id.
    destruct ((temp_types Delta) ! id) eqn:?H; [| apply FF_left].
    apply prop_right.
    eapply env_set_eval_id; eauto.
  + rewrite (add_andp _ _ H0).
    rewrite !andp_assoc.
    apply andp_left2.
    apply andp_left2.
    normalize.
    rewrite H1.
    normalize.
Qed.

End SetB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_FORWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_ptr_compare_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P id cmp e1 e2 ty sh1 sh2,
    sepalg.nonidentity sh1 -> sepalg.nonidentity sh2 ->
   is_comparison cmp = true  ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   typecheck_tid_ptr_compare Delta id = true ->
   @semax CS Espec Delta
        ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&

          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (EX old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) &&
                       subst id `(old) P)).

End CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_FORWARD.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_PTR_CMP_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_ptr_compare_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P id e,
   @semax CS Espec Delta
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P)))
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

Theorem semax_ptr_compare_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P id e,
   @semax CS Espec Delta
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P)))
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
  rewrite exp_andp2.
  apply exp_left; intros old.
  autorewrite with subst.
  rewrite resubst_full.
  intro rho; unfold local, lift1; unfold_lift; simpl.
  unfold typecheck_tid_ptr_compare in H4.
  destruct ((temp_types Delta) ! id) eqn:?H; inv H4.
  normalize.
  erewrite subst_self by eauto.
  auto.
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

Theorem semax_ptr_compare_forward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P id cmp e1 e2 ty sh1 sh2,
    sepalg.nonidentity sh1 -> sepalg.nonidentity sh2 ->
   is_comparison cmp = true  ->
   eqb_type (typeof e1) int_or_ptr_type = false ->
   eqb_type (typeof e2) int_or_ptr_type = false ->
   typecheck_tid_ptr_compare Delta id = true ->
   @semax CS Espec Delta
        ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&

          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          P))
          (Sset id (Ebinop cmp e1 e2 ty))
        (normal_ret_assert
          (EX old:val,
                 local (`eq (eval_id id)  (subst id `(old)
                     (eval_expr (Ebinop cmp e1 e2 ty)))) &&
                       subst id `(old) P)).
Proof.
  intros.
  eapply semax_pre; [| apply semax_ptr_compare_backward].
  apply (exp_right cmp).
  apply (exp_right e1).
  apply (exp_right e2).
  apply (exp_right ty).
  apply (exp_right sh1).
  apply (exp_right sh2).
  apply andp_right; [apply prop_right; repeat split; auto |].
  apply later_ENTAIL.
  apply andp_ENTAIL; [apply ENTAIL_refl |].
  rewrite subst_exp.
  intros rho.
  change (local (tc_environ Delta) rho && P rho
  |-- EX b : val,
       subst id (eval_expr (Ebinop cmp e1 e2 ty)) (local ((` eq) (eval_id id) (subst id (` b) (eval_expr (Ebinop cmp e1 e2 ty)))) && subst id (` b) P) rho).
  apply (exp_right (eval_id id rho)).
  autorewrite with subst.
  unfold local, lift1; unfold_lift; simpl.
  unfold typecheck_tid_ptr_compare in H4.
  simpl in H4.
  destruct ((temp_types Delta) ! id) eqn:?H; inv H4.
  normalize.
  apply andp_right.
  + apply prop_right.
    unfold subst.
    unfold_lift.
    rewrite env_set_env_set.
    rewrite eval_id_same.
    erewrite env_set_eval_id by eauto.
    auto.
  + unfold_lift.
    rewrite resubst_full.
    erewrite subst_self; eauto.
Qed.

End PtrCmpB2F.

Module Type CLIGHT_SEPARATION_HOARE_LOGIC_SSET_BACKWARD.

Declare Module CSHL_Def: CLIGHT_SEPARATION_HOARE_LOGIC_DEF.

Import CSHL_Def.

Axiom semax_set_ptr_compare_load_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
       ((|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P)) ||
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))) ||
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e) &&
              local (`(tc_val (typeof e) v2)) &&
              (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2) * TT) &&
              subst id (`v2) P)) ||
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P)))
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

Theorem semax_set_ptr_compare_load_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
       ((|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P)) ||
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P))) ||
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e) &&
              local (`(tc_val (typeof e) v2)) &&
              (`(mapsto sh (typeof e)) (eval_lvalue e) (`v2) * TT) &&
              subst id (`v2) P)) ||
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P)))
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

Theorem semax_set_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (|> ( (tc_expr Delta e) &&
             (tc_temp_id id (typeof e) Delta e) &&
             subst id (eval_expr e) P))
          (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_set_ptr_compare_load_cast_load_backward].
  apply orp_right1, orp_right1, orp_right1; auto.
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

Theorem semax_ptr_compare_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall P id e,
   @semax CS Espec Delta
        (EX cmp: Cop.binary_operation, EX e1: expr, EX e2: expr,
         EX ty: type, EX sh1: share, EX sh2: share,
          !! (e = Ebinop cmp e1 e2 ty /\
              sepalg.nonidentity sh1 /\ sepalg.nonidentity sh2 /\
              is_comparison cmp = true /\
              eqb_type (typeof e1) int_or_ptr_type = false /\
              eqb_type (typeof e2) int_or_ptr_type = false /\
              typecheck_tid_ptr_compare Delta id = true) &&
            ( |> ( (tc_expr Delta e1) &&
              (tc_expr Delta e2)  &&
          local (`(blocks_match cmp) (eval_expr e1) (eval_expr e2)) &&
          (`(mapsto_ sh1 (typeof e1)) (eval_expr e1) * TT) &&
          (`(mapsto_ sh2 (typeof e2)) (eval_expr e2) * TT) &&
          subst id (eval_expr (Ebinop cmp e1 e2 ty)) P)))
          (Sset id e)
        (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_set_ptr_compare_load_cast_load_backward].
  apply orp_right1, orp_right1, orp_right2; auto.
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

Theorem semax_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e1,
    @semax CS Espec Delta
        (EX sh: share, EX t2: type, EX v2: val,
              !! (typeof_temp Delta id = Some t2 /\
                  is_neutral_cast (typeof e1) t2 = true /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val (typeof e1) v2)) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`v2) P))
        (Sset id e1) (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_set_ptr_compare_load_cast_load_backward].
  apply orp_right1, orp_right2; auto.
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

Theorem semax_cast_load_backward: forall {CS: compspecs} {Espec: OracleKind} (Delta: tycontext),
  forall (P: environ->mpred) id e,
    @semax CS Espec Delta
        (EX sh: share, EX e1: expr, EX t1: type, EX v2: val,
              !! (e = Ecast e1 t1 /\
                  typeof_temp Delta id = Some t1 /\
                  cast_pointer_to_bool (typeof e1) t1 = false /\
                  readable_share sh) &&
         |> ( (tc_lvalue Delta e1) &&
              local (`(tc_val t1) (`(eval_cast (typeof e1) t1 v2))) &&
              (`(mapsto sh (typeof e1)) (eval_lvalue e1) (`v2) * TT) &&
              subst id (`(force_val (sem_cast (typeof e1) t1 v2))) P))
        (Sset id e) (normal_ret_assert P).
Proof.
  intros.
  eapply semax_pre_simple; [| apply semax_set_ptr_compare_load_cast_load_backward].
  apply orp_right2; auto.
Qed.

End Sset2CastLoad.

