Require Export VST.veric.base.
Require Export VST.veric.res_predicates.
Require Import VST.veric.Clight_seplog.
Require Export VST.veric.assert_lemmas.

Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.extend_tc.

Section mpred.

Context `{!heapGS Σ}.

Definition allp_fun_id (Delta : tycontext) (rho : environ): mpred :=
 ∀ id : ident , ∀ fs : funspec ,
  ⌜(glob_specs Delta) !! id = Some fs⌝ →
  (∃ b : block, ⌜Map.get (ge_of rho) id = Some b⌝ ∧ func_ptr_si fs (Vptr b Ptrofs.zero)).

Definition allp_fun_id_sigcc (Delta : tycontext) (rho : environ): mpred :=
(∀ id : ident ,
 (∀ fs : funspec ,
  ⌜(glob_specs Delta) !! id = Some fs⌝ →
  (∃ b : block, ⌜Map.get (ge_of rho) id = Some b⌝ ∧ 
    match fs with
    mk_funspec sig cc _ _ _ => sigcc_at sig cc (b, 0)
    end))).

Lemma allp_fun_id_ex_implies_allp_fun_sigcc Delta rho: 
  allp_fun_id Delta rho ⊢ allp_fun_id_sigcc Delta rho.
Proof.
  rewrite /allp_fun_id /allp_fun_id_sigcc.
  apply bi.forall_mono; intros id.
  apply bi.forall_mono; intros fs.
  apply bi.impl_mono; first done.
  apply bi.exist_mono; intros b.
  apply bi.and_mono; first done.
  rewrite /func_ptr_si.
  iIntros "H"; iDestruct "H" as (? Heq ?) "[#H1 H2]"; inv Heq.
  rewrite /func_at /sigcc_at /funspec_sub_si.
  destruct fs, gs; iDestruct "H1" as "[[-> ->] _]"; eauto.
Qed.

Lemma allp_fun_id_sigcc_sub: forall Delta Delta' rho,
  tycontext_sub Delta Delta' ->
  allp_fun_id_sigcc Delta' rho ⊢ allp_fun_id_sigcc Delta rho.
Proof.
  intros.
  apply bi.forall_mono; intros id.
  iIntros "H" (fs Hid).
  destruct H as (_ & _ & _ & _ & Hg & _).
  specialize (Hg id); rewrite Hid /= in Hg.
  destruct Hg as (gs & Hid' & Hsub).
  iDestruct ("H" with "[%]") as (??) "H"; first done.
  iExists b; iFrame "%".
  iPoseProof Hsub as "Hsub".
  rewrite /funspec_sub_si.
  by destruct fs, gs; iDestruct "Hsub" as "[[-> ->] _]".
Qed.

Lemma allp_fun_id_sub: forall Delta Delta' rho,
  tycontext_sub Delta Delta' ->
  allp_fun_id Delta' rho ⊢ allp_fun_id Delta rho.
Proof.
  intros.
  apply bi.forall_mono; intros id.
  iIntros "H" (fs Hid).
  destruct H as (_ & _ & _ & _ & Hg & _).
  specialize (Hg id); rewrite Hid /= in Hg.
  destruct Hg as (gs & Hid' & Hsub).
  iDestruct ("H" with "[%]") as (??) "H"; first done.
  iExists b; iFrame "%".
  rewrite /func_ptr_si.
  iDestruct "H" as (???) "[#? ?]"; iExists _; iSplit; first auto; iExists _; iSplit; last done.
  iApply funspec_sub_si_trans; eauto.
Qed.

Lemma funassert_allp_fun_id Delta rho: funassert Delta rho ⊢ allp_fun_id Delta rho.
Proof.
  simpl.
  rewrite bi.and_elim_l.
  apply bi.forall_mono; intros id.
  apply bi.forall_mono; intros fs.
  apply bi.impl_mono; first done.
  apply bi.exist_mono; intros b.
  apply bi.and_mono; first done.
  rewrite /func_ptr_si.
  iIntros "H"; iExists b; iSplit; first auto.
  iExists fs; iFrame.
  iPoseProof (funspec_sub_si_refl fs) as "?"; auto.
Qed.

Lemma funassert_allp_fun_id_sub: forall Delta Delta' rho,
  tycontext_sub Delta Delta' ->
  funassert Delta' rho ⊢ allp_fun_id Delta rho.
Proof.
  intros. rewrite funassert_allp_fun_id.
  apply allp_fun_id_sub; trivial.
Qed.

Lemma funassert_allp_fun_id_sigcc Delta rho:
  funassert Delta rho ⊢ allp_fun_id_sigcc Delta rho.
Proof.
  intros. rewrite funassert_allp_fun_id.
  apply allp_fun_id_ex_implies_allp_fun_sigcc.
Qed.

Lemma funassert_allp_fun_id_sigcc_sub: forall Delta Delta' rho,
  tycontext_sub Delta Delta' ->
  funassert Delta' rho ⊢ allp_fun_id_sigcc Delta rho.
Proof.
  intros. rewrite funassert_allp_fun_id_sigcc.
  apply allp_fun_id_sigcc_sub; trivial.
Qed.

Section STABILITY.
Variable CS: compspecs.
Variables Delta Delta': tycontext.
Hypothesis extends: tycontext_sub Delta Delta'.

Lemma tc_bool_e_sub: forall b b' err rho,
  (b = true -> b' = true) ->
  denote_tc_assert (tc_bool b err) rho ⊢
  denote_tc_assert (tc_bool b' err) rho.
Proof.
  intros.
  destruct b.
  + rewrite H; auto.
  + iIntros "[]".
Qed.

Lemma tc_expr_lvalue_sub: forall rho,
  typecheck_environ Delta rho ->
  forall e,
    (tc_expr Delta e rho ⊢ tc_expr Delta' e rho) ∧
    (tc_lvalue Delta e rho ⊢ tc_lvalue Delta' e rho).
Proof.
  intros rho HHH.
  induction e; unfold tc_expr, tc_lvalue; split; auto.
* unfold typecheck_expr.
  destruct (access_mode t); try iIntros "[]".
  destruct (get_var_type Delta i) eqn:?; [ | iIntros "[]"].
  destruct extends as (_ & Hv & _ & Hg & _).
  assert (get_var_type Delta' i = Some t0) as ->; auto.
  unfold get_var_type in *. rewrite <- Hv.
  destruct ((var_types Delta) !! i) eqn: Hi; rewrite ?Hi in Heqo |- *; auto.
  specialize (Hg i).
  destruct ((glob_types Delta) !! i) eqn: Hi'; rewrite ?Hi' in Hg Heqo |- *; inv Heqo.
  by rewrite Hg.
* unfold typecheck_lvalue.
  destruct (get_var_type Delta i) eqn:?; [ | iIntros "[]"].
  destruct extends as (_ & Hv & _ & Hg & _).
  assert (get_var_type Delta' i = Some t0) as ->; auto.
  unfold get_var_type in *. rewrite <- Hv.
  destruct ((var_types Delta) !! i) eqn: Hi; rewrite ?Hi in Heqo |- *; auto.
  specialize (Hg i).
  destruct ((glob_types Delta) !! i) eqn: Hi'; rewrite ?Hi' in Hg Heqo |- *; inv Heqo.
  by rewrite Hg.
* unfold typecheck_expr.
  destruct ((temp_types Delta) !! i) as [? |] eqn:H1; [ | iIntros "[]"].
  destruct extends as [H _]. specialize (H i); hnf in H. rewrite H1 in H.
  destruct ((temp_types Delta') !! i) as [? |] eqn:H2; rewrite H2 in H; subst; done.
* unfold typecheck_expr; fold typecheck_expr.
  destruct (access_mode t) eqn:?H; try iIntros "[]".
  rewrite !denote_tc_assert_andp.
  by destruct IHe as [-> _].
* unfold typecheck_lvalue; fold typecheck_expr.
  rewrite !denote_tc_assert_andp.
  by destruct IHe as [-> _].
* unfold typecheck_expr; fold typecheck_lvalue.
  rewrite !denote_tc_assert_andp.
  by destruct IHe as [_ ->].
* unfold typecheck_expr; fold typecheck_expr.
  rewrite !denote_tc_assert_andp.
  by destruct IHe as [-> _].
* unfold typecheck_expr; fold typecheck_expr.
  rewrite !denote_tc_assert_andp.
  by destruct IHe1 as [-> _], IHe2 as [-> _].
* unfold typecheck_expr; fold typecheck_expr.
  rewrite !denote_tc_assert_andp.
  by destruct IHe as [-> _].
* unfold typecheck_expr; fold typecheck_lvalue.
  destruct (access_mode t) eqn:?H; try iIntros "[]".
  rewrite !denote_tc_assert_andp.
  by destruct IHe as [_ ->].
* unfold typecheck_lvalue; fold typecheck_lvalue.
  rewrite !denote_tc_assert_andp.
  by destruct IHe as [_ ->].
Qed.

Lemma tc_expr_sub:
    forall e rho, typecheck_environ Delta rho -> tc_expr Delta e rho ⊢ tc_expr Delta' e rho.
Proof. intros. apply tc_expr_lvalue_sub; auto. Qed.

Lemma tc_lvalue_sub:
    forall e rho, typecheck_environ Delta rho -> tc_lvalue Delta e rho ⊢ tc_lvalue Delta' e rho.
Proof. intros. apply tc_expr_lvalue_sub; auto. Qed.

Lemma tc_temp_id_sub:
    forall id t e rho,
   tc_temp_id id t Delta e rho ⊢ tc_temp_id id t Delta' e rho.
Proof.
unfold tc_temp_id; intros.
unfold typecheck_temp_id.
destruct extends as (? & _); specialize (H id).
destruct (_ !! _); try iIntros "[]".
destruct (_ !! _); subst; done.
Qed.

Lemma tc_temp_id_load_sub:
   forall id t v rho,
   tc_temp_id_load id t Delta v rho ⊢ tc_temp_id_load id t Delta' v rho.
Proof.
unfold tc_temp_id_load; intros.
apply bi.pure_mono; intros (? & Hid & ?).
destruct extends as (He & _); specialize (He id); rewrite Hid in He.
clear Hid; destruct (_ !! _); [subst; eauto | contradiction].
Qed.

Lemma tc_exprlist_sub:
  forall e t rho, typecheck_environ Delta rho -> tc_exprlist Delta e t rho ⊢ tc_exprlist Delta' e t rho.
Proof.
  intros.
  revert t; induction e; destruct t; simpl; auto.
  unfold tc_exprlist; simpl.
  rewrite !(denote_tc_assert_andp _ (typecheck_exprlist _ _ _)).
  by setoid_rewrite IHe; setoid_rewrite tc_expr_sub.
Qed.

Definition typeof_temp (Delta: tycontext) (id: ident) : option type :=
 match (temp_types Delta) !! id with
 | Some t => Some t
 | None => None
 end.

Lemma typeof_temp_sub:
   forall i t,
    typeof_temp Delta i = Some t ->
    typeof_temp Delta' i = Some t.
Proof.
intros.
destruct extends as [? _].
specialize (H0 i).
unfold typeof_temp in *.
destruct (_ !! _); inv H.
destruct (_ !! _); subst; done.
Qed.

End STABILITY.

End mpred.
