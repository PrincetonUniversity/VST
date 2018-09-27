Require Export VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_seplog.
Require Export VST.veric.assert_lemmas.

Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.extend_tc.

Local Open Scope pred.

Lemma corable_funassert:
  forall G rho, corable (funassert G rho).
Proof.
  intros. eapply corable_funspecs_assert.
Qed.

Hint Resolve corable_funassert.

Definition allp_fun_id (Delta : tycontext) (rho : environ): pred rmap :=
(ALL id : ident ,
 (ALL fs : funspec ,
  !! ((glob_specs Delta) ! id = Some fs) -->
  (EX b : block, !! (Map.get (ge_of rho) id = Some b) && func_at fs (b, 0)))).

Lemma corable_allp_fun_id: forall Delta rho,
  corable (allp_fun_id Delta rho).
Proof.
  intros.
  apply corable_allp; intros id.
  apply corable_allp; intros fs.
  apply corable_imp; [apply corable_prop |].
  apply corable_exp; intros b.
  apply corable_andp; [apply corable_prop |].
  apply corable_func_at.
Qed.
  
Lemma allp_fun_id_sub: forall Delta Delta' rho,
  tycontext_sub Delta Delta' ->
  allp_fun_id Delta' rho |-- allp_fun_id Delta rho.
Proof.
  intros.
  unfold allp_fun_id.
  apply allp_derives; intros id.
  apply allp_derives; intros fs.
  apply imp_derives; auto.
  intros ? ?; simpl in *.
  destruct H as [_ [_ [_ [_ [? _]]]]].
  specialize (H id).
  hnf in H.
  rewrite H0 in H.
  destruct ((glob_specs Delta') ! id); [| tauto].
  auto.
Qed.

Lemma funassert_allp_fun_id_sub: forall Delta Delta' rho,
  tycontext_sub Delta Delta' ->
  funassert Delta' rho |-- allp_fun_id Delta rho.
Proof.
  intros.
  apply andp_left1.
  apply allp_fun_id_sub; auto.
Qed.
(*
Lemma corable_jam: forall {B} {S': B -> Prop} (S: forall l, {S' l}+{~ S' l}) (P Q: B -> pred rmap),
    (forall loc, corable (P loc)) ->
    (forall loc, corable (Q loc)) ->
    forall b, corable (jam S P Q b).
Proof.
intros.
intro.
unfold jam.
simpl.
if_tac.
apply H.
apply H0.
Qed.
*)
Lemma prop_derives {A}{H: ageable A}:
 forall (P Q: Prop), (P -> Q) -> prop P |-- prop Q.
Proof.
intros. intros w ?; apply H0; auto.
Qed.

Section STABILITY.
Variable CS: compspecs.
Variables Delta Delta': tycontext.
Hypothesis extends: tycontext_sub Delta Delta'.

Lemma tc_bool_e_sub: forall b b' err rho phi,
  (b = true -> b' = true) ->
  denote_tc_assert (tc_bool b err) rho phi ->
  denote_tc_assert (tc_bool b' err) rho phi.
Proof.
  intros.
  destruct b.
  + specialize (H eq_refl); subst.
    simpl; exact I.
  + inversion H0.
Qed.

Lemma tc_bool_e_i:
  forall b c rho phi,
   b = true ->
  app_pred (denote_tc_assert (tc_bool b c) rho) phi.
Proof.
intros.
subst. apply I.
Qed.

Lemma tc_expr_lvalue_sub: forall rho,
  typecheck_environ Delta rho ->
  forall e,
    tc_expr Delta e rho |-- tc_expr Delta' e rho /\
    tc_lvalue Delta e rho |-- tc_lvalue Delta' e rho.
Proof.
  rename extends into H.
  intros rho HHH.
  induction e; unfold tc_expr, tc_lvalue; split; intro w; unfold prop;
  simpl; auto;
  try solve [destruct t as [  | [| | |] |  | [|] | | | | |]; auto].
* destruct (access_mode t) eqn:?; auto.
  destruct (get_var_type Delta i) eqn:?; [ | contradiction].
  destruct H as [_ [? [_ [? _]]]].
  assert (H8: get_var_type Delta' i = Some t0); [ | rewrite H8; unfold tc_bool; simple_if_tac; auto].
  unfold get_var_type in *. rewrite <- H.
  destruct ((var_types Delta)!i); auto.
  destruct ((glob_types Delta) ! i) eqn:?; inv Heqo.
  specialize (H0 i). hnf in H0. rewrite Heqo0 in H0. rewrite H0.
  auto.
* destruct (get_var_type Delta i) eqn:?; [ | contradiction].
  destruct H as [_ [? [_ [? _]]]].
  assert (H8: get_var_type Delta' i = Some t0); [ | rewrite H8; unfold tc_bool; simple_if_tac; auto].
  unfold get_var_type in *. rewrite <- H.
  destruct ((var_types Delta)!i); auto.
  destruct ((glob_types Delta) ! i) eqn:?; inv Heqo.
  specialize (H0 i). hnf in H0. rewrite Heqo0 in H0. rewrite H0.
  auto.
* destruct ((temp_types Delta)!i) as [? |] eqn:H1; [ | contradiction].
  destruct H as [H _]. specialize (H i); hnf in H. rewrite H1 in H.
  destruct ((temp_types Delta')!i) as [? |] eqn:H2; [ | contradiction].
  simpl @fst; simpl @snd. subst t1; auto.
* destruct (access_mode t) eqn:?H; intro HH; try inversion HH.
  rewrite !denote_tc_assert_andp in HH |- *.
  destruct HH as [[? ?] ?].
  destruct IHe as [? _].
  repeat split.
  + unfold tc_expr in H1.
    apply (H4 w).
    simpl.
    tauto.
  + unfold tc_bool in H2 |- *; simple_if_tac; tauto.
  + pose proof (H4 w H1).
    simpl in H3 |- *.
    unfold_lift in H3; unfold_lift.
    exact H3.
* destruct IHe.
  repeat rewrite denote_tc_assert_andp.
  intros [[? ?] ?].
  repeat split.
  + unfold tc_expr in H0.
    apply (H0 w); unfold prop; auto.
  + unfold tc_bool in *; simple_if_tac; tauto.
  + pose proof (H0 w H2).
    simpl in H4 |- *.
    unfold_lift in H4; unfold_lift.
    exact H4.
* repeat rewrite denote_tc_assert_andp; intros [? ?]; repeat split.
  + destruct IHe. apply (H3 w); auto.
  + unfold tc_bool in *; simple_if_tac; tauto.
* repeat rewrite denote_tc_assert_andp; intros [? ?]; repeat split; auto.
  destruct IHe. apply (H2 w); auto.
* repeat rewrite denote_tc_assert_andp; intros [[? ?] ?]; repeat split; auto.
  + destruct IHe1 as [H8 _]; apply (H8 w); auto.
  + destruct IHe2 as [H8 _]; apply (H8 w); auto.
* repeat rewrite denote_tc_assert_andp; intros [? ?]; repeat split; auto.
  + destruct IHe as [H8 _]; apply (H8 w); auto.
* destruct (access_mode t) eqn:?; try solve [intro HH; inv HH].
  repeat rewrite denote_tc_assert_andp. intros [? ?]; repeat split; auto.
  + destruct IHe. apply (H3 w); auto.
* repeat rewrite denote_tc_assert_andp; intros [? ?]; repeat split; auto.
  + destruct IHe as [_ H8]; apply (H8 w); auto.
Qed.

Lemma tc_expr_sub:
    forall e rho, typecheck_environ Delta rho -> tc_expr Delta e rho |-- tc_expr Delta' e rho.
Proof. intros. apply tc_expr_lvalue_sub; auto. Qed.

Lemma tc_lvalue_sub:
    forall e rho, typecheck_environ Delta rho -> tc_lvalue Delta e rho |-- tc_lvalue Delta' e rho.
Proof. intros. apply tc_expr_lvalue_sub; auto. Qed.

Lemma tc_temp_id_sub:
    forall id t e rho,
   tc_temp_id id t Delta e rho |-- tc_temp_id id t Delta' e rho.
Proof.
rename extends into H.
unfold tc_temp_id; intros.
unfold typecheck_temp_id.
intros w ?.  hnf in H0|-*.
destruct H as [? _]. specialize (H id).
destruct ((temp_types Delta)! id); try contradiction.
destruct ((temp_types Delta')! id); try contradiction.
destruct H; subst.
rewrite !denote_tc_assert_andp in H0 |- *.
split.
+ eapply tc_bool_e_sub; [| exact (proj1 H0)].
  exact (fun x => x).
+ destruct H0 as [? _].
  apply tc_bool_e in H.
  eapply neutral_isCastResultType.
  exact H.
Qed.

Lemma tc_temp_id_load_sub:
   forall id t v rho,
   tc_temp_id_load id t Delta v rho |--    tc_temp_id_load id t Delta' v rho.
Proof.
rename extends into H.
unfold tc_temp_id_load; simpl; intros.
intros w [tto [? ?]]; exists tto.
destruct H as [H _].
specialize (H id); hnf in H.
rewrite H0 in H.
destruct ((temp_types Delta')! id); try contradiction.
destruct H; subst; auto.
Qed.

Lemma tc_exprlist_sub:
  forall e t rho, typecheck_environ Delta rho -> tc_exprlist Delta e t rho |-- tc_exprlist Delta' e t rho.
Proof.
  intros.
  revert t; induction e; destruct t;  simpl; auto.
  specialize (IHe t).
  unfold tc_exprlist.
  intro w; unfold prop.
  simpl.
  repeat rewrite denote_tc_assert_andp.
  intros [[? ?] ?]; repeat split; auto.
  + apply (tc_expr_sub _ _ H w H0); auto.
Qed.

Definition typeof_temp (Delta: tycontext) (id: ident) : option type :=
 match (temp_types Delta) ! id with
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
destruct ((temp_types Delta) ! i); inv H.
destruct ((temp_types Delta') ! i); try contradiction.
destruct H0; subst; auto.
Qed.

End STABILITY.
