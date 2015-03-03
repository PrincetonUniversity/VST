Require Export veric.base.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.slice.
Require Import veric.res_predicates.
Require Import veric.tycontext.
Require Import veric.expr.
Require Import veric.expr_lemmas.
Require Import veric.seplog.
Require Import veric.Clight_lemmas.
Require Import msl.normalize.
Require Import msl.corable.

Local Open Scope pred.

Lemma mapsto_core_load: forall ch v rsh sh loc m, 
  (address_mapsto ch v rsh sh loc * TT)%pred m -> core_load ch loc v m.
Proof.
unfold address_mapsto, core_load.
intros until m; intros H.
destruct H as [phi0 [phi1 [Hjoin [[bl [[Hlen [Hdec Halign]] H]] ?]]]].
unfold allp, jam in *.
exists bl.
repeat split; auto.
hnf. intro b; spec H b.
hnf in H|-*.
if_tac.
hnf in H|-*.
destruct H as [p ?].
apply (resource_at_join _ _ _ b) in Hjoin.
rewrite H in Hjoin; clear H.
repeat rewrite preds_fmap_NoneP in Hjoin.
inv Hjoin.
do 3 econstructor; try reflexivity.
exists rsh3.
destruct sh3 as [sh3 p3].
exists sh3; exists p3. reflexivity.
auto.
Qed.

Lemma nth_error_in_bounds: forall {A} (l: list A) i, (O <= i < length l)%nat
  -> exists x, nth_error l i = value x.
Proof.
intros until i; intros H.
revert i l H.
induction i; destruct l; intros; simpl in *; 
  try solve [eauto|omegaContradiction].
apply IHi; omega.
Qed.

Lemma nth_eq_nth_error_eq: forall {A} (d: A) (l l': list A) i,
  (O <= i < length l)%nat 
  -> length l = length l' 
  -> nth i l d = nth i l' d
  -> nth_error l i = nth_error l' i.
Proof.
intros until i; intros H H0 H1.
revert i l l' H H0 H1.
induction i; destruct l; destruct l'; intros; simpl in *;
  try solve [auto|omegaContradiction].
rewrite (IHi l l'); try solve [auto|omega].
Qed.

Lemma core_load_fun: forall ch m loc v1 v2,
   core_load ch loc v1 m -> core_load ch loc v2 m -> v1=v2.
Proof.
intros until v2; intros H H0.
unfold core_load in *.
unfold allp, jam in *.
destruct H as [bl [[H1 [H2 Halign]] H]].
destruct H0 as [bl' [[H3 [H4 Halign']] H0]].
cut (forall i, nth_error bl i = nth_error bl' i); [intro H5|].
cut (bl = bl'); [intro H6|].
rewrite H6 in H2.
rewrite H4 in H2.
auto.
clear - H5.
revert bl' H5.
induction bl; destruct bl'; intros; try solve [spec H5 O; inv H5|auto].
f_equal.
spec H5 O; inv H5; auto.
apply IHbl.
intro i. 
spec H5 (S i).
auto.
intro i.
destruct loc as (b, ofs).
spec H (b, ofs + Z_of_nat i).
spec H0 (b, ofs + Z_of_nat i).
hnf in H, H0. if_tac in H.
(* adr_range *)
destruct H as [rsh [sh [p H]]].
destruct H0 as [rsh' [sh' [p' H0]]].
rewrite H0 in H.
clear H0.
simpl in *.
inversion H.
replace (ofs + Z_of_nat i - ofs) with (Z_of_nat i) in * by omega.
rewrite nat_of_Z_eq in *.
rewrite <- H3 in H1.
apply nth_eq_nth_error_eq with (d := Undef); auto.
destruct H5 as [? [H5 H5']].
rewrite size_chunk_conv in H5'.
omega.
(* ~adr_range *)
cut (i >= length bl)%nat. intro Hlen.
cut (i >= length bl')%nat. intro Hlen'.
generalize (nth_error_length i bl) as H6; intro.
generalize (nth_error_length i bl') as H7; intro.
rewrite <- H6 in Hlen.
rewrite <- H7 in Hlen'.
rewrite Hlen; rewrite Hlen'; auto.
rewrite <- H3 in H1; clear H3.
rewrite <- H1; auto.
unfold adr_range in H5.
rewrite size_chunk_conv in H5.
rewrite <- H1 in H5.
cut ( ~(O <= i < length bl))%nat. 
omega.
intro HContra.
apply H5.
split; auto.
cut (0 <= Z_of_nat i < Z_of_nat (length bl)). intro H6.
2: omega.
omega.
Qed.

Lemma extensible_core_load': forall ch loc v
  w w', extendR w w' -> core_load ch loc v w -> core_load ch loc v w'. 
Proof.
intros.
unfold core_load in *.
destruct H0 as [bl ?].
exists bl.
destruct H0 as [[? [? Halign]] ?].
destruct H as [wx ?].
repeat split; auto.
unfold allp, jam in *.
intro loc'.
spec H2 loc'.
apply resource_at_join with (loc := loc') in H.
hnf in H2|-*.
if_tac; auto.
hnf in H2|-*.
destruct H2 as [rsh [sh [p H2]]].
rewrite H2 in H.
inv H; subst; eauto.
exists rsh3.
destruct sh3 as [sh3 p3].
exists sh3; exists p3; auto.
Qed.


Definition Dbool (Delta: tycontext) (e: Clight.expr) : assert := 
  fun rho =>  EX b: bool, !! (bool_of_valf (eval_expr Delta e rho) = Some b).

Lemma assert_truth:  forall {A} `{ageable A} (P:  Prop), P -> forall (Q: pred A), Q |-- (!! P) && Q.
Proof.
intros.
intros st ?.
split; auto.
Qed. 

(*   Lemma assert_Val_is_true:
   forall {A} `{ageable A} (P: pred A), P |-- !!(is_true Vtrue) && P.
  Proof.  intros. apply assert_truth. apply Val_is_true_Vtrue. Qed.

Hint Resolve Val_is_true_Vtrue  @assert_Val_is_true.
*)

(****************** stuff moved from semax_prog  *****************)

Lemma rmap_unage_age:
  forall r, age (rmap_unage r) r.
Proof.
intros; unfold age, rmap_unage; simpl.
case_eq (unsquash r); intros.
change ag_rmap with R.ag_rmap.
rewrite rmap_age1_eq.
rewrite unsquash_squash.
f_equal.
apply unsquash_inj.
rewrite H.
rewrite unsquash_squash.
f_equal.
generalize (equal_f (rmap_fmap_comp (approx (S n)) (approx n)) r0); intro.
unfold compose at 1 in H0.
rewrite H0.
rewrite approx_oo_approx'; auto.
clear - H.
generalize (unsquash_squash n r0); intros.
rewrite <- H in H0.
rewrite squash_unsquash in H0.
congruence.
Qed.

Lemma adr_range_split_lem1: forall n m r loc loc',
  r = n + m -> n >= 0 -> m >= 0 -> adr_range loc n loc' -> adr_range loc r loc'.
Proof.
unfold adr_range; intros.
destruct loc; destruct loc'; simpl in *.
destruct H2; split; auto.
omega.
Qed.

Lemma adr_range_split_lem2: forall n m r loc loc',
  r = n + m -> n >= 0 -> m >= 0 -> adr_range (fst loc, snd loc + n) m loc' 
  -> adr_range loc r loc'.
Proof.
unfold adr_range; intros.
destruct loc; destruct loc'; simpl in *.
destruct H2; split; auto.
omega.
Qed.

Lemma adr_range_split_lem3: forall n m r loc loc',
  r = n + m -> n >= 0 -> m >= 0 
  -> ~adr_range loc n loc'
  -> ~adr_range (fst loc, snd loc + n) m loc'
  -> ~adr_range loc r loc'.
Proof.
unfold adr_range; intros.
destruct loc; destruct loc'; simpl in *.
intros [c1 c2].
destruct (Z_lt_dec z0 (z+n)).
apply H2.
split; auto||omega.
apply H3.
split; auto||omega.
Qed.

Lemma prop_imp_i {A}{agA: ageable A}:
  forall (P: Prop) Q w, (P -> app_pred Q w) -> (!!P --> Q) w.
Proof.
 intros. intros w' ? ?. apply H in H1. eapply pred_nec_hereditary; eauto.
Qed.

Lemma or_pred_ext {A} `{agA : ageable A}: forall P Q P' Q',
       (P <--> P') && (Q <--> Q') |--  (P || Q) <--> (P' || Q').
Proof.
intros.
intros w [? ?].
split; intros w' ? [?|?].
left. destruct H; eauto.
right. destruct H0; eauto.
left. destruct H; eauto.
right. destruct H0; eauto.
Qed.

Lemma corable_pureat: forall pp k loc, corable (pureat pp k loc).
Proof.
 intros. intro w.
 unfold pureat.
  simpl. rewrite <- core_resource_at.
  destruct (w @ loc).
  rewrite core_NO; apply prop_ext; split; intro Hx; inv Hx.
  rewrite core_YES; apply prop_ext; split; intro Hx; inv Hx.
  rewrite core_PURE; rewrite level_core; auto.
Qed.

Lemma corable_funassert:
  forall G rho, corable (funassert G rho).
Proof.
 intros.
 unfold funassert, func_at.
 apply corable_andp.
 apply corable_allp; intro.
 apply corable_allp; intro.
 apply corable_imp; auto.
 apply corable_exp; intro.
 apply corable_andp; auto.
 destruct b0.
 apply corable_pureat.
 apply corable_allp; intro.
 apply corable_allp; intro.
 apply corable_imp; auto.
 destruct b0.
 simpl.
 apply corable_exp; intro.
 apply corable_pureat.
Qed.

Hint Resolve corable_funassert.

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

Lemma corable_fun_assert: forall v fsig A P Q, corable (fun_assert v fsig A P Q).
Proof.
intros.
unfold fun_assert, res_predicates.fun_assert.
apply corable_exp; intro.
apply corable_andp; auto.
unfold FUNspec.
apply corable_allp; intro.
apply corable_jam; intro loc.
apply corable_pureat.
intro w. unfold TTat. apply prop_ext; split; intros; hnf in H|-*; auto.
Qed.

Hint Resolve corable_fun_assert : normalize.

Lemma prop_derives {A}{H: ageable A}: 
 forall (P Q: Prop), (P -> Q) -> prop P |-- prop Q.
Proof.
intros. intros w ?; apply H0; auto.
Qed.

Section STABILITY.
Variables Delta Delta': tycontext.
Hypothesis extends: tycontext_sub Delta Delta'.

Lemma sem_binary_operation'_sub: forall b e1 e2 v1 v2 v t rho,
  denote_tc_assert Delta (isBinOpResultType Delta b e1 e2 t) rho ->
  sem_binary_operation' Delta b (typeof e1) (typeof e2) true2 v1 v2 = Some v ->
  sem_binary_operation' Delta' b (typeof e1) (typeof e2) true2 v1 v2 = Some v.
Proof.
  intros.
  destruct b; try solve [simpl in H0 |- *; auto].
  + simpl in H0 |- *.
    unfold sem_add in H0 |- *.
    unfold isBinOpResultType in H.

    destruct (Cop.classify_add (typeof e1) (typeof e2)); auto; simpl.
    match goal with |- ?S _ _ _ _ = _ => unfold S end.
    erewrite <- sizeof_sub. by eauto.
    


Lemma eval_expr_lvalue_sub: forall e,
  (forall rho w, tc_expr Delta e rho w -> eval_expr Delta e rho = eval_expr Delta' e rho) /\
  (forall rho w, tc_lvalue Delta e rho w -> eval_lvalue Delta e rho = eval_lvalue Delta' e rho).
Proof.
  unfold tc_expr, tc_lvalue.
  induction e; intros; split; intros; try reflexivity; simpl; unfold_lift.
  + simpl in H.
    destruct (access_mode t); try inv H.
    rewrite !denote_tc_assert_andp in H.
    erewrite (proj1 IHe) by tauto.
    reflexivity.
  + simpl in H.
    rewrite !denote_tc_assert_andp in H.
    erewrite (proj1 IHe) by tauto.
    reflexivity.
  + simpl in H.
    rewrite !denote_tc_assert_andp in H.
    eapply (proj2 IHe); tauto.
  + simpl in H.
    rewrite !denote_tc_assert_andp in H.
    erewrite (proj1 IHe) by tauto.
    reflexivity.
  + simpl in H.
    rewrite !denote_tc_assert_andp in H.
    Print isBinOpResultType.
Check sem_binary_operation'.
Lemma tc_expr_lvalue_sub:
  forall Delta Delta', 
    tycontext_sub Delta Delta' ->
  forall rho e,
   (tc_expr Delta e rho |-- tc_expr Delta' e rho && !! (eval_expr Delta e rho = eval_expr Delta' e rho) /\
    tc_lvalue Delta e rho |-- tc_lvalue Delta' e rho && !! (eval_lvalue Delta e rho = eval_lvalue Delta' e rho)).
Proof.
  induction e; unfold tc_expr, tc_lvalue; split; intro w; unfold prop;
  simpl; auto;
  try solve [destruct t as [  | [| | |] |  | [|] | | | | |]; auto].
* destruct (access_mode t) eqn:?; auto.
  destruct (get_var_type Delta i) eqn:?; [ | contradiction].
  destruct H as [_ [? [_ [? _]]]].
  assert (H8: get_var_type Delta' i = Some t0); [ | rewrite H8; unfold tc_bool; if_tac; auto].
  unfold get_var_type in *. rewrite <- H.
  destruct ((var_types Delta)!i); auto.
  destruct ((glob_types Delta) ! i) eqn:?; inv Heqo.
  specialize (H0 i). hnf in H0. rewrite Heqo0 in H0. rewrite H0.
  auto.
* destruct (get_var_type Delta i) eqn:?; [ | contradiction].
  destruct H as [_ [? [_ [? _]]]].
  assert (H8: get_var_type Delta' i = Some t0); [ | rewrite H8; unfold tc_bool; if_tac; auto].
  unfold get_var_type in *. rewrite <- H.
  destruct ((var_types Delta)!i); auto.
  destruct ((glob_types Delta) ! i) eqn:?; inv Heqo.
  specialize (H0 i). hnf in H0. rewrite Heqo0 in H0. rewrite H0.
  auto.
* destruct ((temp_types Delta)!i) as [[? ?]|] eqn:H1; [ | contradiction].
  destruct H as [H _]. specialize (H i); hnf in H. rewrite H1 in H.
  destruct ((temp_types Delta')!i) as [[? ?]|] eqn:H2; [ | contradiction].
  simpl @fst; simpl @snd. destruct H; subst t1; auto.
  destruct b; simpl in H0; subst; try solve [if_tac; auto].
  if_tac; intros; try contradiction.
  destruct b0; auto. exact (conj I eq_refl).
* destruct (access_mode t) eqn:?H; intro HH; try inversion HH.
  rewrite !denote_tc_assert_andp in HH |- *.
  destruct HH as [[? ?] ?].
  destruct IHe as [? _].
  repeat split.
  + unfold tc_expr in H1.
    apply (H4 w).
    simpl.
    tauto.
  + unfold tc_bool in H2 |- *; if_tac; tauto.
  + destruct (H4 w H1) as [? ?].
    simpl in H6.
    simpl in H3 |- *.
    unfold_lift in H3; unfold_lift.
    rewrite <- H6.
    exact H3.
  + destruct (H4 w H1) as [? ?].
    simpl in H6.
    simpl; unfold_lift.
    rewrite H6.
    reflexivity.
* destruct IHe.
  repeat rewrite denote_tc_assert_andp.
  intros [[? ?] ?].
  repeat split.
  + unfold tc_expr in H0.
    apply (H0 w); unfold prop; auto.
  + unfold tc_bool in *; if_tac; tauto.
  + destruct (H0 w H2) as [? ?].
    simpl in H6.
    simpl in H4 |- *.
    unfold_lift in H4; unfold_lift.
    rewrite <- H6.
    exact H4.
  + destruct (H0 w H2) as [? ?].
    simpl in H6.
    unfold_lift.
    rewrite H6.
    reflexivity.
* repeat rewrite denote_tc_assert_andp; intros [? ?]; repeat split.
  + destruct IHe. apply (H3 w); auto.
  + unfold tc_bool in *; if_tac; tauto.
  + destruct IHe as [_ ?].
    destruct (H2 w H0).
    exact H4.
* repeat rewrite denote_tc_assert_andp; intros [? ?]; repeat split.
  + unfold tc_bool in *; if_tac; tauto.
  + destruct IHe. apply (H2 w); auto.
  + destruct IHe as [? _].
    destruct (H2 w H1).
    simpl in H4.
    unfold_lift.
    rewrite H4.
    reflexivity.
* repeat rewrite denote_tc_assert_andp; intros [[? ?] ?]; repeat split.
  + admit. (* preserve isBinOpResultType *)
  + destruct IHe1 as [H8 _]; apply (H8 w); auto.
  + destruct IHe2 as [H8 _]; apply (H8 w); auto.
  + unfold_lift.
    destruct (proj1 IHe1 w H1).
    destruct (proj1 IHe2 w H2).
    simpl in H4, H6.
    rewrite H4, H6.
    admit. (* preserve sem_binary_operation' *)
* repeat rewrite denote_tc_assert_andp; intros [? ?]; repeat split; auto.
  + destruct IHe as [H8 _]; apply (H8 w); auto.
  + admit. (* preserve isCastResultType *)
  + admit. (* preserve sem_cast *)
* destruct (access_mode t) eqn:?; try solve [intro HH; inv HH].
  repeat rewrite denote_tc_assert_andp. intros [? ?]; repeat split; auto.
  + destruct IHe. apply (H3 w); auto.
  + destruct (typeof e); auto;
    destruct ((composite_types Delta) ! i0) as [co |] eqn:?; try inv H1;
    (pose proof composite_types_get_sub _ _ H _ _ Heqo as Heqo'; rewrite Heqo'); [| exact I].
    destruct (field_offset (composite_types Delta) i (co_members co)) eqn: ?H; inv H1.
    erewrite field_offset_sub by eauto.
    exact I.
  + unfold_lift.
    admit. (* preserve eval_field *)
* repeat rewrite denote_tc_assert_andp; intros [? ?]; repeat split; auto.
  + destruct IHe as [_ H8]; apply (H8 w); auto.
  + destruct (typeof e); auto;
    destruct ((composite_types Delta) ! i0) as [co |] eqn:?; try inv H1;
    (pose proof composite_types_get_sub _ _ H _ _ Heqo as Heqo'; rewrite Heqo'); [| exact I].
    destruct (field_offset (composite_types Delta) i (co_members co)) eqn: ?H; inv H1.
    erewrite field_offset_sub by eauto.
    exact I.
  + unfold_lift.
    admit. (* preserve eval_field *)
* unfold tc_bool; simpl.
  intro.
  split.
  + destruct (complete_or_function_type (composite_types Delta) t &&
            eqb_type t0 (Tint I32 Unsigned noattr))%bool eqn:?; inv H0.
    rewrite andb_true_iff in Heqb.
    destruct Heqb.
    rewrite H1; clear H1.
    erewrite complete_or_function_type_sub; eauto.
    exact I.
  + unfold_lift.
    simpl.
Print sizeof_stable.
    erewrite sizeof_sub. by eauto.
  admit. (* preserve complete_type *)
* unfold tc_bool; simpl.
  admit. (* preserve complete_type *)
Qed.

Lemma tc_expr_sub:
   forall Delta Delta',
    tycontext_sub Delta Delta' ->
    forall e rho, tc_expr Delta e rho |-- tc_expr Delta' e rho.
Proof. intros. apply tc_expr_lvalue_sub; auto. Qed.

Lemma tc_lvalue_sub:
   forall Delta Delta',
    tycontext_sub Delta Delta' ->
    forall e rho, tc_lvalue Delta e rho |-- tc_lvalue Delta' e rho.
Proof. intros. apply tc_expr_lvalue_sub; auto. Qed.

Lemma tc_temp_id_sub:
   forall Delta Delta',
    tycontext_sub Delta Delta' ->
    forall id t e rho, 
   tc_temp_id id t Delta e rho |-- tc_temp_id id t Delta' e rho.
Proof.
unfold tc_temp_id; intros.
unfold typecheck_temp_id.
intros w ?.  hnf in H0|-*.
destruct H as [? _]. specialize (H id).
destruct ((temp_types Delta)! id) as [[? ?]|]; try contradiction.
destruct ((temp_types Delta')! id) as [[? ?]|]; try contradiction.
destruct H; subst; auto.
Qed.

  
Lemma tc_temp_id_load_sub:
   forall Delta Delta',
    tycontext_sub Delta Delta' ->
    forall id t v rho, 
   tc_temp_id_load id t Delta v rho |--    tc_temp_id_load id t Delta' v rho.  
Proof.
unfold tc_temp_id_load; simpl; intros.
intros w [tto [x [? ?]]]; exists tto.
destruct H as [H _].
specialize (H id); hnf in H.
rewrite H0 in H; auto.
destruct ((temp_types Delta')! id) as [[? ?]|]; try contradiction.
destruct H; subst.
exists b; auto.
Qed.

Lemma tc_exprlist_sub:
   forall Delta Delta',
    tycontext_sub Delta Delta' ->
    forall e t rho, tc_exprlist Delta e t rho |-- tc_exprlist Delta' e t rho.
Proof.
intros.
revert t; induction e; destruct t;  simpl; auto.
specialize (IHe t).
unfold tc_exprlist.
intro w; unfold prop.
simpl.
repeat rewrite denote_tc_assert_andp.
intros [[? ?] ?]; repeat split; auto.
apply (tc_expr_sub _ _ H e0 rho w); auto.
apply (IHe w); auto.
Qed.

