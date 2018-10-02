Require Import VST.veric.juicy_base.
Require Import VST.msl.normalize.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
Require Import VST.veric.extend_tc.
Require Import VST.veric.Clight_seplog.
Require Import VST.veric.Clight_assert_lemmas.
Require Import VST.veric.Clight_new.
Require Import VST.sepcomp.extspec.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas.
Require Import VST.veric.semax.
Require Import VST.veric.semax_lemmas.
Require Import VST.veric.Clight_lemmas.

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
assert (isSome (modifiedvars' (seq_of_labeled_statement sl) s) ! i). {
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
 rewrite modifiedvars'_union in H|-*.
 destruct H;[left|right]; auto.
Qed.
(*
Lemma typecheck_environ_join_switch2:
   forall sl Delta rho,
    typecheck_environ Delta rho ->
    typecheck_environ (join_tycon_labeled sl Delta) rho.
Proof.
 intros.
 induction sl; simpl; auto.
 apply typecheck_environ_join2 with Delta; auto.
apply tycontext_evolve_update_tycon.
 clear.
 induction sl; simpl; auto.
apply tycontext_evolve_refl.
apply tycontext_evolve_join; auto.
apply tycontext_evolve_update_tycon.
Qed.

Lemma typecheck_environ_join_switch1:
  forall n sl rho Delta,
    typecheck_environ
      (update_tycon Delta (seq_of_labeled_statement (select_switch n sl))) rho ->
    typecheck_environ (join_tycon_labeled sl Delta) rho.
Proof.
 intros.
 unfold select_switch in H.
 destruct (select_switch_case n sl) eqn:?.
 apply typecheck_environ_update in H.
 apply typecheck_environ_join_switch2; auto.
 apply typecheck_environ_update in H.
 apply typecheck_environ_join_switch2; auto.
Qed.
*) 

Lemma frame_tc_expr:
  forall {CS: compspecs} (Q F: mpred) Delta e rho,
  Q |-- tc_expr Delta e rho ->
  Q * F |-- tc_expr Delta e rho.
Proof.
intros.
eapply derives_trans; [apply sepcon_derives; [apply H | apply derives_refl ] | ].
apply extend_sepcon; apply extend_tc_expr.
Qed.

Lemma subp_trans':
  forall A (NA: ageable A) (P Q R: pred A) w,  
    app_pred (P >=> Q) w ->
    app_pred (Q >=> R) w -> 
    app_pred (P >=> R) w.
Proof.
 repeat intro.
 eapply H0; eauto.
 eapply H; eauto.
Qed.

Lemma prop_subp:
   forall A (NA: ageable A) (P Q: Prop) (w: nat),
    (P -> Q) -> app_pred (!! P >=> !! Q)  w.
Proof.
repeat intro. apply H. apply H2.
Qed.

Lemma andp_subp'_right:
  forall A (NA: ageable A) (P Q R: pred A) w,  
    app_pred (P >=> Q) w ->
    app_pred (P >=> R) w -> 
    app_pred (P >=> Q && R) w.
Proof.
repeat intro.
split. eapply H; eauto. eapply H0; eauto.
Qed.

Lemma prop_true_imp:
  forall {A} {agA: ageable A} (P: Prop) (Q: pred A),
   P ->   (!! P --> Q)%pred = Q.
Proof.
intros.
apply pred_ext.
intros ? ?. apply H0; auto.
intros ? ? ? ? ?.
eapply pred_nec_hereditary; eauto.
Qed.

Lemma prop_imp_right: forall A (agA: ageable A) (P: Prop) (Q R: pred A),
   (P -> (Q |-- R)) ->
   Q |-- !! P --> R.
Proof.
intros.
intros w ? ? ? ?.
apply H; auto. eapply pred_nec_hereditary; eauto.
Qed.

(*Moved to semax_lemmas
Lemma semax_eq:
 forall {Espec: OracleKind} {CS: compspecs} Delta P c R,
  semax Espec Delta P c R = 
  (TT |-- (ALL psi : genv,
         ALL Delta' : tycontext,
         !! (tycontext_sub Delta Delta' /\ genv_cenv psi = cenv_cs) -->
         believe Espec Delta' psi Delta' -->
         ALL k : cont ,
         ALL F : assert ,
         !! closed_wrt_modvars c F &&
         rguard Espec psi (exit_tycon c Delta') (frame_ret_assert R F) k -->
         guard Espec psi Delta' (fun rho : environ => F rho * P rho) (Kseq c :: k))).
Proof.
intros.
extensionality w.
rewrite semax_fold_unfold.
apply prop_ext; intuition.
Qed.*)

Lemma imp_right:
 forall A (agA: ageable A) (P Q R : pred A),
  P && Q |-- R ->
  P |-- Q --> R.
Proof.
intros.
intros ? ? ? ? ?.
apply H.
split; auto.
eapply pred_nec_hereditary; eauto.
Qed.

Lemma prop_andp_subp':
  forall (A : Type) (agA : ageable A) (P : Prop) (S: pred nat) (Q R : pred A),
  (P -> S |-- Q >=> R)%pred
  ->  (S  |--  !! P && Q >=> R)%pred.
Proof.
intros.
intros ? ? ? ? ? ? [? ?].
eapply H; eauto.
Qed.

Lemma tc_expr_sound {CS: compspecs}:
 forall Delta e rho, typecheck_environ Delta rho -> 
     tc_expr Delta e rho |-- !! tc_val (typeof e) (eval_expr e rho).
Proof.
repeat intro.
eapply typecheck_expr_sound; eauto.
Qed.

Lemma unfash_allp:  forall {A} {agA: ageable A} {B} (f: B -> pred nat),
  @unfash _ agA (allp f) = allp (fun x:B => unfash (f x)).
Proof.
intros.
apply pred_ext.
intros ? ? ?.
specialize (H b). auto.
repeat intro. apply (H b).
Qed.

Lemma fash_TT: forall {A} {agA: ageable A}, @unfash A agA TT = TT.
Proof.
intros.
apply pred_ext; intros ? ?; apply I.
Qed.

Lemma allp_andp: 
  forall {A} {NA: ageable A} {B: Type} (b0: B) (P: B -> pred A) (Q: pred A),
   (allp P && Q = allp (fun x => P x && Q))%pred.
Proof.
intros.
apply pred_ext.
intros ? [? ?] b. split; auto.
intros ? ?.
split.
intro b. apply (H b).
apply (H b0).
Qed.

Lemma unfash_prop_imp:
  forall {A} {agA: ageable A} (P: Prop) (Q: pred nat),
  (@unfash _ agA (prop P --> Q) = prop P --> @unfash _ agA Q)%pred.
Proof.
intros.
apply pred_ext; repeat intro.
apply H; auto. apply necR_level'; auto.
hnf in H.
specialize (H a (necR_refl _) H1).
eapply pred_nec_hereditary; try apply H0.
apply H.
Qed.

Import age_to.

Lemma unfash_imp:
  forall {A} {NA: ageable A} (P Q: pred nat),
  (@unfash A _ (P --> Q) = (@unfash A _ P) --> @unfash A _ Q)%pred.
Proof.
intros.
apply pred_ext; repeat intro.
apply H; auto. apply necR_level'; auto.
specialize (H (age_to a' a)).
spec H.
apply age_to_necR.
spec H.
do 3 red. 
rewrite level_age_to; auto.
apply necR_level in H0. apply H0.
do 3 red in H.
rewrite level_age_to in H; auto.
apply necR_level in H0.
apply H0.
Qed.

Lemma unfash_andp:  forall {A} {agA: ageable A} (P Q: pred nat),
  (@unfash A agA (andp P Q) = andp (@unfash A agA P) (@unfash A agA Q)).
Proof.
intros.
apply pred_ext.
intros ? ?.
destruct H.
split; auto.
intros ? [? ?].
split; auto.
Qed.

Lemma andp_imp_e:
  forall (A : Type) (agA : ageable A) (P Q : pred A),
   P && (P --> Q) |-- Q.
Proof.
intros.
intros ? [? ?].
eapply H0; auto.
Qed.

Lemma andp_imp_e':
  forall (A : Type) (agA : ageable A) (P Q : pred A),
   P && (P --> Q) |-- P && Q.
Proof.
intros.
apply andp_right.
apply andp_left1; auto.
intros ? [? ?].
eapply H0; auto.
Qed.

Lemma switch_rguard:
 forall (Espec : OracleKind)
  (R : ret_assert)
  (psi : genv)
  (F : assert)
  (Delta' : tycontext)
  (k : cont),
 rguard Espec psi Delta'
        (frame_ret_assert R F) k |--
(rguard Espec psi  Delta'
   (frame_ret_assert (switch_ret_assert R) F) 
   (Kswitch :: k)).
Proof.
intros.
unfold rguard.
apply allp_right; intro ek.
apply allp_right; intro vl.
apply allp_right; intro tx'.
apply allp_right; intro vx'.
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
 apply allp_left with ek'.
 apply allp_left with vl'.
 apply allp_left with tx'.
 apply allp_left with vx'.
 simpl current_function.
 set (rho' := construct_rho (filter_genv psi) vx' tx') in *.
 forget (funassert Delta' rho') as FDR.
 rewrite !proj_frame_ret_assert.
 simpl.
 apply fash_derives.
 destruct R as [?R ?R ?R ?R]; destruct ek; subst ek' vl'; simpl; auto.
 apply imp_right. normalize.
Qed.

Lemma unfash_fash_imp:
  forall A (NA: ageable A) P Q,
  @unfash A _ (# (P --> Q)) |-- P --> Q.
Proof.
intros.
intros ? ?.
intros ? ? ?.
do 3 red in H.
apply (H a'); auto.
apply necR_level; auto.
Qed.

Lemma assert_safe_step_nostore:
  forall {cs: compspecs} Espec psi vx vx2 tx tx2 k1 k2 Delta e rho,
  (forall jm jm', age1 jm = Some jm' ->
    app_pred (tc_expr Delta e rho) (m_phi jm) ->
     cl_step psi (State vx tx k1)
      (m_dry jm) (State vx2 tx2 k2) (m_dry jm)) ->
  assert_safe Espec psi vx2 tx2 k2 (construct_rho (filter_genv psi) vx2 tx2)
 && tc_expr Delta e rho
|-- assert_safe Espec psi vx tx k1 (construct_rho (filter_genv psi) vx tx).
Proof.
intros.
intros w [Hw Hw'] ? J.
eexists; split; eauto; eexists; repeat split; eauto.
intros ora jm ? ?. subst.
destruct (level (m_phi jm)) eqn:?.
constructor.
destruct (levelS_age1 _ _ Heqn) as [phi' H1].
destruct (can_age1_juicy_mem _ _ H1) as [jm' H9].
clear phi' H1.
econstructor 2 with (m' := jm').
econstructor.
rewrite <- (age_jm_dry H9).
apply (H _ _ H9); auto.
split.
apply age1_resource_decay; assumption.
split; [apply age_level; assumption|].
apply age1_ghost_of, age_jm_phi; auto.
pose  proof (age_level _ _ H9).
rewrite <- level_juice_level_phi in Heqn.
rewrite Heqn in H1.
inv H1. clear Heqn.
eapply pred_hereditary in Hw;
  [ | instantiate (1:= (m_phi jm')); apply age_jm_phi; auto].
apply assert_safe_jsafe; auto.
Qed.

Lemma semax_switch: 
  forall {CS: compspecs} Espec Delta (Q: assert) a sl R,
     is_int_type (typeof a) = true ->
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     semax Espec Delta (fun rho => andp (prop (eval_expr a rho = Vint n)) (Q rho))
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     semax Espec Delta Q (Sswitch a sl) R.
Proof.
intros.
rewrite semax_eq.
apply allp_right; intro psi.
apply allp_right; intro Delta'.
apply prop_imp_right; intros [TS HGG].
apply imp_right.
rewrite TT_and.
apply allp_right; intro k.
apply allp_right; intro F.
apply imp_right.
rewrite <- andp_assoc;
 rewrite (andp_comm (believe _ _ _ _));
 rewrite andp_assoc;
 apply prop_andp_left; intro.
unfold guard, _guard.
apply allp_right; intro tx.
apply allp_right; intro vx.
rewrite andp_assoc.
apply prop_andp_subp'; intros [H4 H4'].
set (rho := construct_rho (filter_genv psi) vx tx) in *.
specialize (H0 rho).
apply frame_tc_expr with (F0 := F rho) in  H0.
rewrite sepcon_comm in H0.
apply subp_i1.
eapply derives_trans.
 apply andp_derives; [apply derives_refl | ].
 apply andp_derives; [ | apply derives_refl].
 apply andp_right; [ apply derives_refl | ].
 eapply derives_trans; [apply H0 | ].
 eapply tc_expr_sound; eauto.
 eapply typecheck_environ_sub; eauto.
rewrite andp_comm.
rewrite (andp_comm (_ * _)).
rewrite !andp_assoc.
apply derives_extract_prop; intro H0'.
destruct (typeof a) eqn:?; inv H.
destruct (eval_expr a rho) as [ | n | | | |] eqn:?;  try contradiction H0'.
specialize (H1 n).
rewrite semax_eq in H1.
match goal with |- ?A |-- _ => rewrite <- (TT_and A) end.
eapply derives_trans; [apply andp_derives; [ | apply derives_refl] | ].
eapply derives_trans; [ | apply @unfash_derives; apply H1].
rewrite fash_TT.
auto.
clear H1.
rewrite unfash_allp. rewrite (allp_andp psi). apply allp_left with psi.
rewrite unfash_allp. rewrite (allp_andp Delta'). apply allp_left with Delta'.
rewrite unfash_prop_imp.
rewrite prop_true_imp by auto.
rewrite unfash_imp.
rewrite unfash_andp.
rewrite (andp_comm (sepcon _ _)).
rewrite (andp_comm (funassert _ _)).
rewrite <- !andp_assoc.
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
apply andp_derives; [ | apply derives_refl].
apply andp_derives; [ | apply derives_refl].
rewrite andp_comm.
apply andp_imp_e.
rewrite unfash_allp. rewrite !(allp_andp (Kswitch :: k)). apply allp_left with (Kswitch :: k).
rewrite unfash_allp. rewrite !(allp_andp F). apply allp_left with F.
rewrite prop_true_andp 
  by (eapply closed_wrt_modvars_switch with (n:= Int.unsigned n); eauto).
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
apply andp_derives; [ | apply derives_refl].
apply andp_derives; [apply derives_refl | ].
eapply unfash_derives.
apply switch_rguard.
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
apply andp_derives; [ | apply derives_refl].
rewrite unfash_imp.
rewrite andp_comm.
apply andp_imp_e.
unfold guard, _guard.
rewrite unfash_allp. rewrite !(allp_andp tx). apply allp_left with tx.
rewrite unfash_allp. rewrite !(allp_andp vx). apply allp_left with vx.
fold rho.
rewrite (prop_true_andp (_ = _)) by auto.
eapply derives_trans.
apply andp_derives; [apply derives_refl | ].
apply andp_right; apply derives_refl.
rewrite !andp_assoc.
rewrite (andp_comm (sepcon _ _)).
rewrite <- (andp_assoc (funassert _ _)).
forget (funassert Delta' rho && (F rho * Q rho))%pred as FQ.
simpl current_function.
rewrite prop_true_andp by (split; auto).
rewrite <- andp_assoc.
eapply derives_trans.
apply andp_derives; [ | apply H0].
apply andp_derives; [ | apply derives_refl].
apply unfash_fash_imp.
eapply derives_trans.
apply andp_derives; [ | apply derives_refl].
rewrite andp_comm. apply andp_imp_e.
eapply typecheck_environ_sub in H4; try eassumption.
clear - H4 HGG Heqv Heqt.
apply assert_safe_step_nostore.
intros.
econstructor.
eapply eval_expr_relate; eauto.
fold rho.
rewrite Heqv, Heqt.
reflexivity.
Qed.

Lemma semax_switch_orig: 
  forall {CS: compspecs} Espec Delta (Q: assert) a sl R,
     is_int_type (typeof a) = true ->
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     semax Espec Delta (fun rho => andp (prop (eval_expr a rho = Vint n)) (Q rho))
               (seq_of_labeled_statement (select_switch (Int.unsigned n) sl))
               (switch_ret_assert R)) ->
     semax Espec Delta Q (Sswitch a sl) R.
Proof.
intros.
rewrite semax_unfold.
intros.
unfold guard.
intros tx vx.
set (rho := construct_rho (filter_genv psi) vx tx) in *.
specialize (H0 rho).
apply frame_tc_expr with (F0 := F rho) in  H0.
intros w' Hw' w'' Hw'' [[[H4 H4'] H5] H6].
rewrite sepcon_comm in H0; specialize (H0 _ H5).
assert (H0' := typecheck_expr_sound _ _ _ _ (typecheck_environ_sub _ _ TS _ H4) H0).
destruct (typeof a) eqn:?; inv H.
destruct (eval_expr a rho) as [ | n | | | |] eqn:?;  try contradiction H0'.
specialize (H1 n).
rewrite semax_unfold in H1.
specialize (H1 psi Delta' w TS HGG Prog_OK (Kswitch :: k) F).
specialize (H1 (closed_wrt_modvars_switch _ _ _ _ H2)); clear H2.
set (c := seq_of_labeled_statement (select_switch (Int.unsigned n) sl)) in *.
spec H1.
{ eapply switch_rguard; eauto. }
specialize (H1 tx vx w' Hw' _ Hw'').
spec H1.
{ clear H1.
  split; auto.
  split; auto.
  do 3 red. split; auto.
  fold rho. rewrite prop_true_andp by auto. auto. }
intros ? J; eexists; split; eauto; repeat eexists; auto.
intros ora jm H7 H8. subst; clear H7.
destruct (level (m_phi jm)) eqn:?.
constructor.
destruct (levelS_age1 _ _ Heqn0) as [phi' ?].
destruct (can_age1_juicy_mem _ _ H) as [jm' H9].
clear phi' H.
econstructor 2 with (m' := jm').
econstructor.
rewrite <- (age_jm_dry H9).
econstructor.
eapply eval_expr_relate; eauto.
eapply tc_expr_sub; eauto.
eapply typecheck_environ_sub; eauto.
fold rho. rewrite Heqv, Heqt.
reflexivity.
split.
apply age1_resource_decay; assumption.
split; [apply age_level; assumption|].
apply age1_ghost_of, age_jm_phi; auto.

pose  proof (age_level _ _ H9).
rewrite <- level_juice_level_phi in Heqn0.
rewrite Heqn0 in H.
inv H. clear Heqn0.
eapply assert_safe_jsafe, pred_hereditary, H1.
apply age_jm_phi; auto.
Qed.
