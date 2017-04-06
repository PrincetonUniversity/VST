Require Import veric.juicy_base.
Require Import msl.normalize.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.extend_tc.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import sepcomp.extspec.
Require Import sepcomp.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.expr2.
Require Import veric.expr_lemmas.
Require Import veric.semax.
Require Import veric.semax_lemmas.
Require Import veric.Clight_lemmas.

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
 

Lemma semax_switch: 
  forall Espec {CS: compspecs} Delta (Q: assert) a sl R,
     is_int_type (typeof a) = true ->
     (forall rho, Q rho |-- tc_expr Delta a rho) ->
     (forall n,
     semax Espec Delta (fun rho => andp (prop (eval_expr a rho = Vint (Int.repr n))) (Q rho))
               (seq_of_labeled_statement (select_switch n sl))
               (switch_ret_assert R)) ->
     semax Espec Delta Q (Sswitch a sl) R.
Proof.
intros.
rewrite semax_unfold.
intros.
unfold guard.
intros tx vx.
intros w' Hw' w'' Hw'' [[H4 H5] H6].
intros ora jm H7 H8. subst w''; clear H7.
set (rho := construct_rho (filter_genv psi) vx tx) in *.
specialize (H0 rho).
destruct H5 as [w1 [w2 [? [? ?]]]].
specialize (H0 _ H8).
destruct H4 as [H4 H4'].
assert (H0' := typecheck_expr_sound _ _ _ _ (typecheck_environ_sub _ _ TS _ H4) H0).
destruct (typeof a) eqn:?; inv H.
destruct (eval_expr a rho) eqn:?; try contradiction H0'.
pose (n := Int.unsigned i0).
specialize (H1 n).
destruct (level (m_phi jm)) eqn:?.
constructor.
destruct (levelS_age1 _ _ Heqn0) as [phi' ?].
destruct (can_age1_juicy_mem _ _ H) as [jm' ?].
clear phi' H.
econstructor 2 with (m' := jm').
econstructor.
rewrite <- (age_jm_dry H9).
econstructor.
eapply eval_expr_relate; eauto.
eapply tc_expr_sub; eauto.
eapply typecheck_environ_sub; eauto.
clear - H0 H5.
rewrite <- (extend_tc_expr Delta a rho) in H0.
apply H0. exists w1; auto.
fold rho. rewrite Heqv, Heqt.
reflexivity.
split.
apply age1_resource_decay; assumption.
apply age_level; assumption.
fold n.
set (c := seq_of_labeled_statement (select_switch n sl)) in *.
pose  proof (age_level _ _ H9).
rewrite <- level_juice_level_phi in Heqn0.
rewrite Heqn0 in H.
inv H. clear Heqn0.
rewrite semax_unfold in H1.
specialize (H1 psi Delta' w TS HGG Prog_OK (Kswitch :: k) F).
specialize (H1 (closed_wrt_modvars_switch _ _ _ _ H2)); clear H2.
spec H1. {
 clear - H3.
 intros ek vl tx' vx'.
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
 specialize (H3 ek' vl' tx' vx').
 cbv beta in *.
 set (rho' := construct_rho (filter_genv psi) vx' tx') in *.
 cbv beta zeta in *.
 intros w' H0 w'' H1 [[H2 H4] H5].
 specialize (H3 w' H0 w'' H1).
 spec H3. {
 split; [split | ].
 *
 destruct H2; split.
 +
  clear - H.
  subst ek'.
  destruct ek; simpl in *; auto.
  subst c.
  eapply typecheck_environ_join_switch1; eauto.
   apply typecheck_environ_join_switch2; auto.
 +
  simpl in H2.
  destruct (current_function k); auto.
  destruct H2; split; auto.
   clear - H6.
   subst ek'. rewrite ret_type_exit_tycon in *. auto.
 *
 clear - H4.
 destruct ek; unfold frame_ret_assert in *; 
  simpl switch_ret_assert in H4; auto.
  normalize in H4; contradiction.
 *
  clear - H5.
 rewrite funassert_exit_tycon in H5|-*. auto.
 }
 clear - H3 H4.
 hnf in H3|-*.
 intros. specialize (H3 ora _ H H0).
 clear - H3 H4.
 destruct (level w'') eqn:?.
 constructor.
 inv H3; [ | inv H0 | inv H].
 econstructor 2.
 2: eassumption.
 subst ek' vl'; destruct ek; simpl in *; auto.
 destruct H4 as [? [? [? [? ?]]]]; contradiction.
}
hnf in H1.
specialize (H1 tx vx w' Hw' _ Hw'').
spec H1. {
 clear H1.
 split; auto.
 split; auto.
 do 3 red. split; auto.
 exists w1, w2. split3; auto.
 split; auto. do 3 red.
 fold rho. rewrite Heqv.
 subst n. rewrite Int.repr_unsigned. auto.
}
eapply pred_hereditary in H1;
  [ | instantiate (1:= (m_phi jm')); apply age_jm_phi; auto].
apply H1; auto.
Qed.



