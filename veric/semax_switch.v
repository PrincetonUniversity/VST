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
Require Import veric.semax_congruence.
Require Import veric.Clight_lemmas.

(*
      Clight.eval_expr ge ve te m a v ->
      Cop.sem_switch_arg v (typeof a) = Some n ->
      cl_step ge (State ve te (Kseq (Sswitch a sl) :: k)) m
              (State ve te (Kseq (seq_of_labeled_statement (select_switch n sl)) :: Kswitch :: k)) m

*)

Definition switch_ret_assert (R: ret_assert) : ret_assert :=
 fun ek vl =>
 match ek with
 | EK_normal => seplog.FF
 | EK_break => R EK_normal None
 | EK_continue => R EK_continue None
 | EK_return => R EK_return vl
 end.


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

Lemma semax_switch: 
  forall {CS: compspecs} Espec Delta (Q: assert) a sl R,
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


Print update_tycon.
rewrite semax_unfold in H1.
specialize (H1 psi Delta' w TS HGG Prog_OK (Kswitch :: k) F).
spec H1.
eapply closed_wrt_modvars_switch; eauto.
spec H1.
intros ek vl tx' vx'; specialize (H3 ek vl tx' vx').
simpl in H3|-*.

Print exit_cont.
simpl exit_cont.
simpl in H3.
fold rho.
unfold rguard in H3|-*.  


 eapply IHsl.

 auto. 
  
  
  simpl in Heqo.
  
  auto.
  unfold select_switch in H0.
  simpl in H0.
  destruct o.
  destruct (zeq z n). subst. auto. simpl.
  destruct (select_switch_case n sl) eqn:?.
  rewrite modifiedvars'_union. right. 
  clear - Heqo H0.
  revert s0 l Heqo H0; induction sl; intros.
  inv Heqo.
  simpl. simpl in Heqo. destruct o. destruct (zeq z n). subst z.
  inv Heqo. simpl in H0. auto.
  specialize (IHsl s0 _ Heqo H0).
  rewrite modifiedvars'_union; right; auto.
  specialize (IHsl s0 _ Heqo H0).
  rewrite modifiedvars'_union; right; auto.
  rewrite modifiedvars'_union; right; auto.
  clear - H0.
  induction sl; simpl in *. auto. destruct o.
  rewrite modifiedvars'_union; right; auto.
  simpl in H0. auto.
  simpl.
  unfold select_switch in *.
  destruct (select_switch_case n sl).
  rewrite modifiedvars'_union; right; auto.
  
  apply IHsl.
  
 
  unfold select_switch_default in H0.

  apply IHsl.
*. simpl in Heqo. simpl.
  simpl.
revert s H0; induction sl; simpl; intros.
auto.
unfold select_switch in H0.
simpl in H0.
destruct o.
destruct (zeq z n). subst.
simpl in H0.
clear - H0.


revert s0 H0; induction sl; simpl; intros; auto.
apply IHsl.


auto.
simpl in H0.

Search isSome.
destruct H0.
(H rho te').

hnf in H|-*.
 
simpl in H2.

hnf in H1.

apply H1.
apply resource_decay_refl.
apply juicy_mem_alloc_cohere.

intros.
Search nextblock m_phi.
clear - H.
pose proof juicy_mem_alloc_cohere.
Locate access_cohere.
Search m_dry m_phi.

SearchHead (resource_decay _ _ _).
unfold sem_switch_arg. simpl.
red in H.

SearchAbout tc_expr join.
SearchAbout tycontext_sub.
Check eval_expr_sub.

Search jsafeN.

Lemma tc_val_Tint_e1:
  forall i s a n, tc_val (Tint i s a) (Vint n) ->
     exists n', n = Int.repr n'.
Proof.
intros.
(*destruct i,s; simpl in H.*)
exists (Int.signed n). rewrite Int.repr_signed; auto.

SearchAbout is_int_type.
SearchAbout Int.repr tc_val.
simpl in H0.
 inv H0.
destruct H4.
unfold typecheck_expr in H0.
SearchHead (_ |-- denote_tc_tc_expr _ _ _ ).




unfold exit_tycon in H2.
destruct H3.
simpl in H8.

eapply safeN_step.
Print safeN_.

econstructor 3.
SearchHead (jsafeN _ _ _ _ _ _).
hnf.
hnf in H2.














