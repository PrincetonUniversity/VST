Require Import veric.base.
Require Import msl.normalize.
Require Import veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Import Mem.
Require Import msl.msl_standard.
Require Import veric.juicy_mem veric.juicy_mem_lemmas veric.juicy_mem_ops.
Require Import veric.res_predicates.
Require Import veric.seplog.
Require Import veric.assert_lemmas.
Require Import veric.Clight_new.
Require Import veric.extspec.
Require Import veric.step_lemmas.
Require Import veric.juicy_extspec.
Require Import veric.expr veric.expr_lemmas.
Require Import veric.semax.
Require Import veric.semax_lemmas.
Require Import veric.Clight_lemmas.

Open Local Scope pred.
Open Local Scope nat_scope.

Section extensions.
Context {Z} (Hspec : juicy_ext_spec Z).

Lemma funassert_exit_tycon: forall c Delta ek,
     funassert (exit_tycon c Delta ek) = funassert Delta.
Proof.
intros.
apply same_glob_funassert.
destruct ek; simpl; auto.
apply glob_types_update_tycon.
Qed.

Lemma semax_ifthenelse : 
   forall Delta P (b: expr) c d R,
      bool_type (typeof b) = true ->
     semax Hspec Delta (fun rho => P rho && !! expr_true b rho) c R -> 
     semax Hspec Delta (fun rho => P rho && !! expr_false b rho) d R -> 
     semax Hspec Delta 
              (fun rho => tc_expr Delta b rho && P rho)
              (Sifthenelse b c d) R.
Proof.
intros.
rewrite semax_unfold in H0, H1 |- *.
intros.
specialize (H0 psi _ Prog_OK k F).
specialize (H1 psi _ Prog_OK k F).
spec H0. intros i te' ?.  apply H2; simpl; auto. intros i0; destruct (H4 i0); intuition. left; left; auto.
spec H1. intros i te' ?.  apply H2; simpl; auto.
 clear - H4; intros i0; destruct (H4 i0); intuition. left; right; auto.
assert (H3then: app_pred
       (rguard Hspec psi (exit_tycon c Delta)  F R k) w).
clear - H3.
intros ek vl tx vx; specialize (H3 ek vl tx vx).
cbv beta in H3.
eapply subp_trans'; [ | apply H3].
apply derives_subp; apply andp_derives; auto.
unfold exit_tycon; simpl. destruct ek; simpl; auto.
intros ? ?; auto.
hnf in H|-*.
apply typecheck_environ_join1; auto.
repeat rewrite var_types_update_tycon. auto.
repeat rewrite glob_types_update_tycon. auto.
repeat rewrite funassert_exit_tycon in *; auto.
assert (H3else: app_pred
       (rguard Hspec psi (exit_tycon d Delta) F R k) w).
clear - H3.
intros ek vl tx vx; specialize (H3 ek vl tx vx).
eapply subp_trans'; [ | apply H3].
apply derives_subp; apply andp_derives; auto.
unfold exit_tycon; simpl. destruct ek; simpl; auto.
intros ? ?; hnf in H|-*; auto.
apply typecheck_environ_join2; auto.
repeat rewrite var_types_update_tycon. auto.
repeat rewrite glob_types_update_tycon. auto.
repeat rewrite funassert_exit_tycon in *; auto.
specialize (H0 H3then).
specialize (H1 H3else).
clear Prog_OK H3 H3then H3else.
intros tx vx; specialize (H0 tx vx); specialize (H1 tx vx).
remember (construct_rho (filter_genv psi) vx tx) as rho.
slurp.
rewrite <- fash_and.
intros ? ?. clear w H0.
revert a'.
apply fash_derives.
intros w [? ?].
intros ?w ? [[?TC  ?] ?].
apply extend_sepcon_andp in H4; auto.
destruct H4 as [TC2 H4].
hnf in TC2.
destruct H4 as [w1 [w2 [? [? ?]]]].
specialize (H0 w0 H3).
specialize (H1 w0 H3).
unfold expr_true, expr_false, Cnot in *.
intros ora jm Hge Hphi.
generalize (eval_expr_relate _ _ _ _ _ b (m_dry jm) Hge TC); intro.
assert (exists b': bool, strict_bool_val (eval_expr b rho) (typeof b) = Some b').
clear - TC H TC2.
assert (TCS := typecheck_expr_sound _ _ _ TC TC2).
remember (eval_expr b rho). destruct v;
simpl; destruct (typeof b); intuition; simpl in *; try rewrite TCS; eauto.
(* typechecking proof *)
destruct H9 as [b' ?].
apply wlog_safeN_gt0; intro.
subst w0.
change (level (m_phi jm)) with (level jm) in H10.
revert H10; case_eq (level jm); intros.
omegaContradiction.
apply levelS_age1 in H10. destruct H10 as [jm' ?].
clear H11.
apply (@safe_step'_back2 _ _ _ _ _ _ _ psi ora _ jm 
        (State vx tx (Kseq (if b' then c else d) :: k)) jm' _).
split3.
rewrite <- (age_jm_dry H10); econstructor; eauto.
apply strict_bool_val_sub; auto.
apply age1_resource_decay; auto.
apply age_level; auto.
change (level (m_phi jm)) with (level jm).
replace (level jm - 1)%nat with (level jm' ) by (apply age_level in H10; omega).
eapply @age_safe; try apply H10.
rewrite <- Hge in *.
destruct b'.
eapply H0; auto.
split; auto.
split; auto.
subst; auto.
rewrite andp_comm. rewrite prop_true_andp by auto.
do 2 econstructor; split3; eauto.
eapply H1; auto.
split; auto.
split; auto.
subst; auto.
rewrite andp_comm; rewrite prop_true_andp.
do 2 econstructor; split3; eauto.
clear - H TC TC2 H9.
assert (TCS := typecheck_expr_sound _ _ _ TC TC2).
simpl. unfold lift1. unfold typed_true. 
intuition; simpl in *;
unfold sem_notbool; destruct i0; destruct s; auto; simpl;
inv H9; rewrite negb_false_iff in H1; rewrite H1; auto.
Qed.

Lemma seq_assoc1:  
   forall Delta P s1 s2 s3 R,
        semax Hspec Delta P (Ssequence s1 (Ssequence s2 s3)) R ->
        semax Hspec Delta P (Ssequence (Ssequence s1 s2) s3) R.
Proof.
rewrite semax_unfold; intros.
intros.
specialize (H psi w Prog_OK k F).
spec H.
intros ? ? ?. apply H0.
intro i; destruct (H2 i); intuition.
clear - H3; left. simpl in *. unfold modified2 in *; intuition.
spec H; [solve [auto] |].
clear - H.
intros te ve ? ? ? ? ?.
specialize (H te ve y H0 a' H1 H2).
clear - H.
intros ora jm _ H2; specialize (H ora jm (eq_refl _) H2).
clear - H.
destruct (@level rmap ag_rmap a'); simpl in *; auto.
destruct H as [st' [m' [? ?]]].
destruct (corestep_preservation_lemma Hspec psi 
                     (Kseq (Ssequence s2 s3) :: k)
                     (Kseq s2 :: Kseq s3 :: k)
                     ora ve te jm n (Kseq s1) nil st' m')
       as [c2 [m2 [? ?]]]; simpl; auto.
intros. apply control_suffix_safe; simpl; auto.
clear.
intro; intros.
eapply convergent_controls_safe; try apply H0; simpl; auto.
intros.
destruct H1 as [H1 [H1a H1b]]; split3; auto.  inv H1; auto.
clear.
hnf; intros.
eapply convergent_controls_safe; try apply H0; simpl; auto.
clear; intros.
destruct H as [H1 [H1a H1b]]; split3; auto.  inv H1; auto.
destruct H as [H1 [H1a H1b]]; split3; auto.  inv H1; auto.
do 2 econstructor; split; try apply H2.
destruct H1 as [H1 [H1a H1b]]; split3; auto.
constructor; constructor; auto.
Qed.

Lemma seq_assoc2:  
   forall Delta P s1 s2 s3 R,
        semax Hspec Delta P (Ssequence (Ssequence s1 s2) s3) R ->
        semax Hspec Delta P (Ssequence s1 (Ssequence s2 s3)) R.
Proof.
rewrite semax_unfold; intros.
intros.
specialize (H psi w Prog_OK k F).
spec H.
intros ? ? ?. apply H0.
intro i; destruct (H2 i); intuition.
clear - H3; left. simpl in *. unfold modified2 in *; intuition.
spec H; [solve [auto] |].
clear - H.
intros te ve ? ? ? ? ?.
specialize (H te ve y H0 a' H1 H2).
clear - H.
intros ora jm _ H2; specialize (H ora jm (eq_refl _) H2).
clear - H.
destruct (@level rmap ag_rmap a'); simpl in *; auto.
destruct H as [st' [m' [? ?]]].
destruct (corestep_preservation_lemma Hspec psi 
                     (Kseq s2 :: Kseq s3 :: k)
                     (Kseq (Ssequence s2 s3) :: k)
                     ora ve te jm n (Kseq s1) nil st' m')
       as [c2 [m2 [? ?]]]; simpl; auto.
intros. apply control_suffix_safe; simpl; auto.
clear.
intro; intros.
eapply convergent_controls_safe; try apply H0; simpl; auto.
intros.
destruct H1 as [H1 [H1a H1b]]; split3; auto.
constructor; auto.
clear.
hnf; intros.
eapply convergent_controls_safe; try apply H0; simpl; auto.
clear; intros.
destruct H as [H1 [H1a H1b]]; split3; auto.
constructor; auto.
destruct H as [H1 [H1a H1b]]; split3; auto.
inv H1. inv H9; auto.
do 2 econstructor; split; try apply H2.
destruct H1 as [H1 [H1a H1b]]; split3; auto.
constructor. auto.
Qed. 

Lemma seq_assoc:  
   forall Delta P s1 s2 s3 R,
        semax Hspec Delta P (Ssequence s1 (Ssequence s2 s3)) R <->
        semax Hspec Delta P (Ssequence (Ssequence s1 s2) s3) R.
Proof.
intros.
split; intro.
apply seq_assoc1; auto.
apply seq_assoc2; auto.
Qed.

Lemma funassert_update_tycon:
  forall Delta h, funassert (update_tycon Delta h) = funassert Delta.
intros; apply same_glob_funassert. rewrite glob_types_update_tycon. auto.
Qed.

Lemma semax_seq:
forall Delta (R: ret_assert) P Q h t, 
    semax Hspec Delta P h (overridePost Q R) -> 
    semax Hspec (update_tycon Delta h) Q t R -> 
    semax Hspec Delta P (Clight.Ssequence h t) R.
Proof.
intros.
rewrite semax_unfold in H,H0|-*.
intros.
specialize (H psi w Prog_OK).
specialize (H0 psi w).
spec H0.
clear - Prog_OK.
unfold believe in *.
unfold believe_internal in *.
intros v fsig A P Q; specialize (Prog_OK v fsig A P Q).
intros ? ? ?. specialize (Prog_OK a' H).
spec Prog_OK.
destruct H0 as [id [? ?]]. exists id; split; auto.
rewrite glob_types_update_tycon in H0. auto.
destruct Prog_OK; [ left; auto | right].
destruct H1 as [b [f ?]]; exists b,f.
destruct H1; split; auto.
intro x; specialize (H2 x).
replace (func_tycontext' f (update_tycon Delta h)) with (func_tycontext' f Delta); auto.
unfold func_tycontext'.
f_equal; try reflexivity. apply eq_refl.
rewrite glob_types_update_tycon; auto.
assert ((guard Hspec psi Delta (fun rho : environ => F rho * P rho)%pred
   (Kseq h :: Kseq t :: k)) w).
Focus 2.
   eapply guard_safe_adj; try apply H3;
   intros until n; apply convergent_controls_safe; simpl; auto;
   intros; destruct q'.
   destruct H4 as [? [? ?]]; split3; auto. constructor; auto.
   destruct H4 as [? [? ?]]; split3; auto. constructor; auto.
(* End Focus 2 *)

eapply H; eauto.
repeat intro; apply H1. simpl. unfold modified2. intro i; destruct (H3 i); intuition.

clear - H0 H1 H2.
intros ek vl.
intros tx vx.
unfold overridePost.
if_tac.
subst.
unfold exit_cont.
unfold guard in H0.
rewrite <- andp_assoc.
remember (construct_rho (filter_genv psi) vx tx) as rho.
assert (app_pred
  (!!(typecheck_environ rho (update_tycon Delta h) = true) &&
   (F rho * (Q rho)) && funassert Delta rho >=>
   assert_safe Hspec psi vx tx (Kseq t :: k) rho) w).
subst.
specialize (H0 k F).
spec H0.
clear - H1;
repeat intro; apply H1. simpl. unfold modified2. intro i; destruct (H i); intuition.
spec H0.
clear - H2.
intros ek vl te ve; specialize (H2 ek vl te ve).
eapply subp_trans'; [ | apply H2].
apply derives_subp. apply andp_derives; auto.
simpl.
intros ? ?; hnf in H|-*; auto.
clear - H.
destruct ek; simpl in *; auto; try solve [eapply typecheck_environ_update; eauto].
cbv beta in H2.
repeat rewrite funassert_exit_tycon. 
rewrite funassert_update_tycon; auto.
specialize (H0 tx vx). cbv beta in H0.
rewrite funassert_update_tycon in H0.
apply H0.
eapply subp_trans'; [ | apply H].
apply derives_subp. apply andp_derives; auto. apply andp_derives; auto.
apply sepcon_derives; auto.
apply andp_left2; auto.
rewrite funassert_exit_tycon. auto.
replace (exit_cont ek vl (Kseq t :: k)) with (exit_cont ek vl k)
  by (destruct ek; simpl; congruence).
unfold rguard in H2.
specialize (H2 ek vl tx vx).
replace (exit_tycon h Delta ek) with Delta.
eapply subp_trans'; [ | apply H2].
apply derives_subp.
apply andp_derives; auto.
replace (exit_tycon (Ssequence h t) Delta ek) with Delta; auto.
destruct ek; try congruence; auto.
destruct ek; try congruence; auto.
destruct ek; try congruence; auto.
Qed.

Lemma semax_for : 
forall Delta Q Q' test incr body R,
     bool_type (Clight.typeof test) = true ->
     (forall rho, Q rho |-- tc_expr Delta test rho) ->
     (forall rho,  !! expr_false (test) rho && Q rho |-- R EK_normal None rho) ->
     semax Hspec Delta
                (fun rho => !! expr_true test rho && Q rho) body (for1_ret_assert Q' R) ->
     semax Hspec Delta Q' incr (for2_ret_assert Q R) ->
     semax Hspec Delta Q (Sfor' test incr body) R.
Proof.
intros ? ? ? ? ? ? ? BT TC POST H H0.
rewrite semax_unfold.
intros until 2.
rename H1 into H2.
assert (CLO_body: closed_wrt_modvars body F).
  clear - H2. intros rho te ?. apply (H2 rho te). simpl.  unfold modified2; intro; destruct (H i); auto.
assert (CLO_incr:  closed_wrt_modvars incr F).
  clear - H2. intros rho te ?. apply (H2 rho te). simpl.  unfold modified2; intro; destruct (H i); auto.
revert Prog_OK; induction w using (well_founded_induction lt_wf); intros.
intros tx vx.
intros ? ? ? ? [[? ?] ?]. hnf in H6.
simpl update_tycon in H3.
apply assert_safe_last; intros a2 LEVa2.
assert (NEC2: necR w (level a2)).
  apply age_level in LEVa2. apply necR_nat in H5. apply nec_nat in H5. 
  change w with (level w) in H4|-*. apply nec_nat. clear - H4 H5 LEVa2.
  change compcert_rmaps.R.rmap with rmap in *; omega.
assert (LT: level a2 < level w).
  apply age_level in LEVa2. apply necR_nat in H5. 
 clear - H4 H5 LEVa2.
   change w with (level w) in H4.
  change R.rmap with rmap in *.  rewrite LEVa2 in *.  clear LEVa2. 
  apply nec_nat in H5. omega.
assert (Prog_OK2: (believe Hspec Delta psi Delta) (level a2)) 
  by (apply pred_nec_hereditary with w; auto).
generalize (pred_nec_hereditary _ _ _ NEC2 H3); intro H3'.
remember (construct_rho (filter_genv psi) vx tx) as rho.
assert (exists b, strict_bool_val (eval_expr test rho) (typeof test) = Some b).
clear - H6 TC BT H7.
destruct H7 as [w1 [w2 [_ [_ ?]]]].
apply TC in H. hnf in H.
pose proof (typecheck_expr_sound Delta rho test H6 H).
apply typecheck_bool_val; auto.
destruct H9 as [b ?].
intros ora jm RE H11.
pose (H10:=True).
replace (level a') with (S (level a2)) 
 by (apply age_level in LEVa2;  rewrite LEVa2; apply minus_n_O).
subst a'.
destruct (can_age1_juicy_mem _ _ LEVa2) as [jm' LEVa2'].
unfold age in LEVa2.
assert (a2 = m_phi jm').
  generalize (age_jm_phi LEVa2'); unfold age; change R.rmap with rmap; 
           change R.ag_rmap with ag_rmap;  rewrite LEVa2; intro Hx; inv Hx; auto.
subst a2.
clear LEVa2; rename LEVa2' into LEVa2.
apply safe_corestep_backward
 with (State vx tx (if b then Kseq body :: Kseq Scontinue :: Kfor2 test incr body :: k else k))
        jm'.
split3.
rewrite (age_jm_dry LEVa2); econstructor; apply strict_bool_val_sub in H9; eauto.
apply eval_expr_relate with (Delta:=Delta); auto. destruct H7. 
destruct H7. destruct H7. destruct H11.
specialize (TC rho). unfold tc_expr in TC. specialize (TC _ H12). 
apply TC. 
apply age1_resource_decay; auto.
apply age_level; auto.
assert (w >= level (m_phi jm)).
apply necR_nat in H5. apply nec_nat in H5. 
 change R.rmap with rmap in *; omega. 
clear y H5 H4. rename H11 into H5. pose (H4:=True).
destruct b.
(* Case 1: expr evaluates to true *)
Focus 1.
generalize H; rewrite semax_unfold; intros H'.
specialize (H' psi (level jm') Prog_OK2 (Kseq Scontinue :: Kfor2 test incr body :: k) F CLO_body).
spec H'.
intros ek vl.
destruct ek.
simpl exit_cont.
rewrite semax_unfold in H0.
specialize (H0 psi (level jm') Prog_OK2 (Kfor3 test incr body :: k) F CLO_incr).
spec H0.
intros ek2 vl2 tx2 vx2; unfold for2_ret_assert.
destruct ek2; simpl exit_tycon in *.
unfold exit_cont.
apply (assert_safe_adj' Hspec) with (k:=Kseq (Sfor' test incr body) :: k); auto.
repeat intro. eapply convergent_controls_safe; try apply H12; simpl; auto.
  intros q' m' [? [? ?]]; split3; auto. inv H13; econstructor; eauto.
 eapply subp_trans'; [ |  eapply (H1 _ LT Prog_OK2 H3' tx2 vx2)].
 apply derives_subp.
rewrite andp_assoc.
rewrite funassert_update_tycon; 
apply andp_derives; auto.
intros ? ?; auto.
hnf in H11|-*.
eapply typecheck_environ_update; eauto.
simpl exit_cont.
 normalize. normalize.
change (exit_cont EK_return vl2 (Kfor3 test incr body :: k))
  with (exit_cont EK_return vl2 k).
eapply subp_trans'; [ | apply H3'].
auto.
intros tx2 vx2.
apply (assert_safe_adj' Hspec) with (k:= Kseq incr :: Kfor3 test incr body :: k); auto.
intros ? ? ? ? ? ? ?.
eapply convergent_controls_safe; simpl; eauto.
intros q' m' [? [? ?]]; split3; auto. constructor. simpl. auto.
eapply subp_trans'; try apply H0.
apply derives_subp.
rewrite andp_assoc.
rewrite funassert_exit_tycon; 
apply andp_derives; auto.
simpl exit_tycon.
intros ? ?.
hnf in H11|-*.
eapply typecheck_environ_update; eauto.
simpl exit_cont.
simpl exit_tycon.
unfold for1_ret_assert.
intros tx3 vx3.
eapply subp_trans'; [ | apply (H3' EK_normal None tx3 vx3)].
simpl exit_tycon.
apply derives_subp.
auto.
simpl exit_tycon. simpl exit_cont.
unfold for1_ret_assert.
rewrite semax_unfold in H0.
intros tx2 vx2.
eapply subp_trans'; [ | apply (H0 _ _ Prog_OK2 (Kfor3 test incr body :: k) F CLO_incr)].
apply derives_subp.
rewrite andp_assoc.
apply andp_derives; auto.
clear tx2 vx2.
intros ek2 vl2 tx2 vx2.
destruct ek2.
unfold exit_cont.
apply (assert_safe_adj' Hspec) with (k:=Kseq (Sfor' test incr body) :: k); auto.
intros ? ? ? ? ? ? ?.
eapply convergent_controls_safe; simpl; eauto.
intros q' m' [? [? ?]]; split3; auto. inv H12; econstructor; eauto.
eapply subp_trans'; [ | eapply H1; eauto].
apply derives_subp.
rewrite andp_assoc.
rewrite funassert_exit_tycon; 
apply andp_derives; auto.
simpl exit_tycon.
intros ? ?.  hnf in H11|-*.
eapply typecheck_environ_update; eauto.
unfold exit_cont, for2_ret_assert; normalize.
unfold exit_cont, for2_ret_assert; normalize.


 change (exit_cont EK_return vl2 (Kfor3 test incr body :: k))
  with (exit_cont EK_return vl2 k).
 specialize (H3' EK_return vl2 tx2 vx2). simpl exit_tycon in H3'.
 simpl exit_tycon. auto.
change (exit_cont EK_return vl (Kseq Scontinue :: Kfor2 test incr body :: k))
    with (exit_cont EK_return vl k).
intros tx4 vx4.
eapply subp_trans'; [ | eapply H3'; eauto].
 simpl exit_tycon.
unfold for1_ret_assert.
auto.
apply (H' tx vx _ (le_refl _) (m_phi jm') (necR_refl _)); try solve[subst; auto].
apply pred_hereditary with (m_phi jm); auto.
apply age_jm_phi; auto.
subst.
split; auto.
split; auto.
rewrite prop_true_andp; auto.

(* Case 2: expr evaluates to false *)
apply (H3' EK_normal None tx vx _ (le_refl _) _ (necR_refl _)); auto.
rewrite prop_true_andp by (subst; auto).
apply pred_hereditary with (m_phi jm); auto.
apply age_jm_phi; auto.
split; subst; auto.
eapply sepcon_derives; try apply H7; auto.
eapply derives_trans; try apply POST.
apply andp_right; auto.
intros ? ?.
hnf.

subst.
clear - BT H9.
 simpl in *. 
 change true with (negb false).
 assert (x:=bool_val_Cnot (construct_rho (filter_genv psi) vx tx) test false). simpl in x.
 destruct (typeof test); simpl in *; try congruence; intuition.
Qed.


Lemma semax_while : 
forall Delta Q test body R,
     bool_type (Clight.typeof test) = true ->
    (forall rho, Q rho |-- tc_expr Delta test rho) ->
     (forall rho,  !! (expr_false test rho) && Q rho |-- R EK_normal None rho) ->
     semax Hspec Delta 
                (fun rho => !! expr_true test rho && Q rho) body (for1_ret_assert Q R) ->
     semax Hspec Delta Q (Swhile test body) R.
Proof.
intros ? ? ? ? ? BT TC POST H.
assert (semax Hspec Delta Q Sskip (for2_ret_assert Q R)).
eapply semax_post; [ | apply semax_skip].
destruct ek; unfold normal_ret_assert, for2_ret_assert; intros; normalize; inv H0; try discriminate.
pose proof (semax_for Delta Q Q test Sskip body R BT TC POST H H0).
clear H H0.
rewrite semax_unfold in H1|-*.
rename H1 into H0; pose (H:=True).
intros.
assert (closed_wrt_modvars (Sfor' test Sskip body) F).
hnf; intros; apply H1.
intro i; destruct (H3 i); [left | right]; auto.
clear - H4.
destruct H4; auto.
contradiction H.
specialize (H0 _ _ Prog_OK k F H3 H2).
clear - H0.
eapply guard_safe_adj; try eassumption.
clear; intros.
destruct n; simpl in *; auto.
destruct H as [c' [m' [? ?]]]; exists c'; exists m'; split; auto.
destruct H.
split.
constructor. auto.
auto.
Qed.

End extensions.
