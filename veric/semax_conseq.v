Require Import VST.veric.juicy_base.
Require Import VST.veric.juicy_mem VST.veric.juicy_mem_lemmas VST.veric.juicy_mem_ops.
Require Import VST.veric.res_predicates.
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
Require Import VST.veric.own.

Local Open Scope pred.

(* This file contains two parts:
   1. Proof of semax_conseq.
   2. Deriving simpler and older version of consequence rules from semax_conseq.
   3. semax_extract_pre, and proof of semax_adapt_frame rules from semax_conseq, and 2 specializations of semax_adapt_frame. *)

(* Part 1: Proof of semax_conseq *)

Lemma _guard_mono: forall Espec ge Delta f (P Q: assert) k,
  (forall rho, P rho |-- Q rho) ->
  _guard Espec ge Delta f Q k |-- _guard Espec ge Delta f P k.
Proof.
  intros.
  unfold _guard.
  apply allp_derives; intros tx.
  apply allp_derives; intros vx.
  apply fash_derives.
  apply imp_derives; auto.
Qed.

Lemma guard_mono: forall Espec ge Delta f (P Q: assert) k,
  (forall rho, P rho |-- Q rho) ->
  guard Espec ge Delta f Q k |-- guard Espec ge Delta f P k.
Proof.
  intros.
  unfold guard.
  apply _guard_mono; auto.
Qed.

Lemma rguard_mono: forall Espec ge Delta f (P Q: ret_assert) k,
  (forall rk vl rho, proj_ret_assert P rk vl rho |-- proj_ret_assert Q rk vl rho) ->
  rguard Espec ge Delta f Q k |-- rguard Espec ge Delta f P k.
Proof.
  intros.
  unfold rguard.
  apply allp_derives; intros ek.
  apply allp_derives; intros vl.
  apply _guard_mono; auto.
Qed.

Definition fupd_ret_assert (Q: ret_assert): ret_assert :=
          {| RA_normal := fun rho => fupd (RA_normal Q rho);
             RA_break := fun rho => fupd (RA_break Q rho);
             RA_continue := fun rho => fupd (RA_continue Q rho);
             RA_return := fun v rho => RA_return Q v rho |}.
(* Asymmetric consequence: since there's no CompCert step that
   corresponds to RA_return, we can't do an update there. We could
   probably add a bupd if we really want to, but it may not be
   necessary. *)

Lemma fupd_fupd_andp_prop : forall P Q, fupd (!! P && fupd Q) = fupd (!!P && Q).
Proof.
  intros; apply pred_ext.
  - eapply derives_trans, fupd.fupd_trans.
    apply fupd.fupd_mono, fupd.fupd_andp_prop.
  - apply fupd.fupd_mono.
    apply andp_derives, fupd.fupd_intro; auto.
Qed.

Lemma fupd_idem : forall P, fupd (fupd P) = fupd P.
Proof.
  intros; apply pred_ext.
  - apply fupd.fupd_trans.
  - apply fupd.fupd_intro.
Qed.

Lemma proj_fupd_ret_assert: forall Q ek vl rho,
  fupd (proj_ret_assert (fupd_ret_assert Q) ek vl rho) = fupd (proj_ret_assert Q ek vl rho).
Proof.
  intros.
  destruct ek; simpl; auto; apply fupd_fupd_andp_prop.
Qed.

(* The following four lemmas is not now used. but after deep embedded hoare logic (SL_as_Logic) is
ported, the frame does not need to be quantified in the semantic definition of semax. Then,
these two lemmas can replace the other two afterwards. *)

Lemma assert_safe_fupd':
  forall {Espec: OracleKind} gx vx tx rho (P: environ -> pred rmap) Delta f k,
    match k with Ret _ _ => False | _ => True end ->
    let PP1 := !! guard_environ Delta f rho in
    let PP2 := funassert Delta rho in
    PP1 && (P rho) && PP2 >=>
    assert_safe Espec gx f vx tx k rho =
    PP1 && (fupd (P rho)) && PP2 >=>
    assert_safe Espec gx f vx tx k rho.
Proof.
  intros.
  apply pred_ext.
  * eapply derives_trans; [apply fupd.subp_fupd, derives_refl | apply subp_derives, assert_safe_fupd; auto].
    eapply derives_trans; [apply andp_derives, derives_refl; apply fupd.fupd_andp_prop|].
    rewrite andp_comm, (andp_comm (_ && _)).
    apply fupd.fupd_andp_corable, corable_funassert.
  * apply subp_derives, derives_refl.
    apply andp_derives, derives_refl.
    apply andp_derives, fupd.fupd_intro; apply derives_refl.
Qed.

Lemma _guard_fupd':
  forall {Espec: OracleKind} ge Delta (P: environ -> pred rmap) f k,
    match k with Ret _ _ => False | _ => True end ->
    _guard Espec ge Delta f P k = _guard Espec ge Delta f (fun rho => fupd (P rho)) k.
Proof.
  intros.
  unfold _guard.
  f_equal; extensionality tx.
  f_equal; extensionality vx.
  apply assert_safe_fupd'; auto.
Qed.
  
Lemma guard_fupd':
  forall {Espec: OracleKind} ge Delta f (P: environ -> pred rmap) k,
    guard Espec ge Delta f P k = guard Espec ge Delta f (fun rho => fupd (P rho)) k.
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
  forall {Espec: OracleKind} ge Delta f (P: ret_assert) k,
    rguard Espec ge Delta f P k = rguard Espec ge Delta f (fupd_ret_assert P) k.
Proof.
  intros.
  unfold rguard.
  f_equal; extensionality ek.
  f_equal; extensionality vl.
  destruct (eq_dec ek EK_return); subst; auto.
  rewrite _guard_fupd'; [|apply exit_cont_nonret; auto].
  setoid_rewrite _guard_fupd' at 2; [|apply exit_cont_nonret; auto].
  apply pred_ext; apply _guard_mono; intros; rewrite proj_fupd_ret_assert; auto.
Qed.

Lemma assert_safe_fupd:
  forall {Espec: OracleKind} gx vx tx rho (F P: environ -> pred rmap) Delta f k,
    match k with Ret _ _ => False | _ => True end ->
    let PP1 := !! guard_environ Delta f rho in
    let PP2 := funassert Delta rho in
    PP1 && (F rho * P rho) && PP2 >=>
    assert_safe Espec gx f vx tx k rho =
    PP1 && (F rho * fupd (P rho)) && PP2 >=>
    assert_safe Espec gx f vx tx k rho.
Proof.
  intros.
  apply pred_ext.
  + eapply derives_trans; [apply fupd.subp_fupd, derives_refl | apply subp_derives, assert_safe_fupd; auto].
    eapply derives_trans; [apply andp_derives, derives_refl; apply andp_derives, fupd.fupd_frame_l; apply derives_refl|].
    eapply derives_trans; [apply andp_derives, derives_refl; apply fupd.fupd_andp_prop|].
    rewrite andp_comm, (andp_comm (_ && _)).
    apply fupd.fupd_andp_corable, corable_funassert.
  + apply subp_derives, derives_refl.
    apply andp_derives, derives_refl.
    apply andp_derives, sepcon_derives, fupd.fupd_intro; apply derives_refl.
Qed.

Lemma _guard_fupd:
  forall {Espec: OracleKind} ge Delta f (F P: environ -> pred rmap) k,
    match k with Ret _ _ => False | _ => True end ->
    _guard Espec ge Delta f (fun rho => F rho * P rho) k = _guard Espec ge Delta f (fun rho => F rho * fupd (P rho)) k.
Proof.
  intros.
  unfold _guard.
  f_equal; extensionality tx.
  f_equal; extensionality vx.
  apply assert_safe_fupd; auto.
Qed.
  
Lemma guard_fupd:
  forall {Espec: OracleKind} ge Delta f (F P: environ -> pred rmap) k,
    guard Espec ge Delta f (fun rho => F rho * P rho) k = guard Espec ge Delta f (fun rho => F rho * fupd (P rho)) k.
Proof.
  intros.
  apply _guard_fupd; auto.
Qed.

Lemma fupd_fupd_frame_l : forall P Q, fupd (P * fupd Q) = fupd (P * Q).
Proof.
  intros; apply pred_ext.
  - eapply derives_trans, fupd.fupd_trans.
    apply fupd.fupd_mono, fupd.fupd_frame_l.
  - apply fupd.fupd_mono, sepcon_derives, fupd.fupd_intro; auto.
Qed.

Lemma proj_fupd_ret_assert_frame: forall F Q ek vl rho,
  fupd (F * proj_ret_assert (fupd_ret_assert Q) ek vl rho) = fupd (F * proj_ret_assert Q ek vl rho).
Proof.
  intros.
  destruct ek; simpl; auto;
    rewrite <- fupd_fupd_frame_l, fupd_fupd_andp_prop, fupd_fupd_frame_l; auto.
Qed.

Lemma rguard_fupd:
  forall {Espec: OracleKind} ge Delta F f (P: ret_assert) k,
    rguard Espec ge Delta f (frame_ret_assert P F) k = rguard Espec ge Delta f (frame_ret_assert (fupd_ret_assert P) F) k.
Proof.
  intros.
  unfold rguard.
  f_equal; extensionality ek.
  f_equal; extensionality vl.
  rewrite !proj_frame.
  destruct (eq_dec ek EK_return); subst; auto.
  rewrite _guard_fupd'; [|apply exit_cont_nonret; auto].
  setoid_rewrite _guard_fupd' at 2; [|apply exit_cont_nonret; auto].
  apply pred_ext; apply _guard_mono; intros; rewrite proj_fupd_ret_assert_frame; auto.
Qed.

Lemma _guard_allp_fun_id:
  forall {Espec: OracleKind} ge Delta' Delta f (F P: environ -> pred rmap) k,
    tycontext_sub Delta Delta' ->
    _guard Espec ge Delta' f (fun rho => F rho * P rho) k = _guard Espec ge Delta' f (fun rho => F rho * (allp_fun_id Delta rho && P rho)) k.
Proof.
  intros.
  unfold _guard.
  f_equal; extensionality tx.
  f_equal; extensionality vx.
  f_equal.
  f_equal.
  rewrite !andp_assoc.
  f_equal.
  rewrite corable_sepcon_andp1 by apply corable_allp_fun_id.
  rewrite (andp_comm (allp_fun_id _ _ )), andp_assoc.
  f_equal.
  apply pred_ext; [apply andp_right; auto | apply andp_left2; auto].
  intros w W. hnf.
  eapply funassert_allp_fun_id_sub; eauto.
Qed.

Lemma guard_allp_fun_id: forall {Espec: OracleKind} ge Delta' Delta f (F P: environ -> pred rmap) k,
  tycontext_sub Delta Delta' ->
  guard Espec ge Delta' f (fun rho => F rho * P rho) k = guard Espec ge Delta' f (fun rho => F rho * (allp_fun_id Delta rho && P rho)) k.
Proof.
  intros.
  apply _guard_allp_fun_id; auto.
Qed.

Lemma rguard_allp_fun_id: forall {Espec: OracleKind} ge Delta' Delta f (F: environ -> pred rmap) P k,
  tycontext_sub Delta Delta' ->
  rguard Espec ge Delta' f (frame_ret_assert P F) k = rguard Espec ge Delta' f (frame_ret_assert (conj_ret_assert P (allp_fun_id Delta)) F) k.
Proof.
  intros.
  unfold rguard.
  f_equal; extensionality ek.
  f_equal; extensionality vl.
  rewrite !proj_frame.
  rewrite proj_conj.
  apply _guard_allp_fun_id; auto.
Qed. 

Lemma _guard_tc_environ:
  forall {Espec: OracleKind} ge Delta' Delta f (F P: environ -> pred rmap) k,
    tycontext_sub Delta Delta' ->
    _guard Espec ge Delta' f (fun rho => F rho * P rho) k = 
    _guard Espec ge Delta' f (fun rho => F rho * (!! typecheck_environ Delta rho && P rho)) k.
Proof.
  intros.
  unfold _guard.
  f_equal; extensionality tx.
  f_equal; extensionality vx.
  f_equal.
  f_equal.
  f_equal.
  rewrite corable_sepcon_andp1 by apply corable_prop.
  rewrite <- andp_assoc.
  f_equal.
  apply pred_ext; [apply andp_right; auto | apply andp_left1; auto].
  intros ? ?; simpl in *.
  destruct H0 as [? _].
  eapply typecheck_environ_sub; eauto.
Qed.

Lemma guard_tc_environ: forall {Espec: OracleKind} ge Delta' Delta f (F P: environ -> pred rmap) k,
  tycontext_sub Delta Delta' ->
  guard Espec ge Delta' f (fun rho => F rho * P rho) k = guard Espec ge Delta' f (fun rho => F rho * (!! typecheck_environ Delta rho && P rho)) k.
Proof.
  intros.
  apply _guard_tc_environ; auto.
Qed.

Lemma rguard_tc_environ: forall {Espec: OracleKind} ge Delta' Delta f (F: environ -> pred rmap) P k,
  tycontext_sub Delta Delta' ->
  rguard Espec ge Delta' f (frame_ret_assert P F) k = rguard Espec ge Delta'  f (frame_ret_assert (conj_ret_assert P (fun rho => !! typecheck_environ Delta rho)) F) k.
Proof.
  intros.
  unfold rguard.
  f_equal; extensionality ek.
  f_equal; extensionality vl.
  rewrite !proj_frame.
  rewrite proj_conj.
  apply _guard_tc_environ; auto.
Qed.

Lemma semax_conseq {CS: compspecs} {Espec: OracleKind}:
 forall Delta P' (R': ret_assert) P c (R: ret_assert) ,
   (forall rho,  seplog.derives (!!(typecheck_environ Delta rho) && (allp_fun_id Delta rho && P rho))
                   (fupd (P' rho)) ) ->
   (forall rho,  seplog.derives (!!(typecheck_environ Delta rho) && (allp_fun_id Delta rho && RA_normal R' rho))
                   (fupd (RA_normal R rho))) ->
   (forall rho, seplog.derives (!! (typecheck_environ Delta rho) && (allp_fun_id Delta rho && RA_break R' rho))
                   (fupd (RA_break R rho))) ->
   (forall rho, seplog.derives (!! (typecheck_environ Delta rho) && (allp_fun_id Delta rho && RA_continue R' rho))
                   (fupd (RA_continue R rho))) ->
   (forall vl rho, seplog.derives (!! (typecheck_environ Delta rho) && (allp_fun_id Delta rho && RA_return R' vl rho))
                   (RA_return R vl rho)) ->
   semax Espec Delta P' c R' ->  semax Espec Delta P c R.
Proof.
  intros.
  assert (semax' Espec Delta P' c R' |-- semax' Espec Delta P c R);
    [clear H4 | exact (fun n => H5 n (H4 n))].
  rewrite semax_fold_unfold.
  apply allp_derives; intros gx.
  apply allp_derives; intros Delta'.
  apply allp_derives; intros CS'.
  apply prop_imp_derives; intros [? _].
  apply imp_derives; auto.
  apply allp_derives; intros k.
  apply allp_derives; intros F.
  apply allp_derives; intros f.
  apply imp_derives; [apply andp_derives; auto |]. 
  + erewrite (rguard_allp_fun_id _ _ _ _ _ R') by eauto.
    erewrite (rguard_tc_environ _ _ _ _ _ (conj_ret_assert R' _)) by eauto.
    rewrite (rguard_fupd _ _ _ _ R).
    apply rguard_mono.
    intros.
    rewrite proj_frame, proj_conj, proj_conj.
    destruct rk; simpl;
         [rename H0 into Hx; pose (ek:=RA_normal)
         | rename H1 into Hx; pose (ek:=RA_break)
         | rename H2 into Hx ; pose (ek:=RA_continue)
         | rewrite (sepcon_comm _ (F rho)); apply sepcon_derives, H3; auto]; clear H3.
all: rewrite <- sepcon_andp_prop1; rewrite sepcon_comm; apply sepcon_derives, derives_refl.
all:    specialize (Hx rho); inv Hx; simpl in *;
    apply derives_trans with (!! (vl = None) && 
       (!! typecheck_environ Delta rho &&
        (allp_fun_id Delta rho && ek R' rho))); subst ek;
     [  intros ? [? [? [? ?]]];  split3; auto; split; auto | ];
    apply prop_andp_left; intro Hvl;
    rewrite (prop_true_andp _ _ Hvl); auto.
  + erewrite (guard_allp_fun_id _ _ _ _ _ P) by eauto.
    erewrite (guard_tc_environ _ _ _ _ _ (fun rho => allp_fun_id Delta rho && P rho)) by eauto.
    rewrite (guard_fupd _ _ _ _ P').
    apply guard_mono.
    intros.
    apply sepcon_derives; auto.
    specialize (H rho); inv H; auto.
Qed.

(* Part 2: Deriving simpler and older version of consequence rules from semax_conseq. *)
Lemma semax'_post_fupd:
 forall {CS: compspecs} {Espec: OracleKind} (R': ret_assert) Delta (R: ret_assert) P c,
   (forall ek vl rho, ek <> EK_return -> !!(typecheck_environ Delta rho) && 
                proj_ret_assert R' ek vl rho 
         |-- fupd (proj_ret_assert R ek vl rho)) ->
   (forall vl rho,  !!(typecheck_environ Delta rho) && 
                RA_return R' vl rho 
         |-- RA_return R vl rho) ->
   semax' Espec Delta P c R' |-- semax' Espec Delta P c R.
Proof.
intros.
rewrite semax_fold_unfold.
apply allp_derives; intro psi.
apply allp_derives; intro Delta'.
apply allp_derives; intro CS'.
apply prop_imp_derives; intros [TS HGG].
apply imp_derives; auto.
apply allp_derives; intro k.
apply allp_derives; intro F.
apply allp_derives; intro f.
apply imp_derives; auto.
apply andp_derives; auto.
erewrite (rguard_tc_environ _ _ _ _ _ R') by eauto.
rewrite rguard_fupd.
apply rguard_mono; intros.
destruct (eq_dec rk EK_return); subst.
- destruct R, R'; simpl in *.
  rewrite andp_comm; apply sepcon_derives; auto.
- destruct R, R'; simpl in *.
  specialize (H rk vl rho); destruct rk; try contradiction; simpl in *;
    apply prop_andp_left; intros Hvl; rewrite (prop_true_andp _ _ Hvl) in H;
    rewrite prop_true_andp by auto; rewrite andp_comm; apply sepcon_derives; auto;
    eapply derives_trans, fupd.fupd_mono, andp_left2; try apply H; auto.
Qed.

Lemma semax'_post:
 forall {CS: compspecs} {Espec: OracleKind} (R': ret_assert) Delta (R: ret_assert) P c,
   (forall ek vl rho,  !!(typecheck_environ Delta rho) && 
                proj_ret_assert R' ek vl rho 
         |-- proj_ret_assert R ek vl rho) ->
   semax' Espec Delta P c R' |-- semax' Espec Delta P c R.
Proof.
intros.
apply semax'_post_fupd.
intros; eapply derives_trans, fupd.fupd_intro; auto.
intros; apply (H EK_return).
Qed.

Lemma semax'_pre_fupd:
 forall {CS: compspecs} {Espec: OracleKind} P' Delta R P c,
  (forall rho, typecheck_environ Delta rho ->   P rho |-- fupd (P' rho))
   ->   semax' Espec Delta P' c R |-- semax' Espec Delta P c R.
Proof.
intros.
repeat rewrite semax_fold_unfold.
apply allp_derives; intro psi.
apply allp_derives; intro Delta'.
apply allp_derives; intro CS'.
apply prop_imp_derives; intros [TS HGG].
apply imp_derives; auto.
apply allp_derives; intro k.
apply allp_derives; intro F.
apply allp_derives; intro f.
apply imp_derives; auto.
erewrite (guard_tc_environ _ _ _ _ _ (fun rho => P rho)) by eauto.
rewrite (guard_fupd _ _ _ _ P').
apply guard_mono.
intros.
apply sepcon_derives; auto.
apply prop_andp_left; auto.
Qed.

Lemma semax'_pre:
 forall {CS: compspecs} {Espec: OracleKind} P' Delta R P c,
  (forall rho, typecheck_environ Delta rho ->   P rho |-- P' rho)
   ->   semax' Espec Delta P' c R |-- semax' Espec Delta P c R.
Proof.
intros; apply semax'_pre_fupd.
intros; eapply derives_trans, fupd.fupd_intro; auto.
Qed.

Lemma semax'_pre_post_fupd:
 forall
      {CS: compspecs} {Espec: OracleKind} P' (R': ret_assert) Delta (R: ret_assert) P c,
   (forall rho, typecheck_environ Delta rho ->   P rho |-- fupd (P' rho)) ->
   (forall ek vl rho, ek <> EK_return -> !!(typecheck_environ Delta rho) 
                       &&  proj_ret_assert R ek vl rho 
                    |-- fupd (proj_ret_assert R' ek vl rho)) ->
   (forall vl rho, !!(typecheck_environ Delta rho) 
                       &&  RA_return R vl rho 
                    |-- RA_return R' vl rho) ->
   semax' Espec Delta P' c R |-- semax' Espec Delta P c R'.
Proof.
intros.
eapply derives_trans.
apply semax'_pre_fupd; eauto.
apply semax'_post_fupd; auto.
Qed.

Lemma semax'_pre_post:
 forall
      {CS: compspecs} {Espec: OracleKind} P' (R': ret_assert) Delta (R: ret_assert) P c,
   (forall rho, typecheck_environ Delta rho ->   P rho |-- P' rho) ->
   (forall ek vl rho, !!(typecheck_environ Delta rho) 
                       &&  proj_ret_assert R ek vl rho 
                    |-- proj_ret_assert R' ek vl rho) ->
   semax' Espec Delta P' c R |-- semax' Espec Delta P c R'.
Proof.
intros.
eapply derives_trans.
apply semax'_pre; eauto.
apply semax'_post; auto.
Qed.

Lemma semax_post'_fupd {CS: compspecs} {Espec: OracleKind}:
 forall (R': ret_assert) Delta (R: ret_assert) P c,
   (forall ek vl rho, ek <> EK_return -> !!(typecheck_environ Delta rho) 
                      &&  proj_ret_assert R' ek vl rho
                        |-- fupd (proj_ret_assert R ek vl rho)) ->
   (forall vl rho,  !!(typecheck_environ Delta rho) 
                      &&  RA_return R' vl rho
                        |-- RA_return R vl rho) ->
   semax Espec Delta P c R' ->  semax Espec Delta P c R.
Proof.
unfold semax.
intros.
specialize (H1 n). revert n H1.
apply semax'_post_fupd; auto.
Qed.

Lemma semax_post_fupd {CS: compspecs} {Espec: OracleKind}:
 forall (R': ret_assert) Delta (R: ret_assert) P c,
   (forall rho,  !!(typecheck_environ Delta rho) 
                      &&  RA_normal R' rho |-- fupd (RA_normal R rho)) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_break R' rho |-- fupd (RA_break R rho)) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_continue R' rho |-- fupd (RA_continue R rho)) ->
   (forall vl rho, !! (typecheck_environ Delta rho) 
                      && RA_return R' vl rho |-- RA_return R vl rho) ->
   semax Espec Delta P c R' ->  semax Espec Delta P c R.
Proof.
unfold semax.
intros.
specialize (H3 n). revert n H3.
apply semax'_post_fupd; auto.
intros; destruct ek; try contradiction; simpl;
repeat (apply normalize.derives_extract_prop; intro); rewrite ?prop_true_andp by auto;
specialize (H rho); specialize (H0 rho); specialize (H1 rho); specialize (H2 vl rho);
rewrite ?prop_true_andp in H, H0, H1, H2 by auto; auto.
Qed.

Lemma semax_post' {CS: compspecs} {Espec: OracleKind}:
 forall (R': ret_assert) Delta (R: ret_assert) P c,
   (forall ek vl rho,  !!(typecheck_environ Delta rho) 
                      &&  proj_ret_assert R' ek vl rho
                        |-- proj_ret_assert R ek vl rho) ->
   semax Espec Delta P c R' ->  semax Espec Delta P c R.
Proof.
unfold semax.
intros.
specialize (H0 n). revert n H0.
apply semax'_post.
auto.
Qed.

Lemma semax_post {CS: compspecs} {Espec: OracleKind}:
 forall (R': ret_assert) Delta (R: ret_assert) P c,
   (forall rho,  !!(typecheck_environ Delta rho) 
                      &&  RA_normal R' rho |-- RA_normal R rho) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_break R' rho |-- RA_break R rho) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_continue R' rho |-- RA_continue R rho) ->
   (forall vl rho, !! (typecheck_environ Delta rho) 
                      && RA_return R' vl rho |-- RA_return R vl rho) ->
   semax Espec Delta P c R' ->  semax Espec Delta P c R.
Proof.
unfold semax.
intros.
specialize (H3 n). revert n H3.
apply semax'_post.
intros; destruct ek; simpl;
repeat (apply normalize.derives_extract_prop; intro); rewrite ?prop_true_andp by auto;
specialize (H rho); specialize (H0 rho); specialize (H1 rho); specialize (H2 vl rho);
rewrite prop_true_andp in H, H0, H1, H2 by auto; auto.
Qed.

Lemma semax_pre_fupd {CS: compspecs} {Espec: OracleKind} :
 forall P' Delta P c R,
   (forall rho,  !!(typecheck_environ Delta rho) &&  P rho |-- fupd (P' rho) )%pred ->
     semax Espec Delta P' c R  -> semax Espec Delta P c R.
Proof.
unfold semax.
intros.
specialize (H0 n).
revert n H0.
apply semax'_pre_fupd.
intros ????. apply (H rho a); auto. split; auto.
Qed.

Lemma semax_pre {CS: compspecs} {Espec: OracleKind} :
 forall P' Delta P c R,
   (forall rho,  !!(typecheck_environ Delta rho) &&  P rho |-- P' rho )%pred ->
     semax Espec Delta P' c R  -> semax Espec Delta P c R.
Proof.
unfold semax.
intros.
specialize (H0 n).
revert n H0.
apply semax'_pre.
intros ????. apply (H rho a). split; auto.
Qed.

Lemma semax_pre_post_fupd {CS: compspecs} {Espec: OracleKind}:
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
   (forall rho,  !!(typecheck_environ Delta rho) &&  P rho |-- fupd (P' rho) )%pred ->
   (forall rho,  !!(typecheck_environ Delta rho) 
                      &&  RA_normal R' rho |-- fupd (RA_normal R rho)) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_break R' rho |-- fupd (RA_break R rho)) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_continue R' rho |-- fupd (RA_continue R rho)) ->
   (forall vl rho, !! (typecheck_environ Delta rho) 
                      && RA_return R' vl rho |-- RA_return R vl rho) ->
   semax Espec Delta P' c R' ->  semax Espec Delta P c R.
Proof.
intros.
eapply semax_pre_fupd; eauto.
eapply semax_post_fupd; eauto.
Qed.

Lemma semax_pre_post {CS: compspecs} {Espec: OracleKind}:
 forall P' (R': ret_assert) Delta P c (R: ret_assert) ,
   (forall rho,  !!(typecheck_environ Delta rho) &&  P rho |-- P' rho )%pred ->
   (forall rho,  !!(typecheck_environ Delta rho) 
                      &&  RA_normal R' rho |-- RA_normal R rho) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_break R' rho |-- RA_break R rho) ->
   (forall rho, !! (typecheck_environ Delta rho) 
                      && RA_continue R' rho |-- RA_continue R rho) ->
   (forall vl rho, !! (typecheck_environ Delta rho) 
                      && RA_return R' vl rho |-- RA_return R vl rho) ->
   semax Espec Delta P' c R' ->  semax Espec Delta P c R.
Proof.
intros.
eapply semax_pre; eauto.
eapply semax_post; eauto.
Qed.

Lemma semax_fupd_elim {CS: compspecs} {Espec: OracleKind}:
 forall Delta P c R,
  semax Espec Delta P c R -> semax Espec Delta (fun rho => fupd (P rho)) c R.
Proof.
intros ????; apply semax_pre_fupd.
intro; apply prop_andp_left; auto.
Qed.

Lemma semax_skip {CS: compspecs} {Espec: OracleKind}:
   forall Delta P, semax Espec Delta P Sskip (normal_ret_assert P).
Proof.
intros.
apply derives_skip.
intros.
simpl.
rewrite prop_true_andp by auto.
auto.
Qed.

(*Taken from floyd.SeparationLogicFacts.v*)
Lemma semax_extract_prop:
  forall {CS: compspecs} {Espec: OracleKind},
  forall Delta (PP: Prop) (P:assert) c (Q:ret_assert),
           (PP -> @semax CS Espec Delta P c Q) ->
           @semax CS Espec Delta (fun rho => !!PP && P rho) c Q.
Proof.
  intros.
  eapply semax_pre with (fun rho => EX H: PP, P rho).
  + intros. apply andp_left2.
    apply normalize.derives_extract_prop; intros.
    apply (exp_right H0), derives_refl.
  + apply extract_exists_pre, H.
Qed.

Lemma semax_adapt_frame {cs Espec} Delta c (P P': assert) (Q Q' : ret_assert)
   (H: forall rho,  derives (!!(typecheck_environ Delta rho) && (allp_fun_id Delta rho && P rho))
                   (EX F: assert, (!!(closed_wrt_modvars c F) && fupd (P' rho * F rho) &&
                         !!(forall rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_normal (frame_ret_assert Q' F) rho |-- fupd (RA_normal Q rho)) &&
                         !!(forall rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_break (frame_ret_assert Q' F) rho |-- fupd (RA_break Q rho)) &&
                         !!(forall rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_continue (frame_ret_assert Q' F) rho |-- fupd (RA_continue Q rho)) &&
                         !!(forall vl rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_return (frame_ret_assert Q' F) vl rho |-- RA_return Q vl rho))))
   (SEM: @semax cs Espec Delta P' c Q'):
   @semax cs Espec Delta P c Q.
Proof. intros.
apply (semax_conseq Delta (fun rho => EX F: assert, !!(closed_wrt_modvars c F) && (fupd (sepcon (P' rho) (F rho)) &&
                         (!!(forall rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_normal (frame_ret_assert Q' F) rho |-- fupd (RA_normal Q rho)) &&
                         (!!(forall rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_break (frame_ret_assert Q' F) rho |-- fupd (RA_break Q rho)) &&
                         (!!(forall rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_continue (frame_ret_assert Q' F) rho |-- fupd (RA_continue Q rho)) &&
                         (!!(forall vl rho, (local (tc_environ Delta) rho) && ((allp_fun_id Delta rho)) && RA_return (frame_ret_assert Q' F) vl rho |-- RA_return Q vl rho)))))))
   Q).
+ intros. eapply seplog.derives_trans. constructor. apply H. clear H.
  eapply seplog.derives_trans. 2: { constructor. apply fupd.fupd_intro. }
  constructor. apply exp_derives; intros F. 
  rewrite <- ! andp_assoc; trivial.
+ clear H. intros. constructor. eapply derives_trans, fupd.fupd_intro.
  do 2 apply andp_left2; trivial.
+ clear H. intros. constructor. eapply derives_trans, fupd.fupd_intro.
  do 2 apply andp_left2; trivial.
+ clear H. intros. constructor. eapply derives_trans, fupd.fupd_intro.
  do 2 apply andp_left2; trivial.
+ clear H. intros. constructor.
  do 2 apply andp_left2; trivial.
+ apply extract_exists_pre. intros F. clear H.
  apply semax_extract_prop. intros.
  eapply semax_pre_fupd. 2:{ do 4 (apply semax_extract_prop; intros). 
    eapply semax_conseq. 6:{ apply semax_frame. exact H. apply SEM. }
    2: {
    intros; constructor.
    revert rho. exact H0. }
    2: {
    intros; constructor.
    revert rho. exact H1. }
    2: {
    intros; constructor.
    revert rho. exact H2. }
    2: {
    intros; constructor.
    revert rho. revert vl. exact H3. }

   intros; constructor. eapply derives_trans; [ | apply fupd.fupd_intro].
   apply andp_left2. apply andp_left2. apply derives_refl. }
  intros. unfold local, liftx, lift1, tc_environ; simpl. apply andp_left2.
  rewrite (andp_comm (fupd (P' rho * F rho))). eapply derives_trans, fupd.fupd_andp_prop.
  rewrite andp_assoc; apply andp_derives; [apply prop_derives; intros; rewrite <- andp_assoc; auto|].
  eapply derives_trans, fupd.fupd_andp_prop.
  rewrite andp_assoc; apply andp_derives; [apply prop_derives; intros; rewrite <- andp_assoc; auto|].
  eapply derives_trans, fupd.fupd_andp_prop.
  rewrite andp_assoc; apply andp_derives; [apply prop_derives; intros; rewrite <- andp_assoc; auto|].
  eapply derives_trans, fupd.fupd_andp_prop.
  apply andp_derives; [apply prop_derives; intros; rewrite <- andp_assoc; auto|].
  auto.
Qed.

Lemma semax_adapt_frame' {cs Espec} Delta c (P P': assert) (Q Q' : ret_assert)
   (H: forall rho,  !!(typecheck_environ Delta rho) && (allp_fun_id Delta rho && P rho)
                   |-- EX F: assert, (!!(closed_wrt_modvars c F) && fupd (P' rho * F rho) &&
                        !!(forall rho, RA_normal (frame_ret_assert Q' F) rho |-- fupd (RA_normal Q rho)) &&
                        !!(forall rho, RA_break (frame_ret_assert Q' F) rho |-- fupd (RA_break Q rho)) &&
                        !!(forall rho, RA_continue (frame_ret_assert Q' F) rho |-- fupd (RA_continue Q rho)) &&
                        !!(forall vl rho, RA_return (frame_ret_assert Q' F) vl rho |-- RA_return Q vl rho)))
   (SEM: @semax cs Espec Delta P' c Q'):
   @semax cs Espec Delta P c Q.
Proof.
  intros. eapply semax_adapt_frame. 2: apply SEM.
  intros. eapply derives_trans. apply H. 
  clear. apply exp_derives. intros FR.
  rewrite ! andp_assoc.
  apply andp_derives; trivial.
  apply andp_derives; trivial.
  apply andp_derives. 
  { apply prop_derives; intros. eapply derives_trans. 2: apply H. apply andp_left2; trivial. }
  apply andp_derives. 
  { apply prop_derives; intros. eapply derives_trans. 2: apply H. apply andp_left2; trivial. }
  apply andp_derives. 
  { apply prop_derives; intros. eapply derives_trans. 2: apply H. apply andp_left2; trivial. }
  { apply prop_derives; intros. eapply derives_trans. 2: apply H. apply andp_left2; trivial. }
Qed.

Lemma semax_adapt {cs Espec} Delta c (P P': assert) (Q Q' : ret_assert)
   (H: forall rho,  !!(typecheck_environ Delta rho) && (allp_fun_id Delta rho && P rho)
                   |-- (fupd (P' rho) &&
                        !!(forall rho, RA_normal Q' rho |-- fupd (RA_normal Q rho)) &&
                        !!(forall rho, RA_break Q' rho |-- fupd (RA_break Q rho)) &&
                        !!(forall rho, RA_continue Q' rho |-- fupd (RA_continue Q rho)) &&
                        !!(forall vl rho, RA_return Q' vl rho |-- RA_return Q vl rho)))
   (SEM: @semax cs Espec Delta P' c Q'):
   @semax cs Espec Delta P c Q.
Proof.
  intros. eapply semax_adapt_frame'; eauto. intros. exists (fun rho => emp).
  apply H in H0; clear H.
  destruct H0 as [[[[HP' NORM] BREAK] CONT] RET]. simpl in NORM, BREAK, CONT, RET.
  rewrite sepcon_emp. repeat split; auto; simpl; intros.
  + eapply derives_trans; [ | apply NORM]; clear.
    destruct Q'; simpl; rewrite sepcon_emp; trivial.
  + eapply derives_trans; [ | apply BREAK]; clear.
    destruct Q'; simpl; rewrite sepcon_emp; trivial.
  + eapply derives_trans; [ | apply CONT]; clear.
    destruct Q'; simpl; rewrite sepcon_emp; trivial.
  + eapply derives_trans; [ | apply RET]; clear.
    destruct Q'; simpl; rewrite sepcon_emp; trivial.
Qed.
