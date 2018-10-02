Require Export VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates.
Require Import compcert.cfrontend.Ctypes.
Require Import VST.veric.mpred.
Require Import VST.veric.seplog.

Require Import VST.msl.normalize.

Local Open Scope pred.

Lemma mapsto_core_load: forall ch v sh loc m, 
  (address_mapsto ch v sh loc * TT)%pred m -> core_load ch loc v m.
Proof.
unfold address_mapsto, core_load.
intros until m; intros H.
destruct H as [phi0 [phi1 [Hjoin [[bl [[[Hlen [Hdec Halign]] H] _]] ?]]]].
unfold allp, jam in *.
exists bl.
repeat split; auto.
hnf. intro b; specialize (H b).
hnf in H|-*.
if_tac.
hnf in H|-*.
destruct H as [p ?].
apply (resource_at_join _ _ _ b) in Hjoin.
rewrite H in Hjoin; clear H.
repeat rewrite preds_fmap_NoneP in Hjoin.
inv Hjoin.
do 3 econstructor; try reflexivity.
do 2 econstructor; reflexivity.
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
induction bl; destruct bl'; intros; try solve [specialize (H5 O); inv H5|auto].
f_equal.
specialize (H5 O); inv H5; auto.
apply IHbl.
intro i.
specialize (H5 (S i)).
auto.
intro i.
destruct loc as (b, ofs).
specialize (H (b, ofs + Z_of_nat i)).
specialize (H0 (b, ofs + Z_of_nat i)).
hnf in H, H0. if_tac in H.
* (* adr_range *)
destruct H as [sh [rsh H]].
destruct H0 as [sh' [rsh' H0]].
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
* (* ~adr_range *)
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
specialize (H2 loc').
apply resource_at_join with (loc := loc') in H.
hnf in H2|-*.
if_tac; auto.
hnf in H2|-*.
destruct H2 as [sh [rsh H2]].
rewrite H2 in H.
inv H; subst; eauto.
Qed.

(*
Lenb: should be moved to tycontext or some other Clight-dependent file- but is in fact dead
Definition Dbool {CS: compspecs} (Delta: tycontext) (e: Clight.expr) : assert :=
  fun rho =>  EX b: bool, !! (bool_of_valf (eval_expr e rho) = Some b).
*)
                             
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
generalize (equal_f (rmap_fmap_comp (approx (S n)) (approx (S n)) (approx n) (approx n)) r0); intro.
unfold compose at 1 in H0.
rewrite H0.
rewrite approx_oo_approx'; auto.
rewrite approx'_oo_approx; auto.
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

Lemma corable_func_at: forall f l, corable (func_at f l).
Proof.
  intros.
  unfold func_at.
  destruct f as [fsig0 cc A P Q].
  apply corable_pureat.
Qed.

Lemma corable_func_at': forall f l, corable (func_at' f l).
Proof.
  intros.
  unfold func_at'.
  destruct f as [fsig0 cc A P Q].
  apply corable_exp; intro.
  apply corable_pureat.
Qed.

Lemma corable_func_ptr : forall f v, corable (func_ptr f v).
Proof.
  intros.
  unfold func_ptr.
  apply corable_exp; intro.
  apply corable_andp; auto.
  apply corable_func_at.
Qed.

Hint Resolve corable_func_ptr.

Lemma corable_funspecs_assert:
  forall FS rho, corable (funspecs_assert FS rho).
Proof.
 intros.
 unfold funspecs_assert.
 repeat
 first [
   apply corable_andp|
   apply corable_exp; intro|
   apply corable_allp; intro|
   apply corable_prop|
   apply corable_imp].
 + apply corable_func_at.
 + apply corable_func_at'.
Qed.

Hint Resolve corable_funspecs_assert.

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
(*Lenb: add Hint Resolve corable_jam?*)

(*
Lemma corable_fun_assert: forall v fsig cc A P Q, corable (fun_assert v fsig cc A P Q).
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
*)
Lemma prop_derives {A}{H: ageable A}:
 forall (P Q: Prop), (P -> Q) -> prop P |-- prop Q.
Proof.
intros. intros w ?; apply H0; auto.
Qed.
