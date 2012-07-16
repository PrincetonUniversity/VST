Require Export veric.base.
Require Export veric.Address.
Require Import msl.rmaps.
Require Import msl.rmaps_lemmas.
Require Import veric.compcert_rmaps.
Require Import veric.slice.
Require Import veric.res_predicates.
Require Import veric.expr.
Require Import veric.seplog.
Require Import veric.Clight_lemmas.
Require Import veric.normalize.

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


Definition Dbool (e: Clight.expr) : assert := 
  fun rho =>  Ex b: bool, !! (bool_of_valf (eval_expr rho e) = Some b).

Lemma assert_truth:  forall {A} `{ageable A} (P:  Prop), P -> forall (Q: pred A), Q |-- (!! P) && Q.
Proof.
intros.
intros st ?.
split; auto.
Qed. 

Lemma assert_Val_is_true:
 forall {A} `{ageable A} (P: pred A), P |-- !!(Val.is_true Vtrue) && P.
Proof.  intros. apply assert_truth. apply Val_is_true_Vtrue. Qed.

Hint Resolve Val_is_true_Vtrue  @assert_Val_is_true.

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

(* Admitted: move this to msl? *)
Lemma prop_imp_i {A}{agA: ageable A}:
  forall (P: Prop) Q w, (P -> app_pred Q w) -> (!!P --> Q) w.
Proof.
 intros. intros w' ? ?. apply H in H1. eapply pred_nec_hereditary; eauto.
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

Lemma corable_andp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall P Q, corable P -> corable Q -> corable (P && Q).
Proof.
 unfold corable; intros.
 apply prop_ext; split; intros [? ?]; split; congruence.
Qed.
Lemma corable_orp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall P Q, corable P -> corable Q -> corable (P || Q).
Proof.
 unfold corable; intros.
 apply prop_ext; split; (intros [?|?]; [left|right]; congruence).
Qed.
Lemma corable_allp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall {B: Type} (P:  B -> pred A) , 
      (forall b, corable (P b)) -> corable (allp P).
Proof.
 unfold corable, allp; intros.
 apply prop_ext; split; simpl; intros.
 rewrite <- H; auto. rewrite H; auto.
Qed.
Lemma corable_exp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall {B: Type} (P:  B -> pred A) , 
      (forall b, corable (P b)) -> corable (exp P).
Proof.
 unfold corable, exp; intros.
 apply prop_ext; split; simpl; intros;  destruct H0 as [b ?]; exists b.
 rewrite <- H; auto. rewrite H; auto.
Qed.
Lemma corable_prop{A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall P, corable (prop P).
Proof.
 unfold corable, prop; intros.
 apply prop_ext; split; simpl; intros; auto.
Qed.


Lemma corable_imp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{CA: Canc_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall P Q, corable P -> corable Q -> corable (P --> Q).
Proof.
 unfold corable; intros.
 apply prop_ext; split; intro.
 intros w' ? ?.
 destruct (nec_join (core_unit w) H2) as [y' [z' [? [? ?]]]]. 
 change (@join A JA w' y' z') in H4.
 assert (y'=z'). eapply necR_linear'; eauto. apply join_level in H4; destruct H4; congruence.
 subst z'; clear H6.
 assert (core y' = w').
 rewrite <- (join_core H4).
 apply unit_identity in H4.
 symmetry; apply unit_core. apply identity_unit_equiv in H4; auto.
 subst w'.
 specialize (H1 _ H5).
 rewrite <- H0. apply H1. rewrite H; auto.
 intros w' ? ?.
 destruct (nec_join2 (core_unit w) H2) as [y' [z' [? [? ?]]]]. 
 change (@join A JA y' z' w') in H4.
 assert (app_pred emp (core w)).
 do 3 red. apply core_identity.
 eapply pred_nec_hereditary in H7; try apply H5.
 do 3 red in H7.
 assert (y' = core y'). apply unit_core. apply identity_unit_equiv; auto.
 pose proof (join_core H4).
 rewrite H8 in H5; rewrite H9 in H5.
 rewrite H0.
 eapply H1; try apply H5. rewrite <- H; auto.
Qed.

Hint Resolve @corable_andp @corable_orp @corable_allp @corable_exp 
                    @corable_imp @corable_prop.

Lemma corable_funassert:
  forall G rho, corable (funassert G rho).
Proof.
 intros.
 unfold funassert, func.
 apply corable_andp.
 apply corable_allp; intro.
 apply corable_allp; intro.
 apply corable_imp; auto.
 apply corable_exp; intro.
 apply corable_exp; intro.
 apply corable_andp; auto.
 destruct b0.  destruct s;  destruct p.
 apply corable_pureat.
 apply corable_allp; intro.
 apply corable_allp; intro.
 apply corable_imp; auto.
 destruct b0.  destruct s;  destruct p.
 apply corable_pureat.
Qed.

Hint Resolve corable_funassert.


Lemma corable_jam: forall {B} {S': B -> Prop} (S: forall l, {S' l}+{~ S' l}) P Q, 
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


