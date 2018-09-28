Require Import VST.msl.log_normalize.
Require Import VST.msl.alg_seplog.
Require Import VST.veric.base.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.res_predicates. 

Require Import VST.veric.Clight_lemmas.
Require Import VST.veric.tycontext.
Require Import VST.veric.expr2.
Require Import VST.veric.expr_lemmas3.
Require Import VST.veric.binop_lemmas2.

Require Import VST.veric.address_conflict.
Require Import VST.veric.shares.
Require Import VST.veric.slice.

Require Import VST.veric.mpred.
Require Import VST.veric.Cop2.
Require Export VST.veric.mapsto_memory_block.

Local Open Scope pred.

Lemma mapsto_unsigned_signed:
 forall sign1 sign2 sh sz v i,
  mapsto sh (Tint sz sign1 noattr) v (Vint (Cop.cast_int_int sz sign1 i)) =
  mapsto sh (Tint sz sign2 noattr) v (Vint (Cop.cast_int_int sz sign2 i)).
Proof.
 intros.
 unfold mapsto.
 unfold address_mapsto, res_predicates.address_mapsto.
 simpl.
 destruct sz; auto;
 destruct sign1, sign2;
 [auto | | | auto | auto | |  | auto];
 (destruct v; [auto | auto | auto | auto | auto | ]);
 simpl Cop.cast_int_int;
 repeat rewrite (prop_true_andp (_ <= _ <= _)) by
  first [ apply (expr_lemmas3.sign_ext_range' 8 i); compute; split; congruence
          | apply (expr_lemmas3.sign_ext_range' 16 i); compute; split; congruence
          ];
 repeat rewrite (prop_true_andp (_ <= _)) by
  first [ apply (expr_lemmas3.zero_ext_range' 8 i); compute; split; congruence
          | apply (expr_lemmas3.zero_ext_range' 16 i); compute; split; congruence
          ];
 simpl;
 repeat rewrite (prop_true_andp True) by auto;
 repeat rewrite (prop_false_andp  (Vint _ = Vundef) ) by (intro; discriminate);
 cbv beta;
 repeat first [rewrite @FF_orp | rewrite @orp_FF].
*
 f_equal. if_tac; clear H.
 2:{
   f_equal.
   apply pred_ext; intros ?; hnf; simpl;
   intros; (split; [| tauto]).
   + intros _.
     simpl.
     destruct (zero_ext_range' 8 i); [split; cbv; intros; congruence |].
     exact H1.
   + intros _.
     simpl.
     destruct (sign_ext_range' 8 i); [split; cbv; intros; congruence |].
     exact (conj H0 H1).
 }
 f_equal. f_equal; extensionality bl.
 f_equal. f_equal. f_equal.
 simpl;  apply prop_ext; intuition.
 destruct bl; inv H0. destruct bl; inv H.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 unfold Memdata.decode_int in *.
 rewrite rev_if_be_1 in *. simpl in *.
 apply Vint_inj in H1. f_equal.
 rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)) by omega.
  rewrite <- (Int.zero_ext_sign_ext _ i) by omega.
 f_equal; auto.
 inv H3.
 destruct bl; inv H0. destruct bl; inv H3.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 unfold Memdata.decode_int in *.
 rewrite rev_if_be_1 in *. simpl in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)) by omega.
 rewrite <- (Int.sign_ext_zero_ext _ i) by omega.
 f_equal; auto.
*
 f_equal.
 if_tac; clear H.
 2:{
   f_equal.
   apply pred_ext; intros ?; hnf; simpl;
   intros; (split; [| tauto]).
   + intros _.
     simpl.
     destruct (sign_ext_range' 8 i); [split; cbv; intros; congruence |].
     exact (conj H0 H1).
   + intros _.
     simpl.
     destruct (zero_ext_range' 8 i); [split; cbv; intros; congruence |].
     exact H1.
 }
 f_equal; f_equal; extensionality bl.
 f_equal. f_equal. f_equal.
 simpl;  apply prop_ext; intuition.
 destruct bl; inv H0. destruct bl; inv H3.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 unfold Memdata.decode_int in *.
 rewrite rev_if_be_1 in *. simpl in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)) by omega.
 rewrite <- (Int.sign_ext_zero_ext _ i) by omega.
 f_equal; auto.
 destruct bl; inv H0. destruct bl; inv H3.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 unfold Memdata.decode_int in *.
 rewrite rev_if_be_1 in *. simpl in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)) by omega.
  rewrite <- (Int.zero_ext_sign_ext _ i) by omega.
 f_equal; auto.
*
 f_equal.
  if_tac; [| auto]; clear H.
 2:{
   f_equal.
   apply pred_ext; intros ?; hnf; simpl;
   intros; (split; [| tauto]).
   + intros _.
     simpl.
     destruct (zero_ext_range' 16 i); [split; cbv; intros; congruence |].
     exact H1.
   + intros _.
     simpl.
     destruct (sign_ext_range' 16 i); [split; cbv; intros; congruence |].
     exact (conj H0 H1).
 }
 apply equal_f. apply f_equal. apply f_equal. extensionality bl.
 apply equal_f. apply f_equal. apply equal_f. apply f_equal. apply f_equal.
 simpl;  apply prop_ext; intuition.
 destruct bl; inv H0. destruct bl; inv H3. destruct bl; inv H1.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 destruct m0; try congruence.
 unfold Memdata.decode_int in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)) by omega.
  rewrite <- (Int.zero_ext_sign_ext _ i) by omega.
 f_equal; auto.
 destruct bl; inv H0. destruct bl; inv H3. destruct bl; inv H1.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 destruct m0; try congruence.
 unfold Memdata.decode_int in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)) by omega.
 rewrite <- (Int.sign_ext_zero_ext _ i) by omega.
 f_equal; auto.
*
 f_equal.
  if_tac; [| auto]; clear H.
 2:{
   f_equal.
   apply pred_ext; intros ?; hnf; simpl;
   intros; (split; [| tauto]).
   + intros _.
     simpl.
     destruct (sign_ext_range' 16 i); [split; cbv; intros; congruence |].
     exact (conj H0 H1).
   + intros _.
     simpl.
     destruct (zero_ext_range' 16 i); [split; cbv; intros; congruence |].
     exact H1.
 }
 apply equal_f. apply f_equal. apply f_equal. extensionality bl.
 apply equal_f. apply f_equal. apply equal_f. apply f_equal. apply f_equal.
 simpl;  apply prop_ext; intuition.
 destruct bl; inv H0. destruct bl; inv H3. destruct bl; inv H1.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 destruct m0; try congruence.
 unfold Memdata.decode_int in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)) by omega.
 rewrite <- (Int.sign_ext_zero_ext _ i) by omega.
 f_equal; auto.
 destruct bl; inv H0. destruct bl; inv H3. destruct bl; inv H1.
 unfold Memdata.decode_val in *. simpl in *.
 destruct m; try congruence.
 destruct m0; try congruence.
 unfold Memdata.decode_int in *.
 apply Vint_inj in H. f_equal.
 rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)) by omega.
  rewrite <- (Int.zero_ext_sign_ext _ i) by omega.
 f_equal; auto.
Qed.

Require Import compcert.exportclight.Clightdefs.

Lemma mapsto_tuint_tint:
  forall sh, mapsto sh tuint = mapsto sh tint.
Proof.
intros. apply mapsto_tuint_tint.
Qed.

Lemma tc_val_pointer_nullval:
 forall t, tc_val (tptr t) nullval.
Proof.
 intros. apply tc_val_pointer_nullval.
Qed.
Hint Resolve tc_val_pointer_nullval.


Lemma mapsto_null_mapsto_pointer:
  forall t sh v,
   Archi.ptr64 = false -> 
             mapsto sh tint v nullval =
             mapsto sh (tptr t) v nullval.
Proof.
  intros. apply mapsto_null_mapsto_pointer; trivial.
Qed.