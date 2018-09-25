Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import sha.general_lemmas.

Lemma Zgt_is_gt_bool_f: forall n m : Z, n <= m <-> (n >? m) = false.
Proof. intros. specialize (Zgt_cases n m); intros.
  remember ((n >? m)). destruct b.
  + split; intros. omega. discriminate.
  + split; intros; trivial.
Qed.

Lemma da_emp_isptrornull sh t v p :
   da_emp sh t v p = (!!is_pointer_or_null p) &&  da_emp sh t v p.
 Proof. unfold da_emp; apply pred_ext.
  + apply orp_left.
    - apply derives_extract_prop; intros; subst; simpl. entailer. apply orp_right1. auto.
    - rewrite data_at_isptr with (p0:=p) at 1. normalize.
      destruct p; simpl in *; try contradiction. entailer. apply orp_right2. entailer.
  + entailer.
Qed.

Lemma da_emp_null sh t v p: p=nullval -> da_emp sh t v p = emp.
Proof. intros; subst. unfold da_emp. rewrite data_at_isptr. unfold isptr. simpl.
  apply pred_ext.
  + normalize. apply orp_left. auto. normalize.
  + simpl. apply orp_right1. entailer.
Qed.
Lemma da_emp_ptr sh t v b i: da_emp sh t v (Vptr b i) = !! (sizeof t > 0) && data_at sh t v (Vptr b i).
Proof. intros; unfold da_emp, nullval; simpl.
  apply pred_ext.
  + apply orp_left; normalize. inv H.
  + apply orp_right2. auto.
Qed.

Lemma false_zgt z a: false = (z >? a) -> z<=a. 
Proof. unfold Z.gtb.
  remember (z ?= a). destruct c. symmetry in Heqc; apply Z.compare_eq in Heqc. subst; intros. omega.
  symmetry in Heqc. destruct (Z.compare_lt_iff z a); intros. apply H in Heqc. omega.
  discriminate.
Qed. 
Lemma false_zge z a: false = (z >=? a) -> z<=a. 
Proof. unfold Z.geb.
  remember (z ?= a). destruct c; intros; try discriminate.
  symmetry in Heqc. destruct (Z.compare_lt_iff z a); intros. apply H0 in Heqc. omega.
Qed.

(*
Lemma da_emp_isptrornull sh t v p :
   da_emp sh t v p = (!!is_pointer_or_null p) &&  da_emp sh t v p.
 Proof. unfold da_emp; apply pred_ext.
  + apply orp_left.
    - apply derives_extract_prop; intros; subst; simpl. entailer. apply orp_right1. trivial.
    - rewrite data_at_isptr with (p0:=p) at 1. normalize.
      destruct p; simpl in *; try contradiction. entailer. apply orp_right2. trivial.
  + entailer.
Qed.

Lemma da_emp_null sh t v p: p=nullval -> da_emp sh t v p = emp.
Proof. intros; subst. unfold da_emp. rewrite data_at_isptr.
  apply pred_ext.
  + normalize. rewrite orp_FF. trivial.
  + simpl. apply orp_right1. entailer.
Qed.
Lemma da_emp_ptr sh t v b i: da_emp sh t v (Vptr b i) = data_at sh t v (Vptr b i).
Proof. intros; unfold da_emp, nullval; simpl.
  apply pred_ext.
  + apply orp_left; trivial. normalize. inv H.
  + apply orp_right2. trivial.
Qed.
*)

Lemma Tarray_0_emp sh v c: data_at sh (Tarray tuchar 0 noattr) v c |--  emp.
  unfold data_at. unfold field_at, data_at_rec, at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. entailer.
Qed.

Lemma Tarray_0_emp' sh c: field_compatible (Tarray tuchar 0 noattr) nil c ->
  emp |-- data_at sh (Tarray tuchar 0 noattr) nil c.
Proof. intros.
  unfold data_at. unfold field_at, data_at_rec, at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. simpl.
  entailer.
Qed.

Lemma data_at_weak_valid_ptr: forall (sh : Share.t) (t : type) (v : reptype t) (p : val),
       sepalg.nonidentity sh ->
       (*sizeof cenv_cs t >= 0 -> *) sizeof t > 0 -> data_at sh t v p |-- weak_valid_pointer p.
Proof. intros.
eapply derives_trans. 2: apply valid_pointer_weak. apply data_at_valid_ptr; trivial. Qed.

Lemma sublist_app_exact1:
  forall X (A B: list X), sublist 0 (Zlength A) (A ++ B) = A.
Proof.
  intros.
  pose proof (Zlength_nonneg A).
  rewrite sublist_app1; try omega.
  rewrite sublist_same; auto.
Qed.

Lemma sublist_app_exact2:
  forall X (A B: list X), sublist (Zlength A) (Zlength A + Zlength B) (A ++ B) = B.
Proof.
  intros.
  pose proof (Zlength_nonneg A).
  pose proof (Zlength_nonneg B).
  rewrite sublist_app2; try omega.
  rewrite sublist_same; auto; omega.
Qed.

Lemma data_at_complete_split:
  forall (A B: list val) lengthA lengthB AB length p offset sh,
    field_compatible (tarray tuchar (Zlength A + Zlength B)) [] p ->
    lengthA = Zlength A ->
    lengthB = Zlength B ->
    length = lengthA + lengthB ->
    offset = lengthA ->
    AB = A ++ B ->
    (data_at sh (tarray tuchar length) (AB) p) = (data_at sh (tarray tuchar lengthA) A p) * (data_at sh (tarray tuchar lengthB) B (offset_val offset p)).
Proof.
  intros until sh.
  intros Hfield.
  intros; subst.
  pose proof (Zlength_nonneg A).
  pose proof (Zlength_nonneg B).
  assert (Hisptr: isptr p) by (destruct Hfield; assumption).
  destruct p; try solve [inversion Hisptr]; clear Hisptr.
  unfold tarray.
  rewrite split2_data_at_Tarray_tuchar with (n1:=Zlength A); [|split; omega|rewrite Zlength_app; reflexivity].
  rewrite sublist_app_exact1, sublist_app_exact2.
  replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by omega.
  replace (field_address0 (Tarray tuchar (Zlength A + Zlength B) noattr) [ArraySubsc (Zlength A)] (Vptr b i)) with (Vptr b (Ptrofs.add i (Ptrofs.repr (Zlength A)))).
  reflexivity.
  rewrite field_address0_offset.
  simpl. replace (0 + 1 * Zlength A) with (Zlength A) by omega. reflexivity.
  destruct Hfield as [Hfield1 [Hfield2 [Hfield3 [Hfield4 Hfield5]]]].
  unfold field_compatible0; repeat split; try assumption; auto; omega.
Qed.
