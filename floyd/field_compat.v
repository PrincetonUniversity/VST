Require Import VST.floyd.base2.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require VST.floyd.aggregate_pred. Import VST.floyd.aggregate_pred.aggregate_pred.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.floyd.sublist.
Require Import VST.floyd.field_at.

Lemma field_compatible_offset_zero:
  forall {cs: compspecs} t gfs p,
    field_compatible t gfs p <-> field_compatible t gfs (offset_val 0 p).
Proof.
  intros.
  unfold field_compatible.
  destruct p; simpl; try tauto.
  rewrite !ptrofs_add_repr_0_r.
  tauto.
Qed.

Lemma field_address0_offset:
  forall {cs: compspecs} t gfs p,
    field_compatible0 t gfs p ->
    field_address0 t gfs p = offset_val (nested_field_offset t gfs) p.
Proof. intros. unfold field_address0; rewrite if_true by auto; reflexivity.
Qed.

(* TODO: This has already been proved in nested_field_lemmas, where it's named field_compatible_field_address. *)
Lemma field_address_offset:
  forall {cs: compspecs} t gfs p,
    field_compatible t gfs p ->
    field_address t gfs p = offset_val (nested_field_offset t gfs) p.
Proof. intros. unfold field_address; rewrite if_true by auto; reflexivity.
Qed.

Hint Extern 2 (field_compatible0 _ (ArraySubsc _ :: _) _) =>
   (eapply field_compatible0_cons_Tarray; [reflexivity | | omega])
  : field_compatible.

Hint Extern 2 (field_compatible _ (ArraySubsc _ :: _) _) =>
   (eapply field_compatible_cons_Tarray; [reflexivity | | omega])
  : field_compatible.

Lemma field_compatible_array_smaller0:
  forall {cs: compspecs} t n n' d,
  field_compatible (Tarray t n' noattr) nil d ->
  0 <= n <= n' ->
  field_compatible (Tarray t n noattr) nil d.
Proof.
intros until 1. pose proof I. intros.
hnf in H|-*.
destruct H as [? [? [? [? ?]]]].
unfold sizeof in *; fold (sizeof t) in *.
assert (sizeof t * n <= sizeof t * n')
  by (pose proof (sizeof_pos t); apply Z.mul_le_mono_nonneg_l; omega).
repeat split; auto.
*
hnf in H3|-*.
destruct d; auto.
unfold sizeof in *; fold (sizeof t) in *.
rewrite Z.max_r in * by omega.
omega.
*
destruct d; auto.
hnf in H4 |- *.
constructor.
intros.
eapply align_compatible_rec_Tarray_inv; eauto.
omega.
Qed.

Lemma field_compatible0_array_smaller0:
  forall {cs: compspecs} t n n' d,
  field_compatible0 (Tarray t n' noattr) nil d ->
  0 <= n <= n' ->
  field_compatible0 (Tarray t n noattr) nil d.
Proof.
intros until 1. pose proof I. intros.
hnf in H|-*.
destruct H as [? [? [? [? ?]]]].
unfold sizeof in *; fold (sizeof t) in *.
assert (sizeof t * n <= sizeof t * n')
  by (pose proof (sizeof_pos t); apply Z.mul_le_mono_nonneg_l; omega).
repeat split; auto.
*
hnf in H3|-*.
destruct d; auto.
unfold sizeof in *; fold (sizeof t) in *.
rewrite Z.max_r in * by omega.
omega.
*
destruct d; auto.
hnf in H4 |- *.
constructor.
intros.
eapply align_compatible_rec_Tarray_inv; eauto.
omega.
Qed.


Hint Extern 2 (field_compatible (Tarray _ _ _) nil _) =>
   (eapply field_compatible_array_smaller0; [eassumption | omega]) : field_compatible.

Hint Extern 2 (field_compatible (tarray _ _) nil _) =>
   (eapply field_compatible_array_smaller0; [eassumption | omega]) : field_compatible.

Hint Extern 2 (field_compatible0 (Tarray _ _ _) nil _) =>
   (eapply field_compatible0_array_smaller0; [eassumption | omega]) : field_compatible.

Hint Extern 2 (field_compatible0 (tarray _ _) nil _) =>
   (eapply field_compatible0_array_smaller0; [eassumption | omega]) : field_compatible.

Lemma field_compatible0_array_smaller1:
  forall  {cs: compspecs} t i j n1 n2 p,
    field_compatible0 (Tarray t n1 noattr) (ArraySubsc j::nil) p ->
    0 <= i <= n2 ->
    n2 <= n1 ->
    field_compatible0 (Tarray t n2 noattr) (ArraySubsc i::nil) p.
Proof.
intros until p. intros H0 H' H.
move H0 after H.
hnf in H0|-*.
 assert (SS: sizeof t * n2 <= sizeof t * n1).
  apply Zmult_le_compat_l; auto.
  pose proof (sizeof_pos t); omega.
intuition.
 *
  destruct p; try contradiction; red in H4|-*.
  unfold sizeof in H4|-*; fold (sizeof t) in *.
  rewrite Z.max_r in * by omega.
  omega.
 *
destruct p; auto.
hnf in H5 |- *.
constructor.
intros.
eapply align_compatible_rec_Tarray_inv; eauto.
omega.
 * destruct H7.
   split; auto.
   simpl in H7 |- *.
   omega.
Qed.

Hint Extern 2 (field_compatible0 (Tarray _ _ _) (ArraySubsc _ :: nil) _) =>
   (eapply field_compatible0_array_smaller1; [eassumption | omega | omega]) : field_compatible.

Hint Extern 2 (field_compatible0 (tarray _ _) (ArraySubsc _ :: nil) _) =>
   (eapply field_compatible0_array_smaller1; [eassumption | omega | omega]) : field_compatible.

Arguments nested_field_array_type {cs} t gfs lo hi / .

Hint Resolve field_compatible_field_compatible0 : field_compatible.

Lemma field_compatible0_ArraySubsc0:
 forall {cs: compspecs} t gfs p,
    field_compatible0 t gfs p ->
    legal_nested_field0 t (gfs SUB 0) ->
    field_compatible0 t (gfs SUB 0) p.
Proof.
intros. hnf in H|-*.
intuition.
Qed.

Lemma field_compatible_Tarray_split:
  forall {cs: compspecs} t i n d,
  0 <= i <= n ->
  (field_compatible (tarray t n) nil d <->
   field_compatible (tarray t i) nil d /\
   field_compatible (tarray t (n-i)) nil
       (field_address0 (tarray t n) (ArraySubsc i::nil) d)).
Proof.
intros.
unfold tarray in *.
split; intros.
assert (SP := sizeof_pos t).
assert (SL: sizeof t * i <= sizeof t * n)
  by (apply Zmult_le_compat_l; omega).
assert (SL': sizeof t * (n-i) <= sizeof t * n)
  by (apply Zmult_le_compat_l; omega).
assert (ST: 0*0 <= sizeof t * i).
apply Zmult_le_compat; omega.
change (0*0)%Z with 0 in ST.
assert (field_compatible (Tarray t i noattr) nil d /\
           field_compatible (Tarray t (n - i) noattr) nil
               (offset_val (sizeof t * i) d) /\
           field_compatible0 (Tarray t n noattr) (ArraySubsc i::nil) d). {
  unfold field_compatible, field_compatible0 in *.
decompose [and] H0; clear H0.
destruct d; try contradiction.
repeat split; auto.
*
unfold size_compatible in H2|-*.
unfold sizeof in H2|-*. fold sizeof in H2 |-*.
rewrite Z.max_r in H2|-* by omega.
omega.
*
hnf in H4 |- *.
constructor.
intros.
eapply align_compatible_rec_Tarray_inv; eauto.
omega.
*
unfold size_compatible in H2|-*.
unfold offset_val.
rewrite <- (Ptrofs.repr_unsigned i0).
rewrite ptrofs_add_repr.
unfold sizeof in H2|-*. fold sizeof in H2 |-*.
rewrite Z.max_r in H2|-* by omega.
pose proof (Ptrofs.unsigned_range i0).
destruct (zeq (Ptrofs.unsigned i0 + sizeof t * i) Ptrofs.modulus).
rewrite e.
change (Ptrofs.unsigned (Ptrofs.repr Ptrofs.modulus)) with 0.
rewrite Z.add_0_l.
omega.
rewrite Ptrofs.unsigned_repr.
assert (sizeof t * i + sizeof t * (n - i)  =  sizeof t * n)%Z.
rewrite <- Z.mul_add_distr_l.
f_equal. omega.
omega.
change Ptrofs.max_unsigned with (Ptrofs.modulus-1).
omega.
*
hnf in H4 |- *.
constructor.
intros.
rewrite <- (Ptrofs.repr_unsigned i0).
rewrite ptrofs_add_repr.
simpl in H2.
rewrite Z.max_r in H2 by omega.
solve_mod_modulus.
pose_size_mult cenv_cs t (0 :: i :: i + i1 :: i + i1 + 1 :: n :: nil).
inv_int i0.
rewrite Zmod_small by omega.
rewrite <- Z.add_assoc, <- H8.
eapply align_compatible_rec_Tarray_inv. eauto.
omega.
*
omega.
*
omega.
}
destruct H1 as [? [? ?]].
rewrite field_address0_offset.
split; auto.
auto.
destruct H0.
unfold field_address0 in H1.
if_tac in H1; [ | destruct H1; contradiction].
clear H1.
hnf in H0,H2|-*.
intuition.
Qed.

Hint Resolve field_compatible0_ArraySubsc0 : field_compatible.

Hint Extern 2 (legal_nested_field0 _ _) =>
  (apply compute_legal_nested_field0_spec'; repeat constructor; omega) : field_compatible.
Hint Extern 2 (field_compatible0 _ _ (offset_val _ _)) =>
  (apply field_compatible0_nested_field_array; auto with field_compatible).

Lemma split2_data_at_Tarray_unfold {cs: compspecs}
     sh t n n1 (v v' v1 v2: list (reptype t)) p:
   0 <= n1 <= n ->
  v = v' ->
  v1 = (sublist 0 n1 v') ->
  v2 = (sublist n1 n v') ->
  data_at sh (Tarray t n noattr) v p |--
  data_at sh (Tarray t n1 noattr) v1 p *
  data_at sh (Tarray t (n - n1) noattr) v2
    (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p).
Proof.
  intros.
  assert_PROP (Zlength v' = n). {
    eapply derives_trans; [apply data_at_local_facts | apply prop_derives].
    intros [? ?]. destruct H4 as [? _]. rewrite Z.max_r in H4 by omega.
    rewrite <- H0. exact H4.
  }
  assert_PROP (field_compatible0 (Tarray t n noattr) (ArraySubsc n1::nil) p). {
     eapply derives_trans; [apply data_at_local_facts | apply prop_derives].
     intros [? _]; auto with field_compatible.
  }
  rewrite field_address0_offset by auto.
  rewrite !nested_field_offset_ind by (repeat split; auto; omega).
  rewrite nested_field_type_ind. unfold gfield_offset.
  rewrite Z.add_0_l.
  rewrite data_at_isptr at 1.
  unfold data_at at 1. intros; simpl; normalize.
  erewrite (field_at_Tarray sh  (Tarray t n noattr) _ t); try reflexivity; trivial.
  2: omega.
  rewrite (split2_array_at sh (Tarray t n noattr) nil 0 n1).
  2: auto. 2: rewrite Z.sub_0_r, H0; auto.
  do 2 rewrite array_at_data_at by tauto.
  rewrite Zminus_0_r.
  unfold at_offset.
  erewrite (data_at_type_changable sh
            (nested_field_array_type (Tarray t n noattr) nil 0 n1)
            (Tarray t n1 noattr) _ v1).
  2: unfold nested_field_array_type; simpl; rewrite Zminus_0_r; trivial.
  2: rewrite H1, H0; auto.
  erewrite (data_at_type_changable sh
            (nested_field_array_type (Tarray t n noattr) nil n1 n)
            (Tarray t (n - n1) noattr) _  v2).
  2: unfold nested_field_array_type; simpl; trivial.
  2: rewrite H2, <- H3, H0; auto.
  rewrite !nested_field_offset_ind by (repeat split; auto; omega).
  rewrite !nested_field_type_ind.
  unfold gfield_offset.
  rewrite !Z.add_0_l. rewrite Z.mul_0_r.
  rewrite isptr_offset_val_zero; trivial.
  normalize.
Qed.

Lemma split2_data_at_Tarray_fold {cs: compspecs} sh t n n1 (v v' v1 v2: list (reptype t)) p:
   0 <= n1 <= n ->
   n <= Zlength v' ->
   v = (sublist 0 n v') ->
   v1 = (sublist 0 n1 v') ->
   v2 = (sublist n1 n v') ->
   data_at sh (Tarray t n1 noattr) v1 p *
   data_at sh (Tarray t (n - n1) noattr) v2
        (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p)
   |--
   data_at sh (Tarray t n noattr) v p.
Proof.
  intros until 1. intro Hn; intros.
  unfold field_address0.
  if_tac; [ |
  eapply derives_trans; [apply sepcon_derives;
           apply prop_and_same_derives; apply data_at_local_facts
    | normalize ];
  destruct H6; contradiction].
  assert_PROP (field_compatible (Tarray t n noattr) nil p). {
    eapply derives_trans.
    apply sepcon_derives; apply prop_and_same_derives; apply data_at_local_facts .
    normalize. apply prop_right.
   clear - H3 H4 H.
   hnf in H3,H4|-*; intuition.
  } clear H3; rename H4 into H3.
  rewrite data_at_isptr at 1. unfold at_offset. intros; normalize.
  unfold data_at at 3.  erewrite field_at_Tarray; try reflexivity; eauto; try omega.
  rewrite H0.
  rewrite (split2_array_at sh (Tarray t n noattr) nil 0 n1); trivial.
  2: autorewrite with sublist; auto.
  autorewrite with sublist.
  unfold data_at at 1; erewrite field_at_Tarray; try reflexivity; eauto; try omega.
  unfold data_at at 1; erewrite field_at_Tarray; try reflexivity; eauto; try omega.
  apply sepcon_derives.
  unfold array_at.
  rewrite H1.
  simpl. apply andp_derives; auto.
  2: apply derives_refl. 
  apply prop_derives. intuition.
  assert (sublist n1 (Z.min n (Zlength v')) v' = sublist n1 n v').
  f_equal. autorewrite with sublist. auto.
  rewrite H2.
  clear - H H3.
  rewrite array_at_data_at by omega. normalize.
  rewrite array_at_data_at by omega.
  rewrite !prop_true_andp by auto with field_compatible.
  unfold at_offset.
  apply derives_refl'.
  rewrite offset_offset_val.
  rewrite !nested_field_offset_ind by (repeat split; auto; omega).
  rewrite !nested_field_type_ind. unfold gfield_offset.
  rewrite !Z.add_0_l. rewrite Z.mul_0_r, Z.add_0_r.
  apply equal_f.
  apply data_at_type_changable; auto.
  unfold nested_field_array_type.
  rewrite !nested_field_type_ind.  unfold gfield_type. simpl. f_equal; omega.
Qed.

Lemma split2_data_at_Tarray {cs: compspecs} sh t n n1 (v v' v1 v2: list (reptype t)) p:
   0 <= n1 <= n ->
   n <= Zlength v' ->
   v = (sublist 0 n v') ->
   v1 = (sublist 0 n1 v') ->
   v2 = (sublist n1 n v') ->
   data_at sh (Tarray t n noattr) v p =
    data_at sh (Tarray t n1 noattr) v1 p *
    data_at sh (Tarray t (n - n1) noattr) v2 (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p).
Proof. intros.
 apply pred_ext.
 eapply split2_data_at_Tarray_unfold; try eassumption.
  autorewrite with sublist; auto.
  autorewrite with sublist; auto.
 eapply split2_data_at_Tarray_fold; try eassumption.
Qed.

Lemma field_compatible0_Tarray_offset:
 forall {cs: compspecs} t n i n' i' p p',
  field_compatible0 (Tarray t n' noattr) (ArraySubsc i' :: nil) p ->
  naturally_aligned t ->
  0 <= n <= n' ->
  0 <= i <= n ->
  n-i <= n'-i' ->
  i <= i' ->
  p' = offset_val (sizeof t * (i'-i)) p ->
  field_compatible0 (Tarray t n noattr) (ArraySubsc i :: nil) p'.
Proof.
intros until 1. intros NA ?H ?H Hni Hii Hp. subst p'.
  assert (SP := sizeof_pos t).
  assert (SS: sizeof t * n <= sizeof t * n').
  apply Zmult_le_compat_l. omega. omega.
  assert (SS': (sizeof t * n + sizeof t * (n'-n) = sizeof t * n')%Z).
  rewrite <- Z.mul_add_distr_l. f_equal. omega.
  hnf in H|-*.
  intuition.
  *
  destruct p; try contradiction.
  clear - SP SS SS' H H4 H0 H5 H3 H8 Hni Hii.
  red in H3|-*.
  simpl in H3,H8|-*. rewrite Z.max_r in H3|-* by omega.
  rename i0 into j.
   pose proof (Ptrofs.unsigned_range j).
   assert (0 <= sizeof t * (i'-i) <= sizeof t * n').
   split. apply Z.mul_nonneg_nonneg; omega.
   apply Zmult_le_compat_l. omega. omega.
  assert (sizeof t * (i'-i+n) <= sizeof t * n').
   apply Zmult_le_compat_l. omega. omega.
  unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr (_ * _))
    by (change Ptrofs.max_unsigned with (Ptrofs.modulus -1); omega).
  rewrite Ptrofs.unsigned_repr_eq.
  rewrite Zmod_small by omega.
  pose proof Z.mul_add_distr_l (sizeof t) (i' - i) n.
  omega.
 *
   destruct p; try contradiction.
   simpl in H3, H6 |- *.
   rewrite Z.max_r in H3 by omega.
   constructor; intros.
  unfold Ptrofs.add.
   rewrite !Ptrofs.unsigned_repr_eq.
  assert (Ptrofs.modulus <> 0) by computable.
  rewrite Z.add_mod by auto.
  rewrite Z.mod_mod by auto.
  rewrite <- Z.add_mod by auto.
  inv_int i0.
  pose_size_mult cenv_cs t (0 :: i' - i :: i' - i + i1 ::  n' :: nil).
  rewrite Zmod_small by omega.
  rewrite <- Z.add_assoc, <- H14.
  eapply align_compatible_rec_Tarray_inv; [eassumption |].
  omega.
Qed.

(*
Hint Extern 2 (field_compatible0 (Tarray _ _ _) (ArraySubsc _ :: nil) _) =>
    (eapply field_compatible0_Tarray_offset; [eassumption | omega | omega]) : field_compatible.

Hint Extern 2 (field_compatible0 (tarray _ _) (ArraySubsc _ :: nil) _) =>
    (eapply field_compatible0_Tarray_offset; [eassumption | omega | omega]) : field_compatible.
*)

Lemma split3_data_at_Tarray {cs: compspecs} sh t n n1 n2 v (v' v1 v2 v3: list (reptype t)) p:
   naturally_aligned t ->
   0 <= n1 <= n2 ->
   n2 <= n <= Zlength v' ->
   v = (sublist 0 n v') ->
   v1 = (sublist 0 n1 v') ->
   v2 = (sublist n1 n2 v') ->
   v3 = (sublist n2 n v') ->
   data_at sh (Tarray t n noattr) v p =
    data_at sh (Tarray t n1 noattr) v1 p *
    data_at sh (Tarray t (n2 - n1) noattr) v2 (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p) *
    data_at sh (Tarray t (n - n2) noattr) v3 (field_address0 (Tarray t n noattr) (ArraySubsc n2::nil) p).
Proof. intros until 1. rename H into NA; intros.
  destruct (field_compatible0_dec (tarray t n) (ArraySubsc n2::nil) p).
  erewrite (split2_data_at_Tarray sh t n n1); try eassumption; try omega.
  instantiate (1:= sublist n1 n v').
  2: reflexivity.
  erewrite (split2_data_at_Tarray sh t (n-n1) (n2-n1)); try eassumption; try omega.
  2: instantiate (1:= sublist n1 n v'); autorewrite with sublist; omega.
  2: autorewrite with sublist; auto.
  2: autorewrite with sublist;
     instantiate (1:= sublist n1 n2 v');
     auto.
  2: autorewrite with sublist;
     instantiate (1:= sublist n2 n v');
     auto.
  rewrite sepcon_assoc.
  f_equal. f_equal. f_equal. auto.
  replace  (field_address0 (Tarray t (n - n1) noattr) (SUB (n2 - n1))
     (field_address0 (Tarray t n noattr) (SUB n1) p))
   with (field_address0 (Tarray t n noattr) (SUB n2) p).
  apply equal_f.
  replace (n - n1 - (n2 - n1)) with (n - n2) by omega.
  subst v3; reflexivity.
  rewrite field_address0_offset by auto with field_compatible.
  rewrite (field_address0_offset (Tarray t n noattr) ) by auto with field_compatible.
  rewrite field_address0_offset.
  rewrite offset_offset_val. f_equal.
  rewrite !nested_field_offset_ind by auto with field_compatible.
  rewrite !nested_field_type_ind;   unfold gfield_offset.
  rewrite Z.mul_sub_distr_l.
  omega.
  rewrite !nested_field_offset_ind by auto with field_compatible.
  rewrite !nested_field_type_ind;   unfold gfield_offset.
  rewrite Z.add_0_l.
  eapply field_compatible0_Tarray_offset; try eassumption; try omega.
  f_equal. f_equal. omega.
  apply pred_ext.
  eapply derives_trans. apply data_at_local_facts. normalize.
  contradiction n0. auto with field_compatible.
  unfold field_address0 at 2.
  if_tac.
  contradiction n0. auto with field_compatible.
  eapply derives_trans. apply sepcon_derives; [apply derives_refl | ].
  apply prop_and_same_derives; apply data_at_local_facts .
  normalize. destruct H6 as [H6 _]; contradiction H6.
Qed.

Lemma split2_data_at_Tarray_tuchar {cs: compspecs} sh n n1 (v: list val) p:
   0 <= n1 <= n ->
   Zlength v = n ->
   data_at sh (Tarray tuchar n noattr) v p =
    data_at sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
    data_at sh (Tarray tuchar (n - n1) noattr) (sublist n1 n v) (field_address0 (Tarray tuchar n noattr) (ArraySubsc n1::nil) p).
Proof. intros.
 eapply split2_data_at_Tarray; auto;
 change (@reptype cs tuchar) with val.
 symmetry in H0.
 list_solve.
 rewrite sublist_same; try omega; auto.
Qed.

Lemma split3_data_at_Tarray_tuchar {cs: compspecs} sh n n1 n2 (v: list val) p:
   0 <= n1 <= n2 ->
   n2 <= n ->
   Zlength v = n ->
   data_at sh (Tarray tuchar n noattr) v p =
    data_at sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
    data_at sh (Tarray tuchar (n2 - n1) noattr) (sublist n1 n2 v) (field_address0 (Tarray tuchar n noattr) (ArraySubsc n1::nil) p) *
    data_at sh (Tarray tuchar (n - n2) noattr) (sublist n2 n v) (field_address0 (Tarray tuchar n noattr) (ArraySubsc n2::nil) p).
Proof. intros.
 eapply split3_data_at_Tarray; auto;
 change (@reptype cs tuchar) with val.
  split; simpl; auto. list_solve.
 rewrite sublist_same; try omega; auto.
Qed.

Lemma sizeof_tarray_tuchar {cs} n (N:0<=n): @sizeof cs (tarray tuchar n) = n.
Proof. simpl. rewrite Z.max_r. destruct n; trivial. omega. Qed. 

Opaque sizeof.
Import ListNotations.

Lemma memory_block_field_compatible_tarraytuchar_ent {cs} sh n p (N:0<=n < Ptrofs.modulus):
memory_block sh n p |-- !! @field_compatible cs (tarray tuchar n) nil p.
Proof. Transparent memory_block. unfold memory_block. Opaque memory_block.
   destruct p; try solve [apply FF_left]. normalize.
   apply prop_right. red.
   destruct (Ptrofs.unsigned_range i). simpl.
   repeat split; try rewrite sizeof_tarray_tuchar; trivial; try omega.
   (* TODO: abstract this proof. *)
   eapply align_compatible_rec_hardware_1.
   + exact cenv_consistent.
   + exact cenv_legal_su.
   + exact ha_env_cs_consistent.
   + exact ha_env_cs_complete.
   + reflexivity.
   + reflexivity.
Qed.

Lemma memory_block_field_compatible_tarraytuchar {cs} sh n p (N:0<=n < Ptrofs.modulus):
memory_block sh n p = !!(@field_compatible cs (tarray tuchar n) nil p) && memory_block sh n p.
Proof. apply pred_ext. apply andp_right; trivial. apply memory_block_field_compatible_tarraytuchar_ent; trivial.
normalize.
Qed. 

Lemma memory_block_data_at__tarray_tuchar {cs} sh p n (N: 0<=n < Ptrofs.modulus):
  memory_block sh n p |-- @data_at_ cs sh (tarray tuchar n) p.
Proof. 
  rewrite memory_block_field_compatible_tarraytuchar, memory_block_isptr; trivial. 
  normalize. destruct p; try solve [inv Pp].
  unfold data_at_, data_at.
  rewrite field_at__memory_block. 
  unfold field_address. rewrite if_true; trivial.
  unfold nested_field_offset, nested_field_type; simpl.
  rewrite Ptrofs.add_zero, sizeof_tarray_tuchar; try apply derives_refl; omega.
Qed.

Lemma memory_block_data_at__tarray_tuchar_eq {cs} sh p n (N: 0<=n < Ptrofs.modulus):
  memory_block sh n p = @data_at_ cs sh (tarray tuchar n) p.
Proof.
  apply pred_ext. apply memory_block_data_at__tarray_tuchar; trivial.
  rewrite data_at__memory_block; simpl. normalize. 
  rewrite sizeof_tarray_tuchar; try apply derives_refl; omega. 
Qed.

Lemma isptr_field_compatible0_tarray {cs}:
  forall t (H: complete_legal_cosu_type t = true) p,
       isptr p -> 
      @field_compatible cs (tarray t 0) nil p.
Proof. intros; red. destruct p; try contradiction.
  repeat split; simpl; trivial.
  change (sizeof (tarray t 0)) with (sizeof t * 0)%Z.
  rewrite Z.mul_0_r. rep_omega.
  apply align_compatible_rec_Tarray; intros.
  omega.
Qed.

Transparent sizeof.

Lemma data_at_singleton_array {cs} sh t vl v p:
  vl = [v] ->
  @data_at cs sh t v p |-- @data_at cs sh (tarray t 1) vl p.  
Proof.
  intros. rename H into Heq.
  rewrite data_at_isptr. normalize.
  assert_PROP (field_compatible (tarray t 1) [] p).
  { eapply derives_trans. eapply data_at_local_facts. normalize.
    destruct p; auto.
    inv_int i.
    destruct H as [? [? [? [? ?]]]].
    repeat split; auto.
    simpl. simpl in H3. rewrite Z.mul_1_r. auto.
    simpl in H4|-*.
    apply align_compatible_rec_Tarray. intros. assert (i=0) by omega. subst.
    rewrite Z.mul_0_r, Z.add_0_r. auto.
  }
  unfold data_at at 2.
  erewrite field_at_Tarray.
  2: simpl; trivial. 2: reflexivity. 2: omega. 2:apply JMeq_refl.
  rewrite Heq.
  erewrite array_at_len_1 by apply JMeq_refl.
  rewrite field_at_data_at; simpl.
  rewrite field_address_offset; trivial.
  unfold nested_field_type. simpl. unfold nested_field_offset.
    simpl. rewrite Z.mul_0_r.  rewrite isptr_offset_val_zero; auto.
  eapply field_compatible_cons_Tarray. reflexivity. trivial. omega.
Qed.

Lemma data_at_singleton_array_inv {cs} sh t (vl : list (reptype t)) v p:
  vl = [v] ->
  @data_at cs sh (tarray t 1) vl p |-- @data_at cs sh t v p.  
Proof.
  rewrite data_at_isptr. normalize.
  assert_PROP (field_compatible (tarray t 1) [] p).
  { eapply derives_trans. eapply data_at_local_facts. normalize. }
  unfold data_at at 1.
  erewrite field_at_Tarray.
  2: simpl; trivial. 2: reflexivity. 2: omega. 2: apply JMeq_refl.
  erewrite array_at_len_1. 2: apply JMeq_refl.
  rewrite field_at_data_at; simpl. 
  rewrite field_address_offset; trivial.
  unfold nested_field_type. simpl. unfold nested_field_offset.
    simpl. rewrite Z.mul_0_r.
 rewrite isptr_offset_val_zero; try apply derives_refl; auto.
  eapply field_compatible_cons_Tarray. reflexivity. trivial. omega.
Qed.

Opaque sizeof.
 
Lemma data_at_singleton_array_eq {cs} sh t v (vl: list (reptype t)) p:
  vl = [v] ->
  @data_at cs sh (tarray t 1) vl p = @data_at cs sh t v p.  
Proof. 
  intros.
   apply pred_ext.
  apply data_at_singleton_array_inv; rewrite H; auto.
  apply data_at_singleton_array; auto.
Qed.

Lemma data_at_tuchar_singleton_array {cs} sh (v: val) p:
  @data_at cs sh tuchar v p |-- @data_at cs sh (tarray tuchar 1) [v] p.  
Proof. apply data_at_singleton_array. reflexivity. Qed.

Lemma data_at_tuchar_singleton_array_inv {cs} sh (v: val) p:
  @data_at cs sh (tarray tuchar 1) [v] p |-- @data_at cs sh tuchar v p.  
Proof. apply data_at_singleton_array_inv. reflexivity. Qed.

Lemma data_at_tuchar_singleton_array_eq {cs} sh (v: val) p:
  @data_at cs sh (tarray tuchar 1) [v] p = @data_at cs sh tuchar v p.  
Proof. apply data_at_singleton_array_eq. reflexivity. Qed.

Lemma data_at_zero_array {cs} sh t (v: list (reptype t)) p:
  complete_legal_cosu_type t = true ->
  isptr p ->
  v = (@nil (reptype t)) ->
  emp |-- @data_at cs sh (tarray t 0) v p.  
Proof. intros.
  unfold data_at. 
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: apply JMeq_refl. 2: simpl; trivial.
  rewrite H1.
  rewrite array_at_len_0. apply andp_right; try apply derives_refl.
  apply prop_right.
  apply field_compatible0_ArraySubsc0.
  apply isptr_field_compatible0_tarray; auto.
 simpl.
  split; auto. omega.
Qed.

Lemma data_at_zero_array_inv {cs} sh t (v: list (reptype t)) p:
  complete_legal_cosu_type t = true ->
  v = (@nil (reptype t)) ->
  @data_at cs sh (tarray t 0) v p |-- emp.  
Proof. intros.
  unfold data_at. 
  erewrite field_at_Tarray. 3: reflexivity. 3: omega. 3: rewrite H0; apply JMeq_refl. 2: simpl; trivial.
  rewrite H0.
  rewrite array_at_len_0. normalize. 
Qed.

Lemma data_at_zero_array_eq {cs} sh t (v: list (reptype t)) p:
  complete_legal_cosu_type t = true ->
  isptr p ->
  v = (@nil (reptype t)) ->
  @data_at cs sh (tarray t 0) v p = emp.
Proof. intros. 
  apply pred_ext.
  apply data_at_zero_array_inv; auto.
  apply data_at_zero_array; auto.
Qed. 

Lemma data_at_tuchar_zero_array {cs} sh p: isptr p ->
  emp |-- @data_at cs sh (tarray tuchar 0) [] p.  
Proof. intros. apply data_at_zero_array; auto. Qed.

Lemma data_at_tuchar_zero_array_inv {cs} sh p:
  @data_at cs sh (tarray tuchar 0) [] p |-- emp.  
Proof. intros. apply data_at_zero_array_inv; auto. Qed.

Lemma data_at_tuchar_zero_array_eq {cs} sh p:
  isptr p ->
  @data_at cs sh (tarray tuchar 0) [] p = emp.  
Proof. intros. apply data_at_zero_array_eq; auto. Qed.

Lemma data_at__tuchar_zero_array {cs} sh p (H: isptr p):
  emp |-- @data_at_ cs sh (tarray tuchar 0) p.  
Proof. unfold data_at_, field_at_. apply data_at_tuchar_zero_array; trivial. Qed.

Lemma data_at__tuchar_zero_array_inv {cs} sh p:
  @data_at_ cs sh (tarray tuchar 0) p |-- emp.  
Proof. unfold data_at_, field_at_. apply data_at_tuchar_zero_array_inv. Qed.

Lemma data_at__tuchar_zero_array_eq {cs} sh p (H: isptr p):
  @data_at_ cs sh (tarray tuchar 0) p = emp.  
Proof. intros.
  apply pred_ext.
  apply data_at__tuchar_zero_array_inv.
  apply data_at__tuchar_zero_array; trivial.
Qed. 

Lemma split2_data_at__Tarray_tuchar
     : forall {cs} (sh : Share.t)  (n n1 : Z) (p : val),
       0 <= n1 <= n -> isptr p ->field_compatible (Tarray tuchar n noattr) [] p ->
       @data_at_ cs sh (Tarray tuchar n noattr) p =
       @data_at_ cs sh (Tarray tuchar n1 noattr) p *
       @data_at_ cs sh (Tarray tuchar (n - n1) noattr)
         (field_address0 (Tarray tuchar n noattr) [ArraySubsc n1] p).
Proof. intros. unfold data_at_ at 1; unfold field_at_.
rewrite field_at_data_at.
erewrite (@split2_data_at_Tarray cs sh tuchar n n1).
instantiate (1:= list_repeat (Z.to_nat (n-n1)) Vundef).
instantiate (1:= list_repeat (Z.to_nat n1) Vundef).
unfold field_address. simpl. 
rewrite if_true; trivial. rewrite isptr_offset_val_zero; trivial.
trivial.
simpl.
instantiate (1:=list_repeat (Z.to_nat n) Vundef).
list_solve.
unfold default_val. simpl. autorewrite with sublist. reflexivity.
unfold default_val. simpl. autorewrite with sublist. reflexivity.
unfold default_val. simpl. autorewrite with sublist. reflexivity.
Qed. 

Lemma split2_data_at_Tarray_app:
 forall {cs: compspecs} mid n (sh: Share.t) (t: type)
                           (v1 v2: list (reptype t)) p,
    Zlength v1 = mid ->
    Zlength v2 = n-mid ->
    data_at sh (tarray t n) (v1 ++ v2) p =
    data_at sh (tarray t mid) v1  p *
    data_at sh (tarray t (n-mid)) v2
            (field_address0 (tarray t n) [ArraySubsc mid] p).
Proof.
intros.
pose proof (Zlength_nonneg v1).
pose proof (Zlength_nonneg v2).
apply split2_data_at_Tarray with (v1++v2); auto.
omega.
list_solve.
autorewrite with sublist; auto.
autorewrite with sublist; auto.
autorewrite with sublist; auto.
Qed.

