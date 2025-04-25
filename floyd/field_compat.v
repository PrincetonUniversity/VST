Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
Require Import VST.floyd.base2.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.type_induction.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.reptype_lemmas.
Require VST.floyd.aggregate_pred. Import VST.floyd.aggregate_pred.aggregate_pred.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.jmeq_lemmas.
Require Import VST.zlist.sublist.
Require Import VST.floyd.field_at.

Local Unset SsrRewrite.

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

#[export] Hint Extern 2 (field_compatible0 _ (ArraySubsc _ :: _) _) =>
   (eapply field_compatible0_cons_Tarray; [reflexivity | | lia])
  : field_compatible.

#[export] Hint Extern 2 (field_compatible _ (ArraySubsc _ :: _) _) =>
   (eapply field_compatible_cons_Tarray; [reflexivity | | lia])
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
  by (pose proof (sizeof_pos t); apply Z.mul_le_mono_nonneg_l; lia).
repeat split; auto.
*
hnf in H3|-*.
destruct d; auto.
unfold sizeof, Ctypes.sizeof in *; fold (sizeof t) in *.
rewrite Z.max_r in * by lia.
lia.
*
destruct d; auto.
hnf in H4 |- *.
constructor.
intros.
eapply align_compatible_rec_Tarray_inv; eauto.
lia.
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
  by (pose proof (sizeof_pos t); apply Z.mul_le_mono_nonneg_l; lia).
repeat split; auto.
*
hnf in H3|-*.
destruct d; auto.
unfold sizeof, Ctypes.sizeof in *; fold (sizeof t) in *.
rewrite Z.max_r in * by lia.
lia.
*
destruct d; auto.
hnf in H4 |- *.
constructor.
intros.
eapply align_compatible_rec_Tarray_inv; eauto.
lia.
Qed.


#[export] Hint Extern 2 (field_compatible (Tarray _ _ _) nil _) =>
   (eapply field_compatible_array_smaller0; [eassumption | lia]) : field_compatible.

#[export] Hint Extern 2 (field_compatible (tarray _ _) nil _) =>
   (eapply field_compatible_array_smaller0; [eassumption | lia]) : field_compatible.

#[export] Hint Extern 2 (field_compatible0 (Tarray _ _ _) nil _) =>
   (eapply field_compatible0_array_smaller0; [eassumption | lia]) : field_compatible.

#[export] Hint Extern 2 (field_compatible0 (tarray _ _) nil _) =>
   (eapply field_compatible0_array_smaller0; [eassumption | lia]) : field_compatible.

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
  pose proof (sizeof_pos t); lia.
  intuition.
 *
  destruct p; try contradiction; red in H4|-*.
  unfold sizeof in *; simpl in *; fold (sizeof t) in *.
  rewrite Z.max_r in * by lia.
  lia.
 *
destruct p; auto.
hnf in H5 |- *.
constructor.
intros.
eapply align_compatible_rec_Tarray_inv; eauto.
lia.
 * destruct H7.
   split; auto.
   simpl in H7 |- *.
   lia.
Qed.

#[export] Hint Extern 2 (field_compatible0 (Tarray _ _ _) (ArraySubsc _ :: nil) _) =>
   (eapply field_compatible0_array_smaller1; [eassumption | lia | lia]) : field_compatible.

#[export] Hint Extern 2 (field_compatible0 (tarray _ _) (ArraySubsc _ :: nil) _) =>
   (eapply field_compatible0_array_smaller1; [eassumption | lia | lia]) : field_compatible.

Arguments nested_field_array_type {cs} t gfs lo hi / .

#[export] Hint Resolve field_compatible_field_compatible0 : field_compatible.

Lemma field_compatible0_ArraySubsc0:
 forall {cs: compspecs} t gfs p,
    field_compatible0 t gfs p ->
    legal_nested_field0 t (gfs SUB 0) ->
    field_compatible0 t (gfs SUB 0) p.
Proof.
intros. hnf in H|-*. tauto.
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
  by (apply Zmult_le_compat_l; lia).
assert (SL': sizeof t * (n-i) <= sizeof t * n)
  by (apply Zmult_le_compat_l; lia).
assert (ST: 0*0 <= sizeof t * i).
apply Zmult_le_compat; lia.
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
unfold sizeof in *; simpl in *; fold (sizeof t) in *.
rewrite Z.max_r in H2|-* by lia.
lia.
*
hnf in H4 |- *.
constructor.
intros.
eapply align_compatible_rec_Tarray_inv; eauto.
lia.
*
unfold size_compatible in H2|-*.
unfold offset_val.
rewrite <- (Ptrofs.repr_unsigned i0).
rewrite ptrofs_add_repr.
unfold sizeof in *; simpl in *; fold (sizeof t) in *.
rewrite Z.max_r in H2|-* by lia.
pose proof (Ptrofs.unsigned_range i0).
destruct (zeq (Ptrofs.unsigned i0 + sizeof t * i) Ptrofs.modulus).
rewrite e.
change (Ptrofs.unsigned (Ptrofs.repr Ptrofs.modulus)) with 0.
rewrite Z.add_0_l.
lia.
rewrite Ptrofs.unsigned_repr.
assert (sizeof t * i + sizeof t * (n - i)  =  sizeof t * n)%Z.
rewrite <- Z.mul_add_distr_l.
f_equal. lia.
lia.
change Ptrofs.max_unsigned with (Ptrofs.modulus-1).
lia.
*
hnf in H4 |- *.
constructor.
intros.
rewrite <- (Ptrofs.repr_unsigned i0).
rewrite ptrofs_add_repr.
simpl in H2.
unfold sizeof in *; simpl in *; fold (sizeof t) in *.
rewrite Z.max_r in H2 by lia.
solve_mod_modulus.
pose_size_mult cs t (0 :: i :: i + i1 :: i + i1 + 1 :: n :: nil).
inv_int i0.
rewrite Zmod_small by lia.
rewrite <- Z.add_assoc, <- H8.
eapply align_compatible_rec_Tarray_inv. eauto.
lia.
*
lia.
*
lia.
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
tauto.
Qed.

#[export] Hint Resolve field_compatible0_ArraySubsc0 : field_compatible.

#[export] Hint Extern 2 (legal_nested_field0 _ _) =>
  (apply compute_legal_nested_field0_spec'; repeat constructor; rep_lia) : field_compatible.
#[export] Hint Extern 2 (field_compatible0 _ _ (offset_val _ _)) =>
  (apply field_compatible0_nested_field_array; auto with field_compatible) : core. (*FIXME: should be field_compatible*)

Section mpred.

Context `{!VSTGS OK_ty Σ}.

Lemma andp_prop_eq' : forall P P' (Q Q' : mpred) (Hdec : {P} + {~P} ),
  (P <-> P') -> (P -> (⌜P⌝ ∧ Q) = (⌜P'⌝ ∧ Q')) -> (⌜P⌝ ∧ Q) = (⌜P'⌝ ∧ Q').
Proof.
  intros.
  apply andp_prop_eq; auto; intros.
  rewrite !prop_true_andp in H0 by tauto; auto.
Qed.

Lemma split2_data_at_Tarray {cs: compspecs} sh t n n1 (v v' v1 v2: list (reptype t)) p:
   0 <= n1 <= n ->
   n <= Zlength v' ->
   v = (sublist 0 n v') ->
   v1 = (sublist 0 n1 v') ->
   v2 = (sublist n1 n v') ->
   data_at sh (Tarray t n noattr) v p =
    (data_at sh (Tarray t n1 noattr) v1 p ∗
     data_at sh (Tarray t (n - n1) noattr) v2 (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p)).
Proof.
  intros.
  unfold data_at, field_at; normalize.
  apply andp_prop_eq'.
  { apply field_compatible_dec. }
  { apply field_compatible_Tarray_split; auto. }
  intros Hcompat.
  assert (Zlength v = n) as Hv by (subst; autorewrite with sublist; auto).
  setoid_rewrite field_at_Tarray; eauto; [|lia].
  rewrite (split2_array_at sh (Tarray t n noattr) nil 0 n1); auto; [|setoid_rewrite Hv; lia].
  trans (data_at sh (Tarray t n1 noattr) v1 p ∗
    data_at sh (Tarray t (n - n1) noattr) v2 (field_address0 (Tarray t n noattr) (SUB n1) p)); [|unfold data_at, field_at; normalize].
  erewrite !array_at_data_at''' by (eauto; lia).
  subst; autorewrite with sublist.
  f_equal.
  rewrite field_address0_offset, !nested_field_offset_ind; simpl; auto.
  rewrite Z.mul_0_r, isptr_offset_val_zero by (destruct Hcompat; auto).
  erewrite (data_at_type_changable _ _ (Tarray t n1 noattr)); auto.
  rewrite nested_field_type_ind; simpl.
  rewrite Z.sub_0_r; auto.
  { lia. }
  { rewrite field_compatible0_cons; simpl; split; auto; lia. }
Qed.

Lemma split2_data_at_Tarray_unfold {cs: compspecs}
     sh t n n1 (v v' v1 v2: list (reptype t)) p:
   0 <= n1 <= n ->
  v = v' ->
  v1 = (sublist 0 n1 v') ->
  v2 = (sublist n1 n v') ->
  data_at sh (Tarray t n noattr) v p ⊢
  data_at sh (Tarray t n1 noattr) v1 p ∗
  data_at sh (Tarray t (n - n1) noattr) v2
    (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p).
Proof.
  intros.
  assert_PROP (Zlength v' = n). {
    rewrite data_at_local_facts; apply bi.pure_mono.
    intros [? ?]. destruct H4 as [? _]. rewrite Z.max_r in H4 by lia.
    rewrite <- H0. exact H4.
  }
  subst; erewrite split2_data_at_Tarray; eauto.
  - lia.
  - autorewrite with sublist; auto.
Qed.

Lemma split2_data_at_Tarray_fold {cs: compspecs} sh t n n1 (v v' v1 v2: list (reptype t)) p:
   0 <= n1 <= n ->
   n <= Zlength v' ->
   v = (sublist 0 n v') ->
   v1 = (sublist 0 n1 v') ->
   v2 = (sublist n1 n v') ->
   data_at sh (Tarray t n1 noattr) v1 p ∗
   data_at sh (Tarray t (n - n1) noattr) v2
        (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p)
   ⊢
   data_at sh (Tarray t n noattr) v p.
Proof.
  intros.
  erewrite <-
 split2_data_at_Tarray; eauto.
Qed.

Lemma field_compatible0_Tarray_offset:
 forall {cs: compspecs} t n i n' i' p p',
  field_compatible0 (Tarray t n' noattr) (ArraySubsc i' :: nil) p ->
  0 <= n <= n' ->
  0 <= i <= n ->
  n-i <= n'-i' ->
  i <= i' ->
  p' = offset_val (sizeof t * (i'-i)) p ->
  field_compatible0 (Tarray t n noattr) (ArraySubsc i :: nil) p'.
Proof.
  intros until 1. intros ?H ?H Hni Hii Hp. subst p'.
  assert (SP := sizeof_pos t).
  assert (SS: sizeof t * n <= sizeof t * n').
  apply Zmult_le_compat_l. lia. lia.
  assert (SS': (sizeof t * n + sizeof t * (n'-n) = sizeof t * n')%Z).
  rewrite <- Z.mul_add_distr_l. f_equal. lia.
  hnf in H|-*.
  intuition auto with field_compatible.
  *
  destruct p; try contradiction.
  clear - SP SS SS' H H4 H0 H5 H3 H8 Hni Hii.
  red in H3|-*.
  unfold expr.sizeof in *.
  simpl in H3,H8|-*. rewrite Z.max_r in H3|-* by lia.
  rename i0 into j.
   pose proof (Ptrofs.unsigned_range j).
   fold (sizeof t) in *.
   assert (0 <= sizeof t * (i'-i) <= sizeof t * n').
   split. apply Z.mul_nonneg_nonneg; lia.
   apply Zmult_le_compat_l. lia. lia.
  assert (sizeof t * (i'-i+n) <= sizeof t * n').
   apply Zmult_le_compat_l. lia. lia.
  unfold Ptrofs.add.
  rewrite (Ptrofs.unsigned_repr (_ * _))
    by (change Ptrofs.max_unsigned with (Ptrofs.modulus -1); lia).
  rewrite Ptrofs.unsigned_repr_eq.
  rewrite Zmod_small by lia.
  pose proof Z.mul_add_distr_l (sizeof t) (i' - i) n.
  lia.
 *
   destruct p; try contradiction.
   simpl in H3, H6 |- *.
  unfold expr.sizeof in *.
   simpl in H3, H6 |- *.
   rewrite Z.max_r in H3 by lia.
   constructor; intros.
  unfold Ptrofs.add.
   rewrite !Ptrofs.unsigned_repr_eq.
  assert (Ptrofs.modulus <> 0) by computable.
  rewrite Z.add_mod by auto.
  rewrite Z.mod_mod by auto.
  rewrite <- Z.add_mod by auto.
  inv_int i0.
   fold (sizeof t) in *.
  pose_size_mult cs t (0 :: i' - i :: i' - i + i1 ::  n' :: nil).
  rewrite Zmod_small by lia.
  rewrite <- Z.add_assoc, <- H14.
  eapply align_compatible_rec_Tarray_inv; [eassumption |].
  lia.
Qed.

Lemma split3_data_at_Tarray {cs: compspecs} sh t n n1 n2 v (v' v1 v2 v3: list (reptype t)) p:
   naturally_aligned t ->
   0 <= n1 <= n2 ->
   n2 <= n <= Zlength v' ->
   v = (sublist 0 n v') ->
   v1 = (sublist 0 n1 v') ->
   v2 = (sublist n1 n2 v') ->
   v3 = (sublist n2 n v') ->
   data_at sh (Tarray t n noattr) v p =
    (data_at sh (Tarray t n1 noattr) v1 p ∗
     data_at sh (Tarray t (n2 - n1) noattr) v2 (field_address0 (Tarray t n noattr) (ArraySubsc n1::nil) p) ∗
     data_at sh (Tarray t (n - n2) noattr) v3 (field_address0 (Tarray t n noattr) (ArraySubsc n2::nil) p)).
Proof.
  intros until 1. rename H into NA; intros.
  destruct (field_compatible0_dec (tarray t n) (ArraySubsc n2::nil) p).
  erewrite (split2_data_at_Tarray sh t n n1); try eassumption; try lia.
  instantiate (1:= sublist n1 n v').
  2: reflexivity.
  erewrite (split2_data_at_Tarray sh t (n-n1) (n2-n1)); try eassumption; try lia.
  2: instantiate (1:= sublist n1 n v'); autorewrite with sublist; lia.
  2: autorewrite with sublist; auto.
  2: autorewrite with sublist;
     instantiate (1:= sublist n1 n2 v');
     auto.
  2: autorewrite with sublist;
     instantiate (1:= sublist n2 n v');
     auto.
  f_equiv. f_equiv. f_equiv. auto.
  replace  (field_address0 (Tarray t (n - n1) noattr) (SUB (n2 - n1))
     (field_address0 (Tarray t n noattr) (SUB n1) p))
   with (field_address0 (Tarray t n noattr) (SUB n2) p).
  { replace (n - n1 - (n2 - n1)) with (n - n2) by lia.
    subst v3; reflexivity. }
  rewrite field_address0_offset by auto with field_compatible.
  rewrite (field_address0_offset (Tarray t n noattr) ) by auto with field_compatible.
  rewrite field_address0_offset.
  rewrite offset_offset_val. f_equal.
  rewrite !nested_field_offset_ind by auto with field_compatible.
  rewrite !nested_field_type_ind;   unfold gfield_offset.
  rewrite Z.mul_sub_distr_l.
  lia.
  rewrite !nested_field_offset_ind by auto with field_compatible.
  rewrite !nested_field_type_ind;   unfold gfield_offset.
  rewrite Z.add_0_l.
  eapply field_compatible0_Tarray_offset; try eassumption; try lia.
  f_equal. f_equal. lia.
  unfold data_at, field_at; normalize; rewrite !prop_false_andp; auto.
  - intros (? & ? & Hcompat).
    unfold field_address0 in Hcompat.
    if_tac in Hcompat; auto.
    destruct Hcompat; done.
  - intros ?.
    contradiction n0. auto with field_compatible.
Qed.

Lemma split2_data_at_Tarray_tuchar {cs: compspecs} sh n n1 (v: list val) p:
   0 <= n1 <= n ->
   Zlength v = n ->
   data_at sh (Tarray tuchar n noattr) v p =
   (data_at sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p ∗
    data_at sh (Tarray tuchar (n - n1) noattr) (sublist n1 n v) (field_address0 (Tarray tuchar n noattr) (ArraySubsc n1::nil) p)).
Proof.
  intros.
  eapply split2_data_at_Tarray; auto;
  change (@reptype cs tuchar) with val.
  symmetry in H0.
  list_solve.
  rewrite sublist_same; try lia; auto.
Qed.

Lemma split2_data_at_Tarray_tschar {cs: compspecs} sh n n1 (v: list val) p:
   0 <= n1 <= n ->
   Zlength v = n ->
   data_at sh (Tarray tschar n noattr) v p =
   (data_at sh (Tarray tschar n1 noattr) (sublist 0 n1 v) p ∗
    data_at sh (Tarray tschar (n - n1) noattr) (sublist n1 n v) (field_address0 (Tarray tschar n noattr) (ArraySubsc n1::nil) p)).
Proof.
  intros.
  eapply split2_data_at_Tarray; auto;
  change (@reptype cs tschar) with val.
  symmetry in H0.
  list_solve.
  rewrite sublist_same; try lia; auto.
Qed.

Lemma split3_data_at_Tarray_tuchar {cs: compspecs} sh n n1 n2 (v: list val) p:
   0 <= n1 <= n2 ->
   n2 <= n ->
   Zlength v = n ->
   data_at sh (Tarray tuchar n noattr) v p =
   (data_at sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p ∗
    data_at sh (Tarray tuchar (n2 - n1) noattr) (sublist n1 n2 v) (field_address0 (Tarray tuchar n noattr) (ArraySubsc n1::nil) p) ∗
    data_at sh (Tarray tuchar (n - n2) noattr) (sublist n2 n v) (field_address0 (Tarray tuchar n noattr) (ArraySubsc n2::nil) p)).
Proof.
  intros.
  eapply split3_data_at_Tarray; auto;
  change (@reptype cs tuchar) with val.
  split; simpl; auto. list_solve.
  rewrite sublist_same; try lia; auto.
Qed.

Lemma split3_data_at_Tarray_tschar {cs: compspecs} sh n n1 n2 (v: list val) p:
   0 <= n1 <= n2 ->
   n2 <= n ->
   Zlength v = n ->
   data_at sh (Tarray tschar n noattr) v p =
   (data_at sh (Tarray tschar n1 noattr) (sublist 0 n1 v) p ∗
    data_at sh (Tarray tschar (n2 - n1) noattr) (sublist n1 n2 v) (field_address0 (Tarray tschar n noattr) (ArraySubsc n1::nil) p) ∗
    data_at sh (Tarray tschar (n - n2) noattr) (sublist n2 n v) (field_address0 (Tarray tschar n noattr) (ArraySubsc n2::nil) p)).
Proof.
  intros.
  eapply split3_data_at_Tarray; auto;
  change (@reptype cs tschar) with val.
  split; simpl; auto. list_solve.
  rewrite sublist_same; try lia; auto.
Qed.

Lemma sizeof_tarray_tuchar {cs : compspecs} n (N:0<=n): @sizeof cs (tarray tuchar n) = n.
Proof. unfold sizeof; simpl. rewrite Z.max_r. destruct n; trivial. lia. Qed. 

Lemma sizeof_tarray_tschar {cs : compspecs} n (N:0<=n): @sizeof cs (tarray tschar n) = n.
Proof. unfold sizeof; simpl. rewrite Z.max_r. destruct n; trivial. lia. Qed. 

Opaque sizeof.
Import ListNotations.

Lemma memory_block_field_compatible_tarraytuchar_ent {cs : compspecs} sh n p (N:0<=n < Ptrofs.modulus):
memory_block sh n p ⊢ ⌜@field_compatible cs (tarray tuchar n) nil p⌝.
Proof.
  Transparent memory_block. unfold memory_block. Opaque memory_block.
   destruct p; try solve [iIntros "[]"]. normalize.
   apply bi.pure_intro. red.
   destruct (Ptrofs.unsigned_range i). simpl.
   repeat split; try rewrite sizeof_tarray_tuchar; trivial; try lia.
   (* TODO: abstract this proof. *)
   eapply align_compatible_rec_hardware_1.
   + exact cenv_consistent.
   + exact cenv_legal_su.
   + exact ha_env_cs_consistent.
   + exact ha_env_cs_complete.
   + reflexivity.
   + reflexivity.
Qed.

Lemma memory_block_field_compatible_tarraytschar_ent {cs : compspecs} sh n p (N:0<=n < Ptrofs.modulus):
memory_block sh n p ⊢ ⌜@field_compatible cs (tarray tschar n) nil p⌝.
Proof.
  Transparent memory_block. unfold memory_block. Opaque memory_block.
   destruct p; try solve [iIntros "[]"]. normalize.
   apply bi.pure_intro. red.
   destruct (Ptrofs.unsigned_range i). simpl.
   repeat split; try rewrite sizeof_tarray_tschar; trivial; try lia.
   (* TODO: abstract this proof. *)
   eapply align_compatible_rec_hardware_1.
   + exact cenv_consistent.
   + exact cenv_legal_su.
   + exact ha_env_cs_consistent.
   + exact ha_env_cs_complete.
   + reflexivity.
   + reflexivity.
Qed.

Lemma memory_block_field_compatible_tarraytuchar {cs : compspecs} sh n p (N:0<=n < Ptrofs.modulus):
memory_block sh n p ⊣⊢ ⌜@field_compatible cs (tarray tuchar n) nil p⌝ ∧ memory_block sh n p.
Proof. apply bi.equiv_entails_2. apply bi.and_intro; trivial. apply memory_block_field_compatible_tarraytuchar_ent; trivial.
normalize.
Qed. 

Lemma memory_block_field_compatible_tarraytschar {cs : compspecs} sh n p (N:0<=n < Ptrofs.modulus):
memory_block sh n p ⊣⊢ ⌜@field_compatible cs (tarray tschar n) nil p⌝ ∧ memory_block sh n p.
Proof. apply bi.equiv_entails_2. apply bi.and_intro; trivial. apply memory_block_field_compatible_tarraytschar_ent; trivial.
normalize.
Qed. 

Lemma memory_block_data_at__tarray_tuchar {cs : compspecs} sh p n (N: 0<=n < Ptrofs.modulus):
  memory_block sh n p ⊢ data_at_ sh (tarray tuchar n) p.
Proof. 
  rewrite memory_block_field_compatible_tarraytuchar, memory_block_isptr; trivial.
  normalize. destruct p; try solve [inv Pp].
  unfold data_at_, data_at.
  rewrite field_at__memory_block. 
  unfold field_address. rewrite if_true; trivial.
  unfold nested_field_offset, nested_field_type; simpl.
  rewrite Ptrofs.add_zero, sizeof_tarray_tuchar; try apply derives_refl; lia.
Qed.

Lemma memory_block_data_at__tarray_tschar {cs : compspecs} sh p n (N: 0<=n < Ptrofs.modulus):
  memory_block sh n p ⊢ data_at_ sh (tarray tschar n) p.
Proof. 
  rewrite memory_block_field_compatible_tarraytschar, memory_block_isptr; trivial.
  normalize. destruct p; try solve [inv Pp].
  unfold data_at_, data_at.
  rewrite field_at__memory_block.
  unfold field_address. rewrite if_true; trivial.
  unfold nested_field_offset, nested_field_type; simpl.
  rewrite Ptrofs.add_zero, sizeof_tarray_tschar; try apply derives_refl; lia.
Qed.

Lemma memory_block_data_at__tarray_tuchar_eq {cs : compspecs} sh p n (N: 0<=n < Ptrofs.modulus):
  memory_block sh n p ⊣⊢ data_at_ sh (tarray tuchar n) p.
Proof.
  apply bi.equiv_entails_2. apply memory_block_data_at__tarray_tuchar; trivial.
  rewrite data_at__memory_block; simpl. normalize.
  rewrite sizeof_tarray_tuchar; try apply derives_refl; lia.
Qed.

Lemma memory_block_data_at__tarray_tschar_eq {cs : compspecs} sh p n (N: 0<=n < Ptrofs.modulus):
  memory_block sh n p ⊣⊢ data_at_ sh (tarray tschar n) p.
Proof.
  apply bi.equiv_entails_2. apply memory_block_data_at__tarray_tschar; trivial.
  rewrite data_at__memory_block; simpl. normalize. 
  rewrite sizeof_tarray_tschar; try apply derives_refl; lia. 
Qed.

Lemma isptr_field_compatible0_tarray {cs : compspecs}:
  forall t (H: complete_legal_cosu_type t = true) p,
       isptr p -> 
      field_compatible (tarray t 0) nil p.
Proof. intros; red. destruct p; try contradiction.
  repeat split; simpl; trivial.
  change (sizeof (tarray t 0)) with (sizeof t * 0)%Z.
  rewrite Z.mul_0_r. rep_lia.
  apply align_compatible_rec_Tarray; intros.
  lia.
Qed.

Transparent sizeof.

Lemma data_at_singleton_array {cs : compspecs} sh t vl v p:
  vl = [v] ->
  data_at sh t v p ⊢ data_at sh (tarray t 1) vl p.
Proof.
  intros. rename H into Heq.
  rewrite data_at_isptr. normalize.
  assert_PROP (field_compatible (tarray t 1) [] p).
  { iIntros "H"; iDestruct (data_at_local_facts with "H") as %(? & ?); iPureIntro.
    destruct p; auto.
    inv_int i.
    destruct H as [? [? [? [? ?]]]].
    repeat split; auto.
    simpl in H3|-*. unfold sizeof in H3|-*; simpl in H3|-*.
    rewrite Z.mul_1_r. auto.
    simpl in H4|-*.
    apply align_compatible_rec_Tarray. intros. assert (i=0) by lia. subst.
    rewrite Z.mul_0_r, Z.add_0_r. auto.
  }
  unfold data_at at 2.
  erewrite field_at_Tarray.
  2: simpl; trivial. 2: reflexivity. 2: lia. 2:apply JMeq_refl.
  rewrite Heq.
  erewrite array_at_len_1 by apply JMeq_refl.
  rewrite field_at_data_at; simpl.
  rewrite field_address_offset; trivial.
  unfold nested_field_type. simpl. unfold nested_field_offset.
    simpl. rewrite Z.mul_0_r.  rewrite isptr_offset_val_zero; auto.
  eapply field_compatible_cons_Tarray. reflexivity. trivial. lia.
Qed.

Lemma data_at_singleton_array_inv {cs : compspecs} sh t (vl : list (reptype t)) v p:
  vl = [v] ->
  data_at sh (tarray t 1) vl p ⊢ data_at sh t v p.
Proof.
  rewrite data_at_isptr. normalize.
  assert_PROP (field_compatible (tarray t 1) [] p).
  { rewrite data_at_local_facts; apply bi.pure_mono; tauto. }
  unfold data_at at 1.
  erewrite field_at_Tarray.
  2: simpl; trivial. 2: reflexivity. 2: lia. 2: apply JMeq_refl.
  erewrite array_at_len_1. 2: apply JMeq_refl.
  rewrite field_at_data_at; simpl. 
  rewrite field_address_offset; trivial.
  unfold nested_field_type. simpl. unfold nested_field_offset.
    simpl. rewrite Z.mul_0_r.
 rewrite isptr_offset_val_zero; try apply derives_refl; auto.
  eapply field_compatible_cons_Tarray. reflexivity. trivial. lia.
Qed.

Opaque sizeof.

Lemma data_at_singleton_array_eq {cs : compspecs} sh t v (vl: list (reptype t)) p:
  vl = [v] ->
  data_at sh (tarray t 1) vl p ⊣⊢ data_at sh t v p.
Proof. 
  intros.
   apply bi.equiv_entails_2.
  apply data_at_singleton_array_inv; rewrite H; auto.
  apply data_at_singleton_array; auto.
Qed.

Lemma data_at_tuchar_singleton_array {cs : compspecs} sh (v: val) p:
  data_at sh tuchar v p ⊢ data_at sh (tarray tuchar 1) [v] p.
Proof. apply data_at_singleton_array. reflexivity. Qed.

Lemma data_at_tschar_singleton_array {cs : compspecs} sh (v: val) p:
  data_at sh tschar v p ⊢ data_at sh (tarray tschar 1) [v] p.
Proof. apply data_at_singleton_array. reflexivity. Qed.

Lemma data_at_tuchar_singleton_array_inv {cs : compspecs} sh (v: val) p:
  data_at sh (tarray tuchar 1) [v] p ⊢ data_at sh tuchar v p.
Proof. apply data_at_singleton_array_inv. reflexivity. Qed.

Lemma data_at_tschar_singleton_array_inv {cs : compspecs} sh (v: val) p:
  data_at sh (tarray tschar 1) [v] p ⊢ data_at sh tschar v p.
Proof. apply data_at_singleton_array_inv. reflexivity. Qed.

Lemma data_at_tuchar_singleton_array_eq {cs : compspecs} sh (v: val) p:
  data_at sh (tarray tuchar 1) [v] p ⊣⊢ data_at sh tuchar v p.
Proof. apply data_at_singleton_array_eq. reflexivity. Qed.

Lemma data_at_tschar_singleton_array_eq {cs : compspecs} sh (v: val) p:
  data_at sh (tarray tschar 1) [v] p ⊣⊢ data_at sh tschar v p.
Proof. apply data_at_singleton_array_eq. reflexivity. Qed.

Lemma data_at_zero_array {cs : compspecs} sh t (v: list (reptype t)) p:
  complete_legal_cosu_type t = true ->
  isptr p ->
  v = (@nil (reptype t)) ->
  emp ⊢ data_at sh (tarray t 0) v p.
Proof. intros.
  unfold data_at. 
  erewrite field_at_Tarray. 3: reflexivity. 3: lia. 3: apply JMeq_refl. 2: simpl; trivial.
  rewrite H1.
  rewrite array_at_len_0. apply bi.and_intro; try apply derives_refl.
  apply bi.pure_intro.
  apply field_compatible0_ArraySubsc0.
  apply isptr_field_compatible0_tarray; auto.
  simpl.
  split; auto. lia.
Qed.

Lemma data_at_zero_array_inv {cs : compspecs} sh t (v: list (reptype t)) p:
  complete_legal_cosu_type t = true ->
  v = (@nil (reptype t)) ->
  data_at sh (tarray t 0) v p ⊢ emp.
Proof. intros.
  unfold data_at. 
  erewrite field_at_Tarray. 3: reflexivity. 3: lia. 3: rewrite H0; apply JMeq_refl. 2: simpl; trivial.
  rewrite H0.
  rewrite array_at_len_0. normalize. 
Qed.

Lemma data_at_zero_array_eq {cs : compspecs} sh t (v: list (reptype t)) p:
  complete_legal_cosu_type t = true ->
  isptr p ->
  v = (@nil (reptype t)) ->
  data_at sh (tarray t 0) v p ⊣⊢ emp.
Proof. intros. 
  apply bi.equiv_entails_2.
  apply data_at_zero_array_inv; auto.
  apply data_at_zero_array; auto.
Qed. 

Lemma data_at_tuchar_zero_array {cs : compspecs} sh p: isptr p ->
  emp ⊢ data_at sh (tarray tuchar 0) [] p.
Proof. intros. apply data_at_zero_array; auto. Qed.

Lemma data_at_tschar_zero_array {cs : compspecs} sh p: isptr p ->
  emp ⊢ data_at sh (tarray tschar 0) [] p.
Proof. intros. apply data_at_zero_array; auto. Qed.

Lemma data_at_tuchar_zero_array_inv {cs : compspecs} sh p:
  data_at sh (tarray tuchar 0) [] p ⊢ emp.
Proof. intros. apply data_at_zero_array_inv; auto. Qed.

Lemma data_at_tschar_zero_array_inv {cs : compspecs} sh p:
  data_at sh (tarray tschar 0) [] p ⊢ emp.
Proof. intros. apply data_at_zero_array_inv; auto. Qed.

Lemma data_at_tuchar_zero_array_eq {cs : compspecs} sh p:
  isptr p ->
  data_at sh (tarray tuchar 0) [] p ⊣⊢ emp.
Proof. intros. apply data_at_zero_array_eq; auto. Qed.

Lemma data_at_tschar_zero_array_eq {cs : compspecs} sh p:
  isptr p ->
  data_at sh (tarray tschar 0) [] p ⊣⊢ emp.
Proof. intros. apply data_at_zero_array_eq; auto. Qed.

Lemma data_at__tuchar_zero_array {cs : compspecs} sh p (H: isptr p):
  emp ⊢ data_at_ sh (tarray tuchar 0) p.
Proof. unfold data_at_, field_at_. apply data_at_tuchar_zero_array; trivial. Qed.

Lemma data_at__tschar_zero_array {cs : compspecs} sh p (H: isptr p):
  emp ⊢ data_at_ sh (tarray tschar 0) p.
Proof. unfold data_at_, field_at_. apply data_at_tschar_zero_array; trivial. Qed.

Lemma data_at__tuchar_zero_array_inv {cs : compspecs} sh p:
  data_at_ sh (tarray tuchar 0) p ⊢ emp.
Proof. unfold data_at_, field_at_. apply data_at_tuchar_zero_array_inv. Qed.

Lemma data_at__tschar_zero_array_inv {cs : compspecs} sh p:
  data_at_ sh (tarray tschar 0) p ⊢ emp.
Proof. unfold data_at_, field_at_. apply data_at_tschar_zero_array_inv. Qed.

Lemma data_at__tuchar_zero_array_eq {cs : compspecs} sh p (H: isptr p):
  data_at_ sh (tarray tuchar 0) p ⊣⊢ emp.
Proof. intros.
  apply bi.equiv_entails_2.
  apply data_at__tuchar_zero_array_inv.
  apply data_at__tuchar_zero_array; trivial.
Qed. 

Lemma data_at__tschar_zero_array_eq {cs : compspecs} sh p (H: isptr p):
  data_at_ sh (tarray tschar 0) p ⊣⊢ emp.
Proof. intros.
  apply bi.equiv_entails_2.
  apply data_at__tschar_zero_array_inv.
  apply data_at__tschar_zero_array; trivial.
Qed. 

Lemma split2_data_at__Tarray_tuchar
     : forall {cs : compspecs} (sh : Share.t)  (n n1 : Z) (p : val),
       0 <= n1 <= n -> isptr p ->field_compatible (Tarray tuchar n noattr) [] p ->
       data_at_ sh (Tarray tuchar n noattr) p =
       (data_at_ sh (Tarray tuchar n1 noattr) p ∗
        data_at_ sh (Tarray tuchar (n - n1) noattr)
          (field_address0 (Tarray tuchar n noattr) [ArraySubsc n1] p)).
Proof.
intros. unfold data_at_ at 1; unfold field_at_.
rewrite field_at_data_at.
erewrite (@split2_data_at_Tarray cs sh tuchar n n1).
instantiate (1:= Zrepeat Vundef (n-n1)).
instantiate (1:= Zrepeat Vundef n1).
unfold field_address. simpl. 
rewrite if_true; trivial. rewrite isptr_offset_val_zero; trivial.
trivial.
instantiate (1:=Zrepeat Vundef n).
change (@reptype _ _)  with val.
list_solve.
unfold default_val. simpl. autorewrite with sublist. reflexivity.
unfold default_val. simpl. autorewrite with sublist. reflexivity.
unfold default_val. simpl. autorewrite with sublist. reflexivity.
Qed. 

Lemma split2_data_at__Tarray_tschar
     : forall {cs : compspecs} (sh : Share.t)  (n n1 : Z) (p : val),
       0 <= n1 <= n -> isptr p ->field_compatible (Tarray tschar n noattr) [] p ->
       data_at_ sh (Tarray tschar n noattr) p =
       (data_at_ sh (Tarray tschar n1 noattr) p ∗
        data_at_ sh (Tarray tschar (n - n1) noattr)
         (field_address0 (Tarray tschar n noattr) [ArraySubsc n1] p)).
Proof. intros. unfold data_at_ at 1; unfold field_at_.
rewrite field_at_data_at.
erewrite (@split2_data_at_Tarray cs sh tschar n n1).
instantiate (1:= Zrepeat Vundef (n-n1)).
instantiate (1:= Zrepeat Vundef n1).
unfold field_address. simpl. 
rewrite if_true; trivial. rewrite isptr_offset_val_zero; trivial.
trivial.
simpl.
instantiate (1:=Zrepeat Vundef n).
change (@reptype _ _)  with val.
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
    (data_at sh (tarray t mid) v1  p ∗
     data_at sh (tarray t (n-mid)) v2
            (field_address0 (tarray t n) [ArraySubsc mid] p)).
Proof.
intros.
pose proof (Zlength_nonneg v1).
pose proof (Zlength_nonneg v2).
apply split2_data_at_Tarray with (v1++v2); auto.
lia.
list_solve.
autorewrite with sublist; auto.
autorewrite with sublist; auto.
autorewrite with sublist; auto.
Qed.

(*Repeats a def and lemma from veric, to give access to the right sepcon*)
Fixpoint sepconN N (P: val -> mpred) sz (p:val):mpred :=
  match N with
    O => emp
  | S n => P p ∗ sepconN n P sz (offset_val sz p)
  end.

Lemma mapsto_zeros_mapsto_nullval_N {cenv} N sh t b z:
       readable_share sh ->
       (align_chunk Mptr | Ptrofs.unsigned z) ->
       mapsto_zeros (Z.of_nat N * size_chunk Mptr) sh (Vptr b z)
       ⊢ ⌜0 <= Ptrofs.unsigned z /\
               (Z.of_nat N * size_chunk Mptr + Ptrofs.unsigned z < Ptrofs.modulus)%Z⌝ ∧
           sepconN N (fun p => mapsto sh (Tpointer t noattr) p nullval)
                     (@sizeof cenv (Tpointer t noattr)) (Vptr b z).
Proof.
  intros. constructor. now apply mapsto_memory_block.mapsto_zeros_mapsto_nullval_N.
Qed.

Lemma size_chunk_range: 0 < size_chunk Mptr <= Ptrofs.max_unsigned.
Proof. rewrite size_chunk_Mptr. unfold Ptrofs.max_unsigned.
 specialize Ptrofs.modulus_eq64.
 specialize Ptrofs.modulus_eq32.
 destruct (Archi.ptr64); intros X Y.
 rewrite Y; [ simpl; rep_lia | trivial].
 rewrite X; [ simpl; rep_lia | trivial].
Qed.

Lemma sizeof_Tpointer cenv t a: @sizeof cenv (Tpointer t a) = if Archi.ptr64 then 8 else 4.
Proof. reflexivity. Qed.

Lemma sizeof_Tarray cenv t n a: @sizeof cenv (Tarray t n a) = (@sizeof cenv t * Z.max 0 n)%Z.
Proof. reflexivity. Qed.
Lemma Csizeof_Tpointer cenv t a: @Ctypes.sizeof cenv (Tpointer t a) = if Archi.ptr64 then 8 else 4.
Proof. reflexivity. Qed.

Lemma Csizeof_Tarray cenv t n a: @Ctypes.sizeof cenv (Tarray t n a) = (@Ctypes.sizeof cenv t * Z.max 0 n)%Z.
Proof. reflexivity. Qed.

Lemma sepconN_mapsto_array {cenv t b sh} K : forall z
    (Az: Z.divide (align_chunk Mptr) (Ptrofs.unsigned z))
    (Hz: 0 <= Ptrofs.unsigned z /\
               Z.of_nat K * size_chunk Mptr + Ptrofs.unsigned z < Ptrofs.modulus),
    sepconN K (fun p : val => mapsto sh (Tpointer t noattr) p nullval) (size_chunk Mptr) (Vptr b z)
⊢ data_at(cs := cenv) sh (tarray (Tpointer t noattr) (Z.of_nat K)) (repeat nullval K) (Vptr b z).
Proof.
  specialize (Zle_0_nat K); specialize size_chunk_range; intros SZ Kpos.
  induction K; intros.
+ rewrite data_at_zero_array_eq; simpl; trivial. (* apply derives_refl.*)
+ rewrite (split2_data_at_Tarray_app 1 (Z.of_nat (S K)) sh (Tpointer t noattr) [nullval] (repeat nullval K)).
  2: reflexivity.
  2: rewrite Zlength_repeat'; lia.
  replace (Z.of_nat (S K) * size_chunk Mptr)%Z with 
          (Z.of_nat K * size_chunk Mptr + size_chunk Mptr)%Z in Hz by lia.
  replace  (Z.of_nat (S K) - 1) with (Z.of_nat K) by lia.
  eapply bi.sep_mono.
  - erewrite mapsto_data_at'; simpl; trivial.
    erewrite data_at_singleton_array_eq. apply derives_refl. trivial.
    red; simpl. rewrite sizeof_Tpointer. intuition. unfold size_chunk, Mptr in H2. destruct (Archi.ptr64); simpl; lia.
    econstructor. reflexivity. trivial.
  - assert (0 <= Z.of_nat K) as Hk by lia. 
    assert (0 <= Ptrofs.unsigned z + size_chunk Mptr <= Ptrofs.max_unsigned).
    { clear IHK. split. lia. rewrite Z.add_comm. rewrite <- Z.add_assoc in Hz.
      forget (size_chunk Mptr + Ptrofs.unsigned z) as c. unfold Ptrofs.max_unsigned.
      assert (c < Ptrofs.modulus).
      + eapply Z.le_lt_trans. 2: apply Hz. apply (Z.add_le_mono 0). apply Zmult_gt_0_le_0_compat; lia. lia.
      + lia. }
    fold sepconN. unfold offset_val. etrans.
    * apply IHK; clear IHK; trivial.
      ++ rewrite Ptrofs.add_unsigned. rewrite (Ptrofs.unsigned_repr (size_chunk Mptr)) by lia.
         rewrite Ptrofs.unsigned_repr by trivial.
         apply Z.divide_add_r; trivial. apply align_size_chunk_divides.
      ++ rewrite Ptrofs.add_unsigned. rewrite (Ptrofs.unsigned_repr (size_chunk Mptr)) by lia.
         rewrite Ptrofs.unsigned_repr by trivial. lia.
    * apply bi.equiv_entails_1_1. simpl. clear IHK.
      f_equiv; hnf. unfold field_address0.
      rewrite if_true. reflexivity.
      red; repeat split; try solve [simpl; trivial; lia].
      ++ red. unfold tarray. rewrite sizeof_Tarray, sizeof_Tpointer, Z.max_r by lia.
         unfold Mptr in *. destruct Archi.ptr64; simpl in *; lia.
      ++ red. constructor; intros. econstructor. reflexivity. rewrite Csizeof_Tpointer.
         simpl. unfold Mptr in *. destruct (Archi.ptr64).
         -- apply Z.divide_add_r. trivial.
            eapply Z.divide_trans. apply align_size_chunk_divides. simpl size_chunk. exists i; lia.
         -- apply Z.divide_add_r. trivial.
            eapply Z.divide_trans. apply align_size_chunk_divides. simpl size_chunk. exists i; lia.
Qed.

Lemma mapsto_zeros_data_atTarrayTptr_nullval_N {cenv : compspecs} N sh t b z:
       readable_share sh ->
       (align_chunk Mptr | Ptrofs.unsigned z) ->
       mapsto_zeros (Z.of_nat N * size_chunk Mptr) sh (Vptr b z)
       ⊢ data_at sh (tarray (Tpointer t noattr) (Z.of_nat N)) (repeat nullval N) (Vptr b z).
Proof. intros.
  rewrite mapsto_zeros_mapsto_nullval_N; try done.
  Intros. apply sepconN_mapsto_array; trivial.
Qed.

Lemma mapsto_zeros_isptr z sh p : mapsto_zeros z sh p ⊢ ⌜isptr p⌝.
Proof. unfold mapsto_zeros. destruct p; try iIntros "[]". apply bi.pure_intro. simpl; trivial. Qed.

Lemma field_compatible_byvalue {cs: compspecs}:
 forall big b small s gfs p k,
  access_mode small = By_value s ->
  field_compatible big gfs p ->
  access_mode big = By_value b ->
  (size_chunk s | size_chunk b) ->
  (align_chunk s | align_chunk b) ->
  (size_chunk s | k) ->
  (0 <= k) ->
  (k + size_chunk s <= size_chunk b) ->
  field_compatible small gfs (offset_val k p).
Proof.
intros * NS ? NB ? AL ? ? ?.
destruct H as [? [? [? [? ?]]]].
split3; auto.
destruct small; inv NS; simpl; auto.
destruct p; try contradiction. clear H.
unfold offset_val in *.
unfold size_compatible, align_compatible in *.
replace (sizeof big) with (size_chunk b) in *
 by (destruct big as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | |  ]; inv NB; reflexivity).
replace (sizeof small) with (size_chunk s) in *
 by (destruct small as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | |  ]; inv NS; reflexivity).
unfold Ptrofs.add.
assert (0 < size_chunk b < Ptrofs.modulus) by (destruct b; simpl; rep_lia).
assert (0 < size_chunk s) by (destruct s; simpl; rep_lia).
rewrite (Ptrofs.unsigned_repr k) by rep_lia.
 rewrite Ptrofs.unsigned_repr by rep_lia.
split3.
- rep_lia.
-
 eapply align_compatible_rec_by_value_inv in H6; [ | eassumption ].
 eapply align_compatible_rec_by_value; [ eassumption | ].
 apply Z.divide_add_r.
 eapply Z.divide_trans; eassumption.
 eapply Z.divide_trans; try apply align_size_chunk_divides; eassumption.
-
  clear - H7 NS NB.
  destruct gfs. apply I.
  exfalso.
  revert g H7; induction gfs; intros. destruct H7.
   unfold nested_field_type in H0. simpl in H0.
 destruct big as [ | [ | | | ] [ | ] | [ | ] | [ | ] | | | | |  ]; inv NB; contradiction.
 destruct H7 as [[? ?] ?].
  apply IHgfs with a. split; auto.
Qed.

Lemma field_compatible_byvalue' {cs: compspecs}:
 forall big b small s gfs p k,
  access_mode small = By_value s ->
  field_compatible big gfs p ->
  access_mode big = By_value b ->
  (size_chunk b) mod (size_chunk s) = 0 ->
  (align_chunk b) mod (align_chunk s) = 0 ->
  k mod (size_chunk s) = 0 ->
  Z.leb 0 k = true ->
  Z.leb (k + size_chunk s) (size_chunk b) = true ->
  field_compatible small gfs (offset_val k p).
Proof.
intros.
pose proof (size_chunk_pos s).
eapply field_compatible_byvalue; eauto;
try (apply Zmod_divide; [ try lia | auto ]).
pose proof (align_chunk_pos s); lia.
apply Z.leb_le; auto.
apply Z.leb_le; auto.
Qed.

Lemma field_compatible_byvalue0 {cs: compspecs}:
 forall big b small s gfs p,
  access_mode small = By_value s ->
  field_compatible big gfs p ->
  access_mode big = By_value b ->
  (size_chunk b) mod (size_chunk s) = 0 ->
  (align_chunk b) mod (align_chunk s) = 0 ->
  field_compatible small gfs p.
Proof.
intros.
rewrite <- (isptr_offset_val_zero p) by (destruct H; auto).
eapply field_compatible_byvalue'; eauto.
apply Z.leb_le.
rewrite Z.add_0_l.
pose proof (size_chunk_pos s).
apply Zmod_divide in H2; [ | lia].
destruct H2.
pose proof (size_chunk_pos b).
assert (0 < x) by lia.
rewrite H2 in *. clear b H2 H1 H3.
assert (1 * size_chunk s <= x * size_chunk s); [ | lia].
apply Zmult_le_compat_r; [ | lia].
lia.
Qed.

Lemma split2_data_at__Tarray_app {cs: compspecs}
     : forall (mid n : Z) (sh : Share.t) (t : type) (p : val),
       0 <= mid <= n ->
       data_at_ sh (tarray t n) p ⊣⊢ data_at_ sh (tarray t mid) p
                                                ∗ data_at_ sh (tarray t (n - mid)) 
                                                    (field_address0 (tarray t n) (SUB mid) p).
Proof.
intros.
unfold tarray.
rewrite !data_at__Tarray.
fold (tarray t n). fold (tarray t mid). fold (tarray t (n-mid)).
rewrite <- split2_data_at_Tarray_app by list_solve.
f_equiv. rewrite Zrepeat_app by list_solve. f_equal. lia.
Qed.

Lemma data__at_singleton_array_eq:
  forall {cs : compspecs} (sh : Share.t) (t : type) (p : val), 
  data_at_ sh (tarray t 1) p ⊣⊢ data_at_ sh t p.
Proof.
intros.
apply data_at_singleton_array_eq.
reflexivity.
Qed.

Lemma field_address0_SUB_SUB {cs: compspecs}:
 forall t n1 n2 i j p,
 n2 = j+n1 ->
 0 <= i <= n1 -> 0 <= j ->
 field_address0 (tarray t n1) (SUB i) (field_address0 (tarray t n2) (SUB j) p) =
 field_address0 (tarray t n2) (SUB (i+j)) p.
Proof.
Transparent sizeof.
intros * Hn2 Hn1 Hj.
subst n2.
unfold field_address0.
destruct (field_compatible0_dec (tarray t (j + n1)) (SUB (i + j)) p).
-
rewrite !if_true.
+ unfold nested_field_offset; simpl. rewrite offset_offset_val. f_equal. lia.
+
eapply field_compatible0_array_smaller1; try eassumption; lia.
+
rewrite if_true by (eapply field_compatible0_array_smaller1; try eassumption; lia).
simpl.
destruct f as [? [? [? [? [? ?]]]]].
split3; auto. split3; [ | | split]; auto.
*
destruct p; try contradiction.
red in H1|-*.
unfold nested_field_offset; simpl.
unfold sizeof in *.
simpl Ctypes.sizeof in *.
rewrite Z.max_r in * by lia.
rewrite Z.mul_add_distr_l in H1.
pose proof (Ctypes.sizeof_pos t).
unfold nested_field_offset; simpl.
rewrite <- (Ptrofs.repr_unsigned i0).
rewrite ptrofs_add_repr.
rewrite Ptrofs.unsigned_repr.
lia.
assert (Ctypes.sizeof t * n1 >= 0) by nia.
rep_lia.
*
destruct p; try contradiction.
simpl in H4.
red in H2|-*; unfold nested_field_offset in *; simpl in H2|-*.
apply align_compatible_rec_Tarray. intros.
eapply align_compatible_rec_Tarray_inv with (i:=i1+j) in H2; try lia.
rewrite Z.mul_add_distr_l in H2.
rewrite <- (Ptrofs.repr_unsigned i0), ptrofs_add_repr.
rewrite Ptrofs.unsigned_repr.
unfold sizeof.
rewrite Z.add_0_l.
replace  (Ptrofs.unsigned i0 + (Ctypes.sizeof t * j) + Ctypes.sizeof t * i1)
 with   (Ptrofs.unsigned i0 + (Ctypes.sizeof t * i1 + Ctypes.sizeof t * j))
  by rep_lia; auto.
unfold sizeof.
pose proof (Ctypes.sizeof_pos t).
assert (0 <= Ctypes.sizeof t * j <= Ctypes.sizeof t * j + Ctypes.sizeof t * i1) by nia.
red in H1.
simpl in H1.
rewrite Z.max_r in H1 by lia.
rewrite Z.mul_add_distr_l in H1.
assert (Ctypes.sizeof t * i1 <= Ctypes.sizeof t * n1) by nia.
rep_lia.
-
if_tac; auto.
if_tac; auto.
contradiction n. clear n.
simpl in H.
auto with field_compatible.
Opaque sizeof.
Qed.

End mpred.

#[export] Hint Extern 2 (field_compatible _ _ _) =>
  (eapply field_compatible_byvalue0; [ reflexivity | eassumption | reflexivity..]) : field_compatible.
#[export] Hint Extern 2 (field_compatible _ _ (offset_val _ _)) =>
  (eapply field_compatible_byvalue'; [ reflexivity | eassumption | reflexivity..]) : field_compatible.

#[export] Hint Extern 2 (field_address _ _ _ = field_address _ _ _) =>
  (do 2 rewrite field_address_offset by auto with field_compatible;
   reflexivity) : field_compatible.

#[export] Hint Extern 2 (field_address _ _ _ = field_address0 _ _ _) =>
  (rewrite field_address_offset by auto with field_compatible;
   rewrite field_address0_offset by auto with field_compatible;
   reflexivity) : field_compatible.

#[export] Hint Extern 2 (field_address0 _ _ _ = field_address _ _ _) =>
  (rewrite field_address_offset by auto with field_compatible;
   rewrite field_address0_offset by auto with field_compatible;
   reflexivity) : field_compatible.

#[export] Hint Extern 2 (field_address0 _ _ _ = field_address0 _ _ _) =>
  (do 2 rewrite field_address0_offset by auto with field_compatible;
   reflexivity) : field_compatible.
