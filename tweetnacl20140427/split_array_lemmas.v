Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import ZArith.

(*generalizes Lemma data_at_lemmas.memory_block_data_at__aux1*)
Lemma unsigned_add: forall i pos, 0 <= pos -> Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr pos)) = (Ptrofs.unsigned i + pos) mod Ptrofs.modulus.
Proof.
  intros.
  unfold Ptrofs.add.
  pose proof Ptrofs.modulus_pos.
  pose proof Ptrofs.unsigned_range i.
  pose proof Ptrofs.unsigned_range (Ptrofs.repr pos).
  rewrite !Ptrofs.unsigned_repr_eq in *.
  rewrite Z.add_mod by omega.
  rewrite Z.mod_mod by omega.
  rewrite <- Z.add_mod by omega.
  reflexivity.
Qed.

Lemma Arith_aux1: forall i pos z,
  0 <= pos /\ pos + z <= Ptrofs.modulus - Ptrofs.unsigned i ->
  Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr pos)) + z <= Ptrofs.modulus.
Proof.
  intros.
  destruct H.
  rewrite (unsigned_add i pos H).
  cut ((Ptrofs.unsigned i + pos) mod Ptrofs.modulus <= Ptrofs.unsigned i + pos).
    { intros. omega. }
  pose proof Ptrofs.modulus_pos.
  pose proof Ptrofs.unsigned_range i.
  apply Z.mod_le; omega.
Qed.

Lemma offset_in_range_0 v: offset_in_range 0 v.
  destruct v; simpl; trivial. rewrite Z.add_0_r.
  specialize (Ptrofs.unsigned_range i); intros. omega.
Qed.
Lemma offset_in_range_le n m d:
      offset_in_range n d -> 0<=m<=n ->
      offset_in_range m d.
unfold offset_in_range; intros.
destruct d; simpl in *; trivial.
split; try omega.
apply Z.add_nonneg_nonneg. apply (Ptrofs.unsigned_range i). omega.
Qed.
(*
Lemma offset_in_range_offset_val' n off v:
      offset_in_range off v ->
      offset_in_range (off+1) v ->
      offset_in_range n (offset_val off v) =
      offset_in_range (n+off) v.
intros.
  destruct v; trivial. unfold offset_in_range, offset_val in *.
  rewrite  (Z.add_comm n), Z.add_assoc in *.
  destruct (Ptrofs.unsigned_range i).
  rewrite Ptrofs.add_unsigned.
  rewrite (Ptrofs.unsigned_repr off).
  rewrite <- initialize.max_unsigned_modulus in H0.
  rewrite Ptrofs.unsigned_repr; trivial. omega.
  split; try omega.
  2: destruct (Ptrofs.unsigned_range i); try omega.
  rewrite Ptrofs.unsigned_repr; trivial.
  rewrite <- initialize.max_unsigned_modulus in H0. omega.
  rewrite (Ptrofs.unsigned_repr off); trivial.
  2: destruct (Ptrofs.unsigned_range i); try omega.
  rewrite Ptrofs.unsigned_repr; trivial.
  rewrite <- initialize.max_unsigned_modulus in H0. omega.
Qed.

Lemma offset_in_range_offset_val' n off v:
      offset_in_range (Ptrofs.unsigned off) v ->
      offset_in_range ((Ptrofs.unsigned off)+1) v ->
      offset_in_range n (offset_val off v) =
      offset_in_range (n+Ptrofs.unsigned off) v.
intros.
  destruct v; trivial. unfold offset_in_range, offset_val in *.
  rewrite  (Z.add_comm n), Z.add_assoc in *.
  rewrite Ptrofs.add_unsigned.
  rewrite Ptrofs.unsigned_repr; trivial.
  rewrite <- initialize.max_unsigned_modulus in H0. omega.
Qed.
*)(*
Lemma offset_in_range_offset_val z1 z2 v
        (Z1: 0 <= z1) (Z2: 0 <= z2)
        (Off : offset_in_range (z1 + z2) v):
     offset_in_range z2 (offset_val (Ptrofs.repr z1) v).
Proof.
  unfold offset_val, offset_in_range in *. destruct v; trivial.
  split. apply Z.add_nonneg_nonneg; trivial. apply Ptrofs.unsigned_range.
  apply Arith_aux1. omega.
Qed.
*)
Lemma offset_in_range_offset_val z1 z2 v
        (Z1: 0 <= z1) (Z2: 0 <= z2)
        (Off : offset_in_range (z1 + z2) v):
     offset_in_range z2 (offset_val z1 v).
Proof.
  unfold offset_val, offset_in_range in *. destruct v; trivial.
  split. apply Z.add_nonneg_nonneg; trivial. apply Ptrofs.unsigned_range.
  apply Arith_aux1. omega.
Qed.

Lemma sizeof_Zlength_nonneg {A} {ge: composite_env} t (d:list A): 0 <= sizeof t * Zlength d.
  specialize (Zlength_nonneg d). specialize (sizeof_pos t); intros.
  apply Z.mul_nonneg_nonneg; omega.
Qed.
(*
Lemma data_at_ext {cs} sh t v v' p: v=v' -> @data_at cs sh t v p |-- @data_at cs sh t v' p.
Proof. intros; subst. trivial. Qed.

Lemma data_at_ext_derives {cs} sh t v v' p q: v=v' -> p=q -> @data_at cs sh t v p |-- @data_at cs sh t v' q.
Proof. intros; subst. trivial. Qed.

Lemma data_at_ext_eq {cs} sh t v v' p q: v=v' -> p=q -> @data_at cs sh t v p = @data_at cs sh t v' q.
Proof. intros; subst. trivial. Qed.

(*From sha_lemmas, but repeated here to avoid specialization to sha.CompSpecs*)
Lemma data_at_type_changable {cs}: forall (sh: Share.t) (t1 t2: type) v1 v2,
  t1 = t2 ->
  JMeq v1 v2 ->
  @data_at cs sh t1 v1 = data_at sh t2 v2.
Proof.
  intros.
  subst. apply JMeq_eq in H0. subst v2. reflexivity.
Qed.

Lemma split2_data_at_Tarray_at_tuchar_unfold {cs} sh n n1 v p: 0 <= n1 <= n ->
  @data_at cs sh (Tarray tuchar n noattr) v p |--
  (@data_at cs sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
   at_offset (@data_at cs sh (Tarray tuchar (n - n1) noattr) (sublist n1 (Zlength v) v)) n1 p)%logic.
Proof.
  rewrite data_at_isptr at 1.
  unfold data_at at 1. intros; simpl; normalize.
  erewrite (field_at_Tarray sh  (Tarray tuchar n noattr) _ tuchar); try reflexivity; trivial. 2: omega.
  rewrite (split2_array_at sh (Tarray tuchar n noattr) nil 0 n1); trivial.
  do 2 rewrite array_at_data_at. entailer.
  do 3 rewrite at_offset_eq. rewrite Zminus_0_r.
  erewrite (data_at_type_changable sh
            (nested_field_array_type (Tarray tuchar n noattr) [] 0 n1)
            (Tarray tuchar n1 noattr) _ (sublist 0 n1 v)).
  2: unfold nested_field_array_type; simpl; rewrite Zminus_0_r; trivial.
  2: apply JMeq_refl.
  erewrite (data_at_type_changable sh
            (nested_field_array_type (Tarray tuchar n noattr) [] n1 n)
            (Tarray tuchar (n - n1) noattr) _  (sublist n1 (Zlength v) v)).
  2: unfold nested_field_array_type; simpl; trivial.
  2: apply JMeq_refl.
  simpl.
  rewrite isptr_offset_val_zero, Zplus_0_l, Zmult_1_l; trivial.
Qed.
Lemma split2_data_at_Tarray_at_tuchar_unfold_with_fc {cs} sh n n1 v p: 0 <= n1 <= n ->
  @data_at cs sh (Tarray tuchar n noattr) v p |--
  !!(field_compatible (Tarray tuchar n noattr) [] p) &&
  (@data_at cs sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
   at_offset (@data_at cs sh (Tarray tuchar (n - n1) noattr) (sublist n1 (Zlength v) v)) n1 p)%logic.
Proof.
  intros. apply andp_right. entailer.
  apply split2_data_at_Tarray_at_tuchar_unfold; trivial.
Qed.

Lemma array_at_data_at1 {cs} : forall sh t gfs lo hi v p,
   field_compatible0 t (gfs SUB lo) p ->
   field_compatible0 t (gfs SUB hi) p ->
  @array_at cs sh t gfs lo hi v p =
  at_offset (@data_at cs sh (nested_field_array_type t gfs lo hi)
                (@fold_reptype _ (nested_field_array_type t gfs lo hi)  v))
               (nested_field_offset2 t (ArraySubsc lo :: gfs)) p.
Proof.
  intros. rewrite array_at_data_at. unfold at_offset. apply pred_ext; entailer.
Qed.

Lemma split2_data_at_Tarray_at_tuchar_fold {cs} sh n n1 v p: 0 <= n1 <= n -> n = Zlength v -> n < Int.modulus ->
   field_compatible (Tarray tuchar n noattr) [] p ->
  (@data_at cs sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
   at_offset (@data_at cs sh (Tarray tuchar (n - n1) noattr) (sublist n1 (Zlength v) v)) n1 p)%logic
|--
  @data_at cs sh (Tarray tuchar n noattr) v p.
Proof. intros.
  rewrite data_at_isptr at 1. unfold at_offset. intros; normalize.
  rewrite (data_at_isptr sh (Tarray tuchar (n - n1) noattr) (sublist n1 (Zlength v) v) (offset_val (Int.repr n1) p)).
  unfold data_at at 3. normalize.
  erewrite (field_at_Tarray sh  (Tarray tuchar n noattr) _ tuchar); try reflexivity; trivial. 2: omega.
  rewrite (split2_array_at sh (Tarray tuchar n noattr) nil 0 n1); trivial.
  do 2 rewrite array_at_data_at. entailer. unfold at_offset. simpl.
  rewrite Zplus_0_l, Zmult_1_l.
(*  assert_PROP (field_compatible (Tarray tuchar (Zlength v) noattr) [] p).
    clear H5 H8 H7 H11 H0 H10. apply prop_right. unfold field_compatible in *. intuition.
    unfold legal_alignas_type, nested_pred, local_legal_alignas_type in *; simpl in *.
      rewrite Zle_imp_le_bool; trivial. omega.
    unfold sizeof; simpl. rewrite Z.max_r. 2: omega.
    assert (N: match Zlength v with | 0 => 0 | Z.pos y' => Z.pos y' | Z.neg y' => Z.neg y' end = Zlength v). destruct (Zlength v); trivial.
    rewrite N. omega.
    unfold size_compatible. destruct p; try contradiction; simpl. rewrite Z.max_r. 2: omega.
    assert (N: match Zlength v with | 0 => 0 | Z.pos y' => Z.pos y' | Z.neg y' => Z.neg y' end = Zlength v). destruct (Zlength v); trivial.
    rewrite N. omega.
    assert (N: match n with | 0 => 0 | Z.pos y' => Z.pos y' | Z.neg y' => Z.neg y' end = n). destruct n; trivial.
    rewrite N. simpl in *. omega. reflexivity. Zleb_true. reflexivity.*)
  apply andp_right. apply prop_right.
    split. eapply field_compatible0_cons_Tarray. reflexivity. trivial. omega.
    split. eapply field_compatible0_cons_Tarray. reflexivity. trivial. omega.
    split. eapply field_compatible0_cons_Tarray. reflexivity. trivial. omega.
    eapply field_compatible0_cons_Tarray. reflexivity. trivial. omega.
  rewrite Zminus_0_r.
  erewrite (data_at_type_changable sh
            (nested_field_array_type (Tarray tuchar (Zlength v) noattr) [] 0 n1)
            (Tarray tuchar n1 noattr) _ (sublist 0 n1 v)).
  2: unfold nested_field_array_type; simpl; rewrite Zminus_0_r; trivial.
  2: apply JMeq_refl.
  erewrite <- (data_at_type_changable sh
            (nested_field_array_type (Tarray tuchar (Zlength v) noattr) [] n1 (Zlength v))
            (Tarray tuchar (Zlength v - n1) noattr) _  (sublist n1 (Zlength v) v)).
  2: unfold nested_field_array_type; simpl; trivial.
  2: apply JMeq_refl.
  rewrite isptr_offset_val_zero; trivial.
Qed.

Lemma split2_data_at_Tarray_at_tuchar {cs} sh n n1 v p: 0 <= n1 <= n -> n = Zlength v -> n < Int.modulus ->
   field_compatible (Tarray tuchar n noattr) [] p ->
@data_at cs sh (Tarray tuchar n noattr) v p
= (@data_at cs sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
   at_offset (@data_at cs sh (Tarray tuchar (n - n1) noattr) (sublist n1 (Zlength v) v)) n1 p)%logic.
Proof. intros. apply pred_ext.
  apply (split2_data_at_Tarray_at_tuchar_unfold sh n n1); trivial.
  apply (split2_data_at_Tarray_at_tuchar_fold sh n n1); trivial.
Qed.

Lemma append_split2_data_at_Tarray_at_tuchar {cs} sh n data1 data2 p: Zlength (data1++data2) < Int.modulus ->
   n = Zlength (data1++data2) ->
   field_compatible (Tarray tuchar n noattr) [] p ->
@data_at cs sh (Tarray tuchar n noattr) (data1++data2) p
= (@data_at cs sh (Tarray tuchar (Zlength data1) noattr) data1 p *
   at_offset (@data_at cs sh (Tarray tuchar (Zlength data2) noattr) data2) (Zlength data1) p)%logic.
Proof. intros. subst n.
  specialize (Zlength_nonneg data1).  specialize (Zlength_nonneg data2). intros.
  erewrite (split2_data_at_Tarray_at_tuchar sh _ (Zlength data1)); rewrite Zlength_app in *; try omega; trivial.
  rewrite (sublist0_app1 (Zlength data1)); try omega.
  rewrite sublist_same; trivial.
  rewrite sublist_app2; try omega.
  rewrite Zminus_diag, Z.add_simpl_l.
  rewrite sublist_same; trivial.
Qed.

(*
Lemma split_offset_Tarray_at cs:
  forall n sh t len (contents: reptype (Tarray t len noattr)) v,
  legal_alignas_type t = true ->
  (Z.of_nat n <= Zlength contents)%Z ->
  (Z.of_nat n <= len)%Z ->
  @data_at cs sh (Tarray t len noattr) contents v =
  (!! (offset_in_range (sizeof t * 0) v) &&
   !! (offset_in_range (sizeof t * len) v) &&
  (data_at sh (Tarray t (Z.of_nat n) noattr) (firstn n contents) v *
    data_at sh (Tarray t (len- Z.of_nat n) noattr) (skipn n contents) (offset_val (Int.repr (sizeof t * Z.of_nat n)) v)))%logic.
Proof. apply split_offset_array_at. Qed.
*)
(*
split3seg_array_at:
  forall (cs : compspecs) (sh : Share.t) (t : type) (gfs : list gfield)
    (lo ml mr hi : Z) (v : list (reptype (nested_field_type2 t (gfs SUB 0))))
    (p : val),
  lo <= ml ->
  ml <= mr ->
  mr <= hi ->
  Zlength v = hi - lo ->
  array_at sh t gfs lo hi v p =
  array_at sh t gfs lo ml (sublist 0 (ml - lo) v) p *
  array_at sh t gfs ml mr (sublist (ml - lo) (mr - lo) v) p *
  array_at sh t gfs mr hi (sublist (mr - lo) (hi - lo) v) p
split3_array_at:
  forall (cs : compspecs) (sh : Share.t) (t : type) (gfs : list gfield)
    (lo mid hi : Z) (v : list (reptype (nested_field_type2 t (gfs SUB 0))))
    (v0 : reptype (nested_field_type2 t (gfs SUB mid))) (p : val),
  lo <= mid < hi ->
  Zlength v = hi - lo ->
  JMeq v0
    (Znth (mid - lo) v (default_val (nested_field_type2 t (gfs SUB 0)))) ->
  array_at sh t gfs lo hi v p =
  array_at sh t gfs lo mid (sublist 0 (mid - lo) v) p *
  field_at sh t (gfs SUB mid) v0 p *
  array_at sh t gfs (mid + 1) hi (sublist (mid + 1 - lo) (hi - lo) v) p*)

Lemma split3_data_at_Tarray_at_tuchar_unfold {cs} sh n lo hi v p:
  0 <= lo <= hi -> hi <= n <= Zlength v ->
  @data_at cs sh (Tarray tuchar n noattr) v p |--
  (@data_at cs sh (Tarray tuchar lo noattr) (sublist 0 lo v) p *
   at_offset (@data_at cs sh (Tarray tuchar (hi - lo) noattr) (sublist lo hi v)) lo p *
   at_offset (@data_at cs sh (Tarray tuchar (n - hi) noattr) (sublist hi (Zlength v) v)) hi p)%logic.
Proof. intros.
  eapply derives_trans.
  apply (split2_data_at_Tarray_at_tuchar_unfold sh n hi); try omega.
  cancel.
  eapply derives_trans.
  apply (split2_data_at_Tarray_at_tuchar_unfold sh hi lo); trivial.
  rewrite sublist_sublist; repeat rewrite Zplus_0_r; try omega. cancel.
  rewrite Zlength_sublist; try omega. rewrite sublist_sublist; try rewrite Zminus_0_r; try omega.
    repeat rewrite Zplus_0_r. cancel.
Qed.
Lemma split3_data_at_Tarray_at_tuchar_unfold' {cs} sh n n1 n2 v p:
  n2 + n1 <= n <= Zlength v-> 0<= n1 -> 0<= n2 ->
  @data_at cs sh (Tarray tuchar n noattr) v p |--
  (@data_at cs sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
   at_offset (@data_at cs sh (Tarray tuchar n2 noattr) (sublist n1 (n2 + n1) v)) n1 p *
   at_offset (@data_at cs sh (Tarray tuchar (Zlength v - (n2 + n1)) noattr) (sublist (n2 + n1) (Zlength v) v)) (n2 + n1)  p)%logic.
Proof. intros.
  assert_PROP (Zlength v = Z.max 0 n). entailer. rewrite Z.max_r in H2. 2: omega.
  eapply derives_trans.
  apply (split3_data_at_Tarray_at_tuchar_unfold sh n n1 (n2+n1)); try omega. subst n.
  repeat rewrite sepcon_assoc; rewrite <- Z.add_sub_assoc, Zminus_diag, Zplus_0_r. cancel.
Qed.

Lemma split3_data_at_Tarray_at_tuchar_fold {cs} sh n lo hi v p:
  0 <= lo <= hi -> hi <= n -> n = Zlength v -> n < Int.modulus ->
  field_compatible (Tarray tuchar n noattr) [] p ->
(@data_at cs sh (Tarray tuchar lo noattr) (sublist 0 lo v) p *
   at_offset (@data_at cs sh (Tarray tuchar (hi - lo) noattr) (sublist lo hi v)) lo p *
   at_offset (@data_at cs sh (Tarray tuchar (n - hi) noattr) (sublist hi (Zlength v) v)) hi p)%logic
|--
  @data_at cs sh (Tarray tuchar n noattr) v p.
Proof. intros. subst n.
  assert_PROP (isptr p). entailer. rename H1 into Pp.
  eapply derives_trans. Focus 2.
  apply (split2_data_at_Tarray_at_tuchar_fold sh (Zlength v) lo); trivial. omega.
  cancel.
  unfold at_offset at 3.
  eapply derives_trans.
  2: apply (split2_data_at_Tarray_at_tuchar_fold sh (Zlength v - lo) (hi - lo)).
  repeat rewrite sublist_sublist; try rewrite Zlength_sublist; try omega.
  repeat rewrite Z.sub_simpl_r, Zplus_0_r.
  unfold at_offset. cancel.
  rewrite offset_offset_val, add_repr.
  assert (N: Zlength v - lo - (hi - lo) = Zlength v - hi) by omega. rewrite N; clear N.
  assert (N: lo + (hi - lo) = hi) by omega. rewrite N; clear N.
  assert (N: Zlength v - lo + lo = Zlength v) by omega.  rewrite N; clear N.
  assert (N: hi - lo + lo = hi) by omega.  rewrite N; clear N. cancel.
  omega. rewrite Zlength_sublist; try omega. omega. unfold offset_val.
  destruct p; try contradiction.
  red. simpl. red in H3. simpl in *; intuition.
  unfold legal_alignas_type, nested_pred, local_legal_alignas_type in *. simpl in *.
  rewrite Zle_imp_le_bool. trivial. omega.
  rewrite Zmult_1_l, Z.max_r; omega.
  rewrite Zmult_1_l, Z.max_r in *; try omega.
  destruct (Int.unsigned_add_either i (Int.repr lo)) as [X | X]; rewrite X, (Int.unsigned_repr lo); clear X; try omega.
  rewrite <- max_unsigned_modulus in *; omega.
  rewrite <- max_unsigned_modulus in *; omega.
Qed.
Lemma split3_data_at_Tarray_at_tuchar_fold' {cs} sh n n1 n2 v p:
  n2 + n1 <= n -> 0<= n1 -> 0<= n2 ->
  n=Zlength v -> n < Int.modulus ->
  field_compatible (Tarray tuchar n noattr) [] p ->
(@data_at cs sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
   at_offset (@data_at cs sh (Tarray tuchar n2 noattr) (sublist n1 (n2 + n1) v)) n1 p *
   at_offset (@data_at cs sh (Tarray tuchar (Zlength v - (n2 + n1)) noattr) (sublist (n2+n1) (Zlength v) v)) (n2+n1) p)%logic
|--
  @data_at cs sh (Tarray tuchar n noattr) v p.
Proof. intros.
  eapply derives_trans.
  2: apply (split3_data_at_Tarray_at_tuchar_fold sh n n1 (n2+n1)); trivial; try omega.
  assert (N: n2 + n1 - n1 = n2) by omega. rewrite N; clear N. subst n. cancel.
Qed.

Lemma split3_data_at_Tarray_at_tuchar {cs} sh n n1 n2 v p:
  n2 + n1 <= n -> 0<= n1 -> 0<= n2 ->
  n=Zlength v -> n < Int.modulus ->
  field_compatible (Tarray tuchar n noattr) [] p ->
@data_at cs sh (Tarray tuchar n noattr) v p =
(@data_at cs sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
   at_offset (@data_at cs sh (Tarray tuchar n2 noattr) (sublist n1 (n2 + n1) v)) n1 p *
   at_offset (@data_at cs sh (Tarray tuchar (Zlength v - (n2 + n1)) noattr) (sublist (n2+n1) (Zlength v) v)) (n2+n1) p)%logic.
Proof. intros. apply pred_ext.
  apply (split3_data_at_Tarray_at_tuchar_unfold' sh n n1 n2); trivial. subst n; trivial. clear - H. omega.
  apply (split3_data_at_Tarray_at_tuchar_fold' sh n n1 n2); trivial.
Qed.

Lemma append_split3_data_at_Tarray_at_tuchar {cs} sh n data1 data2 data3 p:
   n = Zlength (data1++data2++data3) ->
   n < Int.modulus ->
   field_compatible (Tarray tuchar n noattr) [] p ->
@data_at cs sh (Tarray tuchar n noattr) (data1++data2++data3) p
= (@data_at cs sh (Tarray tuchar (Zlength data1) noattr) data1 p *
   at_offset (@data_at cs sh (Tarray tuchar (Zlength data2) noattr) data2) (Zlength data1) p *
   at_offset (@data_at cs sh (Tarray tuchar (Zlength data3) noattr) data3) (Zlength data2 + Zlength data1) p)%logic.
Proof. intros.
  specialize (Zlength_nonneg data1). specialize (Zlength_nonneg data2). specialize (Zlength_nonneg data3). intros.
  rewrite (split3_data_at_Tarray_at_tuchar sh n (Zlength data1) (Zlength data2)); try omega; trivial.
  rewrite (sublist0_app1 (Zlength data1)); try omega. rewrite sublist_same; trivial.
  rewrite sublist_app2; try omega. rewrite Zminus_diag. rewrite Z.add_simpl_r.
  rewrite (sublist0_app1 (Zlength data2)); try omega. rewrite sublist_same; trivial.
  repeat rewrite Zlength_app; try omega.
  assert (N1: Zlength data1 + (Zlength data2 + Zlength data3) -
            (Zlength data2 + Zlength data1) =  Zlength data3). omega.
  rewrite N1.
  rewrite sublist_app2; try omega.
  rewrite sublist_app2; try omega.
  assert (N2: Zlength data2 + Zlength data1 - Zlength data1 - Zlength data2 = 0). omega.
  rewrite N2.
  assert (N3: Zlength data1 + (Zlength data2 + Zlength data3) - Zlength data1 -
         Zlength data2 = Zlength data3). omega.
  rewrite N3. rewrite sublist_same; trivial.
  do 2 rewrite Zlength_app in H. omega.
Qed.

Lemma append_split3_data_at_Tarray_at_tuchar' {cs} sh data data1 data2 data3 p:
   data = data1++data2++data3 ->
   Zlength data < Int.modulus ->
   field_compatible (Tarray tuchar (Zlength data) noattr) [] p ->
@data_at cs sh (Tarray tuchar (Zlength data) noattr) data p
= (@data_at cs sh (Tarray tuchar (Zlength data1) noattr) data1 p *
   at_offset (@data_at cs sh (Tarray tuchar (Zlength data2) noattr) data2) (Zlength data1) p *
   at_offset (@data_at cs sh (Tarray tuchar (Zlength data3) noattr) data3) (Zlength data2 + Zlength data1) p)%logic.
Proof. intros. subst.
  apply append_split3_data_at_Tarray_at_tuchar; trivial.
Qed.
*)
(*
Lemma split3_data_at_Tarray_at_tuchar:
      lo n sh data d
      (N: (lo+n <= length data)%nat):
  data_at sh (Tarray tuchar n noattr) data d = (*
  (!! offset_in_range 0 d &&
   !! offset_in_range (sizeof t * Zlength data) d &&*)
  (data_at sh (tarray t (Z.of_nat lo)) (firstn lo data) d *
  data_at sh (tarray t (Z.of_nat n)) (firstn n (skipn lo data)) (offset_val (Int.repr (sizeof t * Z.of_nat lo)) d) *
  data_at sh (tarray t (Zlength data - Z.of_nat (lo+n)))
             (skipn (lo+n) data)  (offset_val (Int.repr (sizeof t * Z.of_nat (lo+n))) d)))%logic.
Proof.
  fold reptype in *.
  assert (Arith1: Zlength (firstn (lo + n) data) = Z.of_nat (lo + n)).
           repeat rewrite Zlength_correct. rewrite firstn_length, min_l; trivial.
  rewrite split_offset_array_at with (n := (lo + n)%nat); trivial. (* by omega.*)
  rewrite split_offset_array_at with (n := lo) (contents := firstn (lo + n) data); trivial.
    (* by
    (rewrite firstn_length; rewrite Min.min_l by omega; omega).*)
  assert (!!offset_in_range (sizeof t * Zlength data) d |--
    !! offset_in_range (sizeof t * Zlength (firstn (lo + n) data)) d)%logic.
    remember (sizeof t) as ST; normalize; subst ST.
    apply offset_in_range_mid with (lo := 0%Z) (hi := Zlength data); try assumption.
    rewrite !Zlength_correct.
    rewrite firstn_length; rewrite Min.min_l by omega. split; try omega.
    apply inj_le, N.
    rewrite Zmult_0_r.
    unfold offset_in_range; destruct d; auto.
    pose proof Int.unsigned_range i; omega.
  rewrite (add_andp _ _ H) at 2. repeat rewrite Zmult_0_r.
  normalize.
  f_equal. f_equal. rewrite Arith1. apply prop_ext; intuition.
  f_equal.
  f_equal.
  rewrite firstn_firstn. trivial.
  rewrite skipn_firstn. trivial.
  rewrite Nat2Z.inj_add, Zminus_plus; trivial.

  rewrite Arith1. apply inj_le. omega.
  apply inj_le. omega.
  rewrite Zlength_correct. apply inj_le; trivial.
  rewrite Zlength_correct. apply inj_le; trivial.
Qed.

Lemma split3_offset_array_at
      t (A: legal_alignas_type t = true)
      lo n sh data d
      (N: (lo+n <= length data)%nat):
  data_at sh (tarray t (Zlength data)) data d =
  (!! offset_in_range 0 d &&
   !! offset_in_range (sizeof t * Zlength data) d &&
  (data_at sh (tarray t (Z.of_nat lo)) (firstn lo data) d *
  data_at sh (tarray t (Z.of_nat n)) (firstn n (skipn lo data)) (offset_val (Int.repr (sizeof t * Z.of_nat lo)) d) *
  data_at sh (tarray t (Zlength data - Z.of_nat (lo+n)))
             (skipn (lo+n) data)  (offset_val (Int.repr (sizeof t * Z.of_nat (lo+n))) d)))%logic.
Proof.
  fold reptype in *.
  assert (Arith1: Zlength (firstn (lo + n) data) = Z.of_nat (lo + n)).
           repeat rewrite Zlength_correct. rewrite firstn_length, min_l; trivial.
  rewrite split_offset_array_at with (n := (lo + n)%nat); trivial. (* by omega.*)
  rewrite split_offset_array_at with (n := lo) (contents := firstn (lo + n) data); trivial.
    (* by
    (rewrite firstn_length; rewrite Min.min_l by omega; omega).*)
  assert (!!offset_in_range (sizeof t * Zlength data) d |--
    !! offset_in_range (sizeof t * Zlength (firstn (lo + n) data)) d)%logic.
    remember (sizeof t) as ST; normalize; subst ST.
    apply offset_in_range_mid with (lo := 0%Z) (hi := Zlength data); try assumption.
    rewrite !Zlength_correct.
    rewrite firstn_length; rewrite Min.min_l by omega. split; try omega.
    apply inj_le, N.
    rewrite Zmult_0_r.
    unfold offset_in_range; destruct d; auto.
    pose proof Int.unsigned_range i; omega.
  rewrite (add_andp _ _ H) at 2. repeat rewrite Zmult_0_r.
  normalize.
  f_equal. f_equal. rewrite Arith1. apply prop_ext; intuition.
  f_equal.
  f_equal.
  rewrite firstn_firstn. trivial.
  rewrite skipn_firstn. trivial.
  rewrite Nat2Z.inj_add, Zminus_plus; trivial.

  rewrite Arith1. apply inj_le. omega.
  apply inj_le. omega.
  rewrite Zlength_correct. apply inj_le; trivial.
  rewrite Zlength_correct. apply inj_le; trivial.
Qed.

Lemma split3_offset_Tarray_at
      t (A: legal_alignas_type t = true)
      lo n sh data d
      (N: (lo+n <= length data)%nat):
  data_at sh (Tarray t (Zlength data) noattr) data d =
  (!! offset_in_range 0 d &&
   !! offset_in_range (sizeof t * Zlength data) d &&
  (data_at sh (Tarray t (Z.of_nat lo) noattr) (firstn lo data) d *
  data_at sh (Tarray t (Z.of_nat n) noattr) (firstn n (skipn lo data)) (offset_val (Int.repr (sizeof t * Z.of_nat lo)) d) *
  data_at sh (Tarray t (Zlength data - Z.of_nat (lo+n)) noattr)
             (skipn (lo+n) data)  (offset_val (Int.repr (sizeof t * Z.of_nat (lo+n))) d)))%logic.
Proof. apply split3_offset_array_at; trivial. Qed.
*)(*
Lemma append_split_Tarray_at:
  forall d t (data1 data2 data :list (reptype t)) sh,
  legal_alignas_type t = true ->
  data1 ++ data2 = data ->
  data_at sh (Tarray t (Zlength data) noattr) data d =
  (!! offset_in_range (sizeof t * 0) d &&
   !! offset_in_range (sizeof t * (Zlength data)) d &&
  (data_at sh (Tarray t (Zlength data1) noattr) data1 d *
   data_at sh (Tarray t (Zlength data2) noattr) data2
             (offset_val (Int.repr (sizeof t * Zlength data1)) d)))%logic.
intros. subst.
rewrite (split_offset_Tarray_at (length data1) sh t (Zlength (data1++data2))
         (data1 ++ data2) d H); repeat rewrite Zlength_correct.
rewrite firstn_exact, skipn_exact; trivial.
rewrite app_length, Nat2Z.inj_add, Z.add_simpl_l; trivial.
rewrite app_length, Nat2Z.inj_add. omega.
rewrite app_length, Nat2Z.inj_add. omega.
Qed.

Lemma append_split3_Tarray_at
      t (data1 data2 data3 data :list (reptype t)) sh
      (A: legal_alignas_type t = true)
      (APP: data1 ++ data2 ++ data3 = data) d:
  data_at sh (Tarray t (Zlength data) noattr) data d =
  (!! offset_in_range 0 d &&
   !! offset_in_range (sizeof t * (Zlength data)) d &&
  (data_at sh (Tarray t (Zlength data1) noattr) data1 d *
   data_at sh (Tarray t (Zlength data2) noattr) data2
             (offset_val (Int.repr (sizeof t * Zlength data1)) d) *
   data_at sh (Tarray t (Zlength data3) noattr) data3
             (offset_val (Int.repr (sizeof t * (Zlength data1 + Zlength data2))) d)))%logic.
Proof.
  subst.
  erewrite (split3_offset_Tarray_at t A (length data1) (length data2)).
  2: repeat rewrite app_length; omega.
  rewrite firstn_exact; trivial.
  rewrite skipn_exact; trivial.
  rewrite firstn_exact; trivial.
  rewrite app_assoc, skipn_app2. 2: rewrite app_length; omega.
  assert (Arith1: (length data1 + length data2 - (length data1 + length data2) = 0)%nat) by omega.
  f_equal. repeat rewrite Zlength_correct. repeat rewrite app_length.
  rewrite Arith1; clear Arith1. simpl.
  f_equal. repeat rewrite Nat2Z.inj_add. rewrite Z.mul_add_distr_l.
  assert (Arith: Z.of_nat (length data1) + Z.of_nat (length data2) +
      Z.of_nat (length data3) -
      (Z.of_nat (length data1) + Z.of_nat (length data2)) = Z.of_nat (length data3)). omega.
  rewrite Arith; clear Arith; trivial.
Qed.
*)

Definition Select_at {cs} sh n (data2: list val) d :=
   @data_at cs sh (Tarray tuchar (Zlength data2) noattr) data2
             (offset_val n d).

Definition Unselect_at {cs} sh (data1 data2 data3: list val) d :=
  (@data_at cs sh (Tarray tuchar (Zlength data1) noattr) data1 d *
   @data_at cs sh (Tarray tuchar (Zlength data3) noattr) data3
             (offset_val (Zlength data2 + Zlength data1) d)).

Lemma Select_Unselect_Tarray_at {cs} l d sh (data1 data2 data3 data: list val)
  (DATA: (data1 ++ data2 ++ data3) = data)
  (L: l = Zlength data)
  (F: @field_compatible cs (Tarray tuchar (Zlength (data1 ++ data2 ++ data3)) noattr) [] d)
  (ZL: Zlength (data1 ++ data2 ++ data3) < Int.modulus):
  @data_at cs sh (Tarray tuchar l noattr) data d =
  @Select_at cs sh (Zlength data1) data2 d * @Unselect_at cs sh data1 data2 data3 d.
Proof.
  subst l. subst data.
  specialize (Zlength_nonneg data1). intros.
  specialize (Zlength_nonneg data2). intros.
  specialize (Zlength_nonneg data3). intros.
  rewrite split3_data_at_Tarray_tuchar with (n1:=Zlength data1)(n2:=Zlength data2 +Zlength data1); try omega.
Locate split3_data_at_Tarray_tuchar.
  autorewrite with sublist.
  unfold Select_at, Unselect_at. simpl.
  unfold offset_val. red in F. destruct d; intuition.
  rewrite field_address0_offset. simpl.
  rewrite field_address0_offset. simpl.
  rewrite (sepcon_comm (data_at sh (Tarray tuchar (Zlength data2) noattr) data2
  (Vptr b (Ptrofs.add i (Ptrofs.repr (Zlength data1)))))).
  repeat rewrite sepcon_assoc.
  f_equal. repeat rewrite Z.mul_1_l. rewrite sepcon_comm. f_equal.
  repeat rewrite Zlength_app in *.
  red; simpl. intuition; try omega.
  repeat rewrite Zlength_app in *.
  red; simpl. intuition; try omega.
  repeat rewrite Zlength_app in *. omega.
Qed.