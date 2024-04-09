From compcert Require Import common.AST cfrontend.Ctypes cfrontend.Clight.
Import Cop.
Require Import VST.floyd.base2.
Require Import VST.floyd.functional_base.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.compare_lemmas.
Require Import VST.floyd.nested_pred_lemmas.
Require Import VST.floyd.nested_field_lemmas.
Require Import VST.floyd.efield_lemmas.
Require Import VST.floyd.mapsto_memory_block.
Require Import VST.floyd.aggregate_type.
Require VST.floyd.aggregate_pred. Import floyd.aggregate_pred.aggregate_pred.
Require Import VST.floyd.reptype_lemmas.
Require Import VST.floyd.simpl_reptype.
Require Import VST.floyd.data_at_rec_lemmas.
Require Import VST.floyd.field_at.
Require Import VST.floyd.field_at_wand.
Require Import VST.floyd.field_compat.
Require Import VST.floyd.stronger.
Require Import VST.floyd.proj_reptype_lemmas.
Require Import VST.floyd.replace_refill_reptype_lemmas.
Require Import VST.floyd.unfold_data_at.
Require Import VST.floyd.entailer.
Require Import VST.floyd.go_lower.
Import ListNotations.

Local Unset SsrRewrite.

Lemma 
  sbyte_ubyte_convert:
  forall i j, 
  Int.sign_ext 8 (Int.repr (Byte.unsigned i)) = Int.repr (Byte.signed j) <->
  Int.zero_ext 8 (Int.repr (Byte.unsigned i)) = Int.repr (Byte.unsigned j).
Proof.
intros.
rewrite Int.zero_ext_and by computable.
simpl.
normalize.
transitivity (Z.land (Byte.unsigned i) 255 = Byte.unsigned j).
2:{
split; intro. f_equal; auto.
apply repr_inj_unsigned; auto.
split. apply Z.land_nonneg; rep_lia.
change 255 with (Z.ones 8).
rewrite (Z.land_ones (Byte.unsigned i) 8 ) by computable.
pose proof (Z_mod_lt (Byte.unsigned i) (2^8)).
spec H0.
compute; auto.
change (2^8) with 256 in *. rep_lia.
rep_lia.
}
change 255 with (Z.ones 8).
rewrite Z.land_ones_low; try rep_lia.
2:{
pose proof (Z.log2_le_mono (Byte.unsigned i) 255).
simpl in H.
spec H; rep_lia.
}
split; intro.
-
apply Z.bits_inj.
intro n.
destruct (zlt n 0).
rewrite !Z.testbit_neg_r by auto. auto.
destruct (zlt n 8).
2:{
assert (forall k, Z.log2 (Byte.unsigned k) < n).
intro. assert (Byte.unsigned k <= 255) by rep_lia.
apply Z.log2_le_mono in H0. simpl in H0. lia.
rewrite Z.bits_above_log2 by (auto; rep_lia).
rewrite Z.bits_above_log2 by (auto; rep_lia).
auto.
}
apply (f_equal (fun i => Int.testbit i n)) in H.
rewrite Int.bits_sign_ext in H by (change Int.zwordsize with 32; lia).
rewrite if_true in H by auto.
rewrite !Int.testbit_repr in H by (change Int.zwordsize with 32; lia).
rewrite H; clear H.
rewrite Byte.bits_signed by lia.
rewrite if_true by auto.
reflexivity.
-
rewrite H.
clear H.
apply Int.same_bits_eq; intros n  ?.
change Int.zwordsize with 32 in H.
rewrite Int.bits_sign_ext by (auto; computable).
if_tac.
rewrite !Int.testbit_repr by auto.
rewrite Byte.bits_signed by lia.
rewrite if_true by auto.
reflexivity.
rewrite !Int.testbit_repr by (change Int.zwordsize with 32; lia).
rewrite Byte.bits_signed by lia.
rewrite if_false by auto.
reflexivity.
Qed.

Module M.
Import VST.veric.base.

Section mpred.

Context `{!VSTGS OK_ty Σ}.

Lemma address_mapsto_any_sbyte_ubyte:
 forall sh b z,
 (∃ v2' : val, address_mapsto Mint8signed v2' sh (b, z)) ⊣⊢
 (∃ v2' : val, address_mapsto Mint8unsigned v2' sh (b, z)).
Proof.
intros.
apply bi.equiv_entails_2;
[pose (f := Byte.unsigned) | pose (f := Byte.signed)];
apply bi.exist_elim; intro v;
pose (v' := match v with Vint j => Vint (Int.repr (f (Byte.repr (Int.unsigned j))))
  | _ => Vundef
end);
rewrite <- (bi.exist_intro v');
unfold address_mapsto;
apply bi.exist_elim; intro bl;
rewrite <- (bi.exist_intro bl);
apply bi.pure_elim_l; intros [? [? ?]];
destruct bl as [| ? [|]]; try solve [inv H];
(rewrite <- prop_and_same_derives'; [auto | 
  split3; auto; unfold decode_val in *; destruct m; subst v v' f; simpl in *; auto;
   unfold decode_int; rewrite rev_if_be_singleton; simpl; rewrite Z.add_0_r;
   f_equal; clear
  ]).
all: assert (Int.zwordsize = 32) by reflexivity;
      assert (Byte.zwordsize = 8) by reflexivity.
all: apply Int.same_bits_eq; intros n ?;
rewrite ?Int.bits_zero_ext by lia;
rewrite ?Int.bits_sign_ext by lia;
rewrite ?Int.testbit_repr by (try if_tac; lia);
rewrite ?Byte.bits_signed by lia;
change (Z.testbit (Byte.unsigned ?A)) with (Byte.testbit A);
rewrite ?Byte.testbit_repr by (try if_tac; lia);
rewrite ?H0; if_tac;
rewrite ?Byte.testbit_repr by (try if_tac; lia).
rewrite <- Int.testbit_repr by lia; rewrite Int.repr_unsigned.
rewrite Int.bits_sign_ext by lia.
rewrite if_true by lia.
rewrite Int.testbit_repr by lia.
reflexivity.
rewrite Byte.bits_above by lia. auto.
rewrite <- Int.testbit_repr by lia; rewrite Int.repr_unsigned.
rewrite Int.bits_zero_ext by lia.
rewrite if_true by auto.
rewrite Int.testbit_repr by lia.
reflexivity.
rewrite <- Int.testbit_repr by lia; rewrite Int.repr_unsigned.
rewrite Int.bits_zero_ext by lia.
rewrite if_true by lia.
rewrite Int.testbit_repr by lia.
reflexivity.
Qed.

End mpred.

End M.

Arguments deref_noload ty v / .
Arguments nested_field_array_type {cs} t gfs lo hi / .
Arguments nested_field_type {cs} t gfs / .  (* redundant? *)
Arguments nested_field_offset {cs} t gfs / .  (* redundant? *)
Arguments Z.mul !x !y.
Arguments Z.sub !m !n.
Arguments Z.add !x !y.
Global Transparent peq.

Section mpred.

Context `{!VSTGS OK_ty Σ}.

Lemma data_at_tarray_tschar_tuchar {cs: compspecs}:
  forall sh n bytes p,
  data_at sh (tarray tschar n) (map Vbyte bytes) p ⊣⊢ data_at sh (tarray tuchar n) (map Vubyte bytes) p.
Proof.
intros.
unfold data_at, field_at.
f_equiv.
f_equiv.
unfold field_compatible.
simpl.
intuition; destruct p; auto;
hnf in H2|-*;
apply align_compatible_rec_Tarray; intros;
apply align_compatible_rec_Tarray_inv with (i:=i0) in H2; auto;
eapply align_compatible_rec_by_value_inv in H2; try reflexivity;
eapply align_compatible_rec_by_value; try reflexivity;
apply H2.
unfold at_offset.
simpl.
rewrite !data_at_rec_eq.
simpl.
apply array_pred_ext.
change (Zlength (map Vbyte bytes) = Zlength (map Vubyte bytes)).
autorewrite with sublist. auto.
intros.
unfold at_offset.
autorewrite with sublist.
rewrite !data_at_rec_eq; simpl.
do 2 change (unfold_reptype ?A) with A.
change (sizeof tschar) with 1.
change (sizeof tuchar) with 1.
forget (offset_val (1 * i) (offset_val 0 p)) as q.
simpl.
destruct q; auto.
unfold mapsto; simpl.
if_tac; auto.
-
simpl.
f_equiv; auto; [f_equiv; auto | ].
+
f_equiv.
destruct (zlt i (Zlength bytes)).
rewrite !Znth_map by lia.
simpl.
split; intro; 
autorewrite with norm norm1 norm2; rep_lia.
rewrite !Znth_overflow by (autorewrite with sublist; auto).
reflexivity.
+
do 2 change (unfold_reptype ?A) with A.
destruct (zlt i (Zlength bytes)).
2:
 rewrite !Znth_overflow by (autorewrite with sublist; auto);
 unfold res_predicates.address_mapsto; simpl;
 f_equiv; intros bl;
 f_equiv; f_equiv;
 intuition;
 destruct bl as [| ? [|]]; inv H3;
 destruct m; inv H; reflexivity.
autorewrite with sublist.
forget (Znth i bytes) as c.
unfold res_predicates.address_mapsto; simpl.
f_equiv; intros bl.
f_equiv.
f_equiv.
intuition;
 destruct bl as [| ? [|]]; inv H3;
 destruct m; try solve [inv H];
 unfold decode_val, proj_bytes in *;
 unfold Vubyte, Vbyte in *;
  apply Vint_inj in H;
  f_equal; clear - H;
unfold decode_int in *;
rewrite rev_if_be_1 in H|-*;
simpl in H|-*;
rewrite Z.add_0_r in *;
apply sbyte_ubyte_convert; auto.
+
f_equiv; auto.
f_equiv.
repeat change (unfold_reptype ?A) with A.
destruct (zlt i (Zlength bytes)).
autorewrite with sublist.
split; intro Hx; inv Hx.
rewrite !Znth_overflow by (autorewrite with sublist; auto).
split; intro; reflexivity.
clear.
forget (Ptrofs.unsigned i0) as z.
apply M.address_mapsto_any_sbyte_ubyte.
-
f_equiv.
f_equiv.
f_equiv.
unfold tc_val'.
destruct (zlt i (Zlength bytes)).
autorewrite with sublist.
split; intros.
red. simpl. normalize. rep_lia.
red. simpl. normalize. rep_lia.
rewrite !Znth_overflow by (autorewrite with sublist; auto).
split; intros; contradiction H2; auto.
Qed.

Section ArrayPointer.

Context {cs: compspecs}.

(*For simplifying pointer arithmetic*)
Lemma sem_sub_pi_offset: forall ty s off n,
  isptr s ->
  complete_type cenv_cs ty = true ->
  Int.min_signed <= n <= Int.max_signed ->
  force_val (sem_sub_pi ty Signed (offset_val off s) (Vint (Int.repr n))) =
  offset_val (off - (sizeof ty) * n) s.
Proof.
  intros ty s off n Hptr Hty Hn.
  replace (off - (sizeof ty) * n) with (off + (- (sizeof ty) * n)) by lia. rewrite <- offset_offset_val.
  assert (Hptr' : isptr (offset_val off s)). rewrite isptr_offset_val; auto.
  destruct (offset_val off s) eqn : Hoff; inversion Hptr'. simpl.
  unfold sem_sub_pi. rewrite Hty. simpl. f_equal. unfold sizeof.
  assert ((Ptrofs.of_ints (Int.repr n)) = Ptrofs.repr n). unfold Ptrofs.of_ints.
  f_equal. apply Int.signed_repr; auto. rewrite H. rewrite ptrofs_mul_repr.
  rewrite Ptrofs.sub_add_opp. f_equal. replace (- Ctypes.sizeof ty * n) with (-(Ctypes.sizeof ty * n)) by lia.
  rewrite <- (Ptrofs.neg_repr). reflexivity.
Qed.

(** Indexing into arrays **)

Lemma arr_field_compatible0 : forall t size p i, 
  field_compatible (tarray t size) [] p ->
  0 <= i <= size ->
  field_compatible0 (tarray t size) (SUB i) p.
Proof.
  intros t size p i Hcomp Hsz.
  unfold field_compatible in *. unfold field_compatible0. destruct Hcomp as [Hptr [Hleg [Hsz_comp [Hal Hnest]]]].
  repeat(split; auto).
Qed.

Lemma arr_field_address0: forall t size p i, 
  field_compatible (tarray t size) [] p ->
  0 <= i <= size ->
  field_address0 (tarray t size) (SUB i) p = offset_val (sizeof t * i) p.
Proof.
  intros t size p i Hcomp Hi.
  unfold field_address0. destruct (field_compatible0_dec (tarray t size) (SUB i) p).
  simpl. auto. exfalso. apply n. apply arr_field_compatible0; auto.
Qed.

Lemma arr_field_compatible : forall t size p i, 
  field_compatible (tarray t size) [] p ->
  0 <= i < size ->
  field_compatible (tarray t size) (SUB i) p.
Proof.
  intros t size p i Hcomp Hsz.
  unfold field_compatible in *. unfold field_compatible0. destruct Hcomp as [Hptr [Hleg [Hsz_comp [Hal Hnest]]]].
  repeat(split; auto).
Qed.

Lemma arr_field_address: forall t size p i, 
  field_compatible (tarray t size) [] p ->
  0 <= i < size ->
  field_address (tarray t size) (SUB i) p = offset_val (sizeof t * i) p.
Proof.
  intros t size p i Hcomp Hi.
  unfold field_address. destruct (field_compatible_dec (tarray t size) (SUB i) p).
  simpl. auto. exfalso. apply n. apply arr_field_compatible; auto.
Qed.

(*Useful for proving that pointers are valid for conditionals*)
Lemma isptr_denote_tc_test_order: forall p1 p2,
  isptr p1 ->
  isptr p2 ->
  denote_tc_test_order p1 p2 = test_order_ptrs p1 p2.
Proof.
  intros p1 p2 Hptr1 Hptr2. destruct p1; destruct Hptr1. destruct p2; destruct Hptr2. reflexivity.
Qed.

(** Lemmas about [sameblock] *)

Lemma isptr_offset_val_sameblock : forall p i,
  isptr p ->
  sameblock p (offset_val i p) = true.
Proof.
  intros. destruct p; destruct H.
  simpl. unfold proj_sumbool. apply peq_true.
Qed.

Lemma sameblock_refl : forall p,
  isptr p ->
  sameblock p p = true.
Proof.
  intros.
  destruct p; destruct H. apply peq_true.
Qed.

Lemma sameblock_symm : forall p1 p2,
  sameblock p1 p2 = true ->
  sameblock p2 p1 = true.
Proof.
  intros.
  destruct p1; destruct p2; try discriminate.
  simpl in *. destruct (peq b b0); try discriminate.
  subst.
  apply peq_true.
Qed.

Lemma sameblock_trans : forall p1 p2 p3,
  sameblock p1 p2 = true ->
  sameblock p2 p3 = true->
  sameblock p1 p3 = true.
Proof.
  intros.
  destruct p1; try discriminate.
  destruct p2; try discriminate.
  destruct p3; try discriminate.
  simpl in *.
  destruct (peq b b0); try discriminate.
  destruct (peq b0 b1); try discriminate.
  subst.
  apply peq_true.
Qed.

Lemma sameblock_offset_val: forall p n1 n2,
  isptr p ->
  sameblock (offset_val n1 p) (offset_val n2 p) = true.
Proof.
  intros p n1 n2 Hptr. eapply sameblock_trans. eapply sameblock_symm. 
  all: apply isptr_offset_val_sameblock; auto.
Qed.

(** Simplifying Pointer Comparisons *)

(* Suppose there is an array of length s, and 2 pointers to elements in the array n and m, and the
   C expression n > m (in a loop guard or conditional). This gives a long, difficult proof obligation.
   The next few lemmas convert this into something usable. *)

(* > case *)
Lemma ptr_comparison_gt_iff: forall t size p i j,
  field_compatible (tarray t size) [] p ->
  0 <= i <= size ->
  0 <= j <= size ->
  0 < sizeof t ->
  isptr p ->
  typed_true tint (force_val (sem_cmp_pp Cgt (field_address0 (tarray t size) (SUB i) p)
    (field_address0 (tarray t size) (SUB j) p))) <-> i > j.
Proof.
  intros t size p i j Hcomp Hi Hj Hszof Hptr.
  assert (Hptri : isptr (field_address0 (tarray t size) (SUB i) p)).
  apply field_address0_isptr. apply arr_field_compatible0; auto.
  assert (Hptrj: isptr (field_address0 (tarray t size) (SUB j) p)).
  apply field_address0_isptr. apply arr_field_compatible0; auto.
  rewrite force_sem_cmp_pp; auto. unfold compare_pp.
  destruct (field_address0 (tarray t size) (SUB i) p) eqn : Fi; inversion Hptri.
  destruct (field_address0 (tarray t size) (SUB j) p) eqn : Fj; inversion Hptrj.
  clear Hptri Hptrj.
  assert (Hsame: sameblock (Vptr b i0) (Vptr b0 i1) = true). { rewrite <- Fi. rewrite <- Fj.
  rewrite !arr_field_address0; auto. eapply sameblock_trans. apply sameblock_symm.
  all: apply  isptr_offset_val_sameblock; auto. } 
  simpl in Hsame. unfold eq_block. destruct (peq b b0); try inversion Hsame. subst. clear Hsame.
  simpl. rewrite arr_field_address0 in Fi; auto. rewrite arr_field_address0 in Fj; auto.
  destruct p; inversion Hptr. simpl in *. inversion Fi; subst. inversion Fj; subst.
  clear Fi Fj Hptr. unfold Ptrofs.ltu.
  assert (Hi2 : 0 <= Ptrofs.unsigned i2) by rep_lia. unfold field_compatible in Hcomp. 
  destruct Hcomp as [Ht [Hcomp [HHsz Hrest]]]. simpl in HHsz.
  replace (Z.max 0 size) with size in HHsz by lia.
  (*We will use these a bunch of times*)
  assert (Hij: forall k, 0 <= k <= size -> 0 <= sizeof t * k < Ptrofs.modulus). {
    intros k Hk. unfold sizeof in *. split. lia.
    assert (Ctypes.sizeof t * k <= Ctypes.sizeof t * size).  apply Z.mul_le_mono_pos_l; lia.
    assert (Ctypes.sizeof t * size < Ptrofs.modulus) by lia. lia. } 
  assert (Hij' : forall k, 0 <= k <= size ->
      0 <= Ptrofs.unsigned i2 + Ptrofs.unsigned (Ptrofs.repr (sizeof t * k)) < Ptrofs.modulus). {
    intros k Hk. unfold sizeof in *. rewrite Ptrofs.unsigned_repr_eq. rewrite Zmod_small.
    2: apply Hij; lia. split. lia. 
    assert (Ptrofs.unsigned i2 + Ctypes.sizeof t * k <= Ptrofs.unsigned i2 + Ctypes.sizeof t * size).
    apply Zplus_le_compat_l. apply Z.mul_le_mono_nonneg_l; lia. eapply Z.le_lt_trans. apply H. assumption. }
  unfold Ptrofs.unsigned. simpl. rewrite !Ptrofs.Z_mod_modulus_eq. rewrite !Zmod_small.
  all: try apply Hij'; auto.
  destruct (zlt (Ptrofs.unsigned i2 + Ptrofs.unsigned (Ptrofs.repr (sizeof t * j)))
          (Ptrofs.unsigned i2 + Ptrofs.unsigned (Ptrofs.repr (sizeof t * i)))).
    - assert (Hptrlt: Ptrofs.unsigned (Ptrofs.repr (sizeof t * j)) < Ptrofs.unsigned (Ptrofs.repr (sizeof t * i))) by lia.
      clear l. unfold Ptrofs.unsigned in Hptrlt. simpl in Hptrlt. rewrite !Ptrofs.Z_mod_modulus_eq in Hptrlt.
      rewrite !Zmod_small in Hptrlt. rewrite <- Z.mul_lt_mono_pos_l in Hptrlt; auto. all: try apply Hij; auto.
      split; intros; auto. lia. reflexivity.
    - assert (Hptrlt: Ptrofs.unsigned (Ptrofs.repr (sizeof t * i)) <= Ptrofs.unsigned (Ptrofs.repr (sizeof t * j))) by lia.
      clear g. unfold Ptrofs.unsigned in Hptrlt. simpl in Hptrlt. rewrite !Ptrofs.Z_mod_modulus_eq in Hptrlt.
      rewrite !Zmod_small in Hptrlt. rewrite <- Z.mul_le_mono_pos_l in Hptrlt; auto. all: try apply Hij; auto.
      split; intros; try lia. inversion H.
Qed.

(*Switch Cgt and Clt*)
Lemma cgt_clt_ptr: forall p1 p2,
  sem_cmp_pp Cgt p1 p2 = sem_cmp_pp Clt p2 p1.
Proof.
  intros p1 p2. unfold sem_cmp_pp. simpl. f_equal. unfold Val.cmplu_bool.
  destruct p1; destruct p2; auto.
  destruct (Archi.ptr64); auto; simpl;
  destruct (eq_block b b0), (eq_block b0 b); subst; try contradiction;
  reflexivity.
Qed.

(*Same for the lt case. This is an easy corollary of the above 2 lemmas*)
Lemma ptr_comparison_lt_iff: forall t size p i j,
  field_compatible (tarray t size) [] p ->
  0 <= i <= size ->
  0 <= j <= size ->
  0 < sizeof t ->
  isptr p ->
  typed_true tint (force_val (sem_cmp_pp Clt (field_address0 (tarray t size) (SUB i) p)
    (field_address0 (tarray t size) (SUB j) p))) <-> i < j. 
Proof.
  intros t sz p i j Hcompat Hi Hj Ht Hptr. rewrite <- cgt_clt_ptr.
  rewrite ptr_comparison_gt_iff by auto. lia.
Qed.

(** Working with 2D Arrays*)

(*We can consider an instance of t at position p to be a valid array of length 1 at p*)
Lemma data_at_array_len_1: forall sh t a p,
data_at sh t a p ⊢ ⌜field_compatible (tarray t 1) [] p⌝.
Proof.
  intros. erewrite <- data_at_singleton_array_eq. 2: reflexivity. entailer!.
Qed.

(*The crucial lemma for showing the relationship between 1D and 2D arrays: if we shift 1 array (in the 2D array)
  or m places (in the 1D array), the result is still compatible*)
Lemma field_compatible0_1d_2d: forall n m t p,
  0 <= m ->
  0 < n ->
  field_compatible (Tarray t m noattr) [] p ->
  (field_compatible0 (tarray (tarray t m) n)) (SUB 1) p <->
  (field_compatible0 (tarray t (n * m)) (SUB m) p).
Proof.
  intros n m t p Hm Hn Hfst.
  unfold field_compatible in Hfst. unfold field_compatible0.
  simpl in *. destruct Hfst as [Hptr1 [Hleg1 [Hszc1 [Hal1 Hlegn1]]]].
  clear Hlegn1.
  (*The interesting part*)
  assert (size_compatible (tarray (tarray t m) n) p /\ align_compatible (tarray (tarray t m) n) p <->
    size_compatible (tarray t (n * m)) p /\ align_compatible (tarray t (n * m)) p ). {
   unfold size_compatible. destruct p; inversion Hptr1. simpl in *.
    replace (Z.max 0 m) with m by lia.
    replace (Z.max 0 n) with n by lia.
    replace (Z.max 0 (n * m)) with (m * n) by lia.
    rewrite Z.mul_assoc. split; intros [Hszc2 Hal2].
    - split. assumption. inversion Hal2; subst. inversion H.
      inversion Hal1; subst. inversion H.
      apply align_compatible_rec_Tarray. intros j Hj.
      assert (m = 0 \/ m > 0) by lia. destruct H as [H | Hm0]. subst. lia.
      assert (0 <= j < m \/ m <= j < n * m) by lia. destruct H as [Hfst | Hrest].
      + specialize (H4 _ Hfst). apply H4.
      + (*To index into the rest of the array, we need to use j/ m and j %m, which gives lots of annoying proof obligations*)
        assert (0 <= j / m  < n). { split. assert (1 <= j / m). rewrite <- (Z_div_same _ Hm0).
        apply Z_div_le; lia. lia. apply Z.div_lt_upper_bound; lia. }
        specialize (H3 _ H). clear H4. inversion H3; subst. inversion H0.
        assert (0 <= j mod m < m). { apply Z.mod_pos_bound; lia. }
        specialize (H5 _ H0). replace (Ptrofs.unsigned i + Ctypes.sizeof t * j) with
        (Ptrofs.unsigned i + Ctypes.sizeof (tarray t m) * (j / m) + Ctypes.sizeof t * (j mod m)). apply H5.
        rewrite <- !Z.add_assoc. f_equal. simpl Ctypes.sizeof. replace (Z.max 0 m) with m by lia.
        rewrite <- Z.mul_assoc. rewrite <- Z.mul_add_distr_l. f_equal.
        replace (Z.max 0 m) with m by lia.
        rewrite <- Z_div_mod_eq_full. reflexivity.
    - split. assumption. inversion Hal2; subst. inversion H.
      inversion Hal1; subst. inversion H.  apply align_compatible_rec_Tarray. intros j Hj.
      apply align_compatible_rec_Tarray. intros k Hk.
      assert (0 = j \/ 1 <= j) by lia. destruct H as [Hfst | Hrest].
      + subst. rewrite Z.mul_0_r. rewrite Z.add_0_r. apply H4. apply Hk.
      + assert (0 = m \/ 0 < m) by lia. destruct H as [H | Hm0]. lia.
        assert (0 <= j * m + k < n * m). { split; try lia.
        assert (j * m + k < j * m + m) by lia. replace (j * m + m) with ((j+1) * m) in H by lia.
        assert ((j+1) * m <= n * m). apply Zmult_le_compat_r; lia. lia. } 
        specialize (H3 _ H). simpl. replace ( Z.max 0 m ) with m by lia.
        replace (Ptrofs.unsigned i + Ctypes.sizeof t * m * j + Ctypes.sizeof t * k) with 
        (Ptrofs.unsigned i + Ctypes.sizeof t * (j * m + k)). apply H3. rewrite <- !Z.add_assoc. f_equal.
        rewrite <- Z.mul_assoc. rewrite <- Z.mul_add_distr_l. f_equal. lia. }
  split; intros [Hptr2 [Hleg2 [Hszc2 [Hal2 [Hlegn2 Hbound2]]]]].
  repeat(split; auto). apply H. split; auto.
  apply H. split; auto. replace m with (1 * m) at 1 by lia. apply Z.mul_le_mono_nonneg_r; lia.
  repeat(split; auto). apply H. split; auto. apply H; split; auto. lia. lia.
Qed.

Lemma Zlength_concat': forall {A: Type} (n m : Z) (l: list (list A)),
  Zlength l = n ->
  Forall (fun x => Zlength x = m) l ->
  Zlength (concat l) = n * m.
Proof.
  intros A m n l. revert m. induction l; intros.
  - list_solve.
  - simpl. rewrite Zlength_app. rewrite (IHl (m-1)). 2: list_solve.
    assert (Zlength a = n). inversion H0; subst; reflexivity. rewrite H1. lia. inversion H0; auto.
Qed.

(*The full relationship between 1D and 2D arrays*)
Lemma data_at_2darray_concat : forall sh t n m (al : list (list (reptype t))) p,
  Zlength al = n ->
  Forall (fun l => Zlength l = m) al ->
  complete_legal_cosu_type t = true ->
  data_at sh (tarray (tarray t m) n) al p
    ⊣⊢ data_at sh (tarray t (n * m)) (concat al) p.
Proof.
  intros.
  generalize dependent n; generalize dependent p; induction al; intros.
  - simpl. replace n with 0 by list_solve. rewrite Z.mul_0_l.
    apply bi.equiv_entails_2; entailer!; rewrite ?data_at_zero_array_eq; auto;
      apply isptr_field_compatible0_tarray; auto.
  - rewrite Zlength_cons in H. simpl. assert (Hmlen: Zlength a = m) by (inversion H0; subst; reflexivity).
    apply bi.equiv_entails_2.
    + (*We will need these later, when we have transformed the [data_at] predicates, so they are harder to prove*)
      assert_PROP (field_compatible (tarray (tarray t m) (Z.succ (Zlength al))) [] p). { entailer!. }
      assert_PROP (field_compatible0 (tarray (tarray t m) n) (SUB 1) p). { entailer!.
        apply arr_field_compatible0. auto. list_solve. }
      change (a :: al) with ([a] ++ al). 
      change (list (reptype t)) with (reptype (tarray t m)) in a.
      rewrite (split2_data_at_Tarray_app 1 _ _ _ [a]). 2: Zlength_solve.
      change (reptype (tarray t m)) with  (list (reptype t)) in a. 2: { rewrite <- H.
      assert (forall x, x = Z.succ x - 1). intros; lia. apply H4. }
      rewrite (split2_data_at_Tarray_app m).
      replace (n * m - m) with ((n-1) * m) by lia.
      erewrite data_at_singleton_array_eq. 2: reflexivity.
      assert (Hm: 0 <= m). rewrite <- Hmlen. list_solve.
      entailer!. rewrite !field_address0_clarify; auto.
      simpl. unfold sizeof. rewrite <- Z.mul_assoc.
      replace (Z.max 0 (Zlength a) * 1) with (Zlength a) by lia. rewrite IHal. cancel.
      inversion H0; subst; auto. lia. unfold field_address0.
      rewrite field_compatible0_1d_2d in H3.
      destruct (field_compatible0_dec (tarray t (Z.succ (Zlength al) * Zlength a)) [ArraySubsc (Zlength a)] p); [| contradiction].
    apply isptr_is_pointer_or_null; auto. list_solve. list_solve. auto.
    inversion H0; subst; reflexivity.
    rewrite (Zlength_concat' (n-1) m). lia. list_solve. inversion H0; auto.
    + assert_PROP ((field_compatible0 (tarray t (n * m)) [ArraySubsc m] p)). { entailer!.
      apply arr_field_compatible0. apply H2.
       split. list_solve. rewrite <- (Z.mul_1_l (Zlength a)) at 1. apply Z.mul_le_mono_nonneg_r; list_solve. }
      change (a :: al) with ([a] ++ al). 
      change (list (reptype t)) with (reptype (tarray t m)) in a.
      rewrite (split2_data_at_Tarray_app 1 _ _ _ [a]). 2: Zlength_solve.
      change (reptype (tarray t m)) with  (list (reptype t)) in a. 2: { rewrite <- H.
      assert (forall x, x = Z.succ x - 1). intros; lia. apply H3. }
      rewrite (split2_data_at_Tarray_app m). 2: auto.
      replace (n * m - m) with ((n-1) * m) by lia.
      erewrite data_at_singleton_array_eq. 2: reflexivity.
      assert (Hm: 0 <= m). rewrite <- Hmlen. list_solve.
      entailer!. rewrite !field_address0_clarify; auto.
      simpl. unfold sizeof. rewrite <- Z.mul_assoc.
      replace (Z.max 0 (Zlength a) * 1) with (Zlength a) by lia. rewrite IHal. cancel.
      inversion H0; subst; auto. lia. unfold field_address0.
      rewrite <- field_compatible0_1d_2d in H2.
      destruct (field_compatible0_dec (tarray (tarray t (Zlength a)) (Z.succ (Zlength al))) [ArraySubsc 1] p); [| contradiction].
      apply isptr_is_pointer_or_null; auto. list_solve. list_solve. auto.
      rewrite (Zlength_concat' (n-1) m). lia. list_solve. inversion H0; auto.
Qed.

(** Working with Arrays of Pointers **)

(*Represents the fact that there is a list of pointers (ptrs), and the contents of those pointers
  are described by contents - a 2D array with possibly different lengths.
  This definition applies to byte arrays (so we don't need to worry about offsets), but it
  could be extended. *)
Definition iter_sepcon_arrays (ptrs : list val) (contents: list (list byte)) :=
  [∗ list] '(l, ptr) ∈ combine contents ptrs, data_at Ews (tarray tuchar (Zlength l)) (map Vubyte l) ptr.

(* up? *)
Lemma Znth_lookup : forall {A} {I : Inhabitant A} (l : list A) i, 0 <= i < Zlength l -> (l !! (Z.to_nat i))%stdpp = Some (Znth i l).
Proof.
  intros.
  destruct (nth_lookup_or_length l (Z.to_nat i) default) as [-> |].
  - rewrite nth_Znth', Z2Nat.id; tauto.
  - rewrite Zlength_correct in *; lia.
Qed.

Lemma iter_sepcon_arrays_Znth: forall ptrs contents i,
  Zlength ptrs = Zlength contents ->
  0 <= i < Zlength contents ->
  iter_sepcon_arrays ptrs contents ⊢ 
    data_at Ews (tarray tuchar (Zlength (Znth i contents))) (map Vubyte (Znth i contents)) (Znth i ptrs) ∗ True.
Proof.
  intros ptrs contents i Hlen Hi. unfold iter_sepcon_arrays.
  rewrite (big_sepL_lookup_acc _ _ (Z.to_nat i)).
  2: { apply Znth_lookup; rewrite Zlength_combine; lia. }
  rewrite Znth_combine by done.
  cancel.
Qed.

Lemma remove_lead_eq: forall {A: Type} (P: Prop) (x: A),
  (x = x -> P) <-> P.
Proof.
  intros. tauto.
Qed.

Lemma iter_sepcon_arrays_local_facts: forall ptrs contents,
  iter_sepcon_arrays ptrs contents ⊢ ⌜Zlength ptrs = Zlength contents -> 
        forall i, 0 <= i < Zlength contents ->
         field_compatible (tarray tuchar (Zlength (Znth i contents))) [] (Znth i ptrs) /\
         Forall (value_fits tuchar) (map Vubyte (Znth i contents))⌝.
Proof.
  intros ptrs contents.
  iIntros "?" (???).
  rewrite iter_sepcon_arrays_Znth by done.
  iStopProof. entailer!.
Qed.

(*
(*We would also like another, more general fact. For [iter_sepcon] that gives an mpred 
  as well as [iter_sepcon_arrays]), we can remove
  the nth element and keep the rest*)

(*An easier definition than [delete_nth], since it uses Z and there are lots of lemmas/automation about sublist*)
Definition remove_nth {A: Type} (n: Z) (l: list A): list A :=
  sublist 0 n l ++ sublist (n+1) (Zlength l) l.

Lemma iter_sepcon_remove_one: forall {B : Type} `{Inhabitant B} (p: B -> mpred) (l: list B) (n: Z),
  0 <= n < Zlength l ->
  iter_sepcon p l = ((p (Znth n l)) * iter_sepcon p (remove_nth n l))%logic.
Proof.
  intros B Hinhab p l n Hn. unfold remove_nth. rewrite <- (sublist_same 0 (Zlength l) l) at 1 by auto.
  rewrite (sublist_split 0 n (Zlength l) l) by lia.
  rewrite (sublist_split n (n+1) (Zlength l) l) by lia. rewrite !iter_sepcon_app.
  rewrite sublist_len_1 by lia. simpl. apply bi.equiv_entails_2; cancel.
Qed.

Lemma combine_sublist: forall {A B: Type} `{Inhabitant A} `{Inhabitant B} (lo hi : Z) (l1 : list A) (l2: list B),
  Zlength l1 = Zlength l2 ->
  0 <= lo <= hi ->
  hi <= Zlength l1 ->
  combine (sublist lo hi l1) (sublist lo hi l2) = sublist lo hi (combine l1 l2).
Proof.
  intros A B Hinh1 Hinh2 lo hi l1 l2 Hlen Hhilo Hhi.
  assert (Hsublen: Zlength (combine (sublist lo hi l1) (sublist lo hi l2)) = hi - lo). {
   rewrite Zlength_combine by (rewrite !Zlength_sublist; lia). list_solve. }
  apply Znth_eq_ext. rewrite Hsublen. rewrite Zlength_sublist; try lia.
  rewrite Zlength_combine; lia.
  intros i Hi. rewrite Hsublen in Hi. rewrite Znth_combine by list_solve.
  rewrite !Znth_sublist by lia. rewrite Znth_combine by lia. reflexivity.
Qed.

Lemma combine_remove_nth: forall {A B: Type} `{Inhabitant A} `{Inhabitant B} n (l1: list A) (l2: list B),
  Zlength l1 = Zlength l2 ->
  0 <= n < Zlength l1 ->
  combine (remove_nth n l1) (remove_nth n l2) = remove_nth n (combine l1 l2).
Proof.
  intros A B Hinh1 Hinh2 n l1 l2 Hlens Hn.
  unfold remove_nth. rewrite combine_app' by list_solve. rewrite Hlens, !combine_sublist by lia.
  rewrite Zlength_combine by lia. rewrite Hlens, Z.min_id. reflexivity.
Qed.

(* Allows one to extract a single [data_at] from an [iter_sepcon] without losing any information *)
Lemma iter_sepcon_arrays_remove_one: forall ptrs contents i,
  Zlength ptrs = Zlength contents ->
  0 <= i < Zlength contents ->
  iter_sepcon_arrays ptrs contents = 
    (data_at Ews (tarray tuchar (Zlength (Znth i contents))) (map Vubyte (Znth i contents)) (Znth i ptrs) *
    iter_sepcon_arrays (remove_nth i ptrs) (remove_nth i contents))%logic.
Proof.
  intros ptrs contents i Hlens Hi. unfold iter_sepcon_arrays. rewrite (iter_sepcon_remove_one _ _ i).
  rewrite Znth_combine by auto. f_equal. rewrite combine_remove_nth by lia. reflexivity.
  rewrite Zlength_combine; lia.
Qed.*)

End ArrayPointer.

(** Convert [data_at] for numeric types *)

Section DataAtNumeric.

Context `{cs: compspecs}.

(*Helper lemmas*)
Lemma decode_int_single: forall (b: byte),
  decode_int [b] = Byte.unsigned b.
Proof.
  intros b. unfold decode_int. unfold rev_if_be.
  destruct Archi.big_endian; simpl; lia.
Qed.

Lemma zero_ext_8_lemma:
  forall i j, Int.zero_ext 8 (Int.repr (Byte.unsigned i)) = Int.repr (Byte.unsigned j) ->
    i=j.
Proof.
intros.
rewrite zero_ext_inrange in H
  by (rewrite Int.unsigned_repr by rep_lia; simpl; rep_lia).
apply repr_inj_unsigned in H; try rep_lia.
rewrite <- (Byte.repr_unsigned i), <- (Byte.repr_unsigned j).
congruence.
Qed.

Lemma decode_val_Vubyte_inj:
  forall i j, decode_val Mint8unsigned [Byte i] = Vubyte j -> i=j.
Proof.
intros.
unfold decode_val, Vubyte in *; simpl in *.
apply Vint_inj in H.
rewrite decode_int_single in *.
apply zero_ext_8_lemma in H.
auto.
Qed.

Lemma decode_int_range: forall bl, 0 <= decode_int bl < two_p (Z.of_nat (Datatypes.length bl) * 8).
Proof.
intros.
unfold decode_int.
unfold rev_if_be.
destruct Archi.big_endian.
rewrite <- rev_length.
apply int_of_bytes_range.
apply int_of_bytes_range.
Qed.

Lemma int_of_bytes_inj: forall al bl, length al = length bl -> int_of_bytes al = int_of_bytes bl -> al=bl.
Proof.
intros.
revert bl H H0; induction al; destruct bl; simpl; intros; auto; try discriminate.
pose proof (Byte.unsigned_range a). pose proof (Byte.unsigned_range i).
change Byte.modulus with 256 in *. 
assert (al=bl). {
   apply IHal. congruence.
   forget (int_of_bytes al) as x. forget (int_of_bytes bl) as y.
   lia.
}
subst bl.
f_equal.
clear - H0 H1 H2.
rewrite <- (Byte.repr_unsigned a).
rewrite <- (Byte.repr_unsigned i).
f_equal.
lia.
Qed.

Lemma decode_int_inj: forall al bl, 
   length al = length bl -> 
   decode_int al = decode_int bl -> al=bl.
Proof.
intros.
unfold decode_int in *.
apply int_of_bytes_inj in H0; auto.
Qed.

(** Convert between 4 bytes and int *)
(*Lemma address_mapsto_4bytes_aux: 
 forall (sh : Share.t)
   (b0 b1 b2 b3 : byte)
   (b : block) (i : ptrofs)
   (SZ : Ptrofs.unsigned i + 4 < Ptrofs.modulus)
(*   (AL : (4 | Ptrofs.unsigned i)) *)
   (r : readable_share sh),
predicates_sl.sepcon
  (predicates_sl.sepcon
     (predicates_sl.sepcon
           (predicates_hered.allp
              (res_predicates.jam
                 (adr_range_dec (b, Ptrofs.unsigned i) (size_chunk Mint8unsigned))
                 (fun loc : address =>
                  res_predicates.yesat compcert_rmaps.RML.R.NoneP
                    (compcert_rmaps.VAL
                       (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned i)))
                          [Byte b0] Undef)) sh loc) res_predicates.noat))
           (predicates_hered.allp
              (res_predicates.jam
                 (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))
                    (size_chunk Mint8unsigned))
                 (fun loc : address =>
                  res_predicates.yesat compcert_rmaps.RML.R.NoneP
                    (compcert_rmaps.VAL
                       (nth
                          (Z.to_nat
                             (snd loc
                                - snd
                                    (b,
                                    Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))))
                          [Byte b1] Undef)) sh loc) res_predicates.noat)))
        (predicates_hered.allp
           (res_predicates.jam
              (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))
                 (size_chunk Mint8unsigned))
              (fun loc : address =>
               res_predicates.yesat compcert_rmaps.RML.R.NoneP
                 (compcert_rmaps.VAL
                    (nth
                       (Z.to_nat
                          (snd loc
                             - snd
                                 (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))))
                       [Byte b2] Undef)) sh loc) res_predicates.noat)))
     (predicates_hered.allp
        (res_predicates.jam
           (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))
              (size_chunk Mint8unsigned))
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth
                    (Z.to_nat
                       (snd loc
                          - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))))
                    [Byte b3] Undef)) sh loc) res_predicates.noat))
          = predicates_hered.allp
                                    (res_predicates.jam
                                       (adr_range_dec (b, Ptrofs.unsigned i)
                                          (size_chunk Mint32))
                                       (fun loc : address =>
                                        res_predicates.yesat
                                          compcert_rmaps.RML.R.NoneP
                                          (compcert_rmaps.VAL
                                             (nth
                                                (Z.to_nat
                                                   (snd loc
                                                      - snd (b, Ptrofs.unsigned i)))
                                                [Byte b0; Byte b1; Byte b2; Byte b3]
                                                Undef)) sh loc) res_predicates.noat).
Proof.
intros.

     simpl snd.
    simpl size_chunk.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
    rewrite  (res_predicates.allp_jam_split2 _ _ _ 
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1; Byte b2; Byte b3] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1; Byte b2] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - (3+Ptrofs.unsigned i)))
                    [Byte b3] Undef)) sh loc)
           (adr_range_dec (b, Ptrofs.unsigned i) 4)
           (adr_range_dec (b, Ptrofs.unsigned i) 3)
           (adr_range_dec (b, 3 + Ptrofs.unsigned i) 1)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1; Byte b2; Byte b3] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1; Byte b2] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - (3+Ptrofs.unsigned i)))
           [Byte b3] Undef)).
    2:{ forget (Ptrofs.unsigned i) as j. clear.
         split; intros [b1 z1]. simpl. intuition rep_lia.
         simpl. intuition rep_lia.
       }
    2:{ intros. destruct l; destruct H; subst. f_equal. f_equal.
          rewrite (app_nth1 [Byte b0; Byte b1; Byte b2] [Byte b3]); auto.
        simpl. rep_lia.
       }
  2:{ intros. f_equal. f_equal. 
       destruct l; destruct H. subst b4. simpl snd.
       assert (z = 3 + Ptrofs.unsigned i) by lia. subst z.
        rewrite Z.sub_diag.
        replace (3 + Ptrofs.unsigned i - Ptrofs.unsigned i) with 3 by lia.
          reflexivity.
      }
   2:{ intros. left. destruct H0. hnf in H0. rewrite H0 in H1 . clear H0.
        destruct l, H. subst. simpl snd in *.
        assert (Z.to_nat (z - Ptrofs.unsigned i) < 4)%nat by rep_lia.
        clear - H1. destruct (Z.to_nat (z - Ptrofs.unsigned i)) as [|[|[|[|]]]]; inv H1; apply I.
       }
   f_equal.
   
    rewrite  (res_predicates.allp_jam_split2 _ _ _ 
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1; Byte b2] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - (2+Ptrofs.unsigned i)))
                    [Byte b2] Undef)) sh loc)
           (adr_range_dec (b, Ptrofs.unsigned i) 3)
           (adr_range_dec (b, Ptrofs.unsigned i) 2)
           (adr_range_dec (b, 2 + Ptrofs.unsigned i) 1)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1; Byte b2] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - (2+Ptrofs.unsigned i)))
           [Byte b2] Undef)).
    2:{ forget (Ptrofs.unsigned i) as j. clear.
         split; intros [b1 z1]. simpl. intuition rep_lia.
         simpl. intuition rep_lia.
       }
    2:{ intros. destruct l; destruct H; subst. f_equal. f_equal.
          rewrite (app_nth1 [Byte b0; Byte b1] [Byte b2]); auto.
        simpl. rep_lia.
       }
  2:{ intros. f_equal. f_equal. 
       destruct l; destruct H. subst b4. simpl snd.
       assert (z = 2 + Ptrofs.unsigned i) by lia. subst z.
        rewrite Z.sub_diag.
        replace (2 + Ptrofs.unsigned i - Ptrofs.unsigned i) with 2 by lia.
          reflexivity.
      }
   2:{ intros. left. destruct H0. hnf in H0. rewrite H0 in H1 . clear H0.
        destruct l, H. subst. simpl snd in *.
        assert (Z.to_nat (z - Ptrofs.unsigned i) < 3)%nat by rep_lia.
        clear - H1. destruct (Z.to_nat (z - Ptrofs.unsigned i)) as [|[|[|]]]; inv H1; apply I.
       }

   f_equal.

    rewrite  (res_predicates.allp_jam_split2 _ _ _ 
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - (1+Ptrofs.unsigned i)))
                    [Byte b1] Undef)) sh loc)
           (adr_range_dec (b, Ptrofs.unsigned i) 2)
           (adr_range_dec (b, Ptrofs.unsigned i) 1)
           (adr_range_dec (b, 1 + Ptrofs.unsigned i) 1)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - (1+Ptrofs.unsigned i)))
           [Byte b1] Undef)).
    2:{ forget (Ptrofs.unsigned i) as j. clear.
         split; intros [b1 z1]. simpl. intuition rep_lia.
         simpl. intuition rep_lia.
       }
    2:{ intros. destruct l; destruct H; subst. f_equal. f_equal.
          rewrite (app_nth1 [Byte b0] [Byte b1]); auto.
        simpl. rep_lia.
       }
  2:{ intros. f_equal. f_equal. 
       destruct l; destruct H. subst b4. simpl snd.
       assert (z = 1 + Ptrofs.unsigned i) by lia. subst z.
        rewrite Z.sub_diag.
        replace (1 + Ptrofs.unsigned i - Ptrofs.unsigned i) with 1 by lia.
          reflexivity.
      }
   2:{ intros. left. destruct H0. hnf in H0. rewrite H0 in H1 . clear H0.
        destruct l, H. subst. simpl snd in *.
        assert (Z.to_nat (z - Ptrofs.unsigned i) < 2)%nat by rep_lia.
        clear - H1. destruct (Z.to_nat (z - Ptrofs.unsigned i)) as [|[|[|]]]; inv H1; apply I.
       }
   f_equal.
Qed.

Import normalize.

Lemma address_mapsto_4bytes:
 forall 
    (AP: Archi.ptr64 = true)  (* Perhaps this premise could be eliminated. *)
   (sh : Share.t)
    (b0 b1 b2 b3 : byte)
    (b : block)
    (i : ptrofs)
    (SZ : Ptrofs.unsigned i + 4 < Ptrofs.modulus)
    (AL : (4 | Ptrofs.unsigned i))
    (r : readable_share sh),
 predicates_sl.sepcon
  (predicates_sl.sepcon
     (predicates_sl.sepcon
        (res_predicates.address_mapsto Mint8unsigned 
           (Vubyte b0) sh (b, Ptrofs.unsigned i))
        (res_predicates.address_mapsto Mint8unsigned 
           (Vubyte b1) sh
           (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))))
     (res_predicates.address_mapsto Mint8unsigned 
        (Vubyte b2) sh (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))))
  (res_predicates.address_mapsto Mint8unsigned (Vubyte b3) sh
     (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))) = 
res_predicates.address_mapsto Mint32
  (Vint (Int.repr (decode_int [b0; b1; b2; b3]))) sh
  (b, Ptrofs.unsigned i).
Proof.
intros.
      unfold res_predicates.address_mapsto. rewrite <- !exp_equiv.
      apply predicates_hered.bi.equiv_entails_2.
  - repeat change (exp ?A) with (predicates_hered.exp A).
      normalize.normalize.
      intros bl3 [A3 [B3 _]] bl2 bl1 bl0.
      normalize.normalize.
      destruct H as [A2 [ B2 _]].
      destruct H0 as [A1 [ B1 _]].
      destruct H1 as [A0 [ B0 _]].
    destruct bl0 as [ | c0 [|]]; inv A0; inv B0. 
    destruct bl1 as [ | c1 [|]]; inv A1; inv B1.
    destruct bl2 as [ | c2 [|]]; inv A2; inv B2. 
    destruct bl3 as [ | c3 [|]]; inv A3; inv B3.
     destruct c0; try discriminate H0.
     destruct c1; try discriminate H1.
     destruct c2; try discriminate H2.
     destruct c3; try discriminate H3.
   apply decode_val_Vubyte_inj in H0,H1,H2,H3. subst.
   apply (predicates_hered.bi.exist_intro [Byte b0; Byte b1; Byte b2; Byte b3]).
     rewrite predicates_hered.prop_true_andp.
      2:{ split3. reflexivity. reflexivity. apply AL. }
  match goal with |- predicates_hered.derives ?A ?B => 
        assert (EQ: A=B); [ | rewrite EQ; apply predicates_hered.derives_refl]
    end.
  apply address_mapsto_4bytes_aux; auto.

 -
  repeat change (exp ?A) with (predicates_hered.exp A).
      normalize.normalize.
  intros bl [? [? ?]]. simpl snd in H1.
      destruct bl as [|c0 [| c1 [| c2 [| c3 [|]]]]]; inv H.
       unfold decode_val, proj_bytes in H0. rewrite AP in H0. clear AP.
       destruct c0; try discriminate H0.
       destruct c1; try discriminate H0.
       destruct c2; try discriminate H0.
       destruct c3; try discriminate H0.
       apply Vint_inj in H0.
       pose proof (decode_int_range [b0;b1;b2;b3]).
       pose proof (decode_int_range [i0;i1;i2;i3]).
       change (two_p _) with Int.modulus in H,H2.
       apply repr_inj_unsigned in H0; try rep_lia.
        apply decode_int_inj in H0.
      clear H H2. inv H0.
     apply predicates_hered.bi.exist_intro with [Byte b3].
      normalize.normalize.
     apply predicates_hered.bi.exist_intro with [Byte b2].
      normalize.normalize.
     apply predicates_hered.bi.exist_intro with [Byte b1].
      normalize.normalize.
     apply predicates_hered.bi.exist_intro with [Byte b0].
     rewrite !predicates_hered.prop_true_andp by 
     (split3; [ reflexivity |  | apply Z.divide_1_l  ];
     unfold decode_val, Vubyte; simpl; f_equal;
     rewrite decode_int_single;
     apply zero_ext_inrange; change (two_p _ - 1) with 255;
     rewrite Int.unsigned_repr by rep_lia; rep_lia).
  match goal with |- predicates_hered.derives ?A ?B => 
        assert (EQ: B=A); [ | rewrite EQ; apply predicates_hered.derives_refl]
    end.
  apply address_mapsto_4bytes_aux; auto.
  reflexivity.
Qed.


Section Foo.

Import predicates_hered predicates_sl res_predicates msl.normalize.

Lemma address_mapsto_8bytes_aux: 
 forall (sh : Share.t)
   (b0 b1 b2 b3 b4 b5 b6 b7: byte)
   (b : block) (i : ptrofs)
   (SZ : Ptrofs.unsigned i + 8 < Ptrofs.modulus)
   (r : readable_share sh),

predicates_sl.sepcon
  (predicates_sl.sepcon
     (predicates_sl.sepcon
        (predicates_sl.sepcon
           (predicates_sl.sepcon
              (predicates_sl.sepcon
                 (predicates_sl.sepcon
                    (predicates_hered.allp
                       (res_predicates.jam
                          (adr_range_dec (b, Ptrofs.unsigned i) (size_chunk Mint8unsigned))
                          (fun loc : address =>
                           res_predicates.yesat compcert_rmaps.RML.R.NoneP
                             (compcert_rmaps.VAL
                                (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned i)))
                                   [Byte b0] Undef)) sh loc) res_predicates.noat))
                    (predicates_hered.allp
                       (res_predicates.jam
                          (adr_range_dec
                             (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))
                             (size_chunk Mint8unsigned))
                          (fun loc : address =>
                           res_predicates.yesat compcert_rmaps.RML.R.NoneP
                             (compcert_rmaps.VAL
                                (nth
                                   (Z.to_nat
                                      (snd loc
                                         - snd
                                             (b,
                                              Ptrofs.unsigned
                                                (Ptrofs.add i (Ptrofs.repr 1)))))
                                   [Byte b1] Undef)) sh loc) res_predicates.noat)))
                 (predicates_hered.allp
                    (res_predicates.jam
                       (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))
                          (size_chunk Mint8unsigned))
                       (fun loc : address =>
                        res_predicates.yesat compcert_rmaps.RML.R.NoneP
                          (compcert_rmaps.VAL
                             (nth
                                (Z.to_nat
                                   (snd loc
                                      - snd
                                          (b,
                                           Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))))
                                [Byte b2] Undef)) sh loc) res_predicates.noat)))
              (predicates_hered.allp
                 (res_predicates.jam
                    (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))
                       (size_chunk Mint8unsigned))
                    (fun loc : address =>
                     res_predicates.yesat compcert_rmaps.RML.R.NoneP
                       (compcert_rmaps.VAL
                          (nth
                             (Z.to_nat
                                (snd loc
                                   - snd
                                       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))))
                             [Byte b3] Undef)) sh loc) res_predicates.noat)))
           (predicates_hered.allp
              (res_predicates.jam
                 (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 4)))
                    (size_chunk Mint8unsigned))
                 (fun loc : address =>
                  res_predicates.yesat compcert_rmaps.RML.R.NoneP
                    (compcert_rmaps.VAL
                       (nth
                          (Z.to_nat
                             (snd loc
                                - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 4)))))
                          [Byte b4] Undef)) sh loc) res_predicates.noat)))
        (predicates_hered.allp
           (res_predicates.jam
              (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 5)))
                 (size_chunk Mint8unsigned))
              (fun loc : address =>
               res_predicates.yesat compcert_rmaps.RML.R.NoneP
                 (compcert_rmaps.VAL
                    (nth
                       (Z.to_nat
                          (snd loc
                             - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 5)))))
                                    [Byte b5] Undef)) sh loc) res_predicates.noat)))
     (predicates_hered.allp
        (res_predicates.jam
           (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 6)))
              (size_chunk Mint8unsigned))
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth
                    (Z.to_nat
                       (snd loc - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 6)))))
                    [Byte b6] Undef)) sh loc) res_predicates.noat)))
  (predicates_hered.allp
     (res_predicates.jam
        (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 7)))
           (size_chunk Mint8unsigned))
        (fun loc : address =>
         res_predicates.yesat compcert_rmaps.RML.R.NoneP
           (compcert_rmaps.VAL
              (nth
                 (Z.to_nat
                    (snd loc - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 7)))))
                 [Byte b7] Undef)) sh loc) res_predicates.noat)) = 
predicates_hered.allp
  (res_predicates.jam (adr_range_dec (b, Ptrofs.unsigned i) (size_chunk Mint64))
     (fun loc : address =>
      res_predicates.yesat compcert_rmaps.RML.R.NoneP
        (compcert_rmaps.VAL
           (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned i)))
              [Byte b0; Byte b1; Byte b2; Byte b3; Byte b4; Byte b5; Byte b6; Byte b7]
              Undef)) sh loc) res_predicates.noat).
Proof.
intros.

     simpl snd.
    simpl size_chunk.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
  change [Byte b0; Byte b1; Byte b2; Byte b3; Byte b4; Byte b5; Byte b6; Byte b7] 
  with (map Byte [b0;b1;b2;b3;b4;b5;b6;b7]).
   

repeat lazymatch goal with |- _ = ?R =>
 lazymatch R with context [nth _ (map Byte ?al)] =>
  lazymatch al with _ :: _ =>
   let len := constr:(Zlength al) in let len := eval compute in len in 
   let part1 := constr:(sublist.sublist 0 (len-1) al) in let part1 := eval compute in part1 in
   let part2 := constr:(sublist.sublist (len-1) len al) in let part2 := eval compute in part2 in
   rewrite  (res_predicates.allp_jam_split2 _ _ _ 
           (fun loc : address =>
            yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    (map Byte al) Undef)) sh loc)
           (fun loc : address =>
            yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    (map Byte part1) Undef)) sh loc)
           (fun loc : address =>
            yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - ((len-1)+Ptrofs.unsigned i)))
                    (map Byte part2) Undef)) sh loc)
           (adr_range_dec (b, Ptrofs.unsigned i) len)
           (adr_range_dec (b, Ptrofs.unsigned i) (len-1))
           (adr_range_dec (b, (len-1) + Ptrofs.unsigned i) 1));
  [ 
  | eexists; apply res_predicates.is_resource_pred_YES_VAL'
  | eexists; apply res_predicates.is_resource_pred_YES_VAL'
  | eexists; apply res_predicates.is_resource_pred_YES_VAL'
  | clear; split; intros [? ?]; simpl; intuition rep_lia
  |intros; f_equal; f_equal;
       destruct l; destruct H; subst; simpl snd;
       change al with (List.app (sublist.sublist 0 (len-1) al) (sublist.sublist (len-1) len al));
       rewrite map_app, app_nth1 by (simpl; lia);
       reflexivity
  | intros; f_equal; f_equal; 
       destruct l; destruct H; subst; simpl snd;
       change al with (List.app (sublist.sublist 0 (len-1) al) (sublist.sublist (len-1) len al));
       rewrite map_app, app_nth2 by (simpl; lia);simpl sublist.sublist;
       simpl length;
       match type of H0 with ?a <= _ < _ => assert (z=a) by lia end; subst z;
       rewrite Z.sub_diag;
       replace (_ - _) with (len-1) by lia;
       reflexivity
  |intros; left; destruct H0; hnf in H0; rewrite H0 in H1; clear H0;
        destruct l, H; subst; simpl snd in *;
    rewrite nth_map'  with (d' :=  Byte.zero) in H1 by (simpl; lia);
    inv H1; apply I
  ];
  f_equal; (set (jj:= len-1) in *; compute in jj; subst jj) (*  really_simplify (len-1)   *)
  end end end.
Qed.

Lemma address_mapsto_8bytes_forward:
 forall 
    (AP: Archi.ptr64 = true)  (* Perhaps this premise could be eliminated. *)
   (sh : Share.t)
    (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
    (b : block)
    (i : ptrofs)
    (SZ : Ptrofs.unsigned i + 8 < Ptrofs.modulus)
    (AL : (8 | Ptrofs.unsigned i))
    (r : readable_share sh),
predicates_hered.derives
 (predicates_sl.sepcon
 (predicates_sl.sepcon
  (predicates_sl.sepcon
   (predicates_sl.sepcon
    (predicates_sl.sepcon
     (predicates_sl.sepcon
      (predicates_sl.sepcon
       (res_predicates.address_mapsto Mint8unsigned 
           (Vubyte b0) sh (b, Ptrofs.unsigned i))
       (res_predicates.address_mapsto Mint8unsigned 
           (Vubyte b1) sh
           (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))))
       (res_predicates.address_mapsto Mint8unsigned 
         (Vubyte b2) sh (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b3) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b4) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 4)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b5) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 5)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b6) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 6)))))
       (res_predicates.address_mapsto Mint8unsigned (Vubyte b7) sh
          (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 7)))))
 (res_predicates.address_mapsto Mint64
  (Vlong (Int64.repr (decode_int [b0; b1; b2; b3; b4; b5; b6; b7]))) sh
  (b, Ptrofs.unsigned i)).
Proof.
intros.
      unfold res_predicates.address_mapsto. rewrite <- !exp_equiv.
    repeat change (seplog.exp ?A) with (predicates_hered.exp A).
    normalize.normalize.
    intros bl7 [A7 [B7 _]] bl6 bl5 bl4 bl3 bl2 bl1 bl0.
    normalize.normalize.
    destruct H as [A6 [ B6 _]].
    destruct H0 as [A5 [ B5 _]].
    destruct H1 as [A4 [ B4 _]].
    destruct H2 as [A3 [ B3 _]].
    destruct H3 as [A2 [ B2 _]].
    destruct H4 as [A1 [ B1 _]].
    destruct H5 as [A0 [ B0 _]].
    destruct bl0 as [ | c0 [|]]; inv A0; inv B0. 
    destruct bl1 as [ | c1 [|]]; inv A1; inv B1.
    destruct bl2 as [ | c2 [|]]; inv A2; inv B2. 
    destruct bl3 as [ | c3 [|]]; inv A3; inv B3.
    destruct bl4 as [ | c4 [|]]; inv A4; inv B4. 
    destruct bl5 as [ | c5 [|]]; inv A5; inv B5.
    destruct bl6 as [ | c6 [|]]; inv A6; inv B6. 
    destruct bl7 as [ | c7 [|]]; inv A7; inv B7.
    destruct c0; try discriminate H0.
    destruct c1; try discriminate H1.
    destruct c2; try discriminate H2.
    destruct c3; try discriminate H3.
    destruct c4; try discriminate H4.
    destruct c5; try discriminate H5.
    destruct c6; try discriminate H6.
    destruct c7; try discriminate H7.
    apply decode_val_Vubyte_inj in H0,H1,H2,H3,H4,H5,H6,H7; subst.
   apply (predicates_hered.exp_right (map Byte [b0;b1;b2;b3;b4;b5;b6;b7])).
     rewrite predicates_hered.prop_true_andp.
      2:{ split3. reflexivity. reflexivity. apply AL. }
   rewrite address_mapsto_8bytes_aux; auto.
Qed.


Lemma nonlock_permission_8bytes:
 forall (sh : Share.t)
     (b : block) (i : ptrofs) 
     (SZ : Ptrofs.unsigned i + 8 < Ptrofs.modulus),
(res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 4))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 5))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 6))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 7))) 1)%logic = 
res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 8.
Proof.
intros.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
 rewrite (res_predicates.nonlock_permission_bytes_split2 7 1 8 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 6 1 7 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 5 1 6 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 4 1 5 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 3 1 4 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 2 1 3 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 1 1 2 sh) by lia.
 repeat change (predicates_sl.sepcon ?A ?B) with (A * B)%logic.
 rewrite !(Z.add_comm (Ptrofs.unsigned i)).
 f_equal.
Qed.

Lemma tc_val_Vubyte: forall b, tc_val tuchar (Vubyte b).
Proof.
intros; red. 
simpl. rewrite Int.unsigned_repr by rep_lia.
rep_lia.
Qed.

End Foo.

Lemma data_at_long_bytes_forward: 
  forall 
    (AP: Archi.ptr64 = true)  (* Perhaps this premise could be eliminated. *)
  sh 
   (b0 b1 b2 b3 b4 b5 b6 b7: byte) p,
  field_compatible tulong [] p  ->
  (data_at sh tuchar (Vubyte b0) p *
  data_at sh tuchar (Vubyte b1) (offset_val 1 p) *
  data_at sh tuchar (Vubyte b2) (offset_val 2 p) *
  data_at sh tuchar (Vubyte b3) (offset_val 3 p) *
  data_at sh tuchar (Vubyte b4) (offset_val 4 p) *
  data_at sh tuchar (Vubyte b5) (offset_val 5 p) *
  data_at sh tuchar (Vubyte b6) (offset_val 6 p) *
  data_at sh tuchar (Vubyte b7) (offset_val 7 p))%logic |--
  data_at sh tulong (Vlong (Int64.repr (decode_int [b0;b1;b2;b3;b4;b5;b6;b7]))) p.
Proof.
  intros AP sh b0 b1 b2 b3 b4 b5 b6 b7 p. unfold data_at. unfold field_at.
  intro. normalize.normalize. clear - AP H. simpl.
 rewrite (prop_true_andp (field_compatible tulong [] p)) by auto.
 destruct H as [H0 [_ [SZ [AL _]]]]. red in SZ. simpl sizeof in SZ.
   destruct p; inversion H0. clear H0.
 assert (8 | Ptrofs.unsigned i)
   by (eapply align_compatible_rec_by_value_inv in AL; [ | reflexivity]; assumption).
 clear AL.
 Intros.
 unfold at_offset.
 rewrite !offset_offset_val. rewrite !Z.add_0_r.
 simpl offset_val. rewrite !ptrofs_add_repr_0_r.
 rewrite !data_at_rec_eq. simpl.
 change (unfold_reptype ?x) with x.
 unfold mapsto.
 simpl access_mode; simpl type_is_volatile; cbv iota.
 rewrite !(prop_true_andp _ _ (tc_val_Vubyte _)).
 rewrite !(prop_false_andp (_ = _)) by (intro Hx; inv Hx).
 rewrite !(prop_true_andp (tc_val tulong _)) by (apply Logic.I).
 rewrite ?prop_and_mpred.
 rewrite ?(prop_true_andp _ _ (tc_val_tc_val' _ _ (tc_val_Vubyte _))).
 rewrite !(prop_true_andp (tc_val' tulong _)) by (apply tc_val_tc_val'; apply Logic.I).
 rewrite ?(prop_true_andp _ _ (Z.divide_1_l _)).
 rewrite !orp_FF.
 rewrite (prop_true_andp (_ | _)) by apply H.
 if_tac.
-
 rewrite derives_eq.
 apply address_mapsto_8bytes_forward; auto.
- rewrite nonlock_permission_8bytes; auto.
  apply derives_refl.
Qed.


Lemma nonlock_permission_4bytes:
 forall (sh : Share.t)
     (b : block) (i : ptrofs) 
     (SZ : Ptrofs.unsigned i + 4 < Ptrofs.modulus),
(res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 2))) 1
   * res_predicates.nonlock_permission_bytes sh
       (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 3))) 1)%logic = 
res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 4.
Proof.
intros.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
 rewrite (res_predicates.nonlock_permission_bytes_split2 3 1 4 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 2 1 3 sh) by lia.
 rewrite (res_predicates.nonlock_permission_bytes_split2 1 1 2 sh) by lia.
 repeat change (predicates_sl.sepcon ?A ?B) with (A * B)%logic.
 rewrite !(Z.add_comm (Ptrofs.unsigned i)).
 f_equal.
Qed.

(* The main result: 4 consecutive bytes can be interpreted as a single int *)
Lemma data_at_int_bytes: 
  forall 
    (AP: Archi.ptr64 = true)  (* Perhaps this premise could be eliminated. *)
  sh 
   (b0 b1 b2 b3 : byte) p,
  field_compatible tuint [] p  ->
  (data_at sh tuchar (Vubyte b0) p *
  data_at sh tuchar (Vubyte b1) (offset_val 1 p) *
  data_at sh tuchar (Vubyte b2) (offset_val 2 p) *
  data_at sh tuchar (Vubyte b3) (offset_val 3 p))%logic =
  data_at sh tuint (Vint (Int.repr (decode_int [b0;b1;b2;b3]))) p.
Proof.
  intros AP sh b0 b1 b2 b3 p. unfold data_at. unfold field_at.
  intro.
  rewrite !prop_true_andp by auto with field_compatible.
 destruct H as [H0 [_ [SZ [AL _]]]]. red in SZ. simpl sizeof in SZ.
   destruct p; inversion H0. clear H0.
 assert (4 | Ptrofs.unsigned i)
   by (eapply align_compatible_rec_by_value_inv in AL; [ | reflexivity]; assumption).
 clear AL.
 unfold at_offset. 
 rewrite !offset_offset_val. rewrite !Z.add_0_r.
 simpl offset_val. rewrite !ptrofs_add_repr_0_r.
 rewrite !data_at_rec_eq. simpl.
 change (unfold_reptype ?x) with x.
 unfold mapsto.
 simpl access_mode; simpl type_is_volatile; cbv iota.
 rewrite !(prop_true_andp _ _ (tc_val_Vubyte _)).
 rewrite !(prop_false_andp (_ = _)) by (intro Hx; inv Hx).
 rewrite !(prop_true_andp (tc_val tuint _)) by (apply Logic.I).
 rewrite ?prop_and_mpred.
 rewrite ?(prop_true_andp _ _ (tc_val_tc_val' _ _ (tc_val_Vubyte _))).
 rewrite !(prop_true_andp (tc_val' tuint _)) by (apply tc_val_tc_val'; apply Logic.I).
 rewrite ?(prop_true_andp _ _ (Z.divide_1_l _)).
 rewrite !orp_FF.
 rewrite (prop_true_andp (_ | _)) by apply H.
 if_tac.
- apply address_mapsto_4bytes; auto.
- apply nonlock_permission_4bytes; auto.
Qed.


(** Convert between 2 bytes and short *)

Lemma address_mapsto_2bytes_aux: 
 forall (sh : Share.t)
   (b0 b1 b2 b3 : byte)
   (b : block) (i : ptrofs)
   (SZ : Ptrofs.unsigned i + 2 < Ptrofs.modulus)
   (r : readable_share sh),
predicates_sl.sepcon
     (predicates_hered.allp
        (res_predicates.jam (adr_range_dec (b, Ptrofs.unsigned i) (size_chunk Mint8unsigned))
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned i))) [Byte b0] Undef)) sh loc)
           res_predicates.noat))
     (predicates_hered.allp
        (res_predicates.jam
           (adr_range_dec (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1))) (size_chunk Mint8unsigned))
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))))
                    [Byte b1] Undef)) sh loc) res_predicates.noat)) = 
 predicates_hered.allp
     (res_predicates.jam (adr_range_dec (b, Ptrofs.unsigned i) (size_chunk Mint16unsigned))
        (fun loc : address =>
         res_predicates.yesat compcert_rmaps.RML.R.NoneP
           (compcert_rmaps.VAL
              (nth (Z.to_nat (snd loc - snd (b, Ptrofs.unsigned i))) [Byte b0; Byte b1] Undef)) sh loc)
    res_predicates.noat).
Proof.
intros. simpl snd. simpl size_chunk.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
    rewrite  (res_predicates.allp_jam_split2 _ _ _ 
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0; Byte b1] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
                    [Byte b0] Undef)) sh loc)
           (fun loc : address =>
            res_predicates.yesat compcert_rmaps.RML.R.NoneP
              (compcert_rmaps.VAL
                 (nth (Z.to_nat (snd loc - (1+Ptrofs.unsigned i)))
                    [Byte b1] Undef)) sh loc)
           (adr_range_dec (b, Ptrofs.unsigned i) 2)
           (adr_range_dec (b, Ptrofs.unsigned i) 1)
           (adr_range_dec (b, 1 + Ptrofs.unsigned i) 1)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0; Byte b1] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - Ptrofs.unsigned i))
           [Byte b0] Undef)).
   2: eexists;
    apply (res_predicates.is_resource_pred_YES_VAL' sh 
     (fun loc => nth (Z.to_nat (snd loc - (1+Ptrofs.unsigned i)))
           [Byte b1] Undef)).
    2:{ forget (Ptrofs.unsigned i) as j. clear.
         split; intros [b1 z1]. simpl. intuition rep_lia.
         simpl. intuition rep_lia.
       }
    2:{ intros. destruct l; destruct H; subst. f_equal. f_equal.
          rewrite (app_nth1 [Byte b0] [Byte b1]); auto.
        simpl. rep_lia.
       }
    2:{ intros. f_equal. f_equal. 
       destruct l; destruct H. subst b4. simpl snd.
       assert (z = 1 + Ptrofs.unsigned i) by lia. subst z.
        rewrite Z.sub_diag.
        replace (1 + Ptrofs.unsigned i - Ptrofs.unsigned i) with 1 by lia.
          reflexivity.
      }
    2:{ intros. left. destruct H0. hnf in H0. rewrite H0 in H1 . clear H0.
        destruct l, H. subst. simpl snd in *.
        assert (Z.to_nat (z - Ptrofs.unsigned i) < 2)%nat by rep_lia.
        clear - H1. destruct (Z.to_nat (z - Ptrofs.unsigned i)) as [|[|[|]]]; inv H1; apply I.
       }
   f_equal.
Qed.

Lemma zero_ext_16: forall z,
  0 <= z < 65536 ->
  Int.zero_ext 16 (Int.repr z) = Int.repr z.
Proof.
  intros. unfold Int.zero_ext. f_equal.
  rewrite Zbits.Zzero_ext_mod by rep_lia.
  replace (two_p 16) with (65536) by reflexivity.
  rewrite Zmod_small; rewrite Int.unsigned_repr; rep_lia.
Qed.

Lemma address_mapsto_2bytes:
 forall (sh : Share.t)
    (b0 b1 : byte)
    (b : block)
    (i : ptrofs)
    (SZ : Ptrofs.unsigned i + 2 < Ptrofs.modulus)
    (AL : (2 | Ptrofs.unsigned i))
    (r : readable_share sh),
predicates_sl.sepcon (res_predicates.address_mapsto Mint8unsigned (Vubyte b0) sh (b, Ptrofs.unsigned i))
  (res_predicates.address_mapsto Mint8unsigned (Vubyte b1) sh
     (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1)))) = res_predicates.address_mapsto Mint16unsigned
                                                              (Vint (Int.repr (decode_int [b0; b1]))) sh
                                                              (b, Ptrofs.unsigned i).
Proof.
  intros. unfold res_predicates.address_mapsto. rewrite <- !exp_equiv.
  apply predicates_hered.bi.equiv_entails_2.
  - repeat change (exp ?A) with (predicates_hered.exp A).
    normalize.normalize.
    intros bl1 [A1 [B1 _]] bl0.
    normalize.normalize.
    destruct H as [A0 [ B0 _]].
    destruct bl0 as [ | c0 [|]]; inv A0; inv B0. 
    destruct bl1 as [ | c1 [|]]; inv A1; inv B1.
    destruct c0; try discriminate.
    destruct c1; try discriminate.
    apply decode_val_Vubyte_inj in H0,H1. subst.
    apply (predicates_hered.bi.exist_intro [Byte b0; Byte b1]).
    rewrite predicates_hered.prop_true_andp.
    2:{ split3. reflexivity. unfold decode_val. simpl.
        f_equal. apply zero_ext_16. 
        pose proof (decode_int_range [b0; b1]). simpl in H.
        assert (two_power_pos 16 = 65536) by reflexivity. lia. apply AL. 
      }
  match goal with |- predicates_hered.derives ?A ?B => 
        assert (EQ: A=B); [ | rewrite EQ; apply predicates_hered.derives_refl]
    end.
  apply address_mapsto_2bytes_aux; auto.
 - repeat change (exp ?A) with (predicates_hered.exp A).
   normalize.normalize.
   intros bl [? [? ?]].
    simpl snd in H1.
   destruct bl as [|c0 [| c1 [| c2 [| c3 [|]]]]]; inv H.
   unfold decode_val, proj_bytes in H0.
   destruct c0; try solve [destruct Archi.ptr64 eqn:AP; discriminate].
   destruct c1; try solve [destruct Archi.ptr64 eqn:AP; discriminate].
   apply Vint_inj in H0.
   pose proof (decode_int_range [b0;b1]).
   pose proof (decode_int_range [i0;i1]).
   change (two_p _) with 65536 in H,H2.
   rewrite zero_ext_16 in H0 by lia.
   apply repr_inj_unsigned in H0; try rep_lia.
    apply decode_int_inj in H0.
   clear H H2. inv H0.
  apply predicates_hered.bi.exist_intro with [Byte b1].
  normalize.normalize.
  apply predicates_hered.bi.exist_intro with [Byte b0].
  rewrite !predicates_hered.prop_true_andp by 
 (split3; [ reflexivity |  | apply Z.divide_1_l  ];
 unfold decode_val, Vubyte; simpl; f_equal;
 rewrite decode_int_single;
 apply zero_ext_inrange; change (two_p _ - 1) with 255;
 rewrite Int.unsigned_repr by rep_lia; rep_lia).
  match goal with |- predicates_hered.derives ?A ?B => 
        assert (EQ: B=A); [ | rewrite EQ; apply predicates_hered.derives_refl]
    end.
  apply address_mapsto_2bytes_aux; auto.
  reflexivity.
Qed.

Lemma nonlock_permission_2bytes:
 forall (sh : Share.t)
     (b : block) (i : ptrofs) 
     (SZ : Ptrofs.unsigned i + 2 < Ptrofs.modulus),
(res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 1
   * res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr 1))) 1)%logic = 
res_predicates.nonlock_permission_bytes sh (b, Ptrofs.unsigned i) 2.
Proof.
intros.
 repeat   match goal with |- context [Ptrofs.add i (Ptrofs.repr ?A)] =>
    replace (Ptrofs.unsigned (Ptrofs.add i (Ptrofs.repr A)))
    with (A + Ptrofs.unsigned i)
    by (unfold Ptrofs.add; rewrite (Ptrofs.unsigned_repr (Z.pos _)) by rep_lia;
        rewrite Ptrofs.unsigned_repr by rep_lia; rep_lia)
   end.
 rewrite (res_predicates.nonlock_permission_bytes_split2 1 1 2 sh) by lia.
 repeat change (predicates_sl.sepcon ?A ?B) with (A * B)%logic.
 rewrite !(Z.add_comm (Ptrofs.unsigned i)).
 f_equal.
Qed.

Lemma tc_val_short: forall (b0 b1 : byte),
  tc_val tushort (Vint (Int.repr (decode_int [b0; b1]))).
Proof.
  intros. simpl. pose proof (decode_int_range [b0; b1]).
  simpl in H. assert (two_power_pos 16 = 65536) by reflexivity.
  rewrite Int.unsigned_repr; rep_lia.
Qed.

Lemma prop_true_eq: forall  {A : Type} {ND : NatDed A} (P : Prop),
  P ->
  !! P = !! True.
Proof.
  intros. apply ND_prop_ext. split; auto.
Qed.


(* The main result: 2 consecutive bytes can be interpreted as a single short *)
Lemma data_at_short_bytes: forall sh
  (b0 b1: byte) p,
  field_compatible tushort [] p ->
  (data_at sh tuchar (Vubyte b0) p *
  data_at sh tuchar (Vubyte b1) (offset_val 1 p))%logic =
  data_at sh tushort (Vint (Int.repr (decode_int [b0; b1]))) p.
Proof.
   intros sh b0 b1 p. unfold data_at. unfold field_at. normalize.
    rewrite !(prop_true_andp _ _ H).
  assert (H': field_compatible tuchar [] p). {
    destruct H as [? [? [? [? ?]]]].
    split3; auto. destruct p; try contradiction.
    red in H1,H2,H3. split3; auto.
   red; simpl sizeof in *. lia.
   red. eapply align_compatible_rec_by_value; [reflexivity | ].
   apply Z.divide_1_l.
  }
  assert (H'': field_compatible tuchar [] (offset_val 1 p)). {
    unfold offset_val.
    destruct H as [? [? [? [? ?]]]].
    split3; auto. destruct p; try contradiction. apply I.
    red in H1,H2,H3.
    unfold Ptrofs.add. rewrite Ptrofs.unsigned_repr by rep_lia.
    destruct p; try contradiction.
   simpl in H1.
    split3; auto.
     red; simpl sizeof in *. rewrite Ptrofs.unsigned_repr by rep_lia. rep_lia.
   red. eapply align_compatible_rec_by_value; [reflexivity | ].
   apply Z.divide_1_l.
  }
   rewrite (prop_true_andp _ _ H').
   rewrite (prop_true_andp _ _ H'').
   simpl. rewrite !data_at_rec_eq. simpl. 
    unfold at_offset. normalize. change (unfold_reptype ?x) with x.
    assert (isptr p) by apply H.
    destruct p; inversion H0. clear H0.
    unfold mapsto. rewrite (prop_true_eq _ (tc_val_short b0 b1)). simpl.
    destruct H as [_ [_ [SZ [AL _]]]]. red in SZ. simpl sizeof in SZ.
    apply align_compatible_rec_by_value_inv with (ch := Mint16unsigned) in AL; auto.
    simpl in AL.
    rewrite !(prop_true_andp _ _ Logic.I).
    rewrite !(prop_false_andp ( _ = Vundef)) by (intro Hx; inv  Hx).
    rewrite !orp_FF.
    rewrite !(prop_true_andp (_ /\ _))
   by (split; [apply (tc_val_tc_val' _ _ (tc_val_Vubyte _)) | apply Z.divide_1_l]).
   destruct (readable_share_dec sh); simpl; normalize.
    + rewrite !Int.unsigned_repr by rep_lia. 
      rewrite !(prop_true_andp (Byte.unsigned _ <= _)) by rep_lia.
   repeat change (?A * ?B)%logic with (predicates_sl.sepcon A B).
   rewrite ?ptrofs_add_repr_0_r.
   apply address_mapsto_2bytes; auto.
   
   +
   rewrite ?ptrofs_add_repr_0_r.
       rewrite !prop_true_andp.
      2 : split; auto; hnf; intros; apply tc_val_short.
      apply nonlock_permission_2bytes; auto.
Qed.*)

End DataAtNumeric.

Lemma field_at_values_cohere {cs:compspecs}:
  forall sh1 sh2 t gfs
            (v1 v2 : reptype (nested_field_type t gfs))
             (p: val),
       value_defined (nested_field_type t gfs) v1 ->
       value_defined (nested_field_type t gfs) v2 ->
    readable_share sh1 -> readable_share sh2 ->
   field_at sh1 t gfs v1 p ∗ field_at sh2 t gfs v2 p ⊢ ⌜v1=v2⌝.
Proof. intros.
  unfold field_at, at_offset; Intros.
  destruct H3 as [? _]. destruct p; try contradiction.
  apply data_at_rec_values_cohere; auto.
Qed.

Lemma data_at_values_cohere {cs:compspecs}:
  forall sh1 sh2 t
            (v1 v2 : reptype t)
             (p: val),
       value_defined t v1 ->
       value_defined t v2 ->
    readable_share sh1 -> readable_share sh2 ->
   data_at sh1 t v1 p ∗ data_at sh2 t v2 p ⊢ ⌜v1=v2⌝.
Proof. intros.
  apply field_at_values_cohere; auto.
Qed.

Import ListNotations.

Definition cstring {CS : compspecs} sh (s: list byte) p := 
  ⌜~In Byte.zero s⌝ ∧
  data_at sh (tarray tschar (Zlength s + 1)) (map Vbyte (s ++ [Byte.zero])) p.

Lemma cstring_local_facts: forall {CS : compspecs} sh s p,
  cstring sh s p ⊢ ⌜isptr p /\ Zlength s + 1 < Ptrofs.modulus⌝.
Proof.
  intros; unfold cstring.
  Intros.
  saturate_local.
  apply bi.pure_intro.
  destruct H0 as [? [_ [? _]]].
  destruct p; try contradiction.
  red in H3.
  split. simpl. auto.
  unfold sizeof, Ctypes.sizeof in H3; clear H1.
  rewrite Z.max_r in H3 by list_solve.
  fold Ctypes.sizeof in H3.
  change (Ctypes.sizeof tschar) with 1 in H3.
  pose proof (Ptrofs.unsigned_range i).
  lia. 
Qed.

Lemma cstring_valid_pointer: forall {CS : compspecs} sh s p, 
   nonempty_share sh ->
   cstring sh s p ⊢ valid_pointer p.
Proof.
  intros; unfold cstring; Intros.
  apply data_at_valid_ptr; auto.
  unfold tarray, tschar, sizeof, Ctypes.sizeof.
  pose proof (Zlength_nonneg s).
  rewrite Z.max_r; lia.
Qed.

Definition cstringn {CS : compspecs} sh (s: list byte) n p :=
  ⌜~In Byte.zero s⌝ ∧
  data_at sh (tarray tschar n) (map Vbyte (s ++ [Byte.zero]) ++
    Zrepeat Vundef (n - (Zlength s + 1))) p.

Fixpoint no_zero_bytes (s: list byte) : bool :=
 match s with
 | nil => true
 | b :: s' => andb (negb (Byte.eq b Byte.zero)) (no_zero_bytes s')
 end.

Lemma data_at_to_cstring:
 forall {CS: compspecs} sh n s p,
  no_zero_bytes s = true ->
 data_at sh (tarray tschar n) (map Vbyte (s ++ [Byte.zero])) p ⊢
 cstring sh s p.
Proof.
intros.
saturate_local. clear H0 H2.
rewrite Zlength_map, Zlength_app, Zlength_cons, Zlength_nil in H1.
simpl in H1.
destruct (Z.max_spec 0 n) as [[? ?]|[? ?]].
2:{ rewrite H2 in H1. pose proof (Zlength_nonneg s). lia. }
rewrite H2 in *.
clear H0 H2.
subst n.
unfold cstring.
apply bi.and_intro; auto.
apply bi.pure_intro.
intro.
induction s; simpl in *; auto.
rewrite andb_true_iff in H.
destruct H.
destruct H0; subst.
rewrite Byte.eq_true in H. inv H.
auto.
Qed.

Lemma cstringn_equiv : forall {CS : compspecs} sh s p, cstring sh s p = cstringn sh s (Zlength s + 1) p.
Proof.
  intros; unfold cstring, cstringn.
  rewrite Zminus_diag, app_nil_r; auto.
Qed.

Lemma cstringn_local_facts: forall {CS : compspecs} sh s n p, 
   cstringn sh s n p ⊢ ⌜isptr p /\ Zlength s + 1 <= n <= Ptrofs.max_unsigned⌝.
Proof.
  intros; unfold cstringn.
  Intros. saturate_local. apply bi.pure_intro.
  rewrite !Zlength_app, !Zlength_map, Zlength_app in H1.
  assert (H8 := Zlength_nonneg s).
  destruct (zlt n (Zlength s + 1)).
  autorewrite with sublist in H1. lia.
  split.
  destruct p, H0; try contradiction; auto.
  autorewrite with sublist in *.
  destruct H0 as [? [_ [? _]]].
  destruct p; try contradiction.
  red in H3. 
  unfold sizeof, Ctypes.sizeof in H3;  fold Ctypes.sizeof in H3.
  rewrite Z.max_r in H3 by lia. change (Ctypes.sizeof tschar) with 1 in H3.
  pose proof (Ptrofs.unsigned_range i).
  rep_lia.
Qed.


Lemma cstringn_valid_pointer: forall {CS : compspecs} sh s n p,
     nonempty_share sh ->
     cstringn sh s n p ⊢ valid_pointer p.
Proof.
  intros.
  unfold cstringn. Intros.
  saturate_local.
  apply data_at_valid_ptr; auto.
  unfold tarray, tschar, sizeof, Ctypes.sizeof; cbv beta iota zeta.
  rewrite Z.mul_1_l.
  rewrite <- H2.
  rewrite !Zlength_app, Zlength_map, Zlength_app, Zlength_cons.
  rewrite Zlength_nil.
  rep_lia.
Qed.



Lemma Znth_zero_zero:
  forall i, Znth i [Byte.zero] = Byte.zero.
Proof.
intros.
unfold Znth.
if_tac; auto. destruct (Z.to_nat i). reflexivity. destruct n; reflexivity.
Qed.

End mpred.

#[export] Hint Resolve cstring_local_facts : saturate_local.
#[export] Hint Resolve cstring_valid_pointer : valid_pointer.
#[export] Hint Resolve cstringn_local_facts : saturate_local.
#[export] Hint Resolve cstringn_valid_pointer : valid_pointer.

(* THIS TACTIC solves goals of the form,
    ~In 0 ls,  Znth i (ls++[0]) = 0 |-  (any lia consequence of)  i < Zlength ls
    ~In 0 ls,  Znth i (ls++[0]) <> 0 |-  (any lia consequence of)  i >= Zlength ls
*)
Ltac cstring :=
  lazymatch goal with
  | H: ~In Byte.zero _ |- _ => idtac
  | |- _ => fail "The cstring tactic expects to see a hypothesis above the line of the form, ~ In Byte.zero _"
  end;
 lazymatch goal with
 | H1: Znth _ (_++[Byte.zero]) = Byte.zero |- _ => idtac 
 | H1: Znth _ (_++[Byte.zero]) <> Byte.zero |- _ => idtac 
 | |- _ => fail "The cstring tactic expects to see one of the following hypotheses above the line:
Znth _ (_++[Byte.zero]) = Byte.zero
Znth _ (_++[Byte.zero]) <> Byte.zero"
 end;
 (pose_Zlength_nonneg;
  apply Classical_Prop.NNPP; intro;
  match goal with
  | H: ~In Byte.zero ?ls, H1: Znth ?i (?ls' ++ [Byte.zero]) = Byte.zero |- _ =>
     constr_eq ls ls'; apply H; rewrite <- H1;
    rewrite app_Znth1 by lia; apply Znth_In; lia
  | H: ~In Byte.zero ?ls, H1: Znth ?i (?ls' ++ [Byte.zero]) <> Byte.zero |- _ =>
     constr_eq ls ls'; apply H1;
     rewrite -> app_Znth2 by lia; apply Znth_zero_zero
  end) ||
  match goal with |- @eq ?t (?f1 _) (?f2 _) =>
       (unify t Z || unify t nat) ||
       (constr_eq f1 f2;
        fail "The cstring tactic solves lia-style goals.
Your goal is an equality at type" t ", not type Z.
Try the [f_equal] tactic first.")
 end.

Ltac cstring' := 
lazymatch goal with
| |- @eq Z _ _ => cstring
| |- ?A _ = ?B _ => constr_eq A B; f_equal; cstring'
| |- _ => cstring
end.

Ltac cstring1 :=
match goal with 
| H: 0 <= ?x < Zlength ?s + 1,
  H1: Znth ?x (?s ++ [Byte.zero]) = Byte.zero |- _ =>
  is_var x; assert (x = Zlength s) by cstring; subst x
end.
