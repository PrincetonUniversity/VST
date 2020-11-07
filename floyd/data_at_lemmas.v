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
Import VST.msl.predicates_hered.
Import VST.veric.res_predicates.

Lemma address_mapsto_any_sbyte_ubyte:
 forall sh b z,
 EX v2' : val, address_mapsto Mint8signed v2' sh (b, z) =
 EX v2' : val, address_mapsto Mint8unsigned v2' sh (b, z).
Proof.
intros.
apply pred_ext;
[pose (f := Byte.unsigned) | pose (f := Byte.signed)];
apply exp_left; intro v;
pose (v' := match v with Vint j => Vint (Int.repr (f (Byte.repr (Int.unsigned j))))
  | _ => Vundef
end);
apply exp_right with v';
unfold address_mapsto;
apply exp_left; intro bl; 
apply exp_right with bl;
apply andp_derives; auto;
apply prop_andp_left; intros [? [? ?]];
destruct bl as [| ? [|]]; try solve [inv H];
(rewrite prop_true_andp; [auto | 
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
End M.

Arguments deref_noload ty v / .
Arguments nested_field_array_type {cs} t gfs lo hi / .
Arguments nested_field_type {cs} t gfs / .  (* redundant? *)
Arguments nested_field_offset {cs} t gfs / .  (* redundant? *)
Arguments Z.mul !x !y.
Arguments Z.sub !m !n.
Arguments Z.add !x !y.
Global Transparent peq.
Global Transparent Archi.ptr64.

Lemma data_at_tarray_tschar_tuchar {cs: compspecs}:
  forall sh n bytes p,
  data_at sh (tarray tschar n) (map Vbyte bytes) p = data_at sh (tarray tuchar n) (map Vubyte bytes) p.
Proof.
intros.
unfold data_at, field_at.
f_equal.
f_equal.
unfold field_compatible.
simpl.
apply prop_ext; intuition; destruct p; auto;
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
f_equal; auto; [f_equal; auto | ].
+
f_equal.
destruct (zlt i (Zlength bytes)).
rewrite !Znth_map by lia.
simpl.
apply prop_ext; split; intro; 
autorewrite with norm norm1 norm2; rep_lia.
rewrite !Znth_overflow by (autorewrite with sublist; auto).
reflexivity.
+
do 2 change (unfold_reptype ?A) with A.
destruct (zlt i (Zlength bytes)).
2:
 rewrite !Znth_overflow by (autorewrite with sublist; auto);
 unfold res_predicates.address_mapsto; simpl;
 f_equal;
 extensionality bl;
 f_equal; f_equal; f_equal;
 apply prop_ext; intuition;
 destruct bl as [| ? [|]]; inv H3;
 destruct m; inv H; reflexivity.
autorewrite with sublist.
forget (Znth i bytes) as c.
unfold res_predicates.address_mapsto; simpl.
f_equal.
extensionality bl.
f_equal.
f_equal.
f_equal.
 apply prop_ext; intuition;
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
f_equal; auto.
f_equal.
repeat change (unfold_reptype ?A) with A.
destruct (zlt i (Zlength bytes)).
autorewrite with sublist.
apply prop_ext; split; intro Hx; inv Hx.
rewrite !Znth_overflow by (autorewrite with sublist; auto).
apply prop_ext; split; intro; reflexivity.
clear.
forget (Ptrofs.unsigned i0) as z.
apply M.address_mapsto_any_sbyte_ubyte.
-
f_equal.
f_equal.
f_equal.
unfold tc_val'.
destruct (zlt i (Zlength bytes)).
autorewrite with sublist.
apply prop_ext; split; intros.
red. simpl. normalize. rep_lia.
red. simpl. normalize. rep_lia.
rewrite !Znth_overflow by (autorewrite with sublist; auto).
apply prop_ext; split; intros; contradiction H2; auto.
Qed.
