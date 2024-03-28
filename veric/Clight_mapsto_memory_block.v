Require Import VST.veric.base.
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

Require Import compcert.export.Clightdefs.

Section mpred.

Context `{!heapGS Σ}.

Lemma address_mapsto_unsigned_signed:
 forall sign1 sign2 sh sz l i ch1 ch2
  (Hch1 : access_mode (Tint sz sign1 noattr) = By_value ch1)
  (Hch2 : access_mode (Tint sz sign2 noattr) = By_value ch2)
  (Hsize : size_chunk_nat ch1 = size_chunk_nat ch2)
  (Halign : align_chunk ch1 = align_chunk ch2),
  address_mapsto ch1 (Vint (Cop.cast_int_int sz sign1 i)) sh l ⊣⊢
  address_mapsto ch2 (Vint (Cop.cast_int_int sz sign2 i)) sh l.
Proof.
  intros; rewrite /address_mapsto.
  apply bi.exist_proper; intros bl.
  rewrite Hsize Halign; apply bi.and_proper; try done.
  apply bi.pure_proper.
  rewrite /decode_val /Cop.cast_int_int.
  destruct sz; try solve [inv Hch1; inv Hch2; auto]; destruct sign1, sign2; inv Hch1; inv Hch2; auto.
  * destruct bl; try (intuition; discriminate); destruct bl; try (intuition; discriminate); simpl.
    destruct m; try (intuition; discriminate).
    split; [rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)), <- (Int.zero_ext_sign_ext _ i) by lia
          | rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)), <- (Int.sign_ext_zero_ext _ i) by lia]; intuition; congruence.
  * destruct bl; try (intuition; discriminate); destruct bl; try (intuition; discriminate); simpl.
    destruct m; try (intuition; discriminate).
    split; [rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)), <- (Int.sign_ext_zero_ext _ i) by lia
          | rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)), <- (Int.zero_ext_sign_ext _ i) by lia]; intuition; congruence.
  * destruct bl; try (split; intros [??]; discriminate); destruct bl; try (split; intros [??]; discriminate); destruct bl; try (split; intros [??]; discriminate); simpl.
    destruct m; try (split; intros [?[??]]; discriminate); destruct m0; try (split; intros [?[??]]; discriminate).
    split; [rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)), <- (Int.zero_ext_sign_ext _ i) by lia
          | rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)), <- (Int.sign_ext_zero_ext _ i) by lia]; intuition; congruence.
  * destruct bl; try (split; intros [??]; discriminate); destruct bl; try (split; intros [??]; discriminate); destruct bl; try (split; intros [??]; discriminate); simpl.
    destruct m; try (split; intros [?[??]]; discriminate); destruct m0; try (split; intros [?[??]]; discriminate).
    split; [rewrite <- (Int.sign_ext_zero_ext _ (Int.repr _)), <- (Int.sign_ext_zero_ext _ i) by lia
           | rewrite <- (Int.zero_ext_sign_ext _ (Int.repr _)), <- (Int.zero_ext_sign_ext _ i) by lia]; intuition; congruence.
Qed.

Lemma mapsto_unsigned_signed:
 forall sign1 sign2 sh sz v i,
  mapsto sh (Tint sz sign1 noattr) v (Vint (Cop.cast_int_int sz sign1 i)) ⊣⊢
  mapsto sh (Tint sz sign2 noattr) v (Vint (Cop.cast_int_int sz sign2 i)).
Proof.
  intros.
  unfold mapsto.
  assert (exists ch1 ch2, access_mode (Tint sz sign1 noattr) = By_value ch1 /\ access_mode (Tint sz sign2 noattr) = By_value ch2 /\
    size_chunk_nat ch1 = size_chunk_nat ch2 /\ align_chunk ch1 = align_chunk ch2) as (ch1 & ch2 & Hch1 & Hch2 & Hsize & Halign).
  { destruct sz; simpl; eauto 7; destruct sign1, sign2; eauto 7. }
  rewrite /type_is_volatile Hch1 Hch2 /=.
  destruct v; auto.
  if_tac; auto.
  - apply bi.or_proper; [apply bi.and_proper|].
    + apply bi.pure_proper; destruct sz; try done; rewrite /Cop.cast_int_int; destruct sign1, sign2; try done; split; intros;
        first [ apply (expr_lemmas3.sign_ext_range' 8 i); compute; split; congruence
          | apply (expr_lemmas3.sign_ext_range' 16 i); compute; split; congruence
          | apply (expr_lemmas3.zero_ext_range' 8 i); compute; split; congruence
          | apply (expr_lemmas3.zero_ext_range' 16 i); compute; split; congruence
          ].
    + apply address_mapsto_unsigned_signed; auto.
    + rewrite -> !(bi.pure_False (Vint _ = Vundef)) by discriminate; by rewrite !bi.False_and.
  - apply bi.and_proper.
    + apply bi.pure_proper; rewrite Halign; destruct sz; try done; rewrite /Cop.cast_int_int; destruct sign1, sign2; try reflexivity; split; intros [TC ?]; (split; [|assumption]); intros _; specialize (TC ltac:(discriminate));
        first [ apply (expr_lemmas3.sign_ext_range' 8 i); compute; split; congruence
          | apply (expr_lemmas3.sign_ext_range' 16 i); compute; split; congruence
          | apply (expr_lemmas3.zero_ext_range' 8 i); compute; split; congruence
          | apply (expr_lemmas3.zero_ext_range' 16 i); compute; split; congruence
          ].
    + by rewrite !size_chunk_conv Hsize.
Qed.

Lemma mapsto_tuint_tint:
  forall sh, mapsto sh tuint = mapsto sh tint.
Proof.
intros. apply mapsto_tuint_tint.
Qed.

Lemma mapsto_null_mapsto_pointer:
  forall t sh v,
   Archi.ptr64 = false -> 
             mapsto sh tint v nullval ⊣⊢
             mapsto sh (tptr t) v nullval.
Proof.
  exact mapsto_null_mapsto_pointer.
Qed.

End mpred.

Lemma tc_val_pointer_nullval:
 forall t, tc_val (tptr t) nullval.
Proof.
 intros. apply tc_val_pointer_nullval.
Qed.
#[export] Hint Resolve tc_val_pointer_nullval : core.
