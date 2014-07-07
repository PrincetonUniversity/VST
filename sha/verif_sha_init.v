Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.sha_lemmas.
Require Import sha.spec_sha.
Local Open Scope nat.
Local Open Scope logic.

Lemma ZnthV_nil_None:
  forall t, ZnthV t nil = fun _ => default_val t.
Proof.
unfold ZnthV; intros.
extensionality i; if_tac; auto.
rewrite nth_overflow; auto.
simpl; omega.
Qed.

Lemma body_SHA256_Init: semax_body Vprog Gtot f_SHA256_Init SHA256_Init_spec.
Proof.
start_function.
name c_ _c.
unfold data_at_.
unfold_data_at 1%nat.
rewrite (field_at_data_at) with (ids := [_h]) by reflexivity.
rewrite at_offset'_eq by (rewrite <- data_at_offset_zero; reflexivity).
unfold nested_field_type2; simpl; unfold tarray.
erewrite data_at_array_at by reflexivity.
normalize.
do 8 (forward;normalize; rewrite upd_Znth_next by (compute; reflexivity); simpl app).
forward. (* c->Nl=0; *)
forward. (* c->Nh=0; *)
forward. (* c->num=0; *)
forward. (* return; *)
unfold sha256state_.
apply exp_right with (map Vint init_registers, 
      (Vint Int.zero, (Vint Int.zero, (nil, Vint Int.zero)))).
unfold_data_at 1%nat.
rewrite (field_at_data_at) with (ids := [_h]) by reflexivity.
rewrite at_offset'_eq by (rewrite <- data_at_offset_zero; reflexivity).
unfold nested_field_type2; simpl nested_field_rec; unfold tarray.
erewrite data_at_array_at by reflexivity.
entailer!.
repeat split; auto.
rewrite hash_blocks_equation. reflexivity.
exists Int.zero, Int.zero; repeat split; reflexivity.
exists 0%Z; simpl; reflexivity.
apply derives_refl'; f_equal.
f_equal.
repeat (apply f_equal2; [f_equal; apply int_eq_e; compute; reflexivity | ]); auto.
Qed.
