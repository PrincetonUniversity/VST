Require Import VST.floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import tweetnacl20140427.Snuffle.
Require Import tweetnacl20140427.Salsa20.
Require Import ZArith.

Require Import tweetnacl20140427.tweetnaclVerifiableC.
Require Import tweetnacl20140427.spec_salsa.
Require Import tweetnacl20140427.verif_salsa_base.
Opaque Snuffle20. Opaque prepare_data. Opaque Snuffle.Snuffle.

Lemma crypto_core_salsa20_ok: semax_body SalsaVarSpecs SalsaFunSpecs
      f_crypto_core_salsa20_tweet crypto_core_salsa20_spec.
Proof. unfold crypto_core_salsa20_spec.
start_function.
abbreviate_semax.
assert_PROP (field_compatible (tarray tuchar 64) [] out /\ isptr out) as HH by entailer!.
destruct HH as [FCout isptrout].
Time forward_call (c, k, Z0, nonce, out, default_val (tarray tuchar 64), data). (*1.8*)
  unfold data_at_, field_at_. rewrite field_at_data_at.
  rewrite field_address_offset by auto with field_compatible.
  rewrite isptr_offset_val_zero; trivial. cancel.
Intros ret.
Time forward. (*1.7*)
unfold fcore_result in H.
  remember (Snuffle20 (prepare_data data)) as d; symmetry in Heqd.
  destruct d. 2: inv H. rewrite Int.eq_true in H.
Exists l.
Time entailer!. apply derives_refl.
Time Qed. (*4.3*)

Lemma Snuffle_sub_simpl data x:
    Snuffle20 (prepare_data data) = Some x ->
    exists s, Snuffle 20 (prepare_data data) = Some s /\
    forall i (I:0 <= i < 16) v,
      Znth i (prepare_data data) = v ->
      littleendian_invert (Int.sub (Znth i x) v) =
      littleendian_invert (Znth i s).
Proof. intros.
Transparent Snuffle20. unfold Snuffle20 in H. Opaque Snuffle20.
remember (Snuffle 20 (prepare_data data)) as sn.
destruct sn; simpl in H. 2: inv H. clear Heqsn.
exists l; split; trivial.
intros. rewrite (sumlist_char_Znth _ _ _ H).
  rewrite Int.add_commut, Int.sub_add_l, H0, Int.sub_idem, Int.add_zero_l. trivial.
symmetry in H; apply sumlist_length in H.
rewrite Zlength_correct, H, prepare_data_length; trivial.
Qed.

Lemma crypto_core_hsalsa20_ok: semax_body SalsaVarSpecs SalsaFunSpecs
      f_crypto_core_hsalsa20_tweet crypto_core_hsalsa20_spec.
Proof. unfold crypto_core_hsalsa20_spec.
start_function.
Time forward_call (c, k, 1, nonce, out, OUT, data). (*1.4*)
Intros res.
Time forward. (*1.6*)
unfold fcore_result in H.
  remember (Snuffle20 (prepare_data data)) as d; symmetry in Heqd.
  destruct d. 2: inv H. rewrite Int.eq_false in H.
destruct (Snuffle_sub_simpl _ _ Heqd) as [x [X1 X2]].
Exists x.
Time entailer!. (*0.6*)
2: apply Int.one_not_zero.
unfold fcorePOST_SEP; cancel.
  destruct data as[[Nonce C] [K L]].
  destruct C as [[[C1 C2] C3] C4].
  destruct Nonce as [[[N1 N2] N3] N4].
  destruct K as [[[K1 K2] K3] K4].
  destruct L as [[[L1 L2] L3] L4].
apply derives_refl'. f_equal.
  do 8 rewrite X2 in H by (try omega; reflexivity).
  apply H.
Time Qed. (*2.8*)