Require Import floyd.proofauto.
Local Open Scope logic.
Require Import List. Import ListNotations.
Require Import general_lemmas.
Require Import Snuffle. 
Require Import Salsa20.
Require Import ZArith. 

Require Import tweetnaclVerifiableC.
Require Import spec_salsa.
Require Import verif_salsa_base.
Opaque Snuffle20. Opaque prepare_data. Opaque Snuffle.Snuffle.

Lemma crypto_core_salsa20_ok: semax_body SalsaVarSpecs SalsaFunSpecs
      f_crypto_core_salsa20_tweet crypto_core_salsa20_spec.
Proof. unfold crypto_core_salsa20_spec.
start_function.
name out' _out.
name in' _in.
name k' _k.
name c' _c.
normalize. 
forward_call (c, k, Z0, nonce, out, OUT, data) l.
forward. apply (exp_right l).
entailer. unfold fcore_result in H.
remember (Snuffle20 (prepare_data data)) as d; symmetry in Heqd.
destruct d. 2: inv H. rewrite Int.eq_true in H.
apply prop_right. exists l0; split; trivial. 
Qed.

Lemma prepare_data_length data: length (prepare_data data) = 16%nat.
Proof.
destruct data as[[Nonce C] [K L]].
destruct C as [[[C1 C2] C3] C4]. 
destruct Nonce as [[[N1 N2] N3] N4].
destruct K as [[[K1 K2] K3] K4].  
destruct L as [[[L1 L2] L3] L4]. reflexivity.
Qed.

Lemma Snuffle_sub_simpl data x:
    Snuffle20 (prepare_data data) = Some x -> 
    exists s, Snuffle 20 (prepare_data data) = Some s /\
    forall i (I:0 <= i < 16) v,
      Znth i (prepare_data data) Int.zero = v ->
      littleendian_invert (Int.sub (Znth i x Int.zero) v) =
      littleendian_invert (Znth i s Int.zero).
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
name out' _out.
name in' _in.
name k' _k.
name c' _c.
normalize. 
forward_call (c, k, 1, nonce, out, OUT, data) l.
forward. apply (exp_right l).
entailer.
apply prop_right. clear - H. unfold fcore_result in H.
remember (Snuffle20 (prepare_data data)) as d; symmetry in Heqd.
destruct d. 2: inv H. rewrite Int.eq_false in H.
apply Snuffle_sub_simpl in Heqd. destruct Heqd as [s [SN I]].
rewrite SN; clear SN. exists s; split; trivial.
destruct data as[[Nonce C] [K L]].
destruct C as [[[C1 C2] C3] C4]. 
destruct Nonce as [[[N1 N2] N3] N4].
destruct K as [[[K1 K2] K3] K4].  
destruct L as [[[L1 L2] L3] L4]. 
rewrite I in H.
rewrite I in H.
rewrite I in H.
rewrite I in H.
rewrite I in H.
rewrite I in H.
rewrite I in H.
rewrite I in H. assumption.
omega. reflexivity.
omega. reflexivity.
omega. reflexivity.
omega. reflexivity.
omega. reflexivity.
omega. reflexivity.
omega. reflexivity.
omega. reflexivity.
apply Int.one_not_zero.
Qed.