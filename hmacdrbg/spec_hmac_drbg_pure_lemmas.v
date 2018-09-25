Require Import compcert.lib.Coqlib.
Require Import List. Import ListNotations.
Require Import VST.floyd.functional_base.

Require Import sha.general_lemmas.
Require Import sha.HMAC256_functional_prog.

Require Import hmacdrbg.entropy.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import hmacdrbg.spec_hmac_drbg.

Lemma hmac256drbgabs_hmac_drbg_update_any_prop_key:
  forall (P: list byte -> Prop) a additional_data,
    (forall x y, P (HMAC256 x y)) ->
    P (hmac256drbgabs_key (hmac256drbgabs_hmac_drbg_update a additional_data)).
Proof.
  intros.
  destruct a; simpl.
  unfold HMAC256_DRBG_update, HMAC_DRBG_update.
  destruct additional_data; apply H.
Qed.

Lemma hmac256drbgabs_hmac_drbg_update_any_prop_V:
  forall (P: list byte -> Prop) a additional_data,
    (forall x y, P (HMAC256 x y)) ->
    P (hmac256drbgabs_value (hmac256drbgabs_hmac_drbg_update a additional_data)).
Proof.
  intros.
  destruct a; simpl.
  unfold HMAC256_DRBG_update, HMAC_DRBG_update.
  destruct additional_data; apply H.
Qed.

Lemma hmac256drbgabs_hmac_drbg_update_Zlength_key:
  forall a additional_data,
    Zlength (hmac256drbgabs_key (hmac256drbgabs_hmac_drbg_update a additional_data)) = Z.of_nat SHA256.DigestLength.
Proof.
  intros.
  apply hmac256drbgabs_hmac_drbg_update_any_prop_key.
  apply hmac_common_lemmas.HMAC_Zlength.
Qed.

Lemma hmac256drbgabs_hmac_drbg_update_Zlength_V:
  forall a additional_data,
    Zlength (hmac256drbgabs_value (hmac256drbgabs_hmac_drbg_update a additional_data)) = Z.of_nat SHA256.DigestLength.
Proof.
  intros.
  apply hmac256drbgabs_hmac_drbg_update_any_prop_V.
  apply hmac_common_lemmas.HMAC_Zlength.
Qed.

Lemma hmac256drbgabs_reseed_any_prop_key:
  forall (P: list byte -> Prop) a s additional_data,
    P (hmac256drbgabs_key a) ->
    (forall x y, P (HMAC256 x y)) ->
    P (hmac256drbgabs_key (hmac256drbgabs_reseed a s additional_data)).
Proof.
  intros.
  destruct a; simpl.
  destruct ((prediction_resistance && negb prediction_resistance)%bool); auto.
  destruct (Zlength additional_data >? 256); auto.
  destruct (get_entropy 32(*256*) entropy_len entropy_len prediction_resistance s); auto.
  unfold HMAC_DRBG_update.
  unfold hmac256drbgabs_key.
  destruct (l ++ additional_data); auto.
Qed.

Lemma hmac256drbgabs_reseed_any_prop_V:
  forall (P: list byte -> Prop) a s additional_data,
    P (hmac256drbgabs_value a) ->
    (forall x y, P (HMAC256 x y)) ->
    P (hmac256drbgabs_value (hmac256drbgabs_reseed a s additional_data)).
Proof.
  intros.
  destruct a; simpl.
  destruct ((prediction_resistance && negb prediction_resistance)%bool); auto.
  destruct (Zlength additional_data >? 256); auto.
  destruct (get_entropy 32(*256*) entropy_len entropy_len prediction_resistance s); auto.
  unfold HMAC_DRBG_update.
  unfold hmac256drbgabs_value.
  destruct (l ++ additional_data); auto.
Qed.

Lemma hmac256drbgabs_reseed_Zlength_key:
  forall a s additional_data,
    Zlength (hmac256drbgabs_key a) = Z.of_nat SHA256.DigestLength ->
    Zlength (hmac256drbgabs_key (hmac256drbgabs_reseed a s additional_data)) = Z.of_nat SHA256.DigestLength.
Proof.
  intros.
  apply hmac256drbgabs_reseed_any_prop_key; auto.
  apply hmac_common_lemmas.HMAC_Zlength.
Qed.

Lemma hmac256drbgabs_reseed_Zlength_V:
  forall a s additional_data,
    Zlength (hmac256drbgabs_value a) = Z.of_nat SHA256.DigestLength ->
    Zlength (hmac256drbgabs_value (hmac256drbgabs_reseed a s additional_data)) = Z.of_nat SHA256.DigestLength.
Proof.
  intros.
  apply hmac256drbgabs_reseed_any_prop_V; auto.
  apply hmac_common_lemmas.HMAC_Zlength.
Qed.

Lemma hmac256drbgabs_update_key_ident:
  forall a key, key = hmac256drbgabs_key a -> hmac256drbgabs_update_key a key = a.
Proof.
  intros.
  destruct a.
  simpl in H; subst.
  reflexivity.
Qed.

Lemma hmac256drbgabs_update_value_ident:
  forall a value, value = hmac256drbgabs_value a -> hmac256drbgabs_update_value a value = a.
Proof.
  intros.
  destruct a.
  simpl in H; subst.
  reflexivity.
Qed.

Lemma hmac256drbgabs_update_key_update_value_commute:
  forall a key value, hmac256drbgabs_update_value (hmac256drbgabs_update_key a key) value = hmac256drbgabs_update_key (hmac256drbgabs_update_value a value) key.
Proof.
  destruct a.
  reflexivity.
Qed.

Lemma HMAC_DRBG_update_value l key V key' V'
  (P:(key', V') = HMAC_DRBG_update HMAC256 l key V):
  Zlength V' = 32.
Proof. unfold HMAC_DRBG_update in P.
  destruct l; inv P;
  apply hmac_common_lemmas.HMAC_Zlength.
Qed.

Lemma Zlength_hmac256drbgabs_reseed_value abs s c
  (HC: Zlength c >? 256 = false) (HV: Zlength (hmac256drbgabs_value abs)=32):
  Zlength (hmac256drbgabs_value (hmac256drbgabs_reseed abs s c)) = 32.
Proof. unfold hmac256drbgabs_reseed. destruct abs.
  remember (mbedtls_HMAC256_DRBG_reseed_function s
         (HMAC256DRBGabs key V reseed_counter entropy_len
            prediction_resistance reseed_interval) c) as d.
  destruct d; trivial.
  destruct d as [[[[? ?] ?] ?] ?]; simpl.
    unfold mbedtls_HMAC256_DRBG_reseed_function, HMAC256_DRBG_reseed_function, DRBG_reseed_function in Heqd.
    rewrite andb_negb_r, HC in Heqd.
    destruct (get_entropy 32(*256*) entropy_len entropy_len prediction_resistance s); inv Heqd.
    remember (HMAC_DRBG_update HMAC256 (l1 ++ c) key V) as q.
    destruct q; inv H0. eapply HMAC_DRBG_update_value; eassumption.
Qed.

Lemma Zlength_hmac256drbgabs_update_value abs c:
  Zlength (hmac256drbgabs_value (hmac256drbgabs_hmac_drbg_update abs c)) = 32.
Proof. unfold hmac256drbgabs_hmac_drbg_update. destruct abs.
  remember (HMAC256_DRBG_update c key V) as d.
  destruct d; simpl. eapply HMAC_DRBG_update_value; eassumption.
Qed.
