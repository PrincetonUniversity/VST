Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import sha.HMAC256_functional_prog.

Fixpoint HMAC_DRBG_update_round (HMAC: list byte -> list byte -> list byte) (provided_data K V: list byte) (round: nat): (list byte * list byte) :=
  match round with
    | O => (K, V)
    | S round' =>
      let (K, V) := HMAC_DRBG_update_round HMAC provided_data K V round' in
      let K := HMAC (V ++ [Byte.repr (Z.of_nat round')] ++ provided_data) K in
      let V := HMAC V K in
      (K, V)
  end.

Definition HMAC_DRBG_update_concrete (HMAC: list byte -> list byte -> list byte) (provided_data K V: list byte): (list byte * list byte) :=
  let rounds := match provided_data with
                  | [] => 1%nat
                  | _ => 2%nat
                end in
  HMAC_DRBG_update_round HMAC provided_data K V rounds.

Theorem HMAC_DRBG_update_concrete_correct:
  forall HMAC provided_data K V, HMAC_DRBG_update HMAC provided_data K V = HMAC_DRBG_update_concrete HMAC provided_data K V.
Proof.
  intros.
  destruct provided_data; reflexivity.
Qed.

Definition update_rounds (non_empty_additional: bool): Z :=
  if non_empty_additional then 2 else 1.

Lemma HMAC_DRBG_update_round_incremental:
  forall key V initial_state_abs contents n,
    (key, V) = HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) n ->
    (HMAC256 (V ++ Byte.repr (Z.of_nat n) :: contents) key,
     HMAC256 V (HMAC256 (V ++ Byte.repr (Z.of_nat n) :: contents) key)) =
    HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) (n + 1).
Proof.
  intros.
  rewrite plus_comm.
  simpl.
  rewrite <- H.
  reflexivity.
Qed.

Lemma HMAC_DRBG_update_round_incremental_Z:
  forall key V initial_state_abs contents i,
    0 <= i ->
    (key, V) = HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) (Z.to_nat i) ->
    (HMAC256 (V ++ Byte.repr i :: contents) key,
     HMAC256 V (HMAC256 (V ++ Byte.repr i :: contents) key)) =
    HMAC_DRBG_update_round HMAC256 contents
                           (hmac256drbgabs_key initial_state_abs)
                           (hmac256drbgabs_value initial_state_abs) (Z.to_nat (i + 1)).
Proof.
  intros.
  specialize (HMAC_DRBG_update_round_incremental _ _ _ _ _ H0); intros. clear H0.
  rewrite (Z2Nat.id _ H) in H1.
  rewrite Z2Nat.inj_add; try assumption; omega.
Qed.

Lemma update_char add_len contents (HL:add_len = Zlength contents \/ add_len = 0)
       (key1 V0 : list byte) additional reseed_counter entropy_len prediction_resistance V key0
     reseed_interval
    (H : (key1, V0) =
    HMAC_DRBG_update_round HMAC256 (contents_with_add additional add_len contents) key0 V
      (Z.to_nat
         (if
           (negb (Memory.EqDec_val additional nullval) &&
            negb (initial_world.EqDec_Z add_len 0))%bool
          then 2
          else 1))):
hmac256drbgabs_hmac_drbg_update
  (HMAC256DRBGabs key0 V reseed_counter entropy_len prediction_resistance
     reseed_interval) (contents_with_add additional add_len contents) =
HMAC256DRBGabs key1 V0 reseed_counter entropy_len prediction_resistance
  reseed_interval.
Proof. rename key0 into K. rename V0 into VV. rename key1 into KK.
unfold hmac256drbgabs_hmac_drbg_update, HMAC256_DRBG_functional_prog.HMAC256_DRBG_update.
rewrite HMAC_DRBG_update_concrete_correct. unfold HMAC_DRBG_update_concrete, contents_with_add in *; simpl in *.
destruct (Memory.EqDec_val additional nullval); simpl in *.
+ inv H; trivial.
+ destruct (initial_world.EqDec_Z add_len 0).
  -  subst add_len. change (negb (left eq_refl)) with false in *. simpl. simpl in H. inv H; trivial.
  - change (negb (right n0)) with true in *. simpl.
    destruct HL; try omega; subst add_len.
    destruct contents. rewrite Zlength_nil in n0; omega. 
    change  (Z.to_nat 2) with 2%nat in H. rewrite <- H; trivial.
Qed. 