Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import floyd.sublist.

Require Import sha.HMAC256_functional_prog.
Require Import sha.general_lemmas.
Require Import sha.spec_sha.

Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.HMAC_DRBG_pure_lemmas.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import hmacdrbg.entropy.
Require Import hmacdrbg.entropy_lemmas.

Definition mpred_passed_to_function (F: mpred) (cond: bool): mpred :=
  if cond then emp else F.

Definition mpred_passed_to_frame (F: mpred) (cond: bool): mpred :=
  if cond then F else emp.

Lemma mpred_cond_correct:
  forall F cond, F = mpred_passed_to_function F cond * mpred_passed_to_frame F cond.
Proof.
  intros.
  destruct cond.
  simpl; symmetry; apply emp_sepcon.
  simpl; symmetry; apply sepcon_emp.
Qed.

Lemma metadata_preserved:
  forall key key0 V V0 reseed_counter reseed_counter0 entropy_len entropy_len0 prediction_resistance prediction_resistance0 reseed_interval reseed_interval0 contents done s,
  HMAC256DRBGabs key0 V0 reseed_counter0
                              entropy_len0 prediction_resistance0
                              reseed_interval0 =
                            hmac256drbgabs_hmac_drbg_update
                              (hmac256drbgabs_update_value
                                 (if if (prediction_resistance
                                         || (reseed_counter >?
                                             reseed_interval))%bool
                                     then false
                                     else
                                      match contents with
                                      | [] => false
                                      | _ :: _ => true
                                      end
                                  then
                                   hmac256drbgabs_hmac_drbg_update
                                     (HMAC256DRBGabs key V reseed_counter
                                        entropy_len prediction_resistance
                                        reseed_interval) contents
                                  else
                                   if (prediction_resistance
                                       || (reseed_counter >? reseed_interval))%bool
                                   then
                                    hmac256drbgabs_reseed
                                      (HMAC256DRBGabs key V reseed_counter
                                         entropy_len prediction_resistance
                                         reseed_interval) s contents
                                   else
                                    HMAC256DRBGabs key V reseed_counter
                                      entropy_len prediction_resistance
                                      reseed_interval)
                                 (fst
                                    (HMAC_DRBG_generate_helper_Z HMAC256
                                       (hmac256drbgabs_key
                                          (if if (prediction_resistance
                                                  || 
                                                  (reseed_counter >?
                                                  reseed_interval))%bool
                                              then false
                                              else
                                               match contents with
                                               | [] => false
                                               | _ :: _ => true
                                               end
                                           then
                                            hmac256drbgabs_hmac_drbg_update
                                              (HMAC256DRBGabs key V
                                                 reseed_counter entropy_len
                                                 prediction_resistance
                                                 reseed_interval) contents
                                           else
                                            if (prediction_resistance
                                                || 
                                                (reseed_counter >?
                                                 reseed_interval))%bool
                                            then
                                             hmac256drbgabs_reseed
                                               (HMAC256DRBGabs key V
                                                  reseed_counter entropy_len
                                                  prediction_resistance
                                                  reseed_interval) s contents
                                            else
                                             HMAC256DRBGabs key V
                                               reseed_counter entropy_len
                                               prediction_resistance
                                               reseed_interval))
                                       (hmac256drbgabs_value
                                          (if if (prediction_resistance
                                                  || 
                                                  (reseed_counter >?
                                                  reseed_interval))%bool
                                              then false
                                              else
                                               match contents with
                                               | [] => false
                                               | _ :: _ => true
                                               end
                                           then
                                            hmac256drbgabs_hmac_drbg_update
                                              (HMAC256DRBGabs key V
                                                 reseed_counter entropy_len
                                                 prediction_resistance
                                                 reseed_interval) contents
                                           else
                                            if (prediction_resistance
                                                || 
                                                (reseed_counter >?
                                                 reseed_interval))%bool
                                            then
                                             hmac256drbgabs_reseed
                                               (HMAC256DRBGabs key V
                                                  reseed_counter entropy_len
                                                  prediction_resistance
                                                  reseed_interval) s contents
                                            else
                                             HMAC256DRBGabs key V
                                               reseed_counter entropy_len
                                               prediction_resistance
                                               reseed_interval)) done)))
                              (if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then []
                               else contents) ->
  entropy_len = entropy_len0 /\ prediction_resistance = prediction_resistance0 /\ reseed_interval = reseed_interval0.
Proof.
  unfold hmac256drbgabs_reseed.
  unfold mbedtls_HMAC256_DRBG_reseed_function.
  unfold mbedtls_HMAC256_DRBG_generate_function.
  unfold HMAC256_DRBG_generate_function, HMAC256_DRBG_reseed_function.
  unfold DRBG_generate_function, DRBG_reseed_function.
  unfold DRBG_generate_function_helper.
  unfold HMAC256_DRBG_generate_algorithm.
  unfold HMAC_DRBG_generate_algorithm.
  unfold hmac256drbgabs_key.
  unfold hmac256drbgabs_value.
  unfold hmac256drbgabs_update_value.
  unfold hmac256drbgabs_hmac_drbg_update.
  unfold hmac256drbgabs_increment_reseed_counter.
  unfold hmac256drbgabs_to_state_handle.
  unfold HMAC256_DRBG_reseed_algorithm.
  unfold HMAC_DRBG_reseed_algorithm.
  unfold HMAC256_DRBG_update.
  unfold HMAC_DRBG_update.
  intros.
  destruct (match contents with
                | [] =>
                    (HMAC256 (V ++ [0] ++ contents) key,
                    HMAC256 V (HMAC256 (V ++ [0] ++ contents) key))
                | _ :: _ =>
                    (HMAC256
                       (HMAC256 V (HMAC256 (V ++ [0] ++ contents) key) ++
                        [1] ++ contents) (HMAC256 (V ++ [0] ++ contents) key),
                    HMAC256 (HMAC256 V (HMAC256 (V ++ [0] ++ contents) key))
                      (HMAC256
                         (HMAC256 V (HMAC256 (V ++ [0] ++ contents) key) ++
                          [1] ++ contents)
                         (HMAC256 (V ++ [0] ++ contents) key)))
                end).
  remember (prediction_resistance || (reseed_counter >? reseed_interval))%bool as should_reseed; clear Heqshould_reseed.
  remember (if should_reseed
                          then false
                          else
                           match contents with
                           | [] => false
                           | _ :: _ => true
                           end) as non_empty_additional; clear Heqnon_empty_additional.
  destruct non_empty_additional.
  {
    destruct should_reseed; destruct contents; inv H; auto.
  }
  destruct should_reseed.
  {
    rewrite andb_negb_r in H.
    destruct (Zlength contents >? 256); [inv H; auto| ].
    destruct (get_entropy 256 entropy_len entropy_len prediction_resistance s); [|inv H; auto].
    destruct (l1 ++ contents); inv H; auto.
  }
  {
    destruct contents; inv H; auto.
  }
Qed.

Lemma reseed_counter_values:
  forall key key0 V V0 reseed_counter reseed_counter0 entropy_len entropy_len0 prediction_resistance prediction_resistance0 reseed_interval reseed_interval0 contents done s,
  HMAC256DRBGabs key0 V0 reseed_counter0
                              entropy_len0 prediction_resistance0
                              reseed_interval0 =
                            hmac256drbgabs_hmac_drbg_update
                              (hmac256drbgabs_update_value
                                 (if if (prediction_resistance
                                         || (reseed_counter >?
                                             reseed_interval))%bool
                                     then false
                                     else
                                      match contents with
                                      | [] => false
                                      | _ :: _ => true
                                      end
                                  then
                                   hmac256drbgabs_hmac_drbg_update
                                     (HMAC256DRBGabs key V reseed_counter
                                        entropy_len prediction_resistance
                                        reseed_interval) contents
                                  else
                                   if (prediction_resistance
                                       || (reseed_counter >? reseed_interval))%bool
                                   then
                                    hmac256drbgabs_reseed
                                      (HMAC256DRBGabs key V reseed_counter
                                         entropy_len prediction_resistance
                                         reseed_interval) s contents
                                   else
                                    HMAC256DRBGabs key V reseed_counter
                                      entropy_len prediction_resistance
                                      reseed_interval)
                                 (fst
                                    (HMAC_DRBG_generate_helper_Z HMAC256
                                       (hmac256drbgabs_key
                                          (if if (prediction_resistance
                                                  || 
                                                  (reseed_counter >?
                                                  reseed_interval))%bool
                                              then false
                                              else
                                               match contents with
                                               | [] => false
                                               | _ :: _ => true
                                               end
                                           then
                                            hmac256drbgabs_hmac_drbg_update
                                              (HMAC256DRBGabs key V
                                                 reseed_counter entropy_len
                                                 prediction_resistance
                                                 reseed_interval) contents
                                           else
                                            if (prediction_resistance
                                                || 
                                                (reseed_counter >?
                                                 reseed_interval))%bool
                                            then
                                             hmac256drbgabs_reseed
                                               (HMAC256DRBGabs key V
                                                  reseed_counter entropy_len
                                                  prediction_resistance
                                                  reseed_interval) s contents
                                            else
                                             HMAC256DRBGabs key V
                                               reseed_counter entropy_len
                                               prediction_resistance
                                               reseed_interval))
                                       (hmac256drbgabs_value
                                          (if if (prediction_resistance
                                                  || 
                                                  (reseed_counter >?
                                                  reseed_interval))%bool
                                              then false
                                              else
                                               match contents with
                                               | [] => false
                                               | _ :: _ => true
                                               end
                                           then
                                            hmac256drbgabs_hmac_drbg_update
                                              (HMAC256DRBGabs key V
                                                 reseed_counter entropy_len
                                                 prediction_resistance
                                                 reseed_interval) contents
                                           else
                                            if (prediction_resistance
                                                || 
                                                (reseed_counter >?
                                                 reseed_interval))%bool
                                            then
                                             hmac256drbgabs_reseed
                                               (HMAC256DRBGabs key V
                                                  reseed_counter entropy_len
                                                  prediction_resistance
                                                  reseed_interval) s contents
                                            else
                                             HMAC256DRBGabs key V
                                               reseed_counter entropy_len
                                               prediction_resistance
                                               reseed_interval)) done)))
                              (if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then []
                               else contents) ->
  reseed_counter0 = 1 \/ reseed_counter0 = reseed_counter.
Proof.
  unfold hmac256drbgabs_reseed.
  unfold mbedtls_HMAC256_DRBG_reseed_function.
  unfold mbedtls_HMAC256_DRBG_generate_function.
  unfold HMAC256_DRBG_generate_function, HMAC256_DRBG_reseed_function.
  unfold DRBG_generate_function, DRBG_reseed_function.
  unfold DRBG_generate_function_helper.
  unfold HMAC256_DRBG_generate_algorithm.
  unfold HMAC_DRBG_generate_algorithm.
  unfold hmac256drbgabs_key.
  unfold hmac256drbgabs_value.
  unfold hmac256drbgabs_update_value.
  unfold hmac256drbgabs_hmac_drbg_update.
  unfold hmac256drbgabs_increment_reseed_counter.
  unfold hmac256drbgabs_to_state_handle.
  unfold HMAC256_DRBG_reseed_algorithm.
  unfold HMAC_DRBG_reseed_algorithm.
  unfold HMAC256_DRBG_update.
  unfold HMAC_DRBG_update.
  intros.
  destruct (match contents with
                | [] =>
                    (HMAC256 (V ++ [0] ++ contents) key,
                    HMAC256 V (HMAC256 (V ++ [0] ++ contents) key))
                | _ :: _ =>
                    (HMAC256
                       (HMAC256 V (HMAC256 (V ++ [0] ++ contents) key) ++
                        [1] ++ contents) (HMAC256 (V ++ [0] ++ contents) key),
                    HMAC256 (HMAC256 V (HMAC256 (V ++ [0] ++ contents) key))
                      (HMAC256
                         (HMAC256 V (HMAC256 (V ++ [0] ++ contents) key) ++
                          [1] ++ contents)
                         (HMAC256 (V ++ [0] ++ contents) key)))
                end).
  remember (prediction_resistance || (reseed_counter >? reseed_interval))%bool as should_reseed; clear Heqshould_reseed.
  remember (if should_reseed
                          then false
                          else
                           match contents with
                           | [] => false
                           | _ :: _ => true
                           end) as non_empty_additional; clear Heqnon_empty_additional.
  destruct non_empty_additional.
  {
    destruct should_reseed; destruct contents; inv H; auto.
  }
  destruct should_reseed.
  {
    rewrite andb_negb_r in H.
    destruct (Zlength contents >? 256); [inv H; auto| ].
    destruct (get_entropy 256 entropy_len entropy_len prediction_resistance s); [|inv H; auto].
    destruct (l1 ++ contents); inv H; auto.
  }
  {
    destruct contents; inv H; auto.
  }
Qed.

Lemma while_loop_post_incremental_snd:
  forall key0 V0 n out_len,
    0 <= (n * 32)%Z <= out_len ->
    (n * 32)%Z <> out_len ->
 snd (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z) ++
 fst
   (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
      ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))) =
 snd
   (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
      ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))).
Proof.
  intros.
  rewrite Zmin_spec.
  destruct (Z_lt_ge_dec 32 (out_len - (n * 32))) as [Hmin | Hmin].
  {
    rewrite zlt_true by assumption.
    apply HMAC_DRBG_generate_helper_Z_incremental_snd; auto; omega.
  }
  {
    rewrite zlt_false by assumption.
    assert (0 < out_len - (n * 32)%Z <= 32).
    {
      split.
      rewrite <- Z2Nat.id in *; try omega.
      remember (Z.to_nat (out_len - n * 32)) as n'; destruct n'.
      {
        (* contradiction. out_len - n <> 0 *)
        assert (0 = out_len - n * 32).
        {
          symmetry;
          apply Z2Nat_inj_0.
          omega.
          symmetry; assumption.
        }
        assert (out_len = (n * 32)%Z) by omega.
        omega.
      }
      rewrite Nat2Z.inj_succ.
      omega.
      omega.
    }
    assert (exists n', (n * 32)%Z = (n' * 32)%Z).
    {
      exists n; reflexivity.
    }
    rewrite HMAC_DRBG_generate_helper_Z_incremental_equiv; auto; try omega.
    apply HMAC_DRBG_generate_helper_Z_incremental_snd; auto; omega.
  }
Qed.

Lemma while_loop_post_incremental_fst:
  forall key0 V0 n out_len,
    0 <= (n * 32)%Z <= out_len ->
    (n * 32)%Z <> out_len ->
  fst (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
      ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))) =
 HMAC256 (fst (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z)) key0.
Proof.
  intros.
  rewrite Zmin_spec.
  destruct (Z_lt_ge_dec 32 (out_len - (n * 32))) as [Hmin | Hmin].
  {
    rewrite zlt_true by assumption.
    symmetry; apply HMAC_DRBG_generate_helper_Z_incremental_fst; auto; omega.
  }
  {
    rewrite zlt_false by assumption.
    assert (0 < out_len - (n * 32)%Z <= 32).
    {
      split.
      rewrite <- Z2Nat.id in *; try omega.
      remember (Z.to_nat (out_len - n * 32)) as n'; destruct n'.
      {
        (* contradiction. out_len - n <> 0 *)
        assert (0 = out_len - n * 32).
        {
          symmetry;
          apply Z2Nat_inj_0.
          omega.
          symmetry; assumption.
        }
        assert (out_len = (n * 32)%Z) by omega.
        omega.
      }
      rewrite Nat2Z.inj_succ.
      omega.
      omega.
    }
    assert (exists n', (n * 32)%Z = (n' * 32)%Z).
    {
      exists n; reflexivity.
    }
    rewrite HMAC_DRBG_generate_helper_Z_incremental_equiv; auto; try omega.
    symmetry; apply HMAC_DRBG_generate_helper_Z_incremental_fst; auto; omega.
  }
Qed.

Lemma while_loop_post_sublist_app:
  forall key0 V0 n out_len,
    0 <= (n * 32)%Z <= out_len ->
    Zlength V0 = 32 ->
  sublist 0 (n * 32)
     (snd (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32))) ++
   sublist 0 (Z.min 32 (out_len - n * 32))
     (fst
        (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
           (n * 32 + Z.min 32 (out_len - n * 32)))) =
   sublist 0 (n * 32 + Z.min 32 (out_len - n * 32))
     (snd (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)) ++
      fst
        (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
           (n * 32 + Z.min 32 (out_len - n * 32)))).
Proof.
  intros.
  remember (snd (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32))) as A.
  assert (HlengthA: Zlength A = (n * 32)%Z).
  {
    subst.
    apply HMAC_DRBG_generate_helper_Z_Zlength_snd.
    omega.
    apply hmac_common_lemmas.HMAC_Zlength.
    exists n; reflexivity.
  }
  clear HeqA.
  remember (fst
        (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
           (n * 32 + Z.min 32 (out_len - n * 32)))) as B.
  assert (HlengthB: Zlength B = 32).
  {
    subst.
    apply HMAC_DRBG_generate_helper_Z_Zlength_fst.
    rewrite Zmin_spec.
    destruct (Z_lt_ge_dec 32 (out_len - (n * 32))) as [Hmin | Hmin].
    rewrite zlt_true by assumption; omega.
    rewrite zlt_false by assumption; omega.
    assumption.
    apply hmac_common_lemmas.HMAC_Zlength.
  }
  clear HeqB.
  rewrite <- HlengthA in *.
  rewrite <- HlengthB in *.
  clear - H HlengthB.
  rewrite sublist_same; auto.
  rewrite sublist_app; try now (
    rewrite Zmin_spec;
    destruct (Z_lt_ge_dec (Zlength B) (out_len - (Zlength A))) as [Hmin | Hmin]; [rewrite zlt_true by assumption| rewrite zlt_false by assumption]; omega).
  assert (Hmin0: Z.min 0 (Zlength A) = 0).
  {
    rewrite Zmin_spec.
    rewrite <- (Z2Nat.id (Zlength A)) in *; try apply Zlength_nonneg.
    destruct (Z.to_nat (Zlength A)).
    reflexivity.
    reflexivity.
  }
  rewrite Hmin0.
  assert (HminA: (Z.min (Zlength A + Z.min (Zlength B) (out_len - Zlength A)) (Zlength A)) = Zlength A).
  {
    rewrite Zmin_spec.
    rewrite zlt_false; auto.
    destruct (Z.min_dec (Zlength B) (out_len - Zlength A)) as [Hmin | Hmin]; rewrite Hmin; omega.
  }
  rewrite HminA.
  rewrite sublist_same with (hi:=Zlength A); try omega.
  assert (Hmax0: (Z.max (0 - Zlength A) 0) = 0).
  {
    rewrite Zmax_spec.
    rewrite zlt_false; auto; omega.
  }
  rewrite Hmax0.
  replace (Zlength A + Z.min (Zlength B) (out_len - Zlength A) - Zlength A) with (Z.min (Zlength B) (out_len - Zlength A)) by omega.
  assert (HmaxB: (Z.max (Z.min (Zlength B) (out_len - Zlength A)) 0) = (Z.min (Zlength B) (out_len - Zlength A))).
  {
    rewrite <- (Z2Nat.id (out_len - Zlength A)) in *; try omega.
    destruct (Z.to_nat (out_len - Zlength A)).
    {
      simpl.
      destruct (Z.min_dec (Zlength B) 0) as [Hmin | Hmin]; rewrite Hmin; try rewrite HlengthB; auto.
    }
    rewrite Zmax_spec.
    rewrite zlt_true; auto.
    rewrite Nat2Z.inj_succ.
    destruct (Z.min_dec (Zlength B) (Z.succ (Z.of_nat n))) as [Hmin | Hmin]; rewrite Hmin; omega.
  }
  rewrite HmaxB.
  reflexivity.
Qed.    
    
Lemma generate_correct:
  forall should_reseed non_empty_additional s initial_state_abs out_len contents,
    hmac256drbgabs_reseed_interval initial_state_abs = 10000 ->
    hmac256drbgabs_entropy_len initial_state_abs = 32 ->
    out_len >? 1024 = false ->
    Zlength contents >? 256 = false ->
    (should_reseed = true -> exists entropy_bytes s', get_entropy 256 (hmac256drbgabs_entropy_len initial_state_abs) (hmac256drbgabs_entropy_len initial_state_abs) (hmac256drbgabs_prediction_resistance initial_state_abs) s = ENTROPY.success entropy_bytes s') ->
    should_reseed = (hmac256drbgabs_prediction_resistance initial_state_abs
                       || (hmac256drbgabs_reseed_counter initial_state_abs >? hmac256drbgabs_reseed_interval initial_state_abs))%bool ->
    non_empty_additional = (if should_reseed
                            then false
                            else
                              match contents with
                                | [] => false
                                | _ :: _ => true
                              end) ->
  mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len contents
  = ENTROPY.success (
        (sublist 0 out_len
                 (snd
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (if non_empty_additional
                           then
                            hmac256drbgabs_hmac_drbg_update initial_state_abs
                              contents
                           else
                            if should_reseed
                            then
                             hmac256drbgabs_reseed initial_state_abs s
                               contents
                            else initial_state_abs))
                       (hmac256drbgabs_value
                          (if non_empty_additional
                           then
                            hmac256drbgabs_hmac_drbg_update initial_state_abs
                              contents
                           else
                            if should_reseed
                            then
                             hmac256drbgabs_reseed initial_state_abs s
                               contents
                            else initial_state_abs)) out_len))),
        (hmac256drbgabs_to_state_handle (hmac256drbgabs_increment_reseed_counter (hmac256drbgabs_hmac_drbg_update
           (hmac256drbgabs_update_value
              (if non_empty_additional
               then
                hmac256drbgabs_hmac_drbg_update initial_state_abs contents
               else
                if should_reseed
                then hmac256drbgabs_reseed initial_state_abs s contents
                else initial_state_abs)
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256
                    (hmac256drbgabs_key
                       (if non_empty_additional
                        then
                         hmac256drbgabs_hmac_drbg_update initial_state_abs
                           contents
                        else
                         if should_reseed
                         then
                          hmac256drbgabs_reseed initial_state_abs s contents
                         else initial_state_abs))
                    (hmac256drbgabs_value
                       (if non_empty_additional
                        then
                         hmac256drbgabs_hmac_drbg_update initial_state_abs
                           contents
                        else
                         if should_reseed
                         then
                          hmac256drbgabs_reseed initial_state_abs s contents
                         else initial_state_abs)) out_len)))
           (if should_reseed then [] else contents))))
                      ) (if should_reseed
         then
          get_stream_result
            (mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs
               contents)
         else s).
Proof.
  intros until contents.
  intros Hreseed_interval Hentropy_len Hout_lenb HZlength_contentsb Hget_entropy Hshould_reseed Hnon_empty_additional.
  destruct initial_state_abs.
  simpl in *.
  unfold hmac256drbgabs_reseed.
  unfold mbedtls_HMAC256_DRBG_reseed_function.
  unfold mbedtls_HMAC256_DRBG_generate_function.
  unfold HMAC256_DRBG_generate_function, HMAC256_DRBG_reseed_function.
  unfold DRBG_generate_function, DRBG_reseed_function.
  unfold DRBG_generate_function_helper.
  unfold HMAC256_DRBG_generate_algorithm.
  unfold HMAC_DRBG_generate_algorithm.
  unfold hmac256drbgabs_key.
  unfold hmac256drbgabs_value.
  unfold hmac256drbgabs_update_value.
  unfold hmac256drbgabs_hmac_drbg_update.
  unfold HMAC256_DRBG_update.
  unfold HMAC_DRBG_update.
  unfold hmac256drbgabs_increment_reseed_counter.
  unfold hmac256drbgabs_to_state_handle.
  rewrite Hout_lenb.
  change (0 >? 256) with false.
  rewrite HZlength_contentsb.
  rewrite andb_negb_r.

  unfold sublist.
  unfold skipn.
  replace (out_len - 0) with out_len by omega.
 
  destruct prediction_resistance.
  {
    (* pr = true *)
    subst.
    destruct Hget_entropy as [entropy_bytes [s' Hget_entropy]]; auto.
    rewrite Hget_entropy.
    destruct entropy_bytes.
    {
      (* contradiction, can't get 0 bytes back as entropy *)
      assert (contra: Zlength (@nil Z) = 32).
      {
        eapply get_bytes_Zlength.
        omega.
        unfold get_entropy in Hget_entropy.
        subst.
        symmetry; apply Hget_entropy;auto.
        
      }
      change (Zlength (@nil Z)) with 0 in contra.
      inversion contra.
    }
    simpl.
    remember (HMAC_DRBG_generate_helper_Z HMAC256
              (HMAC256
                 (HMAC256 V
                    (HMAC256 (V ++ 0 :: z :: entropy_bytes ++ contents) key) ++
                  1 :: z :: entropy_bytes ++ contents)
                 (HMAC256 (V ++ 0 :: z :: entropy_bytes ++ contents) key))
              (HMAC256
                 (HMAC256 V
                    (HMAC256 (V ++ 0 :: z :: entropy_bytes ++ contents) key))
                 (HMAC256
                    (HMAC256 V
                       (HMAC256 (V ++ 0 :: z :: entropy_bytes ++ contents)
                          key) ++ 1 :: z :: entropy_bytes ++ contents)
                    (HMAC256 (V ++ 0 :: z :: entropy_bytes ++ contents) key)))
              out_len) as generate_helper_result; destruct generate_helper_result.
    reflexivity.
  }
  (* pr = false *)
  subst reseed_interval.
  unfold HMAC_DRBG_update.
  rewrite HZlength_contentsb.
  
  destruct (reseed_counter >? 10000).
  {
    (* must reseed *)
    subst.
    destruct Hget_entropy as [entropy_bytes [s' Hget_entropy]]; auto.
    rewrite Hget_entropy.
    destruct entropy_bytes.
    {
      (* contradiction, can't get 0 bytes back as entropy *)
      assert (contra: Zlength (@nil Z) = 32).
      {
        eapply get_bytes_Zlength.
        omega.
        unfold get_entropy in Hget_entropy.
        subst.
        symmetry; apply Hget_entropy; auto.
        
      }
      change (Zlength (@nil Z)) with 0 in contra.
      inversion contra.
    }
    simpl.
    remember (HMAC_DRBG_generate_helper_Z HMAC256
              (HMAC256
                 (HMAC256 V
                    (HMAC256 (V ++ 0 :: z :: entropy_bytes ++ contents) key) ++
                  1 :: z :: entropy_bytes ++ contents)
                 (HMAC256 (V ++ 0 :: z :: entropy_bytes ++ contents) key))
              (HMAC256
                 (HMAC256 V
                    (HMAC256 (V ++ 0 :: z :: entropy_bytes ++ contents) key))
                 (HMAC256
                    (HMAC256 V
                       (HMAC256 (V ++ 0 :: z :: entropy_bytes ++ contents)
                          key) ++ 1 :: z :: entropy_bytes ++ contents)
                    (HMAC256 (V ++ 0 :: z :: entropy_bytes ++ contents) key)))
              out_len) as generate_helper_result; destruct generate_helper_result.
    reflexivity.
  }
  simpl in Hshould_reseed; subst should_reseed.
  destruct contents.
  {
    (* contents empty *)
    subst.
    simpl.
    remember (HMAC_DRBG_generate_helper_Z HMAC256 key V out_len) as generate_helper_result; destruct generate_helper_result.
    reflexivity.
  }
  (* contents not empty *)
  subst.
  destruct (HMAC_DRBG_generate_helper_Z HMAC256
                (HMAC256
                   (HMAC256 V (HMAC256 (V ++ [0] ++ z :: contents) key) ++
                    [1] ++ z :: contents)
                   (HMAC256 (V ++ [0] ++ z :: contents) key))
                (HMAC256
                   (HMAC256 V (HMAC256 (V ++ [0] ++ z :: contents) key))
                   (HMAC256
                      (HMAC256 V (HMAC256 (V ++ [0] ++ z :: contents) key) ++
                       [1] ++ z :: contents)
                      (HMAC256 (V ++ [0] ++ z :: contents) key))) out_len).
  reflexivity.
Qed.

(*
Lemma sublist_hi_plus {A} (l:list A) lo a b: 0<=lo<=a -> 0<=b -> sublist lo (a + b) l =
   sublist lo a l ++ sublist a (a+b) l.
Proof. intros.
  unfold sublist.
  assert (X: a+b -lo = a-lo + b) by omega. rewrite X; clear X.
  rewrite Z2Nat.inj_add, <- firstn_app; try omega. f_equal.
  assert (Y: a + b - a = b) by omega. rewrite Y; clear Y.
  rewrite skipn_skipn, Z2Nat.inj_sub; try omega.
  f_equal. f_equal. rewrite <- le_plus_minus; trivial.
  apply Z2Nat.inj_le; omega.
Qed.

Lemma sublist0_hi_plus {A} (l:list A) a b: 0<=a -> 0<=b -> sublist 0 (a + b) l =
   sublist 0 a l ++ sublist a (a+b) l.
Proof. intros.
  apply sublist_hi_plus; omega.
Qed.*)

  Definition is_multiple (multiple base: Z) : Prop := exists i, multiple = (i * base)%Z.


Lemma loop_closing_entailment (*Espec*) contents additional add_len output out_len ctx md_ctx'
      key V reseed_counter entropy_len prediction_resistance reseed_interval kv
      (info_contents : reptype t_struct_mbedtls_md_info) (s : ENTROPY.stream):
forall
(H : 0 <= add_len <= Int.max_unsigned)
(H0 : 0 <= out_len <= Int.max_unsigned)
(H2 : add_len = Zlength contents)
(H7 : Forall isbyteZ contents)
(initial_state : mdstate * (list val * (val * (val * (val * val)))))
(Heqinitial_state : initial_state =
                   (md_ctx',
                   (map Vint (map Int.repr V),
                   (Vint (Int.repr reseed_counter),
                   (Vint (Int.repr entropy_len),
                   (Val.of_bool prediction_resistance,
                   Vint (Int.repr reseed_interval)))))))
(H12 : out_len <= 1024)
(Hout_len : 0 <= out_len <= 1024)
(Hout_lenb : (out_len >? 1024) = false)
(H13 : add_len <= 256)
(Hadd_len : 0 <= add_len <= 256)
(Hadd_lenb : (add_len >? 256) = false)
(after_reseed_s : ENTROPY.stream)
(isptrAdditional : isptr additional)
(key0 : list Z)
(V0 : list Z)
(reseed_counter0 : Z)
(entropy_len0 : Z)
(prediction_resistance0 : bool)
(reseed_interval0 : Z)
(after_update_key : list Z)
(Heqafter_update_key : after_update_key =
                      hmac256drbgabs_key
                        (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                           prediction_resistance0 reseed_interval0))
(after_update_value : list Z)
(Heqafter_update_value : after_update_value =
                        hmac256drbgabs_value
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0))
(HZlength_after_update_value : Zlength after_update_value =
                              32)
(HisbyteZ_after_update_value : Forall isbyteZ after_update_value)
(done : Z)
(HRE : out_len - done <> 0)
(H14 : 0 <= done <= out_len)
(n : Z)
(Hmultiple : done = (n * 32)%Z)
(Hfield_md_ctx : forall ctx' : val,
                isptr ctx' ->
                field_compatible t_struct_hmac256drbg_context_st
                  [StructField _md_ctx] ctx' ->
                ctx' =
                field_address t_struct_hmac256drbg_context_st
                  [StructField _md_ctx] ctx')
(Hfield_V : forall ctx' : val,
           isptr ctx' ->
           field_compatible t_struct_hmac256drbg_context_st [StructField _V]
             ctx' ->
           offset_val 12 ctx' =
           field_address t_struct_hmac256drbg_context_st [StructField _V]
             ctx')
(Hisptr_ctx : isptr ctx)
(H15 : field_compatible (Tarray tuchar 32 noattr) []
        (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx))
(HZlength_V : Zlength
               (fst
                  (HMAC_DRBG_generate_helper_Z HMAC256
                     (hmac256drbgabs_key
                        (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                           prediction_resistance0 reseed_interval0))
                     after_update_value done)) = 32)
(*Delta_specs := abbreviate : PTree.t funspec*)
(Hfield_compat_output : field_compatible (tarray tuchar out_len) [] output)
(use_len : Z)
(Hequse_len : use_len = Z.min 32 (out_len - done))
(*Delta := abbreviate : tycontext*)
(H19 : is_pointer_or_null (let (x, _) := md_ctx' in x))
(H20 : is_int I32 Signed (Val.of_bool prediction_resistance))
(PNctx : is_pointer_or_null ctx)
(PNoutput : is_pointer_or_null output)
(PNadditional : is_pointer_or_null additional)
(Pkv : isptr kv)
(SC : size_compatible (tarray tuint 64) kv)
(AC : align_compatible (tarray tuint 64) kv)
(H21 : field_compatible (Tarray tuchar use_len noattr) []
        (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx))
(H25 : field_compatible (Tarray tuchar (32 - use_len) noattr) []
        (offset_val use_len
           (field_address t_struct_hmac256drbg_context_st [StructField _V]
              ctx)))
(H27 : Forall (value_fits tuchar)
        (sublist use_len 32
           (map Vint
              (map Int.repr
                 (HMAC256
                    (fst
                       (HMAC_DRBG_generate_helper_Z HMAC256 key0
                          after_update_value done)) key0)))))
(H26 : Zlength
        (sublist use_len 32
           (map Vint
              (map Int.repr
                 (HMAC256
                    (fst
                       (HMAC_DRBG_generate_helper_Z HMAC256 key0
                          after_update_value done)) key0)))) =
      Z.max 0 (32 - use_len))
(H23 : Forall (value_fits tuchar)
        (map Vint
           (sublist 0 use_len
              (map Int.repr
                 (HMAC256
                    (fst
                       (HMAC_DRBG_generate_helper_Z HMAC256 key0
                          after_update_value done)) key0)))))
(H22 : Zlength
        (map Vint
           (sublist 0 use_len
              (map Int.repr
                 (HMAC256
                    (fst
                       (HMAC_DRBG_generate_helper_Z HMAC256 key0
                          after_update_value done)) key0)))) =
      Z.max 0 use_len)
(H1 : Zlength
       (hmac256drbgabs_value
          (HMAC256DRBGabs key V reseed_counter entropy_len
             prediction_resistance reseed_interval)) =
     32)
(Hfield_compat_done_output : field_compatible (tarray tuchar (out_len - done))
                              [] (offset_val done output))
(H18 : is_pointer_or_null
        (force_val
           (sem_add_pi tuchar (offset_val done output)
              (Vint (Int.repr use_len)))))
(H24 : field_compatible (Tarray tuchar use_len noattr) []
        (offset_val done output)),

data_at Tsh (tarray tuchar use_len)
  (map Vint
     (sublist 0 use_len
        (map Int.repr
           (HMAC256
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0 after_update_value
                    done)) key0))))
  (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx) *
data_at Tsh (tarray tuchar use_len)
  (map Vint
     (sublist 0 use_len
        (map Int.repr
           (HMAC256
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0 after_update_value
                    done)) key0)))) (offset_val done output) *
UNDER_SPEC.FULL key0 (snd (snd md_ctx')) *
data_at Tsh t_struct_md_ctx_st md_ctx'
  (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx) *
field_at Tsh t_struct_hmac256drbg_context_st [StructField _reseed_counter]
  (fst
     (snd
        (snd
           (hmac256drbgabs_to_state
              (hmac256drbgabs_update_value
                 (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                    prediction_resistance0 reseed_interval0)
                 (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                       after_update_value done))) initial_state)))) ctx *
field_at Tsh t_struct_hmac256drbg_context_st [StructField _entropy_len]
  (fst
     (snd
        (snd
           (snd
              (hmac256drbgabs_to_state
                 (hmac256drbgabs_update_value
                    (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                       prediction_resistance0 reseed_interval0)
                    (fst
                       (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                          after_update_value done))) initial_state))))) ctx *
field_at Tsh t_struct_hmac256drbg_context_st
  [StructField _prediction_resistance]
  (fst
     (snd
        (snd
           (snd
              (snd
                 (hmac256drbgabs_to_state
                    (hmac256drbgabs_update_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)
                       (fst
                          (HMAC_DRBG_generate_helper_Z HMAC256
                             after_update_key after_update_value done)))
                    initial_state)))))) ctx *
field_at Tsh t_struct_hmac256drbg_context_st [StructField _reseed_interval]
  (snd
     (snd
        (snd
           (snd
              (snd
                 (hmac256drbgabs_to_state
                    (hmac256drbgabs_update_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)
                       (fst
                          (HMAC_DRBG_generate_helper_Z HMAC256
                             after_update_key after_update_value done)))
                    initial_state)))))) ctx *
data_at Tsh t_struct_mbedtls_md_info info_contents
  (hmac256drbgstate_md_info_pointer
     (hmac256drbgabs_to_state
        (hmac256drbgabs_update_value
           (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
              prediction_resistance0 reseed_interval0)
           (fst
              (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                 after_update_value done))) initial_state)) *
data_at Tsh (tarray tuchar done)
  (map Vint
     (map Int.repr
        (sublist 0 done
           (snd
              (HMAC_DRBG_generate_helper_Z HMAC256
                 (hmac256drbgabs_key
                    (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                       prediction_resistance0 reseed_interval0))
                 after_update_value done))))) output *
data_at Tsh (tarray tuchar (out_len - done - use_len))
  (list_repeat (Z.to_nat (out_len - done - use_len)) Vundef)
  (offset_val (done + use_len) output) *
data_at Tsh (tarray tuchar (32 - use_len))
  (sublist use_len 32
     (map Vint
        (map Int.repr
           (HMAC256
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0 after_update_value
                    done)) key0))))
  (offset_val use_len
     (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx))
|-- hmac256drbgabs_common_mpreds
      (HMAC256DRBGabs key0
         (fst
            (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
               after_update_value (done + use_len))) reseed_counter0
         entropy_len0 prediction_resistance0 reseed_interval0) initial_state
      ctx info_contents *
    data_at Tsh (tarray tuchar out_len)
      (map Vint
         (map Int.repr
            (sublist 0 (done + use_len)
               (snd
                  (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                     after_update_value (done + use_len))))) ++
       list_repeat (Z.to_nat (out_len - (done + use_len))) Vundef) output.
Proof. intros.
    assert (X: 0 <= done + use_len).
    { subst use_len. rewrite Zmin_spec. destruct (zlt 32 (out_len - done)); omega. }
    assert (Y: 0< use_len <= 32).
    { subst use_len. rewrite Zmin_spec. destruct (zlt 32 (out_len - done)); omega. }
    assert (D: done + use_len =
        Zlength (map Vint (map Int.repr
        (sublist 0 (done + use_len)
           (snd
              (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                 after_update_value (done + use_len))))))).
    { repeat rewrite Zlength_map. rewrite Zlength_sublist; try omega.
             rewrite HMAC_DRBG_generate_helper_Z_incremental_equiv. 
             rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; try omega.
             apply hmac_common_lemmas.HMAC_Zlength.
             exists (n+1); omega. 
             omega. assumption.
             exists n; omega. }
    rewrite <- Heqafter_update_key, Heqafter_update_value.
    assert (R: 0 <= out_len - done - use_len).
    { subst use_len. rewrite Zmin_spec in *. 
               destruct (zlt 32 (out_len - done) ). omega. omega.
    }
    erewrite data_at_complete_split
    with (p:=output)(length:=out_len)(lengthA:=done)(lengthB:=out_len - done)(offset:=done)
    (A:=(map Vint
     (map Int.repr
        (sublist 0 done
           (snd
              (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                 (hmac256drbgabs_value
                    (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                       prediction_resistance0 reseed_interval0)) done)))))).
    erewrite data_at_complete_split
    with (p:=offset_val done output)(lengthA:=use_len)(lengthB:=(out_len - done - use_len))(length:=out_len - done)
    (A:= (map Vint
     (sublist 0 use_len
        (map Int.repr
           (HMAC256
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0
                    (hmac256drbgabs_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)) done))
              key0))))).
    6: reflexivity. 5: omega. rewrite offset_offset_val.
    (*change (@data_at hmac_drbg_compspecs.CompSpecs Tsh (tarray tuchar use_len))
     with (@data_at CompSpecs Tsh (tarray tuchar use_len)).AGAIN, some conspecs issue*) 
    cancel. 
    Focus 2. rewrite Zlength_map, Zlength_list_repeat. rewrite Heqafter_update_value in *.
             rewrite Zlength_map in H22. rewrite H22.
             rewrite Z.max_r. 2: omega.
             assert (Q: use_len + (out_len - done - use_len) = out_len - done) by omega.
             rewrite Q; assumption.
             assumption.
    Focus 2. rewrite Heqafter_update_value in *. clear - Y H22. rewrite Zlength_map in *. rewrite H22, Zmax_r; omega.
    Focus 2. rewrite Zlength_list_repeat; try omega.
    2: reflexivity.
    Focus 2. rewrite Heqafter_update_value in *; rewrite Zlength_map in *.
             rewrite Zlength_app; repeat rewrite Zlength_map. rewrite H22, Zlength_list_repeat; try omega.
             rewrite Z.max_r, Zlength_sublist; try omega.
             assert (RR: done - 0 + (use_len + (out_len - done - use_len)) = out_len) by omega.
             rewrite RR; assumption. 
             rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; try omega . 
             apply hmac_common_lemmas.HMAC_Zlength.
             exists n; omega. 
    Focus 2. repeat rewrite Zlength_map. rewrite Zlength_sublist; try omega.
             rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; try omega . 
             apply hmac_common_lemmas.HMAC_Zlength.
             exists n; omega. 
    Focus 2. rewrite Zlength_app; repeat rewrite Zlength_map. rewrite Zlength_sublist, Zlength_list_repeat; try omega.
             rewrite Zlength_map, hmac_common_lemmas.HMAC_Zlength; omega.
    2: omega. 2: reflexivity.
    Focus 2. rewrite Z.sub_add_distr, app_assoc. f_equal. subst done use_len.
             rewrite <- (while_loop_post_incremental_snd after_update_key
              (hmac256drbgabs_value
                 (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                    prediction_resistance0 reseed_interval0)) n out_len); try omega.
             rewrite sublist_map. 
             rewrite sublist0_app2.
             Focus 2. rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd, HMAC_DRBG_generate_helper_Z_Zlength_fst; try omega.
                      simpl in *. subst V0; assumption. 
             apply hmac_common_lemmas.HMAC_Zlength.
             apply hmac_common_lemmas.HMAC_Zlength.
             exists n; omega.
             
             do 2 rewrite map_app; rewrite (sublist_same 0 (n*32)%Z).
             2: trivial.
             Focus 2. rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; try omega.
                      apply hmac_common_lemmas.HMAC_Zlength.
                      exists n; omega.
             f_equal. 
             rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; try omega. simpl.
             rewrite Zminus_plus. simpl. f_equal. f_equal. f_equal. subst after_update_key. simpl.

             apply while_loop_post_incremental_fst. omega. omega. 
             apply hmac_common_lemmas.HMAC_Zlength.
             exists n; omega. 

    unfold hmac256drbgabs_common_mpreds. subst. cancel.

    unfold_data_at 4%nat.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]);
    rewrite (field_at_data_at _ _ [StructField _V]).
    
    simpl. unfold md_full.
    (*change (@data_at CompSpecs Tsh (tarray tuchar 32))
    with (@data_at hmac_drbg_compspecs.CompSpecs Tsh (tarray tuchar 32)).
    change (@data_at CompSpecs Tsh (tarray tuchar (32 - Z.min 32 (out_len - n * 32))))
    with (@data_at hmac_drbg_compspecs.CompSpecs Tsh
       (tarray tuchar (32 - Z.min 32 (out_len - n * 32)))).*)
    normalize. apply andp_right. apply prop_right. auto. 
    cancel. 
    erewrite data_at_complete_split
    with (p:=(@field_address hmac_drbg_compspecs.CompSpecs t_struct_hmac256drbg_context_st [StructField _V] ctx))
    (lengthA:=Z.min 32 (out_len - n * 32)) (lengthB:=32 - Z.min 32 (out_len - n * 32)) (length:=32)
    (A:=map Vint
     (sublist 0 (Z.min 32 (out_len - n * 32))
        (map Int.repr
           (HMAC256
              (fst (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)))
              key0))))
    (B:=sublist (Z.min 32 (out_len - n * 32)) 32
     (map Vint
        (map Int.repr
           (HMAC256
              (fst (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)))
              key0))))
    (offset:=Z.min 32 (out_len - n * 32)).
    apply derives_refl. 
    simpl in H22. rewrite sublist_map in H22. repeat rewrite Zlength_map in H22.
          rewrite sublist_map. repeat rewrite Zlength_map.
          rewrite H22, Zlength_sublist, Z.max_r, Zplus_minus. assumption. omega. omega.
    repeat rewrite Zlength_map; rewrite hmac_common_lemmas.HMAC_Zlength; omega.
    rewrite Zlength_map, Zlength_sublist. omega. omega.
    repeat rewrite Zlength_map; rewrite hmac_common_lemmas.HMAC_Zlength; omega.
    rewrite Zlength_sublist. trivial. omega.
    repeat rewrite Zlength_map; rewrite hmac_common_lemmas.HMAC_Zlength; omega.
    omega. omega. 
    rewrite <- sublist_map, sublist_rejoin, sublist_same; try omega.
    2: repeat rewrite Zlength_map; rewrite hmac_common_lemmas.HMAC_Zlength; trivial.
    2: repeat rewrite Zlength_map; rewrite hmac_common_lemmas.HMAC_Zlength; omega.
    f_equal. f_equal. 
    rewrite Zmin_spec in *.
    remember (zlt 32 (out_len - n * 32)) as d.
    destruct d.
    +  symmetry. apply HMAC_DRBG_generate_helper_Z_incremental_fst.  omega. trivial. 
    +  rewrite HMAC_DRBG_generate_helper_Z_incremental_equiv.
       symmetry. apply HMAC_DRBG_generate_helper_Z_incremental_fst.  omega. trivial.
       omega. omega. exists n; trivial.
Time Qed. (*22secs*) 

Opaque hmac256drbgabs_value. 
Opaque hmac256drbgabs_entropy_len. 
Opaque hmac256drbgabs_reseed_interval.  
Opaque hmac256drbgabs_reseed_counter.
Opaque hmac256drbgabs_value.

Opaque hmac256drbg_relate.
Opaque hmac256drbgstate_md_info_pointer.
Opaque return_value_relate_result.
Opaque hmac256drbgabs_common_mpreds.

Opaque get_stream_result.

Opaque hmac256drbgabs_generate.
Opaque hmac256drbgabs_reseed.
Opaque hmac256drbgabs_hmac_drbg_update.

Opaque mbedtls_HMAC256_DRBG_generate_function.
Opaque mbedtls_HMAC256_DRBG_reseed_function.

Lemma loop_before_memcopy Espec contents additional add_len output out_len ctx 
      md_ctx' V' reseed_counter' entropy_len' prediction_resistance' 
      reseed_interval' key V reseed_counter entropy_len prediction_resistance 
      reseed_interval kv (info_contents : reptype t_struct_mbedtls_md_info)
      (s : ENTROPY.stream):
forall
(H : 0 <= add_len <= Int.max_unsigned)
(H0 : 0 <= out_len <= Int.max_unsigned)
(initial_state_abs : hmac256drbgabs)
(Heqinitial_state_abs : initial_state_abs =
                       HMAC256DRBGabs key V reseed_counter entropy_len
                         prediction_resistance reseed_interval)
(H1 : Zlength (hmac256drbgabs_value initial_state_abs) = 32 (*SHA*))
(H2 : add_len = Zlength contents)
(H3 : hmac256drbgabs_entropy_len initial_state_abs = 32)
(H4 : hmac256drbgabs_reseed_interval initial_state_abs = 10000)
(Hreseed_counter_in_range : 0 <=
                           hmac256drbgabs_reseed_counter initial_state_abs <=
                           Int.max_signed)
(H6 : Forall isbyteZ (hmac256drbgabs_value initial_state_abs))
(H7 : Forall isbyteZ contents)
(H5 : map Vint (map Int.repr V) = V')
(H8 : Vint (Int.repr reseed_counter) = reseed_counter')
(H9 : Vint (Int.repr entropy_len) = entropy_len')
(H10 : Vint (Int.repr reseed_interval) = reseed_interval')
(H11 : Val.of_bool prediction_resistance = prediction_resistance')
(initial_state : mdstate * (list val * (val * (val * (val * val)))))
(Heqinitial_state : initial_state =
                   (md_ctx',
                   (map Vint (map Int.repr V),
                   (Vint (Int.repr reseed_counter),
                   (Vint (Int.repr entropy_len),
                   (Val.of_bool prediction_resistance,
                   Vint (Int.repr reseed_interval)))))))
(H12 : out_len <= 1024)
(Hout_len : 0 <= out_len <= 1024)
(Hout_lenb : (out_len >? 1024) = false)
(H13 : add_len <= 256)
(Hadd_len : 0 <= add_len <= 256)
(Hadd_lenb : (add_len >? 256) = false)
(should_reseed : bool)
(Heqshould_reseed : should_reseed =
                   (prediction_resistance
                    || (reseed_counter >? reseed_interval))%bool)
(after_reseed_state_abs : hmac256drbgabs)
(Heqafter_reseed_state_abs : after_reseed_state_abs =
                            (if should_reseed
                             then
                              hmac256drbgabs_reseed initial_state_abs s
                                contents
                             else initial_state_abs))
(after_reseed_s : ENTROPY.stream)
(after_reseed_add_len : Z)
(Heqafter_reseed_add_len : after_reseed_add_len =
                          (if should_reseed then 0 else add_len))
(Hshould_reseed_get_entropy : should_reseed = true ->
                             exists
                               (entropy_bytes : list Z) (s' : ENTROPY.stream),
                               get_entropy 256 entropy_len entropy_len
                                 prediction_resistance s =
                               ENTROPY.success entropy_bytes s')
(isptrAdditional : isptr additional)
(non_empty_additional : bool)
(Heqnon_empty_additional : non_empty_additional =
                          (if eq_dec after_reseed_add_len 0
                           then false
                           else true))
(Hnon_empty_additional_contents : non_empty_additional =
                                 (if should_reseed
                                  then false
                                  else
                                   match contents with
                                   | [] => false
                                   | _ :: _ => true
                                   end))
(Hshould_reseed_non_empty_additional : should_reseed = true ->
                                      non_empty_additional = false)
(Hnon_empty_additional_should_reseed : non_empty_additional = true ->
                                      should_reseed = false)
(key0 : list Z)
(V0 : list Z)
(reseed_counter0 : Z)
(entropy_len0 : Z)
(prediction_resistance0 : bool)
(reseed_interval0 : Z)
(*Delta_specs := abbreviate : PTree.t funspec*)
(after_update_key : list Z)
(Heqafter_update_key : after_update_key =
                      hmac256drbgabs_key
                        (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                           prediction_resistance0 reseed_interval0))
(after_update_value : list Z)
(Heqafter_update_value : after_update_value =
                        hmac256drbgabs_value
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0))
(HZlength_after_update_value : Zlength after_update_value =
                              32)
(HisbyteZ_after_update_value : Forall isbyteZ after_update_value)
(done : Z)
(HRE : out_len - done <> 0)
(H14 : 0 <= done <= out_len)
(n : Z)
(Hmultiple : done = (n * 32)%Z)
(Hfield_md_ctx : forall ctx' : val,
                isptr ctx' ->
                field_compatible t_struct_hmac256drbg_context_st
                  [StructField _md_ctx] ctx' ->
                ctx' =
                field_address t_struct_hmac256drbg_context_st
                  [StructField _md_ctx] ctx')
(Hfield_V : forall ctx' : val,
           isptr ctx' ->
           field_compatible t_struct_hmac256drbg_context_st [StructField _V]
             ctx' ->
           offset_val 12 ctx' =
           field_address t_struct_hmac256drbg_context_st [StructField _V]
             ctx')
(Hisptr_ctx : isptr ctx)
(H15 : field_compatible (Tarray tuchar 32 noattr) []
        (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx))
(HZlength_V : Zlength
               (fst
                  (HMAC_DRBG_generate_helper_Z HMAC256
                     (hmac256drbgabs_key
                        (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                           prediction_resistance0 reseed_interval0))
                     after_update_value done)) = 32)
(H16 : Forall isbyteZ
        (fst
           (HMAC_DRBG_generate_helper_Z HMAC256
              (hmac256drbgabs_key
                 (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                    prediction_resistance0 reseed_interval0))
              after_update_value done)))
(*Delta := abbreviate : tycontext*)
(H17 : Forall isbyteZ
        (HMAC256
           (fst
              (HMAC_DRBG_generate_helper_Z HMAC256
                 (hmac256drbgabs_key
                    (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                       prediction_resistance0 reseed_interval0))
                 after_update_value done)) key0))
(*(DELTA: tycontext)
(DD: tycontext_sub (initialized_list
     [_ctx; _md_len; _left; _out; _info; _prediction_resistance;
     _reseed_counter; _reseed_interval; _use_len; 246%positive; 245%positive;
     244%positive; 241%positive]
     (func_tycontext f_mbedtls_hmac_drbg_random_with_add HmacDrbgVarSpecs
        HmacDrbgFunSpecs)) DELTA)*),
@semax hmac_drbg_compspecs.CompSpecs Espec 
  (initialized_list
     [_ctx; _md_len; _left; _out; _info; _prediction_resistance;
     _reseed_counter; _reseed_interval; _use_len; 246%positive; 245%positive;
     244%positive; 241%positive]
     (func_tycontext f_mbedtls_hmac_drbg_random_with_add HmacDrbgVarSpecs
        HmacDrbgFunSpecs))
(*  DELTA*)
  (PROP  ()
   LOCAL  (temp _use_len (Vint (Int.repr (Z.min 32 (out_len - done))));
   temp _md_len (Vint (Int.repr 32));
   temp _info (let (x, _) := md_ctx' in x);
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance);
   temp _out (offset_val done output);
   temp _left (Vint (Int.repr (out_len - done))); temp _ctx ctx;
   temp _p_rng ctx; temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len));
   temp 246%positive
     (Vint (Int.repr (Z.min 32(*(32)*) (out_len - done))));
   gvar sha._K256 kv)
   SEP  (K_vector kv; UNDER_SPEC.FULL key0 (snd (snd md_ctx'));
   data_at Tsh t_struct_md_ctx_st md_ctx'
     (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx);
   data_at Tsh
     (tarray tuchar
        (Zlength
           (HMAC256
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256
                    (hmac256drbgabs_key
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0))
                    after_update_value done)) key0)))
     (map Vint
        (map Int.repr
           (HMAC256
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256
                    (hmac256drbgabs_key
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0))
                    after_update_value done)) key0)))
     (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx);
   field_at Tsh t_struct_hmac256drbg_context_st [StructField _reseed_counter]
     (fst
        (snd
           (snd
              (hmac256drbgabs_to_state
                 (hmac256drbgabs_update_value
                    (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                       prediction_resistance0 reseed_interval0)
                    (fst
                       (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                          after_update_value done))) initial_state)))) ctx;
   field_at Tsh t_struct_hmac256drbg_context_st [StructField _entropy_len]
     (fst
        (snd
           (snd
              (snd
                 (hmac256drbgabs_to_state
                    (hmac256drbgabs_update_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)
                       (fst
                          (HMAC_DRBG_generate_helper_Z HMAC256
                             after_update_key after_update_value done)))
                    initial_state))))) ctx;
   field_at Tsh t_struct_hmac256drbg_context_st
     [StructField _prediction_resistance]
     (fst
        (snd
           (snd
              (snd
                 (snd
                    (hmac256drbgabs_to_state
                       (hmac256drbgabs_update_value
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)
                          (fst
                             (HMAC_DRBG_generate_helper_Z HMAC256
                                after_update_key after_update_value done)))
                       initial_state)))))) ctx;
   field_at Tsh t_struct_hmac256drbg_context_st
     [StructField _reseed_interval]
     (snd
        (snd
           (snd
              (snd
                 (snd
                    (hmac256drbgabs_to_state
                       (hmac256drbgabs_update_value
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)
                          (fst
                             (HMAC_DRBG_generate_helper_Z HMAC256
                                after_update_key after_update_value done)))
                       initial_state)))))) ctx; Stream after_reseed_s;
   data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
     additional;
   data_at Tsh t_struct_mbedtls_md_info info_contents
     (hmac256drbgstate_md_info_pointer
        (hmac256drbgabs_to_state
           (hmac256drbgabs_update_value
              (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                 prediction_resistance0 reseed_interval0)
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                    after_update_value done))) initial_state));
   data_at Tsh (tarray tuchar out_len)
     (map Vint
        (map Int.repr
           (sublist 0 done
              (snd
                 (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                    after_update_value done)))) ++
      list_repeat (Z.to_nat (out_len - done)) Vundef) output))
  (Ssequence
     (Scall None
        (Evar _memcpy
           (Tfunction
              (Tcons (tptr tvoid) (Tcons (tptr tvoid) (Tcons tuint Tnil)))
              (tptr tvoid) cc_default))
        [Etempvar _out (tptr tuchar);
        Efield
          (Ederef
             (Etempvar _ctx
                (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
             (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
          (tarray tuchar 32); Etempvar _use_len tuint])
     (Ssequence
        (Sset _out
           (Ebinop Oadd (Etempvar _out (tptr tuchar))
              (Etempvar _use_len tuint) (tptr tuchar)))
        (Sset _left
           (Ebinop Osub (Etempvar _left tuint) (Etempvar _use_len tuint)
              tuint))))
  (loop1_ret_assert
     (EX  a : Z,
      PROP  (0 <= a <= out_len; is_multiple a 32 \/ a = out_len)
      LOCAL  (temp _md_len (Vint (Int.repr 32(*(32)*)));
      temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out (offset_val a output);
      temp _left (Vint (Int.repr (out_len - a))); temp _ctx ctx;
      temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
      gvar sha._K256 kv)
      SEP 
      (Stream after_reseed_s *
       (data_at Tsh (tarray tuchar add_len)
          (map Vint (map Int.repr contents)) additional * emp);
      hmac256drbgabs_common_mpreds
        (hmac256drbgabs_update_value
           (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
              prediction_resistance0 reseed_interval0)
           (fst
              (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                 after_update_value a))) initial_state ctx info_contents;
      data_at Tsh (tarray tuchar out_len)
        (map Vint
           (map Int.repr
              (sublist 0 a
                 (snd
                    (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                       after_update_value a)))) ++
         list_repeat (Z.to_nat (out_len - a)) Vundef) output; K_vector kv))%assert
     (overridePost
        (EX  a : Z,
         PROP 
         (typed_false tint
            (Val.of_bool
               (negb (Int.eq (Int.repr (out_len - a)) (Int.repr 0))));
         0 <= a <= out_len; is_multiple a 32 \/ a = out_len)
         LOCAL 
         (temp _md_len (Vint (Int.repr 32(*(32)*)));
         temp _info (let (x, _) := md_ctx' in x);
         temp _reseed_interval (Vint (Int.repr reseed_interval));
         temp _reseed_counter (Vint (Int.repr reseed_counter));
         temp _prediction_resistance (Val.of_bool prediction_resistance);
         temp _out (offset_val a output);
         temp _left (Vint (Int.repr (out_len - a))); temp _ctx ctx;
         temp _p_rng ctx; temp _output output;
         temp _out_len (Vint (Int.repr out_len));
         temp _additional additional;
         temp _add_len (Vint (Int.repr after_reseed_add_len));
         gvar sha._K256 kv)
         SEP 
         (Stream after_reseed_s *
          (data_at Tsh (tarray tuchar add_len)
             (map Vint (map Int.repr contents)) additional * emp);
         hmac256drbgabs_common_mpreds
           (hmac256drbgabs_update_value
              (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                 prediction_resistance0 reseed_interval0)
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                    after_update_value a))) initial_state ctx info_contents;
         data_at Tsh (tarray tuchar out_len)
           (map Vint
              (map Int.repr
                 (sublist 0 a
                    (snd
                       (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                          after_update_value a)))) ++
            list_repeat (Z.to_nat (out_len - a)) Vundef) output; K_vector kv))%assert
        (function_body_ret_assert tint
           (EX  ret_value : val,
            PROP 
            (return_value_relate_result
               (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs
                  out_len contents) ret_value)
            LOCAL  (temp ret_temp ret_value)
            SEP 
            (match
               mbedtls_HMAC256_DRBG_generate_function s initial_state_abs
                 out_len contents
             with
             | ENTROPY.success (bytes, _) _ =>
                 data_at Tsh (tarray tuchar out_len)
                   (map Vint (map Int.repr bytes)) output
             | ENTROPY.error _ _ =>
                 data_at_ Tsh (tarray tuchar out_len) output
             end;
            hmac256drbgabs_common_mpreds
              (hmac256drbgabs_generate initial_state_abs s out_len contents)
              (md_ctx',
              (V',
              (reseed_counter',
              (entropy_len', (prediction_resistance', reseed_interval')))))
              ctx info_contents;
            data_at Tsh (tarray tuchar add_len)
              (map Vint (map Int.repr contents)) additional;
            Stream
              (get_stream_result
                 (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs
                    out_len contents)); K_vector kv))%assert))).
Proof. intros. abbreviate_semax. Optimize Proof. Optimize Heap. (*Time Qed.*) unfold Delta, abbreviate.
Opaque HMAC256.
  unfold abbreviate in Delta_specs. (* admit. Time Qed.*) abbreviate_semax. 
freeze [0;1;2;4;5;6;7;8;9;10] FR_mcpy1.
    assert_PROP (field_compatible (tarray tuchar out_len) [] output) as Hfield_compat_output by entailer!.
    freeze [0;1] FR_mcpy2.
    replace_SEP 1(*5*) (
                  data_at Tsh (tarray tuchar done) (map Vint
           (map Int.repr
              (sublist 0 done
                 (snd
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))))) output *
                  data_at Tsh (tarray tuchar (out_len - done)) (list_repeat (Z.to_nat (out_len - done)) Vundef) (offset_val done output)
    ).
    {
      entailer!.
      apply derives_refl'.

      assert (HZlength1: Zlength (map Vint
        (map Int.repr
           (sublist 0 (n * 32)%Z
              (snd
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0
                    (hmac256drbgabs_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)) (n * 32)%Z))))) = (n * 32)%Z).
      {
        do 2 rewrite Zlength_map.
        rewrite Zlength_sublist; [omega|omega|].
        rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; auto; try omega.
        apply hmac_common_lemmas.HMAC_Zlength.
        exists n; reflexivity.
      }
      
      apply data_at_complete_split; try rewrite HZlength1; try rewrite Zlength_list_repeat; auto; try omega.
      replace ((n * 32)%Z + (out_len - (n * 32)%Z)) with out_len by omega.
      assumption.
    }
    flatten_sepcon_in_SEP. (*normalize.*)
    remember (offset_val done output) as done_output.
    remember (Z.min 32 (out_len - done)) as use_len.
    assert_PROP (field_compatible (tarray tuchar (out_len - done)) [] done_output) as Hfield_compat_done_output.
    {
      clear Heqdone_output Hmultiple.
      entailer!.
      rewrite H21 in H23; apply H23.
      (*rewrite H23 (*Zlength = done *) in H25 (*field compatible *); apply H25.*)
    }
    freeze [0;1] FR_mcpy3.
    replace_SEP 1(*6*) (
                  data_at Tsh (tarray tuchar use_len) (list_repeat (Z.to_nat use_len) Vundef) done_output *
                  data_at Tsh (tarray tuchar (out_len - done - use_len)) (list_repeat (Z.to_nat (out_len - done - use_len)) Vundef) (offset_val use_len done_output)
    ).
    {
      clear Hmultiple Heqdone_output.
      entailer!.
      apply derives_refl'.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_list_repeat; auto; try omega.
        replace (32 + (out_len - done - 32)) with (out_len - done) by omega; assumption.
        rewrite list_repeat_app.
        rewrite <- Z2Nat.inj_add; try omega.
        replace (32 + (out_len - done - 32)) with (out_len - done) by omega; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_list_repeat; auto; try omega.
        replace (out_len - done + (out_len - done - (out_len - done))) with (out_len - done) by omega; assumption.
        replace (out_len - done - (out_len - done)) with 0 by omega; simpl; rewrite app_nil_r; reflexivity.
      }
    }
    flatten_sepcon_in_SEP. (*normalize.*)
    replace_SEP 1(*0*) (memory_block Tsh use_len done_output).
    {
      clear Hmultiple.
      entailer!.
      eapply derives_trans; [apply data_at_memory_block|].
      replace (sizeof (*cenv_cs*) (tarray tuchar (Z.min 32 (out_len - done)))) with (Z.min 32 (out_len - done)).
      apply derives_refl.
      simpl.
      destruct (Z.min_dec 32 (out_len - done));
      rewrite Zmax0r; omega.
    }
    thaw FR_mcpy3. thaw FR_mcpy2. freeze [0;2;4] FR_mcpy4.
    replace_SEP 1(*6*) (data_at Tsh (tarray tuchar use_len) (sublist 0 use_len (map Vint (map Int.repr (HMAC256
                 (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))
                 key0)))) (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx) *
                   data_at Tsh (tarray tuchar (32 - use_len)) (sublist use_len 32 (map Vint (map Int.repr (HMAC256
                 (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))
                 key0)))) (offset_val use_len (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx))
    ).
    {
      clear Hmultiple.
      entailer!.
      apply derives_refl'.
      rewrite hmac_common_lemmas.HMAC_Zlength.
      remember (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0
                    (hmac256drbgabs_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)) done)) as V0'; clear HeqV0'.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        rewrite sublist_nil.
        rewrite app_nil_r.
        symmetry; apply sublist_same.
        reflexivity.
        repeat rewrite Zlength_map; rewrite hmac_common_lemmas.HMAC_Zlength; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (out_len - done - 0 + (32 - (out_len - done))) with 32 by omega; auto.
        rewrite sublist_rejoin; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
        rewrite sublist_same; try reflexivity; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
      }
    }
    (* memcpy( out, ctx->V, use_len ); *)
    forward_call ((Tsh, Tsh), done_output, (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx), use_len, sublist 0 use_len (map Int.repr
              (HMAC256
                 (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))
                 key0))).
    { rewrite <- sublist_map. simpl. 
      (*If  have different compspecs here, we need to do this:
      cancel.  rewrite sepcon_assoc. rewrite sepcon_comm.
      rewrite sepcon_assoc.
      apply sepcon_derives. entailer!. cancel.*)
      cancel. 
    }
    {
      change (Int.max_unsigned) with 4294967295.
      repeat split; auto;
      subst use_len; destruct (Z.min_dec 32 (out_len - done)); omega.
    }

    (*Intros vret; subst vret.*)

    simpl.
    forward. forward.
    
    Exists (done + use_len).
    entailer!.
    (*subst done_output. rewrite offset_offset_val. *) rewrite Z.sub_add_distr.
    repeat split(*; subst use_len*).
    rewrite Zmin_spec. destruct (zlt 32 (out_len - n*32)). omega. omega.
    rewrite Zmin_spec. destruct (zlt 32 (out_len - n*32)). omega. omega.
    rewrite Zmin_spec. destruct (zlt 32 (out_len - n*32)). left. exists (n+1). omega. right; omega.

    thaw FR_mcpy4. thaw FR_mcpy1. cancel.
(*    subst done_output;*) rewrite offset_offset_val.
    clear H3 H4 H6 Hreseed_counter_in_range Hnon_empty_additional_should_reseed
       Hshould_reseed_non_empty_additional Hnon_empty_additional_contents 
       Hshould_reseed_get_entropy  H17 H16 .
x
    eapply (loop_closing_entailment). eassumption. (*Espec*) contents additional add_len output out_len ctx md_ctx'
      key V reseed_counter entropy_len prediction_resistance reseed_interval kv
      info_contents s) with (n:=n); assumption.
Admitted.  (*Time Qed. Does not terminate within 13h. Increased heap from 1.58GB to 1.66 GB *)

Lemma Tarray_0_emp sh v c: data_at sh (Tarray tuchar 0 noattr) v c |--  emp.
  unfold data_at. unfold field_at, data_at', at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. entailer.
Qed. 
Lemma Tarray_0_emp' sh c: field_compatible (Tarray tuchar 0 noattr) nil c ->
  emp |-- data_at sh (Tarray tuchar 0 noattr) nil c.
Proof. intros.
  unfold data_at. unfold field_at, data_at', at_offset; simpl.
  unfold array_pred, unfold_reptype, aggregate_pred.array_pred. simpl.
  entailer.
Qed. 

Lemma body_hmac_drbg_reseed_steps6To8 Espec contents additional add_len output out_len
      ctx md_ctx' V' reseed_counter' entropy_len' prediction_resistance' reseed_interval' 
      key V reseed_counter entropy_len prediction_resistance reseed_interval kv 
      (info_contents : reptype t_struct_mbedtls_md_info) (s : ENTROPY.stream):
forall
(H : 0 <= add_len <= Int.max_unsigned)
(H0 : 0 <= out_len <= Int.max_unsigned)
(initial_state_abs : hmac256drbgabs)
(Heqinitial_state_abs : initial_state_abs =
                       HMAC256DRBGabs key V reseed_counter entropy_len
                         prediction_resistance reseed_interval)
(H1 : Zlength (hmac256drbgabs_value initial_state_abs) =
     32)
(H2 : add_len = Zlength contents)
(H3 : hmac256drbgabs_entropy_len initial_state_abs = 32)
(H4 : hmac256drbgabs_reseed_interval initial_state_abs = 10000)
(Hreseed_counter_in_range : 0 <=
                           hmac256drbgabs_reseed_counter initial_state_abs <=
                           Int.max_signed)
(H6 : Forall isbyteZ (hmac256drbgabs_value initial_state_abs))
(H7 : Forall isbyteZ contents)
(H5 : map Vint (map Int.repr V) = V')
(H8 : Vint (Int.repr reseed_counter) = reseed_counter')
(H9 : Vint (Int.repr entropy_len) = entropy_len')
(H10 : Vint (Int.repr reseed_interval) = reseed_interval')
(H11 : Val.of_bool prediction_resistance = prediction_resistance')
(initial_state : mdstate * (list val * (val * (val * (val * val)))))
(Heqinitial_state : initial_state =
                   (md_ctx',
                   (map Vint (map Int.repr V),
                   (Vint (Int.repr reseed_counter),
                   (Vint (Int.repr entropy_len),
                   (Val.of_bool prediction_resistance,
                   Vint (Int.repr reseed_interval)))))))
(H12 : out_len <= 1024)
(Hout_len : 0 <= out_len <= 1024)
(Hout_lenb : (out_len >? 1024) = false)
(H13 : add_len <= 256)
(Hadd_len : 0 <= add_len <= 256)
(Hadd_lenb : (add_len >? 256) = false)
(should_reseed : bool)
(Heqshould_reseed : should_reseed =
                   (prediction_resistance
                    || (reseed_counter >? reseed_interval))%bool)
(after_reseed_state_abs : hmac256drbgabs)
(Heqafter_reseed_state_abs : after_reseed_state_abs =
                            (if should_reseed
                             then
                              hmac256drbgabs_reseed initial_state_abs s
                                contents
                             else initial_state_abs))
(after_reseed_s : ENTROPY.stream)
(Heqafter_reseed_s : after_reseed_s =
                    (if should_reseed
                     then
                      get_stream_result
                        (mbedtls_HMAC256_DRBG_reseed_function s
                           initial_state_abs contents)
                     else s))
(after_reseed_add_len : Z)
(Heqafter_reseed_add_len : after_reseed_add_len =
                          (if should_reseed then 0 else add_len))
(Hshould_reseed_get_entropy : should_reseed = true ->
                             exists
                               (entropy_bytes : list Z) (s' : ENTROPY.stream),
                               get_entropy 256 entropy_len entropy_len
                                 prediction_resistance s =
                               ENTROPY.success entropy_bytes s')
(isptrAdditional : isptr additional)
(non_empty_additional : bool)
(Heqnon_empty_additional : non_empty_additional =
                          (if eq_dec after_reseed_add_len 0
                           then false
                           else true))
(Hnon_empty_additional_contents : non_empty_additional =
                                 (if should_reseed
                                  then false
                                  else
                                   match contents with
                                   | [] => false
                                   | _ :: _ => true
                                   end))
(Hshould_reseed_non_empty_additional : should_reseed = true ->
                                      non_empty_additional = false)
(Hnon_empty_additional_should_reseed : non_empty_additional = true ->
                                      should_reseed = false)
(after_update_state_abs : hmac256drbgabs)
(Heqafter_update_state_abs : after_update_state_abs =
                            (if non_empty_additional
                             then
                              hmac256drbgabs_hmac_drbg_update
                                initial_state_abs contents
                             else after_reseed_state_abs))
(*Delta_specs := abbreviate : PTree.t funspec
Delta := abbreviate : tycontext*)
(after_update_key : list Z)
(Heqafter_update_key : after_update_key =
                      hmac256drbgabs_key after_update_state_abs)
(after_update_value : list Z)
(Heqafter_update_value : after_update_value =
                        hmac256drbgabs_value after_update_state_abs)
(HZlength_after_update_value : Zlength after_update_value =
                              32)
(HisbyteZ_after_update_value : Forall isbyteZ after_update_value)
(FRloop := [Stream after_reseed_s;
          data_at Tsh (tarray tuchar add_len)
            (map Vint (map Int.repr contents)) additional] : list mpred)
(done : Z)
(HRE : out_len - done = 0)
(H14 : 0 <= done <= out_len)
(H15 : is_multiple done 32 \/ done = out_len),
@semax  hmac_drbg_compspecs.CompSpecs Espec 
  (initialized_list
     [_ctx; _md_len; _left; _out; _info; _prediction_resistance;
     _reseed_counter; _reseed_interval; 245%positive; 244%positive;
     241%positive]
     (func_tycontext f_mbedtls_hmac_drbg_random_with_add HmacDrbgVarSpecs
        HmacDrbgFunSpecs))
  (PROP  ()
   LOCAL  (temp _md_len (Vint (Int.repr (32)));
   temp _info (let (x, _) := md_ctx' in x);
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance);
   temp _out (offset_val done output);
   temp _left (Vint (Int.repr (out_len - done))); temp _ctx ctx;
   temp _p_rng ctx; temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvar sha._K256 kv)
   SEP  (FRZL FRloop;
   hmac256drbgabs_common_mpreds
     (hmac256drbgabs_update_value after_update_state_abs
        (fst
           (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
              after_update_value done))) initial_state ctx info_contents;
   data_at Tsh (tarray tuchar out_len)
     (map Vint
        (map Int.repr
           (sublist 0 done
              (snd
                 (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                    after_update_value done)))) ++
      list_repeat (Z.to_nat (out_len - done)) Vundef) output; K_vector kv))
  (Ssequence
     (Scall None
        (Evar _mbedtls_hmac_drbg_update
           (Tfunction
              (Tcons (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                 (Tcons (tptr tuchar) (Tcons tuint Tnil))) tvoid cc_default))
        [Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr));
        Etempvar _additional (tptr tuchar); Etempvar _add_len tuint])
     (Ssequence
        (Sset _reseed_counter
           (Efield
              (Ederef
                 (Etempvar _ctx
                    (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                 (Tstruct _mbedtls_hmac_drbg_context noattr)) _reseed_counter
              tint))
        (Ssequence
           (Sassign
              (Efield
                 (Ederef
                    (Etempvar _ctx
                       (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                    (Tstruct _mbedtls_hmac_drbg_context noattr))
                 _reseed_counter tint)
              (Ebinop Oadd (Etempvar _reseed_counter tint)
                 (Econst_int (Int.repr 1) tint) tint))
           (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
  (function_body_ret_assert tint
     (EX  ret_value : val,
      PROP 
      (return_value_relate_result
         (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
            contents) ret_value)
      LOCAL  (temp ret_temp ret_value)
      SEP 
      (match
         mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
           contents
       with
       | ENTROPY.success (bytes, _) _ =>
           data_at Tsh (tarray tuchar out_len)
             (map Vint (map Int.repr bytes)) output
       | ENTROPY.error _ _ => data_at_ Tsh (tarray tuchar out_len) output
       end;
      hmac256drbgabs_common_mpreds
        (hmac256drbgabs_generate initial_state_abs s out_len contents)
        (md_ctx',
        (V',
        (reseed_counter',
        (entropy_len', (prediction_resistance', reseed_interval'))))) ctx
        info_contents;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      Stream
        (get_stream_result
           (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs
              out_len contents)); K_vector kv))%assert).
Proof. intros; abbreviate_semax.
  assert (Hdone: done = out_len) by omega. subst done.
  rewrite Zminus_diag. clear HRE H12 H14 H15.
  change (list_repeat (Z.to_nat 0) Vundef) with (@nil val).
  rewrite app_nil_r.
  unfold hmac256drbgabs_common_mpreds.
  thaw FRloop.
(*  normalize.
  assert_PROP (isptr additional) as Hisptr_add by entailer!.*)
  freeze [0;2;3;4;5;6] FR0.
  assert_PROP (field_compatible (tarray tuchar add_len) [] additional) as Hfield_add by entailer!.
  replace_SEP 1 (mpred_passed_to_function (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional) should_reseed * mpred_passed_to_frame (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional) should_reseed).
  {
    clear Heqshould_reseed.
    entailer!.
    apply derives_refl'.
    apply mpred_cond_correct.
  }
  thaw FR0. 
  freeze [0;4;7] FR1.
  (* mbedtls_hmac_drbg_update( ctx, additional, add_len ); *)
  forward_call (if should_reseed then @nil Z else contents, additional, after_reseed_add_len, ctx, (hmac256drbgabs_to_state
         (hmac256drbgabs_update_value after_update_state_abs
            (fst
               (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                  after_update_value out_len))) initial_state), (hmac256drbgabs_update_value after_update_state_abs
         (fst
            (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
               after_update_value out_len))), kv, info_contents).
  { rewrite sepcon_comm. apply sepcon_derives. 2: cancel.
    unfold mpred_passed_to_function(*, mpred_passed_to_frame, fold_right*).
    clear Frame FR1. rewrite Heqafter_reseed_add_len. 
    destruct should_reseed. 2: apply derives_refl.
    apply Tarray_0_emp'.
    eapply field_compatible_array_smaller0. eassumption. omega.
  }
  {
    subst after_reseed_add_len; split.
    destruct should_reseed; omega.
    replace (hmac256drbgabs_value
        (hmac256drbgabs_update_value after_update_state_abs
           (fst
              (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                 after_update_value out_len)))) with (fst
              (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                 after_update_value out_len)) by (
      destruct after_update_state_abs; unfold hmac256drbgabs_value; unfold hmac256drbgabs_update_value; reflexivity).
    repeat split; try now (destruct should_reseed; auto).
    {
      rewrite HMAC_DRBG_generate_helper_Z_Zlength_fst; auto; try omega.
      apply hmac_common_lemmas.HMAC_Zlength.
    }
    {
      apply HMAC_DRBG_generate_helper_Z_isbyteZ_fst; auto; try omega.
      apply hmac_common_lemmas.isbyte_hmac.
    }
  }
  thaw FR1.
  gather_SEP 1 5.
  replace_SEP 0 (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional).
  {
    clear Heqshould_reseed.
    entailer!.
    rewrite mpred_cond_correct with (cond:=should_reseed).
    cancel.
    unfold mpred_passed_to_function.
    destruct should_reseed; [| apply derives_refl].
    apply Tarray_0_emp.
  }

  (* ctx->reseed_counter++; *)
  remember (hmac256drbgabs_hmac_drbg_update
           (hmac256drbgabs_update_value after_update_state_abs
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                    after_update_value out_len)))
           (if should_reseed then [] else contents)) as semi_final_state_abs.
  replace_SEP 1 (hmac256drbgabs_common_mpreds semi_final_state_abs
        initial_state ctx
        info_contents).
  { 
    destruct semi_final_state_abs.
    destruct (hmac256drbgabs_update_value after_update_state_abs
            (fst
               (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                  after_update_value out_len))).
    entailer!.
  }
  
  unfold hmac256drbgabs_common_mpreds. repeat flatten_sepcon_in_SEP.
  freeze [0;2;3;4;5;6] FR2. 
  forward.
  {
    (* type checking *)
    thaw FR2. subst initial_state initial_state_abs.
    entailer!.
    unfold hmac256drbgabs_to_state, hmac256drbgabs_update_value, hmac256drbgabs_hmac_drbg_update, hmac256drbgabs_reseed, hmac256drbgabs_value, hmac256drbgabs_key, HMAC256_DRBG_update, HMAC_DRBG_update. 
    destruct (mbedtls_HMAC256_DRBG_reseed_function s
                               (HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval) contents) as [d s' | e s'];
      try destruct d as [[[[V' key'] reseed_counter'] security_strength'] prediction_resistance'];
      destruct (prediction_resistance || (reseed_counter >? reseed_interval))%bool; destruct contents; auto; unfold is_int; constructor.
  }
  simpl. thaw FR2. 
  destruct semi_final_state_abs.
  rewrite Heqsemi_final_state_abs. simpl. 
  rewrite <- Heqsemi_final_state_abs. simpl. rewrite Heqinitial_state. simpl.
  freeze [0;1;2;3;4;5] FR3. unfold_data_at 1%nat.
  freeze [1;2;4;5;6] OtherFields. forward. (*VST1.6 bug??? why do we need to unfold the data_at to get the forward to succeed here???*)
  thaw OtherFields.
  freeze [0;1;2;3;4;6] CTX. 
  replace_SEP 0
   ( data_at Tsh t_struct_hmac256drbg_context_st
     (md_ctx',
     (map Vint (map Int.repr V0),
     ((Vint (Int.add (Int.repr reseed_counter0) (Int.repr 1))),
     (Vint (Int.repr entropy_len0),
     (Val.of_bool prediction_resistance0, Vint (Int.repr reseed_interval0))))))
     ctx).
  { entailer!. thaw CTX. rewrite add_repr. unfold_data_at 1%nat. cancel. }

  forward.
  Exists Vzero.
  apply andp_right.
  { apply prop_right. unfold return_value_relate_result. 
    rewrite generate_correct with (should_reseed:=(prediction_resistance
                                         || (reseed_counter >?
                                             reseed_interval))%bool) (non_empty_additional:=if (prediction_resistance
                               || (reseed_counter >? reseed_interval))%bool
                           then false
                           else
                            match contents with
                            | [] => false
                            | _ :: _ => true
                            end); auto.
    rewrite <- H2; assumption.
  }
  apply andp_right.
  { apply prop_right. split; trivial. }
  clear CTX. thaw FR3. entailer!.
  unfold hmac256drbgabs_generate.

(*  clear Heqnon_empty_additional.*)

  rewrite generate_correct with (should_reseed:=(prediction_resistance
                                         || (reseed_counter >?
                                             reseed_interval))%bool) (non_empty_additional:=if (prediction_resistance
                               || (reseed_counter >? reseed_interval))%bool
                           then false
                           else
                            match contents with
                            | [] => false
                            | _ :: _ => true
                            end); auto.
  remember (hmac256drbgabs_hmac_drbg_update
               (hmac256drbgabs_update_value
                  (if if (prediction_resistance
                          || (reseed_counter >? reseed_interval))%bool
                      then false
                      else
                       match contents with
                       | [] => false
                       | _ :: _ => true
                       end
                   then
                    hmac256drbgabs_hmac_drbg_update
                      (HMAC256DRBGabs key V reseed_counter entropy_len
                         prediction_resistance reseed_interval) contents
                   else
                    if (prediction_resistance
                        || (reseed_counter >? reseed_interval))%bool
                    then
                     hmac256drbgabs_reseed
                       (HMAC256DRBGabs key V reseed_counter entropy_len
                          prediction_resistance reseed_interval) s contents
                    else
                     HMAC256DRBGabs key V reseed_counter entropy_len
                       prediction_resistance reseed_interval)
                  (fst
                     (HMAC_DRBG_generate_helper_Z HMAC256
                        (hmac256drbgabs_key
                           (if if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then false
                               else
                                match contents with
                                | [] => false
                                | _ :: _ => true
                                end
                            then
                             hmac256drbgabs_hmac_drbg_update
                               (HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval) contents
                            else
                             if (prediction_resistance
                                 || (reseed_counter >? reseed_interval))%bool
                             then
                              hmac256drbgabs_reseed
                                (HMAC256DRBGabs key V reseed_counter
                                   entropy_len prediction_resistance
                                   reseed_interval) s contents
                             else
                              HMAC256DRBGabs key V reseed_counter entropy_len
                                prediction_resistance reseed_interval))
                        (hmac256drbgabs_value
                           (if if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then false
                               else
                                match contents with
                                | [] => false
                                | _ :: _ => true
                                end
                            then
                             hmac256drbgabs_hmac_drbg_update
                               (HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval) contents
                            else
                             if (prediction_resistance
                                 || (reseed_counter >? reseed_interval))%bool
                             then
                              hmac256drbgabs_reseed
                                (HMAC256DRBGabs key V reseed_counter
                                   entropy_len prediction_resistance
                                   reseed_interval) s contents
                             else
                              HMAC256DRBGabs key V reseed_counter entropy_len
                                prediction_resistance reseed_interval)) out_len))) (if (prediction_resistance
                              || (reseed_counter >? reseed_interval))%bool
                          then []
                          else contents)) as semi_final_state_abs.
  remember (sublist 0 out_len
                    (snd
                       (HMAC_DRBG_generate_helper_Z HMAC256
                          (hmac256drbgabs_key
                             (if if (prediction_resistance
                                     || (reseed_counter >? reseed_interval))%bool
                                 then false
                                 else
                                  match contents with
                                  | [] => false
                                  | _ :: _ => true
                                  end
                              then
                               hmac256drbgabs_hmac_drbg_update
                                 (HMAC256DRBGabs key V reseed_counter
                                    entropy_len prediction_resistance
                                    reseed_interval) contents
                              else
                               if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then
                                hmac256drbgabs_reseed
                                  (HMAC256DRBGabs key V reseed_counter
                                     entropy_len prediction_resistance
                                     reseed_interval) s contents
                               else
                                HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval))
                          (hmac256drbgabs_value
                             (if if (prediction_resistance
                                     || (reseed_counter >? reseed_interval))%bool
                                 then false
                                 else
                                  match contents with
                                  | [] => false
                                  | _ :: _ => true
                                  end
                              then
                               hmac256drbgabs_hmac_drbg_update
                                 (HMAC256DRBGabs key V reseed_counter
                                    entropy_len prediction_resistance
                                    reseed_interval) contents
                              else
                               if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then
                                hmac256drbgabs_reseed
                                  (HMAC256DRBGabs key V reseed_counter
                                     entropy_len prediction_resistance
                                     reseed_interval) s contents
                               else
                                HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval)) out_len))) as generate_output_bytes.

  destruct semi_final_state_abs.
  pose proof (Heqsemi_final_state_abs) as Hsemi_final_metadata.
  rewrite Hnon_empty_additional_contents in Hsemi_final_metadata.
  apply metadata_preserved in Hsemi_final_metadata.
  pose proof (Heqsemi_final_state_abs) as Hsemi_final_reseed_counter.
  rewrite Hnon_empty_additional_contents in Hsemi_final_reseed_counter.
  apply reseed_counter_values in Hsemi_final_reseed_counter.
(*  clear Heqgenerate_output_bytes Heqsemi_final_state_abs.*)
  unfold return_value_relate_result.
  unfold get_stream_result.
  unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state_handle, hmac256drbgabs_increment_reseed_counter.
  unfold hmac256drbgabs_to_state, hmac256drbg_relate.
  unfold hmac256drbgstate_md_info_pointer.
  entailer!.
  simpl in *.
  destruct Hsemi_final_metadata as [Hentropy_len0 [Hpr0 Hreseed_interval0]].
  subst entropy_len0.
  subst reseed_interval0.
  rewrite andb_negb_r in *. rewrite Hadd_lenb in *. clear H2.
  remember ((prediction_resistance || (reseed_counter >? reseed_interval))%bool) as b.
  destruct b.
  + unfold initial_world.EqDec_Z in *. simpl. clear H9 H17 H19. simpl in H18. 
    clear HisbyteZ_after_update_value. simpl in HZlength_after_update_value. clear HZlength_after_update_value. 
    clear Hnon_empty_additional_contents Hnon_empty_additional_should_reseed  H5 H18. 
    clear Hshould_reseed_non_empty_additional. 
    destruct (Hshould_reseed_get_entropy (eq_refl _)) as [eb [s' EB]]. clear Hshould_reseed_get_entropy.
    rewrite EB in *.
    remember (HMAC_DRBG_update HMAC256 (eb ++ contents) key V) as DB_HAMCUP. 
    unfold hmac256drbgabs_value in *. unfold hmac256drbgabs_key in *. 
    unfold hmac256drbgabs_update_value in *.
    unfold hmac256drbgabs_hmac_drbg_update in *.
    destruct DB_HAMCUP. simpl in Heqsemi_final_state_abs0.
    inv Heqsemi_final_state_abs0. simpl in Heqsemi_final_state_abs.
    inv Heqsemi_final_state_abs. cancel.
  + unfold initial_world.EqDec_Z in *. simpl. subst prediction_resistance0. clear H9 H17 H19 H18. 
    clear HZlength_after_update_value. 
    clear Hnon_empty_additional_contents Hnon_empty_additional_should_reseed  H5. 
    clear Hshould_reseed_non_empty_additional. clear Hshould_reseed_get_entropy.
    destruct contents.
    - (*nil*) rewrite Zlength_nil in *. simpl in Heqsemi_final_state_abs. simpl in Heqsemi_final_state_abs0.
      rewrite <- Heqsemi_final_state_abs in Heqsemi_final_state_abs0. clear Heqsemi_final_state_abs .
      inv Heqsemi_final_state_abs0. cancel.
    - (*cons*) rewrite Zlength_cons in *. 
      destruct (zeq (Z.succ (Zlength contents)) 0). 
        exfalso. clear - e. unfold Z.succ in e. specialize (Zlength_nonneg contents). intros; omega.
      rewrite <- Heqsemi_final_state_abs in Heqsemi_final_state_abs0. clear Heqsemi_final_state_abs .
      inv Heqsemi_final_state_abs0. cancel.
Admitted. (*Time Qed. Does not finish within 1h*)

Lemma body_hmac_drbg_reseed_steps3To8 Espec contents additional add_len output out_len
      ctx md_ctx' V' reseed_counter' entropy_len' prediction_resistance' reseed_interval' 
      key V reseed_counter entropy_len prediction_resistance reseed_interval kv 
      (info_contents : reptype t_struct_mbedtls_md_info) (s : ENTROPY.stream):
forall
(H : 0 <= add_len <= Int.max_unsigned)
(H0 : 0 <= out_len <= Int.max_unsigned)
(initial_state_abs : hmac256drbgabs)
(Heqinitial_state_abs : initial_state_abs =
                       HMAC256DRBGabs key V reseed_counter entropy_len
                         prediction_resistance reseed_interval)
(H1 : Zlength (hmac256drbgabs_value initial_state_abs) =
     32)
(H2 : add_len = Zlength contents)
(H3 : hmac256drbgabs_entropy_len initial_state_abs = 32)
(H4 : hmac256drbgabs_reseed_interval initial_state_abs = 10000)
(Hreseed_counter_in_range : 0 <=
                           hmac256drbgabs_reseed_counter initial_state_abs <=
                           Int.max_signed)
(H6 : Forall isbyteZ (hmac256drbgabs_value initial_state_abs))
(H7 : Forall isbyteZ contents)
(H5 : map Vint (map Int.repr V) = V')
(H8 : Vint (Int.repr reseed_counter) = reseed_counter')
(H9 : Vint (Int.repr entropy_len) = entropy_len')
(H10 : Vint (Int.repr reseed_interval) = reseed_interval')
(H11 : Val.of_bool prediction_resistance = prediction_resistance')
(initial_state : mdstate * (list val * (val * (val * (val * val)))))
(Heqinitial_state : initial_state =
                   (md_ctx',
                   (map Vint (map Int.repr V),
                   (Vint (Int.repr reseed_counter),
                   (Vint (Int.repr entropy_len),
                   (Val.of_bool prediction_resistance,
                   Vint (Int.repr reseed_interval)))))))
(H12 : out_len <= 1024)
(Hout_len : 0 <= out_len <= 1024)
(Hout_lenb : (out_len >? 1024) = false)
(H13 : add_len <= 256)
(Hadd_len : 0 <= add_len <= 256)
(Hadd_lenb : (add_len >? 256) = false)
(should_reseed : bool)
(Heqshould_reseed : should_reseed =
                   (prediction_resistance
                    || (reseed_counter >? reseed_interval))%bool)
(*Delta_specs := abbreviate : PTree.t funspec*)
(after_reseed_state_abs : hmac256drbgabs)
(Heqafter_reseed_state_abs : after_reseed_state_abs =
                            (if should_reseed
                             then
                              hmac256drbgabs_reseed initial_state_abs s
                                contents
                             else initial_state_abs))
(after_reseed_s : ENTROPY.stream)
(Heqafter_reseed_s : after_reseed_s =
                    (if should_reseed
                     then
                      get_stream_result
                        (mbedtls_HMAC256_DRBG_reseed_function s
                           initial_state_abs contents)
                     else s))
(after_reseed_add_len : Z)
(Heqafter_reseed_add_len : after_reseed_add_len =
                          (if should_reseed then 0 else add_len))
(Hshould_reseed_get_entropy : should_reseed = true ->
                             exists
                               (entropy_bytes : list Z) (s' : ENTROPY.stream),
                               get_entropy 256 entropy_len entropy_len
                                 prediction_resistance s =
                               ENTROPY.success entropy_bytes s')
(isptrAdditional : isptr additional)
(non_empty_additional : bool)
(Heqnon_empty_additional : non_empty_additional =
                          (if eq_dec after_reseed_add_len 0
                           then false
                           else true))
(Hnon_empty_additional_contents : non_empty_additional =
                                 (if should_reseed
                                  then false
                                  else
                                   match contents with
                                   | [] => false
                                   | _ :: _ => true
                                   end))
(Hshould_reseed_non_empty_additional : should_reseed = true ->
                                      non_empty_additional = false)
(Hnon_empty_additional_should_reseed : non_empty_additional = true ->
                                      should_reseed = false)
(after_update_state_abs : hmac256drbgabs)
(Heqafter_update_state_abs : after_update_state_abs =
                            (if non_empty_additional
                             then
                              hmac256drbgabs_hmac_drbg_update
                                initial_state_abs contents
                             else after_reseed_state_abs))
(*Delta := abbreviate : tycontext*),
@semax hmac_drbg_compspecs.CompSpecs Espec 
  (initialized_list
     [_ctx; _md_len; _left; _out; _info; _prediction_resistance;
     _reseed_counter; _reseed_interval; 245%positive; 244%positive;
     241%positive]
     (func_tycontext f_mbedtls_hmac_drbg_random_with_add HmacDrbgVarSpecs
        HmacDrbgFunSpecs))
  (PROP  ()
   LOCAL  (temp _md_len (Vint (Int.repr (32)));
   temp _info (let (x, _) := md_ctx' in x);
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance);
   temp _out output; temp _left (Vint (Int.repr out_len)); temp _ctx ctx;
   temp _p_rng ctx; temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvar sha._K256 kv;
   temp 245%positive (Val.of_bool non_empty_additional))
   SEP  (Stream after_reseed_s;
   hmac256drbgabs_common_mpreds after_update_state_abs initial_state ctx
     info_contents;
   data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
     additional; data_at_ Tsh (tarray tuchar out_len) output; K_vector kv))
  (Ssequence
     (Swhile
        (Ebinop One (Etempvar _left tuint) (Econst_int (Int.repr 0) tint)
           tint)
        (Ssequence
           (Ssequence
              (Sifthenelse
                 (Ebinop Ogt (Etempvar _left tuint) (Etempvar _md_len tuint)
                    tint)
                 (Sset 246%positive (Ecast (Etempvar _md_len tuint) tuint))
                 (Sset 246%positive (Ecast (Etempvar _left tuint) tuint)))
              (Sset _use_len (Etempvar 246%positive tuint)))
           (Ssequence
              (Scall None
                 (Evar _mbedtls_md_hmac_reset
                    (Tfunction
                       (Tcons (tptr (Tstruct _mbedtls_md_context_t noattr))
                          Tnil) tint cc_default))
                 [Eaddrof
                    (Efield
                       (Ederef
                          (Etempvar _ctx
                             (tptr
                                (Tstruct _mbedtls_hmac_drbg_context noattr)))
                          (Tstruct _mbedtls_hmac_drbg_context noattr))
                       _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                    (tptr (Tstruct _mbedtls_md_context_t noattr))])
              (Ssequence
                 (Scall None
                    (Evar _mbedtls_md_hmac_update
                       (Tfunction
                          (Tcons
                             (tptr (Tstruct _mbedtls_md_context_t noattr))
                             (Tcons (tptr tuchar) (Tcons tuint Tnil))) tint
                          cc_default))
                    [Eaddrof
                       (Efield
                          (Ederef
                             (Etempvar _ctx
                                (tptr
                                   (Tstruct _mbedtls_hmac_drbg_context noattr)))
                             (Tstruct _mbedtls_hmac_drbg_context noattr))
                          _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                       (tptr (Tstruct _mbedtls_md_context_t noattr));
                    Efield
                      (Ederef
                         (Etempvar _ctx
                            (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                         (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
                      (tarray tuchar 32); Etempvar _md_len tuint])
                 (Ssequence
                    (Scall None
                       (Evar _mbedtls_md_hmac_finish
                          (Tfunction
                             (Tcons
                                (tptr (Tstruct _mbedtls_md_context_t noattr))
                                (Tcons (tptr tuchar) Tnil)) tint cc_default))
                       [Eaddrof
                          (Efield
                             (Ederef
                                (Etempvar _ctx
                                   (tptr
                                      (Tstruct _mbedtls_hmac_drbg_context
                                         noattr)))
                                (Tstruct _mbedtls_hmac_drbg_context noattr))
                             _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                          (tptr (Tstruct _mbedtls_md_context_t noattr));
                       Efield
                         (Ederef
                            (Etempvar _ctx
                               (tptr
                                  (Tstruct _mbedtls_hmac_drbg_context noattr)))
                            (Tstruct _mbedtls_hmac_drbg_context noattr)) _V
                         (tarray tuchar 32)])
                    (Ssequence
                       (Scall None
                          (Evar _memcpy
                             (Tfunction
                                (Tcons (tptr tvoid)
                                   (Tcons (tptr tvoid) (Tcons tuint Tnil)))
                                (tptr tvoid) cc_default))
                          [Etempvar _out (tptr tuchar);
                          Efield
                            (Ederef
                               (Etempvar _ctx
                                  (tptr
                                     (Tstruct _mbedtls_hmac_drbg_context
                                        noattr)))
                               (Tstruct _mbedtls_hmac_drbg_context noattr))
                            _V (tarray tuchar 32); Etempvar _use_len tuint])
                       (Ssequence
                          (Sset _out
                             (Ebinop Oadd (Etempvar _out (tptr tuchar))
                                (Etempvar _use_len tuint) (tptr tuchar)))
                          (Sset _left
                             (Ebinop Osub (Etempvar _left tuint)
                                (Etempvar _use_len tuint) tuint)))))))))
     (Ssequence
        (Scall None
           (Evar _mbedtls_hmac_drbg_update
              (Tfunction
                 (Tcons (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                    (Tcons (tptr tuchar) (Tcons tuint Tnil))) tvoid
                 cc_default))
           [Etempvar _ctx (tptr (Tstruct _mbedtls_hmac_drbg_context noattr));
           Etempvar _additional (tptr tuchar); Etempvar _add_len tuint])
        (Ssequence
           (Sset _reseed_counter
              (Efield
                 (Ederef
                    (Etempvar _ctx
                       (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                    (Tstruct _mbedtls_hmac_drbg_context noattr))
                 _reseed_counter tint))
           (Ssequence
              (Sassign
                 (Efield
                    (Ederef
                       (Etempvar _ctx
                          (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                       (Tstruct _mbedtls_hmac_drbg_context noattr))
                    _reseed_counter tint)
                 (Ebinop Oadd (Etempvar _reseed_counter tint)
                    (Econst_int (Int.repr 1) tint) tint))
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
  (function_body_ret_assert tint
     (EX  ret_value : val,
      PROP 
      (return_value_relate_result
         (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
            contents) ret_value)
      LOCAL  (temp ret_temp ret_value)
      SEP 
      (match
         mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
           contents
       with
       | ENTROPY.success (bytes, _) _ =>
           data_at Tsh (tarray tuchar out_len)
             (map Vint (map Int.repr bytes)) output
       | ENTROPY.error _ _ => data_at_ Tsh (tarray tuchar out_len) output
       end;
      hmac256drbgabs_common_mpreds
        (hmac256drbgabs_generate initial_state_abs s out_len contents)
        (md_ctx',
        (V',
        (reseed_counter',
        (entropy_len', (prediction_resistance', reseed_interval'))))) ctx
        info_contents;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      Stream
        (get_stream_result
           (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs
              out_len contents)); K_vector kv))%assert).
Proof. intros. abbreviate_semax.
  remember (hmac256drbgabs_key after_update_state_abs) as after_update_key.
  remember (hmac256drbgabs_value after_update_state_abs) as after_update_value.
  assert (HZlength_after_update_value: Zlength after_update_value = 32).
  {
    subst after_update_value after_update_state_abs.
    destruct non_empty_additional.
    {
      apply hmac256drbgabs_hmac_drbg_update_Zlength_V.
    }
    subst after_reseed_state_abs.
    destruct should_reseed;[
      apply hmac256drbgabs_reseed_Zlength_V|]; apply H1.
  }
  assert (HisbyteZ_after_update_value: Forall isbyteZ after_update_value).
  {
    subst after_update_value after_update_state_abs.
    destruct non_empty_additional.
    {
      apply hmac256drbgabs_hmac_drbg_update_isbyteZ_V.
    }
    subst after_reseed_state_abs.
    destruct should_reseed;[
      apply hmac256drbgabs_reseed_isbyteZ_V|]; auto.
  }

  (*
  assert_PROP (isptr output) as Hisptr_output by entailer!.
  destruct output; try solve [inversion Hisptr_output].
  rename i into output_i.
  rename b into output_b.
*)
  freeze [0;2] FRloop.
  forward_while (
    EX done: Z,
      PROP  (0 <= done <= out_len; (is_multiple done 32) \/ done = out_len)
      LOCAL  (temp _md_len (Vint (Int.repr (32)));
      temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out (offset_val done output); temp _left (Vint (Int.repr (out_len - done))); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
      gvar sha._K256 kv
      )
      SEP  (FRZL FRloop; (*Stream after_reseed_s;*)
      hmac256drbgabs_common_mpreds (hmac256drbgabs_update_value after_update_state_abs (fst (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key after_update_value done))) initial_state ctx
        info_contents; 
      (*data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;*)
      data_at Tsh (tarray tuchar out_len) ((map Vint (map Int.repr (sublist 0 done (snd (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key after_update_value done))))) ++ list_repeat (Z.to_nat (out_len - done)) Vundef) output; 
      K_vector kv)
  ).
  {
    (* prove the current pre condition implies the loop condition *)
    Exists 0.
    change (sublist 0 0
                  (snd
                     (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                        after_update_value 0))) with (@nil Z).
    replace (out_len - 0) with out_len by omega.
    change ((map Vint (map Int.repr []) ++
          list_repeat (Z.to_nat out_len) Vundef)) with (list_repeat (Z.to_nat out_len) Vundef).
    assert (Hafter_update: (hmac256drbgabs_update_value after_update_state_abs
            (fst
               (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                  after_update_value 0))) = after_update_state_abs).
    {
      simpl.
      subst after_update_value; destruct after_update_state_abs; reflexivity.
    }
    rewrite Hafter_update.
    entailer!.
    left; exists 0.
    omega.
  }
  {
    (* prove the type checking of the loop condition *)
    entailer!.
  }
  {
    clear Heqafter_update_state_abs Heqafter_reseed_s.
    (* prove the loop body preserves the invariant *)
(*    idtac.*)
    destruct H15 as [Hmultiple | Hcontra]; [| subst done; omega]. (*LENB: was H16*)
    destruct Hmultiple as [n Hmultiple].
    unfold hmac256drbgabs_common_mpreds.
    repeat flatten_sepcon_in_SEP. (* normalize.*)
    assert (Hfield_md_ctx: forall ctx', isptr ctx' -> field_compatible t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx' -> ctx' = field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx').
    {
      intros ctx'' Hisptr Hfc.
      unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [|contradiction].
      simpl. change (Int.repr 0) with Int.zero. rewrite offset_val_force_ptr.
      destruct ctx''; inversion Hisptr. reflexivity.
    }
    assert (Hfield_V: forall ctx', isptr ctx' -> field_compatible t_struct_hmac256drbg_context_st [StructField _V] ctx' -> offset_val 12 ctx' = field_address t_struct_hmac256drbg_context_st [StructField _V] ctx').
    {
      intros ctx'' Hisptr Hfc.
      unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [reflexivity|contradiction].
    }
    assert_PROP (isptr ctx) as Hisptr_ctx by entailer!.
    unfold_data_at 1%nat. simpl.
    
    freeze [3;4;5;6] FR_unused_struct_fields.
    freeze [0;1;4;6] FR1.
(*LENB WAS    freeze [2;3;4;5] FR_unused_struct_fields.
    freeze [0;3;5;6] FR1.*)

    rewrite (field_at_data_at _ _ [StructField _md_ctx]);
    rewrite (field_at_data_at _ _ [StructField _V]);
    simpl.

    unfold hmac256drbg_relate.
    destruct after_update_state_abs.
    unfold hmac256drbgabs_update_value.
    rewrite Heqinitial_state.
    unfold hmac256drbgabs_to_state.
    rewrite Heqafter_update_key.
    unfold md_full. simpl.
    Intros. (*normalize.*)
    (* size_t use_len = left > md_len ? md_len : left; *)
    forward_if (
      PROP  ()
      LOCAL  (temp _md_len (Vint (Int.repr 32)); temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out (offset_val done output); temp _left (Vint (Int.repr (out_len - done)));
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
(*      temp 161%positive (Vint (Int.repr (Z.min (32) (out_len - done))));*)
      temp 246%positive (Vint (Int.repr (Z.min (32) (out_len - done))));
      gvar sha._K256 kv)
      SEP (FRZL FR1;
      data_at Tsh (Tstruct _mbedtls_md_context_t noattr) md_ctx'
        (field_address t_struct_hmac256drbg_context_st 
           [StructField _md_ctx] ctx);
      data_at Tsh (tarray tuchar 32)
        (map Vint
           (map Int.repr
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256
                    (hmac256drbgabs_key
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0))
                    after_update_value done))))
        (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx);
      UNDER_SPEC.FULL key0 (snd (snd md_ctx'));
      K_vector kv)
    ).
    {
      (* md_len < left *)
(*      assert (Hmin: 32 < out_len - done).
      {
        subst md_len.
        simpl in H16.
        unfold Int.ltu in H16.
        destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
        assumption.
        rewrite zlt_false in H16;[ inversion H16|].
        change (Int.unsigned (Int.repr 32)) with 32.
        rewrite (Int.unsigned_repr (out_len - done)); try omega.
      }*)
      simpl.
      forward.
(*      subst md_len.*)
      entailer!.
      rewrite Z.min_l; [reflexivity | omega].
    }
    {
      (* md_len >= left *)
      (*assert (Hmin: 32 >= out_len - done).
      {
        subst md_len.
        simpl in H16.
        unfold Int.ltu in H16.
        destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
        rewrite zlt_true in H16;[ inversion H16|].
        change (Int.unsigned (Int.repr 32)) with 32.
        rewrite (Int.unsigned_repr (out_len - done)); try omega.
        assumption.
      }*)
      simpl.
      forward.
(*      subst md_len.*)
      entailer!.
      rewrite Z.min_r; [reflexivity | omega].
    }
    forward.

    (* mbedtls_md_hmac_reset( &ctx->md_ctx ); *)
    assert_PROP (field_compatible (Tarray tuchar 32 noattr) 
          []
          (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)) by entailer!.
    forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx', key0, kv).
    {
      entailer!.
    }

    (*Intros vret; subst vret.*)

    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    assert (HZlength_V: Zlength (fst
              (HMAC_DRBG_generate_helper_Z HMAC256
                 (hmac256drbgabs_key
                    (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                       prediction_resistance0 reseed_interval0))
                 after_update_value done)) = 32).
    {
      apply HMAC_DRBG_generate_helper_Z_Zlength_fst; auto; try omega.
      apply hmac_common_lemmas.HMAC_Zlength.
    }
    forward_call (key0, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx', field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, @nil Z, (fst (HMAC_DRBG_generate_helper_Z HMAC256
                    (hmac256drbgabs_key
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0))
                    after_update_value done)), kv).
    {
      entailer!.
      (*rename H22 into HZlength.*)
      rename H21 into HZlength.
      do 2 rewrite Zlength_map in HZlength.
      rewrite HZlength.
      reflexivity.
    }
    {
      rewrite HZlength_V.
      cancel.
    }
    {
      rewrite HZlength_V.
      change Int.max_unsigned with 4294967295.
      change (two_power_pos 61) with 2305843009213693952.
      repeat split; try omega.
      apply HMAC_DRBG_generate_helper_Z_isbyteZ_fst; auto; try omega.
      apply hmac_common_lemmas.isbyte_hmac.
    }

    Intros. (*Intros vret; subst vret.*)
    rewrite app_nil_l.

    replace_SEP 2 (memory_block Tsh 32 (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)).
    {
      entailer!.
      simpl in HZlength_V.
      unfold hmac256drbgabs_value.
      rewrite HZlength_V.
      apply data_at_memory_block.
    }
    (* mbedtls_md_hmac_finish( &ctx->md_ctx, ctx->V ); *)
    forward_call ((fst
               (HMAC_DRBG_generate_helper_Z HMAC256
                  (hmac256drbgabs_key
                     (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                        prediction_resistance0 reseed_interval0))
                  after_update_value done)), key0, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx', field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, Tsh, kv).
    {
      entailer!.
    }
    Intros. (*Intros vret; subst vret.*)
    thaw FR1. unfold POSTCONDITION, abbreviate. clear POSTCONDITION.
    thaw FR_unused_struct_fields. thaw FRloop.
    apply (loop_before_memcopy Espec contents additional add_len output out_len ctx 
      md_ctx' V' reseed_counter' entropy_len' prediction_resistance' 
      reseed_interval' key V reseed_counter entropy_len prediction_resistance 
      reseed_interval kv info_contents s)
    with (after_reseed_state_abs:=after_reseed_state_abs)(should_reseed:=should_reseed)
         (non_empty_additional:=non_empty_additional)(n:=n); assumption.
  }
apply (body_hmac_drbg_reseed_steps6To8 Espec contents additional add_len output out_len
      ctx md_ctx' V' reseed_counter' entropy_len' prediction_resistance' reseed_interval' 
      key V reseed_counter entropy_len prediction_resistance reseed_interval kv 
      info_contents s) with (should_reseed:=should_reseed)
      (after_reseed_state_abs:=after_reseed_state_abs)(non_empty_additional:=non_empty_additional);
      assumption.
Admitted. (*Time Qed. Doesn't terminate in 1h*)

Lemma body_hmac_drbg_reseed_after_II_check_inputlength Espec contents additional add_len
      output out_len ctx  md_ctx' V' reseed_counter' entropy_len' prediction_resistance'
      reseed_interval' key V reseed_counter entropy_len prediction_resistance 
      reseed_interval kv info_contents (s : ENTROPY.stream)
      (*Delta_specs := abbreviate : PTree.t funspec*):
forall
(H : 0 <= add_len <= Int.max_unsigned)
(H0 : 0 <= out_len <= Int.max_unsigned)
(initial_state_abs : hmac256drbgabs)
(Heqinitial_state_abs : initial_state_abs =
                       HMAC256DRBGabs key V reseed_counter entropy_len
                         prediction_resistance reseed_interval)
(H1 : Zlength (hmac256drbgabs_value initial_state_abs) =
     32)
(H2 : add_len = Zlength contents)
(H3 : hmac256drbgabs_entropy_len initial_state_abs = 32)
(H4 : hmac256drbgabs_reseed_interval initial_state_abs = 10000)
(Hreseed_counter_in_range : 0 <=
                           hmac256drbgabs_reseed_counter initial_state_abs <=
                           Int.max_signed)
(H6 : Forall isbyteZ (hmac256drbgabs_value initial_state_abs))
(H7 : Forall isbyteZ contents)
(H5 : map Vint (map Int.repr V) = V')
(H8 : Vint (Int.repr reseed_counter) = reseed_counter')
(H9 : Vint (Int.repr entropy_len) = entropy_len')
(H10 : Vint (Int.repr reseed_interval) = reseed_interval')
(H11 : Val.of_bool prediction_resistance = prediction_resistance')
(initial_state : mdstate * (list val * (val * (val * (val * val)))))
(Heqinitial_state : initial_state =
                   (md_ctx',
                   (map Vint (map Int.repr V),
                   (Vint (Int.repr reseed_counter),
                   (Vint (Int.repr entropy_len),
                   (Val.of_bool prediction_resistance,
                   Vint (Int.repr reseed_interval)))))))
(H12 : out_len <= 1024)
(Hout_len : 0 <= out_len <= 1024)
(Hout_lenb : (out_len >? 1024) = false)
(*Delta := abbreviate : tycontext*)
(H13 : add_len <= 256)
(Hadd_len : 0 <= add_len <= 256)
(Hadd_lenb : (add_len >? 256) = false)
(should_reseed : bool)
(Heqshould_reseed : should_reseed =
                   (prediction_resistance
                    || (reseed_counter >? reseed_interval))%bool),
@semax hmac_drbg_compspecs.CompSpecs Espec
  (initialized_list
     [_ctx; _md_len; _left; _out; _info; _prediction_resistance;
     _reseed_counter; _reseed_interval; 241%positive]
     (func_tycontext f_mbedtls_hmac_drbg_random_with_add HmacDrbgVarSpecs
        HmacDrbgFunSpecs))
  (PROP  ()
   LOCAL  (temp _md_len (Vint (Int.repr (32)));
   temp _info (let (x, _) := md_ctx' in x);
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance);
   temp _out output; temp _left (Vint (Int.repr out_len)); temp _ctx ctx;
   temp _p_rng ctx; temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
   SEP  (data_at_ Tsh (tarray tuchar out_len) output;
   data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
     additional;
   data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
   md_full key md_ctx';
   data_at Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx');
   Stream s; K_vector kv))
  (Ssequence
     (Ssequence
        (Sifthenelse
           (Ebinop Oeq (Etempvar _prediction_resistance tint)
              (Econst_int (Int.repr 1) tint) tint)
           (Sset 244%positive (Econst_int (Int.repr 1) tint))
           (Sset 244%positive
              (Ecast
                 (Ebinop Ogt (Etempvar _reseed_counter tint)
                    (Etempvar _reseed_interval tint) tint) tbool)))
        (Sifthenelse (Etempvar 244%positive tint)
           (Ssequence
              (Ssequence
                 (Ssequence
                    (Ssequence
                       (Scall (Some 242%positive)
                          (Evar _mbedtls_hmac_drbg_reseed
                             (Tfunction
                                (Tcons
                                   (tptr
                                      (Tstruct _mbedtls_hmac_drbg_context
                                         noattr))
                                   (Tcons (tptr tuchar) (Tcons tuint Tnil)))
                                tint cc_default))
                          [Etempvar _ctx
                             (tptr
                                (Tstruct _mbedtls_hmac_drbg_context noattr));
                          Etempvar _additional (tptr tuchar);
                          Etempvar _add_len tuint])
                       (Sset 243%positive (Etempvar 242%positive tint)))
                    (Sset _ret (Etempvar 243%positive tint)))
                 (Sifthenelse
                    (Ebinop One (Ecast (Etempvar 243%positive tint) tint)
                       (Econst_int (Int.repr 0) tint) tint)
                    (Sreturn (Some (Etempvar _ret tint))) Sskip))
              (Sset _add_len (Econst_int (Int.repr 0) tint))) Sskip))
     (Ssequence
        (Ssequence
           (Sifthenelse
              (Ebinop One (Etempvar _additional (tptr tuchar))
                 (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              (Sset 245%positive
                 (Ecast
                    (Ebinop One (Etempvar _add_len tuint)
                       (Econst_int (Int.repr 0) tint) tint) tbool))
              (Sset 245%positive (Econst_int (Int.repr 0) tint)))
           (Sifthenelse (Etempvar 245%positive tint)
              (Scall None
                 (Evar _mbedtls_hmac_drbg_update
                    (Tfunction
                       (Tcons
                          (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                          (Tcons (tptr tuchar) (Tcons tuint Tnil))) tvoid
                       cc_default))
                 [Etempvar _ctx
                    (tptr (Tstruct _mbedtls_hmac_drbg_context noattr));
                 Etempvar _additional (tptr tuchar); Etempvar _add_len tuint])
              Sskip))
        (Ssequence
           (Swhile
              (Ebinop One (Etempvar _left tuint)
                 (Econst_int (Int.repr 0) tint) tint)
              (Ssequence
                 (Ssequence
                    (Sifthenelse
                       (Ebinop Ogt (Etempvar _left tuint)
                          (Etempvar _md_len tuint) tint)
                       (Sset 246%positive
                          (Ecast (Etempvar _md_len tuint) tuint))
                       (Sset 246%positive
                          (Ecast (Etempvar _left tuint) tuint)))
                    (Sset _use_len (Etempvar 246%positive tuint)))
                 (Ssequence
                    (Scall None
                       (Evar _mbedtls_md_hmac_reset
                          (Tfunction
                             (Tcons
                                (tptr (Tstruct _mbedtls_md_context_t noattr))
                                Tnil) tint cc_default))
                       [Eaddrof
                          (Efield
                             (Ederef
                                (Etempvar _ctx
                                   (tptr
                                      (Tstruct _mbedtls_hmac_drbg_context
                                         noattr)))
                                (Tstruct _mbedtls_hmac_drbg_context noattr))
                             _md_ctx (Tstruct _mbedtls_md_context_t noattr))
                          (tptr (Tstruct _mbedtls_md_context_t noattr))])
                    (Ssequence
                       (Scall None
                          (Evar _mbedtls_md_hmac_update
                             (Tfunction
                                (Tcons
                                   (tptr
                                      (Tstruct _mbedtls_md_context_t noattr))
                                   (Tcons (tptr tuchar) (Tcons tuint Tnil)))
                                tint cc_default))
                          [Eaddrof
                             (Efield
                                (Ederef
                                   (Etempvar _ctx
                                      (tptr
                                         (Tstruct _mbedtls_hmac_drbg_context
                                            noattr)))
                                   (Tstruct _mbedtls_hmac_drbg_context noattr))
                                _md_ctx
                                (Tstruct _mbedtls_md_context_t noattr))
                             (tptr (Tstruct _mbedtls_md_context_t noattr));
                          Efield
                            (Ederef
                               (Etempvar _ctx
                                  (tptr
                                     (Tstruct _mbedtls_hmac_drbg_context
                                        noattr)))
                               (Tstruct _mbedtls_hmac_drbg_context noattr))
                            _V (tarray tuchar 32); Etempvar _md_len tuint])
                       (Ssequence
                          (Scall None
                             (Evar _mbedtls_md_hmac_finish
                                (Tfunction
                                   (Tcons
                                      (tptr
                                         (Tstruct _mbedtls_md_context_t
                                            noattr))
                                      (Tcons (tptr tuchar) Tnil)) tint
                                   cc_default))
                             [Eaddrof
                                (Efield
                                   (Ederef
                                      (Etempvar _ctx
                                         (tptr
                                            (Tstruct
                                               _mbedtls_hmac_drbg_context
                                               noattr)))
                                      (Tstruct _mbedtls_hmac_drbg_context
                                         noattr)) _md_ctx
                                   (Tstruct _mbedtls_md_context_t noattr))
                                (tptr (Tstruct _mbedtls_md_context_t noattr));
                             Efield
                               (Ederef
                                  (Etempvar _ctx
                                     (tptr
                                        (Tstruct _mbedtls_hmac_drbg_context
                                           noattr)))
                                  (Tstruct _mbedtls_hmac_drbg_context noattr))
                               _V (tarray tuchar 32)])
                          (Ssequence
                             (Scall None
                                (Evar _memcpy
                                   (Tfunction
                                      (Tcons (tptr tvoid)
                                         (Tcons (tptr tvoid)
                                            (Tcons tuint Tnil))) (tptr tvoid)
                                      cc_default))
                                [Etempvar _out (tptr tuchar);
                                Efield
                                  (Ederef
                                     (Etempvar _ctx
                                        (tptr
                                           (Tstruct
                                              _mbedtls_hmac_drbg_context
                                              noattr)))
                                     (Tstruct _mbedtls_hmac_drbg_context
                                        noattr)) _V (tarray tuchar 32);
                                Etempvar _use_len tuint])
                             (Ssequence
                                (Sset _out
                                   (Ebinop Oadd (Etempvar _out (tptr tuchar))
                                      (Etempvar _use_len tuint) (tptr tuchar)))
                                (Sset _left
                                   (Ebinop Osub (Etempvar _left tuint)
                                      (Etempvar _use_len tuint) tuint)))))))))
           (Ssequence
              (Scall None
                 (Evar _mbedtls_hmac_drbg_update
                    (Tfunction
                       (Tcons
                          (tptr (Tstruct _mbedtls_hmac_drbg_context noattr))
                          (Tcons (tptr tuchar) (Tcons tuint Tnil))) tvoid
                       cc_default))
                 [Etempvar _ctx
                    (tptr (Tstruct _mbedtls_hmac_drbg_context noattr));
                 Etempvar _additional (tptr tuchar); Etempvar _add_len tuint])
              (Ssequence
                 (Sset _reseed_counter
                    (Efield
                       (Ederef
                          (Etempvar _ctx
                             (tptr
                                (Tstruct _mbedtls_hmac_drbg_context noattr)))
                          (Tstruct _mbedtls_hmac_drbg_context noattr))
                       _reseed_counter tint))
                 (Ssequence
                    (Sassign
                       (Efield
                          (Ederef
                             (Etempvar _ctx
                                (tptr
                                   (Tstruct _mbedtls_hmac_drbg_context noattr)))
                             (Tstruct _mbedtls_hmac_drbg_context noattr))
                          _reseed_counter tint)
                       (Ebinop Oadd (Etempvar _reseed_counter tint)
                          (Econst_int (Int.repr 1) tint) tint))
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))
  (function_body_ret_assert tint
     (EX  ret_value : val,
      PROP 
      (return_value_relate_result
         (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
            contents) ret_value)
      LOCAL  (temp ret_temp ret_value)
      SEP 
      (match
         mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
           contents
       with
       | ENTROPY.success (bytes, _) _ =>
           data_at Tsh (tarray tuchar out_len)
             (map Vint (map Int.repr bytes)) output
       | ENTROPY.error _ _ => data_at_ Tsh (tarray tuchar out_len) output
       end;
      hmac256drbgabs_common_mpreds
        (hmac256drbgabs_generate initial_state_abs s out_len contents)
        (md_ctx',
        (V',
        (reseed_counter',
        (entropy_len', (prediction_resistance', reseed_interval'))))) ctx
        info_contents;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      Stream
        (get_stream_result
           (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs
              out_len contents)); K_vector kv))%assert).
Proof. intros. abbreviate_semax.
 freeze [0;1;2;3;4;5;6] FR0.
 forward_if (
      PROP  ()
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr (32)));
      temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv;
      (*temp 159%positive (Val.of_bool should_reseed) (* ADDED *)*)
      temp 244%positive (Val.of_bool should_reseed) (* ADDED *)
      )
      SEP  (FRZL FR0)). (*data_at_ Tsh (tarray tuchar out_len) output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
      md_full key md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx');
      Stream s; K_vector kv)
    ).*)
  {
    forward.
    entailer!.
    
    rename H14 into Hpr. (*LENB: WAS H15*)
    destruct prediction_resistance.
    (* true *) reflexivity.
    (* false *)
    inversion Hpr.
  }
  {
    rename H14 into Hpr. (*LENB: WAS H15*)
    destruct prediction_resistance; try solve [inversion Hpr].
    simpl in Heqshould_reseed.
    forward.
    subst should_reseed.
    entailer!. 
    (*rewrite <- H16*)
    
    rewrite Z.gtb_ltb.
    unfold Int.lt.
      unfold hmac256drbgabs_reseed_counter in Hreseed_counter_in_range.
    destruct (zlt reseed_interval reseed_counter) as [Hlt | Hlt].
    {
      (* reseed_interval < reseed_counter *)
      assert (Hltb: reseed_interval <? reseed_counter = true) by (rewrite Z.ltb_lt; assumption).
      rewrite Hltb.
      rewrite zlt_true; [reflexivity | ].
      unfold hmac256drbgabs_reseed_interval in H4; rewrite H4.
      change (Int.signed (Int.repr 10000)) with 10000.
      rewrite Int.signed_repr; change Int.min_signed with (-2147483648); change Int.max_signed with (2147483647) in *; try omega.
    }
    {
      assert (Hltb: reseed_interval <? reseed_counter = false) by (rewrite Z.ltb_nlt; assumption).
      rewrite Hltb.
      rewrite zlt_false; [reflexivity | ].
      unfold hmac256drbgabs_reseed_interval in H4; rewrite H4.
      change (Int.signed (Int.repr 10000)) with 10000.
      rewrite Int.signed_repr; change Int.min_signed with (-2147483648); change Int.max_signed with (2147483647) in *; try omega.
    }
  }

  remember (if should_reseed then hmac256drbgabs_reseed initial_state_abs s contents else initial_state_abs) as after_reseed_state_abs.
  remember (if should_reseed then get_stream_result (mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs contents) else s) as after_reseed_s.
  remember (if should_reseed then 0 else add_len) as after_reseed_add_len.
  thaw FR0.
  forward_if (
      PROP (
          should_reseed = true -> exists entropy_bytes s', get_entropy 256 entropy_len entropy_len prediction_resistance s = ENTROPY.success entropy_bytes s'
      )
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr (32)));
      temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr (if should_reseed then 0 else add_len))); gvar sha._K256 kv; (* ADDED *)
(*      temp 159%positive (Val.of_bool should_reseed)*)
      temp 244%positive (Val.of_bool should_reseed))
      SEP  (
        Stream after_reseed_s;
        hmac256drbgabs_common_mpreds after_reseed_state_abs initial_state ctx info_contents
        ; (* ADDED *)
        data_at_ Tsh (tarray tuchar out_len) output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      K_vector kv)).
  {
    rename H14 into Hshould_reseed. (*LENB WAS H15*)
    (* ret = mbedtls_hmac_drbg_reseed( ctx, additional, add_len ) *)
    forward_call (contents, additional, add_len, ctx, initial_state, initial_state_abs,
                  kv, info_contents, s).
    {
      unfold hmac256drbg_relate.
      rewrite Heqinitial_state, Heqinitial_state_abs.
      entailer!.
    }
    {
      (* prove the PROP clauses *)
      change (Int.max_unsigned) with 4294967295.
      repeat split; auto; omega.
    }
    Intros return_value.
    freeze [0;1;2;3;4] FR1.
    forward.

    forward_if (PROP  (return_value = Vzero) (* ADDED *)
      LOCAL  (temp _ret return_value;
       (*temp 158%positive return_value;*)temp 243%positive return_value;
      temp _md_len (*md_len*)(Vint (Int.repr (32)));
      temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv;
(*      temp 159%positive (Val.of_bool should_reseed);*)
      temp 244%positive (Val.of_bool should_reseed))
      SEP (FRZL FR1)).
(*      (hmac256drbgabs_common_mpreds
         (hmac256drbgabs_reseed initial_state_abs s contents) initial_state
         ctx info_contents;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      Stream
        (get_stream_result
           (mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs contents));
      K_vector kv; data_at_ Tsh (tarray tuchar out_len) output)).*)
    {
      (* return_value != 0 *)
      unfold POSTCONDITION, abbreviate. clear POSTCONDITION. thaw FR1.
      forward.
      rename H14 into Hreturn_value; simpl in Hreturn_value. (*LENB: was H15*)
      (*assert (Hret_not_0: _id0 <> Int.zero).
      {
        clear - H16.
        intros contra. subst.
        inversion H16.
      }*)
      apply negb_true_iff in H15. apply int_eq_false_e in H15. 

      unfold hmac256drbgabs_common_mpreds, get_stream_result, hmac256drbg_relate.
      unfold hmac256drbgabs_generate, hmac256drbgabs_reseed, hmac256drbgabs_to_state.
      (*Exists (Vint _id0).*)
      Exists (Vint return_value).
      apply orb_true_iff in Hshould_reseed.
      replace (Z.of_nat (length contents)) with (Zlength contents) by (rewrite Zlength_correct; auto).
      unfold mbedtls_HMAC256_DRBG_generate_function.
      unfold HMAC256_DRBG_generate_function.
      unfold DRBG_generate_function.
      unfold DRBG_generate_function_helper.
      unfold mbedtls_HMAC256_DRBG_reseed_function.
      unfold HMAC256_DRBG_reseed_function.
      unfold DRBG_reseed_function.
      replace (Z.of_nat (length contents)) with (Zlength contents) by (rewrite Zlength_correct; reflexivity).
      rewrite Hout_lenb in *. rewrite Hadd_lenb in *.
      rewrite andb_negb_r in *.
      change (0 >? 256) with false.
      
      remember (get_entropy 256 entropy_len entropy_len prediction_resistance s) as get_entropy_result; destruct get_entropy_result.
      {
        (* entropy succeeded - not possible *)
        clear - Hreturn_value H15(*Hret_not_0*).
        unfold return_value_relate_result in Hreturn_value.
        inv Hreturn_value.
        elim H15; reflexivity. 
      }
      (* entropy failed *)
      destruct Hshould_reseed as [Hpr | Hcount].
      {
        (* prediction_resistance = true *)
        subst.
        entailer!.
      }
      {
        (* reseed_counter > reseed_interval *)
        destruct prediction_resistance; [entailer!|].
        unfold HMAC256_DRBG_generate_algorithm.
        unfold HMAC_DRBG_generate_algorithm.
        rename H4 into Hreseed_interval.
        simpl in Hreseed_interval.
        subst reseed_interval.
        rewrite Hcount.
        rewrite Hadd_lenb.
        rewrite andb_negb_r.
        rewrite <- Heqget_entropy_result.
        entailer!.
      }
    }
    {
      (* return value = 0 *)
      forward.

      assert (Hret_eq_0: return_value = Vzero).
      {
        clear - H15.
        destruct return_value; inv H15.
        remember (Int.eq i (Int.repr 0)) as i_0; destruct i_0; inv H0.
        apply binop_lemmas2.int_eq_true in Heqi_0.
        rewrite Heqi_0; reflexivity.
      }
      subst return_value.
      unfold hmac256drbgabs_common_mpreds.
      entailer!.
    }

    (* add_len = 0; *)
    forward.
    thaw FR1.
    (* prove post condition of if statement *)
    rename H14 into Hreturn_value. (*LENB: WAS H15*)
    subst return_value.
    subst after_reseed_state_abs after_reseed_add_len.
    rewrite Hshould_reseed.
    unfold result_success.
    unfold return_value_relate_result in Hreturn_value.
    entailer!.
    {
      clear - Hreturn_value.
      unfold mbedtls_HMAC256_DRBG_reseed_function in Hreturn_value.
      unfold HMAC256_DRBG_reseed_function in Hreturn_value; unfold DRBG_reseed_function in Hreturn_value.
      rewrite andb_negb_r in Hreturn_value.
      destruct (Zlength contents >? 256); try solve [inversion Hreturn_value]; try solve [assert (contra: False) by (apply Hreturn_value; reflexivity); inversion contra].
      destruct (get_entropy 256 entropy_len entropy_len prediction_resistance s); try solve [inversion Hreturn_value]; try solve [assert (contra: False) by (apply Hreturn_value; reflexivity); inversion contra].
      exists l; exists s0; reflexivity.
    }
    rewrite Hshould_reseed.
    apply derives_refl.
  }
  {
    forward.

    subst after_reseed_state_abs after_reseed_add_len.
    rewrite H14. (*H15.*)
    unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state.
    subst initial_state_abs initial_state.
    entailer!.
    rewrite H14(*H15*); apply derives_refl.
  }

  Intros. (*normalize.*)
  freeze [0;1;2;4] FR3.
  assert_PROP (isptr additional) as isptrAdditional by entailer!.
  rename H14(*H15*) into Hshould_reseed_get_entropy.
  remember (if (*eq_dec additional nullval then false else if*) eq_dec after_reseed_add_len 0 then false else true) as non_empty_additional.

  assert_PROP (non_empty_additional = if should_reseed then false else
                                        match contents with
                                          | [] => false
                                          | _ => true end) as Hnon_empty_additional_contents.
  {
    clear Heqshould_reseed.
    entailer!.
 
    (*
    destruct (eq_dec additional nullval) as [Hadd' | Hadd'].
    {
      (* additional = null *)
      subst additional. destruct H20 as [Hisptr Hfield_compat]; inversion Hisptr.
    }*)
    {
      destruct should_reseed; try reflexivity.
      destruct contents.
      {
        (* contents is empty *)
        rewrite H2; reflexivity.
      }
      {
        (* contents is not empty *)
        rewrite H2, Zlength_cons.
        destruct (eq_dec (Z.succ (Zlength contents)) 0); try reflexivity.
        pose proof (Zlength_nonneg contents); omega.
      }
    }
  }
  assert (Hshould_reseed_non_empty_additional: should_reseed = true -> non_empty_additional = false).
  {
    intros Hshould_reseed_true; rewrite Hshould_reseed_true in *.
    subst after_reseed_add_len non_empty_additional.
    destruct (eq_dec additional nullval); reflexivity.
  }

  assert (Hnon_empty_additional_should_reseed: non_empty_additional = true -> should_reseed = false).
  {
    intros Hnon_empty_additional_true; rewrite Hnon_empty_additional_true in *.
    clear Hnon_empty_additional_contents.
    subst after_reseed_add_len non_empty_additional.
    destruct (eq_dec additional nullval); destruct should_reseed; try solve [inversion Heqnon_empty_additional].
    reflexivity. trivial.
  }
  thaw FR3.
  (* additional != NULL && add_len != 0 *)
  forward_if (PROP  ()
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr (32)));
      temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len)); 
      gvar sha._K256 kv;
(*      temp 160%positive (Val.of_bool non_empty_additional) (* ADDED *)*)
      temp 245%positive (Val.of_bool non_empty_additional) (* ADDED *)
             )
      SEP (Stream after_reseed_s;
      hmac256drbgabs_common_mpreds after_reseed_state_abs initial_state ctx
        info_contents; data_at_ Tsh (tarray tuchar out_len) output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional; K_vector kv)).
  {
    (* prove that additional is comparable with the null pointer *)
    
    unfold denote_tc_comparable.
    assert (Hsize_of: sizeof (*cenv_cs*) (tarray tuchar (Zlength contents)) >= 0).
    {
      pose proof (Zlength_nonneg contents).
      simpl.
      rewrite Z.mul_1_l.
      rewrite Zmax0r by omega.
      omega.
    }
    clear H14.
    (*assert_PROP (isptr additional) as Hisptr by entailer!. LENB: now established above*)
    destruct additional; try solve [inversion isptrAdditional]; clear isptrAdditional.
    entailer!.
    (*auto 50 with valid_pointer.*) apply sepcon_weak_valid_pointer2. apply data_at_weak_valid_ptr. apply top_share_nonidentity.
    omega.
  }
  {
    clear Hnon_empty_additional_contents.
    (* additional <> null *)
    forward.
    entailer!. 

    destruct (prediction_resistance || (reseed_counter >? reseed_interval))%bool.
    auto.
    destruct (eq_dec (Zlength contents) 0).
    rewrite e.
    reflexivity.
    unfold Int.eq, zeq.
    destruct (Z.eq_dec (Int.unsigned (Int.repr (Zlength contents)))
                    (Int.unsigned (Int.repr 0))).
    {
      rewrite Int.unsigned_repr in e; try omega.
      change (Int.unsigned (Int.repr 0)) with 0 in e.
      omega.
    }
    {
      reflexivity.
    }
  }
  { exfalso. clear - H14 isptrAdditional. subst additional. 
    contradiction.
  }

  remember (if non_empty_additional then hmac256drbgabs_hmac_drbg_update initial_state_abs contents else after_reseed_state_abs) as after_update_state_abs.
  forward_if (PROP  ()
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr (32)));
     temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len)); 
      gvar sha._K256 kv;
(*      temp 160%positive (Val.of_bool non_empty_additional)*)
      temp 245%positive (Val.of_bool non_empty_additional))
      SEP  (Stream after_reseed_s;
        hmac256drbgabs_common_mpreds after_update_state_abs initial_state ctx info_contents; (* ADDED *)
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional; data_at_ Tsh (tarray tuchar out_len) output; K_vector kv)).
  {
    (* mbedtls_hmac_drbg_update( ctx, additional, add_len ); *)
    assert (Hshould_reseed_false: should_reseed = false).
    {
      apply Hnon_empty_additional_should_reseed; assumption.
    }
    rewrite Hshould_reseed_false in *.
    unfold hmac256drbgabs_common_mpreds.
    rewrite Heqafter_reseed_add_len, Heqafter_reseed_state_abs.
    forward_call (contents, additional, add_len, ctx,
                 initial_state,
                 initial_state_abs, kv, info_contents
                 ).
    {
      unfold hmac256drbgabs_to_state.
      rewrite Heqinitial_state_abs.
      rewrite Heqinitial_state.
      cancel.
    }
    subst after_update_state_abs after_reseed_state_abs after_reseed_add_len.
    subst initial_state_abs.
(*    rewrite H15.*) rewrite H14.
    entailer!.
  }
  {
    forward.
    subst after_update_state_abs after_reseed_state_abs after_reseed_add_len.
    subst initial_state_abs.
(*    rewrite H15.*) rewrite H14.
    entailer!.
  }
apply (body_hmac_drbg_reseed_steps3To8 Espec contents additional add_len output out_len
      ctx md_ctx' V' reseed_counter' entropy_len' prediction_resistance' reseed_interval' 
      key V reseed_counter entropy_len prediction_resistance reseed_interval kv 
      info_contents s) 
with (should_reseed:=should_reseed)(after_reseed_state_abs:=after_reseed_state_abs); assumption.
Time Qed. (*520 secs -- and almost runs out of memory*)
(*
semax_subcommand HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_random_with_add .x
hmac_drbg_compspecs.CompSpecs Espec Delta
  remember (hmac256drbgabs_key after_update_state_abs) as after_update_key.
  remember (hmac256drbgabs_value after_update_state_abs) as after_update_value.
  assert (HZlength_after_update_value: Zlength after_update_value = 32).
  {
    subst after_update_value after_update_state_abs.
    destruct non_empty_additional.
    {
      apply hmac256drbgabs_hmac_drbg_update_Zlength_V.
    }
    subst after_reseed_state_abs.
    destruct should_reseed;[
      apply hmac256drbgabs_reseed_Zlength_V|]; apply H1.
  }
  assert (HisbyteZ_after_update_value: Forall isbyteZ after_update_value).
  {
    subst after_update_value after_update_state_abs.
    destruct non_empty_additional.
    {
      apply hmac256drbgabs_hmac_drbg_update_isbyteZ_V.
    }
    subst after_reseed_state_abs.
    destruct should_reseed;[
      apply hmac256drbgabs_reseed_isbyteZ_V|]; auto.
  }

  (*
  assert_PROP (isptr output) as Hisptr_output by entailer!.
  destruct output; try solve [inversion Hisptr_output].
  rename i into output_i.
  rename b into output_b.
*)
  Definition is_multiple (multiple base: Z) : Prop := exists i, multiple = (i * base)%Z.
  forward_while (
    EX done: Z,
      PROP  (0 <= done <= out_len; (is_multiple done 32) \/ done = out_len)
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out (offset_val (Int.repr done) output); temp _left (Vint (Int.repr (out_len - done))); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
      gvar sha._K256 kv
      )
      SEP  (Stream after_reseed_s;
      hmac256drbgabs_common_mpreds (hmac256drbgabs_update_value after_update_state_abs (fst (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key after_update_value done))) initial_state ctx
        info_contents;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional; data_at Tsh (tarray tuchar out_len) ((map Vint (map Int.repr (sublist 0 done (snd (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key after_update_value done))))) ++ list_repeat (Z.to_nat (out_len - done)) Vundef) output; 
      K_vector kv)
  ).
  {
    (* prove the current pre condition implies the loop condition *)
    Exists 0.
    change (sublist 0 0
                  (snd
                     (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                        after_update_value 0))) with (@nil Z).
    replace (out_len - 0) with out_len by omega.
    change ((map Vint (map Int.repr []) ++
          list_repeat (Z.to_nat out_len) Vundef)) with (list_repeat (Z.to_nat out_len) Vundef).
    assert (Hafter_update: (hmac256drbgabs_update_value after_update_state_abs
            (fst
               (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                  after_update_value 0))) = after_update_state_abs).
    {
      simpl.
      subst after_update_value; destruct after_update_state_abs; reflexivity.
    }
    rewrite Hafter_update.
    entailer!.
    left; exists 0.
    omega.
  }
  {
    (* prove the type checking of the loop condition *)
    entailer!.
  }
  {
    clear Heqafter_update_state_abs Heqafter_reseed_s.
    (* prove the loop body preserves the invariant *)
    idtac.
    destruct H16 as [Hmultiple | Hcontra]; [| subst done; omega].
    destruct Hmultiple as [n Hmultiple].
    unfold hmac256drbgabs_common_mpreds.
    normalize.
    assert (Hfield_md_ctx: forall ctx', isptr ctx' -> field_compatible t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx' -> ctx' = field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx').
    {
      intros ctx'' Hisptr Hfc.
      unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [|contradiction].
      simpl. change (Int.repr 0) with Int.zero. rewrite offset_val_force_ptr.
      destruct ctx''; inversion Hisptr. reflexivity.
    }
    assert (Hfield_V: forall ctx', isptr ctx' -> field_compatible t_struct_hmac256drbg_context_st [StructField _V] ctx' -> offset_val (Int.repr 12) ctx' = field_address t_struct_hmac256drbg_context_st [StructField _V] ctx').
    {
      intros ctx'' Hisptr Hfc.
      unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [reflexivity|contradiction].
    }
    assert_PROP (isptr ctx) as Hisptr_ctx by entailer!.
    unfold_data_at 1%nat.
    
    freeze [2;3;4;5] FR_unused_struct_fields.
    freeze [0;3;5;6] FR1.

    rewrite (field_at_data_at _ _ [StructField _md_ctx]);
    rewrite (field_at_data_at _ _ [StructField _V]);
    simpl.

    unfold hmac256drbg_relate.
    destruct after_update_state_abs.
    unfold hmac256drbgabs_update_value.
    rewrite Heqinitial_state.
    unfold hmac256drbgabs_to_state.
    rewrite Heqafter_update_key.
    unfold md_full.
    normalize.
    (* size_t use_len = left > md_len ? md_len : left; *)
    forward_if (
      PROP  ()
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out (offset_val (Int.repr done) output); temp _left (Vint (Int.repr (out_len - done)));
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
      temp 161%positive (Vint (Int.repr (Z.min (32) (out_len - done))));
      gvar sha._K256 kv)
      SEP (FRZL FR1;
      data_at Tsh (Tstruct _mbedtls_md_context_t noattr) md_ctx'
        (field_address t_struct_hmac256drbg_context_st 
           [StructField _md_ctx] ctx);
      data_at Tsh (tarray tuchar 32)
        (map Vint
           (map Int.repr
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256
                    (hmac256drbgabs_key
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0))
                    after_update_value done))))
        (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx);
      UNDER_SPEC.FULL key0 (snd (snd md_ctx'));
      data_at Tsh (tarray tuchar out_len)
        (map Vint
           (map Int.repr
              (sublist 0 done
                 (snd
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done)))) ++
         list_repeat (Z.to_nat (out_len - done)) Vundef) output; 
      K_vector kv)
    ).
    {
      (* md_len < left *)
      assert (Hmin: 32 < out_len - done).
      {
        subst md_len.
        simpl in H16.
        unfold Int.ltu in H16.
        destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
        assumption.
        rewrite zlt_false in H16;[ inversion H16|].
        change (Int.unsigned (Int.repr 32)) with 32.
        rewrite (Int.unsigned_repr (out_len - done)); try omega.
      }
      forward.
      subst md_len.
      entailer!.
      rewrite Z.min_l; [reflexivity | omega].
    }
    {
      (* md_len >= left *)
      assert (Hmin: 32 >= out_len - done).
      {
        subst md_len.
        simpl in H16.
        unfold Int.ltu in H16.
        destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
        rewrite zlt_true in H16;[ inversion H16|].
        change (Int.unsigned (Int.repr 32)) with 32.
        rewrite (Int.unsigned_repr (out_len - done)); try omega.
        assumption.
      }
      forward.
      subst md_len.
      entailer!.
      rewrite Z.min_r; [reflexivity | omega].
    }
    forward.

    (* mbedtls_md_hmac_reset( &ctx->md_ctx ); *)
    assert_PROP (field_compatible (Tarray tuchar 32 noattr) 
          []
          (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)) by entailer!.
    forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx', key0, kv).
    {
      entailer!.
    }

    Intros vret; subst vret.

    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    assert (HZlength_V: Zlength (fst
              (HMAC_DRBG_generate_helper_Z HMAC256
                 (hmac256drbgabs_key
                    (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                       prediction_resistance0 reseed_interval0))
                 after_update_value done)) = 32).
    {
      apply HMAC_DRBG_generate_helper_Z_Zlength_fst; auto; try omega.
      apply hmac_common_lemmas.HMAC_Zlength.
    }
    forward_call (key0, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx', field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, @nil Z, (fst (HMAC_DRBG_generate_helper_Z HMAC256
                    (hmac256drbgabs_key
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0))
                    after_update_value done)), kv).
    {
      entailer!.
      rename H22 into HZlength.
      do 2 rewrite Zlength_map in HZlength.
      rewrite HZlength.
      reflexivity.
    }
    {
      rewrite HZlength_V.
      cancel.
    }
    {
      rewrite HZlength_V.
      change Int.max_unsigned with 4294967295.
      change (two_power_pos 61) with 2305843009213693952.
      repeat split; try omega.
      apply HMAC_DRBG_generate_helper_Z_isbyteZ_fst; auto; try omega.
      apply hmac_common_lemmas.isbyte_hmac.
    }

    Intros vret; subst vret.
    rewrite app_nil_l.

    replace_SEP 2 (memory_block Tsh 32 (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)).
    {
      entailer!.
      simpl in HZlength_V.
      unfold hmac256drbgabs_value.
      rewrite HZlength_V.
      apply data_at_memory_block.
    }

    (* mbedtls_md_hmac_finish( &ctx->md_ctx, ctx->V ); *)
    forward_call ((fst
               (HMAC_DRBG_generate_helper_Z HMAC256
                  (hmac256drbgabs_key
                     (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                        prediction_resistance0 reseed_interval0))
                  after_update_value done)), key0, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx', field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, Tsh, kv).
    {
      entailer!.
    }
    Intros vret; subst vret.
    assert_PROP (field_compatible (tarray tuchar out_len) [] output) as Hfield_compat_output by entailer!.
    replace_SEP 5 (
                  data_at Tsh (tarray tuchar done) (map Vint
           (map Int.repr
              (sublist 0 done
                 (snd
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))))) output *
                  data_at Tsh (tarray tuchar (out_len - done)) (list_repeat (Z.to_nat (out_len - done)) Vundef) (offset_val (Int.repr done) output)
    ).
    {
      entailer!.
      apply derives_refl'.

      assert (HZlength1: Zlength (map Vint
        (map Int.repr
           (sublist 0 (n * 32)%Z
              (snd
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0
                    (hmac256drbgabs_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)) (n * 32)%Z))))) = (n * 32)%Z).
      {
        do 2 rewrite Zlength_map.
        rewrite Zlength_sublist; [omega|omega|].
        rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; auto; try omega.
        apply hmac_common_lemmas.HMAC_Zlength.
        exists n; reflexivity.
      }
      
      apply data_at_complete_split; try rewrite HZlength1; try rewrite Zlength_list_repeat; auto; try omega.
      replace ((n * 32)%Z + (out_len - (n * 32)%Z)) with out_len by omega.
      assumption.
    }
    normalize.
    
    remember (offset_val (Int.repr done) output) as done_output.
    remember (Z.min 32 (out_len - done)) as use_len.
    assert_PROP (field_compatible (tarray tuchar (out_len - done)) [] done_output) as Hfield_compat_done_output.
    {
      clear Heqdone_output Hmultiple.
      entailer!.
      rewrite H23 (*Zlength = done *) in H25 (*field compatible *); apply H25.
    }
    replace_SEP 1 (
                  data_at Tsh (tarray tuchar use_len) (list_repeat (Z.to_nat use_len) Vundef) done_output *
                  data_at Tsh (tarray tuchar (out_len - done - use_len)) (list_repeat (Z.to_nat (out_len - done - use_len)) Vundef) (offset_val (Int.repr use_len) done_output)
    ).
    {
      clear Hmultiple Heqdone_output.
      entailer!.
      apply derives_refl'.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_list_repeat; auto; try omega.
        replace (32 + (out_len - done - 32)) with (out_len - done) by omega; assumption.
        rewrite list_repeat_app.
        rewrite <- Z2Nat.inj_add; try omega.
        replace (32 + (out_len - done - 32)) with (out_len - done) by omega; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_list_repeat; auto; try omega.
        replace (out_len - done + (out_len - done - (out_len - done))) with (out_len - done) by omega; assumption.
        replace (out_len - done - (out_len - done)) with 0 by omega; simpl; rewrite app_nil_r; reflexivity.
      }
    }
    normalize.

    replace_SEP 0 (memory_block Tsh use_len done_output).
    {
      clear Hmultiple.
      entailer!.
      eapply derives_trans; [apply data_at_memory_block|].
      replace (sizeof cenv_cs (tarray tuchar (Z.min 32 (out_len - done)))) with (Z.min 32 (out_len - done)).
      apply derives_refl.
      simpl.
      destruct (Z.min_dec 32 (out_len - done));
      rewrite Zmax0r; omega.
    }
    replace_SEP 6 (data_at Tsh (tarray tuchar use_len) (sublist 0 use_len (map Vint (map Int.repr (HMAC256
                 (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))
                 key0)))) (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx) *
                   data_at Tsh (tarray tuchar (32 - use_len)) (sublist use_len 32 (map Vint (map Int.repr (HMAC256
                 (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))
                 key0)))) (offset_val (Int.repr use_len) (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx))
    ).
    {
      clear Hmultiple.
      entailer!.
      apply derives_refl'.
      rewrite hmac_common_lemmas.HMAC_Zlength.
      remember (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0
                    (hmac256drbgabs_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)) done)) as V0'; clear HeqV0'.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        rewrite sublist_nil.
        rewrite app_nil_r.
        symmetry; apply sublist_same.
        reflexivity.
        repeat rewrite Zlength_map; rewrite hmac_common_lemmas.HMAC_Zlength; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (out_len - done - 0 + (32 - (out_len - done))) with 32 by omega; auto.
        rewrite sublist_rejoin; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
        rewrite sublist_same; try reflexivity; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
      }
    }
    (* memcpy( out, ctx->V, use_len ); *)
    forward_call ((Tsh, Tsh), done_output, (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx), use_len, sublist 0 use_len (map Int.repr
              (HMAC256
                 (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))
                 key0))).
    {
      replace (map Vint
            (sublist 0 use_len
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256
                           (hmac256drbgabs_key
                              (HMAC256DRBGabs key0 V0 reseed_counter0
                                 entropy_len0 prediction_resistance0
                                 reseed_interval0)) after_update_value done))
                     key0)))) with (
            sublist 0 use_len
            (map Vint 
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256
                           (hmac256drbgabs_key
                              (HMAC256DRBGabs key0 V0 reseed_counter0
                                 entropy_len0 prediction_resistance0
                                 reseed_interval0)) after_update_value done))
                     key0)))).
      change (@data_at CompSpecs (fst (Tsh, Tsh)) (tarray tuchar use_len)
         (sublist 0 use_len
            (map Vint
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256
                           (hmac256drbgabs_key
                              (HMAC256DRBGabs key0 V0 reseed_counter0
                                 entropy_len0 prediction_resistance0
                                 reseed_interval0)) after_update_value done))
                     key0))))
         (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)) with
      (@data_at hmac_drbg_compspecs.CompSpecs (fst (Tsh, Tsh)) (tarray tuchar use_len)
         (sublist 0 use_len
            (map Vint
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256
                           (hmac256drbgabs_key
                              (HMAC256DRBGabs key0 V0 reseed_counter0
                                 entropy_len0 prediction_resistance0
                                 reseed_interval0)) after_update_value done))
                     key0))))
         (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)).
      entailer!.
      apply sublist_map.
    }
    {
      change (Int.max_unsigned) with 4294967295.
      repeat split; auto;
      subst use_len; destruct (Z.min_dec 32 (out_len - done)); omega.
    }

    Intros vret; subst vret.

    simpl.
    gather_SEP 0 7.
    replace_SEP 0 (data_at Tsh (tarray tuchar 32) (map Vint
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256 key0
                           after_update_value done)) key0))) (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)).
    {
      clear Hmultiple.
      entailer!.
      apply derives_refl'.
      rewrite <- sublist_map.
      remember (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256 key0
                       (hmac256drbgabs_value
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) (done))) as V0'; clear HeqV0'.
      symmetry.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        rewrite sublist_nil.
        rewrite sublist_same; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
        remember (map Vint (map Int.repr (HMAC256 V0' key0))) as data.
        apply data_at_complete_split; subst data; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        rewrite app_nil_r; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        remember (sublist 0 (out_len - done) (map Vint (map Int.repr (HMAC256 V0' key0)))) as data_left.
        remember (sublist (out_len - done) 32
        (map Vint (map Int.repr (HMAC256 V0' key0)))) as data_right.
        apply data_at_complete_split; subst data_left data_right; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (out_len - done - 0 + (32 - (out_len - done))) with 32 by omega; auto.
        rewrite sublist_rejoin; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
        rewrite sublist_same; try reflexivity; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
      }
    }

    gather_SEP 1 2.
    replace_SEP 0 (data_at Tsh (tarray tuchar (out_len - done)) ((map Vint
           (sublist 0 use_len
              (map Int.repr
                 (HMAC256
                    (fst
                       (HMAC_DRBG_generate_helper_Z HMAC256 key0
                                                    after_update_value done)) key0)))) ++ (list_repeat (Z.to_nat (out_len - done - use_len)) Vundef))
                                       done_output).
    {
      clear Heqdone_output Hmultiple.
      entailer!.
      apply derives_refl'.
      rewrite Zmin_spec.
      symmetry.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; change ((fix map (l : list int) : list val :=
               match l with
               | [] => []
               | a :: t => Vint a :: map t
               end)
              (sublist 0 32
                 (map Int.repr
                    (HMAC256
                       (fst
                          (HMAC_DRBG_generate_helper_Z HMAC256 key0
                             (hmac256drbgabs_value
                                (HMAC256DRBGabs key0 V0 reseed_counter0
                                   entropy_len0 prediction_resistance0
                                   reseed_interval0)) done)) key0)))) with (map Vint
              (sublist 0 32
                 (map Int.repr
                    (HMAC256
                       (fst
                          (HMAC_DRBG_generate_helper_Z HMAC256 key0
                             (hmac256drbgabs_value
                                (HMAC256DRBGabs key0 V0 reseed_counter0
                                   entropy_len0 prediction_resistance0
                                   reseed_interval0)) done)) key0)))); repeat rewrite Zlength_list_repeat; auto; try omega;
        rewrite Zlength_map; rewrite Zlength_sublist; try rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (32 - 0 + (out_len - done - 32)) with (out_len - done) by omega.
        assumption.
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; change ((fix map (l : list int) : list val :=
               match l with
               | [] => []
               | a :: t => Vint a :: map t
               end)
              (sublist 0 (out_len - done)
                 (map Int.repr
                    (HMAC256
                       (fst
                          (HMAC_DRBG_generate_helper_Z HMAC256 key0
                             (hmac256drbgabs_value
                                (HMAC256DRBGabs key0 V0 reseed_counter0
                                   entropy_len0 prediction_resistance0
                                   reseed_interval0)) done)) key0)))) with (map Vint
              (sublist 0 (out_len - done)
                 (map Int.repr
                    (HMAC256
                       (fst
                          (HMAC_DRBG_generate_helper_Z HMAC256 key0
                             (hmac256drbgabs_value
                                (HMAC256DRBGabs key0 V0 reseed_counter0
                                   entropy_len0 prediction_resistance0
                                   reseed_interval0)) done)) key0)))); repeat rewrite Zlength_list_repeat; auto; try omega;
        rewrite Zlength_map; rewrite Zlength_sublist; try rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (out_len - done - 0 + (out_len - done - (out_len - done))) with (out_len - done) by omega.
        assumption.
      }
    }

    gather_SEP 2 0.
    replace_SEP 0 (
                  data_at Tsh (tarray tuchar out_len) ((map Vint
           (map Int.repr
              (sublist 0 done
                 (snd
                    (HMAC_DRBG_generate_helper_Z HMAC256 key0
                       after_update_value done))))) ++ (map Vint
            (sublist 0 use_len
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256 key0
                           after_update_value done)) key0))) ++
          list_repeat (Z.to_nat (out_len - done - use_len)) Vundef)) output
    ).
    {
      entailer!.
      apply derives_refl'.
      symmetry.
      assert (HZlength1: Zlength (
              (snd
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0
                    (hmac256drbgabs_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)) (n * 32)%Z))) = (n * 32)%Z).
      {
        rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; auto; try omega.
        apply hmac_common_lemmas.HMAC_Zlength.
        exists n; reflexivity.
      }
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption];
      apply data_at_complete_split; repeat rewrite Zlength_app; repeat rewrite Zlength_map; try rewrite HZlength1; repeat rewrite Zlength_list_repeat; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
      replace ((n * 32)%Z - 0 + (32 - 0 + (out_len - (n * 32)%Z - 32))) with out_len by omega;
      assumption.
      replace ((n * 32)%Z - 0 + (out_len - (n * 32)%Z - 0 + (out_len - (n * 32)%Z - (out_len - (n * 32)%Z)))) with out_len by omega;
      assumption.
    }

    (* out += use_len; *)
    forward.

    (* left -= use_len; *)
    forward.

    
    Exists (done + use_len).
    unfold hmac256drbgabs_common_mpreds; normalize.

    unfold_data_at 4%nat.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]);
    rewrite (field_at_data_at _ _ [StructField _V]).
    
    unfold md_full.
    
    thaw FR1.
    thaw FR_unused_struct_fields.
    subst.

    entailer!.
    {
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; repeat split; try omega.
      left; exists (n + 1); omega.
      replace (out_len - ((n * 32)%Z + 32)) with (out_len - (n * 32)%Z - 32) by omega;
      reflexivity.
      right; omega.
      replace (out_len - ((n * 32)%Z + (out_len - (n * 32)%Z))) with (out_len - (n * 32)%Z - (out_len - (n * 32)%Z)) by omega;
      reflexivity.
    }

    unfold md_full.
    replace (HMAC256 (fst (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z))
              key0) with (fst
                  (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                     ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z)))).
    cancel.
    apply derives_refl'.
    
    rewrite app_assoc.
    replace (map Vint
        (map Int.repr
           (sublist 0 (n * 32)%Z
              (snd (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z)))) ++
      map Vint
        (sublist 0 (Z.min 32 (out_len - (n * 32)%Z))
           (map Int.repr
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                    ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))))) with (map Vint
        (map Int.repr
           (sublist 0 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))
              (snd
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                    ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))))).
    replace (out_len - (n * 32)%Z - Z.min 32 (out_len - (n * 32)%Z)) with (out_len - ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))) by omega.
    reflexivity.
    rewrite <- map_app.
    rewrite sublist_map.
    rewrite <- map_app.
    replace (sublist 0 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))
           (snd
              (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))) with (sublist 0 (n * 32)%Z
           (snd (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z)) ++
         sublist 0 (Z.min 32 (out_len - (n * 32)%Z))
           (fst
              (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))).
    reflexivity.
    replace (snd
              (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z)))) with (snd (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z) ++ fst
              (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z)))).
    {
      apply while_loop_post_sublist_app; auto.
    }
    {
      apply while_loop_post_incremental_snd; auto.
      intros contra; rewrite contra in HRE; omega.
    }
    {
      apply while_loop_post_incremental_fst; auto.
      idtac.
      intros contra; rewrite contra in HRE; omega.
    }
  }

  assert (Hdone: done = out_len).
  {
    clear - HRE H15 Hout_len.
    assert (Hdiff: out_len - done = 0).
    {
      unfold Int.eq in HRE.
      unfold zeq in HRE.
      destruct (Z.eq_dec (Int.unsigned (Int.repr (out_len - done)))
                (Int.unsigned (Int.repr 0))).
      rewrite (Int.unsigned_repr (out_len - done)) in e.
      rewrite e; reflexivity.
      change (Int.max_unsigned) with 4294967295; omega.
      inversion HRE.
    }
    omega.
  }
  rewrite Hdone.
  replace (out_len - out_len) with 0 by omega.
  change (list_repeat (Z.to_nat 0) Vundef) with (@nil val).
  rewrite app_nil_r.
  unfold hmac256drbgabs_common_mpreds.
  normalize.

  assert_PROP (isptr additional) as Hisptr_add by entailer!.
  assert_PROP (field_compatible (tarray tuchar add_len) [] additional) as Hfield_add by entailer!.
  replace_SEP 4 (mpred_passed_to_function (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional) should_reseed * mpred_passed_to_frame (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional) should_reseed).
  {
    clear Heqshould_reseed.
    entailer!.
    apply derives_refl'.
    apply mpred_cond_correct.
  }

  (* mbedtls_hmac_drbg_update( ctx, additional, add_len ); *)
  forward_call (if should_reseed then @nil Z else contents, additional, after_reseed_add_len, ctx, (hmac256drbgabs_to_state
         (hmac256drbgabs_update_value after_update_state_abs
            (fst
               (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                  after_update_value out_len))) initial_state), (hmac256drbgabs_update_value after_update_state_abs
         (fst
            (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
               after_update_value out_len))), kv, info_contents).
  {
    assert (Stream after_reseed_s *
   mpred_passed_to_frame
     (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional) should_reseed *
   data_at Tsh (tarray tuchar out_len)
     (map Vint
        (map Int.repr
           (sublist 0 out_len
              (snd
                 (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                    after_update_value out_len))))) output |-- fold_right sepcon emp Frame)
    by cancel.
    subst after_reseed_add_len.
    assert (Hadd_0: (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional) = (data_at Tsh (tarray tuchar 0) []
        additional) * (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        (offset_val (Int.repr 0) additional))).
    {
      apply data_at_complete_split; repeat rewrite Zlength_map; try rewrite H2; auto; try omega.
      change (Zlength (@nil Z) + Zlength contents) with (Zlength contents); rewrite <- H2; assumption.
    }
    rewrite Hadd_0.
    subst Frame.
    unfold mpred_passed_to_function, mpred_passed_to_frame, fold_right; destruct should_reseed; entailer!.
    eapply derives_trans.
    apply data_at_memory_block.
    simpl.
    destruct additional; try solve [inversion Hisptr_add].
    apply derives_refl'.
    apply memory_block_zero_Vptr.
  }
  {
    subst after_reseed_add_len; split.
    destruct should_reseed; omega.
    replace (hmac256drbgabs_value
        (hmac256drbgabs_update_value after_update_state_abs
           (fst
              (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                 after_update_value out_len)))) with (fst
              (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                 after_update_value out_len)) by (
      destruct after_update_state_abs; unfold hmac256drbgabs_value; unfold hmac256drbgabs_update_value; reflexivity).
    repeat split; try now (destruct should_reseed; auto).
    {
      rewrite HMAC_DRBG_generate_helper_Z_Zlength_fst; auto; try omega.
      apply hmac_common_lemmas.HMAC_Zlength.
    }
    {
      apply HMAC_DRBG_generate_helper_Z_isbyteZ_fst; auto; try omega.
      apply hmac_common_lemmas.isbyte_hmac.
    }
  }

  gather_SEP 1 4.
  replace_SEP 0 (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional).
  {
    clear Heqshould_reseed.
    entailer!.
    rewrite mpred_cond_correct with (cond:=should_reseed).
    cancel.
    unfold mpred_passed_to_function.
    destruct should_reseed; [| apply derives_refl].
    eapply derives_trans.
    apply data_at_memory_block.
    simpl.
    destruct additional'; try solve [inversion Hisptr_add].
    apply derives_refl';
    apply memory_block_zero_Vptr.
  }

  (* ctx->reseed_counter++; *)
  remember (hmac256drbgabs_hmac_drbg_update
           (hmac256drbgabs_update_value after_update_state_abs
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                    after_update_value out_len)))
           (if should_reseed then [] else contents)) as semi_final_state_abs.
  replace_SEP 1 (hmac256drbgabs_common_mpreds semi_final_state_abs
        initial_state ctx
        info_contents).
  {
    destruct semi_final_state_abs.
    destruct (hmac256drbgabs_update_value after_update_state_abs
            (fst
               (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                  after_update_value out_len))).
    unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state.
    entailer!.
    entailer!.
  }
  
  unfold hmac256drbgabs_common_mpreds. normalize.
  forward.
  idtac.
  {
    (* type checking *)
    subst initial_state initial_state_abs.
    entailer!.
    unfold hmac256drbgabs_to_state, hmac256drbgabs_update_value, hmac256drbgabs_hmac_drbg_update, hmac256drbgabs_reseed, hmac256drbgabs_value, hmac256drbgabs_key, HMAC256_DRBG_update, HMAC_DRBG_update. 
    destruct (mbedtls_HMAC256_DRBG_reseed_function s
                               (HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval) contents) as [d s' | e s'];
      try destruct d as [[[[V' key'] reseed_counter'] security_strength'] prediction_resistance'];
      destruct (prediction_resistance || (reseed_counter >? reseed_interval))%bool; destruct contents; auto; unfold is_int; constructor.
  }

  forward.

  (* return 0; *)
  forward.
  
  Exists Vzero.
  
  unfold hmac256drbgabs_generate.

  clear Heqnon_empty_additional.

  rewrite generate_correct with (should_reseed:=(prediction_resistance
                                         || (reseed_counter >?
                                             reseed_interval))%bool) (non_empty_additional:=if (prediction_resistance
                               || (reseed_counter >? reseed_interval))%bool
                           then false
                           else
                            match contents with
                            | [] => false
                            | _ :: _ => true
                            end); auto.
  remember (hmac256drbgabs_hmac_drbg_update
               (hmac256drbgabs_update_value
                  (if if (prediction_resistance
                          || (reseed_counter >? reseed_interval))%bool
                      then false
                      else
                       match contents with
                       | [] => false
                       | _ :: _ => true
                       end
                   then
                    hmac256drbgabs_hmac_drbg_update
                      (HMAC256DRBGabs key V reseed_counter entropy_len
                         prediction_resistance reseed_interval) contents
                   else
                    if (prediction_resistance
                        || (reseed_counter >? reseed_interval))%bool
                    then
                     hmac256drbgabs_reseed
                       (HMAC256DRBGabs key V reseed_counter entropy_len
                          prediction_resistance reseed_interval) s contents
                    else
                     HMAC256DRBGabs key V reseed_counter entropy_len
                       prediction_resistance reseed_interval)
                  (fst
                     (HMAC_DRBG_generate_helper_Z HMAC256
                        (hmac256drbgabs_key
                           (if if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then false
                               else
                                match contents with
                                | [] => false
                                | _ :: _ => true
                                end
                            then
                             hmac256drbgabs_hmac_drbg_update
                               (HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval) contents
                            else
                             if (prediction_resistance
                                 || (reseed_counter >? reseed_interval))%bool
                             then
                              hmac256drbgabs_reseed
                                (HMAC256DRBGabs key V reseed_counter
                                   entropy_len prediction_resistance
                                   reseed_interval) s contents
                             else
                              HMAC256DRBGabs key V reseed_counter entropy_len
                                prediction_resistance reseed_interval))
                        (hmac256drbgabs_value
                           (if if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then false
                               else
                                match contents with
                                | [] => false
                                | _ :: _ => true
                                end
                            then
                             hmac256drbgabs_hmac_drbg_update
                               (HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval) contents
                            else
                             if (prediction_resistance
                                 || (reseed_counter >? reseed_interval))%bool
                             then
                              hmac256drbgabs_reseed
                                (HMAC256DRBGabs key V reseed_counter
                                   entropy_len prediction_resistance
                                   reseed_interval) s contents
                             else
                              HMAC256DRBGabs key V reseed_counter entropy_len
                                prediction_resistance reseed_interval)) done))) (if (prediction_resistance
                              || (reseed_counter >? reseed_interval))%bool
                          then []
                          else contents)) as semi_final_state_abs.
  remember (sublist 0 done
                    (snd
                       (HMAC_DRBG_generate_helper_Z HMAC256
                          (hmac256drbgabs_key
                             (if if (prediction_resistance
                                     || (reseed_counter >? reseed_interval))%bool
                                 then false
                                 else
                                  match contents with
                                  | [] => false
                                  | _ :: _ => true
                                  end
                              then
                               hmac256drbgabs_hmac_drbg_update
                                 (HMAC256DRBGabs key V reseed_counter
                                    entropy_len prediction_resistance
                                    reseed_interval) contents
                              else
                               if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then
                                hmac256drbgabs_reseed
                                  (HMAC256DRBGabs key V reseed_counter
                                     entropy_len prediction_resistance
                                     reseed_interval) s contents
                               else
                                HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval))
                          (hmac256drbgabs_value
                             (if if (prediction_resistance
                                     || (reseed_counter >? reseed_interval))%bool
                                 then false
                                 else
                                  match contents with
                                  | [] => false
                                  | _ :: _ => true
                                  end
                              then
                               hmac256drbgabs_hmac_drbg_update
                                 (HMAC256DRBGabs key V reseed_counter
                                    entropy_len prediction_resistance
                                    reseed_interval) contents
                              else
                               if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then
                                hmac256drbgabs_reseed
                                  (HMAC256DRBGabs key V reseed_counter
                                     entropy_len prediction_resistance
                                     reseed_interval) s contents
                               else
                                HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval)) done))) as generate_output_bytes.
  destruct semi_final_state_abs.
  pose proof (Heqsemi_final_state_abs) as Hsemi_final_metadata.
  apply metadata_preserved in Hsemi_final_metadata.
  pose proof (Heqsemi_final_state_abs) as Hsemi_final_reseed_counter.
  apply reseed_counter_values in Hsemi_final_reseed_counter.
  clear Heqgenerate_output_bytes Heqsemi_final_state_abs.
  unfold return_value_relate_result.
  unfold get_stream_result.
  unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state_handle, hmac256drbgabs_increment_reseed_counter.
  unfold hmac256drbgabs_to_state, hmac256drbg_relate.
  unfold hmac256drbgstate_md_info_pointer.
  entailer!.
  simpl in *.
  destruct Hsemi_final_metadata as [Hentropy_len0 [Hpr0 Hreseed_interval0]].
  subst entropy_len0.
  subst reseed_interval0.
  entailer!.
Qed.
*)
Lemma body_hmac_drbg_reseed: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_random_with_add hmac_drbg_generate_spec.
Proof. unfold hmac_drbg_generate_spec. 
Transparent hmac_drbg_generate_SPEC.
unfold hmac_drbg_generate_SPEC.
Opaque hmac_drbg_generate_SPEC.
  start_function.
  rename H5 into Hreseed_counter_in_range.
  
  destruct initial_state_abs.
  destruct initial_state as [md_ctx' [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].
  unfold hmac256drbg_relate.
  normalize.
  unfold hmac256drbgstate_md_info_pointer.
  simpl.

  remember (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval) as initial_state_abs.
  remember (md_ctx',
        (map Vint (map Int.repr V),
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))) as initial_state.

  (* mbedtls_hmac_drbg_context *ctx = p_rng; *)
  freeze [0;1;3;4;5] FR0.
  forward.
  assert_PROP (ctx = (force_val (sem_cast_neutral ctx))) as Hctx by entailer!.
  rewrite <- Hctx; clear Hctx. rewrite Heqinitial_state in *.

  (* int left = out_len *)
  forward.

  (* out = output *)
  forward.

  (* prediction_resistance = ctx->prediction_resistance *)
  forward.
  {
    (* typechecking *)
    entailer!.
    destruct prediction_resistance; constructor.
  }

  (* reseed_counter = ctx->reseed_counter *)
  forward.

  (* reseed_interval = ctx->reseed_interval *)
  forward.

  (* info = ctx->md_ctx.md_info; *)
  thaw FR0.
  forward.

  (* md_len = mbedtls_md_get_size(info); *)
  freeze [0;1;2;3;4;5;6] FR1.
  forward_call tt.
(*  Intros md_len.*)
  (*rewrite Heqinitial_state. rewrite <- Heqinitial_state.*)

  (* if( out_len > MBEDTLS_HMAC_DRBG_MAX_REQUEST ) *)
  forward_if (
      PROP  (out_len <= 1024)
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr (32)));
      temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP  (FRZL FR1)). (*data_at_ Tsh (tarray tuchar out_len) output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
      md_full key md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx');
      Stream s; K_vector kv)
    ).*)
  {
    (* return( MBEDTLS_ERR_HMAC_DRBG_REQUEST_TOO_BIG ); *)
    forward.

    (* prove post condition of the function *)
    unfold hmac256drbgabs_common_mpreds, get_stream_result, hmac256drbg_relate.
    unfold hmac256drbgabs_generate, hmac256drbgabs_to_state.
    Exists (Vint (Int.repr (-3))).
    unfold mbedtls_HMAC256_DRBG_generate_function.
    unfold HMAC256_DRBG_generate_function.
    unfold DRBG_generate_function.
    rewrite andb_negb_r.
    assert (Hout_len: out_len >? 1024 = true).
    {
      rewrite Z.gtb_ltb.
      apply Z.ltb_lt.
      assumption.
    }
    rewrite Hout_len.
    entailer!. thaw FR1. cancel.
  }
  {
    forward.
    entailer!.
  }

  Intros. 
  assert (Hout_len: 0 <= out_len <= 1024) by omega.
  assert (Hout_lenb: out_len >? 1024 = false).
  {
    rewrite Z.gtb_ltb.
    apply Z.ltb_nlt.
    omega.
  }

  (* if( add_len > MBEDTLS_HMAC_DRBG_MAX_INPUT ) *)
  forward_if (
      PROP  (add_len <= 256) (* ADDED *)
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr (32)));
      temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP  (FRZL FR1)). (*data_at_ Tsh (tarray tuchar out_len) output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
      md_full key md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx');
      Stream s; K_vector kv)*)
  {
    (* return( MBEDTLS_ERR_HMAC_DRBG_INPUT_TOO_BIG ); *)
    forward.

    (* prove function post condition *)
    unfold hmac256drbgabs_common_mpreds, get_stream_result, hmac256drbg_relate.
    unfold hmac256drbgabs_generate, hmac256drbgabs_to_state.
    Exists (Vint (Int.repr (-5))).
    unfold mbedtls_HMAC256_DRBG_generate_function.
    unfold HMAC256_DRBG_generate_function.
    unfold DRBG_generate_function.
    rewrite andb_negb_r.
    rewrite Hout_lenb.
    assert (Hlength_contents: Zlength contents >? 256 = true).
    {
      rewrite Z.gtb_ltb.
      apply Z.ltb_lt.
      subst; assumption.
    }
    replace (Z.of_nat (length contents)) with (Zlength contents) by (rewrite Zlength_correct; auto).
    rewrite Hlength_contents.
    change (0 >? 256) with false.
    entailer!. thaw FR1. cancel.
  }
  {
    forward.
    entailer!.
  }
  Intros. (*normalize.*)
  assert (Hadd_len: 0 <= add_len <= 256) by omega.
  assert (Hadd_lenb: add_len >? 256 = false).
  {
    rewrite Z.gtb_ltb.
    apply Z.ltb_nlt.
    omega.
  }
  remember (orb prediction_resistance (reseed_counter >? reseed_interval)) as should_reseed.
  thaw FR1.
  eapply semax_pre_post.
  Focus 3. apply (body_hmac_drbg_reseed_after_II_check_inputlength Espec contents additional add_len
      output out_len ctx  md_ctx' V' reseed_counter' entropy_len' prediction_resistance'
      reseed_interval' key V reseed_counter entropy_len prediction_resistance 
      reseed_interval kv info_contents s) with (*(V:=V)(entropy_len:=entropy_len) *)(should_reseed:=should_reseed);
       try assumption. 2: eassumption.  2: eassumption. 2: eassumption. 2: eassumption.  2: eassumption. 2: eassumption.
        assumption.
  entailer!. 
  intros. unfold POSTCONDITION, abbreviate. old_go_lower. clear H14.
  entailer!.
Time Qed. (*80 secs*)(*
semax_subcommand HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_random_with_add. @semax hmac_drbg_compspecs.CompSpecs Espec
 forward_if (
      PROP  ()
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr (32)));
      temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv;
      (*temp 159%positive (Val.of_bool should_reseed) (* ADDED *)*)
      temp 244%positive (Val.of_bool should_reseed) (* ADDED *)
      )
      SEP  (data_at_ Tsh (tarray tuchar out_len) output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      data_at Tsh t_struct_hmac256drbg_context_st initial_state ctx;
      md_full key md_ctx';
      data_at Tsh t_struct_mbedtls_md_info info_contents (fst md_ctx');
      Stream s; K_vector kv)
    ).
  {
    forward.
    entailer!.
    
    rename H14 into Hpr. (*LENB: WAS H15*)
    destruct prediction_resistance.
    (* true *) reflexivity.
    (* false *)
    inversion Hpr.
  }
  {
    rename H14 into Hpr. (*LENB: WAS H15*)
    destruct prediction_resistance; try solve [inversion Hpr].
    simpl in Heqshould_reseed.
    forward.
    subst should_reseed.
    entailer!. 
    (*rewrite <- H16*)
    
    rewrite Z.gtb_ltb.
    unfold Int.lt.
      unfold hmac256drbgabs_reseed_counter in Hreseed_counter_in_range.
    destruct (zlt reseed_interval reseed_counter) as [Hlt | Hlt].
    {
      (* reseed_interval < reseed_counter *)
      assert (Hltb: reseed_interval <? reseed_counter = true) by (rewrite Z.ltb_lt; assumption).
      rewrite Hltb.
      rewrite zlt_true; [reflexivity | ].
      unfold hmac256drbgabs_reseed_interval in H4; rewrite H4.
      change (Int.signed (Int.repr 10000)) with 10000.
      rewrite Int.signed_repr; change Int.min_signed with (-2147483648); change Int.max_signed with (2147483647) in *; try omega.
    }
    {
      assert (Hltb: reseed_interval <? reseed_counter = false) by (rewrite Z.ltb_nlt; assumption).
      rewrite Hltb.
      rewrite zlt_false; [reflexivity | ].
      unfold hmac256drbgabs_reseed_interval in H4; rewrite H4.
      change (Int.signed (Int.repr 10000)) with 10000.
      rewrite Int.signed_repr; change Int.min_signed with (-2147483648); change Int.max_signed with (2147483647) in *; try omega.
    }
  }

  remember (if should_reseed then hmac256drbgabs_reseed initial_state_abs s contents else initial_state_abs) as after_reseed_state_abs.
  remember (if should_reseed then get_stream_result (mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs contents) else s) as after_reseed_s.
  remember (if should_reseed then 0 else add_len) as after_reseed_add_len.
  forward_if (
      PROP (
          should_reseed = true -> exists entropy_bytes s', get_entropy 256 entropy_len entropy_len prediction_resistance s = ENTROPY.success entropy_bytes s'
      )
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr (32)));
      temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr (if should_reseed then 0 else add_len))); gvar sha._K256 kv; (* ADDED *)
      temp 159%positive (Val.of_bool should_reseed))
      SEP  (
        Stream after_reseed_s;
        hmac256drbgabs_common_mpreds after_reseed_state_abs initial_state ctx info_contents
        ; (* ADDED *)
        data_at_ Tsh (tarray tuchar out_len) output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      spec_sha.K_vector kv)).
  {
    rename H14 into Hshould_reseed. (*LENB WAS H15*)
    (* ret = mbedtls_hmac_drbg_reseed( ctx, additional, add_len ) *)
    forward_call (contents, additional, add_len, ctx, initial_state, initial_state_abs,
                  kv, info_contents, s).
    {
      unfold hmac256drbg_relate.
      rewrite Heqinitial_state, Heqinitial_state_abs.
      entailer!.
    }
    {
      (* prove the PROP clauses *)
      change (Int.max_unsigned) with 4294967295.
      repeat split; auto; omega.
    }
    Intros return_value.
      
    forward.

    forward_if (PROP  (return_value = Vzero) (* ADDED *)
      LOCAL  (temp _ret return_value; temp 158%positive return_value;
      temp _md_len (*md_len*)(Vint (Int.repr (32)));
      temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv;
(*      temp 159%positive (Val.of_bool should_reseed;*)
      temp 244%positive (Val.of_bool should_reseed))
      SEP 
      (hmac256drbgabs_common_mpreds
         (hmac256drbgabs_reseed initial_state_abs s contents) initial_state
         ctx info_contents;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional;
      Stream
        (get_stream_result
           (mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs contents));
      K_vector kv; data_at_ Tsh (tarray tuchar out_len) output)).
    {
      (* return_value != 0 *)
      forward.

      rename H14 into Hreturn_value; simpl in Hreturn_value. (*LENB: was H15*)
      (*assert (Hret_not_0: _id0 <> Int.zero).
      {
        clear - H16.
        intros contra. subst.
        inversion H16.
      }*)
      apply negb_true_iff in H15. apply int_eq_false_e in H15. 

      unfold hmac256drbgabs_common_mpreds, get_stream_result, hmac256drbg_relate.
      unfold hmac256drbgabs_generate, hmac256drbgabs_reseed, hmac256drbgabs_to_state.
      (*Exists (Vint _id0).*)
      Exists (Vint return_value).
      apply orb_true_iff in Hshould_reseed.
      replace (Z.of_nat (length contents)) with (Zlength contents) by (rewrite Zlength_correct; auto).
      unfold mbedtls_HMAC256_DRBG_generate_function.
      unfold HMAC256_DRBG_generate_function.
      unfold DRBG_generate_function.
      unfold DRBG_generate_function_helper.
      unfold mbedtls_HMAC256_DRBG_reseed_function.
      unfold HMAC256_DRBG_reseed_function.
      unfold DRBG_reseed_function.
      replace (Z.of_nat (length contents)) with (Zlength contents) by (rewrite Zlength_correct; reflexivity).
      rewrite Hout_lenb in *. rewrite Hadd_lenb in *.
      rewrite andb_negb_r in *.
      change (0 >? 256) with false.
      
      remember (get_entropy 256 entropy_len entropy_len prediction_resistance s) as get_entropy_result; destruct get_entropy_result.
      {
        (* entropy succeeded - not possible *)
        clear - Hreturn_value H15(*Hret_not_0*).
        unfold return_value_relate_result in Hreturn_value.
        inv Hreturn_value.
        elim H15; reflexivity. 
      }
      (* entropy failed *)
      destruct Hshould_reseed as [Hpr | Hcount].
      {
        (* prediction_resistance = true *)
        subst.
        entailer!.
      }
      {
        (* reseed_counter > reseed_interval *)
        destruct prediction_resistance; [entailer!|].
        unfold HMAC256_DRBG_generate_algorithm.
        unfold HMAC_DRBG_generate_algorithm.
        rename H4 into Hreseed_interval.
        simpl in Hreseed_interval.
        subst reseed_interval.
        rewrite Hcount.
        rewrite Hadd_lenb.
        rewrite andb_negb_r.
        rewrite <- Heqget_entropy_result.
        entailer!.
      }
    }
    {
      (* return value = 0 *)
      forward.

      assert (Hret_eq_0: return_value = Vzero).
      {
        clear - H15.
        destruct return_value; inv H15.
        remember (Int.eq i (Int.repr 0)) as i_0; destruct i_0; inv H0.
        apply binop_lemmas2.int_eq_true in Heqi_0.
        rewrite Heqi_0; reflexivity.
      }
      subst return_value.
      unfold hmac256drbgabs_common_mpreds.
      entailer!.
    }

    (* add_len = 0; *)
    forward.

    (* prove post condition of if statement *)
    rename H15 into Hreturn_value.
    subst return_value.
    subst after_reseed_state_abs after_reseed_add_len.
    rewrite Hshould_reseed.
    unfold result_success.
    unfold return_value_relate_result in Hreturn_value.
    entailer!.
    {
      clear - Hreturn_value.
      unfold mbedtls_HMAC256_DRBG_reseed_function in Hreturn_value.
      unfold HMAC256_DRBG_reseed_function in Hreturn_value; unfold DRBG_reseed_function in Hreturn_value.
      rewrite andb_negb_r in Hreturn_value.
      destruct (Zlength contents >? 256); try solve [inversion Hreturn_value]; try solve [assert (contra: False) by (apply Hreturn_value; reflexivity); inversion contra].
      destruct (get_entropy 256 entropy_len entropy_len prediction_resistance s); try solve [inversion Hreturn_value]; try solve [assert (contra: False) by (apply Hreturn_value; reflexivity); inversion contra].
      exists l; exists s0; reflexivity.
    }
    rewrite Hshould_reseed.
    apply derives_refl.
  }
  {
    forward.

    subst after_reseed_state_abs after_reseed_add_len.
    rewrite H15.
    unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state.
    subst initial_state_abs initial_state.
    entailer!.
    rewrite H15; apply derives_refl.
  }

  normalize.
  rename H15 into Hshould_reseed_get_entropy.
  remember (if eq_dec additional nullval then false else if eq_dec after_reseed_add_len 0 then false else true) as non_empty_additional.

  assert_PROP (non_empty_additional = if should_reseed then false else
                                        match contents with
                                          | [] => false
                                          | _ => true end) as Hnon_empty_additional_contents.
  {
    clear Heqshould_reseed.
    entailer!.
    destruct (eq_dec additional' nullval) as [Hadd' | Hadd'].
    {
      (* additional = null *)
      subst additional'. destruct H20 as [Hisptr Hfield_compat]; inversion Hisptr.
    }
    {
      destruct should_reseed; try reflexivity.
      destruct contents.
      {
        (* contents is empty *)
        reflexivity.
      }
      {
        (* contents is not empty *)
        rewrite Zlength_cons.
        destruct (eq_dec (Z.succ (Zlength contents)) 0); try reflexivity.
        pose proof (Zlength_nonneg contents); omega.
      }
    }
  }
  assert (Hshould_reseed_non_empty_additional: should_reseed = true -> non_empty_additional = false).
  {
    intros Hshould_reseed_true; rewrite Hshould_reseed_true in *.
    subst after_reseed_add_len non_empty_additional.
    destruct (eq_dec additional nullval); reflexivity.
  }

  assert (Hnon_empty_additional_should_reseed: non_empty_additional = true -> should_reseed = false).
  {
    intros Hnon_empty_additional_true; rewrite Hnon_empty_additional_true in *.
    clear Hnon_empty_additional_contents.
    subst after_reseed_add_len non_empty_additional.
    destruct (eq_dec additional nullval); destruct should_reseed; try solve [inversion Heqnon_empty_additional].
    reflexivity.
  }

  (* additional != NULL && add_len != 0 *)
  forward_if (PROP  ()
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len)); 
      gvar sha._K256 kv;
      temp 160%positive (Val.of_bool non_empty_additional) (* ADDED *)
             )
      SEP 
      (Stream after_reseed_s;
      hmac256drbgabs_common_mpreds after_reseed_state_abs initial_state ctx
        info_contents; data_at_ Tsh (tarray tuchar out_len) output;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional; K_vector kv)).
  {
    (* prove that additional is comparable with the null pointer *)
    
    unfold denote_tc_comparable.
    assert (Hsize_of: sizeof cenv_cs (tarray tuchar (Zlength contents)) >= 0).
    {
      pose proof (Zlength_nonneg contents).
      simpl.
      rewrite Z.mul_1_l.
      rewrite Zmax0r by omega.
      omega.
    }
    assert_PROP (isptr additional) as Hisptr by entailer!. destruct additional; try solve [inversion Hisptr]; clear Hisptr.
    entailer!.
    auto 50 with valid_pointer.
  }
  {
    clear Hnon_empty_additional_contents.
    (* additional <> null *)
    forward.
    entailer!.

    rewrite <- H17.
    destruct (eq_dec additional' nullval); try contradiction.
    destruct (prediction_resistance || (reseed_counter >? reseed_interval))%bool.
    auto.
    destruct (eq_dec (Zlength contents) 0).
    rewrite e.
    reflexivity.
    unfold Int.eq, zeq.
    destruct (Z.eq_dec (Int.unsigned (Int.repr (Zlength contents)))
                    (Int.unsigned (Int.repr 0))).
    {
      rewrite Int.unsigned_repr in e; try omega.
      change (Int.unsigned (Int.repr 0)) with 0 in e.
      omega.
    }
    {
      reflexivity.
    }
  }
  {
    clear Hnon_empty_additional_contents.
    (* additional = null *)
    forward.

    entailer!.
    clear.
    destruct (eq_dec nullval nullval).
    reflexivity.
    assert (contra: False) by (apply n; reflexivity); inversion contra.
  }

  remember (if non_empty_additional then hmac256drbgabs_hmac_drbg_update initial_state_abs contents else after_reseed_state_abs) as after_update_state_abs.
  forward_if (PROP  ()
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len)); 
      gvar sha._K256 kv;
      temp 160%positive (Val.of_bool non_empty_additional))
      SEP  (
        Stream after_reseed_s;
        hmac256drbgabs_common_mpreds after_update_state_abs initial_state ctx info_contents; (* ADDED *)
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional; data_at_ Tsh (tarray tuchar out_len) output; K_vector kv)).
  {
    (* mbedtls_hmac_drbg_update( ctx, additional, add_len ); *)
    assert (Hshould_reseed_false: should_reseed = false).
    {
      apply Hnon_empty_additional_should_reseed; assumption.
    }
    rewrite Hshould_reseed_false in *.
    unfold hmac256drbgabs_common_mpreds.
    rewrite Heqafter_reseed_add_len, Heqafter_reseed_state_abs.
    forward_call (contents, additional, add_len, ctx,
                 initial_state,
                 initial_state_abs, kv, info_contents
                 ).
    {
      unfold hmac256drbgabs_to_state.
      rewrite Heqinitial_state_abs.
      rewrite Heqinitial_state.
      cancel.
    }
    subst after_update_state_abs after_reseed_state_abs after_reseed_add_len.
    subst initial_state_abs.
    rewrite H15.
    entailer!.
  }
  {
    forward.
    subst after_update_state_abs after_reseed_state_abs after_reseed_add_len.
    subst initial_state_abs.
    rewrite H15.
    entailer!.
  }

  remember (hmac256drbgabs_key after_update_state_abs) as after_update_key.
  remember (hmac256drbgabs_value after_update_state_abs) as after_update_value.
  assert (HZlength_after_update_value: Zlength after_update_value = 32).
  {
    subst after_update_value after_update_state_abs.
    destruct non_empty_additional.
    {
      apply hmac256drbgabs_hmac_drbg_update_Zlength_V.
    }
    subst after_reseed_state_abs.
    destruct should_reseed;[
      apply hmac256drbgabs_reseed_Zlength_V|]; apply H1.
  }
  assert (HisbyteZ_after_update_value: Forall isbyteZ after_update_value).
  {
    subst after_update_value after_update_state_abs.
    destruct non_empty_additional.
    {
      apply hmac256drbgabs_hmac_drbg_update_isbyteZ_V.
    }
    subst after_reseed_state_abs.
    destruct should_reseed;[
      apply hmac256drbgabs_reseed_isbyteZ_V|]; auto.
  }

  (*
  assert_PROP (isptr output) as Hisptr_output by entailer!.
  destruct output; try solve [inversion Hisptr_output].
  rename i into output_i.
  rename b into output_b.
*)
  Definition is_multiple (multiple base: Z) : Prop := exists i, multiple = (i * base)%Z.
  forward_while (
    EX done: Z,
      PROP  (0 <= done <= out_len; (is_multiple done 32) \/ done = out_len)
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out (offset_val (Int.repr done) output); temp _left (Vint (Int.repr (out_len - done))); 
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
      gvar sha._K256 kv
      )
      SEP  (Stream after_reseed_s;
      hmac256drbgabs_common_mpreds (hmac256drbgabs_update_value after_update_state_abs (fst (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key after_update_value done))) initial_state ctx
        info_contents;
      data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional; data_at Tsh (tarray tuchar out_len) ((map Vint (map Int.repr (sublist 0 done (snd (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key after_update_value done))))) ++ list_repeat (Z.to_nat (out_len - done)) Vundef) output; 
      K_vector kv)
  ).
  {
    (* prove the current pre condition implies the loop condition *)
    Exists 0.
    change (sublist 0 0
                  (snd
                     (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                        after_update_value 0))) with (@nil Z).
    replace (out_len - 0) with out_len by omega.
    change ((map Vint (map Int.repr []) ++
          list_repeat (Z.to_nat out_len) Vundef)) with (list_repeat (Z.to_nat out_len) Vundef).
    assert (Hafter_update: (hmac256drbgabs_update_value after_update_state_abs
            (fst
               (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                  after_update_value 0))) = after_update_state_abs).
    {
      simpl.
      subst after_update_value; destruct after_update_state_abs; reflexivity.
    }
    rewrite Hafter_update.
    entailer!.
    left; exists 0.
    omega.
  }
  {
    (* prove the type checking of the loop condition *)
    entailer!.
  }
  {
    clear Heqafter_update_state_abs Heqafter_reseed_s.
    (* prove the loop body preserves the invariant *)
    idtac.
    destruct H16 as [Hmultiple | Hcontra]; [| subst done; omega].
    destruct Hmultiple as [n Hmultiple].
    unfold hmac256drbgabs_common_mpreds.
    normalize.
    assert (Hfield_md_ctx: forall ctx', isptr ctx' -> field_compatible t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx' -> ctx' = field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx').
    {
      intros ctx'' Hisptr Hfc.
      unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [|contradiction].
      simpl. change (Int.repr 0) with Int.zero. rewrite offset_val_force_ptr.
      destruct ctx''; inversion Hisptr. reflexivity.
    }
    assert (Hfield_V: forall ctx', isptr ctx' -> field_compatible t_struct_hmac256drbg_context_st [StructField _V] ctx' -> offset_val (Int.repr 12) ctx' = field_address t_struct_hmac256drbg_context_st [StructField _V] ctx').
    {
      intros ctx'' Hisptr Hfc.
      unfold field_address.
      destruct (field_compatible_dec t_struct_hmac256drbg_context_st); [reflexivity|contradiction].
    }
    assert_PROP (isptr ctx) as Hisptr_ctx by entailer!.
    unfold_data_at 1%nat.
    
    freeze [2;3;4;5] FR_unused_struct_fields.
    freeze [0;3;5;6] FR1.

    rewrite (field_at_data_at _ _ [StructField _md_ctx]);
    rewrite (field_at_data_at _ _ [StructField _V]);
    simpl.

    unfold hmac256drbg_relate.
    destruct after_update_state_abs.
    unfold hmac256drbgabs_update_value.
    rewrite Heqinitial_state.
    unfold hmac256drbgabs_to_state.
    rewrite Heqafter_update_key.
    unfold md_full.
    normalize.
    (* size_t use_len = left > md_len ? md_len : left; *)
    forward_if (
      PROP  ()
      LOCAL  (temp _md_len md_len; temp _info (let (x, _) := md_ctx' in x);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out (offset_val (Int.repr done) output); temp _left (Vint (Int.repr (out_len - done)));
      temp _ctx ctx; temp _p_rng ctx; temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
      temp 161%positive (Vint (Int.repr (Z.min (32) (out_len - done))));
      gvar sha._K256 kv)
      SEP (FRZL FR1;
      data_at Tsh (Tstruct _mbedtls_md_context_t noattr) md_ctx'
        (field_address t_struct_hmac256drbg_context_st 
           [StructField _md_ctx] ctx);
      data_at Tsh (tarray tuchar 32)
        (map Vint
           (map Int.repr
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256
                    (hmac256drbgabs_key
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0))
                    after_update_value done))))
        (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx);
      UNDER_SPEC.FULL key0 (snd (snd md_ctx'));
      data_at Tsh (tarray tuchar out_len)
        (map Vint
           (map Int.repr
              (sublist 0 done
                 (snd
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done)))) ++
         list_repeat (Z.to_nat (out_len - done)) Vundef) output; 
      K_vector kv)
    ).
    {
      (* md_len < left *)
      assert (Hmin: 32 < out_len - done).
      {
        subst md_len.
        simpl in H16.
        unfold Int.ltu in H16.
        destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
        assumption.
        rewrite zlt_false in H16;[ inversion H16|].
        change (Int.unsigned (Int.repr 32)) with 32.
        rewrite (Int.unsigned_repr (out_len - done)); try omega.
      }
      forward.
      subst md_len.
      entailer!.
      rewrite Z.min_l; [reflexivity | omega].
    }
    {
      (* md_len >= left *)
      assert (Hmin: 32 >= out_len - done).
      {
        subst md_len.
        simpl in H16.
        unfold Int.ltu in H16.
        destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
        rewrite zlt_true in H16;[ inversion H16|].
        change (Int.unsigned (Int.repr 32)) with 32.
        rewrite (Int.unsigned_repr (out_len - done)); try omega.
        assumption.
      }
      forward.
      subst md_len.
      entailer!.
      rewrite Z.min_r; [reflexivity | omega].
    }
    forward.

    (* mbedtls_md_hmac_reset( &ctx->md_ctx ); *)
    assert_PROP (field_compatible (Tarray tuchar 32 noattr) 
          []
          (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)) by entailer!.
    forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx', key0, kv).
    {
      entailer!.
    }

    Intros vret; subst vret.

    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    assert (HZlength_V: Zlength (fst
              (HMAC_DRBG_generate_helper_Z HMAC256
                 (hmac256drbgabs_key
                    (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                       prediction_resistance0 reseed_interval0))
                 after_update_value done)) = 32).
    {
      apply HMAC_DRBG_generate_helper_Z_Zlength_fst; auto; try omega.
      apply hmac_common_lemmas.HMAC_Zlength.
    }
    forward_call (key0, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx', field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, @nil Z, (fst (HMAC_DRBG_generate_helper_Z HMAC256
                    (hmac256drbgabs_key
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0))
                    after_update_value done)), kv).
    {
      entailer!.
      rename H22 into HZlength.
      do 2 rewrite Zlength_map in HZlength.
      rewrite HZlength.
      reflexivity.
    }
    {
      rewrite HZlength_V.
      cancel.
    }
    {
      rewrite HZlength_V.
      change Int.max_unsigned with 4294967295.
      change (two_power_pos 61) with 2305843009213693952.
      repeat split; try omega.
      apply HMAC_DRBG_generate_helper_Z_isbyteZ_fst; auto; try omega.
      apply hmac_common_lemmas.isbyte_hmac.
    }

    Intros vret; subst vret.
    rewrite app_nil_l.

    replace_SEP 2 (memory_block Tsh 32 (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)).
    {
      entailer!.
      simpl in HZlength_V.
      unfold hmac256drbgabs_value.
      rewrite HZlength_V.
      apply data_at_memory_block.
    }

    (* mbedtls_md_hmac_finish( &ctx->md_ctx, ctx->V ); *)
    forward_call ((fst
               (HMAC_DRBG_generate_helper_Z HMAC256
                  (hmac256drbgabs_key
                     (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                        prediction_resistance0 reseed_interval0))
                  after_update_value done)), key0, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] ctx, md_ctx', field_address t_struct_hmac256drbg_context_st [StructField _V] ctx, Tsh, kv).
    {
      entailer!.
    }
    Intros vret; subst vret.
    assert_PROP (field_compatible (tarray tuchar out_len) [] output) as Hfield_compat_output by entailer!.
    replace_SEP 5 (
                  data_at Tsh (tarray tuchar done) (map Vint
           (map Int.repr
              (sublist 0 done
                 (snd
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))))) output *
                  data_at Tsh (tarray tuchar (out_len - done)) (list_repeat (Z.to_nat (out_len - done)) Vundef) (offset_val (Int.repr done) output)
    ).
    {
      entailer!.
      apply derives_refl'.

      assert (HZlength1: Zlength (map Vint
        (map Int.repr
           (sublist 0 (n * 32)%Z
              (snd
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0
                    (hmac256drbgabs_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)) (n * 32)%Z))))) = (n * 32)%Z).
      {
        do 2 rewrite Zlength_map.
        rewrite Zlength_sublist; [omega|omega|].
        rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; auto; try omega.
        apply hmac_common_lemmas.HMAC_Zlength.
        exists n; reflexivity.
      }
      
      apply data_at_complete_split; try rewrite HZlength1; try rewrite Zlength_list_repeat; auto; try omega.
      replace ((n * 32)%Z + (out_len - (n * 32)%Z)) with out_len by omega.
      assumption.
    }
    normalize.
    
    remember (offset_val (Int.repr done) output) as done_output.
    remember (Z.min 32 (out_len - done)) as use_len.
    assert_PROP (field_compatible (tarray tuchar (out_len - done)) [] done_output) as Hfield_compat_done_output.
    {
      clear Heqdone_output Hmultiple.
      entailer!.
      rewrite H23 (*Zlength = done *) in H25 (*field compatible *); apply H25.
    }
    replace_SEP 1 (
                  data_at Tsh (tarray tuchar use_len) (list_repeat (Z.to_nat use_len) Vundef) done_output *
                  data_at Tsh (tarray tuchar (out_len - done - use_len)) (list_repeat (Z.to_nat (out_len - done - use_len)) Vundef) (offset_val (Int.repr use_len) done_output)
    ).
    {
      clear Hmultiple Heqdone_output.
      entailer!.
      apply derives_refl'.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_list_repeat; auto; try omega.
        replace (32 + (out_len - done - 32)) with (out_len - done) by omega; assumption.
        rewrite list_repeat_app.
        rewrite <- Z2Nat.inj_add; try omega.
        replace (32 + (out_len - done - 32)) with (out_len - done) by omega; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_list_repeat; auto; try omega.
        replace (out_len - done + (out_len - done - (out_len - done))) with (out_len - done) by omega; assumption.
        replace (out_len - done - (out_len - done)) with 0 by omega; simpl; rewrite app_nil_r; reflexivity.
      }
    }
    normalize.

    replace_SEP 0 (memory_block Tsh use_len done_output).
    {
      clear Hmultiple.
      entailer!.
      eapply derives_trans; [apply data_at_memory_block|].
      replace (sizeof cenv_cs (tarray tuchar (Z.min 32 (out_len - done)))) with (Z.min 32 (out_len - done)).
      apply derives_refl.
      simpl.
      destruct (Z.min_dec 32 (out_len - done));
      rewrite Zmax0r; omega.
    }
    replace_SEP 6 (data_at Tsh (tarray tuchar use_len) (sublist 0 use_len (map Vint (map Int.repr (HMAC256
                 (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))
                 key0)))) (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx) *
                   data_at Tsh (tarray tuchar (32 - use_len)) (sublist use_len 32 (map Vint (map Int.repr (HMAC256
                 (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))
                 key0)))) (offset_val (Int.repr use_len) (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx))
    ).
    {
      clear Hmultiple.
      entailer!.
      apply derives_refl'.
      rewrite hmac_common_lemmas.HMAC_Zlength.
      remember (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0
                    (hmac256drbgabs_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)) done)) as V0'; clear HeqV0'.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        rewrite sublist_nil.
        rewrite app_nil_r.
        symmetry; apply sublist_same.
        reflexivity.
        repeat rewrite Zlength_map; rewrite hmac_common_lemmas.HMAC_Zlength; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (out_len - done - 0 + (32 - (out_len - done))) with 32 by omega; auto.
        rewrite sublist_rejoin; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
        rewrite sublist_same; try reflexivity; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
      }
    }
    (* memcpy( out, ctx->V, use_len ); *)
    forward_call ((Tsh, Tsh), done_output, (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx), use_len, sublist 0 use_len (map Int.repr
              (HMAC256
                 (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256
                       (hmac256drbgabs_key
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) after_update_value done))
                 key0))).
    {
      replace (map Vint
            (sublist 0 use_len
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256
                           (hmac256drbgabs_key
                              (HMAC256DRBGabs key0 V0 reseed_counter0
                                 entropy_len0 prediction_resistance0
                                 reseed_interval0)) after_update_value done))
                     key0)))) with (
            sublist 0 use_len
            (map Vint 
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256
                           (hmac256drbgabs_key
                              (HMAC256DRBGabs key0 V0 reseed_counter0
                                 entropy_len0 prediction_resistance0
                                 reseed_interval0)) after_update_value done))
                     key0)))).
      change (@data_at CompSpecs (fst (Tsh, Tsh)) (tarray tuchar use_len)
         (sublist 0 use_len
            (map Vint
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256
                           (hmac256drbgabs_key
                              (HMAC256DRBGabs key0 V0 reseed_counter0
                                 entropy_len0 prediction_resistance0
                                 reseed_interval0)) after_update_value done))
                     key0))))
         (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)) with
      (@data_at hmac_drbg_compspecs.CompSpecs (fst (Tsh, Tsh)) (tarray tuchar use_len)
         (sublist 0 use_len
            (map Vint
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256
                           (hmac256drbgabs_key
                              (HMAC256DRBGabs key0 V0 reseed_counter0
                                 entropy_len0 prediction_resistance0
                                 reseed_interval0)) after_update_value done))
                     key0))))
         (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)).
      entailer!.
      apply sublist_map.
    }
    {
      change (Int.max_unsigned) with 4294967295.
      repeat split; auto;
      subst use_len; destruct (Z.min_dec 32 (out_len - done)); omega.
    }

    Intros vret; subst vret.

    simpl.
    gather_SEP 0 7.
    replace_SEP 0 (data_at Tsh (tarray tuchar 32) (map Vint
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256 key0
                           after_update_value done)) key0))) (field_address t_struct_hmac256drbg_context_st [StructField _V] ctx)).
    {
      clear Hmultiple.
      entailer!.
      apply derives_refl'.
      rewrite <- sublist_map.
      remember (fst
                    (HMAC_DRBG_generate_helper_Z HMAC256 key0
                       (hmac256drbgabs_value
                          (HMAC256DRBGabs key0 V0 reseed_counter0
                             entropy_len0 prediction_resistance0
                             reseed_interval0)) (done))) as V0'; clear HeqV0'.
      symmetry.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        rewrite sublist_nil.
        rewrite sublist_same; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
        remember (map Vint (map Int.repr (HMAC256 V0' key0))) as data.
        apply data_at_complete_split; subst data; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        rewrite app_nil_r; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        remember (sublist 0 (out_len - done) (map Vint (map Int.repr (HMAC256 V0' key0)))) as data_left.
        remember (sublist (out_len - done) 32
        (map Vint (map Int.repr (HMAC256 V0' key0)))) as data_right.
        apply data_at_complete_split; subst data_left data_right; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (out_len - done - 0 + (32 - (out_len - done))) with 32 by omega; auto.
        rewrite sublist_rejoin; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
        rewrite sublist_same; try reflexivity; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
      }
    }

    gather_SEP 1 2.
    replace_SEP 0 (data_at Tsh (tarray tuchar (out_len - done)) ((map Vint
           (sublist 0 use_len
              (map Int.repr
                 (HMAC256
                    (fst
                       (HMAC_DRBG_generate_helper_Z HMAC256 key0
                                                    after_update_value done)) key0)))) ++ (list_repeat (Z.to_nat (out_len - done - use_len)) Vundef))
                                       done_output).
    {
      clear Heqdone_output Hmultiple.
      entailer!.
      apply derives_refl'.
      rewrite Zmin_spec.
      symmetry.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; change ((fix map (l : list int) : list val :=
               match l with
               | [] => []
               | a :: t => Vint a :: map t
               end)
              (sublist 0 32
                 (map Int.repr
                    (HMAC256
                       (fst
                          (HMAC_DRBG_generate_helper_Z HMAC256 key0
                             (hmac256drbgabs_value
                                (HMAC256DRBGabs key0 V0 reseed_counter0
                                   entropy_len0 prediction_resistance0
                                   reseed_interval0)) done)) key0)))) with (map Vint
              (sublist 0 32
                 (map Int.repr
                    (HMAC256
                       (fst
                          (HMAC_DRBG_generate_helper_Z HMAC256 key0
                             (hmac256drbgabs_value
                                (HMAC256DRBGabs key0 V0 reseed_counter0
                                   entropy_len0 prediction_resistance0
                                   reseed_interval0)) done)) key0)))); repeat rewrite Zlength_list_repeat; auto; try omega;
        rewrite Zlength_map; rewrite Zlength_sublist; try rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (32 - 0 + (out_len - done - 32)) with (out_len - done) by omega.
        assumption.
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; change ((fix map (l : list int) : list val :=
               match l with
               | [] => []
               | a :: t => Vint a :: map t
               end)
              (sublist 0 (out_len - done)
                 (map Int.repr
                    (HMAC256
                       (fst
                          (HMAC_DRBG_generate_helper_Z HMAC256 key0
                             (hmac256drbgabs_value
                                (HMAC256DRBGabs key0 V0 reseed_counter0
                                   entropy_len0 prediction_resistance0
                                   reseed_interval0)) done)) key0)))) with (map Vint
              (sublist 0 (out_len - done)
                 (map Int.repr
                    (HMAC256
                       (fst
                          (HMAC_DRBG_generate_helper_Z HMAC256 key0
                             (hmac256drbgabs_value
                                (HMAC256DRBGabs key0 V0 reseed_counter0
                                   entropy_len0 prediction_resistance0
                                   reseed_interval0)) done)) key0)))); repeat rewrite Zlength_list_repeat; auto; try omega;
        rewrite Zlength_map; rewrite Zlength_sublist; try rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (out_len - done - 0 + (out_len - done - (out_len - done))) with (out_len - done) by omega.
        assumption.
      }
    }

    gather_SEP 2 0.
    replace_SEP 0 (
                  data_at Tsh (tarray tuchar out_len) ((map Vint
           (map Int.repr
              (sublist 0 done
                 (snd
                    (HMAC_DRBG_generate_helper_Z HMAC256 key0
                       after_update_value done))))) ++ (map Vint
            (sublist 0 use_len
               (map Int.repr
                  (HMAC256
                     (fst
                        (HMAC_DRBG_generate_helper_Z HMAC256 key0
                           after_update_value done)) key0))) ++
          list_repeat (Z.to_nat (out_len - done - use_len)) Vundef)) output
    ).
    {
      entailer!.
      apply derives_refl'.
      symmetry.
      assert (HZlength1: Zlength (
              (snd
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0
                    (hmac256drbgabs_value
                       (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
                          prediction_resistance0 reseed_interval0)) (n * 32)%Z))) = (n * 32)%Z).
      {
        rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; auto; try omega.
        apply hmac_common_lemmas.HMAC_Zlength.
        exists n; reflexivity.
      }
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption];
      apply data_at_complete_split; repeat rewrite Zlength_app; repeat rewrite Zlength_map; try rewrite HZlength1; repeat rewrite Zlength_list_repeat; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
      replace ((n * 32)%Z - 0 + (32 - 0 + (out_len - (n * 32)%Z - 32))) with out_len by omega;
      assumption.
      replace ((n * 32)%Z - 0 + (out_len - (n * 32)%Z - 0 + (out_len - (n * 32)%Z - (out_len - (n * 32)%Z)))) with out_len by omega;
      assumption.
    }

    (* out += use_len; *)
    forward.

    (* left -= use_len; *)
    forward.

    
    Exists (done + use_len).
    unfold hmac256drbgabs_common_mpreds; normalize.

    unfold_data_at 4%nat.
    rewrite (field_at_data_at _ _ [StructField _md_ctx]);
    rewrite (field_at_data_at _ _ [StructField _V]).
    
    unfold md_full.
    
    thaw FR1.
    thaw FR_unused_struct_fields.
    subst.

    entailer!.
    {
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; repeat split; try omega.
      left; exists (n + 1); omega.
      replace (out_len - ((n * 32)%Z + 32)) with (out_len - (n * 32)%Z - 32) by omega;
      reflexivity.
      right; omega.
      replace (out_len - ((n * 32)%Z + (out_len - (n * 32)%Z))) with (out_len - (n * 32)%Z - (out_len - (n * 32)%Z)) by omega;
      reflexivity.
    }

    unfold md_full.
    replace (HMAC256 (fst (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z))
              key0) with (fst
                  (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                     ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z)))).
    cancel.
    apply derives_refl'.
    
    rewrite app_assoc.
    replace (map Vint
        (map Int.repr
           (sublist 0 (n * 32)%Z
              (snd (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z)))) ++
      map Vint
        (sublist 0 (Z.min 32 (out_len - (n * 32)%Z))
           (map Int.repr
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                    ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))))) with (map Vint
        (map Int.repr
           (sublist 0 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))
              (snd
                 (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                    ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))))).
    replace (out_len - (n * 32)%Z - Z.min 32 (out_len - (n * 32)%Z)) with (out_len - ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))) by omega.
    reflexivity.
    rewrite <- map_app.
    rewrite sublist_map.
    rewrite <- map_app.
    replace (sublist 0 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))
           (snd
              (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))) with (sublist 0 (n * 32)%Z
           (snd (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z)) ++
         sublist 0 (Z.min 32 (out_len - (n * 32)%Z))
           (fst
              (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))).
    reflexivity.
    replace (snd
              (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z)))) with (snd (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z) ++ fst
              (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0
                 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z)))).
    {
      apply while_loop_post_sublist_app; auto.
    }
    {
      apply while_loop_post_incremental_snd; auto.
      intros contra; rewrite contra in HRE; omega.
    }
    {
      apply while_loop_post_incremental_fst; auto.
      idtac.
      intros contra; rewrite contra in HRE; omega.
    }
  }

  assert (Hdone: done = out_len).
  {
    clear - HRE H15 Hout_len.
    assert (Hdiff: out_len - done = 0).
    {
      unfold Int.eq in HRE.
      unfold zeq in HRE.
      destruct (Z.eq_dec (Int.unsigned (Int.repr (out_len - done)))
                (Int.unsigned (Int.repr 0))).
      rewrite (Int.unsigned_repr (out_len - done)) in e.
      rewrite e; reflexivity.
      change (Int.max_unsigned) with 4294967295; omega.
      inversion HRE.
    }
    omega.
  }
  rewrite Hdone.
  replace (out_len - out_len) with 0 by omega.
  change (list_repeat (Z.to_nat 0) Vundef) with (@nil val).
  rewrite app_nil_r.
  unfold hmac256drbgabs_common_mpreds.
  normalize.

  assert_PROP (isptr additional) as Hisptr_add by entailer!.
  assert_PROP (field_compatible (tarray tuchar add_len) [] additional) as Hfield_add by entailer!.
  replace_SEP 4 (mpred_passed_to_function (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional) should_reseed * mpred_passed_to_frame (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional) should_reseed).
  {
    clear Heqshould_reseed.
    entailer!.
    apply derives_refl'.
    apply mpred_cond_correct.
  }

  (* mbedtls_hmac_drbg_update( ctx, additional, add_len ); *)
  forward_call (if should_reseed then @nil Z else contents, additional, after_reseed_add_len, ctx, (hmac256drbgabs_to_state
         (hmac256drbgabs_update_value after_update_state_abs
            (fst
               (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                  after_update_value out_len))) initial_state), (hmac256drbgabs_update_value after_update_state_abs
         (fst
            (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
               after_update_value out_len))), kv, info_contents).
  {
    assert (Stream after_reseed_s *
   mpred_passed_to_frame
     (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional) should_reseed *
   data_at Tsh (tarray tuchar out_len)
     (map Vint
        (map Int.repr
           (sublist 0 out_len
              (snd
                 (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                    after_update_value out_len))))) output |-- fold_right sepcon emp Frame)
    by cancel.
    subst after_reseed_add_len.
    assert (Hadd_0: (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        additional) = (data_at Tsh (tarray tuchar 0) []
        additional) * (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents))
        (offset_val (Int.repr 0) additional))).
    {
      apply data_at_complete_split; repeat rewrite Zlength_map; try rewrite H2; auto; try omega.
      change (Zlength (@nil Z) + Zlength contents) with (Zlength contents); rewrite <- H2; assumption.
    }
    rewrite Hadd_0.
    subst Frame.
    unfold mpred_passed_to_function, mpred_passed_to_frame, fold_right; destruct should_reseed; entailer!.
    eapply derives_trans.
    apply data_at_memory_block.
    simpl.
    destruct additional; try solve [inversion Hisptr_add].
    apply derives_refl'.
    apply memory_block_zero_Vptr.
  }
  {
    subst after_reseed_add_len; split.
    destruct should_reseed; omega.
    replace (hmac256drbgabs_value
        (hmac256drbgabs_update_value after_update_state_abs
           (fst
              (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                 after_update_value out_len)))) with (fst
              (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                 after_update_value out_len)) by (
      destruct after_update_state_abs; unfold hmac256drbgabs_value; unfold hmac256drbgabs_update_value; reflexivity).
    repeat split; try now (destruct should_reseed; auto).
    {
      rewrite HMAC_DRBG_generate_helper_Z_Zlength_fst; auto; try omega.
      apply hmac_common_lemmas.HMAC_Zlength.
    }
    {
      apply HMAC_DRBG_generate_helper_Z_isbyteZ_fst; auto; try omega.
      apply hmac_common_lemmas.isbyte_hmac.
    }
  }

  gather_SEP 1 4.
  replace_SEP 0 (data_at Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional).
  {
    clear Heqshould_reseed.
    entailer!.
    rewrite mpred_cond_correct with (cond:=should_reseed).
    cancel.
    unfold mpred_passed_to_function.
    destruct should_reseed; [| apply derives_refl].
    eapply derives_trans.
    apply data_at_memory_block.
    simpl.
    destruct additional'; try solve [inversion Hisptr_add].
    apply derives_refl';
    apply memory_block_zero_Vptr.
  }

  (* ctx->reseed_counter++; *)
  remember (hmac256drbgabs_hmac_drbg_update
           (hmac256drbgabs_update_value after_update_state_abs
              (fst
                 (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                    after_update_value out_len)))
           (if should_reseed then [] else contents)) as semi_final_state_abs.
  replace_SEP 1 (hmac256drbgabs_common_mpreds semi_final_state_abs
        initial_state ctx
        info_contents).
  {
    destruct semi_final_state_abs.
    destruct (hmac256drbgabs_update_value after_update_state_abs
            (fst
               (HMAC_DRBG_generate_helper_Z HMAC256 after_update_key
                  after_update_value out_len))).
    unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state.
    entailer!.
    entailer!.
  }
  
  unfold hmac256drbgabs_common_mpreds. normalize.
  forward.
  idtac.
  {
    (* type checking *)
    subst initial_state initial_state_abs.
    entailer!.
    unfold hmac256drbgabs_to_state, hmac256drbgabs_update_value, hmac256drbgabs_hmac_drbg_update, hmac256drbgabs_reseed, hmac256drbgabs_value, hmac256drbgabs_key, HMAC256_DRBG_update, HMAC_DRBG_update. 
    destruct (mbedtls_HMAC256_DRBG_reseed_function s
                               (HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval) contents) as [d s' | e s'];
      try destruct d as [[[[V' key'] reseed_counter'] security_strength'] prediction_resistance'];
      destruct (prediction_resistance || (reseed_counter >? reseed_interval))%bool; destruct contents; auto; unfold is_int; constructor.
  }

  forward.

  (* return 0; *)
  forward.
  
  Exists Vzero.
  
  unfold hmac256drbgabs_generate.

  clear Heqnon_empty_additional.

  rewrite generate_correct with (should_reseed:=(prediction_resistance
                                         || (reseed_counter >?
                                             reseed_interval))%bool) (non_empty_additional:=if (prediction_resistance
                               || (reseed_counter >? reseed_interval))%bool
                           then false
                           else
                            match contents with
                            | [] => false
                            | _ :: _ => true
                            end); auto.
  remember (hmac256drbgabs_hmac_drbg_update
               (hmac256drbgabs_update_value
                  (if if (prediction_resistance
                          || (reseed_counter >? reseed_interval))%bool
                      then false
                      else
                       match contents with
                       | [] => false
                       | _ :: _ => true
                       end
                   then
                    hmac256drbgabs_hmac_drbg_update
                      (HMAC256DRBGabs key V reseed_counter entropy_len
                         prediction_resistance reseed_interval) contents
                   else
                    if (prediction_resistance
                        || (reseed_counter >? reseed_interval))%bool
                    then
                     hmac256drbgabs_reseed
                       (HMAC256DRBGabs key V reseed_counter entropy_len
                          prediction_resistance reseed_interval) s contents
                    else
                     HMAC256DRBGabs key V reseed_counter entropy_len
                       prediction_resistance reseed_interval)
                  (fst
                     (HMAC_DRBG_generate_helper_Z HMAC256
                        (hmac256drbgabs_key
                           (if if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then false
                               else
                                match contents with
                                | [] => false
                                | _ :: _ => true
                                end
                            then
                             hmac256drbgabs_hmac_drbg_update
                               (HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval) contents
                            else
                             if (prediction_resistance
                                 || (reseed_counter >? reseed_interval))%bool
                             then
                              hmac256drbgabs_reseed
                                (HMAC256DRBGabs key V reseed_counter
                                   entropy_len prediction_resistance
                                   reseed_interval) s contents
                             else
                              HMAC256DRBGabs key V reseed_counter entropy_len
                                prediction_resistance reseed_interval))
                        (hmac256drbgabs_value
                           (if if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then false
                               else
                                match contents with
                                | [] => false
                                | _ :: _ => true
                                end
                            then
                             hmac256drbgabs_hmac_drbg_update
                               (HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval) contents
                            else
                             if (prediction_resistance
                                 || (reseed_counter >? reseed_interval))%bool
                             then
                              hmac256drbgabs_reseed
                                (HMAC256DRBGabs key V reseed_counter
                                   entropy_len prediction_resistance
                                   reseed_interval) s contents
                             else
                              HMAC256DRBGabs key V reseed_counter entropy_len
                                prediction_resistance reseed_interval)) done))) (if (prediction_resistance
                              || (reseed_counter >? reseed_interval))%bool
                          then []
                          else contents)) as semi_final_state_abs.
  remember (sublist 0 done
                    (snd
                       (HMAC_DRBG_generate_helper_Z HMAC256
                          (hmac256drbgabs_key
                             (if if (prediction_resistance
                                     || (reseed_counter >? reseed_interval))%bool
                                 then false
                                 else
                                  match contents with
                                  | [] => false
                                  | _ :: _ => true
                                  end
                              then
                               hmac256drbgabs_hmac_drbg_update
                                 (HMAC256DRBGabs key V reseed_counter
                                    entropy_len prediction_resistance
                                    reseed_interval) contents
                              else
                               if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then
                                hmac256drbgabs_reseed
                                  (HMAC256DRBGabs key V reseed_counter
                                     entropy_len prediction_resistance
                                     reseed_interval) s contents
                               else
                                HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval))
                          (hmac256drbgabs_value
                             (if if (prediction_resistance
                                     || (reseed_counter >? reseed_interval))%bool
                                 then false
                                 else
                                  match contents with
                                  | [] => false
                                  | _ :: _ => true
                                  end
                              then
                               hmac256drbgabs_hmac_drbg_update
                                 (HMAC256DRBGabs key V reseed_counter
                                    entropy_len prediction_resistance
                                    reseed_interval) contents
                              else
                               if (prediction_resistance
                                   || (reseed_counter >? reseed_interval))%bool
                               then
                                hmac256drbgabs_reseed
                                  (HMAC256DRBGabs key V reseed_counter
                                     entropy_len prediction_resistance
                                     reseed_interval) s contents
                               else
                                HMAC256DRBGabs key V reseed_counter
                                  entropy_len prediction_resistance
                                  reseed_interval)) done))) as generate_output_bytes.
  destruct semi_final_state_abs.
  pose proof (Heqsemi_final_state_abs) as Hsemi_final_metadata.
  apply metadata_preserved in Hsemi_final_metadata.
  pose proof (Heqsemi_final_state_abs) as Hsemi_final_reseed_counter.
  apply reseed_counter_values in Hsemi_final_reseed_counter.
  clear Heqgenerate_output_bytes Heqsemi_final_state_abs.
  unfold return_value_relate_result.
  unfold get_stream_result.
  unfold hmac256drbgabs_common_mpreds, hmac256drbgabs_to_state_handle, hmac256drbgabs_increment_reseed_counter.
  unfold hmac256drbgabs_to_state, hmac256drbg_relate.
  unfold hmac256drbgstate_md_info_pointer.
  entailer!.
  simpl in *.
  destruct Hsemi_final_metadata as [Hentropy_len0 [Hpr0 Hreseed_interval0]].
  subst entropy_len0.
  subst reseed_interval0.
  entailer!.
Qed.*)