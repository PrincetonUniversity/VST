Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import VST.floyd.sublist.

Require Import sha.HMAC256_functional_prog.
Require Import sha.general_lemmas.
Require Import sha.spec_sha.

Require Import hmacdrbg.entropy.
Require Import hmacdrbg.entropy_lemmas.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.HMAC_DRBG_pure_lemmas.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require hmacdrbg.verif_hmac_drbg_WF.
Require Import hmacdrbg.verif_hmac_drbg_generate_common.

Opaque HMAC256.
Opaque hmac256drbgabs_generate.
Opaque HMAC256_DRBG_generate_function.
Opaque mbedtls_HMAC256_DRBG_generate_function.
(*
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

(*
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
*)(*
Require Import hmacdrbg.verif_gen_c1.
Declare Module M :Continuation1.
*)

(*
Definition postReseedCtx s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents mc1 mc2 mc3 b i: mpred :=
  match mbedtls_HMAC256_DRBG_reseed_function s
               (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
                  reseed_interval) (contents_with_add additional (Zlength contents) contents)
  with ENTROPY.success (RSVal, RSKey, aa, bb, cc) s0 => 
       data_at Tsh t_struct_hmac256drbg_context_st
           (mc1, (mc2, mc3),
           (map Vint (map Int.repr RSVal),
           (Vint (Int.repr aa),
           (Vint (Int.repr entropy_len), (Val.of_bool cc, Vint (Int.repr reseed_interval))))))
           (Vptr b i)
   | _ => FF
  end.
*)

Definition postReseedCtx (CTX:reptype t_struct_hmac256drbg_context_st) s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents (mc:mdstate): Prop :=
  match mbedtls_HMAC256_DRBG_reseed_function s
               (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
                  reseed_interval) (contents_with_add additional (Zlength contents) contents)
  with ENTROPY.success (RSVal, RSKey, aa, bb, cc) s0 => CTX =
           (mc,
           (map Vint (map Int.repr RSVal),
           (Vint (Int.repr aa),
           (Vint (Int.repr entropy_len), (Val.of_bool cc, Vint (Int.repr reseed_interval))))))
   | _ => False
  end.

Definition postReseedKey s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents mc1 mc2 mc3: mpred :=
  match mbedtls_HMAC256_DRBG_reseed_function s
               (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
                  reseed_interval) (contents_with_add additional (Zlength contents) contents)
  with ENTROPY.success (RSVal, RSKey, aa, bb, cc) s0 => md_full RSKey (mc1, (mc2, mc3))
  | _ => FF
  end.

Definition postReseedStream s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents: mpred :=
  match mbedtls_HMAC256_DRBG_reseed_function s
               (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
                  reseed_interval) (contents_with_add additional (Zlength contents) contents)
  with ENTROPY.success (RSVal, RSKey, aa, bb, cc) s0 => Stream s0
  | _ => FF
  end.

Definition mkCTX0 (should_reseed:bool) (initial_state:reptype t_struct_hmac256drbg_context_st) s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents mc p: mpred :=
  EX myctx:reptype t_struct_hmac256drbg_context_st%type, 
           (!!(if should_reseed 
                then postReseedCtx myctx s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents mc
                else myctx = initial_state)) &&
             data_at Tsh t_struct_hmac256drbg_context_st myctx p.
(*alternative definitions that don't help
Definition myMpred0 (should_reseed:bool) initial_state s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents mc p: mpred :=
  EX myctx:(val * (val * val) * (list val * (val * (val * (val * val)))))%type, 
           (!!(if should_reseed 
                then postReseedCtx myctx s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents mc
                else myctx = initial_state)) &&
             data_at Tsh t_struct_hmac256drbg_context_st myctx p.
Definition myMpred1 (should_reseed:bool) initial_state s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents mc p: mpred :=
  EX q1:val, EX q2:val, EX q3:val, EX q4:list val, EX q5:val, EX q6:val, EX q7:val, EX q8:val,
           (!!(if should_reseed 
                then postReseedCtx (q1, (q2, q3), (q4, (q5, (q6, (q7, q8))))) s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents mc
                else (q1, (q2, q3), (q4, (q5, (q6, (q7, q8))))) = initial_state)) &&
             data_at Tsh t_struct_hmac256drbg_context_st (q1, (q2, q3), (q4, (q5, (q6, (q7, q8))))) p.
*)

Definition mkCTX1 (should_reseed:bool) (ctx ctx1:reptype t_struct_hmac256drbg_context_st) 
            s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents mc: Prop :=
     if should_reseed 
     then match mbedtls_HMAC256_DRBG_reseed_function s
        (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval)
        (contents_with_add additional (Zlength contents) contents)
       with
      | ENTROPY.success (RSVal, _, aa, _, cc) _ =>
           ctx1 = (mc,
                  (map Vint (map Int.repr RSVal),
                  (Vint (Int.repr aa),
                  (Vint (Int.repr entropy_len), (Val.of_bool cc, Vint (Int.repr reseed_interval))))))
      | ENTROPY.error _ _ => False
       end
     else ctx1 = ctx.

Definition mkKEY1 (should_reseed:bool) s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents key1 : Prop:=
  if should_reseed
  then match mbedtls_HMAC256_DRBG_reseed_function s
        (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval)
        (contents_with_add additional (Zlength contents) contents)
    with
    | ENTROPY.success (_, RSKey, _, _, _) _ => key1 = RSKey
    | ENTROPY.error _ _ => False
    end
  else key1=key.

Definition mkSTREAM1 (should_reseed:bool) s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents stream1 : Prop :=
  if should_reseed
          then
           match
             mbedtls_HMAC256_DRBG_reseed_function s
               (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
                  reseed_interval)
               (contents_with_add additional (Zlength contents) contents)
           with
           | ENTROPY.success (_, _, _, _, _) s0 => stream1 = s0
           | ENTROPY.error _ _ => False
           end
          else stream1 = s.

(* IT'S PATHETIC THAT WE NEED TO INTRDUCE ctx2' AND a predicate CTXeq to wotk around FLOYD'S typechecker!!*)
Definition CTXeq (c:reptype t_struct_hmac256drbg_context_st)
                 (c':(val * (val * val) * (list val * (val * (val * (val * val)))))%type) : Prop := c'=c.
Definition is_multiple (multiple base: Z) : Prop := exists i, multiple = (i * base)%Z.
*)
Lemma entailment1: forall (contents : list byte) (additional: val) (sha: share) (output : val) (sho: share)
  (out_len : Z) (b : block) (i : ptrofs) (shc: share) (mc1 mc2 mc3 : val) (key V : list byte)
  (reseed_counter entropy_len : Z) (prediction_resistance : bool)
  (reseed_interval : Z) (gv : globals) (info_contents : md_info_state)
  (s : ENTROPY.stream)
  (initial_state_abs := HMAC256DRBGabs key V reseed_counter entropy_len
                       prediction_resistance reseed_interval : hmac256drbgabs)
(*(RI : reseed_interval = 10000)*)
  (initial_state := (mc1, (mc2, mc3),
                 (map Vubyte V,
                 (Vint (Int.repr reseed_counter),
                 (Vint (Int.repr entropy_len),
                 (Val.of_bool prediction_resistance,
                 Vint (Int.repr reseed_interval))))))
              : mdstate * (list val * (val * (val * (val * val)))))
  (Hout_lenb : (out_len >? 1024) = false)
  (ZLa : (Zlength (contents_with_add additional (Zlength contents) contents) >? 256) =
      false)
  (Hshould_reseed : (prediction_resistance || (reseed_counter >? reseed_interval))%bool =
                 true)
(*  (F : (0 >? 256) = false)*)
  (F32 : (32 >? 32) = false)
  (return_value : int)
  (Hrv : negb (Int.eq return_value (Int.repr 0)) = true)
  (Hadd_lenb : (Zlength contents >? 256) = false)
  (Hadd_len: 0 <= Zlength contents <= 256)
  (EL1: entropy_len + Zlength contents <= 384)
   (*ZLc' : Zlength contents' = 0 \/ Zlength contents' = Zlength contents*)
(*  (EL: entropy_len = 32)*),
reseedPOST (Vint return_value) contents additional sha (Zlength contents) s
  initial_state_abs (Vptr b i) shc info_contents gv initial_state *
data_at_ sho (tarray tuchar out_len) output
|-- !! return_value_relate_result
         (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
            (contents_with_add additional (Zlength contents) contents))
         (Vint return_value) &&
    (match
       mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
         (contents_with_add additional (Zlength contents) contents)
     with
     | ENTROPY.success (bytes, _) _ =>
         data_at sho (tarray tuchar out_len) (map Vubyte bytes)
           output
     | ENTROPY.error _ _ => data_at_ sho (tarray tuchar out_len) output
     end *
     hmac256drbgabs_common_mpreds shc
       (hmac256drbgabs_generate initial_state_abs s out_len
          (contents_with_add additional (Zlength contents) contents))
       initial_state (Vptr b i) info_contents *
     da_emp sha (tarray tuchar (Zlength contents))
       (map Vubyte contents) additional *
     Stream
       (get_stream_result
          (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
             (contents_with_add additional (Zlength contents) contents))) *
     K_vector gv).
Proof. intros. (* unfold hmac256drbgabs_common_mpreds, hmac256drbg_relate; normalize.*)
 unfold reseedPOST. apply Zgt_is_gt_bool_f in Hadd_lenb.
 remember ((zlt 256 (Zlength contents)
   || zlt 384 (hmac256drbgabs_entropy_len initial_state_abs + Zlength contents))%bool) as d.
 destruct (zlt 256 (Zlength contents)); simpl in Heqd. omega. clear g.
 destruct (zlt 384 (entropy_len + Zlength contents)); simpl in Heqd; subst d. omega.
 normalize.
      remember (mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs
        (contents_with_add additional (Zlength contents) contents)) as MRS.
      unfold return_value_relate_result in (*H8*)H. 
      destruct MRS. 
      { exfalso. (*clear - H8 Hrv. inv H8.*) inv H. simpl in Hrv; discriminate. }
      unfold hmac256drbgabs_common_mpreds.
      remember (hmac256drbgabs_reseed initial_state_abs s
        (contents_with_add additional (Zlength contents) contents)) as RS.
      unfold hmac256drbgabs_reseed in HeqRS. rewrite <- HeqMRS in HeqRS.
      assert (HRS: RS = initial_state_abs) by (subst initial_state_abs; apply HeqRS). 
      clear HeqRS; subst RS. 
      remember (hmac256drbgabs_generate initial_state_abs s out_len
                (contents_with_add additional (Zlength contents) contents)) as Gen.
      remember (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
             (contents_with_add additional (Zlength contents) contents)) as MGen.
      Transparent hmac256drbgabs_generate.
      Transparent mbedtls_HMAC256_DRBG_generate_function.
      unfold hmac256drbgabs_generate in HeqGen. rewrite <- HeqMGen in HeqGen. 
      unfold mbedtls_HMAC256_DRBG_generate_function in HeqMGen. subst initial_state_abs.
      simpl in HeqMGen. 
      Transparent HMAC256_DRBG_generate_function. unfold HMAC256_DRBG_generate_function in HeqMGen.
      unfold mbedtls_HMAC256_DRBG_reseed_function in HeqMRS.
      unfold DRBG_generate_function in HeqMGen.
      rewrite Hout_lenb, ZLa, andb_negb_r, F32 in HeqMGen. 
      unfold DRBG_generate_function_helper in HeqMGen. rewrite <- HeqMRS in HeqMGen. subst Gen. simpl. normalize.
      destruct prediction_resistance; simpl in *.
      + rewrite ZLa in *. subst MGen.
        unfold return_value_relate_result. 
        apply andp_right. apply prop_right. repeat split; trivial.
        cancel. simpl. entailer!.
      + (*subst reseed_interval;*)   rewrite Hshould_reseed, ZLa in *.
        destruct (get_entropy 32(*256*) entropy_len entropy_len false s); try discriminate.
        inv HeqMRS. unfold return_value_relate_result; simpl.
        apply andp_right. apply prop_right. repeat split; trivial.
        cancel. entailer!. 
Qed.

Opaque hmac256drbgabs_generate.
Opaque HMAC256_DRBG_generate_function.
Opaque mbedtls_HMAC256_DRBG_generate_function.
Opaque mbedtls_HMAC256_DRBG_reseed_function.

Definition POSTRESEED (IS:reptype t_struct_hmac256drbg_context_st)
   (b:bool) (s:ENTROPY.stream) (mc:mdstate) (K V:list byte) (RC EL:Z) (PR:bool) (RI:Z) (c:list byte)
   (s':ENTROPY.stream) (K':list byte) (ctx':reptype t_struct_hmac256drbg_context_st):Prop :=
if b then 
  exists VV KK aa zz cc ss, 
    mbedtls_HMAC256_DRBG_reseed_function s
         (HMAC256DRBGabs K V RC EL PR RI) c
    = ENTROPY.success (VV, KK, aa, zz, cc) ss 
    /\ s' = ss /\ K'=KK /\
       ctx' = (mc,
            (map Vubyte VV,
            (Vint (Int.repr aa),
            (Vint (Int.repr EL),
            (Val.of_bool cc, Vint (Int.repr RI))))))
else s'=s /\ K'=K /\ ctx'=IS.

Definition POSTUPDATE (b:bool) additional c key V (mc:mdstate) RC EL PR RI ctx1 key1 K' (ctx':reptype t_struct_hmac256drbg_context_st): Prop :=
  if b 
  then (exists (bb : block), exists (ii : ptrofs), exists (UVal : list byte),
        additional = Vptr bb ii /\
        (K', UVal) =
           HMAC256_DRBG_update
             (contents_with_add (Vptr bb ii) (Zlength c) c) key V /\
        ctx' = (mc,
         (map Vubyte UVal,
         (Vint (Int.repr RC),
         (Vint (Int.repr EL),
         (Val.of_bool PR, Vint (Int.repr RI)))))))
  else (ctx' = ctx1 /\ K'=key1). 

Lemma body_hmac_drbg_generate: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_random_with_add hmac_drbg_generate_spec.
Proof.
  start_function. 
  destruct H5 as [Hreseed_interval Hreseed_counter_in_range]. 

  destruct I.
  destruct initial_state as [md_ctx' [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].
  unfold hmac256drbg_relate.
  normalize.
  unfold hmac256drbgstate_md_info_pointer.
  simpl.

  rename info_contents into Info. 
  rename H2 into AddLenC. rename H0 into Houtlen. 
  rename H4 into Hentlen.
  rename H into Haddlen. rename H3 into Hent_len_nonneg.
  simpl in H1, Hent_len_nonneg,  Hentlen, Hreseed_interval, Hreseed_counter_in_range |- *.

  rewrite da_emp_isptrornull. (*needed later*)
  rewrite data_at_isptr with (p:=ctx).
  normalize. 
  set (I := HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval) in *.
  set (initial_state := (md_ctx',
        (map Vubyte V,
        (Vint (Int.repr reseed_counter),
        (Vint (Int.repr entropy_len),
        (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval))))))) in *.

  (* mbedtls_hmac_drbg_context *ctx = p_rng; *)
  forward. 

  (* int left = out_len *)
  forward.

  (* out = output *)
  forward.

  (* prediction_resistance = ctx->prediction_resistance *)
  destruct ctx; try contradiction.  (*subst initial_state.*)
  destruct md_ctx' as [mc1 [mc2 mc3]]. simpl.
  rewrite data_at_isptr with (p:=mc1). normalize.
  freeze [0;1;3; 4;5;6] FR0. 
  Time forward. (*Coq8.5pl2:3secs - and without the freezer it is virtually nonterminating*)
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
  forward.

  (* md_len = mbedtls_md_get_size(info); *)
  forward_call tt.

  (* if( out_len > MBEDTLS_HMAC_DRBG_MAX_REQUEST ) *)
  forward_if (out_len <= 1024).
  {
    (* return( MBEDTLS_ERR_HMAC_DRBG_REQUEST_TOO_BIG ); *)
    forward.

    (* prove post condition of the function *)
    Exists (Vint (Int.repr (-3))). entailer!.
    assert (Hout_len: out_len >? 1024 = true).
    {
      rewrite Z.gtb_ltb.
      apply Z.ltb_lt.
      assumption.
    }
    unfold generatePOST. rewrite Hout_len; simpl. entailer!.
    thaw FR0. cancel.
  }
  {
    forward.
    entailer!. (* thaw FR0. cancel. *)
  }

  Intros. thaw FR0. clear Pctx.
  assert (Hout_len: 0 <= out_len <= 1024) by omega.
  assert (Hout_lenb: out_len >? 1024 = false).
  {
    rewrite Z.gtb_ltb.
    apply Z.ltb_nlt.
    omega.
  }
  clear H.

  freeze [0;1;2;3;4;5;6] FR2.

  (* III. if( add_len > MBEDTLS_HMAC_DRBG_MAX_INPUT ) *)
  forward_if (add_len <= 256).
  {
    (* return( MBEDTLS_ERR_HMAC_DRBG_INPUT_TOO_BIG ); *)
    forward.

    (* prove function post condition *)
    Exists (Vint (Int.repr (-5))). entailer!.
    assert (Hadd_lenb: Zlength contents >? 256 = true).
    {
      rewrite Z.gtb_ltb.
      apply Z.ltb_lt.
      assumption.
    }
    unfold generatePOST. rewrite Hout_lenb, Hadd_lenb; simpl.
    entailer!. 
    thaw FR2. cancel. 
  }
  { 
    (*"empty" branch of III: skip*)
    forward.
    entailer!.
  }
  Intros. 
  assert (Hadd_len: 0 <= add_len <= 256) by omega.
  assert (Hadd_lenb: add_len >? 256 = false).
  {
    rewrite Z.gtb_ltb.
    apply Z.ltb_nlt.
    omega.
  }
  (*  subst add_len. *) clear H. rename H1 into LengthV.
  unfold POSTCONDITION, abbreviate, generatePOST. rewrite Hout_lenb, Hadd_lenb. abbreviate_semax.
  assert (ZLa: Zlength (contents_with_add additional add_len contents) >? 256 = false).
     { unfold contents_with_add. simple_if_tac. subst; trivial. rewrite Zlength_nil; trivial. }

  (*1. (aka VII and IX) Check reseed counter and PR*)
  set (should_reseed := orb prediction_resistance (reseed_counter >? reseed_interval)) in *.
  forward_if (temp _t'4 (Val.of_bool should_reseed)).
  {
    forward.
    entailer!.

    rename H into Hpr.
    destruct prediction_resistance; simpl. 
    (* true *) reflexivity.
    (* false *) inversion Hpr.
  }
  {
    rename H into Hpr.
    destruct prediction_resistance; try solve [inversion Hpr].
    simpl in should_reseed; clear Hpr. 
    forward.
    entailer!.
    
    subst should_reseed; rewrite Z.gtb_ltb.
    unfold Int.lt.
      unfold hmac256drbgabs_reseed_counter in Hreseed_counter_in_range.
    destruct Hreseed_interval as [AA BB]. simpl in *. (*red in AA. *)
    remember (reseed_interval <? reseed_counter) as r; simpl. destruct r. 
    {
      (* reseed_interval < reseed_counter *)
      symmetry in Heqr; apply Zlt_is_lt_bool in Heqr. unfold Int.lt.
      rewrite zlt_true; [reflexivity | ].
      rewrite !Int.signed_repr; change Int.min_signed with (-2147483648); change Int.max_signed with (2147483647) in *; try omega.
    }
    { (*subst initial_state_abs.
      assert (Hltb: 10000 <? reseed_counter = false) by (rewrite Z.ltb_nlt; assumption).
      rewrite Hltb.*)
      symmetry in Heqr; apply Z.ltb_ge in Heqr. unfold Int.lt.
      rewrite zlt_false; [reflexivity | ].
      rewrite !Int.signed_repr; change Int.min_signed with (-2147483648); change Int.max_signed with (2147483647) in *; try omega.
    }
  }
  set (after_reseed_add_len := if should_reseed then 0 else add_len) in *.

 (******************)
(*  rename a into initial_state.*)
(*  assert (HIS: exists IS: reptype t_struct_hmac256drbg_context_st, IS = a). 
  { exists a; trivial. }
  destruct HIS as [IS HIS].*)

  set (contents' := contents_with_add additional add_len contents) in *.
  assert (C' : contents' = nil \/ contents' = contents).
  { subst contents'; unfold contents_with_add. simple_if_tac. right; trivial. left; trivial. }
  assert (ZLc' : Zlength contents' = 0 \/ Zlength contents' = Zlength contents).
  { destruct C' as [C' | C']; rewrite C'. left; trivial. right; trivial. }
  forward_if (
   PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance); 
   temp _out output; temp _left (Vint (Int.repr out_len)); temp _ctx (Vptr b i);
   temp _p_rng (Vptr b i); temp _output output; temp _out_len (Vint (Int.repr out_len));
   temp _additional additional; temp _add_len (Vint (Int.repr after_reseed_add_len));
   gvars gv; temp _t'4 (Val.of_bool should_reseed))
   SEP (EX stream1 :ENTROPY.stream, EX key1:list byte, EX ctx1: reptype t_struct_hmac256drbg_context_st,
        (!! POSTRESEED initial_state should_reseed s (mc1, (mc2,mc3)) key V reseed_counter entropy_len
            prediction_resistance reseed_interval
            (contents_with_add additional (Zlength contents) contents)
            stream1 key1 ctx1)
         &&
       (data_at shc t_struct_hmac256drbg_context_st ctx1 (Vptr b i) *
        data_at_ sho (tarray tuchar out_len) output *
        da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional *
        data_at shc t_struct_mbedtls_md_info Info mc1 * K_vector gv *
        md_full key1 (mc1, (mc2, mc3)) *
        Stream stream1))).

  { (*Case should_reseed = true*)
    assert (Hshould_reseed: should_reseed = true) by apply H; clear H.
    unfold POSTCONDITION, abbreviate. rewrite Hshould_reseed in *. clear POSTCONDITION. thaw FR2. 
    abbreviate_semax.

    forward_call (contents, additional, sha, add_len, (*ctx*)Vptr b i, shc, initial_state, 
                  I, Info, s, gv).
    { subst I initial_state; cancel.
      unfold hmac256drbg_relate. simpl in *. entailer!.
    } 
    { split3; auto. simpl in *. repeat split; trivial; try omega.
      rep_omega.
      subst contents'. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc'; omega. 
      subst contents'. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc' in *.
      rep_omega.
      rep_omega.
    }
     
    Intros return_value.
    forward. 

    assert (F: 0>? 256 = false) by reflexivity.
    forward_if (return_value = Vzero).
    {
      (* reseed's return_value != 0 *) 
      rename H into Hrv.
      unfold POSTCONDITION, abbreviate.
      forward. simpl in *.
(*      clear - Hadd_lenb Hadd_len Hrv H3 Hout_lenb ZLa F H4 Hshould_reseed.*)
      Exists (Vint return_value).
      apply andp_right. apply prop_right; split; trivial.
      normalize. 
      apply entailment1; trivial. }

     { (* reseed's return_value = 0 *)
       rename H into Hrv.
       forward. entailer!. unfold Vzero. f_equal. 
       apply negb_false_iff in Hrv. apply int_eq_e in Hrv. trivial.
     }
 
     forward. subst I after_reseed_add_len. rewrite Hshould_reseed in *. clear Hshould_reseed should_reseed.
     entailer!. simpl in *. (*
     Exists  ss KK (mc1, (mc2, mc3),
            (map Vint (map Int.repr VV),
            (Vint (Int.repr aa),
            (Vint (Int.repr entropy_len),
            (Val.of_bool cc, Vint (Int.repr reseed_interval)))))).*)
     unfold reseedPOST; simpl.
     remember ((zlt 256 (Zlength contents)
       || zlt 384 (entropy_len + Zlength contents))%bool) as d.
     destruct (zlt 256 (Zlength contents)); simpl in Heqd; [ omega |].
     destruct (zlt 384 (entropy_len + Zlength contents)); simpl in Heqd; subst d; [ simpl in *; omega |].
     Intros. (* cancel.*)
     unfold return_value_relate_result in H2.
     remember (mbedtls_HMAC256_DRBG_reseed_function s
         (HMAC256DRBGabs key V reseed_counter entropy_len
            prediction_resistance reseed_interval)
         (contents_with_add additional (Zlength contents) contents)) as Reseed.
(*     remember ((hmac256drbgabs_reseed I s
        (contents_with_add additional (Zlength contents) contents))).
     unfold hmac256drbgabs_reseed in Heqh. rewrite <- HeqReseed in Heqh.*)
     destruct Reseed.
     + destruct d as [[[[RSVal RSKey] aa] bb] cc]. (* destruct I; simpl in *. 
       unfold (*hmac256drbgabs_reseed, *)postReseedCtx, postReseedKey, postReseedStream.
       subst I; rewrite <- HeqReseed. simpl. simpl in Heqh. subst h. *)
       Exists s0 RSKey (mc1, (mc2, mc3),
         (map Vubyte RSVal,
         (Vint (Int.repr aa),
         (Vint (Int.repr entropy_len), (Val.of_bool cc, Vint (Int.repr reseed_interval)))))).
       unfold hmac256drbgabs_common_mpreds.
       simpl; normalize.
       apply andp_right; [ apply prop_right | cancel].
       exists RSVal, RSKey, aa, bb, cc, s0. repeat split; trivial. 
     + destruct e; [ discriminate |]. 
       destruct ENT_GenErrAx as [X _]. elim X; trivial.
  }
  { (*Case should_reseed = false*)
    forward. subst after_reseed_add_len. rewrite H (*, Hinitial_state*) in *. clear H (*Hinitial_state*).
    Exists s key initial_state. entailer!. thaw FR2; cancel.
  }
  clear FR2. Intros stream1 key1 ctx1. rename H into PRS. 

(*  exfalso. apply myAx. Time Qed. 42s*)
(*  assert (HIC: exists IC: reptype t_struct_mbedtls_md_info, IC = Info).
  { exists Info; trivial. }
  destruct HIC as [IC HIC]. *)

  freeze [1;3;6] FR3.
  freeze [0;1;3;4] FR4.

  set (na:=(negb (eq_dec additional nullval) && negb (eq_dec ((if should_reseed then 0 else Zlength contents)) 0))%bool) in *.
 
  forward_if (temp _t'5 (Val.of_bool na)).
  { destruct additional; simpl in PNadditional; try contradiction.
    + subst i0; entailer.
    + rewrite da_emp_ptr. normalize.
      apply denote_tc_test_eq_split.
      apply sepcon_valid_pointer2. 
      apply data_at_valid_ptr; trivial. auto.
      auto 50 with valid_pointer.
  }
  { forward. entailer!. subst after_reseed_add_len na.
    destruct should_reseed; simpl; trivial. rewrite andb_false_r. reflexivity.
    destruct (initial_world.EqDec_Z (Zlength contents)  0); simpl. 
    + rewrite e. simpl. rewrite andb_false_r. reflexivity.
    + rewrite Int.eq_false; simpl. 
      destruct (Memory.EqDec_val additional nullval); try reflexivity. contradiction. 
      intros N. assert (U: Int.unsigned (Int.repr (Zlength contents)) = Int.unsigned (Int.repr 0)). rewrite N; trivial. clear N.
      rewrite Int.unsigned_repr in U; trivial. rewrite U in n. elim n; trivial. 
  }
  { forward. rewrite H in *. entailer!. }

  thaw FR4.
  forward_if (EX ctx2:reptype t_struct_hmac256drbg_context_st, EX key2:list byte, 
  (PROP (POSTUPDATE na additional contents key V (mc1,(mc2,mc3)) reseed_counter entropy_len prediction_resistance reseed_interval ctx1 key1 key2 ctx2)
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance);
   temp _out output; temp _left (Vint (Int.repr out_len)); 
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); 
   gvars gv; temp _t'4 (Val.of_bool should_reseed);
   temp _t'5 (Val.of_bool na))
   SEP (FRZL FR3; K_vector gv;
   da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional;
    data_at shc t_struct_hmac256drbg_context_st ctx2 (Vptr b i) *
    md_full key2 (mc1, (mc2, mc3))))).
   { rewrite H in *. subst na.
     destruct should_reseed; simpl in PRS, H. rewrite andb_false_r in H; discriminate.
     destruct (initial_world.EqDec_Z (Zlength contents) 0); simpl in H.
     { rewrite andb_false_r in H; discriminate. }
     rewrite andb_true_r in H.
     destruct additional; simpl in PNadditional; try contradiction.
     { subst i0; discriminate. }
     destruct PRS as [? [? ?]]; subst key1 stream1 ctx1. clear H. 
     
       forward_call (contents, Vptr b0 i0, sha, after_reseed_add_len, 
                    (*ctx*)Vptr b i, shc, initial_state,I, Info, gv).
       { assert (FR: Frame = [data_at_ sho (tarray tuchar out_len) output * Stream s]).
         { subst Frame; reflexivity. }
         subst Frame.
         subst after_reseed_add_len add_len initial_state. cancel.
         thaw FR3. (*subst (*initial_state*) IC.*)
         unfold hmac256drbg_relate, hmac256drbgstate_md_info_pointer; simpl. cancel. entailer!. 
       }
       split3; auto. 
       { (*subst na.*)subst after_reseed_add_len. entailer. unfold hmac256drbgabs_common_mpreds.
         remember ( HMAC256_DRBG_update
             (contents_with_add (Vptr b0 i0) (Zlength contents) contents) key
             V) as UPD. destruct UPD as [KK VV]. simpl. 
         Exists (mc1, (mc2, mc3),
            (map Vubyte VV,
            (Vint (Int.repr reseed_counter),
            (Vint (Int.repr entropy_len),
            (Val.of_bool prediction_resistance,
            Vint (Int.repr reseed_interval)))))) KK.
         normalize.  
         apply andp_right; [ apply prop_right | thaw FR3; cancel].
         split; [| repeat split; trivial].
         exists b0, i0, VV. repeat split; trivial. }  
     }
     { clear - H. forward. rewrite H in *. 
       Exists ctx1 key1. entailer!. }
  Intros ctx2 key2. rename H into PUPD.

(*exfalso. apply myAx. Time Qed. 54s*)

set (after_reseed_state_abs := if should_reseed
          then hmac256drbgabs_reseed I s (contents_with_add additional add_len contents)
          else I) in *.

assert (ZLength_ARSA_val: Zlength (hmac256drbgabs_value after_reseed_state_abs) = 32).
{ subst after_reseed_state_abs add_len.
  destruct should_reseed; trivial. 
  apply Zlength_hmac256drbgabs_reseed_value; trivial. }

assert (RC_x: 0 <= hmac256drbgabs_reseed_counter after_reseed_state_abs < Int.max_signed).
{ subst after_reseed_state_abs. unfold hmac256drbgabs_reseed.
  destruct should_reseed; simpl in *; [|trivial].
  destruct PRS as [? [? [? [? [? [? [PP [? [? ?]]]]]]]]]. subst. subst I. rewrite PP in *; simpl in *.
  assert (RS: mbedtls_HMAC256_DRBG_reseed_function =
          fun (entropy_stream: ENTROPY.stream) (a:hmac256drbgabs)
           (additional_input: list byte) =>
  match a with HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval =>
               let sec_strength:Z := 32 (*not used -- measured in bytes, since that's how the calculations in DRBG_instantiate_function work *) in
               let state_handle: DRBG_state_handle := ((V, key, reseed_counter), sec_strength, prediction_resistance) in
               let max_additional_input_length := 256 
               in HMAC256_DRBG_reseed_function entropy_len entropy_len max_additional_input_length 
                     entropy_stream state_handle prediction_resistance additional_input
  end) by reflexivity.
  rewrite RS in PP; clear RS. Opaque HMAC256_DRBG_reseed_function. simpl in PP.
  symmetry in PP. apply verif_hmac_drbg_WF.HMAC256_DRBG_reseed_functionWFaux in PP; apply PP. }

set (after_update_state_abs := (if na then hmac256drbgabs_hmac_drbg_update I contents else after_reseed_state_abs)) in *.

assert (ZLength_AUSA_val: Zlength (hmac256drbgabs_value after_update_state_abs) = 32).
{ subst after_update_state_abs.
  destruct na; trivial. apply Zlength_hmac256drbgabs_update_value. } 

assert (RC_y: 0 <= hmac256drbgabs_reseed_counter after_update_state_abs < Int.max_signed).
{ subst after_update_state_abs.
  destruct na; trivial. subst I; simpl.
  destruct (HMAC256_DRBG_update contents key V). simpl; trivial. }

thaw FR3.
set (after_update_Mpred := hmac256drbgabs_common_mpreds shc after_update_state_abs initial_state (Vptr b i) Info) in *.
apply semax_pre with (P':=
  (PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance); 
   temp _out output; temp _left (Vint (Int.repr out_len)); 
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvars gv)
   SEP (data_at_ sho (tarray tuchar out_len) output; Stream stream1; 
     K_vector gv;
     da_emp sha (tarray tuchar add_len) (map Vubyte contents) additional;
     after_update_Mpred ))).
{ go_lower. normalize.
  apply andp_right. apply prop_right; repeat split; trivial. cancel.
  subst after_update_Mpred. unfold hmac256drbgabs_common_mpreds(*. subst IC*); simpl.
  unfold hmac256drbg_relate, hmac256drbgstate_md_info_pointer.
  remember (hmac256drbgabs_to_state after_update_state_abs initial_state).
  unfold hmac256drbgabs_to_state in Heqh. subst after_update_state_abs initial_state. simpl in *.

  destruct should_reseed; subst add_len I; simpl in *.
  + assert (NA: na= false).
    { subst na. rewrite andb_false_r; trivial. }
    rewrite NA in *.
    remember (mbedtls_HMAC256_DRBG_reseed_function s (HMAC256DRBGabs key V reseed_counter entropy_len
             prediction_resistance reseed_interval)
                              (contents_with_add additional (Zlength contents)  contents)) as M.
    destruct PRS as [VV [KK [aa [zz [cc [ss [HM [? [? ?]]]]]]]]]. subst ss KK ctx1; rewrite HM in *.
    remember (HMAC256_DRBG_update contents key V) as UPD; destruct UPD as [KKK VVV].
    subst M after_reseed_state_abs. subst h; simpl in *.
    destruct PUPD; subst key2 ctx2. entailer!. 
  + destruct PRS as [? [? ?]]; subst stream1 key1 ctx1 after_reseed_state_abs.
    destruct (Memory.EqDec_val additional nullval); simpl in *.
    - destruct PUPD; subst ctx2 key2 na h; simpl in *. entailer!.
    - remember (initial_world.EqDec_Z (Zlength contents) 0) as q; destruct q; simpl in *. 
      * destruct PUPD; subst ctx2 key2 na h; simpl in *. entailer!. 
      * destruct PUPD as [bb [ii [UVAL [ADD [HUPD CTX2 ]]]]]. 
        unfold contents_with_add in HUPD. simpl in HUPD; rewrite <- Heqq in HUPD; simpl in HUPD.  
        rewrite <- HUPD in *. subst h ctx2; simpl in *. entailer!.
}  
subst after_update_Mpred.
assert (TR: mkSTREAM1 (prediction_resistance || (reseed_counter >? reseed_interval)) s
  key V reseed_counter entropy_len prediction_resistance reseed_interval
  additional contents stream1).
{ subst. red.
  remember ((prediction_resistance || (reseed_counter >? reseed_interval))%bool) as sr.
  destruct sr.
  + subst should_reseed. simpl in *.
    destruct PRS as [VV [KK [aa [zz [cc [ss [M [ES [? ?]]]]]]]]]. subst stream1 key1 ctx1. rewrite M; trivial.
  + subst should_reseed. simpl in *. destruct PRS as [? [? ?]]; subst stream1 key1 ctx1; trivial.
}
clear PUPD PRS ctx1 key1 ctx2 key2.

freeze [1;3] StreamAdd.
rewrite data_at__isptr with (p:=output). Intros.

set (AUV:=hmac256drbgabs_value after_update_state_abs) in *.
set (AUK:=hmac256drbgabs_key after_update_state_abs) in *.

set (HLP := HMAC_DRBG_generate_helper_Z HMAC256 (*after_update_key after_update_value*) AUK AUV).

  forward_while (
    EX done: Z,
      PROP  (0 <= done <= out_len; ((*WMod.*)is_multiple done 32) \/ done = out_len)
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr 32)); temp _info mc1(*(let (x, _) := md_ctx' in x)*);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out (offset_val done output); temp _left (Vint (Int.repr (out_len - done))); 
      temp _ctx (*ctx*)(Vptr b i); temp _p_rng (*ctx*)(Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
      gvars gv
      )
      SEP  ((*Stream stream1;*)
      hmac256drbgabs_common_mpreds shc (hmac256drbgabs_update_value after_update_state_abs 
              (fst (HLP done)))
        initial_state (Vptr b i) Info; FRZL StreamAdd; 
      data_at sho (tarray tuchar out_len) ((map Vubyte
          (sublist 0 done (snd (HLP done)))) ++ 
          list_repeat (Z.to_nat (out_len - done)) Vundef) output; 
      K_vector gv)
  ).
  {
    (* prove the current precondition implies the loop condition *)
    Exists 0.
    change (sublist 0 0 (snd (HLP 0))) with (@nil byte).
    replace (out_len - 0) with out_len by omega.
    change ((map Vint (map Int.repr []) ++
          list_repeat (Z.to_nat out_len) Vundef)) with (list_repeat (Z.to_nat out_len) Vundef).
    assert (Hafter_update: (hmac256drbgabs_update_value after_update_state_abs(*AUSA*)
            (fst (HLP 0))) = after_update_state_abs(*AUSA*)).
    {
      simpl. (*destruct AUSA.*) simpl. subst AUV; simpl. destruct after_update_state_abs; reflexivity. (* unfold hmac256drbgabs_update_value.
      subst after_update_value; destruct after_update_state_abs; reflexivity.*)
    }
    rewrite Hafter_update.
    (*entailer!.*) go_lower. normalize. apply andp_right. apply prop_right; repeat split; trivial. omega. omega.
    left; exists 0; omega.
    cancel.
  }
  {
    (* prove the type checking of the loop condition *)
    entailer!.
  }
  assert (WFI: drbg_protocol_specs.WF
      (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval)).
  { subst I; red; simpl in *. red in Hreseed_interval. repeat split; trivial; try omega. }
  { (*LOOP BODY -- INLINED VERSION*)
(*    semax_subcommand HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_random_with_add.x*)
Opaque HMAC_DRBG_generate_helper_Z.
Opaque hmac256drbgabs_reseed.
    apply sequential.
    eapply semax_post_flipped'.
    apply (loopbody_explicit StreamAdd); simpl; trivial.
    unfold POSTCONDITION, abbreviate. simpl_ret_assert.
    old_go_lower.
    subst.
    Intros v; Exists v.
    normalize. entailer!. apply derives_refl.
  }
  
  assert (Hdone: done = out_len).
  {
    clear - HRE H Hout_len.
    assert (Hdiff: out_len - done = 0).
    {
      unfold Int.eq in HRE.
      unfold zeq in HRE.
      destruct (Z.eq_dec (Int.unsigned (Int.repr (out_len - done)))
                (Int.unsigned (Int.repr 0))).
      rewrite (Int.unsigned_repr (out_len - done)) in e.
      rewrite e; reflexivity.
      change (Int.max_unsigned) with 4294967295; omega.
      rewrite HRE in *. elim n; trivial.
    }
    omega.
  }
  subst done.
  clear H H0.
  replace (out_len - out_len) with 0 by omega. clear HRE.
  change (list_repeat (Z.to_nat 0) Vundef) with (@nil val).
  rewrite app_nil_r.
  unfold hmac256drbgabs_common_mpreds.
  normalize. unfold hmac256drbg_relate.
  remember (hmac256drbgabs_update_value after_update_state_abs (fst (HLP out_len))) as ABS3.
  remember (hmac256drbgabs_to_state ABS3 initial_state) as CTX3.
  destruct ABS3. destruct CTX3 as [aa [bb [cc [dd [ee ff]]]]]. normalize.
  unfold hmac256drbgabs_to_state in HeqCTX3. subst initial_state; simpl in HeqCTX3. inv HeqCTX3.

  set (ctx3 := (mc1, (mc2, mc3),
          (map Vubyte V0,
          (Vint (Int.repr reseed_counter0),
          (Vint (Int.repr entropy_len0),
          (Val.of_bool prediction_resistance0, Vint (Int.repr reseed_interval0))))))) in *.
  thaw StreamAdd.
  freeze [3;5] StreamOut. 

  (* mbedtls_hmac_drbg_update( ctx, additional, add_len ); *)
  (*subst add_len.*)
  forward_call (contents,
         additional, sha, after_reseed_add_len, 
         (*ctx*)Vptr b i, shc, ctx3,
         hmac256drbgabs_update_value after_update_state_abs (fst (HLP out_len)),
         Info, gv).
  { subst after_reseed_add_len. unfold hmac256drbg_relate. rewrite <- HeqABS3.
    subst ctx3. simpl. normalize. 
    apply andp_right. apply prop_right. repeat split; trivial.
    cancel. }
  { subst after_reseed_add_len. rewrite <- HeqABS3; simpl.
    split3; auto. split. destruct should_reseed; omega.
    split. assumption.
    destruct should_reseed; omega. }

  unfold hmac256drbgabs_common_mpreds. normalize.

  remember ((hmac256drbgabs_hmac_drbg_update
                (hmac256drbgabs_update_value after_update_state_abs (fst (HLP out_len)))
                (contents_with_add additional after_reseed_add_len contents))) as ABS4.
  set (ctx4 := hmac256drbgabs_to_state ABS4 ctx3) in *. rewrite <- HeqABS3 in HeqABS4.
  unfold hmac256drbg_relate.
  subst ctx3. simpl in ctx4. destruct ABS4. simpl in ctx4. subst ctx4. simpl. normalize.
  assert (RC1: 0 <= reseed_counter1 < Int.max_signed).
  { clear - RC_x RC_y HeqABS3 HeqABS4. 
    unfold hmac256drbgabs_hmac_drbg_update in HeqABS4.
    remember (HMAC256_DRBG_update
               (contents_with_add additional
                  after_reseed_add_len contents) key0
               V0) as z. destruct z. inv HeqABS4.
    unfold hmac256drbgabs_update_value in HeqABS3.
    subst after_update_state_abs.
    destruct na.
    + subst; simpl in *.
      remember (HMAC256_DRBG_update contents key V) as q. destruct q.
      inv HeqABS3. trivial. 
    + subst; simpl in *. subst after_reseed_state_abs. simpl in *.
      destruct should_reseed.
      - simpl in *.
        remember (hmac256drbgabs_reseed I s
              (contents_with_add additional (Zlength contents) contents)) as q.
        destruct q. simpl in *. inv HeqABS3; trivial.
      - subst I; simpl in *. inv HeqABS3; trivial. } 

  unfold hmac256drbgstate_md_info_pointer. simpl.
  freeze [2;3;4;5] FR5. 
  unfold_data_at 1%nat.
  freeze [1;2;4;5;6;7] FIELDS.
  forward.
  forward.
  forward.
  Exists (Vint (Int.repr 0)).
  apply andp_right. apply prop_right; split; trivial.
  thaw FIELDS. thaw FR5. thaw StreamOut.
(*
  clear - WFI HeqABS4 HeqABS3 STREAM1 H1 H3 H4 H6 Hreseed_counter_in_range
          Hout_lenb ZLa Hreseed_interval.*) subst I contents'. 
  eapply derives_trans.
  apply (entailment2 key0 V0 reseed_counter0 entropy_len0 prediction_resistance0 reseed_interval0); try assumption; simpl in *.
  + red in Hreseed_interval; red; simpl in *. repeat split; trivial; try omega.
  + unfold drbg_protocol_specs.AREP, drbg_protocol_specs.REP, hmac256drbgabs_common_mpreds, hmac256drbgstate_md_info_pointer;
    normalize. rewrite <- H8.
    remember (mbedtls_HMAC256_DRBG_generate_function s
       (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval) out_len
       (contents_with_add additional (Zlength contents) contents)).
Transparent hmac256drbgabs_generate. 
    unfold hmac256drbgabs_generate.
Opaque hmac256drbgabs_generate. rewrite <- Heqr. 
    rewrite !sepcon_assoc.
    apply sepcon_derives. apply derives_refl.
    remember ( (hmac256drbgabs_generate
        (HMAC256DRBGabs key V reseed_counter entropy_len
           prediction_resistance reseed_interval) s out_len
        (contents_with_add additional (Zlength contents) contents))). destruct h. simpl.
    destruct a as [? [? [? [? [? ?]]]]]. normalize.
    destruct r.
    - destruct p as [? [? ?]]. destruct p as [[[? ?] ?] ?]. simpl. entailer!. 
    - simpl. entailer!.
Time Qed. (*Desktop:83ss*) 