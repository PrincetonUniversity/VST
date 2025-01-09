Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import VST.zlist.sublist.

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
Require Import hmacdrbg.drbg_protocol_specs.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require Import hmacdrbg.verif_hmac_drbg_WF.

Opaque HMAC256.
Opaque hmac256drbgabs_generate.
Opaque HMAC256_DRBG_generate_function.
Opaque mbedtls_HMAC256_DRBG_generate_function.

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
    apply HMAC_DRBG_generate_helper_Z_incremental_snd; auto; lia.
  }
  {
    rewrite zlt_false by assumption.
    assert (0 < out_len - (n * 32)%Z <= 32).
    {
      split.
      rewrite <- Z2Nat.id in *; try lia.
      remember (Z.to_nat (out_len - n * 32)) as n'; destruct n'.
      {
        (* contradiction. out_len - n <> 0 *)
        assert (0 = out_len - n * 32).
        {
          symmetry;
          apply Z2Nat_inj_0.
          lia.
          symmetry; assumption.
        }
        assert (out_len = (n * 32)%Z) by lia.
        lia.
      }
      lia.
    }
    assert (exists n', (n * 32)%Z = (n' * 32)%Z).
    {
      exists n; reflexivity.
    }
    rewrite HMAC_DRBG_generate_helper_Z_incremental_equiv; auto; try lia.
    apply HMAC_DRBG_generate_helper_Z_incremental_snd; auto; lia.
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
    symmetry; apply HMAC_DRBG_generate_helper_Z_incremental_fst; auto; lia.
  }
  {
    rewrite zlt_false by assumption.
    assert (0 < out_len - (n * 32)%Z <= 32).
    {
      split.
      rewrite <- Z2Nat.id in *; try lia.
      remember (Z.to_nat (out_len - n * 32)) as n'; destruct n'.
      {
        (* contradiction. out_len - n <> 0 *)
        assert (0 = out_len - n * 32).
        {
          symmetry;
          apply Z2Nat_inj_0.
          lia.
          symmetry; assumption.
        }
        assert (out_len = (n * 32)%Z) by lia.
        lia.
      }
      lia.
    }
    assert (exists n', (n * 32)%Z = (n' * 32)%Z).
    {
      exists n; reflexivity.
    }
    rewrite HMAC_DRBG_generate_helper_Z_incremental_equiv; auto; try lia.
    symmetry; apply HMAC_DRBG_generate_helper_Z_incremental_fst; auto; lia.
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
    lia.
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
    rewrite zlt_true by assumption; lia.
    rewrite zlt_false by assumption; lia.
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
    destruct (Z_lt_ge_dec (Zlength B) (out_len - (Zlength A))) as [Hmin | Hmin]; [rewrite zlt_true by assumption| rewrite zlt_false by assumption]; lia).
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
    destruct (Z.min_dec (Zlength B) (out_len - Zlength A)) as [Hmin | Hmin]; rewrite Hmin; lia.
  }
  rewrite HminA.
  rewrite sublist_same with (hi:=Zlength A); try lia.
  assert (Hmax0: (Z.max (0 - Zlength A) 0) = 0).
  {
    rewrite Zmax_spec.
    rewrite zlt_false; auto; lia.
  }
  rewrite Hmax0.
  replace (Zlength A + Z.min (Zlength B) (out_len - Zlength A) - Zlength A) with (Z.min (Zlength B) (out_len - Zlength A)) by lia.
  assert (HmaxB: (Z.max (Z.min (Zlength B) (out_len - Zlength A)) 0) = (Z.min (Zlength B) (out_len - Zlength A))).
  {
    rewrite <- (Z2Nat.id (out_len - Zlength A)) in *; try lia.
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
  replace (out_len - 0) with out_len by lia.
 
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
        lia.
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
        lia.
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
           (Vint (Int.repr entropy_len), (bool2val cc, Vint (Int.repr reseed_interval))))))
           (Vptr b i)
   | _ => FF
  end.
*)
(*
Definition postReseedCtx (CTX:reptype t_struct_hmac256drbg_context_st) s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents (mc:mdstate): Prop :=
  match mbedtls_HMAC256_DRBG_reseed_function s
               (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
                  reseed_interval) (contents_with_add additional (Zlength contents) contents)
  with ENTROPY.success (RSVal, RSKey, aa, bb, cc) s0 => CTX =
           (mc,
           (map Vint (map Int.repr RSVal),
           (Vint (Int.repr aa),
           (Vint (Int.repr entropy_len), (bool2val cc, Vint (Int.repr reseed_interval))))))
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
             data_at Tsh t_struct_hmac256drbg_context_st myctx p.*)
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
(*
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
                  (Vint (Int.repr entropy_len), (bool2val cc, Vint (Int.repr reseed_interval))))))
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
  else key1=key.*)

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
(*Definition CTXeq (c:reptype t_struct_hmac256drbg_context_st)
                 (c':(val * (val * val) * (list val * (val * (val * (val * val)))))%type) : Prop := c'=c.
*)
Definition is_multiple (multiple base: Z) : Prop := exists i, multiple = (i * base)%Z.

Lemma entailment1: forall (contents : list byte) (additional: val) (sha: share) (output : val) (sho: share)
  (out_len : Z) (b : block) (i : ptrofs) (shc: share) (mc1 mc2 mc3 : val) (key V : list byte)
  (reseed_counter entropy_len : Z) (prediction_resistance : bool)
  (reseed_interval : Z) (gv : globals) (Info : md_info_state)
  (s : ENTROPY.stream)
  (I := HMAC256DRBGabs key V reseed_counter entropy_len
                       prediction_resistance reseed_interval : hmac256drbgabs)
(*(RI : reseed_interval = 10000)*)
  (a := (mc1, (mc2, mc3),
                 (map Vubyte V,
                 (Vint (Int.repr reseed_counter),
                 (Vint (Int.repr entropy_len),
                 (bool2val prediction_resistance,
                 Vint (Int.repr reseed_interval))))))
              : mdstate * (list val * (val * (val * (val * val)))))
  (WFI: WF I)
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
  I (Vptr b i) shc Info gv a *
data_at_ sho (tarray tuchar out_len) output
|-- !! return_value_relate_result
         (mbedtls_HMAC256_DRBG_generate_function s I out_len
            (contents_with_add additional (Zlength contents) contents))
         (Vint return_value) &&
    (match
       mbedtls_HMAC256_DRBG_generate_function s I out_len
         (contents_with_add additional (Zlength contents) contents)
     with
     | ENTROPY.success (bytes, _) _ =>
         data_at sho (tarray tuchar out_len) (map Vubyte bytes)
           output
     | ENTROPY.error _ _ => data_at_ sho (tarray tuchar out_len) output
     end *
     da_emp sha (tarray tuchar (Zlength contents))
       (map Vubyte contents) additional *
     Stream
       (get_stream_result
          (mbedtls_HMAC256_DRBG_generate_function s I out_len  (contents_with_add additional (Zlength contents) contents))) *
     AREP shc gv (hmac256drbgabs_generate I s out_len  (contents_with_add additional (Zlength contents) contents)) (Vptr b i)).
Proof. intros.
 unfold reseedPOST. apply Zgt_is_gt_bool_f in Hadd_lenb.
 remember ((zlt 256 (Zlength contents)
   || zlt 384 (hmac256drbgabs_entropy_len I + Zlength contents))%bool) as d.
 destruct (zlt 256 (Zlength contents)); simpl in Heqd. lia. clear g.
 destruct (zlt 384 (entropy_len + Zlength contents)); simpl in Heqd; subst d. lia.
 normalize.
      remember (mbedtls_HMAC256_DRBG_reseed_function s I
        (contents_with_add additional (Zlength contents) contents)) as MRS.
      unfold return_value_relate_result in H. 
      destruct MRS. 
      { exfalso.  inv H. simpl in Hrv; discriminate. }
      unfold hmac256drbgabs_common_mpreds.
      remember (hmac256drbgabs_reseed I s
        (contents_with_add additional (Zlength contents) contents)) as RS.
      unfold hmac256drbgabs_reseed in HeqRS. rewrite <- HeqMRS in HeqRS.
      assert (HRS: RS = I) by (subst I; apply HeqRS). 
      clear HeqRS; subst RS. 
      remember (hmac256drbgabs_generate I s out_len
                (contents_with_add additional (Zlength contents) contents)) as Gen.
      remember (mbedtls_HMAC256_DRBG_generate_function s I out_len
             (contents_with_add additional (Zlength contents) contents)) as MGen.
      Transparent hmac256drbgabs_generate.
      Transparent mbedtls_HMAC256_DRBG_generate_function.
      unfold hmac256drbgabs_generate in HeqGen. rewrite <- HeqMGen in HeqGen. 
      unfold mbedtls_HMAC256_DRBG_generate_function in HeqMGen. subst I. 
      simpl in HeqMGen. 
      Transparent HMAC256_DRBG_generate_function. unfold HMAC256_DRBG_generate_function in HeqMGen.
      unfold mbedtls_HMAC256_DRBG_reseed_function in HeqMRS.
      unfold DRBG_generate_function in HeqMGen.
      rewrite Hout_lenb, ZLa, andb_negb_r, F32 in HeqMGen. 
      unfold DRBG_generate_function_helper in HeqMGen. rewrite <- HeqMRS in HeqMGen. subst Gen.
      simpl. Intros.
      destruct prediction_resistance; simpl in *.
      + rewrite ZLa in *. subst MGen.
        unfold return_value_relate_result. 
        apply andp_right. apply prop_right. repeat split; trivial.
        simpl; cancel. unfold AREP, REP. Exists Info. Exists a.
        unfold hmac256drbg_relate; simpl. entailer!.
      + rewrite Hshould_reseed, ZLa in *.
        destruct (get_entropy 32(*256*) entropy_len entropy_len false s); try discriminate.
        inv HeqMRS. unfold return_value_relate_result; simpl.
        apply andp_right. apply prop_right. repeat split; trivial.
        cancel. unfold AREP, REP. Exists Info. Exists a.
        unfold hmac256drbg_relate; simpl. entailer!. 
Qed.

Opaque hmac256drbgabs_generate.
Opaque HMAC256_DRBG_generate_function.
Opaque mbedtls_HMAC256_DRBG_generate_function.

Lemma entailment2: forall
key0 V0 reseed_counter0 entropy_len0 prediction_resistance0 reseed_interval0
(contents : list byte)
(additional : val) (sha: share) 
(output : val) (sho: share)
(out_len : Z)
(b : block) (i : ptrofs) (shc: share)
(key V : list byte)
(reseed_counter entropy_len : Z)
(prediction_resistance : bool)
(reseed_interval : Z)
(gv: globals)
(s : ENTROPY.stream)
(I := HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
       reseed_interval : hmac256drbgabs)
(H1 : Zlength (hmac256drbgabs_value I) = 32)
(H3 : 0 < hmac256drbgabs_entropy_len I)
(H4 : hmac256drbgabs_entropy_len I + Zlength contents <= 384)
(Hreseed_interval : RI_range (hmac256drbgabs_reseed_interval I))
(Hreseed_counter_in_range : 0 <= hmac256drbgabs_reseed_counter I <
                           Int.max_signed)
(Info : md_info_state)
(mc1 mc2 mc3 : val)
(WFI : WF I)
(Hout_lenb : (out_len >? 1024) = false)
(contents' := contents_with_add additional (Zlength contents) contents
          : list byte)
(ZLa : (Zlength contents' >? 256) = false)
(should_reseed := (prediction_resistance
                  || (reseed_counter >? reseed_interval))%bool : bool)
(after_reseed_add_len := if should_reseed then 0 else Zlength contents : Z)
(stream1 : ENTROPY.stream)
(STREAM1 : mkSTREAM1 should_reseed s key V reseed_counter entropy_len
            prediction_resistance reseed_interval additional contents stream1)
(na := (negb (eq_dec additional nullval) &&
       negb (eq_dec (if should_reseed then 0 else Zlength contents) 0))%bool
   : bool)
(after_reseed_state_abs := if should_reseed
                          then
                           hmac256drbgabs_reseed I s
                             (contents_with_add additional (Zlength contents)
                                contents)
                          else I : hmac256drbgabs)
(after_update_state_abs := if na
                          then hmac256drbgabs_hmac_drbg_update I contents
                          else after_reseed_state_abs : hmac256drbgabs)
(AUV := hmac256drbgabs_value after_update_state_abs : list byte)
(AUK := hmac256drbgabs_key after_update_state_abs : list byte)
(HLP := HMAC_DRBG_generate_helper_Z HMAC256 AUK AUV : Z -> list byte * list byte)
(HeqABS3 : HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
            prediction_resistance0 reseed_interval0 =
          hmac256drbgabs_update_value after_update_state_abs
            (fst (HLP out_len)))
(key1 V1 : list byte)
(reseed_counter1 entropy_len1 : Z)
(prediction_resistance1 : bool)
(reseed_interval1 : Z)
(HeqABS4 : HMAC256DRBGabs key1 V1 reseed_counter1 entropy_len1
            prediction_resistance1 reseed_interval1 =
          hmac256drbgabs_hmac_drbg_update
            (HMAC256DRBGabs key0 V0 reseed_counter0 entropy_len0
               prediction_resistance0 reseed_interval0)
            (contents_with_add additional after_reseed_add_len contents)),
field_at shc t_struct_hmac256drbg_context_st [StructField _md_ctx]
  (mc1, (mc2, mc3)) (Vptr b i) *
(field_at shc t_struct_hmac256drbg_context_st [StructField _V]
   (map Vubyte V1) (Vptr b i) *
 (field_at shc t_struct_hmac256drbg_context_st [StructField _entropy_len]
    (Vint (Int.repr entropy_len1)) (Vptr b i) *
  (field_at shc t_struct_hmac256drbg_context_st
     [StructField _prediction_resistance]
     (bool2val prediction_resistance1) (Vptr b i) *
   (field_at shc t_struct_hmac256drbg_context_st
      [StructField _reseed_interval] (Vint (Int.repr reseed_interval1))
      (Vptr b i) * (data_at shc t_struct_mbedtls_md_info Info mc1 * emp))))) *
(md_full key1 (mc1, (mc2, mc3)) *
 (da_emp sha (tarray tuchar (Zlength contents))
    (map Vubyte contents) additional *
  (K_vector gv *
   (Stream stream1 *
    (data_at sho (tarray tuchar out_len)
       (map Vubyte (sublist 0 out_len (snd (HLP out_len))))
       output * emp) * emp)))) *
field_at shc t_struct_hmac256drbg_context_st [StructField _reseed_counter]
  (Vint (Int.repr (reseed_counter1 + 1))) (Vptr b i)
|-- !! return_value_relate_result
         (mbedtls_HMAC256_DRBG_generate_function s I out_len contents')
         (Vint (Int.repr 0)) &&
    (match mbedtls_HMAC256_DRBG_generate_function s I out_len contents' with
     | ENTROPY.success (bytes, _) _ =>
         data_at sho (tarray tuchar out_len) (map Vubyte bytes)
           output
     | ENTROPY.error _ _ => data_at_ sho (tarray tuchar out_len) output
     end *
     da_emp sha (tarray tuchar (Zlength contents))
       (map Vubyte contents) additional *
     Stream
       (get_stream_result
          (mbedtls_HMAC256_DRBG_generate_function s I out_len contents')) *
     ((EX a : hmac256drbgstate,
       !! (WF (hmac256drbgabs_generate I s out_len contents')/\ fst a =(mc1, (mc2, mc3)))&&
       data_at shc t_struct_hmac256drbg_context_st a (Vptr b i) *
       hmac256drbg_relate (hmac256drbgabs_generate I s out_len contents') a *
       data_at shc t_struct_mbedtls_md_info Info
         (hmac256drbgstate_md_info_pointer a) * K_vector gv))). 
Proof. intros. assert (H6:=I).
  unfold hmac256drbgabs_common_mpreds, hmac256drbg_relate, hmac256drbgstate_md_info_pointer.
  simpl. Intros.
  set (Gen := hmac256drbgabs_generate I s out_len  contents') in *.
Transparent  hmac256drbgabs_generate.
  unfold hmac256drbgabs_generate in Gen.
Opaque hmac256drbgabs_generate.
  assert (F32: 32 >? 32 = false) by reflexivity.
  simpl in HeqABS4.
  remember (HMAC256_DRBG_update (contents_with_add additional after_reseed_add_len contents) key0 V0) as UPD.
  destruct UPD; inv HeqABS4.
  remember after_update_state_abs as AUSA.
  destruct AUSA. simpl in AUV, AUK, HeqABS3. subst AUV AUK; inv HeqABS3.
  unfold hmac256drbgabs_reseed in after_reseed_state_abs.
  unfold mkSTREAM1 in STREAM1.
  subst I.
  set (MGen := mbedtls_HMAC256_DRBG_generate_function s (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval) out_len
             contents') in *.
  set (MRES := mbedtls_HMAC256_DRBG_reseed_function s (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval)
                 (contents_with_add additional (Zlength contents) contents)) in *.
  simpl in Gen.
  remember should_reseed as sr.
  destruct sr.
  + subst should_reseed after_reseed_add_len. simpl in na.
    remember MRES as MRES'. destruct MRES'; try contradiction. subst MRES.
    destruct d as [[[[? ?] ?] ?] ?]. subst s0. 
    simpl in H1, H3, H4, H6, Hreseed_counter_in_range. 
    remember na as naa.
    destruct naa.
    - subst na. rewrite andb_false_r in Heqnaa. discriminate.
    - subst na. rewrite andb_false_r in Heqnaa. clear Heqnaa.
      subst after_reseed_state_abs. inv HeqAUSA.
      unfold mbedtls_HMAC256_DRBG_reseed_function in HeqMRES'.
Transparent mbedtls_HMAC256_DRBG_generate_function.
Transparent HMAC256_DRBG_generate_function.
      unfold mbedtls_HMAC256_DRBG_generate_function, HMAC256_DRBG_generate_function, DRBG_generate_function in MGen.
Opaque mbedtls_HMAC256_DRBG_generate_function.
Opaque HMAC256_DRBG_generate_function.
      remember MGen as MGen'. subst MGen. subst contents'.
      rewrite Hout_lenb, F32, ZLa, andb_negb_r in HeqMGen'.
      unfold DRBG_generate_function_helper in HeqMGen'.
      rewrite <- HeqMRES' in *.
      unfold HMAC256_DRBG_reseed_function, DRBG_reseed_function in HeqMRES'.
      rewrite andb_negb_r, ZLa in HeqMRES'.
      remember( get_entropy 32(*256*) entropy_len entropy_len  prediction_resistance s) as ENT.
      destruct ENT; inversion HeqMRES'; clear HeqMRES'. subst z0 b0 s0.
      unfold HMAC256_DRBG_update in HeqUPD.
      remember (HMAC_DRBG_update HMAC256 (l3 ++ contents_with_add additional (Zlength contents) contents) key V) as UPD'.
      destruct UPD'; inversion H0; clear H0. subst z l1 l2. 
      assert (RI: 1 >? reseed_interval = false).
      { apply Zgt_is_gt_bool_f. simpl in Hreseed_interval. destruct Hreseed_interval. lia. }
      destruct prediction_resistance.
      * simpl in HeqMGen'. rewrite RI in *.
        remember (HMAC_DRBG_generate_helper_Z HMAC256 l4 l5 out_len) as GH.
        destruct GH. subst MGen'. subst Gen. simpl. 
        (*apply andp_right. apply prop_right; trivial. cancel.
        unfold AREP, REP. Exists Info. *)
        Exists ((mc1, (mc2, mc3)),
           (map Vubyte (HMAC256 l1 (HMAC256 (l1 ++ [Byte.zero]) l4)),
              (Vint (Int.repr 2), (Vint (Int.repr entropy_len), (Vtrue, Vint (Int.repr reseed_interval)))))).
        unfold hmac256drbgstate_md_info_pointer; simpl. entailer!.
        { destruct WFI as [WFI1 [WFI2 [WFI3 WFI4]]]. red in WFI3; simpl in *; repeat split; simpl; trivial; try lia.
           apply hmac_common_lemmas.HMAC_Zlength. 
           apply hmac_common_lemmas.HMAC_Zlength.  } 
        rewrite sublist_firstn. cancel.
        unfold_data_at 3%nat. cancel. 
        subst HLP. simpl in *.
        unfold HMAC_DRBG_update in HeqUPD, HeqUPD'.
        remember (l3 ++ contents_with_add additional (Zlength contents) contents).
        destruct l6; inv HeqUPD'.
        ++ symmetry in Heql6. apply app_eq_nil in Heql6. destruct Heql6; subst l3.
           unfold get_entropy in HeqENT. apply get_bytes_length in HeqENT. simpl in HeqENT. exfalso. clear - HeqENT H3.
           symmetry in HeqENT.  apply Z2Nat_inj_0 in HeqENT. lia. lia. 
        ++ assert (CONT: contents_with_add additional 0 contents = []).
           { unfold contents_with_add; simpl. rewrite andb_false_r; trivial. }
           rewrite CONT in *. inv HeqUPD. 
           rewrite <- HeqGH; simpl. cancel.
      * rewrite orb_false_l in Heqsr. 
        simpl in HeqMGen'. simpl in *. (*subst reseed_interval.*) rewrite <- Heqsr, ZLa, <- HeqENT, <- HeqUPD' in HeqMGen'.
        simpl in HeqMGen'. rewrite RI in *.
        remember (HMAC_DRBG_generate_helper_Z HMAC256 l4 l5 out_len) as GH.
        destruct GH. subst MGen'. subst Gen. simpl. Intros.
        Exists ((mc1, (mc2, mc3)),
           (map Vubyte (HMAC256 l1 (HMAC256 (l1 ++ [Byte.zero]) l4)),
              (Vint (Int.repr 2), (Vint (Int.repr entropy_len), (Vfalse, Vint (Int.repr reseed_interval)))))).
        unfold hmac256drbgstate_md_info_pointer; simpl.
        entailer!.
        { destruct WFI as [WFI1 [WFI2 [WFI3 WFI4]]]. red in WFI3; simpl in *; repeat split; simpl; trivial; try lia.
           apply hmac_common_lemmas.HMAC_Zlength.
           apply hmac_common_lemmas.HMAC_Zlength. } 
        rewrite sublist_firstn. cancel.
        simpl in *.
        unfold HMAC_DRBG_update in HeqUPD, HeqUPD'.
        remember (l3 ++ contents_with_add additional (Zlength contents) contents).
        destruct l6; inv HeqUPD'.
        ++ symmetry in Heql6. apply app_eq_nil in Heql6. destruct Heql6; subst l3.
           unfold get_entropy in HeqENT. apply get_bytes_length in HeqENT. simpl in HeqENT. exfalso. clear - HeqENT H3.
           symmetry in HeqENT.  apply Z2Nat_inj_0 in HeqENT. lia. lia.
        ++ assert (CONT: contents_with_add additional 0 contents = []).
           { unfold contents_with_add; simpl. rewrite andb_false_r; trivial. }
           rewrite CONT in *. inv HeqUPD. cancel.
           unfold_data_at 3%nat. cancel. subst HLP; rewrite <- HeqGH; simpl. cancel. 
  + subst should_reseed after_reseed_add_len. symmetry in Heqsr.
    apply orb_false_iff in Heqsr. destruct Heqsr; subst prediction_resistance. simpl in na.
    simpl in H1, H3, H4, H6, Hreseed_counter_in_range.
    subst after_reseed_state_abs.
    unfold mbedtls_HMAC256_DRBG_reseed_function, HMAC256_DRBG_reseed_function, DRBG_reseed_function in MRES.
    remember MRES as MRES'. subst MRES.
    subst contents'. rewrite andb_negb_r, ZLa in HeqMRES'.
    remember (get_entropy 32(*256*) entropy_len entropy_len false s) as ENT.
    destruct ENT.
    - subst MRES'. 
      remember  MGen as MGen'. subst MGen.
Transparent mbedtls_HMAC256_DRBG_generate_function.
Transparent HMAC256_DRBG_generate_function.
      unfold mbedtls_HMAC256_DRBG_generate_function, HMAC256_DRBG_generate_function, DRBG_generate_function in HeqMGen'.
Opaque mbedtls_HMAC256_DRBG_generate_function.
Opaque HMAC256_DRBG_generate_function.
      rewrite Hout_lenb, F32, ZLa, andb_negb_r in HeqMGen'.
      unfold DRBG_generate_function_helper in HeqMGen'. simpl in HeqMGen'.
      simpl in *. (*subst reseed_interval. *) rewrite H0 in HeqMGen'.
      remember (contents_with_add additional (Zlength contents) contents) as CONT.
      subst HLP. 
(*      unfold AREP, REP. Exists Info.*)
      destruct CONT.
      * (*clear C' ZLc'.*) subst stream1. 
        rewrite Zlength_nil, <- HeqENT(*, F*) in HeqMGen'. simpl in HeqMGen'.
        remember (HMAC_DRBG_generate_helper_Z HMAC256 key V out_len) as p. destruct p.
        remember (HMAC_DRBG_update HMAC256 [] key l2) as q. destruct q.
        subst MGen'. subst Gen.
        Exists (mc1, (mc2, mc3),
             (map Vubyte (HMAC256 l2 (HMAC256 (l2 ++ [Byte.zero]) key)),
             (Vint (Int.repr (reseed_counter + 1)),
             (Vint (Int.repr entropy_len),
             (Vfalse, Vint (Int.repr reseed_interval)))))).
        unfold contents_with_add in HeqCONT.
        destruct (eq_dec (Zlength contents) 0); simpl in HeqCONT. 
        ++ rewrite e in *. rewrite (Zlength_nil_inv _ e) in *.
           simpl in na. destruct (EqDec_Z (Zlength contents) 0); try solve [lia]; simpl in na.
           subst na; rewrite andb_false_r in *. 
           assert (F: (negb (EqDec_val additional nullval) &&
                            false)%bool = false).
           { rewrite andb_false_r. trivial. }
           subst after_update_state_abs; rewrite F in *.
           inv HeqAUSA. simpl.  
           rewrite hmac_common_lemmas.HMAC_Zlength.
           inv Heqq. inv HeqUPD.
           unfold hmac256drbgstate_md_info_pointer; simpl in *. entailer!. 
           { destruct WFI as [WFI1 [WFI2 [WFI3 WFI4]]]. red in Hreseed_interval. red in WFI3; simpl in *; repeat split; simpl; trivial; try lia.
             apply hmac_common_lemmas.HMAC_Zlength. }
           { destruct WFI as [WFI1 [WFI2 [WFI3 WFI4]]]. red in Hreseed_interval.
           rewrite <- Heqp, sublist_firstn; simpl. cancel.
           unfold_data_at 1%nat. cancel.
           }
        ++ destruct (EqDec_val additional nullval); simpl in na, HeqCONT.
           2: subst contents; elim n; apply Zlength_nil.
           subst na. simpl in *.
           inv HeqUPD. inv HeqAUSA. inv Heqq.
           apply andp_right. { apply prop_right; trivial. }
           rewrite hmac_common_lemmas.HMAC_Zlength. 
           entailer!.
           { destruct WFI as [WFI1 [WFI2 [WFI3 WFI4]]]. red in Hreseed_interval. red in WFI3; simpl in *; repeat split; simpl; trivial; try lia. 
             apply hmac_common_lemmas.HMAC_Zlength. }
           rewrite sublist_firstn, <- Heqp; simpl. cancel.
           unfold_data_at 1%nat. cancel.
     * unfold contents_with_add in HeqCONT.
       remember ((negb (eq_dec additional nullval) && negb (eq_dec (Zlength contents) 0))%bool) as f.
       destruct f; try discriminate. symmetry in Heqf; apply andb_true_iff in Heqf.
       destruct Heqf as [Heqf1 Heqf2]. apply negb_true_iff in Heqf1. apply negb_true_iff in Heqf2.
       destruct (eq_dec additional nullval); try discriminate.
       destruct (eq_dec (Zlength contents) 0); try discriminate.
       destruct (EqDec_val additional nullval). { subst additional. elim n; trivial. }
       destruct (EqDec_Z (Zlength contents) 0); simpl in na. { lia. }
       subst na. simpl in HeqAUSA.
       Exists (mc1, (mc2, mc3),
             (map Vubyte l0,
             (Vint (Int.repr (reseed_counter + 1)),
             (Vint (Int.repr entropy_len),
             (Vfalse, Vint (Int.repr reseed_interval)))))).
       unfold HMAC256_DRBG_update in *. subst stream1 contents.
       rename i0 into z.
       remember (HMAC_DRBG_update HMAC256 (z::CONT) key V) as p; destruct p. inv HeqAUSA.
       remember (HMAC_DRBG_generate_helper_Z HMAC256 l2 l3 out_len) as w; destruct w.
       simpl in HeqUPD. inv HeqUPD. 
       remember (HMAC_DRBG_update HMAC256 (z :: CONT) l2 l4) as q; destruct q.
       subst Gen. 
       apply andp_right. apply prop_right. repeat split; trivial.
       simpl. 
       rewrite sublist_firstn. cancel.
       unfold HMAC_DRBG_update in Heqq. inv Heqq. simpl. entailer!.
       { destruct WFI as [WFI1 [WFI2 [WFI3 WFI4]]]. red in Hreseed_interval. red in WFI3; simpl in *; repeat split; simpl; trivial; try lia.
         apply hmac_common_lemmas.HMAC_Zlength.
         apply hmac_common_lemmas.HMAC_Zlength. }
       unfold_data_at 1%nat. cancel.
  - subst HLP MRES'.  
      remember  MGen as MGen'. subst MGen.
Transparent mbedtls_HMAC256_DRBG_generate_function.
Transparent HMAC256_DRBG_generate_function.
      unfold mbedtls_HMAC256_DRBG_generate_function, HMAC256_DRBG_generate_function, DRBG_generate_function in HeqMGen'.
Opaque mbedtls_HMAC256_DRBG_generate_function.
Opaque HMAC256_DRBG_generate_function.
      rewrite Hout_lenb, (*F,*) ZLa, andb_negb_r in HeqMGen'.
      unfold DRBG_generate_function_helper in HeqMGen'. simpl in HeqMGen'.
      simpl in *. (*subst reseed_interval.*) rewrite H0 in HeqMGen'.
      remember (contents_with_add additional (Zlength contents) contents) as CONT.
(*      unfold AREP, REP. Exists Info.*)
      destruct CONT.
      * (*clear C' ZLc'.*) subst stream1. 
        rewrite Zlength_nil, <- HeqENT(*, F*) in HeqMGen'. simpl in HeqMGen'.
        remember (HMAC_DRBG_generate_helper_Z HMAC256 key V out_len) as p. destruct p.
        remember (HMAC_DRBG_update HMAC256 [] key l2) as q. destruct q.
        Exists (mc1, (mc2, mc3),
             (map Vubyte (HMAC256 l1 (HMAC256 (l1 ++ [Byte.zero]) key)),
             (Vint (Int.repr (reseed_counter + 1)),
             (Vint (Int.repr entropy_len),
             (Vfalse, Vint (Int.repr reseed_interval)))))).
        subst MGen'. subst Gen.
        unfold contents_with_add in HeqCONT.
        destruct (eq_dec (Zlength contents) 0); simpl in HeqCONT. 
        ++ rewrite e0 in *. rewrite (Zlength_nil_inv _ e0) in *.
           simpl in na. destruct (EqDec_Z (Zlength contents) 0); try solve [lia]; simpl in na.
           subst na; rewrite andb_false_r in *. 
           assert (F: (negb (EqDec_val additional nullval) &&
                            false)%bool = false).
           { rewrite andb_false_r. trivial. }
           subst after_update_state_abs; rewrite F in *.
           inv HeqAUSA. simpl.  
           rewrite hmac_common_lemmas.HMAC_Zlength.
           inv Heqq. inv HeqUPD.
           unfold hmac256drbgstate_md_info_pointer; simpl in *. entailer!. 
           { destruct WFI as [WFI1 [WFI2 [WFI3 WFI4]]]. red in Hreseed_interval. red in WFI3; simpl in *; repeat split; simpl; trivial; try lia.
             apply hmac_common_lemmas.HMAC_Zlength. }
           rewrite <- Heqp, sublist_firstn; simpl. cancel.
           unfold_data_at 1%nat. cancel.
        ++ destruct (EqDec_val additional nullval); simpl in na, HeqCONT.
           2: subst contents; elim n; apply Zlength_nil.
           subst na. simpl in *.
           inv HeqUPD. inv HeqAUSA. inv Heqq.
           apply andp_right. apply prop_right. repeat split; trivial.
           rewrite hmac_common_lemmas.HMAC_Zlength. 
           entailer!.
           { destruct WFI as [WFI1 [WFI2 [WFI3 WFI4]]]. red in Hreseed_interval. red in WFI3; simpl in *; repeat split; simpl; trivial; try lia. 
             apply hmac_common_lemmas.HMAC_Zlength. }
           rewrite sublist_firstn, <- Heqp; simpl. cancel.
           unfold_data_at 1%nat. cancel.
     * unfold contents_with_add in HeqCONT.
       remember ((negb (eq_dec additional nullval) && negb (eq_dec (Zlength contents) 0))%bool) as f.
       destruct f; try discriminate. symmetry in Heqf; apply andb_true_iff in Heqf.
       destruct Heqf as [Heqf1 Heqf2]. apply negb_true_iff in Heqf1. apply negb_true_iff in Heqf2.
       destruct (eq_dec additional nullval); try discriminate.
       destruct (eq_dec (Zlength contents) 0); try discriminate.
       destruct (EqDec_val additional nullval). { subst additional. elim n; trivial. }
       destruct (EqDec_Z (Zlength contents) 0); simpl in na. { lia. }
       subst na. simpl in HeqAUSA.
       Exists (mc1, (mc2, mc3),
             (map Vubyte l0,
             (Vint (Int.repr (reseed_counter + 1)),
             (Vint (Int.repr entropy_len),
             (Vfalse, Vint (Int.repr reseed_interval)))))).
       unfold HMAC256_DRBG_update in *. subst stream1 contents.
       rename i0 into z.
       remember (HMAC_DRBG_update HMAC256 (z::CONT) key V) as p; destruct p. inv HeqAUSA.
       remember (HMAC_DRBG_generate_helper_Z HMAC256 l1 l2 out_len) as w; destruct w.
       simpl in HeqUPD. inv HeqUPD. 
       remember (HMAC_DRBG_update HMAC256 (z :: CONT) l1 l3) as q; destruct q.
       subst Gen. 
       apply andp_right. apply prop_right. repeat split; trivial.
       simpl. 
       rewrite sublist_firstn. cancel.
       unfold HMAC_DRBG_update in Heqq. inv Heqq. simpl. entailer!.
       { destruct WFI as [WFI1 [WFI2 [WFI3 WFI4]]]. red in Hreseed_interval. red in WFI3; simpl in *; repeat split; simpl; trivial; try lia. 
         apply hmac_common_lemmas.HMAC_Zlength.
         apply hmac_common_lemmas.HMAC_Zlength. }
       unfold_data_at 1%nat. cancel.
Time Qed. (*laptop 11s, desktop25s*) 

Opaque mbedtls_HMAC256_DRBG_reseed_function.
Opaque mbedtls_HMAC256_DRBG_generate_function.

Lemma loopbody_explicit (StreamAdd:list mpred) : forall (Espec : OracleKind)
(contents : list byte)
(additional : val)
(add_len : Z)
(output : val) (sho: share)
(out_len : Z)
(b : block) (i : ptrofs) (shc: share)
(mc1 mc2 mc3 : val)
(key V : list byte)
(reseed_counter entropy_len : Z)
(prediction_resistance : bool)
(reseed_interval : Z)
(gv: globals)
(Info : md_info_state)
(s : ENTROPY.stream)
(*Delta_specs := abbreviate : PTree.t funspec*)
(Haddlen : 0 <= add_len <= Int.max_unsigned)
(Houtlen : 0 <= out_len <= Int.max_unsigned)
(LengthV : Zlength V = 32)
(AddLenC : add_len = Zlength contents)
(Hent_len_nonneg : 0 < entropy_len)
(Hentlen : entropy_len + Zlength contents <= 384)
(Hreseed_interval : RI_range reseed_interval)
(Hreseed_counter_in_range : 0 <= reseed_counter < Int.max_signed)
(I := (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
       reseed_interval) : hmac256drbgabs)
(initial_state := (mc1, (mc2, mc3),
                 (map Vubyte V,
                 (Vint (Int.repr reseed_counter),
                 (Vint (Int.repr entropy_len),
                 (bool2val prediction_resistance,
                 Vint (Int.repr reseed_interval))))))
              : mdstate * (list val * (val * (val * (val * val)))))
(PNadditional : is_pointer_or_null additional)
(Pmc1 : isptr mc1)
(Hout_len : 0 <= out_len <= 1024)
(Hout_lenb : (out_len >? 1024) = false)
(Hadd_len : 0 <= add_len <= 256)
(Hadd_lenb : (add_len >? 256) = false)
(contents' := contents_with_add additional add_len contents : list byte)
(ZLa : (Zlength contents' >? 256) = false)
(should_reseed := (prediction_resistance
                  || (reseed_counter >? reseed_interval))%bool : bool)
(after_reseed_add_len := if should_reseed then 0 else add_len : Z)
(C' : contents' = [] \/ contents' = contents)
(ZLc' : Zlength contents' = 0 \/ Zlength contents' = Zlength contents)
(*(stream1 : ENTROPY.stream)*)
(na := (negb (eq_dec additional nullval) &&
       negb (eq_dec (if should_reseed then 0 else Zlength contents) 0))%bool
   : bool)
(*Delta := abbreviate : tycontext*)
(after_reseed_state_abs := if should_reseed
                          then
                           hmac256drbgabs_reseed I s
                             (contents_with_add additional add_len contents)
                          else I : hmac256drbgabs)
(ZLength_ARSA_val : Zlength (hmac256drbgabs_value after_reseed_state_abs) = 32)
(after_update_state_abs := if na
                          then hmac256drbgabs_hmac_drbg_update I contents
                          else after_reseed_state_abs : hmac256drbgabs)
(AUV := hmac256drbgabs_value after_update_state_abs : list byte)
(ZLength_AUSA_val : Zlength AUV = 32)
(*(TR : mkSTREAM1 (prediction_resistance || (reseed_counter >? reseed_interval))
       s key V reseed_counter entropy_len prediction_resistance
       reseed_interval additional contents stream1)*)
(*(StreamAdd := abbreviate : list mpred)*)
(Poutput : isptr output)
(AUK := hmac256drbgabs_key after_update_state_abs : list byte)
(HLP := HMAC_DRBG_generate_helper_Z HMAC256 AUK AUV : Z -> list byte * list byte)
(done : Z)
(HRE : Int.repr (out_len - done) <> Int.repr 0)
(H : 0 <= done <= out_len)
(H0 : is_multiple done 32 \/ done = out_len)
(Hsho: writable_share sho)
(Hshc: writable_share shc)
(WFI : drbg_protocol_specs.WF
        (HMAC256DRBGabs key V reseed_counter entropy_len
           prediction_resistance reseed_interval)),
@semax hmac_drbg_compspecs.CompSpecs Espec
     (func_tycontext f_mbedtls_hmac_drbg_random_with_add HmacDrbgVarSpecs
        HmacDrbgFunSpecs nil)
  (PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (bool2val prediction_resistance);
   temp _out (offset_val done output);
   temp _left (Vint (Int.repr (out_len - done))); temp _ctx (Vptr b i);
   temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvars gv)
   SEP (hmac256drbgabs_common_mpreds shc
          (hmac256drbgabs_update_value after_update_state_abs
             (fst (HLP done))) initial_state (Vptr b i) Info; FRZL StreamAdd;
   data_at sho (tarray tuchar out_len)
     (map Vubyte (sublist 0 done (snd (HLP done))) ++
      repeat Vundef (Z.to_nat (out_len - done))) output; K_vector gv))
  (Ssequence
     (Ssequence
        (Sifthenelse
           (Ebinop Ogt (Etempvar _left tuint) (Etempvar _md_len tuint) tint)
           (Sset _t'6 (Ecast (Etempvar _md_len tuint) tuint))
           (Sset _t'6 (Ecast (Etempvar _left tuint) tuint)))
        (Sset _use_len (Etempvar _t'6 tuint)))
     (Ssequence
        (Scall None
           (Evar _mbedtls_md_hmac_reset
              (Tfunction [tptr (Tstruct _mbedtls_md_context_t noattr)]
                 tint cc_default))
           [Eaddrof
              (Efield
                 (Ederef
                    (Etempvar _ctx
                       (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                    (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
                 (Tstruct _mbedtls_md_context_t noattr))
              (tptr (Tstruct _mbedtls_md_context_t noattr))])
        (Ssequence
           (Scall None
              (Evar _mbedtls_md_hmac_update
                 (Tfunction [tptr (Tstruct _mbedtls_md_context_t noattr);
                             tptr tuchar; tuint] tint
                    cc_default))
              [Eaddrof
                 (Efield
                    (Ederef
                       (Etempvar _ctx
                          (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                       (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
                    (Tstruct _mbedtls_md_context_t noattr))
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
                    (Tfunction [tptr (Tstruct _mbedtls_md_context_t noattr);
                                 tptr tuchar] tint cc_default))
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
                   (tarray tuchar 32)])
              (Ssequence
                 (Scall None
                    (Evar _memcpy
                       (Tfunction [tptr tvoid; tptr tvoid; tuint] (tptr tvoid) cc_default))
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
                       (Ebinop Osub (Etempvar _left tuint)
                          (Etempvar _use_len tuint) tuint))))))))
  (normal_ret_assert
     (EX a : Z,
      PROP (0 <= a <= out_len; is_multiple a 32 \/ a = out_len)
      LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (bool2val prediction_resistance);
      temp _out (offset_val a output);
      temp _left (Vint (Int.repr (out_len - a))); temp _ctx (Vptr b i);
      temp _p_rng (Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
      gvars gv)
      SEP (hmac256drbgabs_common_mpreds shc
             (hmac256drbgabs_update_value after_update_state_abs
                (fst (HLP a))) initial_state (Vptr b i) Info; FRZL StreamAdd;
      data_at sho (tarray tuchar out_len)
        (map Vubyte (sublist 0 a (snd (HLP a))) ++
         repeat Vundef (Z.to_nat (out_len - a))) output; K_vector gv))%assert
(*
     (overridePost
        (EX a : Z,
         PROP (typed_false tint
                 (bool2val
                    (negb (Int.eq (Int.repr (out_len - a)) (Int.repr 0))));
         0 <= a <= out_len; is_multiple a 32 \/ a = out_len)
         LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
         temp _reseed_interval (Vint (Int.repr reseed_interval));
         temp _reseed_counter (Vint (Int.repr reseed_counter));
         temp _prediction_resistance (bool2val prediction_resistance);
         temp _out (offset_val a output);
         temp _left (Vint (Int.repr (out_len - a))); temp _ctx (Vptr b i);
         temp _p_rng (Vptr b i); temp _output output;
         temp _out_len (Vint (Int.repr out_len));
         temp _additional additional;
         temp _add_len (Vint (Int.repr after_reseed_add_len));
         gvar sha._K256 kv)
         SEP (hmac256drbgabs_common_mpreds
                (hmac256drbgabs_update_value after_update_state_abs
                   (fst (HLP a))) initial_state (Vptr b i) Info;
         FRZL StreamAdd;
         data_at Tsh (tarray tuchar out_len)
           (map Vint (map Int.repr (sublist 0 a (snd (HLP a)))) ++
            repeat Vundef (Z.to_nat (out_len - a))) output; K_vector kv))%assert
        (function_body_ret_assert tint
           (fun a : environ =>
            EX x : val,
            (PROP ( )
             LOCAL (temp ret_temp x)
             SEP (!! return_value_relate_result
                       (mbedtls_HMAC256_DRBG_generate_function s I out_len
                          contents') x &&
                  (match
                     mbedtls_HMAC256_DRBG_generate_function s I out_len
                       contents'
                   with
                   | ENTROPY.success (bytes, _) _ =>
                       data_at Tsh (tarray tuchar out_len)
                         (map Vint (map Int.repr bytes)) output
                   | ENTROPY.error _ _ =>
                       data_at_ Tsh (tarray tuchar out_len) output
                   end *
                   hmac256drbgabs_common_mpreds
                     (hmac256drbgabs_generate I s out_len contents')
                     initial_state (Vptr b i) Info *
                   da_emp Tsh (tarray tuchar add_len)
                     (map Vint (map Int.repr contents)) additional *
                   Stream
                     (get_stream_result
                        (mbedtls_HMAC256_DRBG_generate_function s I out_len
                           contents')) * K_vector kv))) a)))
*)).
Proof. intros.
    rename H into Hdone.
    destruct H0 as [Hmultiple | Hcontra]; [| subst done; elim HRE; f_equal; lia].
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
    unfold_data_at 1%nat.
    
    freeze [2;3;4;5] FR_unused_struct_fields.
    freeze [0;3;5] FR1.

    rewrite (field_at_data_at _ _ [StructField _md_ctx]).
    rewrite (field_at_data_at _ _ [StructField _V]).

    unfold hmac256drbg_relate. subst I.

    destruct after_update_state_abs.
    unfold hmac256drbgabs_update_value.
(*    rewrite Heqinitial_state.*)
    unfold hmac256drbgabs_to_state.
(*    rewrite Heqafter_update_key.*)
    simpl in AUV, AUK. subst AUV AUK.
    unfold md_full. subst initial_state.
    cbv beta iota zeta.
    normalize. 

    (* size_t use_len = left > md_len ? md_len : left; *)
    forward_if (temp _t'6 (Vint (Int.repr (Z.min (Z.of_nat SHA256.DigestLength) (out_len - done))))).
    {
      (* md_len < left *)
      forward.
      entailer!.
      rewrite Z.min_l; [reflexivity | simpl; lia].
    }
    {
      (* md_len >= left *)
      forward.
      entailer!.
      rewrite Z.min_r; [reflexivity | simpl; lia].
    }
    forward.

    (* mbedtls_md_hmac_reset( &ctx->md_ctx ); *)
    assert_PROP (field_compatible (Tarray tuchar 32 noattr) 
          []
          (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))) as FC_V by entailer!.
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st
         [StructField _md_ctx] (Vptr b i)) as FC_M by entailer.
    forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] (*ctx*)(Vptr b i),  (*md_ctx'*)(mc1,(mc2,mc3)), shc, key0, gv).
    { unfold md_full; simpl. cancel. }
    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    rename H into HZlength_V.  
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st [StructField _V] (Vptr b i)) as FCV by entailer!.

    forward_call (key0, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] (*ctx*)(Vptr b i),
                  (*md_ctx'*)(mc1,(mc2,mc3)), shc, 
                  field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i), shc, 
                  @nil byte, (fst (HLP done)), gv).

    { apply prop_right. rewrite HZlength_V, field_address_offset; simpl; trivial. f_equal.
      unfold field_address. rewrite if_true; trivial.
    }
    { simpl; simpl in HZlength_V; rewrite HZlength_V (*, <- Hmultiple*).
      cancel.
    }
    { simpl; simpl in HZlength_V; rewrite HZlength_V.
      compute; reflexivity. 
    }

    (*Intros vret; subst vret.*)
    rewrite app_nil_l.

    replace_SEP 2 (memory_block shc 32 (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))).
    { 
      entailer!.
      simpl in HZlength_V.
      unfold hmac256drbgabs_value.
      rewrite HZlength_V.
      apply data_at_memory_block.
    }

    (* mbedtls_md_hmac_finish( &ctx->md_ctx, ctx->V ); *)
    forward_call ((fst(HLP done)), key0, 
               field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] (*ctx*)(Vptr b i), 
               (*md_ctx'*)(mc1, (mc2, mc3)), shc,
               field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i), shc, gv).
    {
      rewrite <- memory_block_data_at_ by trivial. cancel.
    }
    assert_PROP (field_compatible (tarray tuchar out_len) [] output) as
        Hfield_compat_output by entailer!.
    replace_SEP 5 (
        data_at sho (tarray tuchar done) (map Vubyte (sublist 0 done (snd (HLP done)))) output *
        data_at sho (tarray tuchar (out_len - done)) (repeat Vundef (Z.to_nat (out_len - done))) (offset_val done output)
    ).
    {
      entailer!.
      apply derives_refl'.

      assert (HZlength1: Zlength (map Vubyte (sublist 0 (n * 32)%Z (snd (HLP (n * 32)%Z)))) = (n * 32)%Z).
      {
        rewrite Zlength_map.
        rewrite Zlength_sublist; [lia|lia|]. subst HLP.
        rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; auto; try lia.
        apply hmac_common_lemmas.HMAC_Zlength.
        exists n; reflexivity.
      }
      
      apply data_at_complete_split; try rewrite HZlength1; try rewrite Zlength_repeat; auto; try lia.
      (*simpl. simpl in HZlength1. rewrite HZlength1.*)
      replace ((n * 32)%Z + (out_len - (n * 32)%Z)) with out_len by lia. assumption.
    }
    normalize.
    
    remember (offset_val done output) as done_output.
    remember (Z.min 32 (out_len - done)) as use_len.
    assert_PROP (field_compatible (tarray tuchar (out_len - done)) [] done_output) as Hfield_compat_done_output.
    {
      clear Heqdone_output Hmultiple.
      entailer!.
    }
    Intros.
    replace_SEP 6 (
        data_at sho (tarray tuchar use_len) (repeat Vundef (Z.to_nat use_len)) done_output *
        data_at sho (tarray tuchar (out_len - done - use_len)) (repeat Vundef (Z.to_nat (out_len - done - use_len))) (offset_val use_len done_output)
    ).
    { 
      clear Hmultiple Heqdone_output.
      entailer!. 
      apply derives_refl'.
      rewrite Zmin_spec.
      if_tac.
      { apply data_at_complete_split; repeat rewrite Zlength_repeat; auto; try lia.
        replace (32 + (out_len - done - 32)) with (out_len - done) by lia; assumption.
        rewrite <- repeat_app.
        rewrite <- Z2Nat.inj_add; try lia.
        replace (32 + (out_len - done - 32)) with (out_len - done) by lia; reflexivity.
      }
      {
        apply data_at_complete_split; repeat rewrite Zlength_repeat; auto; try lia.
        replace (out_len - done + (out_len - done - (out_len - done))) with (out_len - done) by lia; assumption.
        replace (out_len - done - (out_len - done)) with 0 by lia; simpl; rewrite app_nil_r; reflexivity.
      }
    }
    Intros.

    replace_SEP 6 (memory_block sho use_len done_output).
    {
      clear Hmultiple.
      entailer!.
      eapply derives_trans; [apply data_at_memory_block|].
      replace (sizeof (*cenv_cs*) (tarray tuchar (Z.min 32 (out_len - done)))) with (Z.min 32 (out_len - done)).
      apply derives_refl.
      simpl.
      destruct (Z.min_dec 32 (out_len - done));
      rewrite Zmax0r; lia.
    }
    set (H256 := HMAC256 (fst (HLP done)) key0) in *.
    assert (ZL_H256: Zlength H256 = 32).
    { subst H256. apply hmac_common_lemmas.HMAC_Zlength. }
    replace_SEP 3 (data_at shc (tarray tuchar use_len)
                      (sublist 0 use_len (map Vubyte H256))
                      (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i)) *
                   data_at shc (tarray tuchar (32 - use_len))
                      (sublist use_len 32 (map Vubyte (H256)))
                      (offset_val use_len (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i)))).
    {
      clear Hmultiple.
      entailer!.
      apply derives_refl'.
      remember (fst (HLP done)) as V0'; clear HeqV0'.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try lia.
        rewrite sublist_nil.
        rewrite app_nil_r.
        symmetry; apply sublist_same.
        reflexivity.
        repeat rewrite Zlength_map; rewrite ZL_H256; reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try lia.
        replace (out_len - done - 0 + (32 - (out_len - done))) with 32 by lia; auto.
        rewrite sublist_rejoin; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try lia.
        rewrite sublist_same; try reflexivity; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try lia.
      }
    }
    (* memcpy( out, ctx->V, use_len ); *)
    forward_call ((shc, sho), done_output, 
                  field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i), 
                  use_len,
                  sublist 0 use_len (map Int.repr (map Byte.unsigned H256))).
    { apply prop_right. subst; simpl. rewrite field_address_offset; trivial. } 
    { entailer!. simpl. rewrite !sublist_map, !map_map. cancel. }

    simpl.
    gather_SEP (data_at _ _ _ (field_address _ [StructField _V] _)) 
                      (data_at _ _ _ (offset_val _ (field_address _ [StructField _V] _))).
    replace_SEP 0 (data_at shc (tarray tuchar 32) (map Vubyte H256)
                               (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))).
    {
      (*clear Hmultiple.*)
      entailer!.
      apply derives_refl'. 
      rewrite <- sublist_map.
      remember (fst (HLP (n*32)%Z)) as V0'; clear HeqV0'.
      symmetry.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - (*done*)(n*32)%Z)) as [Hmin | Hmin].
      { clear - Hmin ZL_H256 Hdone FC_V.
        rewrite zlt_true by assumption. simpl.
        rewrite sublist_same; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try lia.
        remember (map Vubyte (HMAC256 V0' key0)) as data.
        apply data_at_complete_split; subst data; autorewrite with sublist; 
        repeat rewrite Zlength_map; try rewrite ZL_H256, Zlength_nil; autorewrite with sublist; auto; try lia.
        rewrite ZL_H256. auto. 
        unfold Vubyte. rewrite !map_map. reflexivity.
      }
      {
        rewrite zlt_false by assumption.
        remember (sublist 0 (out_len - (*done*)(n*32)%Z) (map Vubyte (HMAC256 V0' key0))) as data_left.
        remember (sublist (out_len - (*done*)(n*32)%Z) 32
        (map Vubyte (HMAC256 V0' key0))) as data_right.
        apply data_at_complete_split; subst data_left data_right; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try lia.
        autorewrite with sublist.
        replace (out_len - (*done*)(n*32)%Z + (32 - (out_len - (*done*)(n*32)%Z))) with 32 by lia; auto.
        list_solve.
        unfold Vubyte.
        rewrite !sublist_map, !map_map. rewrite <- map_app. f_equal.
        rewrite sublist_rejoin; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try lia.
        rewrite sublist_same; try reflexivity; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try lia.
      }
    }

    gather_SEP  (data_at sho (tarray tuchar use_len) _ _)
                       (data_at sho (tarray tuchar (out_len - _ - _)) _ _).
    replace_SEP 0 (data_at sho (tarray tuchar (out_len - done)) 
         ( (map Vubyte (sublist 0 use_len H256))
           ++ (repeat Vundef (Z.to_nat (out_len - done - use_len))))
         done_output).
    {
      (*clear Heqdone_output Hmultiple*)
      entailer!.
      apply derives_refl'.
      rewrite Zmin_spec in *.
      symmetry.
      if_tac.
      { 
        erewrite ( data_at_complete_split
                           (map Vint (sublist 0 32 (map Int.repr (map Byte.unsigned H256))))
                           (repeat Vundef (Z.to_nat (out_len - n * 32 - 32)))); try reflexivity.
        2: autorewrite with sublist; replace (_ + _) with (out_len - n*32) by lia; solve [auto].
        2: autorewrite with sublist; lia.
        2: f_equal; autorewrite with sublist; rewrite !map_map; reflexivity.
        autorewrite with sublist; rewrite ZL_H256, offset_offset_val; reflexivity. 
      }
      { 
        rewrite !sublist_map. rewrite !map_map. 
        erewrite (data_at_complete_split 
            (map (fun x : byte => Vint (Int.repr (Byte.unsigned x))) (sublist 0 (out_len - n * 32) H256))
            (repeat Vundef (Z.to_nat (out_len - n * 32 - (out_len - n * 32))))).
        3: reflexivity. 3: reflexivity. 4: reflexivity.
        + rewrite Zlength_map, Zlength_sublist, Zlength_repeat, Z.sub_0_r, offset_offset_val; try lia.
          trivial.
        + rewrite Zlength_map, Zlength_sublist, Zlength_repeat, Zminus_diag, Z.sub_0_r, Z.add_0_r; try lia. trivial.
        + rewrite Zlength_map, Zlength_sublist, Zlength_repeat; try lia.
        + unfold Vubyte. f_equal.
      }
    }

    gather_SEP (data_at sho (tarray tuchar (n*32)) _ _) (data_at sho (tarray tuchar (out_len - done)) _ _).
    replace_SEP 0 (
                  data_at sho (tarray tuchar out_len) 
                    ((map Vubyte (sublist 0 done (snd (HLP done)))) ++
                     (map Vubyte (sublist 0 use_len H256) ++
                      repeat Vundef (Z.to_nat (out_len - done - use_len)))) output).
    {
      entailer!.
      apply derives_refl'.
      symmetry.
      assert (HZlength1: Zlength ((snd (HLP (n * 32)%Z))) = (n * 32)%Z).
      { subst HLP.
        rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; auto; try lia.
        apply hmac_common_lemmas.HMAC_Zlength.
        exists n; reflexivity.
      }
      rewrite Zmin_spec. simpl in *.
      if_tac.
      apply data_at_complete_split;
      repeat rewrite Zlength_app; repeat rewrite Zlength_map; try rewrite HZlength1; repeat rewrite Zlength_repeat; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try lia;
      try rewrite HZlength_V.
      replace ((n * 32)%Z - 0 + (32 - 0 + (out_len - (n * 32)%Z - 32))) with out_len by lia;
      assumption. 
      replace ((n * 32)%Z - 0 + (out_len - (n * 32)%Z - 0 + (out_len - (n * 32)%Z - (out_len - (n * 32)%Z)))) with out_len by lia.
      apply data_at_complete_split;
      repeat rewrite Zlength_app; repeat rewrite Zlength_map; try rewrite HZlength1; repeat rewrite Zlength_repeat; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try lia;
      try rewrite HZlength_V.
      replace (n * 32 - 0 + (out_len - n * 32 - 0 + (out_len - n * 32 - (out_len - n * 32)))) with
         out_len by lia.
      assumption.
    }

    (* out += use_len; *)
    forward.

    (* left -= use_len; *)
    forward.
    { 
      go_lower.
      Exists (done + use_len).
      unfold hmac256drbgabs_common_mpreds; normalize.

      unfold_data_at 4%nat.
      rewrite (field_at_data_at _ _ [StructField _md_ctx]);
      rewrite (field_at_data_at _ _ [StructField _V]).
    
      unfold md_full.
    
      thaw FR1.
      thaw FR_unused_struct_fields.
      assert (DD: 0 <= done + use_len).
      { subst. rewrite Zmin_spec.
        destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; repeat split; try lia. }        
      assert (XX: is_multiple (done + use_len) 32 \/ done + use_len = out_len).
      { subst.
        rewrite Zmin_spec.
        destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; repeat split; try lia.
        left; exists (n + 1); lia. }
      autorewrite with norm.
      apply andp_right.
      { apply prop_right. repeat split; trivial.
        + subst. rewrite Zmin_spec.
          destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; lia.
        + subst done_output. simpl. destruct output; simpl; auto.
            f_equal. autorewrite with norm. 
           assert (0 <= use_len <= 32).
            subst use_len; clear - Hdone DD.
            destruct (Z.min_spec 32 (out_len - done)) as [[? ?]|[? ?]]; lia. 
            f_equal. f_equal. subst use_len. trivial.
        + autorewrite with norm; f_equal; f_equal. lia.
        + subst HLP. apply HMAC_DRBG_generate_helper_Z_Zlength_fst; trivial. apply hmac_common_lemmas.HMAC_Zlength. }

      subst done use_len. cancel. 

      (*Rest as with "ideal proof"*) 
      unfold md_full. simpl. 
      replace H256 with (fst (HLP (n * 32 + Z.min 32 (out_len - n * 32))))%Z.
      rewrite app_assoc.
      replace (map Vubyte
        (
           (sublist 0 (n * 32)%Z
              (snd (HLP (n * 32)%Z)))) ++
        map Vubyte
         (sublist 0 (Z.min 32 (out_len - (n * 32)%Z))
           (
              (fst
                 (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))))) with
       (map Vubyte
        (
           (sublist 0 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))
              (snd
                 (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))))).
      replace (out_len - (n * 32)%Z - Z.min 32 (out_len - (n * 32)%Z)) with (out_len - ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))) by lia.
      cancel. 
      rewrite <- map_app.
      replace (sublist 0 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))
           (snd
              (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))) with (sublist 0 (n * 32)%Z
           (snd (HLP (n * 32)%Z)) ++
         sublist 0 (Z.min 32 (out_len - (n * 32)%Z))
           (fst
              (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))).
      reflexivity.
      replace (snd
              (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z)))) 
      with (snd (HLP (n * 32)%Z) ++ 
            fst (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z)))).
      {
        apply while_loop_post_sublist_app; auto. 
      }
      {
        apply while_loop_post_incremental_snd; auto.
        intros contra; rewrite contra, Zminus_diag in HRE. clear - HRE.
        elim HRE; trivial. 
      }
      {
        apply while_loop_post_incremental_fst; auto.
        intros contra; rewrite contra, Zminus_diag in HRE. clear - HRE.
        elim HRE; trivial. 
      }
    }
Time Qed. (*Coq8.10.1: 8.9s; was: 27s*)

Opaque mbedtls_HMAC256_DRBG_generate_function.

Lemma generate_loopbody: forall (StreamAdd: list mpred)
(Espec : OracleKind)
(contents : list byte)
(additional : val)
(add_len : Z)
(output : val) (sho: share)
(out_len : Z)
(b : block) (i : ptrofs) (shc: share)
(key V : list byte)
(reseed_counter entropy_len : Z)
(prediction_resistance : bool)
(reseed_interval : Z)
(gv : globals)
(s : ENTROPY.stream)
(Haddlen : 0 <= add_len <= Int.max_unsigned)
(Houtlen : 0 <= out_len <= Int.max_unsigned)
(AddLenC : add_len = Zlength contents)
(I := HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
       reseed_interval : hmac256drbgabs)
(Hentlen : hmac256drbgabs_entropy_len I + Zlength contents <= 384)
(Info : md_info_state)
(mc1 mc2 mc3 : val)
(WFI : WF I)
(Hreseed_counter_in_range : 0 <= hmac256drbgabs_reseed_counter I <
                           Int.max_signed)
(Hreseed_interval : RI_range (hmac256drbgabs_reseed_interval I))
(ZlengthV : Zlength V = 32)
(PNadditional : is_pointer_or_null additional)
(a := (mc1, (mc2, mc3),
     (map Vubyte V,
     (Vint (Int.repr reseed_counter),
     (Vint (Int.repr entropy_len),
     (bool2val prediction_resistance, Vint (Int.repr reseed_interval))))))
  : mdstate * (list val * (val * (val * (val * val)))))
(Pmc1 : isptr mc1)
(Hout_len : 0 <= out_len <= 1024)
(Hout_lenb : (out_len >? 1024) = false)
(Hadd_len : 0 <= add_len <= 256)
(Hadd_lenb : (add_len >? 256) = false)
(contents' := contents_with_add additional add_len contents : list byte)
(ZLa : (Zlength contents' >? 256) = false)
(should_reseed := (prediction_resistance
                  || (reseed_counter >? reseed_interval))%bool : bool)
(after_reseed_add_len := if should_reseed then 0 else add_len : Z)
(C' : contents' = [] \/ contents' = contents)
(ZLc' : Zlength contents' = 0 \/ Zlength contents' = Zlength contents)
(na := (negb (eq_dec additional nullval) &&
       negb (eq_dec (if should_reseed then 0 else Zlength contents) 0))%bool
   : bool)
(after_reseed_state_abs := if should_reseed
                          then
                           hmac256drbgabs_reseed I s
                             (contents_with_add additional add_len contents)
                          else I : hmac256drbgabs)
(ZLength_ARSA_val : Zlength (hmac256drbgabs_value after_reseed_state_abs) = 32)
(after_update_state_abs := if na
                          then hmac256drbgabs_hmac_drbg_update I contents
                          else after_reseed_state_abs : hmac256drbgabs)
(AUV := hmac256drbgabs_value after_update_state_abs : list byte)
(ZLength_AUSA_val : Zlength AUV = 32)
(Poutput : isptr output)
(AUK := hmac256drbgabs_key after_update_state_abs : list byte)
(HLP := HMAC_DRBG_generate_helper_Z HMAC256 AUK AUV : Z -> list byte * list byte)
(done : Z)
(HRE : Int.repr (out_len - done) <> Int.repr 0)
(Hsho: writable_share sho)
(Hshc: writable_share shc)
(H : 0 <= done <= out_len)
(H0 : is_multiple done 32 \/ done = out_len),
@semax hmac_drbg_compspecs.CompSpecs Espec
  (func_tycontext f_mbedtls_hmac_drbg_random_with_add HmacDrbgVarSpecs
        HmacDrbgFunSpecs nil)
  (PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (bool2val prediction_resistance);
   temp _out (offset_val done output);
   temp _left (Vint (Int.repr (out_len - done))); temp _ctx (Vptr b i);
   temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvars gv)
   SEP (hmac256drbgabs_common_mpreds shc
          (hmac256drbgabs_update_value after_update_state_abs
             (fst (HLP done))) a (Vptr b i) Info; FRZL StreamAdd;
   data_at sho (tarray tuchar out_len)
     (map Vubyte (sublist 0 done (snd (HLP done))) ++
      repeat Vundef (Z.to_nat (out_len - done))) output; K_vector gv))
  (Ssequence
     (Ssequence
        (Sifthenelse
           (Ebinop Ogt (Etempvar _left tuint) (Etempvar _md_len tuint) tint)
           (Sset _t'6 (Ecast (Etempvar _md_len tuint) tuint))
           (Sset _t'6 (Ecast (Etempvar _left tuint) tuint)))
        (Sset _use_len (Etempvar _t'6 tuint)))
     (Ssequence
        (Scall None
           (Evar _mbedtls_md_hmac_reset
              (Tfunction [tptr (Tstruct _mbedtls_md_context_t noattr)]
                 tint cc_default))
           [Eaddrof
              (Efield
                 (Ederef
                    (Etempvar _ctx
                       (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                    (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
                 (Tstruct _mbedtls_md_context_t noattr))
              (tptr (Tstruct _mbedtls_md_context_t noattr))])
        (Ssequence
           (Scall None
              (Evar _mbedtls_md_hmac_update
                 (Tfunction [tptr (Tstruct _mbedtls_md_context_t noattr);
                             tptr tuchar; tuint] tint
                    cc_default))
              [Eaddrof
                 (Efield
                    (Ederef
                       (Etempvar _ctx
                          (tptr (Tstruct _mbedtls_hmac_drbg_context noattr)))
                       (Tstruct _mbedtls_hmac_drbg_context noattr)) _md_ctx
                    (Tstruct _mbedtls_md_context_t noattr))
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
                    (Tfunction [tptr (Tstruct _mbedtls_md_context_t noattr);
                                tptr tuchar] tint cc_default))
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
                   (tarray tuchar 32)])
              (Ssequence
                 (Scall None
                    (Evar _memcpy
                       (Tfunction[tptr tvoid; tptr tvoid; tuint]
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
                       (Ebinop Osub (Etempvar _left tuint)
                          (Etempvar _use_len tuint) tuint))))))))
  (normal_ret_assert
     (EX a0 : Z,
      PROP (0 <= a0 <= out_len; is_multiple a0 32 \/ a0 = out_len)
      LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (bool2val prediction_resistance);
      temp _out (offset_val a0 output);
      temp _left (Vint (Int.repr (out_len - a0))); temp _ctx (Vptr b i);
      temp _p_rng (Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
      gvars gv)
      SEP (hmac256drbgabs_common_mpreds shc
             (hmac256drbgabs_update_value after_update_state_abs
                (fst (HLP a0))) a (Vptr b i) Info; FRZL StreamAdd;
      data_at sho (tarray tuchar out_len)
        (map Vubyte (sublist 0 a0 (snd (HLP a0))) ++
         repeat Vundef (Z.to_nat (out_len - a0))) output; K_vector gv))%assert).
Proof. intros.
eapply semax_post_flipped'.
apply (loopbody_explicit StreamAdd); try assumption;
    subst I; red in WFI; simpl in *; lia.
apply andp_left2.
go_lowerx.
Time Qed. (*2s*)