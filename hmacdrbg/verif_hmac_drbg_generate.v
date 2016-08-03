Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import floyd.sublist.

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
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.

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

Lemma entailment1: forall (contents : list Z) (additional output : val)
  (out_len : Z) (b : block) (i : int) (mc1 mc2 mc3 : val) (key V : list Z)
  (reseed_counter entropy_len : Z) (prediction_resistance : bool)
  (reseed_interval : Z) (kv : val) (info_contents : md_info_state)
  (s : ENTROPY.stream)
  (initial_state_abs := HMAC256DRBGabs key V reseed_counter entropy_len
                       prediction_resistance reseed_interval : hmac256drbgabs)
  (RI : reseed_interval = 10000)
  (initial_state := (mc1, (mc2, mc3),
                 (map Vint (map Int.repr V),
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
  (F : (0 >? 256) = false)
  (return_value : int)
  (Hrv : negb (Int.eq return_value (Int.repr 0)) = true)
  (Hadd_lenb : (Zlength contents >? 256) = false),
reseedPOST (Vint return_value) contents additional (Zlength contents) s
  initial_state_abs (Vptr b i) info_contents kv initial_state *
data_at_ Tsh (tarray tuchar out_len) output
|-- !! return_value_relate_result
         (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
            (contents_with_add additional (Zlength contents) contents))
         (Vint return_value) &&
    (match
       mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
         (contents_with_add additional (Zlength contents) contents)
     with
     | ENTROPY.success (bytes, _) _ =>
         data_at Tsh (tarray tuchar out_len) (map Vint (map Int.repr bytes))
           output
     | ENTROPY.error _ _ => data_at_ Tsh (tarray tuchar out_len) output
     end *
     hmac256drbgabs_common_mpreds
       (hmac256drbgabs_generate initial_state_abs s out_len
          (contents_with_add additional (Zlength contents) contents))
       initial_state (Vptr b i) info_contents *
     da_emp Tsh (tarray tuchar (Zlength contents))
       (map Vint (map Int.repr contents)) additional *
     Stream
       (get_stream_result
          (mbedtls_HMAC256_DRBG_generate_function s initial_state_abs out_len
             (contents_with_add additional (Zlength contents) contents))) *
     K_vector kv).
Proof. intros.
 unfold reseedPOST. rewrite Hadd_lenb. normalize.
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
      rewrite Hout_lenb, ZLa, andb_negb_r, F in HeqMGen. 
      unfold DRBG_generate_function_helper in HeqMGen. rewrite <- HeqMRS in HeqMGen. subst Gen. simpl. normalize.
      destruct prediction_resistance; simpl in *.
      + rewrite ZLa in *. subst MGen.
        unfold return_value_relate_result. 
        apply andp_right. apply prop_right. repeat split; trivial.
        cancel. simpl. entailer!.
      + subst reseed_interval; rewrite Hshould_reseed, ZLa in *.
        destruct (get_entropy 256 entropy_len entropy_len false s); try discriminate.
        inv HeqMRS. unfold return_value_relate_result; simpl.
        apply andp_right. apply prop_right. repeat split; trivial.
        cancel. entailer!. 
Qed.

Opaque hmac256drbgabs_generate.
Opaque HMAC256_DRBG_generate_function.
Opaque mbedtls_HMAC256_DRBG_generate_function.

Lemma body_hmac_drbg_reseed: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_random_with_add hmac_drbg_generate_spec.
Proof.
  start_function.
  rename H5 into Hreseed_counter_in_range.

  destruct initial_state_abs.
  destruct initial_state as [md_ctx' [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].
  unfold hmac256drbg_relate.
  normalize.
  unfold hmac256drbgstate_md_info_pointer.
  simpl.

  rewrite da_emp_isptrornull. (*needed later*)
  rewrite data_at_isptr with (p:=ctx).
  normalize. 
  set (initial_state_abs := HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval) in *.
  set (initial_state := (md_ctx',
        (map Vint (map Int.repr V),
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
  forward_if (
      PROP  (out_len <= 1024)
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr 32)); temp _info (*(let (x, _) := md_ctx' in x)*)mc1;
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx (*ctx*)(Vptr b i); temp _p_rng (*ctx*)(Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP  (data_at_ Tsh (tarray tuchar out_len) output;
      da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
      data_at Tsh t_struct_hmac256drbg_context_st (*initial_state*)(mc1, (mc2, mc3),
     (map Vint (map Int.repr V),
     (Vint (Int.repr reseed_counter),
     (Vint (Int.repr entropy_len),
     (Val.of_bool prediction_resistance,
     Vint (Int.repr reseed_interval))))))  (*ctx*)(Vptr b i);
      md_full key (*md_ctx'*)(mc1, (mc2, mc3));
      data_at Tsh t_struct_mbedtls_md_info info_contents (*(fst md_ctx')*) mc1;
      Stream s; K_vector kv)
    ).
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
    unfold generatePOST'. rewrite Hout_len; simpl. entailer!.
    thaw FR0. cancel.
  }
  {
    forward.
    entailer!. thaw FR0. cancel.
  }

  Intros. clear Pctx FR0.
  assert (Hout_len: 0 <= out_len <= 1024) by omega.
  assert (Hout_lenb: out_len >? 1024 = false).
  {
    rewrite Z.gtb_ltb.
    apply Z.ltb_nlt.
    omega.
  }
  clear H5.

  freeze [0;1;2;3;4;5;6] FR2.

  (* III. if( add_len > MBEDTLS_HMAC_DRBG_MAX_INPUT ) *)
  forward_if (
      PROP  (add_len <= 256) (* ADDED *)
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr 32));
              temp _info mc1 (*(let (x, _) := md_ctx' in x)*);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx (*ctx*)(Vptr b i); temp _p_rng (*ctx*)(Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv)
      SEP  (FRZL FR2)). 
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
    unfold generatePOST'. rewrite Hout_lenb, Hadd_lenb; simpl.
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
  (*  subst add_len. *) rename H2 into AddlenC. clear H5.
  unfold POSTCONDITION, abbreviate, generatePOST'. rewrite Hout_lenb, Hadd_lenb. abbreviate_semax.
  assert (ZLa: Zlength (contents_with_add additional (Zlength contents) contents) >? 256 = false).
     { unfold contents_with_add. if_tac. subst; trivial. rewrite Zlength_nil; trivial. }

  (*1. (aka VII and IX) Check reseed counter and PR*)
  set (should_reseed := orb prediction_resistance (reseed_counter >? reseed_interval)) in *.
  forward_if (
      PROP  ()
      LOCAL  (temp _md_len (*md_len*)(Vint (Int.repr 32)); temp _info mc1(*(let (x, _) := md_ctx' in x)*);
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx (*ctx*)(Vptr b i); temp _p_rng (*ctx*)(Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv;
      temp (*159*)244%positive (Val.of_bool should_reseed) (* ADDED *)
      )
      SEP (FRZL FR2)). 
  {
    forward.
    entailer!.

    rename H2 into Hpr.
    destruct prediction_resistance; simpl. 
    (* true *) reflexivity.
    (* false *) inversion Hpr.
  }
  {
    rename H2 into Hpr.
    destruct prediction_resistance; try solve [inversion Hpr].
    simpl in should_reseed; clear Hpr. 
    forward.
    entailer!.
    
    subst should_reseed; rewrite Z.gtb_ltb.
    unfold Int.lt.
      unfold hmac256drbgabs_reseed_counter in Hreseed_counter_in_range.
    destruct (zlt reseed_interval reseed_counter) as [Hlt | Hlt].
    {
      (* reseed_interval < reseed_counter *)
      subst initial_state_abs.
      assert (Hltb: reseed_interval <? reseed_counter = true) by (rewrite Z.ltb_lt; assumption).
      rewrite Hltb.
      rewrite zlt_true; [reflexivity | ]. 
      unfold hmac256drbgabs_reseed_interval in H4; rewrite H4.
      change (Int.signed (Int.repr 10000)) with 10000.
      rewrite Int.signed_repr; change Int.min_signed with (-2147483648); change Int.max_signed with (2147483647) in *; try omega.
    }
    { subst initial_state_abs.
      assert (Hltb: reseed_interval <? reseed_counter = false) by (rewrite Z.ltb_nlt; assumption).
      rewrite Hltb.
      rewrite zlt_false; [reflexivity | ].
      unfold hmac256drbgabs_reseed_interval in H4; rewrite H4.
      change (Int.signed (Int.repr 10000)) with 10000.
      rewrite Int.signed_repr; change Int.min_signed with (-2147483648); change Int.max_signed with (2147483647) in *; try omega.
    }
  }


  set (after_reseed_add_len := if should_reseed then 0 else add_len) in *.
  assert (HIS: exists IS: reptype t_struct_hmac256drbg_context_st, IS = initial_state).
  { exists initial_state; trivial. }
  destruct HIS as [IS HIS].

  forward_if (
   PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance); 
   temp _out output; temp _left (Vint (Int.repr out_len)); temp _ctx (Vptr b i);
   temp _p_rng (Vptr b i); temp _output output; temp _out_len (Vint (Int.repr out_len));
   temp _additional additional; temp _add_len (Vint (Int.repr after_reseed_add_len));
   gvar sha._K256 kv; temp 244%positive (Val.of_bool should_reseed))
   SEP (EX myctx : reptype t_struct_hmac256drbg_context_st,
        (!! (if should_reseed
            then
             postReseedCtx myctx s key V reseed_counter entropy_len prediction_resistance
               reseed_interval additional contents (mc1, (mc2, mc3))
            else myctx = IS) &&
       (data_at Tsh t_struct_hmac256drbg_context_st myctx (Vptr b i) *
        data_at_ Tsh (tarray tuchar out_len) output *
        da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
        data_at Tsh t_struct_mbedtls_md_info info_contents mc1 * K_vector kv *
        (if should_reseed 
            then (postReseedKey s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents mc1 mc2 mc3)
            else md_full key (mc1, (mc2, mc3))) *
        (if should_reseed
            then (postReseedStream s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents)
            else Stream s))))).

  { (*Case should_reseed = true*)
    assert (Hshould_reseed: should_reseed = true) by apply H2; clear H2.
    unfold POSTCONDITION, abbreviate. rewrite Hshould_reseed in *. clear POSTCONDITION. thaw FR2. 
    abbreviate_semax.

    forward_call (*WIT. fails!!*)(contents, additional, add_len, (*ctx*)Vptr b i, initial_state, initial_state_abs,
                  kv, info_contents, s).
    { subst initial_state initial_state_abs; cancel.
      unfold hmac256drbg_relate. entailer!.
    } 
    { repeat split; trivial; omega. }
     
    Intros return_value.
    forward. 

    assert (F: 0>? 256 = false) by reflexivity.
    forward_if (PROP  (return_value = Vzero) (* ADDED *)
      LOCAL  (temp _ret return_value; (*temp (*158*)243%positive return_value;*)
      temp _md_len (Vint (Int.repr 32)); temp _info (*(let (x, _) := md_ctx' in x)*)mc1;
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len)); 
      temp _ctx (*ctx*)(Vptr b i); temp _p_rng (*ctx*)(Vptr b i); temp _output output;
      temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
      temp _add_len (Vint (Int.repr add_len)); gvar sha._K256 kv; 
      temp 244%positive (Val.of_bool true))
      SEP (reseedPOST return_value contents additional add_len s initial_state_abs 
                (Vptr b i) info_contents kv initial_state;
          data_at_ Tsh (tarray tuchar out_len) output)).
    {
      (* reseed's return_value != 0 *)
      rename H2 into Hrv.
      unfold POSTCONDITION, abbreviate.
      forward. simpl in *.
      clear - Hadd_lenb Hrv Hout_lenb ZLa F H4 Hshould_reseed.
      Exists (Vint return_value).
      apply andp_right. apply prop_right; trivial. 
      apply andp_right. apply prop_right; split; trivial.
      normalize.
      apply entailment1; trivial. 
(*Opaque hmac256drbgabs_generate.
Opaque HMAC256_DRBG_generate_function.
Opaque mbedtls_HMAC256_DRBG_generate_function. *) }

     { (* reseed's return_value = 0 *)
       rename H2 into Hrv.
       forward. entailer!. unfold Vzero. f_equal. 
       apply negb_false_iff in Hrv. apply int_eq_e in Hrv. trivial.
     }
 
     forward. subst after_reseed_add_len. rewrite Hshould_reseed in *. clear Hshould_reseed should_reseed.
     entailer!.
     unfold reseedPOST. rewrite Hadd_lenb.
     Intros. (* cancel.*)
     unfold return_value_relate_result in H9.
     remember (mbedtls_HMAC256_DRBG_reseed_function s initial_state_abs
        (contents_with_add additional (Zlength contents) contents)) as Reseed.
     destruct Reseed.
     Focus 2. destruct e; try inv H9; elim H9; trivial. clear H9.
     destruct d as [[[[RSVal RSKey] aa] bb] cc].
     unfold hmac256drbgabs_reseed, postReseedCtx, postReseedKey, postReseedStream.
     subst initial_state_abs; rewrite <- HeqReseed. simpl. 
     Exists  (mc1, (mc2, mc3),
         (map Vint (map Int.repr RSVal),
         (Vint (Int.repr aa),
         (Vint (Int.repr entropy_len), (Val.of_bool cc, Vint (Int.repr reseed_interval)))))).
     normalize. cancel.
     unfold hmac256drbgabs_common_mpreds; simpl. 
     normalize. 
  }
  { (*Case should_reseed = false*)
    forward. subst after_reseed_add_len. rewrite H2, HIS in *. clear H2 HIS.
    Exists initial_state. entailer!. thaw FR2. cancel.
  }

  normalize. (*FAILS*)
  Intros. (*FAILS*)

  assert (HIC: exists IC: reptype t_struct_mbedtls_md_info, IC = info_contents).
  { exists info_contents; trivial. }
  destruct HIC as [IC HIC].

  apply semax_pre with (P':=
    EX ctx1 : reptype t_struct_hmac256drbg_context_st,
    (PROP (mkCTX1 should_reseed IS ctx1 s key V reseed_counter entropy_len 
           prediction_resistance reseed_interval additional contents (mc1, (mc2, mc3)))
    LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
     temp _reseed_interval (Vint (Int.repr reseed_interval));
     temp _reseed_counter (Vint (Int.repr reseed_counter));
     temp _prediction_resistance (Val.of_bool prediction_resistance); 
     temp _out output; temp _left (Vint (Int.repr out_len)); temp _ctx (Vptr b i);
     temp _p_rng (Vptr b i); temp _output output; temp _out_len (Vint (Int.repr out_len));
     temp _additional additional; temp _add_len (Vint (Int.repr after_reseed_add_len));
     gvar sha._K256 kv; temp 244%positive (Val.of_bool should_reseed))
    SEP ((*!! (if should_reseed
            then
             postReseedCtx myctx s key V reseed_counter entropy_len prediction_resistance
               reseed_interval additional contents (mc1, (mc2, mc3))
            else myctx = IS) &&*)
        (data_at Tsh t_struct_hmac256drbg_context_st ctx1 (Vptr b i) *
         data_at_ Tsh (tarray tuchar out_len) output *
         da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional *
         data_at Tsh t_struct_mbedtls_md_info IC mc1 * K_vector kv *
         (if should_reseed
          then
           postReseedKey s key V reseed_counter entropy_len prediction_resistance
             reseed_interval additional contents mc1 mc2 mc3
          else md_full key (mc1, (mc2, mc3))) *
         (if should_reseed
          then
           postReseedStream s key V reseed_counter entropy_len prediction_resistance
             reseed_interval additional contents
          else Stream s))))
  ).
  { go_lower. 
    Intros. (*FAILS*)
    normalize. (*SUCEEDS*)
    Exists myctx.
    normalize.

    (* entailer!. slow...*)
    apply andp_right. apply prop_right; repeat split; trivial.
    cancel. subst IC. cancel.
  }
  Intros. (*STILL FAILS*)
  normalize. (*STILL FAILS*)
  apply extract_exists_pre. (*SUCCEEDS*) intros ctx1.
  Intros. (*succeeds pulling prop-part above the line; alternatively, normalize also succeeds here*)
  rename H2 into CTX1. 

  apply semax_pre with (P':= EX key1:list Z,
   (PROP ( mkKEY1 (should_reseed:bool) s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents key1)
    LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1; temp _reseed_interval (Vint (Int.repr reseed_interval));
     temp _reseed_counter (Vint (Int.repr reseed_counter));
     temp _prediction_resistance (Val.of_bool prediction_resistance); temp _out output;
     temp _left (Vint (Int.repr out_len)); temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
     temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
     temp _add_len (Vint (Int.repr after_reseed_add_len)); gvar sha._K256 kv;
     temp 244%positive (Val.of_bool should_reseed))
    SEP (data_at Tsh t_struct_hmac256drbg_context_st ctx1 (Vptr b i); data_at_ Tsh (tarray tuchar out_len) output;
     da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
     data_at Tsh t_struct_mbedtls_md_info IC mc1; K_vector kv;
     md_full key1 (mc1, (mc2, mc3));
     if should_reseed
     then postReseedStream s key V reseed_counter entropy_len prediction_resistance reseed_interval additional contents
     else Stream s))).
  { go_lower. 
    destruct should_reseed.
    + unfold postReseedKey, mkKEY1.
      remember (mbedtls_HMAC256_DRBG_reseed_function s
         (HMAC256DRBGabs key V reseed_counter entropy_len
            prediction_resistance reseed_interval)
         (contents_with_add additional (Zlength contents) contents)) as RS.
      destruct RS.
      - destruct d as [[[[Val1 Key1] ?] ?] ? ?]. Exists Key1. normalize.
        apply andp_right. apply prop_right; repeat split; trivial.
        cancel.
      - normalize. (*contradiction -- FF on LHS*)
    + Exists key; unfold mkKEY1. normalize.
      apply andp_right. apply prop_right; repeat split; trivial.
      cancel.
  }
  Intros. (*FAILS*)
  normalize. (*FAILS*)
  apply extract_exists_pre. (*SUCCEEDS*) intros key1. 
  Intros. (*SUCCEEDS*) rename H2 into KEY1.

  apply semax_pre with (P':=
   EX stream1:ENTROPY.stream,
    (PROP ((*if should_reseed
         then match mbedtls_HMAC256_DRBG_reseed_function s
            (HMAC256DRBGabs key V reseed_counter entropy_len
               prediction_resistance reseed_interval)
            (contents_with_add additional (Zlength contents) contents)
             with
             | ENTROPY.success (_, _, _, _, _) s0 => s1=s0
             | ENTROPY.error _ _ => False
             end
         else s1=s*)
       mkSTREAM1 should_reseed s key V reseed_counter entropy_len prediction_resistance 
                 reseed_interval additional contents stream1)
     LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
      temp _reseed_interval (Vint (Int.repr reseed_interval));
      temp _reseed_counter (Vint (Int.repr reseed_counter));
      temp _prediction_resistance (Val.of_bool prediction_resistance);
      temp _out output; temp _left (Vint (Int.repr out_len));
      temp _ctx (Vptr b i); temp _p_rng (Vptr b i); 
      temp _output output; temp _out_len (Vint (Int.repr out_len));
      temp _additional additional;
      temp _add_len (Vint (Int.repr after_reseed_add_len));
      gvar sha._K256 kv; temp 244%positive (Val.of_bool should_reseed))
     SEP (data_at Tsh t_struct_hmac256drbg_context_st ctx1 (Vptr b i);
      data_at_ Tsh (tarray tuchar out_len) output;
      da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
      data_at Tsh t_struct_mbedtls_md_info IC mc1; K_vector kv;
      md_full key1 (mc1, (mc2, mc3)); Stream stream1))).
  { unfold postReseedStream, mkSTREAM1.
    remember (mbedtls_HMAC256_DRBG_reseed_function s
               (HMAC256DRBGabs key V reseed_counter entropy_len
                  prediction_resistance reseed_interval)
               (contents_with_add additional (Zlength contents) contents)) as RS.
    go_lower.
    destruct should_reseed.
    + destruct RS. 
      - destruct d as [[[[Val1 Key1] ?] ?] ? ?]. Exists s0. normalize.
        apply andp_right. apply prop_right; repeat split; trivial.
        cancel.
      - normalize. (*contradiction -- FF on LHS*)
    + Exists s. normalize.
      apply andp_right. apply prop_right; repeat split; trivial.
      cancel.
  } 
  Intros. (*FAILS*)
  normalize. (*FAILS*)
  apply extract_exists_pre. (*SUCCEEDS*) intros stream1. 
  Intros. (*SUCCEEDS*) rename H2 into STREAM1.

  clear FR2.
  freeze [1;3;6] FR3.
  freeze [0;1;3;4] FR4.

  set (na:=(negb (eq_dec additional nullval) && negb (eq_dec ((if should_reseed then 0 else Zlength contents)) 0))%bool) in *.
 
  forward_if
  (PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance); 
   temp _out output; temp _left (Vint (Int.repr out_len)); 
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvar sha._K256 kv;
   temp 244%positive (Val.of_bool should_reseed);
   temp 245%positive (Val.of_bool na))
   SEP (FRZL FR4;
        da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional)).
  { destruct additional; simpl in PNadditional; try contradiction.
    + subst i0; entailer.
    + rewrite da_emp_ptr. normalize.
      unfold denote_tc_comparable. entailer.
  }
  { forward. entailer!. subst after_reseed_add_len na.
    destruct should_reseed; simpl; trivial. rewrite andb_false_r. reflexivity.
    destruct (initial_world.EqDec_Z (Zlength contents)  0); simpl. 
    + rewrite e. simpl. rewrite andb_false_r. reflexivity.
    + rewrite Int.eq_false; simpl. 
      destruct (base.EqDec_val additional nullval); try reflexivity. contradiction. 
      intros N. assert (U: Int.unsigned (Int.repr (Zlength contents)) = Int.unsigned (Int.repr 0)). rewrite N; trivial. clear N.
      rewrite Int.unsigned_repr in U; trivial. rewrite U in n. elim n; trivial. 
  }
  { forward. rewrite H2 in *. entailer!. }

  thaw FR4.
  forward_if (PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance);
   temp _out output; temp _left (Vint (Int.repr out_len)); 
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); 
   gvar sha._K256 kv; temp 244%positive (Val.of_bool should_reseed);
   temp 245%positive (Val.of_bool na))
   SEP (FRZL FR3; K_vector kv;
   da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
   if na 
   then (EX bb:block, EX ii: int, EX UKey:list Z, EX UVal:list Z,
           !!(additional = Vptr bb ii /\ 
              (UKey, UVal) = HMAC256_DRBG_update
                    (contents_with_add (Vptr bb ii) (Zlength contents) contents) key V)
           && data_at Tsh t_struct_hmac256drbg_context_st
                (mc1, (mc2, mc3),
                (map Vint (map Int.repr UVal),
                (Vint (Int.repr reseed_counter),
                (Vint (Int.repr entropy_len),
                (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))) 
                (Vptr b i) * md_full UKey (mc1, (mc2, mc3)))
   else data_at Tsh t_struct_hmac256drbg_context_st ctx1 (Vptr b i) *
        md_full key1 (mc1, (mc2, mc3)))).
   { rewrite H2 in *. subst na.
     destruct should_reseed; simpl in *. rewrite andb_false_r in H2; discriminate.
     destruct (initial_world.EqDec_Z (Zlength contents) 0); simpl in H2.
     { rewrite andb_false_r in H2; discriminate. }
     rewrite andb_true_r in H2.
     destruct additional; simpl in PNadditional; try contradiction.
     { subst i0; discriminate. }
     subst key1 stream1 ctx1. clear H2. 
     
       forward_call (contents, Vptr b0 i0, after_reseed_add_len, 
                    (*ctx*)Vptr b i,
                    initial_state,
                 initial_state_abs, kv, info_contents
                 ).
       { assert (FR: Frame = [data_at_ Tsh (tarray tuchar out_len) output * Stream s]).
         { subst Frame; reflexivity. }
         subst Frame.
         subst after_reseed_add_len add_len initial_state. cancel.
         clear POSTCONDITION. thaw FR3.
         unfold hmac256drbg_relate, hmac256drbgstate_md_info_pointer; simpl.
         subst initial_state_abs. normalize.
         apply andp_right. apply prop_right. repeat split; trivial.
         cancel. subst IS IC. cancel.
       }
(*       { repeat split; trivial; omega. }*)
       { (*subst na.*)subst after_reseed_add_len.  entailer. Exists b0 i0.
         apply andp_right. entailer!.
         cancel. 
         unfold hmac256drbgabs_common_mpreds, hmac256drbgstate_md_info_pointer. simpl.
         remember (HMAC256_DRBG_update
          (contents_with_add (Vptr b0 i0) (Zlength contents) contents) key V ) as UPD.
         destruct UPD as [UKey UVal]. simpl. Exists UKey UVal. Intros.
         apply andp_right. apply prop_right; split; trivial.
         thaw FR3. cancel. 
       }
     }
     { forward. rewrite H2 in *. entailer. cancel. }

(* IT'S PATHETIC THAT WE NEED TO INTRDUCE ctx2' AND a predicate CTXeq to wotk around FLOYD'S typechecker!!*)
apply semax_pre with (P' := EX ctx2:reptype t_struct_hmac256drbg_context_st, EX key2:list Z,
  PROP (
     if na
     then exists ctx2':(val * (val * val) * (list val * (val * (val * (val * val)))))%type,
          exists bb : block, exists ii : int, exists V2 : list Z, 
          additional = Vptr bb ii /\ CTXeq ctx2 ctx2' /\
          (key2, V2) = HMAC256_DRBG_update (contents_with_add (Vptr bb ii) (Zlength contents) contents) key V /\
          ctx2' = (mc1, (mc2, mc3),
                 (map Vint (map Int.repr V2),
                 (Vint (Int.repr reseed_counter),
                 (Vint (Int.repr entropy_len),
                 (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval))))))
     else (ctx2=ctx1 /\ key2=key1))
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance); temp _out output;
   temp _left (Vint (Int.repr out_len)); temp _ctx (Vptr b i); temp _p_rng (Vptr b i);
   temp _output output; temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvar sha._K256 kv;
   temp 244%positive (Val.of_bool should_reseed); temp 245%positive (Val.of_bool na))
   SEP (FRZL FR3; K_vector kv;
   da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
   data_at Tsh t_struct_hmac256drbg_context_st ctx2 (Vptr b i) * md_full key2 (mc1, (mc2, mc3)))).
{ go_lower.
  destruct na.
  + normalize. 
    Exists (mc1, (mc2, mc3),
            (map Vint (map Int.repr UVal),
            (Vint (Int.repr reseed_counter),
            (Vint (Int.repr entropy_len), (Val.of_bool prediction_resistance, Vint (Int.repr reseed_interval)))))).
    Exists UKey. entailer!.
    eexists; exists bb, ii, UVal. rewrite <- H9.
    repeat split; try reflexivity.
  + Exists ctx1 key1. normalize. entailer!.
}
Intros. normalize. (*BOTH FAIL*)
apply extract_exists_pre. intros ctx2.
apply extract_exists_pre. intros key2.
Intros. (*SUCCEEDS*) rename H2 into CTX2KEY2.

set (after_reseed_state_abs := if should_reseed
          then hmac256drbgabs_reseed initial_state_abs s (contents_with_add additional add_len contents)
          else initial_state_abs) in *.

assert (ZLength_ARSA_val: Zlength (hmac256drbgabs_value after_reseed_state_abs) = 32).
{ subst after_reseed_state_abs add_len.
  destruct should_reseed; trivial.
  apply Zlength_hmac256drbgabs_reseed_value; trivial. }

assert (isbyte_ARSA_val: Forall isbyteZ (hmac256drbgabs_value after_reseed_state_abs)).
{ subst after_reseed_state_abs add_len.
  destruct should_reseed; trivial.
  apply isbyteZ_hmac256drbgabs_reseed_value; trivial. }

set (after_update_state_abs := (if na then hmac256drbgabs_hmac_drbg_update initial_state_abs contents else after_reseed_state_abs)) in *.

assert (ZLength_AUSA_val: Zlength (hmac256drbgabs_value after_update_state_abs) = 32).
{ subst after_update_state_abs.
  destruct na; trivial. apply Zlength_hmac256drbgabs_update_value. }

assert (isbyte_AUSA_val: Forall isbyteZ (hmac256drbgabs_value after_update_state_abs)).
{ subst after_update_state_abs.
  destruct na; trivial. apply isbyteZ_hmac256drbgabs_update_value. }

thaw FR3.
set (after_update_Mpred := hmac256drbgabs_common_mpreds after_update_state_abs initial_state (Vptr b i) info_contents) in *.
apply semax_pre with (P':=
  (PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance); 
   temp _out output; temp _left (Vint (Int.repr out_len)); 
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvar sha._K256 kv;
   temp 244%positive (Val.of_bool should_reseed); temp 245%positive (Val.of_bool na))
   SEP (data_at_ Tsh (tarray tuchar out_len) output; Stream stream1; 
     K_vector kv;
     da_emp Tsh (tarray tuchar add_len) (map Vint (map Int.repr contents)) additional;
     after_update_Mpred ))).
{ go_lower. normalize.
  apply andp_right. apply prop_right; repeat split; trivial. cancel.
  subst after_update_Mpred. unfold hmac256drbgabs_common_mpreds. subst IC; simpl.
  unfold hmac256drbg_relate, hmac256drbgstate_md_info_pointer.
  remember (hmac256drbgabs_to_state after_update_state_abs initial_state).
  unfold hmac256drbgabs_to_state in Heqh. subst after_update_state_abs initial_state.

  remember na as nna.
  destruct nna.
  + subst initial_state_abs. simpl in Heqh.
    remember (HMAC256_DRBG_update contents key V) as UPD.
    destruct UPD. subst h.
    remember (hmac256drbgabs_hmac_drbg_update
        (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
           reseed_interval) contents) as hh. simpl. cancel.
    destruct hh.
    unfold hmac256drbgabs_hmac_drbg_update in Heqhh. rewrite <- HeqUPD in Heqhh. inv Heqhh. 
    entailer!.
    destruct CTX2KEY2 as [ctx22 [bb [ii [V2 [ADD [CEQ [UPD C2]]]]]]]. subst ctx22 additional.
    unfold CTXeq in CEQ; subst ctx2.
    unfold mkCTX1 in CTX1; unfold mkKEY1 in KEY1; unfold mkSTREAM1 in STREAM1.
    destruct should_reseed.
    - discriminate.
    - subst stream1 ctx1 key1.
      remember (contents_with_add (Vptr bb ii) (Zlength contents) contents) as CONT.
      unfold contents_with_add in HeqCONT. simpl in HeqCONT. simpl in Heqnna.
      destruct (initial_world.EqDec_Z (Zlength contents) 0); simpl in *; try discriminate.
      subst CONT.
      rewrite <- HeqUPD in UPD. inv UPD. cancel.
  + destruct CTX2KEY2; subst ctx2 key2. subst after_reseed_state_abs.
    unfold mkCTX1 in CTX1; unfold mkKEY1 in KEY1; unfold mkSTREAM1 in STREAM1.
    destruct should_reseed.
    - simpl in na. clear Heqnna na. 
      remember (mbedtls_HMAC256_DRBG_reseed_function s
              (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
                 reseed_interval)
              (contents_with_add additional (Zlength contents) contents)) as M.
      destruct M; try contradiction. 
      destruct d as [[[[AA BB] CC] DD] EE]. subst BB s0 ctx1.
      unfold hmac256drbgabs_reseed in Heqh. subst initial_state_abs. subst add_len. rewrite <- HeqM in Heqh. 
      subst h. unfold hmac256drbgabs_reseed. rewrite <- HeqM. simpl. cancel. entailer!.
      { unfold mbedtls_HMAC256_DRBG_reseed_function, HMAC256_DRBG_reseed_function, DRBG_reseed_function in HeqM.
        rewrite andb_negb_r, ZLa in HeqM. 
        destruct (get_entropy 256 entropy_len entropy_len prediction_resistance s); inv HeqM.
        remember(HMAC_DRBG_update HMAC256
           (l ++ contents_with_add additional (Zlength contents) contents) key V) as h.
        destruct h; inv H10. eapply HMAC_DRBG_update_value; eassumption. 
      }
    - subst stream1 key1 initial_state_abs h ctx1 IS. simpl. cancel. entailer!.
}
subst after_update_Mpred.

clear CTX2KEY2 KEY1 CTX1. clear ctx1 key1 ctx2 key2.

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
      gvar sha._K256 kv
      )
      SEP  ((*Stream stream1;*)
      hmac256drbgabs_common_mpreds (hmac256drbgabs_update_value after_update_state_abs 
              (fst (HLP done)))
        initial_state (Vptr b i) info_contents; FRZL StreamAdd; 
      data_at Tsh (tarray tuchar out_len) ((map Vint (map Int.repr
          (sublist 0 done (snd (HLP done))))) ++ 
          list_repeat (Z.to_nat (out_len - done)) Vundef) output; 
      K_vector kv)
  ).
  {
    (* prove the current precondition implies the loop condition *)
    Exists 0.
    change (sublist 0 0 (snd (HLP 0))) with (@nil Z).
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
    cancel. apply derives_refl. 
  }
  {
    (* prove the type checking of the loop condition *)
    entailer!.
  }
  { (*LOOP BODY -- INLINED VERSION*)
    destruct H5 as [Hmultiple | Hcontra]; [| subst done; elim HRE; f_equal; omega].
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

    rewrite (field_at_data_at _ _ [StructField _md_ctx]). simpl.
    rewrite (field_at_data_at _ _ [StructField _V]). 
    simpl.

    unfold hmac256drbg_relate. subst initial_state_abs. simpl in *.

    destruct after_update_state_abs. simpl in *.
    unfold hmac256drbgabs_update_value.
(*    rewrite Heqinitial_state.*)
    unfold hmac256drbgabs_to_state.
(*    rewrite Heqafter_update_key.*)
    simpl in AUV, AUK. subst AUV AUK.
    unfold md_full. subst initial_state. simpl.
    normalize. 

    (* size_t use_len = left > md_len ? md_len : left; *)
    forward_if (
  (PROP ( )
   LOCAL (temp _md_len (Vint (Int.repr 32)); temp _info mc1;
   temp _reseed_interval (Vint (Int.repr reseed_interval));
   temp _reseed_counter (Vint (Int.repr reseed_counter));
   temp _prediction_resistance (Val.of_bool prediction_resistance);
   temp _out (offset_val done output); temp _left (Vint (Int.repr (out_len - done)));
   temp _ctx (Vptr b i); temp _p_rng (Vptr b i); temp _output output;
   temp _out_len (Vint (Int.repr out_len)); temp _additional additional;
   temp _add_len (Vint (Int.repr after_reseed_add_len)); gvar sha._K256 kv;
      temp (*161*)246%positive (Vint (Int.repr (Z.min (Z.of_nat SHA256.DigestLength) (out_len - done)))))
   SEP (FRZL FR1;
   data_at Tsh (Tstruct _mbedtls_md_context_t noattr) (mc1, (mc2, mc3))
     (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] (Vptr b i));
   data_at Tsh (tarray tuchar 32)
     (map Vint (map Int.repr (fst (HLP done))))
     (field_address t_struct_hmac256drbg_context_st [StructField _V] (Vptr b i));
   data_at Tsh (tarray tuchar out_len)
     (map Vint
        (map Int.repr (sublist 0 done (snd (HLP done)))) ++
      list_repeat (Z.to_nat (out_len - done)) Vundef) output;
   UNDER_SPEC.FULL key0 mc3; K_vector kv))).
    {
      (* md_len < left *)
      forward.
      entailer!.
      rewrite Z.min_l; [reflexivity | omega].
    }
    {
      (* md_len >= left *)
      forward.
      entailer!.
      rewrite Z.min_r; [reflexivity | omega].
    }
    forward.

    (* mbedtls_md_hmac_reset( &ctx->md_ctx ); *)
    assert_PROP (field_compatible (Tarray tuchar 32 noattr) 
          []
          (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))) as FC_V by entailer!.
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st
         [StructField _md_ctx] (Vptr b i)) as FC_M by entailer.
    forward_call (field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] (*ctx*)(Vptr b i), (*md_ctx'*)(mc1,(mc2,mc3)), key0, kv).
    { simpl. cancel. }

    (* mbedtls_md_hmac_update( &ctx->md_ctx, ctx->V, md_len ); *)
    rename H5 into HZlength_V. 
    rename H8 into HisbyteZ_V.
    assert_PROP (field_compatible t_struct_hmac256drbg_context_st [StructField _V] (Vptr b i)) as FCV by entailer!.
    forward_call (key0, field_address t_struct_hmac256drbg_context_st [StructField _md_ctx] (*ctx*)(Vptr b i),
                  (*md_ctx'*)(mc1,(mc2,mc3)), 
                  field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i), 
                  @nil Z, (fst (HLP done)), kv).

    { simpl. apply prop_right. rewrite HZlength_V, field_address_offset; trivial.
      split; simpl; trivial. 
      split; trivial. erewrite <- Hfield_md_ctx; simpl; trivial.
      rewrite Int.add_zero; trivial.
    }
    { simpl; simpl in HZlength_V; rewrite HZlength_V (*, <- Hmultiple*).
      cancel.
    }
    {
      simpl; simpl in HZlength_V; rewrite HZlength_V. 
      change Int.max_unsigned with 4294967295.
      change (two_power_pos 61) with 2305843009213693952.
      repeat split; try omega.
      apply HMAC_DRBG_generate_helper_Z_isbyteZ_fst; auto; try omega.
      apply isbyteZ_HMAC256. 
    }

    (*Intros vret; subst vret.*)
    rewrite app_nil_l.

    replace_SEP 2 (memory_block Tsh 32 (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))).
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
               (*md_ctx'*)(mc1, (mc2, mc3)),
               field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i), Tsh, kv).
    {
      entailer!.
      rewrite field_address_offset; trivial. 
    }
    Intros vret; subst vret. simpl.
    assert_PROP (field_compatible (tarray tuchar out_len) [] output) as
        Hfield_compat_output by entailer!.
    replace_SEP 5 (
        data_at Tsh (tarray tuchar done) (map Vint (map Int.repr (sublist 0 done (snd (HLP done))))) output *
        data_at Tsh (tarray tuchar (out_len - done)) (list_repeat (Z.to_nat (out_len - done)) Vundef) (offset_val done output)
    ).
    {
      entailer!.
      apply derives_refl'.

      assert (HZlength1: Zlength (map Vint (map Int.repr (sublist 0 (n * 32)%Z (snd (HLP (n * 32)%Z))))) = (n * 32)%Z).
      {
        do 2 rewrite Zlength_map.
        rewrite Zlength_sublist; [omega|omega|]. subst HLP.
        rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; auto; try omega.
        apply hmac_common_lemmas.HMAC_Zlength.
        exists n; reflexivity.
      }
      
      apply data_at_complete_split; try rewrite HZlength1; try rewrite Zlength_list_repeat; auto; try omega.
      (*simpl. simpl in HZlength1. rewrite HZlength1.*)
      replace ((n * 32)%Z + (out_len - (n * 32)%Z)) with out_len by omega. assumption.
    }
    normalize.
    
    remember (offset_val done output) as done_output.
    remember (Z.min 32 (out_len - done)) as use_len.
    assert_PROP (field_compatible (tarray tuchar (out_len - done)) [] done_output) as Hfield_compat_done_output.
    {
      clear Heqdone_output Hmultiple.
      entailer!.
      rewrite H10 (*Zlength = done *) in *; assumption.
    }
    replace_SEP 1 (
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
    normalize.

    replace_SEP 0 (memory_block Tsh use_len done_output).
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
    set (H256 := HMAC256 (fst (HLP done)) key0) in *.
    assert (ZL_H256: Zlength H256 = 32).
    { subst H256. apply hmac_common_lemmas.HMAC_Zlength. }
    replace_SEP 6 (data_at Tsh (tarray tuchar use_len)
                      (sublist 0 use_len (map Vint (map Int.repr H256)))
                      (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i)) *
                   data_at Tsh (tarray tuchar (32 - use_len))
                      (sublist use_len 32 (map Vint (map Int.repr (H256))))
                      (offset_val use_len (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i)))).
    {
      clear Hmultiple.
      entailer!.
      apply derives_refl'.
      remember (fst (HLP done)) as V0'; clear HeqV0'.
      rewrite ZL_H256, Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        apply data_at_complete_split; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; repeat rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        rewrite sublist_nil.
        rewrite app_nil_r.
        symmetry; apply sublist_same.
        reflexivity.
        repeat rewrite Zlength_map; rewrite ZL_H256; reflexivity.
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
    forward_call ((Tsh, Tsh), done_output, 
                  field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i), 
                  use_len,
                  sublist 0 use_len (map Int.repr H256)).
    {
      (*replace (map Vint (sublist 0 use_len (map Int.repr H256))) with 
              (sublist 0 use_len (map Vint (map Int.repr H256))).*)
      rewrite sublist_map. (*
      change (@data_at CompSpecs (fst (Tsh, Tsh)) (tarray tuchar use_len)
         (sublist 0 use_len (map Vint (map Int.repr H256)))
         (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))) with
      (@data_at hmac_drbg_compspecs.CompSpecs (fst (Tsh, Tsh)) (tarray tuchar use_len)
         (sublist 0 use_len (map Vint (map Int.repr H256)))
         (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))).*)
      Time entailer!.
      rewrite field_address_offset; trivial. 
    }
    { simpl. rewrite sublist_map. cancel. }
    { repeat split; auto;
      subst use_len; destruct (Z.min_dec 32 (out_len - done)); try omega.
      rewrite e; change (Int.max_unsigned) with 4294967295; omega.
    }

    simpl.
    gather_SEP 0 7.
    replace_SEP 0 (data_at Tsh (tarray tuchar 32) (map Vint (map Int.repr H256))
                               (field_address t_struct_hmac256drbg_context_st [StructField _V] (*ctx*)(Vptr b i))).
    {
      clear Hmultiple.
      entailer!.
      apply derives_refl'.
      rewrite <- sublist_map.
      remember (fst (HLP done)) as V0'; clear HeqV0'.
      symmetry.
      rewrite Zmin_spec.
      destruct (Z_lt_ge_dec 32 (out_len - done)) as [Hmin | Hmin].
      {
        rewrite zlt_true by assumption.
        rewrite sublist_nil.
        rewrite sublist_same; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; try omega.
        remember (map Vint (map Int.repr (HMAC256 V0' key0))) as data.
        apply data_at_complete_split; subst data; repeat rewrite Zlength_map; try rewrite ZL_H256, Zlength_nil; auto; try omega.
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
    replace_SEP 0 (data_at Tsh (tarray tuchar (out_len - done)) 
         ( (map Vint (sublist 0 use_len (map Int.repr H256)))
           ++ (list_repeat (Z.to_nat (out_len - done - use_len)) Vundef))
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
        apply data_at_complete_split; 
           repeat rewrite Zlength_map; try rewrite Zlength_list_repeat; trivial; try omega.
        + rewrite Zlength_sublist; try omega.
            replace (32 - 0 + (out_len - done - 32)) with (out_len - done) by omega; trivial.
            rewrite Zlength_map; omega.
        + rewrite Zlength_sublist; try rewrite Zlength_map; omega. 
      }
      {
        rewrite zlt_false by assumption.
        apply data_at_complete_split; change ((fix map (l : list int) : list val :=
               match l with
               | [] => []
               | a :: t => Vint a :: map t
               end)
              (sublist 0 (out_len - done)
                 (map Int.repr H256)))  with (map Vint
              (sublist 0 (out_len - done)
                 (map Int.repr H256))); repeat rewrite Zlength_list_repeat; auto; try omega;
        rewrite Zlength_map; rewrite Zlength_sublist; try rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega.
        replace (out_len - done - 0 + (out_len - done - (out_len - done))) with (out_len - done) by omega.
        assumption.
      }
    }

    gather_SEP 2 0.
    replace_SEP 0 (
                  data_at Tsh (tarray tuchar out_len) 
                    ((map Vint (map Int.repr (sublist 0 done (snd (HLP done))))) ++
                     (map Vint (sublist 0 use_len (map Int.repr H256)) ++
                      list_repeat (Z.to_nat (out_len - done - use_len)) Vundef)) output).
    {
      entailer!.
      apply derives_refl'.
      symmetry.
      assert (HZlength1: Zlength ((snd (HLP (n * 32)%Z))) = (n * 32)%Z).
      { subst HLP.
        rewrite HMAC_DRBG_generate_helper_Z_Zlength_snd; auto; try omega.
        apply hmac_common_lemmas.HMAC_Zlength.
        exists n; reflexivity.
      }
      rewrite Zmin_spec. simpl in *.
      destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption];
      try rewrite HZlength_V.
      apply data_at_complete_split;
      repeat rewrite Zlength_app; repeat rewrite Zlength_map; try rewrite HZlength1; repeat rewrite Zlength_list_repeat; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega;
      try rewrite HZlength_V.
      replace ((n * 32)%Z - 0 + (32 - 0 + (out_len - (n * 32)%Z - 32))) with out_len by omega;
      assumption. 
      replace ((n * 32)%Z - 0 + (out_len - (n * 32)%Z - 0 + (out_len - (n * 32)%Z - (out_len - (n * 32)%Z)))) with out_len by omega.
      apply data_at_complete_split;
      repeat rewrite Zlength_app; repeat rewrite Zlength_map; try rewrite HZlength1; repeat rewrite Zlength_list_repeat; repeat rewrite Zlength_sublist; repeat rewrite Zlength_map; try rewrite hmac_common_lemmas.HMAC_Zlength; auto; try omega;
      try rewrite HZlength_V.
      replace (n * 32 - 0 + (out_len - n * 32 - 0 + (out_len - n * 32 - (out_len - n * 32)))) with
         out_len by omega.
      assumption.
    }

    (* out += use_len; *)
    forward.

    (* left -= use_len; *)
    forward.
    { 
      old_go_lower. 
      Exists (done + use_len).
      unfold hmac256drbgabs_common_mpreds; normalize.

      unfold_data_at 4%nat.
      rewrite (field_at_data_at _ _ [StructField _md_ctx]);
      rewrite (field_at_data_at _ _ [StructField _V]).
    
      unfold md_full.
    
      thaw FR1.
      thaw FR_unused_struct_fields.
      (*Ideal proof - but takes ages:
      Time entailer!. (*Coq8.5pl2: 1245secs*)
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
      So let's do it by hand*)
      subst. rewrite (*H10,*) offset_offset_val. (*clear H10.*)
      apply andp_right. 
      { apply prop_right. 
        rewrite Zmin_spec.
        destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; repeat split; try omega.
        left; exists (n + 1); omega.
        replace (out_len - ((n * 32)%Z + 32)) with (out_len - (n * 32)%Z - 32) by omega.
        (*reflexivity.*) assumption. 
        (*right; omega.*)
        f_equal. f_equal. omega.
(*        replace (out_len - ((n * 32)%Z + (out_len - (n * 32)%Z))) with (out_len - (n * 32)%Z - (out_len - (n * 32)%Z)) by omega.*)
        assumption.
        right; omega. 
        assumption.
        f_equal. f_equal. omega.
        assumption.
      }
      cancel.

      (*Rest as with "ideal proof"*) 
      unfold md_full. simpl. normalize.
      replace H256 with (fst (HLP (n * 32 + Z.min 32 (out_len - n * 32))))%Z.
(*      replace (HMAC256 (fst (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32)%Z))
              key0) with (fst (HMAC_DRBG_generate_helper_Z HMAC256 key0 V0 (n * 32 + Z.min 32 (out_len - n * 32))))%Z.*)
      simpl.
      apply andp_right. apply prop_right; repeat split; trivial.
      { subst HLP. apply HMAC_DRBG_generate_helper_Z_Zlength_fst; trivial.
        rewrite Zmin_spec. destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; try rewrite HZlength_V; omega.
        apply hmac_common_lemmas.HMAC_Zlength. }
      { subst HLP.
        apply HMAC_DRBG_generate_helper_Z_isbyteZ_fst; trivial.
          rewrite Zmin_spec. destruct (Z_lt_ge_dec 32 (out_len - (n * 32)%Z)) as [Hmin | Hmin]; [rewrite zlt_true by assumption | rewrite zlt_false by assumption]; try rewrite HZlength_V; omega. 
          apply isbyteZ_HMAC256. } 
      unfold md_full. simpl. cancel. 
      rewrite app_assoc.
      replace (map Vint
        (map Int.repr
           (sublist 0 (n * 32)%Z
              (snd (HLP (n * 32)%Z)))) ++
        map Vint
         (sublist 0 (Z.min 32 (out_len - (n * 32)%Z))
           (map Int.repr
              (fst
                 (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))))) with (map Vint
        (map Int.repr
           (sublist 0 ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))
              (snd
                 (HLP ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))))))).
      replace (out_len - (n * 32)%Z - Z.min 32 (out_len - (n * 32)%Z)) with (out_len - ((n * 32)%Z + Z.min 32 (out_len - (n * 32)%Z))) by omega.
      apply derives_refl.
      (*reflexivity.*) (*entailer!.*)
      rewrite <- map_app.
      rewrite sublist_map.
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
(*END OF INLINED LOOP BODY
Require Import hamcdrbg_verif_gen_whilebody.
  { (*LOOP BODY*) 
    semax_subcommand HmacDrbgVarSpecs HmacDrbgFunSpecs 
       f_mbedtls_hmac_drbg_random_with_add. 
    eapply gen_loopbodywith (after_update_state_abs :=after_update_state_abs). admit. (*TODO*) *)
  }

  (*POST LOOP*)
  
  assert (Hdone: done = out_len).
  {
    clear - HRE H2 Hout_len.
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
  replace (out_len - out_len) with 0 by omega. clear HRE H2 H5.
  change (list_repeat (Z.to_nat 0) Vundef) with (@nil val).
  rewrite app_nil_r.
  unfold hmac256drbgabs_common_mpreds.
  normalize. unfold hmac256drbg_relate.
  remember (hmac256drbgabs_update_value after_update_state_abs (fst (HLP out_len))) as ABS3.
  remember (hmac256drbgabs_to_state ABS3 initial_state) as CTX3.
  destruct ABS3. destruct CTX3 as [aa [bb [cc [dd [ee ff]]]]]. normalize.
  unfold hmac256drbgabs_to_state in HeqCTX3. subst initial_state. simpl in HeqCTX3. inv HeqCTX3.
  
  set (ctx3 := (mc1, (mc2, mc3),
          (map Vint (map Int.repr V0),
          (Vint (Int.repr reseed_counter0),
          (Vint (Int.repr entropy_len0),
          (Val.of_bool prediction_resistance0, Vint (Int.repr reseed_interval0))))))) in *.
  thaw StreamAdd.
  freeze [3;5] StreamOut. 

  (* mbedtls_hmac_drbg_update( ctx, additional, add_len ); *)
  (*subst add_len.*)
  forward_call (contents,
         additional, after_reseed_add_len, 
         (*ctx*)Vptr b i, ctx3,
         hmac256drbgabs_update_value after_update_state_abs (fst (HLP out_len)),
         kv, info_contents).
  { subst after_reseed_add_len. unfold hmac256drbg_relate. rewrite <- HeqABS3.
    subst ctx3. simpl. normalize. 
    apply andp_right. apply prop_right. repeat split; trivial.
    cancel. }
  { subst after_reseed_add_len. rewrite <- HeqABS3; simpl.
    split. destruct should_reseed; omega.
    split. assumption.
    split. destruct should_reseed; omega.
    split. assumption. assumption. }

  unfold hmac256drbgabs_common_mpreds. normalize.

  remember ((hmac256drbgabs_hmac_drbg_update
                (hmac256drbgabs_update_value after_update_state_abs (fst (HLP out_len)))
                (contents_with_add additional after_reseed_add_len contents))) as ABS4.
  set (ctx4 := hmac256drbgabs_to_state ABS4 ctx3) in *. rewrite <- HeqABS3 in HeqABS4.
  unfold hmac256drbg_relate.
  subst ctx3. simpl in ctx4. destruct ABS4. simpl in ctx4. subst ctx4. simpl. normalize.
  unfold hmac256drbgstate_md_info_pointer. simpl.
  freeze [2;3;4;5] FR5. 
  unfold_data_at 1%nat.
  freeze [1;2;4;5;6;7] FIELDS.
  forward. forward. forward.
  Exists (Vint (Int.repr 0)).
  apply andp_right. apply prop_right; trivial.
  apply andp_right. apply prop_right; split; trivial.
  thaw FIELDS. thaw FR5. thaw StreamOut.  
  unfold hmac256drbgabs_common_mpreds, hmac256drbg_relate, hmac256drbgstate_md_info_pointer.
  simpl. normalize.
  set (Gen := hmac256drbgabs_generate initial_state_abs s out_len
                (contents_with_add additional (Zlength contents) contents)) in *.
Transparent  hmac256drbgabs_generate.
  unfold hmac256drbgabs_generate in Gen.
Opaque hmac256drbgabs_generate.
  assert (F: 0 >? 256 = false) by reflexivity.
  simpl in HeqABS4.
  remember (HMAC256_DRBG_update (contents_with_add additional after_reseed_add_len contents) key0 V0) as UPD.
  destruct UPD; inv HeqABS4.
  remember after_update_state_abs as AUSA.
  destruct AUSA. simpl in AUV, AUK, HeqABS3. subst AUV AUK; inv HeqABS3.
  unfold hmac256drbgabs_reseed in after_reseed_state_abs.
  unfold mkSTREAM1 in STREAM1.
  subst initial_state_abs.
  set (MGen := mbedtls_HMAC256_DRBG_generate_function s (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance reseed_interval) out_len
             (contents_with_add additional (Zlength contents) contents)) in *.
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
      remember MGen as MGen'. subst MGen.
      rewrite Hout_lenb, F, ZLa, andb_negb_r in HeqMGen'.
      unfold DRBG_generate_function_helper in HeqMGen'.
      rewrite <- HeqMRES' in *.
      unfold HMAC256_DRBG_reseed_function, DRBG_reseed_function in HeqMRES'.
      rewrite andb_negb_r, ZLa in HeqMRES'.
      remember( get_entropy 256 32 32 prediction_resistance s) as ENT.
      destruct ENT; inversion HeqMRES'; clear HeqMRES'. subst z0 b0 s0.
      unfold HMAC256_DRBG_update in HeqUPD.
      remember (HMAC_DRBG_update HMAC256 (l3 ++ contents_with_add additional (Zlength contents) contents) key V) as UPD'.
      destruct UPD'; inversion H4; clear H4. subst z l1 l2. 
      destruct prediction_resistance.
      * simpl in HeqMGen'.
        remember (HMAC_DRBG_generate_helper_Z HMAC256 l4 l5 out_len) as GH.
        destruct GH. subst MGen'. subst Gen. simpl.
        apply andp_right. apply prop_right. repeat split; trivial.
        normalize. rewrite hmac_common_lemmas.HMAC_Zlength. 
        apply andp_right. apply prop_right. repeat split; trivial. apply isbyteZ_HMAC256. 
        rewrite sublist_firstn. cancel.
        unfold_data_at 3%nat. cancel.
        subst HLP. simpl in *.
        unfold HMAC_DRBG_update in HeqUPD, HeqUPD'.
        remember (l3 ++ contents_with_add additional (Zlength contents) contents).
        destruct l6; inv HeqUPD'.
        ++ symmetry in Heql6. apply app_eq_nil in Heql6. destruct Heql6; subst l3.
           unfold get_entropy in HeqENT. apply get_bytes_length in HeqENT. simpl in HeqENT. omega.
        ++ assert (CONT: contents_with_add additional 0 contents = []).
           { unfold contents_with_add; simpl. rewrite andb_false_r; trivial. }
           rewrite CONT in *. inv HeqUPD. 
           rewrite <- HeqGH; simpl. cancel.
      * rewrite orb_false_l in Heqsr. 
        simpl in HeqMGen'. rewrite <- Heqsr, ZLa, <- HeqENT, <- HeqUPD' in HeqMGen'.
        simpl in HeqMGen'.
        remember (HMAC_DRBG_generate_helper_Z HMAC256 l4 l5 out_len) as GH.
        destruct GH. subst MGen'. subst Gen. simpl.
        apply andp_right. apply prop_right. repeat split; trivial.
        normalize. rewrite hmac_common_lemmas.HMAC_Zlength. 
        apply andp_right. apply prop_right. repeat split; trivial. apply isbyteZ_HMAC256.
        rewrite sublist_firstn. cancel.
        simpl in *.
        unfold HMAC_DRBG_update in HeqUPD, HeqUPD'.
        remember (l3 ++ contents_with_add additional (Zlength contents) contents).
        destruct l6; inv HeqUPD'.
        ++ symmetry in Heql6. apply app_eq_nil in Heql6. destruct Heql6; subst l3.
           unfold get_entropy in HeqENT. apply get_bytes_length in HeqENT. simpl in HeqENT. omega.
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
    rewrite andb_negb_r, ZLa in HeqMRES'.
    remember (get_entropy 256 entropy_len entropy_len false s) as ENT.
    destruct ENT.
    - subst MRES'. 
      remember  MGen as MGen'. subst MGen.
Transparent mbedtls_HMAC256_DRBG_generate_function.
Transparent HMAC256_DRBG_generate_function.
      unfold mbedtls_HMAC256_DRBG_generate_function, HMAC256_DRBG_generate_function, DRBG_generate_function in HeqMGen'.
      rewrite Hout_lenb, F, ZLa, andb_negb_r in HeqMGen'.
      unfold DRBG_generate_function_helper in HeqMGen'. simpl in HeqMGen'.
      subst reseed_interval. rewrite H15 in HeqMGen'.
      remember (contents_with_add additional (Zlength contents) contents) as CONT.
      subst HLP. 
      destruct CONT.
      * rewrite Zlength_nil, <- HeqENT, F in HeqMGen'.
        remember (HMAC_DRBG_generate_helper_Z HMAC256 key V out_len) as p. destruct p.
        remember (HMAC_DRBG_update HMAC256 [] key l2) as q. destruct q.
        subst MGen'. subst Gen.
        unfold contents_with_add in HeqCONT.
        destruct (eq_dec (Zlength contents) 0); simpl in HeqCONT. 
        ++ rewrite e in *. rewrite (Zlength_nil_inv _ e) in *.
           simpl in na. destruct (initial_world.EqDec_Z (Zlength contents) 0); try solve [omega]; simpl in na.
           subst na; rewrite andb_false_r in *. 
           inv HeqAUSA. simpl.
           apply andp_right. apply prop_right. repeat split; trivial.
           normalize.
           unfold HMAC_DRBG_update, HMAC256_DRBG_update in *. inv Heqq.
           unfold HMAC_DRBG_update in HeqUPD.
           rewrite <- Heqp in *. inv HeqUPD. 
           apply andp_right. apply prop_right. repeat split; trivial.
           rewrite sublist_firstn. cancel.
           unfold_data_at 1%nat. cancel.
        ++ destruct (base.EqDec_val additional nullval); simpl in na, HeqCONT.
           2: subst contents; elim n; apply Zlength_nil.
           subst na. simpl in *.
           inv HeqUPD. inv HeqAUSA. inv Heqq.
           apply andp_right. apply prop_right. repeat split; trivial.
           rewrite hmac_common_lemmas.HMAC_Zlength. 
           normalize.
           apply andp_right. apply prop_right. repeat split; trivial.
              apply isbyteZ_HMAC256. 
           rewrite sublist_firstn, <- Heqp; simpl. cancel.
           unfold_data_at 1%nat. cancel.
     * unfold contents_with_add in HeqCONT.
       remember ((negb (eq_dec additional nullval) && negb (eq_dec (Zlength contents) 0))%bool) as f.
       destruct f; try discriminate. symmetry in Heqf; apply andb_true_iff in Heqf.
       destruct Heqf as [Heqf1 Heqf2]. apply negb_true_iff in Heqf1. apply negb_true_iff in Heqf2.
       destruct (eq_dec additional nullval); try discriminate.
       destruct (eq_dec (Zlength contents) 0); try discriminate.
       destruct (base.EqDec_val additional nullval). { subst additional. elim n; trivial. }
       destruct (initial_world.EqDec_Z (Zlength contents) 0); simpl in na. { omega. }
       subst na. simpl in HeqAUSA.
       unfold HMAC256_DRBG_update in *. subst stream1 contents.
       remember (HMAC_DRBG_update HMAC256 (z::CONT) key V) as p; destruct p. inv HeqAUSA.
       remember (HMAC_DRBG_generate_helper_Z HMAC256 l2 l3 out_len) as w; destruct w.
       simpl in HeqUPD. inv HeqUPD. 
       remember (HMAC_DRBG_update HMAC256 (z :: CONT) l2 l4) as q; destruct q.
       subst Gen. 
       apply andp_right. apply prop_right. repeat split; trivial.
       simpl. 
       rewrite sublist_firstn. cancel.
       unfold HMAC_DRBG_update in Heqq. inv Heqq. simpl. normalize.
       apply andp_right. apply prop_right. repeat split; trivial. cancel.
       unfold_data_at 1%nat. cancel.
  - subst HLP MRES'.  
      remember  MGen as MGen'. subst MGen.
Transparent mbedtls_HMAC256_DRBG_generate_function.
Transparent HMAC256_DRBG_generate_function.
      unfold mbedtls_HMAC256_DRBG_generate_function, HMAC256_DRBG_generate_function, DRBG_generate_function in HeqMGen'.
      rewrite Hout_lenb, F, ZLa, andb_negb_r in HeqMGen'.
      unfold DRBG_generate_function_helper in HeqMGen'. simpl in HeqMGen'.
      subst reseed_interval. rewrite H15 in HeqMGen'.
      remember (contents_with_add additional (Zlength contents) contents) as CONT.
      destruct CONT.
      * rewrite Zlength_nil, <- HeqENT, F in HeqMGen'.
        remember (HMAC_DRBG_generate_helper_Z HMAC256 key V out_len) as p. destruct p.
        remember (HMAC_DRBG_update HMAC256 [] key l2) as q. destruct q.
        subst MGen'. subst Gen.
        unfold contents_with_add in HeqCONT.
        destruct (eq_dec (Zlength contents) 0); simpl in HeqCONT. 
        ++ rewrite e0 in *. rewrite (Zlength_nil_inv _ e0) in *.
           simpl in na. destruct (initial_world.EqDec_Z (Zlength contents) 0); try solve [omega]; simpl in na.
           subst na; rewrite andb_false_r in *. 
           inv HeqAUSA. simpl.
           apply andp_right. apply prop_right. repeat split; trivial.
           normalize.
           unfold HMAC_DRBG_update, HMAC256_DRBG_update in *. inv Heqq.
           unfold HMAC_DRBG_update in HeqUPD. rewrite <- Heqp in *. inv HeqUPD. 
           apply andp_right. apply prop_right. repeat split; trivial.
           rewrite sublist_firstn. cancel.
           unfold_data_at 1%nat. cancel.
        ++ destruct (base.EqDec_val additional nullval); simpl in na, HeqCONT.
           2: subst contents; elim n; apply Zlength_nil.
           subst na. simpl in *.
           inv HeqUPD. inv HeqAUSA. inv Heqq.
           apply andp_right. apply prop_right. repeat split; trivial.
           rewrite hmac_common_lemmas.HMAC_Zlength. 
           normalize.
           apply andp_right. apply prop_right. repeat split; trivial.
             apply isbyteZ_HMAC256.
           rewrite sublist_firstn, <- Heqp; simpl. cancel.
           unfold_data_at 1%nat. cancel.
     * unfold contents_with_add in HeqCONT.
       remember ((negb (eq_dec additional nullval) && negb (eq_dec (Zlength contents) 0))%bool) as f.
       destruct f; try discriminate. symmetry in Heqf; apply andb_true_iff in Heqf.
       destruct Heqf as [Heqf1 Heqf2]. apply negb_true_iff in Heqf1. apply negb_true_iff in Heqf2.
       destruct (eq_dec additional nullval); try discriminate.
       destruct (eq_dec (Zlength contents) 0); try discriminate.
       destruct (base.EqDec_val additional nullval). { subst additional. elim n; trivial. }
       destruct (initial_world.EqDec_Z (Zlength contents) 0); simpl in na. { omega. }
       subst na. simpl in HeqAUSA.
       unfold HMAC256_DRBG_update in *. subst stream1 contents.
       remember (HMAC_DRBG_update HMAC256 (z::CONT) key V) as p; destruct p. inv HeqAUSA.
       remember (HMAC_DRBG_generate_helper_Z HMAC256 l1 l2 out_len) as w; destruct w.
       simpl in HeqUPD. inv HeqUPD. 
       remember (HMAC_DRBG_update HMAC256 (z :: CONT) l1 l3) as q; destruct q.
       subst Gen. 
       apply andp_right. apply prop_right. repeat split; trivial.
       simpl. 
       rewrite sublist_firstn. cancel.
       unfold HMAC_DRBG_update in Heqq. inv Heqq. simpl. normalize.
       apply andp_right. apply prop_right. repeat split; trivial. cancel.
       unfold_data_at 1%nat. cancel.
Time Qed. (*157.766 secs (138.203u,0.093s) if loopbody is solved by exfalso; apply FALSE*)
(*189.172 secs (159.14u,0.171s) (successful), and 12m30s compilation time when loopbody proof is inlined*)