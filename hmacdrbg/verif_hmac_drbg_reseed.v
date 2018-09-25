Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import hmacdrbg.entropy.
Require Import hmacdrbg.entropy_lemmas.
Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require Import hmacdrbg.verif_hmac_drbg_reseed_common.

Opaque hmac256drbgabs_reseed.
Opaque mbedtls_HMAC256_DRBG_reseed_function. 

Lemma body_hmac_drbg_reseed: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
       f_mbedtls_hmac_drbg_reseed hmac_drbg_reseed_spec.
Proof.
  start_function.
  rename v_seed into seed.
  destruct I.
  destruct initial_state as [md_ctx' [V' [reseed_counter' [entropy_len' [prediction_resistance' reseed_interval']]]]].
  unfold hmac256drbg_relate.
  Intros.
  rename H into XH1.
  rename H0 into XH2.
  rename H1 into XH3.
  rename H2 into XH4.
  rename H3 into El2.
  rename H4 into XH6.
  rename H5 into XH7.
  rename H6 into XH8.
  rename H7 into XH9.
  rename H8 into XH10.
  rename H9 into XH11.
  rename H10 into XH12.
  simpl in XH2, XH4, El2, XH6, XH7 |- *.
  rewrite da_emp_isptrornull. (*needed later*)
  rewrite data_at_isptr with (p:=ctx).
  Intros.

  (* entropy_len = ctx->entropy_len *)
  remember (contents_with_add additional add_len contents) as contents'.
  assert (ZLc': Zlength contents' = 0 \/ Zlength contents' = Zlength contents).
    { subst contents'. unfold contents_with_add.
      destruct (eq_dec add_len 0); simpl.
        rewrite andb_false_r. left; apply Zlength_nil.
        destruct (Memory.EqDec_val additional nullval); simpl. left; apply Zlength_nil.
        right; trivial.
    }

  freeze [0;1;3;4;5;6] FR1.
  forward. (*{ rewrite <- H7; entailer!. }*)

  remember (orb (zlt 256 add_len) (zlt 384 (entropy_len + add_len))) as add_len_too_high.

  (* if (len > MBEDTLS_HMAC_DRBG_MAX_INPUT ||
        entropy_len + len > MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT) *)
  freeze [0;1] FR2.
  forward_if (temp _t'1 (Val.of_bool add_len_too_high)).
  { forward. entailer!. }
  { forward. entailer!. simpl.
      unfold Int.ltu; simpl.
      rewrite Int.unsigned_repr by rep_omega.
      rewrite Int.unsigned_repr_eq, Zmod_small.
      + destruct (zlt 384 (entropy_len + (Zlength contents))); simpl; try reflexivity.
      + rep_omega.
  }

  forward_if. 
  { rewrite H in *. subst add_len_too_high. forward.
    Exists (Vint (Int.neg (Int.repr 5))). normalize. entailer!.
    unfold reseedPOST. simpl; rewrite <- Heqadd_len_too_high.
    (*remember (zlt 256 (Zlength contents) || zlt 384 (entropy_len + Zlength contents))%bool as c.
    destruct c; simpl in Heqadd_len_too_high; try discriminate.*)
    normalize. apply andp_right. apply prop_right; repeat split; trivial.
    thaw FR2. thaw FR1. cancel.
  }
  Intros. rewrite H in *; clear H add_len_too_high.
  symmetry in Heqadd_len_too_high; apply orb_false_iff in Heqadd_len_too_high; destruct Heqadd_len_too_high.

  assert (AL256: 256 >= add_len).
  { destruct (zlt 256 add_len); try discriminate; trivial. }
  assert (EL384 : 384 >= entropy_len + add_len).
  { destruct ( zlt 384 (entropy_len + add_len)); try discriminate; trivial. }

  thaw FR2. thaw FR1. freeze [1;2;3;4;5;6] FR3.
  (* memset( seed, 0, MBEDTLS_HMAC_DRBG_MAX_SEED_INPUT ); *)
  forward_call (Tsh, seed, 384, Int.zero).
  { rewrite data_at__memory_block.
    change (sizeof (*cenv_cs*) (tarray tuchar 384)) with 384.
    normalize. cancel.
  }

  (*freeze [1;2;3;4;5;6] FR3.*)
  assert_PROP (field_compatible (tarray tuchar 384) [] seed) as Hfield by entailer!.
  replace_SEP 0 ((data_at Tsh (tarray tuchar entropy_len)
         (list_repeat (Z.to_nat entropy_len) (Vint Int.zero)) seed) * (data_at Tsh (tarray tuchar (384 - entropy_len))
         (list_repeat (Z.to_nat (384 - entropy_len)) (Vint Int.zero)) (offset_val entropy_len seed))).
  {
    (*subst entropy_len.*)
    erewrite <- data_at_complete_split with (length:=384)(AB:=list_repeat (Z.to_nat 384) (Vint Int.zero)); repeat rewrite Zlength_list_repeat; trivial; try omega.
    solve [go_lower; apply derives_refl]. 
    solve [rewrite Zplus_minus; assumption].
    rewrite list_repeat_app, Z2Nat.inj_sub; try omega. rewrite le_plus_minus_r; trivial. apply Z2Nat.inj_le; try omega.
  }
  Intros.

  replace_SEP 0 (memory_block Tsh entropy_len seed).
  {
    (*subst entropy_len.*) go_lower.
     eapply derives_trans. apply data_at_memory_block. simpl. rewrite Z.max_r, Z.mul_1_l; auto.
  }

  (* get_entropy(seed, entropy_len ) *)
  thaw FR3. freeze [1;2;3;4;6;7] FR4. 
  forward_call (Tsh, s, seed, entropy_len).
  { split. split; try omega. rep_omega.
    apply writable_share_top.
(*
    subst entropy_len; auto.*)
  }
  Intros vret. rename H1 into ENT.
  assert (AL256': add_len >? 256 = false).
  { remember (add_len >? 256) as d.
    destruct d; symmetry in Heqd; trivial.
    apply Zgt_is_gt_bool in Heqd.
    destruct (zlt 256 add_len); try discriminate; omega.
  }
  assert (EAL256': (entropy_len + add_len)  >? 384 = false).
  { remember (entropy_len + add_len >? 384) as d.
    destruct d; symmetry in Heqd; trivial.
    apply Zgt_is_gt_bool in Heqd.
    destruct (zlt 384 (entropy_len + add_len)); try discriminate; omega.
  }

  remember (Zlength (contents_with_add additional (Zlength contents) contents)) as ZLa.
  assert (ZLa256: ZLa >? 256 = false).
  { subst ZLa contents' add_len; destruct ZLc' as [PP | PP]; rewrite PP; trivial. }
  
  (* if( get_entropy(seed, entropy_len ) != 0 ) *)
  freeze [0;1;2] FR5.
  forward_if (vret=Vzero).
(*
  forward_if (PROP  (vret=Vzero)
      LOCAL  (temp _t'2 vret;
      temp _entropy_len (Vint (Int.repr entropy_len));
      lvar _seed (tarray tuchar 384) seed; temp _ctx ctx;
      temp _additional additional; temp _len (Vint (Int.repr add_len));
      gvars gv)
      SEP (FRZL FR5)
  ).
*)
  {
    (* != 0 case *)
    forward.
    Exists (Vint (Int.neg (Int.repr (9)))). entailer!. 
    unfold reseedPOST.
    remember ((zlt 256 (Zlength contents)
       || zlt 384
            (hmac256drbgabs_entropy_len
               (HMAC256DRBGabs key V reseed_counter entropy_len prediction_resistance
                  reseed_interval) + (Zlength contents)))%bool) as z.
    destruct z.
    { exfalso. simpl in Heqz. rewrite H, H0 in Heqz. inv Heqz. }
    clear Heqz.
    unfold return_value_relate_result, get_entropy in ENT.
    simpl in ENT.
    remember (ENTROPY.get_bytes (Z.to_nat entropy_len) s) as  GE.
    destruct GE.
    + inv ENT. simpl in H1; discriminate.
    + thaw FR5. unfold GetEntropy_PostSep, get_entropy.
      Transparent  hmac256drbgabs_reseed. unfold hmac256drbgabs_reseed. Opaque hmac256drbgabs_reseed. 
      rewrite <- HeqGE; simpl.
      remember (mbedtls_HMAC256_DRBG_reseed_function s
              (HMAC256DRBGabs key V reseed_counter entropy_len
                 prediction_resistance reseed_interval)
              (contents_with_add additional (Zlength contents) contents)) as MRF.
      Transparent mbedtls_HMAC256_DRBG_reseed_function. 
         unfold mbedtls_HMAC256_DRBG_reseed_function in HeqMRF.
      Opaque mbedtls_HMAC256_DRBG_reseed_function. 
      simpl in HeqMRF. rewrite andb_negb_r, ZLa256 in HeqMRF. 
      unfold get_entropy in HeqMRF. rewrite <- HeqGE in HeqMRF.
      subst MRF. 
      unfold hmac256drbgstate_md_info_pointer, hmac256drbgabs_common_mpreds; simpl.
      entailer!. thaw FR4; cancel.
      rewrite data_at__memory_block. entailer!.
      destruct seed; inv Pseed. unfold offset_val.
      rewrite <- Ptrofs.repr_unsigned with (i:=i). 
      assert (XX: sizeof (tarray tuchar 384) = entropy_len + (384 - entropy_len)) by (simpl; omega). 
      rewrite XX.
      rewrite (memory_block_split Tsh b (Ptrofs.unsigned i) entropy_len (384 - entropy_len)), ptrofs_add_repr; try omega.
      cancel.
      eapply derives_trans. apply data_at_memory_block.
          simpl. rewrite Z.max_r, Z.mul_1_l; try omega; auto.
      rewrite Zplus_minus.
      assert (Ptrofs.unsigned i >= 0) by (pose proof (Ptrofs.unsigned_range i); omega).
      split. omega.
      clear - Hfield. red in Hfield; simpl in Hfield. omega.
  }
  {
    forward.
    entailer!. clear FR4 FR5. (*subst add_len.*)
    apply negb_false_iff in H1. symmetry in H1; apply binop_lemmas2.int_eq_true in H1.
    subst vret; split; trivial.
  }
  Intros. subst vret. unfold return_value_relate_result in ENT.
  (* now that we know entropy call succeeded, use that fact to simplify the SEP clause *)
  remember (entropy.ENTROPY.get_bytes (Z.to_nat entropy_len) s) as entropy_result.
  unfold entropy.get_entropy in ENT;
  rewrite <- Heqentropy_result in ENT.
  destruct entropy_result; [|
    normalize;
    simpl in ENT; destruct e; [inversion ENT | inversion ENT ]
    ].
  2: solve [ destruct ENT_GenErrAx as [EC1 _]; elim EC1; trivial ].
  clear ENT.

  rename l into entropy_bytes.
  thaw FR5. thaw FR4. unfold GetEntropy_PostSep. rewrite <- Heqentropy_result.
  deadvars!.
  subst MORE_COMMANDS; unfold abbreviate.
  subst entropy_len'. subst POSTCONDITION; unfold abbreviate.
  rewrite <- XH7.
  simple eapply reseed_REST  with (s0:=s0)(contents':=contents'); try eassumption;
    auto.
idtac "Timing the Qed of drbg_reseed (goal: 25secs)". omega. 
Time Qed. (*May23th, Coq8.6:12secs
           Feb 23 2017: Finished transaction in 105.344 secs (74.078u,0.015s) (successful)*)
          (*earlier Coq8.5pl2: 24secs*)
