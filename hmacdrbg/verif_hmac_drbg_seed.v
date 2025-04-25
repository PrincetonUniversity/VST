Require Import VST.floyd.proofauto.
Require Import VST.floyd.compat. Import NoOracle.
Import ListNotations.
Require Import VST.zlist.sublist.

Require Import sha.HMAC256_functional_prog.
Require Import sha.general_lemmas.
Require Import sha.spec_sha.

Require Import hmacdrbg.entropy.
Require Import hmacdrbg.entropy_lemmas.
Require Import hmacdrbg.DRBG_functions.
Require Import hmacdrbg.HMAC_DRBG_algorithms.
Require Import hmacdrbg.HMAC256_DRBG_functional_prog.
Require Import hmacdrbg.hmac_drbg.
Require Import hmacdrbg.HMAC_DRBG_pure_lemmas.
Require Import hmacdrbg.spec_hmac_drbg.
Require Import hmacdrbg.HMAC_DRBG_common_lemmas.
Require Import hmacdrbg.spec_hmac_drbg_pure_lemmas.
Require Import VST.floyd.library.

Require Import hmacdrbg.verif_hmac_drbg_seed_common.

Opaque mbedtls_HMAC256_DRBG_reseed_function.
Opaque initial_key. Opaque initial_value.
Opaque mbedtls_HMAC256_DRBG_reseed_function.
Opaque repeat.

Lemma body_hmac_drbg_seed_256: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_seed hmac_drbg_seed_inst256_spec.
Proof.
  start_function.
  abbreviate_semax.
  destruct H as [HDlen1 [HDlen2 RES]]. destruct handle_ss as [handle ss]. simpl in RES.
  
  rewrite data_at_isptr with (p:=ctx). Intros.
  destruct ctx; try contradiction.
  unfold_data_at 1%nat.
  destruct Ctx as [MdCTX [V [RC [EL [PR RI]]]]]. simpl.
  destruct MdCTX as [M1 [M2 M3]].
  freeze [1;2;3;4;5] FIELDS.
  rewrite field_at_compatible'. Intros. rename H into FC_mdx.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial. rewrite ptrofs_add_repr_0_r.
  freeze [0;2;3;4;5;6] FR0.
  Time forward_call ((M1,(M2,M3)), Vptr b i, shc, Vint (Int.repr 1), info, gv).

  Intros v. rename H into Hv.
  freeze [0] FR1.
  forward. thaw FR1.
  forward_if.
  { destruct Hv; try lia. rewrite if_false; trivial. clear H. subst v.
    forward. simpl. Exists (Int.repr (-20864)).
    rewrite Int.eq_true.
    entailer!. thaw FR0. cancel.
    unfold_data_at 2%nat. thaw FIELDS. cancel.
    rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true; simpl; trivial. rewrite ptrofs_add_repr_0_r; auto. }
  subst v. clear Hv. simpl.
  Intros. Intros p.

  (*Alloction / md_setup succeeded. Now get md_size*)
  deadvars!.
  forward_call info.

  (*call mbedtls_md_hmac_starts( &ctx->md_ctx, ctx->V, md_size )*)
  thaw FR0. subst.
  assert (ZL_VV: Zlength initial_key =32) by reflexivity.
  thaw FIELDS.
  freeze [4;5;6;7] FIELDS1.
  rewrite field_at_compatible'. Intros. rename H into FC_V.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial.
  rewrite <- ZL_VV.
  freeze [0;5;6;7;9] FR2.
  forward_call (Vptr b i, shc, ((info,(M2,p)):mdstate), 32, initial_key, b, Ptrofs.add i (Ptrofs.repr 12), shc, gv).
  { split3; auto. split; auto. computable.
  }

  (*call  memset( ctx->V, 0x01, md_size )*)
  freeze [0;1;3;4;5] FR3.
 forward_call
  (shc, Vptr b (Ptrofs.add i (Ptrofs.repr 12)), 32, Int.one).
  { rewrite sepcon_comm. apply sepcon_derives.
     - apply data_at_memory_block.
     - cancel. }
  (*ctx->reseed_interval = MBEDTLS_HMAC_DRBG_RESEED_INTERVAL;*)
  rewrite ZL_VV.
  thaw FR3. thaw FR2. unfold md_relate. simpl.
  replace_SEP 2 (field_at shc t_struct_hmac256drbg_context_st [StructField _md_ctx] (info, (M2, p)) (Vptr b i)). {
    entailer!. rewrite field_at_data_at.
    simpl. rewrite field_compatible_field_address by auto with field_compatible. simpl.
    rewrite ptrofs_add_repr_0_r.
    cancel.
  }
  thaw FIELDS1. forward.
  freeze [0;4;5;6;7] FIELDS2.
  freeze [0;1;2;3;4;5;6;7;8;9] ALLSEP.

  forward_if (temp _t'4 (Vint (Int.repr 32))).
  { discriminate. }
  { clear H.
    forward_if.
    + discriminate. 
    + clear H. forward. forward. entailer!.  }
  forward.
  deadvars!.

  (*NEXT INSTRUCTION:  ctx->entropy_len = entropy_len * 3 / 2*)
  thaw ALLSEP. thaw FIELDS2. forward.

  assert (FOURTYEIGHT: Int.unsigned (Int.mul (Int.repr 32) (Int.repr 3)) / 2 = 48).
  { rewrite mul_repr. simpl; auto.
(*    all: rewrite Int.unsigned_repr by rep_lia; reflexivity.  for Coq 8.13 and before *)
  }
  set (myABS := HMAC256DRBGabs initial_key initial_value rc 48 pr_flag 10000) in *.
  assert (myST: exists ST:hmac256drbgstate, ST =
    ((info, (M2, p)), (map Vint (repeat Int.one 32), (Vint (Int.repr rc),
        (Vint (Int.repr 48), (bool2val pr_flag, Vint (Int.repr 10000))))))). eexists; reflexivity.
  destruct myST as [ST HST].

  freeze [0;2;3;4;8] FR_CTX.
  freeze [1;6;7;8] KVStreamInfoDataFreeBlk.

  (*NEXT INSTRUCTION: mbedtls_hmac_drbg_reseed( ctx, custom, len ) *)
  freeze [1;2;3;4] INI.
  replace_SEP 0 (
         data_at shc t_struct_hmac256drbg_context_st ST (Vptr b i) *
         hmac256drbg_relate myABS ST).
  { simpl liftx. entailer!. thaw INI. clear - FC_V. (*KVStreamInfoDataFreeBlk.*) thaw FR_CTX.
    unfold_data_at 2%nat.
    cancel. simpl. unfold md_full; simpl.
    rewrite field_at_data_at; simpl.
    unfold field_address. rewrite if_true; simpl; trivial.
    entailer!.
    apply UNDER_SPEC.REP_FULL.
  }

  clear INI.
  thaw KVStreamInfoDataFreeBlk. freeze [6] OLD_MD.
  forward_call (Data, data, shd, Zlength Data, Vptr b i, shc, ST, myABS, Info, s, gv).
  { unfold hmac256drbgstate_md_info_pointer.
    subst ST; simpl. cancel.
  }
  { split; auto. compute; congruence. subst myABS; simpl. rewrite <- initialize.max_unsigned_modulus in *; rewrite hmac_pure_lemmas.ptrofs_max_unsigned_eq.
    split. lia.
       unfold contents_with_add. simple_if_tac. lia. rewrite Zlength_nil; lia.
  }

  Intros v.
  assert (ZLc': Zlength (contents_with_add data (Zlength Data) Data) = 0 \/
                 Zlength (contents_with_add data (Zlength Data) Data) = Zlength Data).
         { unfold contents_with_add. simple_if_tac. right; trivial. left; trivial. }
  forward.
  deadvars!. 
  forward_if (v = nullval).
  { rename H into Hv. forward. simpl. Exists v.
    apply andp_right. apply prop_right; split; trivial.
    unfold reseedPOST.

    remember ((zlt 256 (Zlength Data) || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data)) %bool) as d.
    unfold myABS in Heqd; simpl in Heqd.
    destruct (zlt 256 (Zlength Data)); simpl in Heqd.
    + lia.
    + destruct (zlt 384 (48 + Zlength Data)); simpl in Heqd; try lia.
      subst d.
      unfold hmac256drbgstate_md_info_pointer, hmac256drbg_relate; simpl. Intros.
      rename H into RV.
      remember (mbedtls_HMAC256_DRBG_reseed_function s myABS
         (contents_with_add data (Zlength Data) Data)) as MRS.
      rewrite (ReseedRes _ _ _ RV). cancel.
      unfold return_value_relate_result in RV.
      assert (ZLc'256F: Zlength (contents_with_add data (Zlength Data) Data) >? 256 = false).
      { apply Zgt_is_gt_bool_f. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc'; lia. }
      unfold hmac256drbgabs_common_mpreds, hmac256drbgstate_md_info_pointer.
      destruct MRS.
      - exfalso. inv RV. simpl in Hv. discriminate.
      - simpl. Intros. Exists p. thaw OLD_MD. cancel.
        subst myABS. rewrite <- instantiate256_reseed in HeqMRS; trivial.
        rewrite RES in HeqMRS. inv HeqMRS. 
  }
  { rename H into Hv. forward. entailer!.
    apply negb_false_iff in Hv.
    symmetry in Hv; apply binop_lemmas2.int_eq_true in Hv; subst v. trivial.
  }
  deadvars!. Intros. subst v. unfold reseedPOST.

  remember ((zlt 256 (Zlength Data)
          || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data))%bool) as d.
  destruct d; Intros. inv H.

  assert (ZLc'256F: Zlength (contents_with_add data (Zlength Data) Data) >? 256 = false).
      { destruct ZLc' as [HH | HH]; rewrite HH. reflexivity.
        apply Zgt_is_gt_bool_f. lia. }
  subst myABS.
  rewrite <- instantiate256_reseed, RES; trivial. clear - SH RES HST ZLc'256F.
  destruct handle as [[[[newV newK] newRC] dd] newPR].
  unfold hmac256drbgabs_common_mpreds.
  simpl. subst ST. unfold hmac256drbgstate_md_info_pointer. simpl.
  unfold_data_at 1%nat.
  freeze [0;1;2;4;5;6;7;8;9;10;11;12] ALLSEP.
  forward. forward.
 
  Exists Int.zero. simpl.
  apply andp_right. apply prop_right; split; trivial.
  Exists p.
  thaw ALLSEP. thaw OLD_MD. rewrite <- instantiate256_reseed, RES; trivial. simpl. 
  cancel; entailer!.
  unfold_data_at 1%nat. cancel.
  apply hmac_interp_empty.
Time Qed. (*Coq8.10.1: 6.3s; Coq8.6: 32secs*)
