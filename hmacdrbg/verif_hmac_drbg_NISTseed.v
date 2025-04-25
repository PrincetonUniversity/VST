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

Module Instantiate_eq.

Definition OptionalNonce: option (list byte) := None. (*The implementation takes nonce from entropy, using the el*3/2 calculation*)

(*NIST, Section 10.1: highest supported sec strength is given by the hash function's
security strength for preimage resistance. For SHA256, this is
(according to NIST SP 800-107, Table 1, page 11) 256 bits. See also Appendix B2 of NIST SP 800-90A. *)
Definition highest_supported_security_strength := 32. (* in bytes -- see comment for reseed*)

(*Q: should we use the sec strength of HMAC, calculated according to Section 5.3.4 of
NIST SP 800-107 instead?*)
Definition requested_security_strength:= 32.  (*same as in reseed*)


Definition prediction_resistance_supported:bool:=true.

Definition mbedtls_HMAC256_DRBG_instantiate_function (entropy_stream: ENTROPY.stream)
         entropy_len pr_flag (personalization_string: list byte): ENTROPY.result DRBG_state_handle :=
    HMAC256_DRBG_instantiate_function entropy_len entropy_len OptionalNonce
            highest_supported_security_strength max_personalization_string_length
            prediction_resistance_supported entropy_stream
            requested_security_strength pr_flag personalization_string.

Definition entlen:Z := 32.


Parameter Entropy_addSuccess1: forall n m s s1 l1 s2 l2,
        ENTROPY.get_bytes n s = ENTROPY.success l1 s1 ->
        ENTROPY.get_bytes m s1 = ENTROPY.success l2 s2 ->
        ENTROPY.get_bytes (n+m) s = ENTROPY.success (l1++l2) s2.

Parameter Entropy_addSuccess2: forall n m s s1 l1 s2 e,
        ENTROPY.get_bytes n s = ENTROPY.success l1 s1 ->
        ENTROPY.get_bytes m s1 = ENTROPY.error e s2 ->
        ENTROPY.get_bytes (n+m) s = ENTROPY.error e s2.

Parameter Entropy_addError: forall n m s s1 e, ENTROPY.get_bytes n s = ENTROPY.error e s1 ->
        ENTROPY.get_bytes (n+m) s = ENTROPY.error e s1.

Lemma Entropy_le n s l ss: ENTROPY.success l ss = ENTROPY.get_bytes n s ->
  forall m, (m <= n)%nat -> exists l' s', ENTROPY.success l' s' = ENTROPY.get_bytes m s.
Proof. intros.
  remember (ENTROPY.get_bytes m s) as d.
  destruct d. eexists; eexists; trivial.
  symmetry in H; symmetry in Heqd.
  specialize (Entropy_addError _ (n-m)%nat _ _ _ Heqd).
     rewrite Nat.add_comm, Nat.sub_add; trivial.
  intros HH; rewrite HH in *. discriminate.
Qed.

Lemma Entropy_addSuccess3: forall n m s ss l,
        ENTROPY.get_bytes n s = ENTROPY.success l ss -> (m <= n)%nat ->
        exists l1 s1, ENTROPY.get_bytes m s = ENTROPY.success l1 s1 /\ 
        exists l2, ENTROPY.get_bytes (n-m)%nat s1 = ENTROPY.success l2 ss /\ l=l1++l2.
Proof. intros.
  remember (ENTROPY.get_bytes m s). destruct r.
+ exists l0, s0; split; trivial.
  symmetry in Heqr.
  remember (ENTROPY.get_bytes (n-m)%nat s0) as t.
  destruct t; symmetry in Heqt.
  - specialize (Entropy_addSuccess1 m (n-m)%nat s s0). rewrite Heqr, Heqt, Nat.add_comm, Nat.sub_add; trivial.
    intros X. rewrite (X _ _ _ (eq_refl _) (eq_refl _)) in H; clear X Heqr Heqt. inv H. exists l1; split; trivial.
  - specialize (Entropy_addSuccess2 m (n-m)%nat s s0). rewrite Heqr, Heqt, Nat.add_comm, Nat.sub_add; trivial.
    intros X. rewrite (X _ _ _ (eq_refl _) (eq_refl _)) in H; clear X Heqr Heqt. inv H.
+ symmetry in Heqr; exfalso. 
  specialize (Entropy_addError m (n-m)%nat s). rewrite Heqr, Nat.add_comm, Nat.sub_add; trivial.
  intros X. rewrite (X _ _ (eq_refl _)) in H. inv H.
Qed.

Lemma instantiate_eq es prflag pers:
      instantiate_function_256 es prflag pers =
      mbedtls_HMAC256_DRBG_instantiate_function es entlen prflag pers.
Proof. unfold instantiate_function_256, mbedtls_HMAC256_DRBG_instantiate_function, 
   HMAC256_DRBG_instantiate_function, DRBG_instantiate_function, HMAC256_DRBG_instantiate_algorithm; simpl; intros.
destruct (Zlength pers >? max_personalization_string_length).
+ destruct prflag; trivial.
+ unfold entlen, get_entropy; simpl. 
  remember (ENTROPY.get_bytes 48 es) as r.
  destruct r; symmetry in Heqr. 
  - destruct (Entropy_addSuccess3 _ 32 _ _ _ Heqr) as [l1 [s1 [E32 [l2 [E16 L]]]]]. lia.
    simpl in E16. rewrite E32, E16; subst.
    unfold HMAC_DRBG_instantiate_algorithm. simpl. rewrite app_assoc. destruct prflag; trivial.
  - remember  (ENTROPY.get_bytes 32 es) as t; destruct t; symmetry in Heqt.
    * remember (ENTROPY.get_bytes 16 s0) as w; destruct w; symmetry in Heqw.
      ++ specialize (Entropy_addSuccess1 _ _ _ _ _ _ _ Heqt Heqw). simpl. rewrite Heqr. congruence.
      ++ specialize (Entropy_addSuccess2 _ _ _ _ _ _ _ Heqt Heqw). simpl. rewrite Heqr; intros X. inv X; destruct prflag; trivial.
    * specialize (Entropy_addError _ 16 _ _ _ Heqt). simpl. rewrite Heqr; intros X. inv X; destruct prflag; trivial.
Qed.

Lemma instantiate_reseed d s pr_flag rc ri (ZLc'256F : (Zlength d >? 256) = false):
      mbedtls_HMAC256_DRBG_instantiate_function s entlen pr_flag  d =
      mbedtls_HMAC256_DRBG_reseed_function s (HMAC256DRBGabs initial_key initial_value rc 48 pr_flag ri) d.
Proof. rewrite <- instantiate256_reseed, instantiate_eq; trivial. Qed.

Opaque mbedtls_HMAC256_DRBG_reseed_function.
Opaque initial_key. Opaque initial_value.
Opaque mbedtls_HMAC256_DRBG_reseed_function.
Opaque repeat. 

(*specification for the expected case, in which 0<=len<=256.
  But use mbedtls_HMAC256_DRBG_instantiate_function PROP of PRE and assume SUCCESS*)
Definition hmac_drbg_seed_simple_spec :=
  DECLARE _mbedtls_hmac_drbg_seed
   WITH dp:_, ctx: val, info:val, len: Z, data:val, Data: list byte,
        Ctx: hmac256drbgstate,
        Info: md_info_state, s:ENTROPY.stream, rc:Z, pr_flag:bool, ri:Z,
        handle_ss: DRBG_state_handle * ENTROPY.stream, gv: globals
    PRE [(*_ctx OF*) tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         (*_md_info OF*) tptr (Tstruct _mbedtls_md_info_t noattr),
         (*_custom OF*) tptr tuchar, (*_len OF*) tuint ]
       PROP (len = Zlength Data /\ 0 <= len <=256 /\
             mbedtls_HMAC256_DRBG_instantiate_function s entlen pr_flag
                                       (contents_with_add data (Zlength Data) Data)
             = ENTROPY.success (fst handle_ss) (snd handle_ss))
       (*LOCAL (temp _ctx ctx; temp _md_info info;
              temp _len (Vint (Int.repr len)); temp _custom data; gvars gv)*)
       PARAMS (ctx; info; data; Vint (Int.repr len)) GLOBALS (gv)
       SEP (
         data_at Ews t_struct_hmac256drbg_context_st Ctx ctx;
         preseed_relate dp rc pr_flag ri Ctx;
         data_at Ews t_struct_mbedtls_md_info Info info;
         da_emp Ews (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
         K_vector gv; Stream s; mem_mgr gv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp (Vint ret_value))
       SEP (data_at Ews t_struct_mbedtls_md_info Info info;
            da_emp Ews (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
            K_vector gv;
            if Int.eq ret_value (Int.repr (-20864))
            then data_at Ews t_struct_hmac256drbg_context_st Ctx ctx *
                 preseed_relate dp rc pr_flag ri Ctx * Stream s
            else md_empty (fst Ctx) *
                 EX p:val,
                 match (fst Ctx, fst handle_ss) with ((M1, (M2, M3)), ((((newV, newK), newRC), newEL), newPR))
                   => let CtxFinal := ((info, (M2, p)), (map Vubyte newV, (Vint (Int.repr newRC), (Vint (Int.repr 32), (bool2val newPR, Vint (Int.repr 10000)))))) in
                      !!(ret_value = Int.zero) 
                      && data_at Ews t_struct_hmac256drbg_context_st CtxFinal ctx *
                         hmac256drbg_relate (HMAC256DRBGabs newK newV newRC 32 newPR 10000) CtxFinal *
                         Stream (snd handle_ss) 
                end;
            mem_mgr gv).

Lemma body_hmac_drbg_seed_simple: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_seed hmac_drbg_seed_simple_spec.
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
  Time forward_call ((M1,(M2,M3)), Vptr b i, Ews, Vint (Int.repr 1), info, gv).

  Intros v. rename H into Hv.
  forward.
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
  forward_call (info).

  (*call mbedtls_md_hmac_starts( &ctx->md_ctx, ctx->V, md_size )*)
  thaw FR0. subst.
  assert (ZL_VV: Zlength initial_key =32) by reflexivity.
  thaw FIELDS.
  freeze [2;4;5;6;7] FIELDS1.
  rewrite field_at_compatible'. Intros. rename H into FC_V.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial.
  rewrite <- ZL_VV.
  freeze [0;4;5;6;8] FR2.
  forward_call (Vptr b i, Ews, ((info,(M2,p)):mdstate), 32, initial_key, b, Ptrofs.add i (Ptrofs.repr 12), Ews, gv).
  { split; auto; computable. }

  (*call  memset( ctx->V, 0x01, md_size )*)
  freeze [0;1;3;4] FR3.
  forward_call (Ews, Vptr b (Ptrofs.add i (Ptrofs.repr 12)), 32, Int.one).
  { rewrite sepcon_comm. apply sepcon_derives.
     - apply data_at_memory_block.
     - cancel. }
  my_auto.
  (*ctx->reseed_interval = MBEDTLS_HMAC_DRBG_RESEED_INTERVAL;*)
  rewrite ZL_VV.
  thaw FR3. thaw FR2. unfold md_relate. simpl.
  replace_SEP 2 (field_at Ews t_struct_hmac256drbg_context_st [StructField _md_ctx] (info, (M2, p)) (Vptr b i)). {
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
    + clear H. forward. forward. entailer!. }
  forward. simpl. deadvars!. (*drop_LOCAL 7%nat. _t'4*)

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

  freeze [0;3;4;5;9] FR_CTX.
  freeze [1;7;8;9] KVStreamInfoDataFreeBlk.

  (*NEXT INSTRUCTION: mbedtls_hmac_drbg_reseed( ctx, custom, len ) *)
  freeze [1;3;4;5] INI.
  replace_SEP 0 (
         data_at Ews t_struct_hmac256drbg_context_st ST (Vptr b i) *
         hmac256drbg_relate myABS ST).
  { entailer!. thaw INI. clear - FC_V. (*KVStreamInfoDataFreeBlk.*) thaw FR_CTX.
    simpl. entailer!.
    unfold_data_at 2%nat. 
    cancel. unfold md_full; simpl.
    rewrite field_at_data_at; simpl.
    unfold field_address. rewrite if_true; simpl; trivial.
    cancel.
    apply UNDER_SPEC.REP_FULL.
  }

  clear INI.
  thaw KVStreamInfoDataFreeBlk. freeze [6] OLD_MD.
  forward_call (Data, data, Ews, Zlength Data, Vptr b i, Ews, ST, myABS, Info, s, gv).
  { unfold hmac256drbgstate_md_info_pointer.
    subst ST; simpl. cancel.
  }
  { subst myABS; simpl. rewrite <- initialize.max_unsigned_modulus in *.
    split. computable. split. rep_lia. (* rewrite int_max_unsigned_eq; lia.*)
     unfold contents_with_add. simple_if_tac. rep_lia. rewrite Zlength_nil; rep_lia.
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
        subst myABS. rewrite <- instantiate_reseed in HeqMRS; trivial.
        rewrite RES in HeqMRS. inv HeqMRS. 
  }
  { rename H into Hv. forward. entailer!. 
    apply negb_false_iff in Hv.
    symmetry in Hv; apply binop_lemmas2.int_eq_true in Hv; subst v. trivial.
  }
  deadvars!. Intros. subst v.
  unfold reseedPOST. 
  remember ((zlt 256 (Zlength Data)
          || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data))%bool) as d.
  destruct d; Intros. inv H.
  remember (mbedtls_HMAC256_DRBG_reseed_function s myABS
         (contents_with_add data (Zlength Data) Data)) as MRS.
  unfold hmac256drbgabs_reseed. rewrite <- HeqMRS. subst myABS; simpl.

  assert (ZLc'256F: Zlength (contents_with_add data (Zlength Data) Data) >? 256 = false).
      { destruct ZLc' as [HH | HH]; rewrite HH. reflexivity.
        apply Zgt_is_gt_bool_f. lia. }
  rewrite <- instantiate_reseed, RES in HeqMRS; trivial. subst MRS. clear H RES Heqd. 
  destruct handle as [[[[newV newK] newRC] dd] newPR].
  unfold hmac256drbgabs_common_mpreds. simpl. subst ST. unfold hmac256drbgstate_md_info_pointer. simpl. Intros.
  unfold_data_at 1%nat. freeze [0;1;2;4;5;6;7;8;9;10;11;12] ALLSEP.
  forward. forward.
  Exists Int.zero. simpl.
  apply andp_right. apply prop_right; split; trivial.
  thaw ALLSEP. thaw OLD_MD. Exists p. 
  cancel;  normalize. 
  apply andp_right. solve [apply prop_right; repeat split; trivial].
  cancel.
  unfold_data_at 1%nat. cancel.
  apply hmac_interp_empty.
Time Qed. (*Coq8.6: 26secs*)

(*Spec that does not assume len<=256 and includes a clause 
  for the case where mbedtls_HMAC256_DRBG_instantiate_function yields
  Entropy.ERROR, ie no hypothesis about mbedtls_HMAC256_DRBG_instantiate_function in PROP of PRE*)
Definition hmac_drbg_seed_full_spec :=
  DECLARE _mbedtls_hmac_drbg_seed
   WITH dp:_, ctx: val, info:val, len: Z, data:val, Data: list byte,
        Ctx: hmac256drbgstate,
        Info: md_info_state, s:ENTROPY.stream, rc:Z, pr_flag:bool, ri:Z, gv: globals
    PRE [(*_ctx OF*) tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         (*_md_info OF*) tptr (Tstruct _mbedtls_md_info_t noattr),
         (*_custom OF*) tptr tuchar, (*_len OF*) tuint ]
       PROP ( (len = Zlength Data) /\
              0 <= len /\
              48 + len < Int.modulus /\
              0 < 48 + Zlength (contents_with_add data len Data) < Int.modulus)
       PARAMS (ctx; info; data; Vint (Int.repr len)) GLOBALS (gv)
       SEP (
         data_at Ews t_struct_hmac256drbg_context_st Ctx ctx;
         preseed_relate dp rc pr_flag ri Ctx;
         data_at Ews t_struct_mbedtls_md_info Info info;
         da_emp Ews (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
         K_vector gv; Stream s; mem_mgr gv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp (Vint ret_value))
       SEP (data_at Ews t_struct_mbedtls_md_info Info info;
            da_emp Ews (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
            K_vector gv;
            if Int.eq ret_value (Int.repr (-20864))
            then data_at Ews t_struct_hmac256drbg_context_st Ctx ctx *
                 preseed_relate dp rc pr_flag ri Ctx * Stream s
            else md_empty (fst Ctx) *
                 EX p:val,
                 match (fst Ctx) with (M1, (M2, M3)) =>
                   if (zlt 256 (Zlength Data) || (zlt 384 (48 + Zlength Data)))%bool
                   then !!(ret_value = Int.repr (-5)) &&
                     (Stream s *
                     ( let CtxFinal:= ((info, (M2, p)), (repeat (Vint Int.one) 32, (Vint (Int.repr rc),
                                       (Vint (Int.repr 48), (bool2val pr_flag, Vint (Int.repr 10000)))))) in
                       let CTXFinal:= HMAC256DRBGabs initial_key initial_value rc 48 pr_flag 10000 in
                       data_at Ews t_struct_hmac256drbg_context_st CtxFinal ctx *
                                     hmac256drbg_relate CTXFinal CtxFinal))

                   else match mbedtls_HMAC256_DRBG_instantiate_function s entlen pr_flag
                                       (contents_with_add data (Zlength Data) Data)
                        with
                         | ENTROPY.error e ss =>
                            (!!(match e with
                               | ENTROPY.generic_error => Vint ret_value = Vint (Int.repr ENT_GenErr)
                               | ENTROPY.catastrophic_error => Vint ret_value = Vint (Int.repr (-9))
                              end) && (Stream ss *
                                       let CtxFinal:= ((info, (M2, p)), (repeat (Vint Int.one) 32, (Vint (Int.repr rc),
                                                (Vint (Int.repr 48), (bool2val pr_flag, Vint (Int.repr 10000)))))) in
                                       let CTXFinal:= HMAC256DRBGabs initial_key initial_value rc 48 pr_flag 10000 in
                                       data_at Ews t_struct_hmac256drbg_context_st CtxFinal ctx *
                                       hmac256drbg_relate CTXFinal CtxFinal))
                        | ENTROPY.success handle ss => !!(ret_value = Int.zero) &&
                                    match handle with ((((newV, newK), newRC), newEL), newPR) =>
                                      let CtxFinal := ((info, (M2, p)), (map Vubyte newV, (Vint (Int.repr newRC), (Vint (Int.repr 32), (bool2val newPR, Vint (Int.repr 10000)))))) in
                                      let CTXFinal := HMAC256DRBGabs newK newV newRC 32 newPR 10000 in
                                    data_at Ews t_struct_hmac256drbg_context_st CtxFinal ctx *
                                    hmac256drbg_relate CTXFinal CtxFinal *
                                    Stream ss end
                        end
                end;
             mem_mgr gv).

Lemma body_hmac_drbg_seed_full: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_seed hmac_drbg_seed_full_spec.
Proof.
  start_function.
  abbreviate_semax.
  destruct H as (*[PREQ*) [HDlen1 [HDlen2 [DHlen3 [DHlen4 HData]]]](*]*).
  rewrite data_at_isptr with (p:=ctx). Intros.
  destruct ctx; try contradiction.
  unfold_data_at 1%nat.
  destruct Ctx as [MdCTX [V [RC [EL [PR RI]]]]]. simpl.
  destruct MdCTX as [M1 [M2 M3]].
  freeze [1;2;3;4;5] FIELDS.
  rewrite field_at_compatible'. Intros. rename H into FC_mdx.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial. rewrite ptrofs_add_repr_0_r.
  freeze [0;2;3;4;5;6] FR0.
  Time forward_call ((M1,(M2,M3)), Vptr b i, Ews, Vint (Int.repr 1), info, gv).

  Intros v. rename H into Hv.
  freeze [0] FR1. forward. thaw FR1.
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
  freeze [2;4;5;6;7] FIELDS1.
  rewrite field_at_compatible'. Intros. rename H into FC_V.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial.
  rewrite <- ZL_VV.
  freeze [0;4;5;6;8] FR2.
(*
  replace_SEP 1 (UNDER_SPEC.EMPTY Ews p).
  { entailer!. 
    eapply derives_trans. 2: apply UNDER_SPEC.mkEmpty.
    fix_hmacdrbg_compspecs. apply derives_refl.
  }
*)
  forward_call (Vptr b i, Ews, ((info,(M2,p)):mdstate), 32, initial_key, b, Ptrofs.add i (Ptrofs.repr 12), Ews, gv).
  { split; my_auto. }

  (*call  memset( ctx->V, 0x01, md_size )*)
  freeze [0;1;3;4] FR3.
  forward_call (Ews, Vptr b (Ptrofs.add i (Ptrofs.repr 12)), 32, Int.one).
  { rewrite sepcon_comm. apply sepcon_derives.
     - apply data_at_memory_block.
     - cancel. }
  (*ctx->reseed_interval = MBEDTLS_HMAC_DRBG_RESEED_INTERVAL;*)
  rewrite ZL_VV.
  thaw FR3. thaw FR2. unfold md_relate. simpl.
  replace_SEP 2 (field_at Ews t_struct_hmac256drbg_context_st [StructField _md_ctx] (info, (M2, p)) (Vptr b i)). {
    entailer!. rewrite field_at_data_at.
    simpl. rewrite field_compatible_field_address by auto with field_compatible. simpl.
    rewrite ptrofs_add_repr_0_r.
    cancel.
  }
  deadvars!.
  thaw FIELDS1. forward.
  freeze [0;4;5;6;7] FIELDS2.
  freeze [0;1;2;3;4;5;6;7;8;9] ALLSEP.

  forward_if (temp _t'4 (Vint (Int.repr 32))).
  { discriminate. }
  { clear H.
    forward_if.
    + discriminate.
    + clear H. forward. forward. entailer!. }
  forward. simpl. deadvars!. (*drop_LOCAL 7%nat. _t'4*)

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

  freeze [0;3;4;5;9] FR_CTX.
  freeze [1;7;8;9] KVStreamInfoDataFreeBlk.

  (*NEXT INSTRUCTION: mbedtls_hmac_drbg_reseed( ctx, custom, len ) *)
  freeze [1;3;4;5] INI.
  replace_SEP 0 (
         data_at Ews t_struct_hmac256drbg_context_st ST (Vptr b i) *
         hmac256drbg_relate myABS ST).
  { entailer!. thaw INI. clear - FC_V. (*KVStreamInfoDataFreeBlk.*) thaw FR_CTX.
    simpl; entailer!.
    unfold_data_at 2%nat. 
    cancel. unfold md_full; simpl.
    rewrite field_at_data_at; simpl.
    unfold field_address. rewrite if_true; simpl; trivial.
    cancel.
    apply UNDER_SPEC.REP_FULL.
  }

  clear INI.
  thaw KVStreamInfoDataFreeBlk. freeze [6] OLD_MD.
  forward_call (Data, data, Ews, Zlength Data, Vptr b i, Ews, ST, myABS, Info, s, gv).
  { unfold hmac256drbgstate_md_info_pointer.
    subst ST; simpl. cancel.
  }
  { subst myABS; simpl. computable. 
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
    + subst d. unfold hmac256drbgstate_md_info_pointer, hmac256drbg_relate; simpl.
      simpl. subst myABS. normalize. cancel. simpl. 
      Exists p. thaw OLD_MD. normalize.
      apply andp_right. apply prop_right; repeat split; trivial. cancel.
      apply hmac_interp_empty.
    + destruct (zlt 384 (48 + Zlength Data)); simpl in Heqd; try lia.
      subst d.
      unfold hmac256drbgstate_md_info_pointer, hmac256drbg_relate; simpl. Intros.
      rename H into RV.
      remember (mbedtls_HMAC256_DRBG_reseed_function s myABS
         (contents_with_add data (Zlength Data) Data)) as MRS.
      rewrite (ReseedRes _ _ _ RV). cancel.
      unfold return_value_relate_result in RV.
      assert (ZLc'256F: Zlength (contents_with_add data (Zlength Data) Data) >? 256 = false).
      { apply Zgt_is_gt_bool_f. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc';  lia. }
      unfold hmac256drbgabs_common_mpreds, hmac256drbgstate_md_info_pointer.
      destruct MRS.
      - exfalso. inv RV. simpl in Hv. discriminate.
      - simpl. Intros. Exists p. thaw OLD_MD. cancel.
        subst myABS. rewrite <- instantiate_reseed in HeqMRS; trivial.
        rewrite <- HeqMRS. 
        normalize.
        apply andp_right. apply prop_right; repeat split; trivial.
        cancel. apply hmac_interp_empty.
  }
  { rename H into Hv. forward. entailer!. 
    apply negb_false_iff in Hv.
    symmetry in Hv; apply binop_lemmas2.int_eq_true in Hv; subst v. trivial.
  }
  deadvars!. Intros. subst v.
  unfold reseedPOST.
  remember ((zlt 256 (Zlength Data)
          || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data))%bool) as d.
  destruct d; Intros. inv H.
  remember (mbedtls_HMAC256_DRBG_reseed_function s myABS
         (contents_with_add data (Zlength Data) Data)) as MRS.
  unfold hmac256drbgabs_reseed. rewrite <- HeqMRS. subst myABS; simpl.
  unfold return_value_relate_result in H.
  destruct MRS. 2:{ exfalso. destruct e. inv H.
                     destruct ENT_GenErrAx as [EL1 _]. rewrite <- H in EL1. elim EL1; trivial.
  }
  clear H.
  destruct d as [[[[newV newK] newRC] dd] newPR].
  unfold hmac256drbgabs_common_mpreds. simpl. subst ST. unfold hmac256drbgstate_md_info_pointer. simpl. Intros.
  unfold_data_at 1%nat. freeze [0;1;2;4;5;6;7;8;9;10;11;12] ALLSEP.
  forward. forward.
  Exists Int.zero. simpl.
  apply andp_right. apply prop_right; split; trivial.
  symmetry in Heqd. apply orb_false_iff in Heqd. destruct Heqd as [Heqd1 Heqd2].
  destruct (zlt 256 (Zlength Data)); try discriminate. simpl in *. rewrite Heqd2.
  thaw ALLSEP. thaw OLD_MD. Exists p. cancel.
  normalize.
  assert (ZLc'256F: Zlength (contents_with_add data (Zlength Data) Data) >? 256 = false).
      { destruct ZLc' as [HH | HH]; rewrite HH. reflexivity.
        apply Zgt_is_gt_bool_f. lia. }
  rewrite <- instantiate_reseed in HeqMRS; trivial.
  rewrite <- HeqMRS.
  normalize.
  apply andp_right. apply prop_right; repeat split; trivial.
  cancel.
  unfold_data_at 1%nat. cancel.
  apply hmac_interp_empty. 
Time Qed. (*Coq8.6: 32secs*)
   (*Feb 22nd 2017: 245.406 secs (233.843u,0.203s) (successful)*)
   (*earlier: 69.671 secs (59.578u,0.015s) (successful)*)

End Instantiate_eq.

Lemma ReseedRes: forall X r v, @return_value_relate_result X r (Vint v) -> Int.eq v (Int.repr (-20864)) = false.
Proof. intros.
  unfold return_value_relate_result in H.
  destruct r. inv H; reflexivity.
  destruct e; inv H; try reflexivity.
  apply Int.eq_false. eapply ENT_GenErrAx.
Qed.

Definition preseed_relate V rc pr ri (r : hmac256drbgstate):mpred:=
    match r with
     (md_ctx', (V', (reseed_counter', (entropy_len', (prediction_resistance', reseed_interval'))))) =>
    md_empty md_ctx' &&
    !! (map Vubyte V = V' /\
        Zlength V = 32 /\
        Vint (Int.repr rc) = reseed_counter'(* /\
        Vint (Int.repr entropy_len) = entropy_len'*) /\
        Vint (Int.repr ri) = reseed_interval' /\
        bool2val pr = prediction_resistance')
   end.

Definition hmac_drbg_seed_spec :=
  DECLARE _mbedtls_hmac_drbg_seed
   WITH ctx: val, info:val, len: Z, data:val, Data: list byte,
        Ctx: hmac256drbgstate,
        (*CTX: hmac256drbgabs,*)
        Info: md_info_state, s:ENTROPY.stream, rc:Z, pr:bool, ri:Z, VV:list byte, gv: globals
    PRE [(*_ctx OF*) tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         (*_md_info OF*) tptr (Tstruct _mbedtls_md_info_t noattr),
         (*_custom OF*) tptr tuchar, (*_len OF*) tuint ]
       PROP ( (len = Zlength Data) /\
              0 <= len (*<= 336 Int.max_unsigned*) /\
              48 + len < Int.modulus /\
              0 < 48 + Zlength (contents_with_add data len Data) < Int.modulus)
       (*LOCAL (temp _ctx ctx; temp _md_info info;
              temp _len (Vint (Int.repr len)); temp _custom data; gvars gv)*)
       PARAMS (ctx; info; data; Vint (Int.repr len)) GLOBALS (gv)
       SEP (
         data_at Ews t_struct_hmac256drbg_context_st Ctx ctx;
         preseed_relate VV rc pr ri Ctx;
         (*hmac256drbg_relate CTX Ctx;*)
         data_at Ews t_struct_mbedtls_md_info Info info;
         da_emp Ews (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
         K_vector gv; Stream s; mem_mgr gv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp (Vint ret_value))
       SEP (data_at Ews t_struct_mbedtls_md_info Info info;
            da_emp Ews (tarray tuchar (Zlength Data)) (map Vubyte Data) data;
            K_vector gv;
            if Int.eq ret_value (Int.repr (-20864))
            then data_at Ews t_struct_hmac256drbg_context_st Ctx ctx *
                  (*hmac256drbg_relate CTX Ctx *) preseed_relate VV rc pr ri Ctx *
                  Stream s
            else md_empty (fst Ctx) *
                 EX p:val, (* malloc_token Tsh (Tstruct _hmac_ctx_st noattr) p * *)
                 match (fst Ctx) with (M1, (M2, M3)) =>
                   if (zlt 256 (Zlength Data) || (zlt 384 ((*hmac256drbgabs_entropy_len initial_state_abs*)48 + Zlength Data)))%bool
                   then !!(ret_value = Int.repr (-5)) &&
                     (Stream s *
                     ( let CtxFinal:= ((info, (M2, p)), (repeat (Vint Int.one) 32, (Vint (Int.repr rc),
                                       (Vint (Int.repr 48), (bool2val pr, Vint (Int.repr 10000)))))) in
                       let CTXFinal:= HMAC256DRBGabs VV (repeat Byte.one 32) rc 48 pr 10000 in
                       data_at Ews t_struct_hmac256drbg_context_st CtxFinal ctx *
                                     hmac256drbg_relate CTXFinal CtxFinal))

                   else let myABS := HMAC256DRBGabs VV (repeat Byte.one 32) rc 48 pr 10000
                      in match mbedtls_HMAC256_DRBG_reseed_function s myABS
                                (contents_with_add data (Zlength Data) Data)
                         with
                         | ENTROPY.error e ss =>
                            (!!(match e with
                               | ENTROPY.generic_error => Vint ret_value = Vint (Int.repr ENT_GenErr)
                               | ENTROPY.catastrophic_error => Vint ret_value = Vint (Int.repr (-9))
                              end) && (Stream ss *
                                       let CtxFinal:= ((info, (M2, p)), (repeat (Vint Int.one) 32, (Vint (Int.repr rc),
                                                (Vint (Int.repr 48), (bool2val pr, Vint (Int.repr 10000)))))) in
                                       let CTXFinal:= HMAC256DRBGabs VV (repeat Byte.one 32) rc 48 pr 10000 in
                                       data_at Ews t_struct_hmac256drbg_context_st CtxFinal ctx *
                                       hmac256drbg_relate CTXFinal CtxFinal))
                        | ENTROPY.success handle ss => !!(ret_value = Int.zero) &&
                                    match handle with ((((newV, newK), newRC), newEL), newPR) =>
                                      let CtxFinal := ((info, (M2, p)), (map Vubyte newV, (Vint (Int.repr newRC), (Vint (Int.repr 32), (bool2val newPR, Vint (Int.repr 10000)))))) in
                                      let CTXFinal := HMAC256DRBGabs newK newV newRC 32 newPR 10000 in
                                    data_at Ews t_struct_hmac256drbg_context_st CtxFinal ctx *
                                    hmac256drbg_relate CTXFinal CtxFinal *
                                    Stream ss end
                        end
                end;
         mem_mgr gv).

Opaque mbedtls_HMAC256_DRBG_reseed_function.

Lemma body_hmac_drbg_seed: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_seed hmac_drbg_seed_spec.
Proof.
  start_function.
  abbreviate_semax.
  destruct H as [HDlen1 [HDlen2 [DHlen3 [DHlen4 HData]]]].
  rewrite data_at_isptr with (p:=ctx). Intros.
  destruct ctx; try contradiction.
  unfold_data_at 1%nat.
  destruct Ctx as [MdCTX [V [RC [EL [PR RI]]]]]. simpl.
  destruct MdCTX as [M1 [M2 M3]].
  freeze [1;2;3;4;5] FIELDS.
  rewrite field_at_compatible'. Intros. rename H into FC_mdx.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial. rewrite ptrofs_add_repr_0_r.
  freeze [0;2;3;4;5;6] FR0.
  Time forward_call ((M1,(M2,M3)), Vptr b i, Ews, Vint (Int.repr 1), info, gv).
  Intros v. rename H into Hv.
  freeze [0] FR1. forward. thaw FR1.

  forward_if.
  { destruct Hv; try lia. rewrite if_false; trivial. clear H. subst v.
    forward. simpl. Exists (Int.repr (-20864)).
    rewrite Int.eq_true.
    entailer!. thaw FR0. cancel.
    unfold_data_at 2%nat. thaw FIELDS. cancel.
    rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true; simpl; trivial. rewrite ptrofs_add_repr_0_r; auto. }
  subst v. clear Hv. simpl.
  Intros p.

  (*Alloction / md_setup succeeded. Now get md_size*)
  deadvars!. 
  forward_call info.

  (*call mbedtls_md_hmac_starts( &ctx->md_ctx, ctx->V, md_size )*)
  thaw FR0. subst.
  rename H1 into ZL_VV.
  thaw FIELDS.
  freeze [2;4;5;6;7] FIELDS1.
  rewrite field_at_compatible'. Intros. rename H into FC_V.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial.
  rewrite <- ZL_VV.
  freeze [0;4;5;6;8] FR2.
  forward_call (Vptr b i, Ews, ((info,(M2,p)):mdstate), 32, VV, b, Ptrofs.add i (Ptrofs.repr 12), Ews, gv).
  { entailer!. simpl. rewrite ZL_VV, ptrofs_add_repr_0_r; trivial. 
  }
  { split; auto. computable. }
  Intros.

  (*call  memset( ctx->V, 0x01, md_size )*)
  freeze [0;1;3;4] FR3.
  forward_call (Ews, Vptr b (Ptrofs.add i (Ptrofs.repr 12)), 32, Int.one).
  { rewrite ZL_VV; entailer!.
  }
  { rewrite sepcon_comm. apply sepcon_derives.
      eapply derives_trans. apply data_at_memory_block.
        rewrite ZL_VV. simpl. cancel. cancel. }
  (*{ split. apply semax_call.writable_share_top.
    rewrite ZL_V0, client_lemmas.int_max_unsigned_eq. lia. }*)

  (*ctx->reseed_interval = MBEDTLS_HMAC_DRBG_RESEED_INTERVAL;*)
  rewrite ZL_VV.
  thaw FR3. thaw FR2. unfold md_relate. simpl.
  replace_SEP 2 (field_at Ews t_struct_hmac256drbg_context_st [StructField _md_ctx] (info, (M2, p)) (Vptr b i)). {
    entailer!. rewrite field_at_data_at.
    simpl. rewrite field_compatible_field_address by auto with field_compatible. simpl.
    rewrite ptrofs_add_repr_0_r.
    cancel.
  }
  thaw FIELDS1. forward.
  freeze [0;4;5;6;7] FIELDS2.
  freeze [0;1;2;3;4;5;6;7;8;9] ALLSEP.
(*  set (ent_len := new_ent_len (Zlength V0)) in *.*)

  forward_if (temp _t'4 (Vint (Int.repr 32))).
  { discriminate. }
  { clear H.
    forward_if.
    { discriminate. }
    { clear H. forward. forward. entailer!. }
  }
  forward. simpl. drop_LOCAL 1%nat. (*_t'4*)

  (*NEXT INSTRUCTION:  ctx->entropy_len = entropy_len * 3 / 2*)
  thaw ALLSEP. thaw FIELDS2. forward.

  assert (FOURTYEIGHT: Int.unsigned (Int.mul (Int.repr 32) (Int.repr 3)) / 2 = 48).
  { rewrite mul_repr. simpl; auto.
(*    all: rewrite Int.unsigned_repr by rep_lia; reflexivity.  for Coq 8.13 and before *)
  }

  set (myABS := HMAC256DRBGabs VV (repeat Byte.one 32) rc 48 pr 10000) in *.
  assert (myST: exists ST:hmac256drbgstate, ST =
    ((info, (M2, p)), (map Vint (repeat Int.one 32), (Vint (Int.repr rc),
        (Vint (Int.repr 48), (bool2val pr, Vint (Int.repr 10000))))))). eexists; reflexivity.
  destruct myST as [ST HST].

  freeze FR_CTX := (data_at _ _ _ (Vptr b (Ptrofs.add i (Ptrofs.repr 12))))
         (field_at _ _ [StructField _reseed_counter] _ (Vptr b i))
         (field_at _ _ [StructField _entropy_len] _ (Vptr b i))
         (UNDER_SPEC.REP _ _ p)
         (malloc_token _ _ p).
  freeze KVStreamInfoDataFreeBlk :=
      (K_vector gv) 
      (data_at _ _ _ info)
      (da_emp _ _ _ data)
      (Stream s).

  (*NEXT INSTRUCTION: mbedtls_hmac_drbg_reseed( ctx, custom, len ) *)
  freeze [1;3;4;5] INI.
  replace_SEP 0 (
         data_at Ews t_struct_hmac256drbg_context_st ST (Vptr b i) *
         hmac256drbg_relate myABS ST).
  { go_lower. thaw INI. clear KVStreamInfoDataFreeBlk. thaw FR_CTX.
    unfold_data_at 2%nat.
    subst ST; simpl. cancel. normalize.
    apply andp_right. apply prop_right. repeat split; trivial.
    unfold md_full. simpl.
    rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true; simpl; trivial. cancel.
    apply UNDER_SPEC.REP_FULL.
  }

  clear INI.
  thaw KVStreamInfoDataFreeBlk. freeze [6] OLD_MD.
  forward_call (Data, data, Ews, Zlength Data, Vptr b i, Ews, ST, myABS, Info, s, gv).
  { unfold hmac256drbgstate_md_info_pointer.
    subst ST; simpl. cancel.
  }
  { subst myABS; simpl. computable.  }

  Intros v.

  forward.
  forward_if (v = nullval).
  { rename H into Hv. forward. simpl. Exists v.
    apply andp_right. apply prop_right; split; trivial.
    unfold reseedPOST. (*rename H into Mcompat.*)

    remember ((zlt 256 (Zlength Data) || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data)) %bool) as d.
    unfold myABS in Heqd; simpl in Heqd.
    destruct (zlt 256 (Zlength Data)); simpl in Heqd.
    + subst d. unfold hmac256drbgstate_md_info_pointer, hmac256drbg_relate; simpl.
      simpl. subst myABS. Intros. subst v; simpl. cancel.
      Exists p. thaw OLD_MD. cancel. 
      apply andp_right; [ apply prop_right; trivial |  cancel; entailer!]. 
    + destruct (zlt 384 (48 + Zlength Data)); simpl in Heqd; try lia.
      subst d.
      unfold hmac256drbgstate_md_info_pointer, hmac256drbg_relate; simpl. Intros. cancel. 
      rename H into RV.
      remember (mbedtls_HMAC256_DRBG_reseed_function s myABS
                                                     (contents_with_add data (Zlength Data) Data)) as MRS.
      rewrite (ReseedRes _ _ _ RV). cancel.
      unfold return_value_relate_result in RV.
      destruct MRS.
      - exfalso. inv RV. simpl in Hv. discriminate.
      - unfold hmac256drbgabs_common_mpreds, hmac256drbgstate_md_info_pointer; simpl.
        Intros. Exists p. thaw OLD_MD. cancel.
        apply andp_right. apply prop_right; trivial.
        cancel. entailer!.
  }
  { rename H into Hv. forward. simpl in Hv. entailer!.
    apply negb_false_iff in Hv.
    symmetry in Hv; apply binop_lemmas2.int_eq_true in Hv. subst v; trivial.
  }
  deadvars!. Intros. subst v.
  unfold reseedPOST.
  remember ((zlt 256 (Zlength Data)
          || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data))%bool) as d.
  destruct d; Intros. inv H.
  remember (mbedtls_HMAC256_DRBG_reseed_function s myABS
         (contents_with_add data (Zlength Data) Data)) as MRS.
  unfold return_value_relate_result in H.
  destruct MRS. 2:{ exfalso. destruct e. inv H.
                     destruct ENT_GenErrAx as [EL1 _]. rewrite <- H in EL1. elim EL1; trivial.
  }
  clear H. unfold hmac256drbgabs_reseed. rewrite <- HeqMRS. subst myABS; simpl.
  destruct d as [[[[newV newK] newRC] dd] newPR].
  unfold hmac256drbgabs_common_mpreds. simpl. subst ST. unfold hmac256drbgstate_md_info_pointer. simpl. Intros.
  unfold_data_at 1%nat. freeze [0;1;2;4;5;6;7;8;9;10;11] XX.
  forward. forward. 
  Exists Int.zero. simpl. symmetry in Heqd. apply orb_false_iff in Heqd. destruct Heqd as [Heqd1 Heqd2].
  destruct (zlt 256 (Zlength Data)); try discriminate.
  apply andp_right. apply prop_right; split; trivial. 
  thaw XX. thaw OLD_MD. cancel. simpl in *.
  rewrite Heqd2. (* rewrite <- HeqMRS. *)
  Exists p. 
  apply andp_right. apply prop_right; trivial.
  unfold_data_at 1%nat. cancel. entailer!.
Time Qed. (*Coq8.6: 40secs*)
          (*Jan 22nd 2017: 267.171 secs (182.812u,0.015s) (successful)*)
          (*earlier: Finished transaction in 121.296 secs (70.921u,0.062s) (successful)*)
          (*Coq8.9, April 2019: 8.3s*)
