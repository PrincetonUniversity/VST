Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import floyd.sublist.

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
Require Import floyd.library.

Axiom Entropy_addSuccess1: forall n m s s1 l1 s2 l2,
        ENTROPY.get_bytes n s = ENTROPY.success l1 s1 ->
        ENTROPY.get_bytes m s1 = ENTROPY.success l2 s2 ->
        ENTROPY.get_bytes (n+m) s = ENTROPY.success (l1++l2) s2.

Axiom Entropy_addSuccess2: forall n m s s1 l1 s2 e,
        ENTROPY.get_bytes n s = ENTROPY.success l1 s1 ->
        ENTROPY.get_bytes m s1 = ENTROPY.error e s2 ->
        ENTROPY.get_bytes (n+m) s = ENTROPY.error e s2.

Axiom Entropy_addError: forall n m s s1 e, ENTROPY.get_bytes n s = ENTROPY.error e s1 ->
        ENTROPY.get_bytes (n+m) s = ENTROPY.error e s1.

Lemma Entropy_le n s l ss: ENTROPY.success l ss = ENTROPY.get_bytes n s ->
  forall m, (m <= n)%nat -> exists l' s', ENTROPY.success l' s' = ENTROPY.get_bytes m s.
Proof. intros.
  remember (ENTROPY.get_bytes m s) as d.
  destruct d. eexists; eexists; trivial.
  symmetry in H; symmetry in Heqd.
  specialize (Entropy_addError _ (n-m)%nat _ _ _ Heqd).
     rewrite le_plus_minus_r; trivial.
  intros HH; rewrite HH in *. discriminate.
Qed.

Definition OptionalNonce: option (list Z) := None. (*The implementation takes nonce from entropy, using the el*3/2 calculation*)

Parameter max_personalization_string_length: Z. (*NIST SP 800-90A, page 38, Table2: 2^35 bits;
         Our personalization string is a list of bytes, so have max length 2^32*)
Axiom max_personalization_string336: 336 <= max_personalization_string_length.

Definition prediction_resistance_supported:bool:=true.

(*NIST, Section 10.1: highest supported sec strength is given by the has function's
security strength for preimage resistance. For SHA256, this is
(according to NIST SP 800-107, Table 1, page 11) 256 bits*)
Definition highest_supported_security_strength := 32. (* in bytes -- see comment for reseed*)

(*Q: should we use the sec strength of HMAC, calculated according to Section 5.3.4 of
NIST SP 800-107 instead?*)
Definition requested_security_strength:= 32.  (*same as in reseed*)

Definition mbedtls_HMAC256_DRBG_instantiate_function (entropy_stream: ENTROPY.stream)
         entropy_len pr_flag (personalization_string: list Z): ENTROPY.result DRBG_state_handle :=
   let reseed_interval := 10000
   in HMAC256_DRBG_instantiate_function entropy_len entropy_len OptionalNonce
            highest_supported_security_strength max_personalization_string_length
            prediction_resistance_supported entropy_stream
            requested_security_strength pr_flag personalization_string.

Definition entlen:Z := 32.

Definition MD_ANY (r: mdstate): mpred :=
  (md_empty r) || (EX h:_, md_relate h r) || (EX k:_, md_full k r).
(*
Require Import msl.predicates_hered.

Inductive md_any (r: mdstate): compcert_rmaps.RML.R.rmap -> Prop:=
  md_any_empty: forall phi, app_pred (md_empty r) phi -> md_any r phi
| md_any_rep: forall h phi, app_pred (md_relate h r) phi -> md_any r phi
| md_any_full: forall k phi, app_pred (md_full k r) phi -> md_any r phi.

Definition MDANY (r:mdstate):mpred.
refine (exist _ (md_any r) _). red; intros.
inv H0.
apply md_any_empty. destruct (md_empty r); simpl in *. eapply h; eauto.
apply (md_any_rep r h). destruct (md_relate h r); simpl in *. eapply h0; eauto.
apply (md_any_full r k). destruct (md_full k r); simpl in *. eapply h; eauto.
Defined.

Lemma inject_md_any_empty r: md_empty r |-- MDANY r.
constructor; trivial. Qed.
Lemma inject_md_any_rep h r: md_relate h r |-- MDANY r.
red; intros. eapply md_any_rep; eassumption. Qed.
Lemma inject_md_any_full k r: md_full k r |-- MDANY r.
red; intros. eapply md_any_full; eassumption. Qed.

Lemma MDANY_elim r: MDANY r |-- MD_ANY r.
unfold MD_ANY.
red; intros. inv H.
+ eapply orp_right1. 2: apply H0.
  eapply orp_right1. apply derives_refl.
+ eapply orp_right1. 2: apply H0.
  eapply orp_right2. econstructor. apply H.
+ eapply orp_right2. 2: apply H0.
  econstructor. apply H.
Qed.

Lemma MDANY_intros r: MD_ANY r |-- MDANY r.
unfold MD_ANY.
rewrite orp_is_exp. apply exp_left; intros.
destruct x.
+ rewrite orp_is_exp. apply exp_left; intros.
  destruct x.
  - apply inject_md_any_empty.
  - apply exp_left; intros. eapply inject_md_any_rep.
+ apply exp_left; intros. eapply inject_md_any_full.
Qed.
*)

Lemma ReseedRes: forall X r v, @return_value_relate_result X r (Vint v) -> Int.eq v (Int.repr (-20864)) = false.
Proof. intros.
  unfold return_value_relate_result in H.
  destruct r. inv H; reflexivity.
  destruct e; inv H; try reflexivity.
  apply Int.eq_false. eapply ENT_GenErrAx.
Qed.

Lemma instantiate_reseed d s pr_flag rc ri (ZLc'256F : (Zlength d >? 256) = false):
      mbedtls_HMAC256_DRBG_instantiate_function s entlen pr_flag  d =
      mbedtls_HMAC256_DRBG_reseed_function s (HMAC256DRBGabs initial_key initial_value rc 48 pr_flag ri) d.
Proof. intros.
  unfold mbedtls_HMAC256_DRBG_instantiate_function, HMAC256_DRBG_instantiate_function,
       DRBG_instantiate_function, mbedtls_HMAC256_DRBG_reseed_function; simpl.
  rewrite ZLc'256F, andb_negb_r.
  assert (MaxString': Zlength d >? max_personalization_string_length = false).
  { apply Zgt_is_gt_bool_f. apply Zgt_is_gt_bool_f in ZLc'256F.
    specialize max_personalization_string336; intros; omega. }
  rewrite MaxString' in *; clear.
  destruct pr_flag; simpl in *.
  + unfold get_entropy, entlen.
    remember (ENTROPY.get_bytes (Z.to_nat 48) s) as ENT.
    destruct ENT.
    - destruct (Entropy_le _ _ _ _ HeqENT (Z.to_nat 32)) as [l32 [s32 Ent32]]; try (simpl; omega).
      symmetry in Ent32; rewrite Ent32.
      change (32 / 2) with 16 in *.
      remember (ENTROPY.get_bytes (Z.to_nat 16) s32) as  ENT2; symmetry in HeqENT2.
      destruct ENT2.
      * specialize (Entropy_addSuccess1 _ 16 _ _ _ _ _ Ent32 HeqENT2); intros XX.
        simpl in *; rewrite XX in *; clear XX. inv HeqENT.
        f_equal. unfold HMAC256_DRBG_instantiate_algorithm, HMAC_DRBG_instantiate_algorithm.
        rewrite app_assoc; trivial.
      * specialize (Entropy_addSuccess2 _ 16 _ _ _ _ _ Ent32 HeqENT2); intros XX.
        simpl in *; rewrite XX in *; clear XX. inv HeqENT.
    - remember (ENTROPY.get_bytes (Z.to_nat 32) s) as Ent32; symmetry in HeqEnt32.
      destruct Ent32.
      * change (32 / 2) with 16 in *.
        remember (ENTROPY.get_bytes (Z.to_nat 16) s1) as  ENT2; symmetry in HeqENT2.
        destruct ENT2.
        ++ specialize (Entropy_addSuccess1 _ 16 _ _ _ _ _ HeqEnt32 HeqENT2); intros XX.
           simpl in *; rewrite XX in *; clear XX. inv HeqENT.
        ++ specialize (Entropy_addSuccess2 _ 16 _ _ _ _ _ HeqEnt32 HeqENT2); intros XX.
           simpl in *; rewrite XX in *; clear XX. inv HeqENT. trivial.
      * specialize (Entropy_addError _ 16 _ _ _ HeqEnt32); intros XX.
        simpl in *; rewrite XX in *; clear XX. inv HeqENT. trivial.
  + (*same proof...*)
    unfold get_entropy, entlen.
    remember (ENTROPY.get_bytes (Z.to_nat 48) s) as ENT.
    destruct ENT.
    - destruct (Entropy_le _ _ _ _ HeqENT (Z.to_nat 32)) as [l32 [s32 Ent32]]; try (simpl; omega).
      symmetry in Ent32; rewrite Ent32.
      change (32 / 2) with 16 in *.
      remember (ENTROPY.get_bytes (Z.to_nat 16) s32) as  ENT2; symmetry in HeqENT2.
      destruct ENT2.
      * specialize (Entropy_addSuccess1 _ 16 _ _ _ _ _ Ent32 HeqENT2); intros XX.
        simpl in *; rewrite XX in *; clear XX. inv HeqENT.
        f_equal. unfold HMAC256_DRBG_instantiate_algorithm, HMAC_DRBG_instantiate_algorithm.
        rewrite app_assoc; trivial.
      * specialize (Entropy_addSuccess2 _ 16 _ _ _ _ _ Ent32 HeqENT2); intros XX.
        simpl in *; rewrite XX in *; clear XX. inv HeqENT.
    - remember (ENTROPY.get_bytes (Z.to_nat 32) s) as Ent32; symmetry in HeqEnt32.
      destruct Ent32.
      * change (32 / 2) with 16 in *.
        remember (ENTROPY.get_bytes (Z.to_nat 16) s1) as  ENT2; symmetry in HeqENT2.
        destruct ENT2.
        ++ specialize (Entropy_addSuccess1 _ 16 _ _ _ _ _ HeqEnt32 HeqENT2); intros XX.
           simpl in *; rewrite XX in *; clear XX. inv HeqENT.
        ++ specialize (Entropy_addSuccess2 _ 16 _ _ _ _ _ HeqEnt32 HeqENT2); intros XX.
           simpl in *; rewrite XX in *; clear XX. inv HeqENT. trivial.
      * specialize (Entropy_addError _ 16 _ _ _ HeqEnt32); intros XX.
        simpl in *; rewrite XX in *; clear XX. inv HeqENT. trivial.
Qed.

Opaque mbedtls_HMAC256_DRBG_reseed_function.
Opaque initial_key. Opaque initial_value.

Inductive deep_any:=
  deep_any_empty: deep_any
| deep_any_rep: forall h:UNDER_SPEC.HABS, deep_any
| deep_any_full: forall k:list Z, deep_any.

Definition deep_interp (d:deep_any) (r: mdstate):mpred :=
  match d with
    deep_any_empty => md_empty r
  | deep_any_rep h => md_relate h r
  | deep_any_full k => md_full k r
  end.

Lemma deep_interp_empty d r: deep_interp d r |-- md_empty r.
destruct d; simpl. trivial.
+ destruct h. simpl.
  eapply derives_trans.
  apply UNDER_SPEC.REP_FULL.
  apply UNDER_SPEC.FULL_EMPTY.
+ apply UNDER_SPEC.FULL_EMPTY.
Qed.

Definition preseed_relate d rc pr ri (r : hmac256drbgstate):mpred:=
    match r with
     (md_ctx', (V', (reseed_counter', (entropy_len', (prediction_resistance', reseed_interval'))))) =>
    deep_interp d md_ctx' &&
    !! (map Vint (map Int.repr initial_key) = V' /\
        (Vint (Int.repr rc) = reseed_counter')  (*Explicitly reset in sucessful runs of reseed and hence seed*)
        (*Vint (Int.repr entropy_len) = entropy_len' Explicitly set in seed*) /\
        Vint (Int.repr ri) = reseed_interval' /\
        Val.of_bool pr = prediction_resistance')
   end.

Definition hmac_drbg_seed_spec :=
  DECLARE _mbedtls_hmac_drbg_seed
   WITH dp:_, ctx: val, info:val, len: Z, data:val, Data: list Z,
        Ctx: hmac256drbgstate,
        kv: val, Info: md_info_state, s:ENTROPY.stream, rc:Z, pr_flag:bool, ri:Z
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _md_info OF tptr (Tstruct _mbedtls_md_info_t noattr),
         _custom OF tptr tuchar, _len OF tuint ]
       PROP ( (len = Zlength Data) /\
              0 <= len /\
              48 + len < Int.modulus /\
              0 < 48 + Zlength (contents_with_add data len Data) < Int.modulus /\ Forall isbyteZ Data)
       LOCAL (temp _ctx ctx; temp _md_info info;
              temp _len (Vint (Int.repr len)); temp _custom data; gvar sha._K256 kv)
       SEP (
         data_at Tsh t_struct_hmac256drbg_context_st Ctx ctx;
         preseed_relate dp rc pr_flag ri Ctx;
         data_at Tsh t_struct_mbedtls_md_info Info info;
         da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data;
         K_vector kv; Stream s)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp (Vint ret_value))
       SEP (data_at Tsh t_struct_mbedtls_md_info Info info;
            da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data;
            K_vector kv;
            if Int.eq ret_value (Int.repr (-20864))
            then data_at Tsh t_struct_hmac256drbg_context_st Ctx ctx *
                 preseed_relate dp rc pr_flag ri Ctx * Stream s
            else md_empty (fst Ctx) *
                 EX p:val, malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
                 match (fst Ctx) with (M1, (M2, M3)) =>
                   if (zlt 256 (Zlength Data) || (zlt 384 (48 + Zlength Data)))%bool
                   then !!(ret_value = Int.repr (-5)) &&
                     (Stream s *
                     ( let CtxFinal:= ((info, (M2, p)), (list_repeat 32 (Vint Int.one), (Vint (Int.repr rc),
                                       (Vint (Int.repr 48), (Val.of_bool pr_flag, Vint (Int.repr 10000)))))) in
                       let CTXFinal:= HMAC256DRBGabs initial_key initial_value rc 48 pr_flag 10000 in
                       data_at Tsh t_struct_hmac256drbg_context_st CtxFinal ctx *
                                     hmac256drbg_relate CTXFinal CtxFinal))

                   else match mbedtls_HMAC256_DRBG_instantiate_function s entlen pr_flag
                                       (contents_with_add data (Zlength Data) Data)
                        with
                         | ENTROPY.error e ss =>
                            (!!(match e with
                               | ENTROPY.generic_error => Vint ret_value = Vint (Int.repr ENT_GenErr)
                               | ENTROPY.catastrophic_error => Vint ret_value = Vint (Int.repr (-9))
                              end) && (Stream ss *
                                       let CtxFinal:= ((info, (M2, p)), (list_repeat 32 (Vint Int.one), (Vint (Int.repr rc),
                                                (Vint (Int.repr 48), (Val.of_bool pr_flag, Vint (Int.repr 10000)))))) in
                                       let CTXFinal:= HMAC256DRBGabs initial_key initial_value rc 48 pr_flag 10000 in
                                       data_at Tsh t_struct_hmac256drbg_context_st CtxFinal ctx *
                                       hmac256drbg_relate CTXFinal CtxFinal))
                        | ENTROPY.success handle ss => !!(ret_value = Int.zero) &&
                                    match handle with ((((newV, newK), newRC), newEL), newPR) =>
                                      let CtxFinal := ((info, (M2, p)), (map Vint (map Int.repr newV), (Vint (Int.repr newRC), (Vint (Int.repr 32), (Val.of_bool newPR, Vint (Int.repr 10000)))))) in
                                      let CTXFinal := HMAC256DRBGabs newK newV newRC 32 newPR 10000 in
                                    data_at Tsh t_struct_hmac256drbg_context_st CtxFinal ctx *
                                    hmac256drbg_relate CTXFinal CtxFinal *
                                    Stream ss end
                        end
                end).

Lemma body_hmac_drbg_seed: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_seed hmac_drbg_seed_spec.
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
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial. rewrite int_add_repr_0_r.
  freeze [0;2;3;4;5;6] FR0.
  Time forward_call ((M1,(M2,M3)), Vptr b i, Vint (Int.repr 1), info).
   (*8.5pl2: without FR0, this akes about 5mins but succeeds*)

  Intros v. rename H into Hv.
  forward.
  forward_if (
     PROP (v=0)
   LOCAL (temp _ret (Vint (Int.repr v)); temp _t'2 (Vint (Int.repr v));
   temp _ctx (Vptr b i); temp _md_info info; temp _len (Vint (Int.repr len));
   temp _custom data; gvar sha._K256 kv)
   SEP ( (EX p : val, !!malloc_compatible (sizeof (Tstruct _hmac_ctx_st noattr)) p &&
          memory_block Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
          malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
          data_at Tsh (Tstruct _mbedtls_md_context_t noattr) (info,(M2,p)) (Vptr b i));
         FRZL FR0)).
  { destruct Hv; try omega. rewrite if_false; trivial. clear H. subst v.
    forward. simpl. Exists (Int.repr (-20864)).
    rewrite Int.eq_true.
    entailer!. thaw FR0. cancel.
    unfold_data_at 2%nat. thaw FIELDS. cancel.
    rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true; simpl; trivial. rewrite int_add_repr_0_r; trivial. }
  { subst v. clear Hv. simpl. forward. entailer!. }
  Intros. subst v. clear Hv. Intros p. rename H into MCp. simpl in MCp.

  (*Alloction / md_setup succeeded. Now get md_size*)
  drop_LOCAL 0%nat.
  drop_LOCAL 0%nat.
  forward_call tt.

  (*call mbedtls_md_hmac_starts( &ctx->md_ctx, ctx->V, md_size )*)
  thaw FR0. subst.
  assert (ZL_VV: Zlength initial_key =32) by reflexivity.
  thaw FIELDS.
  freeze [4;5;6;7] FIELDS1.
  rewrite field_at_compatible'. Intros. rename H into FC_V.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial.
  rewrite <- ZL_VV.
  freeze [0;2;5;6;7;9] FR2.
  replace_SEP 1 (UNDER_SPEC.EMPTY p).
  { entailer. apply UNDER_SPEC.mkEmpty.
    clear - Pp MCp. destruct p; try contradiction. destruct MCp.
    repeat split; simpl in *; trivial.
    + omega.
    + unfold natural_alignment in H. unfold align_attr. simpl.
      destruct H. exists (x * 2)%Z. omega.
  }
  forward_call (Vptr b i, ((info,(M2,p)):mdstate), 32, initial_key, kv, b, Int.add i (Int.repr 12)).
  { simpl. cancel. }
  { split; trivial. red. simpl. rewrite int_max_signed_eq.
    split. trivial. split. omega. rewrite two_power_pos_equiv.
    replace (2^64) with 18446744073709551616. omega. reflexivity.
    apply isbyteZ_initialKey.
  }
  Intros. clear H.

  (*call  memset( ctx->V, 0x01, md_size )*)
  freeze [0;1;3;4] FR3.
  forward_call (Tsh, Vptr b (Int.add i (Int.repr 12)), 32, Int.one).
  { rewrite sepcon_comm. apply sepcon_derives.
     - apply data_at_memory_block.
     - cancel. }

  (*ctx->reseed_interval = MBEDTLS_HMAC_DRBG_RESEED_INTERVAL;*)
  rewrite ZL_VV.
  thaw FR3. thaw FR2. unfold md_relate. simpl.
  replace_SEP 2 (field_at Tsh t_struct_hmac256drbg_context_st [StructField _md_ctx] (info, (M2, p)) (Vptr b i)). {
    entailer!. rewrite field_at_data_at.
    simpl. rewrite field_compatible_field_address by auto with field_compatible. simpl.
    rewrite int_add_repr_0_r.
    cancel.
  }
  thaw FIELDS1. forward.
  freeze [0;4;5;6;7] FIELDS2.
  freeze [0;1;2;3;4;5;6;7;8;9] ALLSEP.

  forward_if
  (PROP ( )
   LOCAL (temp _md_size (Vint (Int.repr 32)); temp _ctx (Vptr b i); temp _md_info info;
   temp _len (Vint (Int.repr (Zlength Data))); temp _custom data; gvar sha._K256 kv;
   temp _t'4 (Vint (Int.repr 32)))
   SEP (FRZL ALLSEP)).
  { elim H; trivial. }
  { clear H.
    forward_if
     (PROP ( )
      LOCAL (temp _md_size (Vint (Int.repr 32));
             temp _ctx (Vptr b i); temp _md_info info;
             temp _len (Vint (Int.repr (Zlength Data))); temp _custom data; gvar sha._K256 kv;
             temp _t'4 (Vint (Int.repr 32)))
      SEP (FRZL ALLSEP)).
    { elim H; trivial. }
    { clear H. forward. forward. entailer. }
    { intros. (*FLOYD ERROR: entailer FAILS HERE*)
      unfold overridePost.
      destruct (eq_dec ek EK_normal).
      { subst ek. (*entailer. STILL FAILS*) unfold POSTCONDITION, abbreviate.
        normalize. (*simpl. intros.*) (*apply andp_left2. normalize.*)
        entailer!. }
      { apply andp_left2; trivial.
       (*FLOYD: again, entailer fails*)
      }
    }
  }
  forward. simpl. drop_LOCAL 7%nat. (*_t'4*)

  (*NEXT INSTRUCTION:  ctx->entropy_len = entropy_len * 3 / 2*)
  thaw ALLSEP. thaw FIELDS2. forward.

  assert (FOURTYEIGHT: Int.unsigned (Int.mul (Int.repr 32) (Int.repr 3)) / 2 = 48).
  { rewrite mul_repr. simpl.
    rewrite Int.unsigned_repr. reflexivity. rewrite int_max_unsigned_eq; omega. }
  set (myABS := HMAC256DRBGabs initial_key initial_value rc 48 pr_flag 10000) in *.
  assert (myST: exists ST:hmac256drbgstate, ST =
    ((info, (M2, p)), (map Vint (list_repeat 32 Int.one), (Vint (Int.repr rc),
        (Vint (Int.repr 48), (Val.of_bool pr_flag, Vint (Int.repr 10000))))))). eexists; reflexivity.
  destruct myST as [ST HST].

  freeze [0;1;2;3;4] FR_CTX.
  freeze [3;4;6;7;8] KVStreamInfoDataFreeBlk.

  (*NEXT INSTRUCTION: mbedtls_hmac_drbg_reseed( ctx, custom, len ) *)
  freeze [1;2;3] INI.
  specialize (Forall_list_repeat isbyteZ 32 1); intros IB1.
  replace_SEP 0 (
         data_at Tsh t_struct_hmac256drbg_context_st ST (Vptr b i) *
         hmac256drbg_relate myABS ST).
  { go_lower. thaw INI. clear KVStreamInfoDataFreeBlk. thaw FR_CTX.
    unfold_data_at 2%nat.
    subst ST; simpl. cancel. normalize.
    apply andp_right. apply prop_right. repeat split; trivial. apply IB1. split; omega.
    unfold md_full. simpl.
    rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true; simpl; trivial.
    cancel.
    apply UNDER_SPEC.REP_FULL.
  }

  clear INI.
  thaw KVStreamInfoDataFreeBlk. freeze [3;7] OLD_MD.
  forward_call (Data, data, Zlength Data, Vptr b i, ST, myABS, kv, Info, s).
  { unfold hmac256drbgstate_md_info_pointer.
    subst ST; simpl. cancel.
  }
  { subst myABS; simpl. rewrite <- initialize.max_unsigned_modulus in *.
    split. omega. (* rewrite int_max_unsigned_eq; omega.*)
    split. reflexivity.
    split. reflexivity.
    split. omega.
    split. (*change Int.modulus with 4294967296.*) omega.
    split. (* change Int.modulus with 4294967296.*)
       unfold contents_with_add. if_tac. omega. rewrite Zlength_nil; omega.
    split. apply IB1. split; omega.
    assumption.
  }

  Intros v.
  assert (ZLc': Zlength (contents_with_add data (Zlength Data) Data) = 0 \/
                 Zlength (contents_with_add data (Zlength Data) Data) = Zlength Data).
         { unfold contents_with_add. if_tac. right; trivial. left; trivial. }
  forward.

  forward_if (
   PROP ( v = nullval)
   LOCAL (temp _ret v; temp _t'7 v;
   temp _entropy_len (Vint (Int.repr 32));
   temp _md_size (Vint (Int.repr 32)); temp _ctx (Vptr b i);
   temp _md_info info;
   temp _len (Vint (Int.repr (Zlength Data)));
   temp _custom data; gvar sha._K256 kv)
   SEP (reseedPOST v Data data (Zlength Data) s
          myABS (Vptr b i) Info kv ST; FRZL OLD_MD)).
  { rename H into Hv. forward. simpl. Exists v.
    apply andp_right. apply prop_right; trivial.
    apply andp_right. apply prop_right; split; trivial.
    unfold reseedPOST.

    remember ((zlt 256 (Zlength Data) || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data)) %bool) as d.
    unfold myABS in Heqd; simpl in Heqd.
    destruct (zlt 256 (Zlength Data)); simpl in Heqd.
    + subst d. unfold hmac256drbgstate_md_info_pointer, hmac256drbg_relate; simpl.
      simpl. subst myABS. normalize. simpl. cancel.
      Exists p. thaw OLD_MD. normalize.
      apply andp_right. apply prop_right; repeat split; trivial. cancel.
      apply deep_interp_empty.
    + destruct (zlt 384 (48 + Zlength Data)); simpl in Heqd; try omega.
      subst d.
      unfold hmac256drbgstate_md_info_pointer, hmac256drbg_relate; simpl. normalize.
      rename H into RV.
      remember (mbedtls_HMAC256_DRBG_reseed_function s myABS
         (contents_with_add data (Zlength Data) Data)) as MRS.
      rewrite (ReseedRes _ _ _ RV). cancel.
      unfold return_value_relate_result in RV.
      assert (ZLc'256F: Zlength (contents_with_add data (Zlength Data) Data) >? 256 = false).
      { apply Zgt_is_gt_bool_f. destruct ZLc' as [ZLc' | ZLc']; rewrite ZLc'; trivial. omega. }
      unfold hmac256drbgabs_common_mpreds, hmac256drbgstate_md_info_pointer.
      destruct MRS.
      - exfalso. inv RV. simpl in Hv. discriminate.
      - simpl. normalize. Exists p. thaw OLD_MD. cancel.
        subst myABS. rewrite <- instantiate_reseed in HeqMRS; trivial.
        rewrite <- HeqMRS.
        normalize.
        apply andp_right. apply prop_right; repeat split; trivial.
        cancel.
        apply deep_interp_empty.
  }
  { rename H into Hv. forward.
    go_lower. simpl in Hv. apply typed_false_of_bool in Hv. apply negb_false_iff in Hv.
    symmetry in Hv; apply binop_lemmas2.int_eq_true in Hv. subst v.
    entailer!.
  }
  Intros. subst v.
  unfold reseedPOST.
  remember ((zlt 256 (Zlength Data)
          || zlt 384 (hmac256drbgabs_entropy_len myABS + Zlength Data))%bool) as d.
  destruct d; Intros.
  remember (mbedtls_HMAC256_DRBG_reseed_function s myABS
         (contents_with_add data (Zlength Data) Data)) as MRS.
  unfold hmac256drbgabs_reseed. rewrite <- HeqMRS. subst myABS; simpl.
  unfold return_value_relate_result in H.
  destruct MRS. Focus 2. exfalso. destruct e. inv H.
                     destruct ENT_GenErrAx as [EL1 _]. rewrite <- H in EL1. elim EL1; trivial.
  clear H.
  destruct d as [[[[newV newK] newRC] dd] newPR].
  unfold hmac256drbgabs_common_mpreds. simpl. subst ST. unfold hmac256drbgstate_md_info_pointer. simpl. Intros.
  unfold_data_at 1%nat. freeze [0;1;2;4;5;6;7;8;9;10;11;12] ALLSEP.
  forward. forward.
  Exists Int.zero. simpl.
  apply andp_right. apply prop_right; trivial.
  apply andp_right. apply prop_right; split; trivial.
  symmetry in Heqd. apply orb_false_iff in Heqd. destruct Heqd as [Heqd1 Heqd2].
  destruct (zlt 256 (Zlength Data)); try discriminate. simpl in *. rewrite Heqd2.
  thaw ALLSEP. thaw OLD_MD. Exists p. cancel.
  normalize.
  assert (ZLc'256F: Zlength (contents_with_add data (Zlength Data) Data) >? 256 = false).
      { destruct ZLc' as [HH | HH]; rewrite HH. reflexivity.
        apply Zgt_is_gt_bool_f. omega. }
  rewrite <- instantiate_reseed in HeqMRS; trivial.
  rewrite <- HeqMRS.
  normalize.
  apply andp_right. apply prop_right; repeat split; trivial.
  cancel.
  unfold_data_at 1%nat. cancel.
  apply deep_interp_empty.
Time Qed. (*Finished transaction in 65.282 secs (57.5u,0.031s) (successful)*)
