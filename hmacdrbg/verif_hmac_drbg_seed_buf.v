Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.
Require Import VST.floyd.sublist.

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

Lemma body_hmac_drbg_seed_buf: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_seed_buf hmac_drbg_seed_buf_spec.
Proof.
  start_function.
  abbreviate_semax.
  destruct H as [HDlen1 [HDlen2 HData]].
  rewrite data_at_isptr with (p:=ctx). Intros.
  destruct ctx; try contradiction; clear Pctx.
  unfold_data_at 1%nat.
  destruct Ctx as [MdCTX [V [RC [EL [PR RI]]]]]. simpl.
  destruct MdCTX as [M1 [M2 M3]].
  freeze [1;2;3;4;5] FIELDS. 
  rewrite field_at_compatible'. Intros. rename H into FC_mdx.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial. rewrite ptrofs_add_repr_0_r.
  freeze [0;2;3;4;5] FR0.
  Time forward_call ((M1,(M2,M3)), Vptr b i, shc, Vint (Int.repr 1), info).

  Intros v. rename H into Hv. simpl.
  forward.
  forward_if.
  { destruct Hv; try omega. rewrite if_false; trivial.
    forward. Exists (Vint (Int.repr (-20864))). rewrite if_true; trivial.
    entailer!. thaw FR0. cancel. 
    unfold_data_at 2%nat. thaw FIELDS. cancel. rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true; simpl; trivial. rewrite ptrofs_add_repr_0_r; auto.  }
  subst v; clear Hv. rewrite if_true; trivial.
  Intros. Intros p.
  forward_call tt.

  thaw FR0. unfold hmac256drbg_relate. destruct CTX. Intros; subst.
  rename V0 into V. rename H0 into lenV.
  thaw FIELDS.
  freeze [3;4;5;6] FIELDS1.
  rewrite field_at_compatible'. Intros. rename H into FC_V.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial.
 (* rewrite <- lenV. *)
  freeze [0;4;5;6] FR2.
  forward_call (Vptr b i, shc, (((*M1*)info,(M2,p)):mdstate), 32, V, b, Ptrofs.add i (Ptrofs.repr 12), shc, gv).
  { rewrite lenV; simpl. cancel. }
  { split; auto. split; auto. split; auto.
  }
  Intros.

  forward_call tt.

  freeze [0;1;3;4] FR3. rewrite lenV.
  forward_call (shc, Vptr b (Ptrofs.add i (Ptrofs.repr 12)), 32, Int.one).
  { rewrite sepcon_comm. apply sepcon_derives. 2: cancel. 
    eapply derives_trans. apply data_at_memory_block. simpl sizeof. cancel.
  }

  thaw FR3. thaw FR2. unfold md_relate. simpl.
  freeze [1;3;5;6;7;8] OTHER.
  freeze [1;2;3] INI.

  assert (exists xx:reptype t_struct_hmac256drbg_context_st, xx =
   (((*M1*)info, (M2, p)),
    (list_repeat (Z.to_nat 32) (Vint Int.one),
     (Vint (Int.repr reseed_counter),
      (Vint (Int.repr entropy_len),
       (Val.of_bool prediction_resistance,
        (Vint (Int.repr reseed_interval)))))))). eexists; reflexivity.
  destruct H as [xx XX].

  replace_SEP 0
    (data_at shc t_struct_hmac256drbg_context_st xx (Vptr b i)).
  { entailer. unfold_data_at 1%nat.
    thaw INI.
    rewrite field_at_data_at. unfold field_address. rewrite if_true. 2: assumption.
    simpl. rewrite ptrofs_add_repr_0_r.
    unfold t_struct_md_ctx_st. cancel.
    clear OTHER. thaw FIELDS1. cancel.
    rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true. 2: assumption. simpl. cancel.
  }
  clear INI. thaw OTHER.
  set (ABS:= HMAC256DRBGabs V (list_repeat 32 Byte.one) reseed_counter entropy_len prediction_resistance reseed_interval) in *.
  gather_SEP 1 2.
  replace_SEP 0 (hmac256drbg_relate (*(HMAC256DRBGabs V0 (list_repeat 32 1) reseed_counter entropy_len prediction_resistance reseed_interval)*) ABS xx).
  { subst ABS. unfold md_full. entailer!. unfold md_full; simpl; entailer!.
    apply UNDER_SPEC.REP_FULL.
  }

  forward_call (Data, data, shd,  d_len, Vptr b i, shc, xx, ABS, Info, gv).
  { subst xx. unfold hmac256drbgstate_md_info_pointer; simpl. cancel. (*thanks to "M1==info"*)
  }
  freeze [0;1;2;3;4] ALLSEP.
  forward. Exists (Vint (Int.repr 0)). rewrite if_false; [ | intros N; inv N]. 
  thaw ALLSEP.
  unfold hmac256drbgabs_common_mpreds. simpl.
  fold (list_repeat 32 Byte.one). fold (list_repeat 32 (Vint Int.one)).
  remember(HMAC256_DRBG_update (contents_with_add data d_len Data) V
              (list_repeat 32 Byte.one)) as HH.
  destruct HH as [KEY VALUE]. simpl.
  Exists KEY VALUE p. normalize.
  apply andp_right; [apply prop_right; repeat split; auto | cancel].
Time Qed.
          (*Coq8.6: 13secs*)
          (*Feb22nd, 2017: 116.921 secs (111.953u,0.015s) (successful)*)
          (*earlier: 26.657 secs (26.656u,0.s) (successful)*)
(*
Definition hmac_drbg_seed_buf_spec2 :=
  DECLARE _mbedtls_hmac_drbg_seed_buf
   WITH ctx: val, info:val, d_len: Z, data:val, Data: list Z,
        Ctx: hmac256drbgstate,
        CTX: hmac256drbgabs,
        kv: val, Info: md_info_state
    PRE [_ctx OF tptr (Tstruct _mbedtls_hmac_drbg_context noattr),
         _md_info OF (tptr (Tstruct _mbedtls_md_info_t noattr)),
         _data OF tptr tuchar, _data_len OF tuint ]
       PROP ( (d_len = Zlength Data \/ d_len=0) /\
              0 <= d_len <= Int.max_unsigned /\ Forall isbyteZ Data)
       LOCAL (temp _ctx ctx; temp _md_info info;
              temp _data_len (Vint (Int.repr d_len)); temp _data data; gvar sha._K256 kv)
       SEP (
         data_at Tsh t_struct_hmac256drbg_context_st Ctx ctx;
         hmac256drbg_relate CTX Ctx;
         data_at Tsh t_struct_mbedtls_md_info Info info;
         da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data;
         K_vector kv)
    POST [ tint ]
       EX ret_value:_,
       PROP ()
       LOCAL (temp ret_temp ret_value)
       SEP (orp ( !!(ret_value = Vint (Int.repr (-20864))) &&
                  data_at Tsh t_struct_hmac256drbg_context_st Ctx ctx *
                  hmac256drbg_relate CTX Ctx *
                  data_at Tsh t_struct_mbedtls_md_info Info info *
                  da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data *
                  K_vector kv)
                ( !!(ret_value <> Vint (Int.repr (-20864))) &&
  (                      match Ctx, CTX
                         with (mds, (V', (RC', (EL', (PR', RI'))))),
                              HMAC256DRBGabs key V RC EL PR RI
                         => EX KEY:list Z, EX VAL:list Z, EX p:val,
                          !!(HMAC256_DRBG_update (contents_with_add data d_len Data) V (list_repeat 32 1) = (KEY, VAL))
                             && md_full key mds * malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
                                data_at Tsh t_struct_hmac256drbg_context_st ((info, (fst(snd mds), p)), (map Vint (map Int.repr VAL), (RC', (EL', (PR', RI'))))) ctx *
                                hmac256drbg_relate (HMAC256DRBGabs KEY VAL RC EL PR RI) ((info, (fst(snd mds), p)), (map Vint (map Int.repr VAL), (RC', (EL', (PR', RI'))))) *
                               data_at Tsh t_struct_mbedtls_md_info Info info *
                               da_emp Tsh (tarray tuchar (Zlength Data)) (map Vint (map Int.repr Data)) data *
                               K_vector kv
                        end))
       ).

Lemma body_hmac_drbg_seed_buf2: semax_body HmacDrbgVarSpecs HmacDrbgFunSpecs
      f_mbedtls_hmac_drbg_seed_buf hmac_drbg_seed_buf_spec2.
Proof.
  start_function.
  abbreviate_semax.
  destruct H as [HDlen1 [HDlen2 HData]].
  rewrite data_at_isptr with (p:=ctx). Intros.
  destruct ctx; try contradiction.
  unfold_data_at 1%nat.
  destruct Ctx as [MdCTX [V [RC [EL [PR RI]]]]]. simpl.
  destruct MdCTX as [M1 [M2 M3]].
  freeze [1;2;3;4;5] FIELDS.
  rewrite field_at_compatible'. Intros. rename H into FC_mdx.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial. rewrite int_add_repr_0_r.
  freeze [0;2;3;4;5] FR0.
  Time forward_call ((M1,(M2,M3)), Vptr b i, Vint (Int.repr 1), info).
   (*without FR0, this takes about 5mins but succeeds*)

  Intros v. rename H into Hv.
  forward.
  forward_if (
     PROP (v=0)
   LOCAL (temp _ret (Vint (Int.repr v)); temp _t'2 (Vint (Int.repr v));
   temp _ctx (Vptr b i); temp _md_info info; temp _data_len (Vint (Int.repr d_len));
   temp _data data; gvar sha._K256 kv)
   SEP ( (EX p : val, !!malloc_compatible (sizeof (Tstruct _hmac_ctx_st noattr))p &&
            memory_block Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
            malloc_token Tsh (sizeof (Tstruct _hmac_ctx_st noattr)) p *
          data_at Tsh (Tstruct _mbedtls_md_context_t noattr) (info,(M2,p)) (Vptr b i));
         FRZL FR0)).
  { destruct Hv; try omega. rewrite if_false; trivial.
    forward. Exists (Vint (Int.repr (-20864))).
    entailer!. thaw FR0. cancel. apply orp_right1. cancel.
    unfold_data_at 2%nat. thaw FIELDS. cancel. rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true; simpl; trivial. rewrite int_add_repr_0_r; trivial. }
  { subst v; clear Hv. rewrite if_true; trivial.
    forward. entailer!.
  }
  Intros. subst v. clear Hv. Intros p. rename H into MCp.

  forward_call tt.

  thaw FR0. unfold hmac256drbg_relate. destruct CTX. normalize.
  thaw FIELDS.
  freeze [4;5;6;7] FIELDS1.
  rewrite field_at_compatible'. Intros. rename H1 into FC_V.
  rewrite field_at_data_at. unfold field_address. simpl. rewrite if_true; trivial.
  rewrite <- H.
  freeze [0;2;5;6;7] FR2.
  replace_SEP 1 (UNDER_SPEC.EMPTY p).
  { entailer!. 
    eapply derives_trans. 2: apply UNDER_SPEC.mkEmpty.
    rewrite data_at__memory_block. simpl. entailer!. 
  }
  forward_call (Vptr b i, (((*M1*)info,(M2,p)):mdstate), 32, V0, kv, b, Int.add i (Int.repr 12)).
  { rewrite H, int_add_repr_0_r; simpl.
    apply prop_right; repeat split; trivial.
  }
  { simpl. cancel. }
  { split; trivial. red. simpl. rewrite int_max_signed_eq, H.
    split. trivial. split. omega. rewrite two_power_pos_equiv.
    replace (2^64) with 18446744073709551616. omega. reflexivity.
  }
  Intros.

  forward_call tt.

  freeze [0;1;3;4] FR3.
  forward_call (Tsh, Vptr b (Int.add i (Int.repr 12)), 32, Int.one).
  { rewrite sepcon_comm. apply sepcon_derives. 2: cancel.
    eapply derives_trans. apply data_at_memory_block.
    rewrite H. simpl. cancel.
  }

  thaw FR3. thaw FR2. unfold md_relate. simpl.
  freeze [1;3;5;6;7;8] OTHER.
  freeze [1;2;3] INI.

  assert (exists xx:reptype t_struct_hmac256drbg_context_st, xx =
   (((*M1*)info, (M2, p)),
    (list_repeat (Z.to_nat 32) (Vint Int.one),
     (Vint (Int.repr reseed_counter),
      (Vint (Int.repr entropy_len),
       (Val.of_bool prediction_resistance,
        (Vint (Int.repr reseed_interval)))))))). eexists; reflexivity.
  destruct H1 as [xx XX].


  replace_SEP 0
    (data_at Tsh t_struct_hmac256drbg_context_st xx (Vptr b i)).
  { entailer. unfold_data_at 1%nat.
    thaw INI.
    rewrite field_at_data_at. unfold field_address. rewrite if_true. 2: assumption.
    simpl. rewrite int_add_repr_0_r.
    unfold t_struct_md_ctx_st. cancel.
    clear OTHER. thaw FIELDS1. cancel.
    rewrite field_at_data_at. simpl.
    unfold field_address. rewrite if_true. 2: assumption. simpl. cancel.
  }
  clear INI. thaw OTHER.
  specialize (Forall_list_repeat isbyteZ 32 1); intros IB1.
  set (ABS:= HMAC256DRBGabs V0 (list_repeat 32 1) reseed_counter entropy_len prediction_resistance reseed_interval) in *.
  replace_SEP 1 (hmac256drbg_relate (*(HMAC256DRBGabs V0 (list_repeat 32 1) reseed_counter entropy_len prediction_resistance reseed_interval)*) ABS xx).
  { entailer!. subst ABS; unfold md_full. simpl.
    apply andp_right. apply prop_right. repeat split; trivial. apply IB1. split; omega.
    apply UNDER_SPEC.REP_FULL.
  }

  forward_call (Data, data, d_len, Vptr b i, xx, ABS, kv, Info).
  { subst xx. unfold hmac256drbgstate_md_info_pointer; simpl. cancel. (*thanks to "M1==info"*)
  }
  { subst ABS; simpl. repeat split; trivial; try omega. apply IB1. split; omega.
  }

  forward. Exists (Vint (Int.repr 0)). normalize.
  apply andp_right. apply prop_right; split; trivial.
  apply orp_right2.
  unfold hmac256drbgabs_common_mpreds.
  remember(HMAC256_DRBG_update (contents_with_add data d_len Data) V0
    [1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1; 1;
     1; 1; 1; 1; 1; 1; 1; 1]) as HH.
  destruct HH as [KEY VALUE]. simpl. normalize.
  Exists KEY.
  apply andp_right. apply prop_right. intros N. inv N.
  unfold hmac256drbgstate_md_info_pointer. simpl.
  Exists VALUE p. normalize.
  apply andp_right. apply prop_right. repeat split; trivial.
  cancel.
Time Qed.  (*Coq8.6: 21secs*)
           (*Feb 22nd 2017: Finished transaction in 116.281 secs (105.203u,0.062s) (successful)
            earlier: Finished transaction in 45.61 secs (21.031u,0.s) (successful)*)
*)