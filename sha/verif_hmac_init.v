Require Import VST.floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.hmac.
Require Import sha.spec_hmac.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.

Require Import sha.verif_hmac_init_part1.
Require Import sha.verif_hmac_init_part2.

(*to be proven in veric: a frame rule for frozen assertions:
Lemma semax_freeze n Espec {cs: compspecs} Delta P Q  R Rs c xs ys P' Q' R':
 R = map liftx Rs ->
 nth n Rs emp = FRZL xs ->
 delete_nth n Rs = ys ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx (map liftx ys)))) c (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx R')))) ->
 @semax cs Espec Delta (PROPx P (LOCALx Q (SEPx R))) c (normal_ret_assert (PROPx P' (LOCALx Q' (SEPx (map liftx xs ++ R'))))).
Proof. intros. subst.
rewrite semax_unfold.
eapply semax_pre_post. 3: eassumption. 2: intros; entailer.
apply andp_left2. unfold PROPx. normalize.
unfold LOCALx. apply derives_refl'.
f_equal. unfold SEPx. clear - H0.
rewrite map_app, fold_right_sepcon_app. rewrite FRZL_ax in H0.
rewrite (fold_right_sepcon_deletenth' n). rewrite map_delete_nth. f_equal.
rewrite mapnth' with (d:=emp); try reflexivity.
extensionality. rewrite fold_right_sepcon_liftx, <- H0. trivial.
Qed.*)

Lemma initbodyproof Espec c k l wsh sh key gv h1 pad ctxkey
  (Hwsh: writable_share wsh)
  (Hsh: readable_share sh):
@semax CompSpecs Espec (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs nil)
  (PROP  ()
   LOCAL  (lvar _ctx_key (tarray tuchar 64) ctxkey;
           lvar _pad (tarray tuchar 64) pad; temp _ctx c; temp _key k;
           temp _len (Vint (Int.repr l)); gvars gv)
   SEP  (data_at_ Tsh (tarray tuchar 64) ctxkey;
         data_at_ Tsh (tarray tuchar 64) pad;
         K_vector gv; initPre wsh sh c k h1 l key))
  (Ssequence (fn_body f_HMAC_Init) (Sreturn None))
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP  ()
         LOCAL ()
         SEP  (hmacstate_ wsh (hmacInit key) c; 
                 initPostKey sh k key; K_vector gv)))
     (stackframe_of f_HMAC_Init)).
Proof. abbreviate_semax.
(*freeze [1; 2; 3] FR1. *)simpl. 
Time forward. (*0.8 versus 1.3*)

Time assert_PROP (isptr ctxkey) as Pckey by entailer!. (*0.7*)
apply isptrD in Pckey; destruct Pckey as [ckb [ckoff PcKey]].
subst ctxkey.

(*isolate branch if (key != NULL) *)
forward_if (PostKeyNull c k pad gv h1 l wsh sh key ckb ckoff).
  { apply denote_tc_test_eq_split. unfold initPre; normalize. destruct k; try contradiction.
    clear H.
    remember (Int.eq i Int.zero). destruct b.
     apply binop_lemmas2.int_eq_true in Heqb. rewrite Heqb; auto with valid_pointer. entailer!.
     entailer!. apply sepcon_valid_pointer2. apply @data_block_valid_pointer. auto.
     red in H2. omega.
     apply valid_pointer_null. }

  { (* THEN*)
    simpl.
    unfold force_val2, force_val1 in H; simpl in H.
    unfold initPre.
    destruct k; try solve [eapply semax_pre; try eapply semax_ff; entailer].
    (*key' is integer, ie Null*)
      remember (Int.eq i Int.zero) as d.
      destruct d; try solve [eapply semax_pre; try eapply semax_ff; entailer].
      apply binop_lemmas2.int_eq_true in Heqd. simpl in *. elim H. subst; reflexivity.
    (*key' is ptr*)
    normalize. clear H. rename H0 into keyLen.
    Time assert_PROP (isptr c) as Pc by entailer!. (*1*)
    apply isptrD in Pc; destruct Pc as [cb [cofs CC]]; rewrite CC in *.
    rename b into kb; rename i into kofs.
    replace_SEP 1 (data_at sh (tarray tuchar (Zlength key)) (map Vubyte key) (Vptr kb kofs)).
       Time unfold data_block; entailer!. (*1.5*)

    freeze [0; 1; 2; 3; 4] FR1.
    Time forward. (*1secs, versus 2secs*)
    Time forward. (*0.8 versus 1.8 j=HMAC_MAX_MD_CBLOCK*)
    thaw FR1.
    freeze [1;2;4] FR2.
    Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs))
        as FC_ctx by entailer!. (*1 versus 1.7*)

    assert (field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] (Vptr cb cofs)) as  FC_md_ctx.
    { red. clear - FC_ctx. red in FC_ctx; simpl in FC_ctx.
      repeat split; try solve [apply FC_ctx]. left; reflexivity. }

    Time assert_PROP (field_compatible (Tarray tuchar 64 noattr) [] (Vptr ckb ckoff))
      as FC_cxtkey by entailer!. (*1.1 versus 1.9*)

    Time forward_if (PROP  ()
      LOCAL  (temp _reset (Vint (Int.repr 1));
        lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); lvar _pad (tarray tuchar 64) pad;
        temp _ctx (Vptr cb cofs); temp _key (Vptr kb kofs);
        temp _len (Vint (Int.repr l)); gvars gv)
      SEP  (data_at_ Tsh (tarray tuchar 64) pad;
            data_at wsh t_struct_hmac_ctx_st (*keyedHMS'*) HMS (Vptr cb cofs);
            data_at sh (tarray tuchar (Zlength key)) (map Vubyte key)
              (Vptr kb kofs);
           data_at Tsh (tarray tuchar 64) (map Vubyte (HMAC_SHA256.mkKey key))
                  (Vptr ckb ckoff);
          K_vector gv)). (*4.3 versus 5.6*)
    { (* j < len*) 
      rename H into lt_64_l.
      thaw FR2.
      subst MORE_COMMANDS; unfold abbreviate.
      subst.
      destruct keyLen as [? ?]. unfold POSTCONDITION, abbreviate.
      eapply semax_pre; [  |
        eapply (Init_part1_j_lt_len Espec kb ckb cb kofs ckoff cofs l wsh sh key gv pad HMS); try eassumption; trivial].
      entailer!.
      replace (two_p 64) with 18446744073709551616 by reflexivity; rep_omega.
      rewrite Int.signed_repr in lt_64_l; [ trivial | rep_omega].
    }
    { (* j >= len*)
      rename H into ge_64_l. unfold MORE_COMMANDS, POSTCONDITION, abbreviate. subst.
      destruct keyLen as [? ?].
      thaw FR2.
      eapply semax_pre; [  | 
        apply (Init_part1_len_le_j Espec kb ckb cb kofs ckoff cofs l wsh sh key gv pad HMS); try eassumption; trivial].
      entailer!.
      replace (two_p 64) with 18446744073709551616 by reflexivity; rep_omega.
      rewrite Int.signed_repr in ge_64_l; [ trivial | rep_omega ].
    }
   subst.
   unfold PostKeyNull, initPostKeyNullConditional.
   Exists cb cofs 1.
   Time entailer; cancel. (* 1.115 sec;  was: 7.3 versus 8.1*)
  }
  { (*key == NULL*)
     rename H into Hk; rewrite Hk in *.
     Time forward. (*0.2*)
     unfold PostKeyNull, initPre, initPostKeyNullConditional. subst k.
     Time entailer. (*4.2 versus 3.9*)
        unfold hmacstate_PreInitNull. Intros r v.
        Time assert_PROP (isptr c) as Pctx' by entailer!. (*4.3*)
        apply isptrD in Pctx'; destruct Pctx' as [cb [cofs CTX']].
        Exists cb cofs 0. rewrite if_true; trivial.
        Exists r v. Time entailer!. (*6.9*) }
{
unfold PostKeyNull. Intros cb cofs r.
subst c.
rename H0 into R.

(*isolate branch if (reset) *)
apply seq_assoc.
forward_if (EX shaStates:_ ,
          PROP  (innerShaInit (HMAC_SHA256.mkKey key) =(fst shaStates) /\
                  s256_relate (fst shaStates) (fst (snd shaStates)) /\
                  outerShaInit (HMAC_SHA256.mkKey key)
                          = (fst (snd (snd shaStates))) /\
                  s256_relate (fst (snd (snd shaStates))) (snd (snd (snd shaStates))))
          LOCAL  (lvar _pad (tarray tuchar 64) pad;
                  lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
                  temp _ctx (Vptr cb cofs); temp _key k;
                  temp _len (Vint (Int.repr l));
                  gvars gv)
          SEP  (data_at_ Tsh (tarray tuchar 64) pad;
                data_at_ Tsh (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
                initPostResetConditional r (Vptr cb cofs) k h1 wsh sh key (fst (snd shaStates)) (snd (snd (snd shaStates)));
                K_vector gv)).
  { (* THEN*)
    rename H into r_true.
    destruct R as [R | R]; [subst r; contradiction r_true; reflexivity | ].
    subst r; clear r_true.
    remember (map Vubyte (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad)) as IPADcont.
    remember (map Vubyte (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Opad)) as OPADcont.
    assert (ZLI: Zlength (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256.BlockSize; simpl. trivial.
    assert (ZLO: Zlength (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Opad) = 64).
            rewrite Zlength_mkArgZ.
            repeat rewrite map_length. rewrite mkKey_length.
            unfold SHA256.BlockSize; simpl. trivial.
    unfold data_at_, tarray.
    Time assert_PROP (isptr pad) as Ppad by entailer!. (*1*)
    apply isptrD in Ppad; destruct Ppad as [pb [pofs Hpad]]. subst pad.

    apply semax_pre with (P':=EX b:_, EX i:_,
       PROP  (k=Vptr b i)
       LOCAL  (temp _reset (Vint (Int.repr 1));
              lvar _ctx_key (Tarray tuchar 64 noattr) (Vptr ckb ckoff);
              lvar _pad (Tarray tuchar 64 noattr) (Vptr pb pofs);
              temp _ctx (Vptr cb cofs); temp _key (Vptr b i);
              temp _len (Vint (Int.repr l)); gvars gv)
       SEP  (@data_at CompSpecs wsh t_struct_hmac_ctx_st HMS (Vptr cb cofs);
             @data_at CompSpecs Tsh (tarray tuchar 64)
                  (@map byte val Vubyte(HMAC_SHA256.mkKey key))
                  (Vptr ckb ckoff);
            @data_at CompSpecs sh (tarray tuchar (@Zlength byte key))
                  (@map byte val Vubyte key) (Vptr b i);
            @field_at_ CompSpecs Tsh (Tarray tuchar 64 noattr) [] (Vptr pb pofs);
            K_vector gv)).
    { clear POSTCONDITION.
      unfold initPostKeyNullConditional.
      go_lower. ent_iter. (* Issue: we just want these two parts of entailer here... *)
      destruct k; try contradiction.
      Time simple_if_tac; entailer!. (* 0.92 *)
      Exists b i.
      entailer!. }
    Intros kb kofs.
    rename H into H0.
       assert (ZZ: exists HMS':reptype t_struct_hmac_ctx_st, HMS'=HMS). exists HMS. trivial.
       destruct ZZ as [HMS' HH].
       remember (K_vector gv * data_at wsh t_struct_hmac_ctx_st HMS' (Vptr cb cofs)
                          * data_at sh (tarray tuchar (Zlength key)) (map Vubyte key)
                         (Vptr kb kofs)) as myPred.
    forward_seq.
    { (*ipad loop*)
      (*semax_subcommand HmacVarSpecs HmacFunSpecs f_HMAC_Init.*)
       eapply semax_pre.
       2:{ eapply (ipad_loop Espec pb pofs cb cofs ckb ckoff kb kofs l key gv myPred); try eassumption. }
       subst HMS'. clear - HeqmyPred.  Time entailer!; apply derives_refl. 
    }
    subst myPred HMS'.

    (*continuation after ipad-loop*)
    Intros.
    freeze [2;3;4] FR1.
    Time (assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs)) as FC_C
       by entailer!). (*1.9 versus 6.5*)
    Time unfold_data_at 1%nat. (*1*)
    freeze [0;1;4] FR2.
    rewrite (field_at_data_at  wsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField _i_ctx] (Vptr cb cofs)) as FC_ICTX.
    { apply prop_right. clear - FC_C. red in FC_C.
      repeat split; try solve [apply FC_C]. right; left; trivial. }
    rewrite field_address_offset by auto with field_compatible.
    simpl.

    (*Call to _SHA256_Init*)
    Time forward_call (Vptr cb (Ptrofs.add cofs (Ptrofs.repr 108)), wsh). (*9.5 versus 10.5*)

    (*Call to _SHA256_Update*)
    thaw FR2.
    thaw FR1.
    freeze [1;3;5;6] FR3.
    Time forward_call (@nil byte,
                  HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad,
                  Vptr cb (Ptrofs.add cofs (Ptrofs.repr 108)), wsh, Vptr pb pofs, Tsh, 64, gv).
        (*4 versus 10.5*)
    { assert (FR : Frame = [FRZL FR3]).
        subst Frame; reflexivity.
      rewrite FR; clear FR Frame.
      simpl. Time cancel. (*0.3*)
      unfold data_block. rewrite  ZLI, HeqIPADcont.
      simpl. Time entailer!. (*0.9*)
    }
    { clear HeqOPADcont(*; subst IPADcont*).
        rewrite Zlength_mkArgZ. repeat rewrite map_length. rewrite mkKey_length. intuition.
    }
    simpl.
    rewrite sublist_same; try rewrite ZLI; trivial.
    remember (HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Ipad) as ipadSHAabs.

    (*essentially the same for opad*)
    thaw FR3.
    freeze [0; 3; 5;6] FR4.
    forward_seq.
    { (*opad loop*)
      eapply semax_pre.
      2: apply (opadloop Espec pb pofs cb cofs ckb ckoff kb kofs l wsh key gv (FRZL FR4) Hwsh IPADcont) with (ipadSHAabs:=ipadSHAabs); try reflexivity; subst ipadSHAabs; try assumption.
      entailer!.
    }

    (*continuation after opad-loop*)
    thaw FR4.
    freeze [0;1;4;6] FR5.
    freeze [0;1;2] FR6.
    rewrite (field_at_data_at wsh t_struct_hmac_ctx_st [StructField _o_ctx]).
    assert_PROP (field_compatible t_struct_hmac_ctx_st [StructField _o_ctx] (Vptr cb cofs)) as FC_OCTX.
    { apply prop_right. clear - FC_C. red in FC_C. 
      repeat split; try solve [apply FC_C]. right; right; left; trivial. }
    rewrite field_address_offset by auto with field_compatible.

    (*Call to _SHA256_Init*)
    unfold MORE_COMMANDS, abbreviate.

    Time forward_call (Vptr cb (Ptrofs.add cofs (Ptrofs.repr 216)), wsh). (*6.4 versus 10.6*)

    (* Call to sha_update*)
    thaw FR6.
    Time forward_call (@nil byte,
            HMAC_SHA256.mkArg (HMAC_SHA256.mkKey key) Opad,
            Vptr cb (Ptrofs.add cofs (Ptrofs.repr 216)), wsh, 
            Vptr pb pofs, Tsh, 64, gv). (*4.5*)
    { assert (FR : Frame = [FRZL FR5]).
        subst Frame; reflexivity.
      rewrite FR; clear FR Frame.
      unfold data_block. simpl.
      rewrite ZLO; trivial.
      Time entailer!. (*1.5*)
    }
    { rewrite ZLO; intuition. }

    rewrite sublist_same; try rewrite ZLO; trivial.

    Time entailer!. (*4.7 *)
    thaw FR5. unfold sha256state_, data_block.
    rewrite ZLO. (*superfluous...subst ipadSHAabs.*)
    Intros oUpd iUpd.
    change_compspecs CompSpecs.
    Exists (innerShaInit (HMAC_SHA256.mkKey key),(iUpd,(outerShaInit (HMAC_SHA256.mkKey key),oUpd))).
    simpl. rewrite !prop_true_andp by (auto; intuition).
    Time cancel. (*5 versus 4*)
    unfold_data_at 3%nat.
    rewrite (field_at_data_at wsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    rewrite (field_at_data_at wsh t_struct_hmac_ctx_st [StructField _o_ctx]).
    rewrite field_address_offset by auto with field_compatible.
    rewrite field_address_offset by auto with field_compatible.
    Time cancel. (*0.5*)
  }
  { (*ELSE*)
    Time forward. (*0.2*)
    subst. unfold initPostKeyNullConditional. go_lower. (*Time entailer!.  (*6.5*)*)
    destruct R; subst; [clear H |discriminate]. 
    Time destruct k; try solve[entailer]. (*2.9*)
    unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
    Time simple_if_tac; [ | entailer!].
    Intros v x. destruct h1.
    Exists (iSha, (iCtx v, (oSha, oCtx v))). simpl.
    unfold hmacstate_PreInitNull, hmac_relate_PreInitNull; simpl.
    Exists v x.
    change (Tarray tuchar 64 noattr) with (tarray tuchar 64).
    rewrite !prop_true_andp by (auto; intuition). cancel.
   } 

{ (*Continuation after if (reset*)
  apply extract_exists_pre; intros [iSA [iS [oSA oS]]]. simpl.
  assert_PROP (is_pointer_or_null k) as Ptr_null_k by entailer!.
  destruct k; simpl in Ptr_null_k; try contradiction.
  { (*Case key==null*)
    subst i.
    destruct R; subst r; simpl.
    2: solve [apply semax_pre with (P':=FF); try entailer!; try apply semax_ff].
    freeze [0; 1; 3] FR2.
    Time normalize. (*5.7*)
    rename H into InnerRelate.
    rename H0 into OuterRelate.
    unfold hmacstate_PreInitNull.
    Intros s v.
    rename H into Hs.
    unfold hmac_relate_PreInitNull in Hs.
    clear InnerRelate OuterRelate iS oS.
    destruct h1.
    destruct Hs as [IREL [OREL [ILEN [OLEN [ISHA OSHA]]]]].
    destruct s as [mdS [iS oS]].

(* Issue: why is update_reptype not simplifying? *)
     match goal with |- context [@upd_reptype ?cs ?t ?gfs ?x ?v] =>
           change (@upd_reptype cs t gfs x v) with (v,(iS,oS)) end.
     simpl in ISHA, OSHA, IREL, OREL, v |- *.

     Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs))
       as FC_cb by entailer!. (*1.8 versus 3.9*)
     assert (FC_cb_ictx: field_compatible t_struct_hmac_ctx_st [StructField _i_ctx] (Vptr cb cofs)).
     { red in FC_cb. repeat split; try solve [apply FC_cb]. right; left; reflexivity. }
     assert (FC_cb_md: field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] (Vptr cb cofs)).
     { red in FC_cb. repeat split; try solve [apply FC_cb]. left. reflexivity. }

     Time unfold_data_at 1%nat. (*0.8, was slow*)
     rewrite (field_at_data_at _ _ [StructField _i_ctx]).
     (*VST Issue: why does rewrite field_at_data_at at 2 FAIL, but focus_SEP 3; rewrite field_at_data_at at 1. SUCCEED???
        Answer: instead of using "at 2", use the field-specificer in the line above.*)
     rewrite field_address_offset by auto with field_compatible.

     freeze [0; 3] FR3.
     Time forward_call ((wsh, wsh),
             Vptr cb cofs,
             Vptr cb (Ptrofs.add cofs (Ptrofs.repr 108)),
             mkTrep t_struct_SHA256state_st iS,
             @sizeof (@cenv_cs CompSpecs) t_struct_SHA256state_st).
     (*5.9 versus 13*)
     { rewrite sepcon_comm.
       rewrite (field_at_data_at _ _ [StructField _md_ctx]).
       rewrite field_address_offset by auto with field_compatible.
       apply sepcon_derives.
         eapply derives_trans. apply data_at_memory_block. apply derives_refl'. f_equal.
         apply isptr_offset_val_zero; simpl; trivial.
       Time cancel. (*0 versus 2*)
     }

     freeze [0; 1; 2] FR4.
     Time forward. (*return*) (* 3 versus 13*) (*Issue : leaves a somewhat messy subgoal*)
     unfold hmacInit.
     remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
     Time entailer!. (*1.6 versus 7.4*)
     unfold hmacstate_, hmac_relate.
      Exists (iS, (iS, oS)).
      simpl. Time entailer!. (*1.9 versus 5.6*)
     unfold_data_at 1%nat.
     rewrite (field_at_data_at _ _ [StructField _md_ctx]).
     rewrite (field_at_data_at _ _ [StructField _i_ctx]).
      rewrite field_address_offset by auto with field_compatible.
      rewrite field_address_offset by auto with field_compatible.
      simpl; rewrite Ptrofs.add_zero.
      thaw FR4. thaw FR3. thaw FR2.
      change (Tarray tuchar 64 noattr) with (tarray tuchar 64).
      Time cancel. (*1.6 versus 0.7*)
  }

  { (*k is Vptr, key!=NULL*)
    freeze [0;1;3] FR5.
    destruct R as [R | R]; rewrite R; simpl.
    solve [apply semax_pre with (P':=FF); try entailer; try apply semax_ff].
    Intros.
    rename H0 into InnerRelate.
    rename H2 into OuterRelate.
    unfold postResetHMS. simpl.
    freeze [0; 2] FR6.
    Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs)) as FC_cb by entailer!. (*2.8*)
    assert (FC_cb_ictx: field_compatible t_struct_hmac_ctx_st [StructField _i_ctx] (Vptr cb cofs)).
    { red in FC_cb. repeat split; try solve [apply FC_cb]. right; left; reflexivity. }
    assert (FC_cb_md: field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] (Vptr cb cofs)).
    { red in FC_cb. repeat split; try solve [apply FC_cb]. left; reflexivity. }

    unfold_data_at 1%nat.
    freeze [0; 3] FR7.
    rewrite (field_at_data_at _ t_struct_hmac_ctx_st [StructField _i_ctx]).
    rewrite (field_at_data_at _ t_struct_hmac_ctx_st [StructField _md_ctx]).
    rewrite field_address_offset by auto with field_compatible.
    rewrite field_address_offset by auto with field_compatible.
    simpl; rewrite Ptrofs.add_zero.

    Time forward_call ((wsh, wsh),
             Vptr cb cofs,
             Vptr cb (Ptrofs.add cofs (Ptrofs.repr 108)),
             mkTrep t_struct_SHA256state_st iS,
             @sizeof (@cenv_cs CompSpecs) t_struct_SHA256state_st).
    (* 4.7 versus 14.7 *)
    { rewrite sepcon_comm.
      apply sepcon_derives.
          eapply derives_trans. apply data_at_memory_block. apply derives_refl.
          Time cancel. (*0 versus 2*)
    }
    freeze [0; 1; 2] FR8.
    Time forward. (*return*) (*3.4 versus 17*) (*Issue: leaves messy subgoal*)
    Time entailer!. (* 1.2 versus 9*)
    unfold data_block, hmacstate_, hmac_relate.
    Exists (iS, (iS, oS)).
    change (@data_at spec_sha.CompSpecs sh (tarray tuchar (@Zlength byte key)))
       with (@data_at CompSpecs sh (tarray tuchar (@Zlength byte key))).
    change (Tarray tuchar 64 noattr) with (tarray tuchar 64). simpl.
    Time entailer!. (*2.9*)
      unfold s256a_len, innerShaInit, outerShaInit.
           rewrite !Zlength_mkArgZ.
           rewrite mkKey_length. split; reflexivity.
    unfold_data_at 1%nat.
      rewrite (field_at_data_at _ _ [StructField _md_ctx]).
      rewrite (field_at_data_at _ _ [StructField _i_ctx]).
    rewrite field_address_offset by auto with field_compatible.
    rewrite field_address_offset by auto with field_compatible.
    simpl; rewrite Ptrofs.add_zero.
    thaw FR8. thaw FR7. thaw FR6. thaw FR5.
      change (Tarray tuchar 64 noattr) with (tarray tuchar 64).
    Time cancel. (*1.7 versus 1.2 penalty when melting*)
  }
}
}
Time Qed. (*VST 2.0: 10.7s*) 

Lemma body_hmac_init: semax_body HmacVarSpecs HmacFunSpecs
       f_HMAC_Init HMAC_Init_spec.
Proof.
start_function.
apply initbodyproof; auto.
Qed.
