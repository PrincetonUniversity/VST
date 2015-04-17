Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.spec_hmac.
Require Import vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.

Require Import sha.hmac091c.

Require Import sha.verif_hmac_init_part1.
Require Import sha.verif_hmac_init_part2.

Lemma body_hmac_init: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Init HMAC_Init_spec.
Proof.
start_function.
name ctx' _ctx.
name key' _key.
name len' _len.
simpl_stackframe_of. fixup_local_var; intro pad.

destruct H as [KL1 [KL2 KL3]]. normalize.

(*Sset _reset (Econst_int (Int.repr 0) tint)*)
forward v. clear v. (*TODO: if we don't do the remember_value (eval_lvar _pad above, 
   we can't clear v here, although it's actually NOT used in the conclusion (contrary to what's claimed by the tactic.
   I suspect it's some binding issue*)

normalize. 

(*isolate branch if (key != NULL) *)
apply seq_assoc.

remember (EX  cb : block,
                 (EX  cofs : int,
                   (EX  r : Z,
                    PROP  (c = Vptr cb cofs /\ (r=0 \/ r=1))
                    LOCAL  (temp _reset (Vint (Int.repr r));
                      lvar _pad (tarray tuchar 64) pad; temp _ctx c; temp _key k;
                      temp _len (Vint (Int.repr l));
                      gvar sha._K256 kv)
                    SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                    `(initPostKeyNullConditional r c k h1 key);
                    `(K_vector kv))))) as PostKeyNull. 
forward_seq. instantiate (1:= PostKeyNull).  
{ eapply hmac_init_part1; eassumption. }
subst PostKeyNull. normalize.
apply extract_exists_pre; intros cb. 
apply extract_exists_pre; intros cofs. 
apply extract_exists_pre; intros r.
normalize. rename H into HC; rewrite HC. rename H0 into R.

(*isolate branch if (reset) *)
apply seq_assoc.
remember (EX shaStates:_ ,
                        PROP 
                        (innerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                           (fst shaStates) /\
                         s256_relate (fst shaStates) (fst (snd shaStates)) /\
                         outerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                           (fst (snd (snd shaStates))) /\ s256_relate (fst (snd (snd shaStates))) (snd (snd (snd shaStates))))
                        LOCAL  (lvar _pad (tarray tuchar 64) pad; 
                                temp _ctx (Vptr cb cofs); temp _key k;
                                temp _len (Vint (Int.repr l));
                                gvar sha._K256 kv)
                        SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                        `(initPostResetConditional r c k h1 key (fst (snd shaStates)) (snd (snd (snd shaStates))));
                        `(K_vector kv)))
  as PostResetBranch.
  eapply semax_seq. instantiate (1:=PostResetBranch).
  { eapply init_part2; eassumption. }

{ (*Continuation after if (reset*)
  subst PostResetBranch.
  simpl update_tycon.
  apply semax_extensionality_Delta with Delta. apply expr_lemmas.tycontext_sub_refl.
  apply extract_exists_pre; intros [iSA [iS [oSA oS]]]. 
  (*  apply extract_exists_pre; intros iS. 
  apply extract_exists_pre; intros oSA. 
  apply extract_exists_pre; intros oS.*) unfold initPostResetConditional.
  normalize. 
  rename H into INNER. rename H0 into InnerRelate.
  rename H1 into OUTER. rename H2 into OuterRelate.
  unfold initPostResetConditional; rewrite HC.
  destruct k;
    try solve [apply semax_pre with (P':=FF); try entailer; try apply semax_ff].
  { (*k is integer, ie key==null*)
     destruct (Int.eq i Int.zero). 
     Focus 2. apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
     destruct R; subst r; simpl.
     Focus 2. apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
     unfold hmacstate_PreInitNull; simpl. normalize.
     intros s. normalize. intros v. normalize. rename H into Hs.
     unfold hmac_relate_PreInitNull in Hs. 
     clear INNER InnerRelate OUTER OuterRelate iSA iS oSA oS.
     destruct h1.
     destruct Hs as [XX [IREL [OREL [ILEN [OLEN [KK [ii [KLii [KL [HH1 [HH2 HH3]]]]]]]]]]].
     subst key0. destruct s as [mdS [iS [oS [kl K]]]]. simpl in *. subst kl K.
     unfold_data_at 1%nat.

     (* eapply semax_seq'.
     frame_SEP 3 4.*)
     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
     assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _md_ctx]
          (Vptr cb cofs))). entailer. 
     apply isptrD in H. destruct H as [cb' [cofs' PT]]; rewrite PT.
     unfold field_address in PT.
     remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
           (Vptr cb cofs)) as s.
     destruct s. simpl in PT; inversion PT. subst cb' cofs'; clear PT.

     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
     assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _i_ctx]
          (Vptr cb cofs))). entailer. 
     apply isptrD in H. destruct H as [cbI [cIoff CIOff]]. rewrite CIOff in *.
     unfold field_address in CIOff.
     remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
               (Vptr cb cofs)) as s.
     destruct s; simpl in *; inversion CIOff. simpl in *. subst cbI. rewrite CIOff. clear H1.

     simpl.
     forward_call' (((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS)) rv.
     { simpl. rewrite CIOff.
       change (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx])
             with  t_struct_SHA256state_st.
       change (nested_field_offset2 t_struct_hmac_ctx_st [StructField _md_ctx])
               with 0%Z.
       normalize. cancel.
     }
     subst rv. simpl.

     forward. (*return*)
     unfold hmacInit. 
     remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
     apply exp_right with (x:=HMACabs iSha iSha oSha KL key). 
     simpl_stackframe_of. 
     entailer!.
       exists iSha, oSha. 
       rewrite Int.unsigned_repr. auto.
       rewrite int_max_signed_eq  in KL2. rewrite int_max_unsigned_eq.
       destruct (zlt 64 (Zlength key)); omega.     
     rewrite (lvar_eval_lvar _ _ _ _ H0).
     simpl sizeof.
     entailer!.
     unfold hmacstate_, hmac_relate.
      remember (if zlt 64 (Zlength key) then Vint (Int.repr 32)
            else Vint (Int.repr (Zlength key))) as kl.
      apply exp_right with
        (x:=(iS, (iS, (oS, (kl, map Vint (map Int.repr (HMAC_SHA256.mkKey key))))))).
      simpl.
      entailer!.
         destruct (zlt 64 (Zlength key)); simpl in *.
         exists (Int.repr 32); eauto.
         rewrite HH1. exists (Int.repr (Int.unsigned ii)).
         rewrite Int.repr_unsigned; eauto.

      unfold_data_at 3%nat. cancel.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]) by reflexivity.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]) by reflexivity.
      unfold field_address. repeat rewrite if_true by auto.
      unfold nested_field_offset2, nested_field_type2; simpl. rewrite Int.add_zero. cancel.
      destruct (zlt 64 (Zlength key)); rewrite HH1, Int.repr_unsigned; trivial.
    inversion PT.
  }

  { (*k is Vptr, key!=NULL*)
    destruct R; subst r; simpl. 
    { apply semax_pre with (P':=FF); try entailer; try apply semax_ff. }
    normalize. rename H into isbyteKey. 
    unfold postResetHMS. simpl. unfold_data_at 1%nat.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
    rename b into kb; rename i into kofs.
    replace_SEP 4 
      (`(memory_block Tsh (Int.repr (sizeof (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx])))
           (field_address t_struct_hmac_ctx_st [StructField _md_ctx] (Vptr cb cofs)))).
       entailer!.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]); try reflexivity.

    (*Call to _memcpy*)
    forward_call' ((Tsh, Tsh),
             Vptr cb cofs,
             field_address t_struct_hmac_ctx_st [StructField _i_ctx]  (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS) rv.
       entailer!; unfold field_address; rewrite if_true by auto; reflexivity.
       {simpl. unfold field_address.
        destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
            (Vptr cb cofs)); [ | solve [entailer]].
        unfold nested_field_offset2. simpl Int.repr. normalize.
        cancel.
       }
    subst rv; simpl. 

    forward. (*return*)
    remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
    apply exp_right with (x:=HMACabs iSA iSA oSA KL key). 
    entailer.
    apply andp_right. 
      apply prop_right. unfold hmacInit. exists iSA, oSA.
      rewrite Int.unsigned_repr. auto.
      rewrite int_max_signed_eq  in KL2. rewrite int_max_unsigned_eq.
      destruct (zlt 64 (Zlength key)); omega.    
    unfold data_block. simpl_stackframe_of. entailer. cancel.
    unfold hmacstate_, hmac_relate.
    remember (if zlt 64 (Zlength key) then Vint (Int.repr 32)
              else Vint (Int.repr (Zlength key))) as kl.
    normalize.
    apply exp_right with
      (x:=(iS, (iS, (oS, (kl, map Vint (map Int.repr (HMAC_SHA256.mkKey key))))))).
    simpl. entailer.
    apply andp_right. apply prop_right.
      split. rewrite (updAbs_len _ _ _ INNER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.
      split. rewrite (updAbs_len _ _ _ OUTER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.
      exists (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)).
      rewrite Int.unsigned_repr. 
      split. destruct (zlt 64 (Zlength key)); trivial.
      split; trivial.
      rewrite int_max_signed_eq  in KL2. rewrite int_max_unsigned_eq.
      destruct (zlt 64 (Zlength key)); omega.

    (*TODO: this line is new - maybe it can be put into automation?*) rewrite (lvar_eval_lvar _ _ _ _ H0).
    unfold_data_at 3%nat. 
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]) by reflexivity.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]) by reflexivity.
    change (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx])
              with sha.t_struct_SHA256state_st.
    change (nested_field_type2 t_struct_hmac_ctx_st [StructField _i_ctx])
              with sha.t_struct_SHA256state_st.
   cancel.
    unfold field_address; rewrite if_true by auto.
   change (nested_field_offset2 t_struct_hmac_ctx_st [StructField _md_ctx])
           with 0.
   normalize.
  }
} 
Qed.
