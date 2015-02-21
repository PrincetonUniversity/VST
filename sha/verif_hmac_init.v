Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.spec_hmac.
Require Import vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.

Require Import sha.hmac091c.

Require Import sha.verif_hmac_init_part1.
Require Import sha.verif_hmac_init_part2.

(*
Lemma Tarray_emp_field_compatible b ofs: field_compatible (Tarray tuchar 0 noattr) [] (Vptr b ofs).
        Proof. split; simpl. trivial. split. reflexivity. split. reflexivity.
          split. apply (size_0_compatible (Tarray tuchar 0 noattr) (eq_refl _) (Vptr b ofs)).
          split. apply Z.divide_1_l.
          constructor; simpl; trivial.
        Qed. 
        
Lemma data_Tarray_array_at_emp C b ofs: data_at Tsh (Tarray tuchar 0 noattr) C (Vptr b ofs)
                  = !!field_compatible (Tarray tuchar 0 noattr) [] (Vptr b ofs) && emp.
        Proof.
          rewrite data_at_field_at.
          erewrite field_at_Tarray. 2: reflexivity. 2: apply JMeq.JMeq_refl.
          rewrite array_at_emp; trivial. omega.
        Qed.
*)
Lemma body_hmac_init: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Init HMAC_Init_spec.
Proof.
start_function.
name ctx' _ctx.
name key' _key.
name len' _len.
simpl_stackframe_of.
destruct H as [KL1 [KL2 KL3]]. normalize.
(*Sset _reset (Econst_int (Int.repr 0) tint)*)
forward.

(*unfold data_block.*) normalize. 

(*isolate branch if (key != NULL) *)
apply seq_assoc.

remember (EX  cb : block,
                 (EX  cofs : int,
                  (EX  pad : val,
                   (EX  r : Z,
                    PROP  (c = Vptr cb cofs/\ (r=0 \/ r=1))
                    LOCAL  (`(eq (Vint (Int.repr r))) (eval_id _reset);
                    `(eq pad) (eval_var _pad (tarray tuchar 64));
                    `(eq c) (eval_id _ctx); `(eq k) (eval_id _key);
                    `(eq (Vint (Int.repr l))) (eval_id _len);
                    `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
                    SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                    `(initPostKeyNullConditional r c k h1 key);
                    `(K_vector KV)))))) as PostKeyNull. 
forward_seq. instantiate (1:= PostKeyNull). (*eapply semax_seq.*)
{ assert (DD: Delta = initialized _reset 
               (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs)) by reflexivity.
  rewrite DD; clear DD.
  eapply hmac_init_part1; eassumption.
}
subst PostKeyNull. normalize.
apply extract_exists_pre; intros cb. 
apply extract_exists_pre; intros cofs. 
apply extract_exists_pre; intros pad. 
apply extract_exists_pre; intros r.
normalize. rename H into HC; rewrite HC. rename H0 into R.

(*isolate branch if (reset) *)
apply seq_assoc.

remember (EX iSA:_, EX iS:_, EX oSA:_, EX oS:_,
          PROP  (innerShaInit (map Byte.repr (HP.HMAC_SHA256.mkKey key)) iSA /\ s256_relate iSA iS /\
                 outerShaInit (map Byte.repr (HP.HMAC_SHA256.mkKey key)) oSA /\ s256_relate oSA oS)
                 LOCAL  (
                 `(eq pad) (eval_var _pad (tarray tuchar 64));
                 `(eq (Vptr cb cofs)) (eval_id _ctx);
                 `(eq k) (eval_id _key);
                 `(eq (Vint (Int.repr l))) (eval_id _len);
                 `(eq KV) (eval_var sha._K256 (tarray tuint 64)))

                 SEP  (
                 `(data_at_ Tsh (tarray tuchar 64) pad); (*was:`(array_at_ tuchar Tsh 0 64 pad); *)
                 `(initPostResetConditional r c k h1 key iS oS); `(K_vector KV)))
  as PostResetBranch.
(*forward_seq. instantiate (1:= PostResetBranch).*)
eapply semax_seq. instantiate (1:=PostResetBranch).
{ apply init_part2; assumption. } 
{ (*Continuation after if (reset*)
  subst PostResetBranch.
simpl update_tycon.
apply semax_extensionality_Delta with (Delta). apply expr_lemmas.tycontext_sub_refl.
  apply extract_exists_pre; intros iSA. 
  apply extract_exists_pre; intros iS. 
  apply extract_exists_pre; intros oSA. 
  apply extract_exists_pre; intros oS. unfold initPostResetConditional.
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
     rewrite data_at_isptr. (*NEW, order to extract the knowledge about field_address*)
     normalize.
     
     (*XXX: was: rename H into SCc. rename H0 into ACc. now:*)
     apply isptrD in H. destruct H as [cb' [cofs' PT]]; rewrite PT.
     unfold field_address in PT.
     remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
           (Vptr cb cofs)) as s.
     destruct s. simpl in PT; inversion PT. subst cb' cofs'; clear PT.

     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
     simpl.       
     apply semax_pre with (P':= 
        (PROP (isptr
          (field_address t_struct_hmac_ctx_st [StructField _i_ctx]
             (Vptr cb cofs)))
   LOCAL  (`(eq pad) (eval_var _pad (tarray tuchar 64));
   `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vint i)) (eval_id _key);
   `(eq (Vint (Int.repr l))) (eval_id _len);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] (Vint ii)
        (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _key]
       (map Vint (map Int.repr (HP.HMAC_SHA256.mkKey key))) (Vptr cb cofs));
   `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] oS (Vptr cb cofs));
   `(data_at Tsh
       (nested_field_type2 t_struct_hmac_ctx_st [StructField _i_ctx]) iS
       (field_address t_struct_hmac_ctx_st [StructField _i_ctx]
          (Vptr cb cofs)));
   `(data_at Tsh
       (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx]) v
       (Vptr cb
          (Int.add cofs
             (Int.repr
                (nested_field_offset2 t_struct_hmac_ctx_st
                   [StructField _md_ctx])))));
   `(data_at_ Tsh (tarray tuchar 64) pad); `(K_vector KV)))).
     { entailer. } 
     remember (isptr
      (field_address t_struct_hmac_ctx_st [StructField _i_ctx] (Vptr cb cofs))) as PTR.
     normalize.
     subst PTR. 
     apply isptrD in H. destruct H as [cbI [cIoff CIOff]]. rewrite CIOff in *.
     unfold field_address in CIOff.
     remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
               (Vptr cb cofs)) as s.
     destruct s; simpl in *; inversion CIOff. simpl in *. subst cbI. rewrite CIOff. clear H1.

     (*was:rewrite at_offset'_eq.
     2: simpl; rewrite Int.add_zero; reflexivity.*)
     remember ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS) as  WITNESS.
     forward_call WITNESS.
     { assert (FR: Frame = [
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length] (Vint ii) (Vptr cb cofs)); 
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _key]
               (map Vint (map Int.repr (HP.HMAC_SHA256.mkKey key))) (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] oS (Vptr cb cofs));
          `(data_at_ Tsh (tarray tuchar 64) pad); `(K_vector KV)]).
          subst Frame. reflexivity.
       rewrite FR. clear FR Frame. 
       subst WITNESS. entailer. rewrite CIOff. cancel. 
       unfold field_compatible in f.
       (*inversion CMDOff. subst cmdoff; simpl. clear CMDOff.*) 
       (*unfold nested_field_offset2; simpl. rewrite Int.add_zero.*)
        eapply derives_trans. 
         apply data_at_data_at_. 
         rewrite <- memory_block_data_at_; try reflexivity.
         unfold nested_field_offset2; simpl. trivial.

         unfold nested_field_type2; simpl.
         exploit (align_compatible_nested_field t_struct_hmac_ctx_st [StructField _md_ctx]); try apply f.
         unfold nested_field_offset2; simpl. rewrite Int.add_zero. trivial.
     }
     after_call. subst WITNESS. normalize. subst retval0. simpl. 

     forward. (*return*)
     unfold hmacInit. 
     remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
     apply exp_right with (x:=HMACabs iSha iSha oSha KL key).   
     entailer.
     apply andp_right. 
       apply prop_right. exists iSha, oSha. 
       rewrite Int.unsigned_repr. auto.
       rewrite int_max_signed_eq  in KL2. rewrite int_max_unsigned_eq.
       destruct (zlt 64 (Zlength key)); omega.     
     simpl_stackframe_of. unfold tarray. 
     (*was:rewrite <- data_at__array_at_ with (a:=noattr).
     2: omega. 2: reflexivity.*)
     cancel.
     unfold hmacstate_, hmac_relate.
      remember (if zlt 64 (Zlength key) then Vint (Int.repr 32)
            else Vint (Int.repr (Zlength key))) as kl.
      normalize.
      apply exp_right with
        (x:=(iS, (iS, (oS, (kl, map Vint (map Int.repr (HP.HMAC_SHA256.mkKey key))))))).
      simpl.
      apply andp_right. apply prop_right. repeat split; trivial.
      destruct (zlt 64 (Zlength key)); simpl in *.
         exists (Int.repr 32); eauto.
         rewrite Heqkl, HH1. exists (Int.repr (Int.unsigned ii)).
         rewrite Int.repr_unsigned; eauto.

      unfold_data_at 3%nat. cancel.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]); try reflexivity.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
      unfold field_address. rewrite <- Heqs, <- Heqs0; simpl.
        unfold nested_field_offset2, nested_field_type2; simpl. rewrite Int.add_zero. cancel.
        subst kl. destruct (zlt 64 (Zlength key)); rewrite HH1, Int.repr_unsigned; trivial.
      inversion PT.
  }

  { (*k is Vptr, key!=NULL*)
    destruct R; subst r; simpl. 
    apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
    normalize. 
    unfold postResetHMS. simpl. unfold_data_at 1%nat.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
    normalize.
    (*was:rename H into SCc. rename H0 into ACc.
    rewrite at_offset'_eq.
    2: simpl; rewrite Int.add_zero; reflexivity.*)
    (*now:*) rewrite data_at_isptr. normalize. 
             apply isptrD in H0; destruct H0 as [? [? PT]]. 
             rewrite PT. 
             unfold field_address in PT.
             destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
                  (Vptr cb cofs)); inversion PT. subst x x0; clear PT.

    rename b into kb; rename i into kofs.
    eapply semax_pre with (P':=PROP  ()
      LOCAL  (`(eq pad) (eval_var _pad (tarray tuchar 64));
       `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
       `(eq (Vint (Int.repr l))) (eval_id _len);
       `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
      SEP  (`(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length]
            (if zlt 64 (Zlength key)
            then Vint (Int.repr 32)
            else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] oS (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _key]
              (map Vint (map Int.repr (HP.HMAC_SHA256.mkKey key))) (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] iS (Vptr cb cofs));
          `(data_at_ Tsh (tarray tuchar 64) pad);
          `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
              (Vptr kb kofs));
          `(K_vector KV);
          `(memory_block Tsh (Int.repr (sizeof (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx])))
             (offset_val
                (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _md_ctx]))
             (Vptr cb cofs))))).
    { entailer. cancel.
      (*was:unfold tarray. erewrite data_at__array_at_. 2: omega. 2: reflexivity. 
      cancel.*) (*now:*) unfold nested_field_type2; simpl.
      eapply derives_trans.
        apply data_at_data_at_. (*was: reflexivity. *)
        rewrite <- memory_block_data_at_; try reflexivity. cancel.
        (*new:*) apply f. 
    }
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]); try reflexivity.
    (*normalize. 
    (*now:*) rewrite data_at_isptr. normalize. 
             apply isptrD in H0; destruct H0 as [? [? PT]]. 
             rewrite PT. 
             unfold field_address in PT.
             destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
                  (Vptr cb cofs)); inversion PT. subst x x0; clear PT.*)
    simpl.
    apply semax_pre with (P':= 
        (PROP (isptr
          (field_address t_struct_hmac_ctx_st [StructField _i_ctx]
             (Vptr cb cofs)))
        LOCAL  (`(eq pad) (eval_var _pad (tarray tuchar 64));
          `(eq (Vptr cb cofs)) (eval_id _ctx); `(eq (Vptr kb kofs)) (eval_id _key);
          `(eq (Vint (Int.repr l))) (eval_id _len);
          `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
        SEP 
        (`(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length]
             (if zlt 64 (Zlength key)
              then Vint (Int.repr 32)
              else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
        `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] oS (Vptr cb cofs));
        `(field_at Tsh t_struct_hmac_ctx_st [StructField _key]
            (map Vint (map Int.repr (HP.HMAC_SHA256.mkKey key))) (Vptr cb cofs));
        `(data_at Tsh
            (nested_field_type2 t_struct_hmac_ctx_st [StructField _i_ctx]) iS
            (field_address t_struct_hmac_ctx_st [StructField _i_ctx]
               (Vptr cb cofs))); `(data_at_ Tsh (tarray tuchar 64) pad);
        `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
            (Vptr kb kofs)); `(K_vector KV);
        `(memory_block Tsh (Int.repr 108)
            (Vptr cb (Int.add cofs
                       (Int.repr
                       (nested_field_offset2 t_struct_hmac_ctx_st [StructField _md_ctx])))))))).
     { entailer. }
     remember (isptr
      (field_address t_struct_hmac_ctx_st [StructField _i_ctx] (Vptr cb cofs))) as PTR.
     normalize.
     subst PTR. 
     apply isptrD in H0. destruct H0 as [cbI [cIoff CIOff]]. rewrite CIOff in *.
     unfold field_address in CIOff.
     remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
               (Vptr cb cofs)) as s.
     destruct s; simpl in *; inversion CIOff. simpl in *. subst cbI. rewrite CIOff. clear H2.

    remember ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS) as  WITNESS.
    forward_call WITNESS.
    { assert (FR: Frame = [
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _key_length]
            (if zlt 64 (Zlength key)
             then Vint (Int.repr 32)
             else Vint (Int.repr (Zlength key))) (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] oS (Vptr cb cofs));
         `(field_at Tsh t_struct_hmac_ctx_st [StructField _key]
            (map Vint (map Int.repr (HP.HMAC_SHA256.mkKey key))) (Vptr cb cofs));
         `(data_at_ Tsh (tarray tuchar 64) pad);
         `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
            (Vptr kb kofs)); `(K_vector KV)]).
        subst Frame. reflexivity.
      rewrite FR. clear FR Frame. 
      subst WITNESS. entailer. cancel. rewrite CIOff. unfold  nested_field_type2; simpl. cancel.
    }
    after_call. subst WITNESS. normalize.  subst retval0. simpl. 

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
      (x:=(iS, (iS, (oS, (kl, map Vint (map Int.repr (HP.HMAC_SHA256.mkKey key))))))).
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

    unfold_data_at 3%nat. cancel.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]); try reflexivity.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]); try reflexivity.
    (*new:*) unfold field_address; simpl. rewrite <- Heqs. (*
             destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
                  (Vptr cb cofs)); try contradiction.*)
             destruct (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
                  (Vptr cb cofs)); try contradiction. 
             unfold nested_field_offset2; simpl. rewrite Int.add_zero.
             unfold nested_field_type2; simpl. cancel.
  }
} 
Qed.
