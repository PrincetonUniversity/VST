Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.spec_hmacNK.
Require Import vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.

Require Import sha.hmac_NK.

Require Import sha.verif_hmacNK_init_part1. 
Require Import sha.verif_hmacNK_init_part2.

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
simpl_stackframe_of. fixup_local_var; intro pad. fixup_local_var; intro ctxkey. 

destruct H as [KL1 [KL2 KL3]]. 
forward.
 
assert_PROP (isptr ctxkey). { entailer. }
apply isptrD in H; destruct H as [ckb [ckoff X]]; subst ctxkey.

(*isolate branch if (key != NULL) *)
apply seq_assoc.
(*from init_part1:
Definition initPostKeyNullConditional r (c:val) (k: val) h key ctxkey: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 
                   then (hmacstate_PreInitNull key h c) * (data_at_ Tsh (tarray tuchar 64) ctxkey)
                   else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF 
                  else !!(Forall isbyteZ key) &&
                    ((data_at Tsh t_struct_hmac_ctx_st keyedHMS c) *
                     (data_at Tsh (tarray tuchar 64) (map Vint (map Int.repr (HMAC_SHA256.mkKey key)))
                      ctxkey)  *
                     (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key))
                      (Vptr b ofs)))
  | _ => FF
  end.*)
remember (EX  cb : block,
                 (EX  cofs : int,
                   (EX  r : Z, 
                    PROP  (c = Vptr cb cofs /\ (r=0 \/ r=1))
                    LOCAL  (temp _reset (Vint (Int.repr r));
                      lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); 
                      lvar _pad (tarray tuchar 64) pad;
                      temp _ctx c; temp _key k; temp _len (Vint (Int.repr l));
                      gvar sha._K256 kv)
                    SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                    `(initPostKeyNullConditional r c k h1 key (Vptr ckb ckoff));
                    `(K_vector kv))))) as PostKeyNull. 
forward_seq. instantiate (1:= PostKeyNull). 
{  assert (DD: Delta= initialized _reset Delta) by reflexivity.
   rewrite DD.  
   eapply semax_pre_simple.
   2: eapply hmac_init_part1; eassumption.
   entailer.
}
subst PostKeyNull. normalize.
apply extract_exists_pre; intros cb. 
apply extract_exists_pre; intros cofs. 
apply extract_exists_pre; intros r.
normalize. unfold POSTCONDITION, abbreviate. subst c.
 (*rename H into HC; rewrite HC.*) rename H0 into R.

(*isolate branch if (reset) *)
apply seq_assoc.
(*from init_part2:
Definition postResetHMS (iS oS: s256state): hmacstate :=
  (emptySha, (iS, oS)).

Definition initPostResetConditional r (c:val) (k: val) h key iS oS: mpred:=
  match k with
    Vint z => if Int.eq z Int.zero
              then if zeq r Z0 then hmacstate_PreInitNull key h c else FF
              else FF
  | Vptr b ofs => if zeq r 0 then FF
                  else !!(Forall isbyteZ key) &&
                       ((data_at Tsh t_struct_hmac_ctx_st (postResetHMS iS oS) c) *
                        (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr b ofs)))
  | _ => FF
  end.*)
remember (EX shaStates:_ ,
          PROP  (innerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                           (fst shaStates) /\
                  s256_relate (fst shaStates) (fst (snd shaStates)) /\
                  outerShaInit (map Byte.repr (HMAC_SHA256.mkKey key))
                           (fst (snd (snd shaStates))) /\ 
                  s256_relate (fst (snd (snd shaStates))) (snd (snd (snd shaStates))))
          LOCAL  (lvar _pad (tarray tuchar 64) pad; 
                  lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); 
                  temp _ctx (Vptr cb cofs); temp _key k;
                  temp _len (Vint (Int.repr l));
                  gvar sha._K256 kv)
          SEP  (`(data_at_ Tsh (tarray tuchar 64) pad);
                `(data_at_ Tsh (Tarray tuchar 64 noattr) (Vptr ckb ckoff)); 
                `(initPostResetConditional r (Vptr cb cofs) k h1 key (fst (snd shaStates)) (snd (snd (snd shaStates))));
                `(K_vector kv)))
  as PostResetBranch.
(*forward_seq. instantiate (1:= PostResetBranch).*)
eapply semax_seq. instantiate (1:=PostResetBranch).
{  apply init_part2; assumption. }

{ (*Continuation after if (reset*)
  subst PostResetBranch.
  simpl update_tycon.
  apply semax_extensionality_Delta with (Delta). apply expr_lemmas.tycontext_sub_refl.
  apply extract_exists_pre; intros [iSA [iS [oSA oS]]]. 
(*  apply extract_exists_pre; intros iSA. 
  apply extract_exists_pre; intros iS. 
  apply extract_exists_pre; intros oSA. 
  apply extract_exists_pre; intros oS.*) unfold initPostResetConditional.
  normalize. 
  rename H into INNER. rename H0 into InnerRelate.
  rename H1 into OUTER. rename H2 into OuterRelate.
  unfold initPostResetConditional.
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
     destruct Hs as [IREL [OREL [ILEN [OLEN [ISHA OSHA]]]]].
     destruct s as [mdS [iS oS]]. simpl in *.
     unfold_data_at 1%nat.

     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]).
     simpl.       
     rewrite (data_at_isptr Tsh
       (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx])).
     normalize. 
     apply isptrD in H. destruct H as [cbmd [cmdoff CMDOff]]. rewrite CMDOff in *.
     unfold field_address in CMDOff.
     remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
               (Vptr cb cofs)) as s.
     destruct s; simpl in *; inversion CMDOff. simpl in *. subst cbmd. rewrite CMDOff. clear H1.
     rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
     simpl.       
     assert_PROP (isptr
          (field_address t_struct_hmac_ctx_st [StructField _i_ctx]
             (Vptr cb cofs))).
     { entailer. } 
     apply isptrD in H. destruct H as [cbI [cIoff CIOff]]. rewrite CIOff in *.
     unfold field_address in CIOff.
     remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
               (Vptr cb cofs)) as s.
     destruct s; simpl in *; inversion CIOff. simpl in *. subst cbI. rewrite CIOff. clear H1.

     simpl.
     forward_call' ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS) rv.
     { assert (FR: Frame = [
          (field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] oS (Vptr cb cofs));
          (data_at_ Tsh (tarray tuchar 64) (Vptr ckb ckoff));
          (data_at_ Tsh (tarray tuchar 64) pad); (K_vector kv)]).
          subst Frame; reflexivity.
       rewrite FR; clear FR Frame. 
       entailer. cancel. simpl.
       apply sepcon_derives. simpl. rewrite CIOff. cancel.
       unfold field_compatible in f.
       inversion CMDOff. subst cmdoff; simpl. clear CMDOff. (* unfold nested_field_offset2; simpl. rewrite Int.add_zero.*)
        eapply derives_trans. 
         apply data_at_data_at_. 
         rewrite <- memory_block_data_at_; try reflexivity.
         unfold nested_field_offset2; simpl. rewrite Int.add_zero. trivial.

         exploit (align_compatible_nested_field t_struct_hmac_ctx_st [StructField _md_ctx]); try apply f.
         simpl. trivial.
     }
     subst rv. simpl.

     forward. (*return*)
     unfold hmacInit. 
     remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
     apply exp_right with (x:=HMACabs iSha iSha oSha).   
     entailer.
     apply andp_right. 
       apply prop_right. exists iSha, oSha. auto. 
     simpl_stackframe_of. unfold tarray.
     cancel.
     unfold hmacstate_, hmac_relate.
      normalize.
      apply exp_right with (x:=(iS, (iS, oS))).
      simpl. entailer. cancel.

      unfold_data_at 3%nat. cancel.
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
      rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]).
      unfold field_address. rewrite <- Heqs, <- Heqs0; simpl.
        unfold nested_field_offset2, nested_field_type2; simpl. rewrite Int.add_zero. 
      unfold tarray in *. rewrite (lvar_eval_lvar _ _ _ _ H0). 
      rewrite (lvar_eval_lvar _ _ _ _ H1). cancel.
  }

  { (*k is Vptr, key!=NULL*)
    destruct R; subst r; simpl. 
    apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
    normalize. rename H into isbyteKey. 
    unfold postResetHMS. simpl. unfold_data_at 1%nat.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]).
    simpl.
    assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _md_ctx]
            (Vptr cb cofs))).
    { entailer. }
    apply isptrD in H; destruct H as [? [? PT]]. 
    rewrite PT; unfold field_address in PT.
    remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _md_ctx]
                  (Vptr cb cofs)) as s.
    destruct s; inversion PT; clear PT. subst x x0.

    rename b into kb; rename i into kofs.
    eapply semax_pre with (P':=PROP  ()
      LOCAL  (lvar _pad (tarray tuchar 64) pad;
        lvar _ctx_key (tarray tuchar 64) (Vptr ckb ckoff); temp _ctx (Vptr cb cofs);
        temp _key (Vptr kb kofs); temp _len (Vint (Int.repr l));
        gvar sha._K256 kv)
      SEP  (
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] oS (Vptr cb cofs));
          `(field_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx] iS (Vptr cb cofs));
          `(data_at_ Tsh (tarray tuchar 64) pad);
          `(data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr kb kofs));
          `(data_at_ Tsh (tarray tuchar 64) (Vptr ckb ckoff)); `(K_vector kv);
          `(memory_block Tsh (Int.repr (sizeof (nested_field_type2 t_struct_hmac_ctx_st [StructField _md_ctx])))
             (offset_val
                (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _md_ctx]))
             (Vptr cb cofs))))).
    { entailer. cancel.
      unfold field_compatible in f.
        eapply derives_trans. 
         apply data_at_data_at_. 
         rewrite <- memory_block_data_at_; try reflexivity.
         unfold nested_field_offset2; simpl. trivial.

         exploit (align_compatible_nested_field t_struct_hmac_ctx_st [StructField _md_ctx]); try apply f.
         unfold nested_field_offset2; simpl. rewrite Int.add_zero. trivial.
    }
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    assert_PROP (isptr (field_address t_struct_hmac_ctx_st [StructField _i_ctx] (Vptr cb cofs))).
      entailer!.
    apply isptrD in H; destruct H as [cbI [cIoff CIOff]]. rewrite CIOff in *.
    unfold field_address in CIOff.
    remember (field_compatible_dec t_struct_hmac_ctx_st [StructField _i_ctx]
               (Vptr cb cofs)) as s.
    destruct s; simpl in *; inversion CIOff. simpl in *. subst cbI. rewrite CIOff. clear H1.

    forward_call' ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS) rv.
    { assert (FR: Frame = [
         (field_at Tsh t_struct_hmac_ctx_st [StructField _o_ctx] oS (Vptr cb cofs));
         (data_at_ Tsh (tarray tuchar 64) (Vptr ckb ckoff));
         (data_at_ Tsh (tarray tuchar 64) pad);
         (data_at Tsh (tarray tuchar (Zlength key)) (map Vint (map Int.repr key)) (Vptr kb kofs));
         (K_vector kv)]).
        subst Frame; reflexivity.
      rewrite FR; clear FR Frame. 
      entailer. simpl. rewrite CIOff. unfold  nested_field_type2; simpl. cancel.
    }
    subst rv; simpl. 

    forward. (*return*)
    apply exp_right with (x:=HMACabs iSA iSA oSA). 
    entailer.
    apply andp_right. 
      apply prop_right. unfold hmacInit. exists iSA, oSA. auto.
    unfold data_block. simpl_stackframe_of. entailer. cancel.
    unfold hmacstate_, hmac_relate.
    normalize.
    apply exp_right with (x:=(iS, (iS, oS))).
    simpl. entailer.
    apply andp_right. apply prop_right.
      split. rewrite (updAbs_len _ _ _ INNER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.
      rewrite (updAbs_len _ _ _ OUTER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.

    unfold_data_at 3%nat. cancel.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]).
    unfold field_address. rewrite <- Heqs, <- Heqs0. unfold nested_field_type2; simpl.
    inversion CIOff. rewrite H4. unfold nested_field_offset2 in H4; simpl in H4.
      unfold tarray in *. rewrite (lvar_eval_lvar _ _ _ _ H0). 
      rewrite (lvar_eval_lvar _ _ _ _ H1). cancel.
    
    unfold nested_field_offset2; simpl. rewrite Int.add_zero. cancel.
  }
} 
Qed.