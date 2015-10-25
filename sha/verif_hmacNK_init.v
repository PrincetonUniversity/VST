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

Lemma body_hmac_init: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Init HMAC_Init_spec.
Proof.
start_function.
name ctx' _ctx.
name key' _key.
name len' _len.
rename lvar0 into pad. rename lvar1 into ctxkey.

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
   entailer. cancel.
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
  (default_val t_struct_SHA256state_st, (iS, oS)).
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
{ eapply semax_pre_post.
  Focus 3 . apply init_part2; eassumption.
  entailer.
  intros ? ?. apply andp_left2. entailer. }

{ (*Continuation after if (reset*)
  subst PostResetBranch.
  simpl update_tycon.
  apply semax_extensionality_Delta with (Delta). 
  apply tycontext_sub_refl.
  apply extract_exists_pre; intros [iSA [iS [oSA oS]]]. 
  unfold initPostResetConditional.
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

     assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs)) as FC_cb by entailer.
     assert (FC_cb_ictx: field_compatible t_struct_hmac_ctx_st [StructField 14%positive] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. right; left. reflexivity.
     assert (FC_cb_md: field_compatible t_struct_hmac_ctx_st [StructField 13%positive] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. left. reflexivity.

     unfold data_at at 1.
     unfold_field_at 1%nat. (*Issue: Why is this so slow here (2mins)*)
     normalize. 
     (*rewrite field_at_data_at at 2. *)
     (*VST Issue: why does rewrite field_at_data_at at 2 FAIL, but focus_SEP 1. rewrite field_at_data_at at 1. SUCCEED???*)
     focus_SEP 1. rewrite field_at_data_at at 1. 
     unfold field_address. rewrite if_true; trivial.

     forward_call ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS, 
             @sizeof (@cenv_cs CompSpecs) t_struct_SHA256state_st) rv.
     { rewrite field_at_data_at at 1. 
       unfold field_address; simpl. rewrite if_true, Int.add_zero; trivial.
       repeat rewrite sepcon_assoc.
       apply sepcon_derives.
          eapply derives_trans. apply data_at_memory_block. apply derives_refl.
          cancel.
     }
     subst rv. simpl.

     forward. (*return*)
     Exists (Vptr ckb ckoff). normalize.
     Exists pad. normalize.
     unfold hmacInit. 
     remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
     Exists (HMACabs iSha iSha oSha).   
     entailer!. exists iSha, oSha. auto.
     unfold hmacstate_, hmac_relate.
      Exists (iS, (iS, oS)).
      simpl. entailer!.

      unfold data_at at 3. unfold_field_at 2%nat. entailer!.
      do 2 rewrite field_at_data_at.
      unfold field_address; simpl. rewrite if_true; trivial. rewrite if_true; trivial.
      rewrite Int.add_zero. cancel.
  }

  { (*k is Vptr, key!=NULL*)
    destruct R; subst r; simpl. 
    apply semax_pre with (P':=FF); try entailer; try apply semax_ff.
    normalize. rename H into isbyteKey. 
    unfold postResetHMS. simpl.
     assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs)) as FC_cb by entailer.
     assert (FC_cb_ictx: field_compatible t_struct_hmac_ctx_st [StructField 14%positive] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. right; left. reflexivity.
     assert (FC_cb_md: field_compatible t_struct_hmac_ctx_st [StructField 13%positive] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. left. reflexivity.

    unfold data_at at 1. unfold_field_at 1%nat. normalize.
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]).

    forward_call ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset2 t_struct_hmac_ctx_st [StructField _i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS,
             @sizeof (@cenv_cs CompSpecs) t_struct_SHA256state_st) rv.
    { simpl. rewrite field_at_data_at at 1. 
       unfold field_address; simpl. rewrite if_true; trivial. rewrite if_true; trivial. rewrite Int.add_zero.
       repeat rewrite sepcon_assoc. rewrite sepcon_comm. repeat rewrite sepcon_assoc. 
       apply sepcon_derives.
          eapply derives_refl.
       repeat rewrite <- sepcon_assoc. rewrite sepcon_comm. 
       apply sepcon_derives.
          eapply derives_trans. apply data_at_memory_block. apply derives_refl.
          cancel.
    }
    simpl.
    forward. (*return*)
     Exists (Vptr ckb ckoff). normalize.
     Exists pad. normalize.
    Exists (HMACabs iSA iSA oSA). 
    entailer!.
      exists iSA, oSA. auto.
    unfold data_block, hmacstate_, hmac_relate.
    normalize.
    Exists (iS, (iS, oS)).
    entailer!.
      split. rewrite (updAbs_len _ _ _ INNER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.
      rewrite (updAbs_len _ _ _ OUTER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.

      unfold data_at at 3. unfold_field_at 2%nat. entailer!.
      do 2 rewrite field_at_data_at.
      unfold field_address; simpl. rewrite if_true; trivial. rewrite if_true; trivial.
      rewrite Int.add_zero. cancel.
  }
} 
Qed.
