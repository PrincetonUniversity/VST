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
Time forward. (*1.3*)
 
Time assert_PROP (isptr ctxkey) as Pckey by entailer!. (*0.7*) 
apply isptrD in Pckey; destruct Pckey as [ckb [ckoff X]]; subst ctxkey.

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
   entailer!.
}
subst PostKeyNull.
Intros cb cofs r.
Time normalize. (*2.3*)
unfold POSTCONDITION, abbreviate. subst c.
rename H0 into R.

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
eapply semax_seq. instantiate (1:=PostResetBranch).
{ eapply semax_pre_post.
  Focus 3 . apply init_part2; eassumption.
  entailer!.
  intros ? ?. apply andp_left2. entailer!. }

{ (*Continuation after if (reset*)
  subst PostResetBranch.
  simpl update_tycon.
  apply semax_extensionality_Delta with (Delta). 
  apply tycontext_sub_refl.
  apply extract_exists_pre; intros [iSA [iS [oSA oS]]]. simpl. 
  assert_PROP (is_pointer_or_null k) as Ptr_null_k by entailer!.
  destruct k; simpl in Ptr_null_k; try contradiction.
  { (*Case key==null*) 
    subst i.
    destruct R; subst r; simpl.
    2: solve [apply semax_pre with (P':=FF); try entailer!; try apply semax_ff].
    Time normalize. (*5.7*)
    rename H into INNER. rename H0 into InnerRelate.
    rename H1 into OUTER. rename H2 into OuterRelate.
    unfold hmacstate_PreInitNull; simpl.
    Intros s v.
    apply semax_pre with (P':= PROP (hmac_relate_PreInitNull key h1 s)
      LOCAL  (@lvar CompSpecs _pad (tarray tuchar 64) pad;
              @lvar CompSpecs _ctx_key (tarray tuchar 64) (Vptr ckb ckoff);
              temp _ctx (Vptr cb cofs); temp _key (Vint Int.zero);
              temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
      SEP  (`(@data_at_ CompSpecs Tsh (tarray tuchar 64) pad);
            `(@data_at_ CompSpecs Tsh (Tarray tuchar 64 noattr) (Vptr ckb ckoff));
            `(@data_at CompSpecs Tsh t_struct_hmac_ctx_st
                (@upd_reptype CompSpecs t_struct_hmac_ctx_st [StructField _md_ctx] s v)
                (Vptr cb cofs));
            `(K_vector kv))). 
    { Time entailer!. (*8*) }
    Time normalize. (*15.7 SLOW - -should become more wefficient when in next round of extarct_prop Issue*) 
    rename H into Hs.
    clear INNER InnerRelate OUTER OuterRelate iSA iS oSA oS.
    destruct h1.
    destruct Hs as [IREL [OREL [ILEN [OLEN [ISHA OSHA]]]]].
    destruct s as [mdS [iS oS]].

(* Issue: why is update_reptype not simplifying? *)
    match goal with |- context [@upd_reptype ?cs ?t ?gfs ?x ?v] => 
          change (@upd_reptype cs t gfs x v) with (v,(iS,oS)) end.
     
    Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs))
        as FC_cb by entailer!. (*4*)
    assert (FC_cb_ictx: field_compatible t_struct_hmac_ctx_st [StructField _i_ctx] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. right; left. reflexivity.
    assert (FC_cb_md: field_compatible t_struct_hmac_ctx_st [StructField _md_ctx] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. left. reflexivity.

    Time unfold_data_at 1%nat. (*0.8, was slow*)
    rewrite (field_at_data_at _ _ [StructField _i_ctx]).
     (*VST Issue: why does rewrite field_at_data_at at 2 FAIL, but focus_SEP 1. rewrite field_at_data_at at 1. SUCCEED???
       Answer: instead of using "at 2", use the field-specificer in the line above.*)
     unfold field_address. rewrite if_true by trivial.
     simpl @nested_field_type.
      
    Time forward_call ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset t_struct_hmac_ctx_st [StructField _i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS, 
             @sizeof (@cenv_cs CompSpecs) t_struct_SHA256state_st) rv.
     (* 13 secs*)
     { rewrite (field_at_data_at _ _ [StructField _md_ctx]).
       unfold field_address; simpl. rewrite if_true by auto; rewrite Int.add_zero.
       change 108 with (sizeof cenv_cs t_struct_SHA256state_st).
       rewrite memory_block_data_at_ .
       change (Tstruct _SHA256state_st noattr) with t_struct_SHA256state_st.
       (* cancel.  Issue: doesn't work, for some reason. *)
       pull_left (data_at Tsh t_struct_SHA256state_st v (Vptr cb cofs)).
       rewrite !sepcon_assoc. apply sepcon_derives; [ | cancel].
       apply data_at_data_at_.
       clear - FC_cb; hnf in FC_cb|-*; intuition.
       red in H4|-*. simpl in H4|-*. omega.
     }
     subst rv. simpl.

     Time forward. (*return*) (*14 secs SLOW, and leaves a somewhat messy subgoal (Issue)*)
     Exists (Vptr ckb ckoff) pad (HMACabs iSha iSha oSha). 
     unfold hmacInit. 
     remember (Int.unsigned (Int.repr (if zlt 64 (Zlength key) then 32 else Zlength key)))as KL.
     Time entailer!. (*7.4*)
     exists iSha, oSha. auto.
     unfold hmacstate_, hmac_relate.
      Exists (iS, (iS, oS)).
      simpl. Time entailer!. (*5.8*)

      unfold_data_at 3%nat.
      rewrite (field_at_data_at _ _ [StructField _md_ctx]).
      rewrite (field_at_data_at _ _ [StructField _i_ctx]).
      unfold field_address; simpl. rewrite if_true by trivial. rewrite if_true by trivial.
      rewrite Int.add_zero. 
      change (Tarray tuchar 64 noattr) with (tarray tuchar 64).
      Time cancel. (*1*)
  }

  { (*k is Vptr, key!=NULL*)
    destruct R; subst r; simpl. 
    solve [apply semax_pre with (P':=FF); try entailer; try apply semax_ff].
    Time normalize. (*15.3 SLOW*) 
    rename H into INNER. rename H0 into InnerRelate.
    rename H1 into OUTER. rename H2 into OuterRelate. rename H3 into isbyteKey. 
    unfold postResetHMS. simpl.
     assert_PROP (field_compatible t_struct_hmac_ctx_st [] (Vptr cb cofs)) as FC_cb by entailer!.
     assert (FC_cb_ictx: field_compatible t_struct_hmac_ctx_st [StructField 14%positive] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. right; left. reflexivity.
    assert (FC_cb_md: field_compatible t_struct_hmac_ctx_st [StructField 13%positive] (Vptr cb cofs)).
       red; red in FC_cb. intuition. split; trivial. left. reflexivity.

    unfold_data_at 1%nat. 
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _md_ctx]).
    rewrite (field_at_data_at Tsh t_struct_hmac_ctx_st [StructField _i_ctx]).
    unfold field_address. rewrite if_true by trivial. rewrite if_true by trivial. simpl. rewrite Int.add_zero.
   
    Time forward_call ((Tsh, Tsh),
             Vptr cb cofs,
             offset_val
              (Int.repr (nested_field_offset t_struct_hmac_ctx_st [StructField _i_ctx]))
              (Vptr cb cofs),
             mkTrep t_struct_SHA256state_st iS,
             @sizeof (@cenv_cs CompSpecs) t_struct_SHA256state_st) rv.
    (* 18 - SLOW -- maybe can spead up by doing some of the stuff in the proof of the SC prior to the call?*)
    { simpl. 
      change 108 with (sizeof cenv_cs t_struct_SHA256state_st).
      rewrite memory_block_data_at_ .
      change (Tstruct _SHA256state_st noattr) with t_struct_SHA256state_st.
      Time cancel. (*3*)
       clear - FC_cb; hnf in FC_cb|-*; intuition.
       red in H4|-*. simpl in H4|-*. omega.
    }
    simpl.
    Time forward. (*return*) (*19 SLOW*) (*ISssue: leaves a messy subgoal*)
    Exists (Vptr ckb ckoff) pad (HMACabs iSA iSA oSA). 
    Time entailer!. (*11*)
      exists iSA, oSA. auto.
    unfold data_block, hmacstate_, hmac_relate.
    Exists (iS, (iS, oS)).
    change (@data_at spec_sha.CompSpecs Tsh (tarray tuchar (@Zlength Z key)))
       with (@data_at CompSpecs Tsh (tarray tuchar (@Zlength Z key))).
    change (Tarray tuchar 64 noattr) with (tarray tuchar 64).
    Time cancel. (*3*)
    Time entailer!. (*9*)
      split. rewrite (updAbs_len _ _ _ INNER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.
      rewrite (updAbs_len _ _ _ OUTER), Zlength_mkArgZ,
           map_length, mkKey_length; reflexivity.
      unfold_data_at 4%nat.
      rewrite (field_at_data_at _ _ [StructField _md_ctx]).
      rewrite (field_at_data_at _ _ [StructField _i_ctx]).
      unfold field_address; simpl. rewrite if_true by trivial. rewrite if_true by trivial.
      rewrite Int.add_zero. Time cancel. (*0.3*)
  }
} 
Time Qed. (*57*)
