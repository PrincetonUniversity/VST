Require Import VST.floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.hmac_common_lemmas.

Require Import sha.hmac.
Require Import sha.spec_hmac.

Require Import sha.ByteBitRelations.
Require Import sha.verif_hmac_crypto.

Module Type HMAC_ABSTRACT_SPEC.

(*"Ordinary" abstract states contain a key and some data*)
Inductive HABS := hABS: forall (key data:list Z), HABS.

(*The mpred REP (hABS k d) c expresses that pointer value c holds
  a ctx representing the situation where we have hmac-ed
  data a with key k, and are prepeared to accept additional data.*)
Parameter REP: HABS -> val -> mpred.

(*We have two additional protocol states. FULL k c holds after we return
  from hmac-final (so we can't hmac-updeate more data into ctx).
  It's the precondition of calls to hmac_init with argument key==null, ie 
  the case where we want to reuse the key k in the next round of hmac. *)
Parameter FULL: list Z -> val -> mpred.

(*EMPTY c captures the situation where we either haven't provided any key yet,
  or want to use an old ctx, but reinitialize its key. It occurs explicitly
  in the precondition of init_call with argument key==Vptr b i*)
Parameter EMPTY: val -> mpred.

(*We can turn a memory block of hmac_ctx size into an EMPTY abstract HMAC REP*)
(*Parameter mkEmpty: forall v, field_compatible t_struct_hmac_ctx_st [] v -> 
memory_block Tsh (sizeof t_struct_hmac_ctx_st) v |-- EMPTY v.*)
Parameter mkEmpty: forall v, data_at_ Tsh t_struct_hmac_ctx_st v |-- EMPTY v.

(*The reverse operation enables dellocation of stack-allocated hmac contexts at the
end of client functions*)
Parameter EmptyDissolve: forall v, EMPTY v |-- data_at_ Tsh t_struct_hmac_ctx_st v.

(* We can prematurely terminate sequences of hmac-update by simply declaring
   an updateable ctx FULL*)
Parameter REP_FULL: forall key data c, REP (hABS key data) c |-- FULL key c.

(*We can also "wipe" a ctx, ie forget/erase any key material from ctx*)
Parameter FULL_EMPTY: forall key c, FULL key c |-- EMPTY c.

Parameter EMPTY_isptr: forall c, EMPTY c |-- !!isptr c.

Lemma FULL_isptr: forall key c, FULL key c |-- !!isptr c.
Proof.
  intros.
  eapply derives_trans.
  apply FULL_EMPTY.
  apply EMPTY_isptr.
Qed.

Lemma REP_isptr: forall key data c, REP (hABS key data) c |-- !!isptr c.
Proof.
  intros.
  eapply derives_trans.
  apply REP_FULL.
  apply FULL_isptr.
Qed.

(****** Next, here are the new specs of openssl's API functions *************)
(* I have split the two cases for hmac_init. mbedtls separates these situations in its API:
   mbedtls_md_hmac_reset prepares to authenticate a new message with the same key;
   mbedtls_md_hmac_starts sets the key and prepares to authenticate a new message. *)

Definition hmac_reset_spec :=
  DECLARE _HMAC_Init (*Naphat: you'll probably have DECLARE mbedtls_hmac_reset here, and the
                       body of your wrapper function is a call to hmac_init with key==null.*)
   WITH c : val, l:Z, key:list Z, kv:val 
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP ()
         LOCAL (temp _ctx c; temp _key nullval; temp _len (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP (FULL key c; K_vector kv)
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (REP (hABS key nil) c; K_vector kv).

Definition hmac_starts_spec :=
  DECLARE _HMAC_Init (*Naphat: you'll probably have DECLARE mbedtls_hmac_starts here, and the
                       body of your wrapper function is a call to hmac_init with the nonnull key*)
   WITH c : val, l:Z, key:list Z, kv:val, b:block, i:ptrofs
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP (has_lengthK l key)
         LOCAL (temp _ctx c; temp _key (Vptr b i); temp _len (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP (EMPTY c; data_block Tsh key (Vptr b i); K_vector kv)
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (REP (hABS key nil) c; data_block Tsh key (Vptr b i); K_vector kv).

Definition hmac_update_spec :=
  DECLARE _HMAC_Update
   WITH key: list Z, c : val, d:val, data:list Z, data1:list Z, kv:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st, 
         _data OF tptr tvoid, 
         _len OF tuint]
         PROP (0 <= Zlength data1 <= Int.max_unsigned /\
               Zlength data1 + Zlength data + 64 < two_power_pos 61) 
         LOCAL (temp _ctx c; temp _data d; temp  _len (Vint (Int.repr (Zlength data1)));
                gvar sha._K256 kv)
         SEP(REP (hABS key data) c; data_block Tsh data1 d; K_vector kv)
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(REP (hABS key (data++data1)) c; 
              data_block Tsh data1 d; K_vector kv).

Definition hmac_final_spec :=
  DECLARE _HMAC_Final
   WITH data:list Z, key:list Z, c : val, md:val, shmd: share, kv:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _md OF tptr tuchar ]
       PROP (writable_share shmd) 
       LOCAL (temp _md md; temp _ctx c;
              gvar sha._K256 kv)
       SEP(REP (hABS key data) c; K_vector kv;
           memory_block shmd 32 md)
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(K_vector kv; FULL key c;
              data_block shmd (HMAC256 data key) md).

(*Maybe this is not needed in mbedtls?*)
Definition hmac_cleanup_spec :=
  DECLARE _HMAC_cleanup
   WITH key: list Z, c : val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st ]
         PROP () 
         LOCAL (temp _ctx c)
         SEP(FULL key c)
  POST [ tvoid ]  
          PROP () 
          LOCAL ()
          SEP(EMPTY c).

Definition hmac_crypto_spec :=
  DECLARE _HMAC
   WITH md: val, KEY:DATA,
        msg: val, MSG:DATA,
        kv:val, shmd: share, b:block, i:ptrofs
   PRE [ _key OF tptr tuchar,
         _key_len OF tint,
         _d OF tptr tuchar,
         _n OF tint,
         _md OF tptr tuchar ]
         PROP (writable_share shmd; 
               has_lengthK (LEN KEY) (CONT KEY);
               has_lengthD 512 (LEN MSG) (CONT MSG))
         LOCAL (temp _md md; temp _key (Vptr b i);
                temp _key_len (Vint (Int.repr (LEN KEY)));
                temp _d msg; temp _n (Vint (Int.repr (LEN MSG)));
                gvar sha._K256 kv)
         SEP(data_block Tsh (CONT KEY) (Vptr b i); 
             data_block Tsh (CONT MSG) msg; 
             memory_block shmd 32 md;
             K_vector kv)
  POST [ tptr tuchar ] 
         EX digest:_,
          PROP (digest= HMAC256 (CONT MSG) (CONT KEY) /\
                ByteBitRelations.bytesToBits digest = 
                verif_hmac_crypto.bitspec KEY MSG /\ 
                forall A Awf, CRYPTO A Awf)
          LOCAL (temp ret_temp md)
          SEP(K_vector kv;
              data_block shmd digest md;
              data_block Tsh (CONT MSG) msg; data_block Tsh (CONT KEY) (Vptr b i)).

(* Finally, we have proofs that the openssl implementations satisfy these specs*)

Parameter body_hmac_final: semax_body HmacVarSpecs HmacFunSpecs 
                           f_HMAC_Final hmac_final_spec. 

Parameter body_hmac_update: semax_body HmacVarSpecs HmacFunSpecs 
                            f_HMAC_Update hmac_update_spec. 

Parameter body_hmac_starts: semax_body HmacVarSpecs HmacFunSpecs 
                             f_HMAC_Init hmac_starts_spec.
 
Parameter body_hmac_reset: semax_body HmacVarSpecs HmacFunSpecs 
                              f_HMAC_Init hmac_reset_spec. 

Parameter body_hmac_cleanup: semax_body HmacVarSpecs HmacFunSpecs 
                             f_HMAC_cleanup hmac_cleanup_spec.

Parameter body_hmac_crypto: semax_body HmacVarSpecs HmacFunSpecs 
                             f_HMAC hmac_crypto_spec.

End HMAC_ABSTRACT_SPEC.

Lemma haslengthK_simple: forall l, 0 < l <= Int.max_signed -> l * 8 < two_p 64.
intros. 
assert (l < Int.half_modulus). unfold Int.max_signed in H. omega. clear H.
rewrite Int.half_modulus_power in H0. 
assert (Int.zwordsize = 32) by reflexivity. rewrite H in *; clear H. simpl in *.
rewrite two_power_pos_equiv in *. 
assert (l * 8 < 2^31 * 8) by omega. clear H0.
eapply Z.lt_trans. eassumption. clear H. cbv; trivial.
Qed.

Require Import sha.verif_hmac_final.
Require Import sha.verif_hmac_update.
Require Import sha.verif_hmac_init.
Require Import sha.verif_hmac_cleanup.
Import sha.ByteBitRelations.
Import sha.verif_hmac_crypto.

Module OPENSSL_HMAC_ABSTRACT_SPEC <: HMAC_ABSTRACT_SPEC.
Inductive HABS := hABS: forall (key data:list Z), HABS.

Definition abs_relate (a: HABS) (r: hmacstate) : Prop :=
  match a with hABS key data => 
    hmac_relate (hmacUpdate data (hmacInit key)) r
  end. 

Definition REP (a: HABS) (c: val) : mpred :=
   EX r:hmacstate, 
    (!!(abs_relate a r) && data_at Tsh t_struct_hmac_ctx_st r c).

Definition FULL key c:mpred :=
   (*!!(has_lengthK (Zlength key) key) &&*) EX h:_, hmacstate_PreInitNull key h c.

Definition EMPTY c : mpred := data_at_ Tsh t_struct_hmac_ctx_st c.
(*
Lemma mkEmpty v: field_compatible t_struct_hmac_ctx_st [] v -> 
  memory_block Tsh (sizeof t_struct_hmac_ctx_st) v |-- EMPTY v.
Proof. intros. unfold EMPTY.
clear H.

 rewrite data_at__memory_block. entailer.
unfold field_compatible.
rewrite memory_block_size_compatible, memory_block_isptr.
entailer.
unfold align_compatible. simpl. destruct v; try solve [inv Pv]. simpl.
unfold align_attr. simpl. memory_block sh (sizeof t) p. simpl.
 Qed.

Lemma EmptyDissolve: forall v, 
  EMPTY v |-- memory_block Tsh (sizeof t_struct_hmac_ctx_st) v .
Proof. intros. unfold EMPTY. rewrite data_at__memory_block. entailer!. Qed.
*)
Lemma mkEmpty v: data_at_ Tsh t_struct_hmac_ctx_st v |-- EMPTY v.
Proof. apply derives_refl. Qed.

Lemma EmptyDissolve v: EMPTY v |-- data_at_ Tsh t_struct_hmac_ctx_st v.
Proof. apply derives_refl. Qed.

Lemma REP_FULL key data c: REP (hABS key data) c |-- FULL key c.
Proof. unfold REP, FULL. Intros r.
  unfold hmacstate_PreInitNull. simpl in H.
  destruct H as [mREL [iREL [oREL [iLEN oLEN]]]].
  Exists (hmacUpdate data (hmacInit key)) r (fst r).
  apply andp_right.
    apply prop_right. simpl. intuition.
  apply derives_refl'. f_equal. destruct r as [md [IS OS]]. simpl. reflexivity.
Qed.

Lemma FULL_EMPTY key c: FULL key c |-- EMPTY c.
Proof. unfold FULL, EMPTY.
 unfold hmacstate_PreInitNull. Intros h r v. 
 apply data_at_data_at_.
Qed.

Lemma EMPTY_isptr c: EMPTY c |-- !!isptr c. 
Proof. unfold EMPTY. entailer!. Qed.

Lemma FULL_isptr key c: FULL key c |-- !!isptr c.
Proof.
  eapply derives_trans.
  apply FULL_EMPTY.
  apply EMPTY_isptr.
Qed.

Lemma REP_isptr key data c: REP (hABS key data) c |-- !!isptr c.
Proof.
  eapply derives_trans.
  apply REP_FULL.
  apply FULL_isptr.
Qed.

(************************ Abstract specifications of HMAC_init *******************************************************)

Definition hmac_reset_spec :=
  DECLARE _HMAC_Init
   WITH c : val, l:Z, key:list Z, kv:val (*, d:list Z*)
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP ()
         LOCAL (temp _ctx c; temp _key nullval; temp _len (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP (FULL key c; K_vector kv)
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (REP (hABS key nil) c; K_vector kv).

Definition hmac_starts_spec :=
  DECLARE _HMAC_Init
   WITH c : val, l:Z, key:list Z, kv:val, b:block, i:ptrofs
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP (has_lengthK l key)
         LOCAL (temp _ctx c; temp _key (Vptr b i); temp _len (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP (EMPTY c; data_block Tsh key (Vptr b i); K_vector kv)
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (REP (hABS key nil) c; data_block Tsh key (Vptr b i); K_vector kv).

Definition hmac_update_spec :=
  DECLARE _HMAC_Update
   WITH key: list Z, c : val, d:val, data:list Z, data1:list Z, kv:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st, 
         _data OF tptr tvoid, 
         _len OF tuint]
         PROP (0 <= Zlength data1 <= Int.max_unsigned /\
               Zlength data1 + Zlength data + 64 < two_power_pos 61) 
         LOCAL (temp _ctx c; temp _data d; temp  _len (Vint (Int.repr (Zlength data1)));
                gvar sha._K256 kv)
         SEP(REP (hABS key data) c; data_block Tsh data1 d; K_vector kv)
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(REP (hABS key (data++data1)) c; 
              data_block Tsh data1 d; K_vector kv).

Definition hmac_final_spec :=
  DECLARE _HMAC_Final
   WITH data:list Z, key:list Z, c : val, md:val, shmd: share, kv:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _md OF tptr tuchar ]
       PROP (writable_share shmd) 
       LOCAL (temp _md md; temp _ctx c;
              gvar sha._K256 kv)
       SEP(REP (hABS key data) c; K_vector kv;
           memory_block shmd 32 md)
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(K_vector kv;
              FULL key c;
              data_block shmd (HMAC256 data key) md).

Definition hmac_cleanup_spec :=
  DECLARE _HMAC_cleanup
   WITH key: list Z, c : val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st ]
         PROP () 
         LOCAL (temp _ctx c)
         SEP(FULL key c)
  POST [ tvoid ]  
          PROP () 
          LOCAL ()
          SEP(EMPTY c).

Definition hmac_crypto_spec :=
  DECLARE _HMAC
   WITH md: val, KEY:DATA,
        msg: val, MSG:DATA,
        kv:val, shmd: share, b:block, i:ptrofs
   PRE [ _key OF tptr tuchar,
         _key_len OF tint,
         _d OF tptr tuchar,
         _n OF tint,
         _md OF tptr tuchar ]
         PROP (writable_share shmd; 
               has_lengthK (LEN KEY) (CONT KEY);
               has_lengthD 512 (LEN MSG) (CONT MSG))
         LOCAL (temp _md md; temp _key (Vptr b i);
                temp _key_len (Vint (Int.repr (LEN KEY)));
                temp _d msg; temp _n (Vint (Int.repr (LEN MSG)));
                gvar sha._K256 kv)
         SEP(data_block Tsh (CONT KEY) (Vptr b i); 
             data_block Tsh (CONT MSG) msg; 
             memory_block shmd 32 md;
             K_vector kv)
  POST [ tptr tuchar ] 
         EX digest:_,
          PROP (digest= HMAC256 (CONT MSG) (CONT KEY) /\
                ByteBitRelations.bytesToBits digest = 
                verif_hmac_crypto.bitspec KEY MSG /\ 
                forall A Awf, CRYPTO A Awf)
          LOCAL (temp ret_temp md)
          SEP(K_vector kv;
              data_block shmd digest md;
              data_block Tsh (CONT MSG) msg; data_block Tsh (CONT KEY) (Vptr b i)).

Lemma body_hmac_crypto: semax_body HmacVarSpecs HmacFunSpecs 
      f_HMAC hmac_crypto_spec.
Proof.
start_function.
rename v_c into c. rename H into KL. rename H0 into DL.
eapply semax_pre_post.
6: eapply (hmacbodycryptoproof Espec (Vptr b i) KEY msg MSG kv shmd md c); eassumption.
entailer!.
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.
subst POSTCONDITION; unfold abbreviate; simpl_ret_assert.
intros.
apply andp_left2.
apply sepcon_derives; auto.
apply bind_ret_derives.
unfold initPostKey.
Intros digest; Exists digest.
old_go_lower; entailer!.
Qed.

Lemma body_hmac_reset: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Init hmac_reset_spec. 
Proof.
start_function.
rename v_pad into pad. rename v_ctx_key into ctxkey.
abbreviate_semax.
apply semax_pre with (P':=EX h1:hmacabs, 
  (PROP  ()
   LOCAL  (lvar _ctx_key (tarray tuchar 64) ctxkey;
   lvar _pad (tarray tuchar 64) pad; temp _ctx c; temp _key nullval;
   temp _len (Vint (Int.repr l));  gvar sha._K256 kv)
   SEP  (data_at_ Tsh (tarray tuchar 64) ctxkey;
   data_at_ Tsh (tarray tuchar 64) pad; K_vector kv;
   initPre c nullval h1 l key))). 
{ unfold FULL. Intros h1. Exists h1. (*red in H.*)  entailer!. }
Intros h1.
eapply semax_post.
5: apply (initbodyproof Espec c nullval l key kv h1 pad ctxkey).
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.

  intros.
  subst POSTCONDITION; unfold abbreviate; simpl_ret_assert.
apply andp_left2.
apply sepcon_derives; auto.
apply bind_ret_derives.
  old_go_lower.
  entailer!.
  unfold hmacstate_, REP. Intros r. Exists r. entailer!.
  red. rewrite hmacUpdate_nil. assumption. 
Qed.

Lemma body_hmac_final: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Final hmac_final_spec. 
Proof.
start_function.
rename v_buf into buf.
unfold REP, abs_relate. Intros r.
destruct H as [mREL [iREL [oREL [iLEN oLEN]]]].
eapply semax_pre_post.
  6: apply (finalbodyproof Espec c md shmd kv buf (hmacUpdate data (hmacInit key)) SH).
  
  apply andp_left2. unfold hmacstate_. Exists r. old_go_lower. entailer!.
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.

  intros. apply andp_left2.
  subst POSTCONDITION; unfold abbreviate; simpl_ret_assert.
  apply sepcon_derives; auto.
  apply bind_ret_derives.
  rewrite <- hmac_sound. unfold FULL.
  change (hmacFinal (hmacUpdate data (hmacInit key))) with (hmac key data).
  Exists (fst (hmac key data)). old_go_lower. entailer!.
  eapply hmacstate_PostFinal_PreInitNull; reflexivity.
Qed.

Lemma body_hmac_update: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Update hmac_update_spec. 
Proof.
start_function.
destruct H as [Prop1 Prop2].
eapply semax_pre_post.
  6: apply (updatebodyproof Espec c d (Zlength data1) data1 kv (hmacUpdate data (hmacInit key))).

  apply andp_left2. old_go_lower. entailer!; try apply derives_refl.
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.

  intros. apply andp_left2.
  subst POSTCONDITION; unfold abbreviate; simpl_ret_assert.
  apply sepcon_derives; auto.
  apply bind_ret_derives.
  rewrite hmacUpdate_app. old_go_lower. entailer!; try apply derives_refl.
  apply derives_refl.
  split; trivial. split; trivial. simpl.
  unfold innerShaInit, s256a_len.
  rewrite Zlength_app, Zlength_mkArgZ, map_length, mkKey_length, Min.min_idempotent.
  simpl. rewrite (Z.add_comm 64), <- Z.mul_add_distr_r, Z.add_assoc. 
  assert (Tpp: (two_power_pos 64 = two_power_pos 61 * 8)%Z) by reflexivity.
  rewrite Tpp.  
  apply Zmult_lt_compat_r. omega. trivial. 
Qed.  

Lemma body_hmac_starts: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Init hmac_starts_spec. 
Proof.
start_function.
rename v_pad into pad. rename v_ctx_key into ctxkey.
unfold EMPTY. 
remember (HMACabs (S256abs nil nil) (S256abs nil nil) (S256abs nil nil)) as hdummy.
eapply semax_pre_post.
6: apply (initbodyproof Espec c (Vptr b i) l key kv hdummy pad ctxkey).

 entailer!.
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.

  intros. apply andp_left2.
  subst POSTCONDITION; unfold abbreviate; simpl_ret_assert.
  apply sepcon_derives; auto.
  apply bind_ret_derives.
  old_go_lower. entailer!.
   unfold hmacstate_, REP. Intros r. Exists r. entailer!.
   red. rewrite hmacUpdate_nil. assumption.
Qed.

Lemma body_hmac_cleanup: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_cleanup hmac_cleanup_spec.
Proof.
start_function.
unfold FULL. Intros h.
assert_PROP (field_compatible t_struct_hmac_ctx_st [] c).
{ unfold hmacstate_PreInitNull. Intros r v. entailer!. }
eapply semax_pre_post.
  6: apply (cleanupbodyproof1 Espec c h).
  Exists key. apply andp_left2. apply derives_refl. 
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.
simpl_ret_assert; normalize.

  intros. apply andp_left2.
  subst POSTCONDITION; unfold abbreviate; simpl_ret_assert.
  apply sepcon_derives; auto.
  apply bind_ret_derives.
  old_go_lower. entailer!.

  unfold EMPTY. 
  rewrite <- memory_block_data_at_. simpl. unfold data_block.
  clear. simpl. apply andp_left2. apply data_at_memory_block.
  trivial.
  apply derives_refl.
Qed. 

End OPENSSL_HMAC_ABSTRACT_SPEC.
