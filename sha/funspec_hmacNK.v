Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import hmac_common_lemmas.

Require Import sha.hmac_NK.
Require Import spec_hmacNK.

Module Type HMAC_ABSTRACT_SPEC.

(*"Ordinary" abstract states contains a key and some data*)
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
  or want to use an oldd ctx, but reinitialize its key. It occurs explicitly
  in the precondition of init_call with argument key==Vptr b i*)
Parameter EMPTY: val -> mpred.

(* We can prematurely terminate sequences of hmac-update by simply declaring
   an updateable ctx FULL*)
Parameter REP_FULL: forall key data c, REP (hABS key data) c |-- FULL key c.

(*We can also "wipe" a ctx, ie forget/erase any key material from ctx*)
Parameter FULL_EMPTY: forall key c, FULL key c |-- EMPTY c.

(****** Next, here are the new specs of openssl's API functions *************)
(* I have split the two cases for hmac_init. mbedtls separates these situations in its API:
   mbedtls_md_hmac_reset prepares to authenticate a new message with the same key;
   mbedtls_md_hmac_starts sets the key and prepares to authenticate a new message. *)

Definition hmac_reset_spec :=
  DECLARE _HMAC_Init (*Naphat: you'll probably have DECLARE mbedtls_hmac_reset here, and the
                       body of your wrapper function is a call to hmac_init with key==null.*)
   WITH c : val, l:Z, key:list Z, kv:val, d:list Z
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP (has_lengthK l key)
         LOCAL (temp _ctx c; temp _key nullval; temp _len (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP ( `(FULL key c); `(K_vector kv))
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (`(REP (hABS key nil) c); `(K_vector kv)).

Definition hmac_starts_spec :=
  DECLARE _HMAC_Init (*Naphat: you'll probably have DECLARE mbedtls_hmac_starts here, and the
                       body of your wrapper function is a call to hmac_init with the nonnull key*)
   WITH c : val, l:Z, key:list Z, kv:val, b:block, i:Int.int
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP (has_lengthK l key)
         LOCAL (temp _ctx c; temp _key (Vptr b i); temp _len (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP (`(EMPTY c); 
              `(data_block Tsh key (Vptr b i)); `(K_vector kv))
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (`(REP (hABS key nil) c); `(data_block Tsh key (Vptr b i)); `(K_vector kv)).

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
         SEP(`(REP (hABS key data) c); `(data_block Tsh data1 d); `(K_vector kv))
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(`(REP (hABS key (data++data1)) c); 
              `(data_block Tsh data1 d);`(K_vector kv)).

Definition hmac_final_spec :=
  DECLARE _HMAC_Final
   WITH data:list Z, key:list Z, c : val, md:val, shmd: share, kv:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _md OF tptr tuchar ]
       PROP (writable_share shmd) 
       LOCAL (temp _md md; temp _ctx c;
              gvar sha._K256 kv)
       SEP(`(REP (hABS key data) c); `(K_vector kv);
           `(memory_block shmd 32 md))
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(`(K_vector kv);
              `(FULL key c);
              `(data_block shmd (HMAC256 data key) md)).

(*Maybe this is not needed in mbedtls?*)
Definition hmac_cleanup_spec :=
  DECLARE _HMAC_cleanup
   WITH key: list Z, c : val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st ]
         PROP () 
         LOCAL (temp _ctx c)
         SEP(`(FULL key c))
  POST [ tvoid ]  
          PROP () 
          LOCAL ()
          SEP(`(EMPTY c)).

(* Finally, we have prrofs that the openssl implementations satisfy these specs*)

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

End HMAC_ABSTRACT_SPEC.

Module OPENSSL_HMAC_ABSTRACT_SPEC <: HMAC_ABSTRACT_SPEC.
Inductive HABS := hABS: forall (key data:list Z), HABS.

Definition abs_relate (a: HABS) (r: hmacstate) : Prop :=
  match a with hABS key data => 
  exists hInit hUpd, 
    hmacInit key hInit /\ 
    hmacUpdate data hInit hUpd /\
    hmac_relate hUpd r 
  end. 

Definition REP (a: HABS) (c: val) : mpred :=
   EX r:hmacstate, 
    (!!(abs_relate a r) && data_at Tsh t_struct_hmac_ctx_st r c).

Definition FULL key c:mpred :=
   EX h:_, hmacstate_PreInitNull key h c.

Definition EMPTY c : mpred := data_at_ Tsh t_struct_hmac_ctx_st c.

Lemma REP_FULL key data c: REP (hABS key data) c |-- FULL key c.
Proof. unfold REP, FULL. normalize.
  unfold hmacstate_PreInitNull.
  destruct H as [hInit [hUpd [INIT [UPD REL]]]].
  Exists hUpd. Exists r. Exists (fst r).
  apply andp_right.
    apply prop_right. destruct hUpd. simpl in *.
    destruct INIT as [? [? [? [? ?]]]]. subst hInit.
    destruct UPD as [? [? UPD]]. symmetry in UPD; inv UPD.
    intuition.
  apply derives_refl'. f_equal. destruct r as [md [IS OS]]. simpl. reflexivity.
Qed.

Lemma FULL_EMPTY key c: FULL key c |-- EMPTY c.
Proof. unfold FULL, EMPTY. normalize.
 unfold hmacstate_PreInitNull. 
 apply imp_extract_exp_left. intros x. 
 apply imp_extract_exp_left. intros v.
 apply andp_left2. apply data_at_data_at_.
Qed.
(*VST Issue: normalize or entailer or entailer! or simpl; normalize. here take ages!!!*)

(************************ Abstract specifications of HMAC_init *******************************************************)

Definition hmac_reset_spec :=
  DECLARE _HMAC_Init
   WITH c : val, l:Z, key:list Z, kv:val, d:list Z
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP (has_lengthK l key)
         LOCAL (temp _ctx c; temp _key nullval; temp _len (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP ( `(FULL key c); `(K_vector kv))
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (`(REP (hABS key nil) c); `(K_vector kv)).

Definition hmac_starts_spec :=
  DECLARE _HMAC_Init
   WITH c : val, l:Z, key:list Z, kv:val, b:block, i:Int.int
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _key OF tptr tuchar,
         _len OF tint ]
         PROP (has_lengthK l key)
         LOCAL (temp _ctx c; temp _key (Vptr b i); temp _len (Vint (Int.repr l));
                gvar sha._K256 kv)
         SEP ((*`(EX a:_, REP a c)*) `(EMPTY c); 
              `(data_block Tsh key (Vptr b i)); `(K_vector kv))
  POST [ tvoid ] 
     PROP ()
     LOCAL ()
     SEP (`(REP (hABS key nil) c); `(data_block Tsh key (Vptr b i)); `(K_vector kv)).

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
         SEP(`(REP (hABS key data) c); `(data_block Tsh data1 d); `(K_vector kv))
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(`(REP (hABS key (data++data1)) c); 
              `(data_block Tsh data1 d);`(K_vector kv)).

Definition hmac_final_spec :=
  DECLARE _HMAC_Final
   WITH data:list Z, key:list Z, c : val, md:val, shmd: share, kv:val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st,
         _md OF tptr tuchar ]
       PROP (writable_share shmd) 
       LOCAL (temp _md md; temp _ctx c;
              gvar sha._K256 kv)
       SEP(`(REP (hABS key data) c); `(K_vector kv);
           `(memory_block shmd 32 md))
  POST [ tvoid ] 
          PROP () 
          LOCAL ()
          SEP(`(K_vector kv);
              `(FULL key c);
              `(data_block shmd (HMAC256 data key) md)).

Definition hmac_cleanup_spec :=
  DECLARE _HMAC_cleanup
   WITH key: list Z, c : val
   PRE [ _ctx OF tptr t_struct_hmac_ctx_st ]
         PROP () 
         LOCAL (temp _ctx c)
         SEP(`(FULL key c))
  POST [ tvoid ]  
          PROP () 
          LOCAL ()
          SEP(`(EMPTY c)).

(******** Statements about the "true" bodies of all functions, 
         extracted from the proofs in verif_hmacNK_XXX.v ************)

Lemma finalbodyproof Espec c md shmd kv buf (h1 : hmacabs)
      (SH : writable_share shmd):
@semax CompSpecs Espec (func_tycontext f_HMAC_Final HmacVarSpecs HmacFunSpecs)
  (PROP  ()
   LOCAL  (lvar _buf (tarray tuchar 32) buf; temp _md md; temp _ctx c;
   gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh (tarray tuchar 32) buf); `(hmacstate_ h1 c);
   `(K_vector kv); `(memory_block shmd 32 md)))
  (Ssequence (fn_body f_HMAC_Final) (Sreturn None)) 
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (EX  digestH2 : list Z * hmacabs,
         PROP  (hmacFinal h1 (fst digestH2) (snd digestH2))
         LOCAL ()
         SEP  (`(K_vector kv); `(hmacstate_PostFinal (snd digestH2) c);
         `(data_block shmd (fst digestH2) md))))
     (EX  v : val,
      local (lvar _buf (tarray tuchar 32) v) &&
      `(data_at_ Tsh (tarray tuchar 32) v))).
Admitted. 

Lemma updatebodyproof Espec c d len data kv (h1 : hmacabs)
(H : has_lengthD (s256a_len (absCtxt h1)) len data):
@semax CompSpecs Espec (func_tycontext f_HMAC_Update HmacVarSpecs HmacFunSpecs)
  (PROP  ()
   LOCAL  (temp _ctx c; temp _data d; temp _len (Vint (Int.repr len));
   gvar sha._K256 kv)
   SEP  (`(K_vector kv); `(hmacstate_ h1 c); `(data_block Tsh data d)))
  (Ssequence (fn_body f_HMAC_Update) (Sreturn None)) 
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (EX  h2 : hmacabs,
         PROP  (hmacUpdate data h1 h2)
         LOCAL ()
         SEP  (`(K_vector kv); `(hmacstate_ h2 c); `(data_block Tsh data d))))
     emp).
Admitted.

Lemma initbodyproof Espec c k l key kv h1 pad ctxkey (H : has_lengthK l key):
@semax CompSpecs Espec (func_tycontext f_HMAC_Init HmacVarSpecs HmacFunSpecs)
  (PROP  ()
   LOCAL  (lvar _ctx_key (tarray tuchar 64) ctxkey;
   lvar _pad (tarray tuchar 64) pad; temp _ctx c; temp _key k;
   temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh (tarray tuchar 64) ctxkey);
   `(data_at_ Tsh (tarray tuchar 64) pad); `(K_vector kv);
   `(initPre c k h1 key)))
  (Ssequence (fn_body f_HMAC_Init) (Sreturn None)) 
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (EX  h : hmacabs,
         PROP  (hmacInit key h)
         LOCAL ()
         SEP  (`(hmacstate_ h c); `(initPostKey k key); `(K_vector kv))))
     ((EX  v : val,
       local (lvar _pad (tarray tuchar 64) v) &&
       `(data_at_ Tsh (tarray tuchar 64) v)) *
      (EX  v : val,
       local (lvar _ctx_key (tarray tuchar 64) v) &&
       `(data_at_ Tsh (tarray tuchar 64) v)))).
Admitted. 

Lemma cleanupbodyproof1 Espec c h :
@semax CompSpecs Espec (func_tycontext f_HMAC_cleanup HmacVarSpecs HmacFunSpecs)
  (PROP  ()
   LOCAL  (temp _ctx c)
   SEP  (`(EX  key : list Z, hmacstate_PreInitNull key h c)))
  (Ssequence (fn_body f_HMAC_cleanup) (Sreturn None)) 
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP  ()
         LOCAL ()
         SEP 
         (`(data_block Tsh
              (list_repeat (Z.to_nat (sizeof cenv_cs t_struct_hmac_ctx_st)) 0)
              c)))) emp).
Admitted. 

Lemma body_hmac_final: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Final hmac_final_spec. 
Proof.
start_function.
name ctx' _ctx.
name md' _md.
rename lvar0 into buf.
unfold REP, abs_relate; normalize. intros h1. normalize.
destruct H as [hInit [hUpd [Init [UPD REL]]]].
eapply semax_pre_post.
  3: apply (finalbodyproof Espec c md shmd kv buf hUpd SH).
  
  entailer. cancel. unfold hmacstate_. Exists h1; entailer.

  intros. apply andp_left2. unfold POSTCONDITION, abbreviate. entailer.
    destruct ek; entailer. destruct vl; entailer.
    Exists x; normalize.  
    rewrite (hmacSimple_sound key data (fst x0)).
    Focus 2. exists hInit, hUpd. split. trivial. split. trivial.
             rewrite hmacFinal_hmacFinalSimple. exists (snd x0); trivial.
    cancel. 
    unfold FULL. Exists (snd x0). 
    eapply hmacstate_PostFinal_PreInitNull; eassumption. 
Qed.

Lemma body_hmac_update: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Update hmac_update_spec. 
Proof.
start_function.
name ctx' _ctx.
name data' _data.
name len' _len.
destruct H as [Prop1 Prop2].
unfold REP. normalize. intros r. normalize.
destruct H as [hInit [hUpd [INIT [UPD REL]]]].
eapply semax_pre_post.
  3: apply (updatebodyproof Espec c d (Zlength data1) data1 kv hUpd).

  unfold hmacstate_. entailer. Exists r. entailer. cancel.

  intros. apply andp_left2. unfold POSTCONDITION, abbreviate. entailer.
    destruct ek; entailer. destruct vl; entailer. cancel.
    unfold REP, hmacstate_. normalize. Exists x0; entailer. 
    apply prop_right. unfold abs_relate. exists hInit, x. intuition.
    eapply hmacUpdate_app; eassumption.

  destruct hInit. destruct INIT as [iS [oS [? [? II]]]]; inv II.
  destruct hUpd; simpl in *. destruct UPD as [? [? HH]]; symmetry in HH; inv HH.
  rewrite (updAbs_len _ _ _ H1).
  destruct REL as [? [? [? [IL ?]]]]. rewrite IL.
  split. trivial. split. trivial.
  specialize (Z.mul_add_distr_r 64 (Zlength data) 8); simpl; intros D; rewrite <- D; clear D.
  rewrite <- Z.mul_add_distr_r. 
  assert (Tpp: (two_power_pos 64 = two_power_pos 61 * 8)%Z) by reflexivity.
  rewrite Tpp.  
  apply Zmult_lt_compat_r. omega. rewrite (Z.add_comm 64), Z.add_assoc; trivial.
Qed.  

Lemma body_hmac_starts: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Init hmac_starts_spec. 
Proof.
start_function.
name ctx' _ctx.
name key' _key.
name len' _len.
rename lvar0 into pad. rename lvar1 into ctxkey.
unfold EMPTY. 
remember (HMACabs (S256abs nil nil) (S256abs nil nil) (S256abs nil nil)) as hdummy.
eapply semax_pre_post.
Focus 3. apply (initbodyproof Espec c (Vptr b i) l key kv hdummy pad ctxkey H).
  entailer. cancel.
  intros. apply andp_left2. unfold POSTCONDITION, abbreviate.
   entailer. destruct ek; entailer.
   destruct vl; entailer.
   Exists x. entailer. Exists x0; entailer. cancel.
   unfold hmacstate_, REP. normalize. Exists r. entailer!.
   red. exists x1, x1; intuition.
   eapply hmacUpdate_nil. eassumption.
Qed.

Lemma body_hmac_reset: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_Init hmac_reset_spec. 
Proof.
start_function.
name ctx' _ctx.
name key' _key.
name len' _len.
rename lvar0 into pad. rename lvar1 into ctxkey.
apply semax_pre with (P':=EX h1:hmacabs, 
  (PROP  ()
   LOCAL  (lvar _ctx_key (tarray tuchar 64) ctxkey;
   lvar _pad (tarray tuchar 64) pad; temp _ctx c; temp _key nullval;
   temp _len (Vint (Int.repr l)); gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh (tarray tuchar 64) ctxkey);
   `(data_at_ Tsh (tarray tuchar 64) pad); `(K_vector kv);
   `(initPre c nullval h1 key)))). 
{ unfold FULL. entailer!. Exists h. entailer!. }
apply extract_exists_pre. intros h1.
eapply semax_pre_post.
Focus 3. apply (initbodyproof Espec c nullval l key kv h1 pad ctxkey H).
  entailer!.
  intros. apply andp_left2. unfold POSTCONDITION, abbreviate.
   entailer. destruct ek; entailer.
   destruct vl; entailer.
   Exists x. entailer. Exists x0; entailer. cancel.
   unfold hmacstate_, REP. normalize. Exists r. entailer!.
   red. exists x1, x1; intuition.
   eapply hmacUpdate_nil. eassumption.
Qed.

Lemma body_hmac_cleanup: semax_body HmacVarSpecs HmacFunSpecs 
       f_HMAC_cleanup hmac_cleanup_spec.
Proof.
start_function.
name ctx' _ctx.
unfold FULL. normalize. intros h.
assert_PROP (field_compatible t_struct_hmac_ctx_st [] c).
{ unfold hmacstate_PreInitNull. entailer. }
eapply semax_pre_post.
  3: apply (cleanupbodyproof1 Espec c h).
  entailer. unfold hmacstate_PreInitNull, hmacstate_PostFinal. normalize.
    Exists key. entailer!. Exists r. Exists v. entailer!. 

  intros. apply andp_left2. unfold POSTCONDITION, abbreviate.
   entailer. destruct ek; entailer.
   destruct vl; entailer. unfold EMPTY. 
   rewrite <- memory_block_data_at_. simpl. unfold data_block.
   normalize. apply data_at_memory_block. trivial.
Qed. 

End OPENSSL_HMAC_ABSTRACT_SPEC.
