(*In this file, we verify the additional function hmac2, that we added to the c file
  in order to exercise the reuse of a key for several messages. The function calls 
  hmac twice, (on the same message, using the same key) and puts the resulting 
  (identical) digests side by side in a suitably large array.*)

Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Require Import sha.hmac_NK.

Require Import sha.spec_hmacNK.
Require Import vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.
Require Import sha.spec_hmacNK.

Lemma split2_data_at_Tarray_at_tuchar_fold {cs} sh n n1 v p: 0 <= n1 <= n -> n = Zlength v -> n < Int.modulus ->
   field_compatible (Tarray tuchar n noattr) [] p ->
  (@data_at cs sh (Tarray tuchar n1 noattr) (sublist 0 n1 v) p *
   at_offset (@data_at cs sh (Tarray tuchar (n - n1) noattr) (sublist n1 (Zlength v) v)) n1 p)%logic
|-- 
  @data_at cs sh (Tarray tuchar n noattr) v p.
Admitted. (* proof is in tweetnacl/split_array.v*)

Lemma memory_block_valid_ptr:
  forall sh n p, n > 0 ->
     memory_block sh n p |-- valid_pointer p.
Proof.
intros.
Admitted. (* In analogy to floyd/field_at.data_at: surely true ;-)*)

Definition HMAC_Double_spec :=
  DECLARE _HMAC
   WITH keyVal: val, KEY:DATA,
        msgVal: val, MSG:DATA,
        kv:val, shmd: share, md: val
   PRE [ _key OF tptr tuchar,
         _key_len OF tint,
         _d OF tptr tuchar,
         _n OF tint,
         _md OF tptr tuchar ]
         PROP (writable_share shmd; 
               has_lengthK (LEN KEY) (CONT KEY);
               has_lengthD 512 (LEN MSG) (CONT MSG))
         LOCAL (temp _md md; temp _key keyVal; 
                temp _key_len (Vint (Int.repr (LEN KEY)));
                temp _d msgVal;
                temp _n (Vint (Int.repr (LEN MSG)));
                gvar sha._K256 kv)
         SEP(`(data_block Tsh (CONT KEY) keyVal);
             `(data_block Tsh (CONT MSG) msgVal);
             `(K_vector kv);
             `(memory_block shmd 64 md))
  POST [ tvoid ] 
         EX digest:_, 
          PROP (digest = HMAC256 (CONT MSG) (CONT KEY))
          LOCAL ()
          SEP(`(K_vector kv);
              `(data_block shmd (digest++digest) md);
              `(initPostKey keyVal (CONT KEY) );
              `(data_block Tsh (CONT MSG) msgVal)).

Lemma hmacstate_PostFinal_PreInitNull key h0 data h1 dig h2 v:
      forall (HmacInit : hmacInit key h0)
             (HmacUpdate : hmacUpdate data h0 h1)
             (Round1Final : hmacFinal h1 dig h2),
      hmacstate_PostFinal h2 v
  |-- hmacstate_PreInitNull key h2 v.
Proof. intros. 
  unfold hmacstate_PostFinal, hmac_relate_PostFinal, hmacstate_PreInitNull; normalize.
  Exists r.
  Exists (default_val t_struct_SHA256state_st). 
  apply andp_right. 2: apply derives_refl.
  apply prop_right. 
    destruct h2. destruct h1. simpl in *.
    destruct Round1Final as [oSA [UPDO [XX FinDig]]]. inversion XX; subst; clear XX.
    destruct h0. simpl in *. destruct HmacUpdate as [ctx2 [UpdI XX]]. inversion XX; subst; clear XX.
    unfold  hmacInit in HmacInit. simpl in *. 
    destruct HmacInit as [IS [OS [ISHA [OSHA XX]]]].  inversion XX; subst; clear XX. 
    intuition.
Qed.

Lemma body_hmac_double: semax_body HmacVarSpecs HmacFunSpecs 
      f_HMAC2 HMAC_Double_spec.
Proof.
start_function.
name key' _key.
name keylen' _key_len.
name d' _d.
name n' _n.
name md' _md.
rename lvar0 into c.
rename keyVal into k. rename msgVal into d.
destruct KEY as [kl key].
destruct MSG as [dl data]. simpl in *.
rewrite memory_block_isptr. normalize.
rename H into KL. rename H0 into DL. 

forward_if  (
  PROP  (isptr c)
   LOCAL  (lvar _c t_struct_hmac_ctx_st c; temp _md md; temp _key k;
   temp _key_len (Vint (Int.repr kl)); temp _d d;
   temp _n (Vint (Int.repr dl)); gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh t_struct_hmac_ctx_st c); `(data_block Tsh key k);
   `(data_block Tsh data d); `(K_vector kv);
   `(memory_block shmd 64 md))).
  { apply denote_tc_comparable_split. 
       apply sepcon_valid_pointer2. apply memory_block_valid_ptr. omega.
       apply valid_pointer_zero. }
  { (* Branch1 *) exfalso. subst md. contradiction.  }
  { (* Branch2 *) forward. entailer. } 
normalize. 

assert_PROP (isptr k). entailer. 
rename H into Pk. 
remember (HMACabs init_s256abs init_s256abs init_s256abs) as dummyHMA.
forward_call (c, k, kl, key, kv, dummyHMA) h0.
  { unfold initPre.
    destruct k; try contradiction.
    cancel.
  }
rename H into HmacInit. normalize.

assert_PROP (s256a_len (absCtxt h0) = 512).
  { unfold hmacstate_. entailer. apply prop_right. 
    destruct h0; simpl in *.  
    destruct H3 as [reprMD [reprI [reprO [iShaLen oShaLen]]]].
    inversion HmacInit; clear HmacInit.
    destruct H3 as [oS [InnSHA [OntSHA XX]]]. inversion XX; clear XX.
    subst. assumption.
  }
rename H into H0_len512.
forward_call (h0, c, d, dl, data, kv) h1.
  { rewrite H0_len512. assumption. } 
rename H into HmacUpdate. 

apply isptrD in Pmd. destruct Pmd as [b [i Pmd]]. rewrite Pmd in *.
assert (GTmod64: 64 < Int.modulus).
  rewrite <- initialize.max_unsigned_modulus, int_max_unsigned_eq. omega.
specialize (memory_block_size_compatible shmd (tarray tuint 16)). simpl; intros.
rewrite (H _ GTmod64); clear H.
normalize. unfold size_compatible in H. simpl in H; rename H into SizeCompat64.
specialize (memory_block_split shmd b (Int.unsigned i) 32 32); intros XX.
  rewrite Int.repr_unsigned in XX. 
  assert (32 + 32 = 64) by omega. rewrite H in XX; clear H.
  rewrite XX; trivial; clear XX.
2: destruct (Int.unsigned_range i); omega.
clear GTmod64.
normalize.
 
forward_call (h1, c, Vptr b i, shmd, kv) [dig h2]. 
simpl in H; rename H into Round1Final.

(**************Round 2*******************************)

replace_SEP 1 (`(initPre c nullval h2 key)). 
  { entailer. eapply hmacstate_PostFinal_PreInitNull; eassumption.
  }

forward_call (c, nullval, kl, key, kv, h2) h3. rename H into h3_init.

assert_PROP (s256a_len (absCtxt h3) = 512).
  { unfold hmacstate_. entailer. apply prop_right. 
    destruct h3; simpl in *.  
    destruct H4 as [reprMD [reprI [reprO [iShaLen oShaLen]]]].
    inversion h3_init; clear h3_init.
    destruct H4 as [oS [InnSHA [OntSHA XX]]]. inversion XX; clear XX.
    subst ctx iSha oSha. assumption.
  }
rename H into H3_len512.
forward_call (h3, c, d, dl, data, kv) h4.
  { rewrite H3_len512. assumption. }
rename H into h4_update.

assert_PROP (field_compatible (Tstruct _hmac_ctx_st noattr) [] c).
{ unfold hmacstate_; entailer. }
rename H into FC_c.

forward_call (h4, c, Vptr b (Int.repr (Int.unsigned i + 32)), shmd, kv) [dig2 h5].
simpl in H; rename H into Round2Final. simpl.

forward_call (h5,c).
forward.

assert_PROP (field_compatible (tarray tuchar (sizeof cenv_cs t_struct_hmac_ctx_st)) [] c).
{ unfold data_block at 1. unfold Zlength. simpl. rewrite data_at_data_at'. normalize. }
clear H2.
Exists c. entailer.
assert (HS: hmacSimple key data dig).
    exists h0, h1. 
    split. assumption.
    split; try assumption.
    rewrite hmacFinal_hmacFinalSimple. exists h2; assumption.
apply hmacSimple_sound in HS. Exists dig; subst dig. entailer.
cancel.

unfold data_block.
  rewrite Zlength_correct; simpl.
rewrite <- memory_block_data_at_; trivial.
normalize. clear H2.
apply andp_right. 
  apply prop_right. apply Forall_app. split; trivial.
  rewrite (memory_block_data_at_ Tsh (tarray tuchar (sizeof (@cenv_cs CompSpecs) t_struct_hmac_ctx_st))).
  2: trivial.
assert (HS2: hmacSimple key data dig2).
    exists h3, h4. 
    split. assumption.
    split; try assumption.
    rewrite hmacFinal_hmacFinalSimple. exists h5; assumption.
  apply hmacSimple_sound in HS2. subst dig2.
rewrite Zlength_app, HMAC_Zlength. 

assert (FC_b: field_compatible (Tarray tuchar (32 + 32) noattr) [] (Vptr b i)).
  red. intuition. apply Z.divide_1_l.

rewrite sepcon_assoc. rewrite sepcon_comm.
apply sepcon_derives.

  eapply derives_trans.
  Focus 2. apply split2_data_at_Tarray_at_tuchar_fold with (n1:=Zlength (HMAC256 data key)); trivial;
            repeat rewrite Zlength_map; try rewrite Zlength_app; try rewrite HMAC_Zlength; omega.
  repeat rewrite Zlength_map.
  repeat rewrite map_app. rewrite Zlength_app, HMAC_Zlength, Zminus_plus.
  rewrite sublist_app1; repeat rewrite Zlength_map; try rewrite HMAC_Zlength; try omega.
  rewrite sublist_same; repeat rewrite Zlength_map; try rewrite HMAC_Zlength; try omega.
  rewrite sublist_app2; repeat rewrite Zlength_map; try rewrite HMAC_Zlength; try omega.
  rewrite Zminus_diag, sublist_same; try rewrite Zlength_app; repeat rewrite Zlength_map; try rewrite HMAC_Zlength; try omega.
  unfold at_offset. cancel.
eapply derives_trans. apply data_at_data_at_. apply derives_refl.
Qed.