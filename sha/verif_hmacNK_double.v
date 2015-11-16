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
       apply sepcon_valid_pointer2. apply memory_block_valid_ptr. auto. omega.
       apply valid_pointer_zero. }
  { (* Branch1 *) exfalso. subst md. contradiction.  }
  { (* Branch2 *) forward. entailer. } 
normalize. 
assert_PROP (isptr k).
{ unfold data_block. normalize. rewrite data_at_isptr with (p:=k). entailer. } (*Issue: used to be solved just by entailer *) 
assert_PROP (isptr k). entailer. 
rename H into Pk. 
remember (HMACabs init_s256abs init_s256abs init_s256abs) as dummyHMA.
forward_call (c, k, kl, key, kv, dummyHMA) h0.
  { unfold initPre.
    destruct k; try contradiction.
    entailer!.
  }
rename H into HmacInit. normalize.

assert_PROP (s256a_len (absCtxt h0) = 512) as H0_len512.
  { unfold hmacstate_. Intros r. apply prop_right.
    destruct h0; simpl in *.  
    destruct H as [reprMD [reprI [reprO [iShaLen oShaLen]]]].
    inversion HmacInit; clear HmacInit.
    destruct H as [oS [InnSHA [OntSHA XX]]]. inversion XX; clear XX.
    subst. assumption.
  }

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

replace_SEP 1 (`(initPre c nullval h2 kl key)). 
  { entailer. eapply hmacstate_PostFinal_PreInitNull; eassumption.
  }

forward_call (c, nullval, kl, key, kv, h2) h3. rename H into h3_init.

assert_PROP (s256a_len (absCtxt h3) = 512).
  { unfold hmacstate_. entailer. apply prop_right. 
    destruct h3; simpl in *.  
    destruct H7 as [reprMD [reprI [reprO [iShaLen oShaLen]]]].
    inversion h3_init; clear h3_init.
    destruct H7 as [oS [InnSHA [OntSHA XX]]]. inversion XX; clear XX.
    subst ctx iSha oSha. assumption.
  }
rename H into H3_len512.
forward_call (h3, c, d, dl, data, kv) h4.
  { rewrite H3_len512. assumption. }
rename H into h4_update.

assert_PROP (field_compatible (Tstruct _hmac_ctx_st noattr) [] c)
  as FC_c by (unfold hmacstate_; entailer).
simpl.
Intros.

forward_call (h4, c, Vptr b (Int.repr (Int.unsigned i + 32)), shmd, kv) [dig2 h5].
simpl in H; rename H into Round2Final. simpl.

forward_call (h5,c).
Definition n324 := 324%Z.
Opaque n324.
match goal with |- context [data_block  Tsh ?A c] =>
  change A with (list_repeat (Z.to_nat n324) 0)
end.
forward.
clear H2.

assert (HS: hmacSimple key data dig).
    exists h0, h1. 
    split. assumption.
    split; try assumption.
    rewrite hmacFinal_hmacFinalSimple. exists h2; assumption.
apply hmacSimple_sound in HS.
assert (HS2: hmacSimple key data dig2).
    exists h3, h4. 
    split. assumption.
    split; try assumption.
    rewrite hmacFinal_hmacFinalSimple. exists h5; assumption.
  apply hmacSimple_sound in HS2. subst dig2.
Exists c dig.
unfold data_block at 1. simpl.
entailer!.
clear H4.
rewrite <- memory_block_data_at_ by auto.
change (sizeof cenv_cs (Tstruct _hmac_ctx_st noattr))
   with (sizeof cenv_cs (tarray tuchar (Zlength (list_repeat (Z.to_nat n324) 0)))).
rewrite memory_block_data_at_ by auto.
cancel.


assert (FC_b: field_compatible (Tarray tuchar 64 noattr) [] (Vptr b i)).
  red. intuition. apply Z.divide_1_l.

pose proof (HMAC_Zlength data key).
rewrite (split2_data_block 32 _ (HMAC256 data key ++ HMAC256 data key))
 by (autorewrite with sublist; omega).
autorewrite with sublist.
cancel.
apply derives_refl'.
f_equal.
rewrite field_address0_offset.
reflexivity.
rewrite H4. simpl.
auto with field_compatible.
Qed.