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
             `(memory_block shmd (Int.repr 64) md))
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
  unfold hmac_relate_PreInitNull; simpl.
  apply exp_right with (x:=r).
  apply exp_right with (x:=([], (Vundef, (Vundef, ([], Vundef))))).
  apply andp_right. 
    destruct h2. destruct h1. simpl in *.
    destruct Round1Final as [oSA [UPDO [XX FinDig]]]. inversion XX; subst; clear XX.
    destruct h0. simpl in *. destruct HmacUpdate as [ctx2 [UpdI XX]]. inversion XX; subst; clear XX.
    unfold  hmacInit in HmacInit. simpl in *. 
    destruct HmacInit as [IS [OS [ISHA [OSHA XX]]]].  inversion XX; subst; clear XX. 
    apply prop_right; intuition.
  cancel.
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
simpl_stackframe_of. fixup_local_var; intro c.

rename keyVal into k. rename msgVal into d.
destruct KEY as [kl key].
destruct MSG as [dl data]. simpl in *.
rename H into WrshMD. 
rewrite memory_block_isptr. normalize.
rename H into isPtrMD. rename H0 into KL. rename H1 into DL. 

forward_if  (
  PROP  (isptr c)
   LOCAL  (lvar _c t_struct_hmac_ctx_st c; temp _md md; temp _key k;
   temp _key_len (Vint (Int.repr kl)); temp _d d;
   temp _n (Vint (Int.repr dl)); gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh t_struct_hmac_ctx_st c); `(data_block Tsh key k);
   `(data_block Tsh data d); `(K_vector kv);
   `(memory_block shmd (Int.repr 64) md))).
  { (* Branch1 *) inv H. }
  { (* Branch2 *) forward. entailer!. } 
normalize. rename H into isptrC.

assert_PROP (isptr k). entailer!. 
rename H into isPtrK. 
remember (HMACabs init_s256abs init_s256abs init_s256abs) as dummyHMA.
forward_call' (c, k, kl, key, kv, dummyHMA) h0.
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
forward_call' (h0, c, d, dl, data, kv) h1.
  { rewrite H0_len512. assumption. } 
rename H into HmacUpdate. 

destruct md; try contradiction; clear isPtrMD.
assert (GTmod64: 64 < Int.modulus).
  rewrite <- initialize.max_unsigned_modulus, int_max_unsigned_eq. omega.
specialize (memory_block_size_compatible shmd (tarray tuint 16)). simpl; intros.
rewrite (H _ GTmod64); clear H.
normalize. unfold size_compatible in H. simpl in H; rename H into SizeCompat64.
specialize (memory_block_split shmd b (Int.unsigned i) 32 32); intros XX.
  rewrite Int.repr_unsigned in XX. 
  assert (32 + 32 = 64) by omega. rewrite H in XX; clear H.
  rewrite XX; clear XX.
2: omega. 2: trivial. 2: trivial. 
Focus 2. split; try omega. specialize (Int.unsigned_range i). omega.
normalize. (*GTmad64 and SizeCompat play the roles of the earlier OIR_0_md and OIR_64_md*)
 
forward_call' (h1, c, Vptr b i, shmd, kv) [dig h2]. 
simpl in H; rename H into Round1Final.

(**************Round 2*******************************)

replace_SEP 1 (`(initPre c nullval h2 key)). 
  { entailer!. eapply hmacstate_PostFinal_PreInitNull; eassumption.
  }

forward_call' (c, nullval, kl, key, kv, h2) h3. rename H into h3_init.

assert_PROP (s256a_len (absCtxt h3) = 512).
  { unfold hmacstate_. entailer. apply prop_right. 
    destruct h3; simpl in *.  
    destruct H4 as [reprMD [reprI [reprO [iShaLen oShaLen]]]].
    inversion h3_init; clear h3_init.
    destruct H4 as [oS [InnSHA [OntSHA XX]]]. inversion XX; clear XX.
    subst. assumption.
  }
rename H into H3_len512.
forward_call' (h3, c, d, dl, data, kv) h4.
  { rewrite H3_len512. assumption. }
rename H into h4_update.

forward_call' (h4, c, Vptr b (Int.repr (Int.unsigned i + 32)), shmd, kv) [dig2 h5].
simpl in H; rename H into Round2Final. simpl.

forward_call' (h5,c). destruct H as [SCc ACc].

forward.
apply (exp_right dig).
simpl_stackframe_of. normalize. clear H2. 
assert (HS: hmacSimple key data dig).
    exists h0, h1. 
    split. assumption.
    split; try assumption.
    rewrite hmacFinal_hmacFinalSimple. exists h2; assumption.
assert (Size: sizeof t_struct_hmac_ctx_st <= Int.max_unsigned).
  rewrite int_max_unsigned_eq; simpl. omega.

apply andp_right. apply prop_right. split; trivial.
  rewrite hmac_hmacSimple in HS. destruct HS. eapply hmac_sound; eassumption.
apply andp_right. apply prop_right. trivial. cancel.
rewrite sepcon_assoc. rewrite sepcon_comm.
apply sepcon_derives.
{ assert (D1: dig = HMAC256 data key).
     apply hmac_sound with (h:=h2).
     exists h0, h1. auto.
  assert (D2: dig2 = HMAC256 data key).
     eapply hmac_sound with (h:=h5).
     exists h3, h4. auto.

  rewrite (split2_data_block 32 shmd (dig ++ dig)).
  2: subst dig; rewrite app_length, HMAC_length; omega.
  entailer.
  rewrite initial_world.Zlength_app, HMAC_Zlength. 
   apply andp_right. apply prop_right; simpl.
    specialize (Int.unsigned_range i). omega. 

  rewrite firstn_app1. 2: rewrite HMAC_length; trivial.
  rewrite firstn_precise.  2: rewrite HMAC_length; trivial.
  cancel.

  rewrite skipn_app2; rewrite HMAC_length. 2: omega. 
  simpl. cancel. }
{ unfold data_block.
  rewrite Zlength_correct; simpl.
  rewrite <- memory_block_data_at_; try reflexivity. 
  2: rewrite lvar_eval_lvar with (v:=c); trivial. 
  normalize. rewrite lvar_eval_lvar with (v:=c); trivial. 
  rewrite (memory_block_data_at_ Tsh (tarray tuchar (sizeof t_struct_hmac_ctx_st))).
  apply data_at_data_at_.
  trivial.
  trivial.
  trivial. 
  destruct c; trivial. unfold align_compatible. simpl. apply Z.divide_1_l. 
  simpl. rewrite <- initialize.max_unsigned_modulus, int_max_unsigned_eq. omega. }
Qed.
