(*In this file, we verify the additional function hmac2, that we added to the c file
  in order to exercise the reuse of a key for several messages. The function calls
  hmac twice, (on the same message, using the same key) and puts the resulting
  (identical) digests side by side in a suitably large array.*)

Require Import VST.floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Require Import sha.hmac.

Require Import sha.spec_hmac.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.

Definition HMAC_Double_spec :=
  DECLARE _HMAC
   WITH keyVal: val, KEY:DATA,
        msgVal: val, MSG:DATA,
        sh: share, shmd: share, md: val, gv: globals
   PRE [ _key OF tptr tuchar,
         _key_len OF tint,
         _d OF tptr tuchar,
         _n OF tint,
         _md OF tptr tuchar ]
         PROP (readable_share sh; writable_share shmd;
               has_lengthK (LEN KEY) (CONT KEY);
               has_lengthD 512 (LEN MSG) (CONT MSG))
         LOCAL (temp _md md; temp _key keyVal;
                temp _key_len (Vint (Int.repr (LEN KEY)));
                temp _d msgVal;
                temp _n (Vint (Int.repr (LEN MSG)));
                gvars gv)
         SEP(data_block sh (CONT KEY) keyVal;
             data_block sh (CONT MSG) msgVal;
             K_vector gv;
             memory_block shmd 64 md)
  POST [ tptr tuchar ] 
         EX digest:_, 
          PROP (digest = HMAC256 (CONT MSG) (CONT KEY))
          LOCAL (temp ret_temp md)
          SEP(K_vector gv;
              data_block shmd (digest++digest) md;
              initPostKey sh keyVal (CONT KEY);
              data_block sh (CONT MSG) msgVal).

Definition n324 := 324%Z.
Opaque n324.

Lemma body_hmac_double: semax_body HmacVarSpecs HmacFunSpecs 
      f_HMAC2 HMAC_Double_spec.
Proof.
start_function.
name key' _key.
name keylen' _key_len.
name d' _d.
name n' _n.
name md' _md.
rename v_c into c.
rename keyVal into k. rename msgVal into d.
destruct KEY as [kl key].
destruct MSG as [dl data]. simpl CONT in *; simpl LEN in *.
rewrite memory_block_isptr. normalize.
rename H into KL. rename H0 into DL.

forward_if (isptr c).
  { (* Branch1 *) exfalso. subst md. contradiction.  }
  { (* Branch2 *) forward. entailer. }
Intros.
assert_PROP (isptr k).
{ unfold data_block. normalize. rewrite data_at_isptr with (p:=k). entailer. } (*Issue: used to be solved just by entailer *)
rename H into Pk.
forward_call (Tsh, sh, c, k, kl, key, HMACabs nil nil nil, gv).
  { unfold initPre.
    destruct k; try contradiction.
    unfold t_struct_hmac_ctx_st.
    entailer!.
  }

assert_PROP (s256a_len (absCtxt (hmacInit key)) = 512) as H0_len512.
  { unfold hmacstate_. Intros r. apply prop_right. apply H. }
remember (hmacInit key) as h0.
forward_call (Tsh, sh, h0, c, d, dl, data, gv).
  { rewrite H0_len512. split3; auto. }
apply isptrD in Pmd. destruct Pmd as [b [i Pmd]]. rewrite Pmd in *.
assert (GTmod64: 64 < Ptrofs.modulus).
  rewrite <- initialize.max_unsigned_modulus, ptrofs_max_unsigned_eq. omega.
specialize (memory_block_size_compatible shmd (tarray tuint 16)). simpl; intros.
rewrite H (*_ GTmod64)*); clear H.
normalize. unfold size_compatible in H. simpl in H; rename H into SizeCompat64.
specialize (memory_block_split shmd b (Ptrofs.unsigned i) 32 32); intros XX.
  rewrite Ptrofs.repr_unsigned in XX.
  assert (32 + 32 = 64) by omega. rewrite H in XX; clear H.
  rewrite XX; trivial; clear XX.
2: destruct (Ptrofs.unsigned_range i); omega.
clear GTmod64.
flatten_sepcon_in_SEP.

forward_call (Tsh, hmacUpdate data h0, c, Vptr b i, shmd, gv).
simpl.

(**************Round 2*******************************)
remember (hmacFinal (hmacUpdate data h0)) as RND1.
destruct RND1 as [h2 dig].
replace_SEP 1 (initPre Tsh sh c nullval h2 kl key).
  { entailer!. eapply hmacstate_PostFinal_PreInitNull.
    symmetry in HeqRND1. apply HeqRND1. }
forward_call (Tsh, sh, c, nullval, kl, key, h2, gv).
simpl; normalize.

assert_PROP (s256a_len (absCtxt (hmacInit key)) = 512).
  { unfold hmacstate_. entailer!. }
rename H into H3_len512.
forward_call (Tsh, sh, hmacInit key, c, d, dl, data, gv).
  { rewrite H3_len512. split3; auto. }

assert_PROP (field_compatible (Tstruct _hmac_ctx_st noattr) [] c)
  as FC_c by (unfold hmacstate_; Intros r;  entailer!).
forward_call (Tsh, hmacUpdate data (hmacInit key), c, Vptr b (Ptrofs.repr (Ptrofs.unsigned i + 32)), shmd, gv).
remember (hmacFinal (hmacUpdate data (hmacInit key))) as RND2.
destruct RND2 as [h5 dig2].
simpl.

forward_call (Tsh, h5,c).
match goal with |- context [data_block  Tsh ?A c] =>
  change A with (list_repeat (Z.to_nat n324) Byte.zero)
end.
forward.
clear H2.
pose proof (HMAC_Zlength data key).
rewrite <- (hmac_sound key data) in *. unfold hmac in *.
rewrite <- HeqRND2 in HeqRND1. inv HeqRND1.
rewrite <- HeqRND2 in *. simpl in *.
Exists dig2.
unfold data_block at 1. simpl. entailer!.
rewrite <- memory_block_data_at_ by auto.
change (sizeof (Tstruct _hmac_ctx_st noattr))
   with (sizeof (tarray tuchar (Zlength (list_repeat (Z.to_nat n324) 0)))).
rewrite memory_block_data_at_ by auto.
cancel.

assert (FC_b: field_compatible (Tarray tuchar 64 noattr) [] (Vptr b i)).
{
  red. intuition.
  simpl.
  constructor.
  intros.
  econstructor.
  + reflexivity.
  + apply Z.divide_1_l.
}
rewrite (split2_data_block 32 _ (dig2 ++ dig2))
 by (autorewrite with sublist; omega).
autorewrite with sublist.
cancel.
apply derives_refl'.
  f_equal.
  rewrite field_address0_offset  by auto with field_compatible.
  reflexivity.
Qed.
