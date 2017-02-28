Require Import floyd.proofauto.
Import ListNotations.
Local Open Scope logic.

Require Import sha.hmac_common_lemmas.

Require Import sha.hkdf.
Require Import sha.spec_hmac.
Require Import sha.spec_hkdf.
Require Import sha.hkdf_functional_prog.

Definition vv :reptype (Tarray tuchar (64 - 32) noattr) := list_repeat 64 Vundef.

Lemma body_hkdf: semax_body Hkdf_VarSpecs Hkdf_FunSpecs 
       f_HKDF HKDF_spec.
Proof.
start_function. 
rename lvar0 into prk. rename lvar1 into plen.
rename H into lenSalt. rename H0 into lenSecret.
rename H1 into lenInfoA. rename H2 into lenInfoB. rename H3 into lenInfoC.
rename H4 into OlenA. rename H5 into OlenB.
assert_PROP (isptr prk /\ field_compatible (tarray tuchar 64) [] prk) by entailer!. destruct H as [Pprk FCprk].
destruct prk; try contradiction. clear Pprk.
assert_PROP (isptr plen /\ field_compatible (tuint) [] plen) by entailer. destruct H as [Pplen FCplen].

unfold data_at_, field_at_.
rewrite field_at_data_at. simpl.
rewrite field_at_data_at. unfold tarray. simpl.
assert (JM: JMeq (default_val (Tarray tuchar 64 noattr)) (sublist 0 64 vv)).
{ unfold vv. rewrite sublist_list_repeat with (k:=64); try omega. simpl. apply JMeq_refl. }
erewrite  split2_data_at_Tarray with (n1:=32). 
2: omega.
3: apply JMeq_refl.
3: apply JMeq_refl.
2: eassumption.
normalize. simpl.

freeze [1; 5; 7] FR1.

forward_call (Vptr b i, plen, secret, SECRET, salt, SALT, kv, Tsh).
{ assert (Frame = [FRZL FR1]). subst Frame; reflexivity.
  subst Frame. simpl. cancel.
  rewrite field_address_offset by auto with field_compatible. simpl. rewrite Int.add_zero.
  rewrite field_address_offset; trivial.
    simpl. rewrite isptr_offset_val_zero; trivial.
  cancel. eapply derives_trans. apply data_at_memory_block. simpl. trivial. }

forward.

assert (Zlength (HKDF_extract (CONT SALT) (CONT SECRET))=32) as ZlengthExtract by apply HMAC_Zlength.
thaw FR1. freeze [1; 2; 5] FR2.

forward_call (out, olen, 
              Vptr b i,
              Build_DATA 32
                  (HKDF_extract (CONT SALT) (CONT SECRET)),
              info, INFO, kv, shmd).
{ simpl. cancel. }
{ simpl. repeat split; try solve [trivial]; omega. }

apply extract_exists_pre. intros x. destruct x. Intros. rename H into EXPAND_RES. simpl in *.
unfold expand_out_post, digest_len in EXPAND_RES. rewrite if_false in EXPAND_RES; try omega.
replace (olen + 32 - 1)%Z with (olen + 31)%Z in EXPAND_RES by omega.

destruct (zlt 255 ((olen + 31) / 32)); inv EXPAND_RES.
+ forward_if
  (PROP ( )
   LOCAL (temp _t'3 (Vint (Int.repr 1));
   lvar _prk_len tuint plen; lvar _prk (Tarray tuchar 64 noattr) (Vptr b i); 
   temp _out_key out; temp _out_len (Vint (Int.repr olen)); temp _salt salt;
   temp _salt_len (Vint (Int.repr (LEN SALT))); temp _secret secret;
   temp _secret_len (Vint (Int.repr (LEN SECRET))); temp _info info;
   temp _info_len (Vint (Int.repr (LEN INFO))); gvar sha._K256 kv)
   SEP (spec_sha.K_vector kv; spec_sha.data_block Tsh (CONT INFO) info;
   spec_sha.data_block Tsh (HKDF_extract (CONT SALT) (CONT SECRET)) (Vptr b i);
   memory_block shmd olen out; FRZL FR2; data_at Tsh tuint (Vint (Int.repr 32)) plen)).
  { congruence. }
  { forward. entailer!. }

  forward_if (`FF).
  { forward. Exists plen. Exists (Vptr b i). Exists 0. entailer!.
    thaw FR2. erewrite (split2_data_at__Tarray_tuchar Tsh 64 32); simpl; trivial; try omega.
    rewrite field_address_offset by auto with field_compatible. simpl. rewrite Int.add_zero.
    cancel.
    unfold spec_sha.data_block. rewrite ZlengthExtract. entailer!. }
  { discriminate. } 
  apply semax_ff.

+ forward_if (
  (PROP ( )
   LOCAL (lvar _prk_len tuint plen; lvar _prk (Tarray tuchar 64 noattr) (Vptr b i); 
   temp _out_key out; temp _t'3 (Vint (Int.repr 0)); temp _out_len (Vint (Int.repr olen)); temp _salt salt;
   temp _salt_len (Vint (Int.repr (LEN SALT))); temp _secret secret;
   temp _secret_len (Vint (Int.repr (LEN SECRET))); temp _info info;
   temp _info_len (Vint (Int.repr (LEN INFO))); gvar sha._K256 kv)
   SEP (spec_sha.K_vector kv; spec_sha.data_block Tsh (CONT INFO) info;
   spec_sha.data_block Tsh (HKDF_extract (CONT SALT) (CONT SECRET)) (Vptr b i);
   spec_sha.data_block shmd (HKDF_expand (HKDF_extract (CONT SALT) (CONT SECRET)) (CONT INFO) olen) out;
   FRZL FR2; data_at Tsh tuint (Vint (Int.repr 32)) plen))). 
  { congruence. }
  { forward. entailer!. }

  forward_if (
  (PROP ( )
   LOCAL (lvar _prk_len tuint plen; lvar _prk (Tarray tuchar 64 noattr) (Vptr b i); 
   temp _out_key out; temp _out_len (Vint (Int.repr olen));
   temp _salt salt; temp _salt_len (Vint (Int.repr (LEN SALT))); temp _secret secret;
   temp _secret_len (Vint (Int.repr (LEN SECRET))); temp _info info;
   temp _info_len (Vint (Int.repr (LEN INFO))); gvar sha._K256 kv)
   SEP (spec_sha.K_vector kv; spec_sha.data_block Tsh (CONT INFO) info;
   spec_sha.data_block Tsh (HKDF_extract (CONT SALT) (CONT SECRET)) (Vptr b i);
   spec_sha.data_block shmd (HKDF_expand (HKDF_extract (CONT SALT) (CONT SECRET)) (CONT INFO) olen) out;
   FRZL FR2; data_at Tsh tuint (Vint (Int.repr 32)) plen))).
  { elim H; trivial. }
  { forward. entailer!. }
  forward. Exists plen (Vptr b i) 1. entailer!. thaw FR2. cancel.   
  erewrite (split2_data_at__Tarray_tuchar Tsh 64 32); simpl; trivial; try omega.
  rewrite field_address_offset by auto with field_compatible. simpl. rewrite Int.add_zero.
  cancel.
  unfold spec_sha.data_block. rewrite ZlengthExtract. entailer!.
Time Qed. (*Finished transaction in 16.671 secs (15.484u,0.s) (successful)*)