Require Import VST.floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.hmac_common_lemmas.

Require Import sha.hmac.

Require Import sha.spec_hmac.
Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.

Lemma body_hmac_simple: semax_body HmacVarSpecs HmacFunSpecs
      f_HMAC HMAC_spec.
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
rename H into KL. rename H0 into DL.
Time assert_PROP (isptr md) as isPtrMD by entailer!. (*1.3*)
Time forward_if  (
  PROP  (isptr c)
   LOCAL  (lvar _c t_struct_hmac_ctx_st c; temp _md md; temp _key k;
   temp _key_len (Vint (Int.repr kl)); temp _d d;
   temp _n (Vint (Int.repr dl)); gvars gv)
   SEP  (data_at_ Tsh t_struct_hmac_ctx_st c; data_block shk key k;
   data_block shm data d; K_vector gv;
   memory_block shmd 32 md)).
  (*3.3*)
  { (*Branch1*) exfalso. subst md. contradiction.  }
  { (* Branch2 *) Time forward. (*0.3*) fold t_struct_hmac_ctx_st. Time entailer!. (*1.9*)}
Time normalize. (*0.8*)
freeze [2;4] FR1.
assert_PROP (isptr k) as isPtrK.
{ unfold data_block. Time normalize. (*1.6 versus 2.2*) rewrite data_at_isptr with (p:=k). Time entailer!. (*1.6 versus 2.5*) }

Time forward_call (Tsh, shk, c, k, kl, key, HMACabs nil nil nil, gv). (*3*)
 { apply isptrD in isPtrK. destruct isPtrK as [kb [kofs HK]]. rewrite HK.
   unfold initPre. Time entailer!. (*0.6 versus 1.1*)
 }
freeze [1;2;3] FR2.
assert_PROP (s256a_len (absCtxt (hmacInit key)) = 512 /\
             field_compatible (Tstruct _hmac_ctx_st noattr) [] c).
  { unfold hmacstate_. Intros r. entailer!. apply H. }
destruct H as [H0_len512 FC_c].
thaw FR2.
thaw FR1.
freeze [0;3] FR3.
Time forward_call (Tsh, shm, hmacInit key, c, d, dl, data, gv). (*2.8*)
  { split3; auto. rewrite H0_len512; assumption. }

thaw FR3.
freeze [2;3] FR4.
Time forward_call (Tsh, hmacUpdate data (hmacInit key), c, md, shmd, gv). (*2.3*)
freeze [0;2;3] FR5.
forward_call (Tsh, fst (hmacFinal (hmacUpdate data (hmacInit key))), c).
freeze [0;1] FR6.
Time forward. (*4.2*)
Exists (HMAC256 data key). entailer.
thaw FR6. thaw FR5. Time cancel. (*2.2*)
thaw FR4. Time cancel. (*2.1*)
rewrite <- (hmac_sound key data). unfold hmac.
Time cancel.
unfold data_block.
  rewrite Zlength_correct; simpl.
rewrite <- memory_block_data_at_; trivial.
normalize.
assert_PROP (field_compatible (tarray tuchar (sizeof t_struct_hmac_ctx_st)) [] c).
{ eapply derives_trans; [apply data_at_local_facts |].  Time normalize. (* 4 *) }
rewrite (memory_block_data_at_ Tsh (tarray tuchar (@sizeof (@cenv_cs CompSpecs) t_struct_hmac_ctx_st))).
  2: trivial.
  eapply derives_trans. apply data_at_data_at_. apply derives_refl.
Time Qed. 