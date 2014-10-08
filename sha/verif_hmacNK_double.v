Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.

Require Import sha.hmac_NK.

Require Import sha.spec_hmacNK.
Require Import HMAC_lemmas.

Lemma body_hmac_double: semax_body HmacVarSpecs HmacFunSpecs 
      f_HMAC2 HMAC_Double_spec.
Proof.
start_function.
name key' _key.
name keylen' _key_len.
name d' _d.
name n' _n.
name md' _md.
simpl_stackframe_of.
rename keyVal into k. rename msgVal into d.
destruct KEY as [kl key].
destruct MSG as [dl data]. simpl in *.
rename H into WrshMD. 
rewrite memory_block_isptr. normalize.
rename H into isPtrMD. rename H0 into KL. rename H1 into DL. 
remember (
EX c:_,
PROP  (isptr c)
   LOCAL  (`(eq md) (eval_id _md); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr kl))) (eval_id _key_len); `(eq d) (eval_id _d);
   `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(data_at_ Tsh t_struct_hmac_ctx_st c);
   `(data_block Tsh key k); `(data_block Tsh data d); `(K_vector KV);
   `(memory_block shmd (Int.repr 64) md))) as POSTCOND.
forward_if POSTCOND.
  normalize. forward.
  simpl; intros rho. entailer.
    apply isptrD in isPtrMD. destruct isPtrMD as [b [i HH]]; rewrite HH in *.
    simpl in *. inversion H0.
  simpl in *. apply isptrD in isPtrMD. destruct isPtrMD as [b [i HH]]; subst. 
   intros rho. 
   entailer.
   
  forward. subst POSTCOND. simpl. intros rho. entailer.
   rewrite data_at__isptr. normalize.
   apply exp_right with (x:=eval_var _c t_struct_hmac_ctx_st rho).
   entailer.

subst POSTCOND.
apply extract_exists_pre. intros c. normalize. rename H into isPtrC.
eapply semax_seq'. 
frame_SEP 0 1 3.
remember (HMACabs init_s256abs init_s256abs init_s256abs) as dummyHMA.
remember (c, k, kl, key, KV, dummyHMA) as WITNESS.
forward_call WITNESS.
  assert (FR: Frame =nil).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
  subst WITNESS. entailer. cancel. unfold initPre. 
   apply isptrD in Pkey'. destruct Pkey' as [kb [kofs HK]]. subst key'.
   cancel.
after_call.
subst WITNESS. normalize. simpl. rewrite elim_globals_only'. normalize.
intros h0. normalize. rename H into HmacInit.

eapply semax_seq'. 
frame_SEP 0 2 3.
remember (h0, c, d, dl, data, KV) as WITNESS.
(*Remark on confusing error messages: if the spec of HMAC_update includes _len OF tuint
  instead of _len OF tint, the following forward_call fails, complaining that
  WITNESS is not of type hmacabs * val * val * Z * list Z * val. But it is, 
  and the error message is wrong.*)
forward_call WITNESS.
  assert (FR: Frame =nil).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
  subst WITNESS. entailer.
  apply andp_right. 2: cancel.
    unfold hmacstate_. normalize. apply prop_right. 
    assert (HH: s256a_len (absCtxt h0) = 512).
    Focus 2. destruct DL as [DL1 [DL2 DL3]]. split; trivial. split; trivial.
             rewrite HH; assumption. 
    destruct h0; simpl in *. 
    destruct H1 as [reprMD [reprI [reprO [iShaLen oShaLen]]]].
    inversion HmacInit; clear HmacInit.
    destruct H1 as [oS [InnSHA [OntSHA XX]]]. inversion XX; clear XX.
    subst. assumption.
after_call.
subst WITNESS. normalize.
unfold update_tycon. simpl. normalize.

(**** It's not quite clear to me why we need to use semax_pre here - 
  ie why normalize can't figure this out (at least partially).
  It seems exp doesn't distribute over liftx, but it should *)
eapply semax_pre with (P':= EX  x : hmacabs, 
   PROP  ()
   LOCAL  (tc_environ Delta; tc_environ Delta; `(eq md) (eval_id _md);
   `(eq k) (eval_id _key); `(eq (Vint (Int.repr kl))) (eval_id _key_len);
   `(eq d) (eval_id _d); `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP (`(fun a : environ =>
      (PROP  (hmacUpdate data h0 x)
       LOCAL ()
       SEP  (`(K_vector KV); `(hmacstate_ x c); `(data_block Tsh data d))) a)
      globals_only; `(initPostKey k key); `(memory_block shmd (Int.repr 64) md))).
  entailer. rename x into h1. apply exp_right with (x:=h1).
  entailer. 
(********************************************************)
apply extract_exists_pre. intros h1. normalize. simpl. normalize.
rename H into HmacUpdate.

rewrite (split_memory_block 32). 2: omega. 2: trivial. simpl. 
normalize. rename H into OIR_0_md. rename H0 into OIR_64_md.
 
eapply semax_seq'. 
frame_SEP 3 2 0.
remember (h1, c, md, shmd, KV) as WITNESS.
forward_call WITNESS.
  assert (FR: Frame =nil).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
  subst WITNESS. entailer.
after_call.
subst WITNESS. normalize.
unfold update_tycon. simpl. normalize. 

(**** Again, distribute EX over lift*)
eapply semax_pre with (P':=
      EX dig : list Z,
  (PROP  ()
   LOCAL  (tc_environ Delta; tc_environ Delta; tc_environ Delta;
   `(eq md) (eval_id _md); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr kl))) (eval_id _key_len); `(eq d) (eval_id _d);
   `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(fun a : environ =>
      (EX  h2 : hmacabs,
       (PROP  (hmacFinal h1 dig h2)
        LOCAL ()
        SEP  (`(K_vector KV); `(hmacstate_PostFinal h2 c);
        `(data_block shmd dig md))) a)) globals_only;
   `(memory_block shmd (Int.repr 32) (offset_val (Int.repr 32) md));
   `(data_block Tsh data d); `(initPostKey k key)))).
   entailer.
   apply exp_right with (x1:=x). entailer. 
   apply exp_right with (x1:=x0). entailer. 
apply extract_exists_pre. intros dig. normalize.
eapply semax_pre with (P':=
      EX h2 : hmacabs,
  (PROP  ()
   LOCAL  (tc_environ Delta; tc_environ Delta; tc_environ Delta;
   `(eq md) (eval_id _md); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr kl))) (eval_id _key_len); `(eq d) (eval_id _d);
   `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(fun a : environ =>
      (PROP  (hmacFinal h1 dig h2)
       LOCAL ()
       SEP  (`(K_vector KV); `(hmacstate_PostFinal h2 c);
       `(data_block shmd dig md))) a) globals_only;
   `(memory_block shmd (Int.repr 32) (offset_val (Int.repr 32) md));
   `(data_block Tsh data d); `(initPostKey k key)))).
   entailer. 
   apply exp_right with (x0:=x). entailer. 
apply extract_exists_pre. intros h2. normalize. simpl. normalize.
rename H into Round1Final.

(**************Round 2*******************************)
eapply semax_pre with (P':=
  (PROP  ()
   LOCAL  (tc_environ Delta; 
   `(eq md) (eval_id _md); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr kl))) (eval_id _key_len); `(eq d) (eval_id _d);
   `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP  (`(K_vector KV);
   `(initPre c nullval h2 key);
   `(data_block shmd dig md);
   `(memory_block shmd (Int.repr 32) (offset_val (Int.repr 32) md));
   `(data_block Tsh data d); `(initPostKey k key)))).
{ entailer. cancel. 
  unfold hmacstate_PostFinal, hmac_relate_PostFinal, hmacstate_PreInitNull; normalize.
  unfold hmac_relate_PreInitNull; simpl.
  apply exp_right with (x:=r).
  apply exp_right with (x:=([], (Vundef, (Vundef, ([], Vundef))))).
  apply andp_right. 
  { destruct h2. destruct h1. simpl in *.
    destruct Round1Final as [oSA [UPDO [XX FinDig]]]. inversion XX; subst; clear XX.
    destruct h0. simpl in *. destruct HmacUpdate as [ctx2 [UpdI XX]]. inversion XX; subst; clear XX.
    unfold  hmacInit in HmacInit. simpl in *. 
    destruct HmacInit as [IS [OS [ISHA [OSHA XX]]]].  inversion XX; subst; clear XX. 
    apply prop_right; intuition.     
(*    destruct H8 as [i [I1 [I2 I3]]]. exists i; intuition.*)
  }
  cancel.
}

eapply semax_seq'. 
frame_SEP 0 1.
remember (c, nullval, kl, key, KV, h2) as WITNESS.
forward_call WITNESS.
  assert (FR: Frame =nil).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
  subst WITNESS. entailer. 
after_call.
subst WITNESS. normalize. simpl. rewrite elim_globals_only'. normalize.
intros h3. normalize. rename H into h3_init.

eapply semax_seq'. 
frame_SEP 0 1 4.
remember (h3, c, d, dl, data, KV) as WITNESS.
forward_call WITNESS.
  assert (FR: Frame =nil).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
  subst WITNESS. entailer.
  apply andp_right. 2: cancel.
    unfold hmacstate_. normalize. apply prop_right. 
    assert (HH: s256a_len (absCtxt h3) = 512).
    Focus 2. destruct DL as [DL1 [DL2 DL3]]. split; trivial. split; trivial.
             rewrite HH; assumption. 
    destruct h3; simpl in *. 
    destruct H1 as [reprMD [reprI [reprO [iShaLen oShaLen]]]].
    inversion h3_init; clear h3_init.
    destruct H1 as [oS [InnSHA [OntSHA XX]]]. inversion XX; clear XX.
    subst. assumption.
after_call.
subst WITNESS. normalize.
unfold update_tycon. simpl. normalize.

eapply semax_pre with (P':=EX  x : hmacabs, 
  (PROP  ()
   LOCAL  (tc_environ Delta; tc_environ Delta; tc_environ Delta;
   `(eq md) (eval_id _md); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr kl))) (eval_id _key_len); `(eq d) (eval_id _d);
   `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(fun a : environ =>
      (PROP  (hmacUpdate data h3 x)
       LOCAL ()
       SEP  (`(K_vector KV); `(hmacstate_ x c); `(data_block Tsh data d))) a)
      globals_only; `(data_block shmd dig md);
   `(memory_block shmd (Int.repr 32) (offset_val (Int.repr 32) md));
   `(initPostKey k key)))).
  entailer. rename x into h4. apply exp_right with (x:=h4).
  entailer. 
(********************************************************)
apply extract_exists_pre. intros h4. normalize. simpl. normalize.
rename H into h4_update.

eapply semax_seq'. 
frame_SEP 0 1 4.
remember (h4, c, offset_val (Int.repr 32) md, shmd, KV) as WITNESS.
forward_call WITNESS.
  assert (FR: Frame =nil).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
  subst WITNESS. entailer. cancel.
after_call.
subst WITNESS. normalize.
unfold update_tycon. simpl. normalize. 

(**** Again, distribute EX over lift*)
eapply semax_pre with (P':=
      EX dig2 : list Z,
  (PROP  ()
   LOCAL  (tc_environ Delta; tc_environ Delta; tc_environ Delta;
   tc_environ Delta; `(eq md) (eval_id _md); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr kl))) (eval_id _key_len); `(eq d) (eval_id _d);
   `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(fun a : environ =>
      (EX  x0 : hmacabs,
       (PROP  (hmacFinal h4 dig2 x0)
        LOCAL ()
        SEP  (`(K_vector KV); `(hmacstate_PostFinal x0 c);
        `(data_block shmd dig2 (offset_val (Int.repr 32) md)))) a)) globals_only;
   `(data_block Tsh data d); `(data_block shmd dig md); `(initPostKey k key)))).
   entailer.
   apply exp_right with (x1:=x). entailer. 
   apply exp_right with (x1:=x0). entailer. 
apply extract_exists_pre. intros dig2. normalize.
eapply semax_pre with (P':=
      EX h5 : hmacabs,
  (PROP  ()
   LOCAL  (tc_environ Delta; tc_environ Delta; tc_environ Delta;
   tc_environ Delta; `(eq md) (eval_id _md); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr kl))) (eval_id _key_len); `(eq d) (eval_id _d);
   `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(fun a : environ =>
      (PROP  (hmacFinal h4 dig2 h5)
       LOCAL ()
       SEP  (`(K_vector KV); `(hmacstate_PostFinal h5 c);
       `(data_block shmd dig2 (offset_val (Int.repr 32) md)))) a)
      globals_only; `(data_block Tsh data d); `(data_block shmd dig md);
   `(initPostKey k key)))).
   entailer. 
   apply exp_right with (x0:=x). entailer. 
apply extract_exists_pre. intros h5. normalize. simpl. normalize.
rename H into Round2Final.

eapply semax_seq'.
frame_SEP 1.
remember (h5,c) as WITNESS.
forward_call WITNESS.
  assert (FR: Frame =nil).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
  subst WITNESS. entailer.
after_call.
subst WITNESS. normalize.
unfold update_tycon. simpl. normalize. simpl. normalize.
  rename H into SCc. rename H0 into ACc.

forward.
apply exp_right with (x:=dig).
simpl_stackframe_of. normalize. clear H0. 
assert (HS: hmacSimple key data dig).
    exists h0, h1. 
    split. destruct KL as [KL1 [KLb KLc]].
           (*rewrite KL1.*) assumption.
    split; try assumption.
    rewrite hmacFinal_hmacFinalSimple. exists h2; assumption.
assert (Size: sizeof t_struct_hmac_ctx_st <= Int.max_unsigned).
  rewrite int_max_unsigned_eq; simpl. omega.
apply andp_right. apply prop_right. split; trivial.
apply andp_right. apply prop_right. trivial. cancel.
rewrite sepcon_assoc. rewrite sepcon_comm.
apply sepcon_derives.
  assert (D1: dig = HMAC_FUN.HMAC data key).
     apply hmac_sound with (h:=h2).
     exists h0, h1. auto.
  assert (D2: dig2 = HMAC_FUN.HMAC data key).
     eapply hmac_sound with (h:=h5).
     exists h3, h4. auto.

  rewrite (split2_data_block 32 shmd (dig ++ dig)).
  2: subst dig; rewrite app_length, HMAC_length; omega.
  entailer.
  rewrite initial_world.Zlength_app, HMAC_Zlength. 
   apply andp_right. apply prop_right; assumption. 

  rewrite firstn_app1. 2: rewrite HMAC_length; trivial.
  rewrite firstn_precise.  2: rewrite HMAC_length; trivial.
  cancel.

  rewrite skipn_app2; rewrite HMAC_length. 2: omega. 
  simpl. cancel.

unfold data_block.
  rewrite Zlength_correct; simpl.
rewrite <- memory_block_data_at_; try reflexivity. 
rewrite memory_block_array_tuchar. 
normalize. clear H0. 
  apply andp_right.
    apply prop_right. trivial. cancel.
simpl; omega.
Qed.
