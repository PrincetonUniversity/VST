Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.

Require Import sha.hmac091c.

Require Import sha.spec_hmac.
Require Import vst_lemmas.
Require Import hmac_pure_lemmas.
Require Import hmac_common_lemmas.
Require Import sha.HMAC_functional_prog.

Require Import Blist.
Require Import HMAC_equivalence.
Require Import ByteBitRelations.
Require Import HMAC_isPRF.
Require Import ShaInstantiation.

Lemma key_vector l:
  length (bytesToBits (HP.HMAC_SHA256.mkKey l)) = b.
Proof. rewrite bytesToBits_len, hmac_common_lemmas.mkKey_length; reflexivity. Qed.

Definition mkCont (l:list Z) : HMAC_spec_abstract.HMAC_Abstract.Message (fun x => x=bytesToBits l /\ NPeano.divide 8 (length x)).
eapply exist. split. reflexivity. 
rewrite bytesToBits_len. exists (length l). trivial.
Qed.

Definition bitspec KEY MSG :=
  Vector.to_list ( HMAC_spec.HMAC h_v iv_v (HMAC_spec_abstract.HMAC_Abstract.wrappedSAP _ _ splitAndPad_v)
                      fpad_v opad_v ipad_v
                      (of_list_length _ (key_vector (CONT KEY)))
                      (mkCont (CONT MSG))).

Definition CRYPTO P (A : Comp.OracleComp (HMAC_spec_abstract.HMAC_Abstract.Message P)
                                       (Bvector.Bvector c) bool) 
                  (A_wf : DistSem.well_formed_oc A):=
           forall (HypP:forall m : Blist, P m -> NPeano.divide 8 (length m))
                  tau eps sig, h_PRF A tau ->
                               h_star_WCR A eps ->
                               dual_h_RKA A sig ->
  isPRF (Comp.Rnd (HMAC_PRF.b c p))
    (Comp.Rnd c)
    (HMAC_PRF.HMAC h_v iv_v (HMAC_spec_abstract.HMAC_Abstract.wrappedSAP _ _ splitAndPad_v) fpad_v opad_v ipad_v)
    (Message_eqdec P)
    (EqDec.Bvector_EqDec c)
    (Rat.ratAdd (Rat.ratAdd tau eps) sig) A.

Definition HMAC_crypto :=
  DECLARE _HMAC
   WITH keyVal: val, KEY:DATA,
        msgVal: val, MSG:DATA,
        KV:val, shmd: share, md: val
   PRE [ _key OF tptr tuchar,
         _key_len OF tint,
         _d OF tptr tuchar,
         _n OF tint,
         _md OF tptr tuchar ]
         PROP (writable_share shmd; 
               has_lengthK (LEN KEY) (CONT KEY);
               has_lengthD 512 (LEN MSG) (CONT MSG))
         LOCAL (`(eq md) (eval_id _md); 
                `(eq keyVal) (eval_id _key);
                `(eq (Vint (Int.repr (LEN KEY)))) (eval_id _key_len);
                `(eq msgVal) (eval_id _d);
                `(eq (Vint (Int.repr (LEN MSG)))) (eval_id _n);
                `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
         SEP(`(data_block Tsh (CONT KEY) keyVal);
             `(data_block Tsh (CONT MSG) msgVal);
             `(K_vector KV);
             `(memory_block shmd (Int.repr 32) md))
  POST [ tvoid ] 
         EX digest:_, 
          PROP (bytesToBits digest = bitspec KEY MSG /\ 
                forall P A Awf, CRYPTO P A Awf)
          LOCAL ()
          SEP(`(K_vector KV);
              `(data_block shmd digest md);
              `(initPostKey keyVal (CONT KEY) );
              `(data_block Tsh (CONT MSG) msgVal)).

Lemma body_hmac_simple: semax_body HmacVarSpecs HmacFunSpecs 
      f_HMAC HMAC_crypto.
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
(*NEW: crypto proof requires that we first extract isbyteZ key*)
apply semax_pre with (P':=PROP  (Forall isbyteZ key)
   LOCAL  (`(eq md) (eval_id _md); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr kl))) (eval_id _key_len); `(eq d) (eval_id _d);
   `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(data_at_ Tsh t_struct_hmac_ctx_st) (eval_var _c t_struct_hmac_ctx_st);
   `(data_block Tsh key k); `(data_block Tsh data d); `(K_vector KV);
   `(memory_block shmd (Int.repr 32) md))).
  entailer. normalize. rename H2 into isbyteZ_Key.
rename H into isPtrMD. rename H0 into KL. rename H1 into DL. 
forward_if  (EX c:_,
  PROP  (isptr c)
   LOCAL  (`(eq md) (eval_id _md); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr kl))) (eval_id _key_len); `(eq d) (eval_id _d);
   `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(data_at_ Tsh t_struct_hmac_ctx_st c);
   `(data_block Tsh key k); `(data_block Tsh data d); `(K_vector KV);
   `(memory_block shmd (Int.repr 32) md))).
  apply isptrD in isPtrMD. destruct isPtrMD as [b [i HH]]; rewrite HH in *.
    forward; entailer.
   
  forward. entailer.
   rewrite data_at__isptr. 
   apply exp_right with (x:=eval_var _c t_struct_hmac_ctx_st rho).
   entailer.
apply extract_exists_pre. intros c. normalize. rename H into isPtrC.

eapply semax_seq'. 
myframe_SEP'' (cons 0 (cons 1 (cons 3 (@nil Z)))).
remember (HMACabs init_s256abs init_s256abs init_s256abs Z0 nil) as dummyHMA.
remember (c, k, kl, key, KV, dummyHMA) as WITNESS.
forward_call WITNESS.
  assert (FR: Frame =nil).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
  subst WITNESS. entailer. cancel. unfold initPre. 
   apply isptrD in Pkey'. destruct Pkey' as [kb [kofs HK]]. subst key'.
   cancel.
after_call.
subst WITNESS. normalize. simpl.

apply semax_pre with (P':= EX  h : hmacabs,
  (PROP  (hmacInit key h)
   LOCAL  (tc_environ Delta; `(eq md) (eval_id _md); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr kl))) (eval_id _key_len); `(eq d) (eval_id _d);
   `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
   (`(hmacstate_ h c); `(initPostKey k key); `(K_vector KV);
    `(data_block Tsh data d);
    `(memory_block shmd (Int.repr 32) md)))).
  entailer. apply (exp_right h); entailer.
apply extract_exists_pre; intros h0. normalize. rename H into HmacInit.

eapply semax_seq'. 
myframe_SEP'' (cons 0 (cons 2 (cons 3 (@nil Z)))). 
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
    destruct H1 as [reprMD [reprI [reprO [iShaLen [oShaLen [K [i [KL1 [KL2 KL3]]]]]]]]].
    inversion HmacInit; clear HmacInit.
    destruct H1 as [oS [InnSHA [OntSHA XX]]]. inversion XX; clear XX.
    subst.
      unfold innerShaInit in InnSHA. inversion InnSHA; clear InnSHA.
      simpl in *. subst. unfold HP.HMAC_SHA256.mkArgZ, HP.HMAC_SHA256.mkArg in H10.
      assert (Zlength (map Byte.unsigned
        (map (fun p : byte * byte => Byte.xor (fst p) (snd p))
           (combine (map Byte.repr (HP.HMAC_SHA256.mkKey key)) (HP.HMAC_SHA256.sixtyfour HP.Ipad))))
        = Zlength (intlist_to_Zlist blocks ++ newfrag)).
        rewrite H10; reflexivity.
     clear H10.
     rewrite Zlength_correct in *. rewrite map_length in H1. 
     rewrite Zlength_correct in *. rewrite map_length, combine_length in H1.
     rewrite app_length in H1.
     rewrite map_length, mkKey_length in H1.
     unfold HP.SHA256.BlockSize, HP.HMAC_SHA256.sixtyfour in H1.
     rewrite length_list_repeat, length_intlist_to_Zlist in H1. unfold WORD.
     rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z.mul_comm in H1. simpl in H1.
     unfold bitlength. repeat rewrite Zlength_correct. unfold WORD. rewrite <- H1. simpl. trivial. 
after_call.
subst WITNESS. normalize. simpl.

eapply semax_pre with (P':=EX  x : hmacabs,
  (PROP  (hmacUpdate data h0 x)
   LOCAL  (tc_environ Delta; `(eq md) (eval_id _md);
   `(eq k) (eval_id _key); `(eq (Vint (Int.repr kl))) (eval_id _key_len);
   `(eq d) (eval_id _d); `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP (`(K_vector KV); `(hmacstate_ x c); `(data_block Tsh data d);
        `(initPostKey k key); `(memory_block shmd (Int.repr 32) md)))).
   entailer. apply (exp_right x); entailer.
apply extract_exists_pre; intros h1. normalize. rename H into HmacUpdate.

eapply semax_seq'. 
myframe_SEP'' (cons 0 (cons 1 (cons 4 (@nil Z)))).
forward_call (h1, c, md, shmd, KV).
  assert (FR: Frame =nil).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
  entailer. cancel. 
after_call.
simpl.

eapply semax_pre with (P':=
      EX  x : list Z, EX  x0 : hmacabs,
       (PROP  (hmacFinal h1 x x0)
   LOCAL  (tc_environ Delta; 
   `(eq md) (eval_id _md); `(eq k) (eval_id _key);
   `(eq (Vint (Int.repr kl))) (eval_id _key_len); `(eq d) (eval_id _d);
   `(eq (Vint (Int.repr dl))) (eval_id _n);
   `(eq c) (eval_var _c t_struct_hmac_ctx_st);
   `(eq KV) (eval_var sha._K256 (tarray tuint 64)))
   SEP 
    (`(K_vector KV); `(hmacstate_PostFinal x0 c);
     `(data_block shmd x md); `(data_block Tsh data d);
     `(initPostKey k key)))).
   entailer.
   apply (exp_right x).
   apply (exp_right x0). entailer.
apply extract_exists_pre. intros dig.
apply extract_exists_pre. intros h2. normalize. rename H into HmacFinalSimple.

eapply semax_seq'. 
myframe_SEP'' (cons 1 (@nil Z)).
forward_call (h2,c).
  assert (FR: Frame =nil).
       subst Frame. reflexivity.
     rewrite FR. clear FR Frame. 
  entailer.
after_call.
simpl. normalize. simpl. normalize.
rename H into SCc. rename H0 into ACc.

forward.
apply (exp_right dig).
simpl_stackframe_of. normalize. clear H0.
assert (HS: hmacSimple key data dig).
    exists h0, h1. 
    split. destruct KL as [KL1 [KLb KLc]].
           assumption.
    split; try assumption.
    rewrite hmacFinal_hmacFinalSimple. exists h2; trivial.
assert (Size: sizeof t_struct_hmac_ctx_st <= Int.max_unsigned).
  rewrite int_max_unsigned_eq; simpl. omega.
apply andp_right. apply prop_right.
  rewrite hmac_hmacSimple in HS. destruct HS as [hh HH]. 
  specialize (hmac_sound _ _ _ _ HH). intros D; subst dig.
  split. unfold bitspec. simpl. rewrite HMAC_equivalence.Equivalence.
         f_equal. unfold HMAC_spec_abstract.HMAC_Abstract.Message2Blist.
       remember (mkCont data) as dd. destruct dd. destruct a; subst x.
         rewrite ByteBitRelations.bytes_bits_bytes_id.
         rewrite HMAC_equivalence.of_length_proof_irrel.
         rewrite ByteBitRelations.bytes_bits_bytes_id. reflexivity.
           apply isbyteZ_mkKey. assumption.   
           apply H2. 
           intros ? X; eapply X.
  split; trivial.
  unfold CRYPTO; intros. apply sha.HMAC_isPRF.HMAC_isPRF; try assumption.
apply andp_right. apply prop_right. trivial. cancel.
unfold data_block.
  rewrite Zlength_correct; simpl.
rewrite <- memory_block_data_at_; try reflexivity. 
(*XXX: WAS: rewrite memory_block_array_tuchar. 
  normalize. clear H1. 
  apply andp_right.
    apply prop_right. trivial. cancel.
  simpl; omega.
Now need this:*)
normalize.
rewrite (memory_block_data_at_ Tsh (tarray tuchar (sizeof t_struct_hmac_ctx_st))).
  apply data_at_data_at_.
  trivial.
  trivial.
  trivial.
  unfold align_compatible. destruct (eval_var _c t_struct_hmac_ctx_st rho); trivial.
   simpl. apply Z.divide_1_l.
  simpl. rewrite <- initialize.max_unsigned_modulus, int_max_unsigned_eq. omega.
 
unfold align_compatible. destruct (eval_var _c t_struct_hmac_ctx_st rho); trivial.
Qed.
