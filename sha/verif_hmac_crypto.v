Require Import floyd.proofauto.
Import ListNotations.
Require Import Blist.

Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import ByteBitRelations.

Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.

Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.hmac_common_lemmas.
Require Import ShaInstantiation.
Require Import HMAC256_equivalence.
Require Import HMAC256_isPRF.

Require Import sha.hmac091c.
Require Import sha.spec_hmac.

Lemma key_vector l:
  length (bytesToBits (HMAC_SHA256.mkKey l)) = b.
Proof. rewrite bytesToBits_len, hmac_common_lemmas.mkKey_length; reflexivity. Qed.

Definition mkCont (l:list Z) : HMAC_spec_abstract.HMAC_Abstract.Message (fun x => x=bytesToBits l /\ NPeano.divide 8 (length x)).
eapply exist. split. reflexivity. 
rewrite bytesToBits_len. exists (length l). trivial.
Qed.

Definition bitspec KEY MSG :=
  Vector.to_list ( HMAC_spec.HMAC EQ.h_v iv_v (HMAC_spec_abstract.HMAC_Abstract.wrappedSAP _ _ splitAndPad_v)
                      fpad_v EQ.opad_v EQ.ipad_v
                      (of_list_length _ (key_vector (CONT KEY)))
                      (mkCont (CONT MSG))).

Definition CRYPTO (A : Comp.OracleComp (HMAC_spec_abstract.HMAC_Abstract.Message PARS256.P)
                                       (Bvector.Bvector c) bool) 
                  (A_wf : DistSem.well_formed_oc A):=
           forall tau eps sig, PRFMod.h_PRF A tau ->
                               PRFMod.h_star_WCR A eps ->
                               PRFMod.dual_h_RKA A sig ->
  PRFMod.isPRF (Comp.Rnd (HMAC_PRF.b c p))
    (Comp.Rnd c)
    (HMAC_PRF.HMAC PRFMod.M.h_v EQ256.iv_v
      (HMAC_spec_abstract.HMAC_Abstract.wrappedSAP _ _ splitAndPad_v) EQ256.fpad_v PRFMod.M.opad_v PRFMod.M.ipad_v)
    PRFMod.Message_eqdec
    (EqDec.Bvector_EqDec c)
    (Rat.ratAdd (Rat.ratAdd tau eps) sig) A.

Definition HMAC_crypto :=
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
                temp _d msgVal; temp _n (Vint (Int.repr (LEN MSG)));
                gvar sha._K256 kv)
         SEP(`(data_block Tsh (CONT KEY) keyVal);
             `(data_block Tsh (CONT MSG) msgVal);
             `(K_vector kv);
             `(memory_block shmd (Int.repr 32) md))
  POST [ tvoid ] 
         EX digest:_, 
          PROP (bytesToBits digest = bitspec KEY MSG /\ 
                forall A Awf, CRYPTO A Awf)
          LOCAL ()
          SEP(`(K_vector kv);
              `(data_block shmd digest md);
              `(initPostKey keyVal (CONT KEY) );
              `(data_block Tsh (CONT MSG) msgVal)).

Lemma body_hmac_crypto: semax_body HmacVarSpecs HmacFunSpecs 
      f_HMAC HMAC_crypto.
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
(*NEW: crypto proof requires that we first extract isbyteZ key*)
assert_PROP (Forall isbyteZ key).
  entailer.
rename H2 into isbyteZ_Key.
rename H into isPtrMD. rename H0 into KL. rename H1 into DL.

forward_if  (
  PROP  (isptr c)
   LOCAL  (lvar _c t_struct_hmac_ctx_st c; temp _md md; temp _key k;
   temp _key_len (Vint (Int.repr kl)); temp _d d;
   temp _n (Vint (Int.repr dl)); gvar sha._K256 kv)
   SEP  (`(data_at_ Tsh t_struct_hmac_ctx_st c); `(data_block Tsh key k);
   `(data_block Tsh data d); `(K_vector kv);
   `(memory_block shmd (Int.repr 32) md))).
  { (* Branch1 *) exfalso. subst md. contradiction.  }
  { (* Branch2 *) forward. entailer. } 
normalize. rename H into isptrC.

remember (HMACabs init_s256abs init_s256abs init_s256abs Z0 nil) as dummyHMA.
forward_call' (c, k, kl, key, kv, dummyHMA) h.
  { unfold initPre. entailer.
    apply isptrD in Pk. destruct Pk as [kb [kofs HK]]. rewrite HK.
    cancel.
  }
normalize. rename H into HmacInit.

forward_call' (h, c, d, dl, data, kv) h1.
  { assert (HH: s256a_len (absCtxt h) = 512).
    Focus 2. destruct DL as [DL1 [DL2 DL3]]. split; trivial. split; trivial.
             rewrite HH; assumption. 
    destruct h; simpl in *. 
    inversion HmacInit; clear HmacInit.
    destruct H as [oS [InnSHA [OntSHA XX]]]. inversion XX; clear XX.
    subst.
      unfold innerShaInit in InnSHA. inversion InnSHA; clear InnSHA.
      simpl in *. subst. unfold HMAC_SHA256.mkArgZ, HMAC_SHA256.mkArg in H7.
      assert (Zlength (map Byte.unsigned
        (map (fun p : byte * byte => Byte.xor (fst p) (snd p))
           (combine (map Byte.repr (HMAC_SHA256.mkKey key)) (HMAC_SHA256.sixtyfour Ipad))))
        = Zlength (intlist_to_Zlist blocks ++ newfrag)).
        rewrite H7; reflexivity.
     clear H7.
     rewrite Zlength_correct in *. rewrite map_length in H. 
     rewrite Zlength_correct in *. rewrite map_length, combine_length in H.
     rewrite app_length in H.
     rewrite map_length, mkKey_length in H.
     unfold SHA256.BlockSize, HMAC_SHA256.sixtyfour in H.
     rewrite length_list_repeat, length_intlist_to_Zlist in H. unfold WORD.
     rewrite Nat2Z.inj_add, Nat2Z.inj_mul, Z.mul_comm in H. simpl in H.
     unfold bitlength. repeat rewrite Zlength_correct. unfold WORD. rewrite <- H. simpl. trivial.
  }
rename H into HmacUpdate.

(* Call to HMAC_Final*)
forward_call' (h1, c, md, shmd, kv) [dig h2].
simpl in H; rename H into HmacFinalSimple.

forward_call' (h2,c).
destruct H as [SCc ACc].

forward.
apply (exp_right dig).
simpl_stackframe_of. normalize. clear H2.
assert (HS: hmacSimple key data dig).
    exists h, h1. 
    split. destruct KL as [KL1 [KLb KLc]].
           assumption.
    split; try assumption.
    rewrite hmacFinal_hmacFinalSimple. exists h2; trivial.
assert (Size: sizeof t_struct_hmac_ctx_st <= Int.max_unsigned).
  rewrite int_max_unsigned_eq; simpl. omega.
apply andp_right. apply prop_right.
  rewrite hmac_hmacSimple in HS. destruct HS as [hh HH]. 
  specialize (hmac_sound _ _ _ _ HH). intros D; subst dig.
  split. unfold bitspec. simpl. rewrite Equivalence.
         f_equal. unfold HMAC_spec_abstract.HMAC_Abstract.Message2Blist.
       remember (mkCont data) as dd. destruct dd. destruct a; subst x.
         rewrite ByteBitRelations.bytes_bits_bytes_id.
         rewrite HMAC_equivalence.of_length_proof_irrel.
         rewrite ByteBitRelations.bytes_bits_bytes_id. reflexivity.
           apply isbyteZ_mkKey. assumption.   
           apply H4. 
           intros ? X; eapply X.
  split; trivial.
  unfold CRYPTO; intros. apply HMAC256_isPRF; assumption.
apply andp_right. apply prop_right. trivial. cancel.
unfold data_block.
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
  simpl. rewrite <- initialize.max_unsigned_modulus, int_max_unsigned_eq. omega.
Qed.