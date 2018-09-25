Require Import VST.floyd.proofauto.
Import ListNotations.
Require Import fcf.Blist.

Require Import sha.vst_lemmas.
Require Import sha.hmac_pure_lemmas.
Require Import sha.ByteBitRelations.

Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.

Require Import sha.HMAC_functional_prog.
Require Import sha.HMAC256_functional_prog.
Require Import sha.hmac_common_lemmas.
Require Import sha.ShaInstantiation.
Require Import sha.HMAC256_equivalence.
Require Import sha.HMAC256_isPRF.

Require Import sha.hmac.
Require Import sha.spec_hmac.

Require Import List.

Lemma key_vector l:
  length (bytesToBits (HMAC_SHA256.mkKey l)) = b.
Proof. rewrite bytesToBits_len, hmac_common_lemmas.mkKey_length; reflexivity. Qed.

Definition mkCont (l:list byte) : HMAC_spec_abstract.HMAC_Abstract.Message (fun x => x=bytesToBits l /\ NPeano.Nat.divide 8 (length x)).
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
        shk: share, shm: share, shmd: share, md: val, gv: globals
   PRE [ _key OF tptr tuchar,
         _key_len OF tint,
         _d OF tptr tuchar,
         _n OF tint,
         _md OF tptr tuchar ]
         PROP (readable_share shk; readable_share shm; writable_share shmd;
               has_lengthK (LEN KEY) (CONT KEY);
               has_lengthD 512 (LEN MSG) (CONT MSG))
         LOCAL (temp _md md; temp _key keyVal;
                temp _key_len (Vint (Int.repr (LEN KEY)));
                temp _d msgVal; temp _n (Vint (Int.repr (LEN MSG)));
                gvars gv)
         SEP(data_block shk (CONT KEY) keyVal;
             data_block shm (CONT MSG) msgVal;
             K_vector gv;
             memory_block shmd 32 md)
  POST [ tptr tuchar ] 
         EX digest:_,
          PROP (digest= HMAC256 (CONT MSG) (CONT KEY) /\
                bytesToBits digest = bitspec KEY MSG /\ 
                forall A Awf, CRYPTO A Awf)
          LOCAL (temp ret_temp md)
          SEP(K_vector gv;
              data_block shmd digest md;
              initPostKey shk keyVal (CONT KEY);
              data_block shm (CONT MSG) msgVal).

Lemma hmacbodycryptoproof Espec k KEY msg  MSG gv shk shm shmd md buf
      (Hshk: readable_share shk) (Hshm: readable_share shm) (SH : writable_share shmd) 
      (KL: has_lengthK (LEN KEY) (CONT KEY))
      (DL: has_lengthD 512 (LEN MSG) (CONT MSG)):
@semax CompSpecs Espec (func_tycontext f_HMAC HmacVarSpecs HmacFunSpecs nil)
  (PROP  ()
   LOCAL  (lvar _c (Tstruct _hmac_ctx_st noattr) buf; temp _md md;
     temp _key k; temp _key_len (Vint (Int.repr (LEN KEY)));
     temp _d msg; temp _n (Vint (Int.repr (LEN MSG))); gvars gv)
   SEP  (data_at_ Tsh (Tstruct _hmac_ctx_st noattr) buf;
     data_block shk (CONT KEY) k; data_block shm (CONT MSG) msg;
     K_vector gv; memory_block shmd 32 md))
  (*(Ssequence (fn_body f_HMAC) (Sreturn (@Some expr (Etempvar _md (tptr tuchar)))))*)
  (fn_body f_HMAC)
  (frame_ret_assert
     (function_body_ret_assert (tptr tuchar)
        (EX  digest : list byte,
         PROP 
         (digest= HMAC256 (CONT MSG) (CONT KEY) /\ bytesToBits digest = bitspec KEY MSG /\
          (forall
             (A : Comp.OracleComp
                    (HMAC_spec_abstract.HMAC_Abstract.Message PARS256.P)
                    (Bvector c) bool)
             (Awf : @DistSem.well_formed_oc
                      (HMAC_spec_abstract.HMAC_Abstract.Message PARS256.P)
                      (Bvector c) bool A), CRYPTO A Awf))
         LOCAL (temp ret_temp md)
         SEP  (K_vector gv; @data_block CompSpecs shmd digest md;
         initPostKey shk k (CONT KEY);
         @data_block CompSpecs shm (CONT MSG) msg))%assert)
     (stackframe_of f_HMAC)%assert).
Proof. intros. abbreviate_semax.
destruct KEY as [kl key].
destruct MSG as [dl data]. simpl LEN in *; simpl CONT in *.
rewrite memory_block_isptr. Intros.
simpl fn_body.
forward_if (isptr buf).
  { (* Branch1 *) exfalso. subst md. contradiction.  }
  { (* Branch2 *) forward. entailer. }
Intros.
assert_PROP (isptr k) as isPtrK by entailer!.
change (Tstruct _hmac_ctx_st noattr) with (t_struct_hmac_ctx_st).  
forward_call (Tsh, shk, buf, k, kl, key, HMACabs nil nil nil, gv).
  { apply isptrD in isPtrK. destruct isPtrK as [kb [kofs HK]]. rewrite HK.
    unfold initPre. entailer!.
  }
assert_PROP (s256a_len (absCtxt (hmacInit key)) = 512).
  { unfold hmacstate_. Intros r. apply prop_right. apply H. }
rename H into absH_len512.

forward_call (Tsh, shm, hmacInit key, buf, msg, dl, data, gv).
  { rewrite absH_len512. split3; auto. }

(* Call to HMAC_Final*)
assert_PROP (@field_compatible CompSpecs (Tstruct _hmac_ctx_st noattr) nil buf).
{ unfold hmacstate_.  Intros r; entailer!. }
rename H into FC_buf.

forward_call (Tsh, hmacUpdate data (hmacInit key), buf, md, shmd, gv).
remember (hmacFinal (hmacUpdate data (hmacInit key))) as RES.
destruct RES as [h2 dig].
simpl.

forward_call (Tsh, h2,buf).
freeze [0; 1; 2; 3; 4] FR1.
forward.
(*assert_PROP (field_compatible (tarray tuchar (sizeof t_struct_hmac_ctx_st)) nil buf).
{ unfold data_block at 1. unfold Zlength. simpl. apply prop_right. assumption. }
rename H5 into FBUF.*)
specialize (hmac_sound key data). unfold hmac.
rewrite <- HeqRES. simpl; intros.
Exists dig. thaw FR1. entailer!. 
{ subst.
       split. unfold bitspec. simpl. rewrite Equivalence.
         f_equal. unfold HMAC_spec_abstract.HMAC_Abstract.Message2Blist.
         remember (mkCont data) as dd. destruct dd. destruct a; subst x.
         rewrite ByteBitRelations.bytes_bits_bytes_id.
         rewrite HMAC_equivalence.of_length_proof_irrel.
         rewrite ByteBitRelations.bytes_bits_bytes_id. reflexivity.
           intros ? X. apply X.
       (*split; trivial. split; trivial. *)
       intros ? X.
        unfold CRYPTO; intros. apply HMAC256_isPRF; assumption. }
unfold data_block.
  rewrite Zlength_correct; simpl.
  rewrite <- memory_block_data_at_; trivial.
  rewrite (memory_block_data_at_ Tsh
                    (tarray tuchar (@sizeof (@cenv_cs CompSpecs) (Tstruct _hmac_ctx_st noattr)))).
  2: trivial.
  eapply derives_trans. apply data_at_data_at_. apply derives_refl.
Qed.

Lemma body_hmac_crypto: semax_body HmacVarSpecs HmacFunSpecs
      f_HMAC HMAC_crypto.
Proof.
start_function.
apply hmacbodycryptoproof; trivial.
Qed.
