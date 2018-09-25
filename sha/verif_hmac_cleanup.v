Require Import VST.floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require Import sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha.sha_lemmas.

Require Import sha.hmac.

Require Import sha.spec_hmac.
Require Import sha.hmac_common_lemmas.

Lemma body_hmac_cleanup: semax_body HmacVarSpecs HmacFunSpecs
       f_HMAC_cleanup HMAC_Cleanup_spec.
Proof.
start_function.
name ctx' _ctx.
unfold hmacstate_PostFinal, hmac_relate_PostFinal.
Intros hst.
Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] c) as FCc by entailer!. (*8.7*)
forward_call (wsh, c, sizeof t_struct_hmac_ctx_st, Int.zero).
  { eapply derives_trans. apply data_at_data_at_.
    rewrite <- memory_block_data_at_; try reflexivity. cancel.
    trivial. }
subst POSTCONDITION; unfold abbreviate.
pose proof (sizeof_pos t_struct_hmac_ctx_st).
forget (sizeof t_struct_hmac_ctx_st) as NN.
forward.
unfold data_block. simpl. rewrite Zlength_list_repeat by omega.
rewrite !map_list_repeat.
 entailer!; auto.
Qed.

(*Here's the proof for the alternative specification:*)
Lemma cleanupbodyproof1 Espec wsh c h 
  (Hwsh: writable_share wsh):
@semax CompSpecs Espec (func_tycontext f_HMAC_cleanup HmacVarSpecs HmacFunSpecs nil)
  (PROP  ()
   LOCAL  (temp _ctx c)
   SEP  (EX  key : list byte, hmacstate_PreInitNull wsh key h c))
  (Ssequence (fn_body f_HMAC_cleanup) (Sreturn None))
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (PROP  ()
         LOCAL ()
         SEP
         (data_block wsh
            (list_repeat (Z.to_nat (sizeof t_struct_hmac_ctx_st)) Byte.zero)
            c))) emp).
Proof. abbreviate_semax.
set (x := fn_body f_HMAC_cleanup); hnf in x; subst x.
Intros key.
unfold hmacstate_PreInitNull, hmac_relate_PreInitNull.
Intros hst X.
Time assert_PROP (field_compatible t_struct_hmac_ctx_st [] c) as FCc by entailer!. (*8.9*)
forward_call (wsh, c, sizeof t_struct_hmac_ctx_st, Int.zero).
  { eapply derives_trans. apply data_at_data_at_.
    rewrite <- memory_block_data_at_; try reflexivity. cancel.
    trivial. }
subst POSTCONDITION; unfold abbreviate.
pose proof (sizeof_pos t_struct_hmac_ctx_st).
forget (sizeof t_struct_hmac_ctx_st) as NN.
forward.
unfold data_block. simpl. rewrite Zlength_list_repeat by omega.
rewrite !map_list_repeat.
 entailer!; auto.
Qed.

Lemma body_hmac_cleanup1: semax_body HmacVarSpecs HmacFunSpecs
       f_HMAC_cleanup HMAC_Cleanup_spec1.
Proof.
start_function.
apply cleanupbodyproof1; auto.
Qed.
