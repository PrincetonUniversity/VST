Require Import floyd.proofauto.
Import ListNotations.
Require sha.sha.
Require sha.SHA256.
Local Open Scope logic.

Require Import sha.spec_sha.
Require Import sha_lemmas.
Require Import sha.HMAC_functional_prog.

Require Import sha.hmac091c.

Require Import sha.spec_hmac.

Lemma isbyte_Nlist i n: isbyteZ i -> Forall isbyteZ (Nlist i n).
  intros. apply Forall_forall. intros.
  induction n; simpl in *. contradiction.
  destruct H0. subst. trivial.
  apply (IHn H0).
Qed.

Lemma body_hmac_sha256: semax_body Vprog Gtot 
       f_HMAC_cleanup HMAC_Cleanup_spec.
Proof.
start_function.
name ctx' _ctx.
forward_call (Tsh, c, sizeof t_struct_hmac_ctx_st, Int.zero).
  { assert (FR: Frame = nil).  
      subst Frame. reflexivity.
    rewrite FR. clear FR Frame.
    entailer.
    unfold hmacstate_. entailer.
    eapply derives_trans. apply data_at_data_at_.
       reflexivity.
    rewrite <- memory_block_data_at_; try reflexivity.
    entailer. 
  }
after_call. subst retval0.
forward.
assert (isByte0:  isbyteZ 0). unfold isbyteZ. omega.
specialize (isbyte_Nlist 0 (Z.to_nat (sizeof t_struct_hmac_ctx_st)) isByte0). 
unfold data_block. rewrite Zlength_correct; simpl. intros.
entailer. 
Qed.