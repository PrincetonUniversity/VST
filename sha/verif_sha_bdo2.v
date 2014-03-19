Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.sha_lemmas.
Require Import sha.sha_lemmas2.
Require Import sha.spec_sha.
Local Open Scope logic.

Lemma sha256_block_data_order_return:
   forall (Espec : OracleKind) (hashed b : list int) (ctx data : val)
            (sh : share) (regs : registers),
  Zlength b = LBLOCKz ->
  (LBLOCKz | Zlength hashed) ->
  regs = hash_blocks init_registers hashed ->
  semax (initialized _t Delta_loop1)
  (PROP  ()
   LOCAL  (`(eq ctx) (eval_id _ctx))
   SEP 
   (`(array_at tuint Tsh
        (tuints (hash_block regs b)) 0 8 ctx);
   K_vector;
   `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16));
   `(data_block sh (intlist_to_Zlist b) data))) (Sreturn None)
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (`(array_at tuint Tsh
             (tuints (hash_blocks init_registers (hashed ++ b))) 0 8 ctx) *
         `(data_block sh (intlist_to_Zlist b) data) *
         K_vector))
     (stackframe_of f_sha256_block_data_order)).
Proof.
intros.
rewrite <- process_block_hash_block. (* FIXME to avoid using process_block at all *)
2: rewrite H1; apply length_hash_blocks; auto.
2: apply Zlength_length in H; auto.
unfold process_block.
unfold Delta_loop1; simplify_Delta.
forward. (* return; *)
unfold frame_ret_assert; simpl.
unfold sha256state_.
set (regs := map2 Int.add (hash_blocks init_registers hashed)
        (rnd_64 (hash_blocks init_registers hashed) K
           (rev (generate_word (rev b) 48)))).
unfold K_vector; unfold_lift.
erewrite elim_globals_only by (split3; [eassumption | reflexivity.. ]).
entailer!.
unfold stackframe_of; simpl.
rewrite var_block_data_at_ by reflexivity.
rewrite prop_true_andp by (compute; congruence).
simpl_data_at.
unfold id.
cancel.
apply derives_refl'; f_equal.
f_equal.
unfold regs.
rewrite <- process_msg_hash_blocks; auto.
rewrite <- process_msg_hash_blocks; auto.
apply process_msg_block; auto.
apply Zlength_length in H; auto.
apply divide_hashed; auto.
rewrite initial_world.Zlength_app.
clear - H0 H.
destruct H0 as [n ?]; exists (n+1)%Z.
rewrite Z.mul_add_distr_r.
f_equal; auto.
Qed.
