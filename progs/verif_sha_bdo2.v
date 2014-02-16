Require Import floyd.proofauto.
Require Import progs.sha.
Require Import progs.SHA256.
Require Import progs.sha_lemmas.
Require Import progs.spec_sha.
Local Open Scope logic.

Lemma sha256_block_data_order_return:
   forall (Espec : OracleKind) (hashed b : list int) (ctx data : val)
            (sh : share) (regs : registers),
  length b = LBLOCK ->
  NPeano.divide LBLOCK (length hashed) ->
  regs = process_msg init_registers hashed ->
  semax (initialized _t Delta_loop1)
  (PROP  ()
   LOCAL  (`(eq ctx) (eval_id _ctx))
   SEP 
   (`(array_at tuint Tsh
        (tuints
           (map2 Int.add regs
              (rnd_64 regs K (rev (generate_word (rev b) 48))))) 0 8 ctx);
   K_vector;
   `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16));
   `(data_block sh (intlist_to_Zlist b) data))) (Sreturn None)
  (frame_ret_assert
     (function_body_ret_assert tvoid
        (`(array_at tuint Tsh
             (tuints (process_msg init_registers (hashed ++ b))) 0 8 ctx) *
         `(data_block sh (intlist_to_Zlist b) data) *
         K_vector))
     (stackframe_of f_sha256_block_data_order)).
Proof.
intros.
unfold Delta_loop1; simplify_Delta.
forward. (* return; *)
unfold frame_ret_assert; simpl.
unfold sha256state_.
set (regs := map2 Int.add (process_msg init_registers hashed)
        (rnd_64 (process_msg init_registers hashed) K
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
apply process_msg_block; auto.
Qed.
