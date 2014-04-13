Require Import floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Require Import sha.verif_sha_bdo2.
Require Import sha.verif_sha_bdo4.
Require Import sha.verif_sha_bdo7.
Require Import sha.verif_sha_bdo8.
Local Open Scope logic.

Lemma body_sha256_block_data_order: semax_body Vprog Gtot f_sha256_block_data_order sha256_block_data_order_spec.
Proof.
start_function.
name a_ _a.
name b_ _b.
name c_ _c.
name d_ _d.
name e_ _e.
name f_ _f.
name g_ _g.
name h_ _h.
name l_ _l.
name Ki _Ki.
name in_ _in.
name ctx_ _ctx.
name i_ _i.
name data_ _data.
simpl_stackframe_of. 

remember (hash_blocks init_registers hashed) as regs eqn:Hregs.
assert (Lregs: length regs = 8%nat) 
  by (subst regs; apply length_hash_blocks; auto).
assert (Zregs: Zlength regs = 8%Z)
 by (rewrite Zlength_correct; rewrite Lregs; reflexivity).
forward. (* data = in; *)
apply (assert_PROP (isptr data)).
entailer. intro.
normalize.
match goal with |- semax _ _ ?c _ =>
 eapply seq_assocN with (cs := sequenceN 8 c)
end.
eapply semax_frame1.
eapply sha256_block_load8 with (ctx:=ctx); eassumption.
simplify_Delta; reflexivity.
rewrite Zregs.
entailer!.
instantiate (1:=[`K_vector (eval_var _K256 (tarray tuint 64))]); simpl; (* this line shouldn't be needed? *)
 cancel.
auto 50 with closed.
abbreviate_semax.
simpl.
forward.  (* i = 0; *)
eapply semax_frame_seq
 with (Frame:= [`(array_at tuint Tsh (tuints (hash_blocks init_registers hashed)) 0 8) (eval_id _ctx) ]).
replace Delta with Delta_loop1
 by (simplify_Delta; reflexivity).
simple apply (sha256_block_data_order_loop1_proof
  _ sh b ctx data regs); auto.
apply Zlength_length in H; auto.
rewrite Zregs.
simpl_data_at.
entailer!.
auto 50 with closed.
simpl; abbreviate_semax.

eapply semax_frame_seq
 with (Frame := [`(array_at tuint Tsh (tuints (hash_blocks init_registers hashed)) 0 8) (eval_id _ctx),
                          `(data_block sh (intlist_to_Zlist b) data)]).
match goal with |- semax _ _ ?c _ =>
  change c with block_data_order_loop2
end.
apply sha256_block_data_order_loop2_proof
              with (regs:=regs)(b:=b); eassumption.
entailer!.
auto 50 with closed.
abbreviate_semax.
eapply seq_assocN with (cs := add_them_back).
eapply semax_frame1
 with (Frame := [
   `K_vector (eval_var _K256 (tarray tuint 64)),
  `(array_at_ tuint Tsh 0 16) (eval_var _X (tarray tuint 16)),
  `(data_block sh (intlist_to_Zlist b) data)]).
apply (add_them_back_proof _ regs (Round regs (nthi b) 63) ctx); try assumption.
apply length_Round; auto.
simplify_Delta; reflexivity.
rewrite <- Hregs.
entailer!.
auto 50 with closed.
simpl; abbreviate_semax.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
replace Delta with (initialized _t Delta_loop1) 
 by (simplify_Delta; reflexivity).
clear Delta.
fold (hash_block regs b).
simple apply sha256_block_data_order_return; auto.
Qed.










