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
unfold POSTCONDITION, abbreviate.
simpl_stackframe_of.
apply (remember_value (eval_lvar _X (tarray tuint 16))); intro Xv.
assert_LOCAL (lvar _X (tarray tuint 16) Xv). {
  entailer!.
  unfold lvar, eval_lvar in H3|-*.
  destruct (Map.get (ve_of rho) _X) as [[? ?]|]; try contradiction; auto.
  destruct (eqb_type (tarray tuint 16) t); try contradiction; auto.
}
replace_SEP 0 (`(data_at_ Tsh (tarray tuint 16) Xv)) .
 entailer!.
remember (hash_blocks init_registers hashed) as regs eqn:Hregs.
assert (Lregs: length regs = 8%nat) 
  by (subst regs; apply length_hash_blocks; auto).
assert (Zregs: Zlength regs = 8%Z)
 by (rewrite Zlength_correct; rewrite Lregs; reflexivity).
forward data_old. (* data = in; *)
assert_PROP (isptr data); [  entailer | ].
 match goal with |- semax _ _ ?c _ =>
  eapply seq_assocN with (cs := sequenceN 8 c)
 end.
*
 eapply (semax_frame1 
             [ lvar _X (tarray tuint 16) Xv ] 
             [`(data_at_ Tsh (tarray tuint 16) Xv);
                         `(data_block sh (intlist_to_Zlist b) data);
                         `(K_vector kv)]).
 + eapply sha256_block_load8 with (ctx:=ctx); eassumption.
 + simplify_Delta; reflexivity.
 +
    instantiate (1:=kv). instantiate (1:=data). (* this line should not be necessary *)
    entailer!.
 + auto 50 with closed.
*
abbreviate_semax.
simpl.
eapply (semax_frame_seq [ lvar _X (tarray tuint 16) Xv ]
              [`(field_at Tsh t_struct_SHA256state_st [StructField _h] (map Vint regs)
        ctx)]).
+ replace Delta with Delta_loop1
    by (simplify_Delta; reflexivity).
    apply (sha256_block_data_order_loop1_proof _ sh b ctx data regs kv Xv); auto.
    apply Zlength_length in H; auto.
 +
    entailer!.
 + auto 50 with closed.
 +  simpl; abbreviate_semax.
 eapply (semax_frame_seq [ ]
        [`(field_at Tsh t_struct_SHA256state_st [StructField _h] (map Vint regs) ctx);
         `(data_block sh (intlist_to_Zlist b) data)]).
match goal with |- semax _ _ ?c _ =>
  change c with block_data_order_loop2
end.
apply sha256_block_data_order_loop2_proof
              with (regs:=regs)(b:=b); eassumption.
 instantiate (1:=Xv).  instantiate (1:=kv). instantiate (1:=ctx). (* should not be necessary *)
entailer!.
auto 50 with closed.
abbreviate_semax.
eapply seq_assocN with (cs := add_them_back).
eapply (semax_frame1  [  lvar _X (tarray tuint 16) Xv ]
             [`(K_vector kv);
             `(data_at_ Tsh (tarray tuint LBLOCKz) Xv);
             `(data_block sh (intlist_to_Zlist b) data)]).
apply (add_them_back_proof _ regs (Round regs (nthi b) 63) ctx); try assumption.
apply length_Round; auto.
simplify_Delta; reflexivity.
        instantiate (1:=kv).
entailer!.
auto 50 with closed.
simpl; abbreviate_semax.
unfold POSTCONDITION, abbreviate; clear POSTCONDITION.
replace Delta with (initialized _t (initialized _i Delta_loop1)) 
 by (simplify_Delta; reflexivity).
clear Delta.
fold (hash_block regs b).
simple apply sha256_block_data_order_return; auto.
Qed.










