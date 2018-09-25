Require Import VST.floyd.proofauto.
Require Import sha.sha.
Require Import sha.SHA256.
Require Import sha.spec_sha.
Require Import sha.sha_lemmas.
Require Import sha.bdo_lemmas.
Require Import sha.verif_sha_bdo4.
Require Import sha.verif_sha_bdo7.
Require Import sha.verif_sha_bdo8.
Local Open Scope logic.

Lemma body_sha256_block_data_order: semax_body Vprog Gtot f_sha256_block_data_order sha256_block_data_order_spec.
Proof.
start_function.
rename v_X into Xv.
assert (Lregs: length regs = 8%nat)
 by (change 8%nat with (Z.to_nat 8); rewrite <- Zlength_length; auto).
forward. (* data = in; *)
 match goal with |- semax _ _ ?c _ =>
  eapply seq_assocN with (cs := sequenceN 8 c)
 end. {
 semax_frame [ lvar _X (tarray tuint 16) Xv  ]
             [data_at_ Tsh (tarray tuint 16) Xv;
                      data_block sh (intlist_to_bytelist b) data;
                      K_vector gv].
 simple apply sha256_block_load8 with (ctx:=ctx); assumption.
}
eapply semax_seq'. {
  semax_frame
      [  ]
      [field_at wsh t_struct_SHA256state_st [StructField _h] (map Vint regs) ctx].
  simpl sequence.
  simple apply (sha256_block_data_order_loop1_proof _ sh b ctx data regs gv Xv); auto.
}
eapply semax_seq'. {
  semax_frame  [ ]
        [field_at wsh t_struct_SHA256state_st [StructField _h] (map Vint regs) ctx;
         data_block sh (intlist_to_bytelist b) data].
  match goal with |- semax _ _ ?c _ => change c with block_data_order_loop2 end.
  simple eapply sha256_block_data_order_loop2_proof; eassumption.
}
eapply seq_assocN with (cs := add_them_back). {
  semax_frame  [  lvar _X (tarray tuint 16) Xv ]
             [K_vector gv;
             data_at_ Tsh (tarray tuint LBLOCKz) Xv;
             data_block sh (intlist_to_bytelist b) data].
  simple apply (add_them_back_proof _ regs (Round regs (nthi b) 63) ctx); try assumption.
  apply length_Round; auto.
}
simpl; abbreviate_semax.
forward. (* return; *)
fold (hash_block regs b).
entailer!.
apply derives_refl.
Qed.










