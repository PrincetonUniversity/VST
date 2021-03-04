Require Import mailbox.verif_atomic_exchange.
Require Import VST.progs.conclib.
Require Import VST.progs.ghosts.
Require Import VST.floyd.library.
Require Import VST.floyd.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.
Require Import mailbox.verif_mailbox_read.
Require Import mailbox.verif_mailbox_write.
Require Import mailbox.verif_mailbox_init.
Require Import mailbox.verif_mailbox_reader.
Require Import mailbox.verif_mailbox_writer.
Require Import mailbox.verif_mailbox_main.

Set Bullet Behavior "Strict Subproofs".

Definition extlink := ext_link_prog prog.
Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

(* This lemma ties all the function proofs into a single proof for the entire program. *)
Lemma all_funcs_correct:
  semax_func Vprog Gprog (Genv.globalenv prog) (prog_funct prog) 
   ltac:(old_with_library prog Gprog).
Proof.
unfold prog, prog_funct, main_post, prog_vars; simpl.
prove_semax_prog_setup_globalenv.
repeat (eapply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | LookupID | LookupB |]).
repeat semax_func_cons_ext.
semax_func_cons body_malloc. apply semax_func_cons_malloc_aux.
repeat semax_func_cons_ext.
{ unfold PROPx, LOCALx, local, lift1, liftx, lift; simpl.
  unfold liftx, lift; simpl.
  Intros; subst.
  apply prop_right; unfold make_ext_rval, eval_id in *; simpl in *.
  destruct ret; auto. }
semax_func_cons body_surely_malloc.
semax_func_cons body_memset.
semax_func_cons body_initialize_channels.
semax_func_cons body_initialize_reader.
semax_func_cons body_start_read.
semax_func_cons body_finish_read.
semax_func_cons body_initialize_writer.
eapply semax_func_cons; [ reflexivity
           | repeat apply Forall_cons; try apply Forall_nil; simpl; auto; computable
           | unfold var_sizes_ok; repeat constructor; simpl; computable | reflexivity | LookupID | LookupB 
           | apply body_start_write |].
semax_func_cons body_finish_write.
semax_func_cons body_reader.
semax_func_cons body_writer.
semax_func_cons body_main.
Qed.
