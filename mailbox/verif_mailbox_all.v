Require Import mailbox.verif_atomic_exchange.
Require Import VST.concurrency.conclib.
Require Import VST.floyd.library.
Require Import VST.zlist.sublist.
Require Import mailbox.mailbox.
Require Import mailbox.verif_mailbox_specs.
Require Import mailbox.verif_mailbox_read.
Require Import mailbox.verif_mailbox_write.
Require Import mailbox.verif_mailbox_init.
Require Import mailbox.verif_mailbox_reader.
Require Import mailbox.verif_mailbox_writer.
Require Import mailbox.verif_mailbox_main.

Section mpred.

Context `{!VSTGS unit Σ, AEGS0 : !AEGS t_atom_int, !inG Σ (excl_authR (leibnizO val))}.

Definition ext_link := ext_link_prog prog.

#[local] Instance AE_ext_spec : ext_spec unit := add_funspecs_rec unit ext_link (void_spec unit)
  [(ext_link "make_atomic", SC_atomics.make_atomic_spec);
   (ext_link "atom_exchange", SC_atomics.atomic_exchange_spec);
   (ext_link "spawn", semax_conc.spawn_spec)].

(* This lemma ties all the function proofs into a single proof for the entire program. *)
Lemma all_funcs_correct:
  semax_prog prog tt Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_malloc.
{ destruct x; apply semax_func_cons_malloc_aux. }
semax_func_cons body_exit.
semax_func_cons_ext.
{ simpl; monPred.unseal; Intro p.
  assert_PROP (isptr p); last by apply typecheck_return_value with (t := Xint16signed); auto.
  rewrite /PROPx /LOCALx /SEPx; monPred.unseal.
  rewrite !bi.and_elim_r.
  rewrite bi.sep_emp; apply atomic_int_isptr. }
semax_func_cons_ext.
{ simpl; destruct x as ((((?, ?), ?), ?), ?); monPred.unseal; Intro i.
  apply typecheck_return_value with (t := Xint16signed); auto. }
semax_func_cons_ext.
semax_func_cons body_surely_malloc.
semax_func_cons body_memset.
semax_func_cons body_initialize_channels.
semax_func_cons body_initialize_reader.
semax_func_cons body_start_read.
semax_func_cons body_finish_read.
semax_func_cons body_initialize_writer.
semax_func_cons body_start_write.
semax_func_cons body_finish_write.
semax_func_cons body_reader.
semax_func_cons body_writer.
semax_func_cons body_main.
Qed.

End mpred.
