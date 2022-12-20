Require Import VST.floyd.proofauto.
Require Import malloc.
Require Import malloc_lemmas.
Require Import malloc_sep.
Require Import VSU_malloc_definitions.
Local Open Scope logic.
(*
Definition Gprog : funspecs := external_specs ++ private_specs.
*)
Lemma body_malloc_large: semax_body MF_Vprog MF_Gprog f_malloc_large malloc_large_spec.
Proof.
start_function. 
forward_call (n+WA+WORD). (*! t'1 = mmap0(nbytes+WASTE+WORD ...) !*)
{ entailer!. }
(*{ rep_lia. }*)
Intros p.
(* NOTE could split cases here; then two symbolic executions but simpler ones *)
forward_if. (*! if (p==NULL) !*)
- (* typecheck guard *) 
  if_tac; entailer!.
- (* case p == NULL *) 
  forward. (*! return NULL  !*)
  Exists (Vint (Int.repr 0)).
  if_tac; entailer!. (* cases in post of mmap *)
- (* case p <> NULL *) 
  if_tac. (* cases in post of mmap *)
  + (* impossible case *)
    exfalso. destruct p; try contradiction; simpl in *.
  + assert_PROP (
        (force_val
           (sem_add_ptr_int tuint Signed
                            (force_val
                               (sem_cast_pointer
                                  (force_val
                                     (sem_add_ptr_int tschar Unsigned p
                                                      (Vint
                                                         (Int.sub
                                                            (Int.mul (Ptrofs.to_int (Ptrofs.repr 4)) (Int.repr 2))
                                                            (Ptrofs.to_int (Ptrofs.repr 4))))))))
                            (Vint (Int.repr 0))) = field_address tuint [] (offset_val WA p)) ).
    (* painful pointer reasoning to enable forward (p+WASTE)[0] = nbytes *)
    { entailer!. 
      destruct p; try contradiction; simpl.
      normalize.
      unfold field_address.
      rewrite if_true.
      { simpl.  normalize. }
      hnf. (* drill down *) 
      repeat split; auto.
      - (* size compat *)
        red. 
        match goal with | H:size_compatible' _ _ |- _ => red in H end.
        unfold Ptrofs.add.
        rewrite (Ptrofs.unsigned_repr WA) by rep_lia.
        rewrite Ptrofs.unsigned_repr by rep_lia.
        simpl sizeof. rep_lia.
      - (* align compat *)
        red.
        eapply align_compatible_rec_by_value; try reflexivity.
        simpl in *. unfold natural_alignment in *. unfold Z.divide in *.
        match goal with | HA: (exists z:Z, _) /\ _ |- _ => destruct HA as [Hz Hlim] end. 
        inv Hz.
        rewrite <- (Ptrofs.repr_unsigned i). 
        match goal with | HA: Ptrofs.unsigned _ = _ |- _ => rewrite HA end. 
        exists (2*x+1). change WA with 4.
        rewrite ptrofs_add_repr. rewrite Ptrofs.unsigned_repr.
        lia. rep_lia.
    }
    rewrite malloc_large_chunk; try rep_lia; try assumption.
    Intros. (* flatten sep *)
    forward. (*! (p+WASTE)[0] = nbytes;  !*)
    forward. (*! return (p+WASTE+WORD);  !*)
    (* postcond *)
    Exists (offset_val (WA+WORD) p).
    entailer!.
    simpl.
    if_tac. 
    { exfalso. destruct p; try contradiction; simpl in *. 
      match goal with | HA: Vptr _ _  = nullval |- _ => inv HA end. }
    unfold malloc_token'.
    Exists n.
    unfold malloc_tok.
    if_tac. rep_lia. entailer!. 
    { apply malloc_compatible_offset; try rep_lia; try apply WORD_ALIGN_aligned.
      replace (n+(WA+WORD)) with (n + WA + WORD) by lia. assumption. }
    cancel. 
    (* split off the token's share of chunk *)
    rewrite <- memory_block_Ews_join.
    (* data_at_ from memory_block *)
    replace (n - n) with 0 by lia.
    rewrite memory_block_zero.  entailer!.
Qed.
(*
Definition module := [mk_body body_malloc_large].
*)