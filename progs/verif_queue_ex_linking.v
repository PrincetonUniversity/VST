Require Import progs.verif_conc_queue.
Require Import progs.verif_queue_ex.

Lemma Gprog_sub : incl verif_conc_queue.Gprog Gprog.
Proof.
  unfold verif_conc_queue.Gprog, Gprog.
  repeat apply incl_same_head.
  do 3 apply incl_tl; repeat apply incl_same_head; auto.
Qed.

Definition extlink := ext_link_prog prog.

Definition Espec := add_funspecs (Concurrent_Espec unit _ extlink) extlink Gprog.
Existing Instance Espec.

(* Use semax_func_mono here. *)
Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity |]).
eapply semax_func_cons_ext; try reflexivity.
{ intros; entailer!. }
{ admit. }
eapply semax_func_cons_ext; try reflexivity.
{ admit. }
{ admit. }
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons_ext.
semax_func_cons body_get_request.
semax_func_cons body_process_request.
semax_func_cons body_q_new.
semax_func_cons body_q_del.
semax_func_cons body_q_add.
semax_func_cons body_q_remove.
semax_func_cons body_f.
(* XX For some reason, precondition_closed can't prove that all the gvars
   aren't local variables. *)
apply semax_func_cons; 
 [ reflexivity 
 | repeat apply Forall_cons; try apply Forall_nil; auto; computable
 | unfold var_sizes_ok; repeat constructor; simpl; computable | reflexivity
 | | apply body_g | ].
{ precondition_closed.
  apply closed_wrtl_PROPx, closed_wrtl_LOCALx, closed_wrtl_SEPx.
  repeat constructor; apply closed_wrtl_gvar; unfold is_a_local; simpl;
    intros [? | ?]; try contradiction; discriminate. }
(* Here it's just missing an auto. *)
apply semax_func_cons; 
 [ reflexivity 
 | repeat apply Forall_cons; try apply Forall_nil; (*here*)auto; computable
 | unfold var_sizes_ok; repeat constructor; simpl; computable | reflexivity
 | precondition_closed | apply body_main | ].
apply semax_func_nil.
Admitted.
*)