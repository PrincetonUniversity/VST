Require Import VST.floyd.proofauto.
Require Import VST.progs.even.
Require Import VST.progs.verif_evenodd_spec.

Local Open Scope assert.

Definition Gprog : funspecs :=
     ltac:(with_library prog [odd_spec; even_spec; main_spec]).

Lemma body_even : semax_body Vprog Gprog f_even even_spec.
Proof.
start_function.
forward_if.
*
 forward.
*
  forward_call (z-1, tt).
  (* Prove that PROP precondition is OK *)
  rep_omega.
  (* After the call *)
  forward.
  entailer!.
  rewrite Z.odd_sub; simpl.
  case_eq (Z.odd z); rewrite Zodd_even_bool; destruct (Z.even z); simpl; try congruence.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof.
start_function.
forward_call (42).
rep_omega.
forward.
Qed.

(* The Espec for odd is different from the Espec for even;
  the former has only "even" as an external function, and vice versa. *)
Definition Espec := add_funspecs NullExtension.Espec (ext_link_prog even.prog) Gprog.
Existing Instance Espec.

(* Can't prove   prog_correct: semax_prog prog Vprog Gprog
  because there is no _main function, so prove all_funcs_correct instead. *)
Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
semax_func_cons_ext.
semax_func_cons body_even.
semax_func_cons body_main.
Qed.
