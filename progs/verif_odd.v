Require Import VST.floyd.proofauto.
Require Import VST.progs.odd.
Require Import VST.progs.verif_evenodd_spec.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Definition Gprog : funspecs :=
     ltac:(with_library prog [odd_spec; even_spec]).

Lemma body_odd : semax_body Vprog Gprog f_odd odd_spec.
Proof.
start_function.
change even._n with _n.
forward_if.
*
 forward.
*
  forward_call (z-1).
  omega.
  forward.
  entailer!.
  rewrite Z.even_sub; simpl.
  case_eq (Z.odd z); rewrite Zodd_even_bool;
  destruct (Z.even z); simpl; try (intros; congruence).
Qed.

(* The Espec for odd is different from the Espec for even;
  the former has only "even" as an external function, and vice versa. *)
Definition Espec := add_funspecs NullExtension.Espec (ext_link_prog odd.prog) Gprog.
Existing Instance Espec.

(* Can't prove   prog_correct: semax_prog prog Vprog Gprog
  because there is no _main function, so prove all_funcs_correct instead. *)
Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
repeat (apply semax_func_cons_ext_vacuous; [reflexivity | reflexivity | ]).
semax_func_cons_ext.
semax_func_cons body_odd.
Qed.
