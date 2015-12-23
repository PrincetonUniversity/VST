Require Import floyd.proofauto.
Require Import progs.odd.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.

Require Import progs.verif_even.

Definition Gprog : funspecs := even_spec :: odd_spec :: nil.

Lemma body_odd : semax_body Vprog Gprog f_odd odd_spec.
Proof.
start_function.
change even._n with _n.
forward_if (PROP (z > 0) LOCAL (temp _n (Vint (Int.repr z))) SEP ()).
*
 forward.
*
 forward. entailer!.
* 
  normalize. 
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

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
semax_func_cons_ext. renormalize.
  apply (temp_make_ext_rval_e gx (Vint (if Z.even x then Int.one else Int.zero)) ret) in H; try congruence.
  subst; simpl; entailer.
semax_func_cons body_odd.
apply semax_func_nil.
Qed.
