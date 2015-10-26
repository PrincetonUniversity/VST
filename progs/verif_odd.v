Require Import floyd.proofauto.
Require Import progs.odd.
Definition CompSpecs' : compspecs.
Proof. make_compspecs1 prog. Defined.
Instance CompSpecs : compspecs.
Proof. make_compspecs2 CompSpecs'. Defined.
Local Open Scope logic.

Require Import progs.verif_even.

Definition Gprog : funspecs := even_spec :: odd_spec :: nil.

Lemma body_odd : semax_body Vprog Gprog f_odd odd_spec.
Proof.
start_function.
change even._n with _n.
name n _n.
forward_if (PROP (z > 0) LOCAL (temp _n (Vint (Int.repr z))) SEP ()).
*
 forward.
*
 forward. entailer!.
* 
  normalize. 
  forward_call (z-1) vret.
  omega.
  subst vret.
  forward.
  entailer!.
  rewrite Z.even_sub; simpl. 
  case_eq (Z.odd z); rewrite Zodd_even_bool; 
   destruct (Z.even z); simpl; try (intros; congruence).
Qed.

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
