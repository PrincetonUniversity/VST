Require Import floyd.proofauto.
Require Import progs.odd.
Local Open Scope logic.

Require Import progs.verif_even.

Definition Gprog : funspecs := even_spec :: odd_spec :: nil.

Lemma body_odd : semax_body Vprog Gprog f_odd odd_spec.
Proof.
start_function.
change even._n with _n.
name n _n.
forward_if (PROP (z > 0) LOCAL (temp _n v) SEP ()).
*
 simpl typeof.
 assert_PROP (v= Vint (Int.repr 0)).
 entailer!. apply int_eq_e in H0; f_equal; auto.
 drop_LOCAL 0%nat.
 forward. entailer!. eapply repr0_not_odd in H; eauto. rewrite H; auto. 
*
 assert_PROP (v <> Vint (Int.repr 0)).
 entailer!.
 apply int_eq_false_e in H0. congruence.
 drop_LOCAL 0%nat.
 forward. entailer!.
 inv H.
  assert (z <> 0) by congruence. omega.
* 
  normalize. 
  forward_call' (z-1,Vint (Int.sub (Int.repr z) (Int.repr 1))).
  entailer!. inv H. normalize.
  normalize. inv H; constructor; omega.
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
semax_func_cons_ext.
  apply temp_make_ext_rval_e in H; try congruence.
  subst; simpl; entailer.
semax_func_cons body_odd.
apply semax_func_nil.
Qed.
