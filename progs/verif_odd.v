Require Import floyd.proofauto.
Require Import progs.odd.
Local Open Scope logic.

Require Import progs.verif_even.

Definition Gprog : funspecs := even_spec :: odd_spec :: nil.

Lemma body_odd : semax_body Vprog Gprog f_odd odd_spec.
Proof.
start_function.
assert (even._n = _n) by auto. rewrite H0. clear H0.
name n _n.
forward_if (PROP (repr z v /\ z > 0) LOCAL (`(eq v) (eval_id _n)) SEP ()).
* forward. eapply repr0_not_odd in H0; eauto. rewrite H0. entailer. 
* forward; entailer; inv H.
  assert (z <> 0) by (apply repr_eq0_not0; auto); entailer.
* forward_call (z-1,Vint (Int.sub (Int.repr z) (Int.repr 1))). 
  entailer; inversion H; subst z0; rewrite <-H5 in H2; inversion H2; subst n.
  entailer.
  assert (repr (z - 1) (Vint (Int.repr (z - 1)))). 
  { clear -H H1. inv H. constructor. omega. }
  entailer!. 
  after_call; forward.
  rewrite Z.even_sub; simpl. 
  case_eq (Z.odd z); rewrite Zodd_even_bool; 
   destruct (Z.even z); simpl; try (intros; congruence).
  intros. entailer. intros. entailer.
Qed.

Lemma all_funcs_correct:
  semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct; simpl.
semax_func_skipn.
semax_func_cons_ext.
rewrite <-H; entailer!.
semax_func_cons body_odd.
apply semax_func_nil.
Qed.
