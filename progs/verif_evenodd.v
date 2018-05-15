Require Import VST.floyd.proofauto.
Require Import VST.progs.evenodd.
Local Open Scope logic.

Inductive repr : Z -> val -> Prop :=
| mk_repr : forall z, z >= 0 -> repr z (Vint (Int.repr z)).

Lemma repr0_not_odd z n :
  repr z (Vint n) -> Int.eq n (Int.repr 0) = true -> Z.odd z = false.
Proof.
inversion 1; subst; intros A.
symmetry in A; apply binop_lemmas.int_eq_true in A.
rewrite A in H; inv H.
rewrite Int.Z_mod_modulus_eq, Zmod_divides in H0.
destruct H0 as [c H0]; rewrite H0, Z.odd_mul; auto.
unfold Int.modulus; simpl; intro Contra; inv Contra.
Qed.

Lemma repr0_even z n :
  repr z (Vint n) -> Int.eq n (Int.repr 0) = true -> Z.even z = true.
Proof.
inversion 1; subst; intros A.
symmetry in A; apply binop_lemmas.int_eq_true in A.
rewrite A in H; inv H.
rewrite Int.Z_mod_modulus_eq, Zmod_divides in H0.
destruct H0 as [c H0]; rewrite H0, Z.even_mul; auto.
unfold Int.modulus; simpl; intro Contra; inv Contra.
Qed.

Lemma repr_eq0_not0 z :
  Int.eq (Int.repr z) (Int.repr 0) = false -> z <> 0.
Proof.
intros H; generalize (Int.eq_spec (Int.repr z) (Int.repr 0)); rewrite H.
intros H2 H3; rewrite H3 in H2; apply H2; auto.
Qed.

Definition odd_spec :=
 DECLARE _odd
  WITH sh : share, z : Z, v : val
  PRE [ _n OF tuint] PROP(repr z v) LOCAL (`(eq v) (eval_id _n)) SEP ()
  POST [ tint ] local (`(eq (Vint (if Z.odd z then Int.one else Int.zero))) retval).

Definition even_spec :=
 DECLARE _even
  WITH z : Z, v : val
  PRE [ _n OF tuint] PROP(repr z v) LOCAL (`(eq v) (eval_id _n)) SEP ()
  POST [ tint ] local (`(eq (Vint (if Z.even z then Int.one else Int.zero))) retval).

Definition main_spec :=
 DECLARE _main
  WITH z : Z, v : val
  PRE [ ] PROP(repr 42 v) LOCAL () SEP ()
  POST [ tint ] local (`(eq (Vint (if Z.even 42 then Int.one else Int.zero))) retval).

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs :=
     ltac:(with_library prog [ odd_spec; even_spec; main_spec]).

Lemma body_odd : semax_body Vprog Gprog f_odd odd_spec.
Proof.
start_function.
name n _n.
forward_if (PROP (repr z v /\ z > 0) LOCAL (`(eq v) (eval_id _n)) SEP ()).
* forward; eapply repr0_not_odd in H0; eauto; rewrite H0; entailer.
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
   destruct (Z.even z); simpl; congruence.
Qed.

Lemma body_even : semax_body Vprog Gprog f_even even_spec.
Proof.
start_function.
name n _n.
forward_if (PROP (repr z v /\ z > 0) LOCAL (`(eq v) (eval_id _n)) SEP ()).
* forward. eapply repr0_even in H0; eauto; rewrite H0; entailer.
* forward; entailer; inv H.
  assert (z <> 0) by (apply repr_eq0_not0; auto); entailer.
* forward_call (Share.top,z-1,Vint (Int.sub (Int.repr z) (Int.repr 1))).
  entailer; inversion H; subst z0; rewrite <-H5 in H2; inversion H2; subst n.
  entailer.
  assert (repr (z - 1) (Vint (Int.repr (z - 1)))).
  { clear -H H1. inv H. constructor. omega. }
  entailer!.
  after_call; forward.
  rewrite Z.odd_sub; simpl.
  case_eq (Z.odd z); rewrite Zodd_even_bool;
   destruct (Z.even z); simpl; congruence.
Qed.

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof with (try solve[entailer!|entailer!; constructor; omega]).
start_function.
forward_call (42,Vint (Int.repr 42))... after_call.
forward.
Qed.

Existing Instance NullExtension.Espec.

Lemma prog_correct:
  semax_prog prog Vprog Gprog.
Proof.
prove_semax_prog.
semax_func_cons body_odd.
semax_func_cons body_even.
semax_func_cons body_main.
Qed.

