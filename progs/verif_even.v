Require Import floyd.proofauto.

Require Import progs.even.
Local Open Scope logic.

Inductive repr : Z -> val -> Prop :=
| mk_repr : forall z, 0 <= z <= Int.max_signed -> repr z (Vint (Int.repr z)).

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
  WITH z : Z, v : val, b: unit
  PRE [ _n (*1%positive*) OF tuint] PROP(repr z v) LOCAL(`(eq v) (eval_id _n (*1%positive*))) SEP()
  POST [ tint ] 
    PROP() LOCAL(`(eq (Vint (if Z.odd z then Int.one else Int.zero))) retval) SEP().

Definition even_spec :=
 DECLARE _even
  WITH z : Z, v : val
  PRE [ _n OF tuint] PROP(repr z v) LOCAL(`(eq v) (eval_id _n)) SEP()
  POST [ tint ] 
    PROP() LOCAL(`(eq (Vint (if Z.even z then Int.one else Int.zero))) retval) SEP().

Definition main_spec :=
 DECLARE _main
  WITH z : Z, v : val
  PRE [ ] PROP(repr 42 v) LOCAL() SEP ()
  POST [ tint ] 
    PROP() LOCAL(`(eq (Vint (if Z.even 42 then Int.one else Int.zero))) retval) SEP().

Definition Vprog : varspecs := nil.

Definition Gprog : funspecs := odd_spec :: even_spec :: main_spec :: nil.

Lemma body_even : semax_body Vprog Gprog f_even even_spec.
Proof.
start_function.
name n _n.
forward_if (PROP (repr z v /\ z > 0) LOCAL (`(eq v) (eval_id _n)) SEP ()).
* forward; eapply repr0_even in H0; eauto; rewrite H0; entailer.
* forward; entailer; inv H.
  assert (z <> 0) by (apply repr_eq0_not0; auto). entailer.
* forward_call (z-1,Vint (Int.sub (Int.repr z) (Int.repr 1)), tt).
  entailer; inversion H; subst z0; rewrite <-H5 in H2; inversion H2; subst n.
  entailer!.
  inv H. constructor. omega.
  after_call; forward.
  rewrite Z.odd_sub; simpl. 
  case_eq (Z.odd z); rewrite Zodd_even_bool; destruct (Z.even z); simpl; try congruence.
  intros; entailer!.
  intros; entailer!. 
Qed.

Ltac repr_tac := 
  constructor; split; [omega | 
  unfold Int.max_signed, Int.half_modulus, Int.modulus; simpl; omega].

Lemma body_main : semax_body Vprog Gprog f_main main_spec.
Proof with (try solve[entailer!|entailer!; constructor; omega]).
start_function. 
assert (X: repr 42 (Vint (Int.repr 42))) by (repr_tac).
forward_call (42,Vint (Int.repr 42))... 
after_call.
forward.
Qed.

Definition Espec := add_funspecs NullExtension.Espec Gprog.
Existing Instance Espec.

Lemma all_funcs_correct: semax_func Vprog Gprog (prog_funct prog) Gprog.
Proof.
unfold Gprog, prog, prog_funct.
semax_func_skipn.
semax_func_cons_ext.
rewrite <- H; entailer!.
semax_func_cons body_even.
semax_func_cons body_main.
apply semax_func_nil.
Qed.

