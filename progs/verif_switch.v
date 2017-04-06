Require Import floyd.proofauto.
Require Import Coqlib.
Require Import Recdef.
Existing Instance NullExtension.Espec.
Require Import progs.switch.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Definition twice_spec :=
  DECLARE _twice
    WITH n : Z
    PRE [ _n OF tint ]
      PROP  (0 <= n+n <= Int.max_unsigned)
      LOCAL (temp _n (Vint (Int.repr n)))
      SEP ()
    POST [ tint ]
      PROP ()
      LOCAL (temp ret_temp (Vint (Int.repr (n+n))))
      SEP ().

Definition Gprog : funspecs :=   ltac:(with_library prog [twice_spec]).

Lemma semax_switch_PQR: 
  forall {Espec: OracleKind}{CS: compspecs} ,
  forall n Delta (Pre: environ->mpred) a sl (Post: ret_assert),
     is_int_type (typeof a) = true ->
     ENTAIL Delta, Pre |-- tc_expr Delta a ->
     ENTAIL Delta, Pre |-- local (`(eq (Vint (Int.repr n))) (eval_expr a)) ->
     0 <= n <= Int.max_unsigned ->
     @semax CS Espec Delta 
               Pre
               (seq_of_labeled_statement (select_switch n sl))
               (seplog.switch_ret_assert Post) ->
     @semax CS Espec Delta Pre (Sswitch a sl) Post.
Proof.
intros.
eapply semax_pre.
apply derives_refl.
apply (semax_switch); auto.
intro n'.
assert_PROP (n = Int.unsigned n').
apply derives_trans with (local (`( eq (Vint (Int.repr n))) (eval_expr a)) && local (` eq (eval_expr a) ` (Vint n'))).
apply andp_right.
eapply derives_trans; [ | eassumption].
intro rho.
unfold local, lift1, liftx, lift; simpl.
normalize.
intro rho.
unfold local, lift1, liftx, lift; simpl.
normalize.
intro rho.
unfold local, lift1, liftx, lift; simpl.
normalize.
rewrite <- H4 in H5.
apply Vint_inj in H5.
subst n'.
rewrite Int.unsigned_repr by auto. auto.
subst.
eapply semax_pre; [ | eassumption].
apply andp_left2.
apply andp_left2.
apply andp_left2.
auto.
Qed.

Lemma body_twice: semax_body Vprog Gprog f_twice twice_spec.
Proof.
start_function.
apply seq_assoc.
apply semax_seq
 with (PROP() LOCAL(temp _n (Vint (Int.repr (n+n)))) SEP()).
2: abbreviate_semax; forward.
eapply semax_switch_PQR.
reflexivity.
entailer!.
entailer!.
omega.
destruct (zeq n 0).
subst.
simpl.
forward.
destruct (zeq n 1).
subst.
simpl.
forward.
forward.
entailer!.
destruct (zeq n 3).
subst.
simpl. forward. forward. entailer!.
unfold select_switch.
unfold select_switch_case.
rewrite !zeq_false by omega.
simpl.
forward.
forward.
entailer!.
Qed.

