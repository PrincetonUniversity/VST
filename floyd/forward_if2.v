Lemma sem_cast_i2bool_of_bool : forall (b : bool),
  sem_cast_i2bool (Val.of_bool b) = Some (Val.of_bool b).
Proof.
  destruct b; auto.
Qed.

Ltac forward_if2 :=
  repeat apply seq_assoc1;
  apply semax_if_seq;
  forward_if.
Ltac step2 := first [step | forward_if2].
Ltac info_step2 := first [simpl eval_binop; rewrite sem_cast_i2bool_of_bool | info_step | forward_if2; idtac "forward_if2."].

Definition typed_true_bool (t : type) (v : val) :=
   eqb_option Bool.eqb (strict_bool_val v t) (Some true).

Definition typed_false_bool (t : type) (v : val) :=
   eqb_option Bool.eqb (strict_bool_val v t) (Some false).

Definition cond (b : bool) (s : statement) :=
  if b then s else Sskip.



Lemma semax_if_merge :
  forall (Espec : OracleKind) (cs : compspecs) (v : val) (Delta : tycontext) (P : list Prop) (Q : list localdef) 
         (R : list mpred) (b : expr) (c d : statement) (Post : ret_assert),
  bool_type (typeof b) = true ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- (tc_expr Delta (Eunop Cop.Onotbool b tint)) ->
  ENTAIL Delta, PROPx P (LOCALx Q (SEPx R)) |-- local ((` (eq v)) (eval_expr b)) ->
  semax Delta (PROPx P (LOCALx Q (SEPx R)))
    (Ssequence (cond (typed_true_bool (typeof b) v) c) (cond (typed_false_bool (typeof b) v) d)) Post ->
  semax Delta (PROPx P (LOCALx Q (SEPx R))) (Sifthenelse b c d) Post.
Proof.
  intros. apply semax_ifthenelse_PQR' with v; auto;
  unfold typed_true_bool, typed_false_bool in *; destruct (strict_bool_val v (typeof b)) as [[] | ] eqn:?; simpl in *.
  3, 6 :
    assert_PROP (tc_val (typeof b) v) by admit; (* Don't know how to prove this *)
    assert (exists b0, strict_bool_val v (typeof b) = Some b0) as HSome;
    [apply expr_lemmas.tc_bool_val; auto | destruct HSome; congruence].
  all : unfold typed_true, typed_false; apply semax_extract_PROP; intros.
  2, 3 : congruence.
  apply semax_seq_skip in H2; auto.
  apply semax_skip_seq in H2; auto.
Admitted.

Definition val_of_bool (b : bool) :=
  if b then Vtrue else Vfalse.

Lemma val_of_bool_strict_bool_val : forall b,
  strict_bool_val (val_of_bool b) tint = Some b.
Proof.
  destruct b; auto.
Qed.

