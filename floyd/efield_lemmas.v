Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_pred_lemmas.
Require Import floyd.nested_field_lemmas.
Require Import floyd.fieldlist.
Local Open Scope logic.

Inductive efield : Type :=
  | eArraySubsc: forall i: expr, efield
  | eStructField: forall i: ident, efield
  | eUnionField: forall i: ident, efield.

Fixpoint nested_efield (e: expr) (efs: list efield) (tts: list type) : expr :=
  match efs, tts with
  | nil, _ => e
  | _, nil => e
  | cons ef efs', cons t0 tts' =>
    match ef with
    | eArraySubsc ei => Ederef (Ebinop Oadd (nested_efield e efs' tts') ei (tptr t0)) t0
    | eStructField i => Efield (nested_efield e efs' tts') i t0
    | eUnionField i => Efield (nested_efield e efs' tts') i t0
    end
  end.

Fixpoint compute_nested_efield e : expr * list efield * list type :=
  match e with
  | Efield e' id t => 
    match compute_nested_efield e', typeof e' with
    | (e'', efs, tts), Tstruct _ _ => (e'', eStructField id :: efs, t :: tts)
    | (e'', efs, tts), Tunion _ _ => (e'', eUnionField id :: efs, t :: tts)
    | _, _ => (e, nil, nil)
    end
  | Ederef (Ebinop Oadd e' ei (Tpointer t a)) t' =>
    match compute_nested_efield e', typeof e', eqb_type t t', eqb_attr a noattr with
    | (e'', efs, tts), Tarray _ _ _, true, true => (e'', eArraySubsc ei :: efs, t :: tts)
    | (e'', efs, tts), Tpointer _ _, true, true => (e', eArraySubsc ei :: nil, t :: nil)
    | _, _, _, _ => (e, nil, nil)
    end
  | _ => (e, nil, nil)
  end.

Definition compute_lr e (efs: list efield) :=
  match typeof e, length efs with
  | Tpointer _ _, S _ => RRRR
  | Tarray _ _ _, _ => RRRR
  | _, _ => LLLL
  end.

Fixpoint efield_denote {cs: compspecs} (efs: list efield) (gfs: list gfield) : environ -> mpred :=
  match efs, gfs with
  | nil, nil => TT
  | eArraySubsc ei :: efs', ArraySubsc i :: gfs' => 
    local (`(eq (Vint (Int.repr i))) (eval_expr ei)) &&
    !! (match typeof ei with | Tint _ _ _ => True | _ => False end) &&
    efield_denote efs' gfs'
  | eStructField i :: efs', StructField i0 :: gfs' =>
    !! (i = i0) && efield_denote efs' gfs'
  | eUnionField i :: efs', UnionField i0 :: gfs' =>
    !! (i = i0) && efield_denote efs' gfs'
  | _, _ => FF
  end.

Fixpoint tc_efield {cs: compspecs} (Delta: tycontext) (efs: list efield) rho : mpred :=
  match efs with
  | nil => TT
  | eArraySubsc ei :: efs' => 
    tc_expr Delta ei rho && tc_efield Delta efs' rho
  | eStructField i :: efs' =>
    tc_efield Delta efs' rho
  | eUnionField i :: efs' =>
    tc_efield Delta efs' rho
  end.

Lemma compute_nested_efield_aux: forall e t,
  match compute_nested_efield e with
  | (e', gfs, tts) => nested_efield e' gfs tts = e
  end /\
  match compute_nested_efield (Ederef e t) with
  | (e', gfs, tts) => nested_efield e' gfs tts = Ederef e t
  end.
Proof.
  intros.
  revert t.
  induction e; intros; split; try reflexivity.
  + destruct (IHe t).
    exact H0.
  + clear IHe2.
    destruct (IHe1 t) as [? _]; clear IHe1.
    simpl; destruct b, t; try reflexivity.
    destruct (compute_nested_efield e1) as ((?, ?), ?); try reflexivity.
    destruct (typeof e1); try reflexivity.
    - destruct (eqb_type t t0) eqn:?H; try reflexivity.
      apply eqb_type_spec in H0.
      destruct (eqb_attr a noattr) eqn:?H; try reflexivity.
      apply eqb_attr_spec in H1.
      subst.
      reflexivity.
    - destruct (eqb_type t t0) eqn:?H; try reflexivity.
      apply eqb_type_spec in H0.
      destruct (eqb_attr a noattr) eqn:?H; try reflexivity.
      apply eqb_attr_spec in H1.
      subst.
      reflexivity.
  + destruct (IHe t) as [? _]; clear IHe.
    simpl.
    destruct (compute_nested_efield e) as ((?, ?), ?); try reflexivity.
    destruct (typeof e); try reflexivity.
    - simpl. rewrite <- H. reflexivity.
    - simpl. rewrite <- H. reflexivity.
Qed.

Lemma compute_nested_efield_lemma: forall e,
  match compute_nested_efield e with
  | (e', gfs, tts) => nested_efield e' gfs tts = e
  end.
Proof.
  intros.
  destruct (compute_nested_efield_aux e Tvoid).
  auto.
Qed.

Section CENV.

Context {cs: compspecs}.

(* Null Empty Path situation *)
Definition type_almost_match e t lr:=
  match typeof e, t, lr with
  | _, Tarray t1 _ a1, RRRR => eqb_type (typeconv (typeof e)) (Tpointer t1 noattr)
  | _, _, LLLL => eqb_type (typeof e) t
  | _, _, _ => false
  end.

(* Empty Path situation *)
Definition type_almost_match' e t lr:=
  match typeof e, t, lr with
  | _, _, LLLL => eqb_type (typeof e) t
  | _, _, _ => false
  end.

Fixpoint legal_nested_efield_rec t_root (gfs: list gfield) (tts: list type): bool :=
  match gfs, tts with
  | nil, nil => true
  | nil, _ => false
  | _ , nil => false
  | gf :: gfs0, t0 :: tts0 => (legal_nested_efield_rec t_root gfs0 tts0 && eqb_type (nested_field_type t_root gfs) t0)%bool
  end.

Definition legal_nested_efield t_root e gfs tts lr :=
 (match gfs with
  | nil => type_almost_match' e t_root lr
  | _ => type_almost_match e t_root lr
  end &&
  legal_nested_efield_rec t_root gfs tts)%bool.

Lemma legal_nested_efield_rec_cons: forall t_root gf gfs t tts,
  legal_nested_efield_rec t_root (gf :: gfs) (t :: tts) = true ->
  legal_nested_efield_rec t_root gfs tts = true.
Proof.
  intros.
  simpl in H.
  rewrite andb_true_iff in H.
  tauto.
Qed.

Lemma typeof_nested_efield': forall rho t_root e ef efs gf gfs t tts,
  legal_nested_efield_rec t_root (gf :: gfs) (t :: tts) = true ->
  efield_denote (ef :: efs) (gf :: gfs) rho |--
    !! (nested_field_type t_root (gf :: gfs) =
        typeof (nested_efield e (ef :: efs) (t :: tts))).
Proof.
  intros.
  simpl in H.
  rewrite andb_true_iff in H; destruct H.
  apply eqb_type_true in H0; subst.
  destruct ef; apply prop_right; reflexivity.
Qed.

Lemma typeof_nested_efield: forall t_root e efs gfs tts lr,
  legal_nested_efield t_root e gfs tts lr = true ->
  efield_denote efs gfs |--
    !! (nested_field_type t_root gfs = typeof (nested_efield e efs tts)).
Proof.
  intros.
  unfold legal_nested_efield in H.
  rewrite andb_true_iff in H.
  intro rho; simpl.
  destruct H.
  destruct gfs, efs, tts;
  try solve [inversion H0 | simpl; normalize | destruct e0; simpl; normalize].
  + destruct lr; try discriminate.
    apply eqb_type_true in H; subst.
    apply prop_right; reflexivity.
  + apply typeof_nested_efield'; auto.
Qed.

Lemma offset_val_sem_add_pi: forall ofs t0 e rho i,
   offset_val (Int.repr ofs)
     (force_val (sem_add_pi t0 (eval_expr e rho) (Vint (Int.repr i)))) =
   offset_val (Int.repr ofs)
     (offset_val (Int.mul (Int.repr (sizeof cenv_cs t0)) (Int.repr i)) (eval_expr e rho)).
Proof.
  intros.
  destruct (eval_expr e rho); try reflexivity.
Qed.

Lemma By_reference_eval_expr: forall Delta e rho,
  access_mode (typeof e) = By_reference ->
  tc_environ Delta rho ->
  tc_lvalue Delta e rho |-- 
  !! (eval_expr e rho = eval_lvalue e rho).
Proof.
  intros.
  eapply derives_trans. apply typecheck_lvalue_sound; auto.
  normalize.
  destruct e; try contradiction; simpl in *;
  reflexivity.
Qed.

Lemma By_reference_tc_expr: forall Delta e rho,
  access_mode (typeof e) = By_reference ->
  tc_environ Delta rho ->
  tc_lvalue Delta e rho |--  tc_expr Delta e rho.
Proof.
  intros.
  unfold tc_lvalue, tc_expr.
  destruct e; simpl in *; try apply @FF_left; rewrite H; auto.
Qed.

Definition LR_of_type (t: type) :=
  match access_mode t with
  | By_reference => RRRR
  | _ => LLLL
  end.

Lemma legal_nested_efield_weaken: forall t_root e gfs tts,
  legal_nested_efield t_root e gfs tts (LR_of_type t_root) = true ->
  legal_nested_efield_rec t_root gfs tts = true /\
  type_almost_match e t_root (LR_of_type t_root) = true.
Proof.
  intros.
  unfold legal_nested_efield in H.
  rewrite andb_true_iff in H.
  split; [tauto |].
  destruct gfs; [| tauto].
  destruct H as [? _].
  unfold type_almost_match' in H.
  unfold type_almost_match.
  destruct (LR_of_type t_root), t_root, (typeof e); simpl in H |- *;
  try inv H; auto.
Qed.

Lemma weakened_legal_nested_efield_spec: forall t_root e gfs efs tts rho,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  efield_denote efs gfs rho
       |-- !!(typeconv (nested_field_type t_root gfs) =
              typeconv (typeof (nested_efield e efs tts))).
Proof.
  intros.
  destruct gfs as [| [| |]], efs as [| [| |]], tts; try solve [inv H];
  try solve [simpl; normalize];
  try solve [rewrite (add_andp _ _ (typeof_nested_efield' _ t_root e _ _ _ _ _ _ H));
             apply andp_left2; normalize; f_equal; auto].

  apply prop_right.
  rewrite nested_field_type_ind.
  simpl typeof.
  unfold type_almost_match in H0.
  destruct (LR_of_type t_root), t_root, (typeof e); try solve [inv H0]; auto;
  apply eqb_type_spec in H0; rewrite H0; auto.
Qed.

Lemma classify_add_add_case_pi: forall ei ty t n a,
  match typeof ei with | Tint _ _ _ => True | _ => False end ->
  typeconv (Tarray t n a) = typeconv ty ->
  classify_add ty (typeof ei) = add_case_pi t.
Proof.
  intros.
  destruct (typeof ei); try solve [inversion H].
  simpl.
  rewrite <- H0.
  destruct i; reflexivity.
Qed.

Lemma isBinOpResultType_add_ptr: forall e t n a t0 ei,
  match typeof ei with | Tint _ _ _ => True | _ => False end ->
  typeconv (Tarray t0 n a) = typeconv (typeof e) ->
  complete_type cenv_cs t0 = true ->
  isBinOpResultType Oadd e ei (tptr t) = tc_isptr e.
Proof.
  intros.
  unfold isBinOpResultType.
  erewrite classify_add_add_case_pi by eauto.
  rewrite tc_andp_TT2.
  rewrite H1, tc_andp_TT2.
  auto.
Qed.

Lemma array_op_facts: forall ei rho t_root e efs gfs tts t n a t0 p,
  legal_nested_efield_rec t_root gfs tts = true ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  match typeof ei with | Tint _ _ _ => True | _ => False end ->
  nested_field_type t_root gfs = Tarray t n a ->
  field_compatible t_root gfs p ->
  complete_type cenv_cs t_root = true ->
  efield_denote efs gfs rho =
  efield_denote efs gfs rho &&
  !! (classify_add (typeof (nested_efield e efs tts)) (typeof ei) = add_case_pi t /\
      isBinOpResultType Oadd (nested_efield e efs tts) ei (tptr t0) = tc_isptr (nested_efield e efs tts)).
Proof.
  intros.
  apply add_andp.
  rewrite (add_andp _ _ (weakened_legal_nested_efield_spec _ _ _ _ _ _ H H0)); normalize.
  apply prop_right.
  rewrite H2 in H5.
  split.
  + eapply classify_add_add_case_pi; eauto.
  + eapply isBinOpResultType_add_ptr; eauto.
    eapply nested_field_type_complete_type with (gfs0 := gfs) in H4; [| destruct H3; tauto].
    rewrite H2 in H4.
    exact H4.
Qed.

Lemma in_members_Ctypes_offset: forall i m e, in_members i m -> Ctypes.field_offset cenv_cs i m = Errors.Error e -> False.
Proof.
  intros.
  unfold Ctypes.field_offset in H0.
  revert H0; generalize 0; induction m as [| [? ?] ?]; intros.
  + inv H.
  + simpl in H0.
    if_tac in H0; inv H0.
    spec IHm.
    - destruct H; [simpl in H; congruence | auto].
    - apply IHm in H3; auto.
Qed.

Lemma struct_op_facts: forall Delta t_root e gfs efs tts i a i0 t rho,
  legal_nested_efield_rec t_root gfs tts = true ->
  legal_nested_field t_root (gfs DOT i0) ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  nested_field_type t_root gfs = Tstruct i a ->
  efield_denote efs gfs rho =
  efield_denote efs gfs rho &&
  ((tc_lvalue Delta (nested_efield e efs tts) rho -->
   tc_lvalue Delta (nested_efield e (eStructField i0 :: efs) (t :: tts)) rho) &&
  !! (eval_field (typeof (nested_efield e efs tts)) i0 =
      offset_val (Int.repr (field_offset cenv_cs i0 (co_members (get_co i)))))).
Proof.
  intros.
  apply add_andp.
  rewrite (add_andp _ _ (weakened_legal_nested_efield_spec _ _ _ _ _ _ H H1)); normalize.
  rewrite H2 in H3; simpl in H3.
  destruct (typeof (nested_efield e efs tts)) eqn:?H; inv H3.
  1: destruct i1; inv H6.
  destruct H0.
  rewrite H2 in H3; simpl in H3.
  unfold tc_lvalue, eval_field.
  simpl.
  rewrite H4.
  unfold field_offset, fieldlist.field_offset.
  unfold get_co in *.
  destruct (cenv_cs ! i1); [| inv H3].
  destruct (Ctypes.field_offset cenv_cs i0 (co_members c)) eqn:?H.
  + apply andp_right; normalize.
    apply imp_andp_adjoint; apply andp_left2; auto.
  + exfalso.
    pose proof in_members_Ctypes_offset i0 (co_members c) e0; auto.
Qed.

Lemma union_op_facts: forall Delta t_root e gfs efs tts i a i0 t rho,
  legal_nested_efield_rec t_root gfs tts = true ->
  legal_nested_field t_root (gfs UDOT i0) ->
  type_almost_match e t_root (LR_of_type t_root) = true ->
  nested_field_type t_root gfs = Tunion i a ->
  efield_denote efs gfs rho =
  efield_denote efs gfs rho &&
  ((tc_lvalue Delta (nested_efield e efs tts) rho -->
   tc_lvalue Delta (nested_efield e (eUnionField i0 :: efs) (t :: tts)) rho) &&
  !! (eval_field (typeof (nested_efield e efs tts)) i0 = offset_val Int.zero)).
Proof.
  intros.
  apply add_andp.
  rewrite (add_andp _ _ (weakened_legal_nested_efield_spec _ _ _ _ _ _ H H1)); normalize.
  rewrite H2 in H3; simpl in H3.
  destruct (typeof (nested_efield e efs tts)) eqn:?H; inv H3.
  1: destruct i1; inv H6.
  destruct H0.
  rewrite H2 in H3; simpl in H3.
  unfold tc_lvalue, eval_field.
  simpl.
  rewrite H4.
  unfold get_co in *.
  destruct (cenv_cs ! i1); [| inv H3].
  apply andp_right; normalize.
  apply imp_andp_adjoint; apply andp_left2; auto.
Qed.

Definition lvalue_LR_of_type: forall Delta rho P p t e,
  P |-- !! (t = typeof e) ->
  tc_environ Delta rho ->
  P |-- !! (p = eval_lvalue e rho) && tc_lvalue Delta e rho ->
  P |-- !! (p = eval_LR e (LR_of_type t) rho) && tc_LR_strong Delta e (LR_of_type t) rho.
Proof.
  intros.
  destruct (LR_of_type t) eqn:?H.
  + exact H1.
  + rewrite (add_andp _ _ H); clear H.
    rewrite (add_andp _ _ H1); clear H1.
    simpl; normalize.
    apply andp_left2.
    unfold LR_of_type in H2.
    destruct (access_mode (typeof e)) eqn:?H; inv H2.
    apply andp_right.
    - eapply derives_trans; [apply By_reference_eval_expr |]; auto.
      normalize.
    - apply By_reference_tc_expr; auto.
Qed.

Lemma eval_lvalue_nested_efield_aux: forall Delta t_root e efs gfs tts p,
  field_compatible t_root gfs p ->
  legal_nested_efield t_root e gfs tts (LR_of_type t_root) = true ->
  local (`(eq p) (eval_LR e (LR_of_type t_root))) &&
  tc_LR Delta e (LR_of_type t_root) &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  efield_denote efs gfs |--
  local (`(eq (field_address t_root gfs p))
   (eval_LR (nested_efield e efs tts) (LR_of_type (nested_field_type t_root gfs)))) &&
  tc_LR_strong Delta (nested_efield e efs tts) (LR_of_type (nested_field_type t_root gfs)).
Proof.
  intros.
  unfold local, lift1; simpl; intro rho.
  unfold_lift.
  normalize.
  apply derives_trans with
    (tc_LR_strong Delta e (LR_of_type t_root) rho && tc_efield Delta efs rho &&
     efield_denote efs gfs rho).
  Focus 1. {
    repeat (apply andp_derives; auto).
    eapply derives_trans; [| apply tc_LR_tc_LR_strong].
    rewrite andp_comm, prop_true_andp by auto.
    auto.
  } Unfocus.

  apply legal_nested_efield_weaken in H0; destruct H0.
  rewrite field_compatible_field_address by auto.
  revert gfs tts H H0; induction efs as [| [| |]]; intros; destruct gfs as [| [| |]], tts;
  try solve [inversion H0];
  try solve [unfold efield_denote; normalize];
  specialize (IHefs gfs tts);
  (pose proof H;
   apply field_compatible_cons in H;
    destruct (nested_field_type t_root gfs) eqn:?H; try solve [inv H]);
  pose proof (proj1 (proj1 (andb_true_iff _ _) H0) : legal_nested_efield_rec t_root gfs tts = true);
  (spec IHefs; [tauto |]);
  (spec IHefs; [auto |]);
  (apply lvalue_LR_of_type;
   [apply andp_left2; apply typeof_nested_efield'; auto | assumption |]).
  + destruct H.
    unfold tc_lvalue.
    Opaque isBinOpResultType. simpl. Transparent isBinOpResultType.
    unfold local, lift1; unfold_lift.
    normalize.
    erewrite array_op_facts with (t0 := t) by eauto; normalize.
    rewrite !andp_assoc, (andp_comm (tc_expr Delta i rho)), <- !andp_assoc.
    eapply derives_trans; [apply andp_derives; [exact IHefs | apply derives_refl] |].
    normalize.
    rewrite !denote_tc_assert_andp, H10.
    unfold denote_tc_assert at 1 4, denote_tc_isptr; simpl.
    unfold local, lift1, force_val2; unfold_lift.
    assert (offset_val (Int.repr (nested_field_offset t_root (gfs SUB i0)))
            (eval_LR e (LR_of_type t_root) rho) =
            force_val
               (sem_add (typeof (nested_efield e efs tts)) 
                  (typeof i) (eval_expr (nested_efield e efs tts) rho)
                  (eval_expr i rho)));
     [| repeat apply andp_right; try apply prop_right; auto].
    - rewrite offset_val_nested_field_offset_ind by auto.
      simpl; unfold sem_add.
      unfold local, lift1; unfold_lift.
      rewrite H9.
      simpl in H11; rewrite <- H11, <- H7.
      unfold force_val; rewrite sem_add_pi_ptr by auto.
      f_equal.
      rewrite mul_repr.
      f_equal.
      rewrite H4.
      reflexivity.
    - simpl in H11; rewrite <- H11; auto.
    - apply andp_left1; auto.
    - apply andp_left2; auto.
    - rewrite <- H12; auto.
  + destruct H.
    simpl.
    unfold local, lift1; unfold_lift.
    normalize.
    erewrite struct_op_facts with (Delta := Delta) (t := t) by eauto.
    normalize.
    rewrite <- !andp_assoc.
    eapply derives_trans; [apply andp_derives; [apply IHefs | apply derives_refl] |]; normalize.
    simpl.
    eapply derives_trans; [apply modus_ponens |].
    apply andp_right; [apply prop_right | auto].
    rewrite H7.
    rewrite offset_val_nested_field_offset_ind by auto.
    rewrite H4; simpl.
    simpl in H8; rewrite <- H8.
    reflexivity.
  + destruct H.
    simpl.
    unfold local, lift1; unfold_lift.
    normalize.
    erewrite union_op_facts with (Delta := Delta) (t := t) by eauto.
    normalize.
    rewrite <- !andp_assoc.
    eapply derives_trans; [apply andp_derives; [apply IHefs | apply derives_refl] |]; normalize.
    simpl.
    eapply derives_trans; [apply modus_ponens |].
    apply andp_right; [apply prop_right | auto].
    rewrite H7.
    rewrite offset_val_nested_field_offset_ind by auto.
    rewrite H4; simpl.
    simpl in H8; rewrite <- H8.
    reflexivity.
Qed.

Lemma eval_lvalue_nested_efield: forall Delta t_root e efs gfs tts lr p,
  field_compatible t_root gfs p ->
  LR_of_type t_root = lr ->
  legal_nested_efield t_root e gfs tts lr = true ->
  type_is_by_value (nested_field_type t_root gfs) = true ->
  local (`(eq p) (eval_LR e lr)) &&
  tc_LR Delta e lr &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  efield_denote efs gfs |--
  local (`(eq (field_address t_root gfs p)) (eval_lvalue (nested_efield e efs tts))).
Proof.
  intros.
  subst lr.
  eapply derives_trans; [apply eval_lvalue_nested_efield_aux; eauto |].
  apply andp_left1.
  destruct (LR_of_type (nested_field_type t_root gfs)) eqn:?H; auto.
  unfold LR_of_type in H0.
  destruct (nested_field_type t_root gfs) as [| [| | |] [|] | | [|] | | | | |]; inv H2; inv H0.
Qed.

Lemma tc_lvalue_nested_efield: forall Delta t_root e efs gfs tts lr p,
  field_compatible t_root gfs p ->
  LR_of_type t_root = lr ->
  legal_nested_efield t_root e gfs tts lr = true ->
  type_is_by_value (nested_field_type t_root gfs) = true ->
  local (`(eq p) (eval_LR e lr)) &&
  tc_LR Delta e lr &&
  local (tc_environ Delta) &&
  tc_efield Delta efs &&
  efield_denote efs gfs |--
  tc_lvalue Delta (nested_efield e efs tts).
Proof.
  intros.
  subst lr.
  eapply derives_trans; [apply eval_lvalue_nested_efield_aux; eauto |].
  apply andp_left2.
  destruct (LR_of_type (nested_field_type t_root gfs)) eqn:?H; auto.
  unfold LR_of_type in H0.
  destruct (nested_field_type t_root gfs) as [| [| | |] [|] | | [|] | | | | |]; inv H2; inv H0.
Qed.

End CENV.
