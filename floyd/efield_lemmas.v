Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.nested_pred_lemmas.
Require Import floyd.nested_field_lemmas.
Local Open Scope logic.

Inductive LLRR : Type :=
  | LLLL : LLRR
  | RRRR : LLRR.

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
  | _, _ => LLLL
  end.

Fixpoint efield_denote (Delta: tycontext) (efs: list efield) (gfs: list gfield) : environ -> mpred :=
  match efs, gfs with
  | nil, nil => TT
  | eArraySubsc ei :: efs', ArraySubsc i :: gfs' => 
    local (`(eq (Vint (Int.repr i))) (eval_expr Delta ei)) &&
    !! (match typeof ei with | Tint _ _ _ => True | _ => False end) &&
    efield_denote Delta efs' gfs'
  | eStructField i :: efs', StructField i0 :: gfs' =>
    !! (i = i0) && efield_denote Delta efs' gfs'
  | eUnionField i :: efs', UnionField i0 :: gfs' =>
    !! (i = i0) && efield_denote Delta efs' gfs'
  | _, _ => FF
  end.

Fixpoint tc_efield (Delta: tycontext) (efs: list efield) rho : mpred :=
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

Definition type_almost_match e t lr:=
  match typeof e, t, lr with
  | Tpointer t0 a0, Tarray t1 _ a1, RRRR => eqb_type (typeof e) (Tpointer t1 a1)
  | _, _, LLLL => eqb_type (typeof e) t
  | _, _, _ => false
  end.

Fixpoint legal_nested_efield_rec t_root e (gfs: list gfield) (tts: list type) lr: bool :=
  match gfs, tts with
  | nil, nil => type_almost_match e t_root lr
  | nil, _ => false
  | _ , nil => false
  | gf :: gfs0, t0 :: tts0 => 
    match nested_field_rec t_root gfs with
    | Some (_, ttt) => (legal_nested_efield_rec t_root e gfs0 tts0 lr && eqb_type ttt t0)%bool
    | None => false
    end
  end.

Definition legal_nested_efield t_root e gfs tts lr :=
  match gfs, tts, lr with
  | nil, nil, RRRR => false
  | nil, nil, LLLL => eqb_type t_root (typeof e)
  | nil, _, _ => false
  | _ , nil, _ => false
  | gf :: gfs0, t0 :: tts0, _ => 
    match nested_field_rec t_root gfs with
    | Some (_, ttt) => (legal_nested_efield_rec t_root e gfs0 tts0 lr && eqb_type ttt t0)%bool
    | None => false
    end
  end.

(*
Lemma legal_nested_efield_cons: forall env t_root gf gfs t tts ,
  legal_nested_efield env t_root (gf :: gfs) (t :: tts) = true ->
  legal_nested_efield env t_root gfs tts = true.
Proof.
Opaque nested_field_rec.
  intros.
  simpl in H.
  valid_nested_field_rec t_root (gf :: gfs) H.
  solve_nested_field_rec_cons_eq_Some H0;
  rewrite andb_true_iff in H;
  tauto.
Transparent nested_field_rec.
Qed.
*)
(*
Lemma legal_nested_efield_nested_field_rec_isSome: forall env t_root e gfs tts lr,
  legal_nested_efield env t_root e gfs tts lr = true -> isSome (nested_field_rec t_root gfs).
Proof.
  intros.
  destruct gfs.
  + simpl; auto.
Opaque nested_field_rec.
  + simpl in H.
    destruct tts; try solve [inversion H].
    destruct (nested_field_rec t_root (g :: gfs)); [simpl; auto | inversion H].
Transparent nested_field_rec.
Qed.
*)

Lemma typeof_nested_efield: forall Delta t_root e efs gfs tts lr,
  legal_nested_efield t_root e gfs tts lr = true ->
  (tc_efield Delta efs) && efield_denote Delta efs gfs |--
    !! (nested_field_type2 t_root gfs = typeof (nested_efield e efs tts)).
Proof.
Admitted.
(*
Opaque nested_field_rec.
  unfold type_almost_match.
  intros.
  eapply derives_trans.
  Focus 2. {
    apply prop_left; intros.
    apply prop_right.
    apply eqb_type_true.
    exact H2.
  } Unfocus.
  revert efs tts H H0.
  induction gfs as [| gf gfs']; intros;
  destruct efs as [| ef efs']; destruct tts as [|t tts']; unfold nested_field_type2 in *;
    simpl in *; intros; try solve [inversion H]; try congruence;
    try solve [(apply prop_left; intro; inversion H0)].
  + change (!! False) with FF; destruct ef; apply FF_left.
  + specialize (IHgfs' efs' tts').
    valid_nested_field_rec t_root (gf :: gfs') H.
    solve_nested_field_rec_cons_eq_Some H2;
    apply prop_right;
    apply andb_true_iff in H; destruct H as [_ HH];
    destruct ef;
    exact HH.
Transparent nested_field_rec.
Qed.
*)

Lemma offset_val_sem_add_pi: forall Delta ofs t0 e rho i,
   offset_val (Int.repr ofs)
     (force_val (sem_add_pi Delta t0 (eval_expr Delta e rho) (Vint (Int.repr i)))) =
   offset_val (Int.repr ofs)
     (offset_val (Int.mul (Int.repr (sizeof (composite_types Delta) t0)) (Int.repr i)) (eval_expr Delta e rho)).
Proof.
  intros.
  destruct (eval_expr Delta e rho); try reflexivity.
Qed.

Lemma By_reference_eval_expr: forall Delta e rho,
  access_mode (typeof (e)) = By_reference ->
  typecheck_environ Delta rho ->
  tc_lvalue Delta e rho |-- 
  !! (eval_expr Delta e rho = eval_lvalue Delta e rho).
Proof.
  intros.
  eapply derives_trans. apply typecheck_lvalue_sound; auto.
  normalize.
  destruct e; try contradiction; simpl in *; unfold deref_noload; rewrite H;
     try reflexivity.
Qed.

Lemma By_reference_tc_expr: forall Delta e rho,
  access_mode (typeof (e)) = By_reference ->
  typecheck_environ Delta rho ->
  tc_lvalue Delta e rho |--  tc_expr Delta e rho.
Proof.
  intros.
  unfold tc_lvalue, tc_expr.
  destruct e; simpl in *; try apply @FF_left; rewrite H; auto.
Qed.

(*
Lemma efield_denote_mut: forall P Q Delta env,
  (forall t_root e efs gfs tts, P t_root e efs gfs tts |-- efield_denote Delta efs gfs) ->
  (forall t_root e, P t_root e nil nil nil |-- Q t_root e nil nil nil) ->
  (forall t_root e efs gfs tts ei i t0 t1 n a,
     legal_nested_efield env t_root gfs tts = true ->
     legal_nested_efield env t_root (ArraySubsc i :: gfs) (t0 :: tts) = true ->
     nested_field_type2 t_root gfs = Tarray t1 n a ->
     0 <= i < n ->
     uncompomize env t1 = t0 ->
     type_almost_match e t_root ->
     P t_root e efs gfs tts |-- Q t_root e efs gfs tts ->
     P t_root e (eArraySubsc ei :: efs) (ArraySubsc i :: gfs) (t0 :: tts) |--
     Q t_root e (eArraySubsc ei :: efs) (ArraySubsc i :: gfs) (t0 :: tts)) ->
  (forall t_root e efs gfs tts i t0 t1 i0 f a,
     legal_nested_efield env t_root gfs tts = true ->
     legal_nested_efield env t_root (StructField i :: gfs) (t0 :: tts) = true ->
     nested_field_type2 t_root gfs = Tstruct i0 f a ->
     field_type i f = Errors.OK t1 ->
     uncompomize env t1 = t0 ->
     type_almost_match e t_root ->
     P t_root e efs gfs tts |-- Q t_root e efs gfs tts ->
     P t_root e (eStructField i :: efs) (StructField i :: gfs) (t0 :: tts) |--
     Q t_root e (eStructField i :: efs) (StructField i :: gfs) (t0 :: tts)) ->
  (forall t_root e efs gfs tts i t0 t1 i0 f a,
     legal_nested_efield env t_root gfs tts = true ->
     legal_nested_efield env t_root (UnionField i :: gfs) (t0 :: tts) = true ->
     nested_field_type2 t_root gfs = Tunion i0 f a ->
     field_type i f = Errors.OK t1 ->
     uncompomize env t1 = t0 ->
     type_almost_match e t_root ->
     P t_root e efs gfs tts |-- Q t_root e efs gfs tts ->
     P t_root e (eUnionField i :: efs) (UnionField i :: gfs) (t0 :: tts) |--
     Q t_root e (eUnionField i :: efs) (UnionField i :: gfs) (t0 :: tts)) ->
  forall t_root e efs gfs tts,
  legal_nested_efield env t_root gfs tts = true ->
   type_almost_match e t_root ->
  P t_root e efs gfs tts |-- Q t_root e efs gfs tts.
Proof.
  intros.
  revert gfs tts H4; induction efs as [| ef efs]; intros;
  simpl; intro rho;
  rewrite (add_andp _ _ (H _ _ _ _ _));
  destruct gfs as [| gf gfs];
  destruct tts as [| tt tts];
  try solve [(simpl in H4; inversion H4)];
  try solve [(simpl efield_denote; try destruct ef;
              simpl; apply andp_left2; apply FF_left)].
  + rewrite <- (add_andp _ _ (H _ _ _ _ _)); apply H0.
  + pose proof legal_nested_efield_nested_field_rec_isSome _ _ _ _ H4.
    destruct (nested_field_rec t_root (gf :: gfs)) as [[? ?]|] eqn: ?H;
      [clear H6 | simpl in H6; inversion H6].
    assert ((ef :: efs) <> nil) by (unfold not; intros ?H; congruence).
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ _ H4 H6 H5)).
    solve_nested_field_rec_cons_eq_Some H7; destruct ef;
    try solve [(simpl efield_denote; try destruct ef;
                simpl; apply andp_left2; apply andp_left1; apply FF_left)];
    simpl efield_denote; normalize; apply andp_left1.
Opaque nested_field_rec.
    - unfold nested_field_type2 in H11; rewrite H7 in H11.
      pose proof (legal_nested_efield_cons _ _ _ _ _ _ H4).
      simpl in H1; eapply H1.
      * exact H15.
      * apply legal_nested_efield_cons in H4; rewrite H4.
        rewrite H7, H11, eqb_type_refl.
        reflexivity.
      * unfold nested_field_type2.
        rewrite H8; reflexivity.
      * exact H9.
      * exact H11.
      * exact H5.
      * apply IHefs.
        eapply legal_nested_efield_cons, H4.
    - unfold nested_field_type2 in H11; rewrite H7 in H11.
      pose proof (legal_nested_efield_cons _ _ _ _ _ _ H4).
      simpl in H2; eapply H2.
      * exact H12.
      * apply legal_nested_efield_cons in H4; rewrite H4.
        rewrite H7, H11, eqb_type_refl.
        reflexivity.
      * unfold nested_field_type2.
        rewrite H8; reflexivity.
      * exact H9.
      * exact H11.
      * exact H5.
      * apply IHefs.
        eapply legal_nested_efield_cons, H4.
    - unfold nested_field_type2 in H10; rewrite H7 in H10.
      pose proof (legal_nested_efield_cons _ _ _ _ _ _ H4).
      simpl in H3; eapply H3.
      * exact H11.
      * apply legal_nested_efield_cons in H4; rewrite H4.
        rewrite H7, H10, eqb_type_refl.
        reflexivity.
      * unfold nested_field_type2.
        rewrite H8; reflexivity.
      * exact H9.
      * exact H10.
      * exact H5.
      * apply IHefs.
        eapply legal_nested_efield_cons, H4.
Transparent nested_field_rec.
Qed.
*)

Lemma classify_add_add_case_pi: forall ei t n a,
  match typeof ei with | Tint _ _ _ => True | _ => False end ->
  classify_add (Tarray t n a) (typeof ei) = add_case_pi t.
Proof.
  intros.
  destruct (typeof ei); try solve [inversion H].
  simpl.
  destruct i; reflexivity.
Qed.

(*
Lemma eval_lvalue_nested_efield_aux0: forall ei env Delta t_root e efs gfs tts t n a,
  legal_nested_efield env t_root gfs tts = true ->
  match typeof ei with | Tint _ _ _ => True | _ => False end ->
  nested_field_type2 t_root gfs = Tarray t n a ->
  type_almost_match e t_root ->
  efield_denote Delta efs gfs |--
  !! (classify_add (typeof (nested_efield e efs tts)) (typeof ei) = add_case_pi t).
Proof.
  Admitted.
*)

Definition eval_LR Delta e lr :=
  match lr with
  | LLLL => eval_lvalue Delta e
  | RRRR => eval_expr Delta e
  end.

Definition tc_LR Delta e lr :=
  match lr with
  | LLLL => tc_lvalue Delta e
  | RRRR => tc_expr Delta e
  end.

Lemma eval_lvalue_nested_efield_aux: forall Delta t_root e efs gfs tts lr,
  legal_nested_efield t_root e gfs tts lr = true ->
  local (`isptr (eval_LR Delta e lr)) &&  (tc_LR Delta e lr) &&
     (tc_efield Delta efs) && efield_denote Delta efs gfs |--
  local (`isptr (eval_lvalue Delta (nested_efield e efs tts))) &&
     (tc_lvalue Delta (nested_efield e efs tts)) &&
    local (`eq (eval_lvalue Delta (nested_efield e efs tts))
      (`(field_address t_root gfs) (eval_LR Delta e lr))).
Proof.
Admitted.
(*
  intros.
  apply efield_denote_mut 
    with (P := fun t_root e efs gfs tts => local (`isptr (eval_lvalue e)) &&
            local (tc_lvalue Delta e) && efield_denote Delta efs gfs)
         (Q := fun t_root e efs gfs tts => local (`isptr (eval_lvalue (nested_efield e efs tts))) &&
            local (tc_lvalue Delta (nested_efield e efs tts)) &&
            local (`eq (eval_lvalue (nested_efield e efs tts))
              (`(offset_val (Int.repr (nested_field_offset2 t_root gfs))) (eval_lvalue e))))
         (Delta := Delta)
         (env := env).
  + intros. apply andp_left2; apply derives_refl.
  + simpl; intros e0 rho. normalize.
Opaque classify_add.
  + (* Tarray *)
    intros.
    simpl; intro rho.
    specialize (H7 rho).
    unfold_lift.
    normalize.
    unfold_lift in H7.
    normalize in H7.
    rewrite (add_andp _ _ H7).
    rewrite (add_andp _ _
      (eval_lvalue_nested_efield_aux0 ei env Delta t_root0 e0 efs0 gfs0 tts0 t1 n a H1 H8 H3 H6)).
    normalize.
    apply prop_right.
    unfold tc_lvalue.
    simpl.
    rewrite H16.
    rewrite !denote_tc_assert_andp.
    simpl.
    unfold_lift.
    admit.
(*
    assert (eval_expr (nested_efield e0 efs0 tts0) rho =
            eval_lvalue (nested_efield e0 efs0 tts0) rho).
      eapply By_reference_eval_expr. [rewrite <- H9; reflexivity | eauto]).
    destruct (eval_lvalue (nested_efield e0 efs0 tts0) rho) eqn:?H; try inversion H10.
    assert (offset_val Int.zero 
           (force_val (sem_add (Tarray t1 n a) (typeof ei)
           (eval_expr (nested_efield e0 efs0 tts0) rho) 
           (eval_expr ei rho))) =
           offset_val
           (Int.repr (nested_field_offset2 (typeof e0) (ArraySubsc i :: gfs0)))
           (eval_lvalue e0 rho) /\
           isptr (force_val (sem_add (Tarray t1 n a) (typeof ei)
           (eval_expr (nested_efield e0 efs0 tts0) rho) 
           (eval_expr ei rho)))).
    Focus 1. {
      rewrite H15.
      unfold sem_add.
      rewrite classify_add_add_case_pi by exact H6.
      rewrite <- H7, sem_add_pi_ptr by (simpl; auto).
      simpl.
      split; [| auto].
      erewrite nested_field_offset2_Tarray by eauto.
      destruct (eval_lvalue e0 rho); inversion H13.
      simpl H12; inversion H12.
      clear - H19.
      simpl.
      f_equal.
      apply unsigned_eq_eq.
      solve_mod_eq.
      rewrite <- !Z.add_assoc.
      solve_mod_eq.
      rewrite !Z.add_assoc.
      rewrite (Z.add_comm _ ((sizeof t1 * i) mod Int.modulus)).
      rewrite <- Z.add_assoc.
      solve_mod_eq.
      f_equal.
      change (Int.unsigned Int.zero) with 0.
      omega.
    } Unfocus.
    destruct H17.
    repeat split; auto.
    - rewrite isptr_offset_val_zero by exact H18.
      exact H18.
    - rewrite H15; simpl; auto.
    - apply By_reference_tc_expr.
      rewrite <- H9; simpl; auto.
      auto.
 *)
  + (* Tstruct *)
    intros.
    simpl; intro rho.
    simpl in H7; specialize (H7 rho).
    rewrite andp_comm, !andp_assoc.
    rewrite andp_comm in H7.
    rewrite (add_andp _ _ H7).
    admit.
(*
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ H0)).
    normalize.
    rewrite <- !prop_and; apply prop_right.
    rewrite H2 in H6; simpl in H6.
    rewrite <- H6.
    unfold tc_lvalue.
    simpl.
    rewrite <- H6.
    simpl.
    rewrite denote_tc_assert_andp.
    solve_field_offset_type i f; [| inversion H3].
    repeat split; auto.
    - destruct (eval_lvalue (nested_efield e0 efs0 tts0) rho); inversion H7.
      simpl; auto.
    - erewrite H9, nested_field_offset2_Tstruct by eauto.
      destruct (eval_lvalue e0 rho); inversion H10.
      simpl.
      f_equal.
      apply unsigned_eq_eq.
      solve_mod_eq.
      rewrite (Z.add_comm _ (nested_field_offset2 (typeof e0) gfs0 mod Int.modulus)).
      rewrite <- Z.add_assoc.
      solve_mod_eq.
      f_equal; omega.
*)
  + (* Tunion *)
    admit.
  + exact H.
  + exact H0.
Qed.
*)

Lemma eval_lvalue_nested_efield: forall Delta t_root e efs gfs tts lr,
  legal_nested_efield t_root e gfs tts lr = true ->
  local (`isptr (eval_LR Delta e lr)) &&  (tc_LR Delta e lr) &&
   (tc_efield Delta efs) && efield_denote Delta efs gfs |-- local (`eq (eval_lvalue Delta (nested_efield e efs tts))
      (`(field_address t_root gfs) (eval_LR Delta e lr))).
Proof.
  intros.
  eapply derives_trans; [eapply eval_lvalue_nested_efield_aux; eauto |].
  simpl; intros; normalize.
Qed.

Lemma tc_lvalue_nested_efield: forall Delta t_root e efs gfs tts lr,
  legal_nested_efield t_root e gfs tts lr = true ->
  local (`isptr (eval_LR Delta e lr)) &&  (tc_LR Delta e lr) &&
   (tc_efield Delta efs) && efield_denote Delta efs gfs |--
    local (`isptr (eval_lvalue Delta (nested_efield e efs tts))) &&
     (tc_lvalue Delta (nested_efield e efs tts)).
Proof.
  intros.
  eapply derives_trans; [eapply eval_lvalue_nested_efield_aux; eauto |].
  simpl; intros; normalize.
Qed.

End CENV.
