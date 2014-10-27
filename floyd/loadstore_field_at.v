Require Import floyd.base.
Require Import floyd.assert_lemmas.
Require Import floyd.client_lemmas.
Require Import floyd.fieldlist.
Require Import floyd.nested_field_lemmas.
Require Import floyd.type_id_env.
Require Import floyd.mapsto_memory_block.
Require Import floyd.data_at_lemmas.
Require Import floyd.field_at.
Require Import floyd.loadstore_mapsto.
Require Import floyd.loadstore_data_at.
Require Import Coq.Logic.JMeq.

Local Open Scope logic.

(********************************************

Max length ids field_at load store:
  semax_max_path_field_load_37'.
  semax_max_path_field_cast_load_37'.
  semax_max_path_field_store_nth.

********************************************)

Fixpoint legal_nested_efield env t (gfs: list gfield) (tts: list type) : bool :=
  match gfs, tts with
  | nil, nil => eqb_type (uncompomize env t) t
  | nil, _ => false
  | _ , nil => false
  | cons gf gfs', cons t0 tts' => 
    match nested_field_rec t gfs with
    | Some (_, ttt) => (legal_nested_efield env t gfs' tts' && 
                       eqb_type (uncompomize env ttt) t0)%bool
    | None => false
    end
  end.

Lemma legal_nested_efield_cons: forall env gf gfs t tts e,
  legal_nested_efield env (typeof e) (gf :: gfs) (t :: tts) = true ->
  legal_nested_efield env (typeof e) gfs tts = true.
Proof.
Opaque nested_field_rec.
  intros.
  simpl in H.
  valid_nested_field_rec (typeof e) (gf :: gfs) H.
  solve_nested_field_rec_cons_eq_Some H0;
  rewrite andb_true_iff in H;
  tauto.
Transparent nested_field_rec.
Qed.

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
    | (e'', efs, tts), Tstruct _ _ _ => (e'', eStructField id :: efs, t :: tts)
    | (e'', efs, tts), Tunion _ _ _ => (e'', eUnionField id :: efs, t :: tts)
    | _, _ => (e, nil, nil)
    end
  | Ederef (Ebinop Oadd e' ei (Tpointer t a)) t' =>
    match compute_nested_efield e', typeof e', eqb_type t t', eqb_attr a noattr with
    | (e'', efs, tts), Tarray _ _ _, true, true => (e'', eArraySubsc ei :: efs, t :: tts)
    | _, _, _, _ => (e, nil, nil)
    end
  | _ => (e, nil, nil)
  end.

(*
Fixpoint efield_match (efs: list efield) (gfs: list gfield) : Prop :=
  match efs, gfs with
  | nil, nil => True
  | eArraySubsc _ :: efs', ArraySubsc _ :: gfs' => efield_match efs' gfs'
  | eStructField i :: efs', StructField i0 :: gfs' => i = i0 /\ efield_match efs' gfs'
  | eUnionField i :: efs', UnionField i0 :: gfs' => i = i0 /\ efield_match efs' gfs'
  | _, _ => False
  end.
*)

Fixpoint efield_denote (Delta: tycontext) (efs: list efield) (gfs: list gfield) : environ -> mpred :=
  match efs, gfs with
  | nil, nil => TT
  | eArraySubsc ei :: efs', ArraySubsc i :: gfs' => 
    local (`(eq (Vint (Int.repr i))) (eval_expr ei)) &&
    !! (match typeof ei with | Tint _ _ _ => True | _ => False end) &&
    local (tc_expr Delta ei) &&
    efield_denote Delta efs' gfs'
  | eStructField i :: efs', StructField i0 :: gfs' =>
    !! (i = i0) && efield_denote Delta efs' gfs'
  | eUnionField i :: efs', UnionField i0 :: gfs' =>
    !! (i = i0) && efield_denote Delta efs' gfs'
  | _, _ => FF
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
    destruct (eqb_type t t0) eqn:?H; try reflexivity.
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

(*
Lemma efield_denote_match: forall efs gfs,
  efield_denote efs gfs |-- !! (efield_match efs gfs).
Proof.
  intros.
  revert gfs; induction efs as [| ef efs']; intro gfs;
  destruct gfs as [| gf gfs']; simpl; auto.
  + intros; destruct ef; auto.
  + intros. destruct ef; destruct gf; auto.
    - apply andp_left2, IHefs'.
    - rewrite prop_and.
      apply andp_derives; [apply derives_refl | apply IHefs'].
    - rewrite prop_and.
      apply andp_derives; [apply derives_refl | apply IHefs'].
Qed.
*)

Lemma legal_nested_efield_nested_field_rec_isSome: forall env t gfs tts,
  legal_nested_efield env t gfs tts = true -> isSome (nested_field_rec t gfs).
Proof.
  intros.
  destruct gfs.
  + simpl; auto.
Opaque nested_field_rec.
  + simpl in H.
    destruct tts; try solve [inversion H].
    destruct (nested_field_rec t (g :: gfs)); [simpl; auto | inversion H].
Transparent nested_field_rec.
Qed.

Lemma typeof_nested_efield: forall env Delta e efs gfs tts,
  legal_nested_efield env (typeof e) gfs tts = true ->
  efield_denote Delta efs gfs |--
    !! (uncompomize env (nested_field_type2 (typeof e) gfs) = typeof (nested_efield e efs tts)).
Proof.
Opaque nested_field_rec.
  intros.
  eapply derives_trans.
  Focus 2. {
    apply prop_left; intros.
    apply prop_right.
    apply eqb_type_true.
    exact H0.
  } Unfocus.
  revert efs tts H.
  induction gfs as [| gf gfs']; intros;
  destruct efs as [| ef efs']; destruct tts as [|t tts']; unfold nested_field_type2 in *;
    simpl in *; intros; try solve [inversion H];
    try solve [(apply prop_left; intro; inversion H0)]. 
  + apply prop_right. exact H.
  + apply prop_right. exact H.
  + specialize (IHgfs' efs' tts').
    valid_nested_field_rec (typeof e) (gf :: gfs') H.
    solve_nested_field_rec_cons_eq_Some H0;
    apply prop_right;
    apply andb_true_iff in H; destruct H as [_ HH];
    destruct ef;
    exact HH.
Transparent nested_field_rec.
Qed.

Lemma offset_val_sem_add_pi: forall ofs t0 e rho i,
   offset_val (Int.repr ofs)
     (force_val (sem_add_pi t0 (eval_expr e rho) (Vint (Int.repr i)))) =
   offset_val (Int.repr ofs)
     (offset_val (Int.mul (Int.repr (sizeof t0)) (Int.repr i)) (eval_expr e rho)).
Proof.
  intros.
  destruct (eval_expr e rho); try reflexivity.
Qed.

Lemma By_reference_eval_expr: forall Delta e rho,
  access_mode (typeof (e)) = By_reference ->
  tc_lvalue Delta e rho ->
  eval_expr e rho = eval_lvalue e rho.
Proof.
  intros.
  unfold tc_lvalue in H0.
  destruct e; simpl in H0; try inversion H0.
  + simpl in H.
    simpl.
    unfold deref_noload.
    rewrite H.
    reflexivity.
  + simpl in H.
    simpl.
    unfold deref_noload.
    rewrite H.
    reflexivity.
  + simpl in H.
    simpl.
    unfold deref_noload.
    rewrite H.
    reflexivity.
Qed.

Lemma By_reference_tc_expr: forall Delta e rho,
  access_mode (typeof (e)) = By_reference ->
  tc_lvalue Delta e rho ->
  tc_expr Delta e rho.
Proof.
  intros.
  unfold tc_lvalue, tc_expr.
  destruct e; simpl in H |- *; intros; normalize.
  + rewrite H. exact H0.
  + rewrite H. exact H0.
  + rewrite H. exact H0.
Qed.

Lemma efield_denote_mut: forall P Q Delta env,
  (forall  e efs gfs tts, P e efs gfs tts |-- efield_denote Delta efs gfs) ->
  (forall e, P e nil nil nil |-- Q e nil nil nil) ->
  (forall  e efs gfs tts ei i t0 t1 n a,
     legal_nested_efield env (typeof e) gfs tts = true ->
     legal_nested_efield env (typeof e) (ArraySubsc i :: gfs) (t0 :: tts) = true ->
     nested_field_type2 (typeof e) gfs = Tarray t1 n a ->
     0 <= i < n ->
     uncompomize env t1 = t0 ->
     P e efs gfs tts |-- Q e efs gfs tts ->
     P e (eArraySubsc ei :: efs) (ArraySubsc i :: gfs) (t0 :: tts) |--
     Q e (eArraySubsc ei :: efs) (ArraySubsc i :: gfs) (t0 :: tts)) ->
  (forall  e efs gfs tts i t0 t1 i0 f a,
     legal_nested_efield env (typeof e) gfs tts = true ->
     legal_nested_efield env (typeof e) (StructField i :: gfs) (t0 :: tts) = true ->
     nested_field_type2 (typeof e) gfs = Tstruct i0 f a ->
     field_type i f = Errors.OK t1 ->
     uncompomize env t1 = t0 ->
     P e efs gfs tts |-- Q e efs gfs tts ->
     P e (eStructField i :: efs) (StructField i :: gfs) (t0 :: tts) |--
     Q e (eStructField i :: efs) (StructField i :: gfs) (t0 :: tts)) ->
  (forall  e efs gfs tts i t0 t1 i0 f a,
     legal_nested_efield env (typeof e) gfs tts = true ->
     legal_nested_efield env (typeof e) (UnionField i :: gfs) (t0 :: tts) = true ->
     nested_field_type2 (typeof e) gfs = Tunion i0 f a ->
     field_type i f = Errors.OK t1 ->
     uncompomize env t1 = t0 ->
     P e efs gfs tts |-- Q e efs gfs tts ->
     P e (eUnionField i :: efs) (UnionField i :: gfs) (t0 :: tts) |--
     Q e (eUnionField i :: efs) (UnionField i :: gfs) (t0 :: tts)) ->
  forall  e efs gfs tts,
  legal_nested_efield env (typeof e) gfs tts = true ->
  P e efs gfs tts |-- Q e efs gfs tts.
Proof.
  intros.
  revert gfs tts H4; induction efs as [| ef efs]; intros;
  simpl; intro rho;
  rewrite (add_andp _ _ (H _ _ _ _));
  destruct gfs as [| gf gfs];
  destruct tts as [| tt tts];
  try solve [(simpl in H4; inversion H4)];
  try solve [(simpl efield_denote; try destruct ef;
              simpl; apply andp_left2; apply FF_left)].
  + rewrite <- (add_andp _ _ (H _ _ _ _)); apply H0.
  + pose proof legal_nested_efield_nested_field_rec_isSome _ _ _ _ H4.
    destruct (nested_field_rec (typeof e) (gf :: gfs)) as [[? ?]|] eqn: ?H;
      [clear H5 | simpl in H5; inversion H5].
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ H4)).
    solve_nested_field_rec_cons_eq_Some H6; destruct ef;
    try solve [(simpl efield_denote; try destruct ef;
                simpl; apply andp_left2; apply andp_left1; apply FF_left)];
    simpl efield_denote; normalize; apply andp_left1.
Opaque nested_field_rec.
    - unfold nested_field_type2 in H9; rewrite H6 in H9.
      pose proof (legal_nested_efield_cons _ _ _ _ _ _ H4).
      simpl in H1; eapply H1.
      * exact H13.
      * apply legal_nested_efield_cons in H4; rewrite H4.
        rewrite H6, H9, eqb_type_refl.
        reflexivity.
      * unfold nested_field_type2.
        rewrite H5; reflexivity.
      * exact H7.
      * exact H9.
      * apply IHefs.
        eapply legal_nested_efield_cons, H4.
    - unfold nested_field_type2 in H9; rewrite H6 in H9.
      pose proof (legal_nested_efield_cons _ _ _ _ _ _ H4).
      simpl in H2; eapply H2.
      * exact H10.
      * apply legal_nested_efield_cons in H4; rewrite H4.
        rewrite H6, H9, eqb_type_refl.
        reflexivity.
      * unfold nested_field_type2.
        rewrite H5; reflexivity.
      * exact H7.
      * exact H9.
      * apply IHefs.
        eapply legal_nested_efield_cons, H4.
    - unfold nested_field_type2 in H8; rewrite H6 in H8.
      pose proof (legal_nested_efield_cons _ _ _ _ _ _ H4).
      simpl in H3; eapply H3.
      * exact H9.
      * apply legal_nested_efield_cons in H4; rewrite H4.
        rewrite H6, H8, eqb_type_refl.
        reflexivity.
      * unfold nested_field_type2.
        rewrite H5; reflexivity.
      * exact H7.
      * exact H8.
      * apply IHefs.
        eapply legal_nested_efield_cons, H4.
Transparent nested_field_rec.
Qed.

Lemma classify_add_add_case_pi: forall ei t n a,
  match typeof ei with | Tint _ _ _ => True | _ => False end ->
  classify_add (Tarray t n a) (typeof ei) = add_case_pi t.
Proof.
  intros.
  destruct (typeof ei); try solve [inversion H].
  simpl.
  destruct i; reflexivity.
Qed.

Lemma unsigned_eq_eq: forall i j, Int.unsigned i = Int.unsigned j -> i = j.
Proof.
  intros.
  rewrite <- (Int.repr_unsigned i), <- (Int.repr_unsigned j).
  rewrite H.
  reflexivity.
Qed.

Ltac solve_mod_eq :=
  unfold Int.add, Int.mul;
  repeat rewrite Int.unsigned_repr_eq;
  repeat
  (repeat rewrite Zmod_mod;
  repeat rewrite Zmult_mod_idemp_l;
  repeat rewrite Zmult_mod_idemp_r;
  repeat rewrite Zplus_mod_idemp_l;
  repeat rewrite Zplus_mod_idemp_r).

Lemma eval_lvalue_nested_efield_aux: forall Delta env e efs gfs tts,
  legal_nested_efield env (typeof e) gfs tts = true ->
  local (`isptr (eval_lvalue e)) && local (tc_lvalue Delta e) && efield_denote Delta efs gfs |--
    local (`isptr (eval_lvalue (nested_efield e efs tts))) &&
    local (tc_lvalue Delta (nested_efield e efs tts)) &&
    local (`eq (eval_lvalue (nested_efield e efs tts))
      (`(offset_val (Int.repr (nested_field_offset2 (typeof e) gfs))) (eval_lvalue e))).
Proof.
  intros.
  apply efield_denote_mut 
    with (P := fun e efs gfs tts => local (`isptr (eval_lvalue e)) &&
            local (tc_lvalue Delta e) && efield_denote Delta efs gfs)
         (Q := fun e efs gfs tts => local (`isptr (eval_lvalue (nested_efield e efs tts))) &&
            local (tc_lvalue Delta (nested_efield e efs tts)) &&
            local (`eq (eval_lvalue (nested_efield e efs tts))
              (`(offset_val (Int.repr (nested_field_offset2 (typeof e) gfs))) (eval_lvalue e))))
         (Delta := Delta)
         (env := env).
  + intros. apply andp_left2; apply derives_refl.
  + simpl; intros e0 rho. normalize.
Opaque classify_add.
  + (* Tarray *)
    intros.
    simpl; intro rho.
    simpl in H5; specialize (H5 rho).
    rewrite andp_comm, !andp_assoc.
    rewrite andp_comm in H5.
    rewrite (add_andp _ _ H5).
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ H0)).
    normalize.
    rewrite <- !prop_and; apply prop_right.
    rewrite H2 in H9; simpl in H9.
    unfold tc_lvalue.
    simpl.
    rewrite <- H9; simpl.
    rewrite classify_add_add_case_pi by exact H6.
    rewrite !denote_tc_assert_andp.
    simpl.
    unfold_lift.
    rewrite <- H9; simpl.
    assert (eval_expr (nested_efield e0 efs0 tts0) rho =
            eval_lvalue (nested_efield e0 efs0 tts0) rho)
      by (eapply By_reference_eval_expr; [rewrite <- H9; reflexivity | eauto]).
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
  + (* Tstruct *)
    intros.
    simpl; intro rho.
    simpl in H5; specialize (H5 rho).
    rewrite andp_comm, !andp_assoc.
    rewrite andp_comm in H5.
    rewrite (add_andp _ _ H5).
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
  + (* Tunion *)
    intros.
    simpl; intro rho.
    simpl in H5; specialize (H5 rho).
    rewrite andp_comm, !andp_assoc.
    rewrite andp_comm in H5.
    rewrite (add_andp _ _ H5).
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
    - erewrite H9, nested_field_offset2_Tunion with (f := f); [| eauto | rewrite H14; simpl; auto].
      destruct (eval_lvalue e0 rho); inversion H10.
      simpl.
      f_equal.
  + exact H.
Qed.

Lemma eval_lvalue_nested_efield: forall Delta env e efs gfs tts,
  legal_nested_efield env (typeof e) gfs tts = true ->
  local (`isptr (eval_lvalue e)) && local (tc_lvalue Delta e) && efield_denote Delta efs gfs |--
    local (`eq (eval_lvalue (nested_efield e efs tts))
      (`(offset_val (Int.repr (nested_field_offset2 (typeof e) gfs))) (eval_lvalue e))).
Proof.
  intros.
  eapply derives_trans; [eapply eval_lvalue_nested_efield_aux; eauto |].
  simpl; intros; normalize.
Qed.

Lemma tc_lvalue_nested_efield: forall Delta env e efs gfs tts,
  legal_nested_efield env (typeof e) gfs tts = true ->
  local (`isptr (eval_lvalue e)) && local (tc_lvalue Delta e) && efield_denote Delta efs gfs |--
    local (`isptr (eval_lvalue (nested_efield e efs tts))) &&
    local (tc_lvalue Delta (nested_efield e efs tts)).
Proof.
  intros.
  eapply derives_trans; [eapply eval_lvalue_nested_efield_aux; eauto |].
  simpl; intros; normalize.
Qed.

Lemma semax_max_path_field_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (efs: list efield) (gfs: list gfield) (tts: list type)
      (v : val) (v' : reptype (nested_field_type2 (typeof e1) gfs)),
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 efs tts)) t = true ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) gfs tts = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta e1) &&
        local `(tc_val (typeof (nested_efield e1 efs tts)) v) &&
        efield_denote Delta efs gfs &&
        (`(field_at sh (typeof e1) gfs v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 efs tts))
          (normal_ret_assert
            (EX old : val,
              PROPx P
                (LOCALx (`(eq v) (eval_id id) :: map (subst id `old) Q)
                  (SEPx (map (subst id `old) R))))).
Proof.
  intros.
  eapply semax_ucdata_load_37'.
  + exact H.
  + exact H0.
  + exact H3.
  + eapply derives_trans; [exact H4|].
    instantiate (1:=sh).
    instantiate (1:=e).
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ H2)).
    simpl; intro rho; normalize.
    rewrite field_at_isptr.
    rewrite field_at_data_at; [|exact H1].
    rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].
    normalize.
    pose proof (eval_lvalue_nested_efield Delta e e1 efs gfs tts H2 rho).
    pose proof (tc_lvalue_nested_efield Delta e e1 efs gfs tts H2 rho).
    normalize in H12.
    normalize in H13.
    rewrite (add_andp _ _ H12).
    rewrite (add_andp _ _ H13).
    normalize.
    rewrite H14.
    apply andp_left2.
    apply derives_refl.
Qed.

Lemma semax_max_path_field_cast_load_37':
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (efs: list efield) (gfs: list gfield) (tts: list type)
      (v : val) (v' : reptype (nested_field_type2 (typeof e1) gfs)),
      typeof_temp Delta id = Some t ->
      type_is_by_value (typeof (nested_efield e1 efs tts)) ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) gfs tts = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- 
        local (tc_lvalue Delta e1) &&
        local (`(tc_val t (eval_cast (typeof (nested_efield e1 efs tts)) t v))) &&
        efield_denote Delta efs gfs &&
        (`(field_at sh (typeof e1) gfs v') (eval_lvalue e1) * TT) ->
      semax Delta (|> PROPx P (LOCALx Q (SEPx R)))
        (Sset id (Ecast (nested_efield e1 efs tts) t))
          (normal_ret_assert
            (EX old:val,
              PROPx P
                (LOCALx (`(eq (eval_cast (typeof (nested_efield e1 efs tts)) t v)) (eval_id id) :: map (subst id (`old)) Q)
                  (SEPx (map (subst id (`old)) R))))).
Proof.
  intros.
  eapply semax_ucdata_cast_load_37'; try eassumption.
  + eapply derives_trans; [exact H4|].
    instantiate (1:=sh).
    instantiate (1:=e).
    rewrite (add_andp _ _ (typeof_nested_efield _ _ _ _ _ _ H2)).
    simpl; intro rho; normalize.
    rewrite field_at_isptr.
    rewrite field_at_data_at; [|exact H1].
    rewrite at_offset'_eq; [| rewrite <- data_at_offset_zero; reflexivity].
    normalize.
    pose proof (eval_lvalue_nested_efield Delta e e1 efs gfs tts H2 rho).
    pose proof (tc_lvalue_nested_efield Delta e e1 efs gfs tts H2 rho).
    normalize in H12.
    normalize in H13.
    rewrite (add_andp _ _ H12).
    rewrite (add_andp _ _ H13).
    normalize.
    rewrite H14.
    apply andp_left2.
    apply derives_refl.
Qed.

(*
Lemma semax_max_path_field_load_38:
  forall {Espec: OracleKind},
    forall Delta sh e id P Q R (e1: expr)
      (t : type) (gfs: list ident) (tts: list type)
      (v : val) (v' : reptype (nested_field_type2 (typeof e1) gfs)),
      Forall (closed_wrt_vars (eq id)) Q ->
      Forall (closed_wrt_vars (eq id)) R ->
      typeof_temp Delta id = Some t ->
      is_neutral_cast (typeof (nested_efield e1 gfs tts)) t = true ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) gfs tts = true ->
      JMeq v' v ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta (nested_efield e1 gfs tts)) &&
        local `(tc_val (typeof (nested_efield e1 gfs tts)) v) &&
        (`(field_at sh (typeof e1) gfs v') (eval_lvalue e1) * TT) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sset id (nested_efield e1 gfs tts))
          (normal_ret_assert
            (PROPx P
              (LOCALx (`(eq v) (eval_id id) :: Q) (SEPx R)))).
Proof.
  intros.
  eapply semax_post';[ | eapply semax_max_path_field_load_37'; eauto].
  apply exp_left; intro old.
  autorewrite with subst. apply derives_refl.
Qed.
*)
Lemma lower_andp_lifted_val:
  forall (P Q: val->mpred) v, 
  (`(P && Q) v) = (`P v && `Q v).
Proof. reflexivity. Qed.

Lemma remove_one_LOCAL_left: forall P Q0 Q R S,
  PROPx P (LOCALx Q R) |-- S -> PROPx P (LOCALx (Q0 :: Q) R) |-- S.
Proof.
  intros.
  simpl in H |- *.
  intro rho; specialize (H rho).
  unfold PROPx, LOCALx, SEPx in *.
  normalize.
  normalize in H.
Qed.

Lemma semax_max_path_field_store_nth:
  forall {Espec: OracleKind},
    forall Delta sh e n P Q R Rn (e1 e2 : expr)
      (t : type) (efs: list efield) (gfs: list gfield) (tts: list type),
      typeof (nested_efield e1 efs tts) = t ->
      type_is_by_value t ->
      legal_alignas_type (typeof e1) = true ->
      legal_nested_efield e (typeof e1) gfs tts = true ->
      nth_error R n = Some Rn ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEP (Rn))) |--
        `(field_at_ sh (typeof e1) gfs) (eval_lvalue e1) ->
      writable_share sh ->
      PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
        local (tc_lvalue Delta e1) && 
        efield_denote Delta efs gfs &&
        local (tc_expr Delta (Ecast e2 t)) ->
      semax Delta (|>PROPx P (LOCALx Q (SEPx R))) 
        (Sassign (nested_efield e1 efs tts) e2)
          (normal_ret_assert
            (PROPx P
              (LOCALx Q
                (SEPx
                  (replace_nth n R
                    (`(field_at sh (typeof e1) gfs)
                      (`(valinject (nested_field_type2 (typeof e1) gfs)) (eval_expr (Ecast e2 t))) 
                        (eval_lvalue e1)
                          )))))).
Proof.
  intros.
  eapply semax_pre_simple; [| eapply semax_post'].
  Focus 1. {
    hoist_later_left.
    apply later_derives.
    rewrite insert_local.
    instantiate (1 := 
      PROPx P
      (LOCALx (`(size_compatible (typeof e1)) (eval_lvalue e1) ::
               `(align_compatible (typeof e1)) (eval_lvalue e1) ::
               `(isSome (nested_field_rec (typeof e1) gfs)) ::
               tc_expr Delta (Ecast e2 t) ::
               tc_lvalue Delta (nested_efield e1 efs tts) ::
               `eq (eval_lvalue (nested_efield e1 efs tts)) 
                 (`(offset_val (Int.repr (nested_field_offset2 (typeof e1) gfs))) (eval_lvalue e1)) ::
               `((uncompomize e (nested_field_type2 (typeof e1) gfs) =
                 typeof (nested_efield e1 efs tts))) ::
               Q) (SEPx R))).
    assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |-- local (`isptr (eval_lvalue e1))).
    Focus 1. {
      erewrite SEP_nth_isolate with (R := R) by exact H3.
      apply derives_trans with ((PROPx P (LOCALx (tc_environ Delta :: Q) SEP (Rn)) * TT)).
      - simpl; intros; normalize; cancel.
      - rewrite (add_andp _ _ H4).
        simpl; intro rho.
        unfold_lift.
        rewrite field_at__isptr.
        normalize.
    } Unfocus.
    assert (PROPx P (LOCALx (tc_environ Delta :: Q) (SEPx R)) |--
      local (`(size_compatible (typeof e1)) (eval_lvalue e1)) &&
      local (`(align_compatible (typeof e1)) (eval_lvalue e1)) &&
      !! (isSome (nested_field_rec (typeof e1) gfs)) &&
      local (tc_expr Delta (Ecast e2 t)) &&
      (local (tc_lvalue Delta (nested_efield e1 efs tts)) &&
       local (`eq (eval_lvalue (nested_efield e1 efs tts)) 
         (`(offset_val (Int.repr (nested_field_offset2 (typeof e1) gfs))) (eval_lvalue e1))) &&
       !! (uncompomize e (nested_field_type2 (typeof e1) gfs) = typeof (nested_efield e1 efs tts)))).
    Focus 1. {
      apply andp_right; [apply andp_right |].
      + erewrite SEP_nth_isolate with (R := R) by exact H3.
        apply derives_trans with ((PROPx P (LOCALx (tc_environ Delta :: Q) SEP (Rn)) * TT)).
        - simpl; intros; normalize; cancel.
        - rewrite (add_andp _ _ H4).
          simpl; intros; normalize.
          rewrite field_at__data_at_.
          normalize.
          exact H1.
      + eapply derives_trans; [exact H6 |].
        apply andp_left2.
        apply derives_refl.
      + rewrite (add_andp _ _ H6).
        rewrite (add_andp _ _ H7).
        simpl; intro rho; normalize.
        normalize.
        pose proof (eval_lvalue_nested_efield Delta e e1 efs gfs tts H2 rho).
        pose proof (tc_lvalue_nested_efield Delta e e1 efs gfs tts H2 rho).
        pose proof (typeof_nested_efield _ Delta _ efs _ _ H2 rho).
        normalize in H14.
        normalize in H15.
        rewrite (add_andp _ _ H14).
        rewrite (add_andp _ _ H15).
        rewrite (add_andp _ _ H16).
        normalize.
        normalize.
    } Unfocus.
    rewrite (add_andp _ _ H8).
    simpl; intros; normalize.
  } Unfocus.
  Focus 2. {
    eapply semax_ucdata_store_nth.
    + exact H.
    + exact H0.
    + exact H3.
    + repeat rewrite LOCAL_2_hd, <- insert_local.
      rewrite (add_andp _ _ H4).
      simpl; intro rho; normalize.
      rewrite field_at__data_at_ by exact H1.
      rewrite at_offset'_eq by (rewrite <- data_at__offset_zero; reflexivity).
      rewrite H12.
      apply andp_left2.
      normalize.
    + exact H5.
    + instantiate (1 := e).
      rewrite <- H.
      simpl; intro rho; normalize.
  } Unfocus.
  match goal with
  | |- ?L |-- ?R =>
      remember L as LL eqn:HL;
      remember R as RR eqn:HR;
      erewrite SEP_replace_nth_isolate in HL by exact H3;
      erewrite SEP_replace_nth_isolate in HR by exact H3;
      subst LL RR
  end.
  simpl; intro rho; normalize.
  apply sepcon_derives; [| apply derives_refl].
  rewrite field_at_data_at by exact H1.
  rewrite at_offset'_eq by (rewrite <- data_at_offset_zero; reflexivity).
  rewrite H13.
  normalize.
Qed.
      
