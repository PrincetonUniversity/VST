Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.canonicalize.
Require Import floyd.forward_lemmas.
Require Import floyd.call_lemmas.
Require Import floyd.extcall_lemmas.
Require Import floyd.type_id_env.

Local Open Scope logic.

Inductive local2ptree:
  list (environ -> Prop) -> PTree.t val -> PTree.t (type * val) -> list (environ -> Prop) -> Prop :=
  | local2ptree_nil:
      local2ptree nil (PTree.empty _) (PTree.empty _) nil
  | local2ptree_temp_var: forall v i Q T1 T2 Q',
      local2ptree Q T1 T2 Q'->
      local2ptree (temp i v :: Q) (PTree.set i v T1) T2 Q'
  | local2ptree_gl_var: forall v i t Q T1 T2 Q',
      local2ptree Q T1 T2 Q'->
      local2ptree (var i t v :: Q) T1 (PTree.set i (t, v) T2) Q'
  | local2ptree_unknown: forall Q0 Q T1 T2 Q',
      local2ptree Q T1 T2 Q'->
      local2ptree (Q0 :: Q) T1 T2 (Q0 :: Q').
(* repeat constructor will try the first succesful tactic. So local2ptree_temp_ *)
(* var, local2ptree_gl_var will be used whenever is possible before local2ptree_*)
(* unknown.                                                                     *)

Module TEST.
Goal False.
evar (T1: PTree.t val).
evar (T2: PTree.t (type * val)).
evar (Q' : list (environ -> Prop)).

assert (local2ptree  ((`(eq Vundef) (eval_id 1%positive)) :: (`(eq (Vint (Int.repr 1))) (eval_id 1%positive)) :: 
   (`(eq 1 3)) :: nil)
  T1 T2 Q').
subst T1 T2 Q'.
repeat constructor; repeat simpl; auto.
Abort.

Goal False.
evar (T1: PTree.t val).
evar (T2: PTree.t (type * val)).
evar (Q' : list (environ -> Prop)).
assert (local2ptree ((`(eq Vundef) (eval_id 1%positive))::nil) T1 T2 Q').
subst T1 T2 Q'.
repeat constructor; repeat simpl; auto.
Abort.
End TEST.

Definition LocalD (T1: PTree.t val) (T2: PTree.t (type * val)) (Q: list (environ -> Prop)) :=
  PTree.fold (fun Q i v => temp i v :: Q) T1
  (PTree.fold (fun Q i tv => var i (fst tv) (snd tv) :: Q) T2 Q).

Lemma PTree_elements_set: forall {A} i (v: A) elm T,
  In elm (PTree.elements (PTree.set i v T)) ->
  elm = (i, v) \/ In elm (PTree.elements T).
Proof.
  intros.
  destruct elm as [i' v'].
  apply PTree.elements_complete in H.
  destruct (ident_eq i i').
  + subst.
    rewrite PTree.gss in H.
    inversion H.
    subst.
    left; auto.
  + rewrite PTree.gso in H by auto.
    right.
    apply PTree.elements_correct.
    auto.
Qed.

Lemma LocalD_sound: forall Q0 T1 T2 Q,
  (exists i v, PTree.get i T1 = Some v /\ (Q0 = temp i v)) \/ 
  (exists i t v, PTree.get i T2 = Some (t, v) /\ (Q0 = var i t v)) \/
  In Q0 Q ->
  In Q0 (LocalD T1 T2 Q).
Proof.
  intros.
  unfold LocalD.
  rewrite !PTree.fold_spec.
  assert ((exists (i : positive) (v : val),
             In (i, v) (PTree.elements T1) /\ Q0 = temp i v) \/
          (exists (i : positive) (t : type) (v : val),
             In (i, (t, v)) (PTree.elements T2) /\ Q0 = var i t v) \/ 
          In Q0 Q).
  {
    destruct H; [left | right; destruct H; [left | right]].
    + destruct H as [i [v [? ?]]].
      exists i, v.
      split; [| exact H0].
      apply PTree.elements_correct, H.
    + destruct H as [i [t [v [? ?]]]].
      exists i, t, v.
      split; [| exact H0].
      apply PTree.elements_correct, H.
    + exact H.
  }
  clear H.
  match goal with
  | |- In _ (fold_left _ _ ?QR) =>
       assert ((exists (i : positive) (v : val), 
       In (i, v) (PTree.elements T1) /\ Q0 = temp i v) \/ (In Q0 QR))
  end.
  {
    destruct H0 as [H | H]; [left; exact H | right].
    revert Q H; induction (PTree.elements T2); intros;
    destruct H as [[i [t [v [? ?]]]] | ?].
    + inversion H.
    + simpl.
      exact H.
    + simpl in H.
      destruct H.
      - subst a; simpl.
        apply IHl.
        right.
        subst Q0.
        simpl.
        left.
        reflexivity.
      - simpl.
        apply IHl.
        left.
        exact (ex_intro _ i (ex_intro _ t (ex_intro _ v (conj H H0)))).
    + simpl.
      apply IHl.
      right.
      simpl.
      right.
      exact H.
  }
  clear H0.
  match goal with
  | |- In _ (fold_left _ _ ?QR) => revert H; generalize QR; intros Res H
  end.
  revert Res H; induction (PTree.elements T1); intros;
  destruct H as [[i [v [? ?]]] | ?].
  + inversion H.
  + simpl.
    exact H.
  + simpl in H.
    destruct H.
    - subst a; simpl.
      apply IHl.
      right.
      subst Q0.
      simpl.
      left.
      reflexivity.
    - simpl.
      apply IHl.
      left.
      exact (ex_intro _ i (ex_intro _ v (conj H H0))).
  + simpl.
    apply IHl.
    right.
    simpl.
    right.
    exact H.
Qed.

Lemma LocalD_complete: forall Q0 T1 T2 Q,
  In Q0 (LocalD T1 T2 Q) ->
  (exists i v, PTree.get i T1 = Some v /\ (Q0 = temp i v)) \/ 
  (exists i t v, PTree.get i T2 = Some (t, v) /\ (Q0 = var i t v)) \/
  In Q0 Q.
Proof.
  intros.
  cut ((exists (i : positive) (v : val),
          In (i, v) (PTree.elements T1) /\ Q0 = temp i v) \/
       (exists (i : positive) (t : type) (v : val),
          In (i, (t, v)) (PTree.elements T2) /\ Q0 = var i t v) \/ 
       In Q0 Q).
  {
    intros.
    clear H.
    destruct H0; [left | right; destruct H; [left | right]].
    + destruct H as [i [v [? ?]]].
      exists i, v.
      split; [| exact H0].
      apply PTree.elements_complete, H.
    + destruct H as [i [t [v [? ?]]]].
      exists i, t, v.
      split; [| exact H0].
      apply PTree.elements_complete, H.
    + exact H.
  }
  unfold LocalD in H.
  rewrite !PTree.fold_spec in H.
  match type of H with
  | In _ (fold_left _ _ ?QR) =>
       cut ((exists (i : positive) (v : val), 
       In (i, v) (PTree.elements T1) /\ Q0 = temp i v) \/ (In Q0 QR))
  end.
  {
    intros.
    clear H.
    destruct H0 as [H | H]; [left; exact H | right].
    revert Q H; induction (PTree.elements T2); intros.
    + simpl in H.
      right.
      exact H.
    + simpl in H.
      apply IHl in H.
      destruct H; [ |simpl in H; destruct H].
      - left.
        destruct H as [i [t [v [? ?]]]].
        exists i, t, v.
        split; [| exact H0].
        simpl.
        right.
        exact H.
      - left.
        exists (fst a), (fst (snd a)), (snd (snd a)).
        subst; split; [| reflexivity].
        simpl.
        left.
        destruct a as [? [? ?]]; reflexivity.
      - right; exact H.
  }
  match type of H with
  | In _ (fold_left _ _ ?QR) => revert H; generalize QR; intros Res H
  end.
  revert Res H; induction (PTree.elements T1); intros.
  + simpl in H.
    right.
    exact H.
  + simpl in H.
    apply IHl in H.
    destruct H; [ |simpl in H; destruct H].
    - left.
      destruct H as [i [v [? ?]]].
      exists i, v.
      split; [| exact H0].
      simpl.
      right.
      exact H.
    - left.
      exists (fst a), (snd a).
      subst; split; [| reflexivity].
      simpl.
      left.
      destruct a as [? ?]; reflexivity.
    - right; exact H.
Qed.

Lemma LOCALx_expand_temp_var: forall i v T1 T2 Q Q0,
  In Q0 (LocalD (PTree.set i v T1) T2 Q) -> 
  In Q0 (temp i v :: LocalD T1 T2 Q).
Proof.
  intros.
  simpl.
  apply LocalD_complete in H.
  destruct H.
  + destruct H as [i0 [v0 [? ?]]].
    destruct (ident_eq i0 i).
    - subst.
      rewrite PTree.gss in H.
      inversion H; subst.
      left; reflexivity.
    - rewrite PTree.gso in H by auto.
      right.
      apply LocalD_sound.
      left.
      exists i0, v0.
      exact (conj H H0).
  + right.
    apply LocalD_sound.
    right.
    exact H.
Qed.

Lemma LOCALx_expand_gl_var: forall i t v T1 T2 Q Q0,
  In Q0 (LocalD T1 (PTree.set i (t, v) T2) Q) -> 
  In Q0 (var i t v :: LocalD T1 T2 Q).
Proof.
  intros.
  simpl.
  apply LocalD_complete in H.
  destruct H as [ |[ |]].
  + right.
    apply LocalD_sound.
    left.
    exact H.
  + destruct H as [i0 [t0 [v0 [? ?]]]].
    destruct (ident_eq i0 i).
    - subst.
      rewrite PTree.gss in H.
      inversion H; subst.
      left; reflexivity.
    - rewrite PTree.gso in H by auto.
      right.
      apply LocalD_sound.
      right; left.
      exists i0, t0, v0.
      exact (conj H H0).
  + right.
    apply LocalD_sound.
    right; right.
    exact H.
Qed.

Lemma LOCALx_expand_res: forall Q1 T1 T2 Q Q0,
  In Q0 (LocalD T1 T2 (Q1 ::Q)) -> 
  In Q0 (Q1 ::LocalD T1 T2 Q).
Proof.
  intros.
  simpl.
  apply LocalD_complete in H.
  destruct H as [ |[ |]].
  + right.
    apply LocalD_sound.
    left; exact H.
  + right.
    apply LocalD_sound.
    right; left; exact H.
  + simpl in H; destruct H.
    - subst; left; reflexivity.
    - right.
      apply LocalD_sound.
      right; right; exact H.
Qed.

Lemma LOCALx_shuffle: forall P Q Q' R,
  (forall Q0, In Q0 Q' -> In Q0 Q) ->
  PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx Q' (SEPx R)).
Proof.
  intros.
  induction Q'; [simpl; intro; normalize |].
  pose proof (H a (or_introl _ eq_refl)).
  rewrite <- insert_local.
  apply andp_right.
  + clear -H0.
    induction Q; [inversion H0 |].
    rewrite <- insert_local.
    simpl in H0; inversion H0.
    - subst.
      apply andp_left1.
      apply derives_refl.
    - apply andp_left2.
      apply IHQ, H.
  + apply IHQ'.
    intros.
    apply H.
    simpl.
    right.
    apply H1.
Qed.

Lemma LOCALx_expand_temp_var': forall i v T1 T2 Q Q0,
  In Q0 (LocalD (PTree.set i v T1) T2 Q) -> 
  Q0 = temp i v \/ In Q0 (LocalD (PTree.remove i T1) T2 Q).
Proof.
  intros.
  simpl.
  apply LocalD_complete in H.
  destruct H.
  + destruct H as [i0 [v0 [? ?]]].
    destruct (ident_eq i0 i).
    - subst.
      rewrite PTree.gss in H.
      inversion H; subst.
      left; reflexivity.
    - rewrite PTree.gso in H by auto.
      right.
      apply LocalD_sound.
      left.
      exists i0, v0.
      rewrite PTree.gro by auto.
      exact (conj H H0).
  + right.
    apply LocalD_sound.
    right.
    exact H.
Qed.

Lemma LocalD_subst: forall id v Q0 T1 T2 Q,
  In Q0 (LocalD (PTree.remove id T1) T2 (map (subst id v) Q)) ->
  In Q0 (map (subst id v) (LocalD T1 T2 Q)). 
Proof.
  intros.
  apply in_map_iff.
  apply LocalD_complete in H.
  destruct H; [| destruct H]; [exists Q0 | exists Q0 | ].
  + destruct H as [i0 [v0 [?H ?H]]].
    destruct (peq id i0).
    - subst.
      rewrite PTree.grs in H.
      inversion H.
    - split.
      * subst.
        unfold temp.
        autorewrite with subst.
        reflexivity.
      * apply LocalD_sound.
        left.
        exists i0, v0.
        rewrite PTree.gro in H by auto.
        auto.
  + destruct H as [i0 [t [v0 [?H ?H]]]].
    split.
    - subst.
      unfold var.
      autorewrite with subst.
      reflexivity.
    - apply LocalD_sound.
      right; left.
      exists i0, t, v0.
      auto.
  + apply in_map_iff in H.
    destruct H as [x [?H ?H]].
    exists x.
    split; [auto |].
    apply LocalD_sound.
    right; right.
    auto.
Qed.

Lemma SC_remove_subst: forall P T1 T2 R id v old,
   PROPx P
     (LOCALx (temp id v :: map (subst id `old) (LocalD T1 T2 nil))
        (SEPx (map (subst id `old) (map liftx R))))
   |-- PROPx P
         (LOCALx (LocalD (PTree.set id v T1) T2 nil) (SEPx (map liftx R))).
Proof.
  intros.
  replace (SEPx (map (subst id `old) (map liftx R))) with (SEPx (map liftx R)).
  Focus 2. {
    f_equal.
    f_equal.
    rewrite map_map.
    f_equal.
  } Unfocus.
  apply LOCALx_shuffle; intros.
  apply LOCALx_expand_temp_var' in H.
  destruct H; [left; auto | right].
  apply LocalD_subst, H.
Qed.

Lemma local2ptree_soundness: forall P Q R T1 T2 Q',
  local2ptree Q T1 T2 Q' ->
  PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx (LocalD T1 T2 Q') (SEPx R)).
Proof.
  intros.
  induction H.
  + unfold LocalD.
    rewrite !PTree.fold_spec.
    simpl.
    auto.
  + eapply derives_trans.
    - rewrite <- insert_local.
      apply andp_derives; [apply derives_refl | exact IHlocal2ptree].
    - rewrite insert_local.
      apply LOCALx_shuffle, LOCALx_expand_temp_var.
  + eapply derives_trans.
    - rewrite <- insert_local.
      apply andp_derives; [apply derives_refl | exact IHlocal2ptree].
    - rewrite insert_local.
      apply LOCALx_shuffle, LOCALx_expand_gl_var.
  + eapply derives_trans.
    - rewrite <- insert_local.
      apply andp_derives; [apply derives_refl | exact IHlocal2ptree].
    - rewrite insert_local.
      apply LOCALx_shuffle, LOCALx_expand_res.
Qed.

Fixpoint msubst_eval_expr (T1: PTree.t val) (T2: PTree.t (type * val)) (e: Clight.expr) : option val :=
  match e with
  | Econst_int i ty => Some (Vint i)
  | Econst_long i ty => Some (Vlong i)
  | Econst_float f ty => Some (Vfloat f)
  | Econst_single f ty => Some (Vsingle f)
  | Etempvar id ty => PTree.get id T1
  | Eaddrof a ty => msubst_eval_lvalue T1 T2 a 
  | Eunop op a ty => option_map (eval_unop op (typeof a)) (msubst_eval_expr T1 T2 a) 
  | Ebinop op a1 a2 ty =>
      match (msubst_eval_expr T1 T2 a1), (msubst_eval_expr T1 T2 a2) with
      | Some v1, Some v2 => Some (eval_binop op (typeof a1) (typeof a2) v1 v2) 
      | _, _ => None
      end
  | Ecast a ty => option_map (eval_cast (typeof a) ty) (msubst_eval_expr T1 T2 a)
  | Evar id ty => option_map (deref_noload ty)
                    match PTree.get id T2 with
                    | Some (ty', v) =>
                      if eqb_type ty ty'
                      then Some v
                      else None
                    | None => None
                    end
  | Ederef a ty => option_map (deref_noload ty) (option_map force_ptr (msubst_eval_expr T1 T2 a))
  | Efield a i ty => option_map (deref_noload ty) (option_map (eval_field (typeof a) i) (msubst_eval_lvalue T1 T2 a))
  end
  with msubst_eval_lvalue (T1: PTree.t val) (T2: PTree.t (type * val)) (e: Clight.expr) : option val := 
  match e with 
  | Evar id ty => match PTree.get id T2 with
                  | Some (ty', v) =>
                    if eqb_type ty ty'
                    then Some v
                    else None
                  | None => None
                  end
  | Ederef a ty => option_map force_ptr (msubst_eval_expr T1 T2 a)
  | Efield a i ty => option_map (eval_field (typeof a) i) (msubst_eval_lvalue T1 T2 a)
  | _  => Some Vundef
  end.

Lemma msubst_eval_expr_eq_aux:
  forall (T1: PTree.t val) (T2: PTree.t (type * val)) e rho v,
    (forall i v, T1 ! i = Some v -> eval_id i rho = v) ->
    (forall i t v, T2 ! i = Some (t, v) -> eval_var i t rho = v) ->
    msubst_eval_expr T1 T2 e = Some v ->
    eval_expr e rho = v
with msubst_eval_lvalue_eq_aux: 
  forall (T1: PTree.t val) (T2: PTree.t (type * val)) e rho v,
    (forall i v, T1 ! i = Some v -> eval_id i rho = v) ->
    (forall i t v, T2 ! i = Some (t, v) -> eval_var i t rho = v) ->
    msubst_eval_lvalue T1 T2 e = Some v ->
    eval_lvalue e rho = v.
Proof.
  + clear msubst_eval_expr_eq_aux.
    induction e; intros; simpl in H1 |- *; try solve [inversion H1; auto].
    - destruct (T2 ! i) as [[t0 ?]|] eqn:?; [| inversion H1].
      destruct (eqb_type t t0) eqn:HH; [| inversion H1].
      apply eqb_type_true in HH; subst.
      inversion H1.
      unfold_lift; simpl.
      erewrite H0 by eauto.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe with (v := v0) by auto.
      reflexivity.
    - erewrite msubst_eval_lvalue_eq_aux by eauto.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe with (v := v0) by auto.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e1) eqn:?; [| inversion H1].
      destruct (msubst_eval_expr T1 T2 e2) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe1 with (v := v0) by auto.
      rewrite IHe2 with (v := v1) by auto.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe with (v := v0) by auto.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_lvalue T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      erewrite msubst_eval_lvalue_eq_aux by eauto.
      reflexivity.
  + clear msubst_eval_lvalue_eq_aux.
    induction e; intros; simpl in H1 |- *; try solve [inversion H1; auto].
    - destruct (T2 ! i) as [[t0 ?]|] eqn:?; [| inversion H1].
      destruct (eqb_type t t0) eqn:HH; [| inversion H1].
      apply eqb_type_true in HH; subst.
      inversion H1.
      unfold_lift; simpl.
      erewrite H0 by eauto.
      subst.
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_expr T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      erewrite msubst_eval_expr_eq_aux by eauto;
      reflexivity.
    - unfold_lift; simpl.
      destruct (msubst_eval_lvalue T1 T2 e) eqn:?; [| inversion H1].
      inversion H1.
      rewrite IHe with (v := v0) by auto.
      reflexivity.
Qed.

Lemma local_ext: forall Q0 Q rho, In Q0 Q -> fold_right `and `True Q rho -> Q0 rho.
Proof.
  intros.
  induction Q.
  + inversion H.
  + destruct H.
    - subst; simpl in H0; unfold_lift in H0.
      tauto.
    - apply IHQ; auto.
      unfold_lift in H0.
      unfold_lift.
      simpl in H0.
      tauto.
Qed.

Lemma msubst_eval_eq_aux: forall T1 T2 Q rho,
  fold_right `and `True (LocalD T1 T2 Q) rho ->
  (forall i v, T1 ! i = Some v -> eval_id i rho = v) /\
  (forall i t v, T2 ! i = Some (t, v) -> eval_var i t rho = v).
Proof.
  intros; split; intros.
  + intros.
    assert (In (temp i v) (LocalD T1 T2 Q)).
      apply LocalD_sound.
      left.
      eauto.
    pose proof local_ext _ _ _ H1 H.
    unfold_lift in H2.
    auto.
  + intros.
    assert (In (var i t v) (LocalD T1 T2 Q)).
      apply LocalD_sound.
      right; left.
      eauto.
    pose proof local_ext _ _ _ H1 H.
    unfold_lift in H2.
    auto.
Qed.

Lemma msubst_eval_expr_eq: forall P T1 T2 Q R e v,
  msubst_eval_expr T1 T2 e = Some v ->
  PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    local (`(eq v) (eval_expr e)).
Proof.
  intros.
  apply andp_left2.
  apply andp_left1.
  simpl; intro rho.
  simpl in H.
  normalize; intros.
  destruct (msubst_eval_eq_aux _ _ _ _ H0).
  apply eq_sym, msubst_eval_expr_eq_aux with (T1 := T1) (T2 := T2); auto.
Qed.

Lemma msubst_eval_lvalue_eq: forall P T1 T2 Q R e v,
  msubst_eval_lvalue T1 T2 e = Some v ->
  PROPx P (LOCALx (LocalD T1 T2 Q) (SEPx R)) |--
    local (`(eq v) (eval_lvalue e)).
Proof.
  intros.
  apply andp_left2.
  apply andp_left1.
  simpl; intro rho.
  simpl in H.
  normalize; intros.
  destruct (msubst_eval_eq_aux _ _ _ _ H0).
  apply eq_sym, msubst_eval_lvalue_eq_aux with (T1 := T1) (T2 := T2); auto.
Qed.


