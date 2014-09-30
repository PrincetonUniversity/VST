Require Import floyd.base.
Require Import floyd.client_lemmas.
Require Import floyd.field_mapsto.
Require Import floyd.assert_lemmas.
Require Import floyd.closed_lemmas.
Require Import floyd.canonicalize floyd.forward_lemmas floyd.call_lemmas.
Require Import floyd.extcall_lemmas.
Require Import floyd.type_id_env.

Local Open Scope logic.

Inductive local2ptree:
  list (environ -> Prop) -> PTree.t val -> PTree.t (type * val) -> list (environ -> Prop) -> Prop :=
  | local2ptree_nil:
      local2ptree nil (PTree.empty _) (PTree.empty _) nil
  | local2ptree_temp_var: forall v i Q T1 T2 Q',
      local2ptree Q T1 T2 Q'->
      local2ptree (`(eq v) (eval_id i) :: Q) (PTree.set i v T1) T2 Q'
  | local2ptree_gl_var: forall v i t Q T1 T2 Q',
      local2ptree Q T1 T2 Q'->
      local2ptree (`(eq v) (eval_var i t) :: Q) T1 (PTree.set i (t, v) T2) Q'
  | local2ptree_unknown: forall Q0 Q T1 T2 Q',
      local2ptree Q T1 T2 Q'->
      local2ptree (Q0 :: Q) T1 T2 (Q0 :: Q').
(* repeat constructor will try the first succesful tactic. So local2ptree_temp_ *)
(* var, local2ptree_gl_var will be used whenever is possible before local2ptree_*)
(* unknown.                                                                     *)

Definition LocalD (T1: PTree.t val) (T2: PTree.t (type * val)) (Q: list (environ -> Prop)) :=
  PTree.fold (fun Q i v => `(eq v) (eval_id i) :: Q) T1
  (PTree.fold (fun Q i tv => `(eq (snd tv)) (eval_var i (fst tv)) :: Q) T2 Q).

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
  (exists i v, PTree.get i T1 = Some v /\ (Q0 = `(eq v) (eval_id i))) \/ 
  (exists i t v, PTree.get i T2 = Some (t, v) /\ (Q0 = `(eq v) (eval_var i t))) \/
  In Q0 Q ->
  In Q0 (LocalD T1 T2 Q).
Proof.
  intros.
  unfold LocalD.
  rewrite !PTree.fold_spec.
  assert ((exists (i : positive) (v : val),
             In (i, v) (PTree.elements T1) /\ Q0 = `(eq v) (eval_id i)) \/
          (exists (i : positive) (t : type) (v : val),
             In (i, (t, v)) (PTree.elements T2) /\ Q0 = `(eq v) (eval_var i t)) \/ 
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
       In (i, v) (PTree.elements T1) /\ Q0 = `(eq v) (eval_id i)) \/ (In Q0 QR))
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
  (exists i v, PTree.get i T1 = Some v /\ (Q0 = `(eq v) (eval_id i))) \/ 
  (exists i t v, PTree.get i T2 = Some (t, v) /\ (Q0 = `(eq v) (eval_var i t))) \/
  In Q0 Q.
Proof.
  intros.
  cut ((exists (i : positive) (v : val),
          In (i, v) (PTree.elements T1) /\ Q0 = `(eq v) (eval_id i)) \/
       (exists (i : positive) (t : type) (v : val),
          In (i, (t, v)) (PTree.elements T2) /\ Q0 = `(eq v) (eval_var i t)) \/ 
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
       In (i, v) (PTree.elements T1) /\ Q0 = `(eq v) (eval_id i)) \/ (In Q0 QR))
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

(*
Lemma LOCALx_potential_expand: forall Q0 

Lemma local2ptree_soundness: forall P Q R T1 T2 Q',
  local2ptree Q T1 T2 Q' ->
  PROPx P (LOCALx Q (SEPx R)) |-- PROPx P (LOCALx (LocalD T1 T2 Q') (SEPx R)).
Proof.
  intros.
  unfold LocalD.
  rewrite !PTree.fold_spec.
  induction H.
  + simpl.
    auto.
  + 
    Print PTree.
*)

Goal False.
evar (T1: PTree.t val).
evar (T2: PTree.t (type * val)).
evar (Q' : list (environ -> Prop)).

assert (local2ptree  ((`(eq Vundef) (eval_id 1%positive)) :: (`(eq (Vint (Int.repr 1))) (eval_id 1%positive)) :: 
   (`(eq 1 3)) :: nil)
  T1 T2 Q').
subst T1 T2 Q'.
repeat constructor; repeat simpl; auto.
Admitted.


(*
assert (local2ptree nil ((`(eq Vundef) (eval_id 1%positive))::nil) T1 T2 P' Q').
subst T1 T2 P' Q'.
repeat constructor; repeat simpl; auto.
*)


