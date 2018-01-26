Require Import VST.floyd.base.
Require Import VST.floyd.client_lemmas.
Require Import VST.floyd.assert_lemmas.
Require Import VST.floyd.closed_lemmas.
Require Import VST.floyd.canonicalize.
Require Import VST.floyd.forward_lemmas.
Require Import VST.floyd.call_lemmas.
Require Import VST.floyd.extcall_lemmas.
Require Import VST.floyd.type_id_env.

Local Open Scope logic.

Inductive local2list:
  list (environ -> Prop) -> list (ident * val) -> list (ident * (type * val)) -> list (environ -> Prop) -> Prop :=
  | local2list_nil:
      local2list nil (nil) (nil) nil
  | local2list_temp_var: forall v i Q T1 T2 Q',
      local2list Q T1 T2 Q'->
      local2list (`(eq v) (eval_id i) :: Q) (cons (i, v) T1) T2 Q'
  | local2list_gl_var: forall v i t Q T1 T2 Q',
      local2list Q T1 T2 Q'->
      local2list (`(eq v) (eval_var i t) :: Q) T1 (cons (i, (t, v)) T2) Q'
  | local2list_unknown: forall Q0 Q T1 T2 Q',
      local2list Q T1 T2 Q'->
      local2list (Q0 :: Q) T1 T2 (Q0 :: Q').
(* repeat constructor will try the first succesful tactic. So local2list_temp_ *)
(* var, local2list_gl_var will be used whenever is possible before local2list_*)
(* unknown.                                                                     *)

Module TEST.
Goal False.
evar (T1: list (ident * val)).
evar (T2: list (ident * (type * val))).
evar (Q' : list (environ -> Prop)).

assert (local2list  ((`(eq Vundef) (eval_id 1%positive)) :: (`(eq (Vint (Int.repr 1))) (eval_id 1%positive)) ::
   (`(eq 1 3)) :: nil)
  T1 T2 Q').
subst T1 T2 Q'.
repeat constructor; repeat simpl; auto.
simpl in H.
Abort.

Goal False.
evar (T1: list (ident * val)).
evar (T2: list (ident * (type * val))).
evar (Q' : list (environ -> Prop)).
assert (local2list ((`(eq Vundef) (eval_id 1%positive))::nil) T1 T2 Q').
subst T1 T2 Q'.
repeat constructor; repeat simpl; auto.
Abort.
End TEST.

Definition localtempD (p : (ident * val)) := let (i, v) := p in `(eq v) (eval_id i).
Definition localvarD (p : ident * (type * val))  := let (i, tv) := p in `(eq (snd tv)) (eval_var i (fst tv)).

Definition LocallistD (T1: list (ident * val)) (T2: list (ident * (type * val))) (Q: list (environ -> Prop)) :=
  map localtempD T1 ++ map localvarD T2 ++ Q.

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


Lemma local2list_soundness: forall P Q R T1 T2 Q',
  local2list Q T1 T2 Q' ->
  PROPx P (LOCALx Q (SEPx R)) = PROPx P (LOCALx (LocallistD T1 T2 Q') (SEPx R)).
Proof.
  intros.
  apply pred_ext.
* induction H.
  + auto.
  + eapply derives_trans.
    - rewrite <- insert_local.
      apply andp_derives; [apply derives_refl | exact IHlocal2list].
    - rewrite insert_local. auto.
  + eapply derives_trans.
    - rewrite <- insert_local.
      apply andp_derives; [apply derives_refl | exact IHlocal2list].
    - rewrite insert_local.
      apply LOCALx_shuffle.
      intros. unfold LocallistD in *.
      simpl.
      repeat rewrite in_app in *. simpl in *. intuition.
  + eapply derives_trans.
    - rewrite <- insert_local.
      apply andp_derives; [apply derives_refl | exact IHlocal2list].
    - rewrite insert_local.
      apply LOCALx_shuffle. intros.
      unfold LocallistD in *. repeat rewrite in_app in *. simpl in *.
      intuition.
*induction H.
  + auto.
  + rewrite <- insert_local.
Admitted.

Fixpoint locallist2ptree {A : Type} (l : list (ident * A)) (p : PTree.t A) (e : list Prop) : ((PTree.t A) * (list Prop)) :=
match l with
| (id, v) :: t => match (p ! id) with
                    | Some (v2) => locallist2ptree t p ((v = v2) :: e)
                    | None => locallist2ptree t (PTree.set id v p) e
                  end
| nil => (p, e)
end.
