Require Import msl.msl_standard.
Require Import Maps.

(*** Machine specification ***)

(** Abstract syntax of machine code **)

Definition var: Set := positive.
Definition var_eq: forall (v1 v2: var), {v1=v2} + {v1<>v2} := positive_eq_dec.
Definition V (n: nat) : var := P_of_succ_nat n.

Definition label: Set := positive.
Definition label_eq: forall (l1 l2: label), {l1=l2} + {l1<>l2} := positive_eq_dec.
Definition L (n: nat) : label := P_of_succ_nat n.

Section instr_def.
  Variable X:Type.

  Inductive instr : Type :=
  | instr_assert : X -> instr

  | instr_getlabel: label -> var -> instr
  | instr_fetch_field: var -> nat -> var -> instr
  | instr_cons: var -> var -> var -> instr

  | instr_seq: instr -> instr -> instr
  | instr_if_nil : var -> instr -> instr -> instr
  | instr_call: var -> instr
  | instr_return: instr

  | instr_nil : instr.
End instr_def.

Implicit Arguments instr_assert [X].
Implicit Arguments instr_getlabel [X].
Implicit Arguments instr_fetch_field [X].
Implicit Arguments instr_cons [X].
Implicit Arguments instr_seq [X].
Implicit Arguments instr_if_nil [X].
Implicit Arguments instr_call [X].
Implicit Arguments instr_return [X].

Fixpoint fmap_instr {A B} (f:A->B) (x:instr A) : instr B :=
  match x with
  | instr_assert a => instr_assert (f a)
  | instr_getlabel l v => instr_getlabel l v
  | instr_fetch_field v1 n v2 => instr_fetch_field v1 n v2
  | instr_cons v1 v2 v3 => instr_cons v1 v2 v3
  | instr_seq i1 i2 => instr_seq (fmap_instr f i1) (fmap_instr f i2)
  | instr_if_nil v i1 i2 => instr_if_nil v (fmap_instr f i1) (fmap_instr f i2)
  | instr_call v => instr_call v
  | instr_return => instr_return
  | instr_nil => instr_nil _
  end.

(** Run-time values and environments **)

Inductive value: Set :=
  | value_label: label -> value
  | value_cons: value -> value -> value.

Definition store := map value.
Definition store_empty : store := empty value.

Definition program X := map (instr X).

Definition terminationMeasure : Type :=
  label -> store -> option nat.

Definition store_incr (r1 r2:store) :=
  forall l x,
    r1#l = Some x ->
    r2#l = Some x.

Definition termMeasure_incr (s1 s2:terminationMeasure) :=
  forall l r, s1 l r = None \/ s1 l r = s2 l r.

Module KnotInput <: KNOT_INPUT__HERED_PROP_OTH_REL.
  Definition F := program.

  Definition fmap A B (f:A->B) := map_fmap _ _ (fmap_instr f).
  Implicit Arguments fmap [A B].

  Lemma fmap_id : forall A, fmap (id A) = id (F A).
  Proof.
    intros; unfold fmap.
    extensionality x.
    induction x; simpl; auto.
    destruct o; unfold id; f_equal; auto.
    f_equal.
    induction i; simpl; auto; congruence.
  Qed.

  Lemma fmap_comp : forall A B C (f:B -> C) (g:A -> B),
    fmap f oo fmap g = fmap (f oo g).
  Proof.
    unfold fmap, compose; intros; extensionality x.
    induction x; simpl; auto.
    destruct o; unfold id; f_equal; auto.
    f_equal.
    induction i; simpl; auto; congruence.
  Qed.

  Definition Rel A (x y:F A) : Prop := x = y.
  Lemma Rel_fmap : forall A B (f:A->B) x y,
    Rel A x y -> Rel B (fmap f x) (fmap f y).
  Proof.
    unfold Rel; intros; f_equal; auto.
  Qed.

  Definition Rel_unfmap : forall A B (f:A->B) x y,
    Rel B (fmap f x) y ->
      exists y', Rel A x y' /\ fmap f y' = y.
  Proof.
    unfold Rel; intros.
    exists x; split; auto.
  Qed.

  Lemma Rel_refl : forall A x, Rel A x x.
  Proof.
    unfold Rel; intros; auto.
  Qed.

  Lemma Rel_trans : forall A x y z,
    Rel A x y -> Rel A y z -> Rel A x z.
  Proof.
    unfold Rel; intros; congruence.
  Qed.

  Definition other := (store * terminationMeasure)%type.

  Definition ORel (x y:other) : Prop :=
    store_incr (fst x) (fst y) /\
    termMeasure_incr (snd x) (snd y).

  Lemma ORel_refl : reflexive other ORel.
  Proof.
    repeat intro; split; hnf; eauto.
  Qed.

  Lemma ORel_trans : transitive other ORel.
  Proof.
    unfold ORel, store_incr, termMeasure_incr;
      repeat intro; intuition.
    destruct x; destruct y; destruct z; simpl in *.
    destruct (H2 l r); auto.
    rewrite H0.
    destruct (H3 l r); auto.
  Qed.
End KnotInput.

Module K <: KNOT__HERED_PROP_OTH_REL := Knot_HeredPropOthRel(KnotInput).
Import K.

Definition prog := K.knot.
Definition world := (prog * (store * terminationMeasure))%type.

Definition instruction := instr assert.
Definition stack := list instruction.

Infix ";;" := instr_seq (at level 60, right associativity).

Definition prog_lookup (p:prog) (l:label) : option instruction :=
  get _ (snd (unsquash p)) l.

(** Execution of machine code **)

Inductive step (t:terminationMeasure) : prog -> prog -> store -> stack -> store -> stack -> Prop :=

  | step_assert : forall p r i stk (P:assert),
      proj1_sig P (p,(r,t)) ->
    (*----------------------------------------------------*)
      step t p p r ((instr_assert P ;; i) :: stk) r (i :: stk)

  | step_getlabel: forall p r l v i stk,
    (*----------------------------------------------------*)
      step t p p r ((instr_getlabel l v ;; i) :: stk) (r#v <- (value_label l)) (i :: stk)

  | step_fetch_field_0: forall p r v1 v2 i a0 a1 stk,
      r#v1 = Some (value_cons a0 a1) ->
    (*----------------------------------------------------*)
      step t p p r ((instr_fetch_field v1 0 v2 ;; i) :: stk) (r#v2 <- a0) (i :: stk)

  | step_fetch_field_1: forall p r v1 v2 i a0 a1 stk,
      r#v1 = Some (value_cons a0 a1) ->
    (*----------------------------------------------------*)
      step t p p r ((instr_fetch_field v1 1 v2 ;; i) :: stk) (r#v2 <- a1) (i :: stk)

  | step_cons: forall p r v1 v2 v3 i a1 a2 stk,
      r#v1 = Some a1 ->
      r#v2 = Some a2 ->
    (*----------------------------------------------------*)
      step t p p r ((instr_cons v1 v2 v3 ;; i) :: stk) (r#v3 <- (value_cons a1 a2)) (i :: stk)

  | step_seq: forall p r i1 i2 i3 stk,
    (*----------------------------------------------------*)
      step t p p r (((i1 ;; i2) ;; i3) :: stk) r ((i1 ;; i2 ;; i3) :: stk)

  | step_if_nil1 : forall p r v i1 i2 i stk,
      r#v = Some (value_label (L 0)) ->
    (*----------------------------------------------------*)
      step t p p r ((instr_if_nil v i1 i2 ;; i) :: stk) r ((i1 ;; i) :: stk)

  | step_if_nil2 : forall p r v i1 i2 i a1 a2 stk,
      r#v = Some (value_cons a1 a2) ->
    (*----------------------------------------------------*)
      step t p p r ((instr_if_nil v i1 i2 ;; i) :: stk) r ((i2 ;; i) :: stk)

  | step_call : forall p p' r v l i i' stk,
      r#v = Some (value_label l) ->
      prog_lookup p l = Some i' ->
      age p p' ->
    (*----------------------------------------------------*)
      step t p p' r ((instr_call v ;; i) :: stk) r ((i' ;; instr_nil _) :: i :: stk)

  | step_call_apocalypse : forall p r v i stk,
      level p = 0 ->
    (*----------------------------------------------------*)
      step t p p r ((instr_call v ;; i) :: stk) r ((instr_call v ;; i) :: stk)

  | step_return : forall p r stk i,
    (*----------------------------------------------------*)
      step t p p r ((instr_return ;; i) :: stk) r stk.

(* Safety property *)

Inductive stepstar (t:terminationMeasure) : prog -> prog -> store -> stack -> store -> stack ->  Prop :=
 | stepstar_O: forall s i p, stepstar t p p s i s i
 | stepstar_S: forall p p' p'' s i s' i' s'' i'',
              step t p p' s i s' i' -> stepstar t p' p'' s' i' s'' i'' -> stepstar t p p'' s i s'' i''.

Inductive step_or_halt (t:terminationMeasure) : prog -> store -> stack -> Prop :=
  | step_or_halt_step: forall p p' r i r' i',
      step t p p' r i r' i' -> step_or_halt t p r i
  | step_or_halt_halt: forall p r,
      step_or_halt t p r nil.

Definition safe (t:terminationMeasure) (p: prog) (s: store) (k: stack) :=
   forall p' s' k', stepstar t p p' s k s' k' -> step_or_halt t p' s' k'.

Definition safe_prog (p: program assert) (l:label) :=
  exists t, exists i,
    p#l = Some i /\
    forall n s, safe t (K.squash (n,p)) s (i::nil).

Definition eventually_halts (t:terminationMeasure) (p:prog) (r:store) (s:stack) : Prop :=
  exists p', exists r', stepstar t p p' r s r' nil.

(*****)
(* Other Stuff *)


Inductive stepN : nat -> terminationMeasure -> prog -> prog -> store -> stack -> store -> stack ->  Prop :=
 | stepN_O: forall t p s i, stepN O t p p s i s i
 | stepN_S: forall n t s i p p' p'' s' i' s'' i'',
              step t p p' s i s' i' -> stepN n t p' p'' s' i' s'' i'' -> stepN (S n) t p p'' s i s'' i''.

Lemma stepstar_stepN : forall t p p' s i s' i',
  stepstar t p p' s i s' i' ->
  exists n, stepN n t p p' s i s' i'.
Proof.
  intros t p p' s i s' i' H; induction H.
  exists 0; apply stepN_O.
  destruct IHstepstar as [n Hn].
  exists (S n).
  eapply stepN_S.
  apply H.
  apply Hn.
Qed.

Lemma stepN_stepstar : forall t p p' n s i s' i',
  stepN n t p p' s i s' i' ->
  stepstar t p p' s i s' i'.
Proof.
  intros t p p' n s i s' i' H; induction H.
  apply stepstar_O.
  eapply stepstar_S.
  apply H.
  apply IHstepN.
Qed.

Lemma step_deterministic : forall t p p1 p2 s i s1 s2 i1 i2,
  step t p p1 s i s1 i1 ->
  step t p p2 s i s2 i2 ->
  s1 = s2 /\ i1 = i2 /\ p1 = p2.
Proof.
  intros t p p1 p2 s i s1 s2 i1 i2 H1 H2.
  inversion H1; subst; inversion H2; subst; unfold age in *;
    try intuition congruence.
  rewrite knot_level in H12.
  rewrite knot_age1 in H3.
  destruct (unsquash p2).
  simpl in H12.
  subst n.
  discriminate.
  rewrite knot_level in H.
  rewrite knot_age1 in H12.
  destruct (K.unsquash p1).
  simpl in H.
  subst n.
  discriminate.
Qed.

Lemma step_confluent : forall t p p1 p2 p' n s s1 s2 s' i i1 i2 i',
  step t p p1 s i s1 i1 ->
  step t p p2 s i s2 i2 ->
  stepN n t p1 p' s1 i1 s' i' ->
  stepN n t p2 p' s2 i2 s' i'.
Proof.
 intros t p p1 p2 p' n s s1 s2 s' i i1 i2 i' H1 H2 H3.
 generalize (step_deterministic _ _ _ _ _ _ _ _ _ _ H1 H2).
 intuition; subst; auto.
Qed.

Lemma step_triangle : forall n1 n2 t p p1 p2 s s1 s2 i i1 i2,
  n1 <= n2 ->
  stepN n1 t p p1 s i s1 i1 ->
  stepN n2 t p p2 s i s2 i2 ->
  stepN (n2 - n1) t p1 p2 s1 i1 s2 i2.
Proof.
  intros n1; induction n1; simpl; intros.
  inversion H0; subst; clear H0.
  replace (n2 -0) with n2; [ auto | omega ].
  inversion H0; subst; clear H0.
  destruct n2; simpl in *.
  inversion H.
  eapply IHn1.
  omega.
  apply H4.
  inversion H1; subst; clear H1.
  destruct (step_deterministic t p p' p'0 s i s' s'0 i' i'0) as [? [? ?]]; auto.
  subst; auto.
Qed.
