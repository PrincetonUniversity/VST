(* Copyright 2006, 2008 Andrew W. Appel, Robert Dockins and Xavier Leroy
 * This file is part of the List-machine Benchmark.
 * The List-machine Benchmark is licensed under GPLv3; see LICENSE.
 *)

Require Import Maps.

(*** Machine specification ***)

(** Abstract syntax of machine code **)

Definition var: Set := positive.
Definition var_eq: forall (v1 v2: var), {v1=v2} + {v1<>v2} := peq.
Definition V (n: nat) : var := P_of_succ_nat n.

Definition label: Set := positive.
Definition label_eq: forall (l1 l2: label), {l1=l2} + {l1<>l2} := peq.
Definition L (n: nat) : label := P_of_succ_nat n.

Inductive instr: Set :=
  | instr_jump: var -> instr
  | instr_getlabel: label -> var -> instr
  | instr_branch_if_nil: var -> label -> instr
  | instr_fetch_field: var -> nat -> var -> instr
  | instr_cons: var -> var -> var -> instr
  | instr_halt: instr
  | instr_seq: instr -> instr -> instr.

Infix ";;" := instr_seq (at level 60, right associativity).

Definition program := map instr.

(** Run-time values and environments **)

Inductive value: Set :=
  | value_label: label -> value
  | value_cons: value -> value -> value.

Definition store := map value.
Definition store_empty : store := empty value.

(** Execution of machine code **)

Inductive step: program -> store -> instr -> store -> instr -> Prop :=

  | step_seq: forall p r i1 i2 i3,
    (*----------------------------------------------------*)
      step p r ((i1 ;; i2) ;; i3) r (i1 ;; i2 ;; i3)

  | step_fetch_field_0: forall p r v1 v2 i a0 a1,
      r#v1 = Some (value_cons a0 a1) ->
    (*----------------------------------------------------*)
      step p r (instr_fetch_field v1 0 v2 ;; i) (r#v2 <- a0) i

  | step_fetch_field_1: forall p r v1 v2 i a0 a1,
      r#v1 = Some (value_cons a0 a1) ->
    (*----------------------------------------------------*)
      step p r (instr_fetch_field v1 1 v2 ;; i) (r#v2 <- a1) i

  | step_cons: forall p r v1 v2 v3 i a1 a2,
      r#v1 = Some a1 ->
      r#v2 = Some a2 ->
    (*----------------------------------------------------*)
      step p r (instr_cons v1 v2 v3 ;; i) (r#v3 <- (value_cons a1 a2)) i

  | step_branch_not_taken: forall p r v l i a1 a2,
      r#v = Some (value_cons a1 a2) ->
    (*----------------------------------------------------*)
      step p r (instr_branch_if_nil v l ;; i) r i

  | step_branch_taken: forall p r v l i i',
      r#v = Some (value_label (L 0)) ->
      p#l = Some i' ->
    (*----------------------------------------------------*)
      step p r (instr_branch_if_nil v l ;; i) r i'

  | step_jump: forall p r v l i',
      r#v = Some (value_label l) ->
      p#l = Some i' ->
    (*----------------------------------------------------*)
      step p r (instr_jump v) r i'

   | step_getlabel: forall p r l v i,
    (*----------------------------------------------------*)
      step p r (instr_getlabel l v ;; i) (r#v <- (value_label l)) i.


(* Safety property *)

Definition entry_label := L 0.

Definition start_state (p: program) (s: store) (i: instr) :=
         p#entry_label = Some i.

Inductive stepstar (p: program) : store -> instr -> store -> instr ->  Prop :=
 | stepstar_O: forall s i, stepstar p s i s i
 | stepstar_S: forall s i s' i' s'' i'',
              step p s i s' i' -> stepstar p s' i' s'' i'' -> stepstar p s i s'' i''.

Inductive step_or_halt: program -> store -> instr -> Prop :=
  | step_or_halt_step: forall p r i r' i',
      step p r i r' i' -> step_or_halt p r i
  | step_or_halt_halt: forall p r,
      step_or_halt p r instr_halt.

Definition safe (p: program) (s: store) (i: instr) :=
   forall s' i', stepstar p s i s' i' -> step_or_halt p s' i'.

Definition safe_prog (p: program) := forall s i, start_state p s i -> safe p s i.


Inductive stepN (p: program) : nat -> store -> instr -> store -> instr ->  Prop :=
 | stepN_O: forall s i, stepN p O s i s i
 | stepN_S: forall n s i s' i' s'' i'',
              step p s i s' i' -> stepN p n s' i' s'' i'' -> stepN p (S n) s i s'' i''.

Lemma stepstar_stepN : forall p s i s' i',
  stepstar p s i s' i' ->
  exists n, stepN p n s i s' i'.

  intros p s i s' i' H; induction H.
  exists 0; apply stepN_O.
  destruct IHstepstar as [n Hn].
  exists (S n).
  eapply stepN_S.
  apply H.
  apply Hn.
 Qed.

Lemma stepN_stepstar : forall p n s i s' i',
  stepN p n s i s' i' ->
  stepstar p s i s' i'.

  intros p n s i s' i' H; induction H.
  apply stepstar_O.
  eapply stepstar_S.
  apply H.
  apply IHstepN.
 Qed.


Lemma step_deterministic : forall p s i s1 s2 i1 i2,
  step p s i s1 i1 ->
  step p s i s2 i2 ->
  s1 = s2 /\ i1 = i2.

  intros p s i s1 s2 i1 i2 H1 H2.
  inversion H1; subst; inversion H2; subst;
     intuition congruence.
 Qed.

Lemma step_confluent : forall p n s s1 s2 s' i i1 i2 i',
  step p s i s1 i1 ->
  step p s i s2 i2 ->
  stepN p n s1 i1 s' i' ->
  stepN p n s2 i2 s' i'.

 intros p n s s1 s2 s' i i1 i2 i' H1 H2 H3.
 generalize (step_deterministic _ _ _ _ _ _ _ H1 H2).
 intuition; subst; auto.
 Qed.


Lemma step_triangle : forall p n1 n2 s s1 s2 i i1 i2,
  n1 <= n2 ->
  stepN p n1 s i s1 i1 ->
  stepN p n2 s i s2 i2 ->
  stepN p (n2 - n1) s1 i1 s2 i2.

  intros p n1; induction n1; simpl; intros.
  inversion H0; subst; clear H0.
  replace (n2 -0) with n2; [ auto | omega ].
  inversion H0; subst; clear H0.
  destruct n2; simpl in *.
  inversion H.
  eapply IHn1.
  omega.
  apply H4.
  inversion H1; subst; clear H1.
  destruct (step_deterministic p s i s' s'0 i' i'0); auto.
  rewrite H0; rewrite H1; auto.
 Qed.

