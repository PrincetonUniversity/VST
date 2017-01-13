Require Import msl.msl_standard.
Require Import Maps.
Require Import FuncListMachine.
Require Import lemmas.
Require Import hoare_total.
Require Import wp.

Fixpoint list_nat (n:nat) (x:value) {struct n} :=
  match n, x with
  | 0, value_label 1%positive => True
  | S n', value_cons (value_label 1%positive) x' => list_nat n' x'
  | _, _ => False
  end.

Fixpoint list_length (x:value) :=
  match x with
  | value_cons _ x' => S (list_length x')
  | _ => 0
  end.

Definition list_nat_var (n:nat) (v:var) (r:store) :=
  match r#v with
  | None => False
  | Some x => list_nat n x
  end.

Definition add_term_measure (_:label) (r:store) :=
  match r#(V 1) with
  | Some x => Some (list_length x)
  | None => None
  end.

Definition add_P' n m st :=
    list_nat_var n (V 1) st /\
    list_nat_var m (V 2) st.

Definition add_Q' n m st := list_nat_var (n+m) (V 2) st.

Definition add_P (nm:nat*nat) := store_op (add_P' (fst nm) (snd nm)).
Definition add_Q (nm:nat*nat) := store_op (add_Q' (fst nm) (snd nm)).

(* Destructively add the unary-enocded natural numbers
   stored in V 1 and V 2, putting the result in V 2
 *)
Program Definition add_phi : map instruction :=
  set _ (empty _) (L 0)
    ( instr_assert (EX nm:_, add_P nm) ;;
      instr_if_nil (V 1)
        (*then *) (
          instr_return
        ) (*else *) (
          (instr_fetch_field (V 1) 0 (V 3) ;;
          instr_fetch_field (V 1) 1 (V 1) ;;
          instr_cons (V 3) (V 2) (V 2)) ;;
          instr_getlabel (L 0) (V 0) ;;
          (instr_call (V 0) ;;
           instr_return)
        )
    ).
Next Obligation.
  unfold hereditary; intros.
(*  apply boxy_i; auto.
  simpl; intros.*)
  destruct a as [? [? ?]].
  destruct a' as [? [? ?]].
  destruct H0 as [[n m] [_ [? _]]].
  simpl in *.
  unfold add_P' in *. exists (n,m); simpl in *.
  unfold age, age1 in H. simpl in H.
  revert H; case_eq (age1 k); intros; inv H1. auto.
Qed.
Next Obligation.
  apply boxy_i; auto.
  simpl; intros.
  destruct w as [? [? ?]].
  destruct w' as [? [? ?]].
  destruct H0 as [[n m] [_ [? _]]].
  rewrite K.expandM_spec in H.
  destruct H. destruct H1. simpl in *.
  exists (n,m). split; auto. split; auto.
  simpl.
  destruct H0; split.
  hnf in H0. hnf; simpl V in *.
  hnf in H1.
  case_eq (s#2); intros;
    rewrite H4 in H0; try tauto.
  apply H1 in H4. rewrite H4; auto.
  hnf in H3. hnf; simpl V in *.
  case_eq (s#3); intros;
    rewrite H4 in H3; try tauto.
  apply H1 in H4. rewrite H4; auto.
Qed.

Lemma add_verify :
  verify_prog add_term_measure (funptr (L 0) _ add_P add_Q && TT) add_phi (funptr (L 0) _ add_P add_Q && TT).
Proof.
  eapply verify_func.

  simpl. reflexivity.
  simpl; intros.
  destruct a as [n m]. simpl in *.
  destruct H0 as [_ [[? ?] _]].
  unfold add_term_measure.
  hnf in H0.
  simpl V in *.
  destruct (r#2).
  econstructor; eauto.
  elim H0.
  intros.

Opaque get set funptr.
  apply hoare_wp.
  rewrite andp_comm.
  rewrite TT_and.
  apply boxy_funptr.

  subst Pr Pr'.
  intros [? [? ?]].
  destruct a as [n1 m1]; simpl in *.
  simpl; intuition.
  destruct a' as [? [? ?]].
  exists (n1,m1). simpl; split; auto. split; auto.
  apply worldNec_unfold in H3.
  intuition; subst; auto.
  destruct H1.
  hnf in H1, H3. simpl V in *.
  case_eq (s#2); intros;
    rewrite H6 in H1; try tauto.
  exists v; split; auto.
  case_eq (s#3); intros;
    rewrite H7 in H3; try tauto.
  unfold add_term_measure in H2.
  simpl in H2; rewrite H6 in H2.
  destruct n1; simpl in H1;
    destruct v; try tauto.
  destruct l; try tauto.
  simpl in H2. inv H2.
  left; simpl; intuition.
  hnf. simpl. rewrite H7. auto.
  destruct v1; try tauto.
  destruct l; try tauto.
  simpl in *.
  right; simpl; intuition.
  eauto.
  do 2 econstructor; intuition.
  inv H8.
  do 2 econstructor; intuition.
  rewrite get_set_other. 2: discriminate. eauto.
  inv H8.
  do 2 econstructor; intuition.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_same. auto.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_other. 2: discriminate.
  eauto.
  inv H8. inv H9.
  exists (L 0). exists (nat * nat)%type.
  do 2 econstructor.
  exists (list_length v2).
  exists (n1, S m1).
  intuition.
  rewrite get_set_same. auto.
  unfold add_term_measure; simpl.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_same. auto.
  injection H2; omega.
  apply H10.
  simpl; intuition.
  split; hnf; simpl.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_same. auto.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_same. auto.
  exists (list_length v2).
  unfold add_term_measure. simpl.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_same. auto.
  split; auto. injection H2; omega.
  destruct a' as [? [? ?]].
  hnf in H8. simpl in H8.
  destruct H8; subst.
  destruct a'0 as [? [? ?]].
  rewrite worldNec_unfold in H9.
  intuition; subst s1 t0.
  destruct H10 as [_ [? _]].
  simpl in H9.
  unfold add_Q' in *. simpl.
  replace (S (n1 + m1)) with (n1 + S m1) by omega.
  auto.

  repeat intro. hnf; auto.
Qed.

(* For every store satisfying the addition precondition,
   calling the addition function will halt with a store
   satisfing the postcondition.
 *)

Lemma addition_totally_correct :
  forall r n m,
    add_P' n m r ->
    exists n', exists p', exists r',
      stepstar add_term_measure (K.squash (n',add_phi)) p'
        r ((instr_getlabel (L 0) (V 0) ;; instr_call (L 0) ;; instr_return ;; instr_nil _)::nil)
        r' nil /\
      add_Q' n m r'.
Proof.
  intros.
  destruct (verify_totally_correct add_term_measure (funptr (L 0) _ add_P add_Q && TT) _ add_P add_Q add_phi (L 0) (n,m))
    with (r:=r).
  2: apply add_verify.
  intros [? ?].
  apply boxy_i; auto.
  hnf; unfold add_Q, add_Q'; simpl; intros.
  destruct w as [? [? ?]]. destruct w' as [? [? ?]].
  intuition.
  hnf in H1.
  case_eq (s#3); intros.
  rewrite H3 in H1.
  rewrite K.expandM_spec in H0.
  destruct H0. destruct H5.
  simpl in *.
  apply H5 in H3.
  hnf. rewrite H3. auto.
  rewrite H3 in H1; tauto.
  hnf; intros. destruct H0; auto.
  simpl; intuition.
  destruct H; split; unfold list_nat_var in *.
  rewrite get_set_other. 2: discriminate.
  destruct (r#(V 1)); auto.
  rewrite get_set_other. 2: discriminate.
  destruct (r#(V 2)); auto.
  destruct H0 as [p' [r' [? ?]]].
  exists x; exists p'; exists r'; split; auto.
  hnf in H1. simpl in *; intuition.
Qed.

Print Assumptions addition_totally_correct.
