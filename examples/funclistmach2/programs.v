Require Import msl.msl_standard.
Require Import Maps.
Require Import FuncListMachine.
Require Import lemmas.
Require Import hoare_total.
Require Import wp.

(* This is some tentative work-in-progress *)

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

Program Definition add_term_measure : termMeas :=
  fun r n =>
  match r#(V 1) with
  | Some x => list_length x = n
  | None => False
  end.
Next Obligation.
 destruct x as [ | x o0 x1] ; [contradiction H | ].
 destruct x; [ contradiction H | simpl in *] .
 destruct o; simpl in *;  [congruence | contradiction].
Qed.

Definition add_P' n m st :=
    list_nat_var n (V 1) st /\
    list_nat_var m (V 2) st.

Definition add_Q' n m st := list_nat_var (n+m) (V 2) st.

Definition add_P (nm:nat*nat) := store_op (add_P' (fst nm) (snd nm)).
Definition add_Q (nm:nat*nat) := store_op (add_Q' (fst nm) (snd nm)).

Definition valueTermMeas :=
  { R: value -> nat -> Prop |
    forall v n n', R v n -> R v n' -> n = n' }.

Record stdFunspec A :=
  { sfs_t     : valueTermMeas
  ; sfs_P     : A -> value -> pred prog
  ; sfs_Q     : A -> value -> pred prog
  }.

Implicit Arguments sfs_t.
Implicit Arguments sfs_P.
Implicit Arguments sfs_Q.

Program Definition value_to_store_termMeas (vt:valueTermMeas) : termMeas :=
  fun s n => match s#(V 0) with
             | Some v => proj1_sig vt v n
             | None   => False
             end.
Next Obligation.
  destruct x; simpl in *; intuition.
  destruct o; simpl in *; intuition.
  destruct vt; simpl in *.
  eauto.
Qed.

(* Define a simple calling convention for "standard"
   functions.  register 0 is for arguments and results.
   registers 1 2 3 and 4 are callee-saves registers,
   and registers >= 5 are caller-saves.

   It is not specified, but register 1 is usually
   used as a value stack.
 *)
Definition stdfun (l:label) (fs:{A:Type & stdFunspec A}) :=
  funptr l (projT1 fs * (value*value*value*value))
         (value_to_store_termMeas (sfs_t (projT2 fs)))
         (fun avs =>
           match avs with
             (a,(v1,v2,v3,v4)) =>
             EX v0:_,
             world_op
               (sfs_P (projT2 fs) a v0)
               (fun s =>
                 s#(V 0) = Some v0 /\
                 s#(V 1) = Some v1 /\
                 s#(V 2) = Some v2 /\
                 s#(V 3) = Some v3 /\
                 s#(V 4) = Some v4)
           end)
         (fun avs =>
           match avs with
             (a,(v1,v2,v3,v4)) =>
             EX v0:_,
             world_op
                (sfs_Q (projT2 fs) a v0)
                (fun s =>
                  s#(V 0) = Some v0 /\
                  s#(V 1) = Some v1 /\
                  s#(V 2) = Some v2 /\
                  s#(V 3) = Some v3 /\
                  s#(V 4) = Some v4)
           end).

Definition apply_P (fs:{ A:Type & stdFunspec A}) (x:projT1 fs) (v:value) : pred prog :=
  match v with
  | value_cons (value_label l) v' =>
       stdfun l fs && sfs_P (projT2 fs) x v'
  | _ => FF
  end.

Definition apply_Q (fs:{A :Type & stdFunspec A}) (x:projT1 fs) (v:value) : pred prog :=
  sfs_Q (projT2 fs) x v.

Program Definition apply_tm (fs:{A:Type & stdFunspec A}) : valueTermMeas :=
  fun v n =>
  match v, n with
  | value_cons (value_label l) v', S n' =>
      sfs_t (projT2 fs) v' n'
  | _, _ => False
  end.
Next Obligation.
  destruct v; simpl in *; intuition.
  discriminate.
  destruct v1; simpl in *; intuition; discriminate.
Qed.
Next Obligation.
 intros [? ?].
 inv H.
Qed.
Next Obligation.
 destruct v; simpl in *; try contradiction.
 destruct v1; simpl in *; try contradiction.
 destruct n; simpl in *; try contradiction.
 destruct n'; simpl in *; try contradiction.
 destruct fs; simpl in *.
 destruct s; simpl in *.
 destruct sfs_t0; simpl in *.
 f_equal; eapply e; eauto.
Qed.

Definition apply_fs (fs:{A:Type & stdFunspec A}) : {A:Type & stdFunspec A} :=
  existT _ (projT1 fs)
     (Build_stdFunspec (projT1 fs) (apply_tm fs) (apply_P fs) (apply_Q fs)).

Program Definition phi : map instruction :=
  set _ (set _ (set _ (set _ (set _ (set _ (empty _)

  (* The "map" wrapper function *)
  (L 5)
    ( (* push the values of V2 and V3 *)
      instr_cons (V 2) (V 1) (V 1) ;;
      instr_cons (V 3) (V 1) (V 1) ;;
      (* load the function pointer into V2 *)
      instr_fetch_field (V 0) 0 (V 2) ;;
      (* load the remainder of the list into V3 *)
      instr_fetch_field (V 0) 1 (V 3) ;;
      (* call the map worker function *)
      instr_getlabel (L 4) (V 5) ;;
      instr_call (V 5) ;;
      (* restore V3 *)
      instr_fetch_field (V 1) 0 (V 3) ;;
      instr_fetch_field (V 1) 1 (V 1) ;;
      (* restore V2 *)
      instr_fetch_field (V 1) 0 (V 2) ;;
      instr_fetch_field (V 1) 1 (V 1) ;;
      instr_return
    ))

  (* The "map" worker function *)
  (L 4)
    ( instr_if_nil (V 3)
       (*if nil, return nil *)
        ( instr_getlabel (L 0) (V 0) ;;
          instr_return )
       (*otherwise, recursive call*)
        ( (* get the head of the list *)
          instr_fetch_field (V 3) 0 (V 0) ;;
          (* call the mapping function *)
          instr_call (V 2) ;;
          (* push the mapped value *)
          instr_cons (V 0) (V 1) (V 1) ;;
          (* pop the head of the list *)
          instr_fetch_field (V 3) 1 (V 3) ;;
          (* recursive "map" call *)
          instr_getlabel (L 4) (V 5) ;;
          instr_call (V 5) ;;
          (* add the new list head *)
          instr_fetch_field (V 1) 0 (V 5) ;;
          instr_cons (V 5) (V 0) (V 0) ;;
          (* pop the stack *)
          instr_fetch_field (V 1) 1 (V 1) ;;
          instr_return
         )
       (* endif *)
    ))

  (* The "succ" function *)
  (L 3)
    ( instr_getlabel (L 0) (V 5) ;;
      instr_cons (V 5) (V 0) (V 0) ;;
      instr_return
    ))

  (* Set up a double-indirect call to succ.
     Call apply, which indirectly calls apply to
     call succ.
  *)
  (L 2)
    ( instr_getlabel (L 0) (V 0) ;;
      instr_getlabel (L 3) (V 1) ;;
      instr_getlabel (L 0) (V 2) ;;
      instr_getlabel (L 0) (V 3) ;;
      instr_getlabel (L 0) (V 4) ;;
      instr_cons (V 2) (V 0) (V 0) ;;
      instr_cons (V 2) (V 0) (V 0) ;;
      instr_cons (V 1) (V 0) (V 0) ;;
      instr_getlabel (L 1) (V 1) ;;
      instr_cons (V 1) (V 0) (V 0) ;;
      instr_call (V 1) ;;
      instr_return
    ))

  (* The "apply" function *)
  (L 1)
    ( instr_fetch_field (V 0) 0 (V 5) ;;
      instr_fetch_field (V 0) 1 (V 0) ;;
      instr_call (V 5) ;;
      instr_return
    ))

  (* An addition function *)
  (L 0)
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

Program Definition succ_fs : stdFunspec nat :=
  Build_stdFunspec nat
    (fun _ n => n = 0)
    (fun n v => !!(list_nat n v))
    (fun n v => !!(list_nat (S n) v)).

Definition succ_fs' : {A:Type & stdFunspec A} :=
  existT (fun X => stdFunspec X) nat succ_fs.

Lemma succ_verify : forall G,
  verify_prog phi G ->
  verify_prog
    phi
    (stdfun (L 3) succ_fs' && G).
Proof.
  intros.
  eapply verify_func_simple; auto.
  simpl. reflexivity.
  clear H.
Opaque get set funptr.
  simpl; intros.
  apply hoare_wp. simpl.
  intros [? ?].
  simpl. intuition.
  destruct a as [x [[[v1 v2] v3] v4]].
  destruct H0 as [v0 [? ?]].
  intuition.
  rewrite H7 in H5.
  inv H5.
  inv H3.
  simpl in H0.
  rewrite get_set_same.
  rewrite get_set_other. 2: discriminate.
  do 2 econstructor. intuition; eauto.
  inv H3.
  econstructor; split.
  2: repeat split;
    repeat (rewrite get_set_other; [ | discriminate]);
        try rewrite get_set_same; auto.
  simpl. auto.
Qed.

Section map_tm.
  Variable (f_tm : valueTermMeas).

  Fixpoint map_inner_tm (v:value) : nat -> Prop :=
    fun n =>
    match v with
      | value_label _ => n = 0
      | value_cons v1 v2 =>
          exists x1, exists x2,
           proj1_sig f_tm v1 x1 /\
           map_inner_tm v2 x2  /\
           n = 1 + x1 + 1 + x2
    end.

  Lemma map_inner_tm_fun : forall v x1 x2,
    map_inner_tm v x1 ->
    map_inner_tm v x2 ->
    x1 = x2.
  Proof.
    induction v; simpl; intros. congruence.
    destruct H as [a1 [a2 [? [? ?]]]].
    destruct H0 as [b1 [b2 [? [? ?]]]].
    subst.
    cut (a1 = b1 /\ a2 = b2).
    intuition congruence.
    split; auto.
    eapply (proj2_sig f_tm); eauto.
  Qed.
End map_tm.

Program Definition map_worker_tm (fs:{A:Type & stdFunspec A}) : termMeas :=
  fun s n =>
  match s#(V 3) with
  | Some v => map_inner_tm (sfs_t (projT2 fs)) v n
  | _ => False
  end.
Next Obligation.
 congruence.
Qed.
Next Obligation.
 simpl in *.
  destruct (x#4); simpl in *; intuition.
  eapply map_inner_tm_fun; eauto.
Qed.

Program Definition map_tm (fs:{A:Type & stdFunspec A}) : valueTermMeas :=
  fun v n =>
  match v, n with
  | value_cons _ v, S n'  =>
     map_inner_tm (sfs_t (projT2 fs)) v n'
  | _, _ => False
  end.
Next Obligation.
intros [? ?]. inv H.
Qed.
Next Obligation.
  destruct v. elim H.
  destruct n; destruct n'; try tauto.
  f_equal.
  eapply map_inner_tm_fun; eauto.
Qed.

Section map_pre_post.
  Variable A:Type.
  Variable P:A->value->pred prog.

  Fixpoint list_val_match (l:list A) (v:value) {struct l} : pred prog :=
    match l, v with
    | nil, value_label 1%positive => TT
    | x::l', value_cons v1 v2 => P x v1 && list_val_match l' v2
    | _, _ => FF
    end.
End map_pre_post.

Definition map_worker_pre (fs:{A:Type & stdFunspec A}) (x:value*label*list (projT1 fs)*value) :=
  match x with
    (v1,lab,l,v4) =>
    EX v3:_,
    world_op
      (stdfun lab fs &&
       list_val_match (projT1 fs) (sfs_P (projT2 fs)) l v3)
      (fun s =>
         s#(V 1) = Some v1 /\
         s#(V 2) = Some (value_label lab) /\
         s#(V 3) = Some v3 /\
         s#(V 4) = Some v4)
  end.

Definition map_worker_post (fs:{A:Type & stdFunspec A}) (x:value*label*list (projT1 fs)*value) :=
  match x with
    (v1,lab,l,v4) =>
    EX v0:_,
    world_op
      (stdfun lab fs &&
        list_val_match (projT1 fs) (sfs_Q (projT2 fs)) l v0)
      (fun s =>
         s#(V 0) = Some v0 /\
         s#(V 1) = Some v1 /\
         s#(V 2) = Some (value_label lab) /\
         s#(V 4) = Some v4)
  end.

Definition map_pre
  (fs:{A:Type & stdFunspec A})
  l
  (x:value) :=
  match x with
  | value_cons (value_label lab) v =>
      stdfun lab fs &&
      list_val_match (projT1 fs) (sfs_P (projT2 fs)) l v
  | _ => FF
  end.

Definition map_post
  (fs:{A:Type & stdFunspec A})
  l
  (x:value) :=
  list_val_match (projT1 fs) (sfs_Q (projT2 fs)) l x.

Definition map_spec (fs:{A:Type & stdFunspec A}) : {A:Type & stdFunspec A} :=
  existT (fun X => stdFunspec X) (list (projT1 fs))
    (Build_stdFunspec _ (map_tm fs) (map_pre fs) (map_post fs)).

Lemma map_worker_verify : forall G,
  verify_prog phi G ->
  verify_prog
    phi
    ((ALL fs:{A:Type & stdFunspec A},
         funptr (L 4) _ (map_worker_tm fs) (map_worker_pre fs) (map_worker_post fs)) && G).
Proof.
  intros.
Transparent get set.
  eapply verify_func; auto.
  simpl. reflexivity.
  clear H.
Opaque get set funptr.
  simpl; intros.
  apply hoare_wp. simpl.
  intros [? ?].
  simpl. intuition.
  destruct a as [[[v1 lab] l] v4].
  clear H2. unfold map_worker_pre in H0.
  destruct H0 as [v3 [[? ?] ?]].
  intuition.
  clear H.
  econstructor. intuition.
  eauto.
  destruct l; simpl in H2; [ left | right ].
  destruct v3; try (elim H2; fail).
  destruct l; try (elim H2; fail).
  split; auto.
  intros. inv H.
  unfold map_worker_post.
  simpl. exists (value_label 1%positive).
  intuition;
    repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  destruct v3; try (elim H2; fail).
  destruct H2.
  split. eauto.
  do 2 econstructor; intuition.
  eauto.
  hnf in H5.
  unfold map_worker_tm in H5.
  simpl in H7.
  rewrite H7 in H5. simpl in H5.
  destruct H5 as [n0 [n1 [? [? ?]]]].
  subst n.
  exists (1+n0). exists (1+n1).
  split. 2: omega.
  inv H8.
  do 5 econstructor; intuition.
  exists n0.
  econstructor.
  intuition.
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  eauto.
  2: apply H0.
  simpl.
  rewrite get_set_same; auto.
  simpl.
  instantiate (1:=(p0,(v1,(value_label lab),value_cons v3_1 v3_2,v4))).
  simpl. econstructor; intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  eauto.
  simpl in H12.
  destruct a'.
  hnf in H8. simpl in H8. subst.
  destruct a'0.
  rewrite worldNec_unfold in H11.
  destruct H11; subst.
  destruct H12; intuition.
  do 2 econstructor; intuition; eauto.
  inv H16.
  do 2 econstructor. intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  eauto.
  inv H16. inv H18.
  do 5 econstructor. exists n1.
  exists (value_cons x v1,lab,l,v4).
  intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  2: eapply pred_nec_hereditary; [ | apply H1 ]; auto.
  unfold map_worker_tm. simpl.
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  simpl. split.
  econstructor; intuition; auto.
  eapply pred_nec_hereditary; eauto.
  eapply pred_nec_hereditary; eauto.
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  split. auto.
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  simpl.
  exists n1. split. auto.
  omega.
  destruct a'. destruct a'0.
  inv H16. rewrite worldNec_unfold in H18.
  destruct H18; simpl in *; subst.
  destruct H19 as [? [? ?] ?]; intuition.
  do 2 econstructor; intuition; eauto.
  inv H23.
  do 2 econstructor; intuition;
    repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; eauto.
  inv H23.
  do 2 econstructor; intuition;
    repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; eauto.
  inv H23.
  exists (value_cons x x0); intuition.
  split; auto.
  eapply pred_nec_hereditary; eauto.
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
    repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
Qed.

Lemma map_verify : forall G,
    verify_prog phi G ->
    verify_prog
    phi
    ((ALL fs:{A:Type & stdFunspec A}, stdfun (L 5) (map_spec fs)) &&
    ((ALL fs:{A:Type & stdFunspec A},
         funptr (L 4) _ (map_worker_tm fs) (map_worker_pre fs) (map_worker_post fs))
        && G)).
Proof.
  intros.
Transparent get set.
  eapply verify_func.
  simpl. auto.
  2: apply map_worker_verify; auto.
  clear H.
Opaque get set funptr.
  simpl; intros.
  apply hoare_wp. simpl.
  intros [? ?].
  simpl. intuition.
  destruct a as [x [[[v1 v2] v3] v4]].
  destruct H0 as [v0 [? ?]]. intuition.
  rewrite H7 in H5.
  clear H H2.
  unfold map_pre in H0.
  destruct v0; try (elim H0; fail).
  destruct v0_1; try (elim H0; fail).
  destruct H0.
  do 2 econstructor; intuition; eauto.
  inv H2.
  do 2 econstructor; intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; eauto.
  inv H2.
  do 2 econstructor; intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; eauto.
  inv H2.
  do 2 econstructor; intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; eauto.
  inv H2; inv H10.
  simpl in H5.
  destruct n; try tauto.
  do 5 econstructor.
  exists n.
  exists (value_cons v3 (value_cons v2 v1),l,x,v4).
  intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  unfold map_worker_tm. simpl.
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  simpl. econstructor; intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; auto.
  eauto.
  destruct a'; destruct a'0.
  rewrite worldNec_unfold in H10.
  destruct H10; subst.
  destruct H12 as [? [? ?] ?]; intuition.
  do 2 econstructor; intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; eauto.
  inv H16.
  do 2 econstructor; intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; eauto.
  inv H16.
  do 2 econstructor; intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; eauto.
  inv H16.
  do 2 econstructor; intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; eauto.
  inv H16.
  destruct H2. simpl in *; subst.
  econstructor; intuition;
  repeat (rewrite get_set_other; [ | discriminate]);
      try rewrite get_set_same; eauto.
Qed.

Lemma apply_verify : forall G,
  verify_prog phi G ->
  verify_prog
    phi
    ((ALL fs:{A:Type & stdFunspec A}, stdfun (L 1) (apply_fs fs)) && G).
Proof.
  intros.
Transparent get set.
  eapply verify_func; auto.
  simpl. reflexivity.
  clear H.
Opaque get set funptr.
  simpl; intros.
  apply hoare_wp. simpl.
  intros [? ?].
  simpl. intuition.
  destruct a as [x [[[v1 v2] v3] v4]].
  destruct H0 as [v0 [? ?]]. intuition.
  rewrite H6 in H5.
  unfold apply_tm in H5.
  destruct v0; try tauto.
  destruct v0_1; try tauto.
  destruct n; try tauto.
  do 2 econstructor.
  intuition; eauto.
  inv H9.
  do 2 econstructor.
  intuition; eauto.
  rewrite get_set_other. 2: discriminate.
  eauto.
  inv H9.
  do 5 econstructor.
  exists n.
  exists (x,(v1,v2,v3,v4)).
  econstructor.
  intuition.
  destruct H0.
  3: apply H0.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_same. auto.
  simpl.
  simpl. rewrite get_set_same. auto.
  simpl.
  destruct H0.
  econstructor. split. eauto.
  repeat split;
  repeat (rewrite get_set_other; [ | discriminate]);
    try rewrite get_set_same; auto.
  simpl. intros. auto.
Qed.

Lemma add_verify : forall G,
  verify_prog phi G ->
  verify_prog phi (funptr (L 0) _ add_term_measure add_P add_Q && G).
Proof.
  intros. eapply verify_func_simple; auto.

Transparent get set.
  simpl. reflexivity.
  intros.
Opaque get set funptr.
  intros. apply hoare_wp.
  subst Pr Pr'. simpl.
  intros [? ?].
  destruct a as [n1 m1]; simpl in *.
  simpl; intuition.
  exists (n1,m1). simpl; split; auto.
  intuition; subst; auto.
  destruct H6.
  hnf in H4, H6. simpl V in *.
  case_eq (s#2); intros;
    rewrite H8 in H4; try tauto.
  case_eq (s#3); intros;
    rewrite H9 in H6; try tauto.
  unfold add_term_measure in H7.
  simpl in H7; rewrite H8 in H7.
  inv H7.
  exists v; intuition.
  destruct n1; simpl in H4;
    destruct v; try tauto.
  destruct l; try tauto.
  left; simpl; intuition.
  hnf. simpl. rewrite H9. auto.
  destruct v1; try tauto.
  destruct l; try tauto.
  simpl in *.
  right; simpl; intuition.
  eauto.
  do 2 econstructor; intuition.
  inv H7.
  do 2 econstructor; intuition.
  rewrite get_set_other. 2: discriminate. eauto.
  inv H7.
  do 2 econstructor; intuition.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_same. auto.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_other. 2: discriminate.
  eauto.
  inv H7. inv H10.
  exists (L 0). exists (nat * nat)%type.
  exists add_term_measure.
  do 2 econstructor.
  exists (list_length v2).
  exists (n1, S m1).
  intuition.
  rewrite get_set_same. auto.
  unfold add_term_measure; simpl.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_other. 2: discriminate.
  rewrite get_set_same. auto.
  apply H2.
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
  destruct a' as [? ?].
  inv H7. simpl in *.
  destruct a'0 as [? ?].
  intuition; subst.
  apply worldNec_unfold in H10. destruct H10; subst.
  hnf in H13. hnf.
  simpl V in *.
  destruct (s1#3).
  replace (S n1 + m1) with (n1 + S m1) by omega. auto.
  auto.
Qed.

Program Definition main_tm : termMeas :=
  fun _ n => n = 5.

Let PROG_G :=
  (funptr (L 2) unit main_tm
                     (fun _ => TT)
                     (fun _ => store_op (fun r => exists v, r#(V 0) = Some v /\ list_nat 3 v))) &&
  ((stdfun (L 3) succ_fs') &&
   ((ALL fs:{A:Type & stdFunspec A}, stdfun (L 1) (apply_fs fs)) &&
    ((funptr (L 0) _ add_term_measure add_P add_Q) && TT))).

Lemma main_verify :
  verify_prog phi PROG_G.
Proof.
  unfold PROG_G.
  eapply verify_func_simple.
Transparent get set.
  simpl. reflexivity.
  2: apply succ_verify.
  2: apply apply_verify.
  2: apply add_verify.
  2: repeat intro; hnf; auto.
  intros.
Opaque get set funptr list_nat.
  apply hoare_wp; subst.
  simpl. intros [? ?]. subst Pr Pr'.
  simpl; intuition.
  inv H5.
  inv H7; inv H9; inv H10; inv H11; inv H12.
  clear H H0 H2 H8.
  do 2 econstructor; intuition;
      repeat (rewrite get_set_other; [ | discriminate]);
        try rewrite get_set_same; auto.
  inv H.
  do 2 econstructor; intuition;
      repeat (rewrite get_set_other; [ | discriminate]);
        try rewrite get_set_same; auto.
  inv H.
  do 2 econstructor; intuition;
      repeat (rewrite get_set_other; [ | discriminate]);
        try rewrite get_set_same; auto.
  inv H. inv H0.
  do 2 econstructor; intuition;
      repeat (rewrite get_set_other; [ | discriminate]);
        try rewrite get_set_same; auto.
  inv H.
  repeat (rewrite get_set_other; [ | discriminate]);
    try rewrite get_set_same; auto.
  do 5 econstructor.
  exists 2.
  evar (x1:value).
  evar (x2:value).
  evar (x3:value).
  evar (x4:value).
  exists (2,(x1,x2,x3,x4)).
  subst x1 x2 x3 x4.
  intuition.
  2: apply (H4 (apply_fs succ_fs')).
  simpl.
  repeat (rewrite get_set_other; [ | discriminate]);
    try rewrite get_set_same; auto.
  simpl.
  repeat (rewrite get_set_other; [ | discriminate]);
    try rewrite get_set_same; auto.
  econstructor; split.
  2: repeat split;
   repeat (rewrite get_set_other; [ | discriminate]);
    try rewrite get_set_same; auto.
  unfold apply_P.
  simpl. intuition.
Transparent list_nat.
  simpl. auto.
Opaque list_nat.
  simpl in H2.
  destruct H2.
  hnf in H. simpl in H. subst.
  destruct a'0.
  intuition.
  exists x. split; auto.
Qed.

Lemma main_totally_correct :
  forall r c,
    phi#(L 2) = Some c ->
    exists n', exists p', exists r',
      stepstar (K.squash (n',phi)) p'
        r ((c ;; instr_assert FF)::nil)
        r' nil /\
        exists v, r'#(V 0) = Some v /\ list_nat 3 v.
Proof.
  intros.
  generalize (verify_totally_correct PROG_G unit (fun _ => TT)
    (fun _ => store_op (fun r => exists v, r#(V 0) = Some v /\ list_nat 3 v))
    phi (L 2) main_tm tt); intros.
  spec H0. apply main_verify.
  spec H0. unfold PROG_G. hnf; simpl; intuition.
  spec H0 r. spec H0. intros; hnf. auto.
  spec H0 5.
  spec H0 c.
  spec H0. simpl; auto.
  spec H0. auto.
  destruct H0 as [p' [r' [? ?]]].
  econstructor.
  exists p'. exists r'.
  split; eauto.
  destruct H1; auto.
Qed.

(* For every store satisfying the addition precondition,
   calling the addition function will halt with a store
   satisfing the postcondition.
 *)

Transparent list_nat.
Lemma addition_totally_correct :
  forall r n m c,
    add_P' n m r ->
    phi#(L 0) = Some c ->
    exists n', exists p', exists r',
      stepstar (K.squash (n',phi)) p'
        r ((c ;; instr_assert FF)::nil)
        r' nil /\
      add_Q' n m r'.
Proof.
  intros.
  generalize (verify_totally_correct (funptr (L 0) _ add_term_measure add_P add_Q && TT) _ add_P add_Q phi (L 0) add_term_measure (n,m)); intros.
  spec H1. apply add_verify.
  repeat intro; hnf; auto.
  spec H1. hnf; simpl; intuition.
  spec H1 r. spec H1.
  simpl; intuition.
  spec H1 n c.
  spec H1.
  destruct H. simpl.
  unfold list_nat_var in *.
  simpl in *.
  destruct (r#2); auto.

  clear - H.
  revert v H; induction n; simpl; intros;
    destruct v; try tauto.
  destruct v1; try tauto.
  destruct l; try tauto.
  simpl. f_equal. auto.
  spec H1; auto.
  destruct H1 as [p' [r' [? ?]]].
  do 3 econstructor; split; eauto.
  destruct H2; auto.
Qed.
