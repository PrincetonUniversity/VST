Require Import floyd.base.
Require Import floyd.type_induction.
Require Import floyd.fieldlist.
Require Import floyd.jmeq_lemmas.
Require Import Coq.Logic.JMeq.

Definition proj_struct (i : ident) (m : members) {A: ident * type -> Type} (v: compact_prod (map A m)) (d: A (i, field_type2 i m)): A (i, field_type2 i m).
Proof.
  destruct m as [| (i0, t0) m]; [exact d |].
  unfold field_type2 in *.
  revert i0 t0 v d; induction m as [| (i1, t1) m]; intros.
  + simpl in *.
    if_tac.
    - subst; exact v.
    - exact d.
  + change (field_type i ((i0, t0) :: (i1, t1) :: m)) with
      (if ident_eq i i0 then Errors.OK t0 else field_type i ((i1, t1) :: m)) in *.
    if_tac.
    - subst; exact (fst v).
    - exact (IHm i1 t1 (snd v) d).
Defined.

Definition proj_union (i : ident) (m : members) {A: ident * type -> Type} (v: compact_sum (map A m)) (d: A (i, field_type2 i m)): A (i, field_type2 i m).
Proof.
  destruct m as [| (i0, t0) m]; [exact d |].
  unfold field_type2 in *.
  revert i0 t0 v d; induction m as [| (i1, t1) m]; intros.
  + simpl in *.
    if_tac.
    - subst; exact v.
    - exact d.
  + change (field_type i ((i0, t0) :: (i1, t1) :: m)) with
      (if ident_eq i i0 then Errors.OK t0 else field_type i ((i1, t1) :: m)) in *.
    if_tac.
    - subst; destruct v as [v | v].
      * exact v.
      * exact d.
    - destruct v as [v | v].
      * exact d.
      * exact (IHm i1 t1 v d).
Defined.

Definition union_val {m: members} {A} i (v: A (i, field_type2 i m)) (d: forall it, A it) : compact_sum (map A m).
Proof.
  unfold field_type2 in v.
  destruct m as [| (i0, t0) m]; [exact tt |].
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl in v |- *.
    if_tac in v.
    - subst; exact v.
    - exact (d (i0, t0)).
  + simpl in v |- *.
    if_tac in v.
    - subst.
      exact (inl v).
    - exact (inr (IHm i1 t1 v)).
Defined.

Definition members_union_inj {m: members} {A} (v: compact_sum (map A m)) : ident * type.
Proof.
  destruct m as [| (i0, t0) m]; [exact (1%positive, Tvoid) |].
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + exact (i0, t0).
  + destruct v.
    - exact (i0, t0).
    - exact (IHm i1 t1 c).
Defined.

Lemma members_union_inj_in_members: forall m A (v: compact_sum (map A m)),
  m <> nil ->
  in_members (fst (members_union_inj v)) m.
Proof.
  intros.
  destruct m as [| (i0, t0) m]; [congruence |].
  clear H.
  revert i0 t0 v; induction m as [| (i1, t1) m]; intros.
  + simpl.
    left; simpl.
    auto.
  + destruct v.
    - simpl.
      left; simpl.
      auto.
    - right.
      apply IHm.
Qed.

Lemma members_unions_inj_eq_spec: forall i0 t0 i1 t1 m A0 A1 (v0: compact_sum (map A0 ((i0, t0) :: (i1, t1) :: m))) (v1: compact_sum (map A1 ((i0, t0) :: (i1, t1) :: m))),
  members_no_replicate ((i0, t0) :: (i1, t1) :: m) = true ->
  (members_union_inj v0 = members_union_inj v1 <->
  match v0, v1 with
  | inl _, inl _ => True
  | inr v0, inr v1 => members_union_inj (v0: compact_sum (map A0 ((i1, t1) :: m))) = members_union_inj (v1: compact_sum (map A1 ((i1, t1) :: m)))
  | _, _ => False
  end).
Proof.
  intros.
  destruct v0 as [v0 | v0];
  [ change (members_union_inj (inl v0: compact_sum (map A0 ((i0, t0) :: (i1, t1) :: m)))) with (i0, t0)
  | change (members_union_inj (inr v0: compact_sum (map A0 ((i0, t0) :: (i1, t1) :: m)))) with
     (members_union_inj (v0: compact_sum (map A0 ((i1, t1) :: m))))];
  (destruct v1 as [v1 | v1];
  [ change (members_union_inj (inl v1: compact_sum (map A1 ((i0, t0) :: (i1, t1) :: m)))) with (i0, t0)
  | change (members_union_inj (inr v1: compact_sum (map A1 ((i0, t0) :: (i1, t1) :: m)))) with
     (members_union_inj (v1: compact_sum (map A1 ((i1, t1) :: m))))]).
  + tauto.
  + pose proof members_union_inj_in_members ((i1, t1) :: m) A1 v1.
    spec H0; [congruence |].
    split; [intros | tauto].
    rewrite <- H1 in H0; unfold fst in H0.
    rewrite members_no_replicate_ind in H.
    tauto.
  + pose proof members_union_inj_in_members ((i1, t1) :: m) A0 v0.
    spec H0; [congruence |].
    split; [intros | tauto].
    rewrite H1 in H0; unfold fst in H0.
    rewrite members_no_replicate_ind in H.
    tauto.
  + tauto.
Qed.

Lemma proj_union_union_val: forall i m A v d (d0: A (i, field_type2 i m)),
  in_members i m ->
  proj_union i m (union_val i v d) d0 = v.
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [inversion H |].
  revert i0 t0 v d0 H; induction m as [| (i1, t1) m]; intros.
  + inversion H; [subst | tauto].
    simpl in v, d0 |- *.
    clear H.
    if_tac; [| congruence].
    unfold eq_rect_r.
    rewrite <- !eq_rect_eq.
    auto.
  + simpl in v, d0 |- *; subst.
    if_tac.
    - subst;
      unfold eq_rect_r.
      rewrite <- !eq_rect_eq.
      auto.
    - destruct H; [unfold fst in H; congruence |].
      exact (IHm i1 t1 v d0 H).
Qed.

Lemma members_union_inj_union_val: forall A i m (v0: A (i, field_type2 i m)) (v: compact_sum (map A m)) d,
  members_no_replicate m = true ->
  fst (members_union_inj v) = i ->
  members_union_inj v = members_union_inj (union_val i v0 d).
Proof.
  unfold field_type2.
  intros A i m v0 v d NO_REPLI ?.
  destruct m as [| (i0, t0) m]; [auto |].
  revert i0 t0 v0 v H NO_REPLI; induction m as [| (i1, t1) m]; intros.
  + simpl in H; subst.
    auto.
  + simpl in H, v0, v |- *.
    destruct (ident_eq i i0).
    - subst.
      destruct v as [v | v].
      * unfold fst in H; subst.
        unfold eq_rect_r; rewrite <- !eq_rect_eq.
        auto.
      * pose proof members_union_inj_in_members ((i1, t1) :: m) _ v.
        spec H0; [congruence |].
        replace (fst (@members_union_inj ((i1, t1) :: m) _ v)) with i0 in H0 by exact H.
        rewrite members_no_replicate_ind in NO_REPLI; tauto.
    - destruct v as [v | v].
      * unfold fst in H; congruence.
      * apply IHm; [auto | rewrite members_no_replicate_ind in NO_REPLI; tauto].
Qed.

Lemma proj_struct_gen: forall {A} i m d (gen: forall it, A it),
  in_members i m ->
  members_no_replicate m = true ->
  proj_struct i m (compact_prod_gen gen m) d = gen (i, field_type2 i m).
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [inversion H |].
  revert i0 t0 H H0 d; induction m as [| (i1, t1) m]; intros.
  + destruct H; [| inversion H].
    simpl in d, H |- *; subst.
    if_tac; [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
  + destruct H.
    - simpl in d, H |- *; subst.
      if_tac; [| congruence].
      unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
    - pose proof in_members_tail_no_replicate _ _ _ _ H0 H.
      simpl in d, H |- *; if_tac; [congruence |].
      apply IHm; auto.
      rewrite members_no_replicate_ind in H0.
      tauto.
Qed.

Lemma proj_union_gen: forall {A} i m d (gen: forall it, A it),
  i = fst (members_union_inj (compact_sum_gen gen m)) ->
  m <> nil ->
  members_no_replicate m = true ->
  proj_union i m (compact_sum_gen gen m) d = gen (i, field_type2 i m).
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [congruence |].
  destruct m as [| (i1, t1) m].
  + simpl in d, H |- *; subst.
    if_tac; [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
  + simpl in H; subst.
    simpl in d |- *; subst.
    if_tac; [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
Qed.

Module compact_prod_sum.

Export floyd.fieldlist.fieldlist.

Definition proj_struct: forall (i : ident) (m : members) {A: ident * type -> Type} (v: compact_prod (map A m)) (d: A (i, field_type i m)), A (i, field_type i m)
:= @proj_struct.

Definition proj_union: forall (i : ident) (m : members) {A: ident * type -> Type} (v: compact_sum (map A m)) (d: A (i, field_type i m)), A (i, field_type i m)
:= @proj_union.

Definition members_union_inj: forall {m: members} {A} (v: compact_sum (map A m)), ident * type
:= @members_union_inj.

Definition members_union_inj_in_members: forall m A (v: compact_sum (map A m)),
  m <> nil ->
  in_members (fst (members_union_inj v)) m
:= @members_union_inj_in_members.

Definition proj_struct_gen:
  forall {A} i m d (gen: forall it, A it),
  in_members i m ->
  members_no_replicate m = true ->
  proj_struct i m (compact_prod_gen gen m) d = gen (i, field_type i m)
:= @proj_struct_gen.

Definition proj_union_gen:
  forall {A} i m d (gen: forall it, A it),
  i = fst (members_union_inj (compact_sum_gen gen m)) ->
  m <> nil ->
  members_no_replicate m = true ->
  proj_union i m (compact_sum_gen gen m) d = gen (i, field_type i m)
:= @proj_union_gen.

End compact_prod_sum.
