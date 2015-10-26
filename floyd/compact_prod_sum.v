Require Import List.
Require Import Coqlib msl.Coqlib2 floyd.coqlib3.
Require Import floyd.jmeq_lemmas.

Fixpoint compact_prod (T: list Type): Type :=
  match T with 
  | nil => unit
  | t :: nil => t
  | t :: T0 => (t * compact_prod T0)%type
  end.

Fixpoint compact_sum (T: list Type): Type :=
  match T with 
  | nil => unit
  | t :: nil => t
  | t :: T0 => (t + compact_sum T0)%type
  end.

Definition compact_prod_gen {A} {F} (gen: forall a: A, F a) (l: list A): compact_prod (map F l).
Proof.
  destruct l; [exact tt |].
  revert a; induction l; intros.
  + exact (gen a).
  + exact (gen a0, IHl a).
Defined.

Definition compact_sum_gen {A} {F} (filter: A -> bool) (gen: forall a: A, F a) (l: list A): compact_sum (map F l).
Proof.
  destruct l; [exact tt |].
  revert a; induction l; intros.
  + exact (gen a).
  + destruct (filter a0).
    - exact (inl (gen a0)).
    - exact (inr (IHl a)).
Defined.

Definition compact_prod_upd {A} {F} (l: list A) (v: compact_prod (map F l)) (a: A) (v0: F a) (H: forall a b: A, {a = b} + {a <> b}) : compact_prod (map F l).
Proof.
  intros.
  destruct l; [exact v |].
  revert a0 v; induction l; intros.
  + destruct (H a a0).
    - subst.
      exact v0.
    - exact v.
  + destruct (H a a1).
    - subst.
      exact (v0, (snd v)).
    - exact ((fst v), IHl a0 (snd v)).
Defined.

Lemma aux0: forall {A} {a a0: A}, In a (a0 :: nil) -> a <> a0 -> False.
Proof.
  intros.
  destruct H; [congruence | tauto].
Defined. 

Lemma aux1: forall {A} {a a0: A} {l}, In a (a0 :: l) -> a <> a0 -> In a l.
Proof.
  intros.
  destruct H; [congruence | tauto].
Defined.

Definition compact_sum_upd {A} {F} (l: list A) (v: compact_sum (map F l)) (a: A) (v0: F a) (H: forall a b: A, {a = b} + {a <> b}) : compact_sum (map F l).
Proof.
  destruct (in_dec H a l); [| exact v].
  clear v.
  destruct l; [exact tt |].
  revert a0 i; induction l; intros.
  + destruct (H a a0).
    - subst.
      exact v0.
    - pose proof aux0 i n.
      inversion H0.
  + destruct (H a a1).
    - subst.
      exact (inl v0).
    - exact (inr (IHl a0 (aux1 i n))).
Defined.

Definition proj_compact_prod {A: Type} {F: A -> Type} (a: A) (l: list A) (v: compact_prod (map F l)) (default: F a) (H: forall a b: A, {a = b} + {a <> b}) : F a.
Proof.
  destruct l; [exact default |].
  revert a0 v; induction l; intros.
  + destruct (H a a0).
    - subst.
      exact v.
    - exact default.
  + destruct (H a a1).
    - subst.
      exact (fst v).
    - exact (IHl a0 (snd v)).
Defined.

Definition proj_compact_sum {A: Type} {F: A -> Type} (a: A) (l: list A) (v: compact_sum (map F l)) (default: F a) (H: forall a b: A, {a = b} + {a <> b}) : F a.
Proof.
  destruct l; [exact default |].
  revert a0 v; induction l; intros.
  + destruct (H a a0).
    - subst.
      exact v.
    - exact default.
  + destruct (H a a1).
    - subst.
      destruct v as [v | v].
      * exact v.
      * exact default.
    - destruct v as [v | v].
      * exact default.
      * exact (IHl a0 v).
Defined.

Definition compact_sum_inj {A: Type} {F: A -> Type} {l: list A} (v: compact_sum (map F l)) (a: A) (H: forall a b: A, {a = b} + {a <> b}): Prop.
  destruct l as [| a0 l]; [exact False |].
  revert a0 v; induction l as [| a1 l]; intros.
  + exact (if H a a0 then True else False).
  + destruct v as [v | v].
    - exact (if H a a0 then True else False).
    - exact (if H a a0 then False else IHl a1 v).
Defined.

Lemma compact_sum_inj_in: forall {A: Type} {F: A -> Type} {l: list A} (v: compact_sum (map F l)) (a: A) H,
  compact_sum_inj v a H ->
  In a l.
Proof.
  intros.
  destruct l as [| a0 l]; [simpl in H0; tauto |].
  revert a0 v H0; induction l as [| a1 l]; intros.
  + simpl in H0 |- *.
    destruct (H a a0); [| tauto].
    auto.
  + destruct v as [v | v].
    - simpl in H0 |- *.
      destruct (H a a0); [| tauto].
      auto.
    - simpl in H0 |- *.
      destruct (H a a0); [tauto |].
      right.
      apply (IHl a1 v).
      exact H0.
Qed.

Lemma compact_prod_proj_gen: forall {A: Type} {F: A -> Type} {l: list A} a d (gen: forall a, F a) (H: forall a b : A, {a = b} + {a <> b}),
  In a l ->
  proj_compact_prod a l (compact_prod_gen gen l) d H = gen a.
Proof.
  intros.
  destruct l as [| a0 l]; [inversion H0 |].
  revert a0 H0; induction l as [| a1 l]; intros.
  + destruct H0; [| inversion H0].
    simpl in H |- *; subst.
    destruct (H a a); [| congruence].
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
  + destruct (H a a0).
    - simpl.
      destruct (H a a0); [| congruence].
      subst.
      unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
    - inversion H0; [congruence |].
      simpl.
      destruct (H a a0); [congruence |].
      apply IHl; auto.
Qed.
(*
Fixpoint no_replicate {A} (l: list A) :=
  match l with
  | nil => True
  | hd :: tl => (~ In hd tl) /\ no_replicate tl
  end.

Lemma members_no_replicate_no_replicate: forall m,
  members_no_replicate m = true ->
  no_replicate m.
Proof.
  intros.
  induction m.
  + constructor.
  + unfold members_no_replicate in H.
    simpl in H |- *.
    destruct (id_in_list (fst a) (map fst m)) eqn:?H.
    - inversion H.
    - apply id_in_list_false in H0.
      apply IHm in H.
      pose proof in_map fst m a.
      tauto.
Qed.
*)
(*
Fixpoint legal_compact_sum_filter {A: Type} (filter: A -> bool) (l: list A): bool :=
  match l with
  | nil => false
  | hd :: tl => if filter hd then true else legal_compact_sum_filter filter tl
  end.
*)
Lemma compact_sum_proj_gen: forall {A: Type} {F: A -> Type} {l: list A} a df (filter: A -> bool) (gen: forall a, F a) (H: forall a b : A, {a = b} + {a <> b}),
  compact_sum_inj (compact_sum_gen filter gen l) a H ->
  proj_compact_sum a l (compact_sum_gen filter gen l) df H = gen a.
Proof.
  intros.
  destruct l as [| a0 l]; [simpl in H0; tauto |].
  revert a0 H0; induction l as [| a1 l]; intros.
  + simpl in *.
    destruct (H a a0); [| tauto].
    subst.
    unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
  + simpl in *.
    destruct (filter a0).
    - destruct (H a a0); [| tauto].
      subst.
      unfold eq_rect_r; rewrite <- eq_rect_eq; auto.
    - destruct (H a a0); [tauto |].
      apply (IHl a1).
      auto.
Qed.

Lemma proj_compact_prod_JMeq: forall A i (l: list A) F1 F2 d1 d2 (v1: compact_prod (map F1 l)) (v2: compact_prod (map F2 l)) H,
  (forall i, In i l -> F1 i = F2 i) ->
  In i l ->
  JMeq v1 v2 ->
  JMeq (proj_compact_prod i l v1 d1 H) (proj_compact_prod i l v2 d2 H).
Proof.
  intros.
  destruct l as [| a0 l]; [inversion H1 |].
  revert a0 v1 v2 H0 H1 H2; induction l as [| a1 l]; intros.
  + inversion H1; [simpl in H3 | inversion H3].
    subst.
    revert v2 H1 H2; simpl.
    destruct (H i i); [intros | congruence].
    unfold eq_rect_r; rewrite <- !eq_rect_eq.
    auto.
  + assert (F1 a0 = F2 a0).
    Focus 1. {
      clear - H0.
      specialize (H0 a0).
      apply H0.
      left; simpl; auto.
    } Unfocus.
    assert (compact_prod (map F1 (a1 :: l)) = compact_prod (map F2 (a1 :: l))).
    Focus 1. {
      f_equal.
      clear - H0.
      apply list_map_exten.
      intros i ?H.
      specialize (H0 i).
      spec H0; [right; auto |].
      symmetry; auto.
    } Unfocus.
    destruct (H i a0) as [?H | ?H].
    - subst.
      clear IHl.
      revert v1 v2 H0 H2; simpl.
      destruct (H a0 a0); [intros | congruence].
      unfold eq_rect_r; rewrite <- !eq_rect_eq.
      apply JMeq_fst; auto.
    - inversion H1; [congruence |].
      revert v1 v2 H2 H3; simpl.
      destruct (H i a0); [congruence |].
      intros.
      apply (IHl a1 (snd v1) (snd v2)); auto.
      * clear - H0.
        intros i ?.
        specialize (H0 i).
        apply H0.
        right; auto.
      * apply JMeq_snd; auto.
Qed.

Lemma proj_compact_sum_JMeq: forall A i (l: list A) F1 F2 d1 d2 (v1: compact_sum (map F1 l)) (v2: compact_sum (map F2 l)) H,
  (forall i, In i l -> F1 i = F2 i) ->
  compact_sum_inj v1 i H ->
  JMeq v1 v2 ->
  JMeq (proj_compact_sum i l v1 d1 H) (proj_compact_sum i l v2 d2 H).
Proof.
  intros.
  destruct l as [| a0 l]; [simpl in H1; tauto |].
  revert a0 v1 v2 H0 H1 H2; induction l as [| a1 l]; intros.
  + simpl in H1 |- *.
    destruct (H i a0); [| tauto].
    subst.
    unfold eq_rect_r; rewrite <- !eq_rect_eq.
    auto.
  + assert (F1 a0 = F2 a0).
    Focus 1. {
      clear - H0.
      apply H0.
      left; simpl; auto.
    } Unfocus.
    assert (compact_sum (map F1 (a1 :: l)) = compact_sum (map F2 (a1 :: l))).
    Focus 1. {
      f_equal.
      clear - H0.
      apply list_map_exten.
      intros i ?H.
      specialize (H0 i).
      spec H0; [right; auto |].
      symmetry; auto.
    } Unfocus.
    simpl in H2.
    solve_JMeq_sumtype H2.
    - simpl in H1 |- *.
      destruct (H i a0); [| tauto].
      subst.
      unfold eq_rect_r; rewrite <- !eq_rect_eq.
      auto.
    - simpl in H1 |- *.
      destruct (H i a0); [tauto |].
      apply (IHl a1 c c0); auto.
      clear - H0.
      intros ?i ?.
      apply H0.
      right; auto.
Qed.

Lemma compact_sum_inj_JMeq: forall {A} (l: list A) F1 F2 (v1: compact_sum (map F1 l)) (v2: compact_sum (map F2 l)) H,
  (forall i, In i l -> F1 i = F2 i) ->
  JMeq v1 v2 ->
  (forall i, compact_sum_inj v1 i H <-> compact_sum_inj v2 i H).
Proof.
  intros.
  destruct l as [| a0 l]; [simpl; tauto |].
  revert a0 v1 v2 H0 H1; induction l as [| a1 l]; intros.
  + simpl in *.
    destruct (H i a0); [| tauto].
    tauto.
  + assert (F1 a0 = F2 a0).
    Focus 1. {
      clear - H0.
      apply H0.
      left; simpl; auto.
    } Unfocus.
    assert (compact_sum (map F1 (a1 :: l)) = compact_sum (map F2 (a1 :: l))).
    Focus 1. {
      f_equal.
      clear - H0.
      apply list_map_exten.
      intros i ?H.
      specialize (H0 i).
      spec H0; [right; auto |].
      symmetry; auto.
    } Unfocus.
    simpl in H1.
    solve_JMeq_sumtype H1.
    - simpl in *.
      destruct (H i a0); [| tauto].
      tauto.
    - simpl in *.
      destruct (H i a0); [tauto |].
      apply (IHl a1 c c0); auto.
Qed.

(*
Require Import floyd.fieldlist.



Definition proj_struct (i : ident) (m : members) {A: ident * type -> Type} (v: compact_prod (map A m)) (d: A (i, field_type2 i m)): A (i, field_type2 i m) :=
  proj_compact_prod (i, field_type2 i m) m v d member_dec.
*)

(*




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

Lemma proj_struct_JMeq: forall i m A1 A2 d1 d2 (v1: compact_prod (map A1 m)) (v2: compact_prod (map A2 m)),
  (forall i, in_members i m -> A1 (i, field_type2 i m) = A2 (i, field_type2 i m)) ->
  in_members i m ->
  members_no_replicate m = true ->
  JMeq v1 v2 ->
  JMeq (proj_struct i m v1 d1) (proj_struct i m v2 d2).
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [inversion H0 |].
  revert i0 t0 d1 d2 v1 v2 H H0 H1 H2; induction m as [| (i1, t1) m]; intros.
  + inversion H0; [simpl in H3 | inversion H3].
    subst.
    revert d1 d2 v2 H1 H2; simpl.
    if_tac; [intros | congruence].
    unfold eq_rect_r; rewrite <- !eq_rect_eq.
    auto.
  + assert (A1 (i0, t0) = A2 (i0, t0)).
    Focus 1. {
      clear - H.
      specialize (H i0).
      spec H; [left; simpl; auto |].
      simpl in H; if_tac in H; [| congruence].
      auto.
    } Unfocus.
    assert (compact_prod (map A1 ((i1, t1) :: m)) = compact_prod (map A2 ((i1, t1) :: m))).
    Focus 1. {
      f_equal.
      clear - H H1.
      apply map_members_ext; [rewrite members_no_replicate_ind in H1; tauto |].
      intros.
      specialize (H i).
      spec H; [right; auto |].
      pose proof in_members_tail_no_replicate _ _ _ _ H1 H0.
      simpl in H; if_tac in H; [congruence |].
      auto.
    } Unfocus.
    destruct (ident_eq i i0).
    - subst.
      clear IHm.
      revert d1 d2 v1 v2 H H2; simpl.
      if_tac; [intros | congruence].
      unfold eq_rect_r; rewrite <- !eq_rect_eq.
      apply JMeq_fst; auto.
    - inversion H0; [simpl in H5; congruence |].
      revert d1 d2 v1 v2 H1 H2; simpl.
      if_tac; [congruence |].
      intros.
      apply (IHm i1 t1); auto.
      * clear - H H2.
        intros.
        specialize (H i).
        spec H; [right; auto |].
        simpl in H.
        pose proof in_members_tail_no_replicate _ _ _ _ H2 H0.
        if_tac in H; [congruence |].
        exact H.
      * rewrite members_no_replicate_ind in H2; tauto.
      * apply JMeq_snd; auto.
Qed.

Lemma proj_union_JMeq: forall i m A1 A2 d1 d2 (v1: compact_sum (map A1 m)) (v2: compact_sum (map A2 m)),
  (forall i, in_members i m -> A1 (i, field_type2 i m) = A2 (i, field_type2 i m)) ->
  i = fst (members_union_inj v1) ->
  m <> nil ->
  members_no_replicate m = true ->
  JMeq v1 v2 ->
  JMeq (proj_union i m v1 d1) (proj_union i m v2 d2).
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [congruence |].
  clear H1.
  revert i0 t0 d1 d2 v1 v2 H H0 H2 H3; induction m as [| (i1, t1) m]; intros.
  + simpl in H0.
    subst.
    revert d1 d2 v1 v2 H3; simpl.
    if_tac; [intros | congruence].
    unfold eq_rect_r; rewrite <- !eq_rect_eq.
    auto.
  + assert (A1 (i0, t0) = A2 (i0, t0)).
    Focus 1. {
      clear - H.
      specialize (H i0).
      spec H; [left; simpl; auto |].
      simpl in H; if_tac in H; [| congruence].
      auto.
    } Unfocus.
    assert (compact_sum (map A1 ((i1, t1) :: m)) = compact_sum (map A2 ((i1, t1) :: m))).
    Focus 1. {
      f_equal.
      clear - H H2.
      apply map_members_ext; [rewrite members_no_replicate_ind in H2; tauto |].
      intros.
      specialize (H i).
      spec H; [right; auto |].
      pose proof in_members_tail_no_replicate _ _ _ _ H2 H0.
      simpl in H; if_tac in H; [congruence |].
      auto.
    } Unfocus.
    simpl in H3.
    solve_JMeq_sumtype H3.
    - simpl in H0.
      subst i0.
      revert d1 d2; simpl.
      if_tac; [intros | congruence].
      unfold eq_rect_r; rewrite <- !eq_rect_eq.
      auto.
    - pose proof members_union_inj_in_members ((i1, t1) :: m) _ c.
      spec H5; [congruence |].
      replace (fst (members_union_inj c)) with i in H5 by auto.
      pose proof in_members_tail_no_replicate _ _ _ _ H2 H5.
      revert d1 d2 c c0 H0 H1 H3; simpl.
      if_tac; [congruence |].
      intros.
      apply (IHm i1 t1); auto.
      * clear - H H2.
        intros; specialize (H i).
        spec H; [right; auto |].
        pose proof in_members_tail_no_replicate _ _ _ _ H2 H0.
        simpl in H; if_tac in H; [congruence |].
        exact H.
      * clear - H2.
        rewrite members_no_replicate_ind in H2.
        tauto.
Qed.

Lemma members_union_inj_JMeq: forall m A1 A2 (v1: compact_sum (map A1 m)) (v2: compact_sum (map A2 m)),
  (forall i, in_members i m -> A1 (i, field_type2 i m) = A2 (i, field_type2 i m)) ->
  members_no_replicate m = true ->
  JMeq v1 v2 ->
  members_union_inj v1 = members_union_inj v2.
Proof.
  unfold field_type2.
  intros.
  destruct m as [| (i0, t0) m]; [auto |].
  revert i0 t0 v1 v2 H H0 H1; induction m as [| (i1, t1) m]; intros.
  + simpl.
    auto.
  + assert (A1 (i0, t0) = A2 (i0, t0)).
    Focus 1. {
      clear - H.
      specialize (H i0).
      spec H; [left; simpl; auto |].
      simpl in H; if_tac in H; [| congruence].
      auto.
    } Unfocus.
    assert (compact_sum (map A1 ((i1, t1) :: m)) = compact_sum (map A2 ((i1, t1) :: m))).
    Focus 1. {
      f_equal.
      clear - H H0.
      apply map_members_ext; [rewrite members_no_replicate_ind in H0; tauto |].
      intros.
      specialize (H i).
      spec H; [right; auto |].
      pose proof in_members_tail_no_replicate _ _ _ _ H0 H1.
      simpl in H; if_tac in H; [congruence |].
      auto.
    } Unfocus.
    simpl in H1.
    solve_JMeq_sumtype H1.
    simpl.
    apply (IHm i1 t1); auto.
    - clear - H H0.
      intros; specialize (H i).
      spec H; [right; auto |].
      pose proof in_members_tail_no_replicate _ _ _ _ H0 H1.
      simpl in H; if_tac in H; [congruence |].
      exact H.
    - rewrite members_no_replicate_ind in H0; tauto.
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

Definition proj_struct_JMeq: forall i m A1 A2 d1 d2 (v1: compact_prod (map A1 m)) (v2: compact_prod (map A2 m)),
  (forall i, in_members i m -> A1 (i, field_type i m) = A2 (i, field_type i m)) ->
  in_members i m ->
  members_no_replicate m = true ->
  JMeq v1 v2 ->
  JMeq (proj_struct i m v1 d1) (proj_struct i m v2 d2)
:= @proj_struct_JMeq.

Definition proj_union_JMeq: forall i m A1 A2 d1 d2 (v1: compact_sum (map A1 m)) (v2: compact_sum (map A2 m)),
  (forall i, in_members i m -> A1 (i, field_type i m) = A2 (i, field_type i m)) ->
  i = fst (members_union_inj v1) ->
  m <> nil ->
  members_no_replicate m = true ->
  JMeq v1 v2 ->
  JMeq (proj_union i m v1 d1) (proj_union i m v2 d2)
:= @proj_union_JMeq.

Definition members_union_inj_JMeq: forall m A1 A2 (v1: compact_sum (map A1 m)) (v2: compact_sum (map A2 m)),
  (forall i, in_members i m -> A1 (i, field_type i m) = A2 (i, field_type i m)) ->
  members_no_replicate m = true ->
  JMeq v1 v2 ->
  members_union_inj v1 = members_union_inj v2
:= @members_union_inj_JMeq.

End compact_prod_sum.
*)