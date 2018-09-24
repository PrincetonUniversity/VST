Require Import Coq.Lists.List.
Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2 VST.floyd.coqlib3.
Require Import VST.floyd.jmeq_lemmas.

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

Definition upd_compact_prod {A} {F} (l: list A) (v: compact_prod (map F l)) (a: A) (v0: F a) (H: forall a b: A, {a = b} + {a <> b}) : compact_prod (map F l).
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

Lemma compact_prod_eq: forall {A} {F1: A -> Type} {F2: A -> Type} (l: list A), (forall a, In a l -> @eq Type (F1 a) (F2 a)) -> @eq Type (compact_prod (map F1 l)) (compact_prod (map F2 l)).
Proof.
  intros.
  destruct l; auto.
  revert a H; induction l; intros.
  + simpl.
    apply H.
    simpl; auto.
  + simpl.
    rewrite H by (left; auto).
    change (match @map A Type F1 l with
                       | nil => F1 a
                       | cons _ _ => prod (F1 a) (compact_prod (@map A Type F1 l))
                       end) with
           (compact_prod (@map A Type F1 (@cons A a l))).
    rewrite IHl; [apply eq_refl |].
    intros.
    apply H.
    simpl; auto.
Qed.

Lemma compact_sum_eq: forall {A} {F1: A -> Type} {F2: A -> Type} (l: list A), (forall a, In a l -> @eq Type (F1 a) (F2 a)) -> @eq Type (compact_sum (map F1 l)) (compact_sum (map F2 l)).
Proof.
  intros.
  destruct l; auto.
  revert a H; induction l; intros.
  + simpl.
    apply H.
    simpl; auto.
  + simpl.
    rewrite H by (left; auto).
    change (match @map A Type F1 l with
                       | nil => F1 a
                       | cons _ _ => sum (F1 a) (compact_sum (@map A Type F1 l))
                       end) with
           (compact_sum (@map A Type F1 (@cons A a l))).
    rewrite IHl; [apply eq_refl |].
    intros.
    apply H.
    simpl; auto.
Qed.

Lemma compact_prod_gen_JMeq: forall {A} {F1} {F2} (gen1: forall a: A, F1 a) (gen2: forall a: A, F2 a)  (l: list A), (forall a, In a l -> JMeq (gen1 a) (gen2 a)) -> JMeq (compact_prod_gen gen1 l) (compact_prod_gen gen2 l).
Proof.
  intros.
  destruct l; auto.
  revert a H; induction l; intros.
  + simpl.
    apply H.
    simpl; auto.
  + simpl.
    apply JMeq_pair; [apply H; left; auto |].
    apply IHl.
    intros.
    apply H.
    simpl; auto.
Qed.

Lemma compact_sum_gen_JMeq: forall {A} {F1} {F2} (filter: A -> bool) (gen1: forall a: A, F1 a) (gen2: forall a: A, F2 a)  (l: list A), (forall a, In a l -> JMeq (gen1 a) (gen2 a)) -> JMeq (compact_sum_gen filter gen1 l) (compact_sum_gen filter gen2 l).
Proof.
  intros.
  destruct l; auto.
  revert a H; induction l; intros.
  + simpl.
    apply H.
    simpl; auto.
  + simpl.
    destruct (filter a0).
    - apply @JMeq_inl.
      * apply (@compact_sum_eq A F1 F2 (a :: l)).
        intros.
        apply H; right; auto.
      * apply H; left; auto.
    - apply @JMeq_inr.
      * apply H; left; auto.
      * apply IHl.
        intros; apply H; right; auto.
Qed.

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

Definition upd_compact_sum {A} {F} (l: list A) (v: compact_sum (map F l)) (a: A) (v0: F a) (H: forall a b: A, {a = b} + {a <> b}) : compact_sum (map F l).
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

Lemma proj_compact_prod_JMeq: forall A i (l: list A) {F1: A -> Type} {F2: A -> Type} d1 d2 (v1: compact_prod (map F1 l)) (v2: compact_prod (map F2 l)) H,
  (forall i, In i l -> @eq Type (F1 i) (F2 i)) ->
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
  + assert (@eq Type (F1 a0) (F2 a0)). {
      clear - H0.
      specialize (H0 a0).
      apply H0.
      left; simpl; auto.
    }
    assert (@eq Type (compact_prod (map F1 (a1 :: l))) (compact_prod (map F2 (a1 :: l)))).
    {
      apply compact_prod_eq.
      clear - H0.
      intros i ?H.
      specialize (H0 i).
      spec H0; [right; auto |].
      symmetry; auto.
    }
    destruct (H i a0) as [?H | ?H].
    - subst.
      clear IHl.
      revert v1 v2 H0 H2; simpl.
      destruct (H a0 a0); [intros | congruence].
      unfold eq_rect_r; rewrite <- !eq_rect_eq.
      apply @JMeq_fst; auto.
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
      * apply @JMeq_snd; auto.
Qed.

Lemma proj_compact_sum_JMeq': forall A i (l: list A) {F1: A -> Type} {F2: A -> Type} d1 d2 (v1: compact_sum (map F1 l)) (v2: compact_sum (map F2 l)) H,
  (forall i, In i l -> @eq Type (F1 i) (F2 i)) ->
  JMeq d1 d2 ->
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
  + assert (@eq Type (F1 a0) (F2 a0)).
    {
      clear - H0.
      apply H0.
      left; simpl; auto.
    }
    assert (@eq Type (compact_sum (map F1 (a1 :: l))) (compact_sum (map F2 (a1 :: l)))).
    {
      apply compact_sum_eq.
      clear - H0.
      intros i ?H.
      specialize (H0 i).
      spec H0; [right; auto |].
      symmetry; auto.
    }
    simpl in H2.
    solve_JMeq_sumtype H2.
    - simpl in H1 |- *.
      destruct (H i a0); [| tauto].
      subst.
      unfold eq_rect_r; rewrite <- !eq_rect_eq.
      auto.
    - simpl in H1 |- *.
      destruct (H i a0).
      * subst i.
        unfold eq_rect_r; rewrite <- !eq_rect_eq; auto.
      * apply (IHl a1 c c0); auto.
        clear - H0.
        intros ?i ?.
        apply H0.
        right; auto.
Qed.

Lemma proj_compact_sum_JMeq: forall A i (l: list A) {F1: A -> Type} {F2: A -> Type} d1 d2 (v1: compact_sum (map F1 l)) (v2: compact_sum (map F2 l)) H,
  (forall i, In i l -> @eq Type (F1 i) (F2 i)) ->
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
  + assert (@eq Type (F1 a0) (F2 a0)).
    {
      clear - H0.
      apply H0.
      left; simpl; auto.
    }
    assert (@eq Type (compact_sum (map F1 (a1 :: l))) (compact_sum (map F2 (a1 :: l)))).
    {
      apply compact_sum_eq.
      clear - H0.
      intros i ?H.
      specialize (H0 i).
      spec H0; [right; auto |].
      symmetry; auto.
    }
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

Lemma compact_sum_inj_JMeq: forall {A} (l: list A) {F1: A -> Type} {F2: A -> Type} (v1: compact_sum (map F1 l)) (v2: compact_sum (map F2 l)) H,
  (forall i, In i l -> @eq Type (F1 i) (F2 i)) ->
  JMeq v1 v2 ->
  (forall i, compact_sum_inj v1 i H <-> compact_sum_inj v2 i H).
Proof.
  intros.
  destruct l as [| a0 l]; [simpl; tauto |].
  revert a0 v1 v2 H0 H1; induction l as [| a1 l]; intros.
  + simpl in *.
    destruct (H i a0); [| tauto].
    tauto.
  + assert (@eq Type (F1 a0) (F2 a0)).
    {
      clear - H0.
      apply H0.
      left; simpl; auto.
    }
    assert (@eq Type (compact_sum (map F1 (a1 :: l))) (compact_sum (map F2 (a1 :: l)))).
    {
      apply compact_sum_eq.
      clear - H0.
      intros i ?H.
      specialize (H0 i).
      spec H0; [right; auto |].
      symmetry; auto.
    }
    simpl in H1.
    solve_JMeq_sumtype H1.
    - simpl in *.
      destruct (H i a0); [| tauto].
      tauto.
    - simpl in *.
      destruct (H i a0); [tauto |].
      apply (IHl a1 c c0); auto.
Qed.

Lemma upd_compact_prod_JMeq: forall A i (l: list A) {F1: A -> Type} {F2: A -> Type} d1 d2 (v1: compact_prod (map F1 l)) (v2: compact_prod (map F2 l)) H,
  (forall i, In i l -> @eq Type (F1 i) (F2 i)) ->
  JMeq d1 d2 ->
  JMeq v1 v2 ->
  JMeq (upd_compact_prod l v1 i d1 H) (upd_compact_prod l v2 i d2 H).
Proof.
  intros.
  destruct l as [| a0 l]; [simpl; auto |].
  revert a0 v1 v2 H2 H0; induction l as [| a1 l]; intros.
  + simpl.
    destruct (H i a0); auto.
    subst i.
    unfold eq_rect_r.
    rewrite <- !eq_rect_eq.
    auto.
  + simpl.
    assert (JMeq (fst v1) (fst v2)).
    {
      apply @JMeq_fst; auto.
      + apply H0; simpl; auto.
      + apply (@compact_prod_eq _ F1 F2 (a1 :: l)).
        intros.
        apply H0.
        simpl; auto.
    }
    assert (JMeq (snd v1) (snd v2)).
    {
      apply @JMeq_snd; auto.
      + apply H0; simpl; auto.
      + apply (@compact_prod_eq _ F1 F2 (a1 :: l)).
        intros.
        apply H0.
        simpl; auto.
    }
    destruct (H i a0).
    - subst i.
      unfold eq_rect_r.
      rewrite <- !eq_rect_eq.
      apply @JMeq_pair; auto.
    - apply @JMeq_pair; auto.
      apply IHl; auto.
      intros; apply H0; simpl; auto.
Qed.

Lemma upd_compact_sum_JMeq: forall A i (l: list A) {F1: A -> Type} {F2: A -> Type} d1 d2 (v1: compact_sum (map F1 l)) (v2: compact_sum (map F2 l)) H,
  (forall i, In i l -> @eq Type (F1 i) (F2 i)) ->
  JMeq d1 d2 ->
  JMeq v1 v2 ->
  JMeq (upd_compact_sum l v1 i d1 H) (upd_compact_sum l v2 i d2 H).
Proof.
  intros.
  unfold upd_compact_sum.
  destruct (in_dec H i l) as [?H | ?H]; auto.
  clear v1 v2 H2.
  destruct l as [| a0 l]; [simpl; auto |].
  revert a0 H0 H3; induction l as [| a1 l]; intros.
  + simpl.
    destruct (H i a0); [| destruct H3; [congruence | inv i0]].
    subst i.
    unfold eq_rect_r.
    rewrite <- !eq_rect_eq.
    auto.
  + simpl.
    destruct (H i a0).
    - subst i.
      unfold eq_rect_r.
      rewrite <- !eq_rect_eq.
      apply @JMeq_inl; auto.
      apply (@compact_sum_eq _ F1 F2 (a1 :: l)).
      intros.
      apply H0.
      simpl; auto.
    - apply @JMeq_inr; auto.
      * apply H0; simpl; auto.
      * apply IHl.
        intros.
        apply H0.
        simpl; auto.
Qed.
