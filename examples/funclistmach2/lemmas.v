Require Import Min.

Require Import msl.msl_standard.
Require Import Maps.
Require Import FuncListMachine.


Open Scope pred.

(* Various utility lemmas *)

Lemma later_level : forall k1 k2 : K.knot,
  laterR k1 k2 ->
  level k2 < level k1.
Proof.
  intros k1 k2 H; induction H.
  do 2 rewrite K.knot_level.
  hnf in H.
  rewrite K.knot_age1 in H.
  destruct (K.unsquash x).
  destruct n; try discriminate.
  inv H.
  rewrite K.unsquash_squash; simpl.
  auto with arith.
  apply lt_trans with (level y); auto.
Qed.

Lemma nec_level : forall k1 k2 : K.knot,
  necR k1 k2 ->
  level k2 <= level k1.
Proof.
  intros k1 k2 H; induction H.
  do 2 rewrite K.knot_level.
  hnf in H.
  rewrite K.knot_age1 in H.
  destruct (K.unsquash x).
  destruct n; try discriminate.
  inv H.
  rewrite K.unsquash_squash; simpl.
  auto with arith. auto.
  apply le_trans with (level y); auto.
Qed.

Lemma age1_level : forall p1 p2 : K.knot,
  age1 p1 = Some p2 ->
  level p1 = S (level p2).
Proof.
  intros.
  do 2 rewrite K.knot_level.
  rewrite K.knot_age1 in H.
  remember (K.unsquash p1).
  icase p.
  icase n.
  inv H.
  rewrite K.unsquash_squash.
  simpl.
  trivial.
Qed.

Fixpoint ageN (n : nat) (p1 p2 : prog) : Prop :=
  match n with
   | 0 => p1 = p2
   | S n' => exists p', age p1 p' /\ ageN n' p' p2
  end.

Lemma ageN_det: forall n p1 p2 p2',
  ageN n p1 p2 ->
  ageN n p1 p2' ->
  p2 = p2'.
Proof.
  induction n; intros.
  compute in *. congruence.
  destruct H as [px [? ?]]. destruct H0 as [px' [? ?]].
  red in H, H0.
  rewrite H in H0.
  inv H0.
  eapply IHn; eauto.
Qed.
Implicit Arguments ageN_det.

Lemma ageN_necR: forall p1 p2,
  (exists n, ageN n p1 p2) = necR p1 p2.
Proof.
  intros. apply prop_ext. split; intro.
  destruct H. revert p1 H.
  induction x; intros.
  compute in H. subst. auto.
  destruct H as [? [? ?]].
  apply rt_trans with x0. apply rt_step. trivial.
  eapply IHx; eauto.
  induction H.
  exists 1. exists y. intuition.
  exists 0. red. auto.
  destruct IHclos_refl_trans1 as [n1 ?].
  destruct IHclos_refl_trans2 as [n2 ?].
  exists (n1 + n2).
  clear H H0. revert x y z n2 H1 H2.
  induction n1; intros.
  inv H1.
  apply H2.
  simpl in *.
  destruct H1 as [px [? ?]].
  exists px.
  split. trivial.
  eapply IHn1; eauto.
Qed.

Lemma ageN_level: forall n p1 p2,
  ageN n p1 p2 ->
  level p1 = level p2 + n.
Proof.
  unfold prog. induction n; intros.
  inv H. auto.
  inv H. destruct H0.
  apply age1_level in H.
  spec IHn x p2 H0. omega.
Qed.

Let closedR (w1 w2:world) := fst w1 = fst w2.
Program Definition closedM : @modality world _ := exist _ closedR _.
Next Obligation.
  split; repeat intro; unfold closedR in *;
    destruct x as [? ?]; destruct y as [? ?];
      destruct z as [? ?]; simpl in *; intuition subst.
  hnf in H; simpl in H.
  exists  (p,s1); simpl; auto.
  hnf; simpl.
  destruct (@age1 _ K.ageable_knot p0).
  inv H. auto. discriminate.
  hnf in H0; simpl in H0.
  exists (p1,s); simpl; auto.
  hnf; simpl in *.
  destruct (@age1 _ K.ageable_knot p1).
  inv H0. auto. discriminate.
Qed.
Definition closed := box closedM.

Inductive setR v x : relation world :=
  intro_setR : forall p r r',
    r' = r#v <- x ->
    setR v x (p,r) (p,r').

Program Definition setM v x : @modality world _ := setR v x.
Next Obligation.
  split; hnf; intros.
  inv H0.
  hnf in H; simpl in H.
  case_eq (age1 p); intros; unfold prog in *;
    rewrite H0 in H; try discriminate.
  inv H.
  exists (p0,r).
  constructor; auto.
  hnf. simpl. rewrite H0. auto.
  inv H.
  destruct z.
  hnf in H0; simpl in H0.
  case_eq (age1 p0); unfold prog in *; intros;
    rewrite H in H0.
  inv H0.
  exists (p0,(r#v <- x)).
  hnf. simpl. rewrite H. auto.
  constructor; auto.
  discriminate.
Qed.

Program Definition world_op (Pp : pred prog) (Pr : store -> Prop) : pred world :=
  fun pr => let (p,r) := pr in Pp p /\ Pr r.
Next Obligation.
  unfold hereditary; intros.
  destruct a as [p r].
  destruct a' as [p' r'].
  hnf in H.
  simpl in H.
  rewrite K.knot_age1 in H.
  case_eq (K.unsquash p); intros; rewrite H1 in H.
  destruct n; try discriminate.
  inv H.
  intuition.
  destruct Pp as [Pp HPp].
  simpl.
  simpl in H.
  eapply HPp.
  2: apply H.
  hnf.
  rewrite K.knot_age1.
  rewrite H1; auto.
Qed.

Definition store_op (Pr : store -> Prop) := world_op TT Pr.
Definition prog_op (X:pred prog) :=  world_op X (fun _ => True).

Lemma worldNec_unfold : forall p r p' r',
  @necR world _ (p,r) (p',r') <->
  necR p p' /\ r = r'.
Proof.
  intros; split; intro H.
  remember (p,r) as w1.
  remember (p',r') as w2.
  revert p r p' r' Heqw1 Heqw2.
  induction H; simpl; intros; subst.
  hnf in H; simpl in H.
  unfold prog in *.
  case_eq (age1 p); intros; rewrite H0 in H.
  inv H. intuition.
  discriminate.
  inv Heqw2. intuition.
  destruct y as [p2 r2].
  assert (necR p p2 /\ r = r2). auto.
  assert (necR p2 p' /\ r2 = r'). auto.
  intuition; try congruence.
  eapply rt_trans; eauto.
  intuition; subst. induction H0.
  apply rt_step; hnf; simpl. hnf in H.
  unfold prog in *. rewrite H; auto.
  apply rt_refl.
  eapply rt_trans; eauto.
Qed.

Lemma worldLater_unfold : forall p r p' r',
  @laterR world _ (p,r) (p',r') <->
  laterR p p' /\ r = r'.
Proof.
  intros; split; intro H.
  remember (p,r) as w1.
  remember (p',r') as w2.
  revert p r p' r' Heqw1 Heqw2.
  induction H; simpl; intros; subst.
  hnf in H; simpl in H.
  unfold prog in *.
  case_eq (age1 p); intros; rewrite H0 in H.
  inv H. intuition.
  apply t_step; auto.
  discriminate.
  destruct y as [p2 r2].
  assert (laterR p p2 /\ r = r2). auto.
  assert (laterR p2 p' /\ r2 = r'). auto.
  intuition; try congruence.
  eapply t_trans; eauto.
  intuition; subst.
  induction H0. apply t_step.
  hnf; simpl. hnf in H. unfold prog in *. rewrite H. auto.
  eapply t_trans; eauto.
Qed.

Definition instr_approx_rel (n:nat) (i1 i2:instruction) : Prop :=
  fmap_instr (K.approx n) i1 = fmap_instr (K.approx n) i2.

Lemma intro_instr_approx_rel : forall m n i,
  m >= n ->
  instr_approx_rel n i (fmap_instr (K.approx m) i).
Proof.
  intros; hnf.
  induction i; simpl; auto.
  replace (K.approx n (K.approx m x))
    with (K.approx n x); auto.
  change (K.approx n x = (K.approx n oo K.approx m) x).
  replace m with ((m-n)+n) by omega.
  rewrite <- K.approx_approx1; auto.
  rewrite <- IHi1.
  rewrite <- IHi2.
  auto.
  rewrite <- IHi1.
  rewrite <- IHi2.
  auto.
Qed.

Lemma collapse_instr_approx : forall n m i,
  fmap_instr (K.approx n) (fmap_instr (K.approx m) i) =
  fmap_instr (K.approx (min n m)) i.
Proof.
  intros. induction i; simpl; auto.
  destruct (le_gt_dec n m).
  rewrite min_l; auto.
  assert ((m-n)+n = m) by omega.
  rewrite <- H.
  pattern (K.approx n) at 2.
  rewrite (K.approx_approx1 (m-n) n).
  unfold compose. rewrite H. auto.
  rewrite min_r.
  assert ((n-m)+m = n) by omega.
  rewrite <- H.
  pattern (K.approx m) at 2.
  rewrite (K.approx_approx2 (n-m) m).
  unfold compose. rewrite H. auto.
  omega.
  rewrite IHi1. rewrite IHi2. auto.
  rewrite IHi1. rewrite IHi2. auto.
Qed.

Lemma collapse_instr_approx_same : forall n  i,
  fmap_instr (K.approx n) (fmap_instr (K.approx n) i) =
  fmap_instr (K.approx n) i.
Proof.
  intros.
  rewrite collapse_instr_approx.
  apply min_case; auto.
Qed.

Inductive stack_approx_rel (n:nat) : stack -> stack -> Prop :=
  | stack_approx_nil : stack_approx_rel n nil nil
  | stack_approx_cons : forall i i' stk stk',
     instr_approx_rel n i i' ->
     stack_approx_rel n stk stk' ->
     stack_approx_rel n (i::stk) (i'::stk').

Lemma stack_approx_rel_refl : forall n stk,
  stack_approx_rel n stk stk.
Proof.
  induction stk; constructor; auto.
  hnf; auto.
Qed.

Lemma stack_approx_downward : forall n m s1 s2,
  n <= m ->
  stack_approx_rel m s1 s2 ->
  stack_approx_rel n s1 s2.
Proof.
  do 3 intro.
  revert n m.
  induction s1; intros.
  inversion H0.
  constructor.
  inversion H0.
  subst.
  constructor.
  replace n with (min n m).
  red.
  do 2 rewrite <- collapse_instr_approx.
  rewrite H3.
  trivial.
  apply min_l; trivial.
  apply IHs1 with m; trivial.
Qed.

Lemma nec_prog_lookup : forall p p' l i,
  necR p p' ->
  prog_lookup p l = Some i ->
  prog_lookup p' l = Some (fmap_instr (K.approx (level p')) i).
Proof.
  unfold prog_lookup; intros.
  revert l i H0. induction H; simpl; intros; auto.
  hnf in H.
  rewrite K.knot_age1 in H.
  destruct (K.unsquash x). destruct n; try discriminate.
  simpl in *.
  rewrite K.knot_level.
  inv H.
  rewrite K.unsquash_squash. simpl.
  unfold KnotInput.fmap.
  erewrite fmap_eqn; eauto.
  rewrite H0. f_equal.
  rewrite K.knot_level.
  case_eq (K.unsquash x); intros.
  rewrite H in H0. simpl in H0.
  apply K.unsquash_approx in H.
  generalize H0; intro.
  rewrite H in H0.
  unfold KnotInput.fmap in H0.
  erewrite fmap_eqn in H0; eauto.
  simpl; congruence.
  replace (fmap_instr (K.approx (level z)) i)
    with (fmap_instr (K.approx (level z))
          (fmap_instr (K.approx (level y)) i)).
  apply IHclos_refl_trans2.
  apply IHclos_refl_trans1. auto.
  rewrite collapse_instr_approx.
  rewrite min_l; auto.
  apply nec_level; auto.
Qed.

Lemma step_prog: forall p1 p2 r1 s1 r2 s2,
  step p1 p2 r1 s1 r2 s2 ->
  p1 = p2 \/ age p1 p2.
Proof.
  intros.
  inv H; auto.
Qed.

Lemma step_prog_levels : forall p p' r s r' s',
  step p p' r s r' s' ->
  level p' <= level p.
Proof.
  intros.
  apply step_prog in H. destruct H.
  subst p'. trivial.
  do 2 rewrite K.knot_level.
  hnf in H; simpl in H.
  rewrite K.knot_age1 in H.
  destruct (K.unsquash p).
  icase n.
  inv H.
  rewrite K.unsquash_squash; simpl.
  auto.
Qed.

Lemma step_approxprog: forall n p1 p2 p1' p2' r1 s1 s1' r2 s2,
  step p1 p2 r1 s1 r2 s2 ->
  ageN n p1 p1' ->
  ageN n p2 p2' ->
  stack_approx_rel (S (level p1')) s1 s1' ->
  exists s2',
    step p1' p2' r1 s1' r2 s2' /\
    stack_approx_rel (S (level p2')) s2 s2'.
Proof.
  unfold prog.
  intros.
  inversion H; subst.
(* assert *)
  generalize (ageN_det _ _ _ _ H0 H1). intro. subst p2'.
  inversion H2; subst.
  icase i'. icase i'1.
  exists (i'2 :: stk').
  inversion H2. subst.
  red in H9. simpl in H9. inv H9.
  split.
  constructor.
  assert (K.approx (S (level p1')) P (p1', r2)).
    rewrite K.approx_spec. simpl.
    apply (pred_nec_hereditary _ _ (p1',r2)) in H3.
    split; trivial. omega.
    simpl; rewrite worldNec_unfold; split; trivial.
      rewrite <- ageN_necR. exists n. trivial.
  rewrite H5 in H4.
  rewrite K.approx_spec in H4. destruct H4. trivial.
  apply stack_approx_downward with (S (level p1')). omega.
  constructor; trivial.
(* getlab *)
  generalize (ageN_det _ _ _ _ H0 H1). intro. subst p2'.
  inversion H2; subst.
  icase i'. icase i'1.
  exists (i'2 :: stk').
  inversion H5; subst.
  split. constructor; trivial.
  apply stack_approx_downward with (S (level p1')). omega.
  constructor; trivial.
(* fetch1 *)
  generalize (ageN_det _ _ _ _ H0 H1). intro. subst p2'.
  inversion H2; subst.
  icase i'. icase i'1.
  exists (i'2 :: stk').
  inversion H6; subst.
  split. econstructor; eauto.
  apply stack_approx_downward with (S (level p1')). omega.
  constructor; trivial.
(* fetch2 *)
  generalize (ageN_det _ _ _ _ H0 H1). intro. subst p2'.
  inversion H2; subst.
  icase i'. icase i'1.
  exists (i'2 :: stk').
  inversion H6; subst.
  split. econstructor; eauto.
  apply stack_approx_downward with (S (level p1')). omega.
  constructor; trivial.
(* cons *)
  generalize (ageN_det _ _ _ _ H0 H1). intro. subst p2'.
  inversion H2; subst.
  icase i'. icase i'1.
  exists (i'2 :: stk').
  inversion H7; subst.
  split. constructor; trivial.
  apply stack_approx_downward with (S (level p1')). omega.
  constructor; trivial.
(* seq *)
  generalize (ageN_det _ _ _ _ H0 H1). intro. subst p2'.
  inversion H2; subst.
  icase i'. icase i'1.
  exists ((i'1_1 ;; (i'1_2 ;; i'2)) :: stk').
  inversion H5; subst.
  split. econstructor; eauto.
  apply stack_approx_downward with (S (level p1')). omega.
  constructor; trivial.
  red. simpl. congruence.
(* if1 *)
  generalize (ageN_det _ _ _ _ H0 H1). intro. subst p2'.
  inversion H2; subst.
  icase i'. icase i'1.
  exists ((i'1_1 ;; i'2) :: stk').
  inversion H6; subst.
  split. econstructor; eauto.
  apply stack_approx_downward with (S (level p1')). omega.
  constructor; trivial.
  red. simpl. congruence.
(* if2 *)
  generalize (ageN_det _ _ _ _ H0 H1). intro. subst p2'.
  inversion H2; subst.
  icase i'. icase i'1.
  exists ((i'1_2 ;; i'2) :: stk').
  inversion H6; subst.
  split. econstructor; eauto.
  apply stack_approx_downward with (S (level p1')). omega.
  constructor; trivial.
  red. simpl. congruence.
(* call *)
  assert (age p1' p2').
    clear - H5 H0 H1. revert p1 p1' p2 p2' H0 H1 H5.
    induction n; intros; simpl in H0, H1.
    subst p1' p2'. trivial.
    destruct H0 as [px [? ?]]. destruct H1 as [px' [? ?]]. unfold prog in *.
    red in H, H5. rewrite H in H5. inv H5.
    eapply IHn; eauto.
  unfold prog in *.
  icase s1'. inversion H2.
  icase i0; inversion H2; disc. subst.
  icase i0_1.
  inversion H10. subst v0.
  exists ( ((fmap_instr (K.approx (level p1')) i') ;; instr_assert FF) :: i0_2 :: s1').
  split. econstructor; eauto.
  apply (nec_prog_lookup p1 p1' l i'); trivial.
  rewrite <- ageN_necR. exists n. trivial.
  apply age_level in H6.
  constructor.
  red. simpl.
  rewrite collapse_instr_approx. rewrite min_l. trivial. omega.
  apply stack_approx_downward with (S (level p1')). omega.
  constructor; trivial.
(* return *)
  generalize (ageN_det _ _ _ _ H0 H1). intro. subst p2'.
  inversion H2; subst.
  icase i'. icase i'1.
  exists stk'.
  inversion H5; subst.
  split. constructor; eauto.
  apply stack_approx_downward with (S (level p1')). omega.
  trivial.
Qed.

Lemma stepstar_prog_levels : forall p p' r s r' s',
  stepstar p p' r s r' s' ->
  level p' <= level p.
Proof.
  intros; induction H; auto.
  apply le_trans with (level p'); auto.
  eapply step_prog_levels; eauto.
Qed.

Lemma stepstar_approxprog: forall n p1 p2 p1' p2' r1 s1 s1' r2 s2,
  stepstar p1 p2 r1 s1 r2 s2 ->
  ageN n p1 p1' ->
  ageN n p2 p2' ->
  stack_approx_rel (S (level p1')) s1 s1' ->
  exists s2',
    stepstar p1' p2' r1 s1' r2 s2' /\
    stack_approx_rel (S (level p2')) s2 s2'.
Proof.
  do 11 intro.
  apply stepstar_stepN in H.
  destruct H as [m ?].
  revert n p1 p2 p1' p2' r1 s1 s1' r2 s2 H.
  induction m; intros.
  inversion H; subst.
  exists s1'.
  generalize (ageN_det _ _ _ _ H0 H1). intro. subst p2'.
  split. constructor.
  apply stack_approx_downward with (S (level p1')). omega.
  trivial.
  inversion H; subst.
  assert (exists p'2, ageN n p' p'2).
    apply step_prog in H4.
    destruct H4.
    subst p'. exists p1'. trivial.
    apply stepN_stepstar in H5.
    apply stepN_stepstar in H.
    apply stepstar_prog_levels in H.
    apply stepstar_prog_levels in H5.
    apply ageN_level in H1.
    apply ageN_level in H0.
    apply age_level in H3.
    assert (level p' >= n) by (unfold prog in *; omega).
    clear -H4. revert p' H4.
    induction n; intros.
    exists p'. red. trivial.
    rewrite K.knot_level in H4.
    remember (K.unsquash p'). destruct p. simpl in H4.
    destruct n0. omegac.
    spec IHn (K.squash (n0, f)). spec IHn.
    rewrite K.knot_level. rewrite K.unsquash_squash.
    simpl. omega.
    destruct IHn as [px ?].
    exists px. exists (K.squash (n0,f)).
    split; trivial.
    red. rewrite K.knot_age1.
    rewrite <- Heqp. trivial.
  destruct H3 as [p'2 ?].
  destruct (step_approxprog _ _ _ _ _ _ _ _ _ _ H4 H0 H3 H2) as [sx [? ?]].
  spec IHm n p' p2 p'2 p2'.
  spec IHm s' i' sx r2 s2.
  spec IHm H5 H3 H1 H7.
  destruct IHm as [sx' [? ?]].
  exists sx'.
  split; trivial.
  econstructor 2; eauto.
Qed.

Program Definition agedfrom {A} `{ageable A} (x:A) : pred A := necR x.
Next Obligation.
  unfold hereditary; intros.
  apply rt_trans with a; auto.
  apply rt_step; auto.
Qed.


(* The next two also maybe can be combined *)
(*
Lemma safe_approx : forall p n r s s',
  level p < n ->
  stack_approx_rel n s s' ->
  safe p r s ->
  safe p r s'.
Proof.
  repeat intro.
  apply stepstar_stepN in H2.
  destruct H2 as [x H2].
  revert p n r s s' H H0 H1 p' s'0 k' H2.
  induction x; intros.
  inv H2.
  cut (step_or_halt p' s'0 s).
  intros.
  inv H2.
  cut (level p'0 < n); intros.
  generalize H3; intros.
  eapply step_approx in H3; eauto.
  destruct H3 as [s'' [? ?]].
  econstructor; eauto.
  apply le_lt_trans with (level p'); auto.
  eapply step_prog_levels; eauto.
  inv H0.
  constructor.
  apply H1; constructor.

  inv H2.
  cut (step_or_halt p r s).
  intros.
  inv H2.
  cut (level p'1 < n); intros.
  generalize H3; intros.
  eapply step_approx with (n:=n) in H3; eauto.
  destruct H3 as [s'' [? ?]].
  assert (s'1 = r' /\ i' = s'' /\ p'0 = p'1).
  eapply step_deterministic; eauto.
  decompose [and] H8; subst; clear H8.
  revert H5; eapply IHx; eauto.
  repeat intro.
  eapply H1.
  econstructor; eauto.
  apply le_lt_trans with (level p); auto.
  eapply step_prog_levels; eauto.
  inv H0.
  inv H4.
  apply H1.
  constructor.
Qed.

Lemma ev_halts_approx : forall p n r s s',
  level p < n ->
  stack_approx_rel n s s' ->

  eventually_halts p r s ->
  eventually_halts p r s'.
Proof.
  repeat intro.
  destruct H1 as [pz [rz ?]].
  destruct (stepstar_approx _ _ _ _ _ _ _ _  H H0 H1)
    as [z [? ?]].
  exists pz. exists rz.
  inv H3.
  auto.
Qed.

Lemma step_approx :
  forall n p1 p2 s1 s1' s2 r1 r2,
    level p2 < n ->
    stack_approx_rel n s1 s2 ->
    step p1 p2 r1 s1 r2 s1' ->
    exists s2',
      step p1 p2 r1 s2 r2 s2' /\
      stack_approx_rel n s1' s2'.
Proof.
  intros. inv H1; inv H0.

  (* step assert *)
  hnf in H4.
  destruct i'; inv H4.
  destruct i'1; inv H1.
  exists (i'2::stk'); split.
  apply step_assert.
  assert ((K.approx n a) (p2,r2)).
  rewrite <- H4.
  rewrite K.approx_spec.
  simpl; intuition.
  rewrite K.approx_spec in H0.
  simpl in H2; intuition.
  constructor; auto.

  (* step getlabel *)
  hnf in H3; destruct i'; inv H3.
  destruct i'1; inv H1.
  exists (i'2 :: stk'); split;
    econstructor; eauto.

  (* step fetch field 0 *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H1.
  exists (i'2 :: stk'); split;
    econstructor; eauto.

  (* step fetch field 1 *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H1.
  exists (i'2 :: stk'); split;
    econstructor; eauto.

  (* step cons *)
  hnf in H5; destruct i'; inv H5.
  destruct i'1; inv H1.
  exists (i'2 :: stk'); split;
    econstructor; eauto.

  (* step seq *)
  hnf in H3; destruct i'; inv H3.
  destruct i'1; inv H1.
  exists ((i'1_1 ;; i'1_2 ;; i'2) :: stk'); split.
  econstructor; eauto.
  constructor; auto.
  hnf; simpl.
  f_equal; auto.
  f_equal; auto.

  (* step if nil 1 *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H1.
  exists ((i'1_1 ;; i'2) :: stk'); split;
    econstructor; eauto.
  hnf; simpl; f_equal; auto.

  (* step if nil 2 *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H1.
  exists ((i'1_2 ;; i'2) :: stk'); split;
    econstructor; eauto.
  hnf; simpl; f_equal; auto.

  (* step call *)
  hnf in H6; destruct i'0; inv H6.
  destruct i'0_1; inv H1.
  exists ((i' ;; instr_assert FF):: i'0_2 :: stk'); split;
    econstructor; eauto.
  constructor; auto.
  constructor; auto.

  (* step return *)
  hnf in H3; destruct i'; inv H3.
  destruct i'1; inv H1.
  exists stk'; split.
  econstructor.
  auto.
Qed.
*)
(* end nagging suspicion *)
(*
Lemma stepstar_approx :
  forall n p1 p2 s1 s1' s2 r1 r2,
    level p1 < n ->
    stack_approx_rel n s1 s2 ->
    stepstar p1 p2 r1 s1 r2 s1' ->
    exists s2',
      stepstar p1 p2 r1 s2 r2 s2' /\
      stack_approx_rel n s1' s2'.
Proof.
  intros.
  apply stepstar_stepN in H1.
  destruct H1 as [x H1].
  revert n p1 p2 s1 s1' s2 r1 r2 H H0 H1.
  induction x; intros; inv H1.
  exists s2; split; auto.
  constructor.
  assert (level p' < n).
  apply le_lt_trans with (level p1); auto.
  eapply step_prog_levels; eauto.
  destruct (step_approx _ _ _ _ _ _ _ _ H1 H0 H3)
    as [z [? ?]].
  destruct (IHx _ _ _ _ _ _ _ _ H1 H5 H4)
    as [z' [? ?]].
  exists z'; split; auto.
  eapply stepstar_S; eauto.
Qed.
*)

