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



Definition instr_approx_rel (n:nat) (i1 i2:instruction) : Prop :=
  fmap_instr (K.approx n) i1 = fmap_instr (K.approx n) i2.

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

Lemma step_approx :
  forall n t t' p1 p2 s1 s1' s2 r1 r1' r2,
    level p2 < n ->
    termMeasure_incr t t' ->
    store_incr r1 r1' ->
    stack_approx_rel n s1 s2 ->
    step t p1 p2 r1 s1 r2 s1' ->
    exists r2', exists s2',
      step t' p1 p2 r1' s2 r2' s2' /\
      store_incr r2 r2' /\
      stack_approx_rel n s1' s2'.
Proof.
  intros.
  inv H2; inv H3.

  (* step assert *)
  hnf in H4.
  destruct i'; inv H4.
  destruct i'1; inv H3.
  exists r1'.
  exists (i'2::stk'); split.
  apply step_assert.
  assert (proj1_sig (K.approx n a) (p2,(r1',t))).
  rewrite <- H4.
  rewrite K.approx_spec.
  simpl; intuition.
  destruct P as [P HP]; simpl in *.
  rewrite <- HP in H12.
  apply H12.
  rewrite K.expandM_spec.
  split.
  hnf.
  destruct (K.unsquash p2); split; auto.
  hnf; auto.
  split; simpl; auto.
  hnf; eauto.
  rewrite K.approx_spec in H2.
  simpl in H2; intuition.
  destruct a as [a Ha]; simpl in *.
  rewrite <- Ha in H7.
  apply H7.
  rewrite K.expandM_spec; split.
  hnf.
  destruct (K.unsquash p2);split; auto.
  hnf; auto.
  split; simpl; auto.
  hnf; auto.
  split; auto.
  constructor; auto.

  (* step getlabel *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H3.
  econstructor.
  exists (i'2 :: stk'); split;
    econstructor; eauto.
  repeat intro.
  destruct (var_eq v0 l); subst.
  rewrite get_set_same in H2.
  rewrite get_set_same.
  auto.
  rewrite get_set_other in H2; auto.
  rewrite get_set_other; auto.
  constructor; auto.

  (* step fetch field 0 *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H3.
  econstructor.
  exists (i'2 :: stk'); split;
    econstructor; eauto.
  repeat intro.
  destruct (var_eq v0 l); subst.
  rewrite get_set_same in H2.
  rewrite get_set_same.
  auto.
  rewrite get_set_other in H2; auto.
  rewrite get_set_other; auto.
  constructor; auto.

  (* step fetch field 1 *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H3.
  econstructor.
  exists (i'2 :: stk'); split;
    econstructor; eauto.
  repeat intro.
  destruct (var_eq v0 l); subst.
  rewrite get_set_same in H2.
  rewrite get_set_same.
  auto.
  rewrite get_set_other in H2; auto.
  rewrite get_set_other; auto.
  constructor; auto.

  (* step cons *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H3.
  econstructor.
  exists (i'2 :: stk'); split;
    econstructor; eauto.
  repeat intro.
  destruct (var_eq v4 l); subst.
  rewrite get_set_same in H2.
  rewrite get_set_same.
  auto.
  rewrite get_set_other in H2; auto.
  rewrite get_set_other; auto.
  constructor; auto.

  (* step seq *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H3.
  econstructor.
  exists ((i'1_1 ;; i'1_2 ;; i'2) :: stk'); split.
  econstructor; eauto.
  split; auto.
  constructor; auto.
  hnf; simpl.
  f_equal; auto.
  f_equal; auto.

  (* step if nil 1 *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H3.
  econstructor.
  exists ((i'1_1 ;; i'2) :: stk'); split;
    econstructor; eauto.
  constructor; auto.
  hnf; simpl; f_equal; auto.

  (* step if nil 2 *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H3.
  econstructor.
  exists ((i'1_2 ;; i'2) :: stk'); split;
    econstructor; eauto.
  constructor; auto.
  hnf; simpl; f_equal; auto.

  (* step call *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H3.
  econstructor.
  exists ((i'0 ;; instr_nil _):: i'2 :: stk'); split;
    econstructor; eauto.
  constructor; auto.
  hnf; auto.
  constructor; auto.

  (* step apocalypse *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H3.
  econstructor.
  exists ((instr_call v0 ;; i'2) :: stk'); split;
    econstructor; eauto.
  constructor; auto.
  hnf; simpl; f_equal; auto.

  (* step return *)
  hnf in H4; destruct i'; inv H4.
  destruct i'1; inv H3.
  econstructor.
  exists stk'; split.
  econstructor.
  split; auto.
Qed.

Lemma step_prog_levels : forall t p p' r s r' s',
  step t p p' r s r' s' ->
  level p' <= level p.
Proof.
  intros.
  inv H; auto.
  do 2 rewrite K.knot_level.
  hnf in H2; simpl in H2.
  rewrite K.knot_age1 in H2.
  destruct (K.unsquash p).
  destruct n; try discriminate.
  inv H2.
  rewrite K.unsquash_squash; simpl.
  auto.
Qed.

Lemma stepstar_prog_levels : forall t p p' r s r' s',
  stepstar t p p' r s r' s' ->
  level p' <= level p.
Proof.
  intros; induction H; auto.
  apply le_trans with (level p'); auto.
  eapply step_prog_levels; eauto.
Qed.

Lemma stepstar_approx :
  forall n t t' p1 p2 s1 s1' s2 r1 r1' r2,
    level p1 < n ->
    termMeasure_incr t t' ->
    store_incr r1 r1' ->
    stack_approx_rel n s1 s2 ->
    stepstar t p1 p2 r1 s1 r2 s1' ->
    exists r2', exists s2',
      stepstar t' p1 p2 r1' s2 r2' s2' /\
      store_incr r2 r2' /\
      stack_approx_rel n s1' s2'.
Proof.
  intros.
  apply stepstar_stepN in H3.
  destruct H3 as [x H3].
  revert n p1 p2 s1 s1' s2 r1 r1' r2 H H0 H1 H2 H3.
  induction x; intros; inv H3.
  exists r1'; exists s2; split; auto.
  constructor.
  assert (level p' < n).
  apply le_lt_trans with (level p1); auto.
  eapply step_prog_levels; eauto.
  destruct (step_approx _ _ _ _ _ _ _ _ _ _ _ H3 H0 H1 H2 H5)
    as [rz [z [? [? ?]]]].
  destruct (IHx _ _ _ _ _ _ _ _ _ H3 H0 H7 H8 H6)
    as [rz' [z' [? [? ?]]]].
  exists rz'; exists z'; split; auto.
  eapply stepstar_S; eauto.
Qed.

Program Definition agedfrom {A} `{ageable A} (x:A) : pred A := necR x.
Next Obligation.
  unfold hereditary; intros.
  apply rt_trans with a; auto.
  apply rt_step; auto.
Qed.

Lemma safe_approx : forall t t' p n r r' s s',
  level p < n ->
  termMeasure_incr t t' ->
  store_incr r r' ->
  stack_approx_rel n s s' ->
  safe t  p r s ->
  safe t' p r' s'.
Proof.
  repeat intro.
  apply stepstar_stepN in H4.
  destruct H4 as [x H4].
  revert p n r r' s s' H H0 H1 H2 H3 p' s'0 k' H4.
  induction x; intros.
  inv H4.
  cut (step_or_halt t p' r s).
  intros.
  inv H4.
  cut (level p'0 < n); intros.
  destruct (step_approx n _ t' _ _ _ _ k' _ s'0 _ H4 H0 H1 H2 H5)
    as [s'' [z [? [? ?]]]].
  econstructor; eauto.
  hnf; auto.
  apply le_lt_trans with (level p'); auto.
  eapply step_prog_levels; eauto.
  inv H2.
  constructor.
  apply H3; constructor.

  inv H4.
  cut (step_or_halt t p r s).
  intros.
  inv H4.

  cut (level p'1 < n); intros.
  destruct (step_approx _ _ _ _ _ _ _ _ _ _ _ H4 H0 H1 H2 H5)
    as [s'' [z [? [? ?]]]].
  assert (s'1 = s'' /\ i' = z /\ p'0 = p'1).
  eapply step_deterministic; eauto.
  decompose [and] H11; subst; clear H11.
  clear H6.
  revert H7; eapply IHx; eauto.
  repeat intro.
  eapply H3.
  econstructor; eauto.
  apply le_lt_trans with (level p); auto.
  eapply step_prog_levels; eauto.
  inv H2.
  inv H6.
  apply H3.
  constructor.
Qed.

Lemma ev_halts_approx : forall t t' p n r r' s s',
  level p < n ->
  termMeasure_incr t t' ->
  store_incr r r' ->
  stack_approx_rel n s s' ->

  eventually_halts t  p r  s ->
  eventually_halts t' p r' s'.
Proof.
  repeat intro.
  destruct H3 as [pz [rz ?]].
  destruct (stepstar_approx _ _ _ _ _ _ _ _ _ _ _ H H0 H1 H2 H3)
    as [q [z [? [? ?]]]].
  exists pz; exists q.
  inv H6.
  auto.
Qed.

Let closedR (w1 w2:world) := fst w1 = fst w2 /\ snd (snd w1) = snd (snd w2).
Program Definition closedM : @modality world _ := exist _ closedR _.
Next Obligation.
  split; repeat intro; unfold closedR in *;
    destruct x as [? [? ?]]; destruct y as [? [? ?]];
      destruct z as [? [? ?]]; simpl in *; intuition subst.
  hnf in H; simpl in H.
  exists  (p,(s1,t)); simpl; auto.
  hnf; simpl.
  destruct (@age1 _ K.ageable_knot p0).
  inv H. auto. discriminate.
  hnf in H0; simpl in H0.
  exists (p1,(s,t1)); simpl; auto.
  hnf; simpl in *.
  destruct (@age1 _ K.ageable_knot p1).
  inv H0. auto. discriminate.
Qed.
Definition closed := box closedM.


Inductive setR v x : relation world :=
  intro_setR : forall p r r' t,
    r' = r#v <- x ->
    setR v x (p,(r,t)) (p,(r',t)).

Program Definition setM v x : @modality world _ := setR v x.
Next Obligation.
  split; hnf; intros.
  inv H0.
  hnf in H; simpl in H.
  case_eq (age1 p); intros; unfold prog in *;
    rewrite H0 in H; try discriminate.
  inv H.
  exists (p0,(r,t)).
  constructor; auto.
  hnf. simpl. rewrite H0. auto.
  inv H.
  destruct z.
  hnf in H0; simpl in H0.
  case_eq (age1 p0); unfold prog in *; intros;
    rewrite H in H0.
  inv H0.
  exists (p0,(r#v <- x,t)).
  hnf. simpl. rewrite H. auto.
  constructor; auto.
  discriminate.
Qed.


Program Definition world_op (Pp : pred prog) (Pr : store -> Prop) (Pt: terminationMeasure -> Prop) : pred world :=
  fun prt =>
    match prt with (p,(r,t)) =>
      Pp p /\ Pr r /\ Pt t
    end.
Next Obligation.
  unfold hereditary; intros.
  destruct a as [p [r t]].
  destruct a' as [p' [r' t']].
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

Definition store_op (Pr : store -> Prop) :=
  world_op TT Pr (fun _ => True).


Lemma worldNec_unfold : forall p r t p' r' t',
  @necR world _ (p,(r,t)) (p',(r',t')) <->
  necR p p' /\ r = r' /\ t = t'.
Proof.
  intros; split; intro H.
  remember (p,(r,t)) as w1.
  remember (p',(r',t')) as w2.
  revert p r t p' r' t' Heqw1 Heqw2.
  induction H; simpl; intros; subst.
  hnf in H; simpl in H.
  unfold prog in *.
  case_eq (age1 p); intros; rewrite H0 in H.
  inv H. intuition.
  discriminate.
  inv Heqw2. intuition.
  destruct y as [p2 [r2 t2]].
  assert (necR p p2 /\ r = r2 /\ t = t2). auto.
  assert (necR p2 p' /\ r2 = r' /\ t2 = t'). auto.
  intuition; try congruence.
  eapply rt_trans; eauto.
  intuition; subst. induction H0.
  apply rt_step; hnf; simpl. hnf in H.
  unfold prog in *. rewrite H; auto.
  apply rt_refl.
  eapply rt_trans; eauto.
Qed.

Lemma worldLater_unfold : forall p r t p' r' t',
  @laterR world _ (p,(r,t)) (p',(r',t')) <->
  laterR p p' /\ r = r' /\ t = t'.
Proof.
  intros; split; intro H.
  remember (p,(r,t)) as w1.
  remember (p',(r',t')) as w2.
  revert p r t p' r' t' Heqw1 Heqw2.
  induction H; simpl; intros; subst.
  hnf in H; simpl in H.
  unfold prog in *.
  case_eq (age1 p); intros; rewrite H0 in H.
  inv H. intuition.
  apply t_step; auto.
  discriminate.
  destruct y as [p2 [r2 t2]].
  assert (laterR p p2 /\ r = r2 /\ t = t2). auto.
  assert (laterR p2 p' /\ r2 = r' /\ t2 = t'). auto.
  intuition; try congruence.
  eapply t_trans; eauto.
  intuition; subst.
  induction H0. apply t_step.
  hnf; simpl. hnf in H. unfold prog in *. rewrite H. auto.
  eapply t_trans; eauto.
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

Lemma termMeasure_incr_trans : forall t1 t2 t3,
  termMeasure_incr t1 t2 ->
  termMeasure_incr t2 t3 ->
  termMeasure_incr t1 t3.
Proof.
  repeat intro.
  destruct (H l r); destruct (H0 l r); auto.
  left; congruence.
  right; congruence.
Qed.
