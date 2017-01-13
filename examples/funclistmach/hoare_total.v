Require Import Min.

Require Import msl.msl_standard.
Require Import Maps.
Require Import FuncListMachine.
Require Import lemmas.

Open Scope pred.

Program Definition guards (n:nat) (X:pred world) (stk:stack) : pred world :=
  fun prt =>
    match prt with (p,(r,t)) =>

      forall p',
        necR p p' ->
        X (p',(r,t)) ->
        safe t p' r stk /\
        (level p' >= n -> eventually_halts t p' r stk)
  end.
Next Obligation.
  unfold hereditary; intros.
  destruct a as [p [r' t]].
  destruct a' as [p' [r'' t']].
  hnf in H.
  simpl in H.
  unfold prog in *.
  case_eq (age1 p); intros.
  rewrite H1 in H.
  inv H.
  spec H0 p'0.
  spec H0.
  apply rt_trans with p'; auto.
  apply rt_step; auto.
  spec H0; auto.
  rewrite H1 in H; discriminate.
Qed.

Program Definition term_guards (t:store -> option nat) (n:nat) (X:pred world) (stk:stack) : pred world :=
  fun prt =>
    match prt with (p,(r,t')) =>

      forall p',
        necR p p' ->
        X (p',(r,t')) ->
        exists n',
          t r = Some n' /\
          safe t' p' r stk /\
          (level p' >= (n'+n) -> eventually_halts t' p' r stk)
  end.
Next Obligation.
  unfold hereditary; intros.
  destruct a as [? [? ?]].
  destruct a' as [? [? ?]].
  intros.
  hnf in H.
  unfold prog in *.
  simpl in H.
  case_eq (age1 p); intros; rewrite H3 in H; inv H.
  spec H0 p'. spec H0.
  apply rt_trans with p0; auto.
  apply rt_step; auto.
  spec H0; auto.
Qed.

Program Definition funptr (l:label) (A:Type) (P Q: A -> pred world) : pred world :=
  fun prt =>
    match prt with (p,(_,t)) =>
      exists i,  prog_lookup p l = Some i /\
        (forall stk p' n t' (x:A),
          termMeasure_incr t t' ->
           laterR p p' ->
           (forall r', guards n (Q x) stk (p',(r' ,t'))) ->
           (forall r , term_guards (t l) n (P x) ((i;;instr_nil _)::stk) (p',(r,t'))))
    end.
Next Obligation.
  unfold hereditary; intros.
  destruct a as [p [r' t]].
  destruct a' as [p' [r'' t']].
  hnf in H; simpl in H.
  case_eq (age1 p); intros.
  unfold prog in *.
  rewrite H1 in H.
  inv H.
  rename t' into t.
  destruct H0 as [i [? ?]].
  rewrite K.knot_age1 in H1.
  case_eq (K.unsquash p); intros.
  rewrite H2 in H1.
  destruct n; try discriminate.
  inv H1.
  exists (fmap_instr (K.approx n) i).
  split.
  unfold prog_lookup.
  rewrite K.unsquash_squash; simpl.
  unfold KnotInput.fmap.
  apply fmap_eqn.
  unfold prog_lookup in H.
  rewrite H2 in H.
  auto.
  intros.
  spec H0 stk p' n0 t' x.
  spec H0; auto.
  spec H0.
  apply t_trans with (K.squash (n,f)); auto.
  apply t_step.
  hnf. simpl.
  rewrite K.knot_age1. rewrite H2. auto.
  spec H0. auto.
  hnf; intros.
  spec H0 r p'0 H5 H6.
  destruct H0 as [n' [? ?]].
  exists n'; split; auto.
  destruct H7; split.
  revert H7; apply safe_approx with n; eauto.
  replace n with (level (K.squash (n,f))).
  apply later_level.
  apply Rt_Rft_trans with p'; auto.
  rewrite K.knot_level.
  rewrite K.unsquash_squash; auto.
  hnf; eauto.
  hnf; auto.
  constructor; auto.
  apply (intro_instr_approx_rel _ _ (i;;instr_nil _)); auto.
  apply stack_approx_rel_refl.
  intros; spec H8; auto.
  revert H8.
  apply ev_halts_approx with n.
  replace n with (level (K.squash (n,f))).
  apply later_level.
  apply Rt_Rft_trans with p'; auto.
  rewrite K.knot_level.
  rewrite K.unsquash_squash; auto.
  hnf; eauto.
  hnf; auto.
  constructor; auto.
  apply (intro_instr_approx_rel _ _ (i;;instr_nil _)); auto.
  apply stack_approx_rel_refl.

  unfold prog in *.
  rewrite H1 in H.
  discriminate.
Qed.

Lemma boxy_funptr : forall l A P Q,
  boxy K.expandM (funptr l A P Q).
Proof.
  intros. apply boxy_i; auto.
  simpl; intros.
  destruct w; destruct w'.
  destruct o; destruct o0.
  rewrite K.expandM_spec in H.
  destruct H.
  assert (k=k0).
  hnf in H.
  apply K.unsquash_inj.
  destruct (K.unsquash k). destruct (K.unsquash k0).
  destruct H; f_equal; auto.
  subst k0.
  destruct H1. simpl in *.
  destruct H0 as [i [? ?]].
  exists i; split; auto.
  intros.
  spec H3 stk p' n t' x. spec H3; auto.
  do 2 intro. destruct (H2 l0 r0); auto.
  rewrite H9; auto.
  spec H3; auto.
  spec H3; auto.
  spec H3 r p'0 H7 H8.
  destruct H3 as [n' [? ?]].
  exists n'; split; auto.
  destruct (H2 l r); auto.
  rewrite H3 in H10; discriminate.
  congruence.
Qed.

(* Definition of the hoare relation and rules *)

Definition hoare (t:terminationMeasure) (n':nat) (G R P:pred world) (c:instruction) (Q:pred world) :=
  forall t', termMeasure_incr t t' ->

  forall p n k stk,
    (forall s, G (p,(s,t'))) ->
    (forall r', guards n R stk       (p,(r',t'))) ->
    (forall r', guards n Q (k::stk)  (p,(r',t'))) ->
    (forall r,  guards (n'+n) P ((c ;; k)::stk) (p,(r,t'))).


Lemma hoare_weaken : forall t t' x x' (G G' R R' P P' Q Q':pred world) i,
  termMeasure_incr t t' ->
  x <= x' ->
  G' |-- G  ->
  R  |-- R' ->
  P' |-- P  ->
  Q  |-- Q' ->
  hoare t  x  G  R  P  i Q ->
  hoare t' x' G' R' P' i Q'.
Proof.
  intros until i; repeat intro.
  hnf in H5.
  spec H5 t'0.
  spec H5; auto.
  do 2 intro. destruct (H l r0); auto.
  rewrite H12; auto.
  spec H5 p n k stk.
  spec H5; auto.
  spec H5. repeat intro. eapply H8; eauto.
  spec H5. repeat intro. eapply H9; eauto.
  spec H5 r p' H10.
  spec H5; auto.
  destruct H5; split; auto.
  intro. spec H12. omega.
  auto.
Qed.

Lemma hoare_weaken_time : forall t x x' G R P i Q,
  x <= x' ->
  hoare t x G R P i Q ->
  hoare t x' G R P i Q.
Proof.
  intros until Q. intro. apply hoare_weaken; auto; hnf; auto.
Qed.

Lemma hoare_weaken_pre : forall t x G R P P' i Q,
  P' |-- P ->
  hoare t x G R P i Q ->
  hoare t x G R P' i Q .
Proof.
  intros until Q. intro.
  apply hoare_weaken; auto; hnf; auto.
Qed.

Lemma hoare_weaken_post : forall t x G R P i Q Q',
  Q |-- Q' ->
  hoare t x G R P i Q ->
  hoare t x G R P i Q'.
Proof.
  intros until Q'. intro.
  apply hoare_weaken; auto; hnf; auto.
Qed.

Lemma hoare_ex_pre : forall t x G R T P i Q,
  (forall z:T, hoare t x G R (P z) i Q) ->
  hoare t x G R (exp P) i Q.
Proof.
  repeat intro.
  destruct H5.
  spec H x0.
  eapply H; eauto.
Qed.

Lemma hoare_fact_pre : forall t x G R (X:Prop) P i Q,
  (X -> hoare t x G R P i Q) ->
  hoare t x G R (!!X && P) i Q.
Proof.
  repeat intro.
  destruct H5. hnf in H5.
  spec H H5. eapply H; eauto.
Qed.


Lemma hoare_return : forall t (G R:pred world),
  hoare t 0 G R R instr_return FF.
Proof.
  repeat intro.
  spec H1 r p' H3 H4.
  destruct H1. split.
  repeat intro.
  inv H6. econstructor.
  eapply step_return.
  inv H7. apply H1; auto.
  intro. spec H5. omega.
  destruct H5 as [pz [rz ?]].
  exists pz. exists rz.
  econstructor. eapply step_return.
  auto.
Qed.

Lemma hoare_getlabel : forall t l v (G R P:pred world),
  hoare t 0 G R
    (box (setM v (value_label l)) P)
    (instr_getlabel l v)
    P.
Proof.
  repeat intro.
  spec H2 (r#v <- (value_label l)).
  spec H2 p' H3.
  spec H2. apply H4. constructor; auto.
  destruct H2. split.
  repeat intro.
  inv H6. econstructor. econstructor.
  inv H7. apply H2; auto.
  intro; spec H5. omega.
  destruct H5 as [pz [rz ?]].
  exists pz; exists rz.
  econstructor. econstructor.
  auto.
Qed.

Lemma hoare_step_fetch0 : forall t v1 v2 x1 x2 (G R P:pred world),
  hoare t 0 G R
    (store_op (fun r => r#v1 = Some (value_cons x1 x2)) && box (setM v2 x1) P)
    (instr_fetch_field v1 0 v2)
    P.
Proof.
  repeat intro.
  destruct H4.
  destruct H4 as [_ [? _]].
  spec H2 (r#v2 <- x1).
  spec H2 p' H3.
  spec H2. apply H5. constructor. auto.
  destruct H2. split.
  repeat intro.
  inv H7.
  econstructor. econstructor; eauto.
  inv H8.
  apply H2; auto.
  replace x1 with a0 by congruence. auto.
  intro. spec H6. omega.
  destruct H6 as [pz [rz ?]].
  exists pz; exists rz.
  econstructor. econstructor. eauto.
  auto.
Qed.

Lemma hoare_step_fetch1 : forall t v1 v2 x1 x2 (G R P:pred world),
  hoare t 0 G R
    (store_op (fun r => r#v1 = Some (value_cons x1 x2)) && box (setM v2 x2) P)
    (instr_fetch_field v1 1 v2)
    P.
Proof.
  repeat intro.
  destruct H4.
  destruct H4 as [_ [? _]].
  spec H2 (r#v2 <- x2).
  spec H2 p' H3.
  spec H2. apply H5. constructor. auto.
  destruct H2. split.
  repeat intro.
  inv H7.
  econstructor. econstructor; eauto.
  inv H8.
  apply H2; auto.
  replace x2 with a1 by congruence. auto.
  intro. spec H6. omega.
  destruct H6 as [pz [rz ?]].
  exists pz; exists rz.
  econstructor. econstructor. eauto.
  auto.
Qed.

Lemma hoare_cons : forall t v1 v2 v3 x1 x2 (G R P:pred world),
  hoare t 0 G R
     (store_op (fun r => r#v1 = Some x1 /\ r#v2 = Some x2) &&
        box (setM v3 (value_cons x1 x2)) P)
     (instr_cons v1 v2 v3)
     P.
Proof.
  repeat intro.
  destruct H4.
  destruct H4 as [_ [[? ?] _]].
  spec H2 (r#v3 <- (value_cons x1 x2)).
  spec H2 p' H3.
  spec H2.
  apply H5. constructor. auto.
  destruct H2. split.
  repeat intro.
  inv H8.
  econstructor. econstructor; eauto.
  inv H9.
  apply H2.
  replace x1 with a1 by congruence.
  replace x2 with a2 by congruence.
  auto.
  intro. spec H7. omega.
  destruct H7 as [pz [rz ?]].
  exists pz; exists rz.
  econstructor. econstructor; eauto.
  auto.
Qed.

Lemma hoare_if : forall t x v s1 s2 G R P Q,
  P |-- store_op (fun r => match r#v with
                           | Some (value_label l) => l = L 0
                           | Some (value_cons _ _) => True
                           | _ => False
                           end) ->
  hoare t x G R (P && store_op (fun r => r#v = Some (value_label (L 0)))) s1 Q ->
  hoare t x G R (P && store_op (fun r => exists x1, exists x2, r#v = Some (value_cons x1 x2))) s2 Q ->
  hoare t x G R P (instr_if_nil v s1 s2) Q.
Proof.
  repeat intro.
  generalize H7; intros.
  apply H in H8.
  simpl in H8. destruct H8 as [_ [? _]].
  case_eq (r#v); intros; rewrite H9 in H8;
    try tauto.
  destruct v0.

  (* nil case *)
  subst l.
  spec H0 t' H2 p n k.
  spec H0 stk.
  do 3 (spec H0; auto).
  spec H0 r p' H6.
  spec H0.
  split; auto.
  simpl. intuition.
  destruct H0; split.
  repeat intro.
  inv H10.
  econstructor 1.
  eapply step_if_nil1. auto.
  inv H11.
  eapply H0; eauto.
  rewrite H22 in H9. discriminate.
  intro; spec H8; auto.
  destruct H8 as [pz [rz ?]].
  exists pz; exists rz.
  econstructor.
  eapply step_if_nil1; auto.
  auto.

  (* cons case *)
  spec H1 t' H2 p n k.
  spec H1 stk.
  do 3 (spec H1; auto).
  spec H1 r p' H6.
  spec H1. split. auto.
  simpl; intuition. eauto.
  destruct H1. split.
  repeat intro.
  inv H11.
  econstructor 1. eapply step_if_nil2; eauto.
  eapply H1; eauto.
  inv H12. rewrite H23 in H9; discriminate.
  rewrite H23 in H9. inv H9. auto.
  intro; spec H10; auto.
  destruct H10 as [pz [rz ?]].
  exists pz; exists rz.
  econstructor.
  eapply step_if_nil2; eauto.
  auto.
Qed.

Lemma hoare_call : forall t x G R v Q,
  let wp :=
    EX l:label, EX A:Type, EX lP:(A->pred world), EX lQ:(A -> pred world), EX n':nat, EX a:A,
      store_op (fun r => r#v = Some (value_label l) /\ t l r = Some n' /\ n' < x) &&
      (G --> funptr l A lP lQ) &&
      lP a && (closed (lQ a --> Q))
 in
  hoare t x G R wp (instr_call v) Q.
Proof.
  repeat intro.
  unfold wp in H4.
  destruct H4 as [l [A [lP [lQ [n' [a ?]]]]]].
  destruct H4 as [[[? ?] ?] ?].
  destruct H4 as [_ [? _]].
  destruct H4 as [? [? ?]].
  destruct x. elimtype False; omega.
  assert (funptr l A lP lQ (p',(r,t'))).
  apply H5. auto.
  apply pred_nec_hereditary with (p,(r,t')); auto.
  rewrite worldNec_unfold; intuition.
  case_eq (age1 p'); intros.
  destruct H10 as [i [? ?]].
  spec H12 (k::stk) p0 n t' a.
  spec H12. hnf; auto.
  spec H12. apply t_step. auto.
  spec H12.
    intro r'. spec H2 r'.
    repeat intro.
    spec H2 p'0.
    spec H2.
    apply rt_trans with p'; auto.
    apply rt_trans with p0; auto.
    apply rt_step; auto.
    spec H2; auto.
    spec H7 (p',(r',t')).
    spec H7. simpl; hnf; auto.
    apply H7.
    rewrite worldNec_unfold; intuition.
    apply rt_trans with p0; auto.
    apply rt_step; auto.
    auto.

  spec H12 r p0. spec H12; auto.
  spec H12. apply pred_nec_hereditary with (p',(r,t')); auto.
  rewrite worldNec_unfold; intuition.
  destruct H12 as [n2 [? ?]].
  destruct (H l r). congruence.
  rewrite <- H14 in H12.
  rewrite H8 in H12. inv H12. clear H14.

  destruct H13. split.
  repeat intro.
  inv H14.
  econstructor 1.
  eapply step_call with (i':=i); eauto.
  inv H15.
  assert (p0 = p'1) by congruence. subst p'1.
  assert (l = l0) by congruence. subst l0.
  assert (i = i'0) by congruence. subst i'0.
  apply H12; auto.
  apply (af_level2 age_facts) in H11.
  congruence.
  intro. spec H13.
  apply (af_level2 age_facts) in H11. omega.
  destruct H13 as [pz [rz ?]].
  exists pz; exists rz.
  econstructor.
  econstructor; eauto.
  auto.

  split.
  clear -H11.
  repeat intro.
  apply stepstar_stepN in H. destruct H as [n H].
  revert p' H11 p'0 s' k k' stk H.
  induction n; simpl; intros.
  inv H.
  econstructor 1.
  eapply step_call_apocalypse.
  rewrite <- (af_level1 age_facts); auto.
  inv H.
  inv H1.
  hnf in H12. rewrite H12 in H11. discriminate.
  eapply IHn; eauto.
  rewrite (af_level1 age_facts) in H11.
  intro. elimtype False. omega.
Qed.


Lemma hoare_assert : forall t (G R P:pred world) (Q:K.assert),
  boxy K.expandM G ->
  G && P |-- (proj1_sig Q) ->
  hoare t 0 G R P (instr_assert Q) P.
Proof.
  repeat intro.
  split.
  hnf; intros.
  inv H7.
  econstructor 1.
  econstructor.
  apply H0. split; auto.
  eapply pred_nec_hereditary.
  2: apply H2.
  instantiate (1:=s').
  rewrite worldNec_unfold. intuition.
  inv H8.
  destruct (H4 s'0 p'1); auto.
  repeat intro.
  destruct (H4 r p'); auto.
  spec H9. omega.
  destruct H9 as [p'' [r' ?]].
  exists p''; exists r'.
  econstructor 2.
  econstructor.
  apply H0.
  split; auto.
  eapply pred_nec_hereditary.
  2: apply H2.
  instantiate (1:=r).
  rewrite worldNec_unfold; intuition.
  auto.
Qed.

Lemma hoare_seq : forall t x y G R P Q S i1 i2,
  hoare t x G R P i1 Q ->
  hoare t y G R Q i2 S ->
  hoare t (x+y) G R P (i1 ;; i2) S.
Proof.
  intros. hnf; intros.
  assert (guards (x+(y+n)) P ((i1;;i2;;k)::stk) (p,(r,t'))).
  apply H; auto.
  repeat intro.
  spec H3 r' p' H5 H6.
  intuition.
  repeat intro.
  spec H5 p' H6 H7.
  destruct H5; split.
  repeat intro.
  inv H9.
  econstructor 1. econstructor.
  inv H10.
  eapply H5; eauto.
  intro.
  spec H8. omega.
  destruct H8 as [pz [rz ?]].
  exists pz; exists rz.
  econstructor. econstructor.
  auto.
Qed.


(* Verifying function bodies and entire programs *)

Definition verify_prog (t:terminationMeasure) (G:pred world) (psi:program K.assert) (G':pred world) :=
  forall n r,
     agedfrom (K.squash (n,psi),(r,t)) && |>(box K.expandM (closed G))
       |-- box K.expandM (closed G').

Lemma verify_complete : forall G G' psi t,
  G' |-- G ->
  verify_prog t G psi G' ->
  forall n r, G' (K.squash (n,psi),(r,t)).
Proof.
  intros.
  spec H0 n r.
  cut (agedfrom (K.squash (n,psi),(r,t)) |-- (box K.expandM (closed G'))).
  intros.
  eapply H1.
  hnf; apply rt_refl.
  apply K.expandM_refl.
  hnf; simpl; auto.
  apply goedel_loeb.
  apply derives_trans with
    (agedfrom (K.squash (n,psi),(r,t)) && |>(box K.expandM (closed G))); auto.
  intros a Ha; destruct Ha; split; auto.
  clear H1.
  revert a H2.
  do 3 apply box_positive; auto.
Qed.


Lemma verify_func : forall psi l (G:pred world) (A:Type) (P Q:A -> pred world) i t,
  psi#l = Some i ->

  (forall a p r t', termMeasure_incr t t' -> proj1_sig (P a) (p,(r,t')) -> exists n, t l r = Some n) ->

  (forall a n,
    let Pr  := P a && store_op (fun r' => t l r' = Some n) in
    let Pr' a' := P a' && store_op (fun r' => exists n', t l r' = Some n' /\ n' < n) in
    hoare t n (funptr l A Pr' Q && G) (Q a) Pr i FF) ->

  verify_prog t  G psi G ->
  verify_prog t (funptr l A P Q && G) psi (funptr l A P Q && G).
Proof.
  repeat intro.
  destruct H3.
  unfold closed in H6.
  do 3 rewrite box_and in H6.
  destruct H6.
  split. 2: eapply H2; eauto; split; eauto.
  destruct a. destruct a'. destruct a'0.
  destruct H5.
  destruct p. destruct p1. destruct o.
  simpl in H5, H8. subst p0 t1.
  rewrite K.expandM_spec in H4.
  assert (k = k0 /\ r = s /\ t = t0).
  simpl in H3. rewrite worldNec_unfold in H3.
  intuition.
  hnf in H3.
  apply K.unsquash_inj.
  destruct (K.unsquash k). destruct (K.unsquash k0).
  f_equal; intuition.
  destruct H5 as [? [? ?]]; subst s t0 k0.
  destruct H4 as [_ ?].
  destruct H4. simpl in H4, H5.
  assert (Hlookup :
    prog_lookup k l =
      Some (fmap_instr (K.approx (level k)) i)).
  replace (fmap_instr (K.approx (level k)) i)
    with (fmap_instr (K.approx (level k)) (fmap_instr (K.approx n) i)).
  apply nec_prog_lookup with (K.squash (n,psi)); auto.
  simpl in H3. rewrite worldNec_unfold in H3; intuition.
  unfold prog_lookup. rewrite K.unsquash_squash.
  simpl. unfold KnotInput.fmap.
  apply fmap_eqn. auto.
  rewrite collapse_instr_approx.
  rewrite min_l; auto.
  replace n with (level (K.squash (n,psi))).
  apply nec_level. simpl in H3. rewrite worldNec_unfold in H3; intuition.
  rewrite K.knot_level. rewrite K.unsquash_squash; auto.

  simpl.
  exists (fmap_instr (K.approx (level k)) i).
  split. auto.

  clear s0.
  intros stk p' n0 t' x G1 G2 G3 r0.
  revert stk p' n0 t' x G1 G2 G3.
  set (R r1 r2 :=
           match t l r1, t l r2 with
           | Some n1, Some n2 => n1 < n2
           | _, _ => False
           end).
  assert (well_founded R).
  clear. hnf; intro a.
  case_eq (t l a); intros.
  revert a H.
  induction n using (well_founded_induction lt_wf); intros.
  constructor; intros.
  hnf in H1.
  case_eq (t l y); intros.
  rewrite H2 in H1. rewrite H0 in H1.
  apply H with n0; auto.
  rewrite H2 in H1. elim H1.
  constructor; intros.
  hnf in H0. destruct (t l y).
  rewrite H in H0. elim H0. elim H0.

  move r0 after H8.
  induction r0 using (well_founded_induction H8).
  intros.
  destruct (H0 x p'0 r0 t') as [n' ?]; auto.
  eapply termMeasure_incr_trans; eauto.
  exists n'; split; auto.
  destruct (H5 l r0); congruence.

  spec H1 x n' t'.
  spec H1. eapply termMeasure_incr_trans; eauto.
  spec H1 p' n0 (instr_nil K.assert) stk.
  spec H1.

    repeat intro.
    split.
    exists (fmap_instr (K.approx (level p')) i).
    split.
    replace (fmap_instr (K.approx (level p')) i)
      with (fmap_instr (K.approx (level p')) (fmap_instr (K.approx (level k)) i)).
    apply nec_prog_lookup with k; auto.
    apply Rt_Rft; auto.
    rewrite collapse_instr_approx.
    rewrite min_l; auto.
    apply later_level in G2.
    unfold prog in *. omega.

    clear H1.
    repeat intro.
    destruct H16.
    simpl in H17.
    destruct H17 as [_ [? _]].
    destruct H17 as [n'' [? ?]].
    exists n''. split.
    destruct (H5 l r1). congruence.
    destruct (G1 l r1); congruence.
    spec H9 r1. spec H9.
    hnf. rewrite H17. rewrite H12. auto.
    spec H9 stk0 p'1 n1 t'0 x0.
    spec H9.
    eapply termMeasure_incr_trans; eauto.
    spec H9. apply t_trans with p'; auto.
    spec H9. auto.
    spec H9 p'2. spec H9. auto.
    spec H9. auto.
    destruct H9 as [n2 [? ?]].
    assert (n'' = n2).
    destruct (H5 l r1); congruence.
    subst n''.
    destruct H19; split.
    revert H19.
    apply safe_approx with (level p').
    apply later_level.
    apply Rt_Rft_trans with p'1; auto.
    hnf; auto.
    hnf; auto.
    constructor. hnf. simpl. f_equal.
    rewrite collapse_instr_approx.
    rewrite collapse_instr_approx_same.
    rewrite min_l; auto.
    apply later_level in G2.
    unfold prog in *; omega.
    apply stack_approx_rel_refl.
    intro. spec H20. auto.
    revert H20.
    apply ev_halts_approx with (level p').
    apply later_level. apply Rt_Rft_trans with p'1; auto.
    hnf; auto.
    hnf. auto.
    constructor. hnf. simpl. f_equal.
    rewrite collapse_instr_approx.
    rewrite collapse_instr_approx_same.
    rewrite min_l; auto.
    apply later_level in G2.
    unfold prog in *; omega.
    apply stack_approx_rel_refl.
    eapply H7.
    instantiate (1:=(p',(r,t))).
    simpl.
    rewrite worldLater_unfold. intuition.
    instantiate (1:= (p',(r,t'))).
    rewrite K.expandM_spec.
    split. hnf. destruct (K.unsquash p'); split; hnf; auto.
    split; simpl; auto. hnf; auto.
    eapply termMeasure_incr_trans; eauto.
    split; simpl; auto.

  spec H1. auto.
  spec H1. repeat intro. elim H14.
  spec H1 r0.
  spec H1 p'0.
  spec H1; auto.
  spec H1. split; auto.
  simpl. auto.
  destruct H1; split.
  revert H1.
  apply safe_approx with (level k).
  apply later_level. apply Rt_Rft_trans with p'; auto.
  hnf; auto.
  hnf; auto.
  constructor.
  hnf. simpl. f_equal.
  rewrite collapse_instr_approx_same; auto.
  apply stack_approx_rel_refl.
  intro; spec H13; auto.
  revert H13.
  apply ev_halts_approx with (level k).
  apply later_level. apply Rt_Rft_trans with p'; auto.
  hnf; auto.
  hnf; auto.
  constructor.
  hnf. simpl. f_equal.
  rewrite collapse_instr_approx_same; auto.
  apply stack_approx_rel_refl.
Qed.


Lemma end_assert_lemma : forall Q t n p p' r r' stk,
    stepN n t p p' r (stk++(instr_assert Q ;; instr_return ;; instr_nil _) :: nil) r' nil ->
    stepstar t p p' r (stk++(instr_return ;; instr_nil _) :: nil) r' nil /\ proj1_sig Q (p',(r',t)).
Proof.
  induction n; simpl; intros; inv H.
  destruct stk; discriminate.
  destruct stk. simpl in H1.
  inv H1. simpl.
  split; auto.
  apply stepN_stepstar with n; auto.
  inv H2. inv H.
  inv H0. auto.
  inv H.

  simpl in H1.
  inv H1.
  apply IHn with (stk:= i0::stk) in H2.
  intuition. econstructor. econstructor; auto. auto.
  apply IHn with (stk:= i0::stk) in H2.
  intuition. econstructor. econstructor; auto. auto.
  apply IHn with (stk:= i0::stk) in H2.
  intuition. econstructor. econstructor; eauto. auto.
  apply IHn with (stk:= i0::stk) in H2.
  intuition. econstructor. econstructor; eauto. auto.
  apply IHn with (stk:= i0::stk) in H2.
  intuition. econstructor. econstructor; eauto. auto.
  apply IHn with (stk:= (i1;;i2;;i3)::stk) in H2.
  intuition. econstructor. econstructor; eauto. auto.
  apply IHn with (stk:= (i1;;i0)::stk) in H2.
  intuition. econstructor. econstructor; eauto. auto.
  apply IHn with (stk:= (i2;;i0)::stk) in H2.
  intuition. econstructor. eapply step_if_nil2; eauto. auto.
  apply IHn with (stk:= (i'0;;instr_nil _)::i0::stk) in H2.
  intuition. econstructor. econstructor; eauto. auto.
  apply IHn with (stk:= (instr_call v;;i0)::stk) in H2. intuition.
  apply IHn with (stk:=stk) in H2.
  intuition. econstructor. econstructor. auto.
Qed.

(* Fundamental liveness theorem.  A verified function,
   when started in a state satisfying its precondition,
   will halt in a state satisfying its postcondition.
 *)

Lemma verify_totally_correct : forall t G A P Q psi l x
  (HQ:forall x, boxy K.expandM (Q x)),
  verify_prog t G psi G ->
  G |-- funptr l A P Q ->
  forall r,
    (forall n, P x (K.squash (n,psi),(r#(L 0) <- (value_label l),t))) ->
    exists n, exists p', exists r',
      stepstar t (K.squash (n,psi)) p'
        r ((instr_getlabel l (L 0) ;; instr_call (L 0) ;; instr_return ;; instr_nil _)::nil)
        r' nil /\
      Q x (p',(r',t)).
Proof.
  intros.
  assert (forall n r, G (K.squash (n,psi),(r,t))).
  apply verify_complete with G; auto.
  hnf; auto.
  set (r' :=(r#(L 0) <- (value_label l))).
  assert (exists n, t l r' = Some n).
  assert (funptr l A P Q (K.squash (1,psi),(r,t))) by auto.
  destruct H3 as [i [? ?]].
  spec H4 (nil : stack) (K.squash (0,psi)) 0 t x.
  spec H4. hnf; auto.
  spec H4. apply t_step. hnf.
  rewrite K.knot_age1. rewrite K.unsquash_squash.
  f_equal. apply K.unsquash_inj.
  repeat rewrite K.unsquash_squash.
  f_equal.
  change ((KnotInput.fmap (K.approx 0) oo KnotInput.fmap (K.approx 1)) psi =
    KnotInput.fmap (K.approx 0) psi).
  rewrite KnotInput.fmap_comp.
  replace 1 with (1+0) by omega.
  rewrite <- (K.approx_approx1 1 0); auto.
  spec H4.
  repeat intro. split; repeat intro.
  inv H7. constructor 2.
  inv H8.
  exists p'. exists r'0. apply stepstar_O.
  spec H4 r' (K.squash (0,psi)).
  spec H4. auto.
  spec H4. auto.
  destruct H4 as [n' [? ?]]. eauto.
  destruct H3 as [n ?].
  assert (funptr l A P Q (K.squash (S n,psi),(r,t))) by auto.
  destruct H4 as [i [? ?]].
  spec H5 ((instr_assert (exist _ (Q x) (HQ x)) ;; instr_return ;; instr_nil K.assert)::nil).
  spec H5 (K.squash (n,psi)) 0 t x.
  spec H5. hnf; auto.
  spec H5.
  apply t_step.
  hnf. rewrite K.knot_age1.
  rewrite K.unsquash_squash; simpl.
  f_equal.
  apply K.unsquash_inj.
  repeat rewrite K.unsquash_squash.
  f_equal.
  transitivity (KnotInput.fmap (K.approx n oo K.approx (S n)) psi).
  rewrite <- KnotInput.fmap_comp; auto.
  replace (K.approx n oo K.approx (S n)) with (K.approx n); auto.
  extensionality.
  unfold compose.
  change (K.approx n x0 = (K.approx n oo K.approx (1+n)) x0).
  rewrite <- K.approx_approx1; auto.
  hnf; auto.
  spec H5.
  repeat intro.
  split.
  hnf.
  intros.
  inv H8.
  econstructor 1.
  econstructor.
  auto.
  inv H9. simpl in *.
  inv H10.
  econstructor 1.
  econstructor.
  inv H8.
  inv H9.
  constructor.
  inv H8.
  intros.
  econstructor.
  econstructor.
  econstructor 2.
  econstructor.
  simpl; auto.
  econstructor. econstructor.
  econstructor 1.
  spec H5 r' (K.squash (n,psi)).
  spec H5; auto.
  spec H5. auto.
  destruct H5 as [n' [? ?]].
  assert (n = n') by congruence. subst n'.
  destruct H6. spec H7; auto.
  rewrite K.knot_level.
  rewrite K.unsquash_squash; simpl. omega.
  exists (S n).
  destruct H7 as [pz [rz ?]].
  exists pz; exists rz.
  cut
    (stepstar t (K.squash (n, psi)) pz r'
         ((i;; instr_nil K.assert)
          :: (instr_return;; instr_nil K.assert) :: nil) rz nil
         /\ Q x (pz,(rz,t))).
  intros [? ?]; split; auto.
  econstructor 2.
  econstructor.
  econstructor 2.
  econstructor; eauto.
  rewrite get_set_same; auto.
  hnf; simpl.
  rewrite K.knot_age1.
  rewrite K.unsquash_squash.
  reflexivity.
  match goal with [ |- stepstar _ ?X _ _ _ _ _ ] =>
    replace X with (K.squash (n,psi))
  end.
  auto.
  apply K.unsquash_inj.
  repeat rewrite K.unsquash_squash.
  f_equal.
  symmetry.
  transitivity (KnotInput.fmap (K.approx n oo K.approx (S n)) psi).
  rewrite <- KnotInput.fmap_comp; auto.
  change (S n) with (1+n).
  rewrite <- K.approx_approx1; auto.

  apply stepstar_stepN in H7. destruct H7.
  eapply end_assert_lemma with (Q:=exist _ (Q x) (HQ x))
    (stk:=(i;;instr_nil _)::nil). eauto.
Qed.

(* Weaker corallary: a program with a safe entry point
   will eventually halt.
 *)
Corollary verify_halts : forall t G psi l,
  verify_prog t G psi G ->
  G |-- funptr l unit (fun _ => TT) (fun _ => TT) ->
  forall r, exists n,
    eventually_halts t (K.squash (n,psi)) r
        ((instr_getlabel l (L 0) ;; instr_call (L 0) ;; instr_return ;; instr_nil _)::nil).
Proof.
  intros.
  destruct (verify_totally_correct t G unit (fun _ => TT) (fun _ => TT) psi l tt) with (r:=r)
    as [n [p' [r' [? ?]]]]; auto.
  exists n. hnf. eauto.
Qed.
