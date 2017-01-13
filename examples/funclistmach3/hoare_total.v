Import Require Min.

Require Import msl.msl_standard.
Require Import Maps.
Require Import FuncListMachine.
Require Import lemmas.

Open Scope pred.

Program Definition getsn (n:nat) (stk stk':stack) (Q:pred world) : pred world :=
  fun pr => let (p,r) := pr in
    level p >= n -> exists n', n' < n /\
      exists p', exists r', stepN n' p p' r stk r' stk' /\
        Q (p',r').
Next Obligation.
  hnf. simpl; intros.
  destruct a. destruct a'.
  intro.
  cut (S (level p0) = level p).
  intro. rewrite <- H2 in H0 .
  spec H0. omega.
  destruct H0 as [n' [? ?]].
  exists n'. split; auto.
admit.
admit.
Qed.

Program Definition haltsn (n : nat) (stk : stack) : pred world :=
  fun pr => let (p,r) := pr in
    (level p >= n -> eventually_halts_n n p r stk).
Next Obligation.
  unfold hereditary; intros.
  destruct a as [p r'].
  destruct a' as [p' r''].
  intros.
  unfold prog in *.
  spec H0.
  apply age_level in H; simpl in H; omega.
  hnf in H.
  simpl in H.
  unfold prog_lookup, prog in *.
  remember (age1 p).
  icase o.
  rewrite K.knot_age1 in Heqo.
  remember (K.unsquash p).
  destruct p0.
  icase n0.
  inv H.
  inv Heqo.
  destruct H0 as [px [rx [? ?]]].
  repeat rewrite K.knot_level in *.
  rewrite <- Heqp0 in H.
  rewrite K.unsquash_squash in H1.
  remember (K.unsquash px).
  destruct p0.
  simpl in *.
  destruct n1.
  omegac.
  exists (K.squash (n1, f0)).
  exists rx.
  split.
  repeat rewrite K.knot_level in *.
  repeat rewrite K.unsquash_squash.
  trivial.
  generalize (stepstar_approxprog 1 _ _ (K.squash (n0,f)) (K.squash (n1, f0)) _ _ stk _ _ H0); intro.
  spec H2.
  exists (K.squash (n0,f)). split; try reflexivity.
  hnf. rewrite K.knot_age1.
  rewrite <- Heqp0. trivial.
  spec H2.
  exists (K.squash (n1,f0)). split; try reflexivity.
  hnf. rewrite K.knot_age1.
  rewrite <- Heqp1. trivial.
  spec H2. apply stack_approx_rel_refl.
  destruct H2 as [s2' [? ?]].
  inversion H3. subst s2'.
  trivial.
Qed.

Definition guardsn (n : nat) (P : pred world) (stk : stack) : pred world :=
  P --> haltsn n stk.

Definition termMeas :=
  { R : store -> nat -> Prop |
    forall x y y', R x y -> R x y' -> y = y' }.

Program Definition code (l : label) (c : instruction) : pred prog :=
  fun p =>
    exists i, prog_lookup p l = Some i /\ instr_approx_rel (level p) c i.
Next Obligation.
  unfold hereditary; intros.
  hnf in H.
  unfold prog_lookup, prog in *.
  destruct H0 as [i [? ?]].
  exists (fmap_instr (K.approx (level a')) c).
  split.
  2: red; symmetry; apply collapse_instr_approx_same.
  rewrite K.knot_age1 in H.
  remember (K.unsquash a).
  destruct p.
  icase n.
  inv H.
  rewrite K.knot_level in *.
  rewrite <- Heqp in H1.
  rewrite K.unsquash_squash.
  simpl in *.
  unfold KnotInput.fmap.
  erewrite fmap_eqn.
  2: apply H0.
  red in H1.
  replace n with (min n (S n)) by (apply min_l; auto with arith).
  do 2 rewrite <- collapse_instr_approx.
  rewrite H1.
  trivial.
Qed.

Program Definition evalTM (t : termMeas) (n : nat) : pred world :=
  fun w => let (_, r) := w in
    proj1_sig t r n.
Next Obligation.
  unfold hereditary; intros.
  destruct a. destruct a'.
  hnf in H. simpl in H. unfold prog in *.
  icase (age1 p).
  inv H. trivial.
Qed.

Program Definition embedWP (P : pred world) : pred prog :=
  fun p => forall r, P (p,r).
Next Obligation.
  unfold hereditary; intros.
  rewrite <- (nec_useless P) in H0.
  apply (H0 r (a',r)).
  simpl. rewrite worldNec_unfold. intuition.
Qed.

(* Definition of the hoare relation and rules *)

Definition hoare' (n':nat) (G:pred prog) (R P:pred world) (c:instruction) (Q:pred world) :=
  forall p n k stk,
    G p ->
    (forall r', guardsn n R stk       (p,r')) ->
    (forall r', guardsn n Q (k::stk)  (p,r')) ->
    (forall r,  guardsn (n'+n) P ((c ;; k)::stk) (p,r)).

Definition hoare (G:pred prog) (R P:pred world) (c:instruction) (Q:pred world) :=
  forall p k stk,
    G p -> forall r p', necR p p' -> P (p',r) -> exists n,
      getsn n ((c;;k)::stk) (k::stk) Q (p',r)  \/
      getsn n ((c;;k)::stk) stk R (p',r).

Lemma hoare_seq2 : forall G R P Q S i1 i2,
  hoare G R P i1 Q ->
  hoare G R Q i2 S ->
  hoare G R P (i1 ;; i2) S.
Proof.
  repeat intro.
  spec H p (i2;;k) stk H1.
  spec H r p' H2 H3.
  destruct H as [n1 [?|?]].
  hnf in H.
  destruct (le_lt_dec n1 (level p')).
  spec H. omega.
  destruct H as [n' [? ?]].
  destruct H4 as [p'' [r'' [? ?]]].
  spec H0 p k stk H1.
  spec H0 r'' p''.
  spec H0. admit.
  spec H0; auto.
  destruct H0 as [n2 [?|?]].
  exists (n1+n2). left.
  hnf; intros.
  hnf in H0. spec H0.
admit.
  destruct H0 as [n'' [??]].
  destruct H7 as [p''' [r''' [? ?]]].
  exists (n'+n''). split. omega.
  do 2 econstructor; split. 2: eauto.
admit.
  exists (n1+n2). right.
admit.
  clear H.
  exists n1. left. intro. elimtype False; omega.
  exists (n1+1). right.
  repeat intro.
  hnf in  H. spec H. omega.
  destruct H as [n' [? ?]].
  exists (n'+1). split. omega.
admit.
Qed.

(*
Definition funptr' (l:label) (A:Type) (t:termMeas) (P Q: A -> pred world) : pred prog :=
  EX c : instruction, code l c &&
    ALL stk : stack, ALL n : nat, ALL x : A,
      |> ((embedWP (guardsn n (Q x) stk)) -->
           (ALL n' : nat, embedWP (evalTM t n'   -->
                                    guardsn (n+n') (P x) ((c;;instr_assert FF)::stk) ))).
*)

Definition funptr' (l:label) (A:Type) (t:termMeas) (P Q: A -> pred world) : pred prog :=
  EX c : instruction, code l c &&
  ALL stk : stack,  ALL x : A,
      embedWP (P x --> EX n:nat, evalTM t n &&
                 |>getsn n ((c;;instr_assert FF)::stk) stk (Q x)).

Definition funptr l A P Q : pred prog :=
  EX t:termMeas,
      funptr' l A t P Q &&
      ALL x:A, (embedWP (P x --> EX n:nat, evalTM t n)).

(*
Lemma hoare_call : forall G R v Q l A lP lQ a,
  let wp :=
      store_op (fun r => r#v = Some (value_label l)) &&
      prog_op (funptr l A lP lQ) &&
      lP a && (closed (lQ a --> Q))
 in
  hoare G R wp (instr_call v) Q.
Proof.
  repeat intro.
  subst wp.
  destruct H1 as [[[??]?]?].
  hnf in H2. destruct H2 as [? _].
  destruct H2 as [t [? ?]].
  hnf in H2.
  hnf in H2.
  destruct H2 as [i [? ?]].
  spec H6 (k :: stk) a r.
  spec H6 (p',r). spec H6; auto.
  spec H6; auto.
  destruct H6 as [n1 [? ?]].
  exists (1+n1). left.
  intro.
  case_eq (age1 p'); intros.
  spec H7 (p0,r). spec H7.
admit.
  hnf in H7. spec H7.
admit.
  destruct H7 as [n' [? ?]]. exists (1+n'). split. omega.
  destruct H10 as [p'' [r'' [? ?]]].
(*
  case_eq (age1 p''). intros p''' ?.
  exists p'''; exists r''; split.*)
  exists p''. exists r''. split; auto.
  destruct H2 as [i' [? ?]].
  econstructor.
  econstructor; eauto.
  hnf in H1. destruct H1.
  apply H13.
admit.
  spec H4 (p',r''). spec H4; simpl; auto.
  hnf. simpl; auto.
  eapply H4; eauto.
admit.
admit.
Qed.
*)

Definition verify_prog (psi:program assert) (G:pred prog) :=
  forall n, agedfrom (K.squash (n,psi)) && |>G |-- G.

(*
Lemma verify_func_simple : forall psi l (G:pred prog) (A:Type) (P Q:A -> pred world) i
  (REL:A -> A -> Prop),
  well_founded REL ->
  psi#l = Some i ->
  (forall a,
    let Pr' a' := P a' && !!(REL a' a) in
      exists t:termMeas,
        hoare (funptr' l A t Pr' Q && G) (Q a) (P a) i FF) ->

  verify_prog psi G ->
  verify_prog psi (funptr l A P Q  && G).
Proof.
  do 13 intro.
  intros w Hw.
  destruct Hw as [Hw1 Hw2].
  split.
  2: eapply H2; eauto.
  2: split; eauto.
  2: repeat rewrite later_and in Hw2.
  2: destruct Hw2; auto.
  hnf. intro x.
  induction x using (well_founded_induction H).
  destruct (H1 x) as [t' ?].
  hnf in H4.




  hnf; exists i. split.
admit.
  intros stk x r w' ? ?.
  spec H0 x r. simpl in H0. hnf in H0.
  case_eq (age1 w'); intros.
  spec H0 (fst w0).
  generalize (H0 (instr_assert FF)). clear H0; intro.
  spec H0 stk. spec H0.
  clear H0.
  split.
  spec H2 (level w0). spec H2.
admit.
  spec H2 (fst w0). spec H2.
  split; auto.
admit.
admit.
  destruct H2.
  destruct H0 as [? ?].
  destruct H0 as [i' [? ?]].
  exists i'. split; auto.
  intros stk' x' r' w'' ? ?.
  destruct H9. destruct w''; destruct H10. clear H10.
  rewrite later_and in Hw2.
  destruct Hw2.
  rewrite later_and in H10.
  destruct H10.
  spec H13 (fst w0).
  spec H13.
admit.
  spec H13 x r (fst w0, r). spec H13; auto.
  spec H13.
admit.
  destruct H13 as [n1 ?].
  simpl in H13.
  spec H11 n1 H13.
  destruct H11 as [n2 [? ?]].
  spec H7 stk' x' s (p,s).
  spec H7.
admit.
  spec H7; auto.
admit.

  spec H0 r (fst w0). spec H0; auto.
  spec H0. split.
admit.
  repeat rewrite later_and in Hw2.
  destruct Hw2. destruct H6.
  spec H8 (fst w0).
  spec H8.
admit.
  spec H8 x r. spec H8 (fst w0, r). spec H8; auto.
  spec H8.
admit.
  destruct H8 as [n' ?]. simpl in H8.
  exists n'; split; auto. hnf; auto.
  destruct H0 as [n' [?|?]].
admit.

  exists n'. split; auto.

*)

Lemma verify_func_simple : forall psi l (G:pred prog) (A:Type) (P Q:A -> pred world) i (t:termMeas),
  psi#l = Some i ->

  (forall a r,
    let Pr  := P a && EX n:nat, store_op (fun r' => proj1_sig t r' n /\ (r' = r)) in
    let Pr' a' := P a' && store_op (fun r' => forall n, proj1_sig t r n -> exists n', proj1_sig t r' n' /\ n' < n) in
    hoare (funptr' l A t Pr' Q && G) (Q a) Pr i FF) ->

  verify_prog psi G ->
  verify_prog psi (funptr' l A t P Q  &&
                   (ALL a:A, embedWP (P a --> EX x:nat, evalTM t x))
                   && G).
Proof.
  do 12 intro. induction n using (well_founded_induction lt_wf).
  intros w Hw.
  destruct Hw as [Hw1 Hw2].
  split.
  2: eapply H1; eauto.
  2: split; eauto.
  2: repeat rewrite later_and in Hw2.
  2: destruct Hw2; auto.
  split; intros.
  hnf; exists i. split.
admit.
  intros stk x r w' ? ?.
  spec H0 x r. simpl in H0. hnf in H0.
  case_eq (age1 w'); intros.
  spec H0 (fst w0).
  generalize (H0 (instr_assert FF)). clear H0; intro.
  spec H0 stk. spec H0.
  clear H0.
  split.
  spec H2 (level w0). spec H2.
admit.
  spec H2 (fst w0). spec H2.
  split; auto.
admit.
admit.
  destruct H2.
  destruct H0 as [? ?].
  destruct H0 as [i' [? ?]].
  exists i'. split; auto.
  intros stk' x' r' w'' ? ?.
  destruct H9. destruct w''; destruct H10. clear H10.
  rewrite later_and in Hw2.
  destruct Hw2.
  rewrite later_and in H10.
  destruct H10.
  spec H13 (fst w0).
  spec H13.
admit.
  spec H13 x' r (fst w0, r). spec H13; auto.
  spec H13.
admit.
  destruct H13 as [n1 ?].
  simpl in H13.
  spec H11 n1 H13.
  destruct H11 as [n2 [? ?]].
  spec H7 stk' x' s (p,s).
  spec H7.
admit.
  spec H7; auto.
admit.

  spec H0 r (fst w0). spec H0; auto.
  spec H0. split.
admit.
  repeat rewrite later_and in Hw2.
  destruct Hw2. destruct H6.
  spec H8 (fst w0).
  spec H8.
admit.
  spec H8 x r. spec H8 (fst w0, r). spec H8; auto.
  spec H8.
admit.
  destruct H8 as [n' ?]. simpl in H8.
  exists n'; split; auto. hnf; auto.
  destruct H0 as [n' [?|?]].
admit.
  repeat rewrite later_and in Hw2.
  destruct Hw2. destruct H6.
  spec H8 (fst w0).
  spec H8.
admit.
  spec H8 x r. spec H8 (fst w0, r). spec H8; auto.
  spec H8.
admit.
  destruct H8 as [n'' ?].
  exists n''. split; auto.
admit.































Lemma hoare_weaken : forall x x' G G' (R R' P P' Q Q':pred world) i,
  x <= x' ->
  G' |-- G  ->
  prog_op G' && R  |-- R' ->
  prog_op G' && P' |-- P  ->
  prog_op G' && Q  |-- Q' ->
  hoare' x  G  R  P  i Q ->
  hoare' x' G' R' P' i Q'.
Proof.
  intros until i; repeat intro.
  destruct a'.
  spec H4 p n k stk.
  spec H4; auto.
  rewrite worldNec_unfold in H8.
  destruct H8.
  subst s.
  spec H4. repeat intro. eapply H6; eauto.
  apply H1. split; auto. destruct a'. rewrite worldNec_unfold in H10. split; trivial.
  apply pred_nec_hereditary with p; intuition.
  spec H4. repeat intro. eapply H7; eauto.
  apply H3. split; auto. destruct a'. rewrite worldNec_unfold in H10. split; auto.
  apply pred_nec_hereditary with p; intuition.
  spec H4 r (p0, r).
  spec H4. rewrite worldNec_unfold. intuition.
  spec H4; auto.
  apply H2. split; auto. split; auto.
  apply pred_nec_hereditary with p; auto.
  simpl in *.
  intro.
  spec H4. omega.
  destruct H4 as [px [rx [? ?]]].
  exists px. exists rx. split; trivial.
  omega.
Qed.

Lemma hoare_weaken_time : forall x x' G R P i Q,
  x <= x' ->
  hoare' x G R P i Q ->
  hoare' x' G R P i Q.
Proof.
  intros until Q. intro. apply hoare_weaken; hnf; simpl; intuition.
Qed.

Lemma hoare_weaken_pre : forall x G R P P' i Q,
  prog_op G && P' |-- P ->
  hoare' x G R P i Q ->
  hoare' x G R P' i Q .
Proof.
  intros until Q. intro.
  apply hoare_weaken; hnf; simpl; intuition.
Qed.

Lemma hoare_weaken_post : forall x G R P i Q Q',
  prog_op G && Q |-- Q' ->
  hoare' x G R P i Q ->
  hoare' x G R P i Q'.
Proof.
  intros until Q'. intro.
  apply hoare_weaken; hnf; simpl; intuition.
Qed.

Lemma hoare_ex_pre : forall x G R T P i Q,
  (forall z:T, hoare' x G R (P z) i Q) ->
  hoare' x G R (exp P) i Q.
Proof.
  repeat intro.
  destruct H4.
  spec H x0.
  eapply H; eauto.
Qed.

Lemma hoare_ex_pre' : forall x G R T P i Q,
  hoare' x G R (exp P) i Q ->
  (forall z:T, hoare' x G R (P z) i Q).
Proof.
  repeat intro.
  eapply H; eauto.
  exists z. auto.
Qed.

Lemma hoare_fact_pre : forall x G R (X:Prop) P i Q,
  (X -> hoare' x G R P i Q) ->
  hoare' x G R (!!X && P) i Q.
Proof.
  repeat intro.
  destruct H4. hnf in H4.
  spec H H4. eapply H; eauto.
Qed.

Lemma hoare_return : forall G R,
  hoare' 0 G R R instr_return FF.
Proof.
  repeat intro.
  spec H0 r a' H2 H3.
  destruct a'.
  intro.
  destruct H0 as [pz [rz [? ?]]]. omega.
  exists pz. exists rz.
  split. omega.
  econstructor. eapply step_return.
  auto.
Qed.

Lemma hoare_seq : forall x y G R P Q S i1 i2,
  hoare' x G R P i1 Q ->
  hoare' y G R Q i2 S ->
  hoare' (x+y) G R P (i1 ;; i2) S.
Proof.
  intros. hnf; intros.
  assert (guardsn (x+(y+n)) P ((i1;;i2;;k)::stk) (p,r)).
    apply H; auto.
    repeat intro. destruct a'. repeat intro.
    rewrite worldNec_unfold in H4. destruct H4. subst s.
    spec H2 r' (p0, r'). spec H2. rewrite worldNec_unfold. intuition.
    spec H2 H5.
    unfold haltsn in H2. simpl in H2. spec H2. omega.
    destruct H2 as [pz [rz [? ?]]].
    exists pz; exists rz.
    split. omega.
    trivial.
  do 3 intro.
  spec H4 a' H5 H6.
  destruct a'. intro. unfold haltsn in H4. simpl in H4. spec H4. omega.
  destruct H4 as [px [rx [? ?]]].
  exists px. exists rx.
  split. omega.
  econstructor. econstructor.
  auto.
Qed.



Lemma hoare_getlabel : forall l v G R P,
  hoare' 0 G R
    (box (setM v (value_label l)) P)
    (instr_getlabel l v)
    P.
Proof.
  repeat intro.
  spec H1 (r#v <- (value_label l)).
  destruct a'.
  rewrite worldNec_unfold in H2. destruct H2. subst s.
  spec H1 (p0, r#v <- (value_label l)).
  spec H1. rewrite worldNec_unfold. intuition.
  spec H1. apply H3. constructor; auto.
  intro.
  destruct H1 as [pz [rz [? ?]]]. omega.
  exists pz; exists rz.
  split. omega.
  econstructor. econstructor.
  auto.
Qed.

Lemma hoare_call : forall x G R v Q l A t lP lQ a,
  let wp :=
      store_op (fun r => r#v = Some (value_label l)) &&
      evalTM t x &&
      (prog_op (funptr' l A t lP lQ)) &&
      lP a && (closed (lQ a --> Q))
 in
  hoare' (S x) G R wp (instr_call v) Q.
Proof.
  do 23 intro.
  unfold wp in H3.
  destruct H3 as [[[[? ?] ?] ?] ?].
  destruct a'.
  destruct H5 as [[i [? ?]] _].
  intro.
  case_eq (age1 p0); intros.
  2: rewrite (af_level1 age_facts) in H10; omegac.
  spec H8 (k::stk) n a p1.
  spec H8. simpl. apply t_step. trivial.
  spec H8 p1. spec H8. apply rt_refl.
  spec H8.
    intros r'. spec H1 r'.
    repeat intro.
    spec H1 a'.
    spec H1.
    destruct a'.
    rewrite worldNec_unfold in H11. destruct H11. subst s0.
    rewrite worldNec_unfold in H2. destruct H2. subst s.
    rewrite worldNec_unfold. split; trivial.
    apply rt_trans with p0. trivial.
    apply rt_trans with p1. apply rt_step. trivial. trivial.
    spec H1; auto.
    destruct a'.
    spec H7 (p0,s0).
    spec H7. simpl; hnf; auto.
    apply H7; auto.
    repeat rewrite worldNec_unfold in *; intuition.
    apply rt_trans with p1; auto.
    apply rt_step; auto.
  spec H8 x s (p1,s).
  spec H8. simpl; hnf; auto.
  spec H8. apply H4.
  spec H8 (p1,s).
  spec H8. apply rt_refl.
  spec H8. apply pred_nec_hereditary with (p0,s); auto.
  rewrite worldNec_unfold; intuition.

  copy H10.
  apply (af_level2 age_facts) in H10.
  destruct H8 as [pz [rz [? ?]]]. omega.
  exists pz; exists rz.
  split. omega.
  destruct H5 as [ix [? ?]].
  econstructor.
  eapply step_call.
  apply H3.
  apply H5.
  apply H11.
  generalize (stepstar_approxprog 0 p1 pz p1 pz s
      ((i;; instr_assert FF) :: k :: stk) ((ix;; instr_assert FF) :: k :: stk)
      rz nil); intro.
  spec H14 H12.
  spec H14. red. trivial.
  spec H14. red. trivial.
  spec H14.
  constructor.
  rewrite <- H10.
  red. simpl. red in H13. congruence.
  apply stack_approx_rel_refl.
  destruct H14 as [sx [? ?]].
  inversion H15.
  subst sx.
  trivial.
Qed.

Lemma hoare_call2 : forall G R v Q l A t lP lQ a,
  let wp :=
      store_op (fun r => r#v = Some (value_label l)) &&
      (prog_op (funptr' l A t lP lQ)) &&
      lP a && (closed (lQ a --> Q))
 in
  hoare G R wp (instr_call v) Q.
Proof.
  intros.
  hnf. subst wp.







Lemma hoare_call' : forall x G R v Q,
  let wp :=
    EX l:label, EX A:Type, EX t:termMeas,
    EX lP:(A->pred world), EX lQ:(A -> pred world), EX a:A,
      store_op (fun r => r#v = Some (value_label l)) &&
      (evalTM t x) &&
      (prog_op (funptr l A t lP lQ)) &&
      lP a && (closed (lQ a --> Q))
 in
  hoare (S x) G R wp (instr_call v) Q.
Proof.
  intros. subst wp.
  repeat (apply hoare_ex_pre; intro).
  apply hoare_call.
Qed.

Lemma hoare_step_fetch0 : forall v1 v2 x1 x2 G R P,
  hoare 0 G R
    (store_op (fun r => r#v1 = Some (value_cons x1 x2)) && box (setM v2 x1) P)
    (instr_fetch_field v1 0 v2)
    P.
Proof.
  repeat intro.
  destruct a'.
  destruct H3.
  destruct H3 as [_ ?].
  rewrite worldNec_unfold in H2. destruct H2. subst s.
  spec H1 (r#v2 <- x1).
  spec H1 (p0,r#v2 <- x1).
  spec H1. repeat rewrite worldNec_unfold; intuition.
  spec H1. apply H4. constructor. auto.
  intro.
  spec H1 H5.
  destruct H1 as [pz [rz [? ?]]].
  exists pz; exists rz.
  split; trivial.
  econstructor. econstructor. eauto.
  auto.
Qed.

Lemma hoare_step_fetch1 : forall v1 v2 x1 x2 G R P,
  hoare 0 G R
    (store_op (fun r => r#v1 = Some (value_cons x1 x2)) && box (setM v2 x2) P)
    (instr_fetch_field v1 1 v2)
    P.
Proof.
  repeat intro.
  destruct a'.
  destruct H3.
  destruct H3 as [_ ?].
  rewrite worldNec_unfold in H2. destruct H2. subst s.
  spec H1 (r#v2 <- x2).
  spec H1 (p0,r#v2 <- x2).
  spec H1. repeat rewrite worldNec_unfold; intuition.
  spec H1. apply H4. constructor. auto.
  intro.
  spec H1 H5.
  destruct H1 as [pz [rz [? ?]]].
  exists pz; exists rz.
  split; trivial.
  econstructor. econstructor. eauto.
  auto.
Qed.

Lemma hoare_cons : forall v1 v2 v3 x1 x2 G R P,
  hoare 0 G R
     (store_op (fun r => r#v1 = Some x1 /\ r#v2 = Some x2) &&
        box (setM v3 (value_cons x1 x2)) P)
     (instr_cons v1 v2 v3)
     P.
Proof.
  repeat intro.
  destruct a'.
  destruct H3.
  destruct H3 as [_ ?].
  rewrite worldNec_unfold in H2. destruct H2. subst s.
  spec H1 (r#v3 <- (value_cons x1 x2)).
  spec H1 (p0, r#v3 <- (value_cons x1 x2)).
  spec H1. repeat rewrite worldNec_unfold; intuition.
  spec H1. apply H4. constructor. auto.
  intro.
  spec H1 H5.
  destruct H1 as [pz [rz [? ?]]].
  exists pz; exists rz.
  split; trivial.
  destruct H3.
  econstructor. econstructor; eauto.
  auto.
Qed.

Lemma hoare_if : forall x v s1 s2 P1 P2 G R Q,
  let wp :=
    EX val:value,
      store_op (fun r => r#v = Some val) &&
    (

      ((!!(val = value_label (L 0)) && P1))
      ||
      ((EX x1:value, (EX x2:value,
        !!(val = (value_cons x1 x2)))) && P2)
    )
   in
  hoare x G R P1 s1 Q ->
  hoare x G R P2 s2 Q ->
  hoare x G R wp (instr_if_nil v s1 s2) Q.
Proof.
  do 23 intro.
  hnf in H5.
  destruct a'.
  destruct H5 as [v' [[_ ?] ?]].
  destruct H6 as [[? ?]|[? ?]].

  (* nil case *)
  simpl in H6.
  spec H p n k stk.
  do 3 (spec H; auto).
  rewrite worldNec_unfold in H4. destruct H4. subst s.
  spec H r (p0,r).
  spec H. rewrite worldNec_unfold. intuition.
  spec H H7.
  intro.
  spec H H8.
  destruct H as [pz [rz [? ?]]].
  exists pz; exists rz.
  split; trivial.
  econstructor. eapply step_if_nil1; eauto.
  subst v'; auto.
  auto.

  (* cons case *)
  destruct H6 as [v1 [v2 ?]]. simpl in H6. subst v'.
  spec H0 p n k stk.
  do 3 (spec H0; auto).
  rewrite worldNec_unfold in H4. destruct H4. subst s.
  spec H0 r (p0,r).
  spec H0. rewrite worldNec_unfold. intuition.
  spec H0 H7.
  intro. spec H0 H6.
  destruct H0 as [pz [rz [? ?]]].
  exists pz; exists rz.
  split; trivial.
  econstructor. eapply step_if_nil2; eauto.
  auto.
Qed.

Lemma hoare_assert : forall G R P (Q:assert),
  prog_op G && P |-- Q ->
  hoare 0 G R P (instr_assert Q) P.
Proof.
  repeat intro.
  spec H2 r a' H3 H4.
  destruct a'.
  intro.
  spec H2 H5.
  destruct H2 as [px [rx [? ?]]].
  exists px. exists rx.
  split. trivial.
  econstructor 2.
  econstructor.
  apply H.
  split; auto.
  rewrite <- (nec_useless G) in H0.
  simpl; split; auto.
  apply H0.
  rewrite worldNec_unfold in H3. intuition.
  auto.
Qed.


(* Verifying function bodies and entire programs *)

Definition verify_prog (psi:program assert) (G:pred prog) :=
  forall n, agedfrom (K.squash (n,psi)) && |>G |-- G.

Lemma verify_complete : forall G psi,
  verify_prog psi G ->
  forall n, G (K.squash (n,psi)).
Proof.
  intros.
  spec H n.
  cut (agedfrom (K.squash (n,psi)) |-- G).
  intros.
  eapply H0.
  hnf; apply rt_refl.
  apply goedel_loeb.
  apply derives_trans with
    (agedfrom (K.squash (n,psi)) && |>G); auto.
  intros a Ha; destruct Ha; split; auto.
Qed.

Record funspec (B:Type) :=
  { fs_A  : B -> Type
  ; fs_t  : B -> termMeas
  ; fs_P  : forall b, fs_A b -> pred world
  ; fs_Q  : forall b, fs_A b -> pred world
  }.

Definition funspec_assumptions B b n (fss:list (label*funspec B) ) : pred prog :=
  ALL l:_, ALL fs:_, !!(In (l,fs) fss) -->
    let P' a := fs_P B fs b a &&
      store_op (fun r => exists n', proj1_sig (fs_t B fs b) r n' /\ n' < n)
    in funptr l (fs_A B fs b) (fs_t B fs b) P' (fs_Q B fs b).

Lemma verify_true :
  forall psi,
    verify_prog psi TT.
Proof.
  repeat intro; hnf; auto.
Qed.

Lemma verify_clique : forall psi G B (fss:list (label * funspec B)),

  (forall l fs,
    In (l,fs) fss ->
    exists i, psi#l = Some i /\
    forall b a n,
    let Pr := fs_P B fs b a && store_op (fun r' => proj1_sig (fs_t B fs b) r' n) in
      hoare n (funspec_assumptions B b n fss && G) (fs_Q B fs b a) Pr i FF) ->

  verify_prog psi G ->

  verify_prog
      psi
      ((ALL b:B, ALL l:_, ALL fs:_,
        !!(In (l,fs) fss) -->
        funptr l (fs_A B fs b) (fs_t B fs b)
        (fs_P B fs b) (fs_Q B fs b)) && G).
Proof.
  repeat intro.
  destruct H1.
  rewrite box_and in H2; destruct H2.
  split. 2: eapply H0; eauto; split; eauto.
  apply verify_complete with _ _ n in H0.
  clear H3.
  simpl in H1.
  clear H2.
  intros b l fs p' ? ?. simpl in H3.
  unfold funptr.
  destruct (H l fs H3) as [i [? ?]].
  exists (fmap_instr (K.approx (level p')) i).
  split.
  exists
    (fmap_instr (K.approx (level p')) (fmap_instr (K.approx n) i)). split.
  apply nec_prog_lookup with (K.squash (n,psi)).
  eapply rt_trans; eauto.
  unfold prog_lookup. rewrite K.unsquash_squash. simpl. unfold KnotInput.fmap.
  erewrite fmap_eqn.
  auto.
  auto.
  hnf.
  f_equal.
  rewrite collapse_instr_approx.
  rewrite min_l; auto.
  replace n with (level (K.squash (n,psi))).
  apply nec_level. apply rt_trans with a; auto.
  rewrite K.knot_level.
  rewrite K.unsquash_squash; auto.

  clear H5.
  intros stk n0 x ? ? ? ? ? n'.
  revert stk n0 x a' a'0 H5 H6 H7.
  revert l fs i H3 H4.
  induction n' using (well_founded_induction lt_wf).

  repeat intro.
  destruct a'1. rewrite worldNec_unfold in H9. destruct H9; subst.
  destruct a'2. rewrite worldNec_unfold in H11. destruct H11; subst.
  simpl in H10.
  destruct (H l fs H4) as [i' [? ?]].
  rewrite H5 in H13; inv H13.
  rename i' into i.
  spec H14 b x n'.
  hnf in H14.
  spec H14 p n0.
  generalize (H14 (instr_assert FF)). clear H14; intro H14.
  spec H14 stk.
  spec H14.
    split.
    hnf; simpl; intros.
    destruct (H b0 b1 H15) as [i' [? ?]].
    exists (fmap_instr (K.approx (level a'1) )i'). split.
    exists (fmap_instr (K.approx (level a'1)) i'). split.
    replace (fmap_instr (K.approx (level a'1)) i')
      with  (fmap_instr (K.approx (level a'1)) (fmap_instr (K.approx n) i')).
    apply nec_prog_lookup with (K.squash (n,psi)).
    apply rt_trans with p; auto.
    apply rt_trans with a'0; auto.
    apply rt_trans with a'; auto.
    apply rt_trans with p'; auto.
    apply rt_trans with a; auto.
    apply Rt_Rft; auto.
    unfold prog_lookup.
    rewrite K.unsquash_squash; simpl.
    unfold KnotInput.fmap.
    eapply fmap_eqn; auto.
    rewrite collapse_instr_approx.
    rewrite min_l; auto.
    replace n with (level (K.squash (n,psi))).
    apply nec_level.
    apply rt_trans with a; auto.
    apply rt_trans with p'; auto.
    apply rt_trans with a'; auto.
    apply Rt_Rft; auto.
    apply rt_trans with a'0; auto.
    apply rt_trans with p; auto.
    rewrite K.knot_level. rewrite K.unsquash_squash.
    simpl; auto.
    hnf. auto.

    intros.
    destruct H24.
    destruct a'5.
    destruct H25.
    destruct H26 as [n'' [? ?]].
    destruct a'4.
    rewrite worldNec_unfold in H21.
    destruct H21.
    subst s1.
    intros.
    rewrite worldNec_unfold in H23.
    destruct H23; subst.
    assert (n'' = b5).
    destruct (fs_t B b1 b); eauto.
    subst b5.
    spec H3 n''.
    spec H3; auto.
    spec H3 b0 b1 i'.
    spec H3; auto.
    spec H3; auto.
    spec H3 b2 b3 b4.
    spec H3 a'1 a'3.
    spec H3.
      simpl.
      apply Rt_Rft_trans with a'; auto.
      apply rt_trans with p; auto.
      apply rt_trans with a'0; auto.
    spec H3.
      apply rt_trans with a'2; auto.
      apply Rt_Rft; auto.
    spec H3; auto.
    simpl in H3.
    spec H3 s (p2,s).
    spec H3.
    rewrite worldNec_unfold; simpl; auto.
    spec H3; auto.
    spec H3 (p1,s).
    spec H3.
    rewrite worldNec_unfold; simpl; auto.
    spec H3; auto.
    spec H3; auto.
    destruct H3 as [? [? [? ?]]].
    destruct (stepstar_approxprog 0 p1 x0 p1 x0 _ _ (((fmap_instr (K.approx (level a'1)) i');;instr_assert FF) :: b2) _ _ H29).
    simpl; auto.
    simpl; auto.
    constructor.
    hnf. simpl. f_equal.
    rewrite collapse_instr_approx.
    rewrite min_l.
    rewrite collapse_instr_approx.
    rewrite min_l.
    auto.
    apply later_level.
    apply Rt_Rft_trans with a'2; auto.
    apply rt_trans with a'3; auto.
    apply rt_trans with p2; auto.

    apply later_level.
    apply Rt_Rft_trans with a'; auto.
    apply rt_trans with a'0; auto.
    apply rt_trans with p; auto.
    apply rt_trans with a'1; auto.
    apply rt_trans with a'2; auto.
    apply Rt_Rft; auto.
    apply rt_trans with a'3; auto.
    apply rt_trans with p2; auto.

    apply stack_approx_rel_refl.
    destruct H30.
    inv H31. hnf; eauto.
    apply pred_nec_hereditary with (K.squash (n,psi)); auto.
    apply rt_trans with a; auto.
    apply rt_trans with p'; auto.
    apply rt_trans with a'; auto.
    apply Rt_Rft; auto.
    apply rt_trans with a'0; auto.

  spec H14.
  intro r'.
  spec H8 r'.
  apply pred_nec_hereditary with (a'0,r'); auto.
  rewrite worldNec_unfold; auto.
  spec H14; repeat intro. inv H15.
  spec H14 s0.
  simpl in H14.
  spec H14 (p0,s0).
  spec H14.
  rewrite worldNec_unfold; auto.
  spec H14; intuition.
  spec H14. omega.
  rewrite plus_comm.
  destruct H14 as [? [? [? ?]]].
  destruct (stepstar_approxprog 0 p0 x0 p0 x0 _ _ (((fmap_instr (K.approx (level p')) i);;instr_assert FF) :: stk) _ _ H15).
  simpl; auto.
  simpl; auto.
  constructor.
  hnf; simpl. f_equal.
  rewrite collapse_instr_approx.
  rewrite min_l.
  auto.
  apply later_level.
  apply Rt_Rft_trans with a'; auto.
  apply rt_trans with a'0; auto.
  apply rt_trans with p; auto.
  apply stack_approx_rel_refl.
  destruct H16.
  inv H17.
  hnf; eauto.
Qed.


Lemma verify_func : forall psi l (G:pred prog) (B:Type) (A:B->Type) (P Q:forall b, A b -> pred world) i (t:B -> termMeas),
  psi#l = Some i ->

  (forall b a n,
    let Pr  := P b a && store_op (fun r' => proj1_sig (t b) r' n) in
    let Pr' a' := P b a' && store_op (fun r' => exists n', proj1_sig (t b) r' n' /\ n' < n) in
    hoare n (funptr l (A b) (t b) Pr' (Q b) && G) (Q b a) Pr i FF) ->

  verify_prog psi G ->
  verify_prog psi
              ((ALL b:_, funptr l (A b) (t b) (P b) (Q b)) && G).
Proof.
  intros.
  generalize (verify_clique psi G B
    ((l,Build_funspec B A t P Q)::nil)); intros.
  spec H2.
    clear H2.
    intros.
    simpl in H2. intuition. inv H3.
    exists i; split; auto.
    simpl. intros.
    spec H0 b a n.
    revert H0.
    Opaque funptr.
    apply hoare_weaken; auto;
      hnf; simpl; intuition.
    spec H2 l0 (Build_funspec B A t P Q) a0.
    spec H2; auto.
  spec H2; auto.
  repeat intro.
  spec H2 n a.
  destruct H3.
  spec H2; split; auto.
    repeat intro.
    spec H4 a' H5.
    destruct H4; split; auto.
    repeat intro.
    simpl in H4.
    spec H4 b.
    simpl in H8. intuition.
    inv H9.
    simpl.
    eapply pred_nec_hereditary; eauto.
    destruct H2.
    intro b.
    spec H2 b.
    spec H2 l (Build_funspec B A t P Q).
    spec H2 a. spec H2; auto.
    simpl in H2. spec H2; auto.
    destruct H2; auto.
Qed.

Lemma verify_func_simple : forall psi l (G:pred prog) (A:Type) (P Q:A -> pred world) i (t:termMeas),
  psi#l = Some i ->

  (forall a n,
    let Pr  := P a && store_op (fun r' => proj1_sig t r' n) in
    let Pr' a' := P a' && store_op (fun r' => exists n', proj1_sig t r' n' /\ n' < n) in
    hoare n (funptr l A t Pr' Q && G) (Q a) Pr i FF) ->

  verify_prog psi G ->
  verify_prog psi (funptr l A t P Q && G).
Proof.
  intros.
  generalize (verify_func psi l G unit (fun _ => A) (fun _ => P) (fun _ => Q) i (fun _ => t) H); intros.
  spec H2. intros. eapply H0; eauto.
  spec H2. intros. eapply H1; eauto.
  repeat intro.
  spec H2 n a.
  rewrite box_and in H3.
  destruct H3.
  destruct H4.
  spec H2. split; auto.
  rewrite box_and. split; auto.
  rewrite box_all. intro. auto.
  destruct H2; split; auto.
  apply H2. exact tt.
Qed.

Lemma end_assert_lemma : forall Q n p p' r r' stk,
    stepN n p p' r (stk++(instr_assert Q ;; instr_return ;; instr_assert FF) :: nil) r' nil ->
    stepstar p p' r stk r' nil /\ proj1_sig Q (p',r').
Proof.
  induction n; simpl; intros; inv H.
  destruct stk; discriminate.
  destruct stk. simpl in H1.
  inv H1.
  inv H2.
  inv H.
  inv H0.
  split; auto.
  constructor.
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
  apply IHn with (stk:= (i'0;;instr_assert FF)::i0::stk) in H2.
  intuition. econstructor. econstructor; eauto. auto.
  apply IHn with (stk:=stk) in H2.
  intuition. econstructor. econstructor. auto.
Qed.

(* Fundamental liveness theorem.  A verified function,
   when started in a state satisfying its precondition,
   will halt in a state satisfying its postcondition.
 *)

Lemma verify_totally_correct : forall G A P Q psi l t x,
  verify_prog psi G ->
  G |-- funptr l A t P Q ->
  forall r,
    (forall n, P x (K.squash (n,psi),r)) ->
    forall n c, proj1_sig t r n ->
      psi#l = Some c ->
      exists p', exists r',
        stepstar (K.squash (n,psi)) p'
        r ((c ;; instr_assert FF)::nil)
        r' nil /\
        Q x (p',r').
Proof.
  intros.
  assert (forall n, G (K.squash (n,psi))).
  apply verify_complete; auto.
  hnf; auto.
  assert (funptr l A t P Q (K.squash (S n,psi))) by auto.
  destruct H5 as [i [? ?]].
  spec H6 ((instr_assert (Q x) ;; instr_return ;; instr_assert FF)::nil).
  spec H6 0 x (K.squash (n,psi)).
  spec H6.
  simpl.
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
  spec H6 (K.squash (n,psi)).
  spec H6.
  apply rt_refl.
  spec H6.
  repeat intro.
  destruct a'.
  simpl.
  intro.
  exists p.
  econstructor.
  split.
  omega.
  econstructor.
  econstructor.
  auto.
  econstructor 2.
  econstructor.
  econstructor.

  spec H6 n r.
  spec H6 (K.squash (n,psi),r).
  spec H6; auto.
  spec H6. auto.
  spec H6 (K.squash (n,psi),r).
  spec H6; auto.
  spec H6. auto.
  hnf in H6.
  spec H6; auto.
  rewrite K.knot_level.
  rewrite K.unsquash_squash; simpl. omega.
  destruct H6 as [pz [rz [? ?]]].
  exists pz; exists rz.
  destruct H5 as [i' [? ?]].
  rewrite K.knot_level in H8.
  rewrite K.unsquash_squash in H8.
  simpl in H8.
  unfold prog_lookup in H5.
  rewrite K.unsquash_squash in H5.
  simpl in H5.
  unfold KnotInput.fmap in H5.
  apply fmap_eqn2 in H5.
  destruct H5 as [? [? ?]].
  unfold prog in *.
  unfold assert, world, prog, KnotInput.other in *.
  rewrite H3 in H5.
  inv H5.
  assert (stepstar (K.squash (n,psi)) pz r
    ((x0;;instr_assert FF) ::
      (instr_assert (Q x) ;; instr_return ;; instr_assert FF) :: nil) rz nil).
  generalize H7; intros.
  eapply stepstar_approxprog in H7.
  2: instantiate (2:=O). 2: simpl; auto.
  2: simpl; auto.
  2: instantiate (1:=
    (x0;; instr_assert FF) ::
    (instr_assert (Q x);; instr_return;;instr_assert FF) :: nil).
  destruct H7 as [? [? ?]].
  inv H9.
  auto.
  constructor.
  rewrite K.knot_level; simpl.
  rewrite K.unsquash_squash.
  simpl.
  hnf.
  hnf in H8.
  simpl; f_equal.
  rewrite collapse_instr_approx in H8.
  rewrite min_l in H8; auto.
  apply stack_approx_rel_refl.
  apply stepstar_stepN in H5.
  destruct H5.
  eapply end_assert_lemma; eauto.
Qed.

(* Weaker corollary: a program with a safe entry point
   will eventually halt.
 *)
Corollary verify_halts : forall t G psi l,
  verify_prog psi G ->
  G |-- funptr l unit t (fun _ => TT) (fun _ => TT) ->
  forall r n c,
    proj1_sig t r n ->
    psi#l = Some c ->
    eventually_halts (K.squash (n,psi)) r
       ((c ;; instr_assert FF)::nil).
Proof.
  intros.
  generalize (verify_totally_correct G unit (fun _ => TT) (fun _ => TT) psi l t tt); intros.
  spec H3; auto.
  spec H3; auto.
  spec H3 r.
  spec H3; auto.
  intros; hnf; auto.
  spec H3 n c H1 H2.
  hnf.
  destruct H3 as [? [? [? ?]]].
  eauto.
Qed.
