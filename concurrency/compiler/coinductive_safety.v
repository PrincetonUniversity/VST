(** printing \2/ $\cup$ #&cup;# *)
(** printing <2= $\subseteq$ #&sube;# *)
(** printing forall $\forall$ #&forall;# *)
(** printing -> $\rightarrow$ #&rarr;# *)
(** printing /\ $\land$ #&and;# *)

Require Import Setoid Program.
Require Import VST.concurrency.paco.src.paco.

Section safety_equivalence.

  Context
  ( X Y:Type)
  ( halted: X -> Y -> Prop)
  ( int_step: X -> Y -> Y -> Prop)
  ( ext_step: X -> Y -> X -> Y -> Prop)
  ( valid: X -> Y -> Prop).

  Axiom determinism:
    forall x y y',
      valid x y  -> int_step x y y' ->
      forall x',
        valid x' y -> int_step x' y y'.

  Axiom valid_step:
    forall x y y',
      valid x y  -> int_step x y y' ->
      valid x y'.

  Section explicit_safety.

    (** *Normal explicit safety *)
    CoInductive exp_safety (x:X) (y:Y): Prop:=
    | halted_safety : halted x y -> exp_safety x y
    | internal_safety y': int_step x y y'  ->
                          (forall x',  valid x' y' -> exp_safety x' y') ->
                          exp_safety x y
    | external_safety x' y': ext_step x y x' y' ->
                             (forall x',  valid x' y' -> exp_safety x' y') ->
                             exp_safety x y.

    (*Parametrized version*)
    Inductive exp_safety_gen {_exp_safety} (x:X) (y:Y): Prop:=
    | paco_halted_safety : halted x y -> exp_safety_gen x y
    | paco_internal_safety y': int_step x y y'  ->
                               (forall x',  valid x' y' -> _exp_safety x' y') ->
                               exp_safety_gen x y
    | paco_external_safety x' y': ext_step x y x' y' ->
                                  (forall x',  valid x' y' -> _exp_safety x' y') ->
                                  exp_safety_gen x y.
    Definition paco_exp_safety := paco2 (@exp_safety_gen).



    (*Show that the paco representation is correct. *)
    Lemma exp_safety_paco_correct:
      forall x y, exp_safety x y <-> paco_exp_safety bot2 x y.
    Proof.
      intros x y; split; generalize x y; clear x y.
      - pcofix CO; intros x y HH.
        pfold. inversion HH;
          [ econstructor 1; eauto |
            econstructor 2; eauto |
            econstructor 3; eauto ]; intros x'' VAL'.
      - cofix CO; intros x y HH.
        inversion HH. inversion SIM;
          [ econstructor 1; eauto |
            econstructor 2; eauto |
            econstructor 3; eauto ]; intros x'' VAL'; eapply CO.
        + specialize (LE _ _ (H0 _ VAL')).
          destruct LE. 2: compute in *; tauto.
          apply H1.
        + specialize (LE _ _ (H0 _ VAL')).
          destruct LE. 2: compute in *; tauto.
          apply H1.
    Qed.

  End explicit_safety.

  Section explicit_safetyN.
    Inductive stepN x y y': nat -> Prop :=
    | trivial_step: y = y' -> stepN x y y' 0
    | _stepN n _y: int_step x y _y -> stepN x _y y' n -> stepN x y y' (S n).

    (** *Safety with stepN *)
    Inductive exp_safetyN_gen {_exp_safety} (x:X) (y:Y): Prop:=
    | paco_halted_safetyN : halted x y -> exp_safetyN_gen x y
    | paco_internal_safetyN y' n: stepN x y y' (S n)  ->
                                  (forall x',  valid x' y' -> _exp_safety x' y') ->
                                  exp_safetyN_gen x y
    | paco_external_safetyN x' y': ext_step x y x' y' ->
                                   (forall x',  valid x' y' -> _exp_safety x' y') ->
                                   exp_safetyN_gen x y.
    Definition paco_exp_safetyN := paco2 (@exp_safetyN_gen).

    Lemma determinismN:
      forall n,
      forall x y y',
        valid x y  -> stepN x y y' n ->
        forall x',
          valid x' y -> stepN x' y y' n.
    Proof. induction n.
           - intros; econstructor.
             inversion H0; assumption.
           - intros.
             inversion H0; subst.
             econstructor.
             eapply (determinism x y _y); eauto.
             eapply IHn; eauto.
             eapply valid_step; eauto.
             eapply valid_step; eauto.
             eapply (determinism x y _y); eauto.
    Qed.

    Lemma valid_stepN:
      forall n,
      forall x y y',
        valid x y  -> stepN x y y' n ->
        valid x y'.
    Proof. induction n; intros ? ? ? VAL HH; inversion HH; subst.
           - exact VAL.
           - apply (IHn _ _y); try assumption.
             apply (valid_step x y _y VAL H0).
    Qed.

    Lemma safetyN_equivalence:
      forall x y,
        valid x y ->
        paco_exp_safety bot2 x y <-> paco_exp_safetyN bot2 x y.
    Proof.
      intros x y VAL.
      split; generalize x y VAL; clear VAL x y.
      - pcofix CO.
        intros x y VAL HH.
        inversion HH.
        inversion SIM; subst; clear SIM.
        + pfold.
          econstructor 1; eassumption.
        + pfold.
          econstructor 2. apply (_stepN x y y' 0 y'); auto.
          constructor; reflexivity.
          intros x' AA.
          right.
          eapply CO; try assumption.
          specialize (LE _ _ (H0 _ AA)).
          destruct LE. 2: compute in *; tauto.
          unfold paco_exp_safety.
          apply H1.
        + pfold.
          econstructor 3. eauto.
          intros x'0 AA.
          right.
          eapply CO; try assumption.
          specialize (LE _ _ (H0 _ AA)).
          destruct LE. 2: compute in *; tauto.
          unfold paco_exp_safety.
          apply H1.
      - pcofix CO.
        intros x y VAL HH; inversion HH; clear HH.
        inversion SIM; subst; clear SIM.
        + pfold.
          econstructor 1; eassumption.
        + cut (valid x y').
          { intros VAL'.
            assert (LE':= LE).
            specialize (LE _ _ (H0 _ VAL')).
            destruct LE. 2: compute in *; tauto.
            generalize dependent y; generalize x.
            induction n.
            * (*base case*)
              intros ? ? VAL H; inversion H; inversion H4; subst; clear H H4.
              pfold. econstructor 2. eassumption.
              intros x' AA.
              right.
              eapply CO; try assumption.
              specialize (LE' _ _ (H0 _ AA)).
              destruct LE'; [ | compute in *; tauto].
              unfold paco_exp_safetyN.
              apply H.
            * (*inductive step*)
              intros. inversion H; subst; clear H.
              pfold; econstructor 2; eauto.
              intros.
              unfold upaco2.
              left; eapply IHn; eauto.
              eapply (determinismN _ x0 _y y' ) with (x'0:= x'); eauto.
              eapply valid_step; eauto.
          }
          { (*Prove the cut*)
            eapply valid_stepN; eauto.
          }
        + pfold.
          econstructor 3. eauto.
          intros x'0 AA.
          right.
          eapply CO; try assumption.
          specialize (LE _ _ (H0 _ AA)).
          destruct LE. 2: compute in *; tauto.
          unfold paco_exp_safety.
          apply H1.
    Qed.

  End explicit_safetyN.


  Section explicit_safetyN_stutter.

  Context {core_data: Type}
          {core_ord : core_data -> core_data -> Prop}
          (core_ord_wf: well_founded core_ord).

  (** *Safety with Stutter and stepN*)
  CoInductive exp_safetyN_stutter (cd:core_data) (x:X) (y:Y): Prop:=
  | halted_safetyN_stut : halted x y -> exp_safetyN_stutter cd x y
  | internal_safetyN_stut cd' y' n: stepN x y y' (S n)  ->
                            (forall x',  valid x' y' -> exp_safetyN_stutter cd' x' y') ->
                            exp_safetyN_stutter cd x y
  | external_safetyN_stut cd' x' y': ext_step x y x' y' ->
                            (forall x',  valid x' y' -> exp_safetyN_stutter cd' x' y') ->
                            exp_safetyN_stutter cd x y
  | stutter cd': core_ord cd' cd ->
                 exp_safetyN_stutter cd' x y ->
                 exp_safetyN_stutter cd x y.

  (*Paco version*)
  Inductive exp_safetyN_stutter_gen {_exp_safety} (cd:core_data) (x:X) (y:Y): Prop:=
  | paco_halted_safetyN_stut : halted x y -> exp_safetyN_stutter_gen cd x y
  | paco_internal_safetyN_stut cd' y' n: stepN x y y' (S n)  ->
                            (forall x',  valid x' y' -> _exp_safety cd' x' y') ->
                            exp_safetyN_stutter_gen cd x y
  | paco_external_safetyN_stut cd' x' y': ext_step x y x' y' ->
                            (forall x',  valid x' y' -> _exp_safety cd' x' y') ->
                            exp_safetyN_stutter_gen cd x y
  | paco_stutter cd': core_ord cd' cd ->
                 _exp_safety cd' x y ->
                 exp_safetyN_stutter_gen cd x y.
  Definition paco_exp_safetyN_stutter := paco3 (@exp_safetyN_stutter_gen).

  (*Show that the paco representation is correct. *)
  Lemma exp_safetyN_stutter_paco_correct:
    forall cd x y, exp_safetyN_stutter cd x y <-> paco_exp_safetyN_stutter bot3 cd x y.
  Proof.
    intros cd x y; split; generalize cd x y; clear cd x y.
    - pcofix CO; intros cd x y HH.
      pfold. inversion HH;
        [ econstructor 1; eauto |
            econstructor 2; eauto |
            econstructor 3; eauto |
            econstructor 4; eauto ]; intros x'' VAL'.
    - cofix CO; intros cd x y HH.
      inversion HH. inversion SIM;
        [ econstructor 1; eauto |
          econstructor 2; eauto |
          econstructor 3; eauto |
          econstructor 4; eauto ].
      + intros x'' VAL'; eapply CO.
        specialize (LE _ _ _ (H0 _ VAL')).
        destruct LE. 2: compute in *; tauto.
        apply H1.
      + intros x'' VAL'; eapply CO.
        specialize (LE _ _ _ (H0 _ VAL')).
          destruct LE. 2: compute in *; tauto.
          apply H1.
      + eapply CO .
        specialize (LE _ _ _ (H0)).
        destruct LE. 2: compute in *; tauto.
        apply H1.
  Qed.

  (*The stutter doesn't matter*)
  Lemma speach_therapy:
    forall cd x y,
      paco_exp_safetyN bot2 x y <->
      paco_exp_safetyN_stutter bot3 cd x y.
  Proof.
    intros cd x y.
    split; generalize cd x y; clear cd x y.
    - pcofix CO.
      intros cd x y HH; inversion HH; subst; clear HH.
      pfold.
      inversion SIM;
        [ econstructor 1; eauto |
          econstructor 2; eauto |
          econstructor 3; eauto ]; intros x0 VAL'.
      + specialize (LE _ _ (H0 _ VAL')).
        destruct LE; [| compute in *; tauto].
        unfold upaco3. right. apply CO. eapply H1.

      + specialize (LE _ _ (H0 _ VAL')).
        destruct LE; [| compute in *; tauto].
        unfold upaco3. right. apply CO. eapply H1.
    - pcofix CO.
      intros cd x y HH; pfold.
      generalize cd x y HH; clear HH y x cd.
      (*set up the well formed induction*)
      apply (@well_founded_ind _ core_ord core_ord_wf
                               (fun cd => forall (x : X) (y : Y),
                                      paco_exp_safetyN_stutter bot3 cd x y ->
                                      exp_safetyN_gen x y)); auto.

      (*now do teh cofixpoint induction*)

      intros x wf_ind x' y HH; inversion HH; subst; clear HH.
      inversion SIM; clear SIM;
        [ econstructor 1; eauto |
          econstructor 2; eauto |
          econstructor 3; eauto |].
      + intros x0 VAL'. specialize (LE _ _ _ (H0 _ VAL')).
        destruct LE; [| compute in *; tauto].
        unfold upaco3. right. eapply CO. eapply H1.
      + intros x0 VAL'. specialize (LE _ _ _ (H0 _ VAL')).
        destruct LE; [| compute in *; tauto].
        unfold upaco3. right. eapply CO. eapply H1.
      + eapply wf_ind in H; [ exact H|].
        pfold. specialize (LE _ _ _ (H0)).
        destruct LE; [| compute in *; tauto].
        simpl. punfold H1.
        {
          clear.
          unfold monotone3.
          intros.
          inversion IN;
        [ econstructor 1; eauto |
          econstructor 2; eauto |
          econstructor 3; eauto |
          econstructor 4; eauto ]. }
        Grab Existential Variables.
        assumption.
        assumption.
  Qed.
  End explicit_safetyN_stutter.

  Section The_Equivalence.

  Context (core_data: Type)
          (core_ord : core_data -> core_data -> Prop)
          (core_ord_wf: well_founded core_ord)
          (default: core_data).

  Theorem safety_stutter_stepN_equiv:
    forall x y,
      valid x y ->
      exp_safety x y <-> exists cd, @exp_safetyN_stutter _ core_ord cd x y.
  Proof.
    intros x y VAL; split; intros HH.
    - exists default.
      apply exp_safetyN_stutter_paco_correct.
      apply speach_therapy; [assumption|].
      apply safetyN_equivalence; [assumption|].
      apply exp_safety_paco_correct; assumption.
    - destruct HH as [cd HH].
      apply exp_safety_paco_correct.
      apply safetyN_equivalence; [assumption|].
      eapply speach_therapy with (cd0:=cd); [eassumption|].
      apply exp_safetyN_stutter_paco_correct; assumption.
  Qed.

  End The_Equivalence.

End safety_equivalence.
