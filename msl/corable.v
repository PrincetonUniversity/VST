Require Import VST.msl.base.
Require Import VST.msl.ageable.
Require Import VST.msl.sepalg.
Require Import VST.msl.sepalg_generators.
Require Import VST.msl.age_sepalg.
Require Import VST.msl.predicates_hered.
Require Import VST.msl.predicates_sl.

Local Open Scope pred.

(*Definition corable {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}
         (P: pred A) := forall w, P w = P (core w).

Lemma corable_spec: forall {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}
  (P: pred A),
    corable P = forall x y:A, core x = core y -> P x -> P y.
Proof.
  unfold corable; intros; apply prop_ext; split; intros.
  + rewrite H in H1 |- *.
    rewrite <- H0.
    auto.
  + pose proof core_idem w.
    pose proof (H _ _ H0).
    pose proof (H _ _ (eq_sym H0)).
    apply prop_ext; split; auto.
Qed.*)

(* from Iris: "persistent and absorbing" *)
Definition corable {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}
         (P: pred A) := forall w, P w -> forall w', (join_sub w w' \/ join_sub w' w \/ ext_order w' w) -> P w'.

Lemma corable_core : forall {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A} P w1 w2, corable P ->
  core w1 = core w2 -> P w1 -> P w2.
Proof.
  intros.
  eapply H; [eapply H; [eassumption|]|].
  - right; left; eexists; apply core_unit.
  - left; rewrite H0; eexists; apply core_unit.
Qed.

Lemma corable_andp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}:
  forall P Q, corable P -> corable Q -> corable (P && Q).
Proof.
 unfold corable; intros; simpl.
 destruct H1; eauto.
Qed.
Lemma corable_orp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}:
  forall P Q, corable P -> corable Q -> corable (P || Q).
Proof.
 unfold corable; intros; simpl.
 destruct H1; eauto.
Qed.
Lemma corable_allp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}:
  forall {B: Type} (P:  B -> pred A) ,
      (forall b, corable (P b)) -> corable (allp P).
Proof.
 unfold corable; simpl; intros.
 eauto.
Qed.
Lemma corable_exp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}:
  forall {B: Type} (P:  B -> pred A) ,
      (forall b, corable (P b)) -> corable (exp P).
Proof.
 unfold corable; intros; simpl.
 destruct H0; eauto.
Qed.
Lemma corable_prop {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}:
  forall P, corable (prop P).
Proof.
 unfold corable, prop; intros.
 simpl in *; auto.
Qed.

Lemma ext_later_compat {A}{agA: ageable A}{EO: Ext_ord A}: forall a b a', ext_order a b -> laterR a a' -> exists b', laterR b b' /\ ext_order a' b'.
Proof.
  intros.
  revert dependent b; induction H0; intros.
  - eapply ext_age_compat in H as (? & ? & ?); eauto.
    do 2 eexists; [|eauto].
    apply t_step; auto.
  - apply IHclos_trans1 in H as (? & ? & Hext).
    apply IHclos_trans2 in Hext as (? & ? & Hext).
    do 2 eexists; [eapply t_trans|]; eauto.
Qed.

Lemma ext_nec_compat {A}{agA: ageable A}{EO: Ext_ord A}: forall a b a', ext_order a b -> necR a a' -> exists b', necR b b' /\ ext_order a' b'.
Proof.
  intros.
  apply nec_refl_or_later in H0 as [|]; subst; eauto.
  eapply ext_later_compat in H as (? & ? & ?); eauto.
  do 2 eexists; [apply laterR_necR|]; eauto.
Qed.

Lemma corable_imp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A} {agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}:
  forall P Q, corable P -> corable Q -> corable (P --> Q).
Proof.
  unfold corable; simpl; intros.
  destruct H2 as [[? J] | [[? J] | E]].
  - eapply nec_join2 in J as (? & ? & ? & Hw & ?); eauto.
    eapply ext_join_commut in H2 as (? & ? & ?); eauto.
    eapply H1 in H2; eauto.
  - eapply nec_join in J as (? & ? & ? & ? & Hw); eauto.
    eapply H1 in Hw; [| eauto | eauto].
    + eapply pred_upclosed, H0; eauto.
    + apply H with a'; eauto.
  - eapply ext_nec_compat in E as (? & Hnec & ?); eauto.
    eapply H1 in Hnec; try reflexivity.
    + eapply pred_upclosed, H0; eauto.
    + eapply pred_upclosed, H; eauto.
Qed.

Lemma corable_sepcon {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}:
  forall P Q, corable P -> corable Q -> corable (P * Q).
Proof.
  unfold corable; simpl; intros.
  destruct H1 as (? & ? & J & HP & HQ).
  destruct H2 as [[? J'] | [[? J'] | E]].
  - destruct (join_assoc J J') as (? & ? & ?).
    do 3 eexists; eauto.
  - do 3 eexists; [apply core_unit|].
    split.
    + eapply H; [eapply H; [eassumption|]|].
      * left; eexists; apply J.
      * right; left; eapply join_sub_trans; [|eexists; eauto].
        eexists; apply core_unit.
    + eapply H0; [eapply H0; [eassumption|]|].
      * left; eexists; apply join_comm, J.
      * eauto.
  - do 3 eexists; [apply core_unit|].
    split.
    + eapply H in HP; [|left; eexists; eauto].
      eapply H in HP; [|right; right; eauto].
      eapply H; eauto.
      right; left; eexists; apply core_unit.
    + eapply H0 in HQ; [|left; eexists; eauto]; eauto.
Qed.

Lemma corable_wand: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} {EO: Ext_ord A}{EA: Ext_alg A} (P Q: pred A), corable P -> corable Q -> corable (P -* Q).
Proof.
  unfold corable; simpl; intros.
  destruct H2 as [[? J] | [[? J] | E]].
  - eapply nec_join2 in J as (? & ? & J' & Hw & ?); eauto.
    eapply H1 in Hw; try apply J'; eauto.
    eapply H; [eapply H; [eapply H; [eassumption|]|]|].
    + left; eexists; apply join_comm; eassumption.
    + right; left; eexists; eauto.
    + eauto.
  - eapply nec_join in J as (? & ? & J' & ? & Hw); eauto.
    eapply H1 in Hw; try apply join_comm, core_unit.
    + eapply H0; [eapply H0; [eassumption|]|].
      * right; left; eexists; eauto.
      * left; eexists; eauto.
    + eapply H; [eapply H; [eapply H; [eapply H; [eassumption|]|]|]|].
      * left; eexists; eauto.
      * right; left; eexists; eauto.
      * left; eexists; eauto.
      * right; left; eexists; apply core_unit.
  - eapply ext_nec_compat in E as (? & Hnec & ?); eauto.
    eapply H1 in Hnec; [| apply join_comm, core_unit |].
    + eapply H0; [eapply H0; eauto|]; eauto.
    + eapply H; [|right; left; eexists; apply core_unit].
      eapply pred_upclosed; eauto.
      eapply H; [|right; left; eexists; eauto]; eauto.
Qed.

Lemma corable_later: forall {A:Type} {agA:ageable A} {JA: Join A} {PA: Perm_alg A} {SaA: Sep_alg A} {XA: Age_alg A} {EO: Ext_ord A}{EA: Ext_alg A} P, corable P -> corable (|> P).
Proof.
  unfold corable; simpl; intros.
  destruct H1 as [[? J] | [[? J] | E]].
  - eapply later_join2 in J as (? & ? & ? & ? & ?); eauto.
  - eapply later_join in J as (? & ? & ? & ? & ?); eauto.
    eapply H; eauto.
  - eapply ext_later_compat in E as (? & ? & ?); eauto.
Qed.

#[export] Hint Resolve corable_andp corable_orp corable_allp corable_exp
                    (*corable_imp*) corable_prop corable_sepcon corable_wand corable_later : core.

Lemma corable_andp_sepcon1{A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}:
   forall P Q R, corable P ->  (P && Q) * R = P && (Q * R).
Proof.
intros.
apply pred_ext.
intros w [w1 [w2 [? [[? ?] ?]]]].
split; [eapply H; eauto|].
exists w1, w2; auto.
intros w [? [w1 [w2 [? [? ?]]]]].
exists w1; exists w2; split; [|split]; auto.
split; eauto.
Qed.

(* The following 3 lemmas should not be necessary *)
Lemma corable_andp_sepcon2{A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}:
   forall P Q R, corable P ->  (Q && P) * R = P && (Q * R).
Proof.
intros. rewrite andp_comm. apply corable_andp_sepcon1. auto.
Qed.

Lemma corable_sepcon_andp1 {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}:
   forall P Q R, corable P ->  Q  * (P && R) = P && (Q * R).
Proof.
intros. rewrite sepcon_comm. rewrite corable_andp_sepcon1; auto. rewrite sepcon_comm; auto.
Qed.

Lemma corable_sepcon_andp2 {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}{EO: Ext_ord A}{EA: Ext_alg A}:
   forall P Q R, corable P ->  Q  * (R && P) = P && (Q * R).
Proof.
intros. rewrite sepcon_comm. rewrite andp_comm. rewrite corable_andp_sepcon1; auto. rewrite sepcon_comm; auto.
Qed.

(* This hint doesn't work well, hence the extra clauses in normalize1 and normalize1_in *)
#[export] Hint Rewrite @corable_andp_sepcon1 @corable_andp_sepcon2
                    @corable_sepcon_andp1 @corable_sepcon_andp2 using solve [auto with normalize typeclass_instances] : core.