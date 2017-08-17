Require Import VST.msl.msl_standard.

Local Open Scope pred.

Lemma andp_TT {A}`{ageable A}: forall (P: pred A), P && TT = P.
Proof.
intros.
apply pred_ext; intros w ?.
destruct H0; auto.
split; auto.
Qed.

Lemma sepcon_andp_prop' {A}  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}: forall P Q R, (!!Q && P)*R = !!Q&&(P*R).
Proof.
intros.
rewrite sepcon_comm. rewrite sepcon_andp_prop.
rewrite sepcon_comm; auto.
Qed.

Hint Rewrite @sepcon_emp @emp_sepcon @TT_and @andp_TT
             @exp_sepcon1 @exp_sepcon2
               @exp_andp1 @exp_andp2
         @sepcon_andp_prop @sepcon_andp_prop'
        : normalize.

Definition pure {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}
     (P: pred A) : Prop :=
   P |-- emp.

Lemma pure_sepcon {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}: forall (P : pred A), pure P -> P*P=P.
Proof.
pose proof I.
intros.
apply pred_ext; intros w ?.
assert ((emp * P)%pred w).
eapply sepcon_derives; try apply H1; auto.
rewrite emp_sepcon in H2.
auto.
exists w; exists w.
split; [|split]; auto.
apply H0 in H1.
do 3 red in H1. apply identity_unit' in H1.
apply H1.
Qed.

Lemma pure_e {A}{JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}: forall (P: pred A), pure P -> (P |-- emp).
Proof.
intros.
apply H.
Qed.

Hint Resolve @pure_e.

Lemma sepcon_pure_andp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
 forall P Q, pure P -> pure Q -> ((P * Q) = (P && Q)).
Proof.
intros.
apply pred_ext; intros w ?.
destruct H1 as [w1 [w2 [? [? ?]]]].
unfold pure in *.
assert (unit_for w1 w2). apply H in H2; simpl in H2;
apply identity_unit; auto. exists w; auto.
unfold unit_for in H4.
assert (w2=w) by (apply (join_eq H4 H1)).
subst w2.
assert (join w w1 w1).
apply identity_unit; apply H0 in H3; simpl in H3; auto. exists w; auto.
assert (w1=w) by (apply (join_eq H5 (join_comm H1))).
subst w1.
split; auto.
destruct H1.
exists w; exists w; split; [|split]; auto.
apply H in H1.
do 3 red in H1.
clear dependent P. clear dependent Q.
pose proof (core_unit w); unfold unit_for in *.
pose proof (H1 _ _ (join_comm H)).
rewrite H0 in H; auto.
Qed.

Lemma pure_emp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}: pure emp.
Proof.
intros. unfold pure; auto.
Qed.
Hint Resolve @pure_emp.

Lemma join_equiv_refl {A}: forall x:A, @join A (Join_equiv A) x x x.
Proof. split; auto. Qed.
Hint Resolve @join_equiv_refl.

Lemma pure_sepcon1'' {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}: forall P Q R, pure P -> Q |-- R -> P * Q |-- R.
Proof.
pose proof I.
intros.
intros w [w1 [w2 [? [? ?]]]].
apply H0 in H3.
apply join_unit1_e in H2; auto.
subst; auto.
Qed.


Lemma pure_existential {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
   forall B (P: B -> pred A),    (forall x: B , pure (P x)) -> pure (exp P).
Proof.
intros.
unfold pure in *.
intros w [x ?].
apply (H x); auto.
Qed.

Hint Resolve @pure_existential.

Lemma pure_core {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall P w, pure P -> P w -> P (core w).
Proof.
intros.
rewrite <- identity_core; auto.
apply H; auto.
Qed.

Lemma FF_sepcon {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
           forall P, FF * P = FF.
Proof.
intros.
apply pred_ext; intros w ?; try contradiction.
destruct H as [w1 [w2 [? [? ?]]]]; contradiction.
Qed.
Lemma sepcon_FF {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
            forall P, P * FF = FF.
Proof.
intros.
rewrite sepcon_comm. apply FF_sepcon.
Qed.
Hint Rewrite @FF_sepcon @sepcon_FF : normalize.

Hint Rewrite @prop_true_andp using (solve [auto]) : normalize.

Lemma true_eq {A} `{ageable A}:  forall P: Prop, P -> (!! P) = (TT: pred A).
Proof.
intros. apply pred_ext; intros ? ?; simpl in *; intuition.
Qed.
Hint Rewrite @true_eq using (solve [auto]) : normalize.


Lemma pure_con' {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
      forall P Q, pure P -> pure Q -> pure (P*Q).
Proof.
intros.
unfold pure in *.
rewrite <- sepcon_emp.
apply sepcon_derives; auto.
Qed.
Hint Resolve @pure_con'.

Lemma pure_intersection1: forall {A}  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}
       (P Q: pred A), pure P -> pure (P && Q).
Proof.
unfold pure; intros; auto.
intros w [? ?]; auto.
Qed.
Lemma pure_intersection2: forall {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}
     (P Q: pred A), pure Q -> pure (P && Q).
Proof.
unfold pure; intros; auto.
intros w [? ?]; auto.
Qed.
Hint Resolve @pure_intersection1 @pure_intersection2.

Lemma FF_andp {A} `{ageable A}:  forall P: pred A, FF && P = FF.
Proof.
unfold FF, prop, andp; intros; apply pred_ext; intros ? ?; simpl in *; intuition.
Qed.
Lemma andp_FF {A}`{ageable A}:  forall P: pred A, P && FF = FF.
Proof.
unfold FF, prop, andp; intros; apply pred_ext; intros ? ?; simpl in *; intuition.
Qed.
Hint Rewrite @FF_andp @andp_FF : normalize.

Hint Rewrite @andp_dup : normalize.

Lemma andp_emp_sepcon_TT {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
 forall (Q: pred A),
     (forall w1 w2, core w1 = core w2 -> Q w1 -> Q w2) ->
      (Q && emp * TT = Q).
Proof.
intros.
apply pred_ext.
intros w [w1 [w2 [? [[? ?] ?]]]].
apply H with w1; auto.
apply join_core in H0; auto.
intros w ?.
destruct (join_ex_identities w) as [e [He [? Hj]]].
exists e; exists w; split; [|split]; auto.
specialize (He _ _ Hj); subst; auto.
split; auto.
apply H with w; auto.
symmetry; eapply join_core2; eauto.
Qed.

Lemma sepcon_TT {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
   forall (P: pred A), P |-- (P * TT).
Proof.
intros.
rewrite <- (sepcon_emp P) at 1.
eapply sepcon_derives; try apply H0; auto.
Qed.
Hint Resolve @sepcon_TT.

Lemma imp_extract_exp_left {B A: Type} `{ageable A}:
    forall    (p : B -> pred A) (q: pred A),
  (forall x, p x |-- q) ->
   exp p |-- q.
Proof.
intros.
intros w [x ?].
eapply H0; eauto.
Qed.

Lemma pure_sepcon_TT_andp {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall P Q, pure P -> (P * TT) && Q = (P*Q).
Proof.
 pose proof I.
intros.
apply pred_ext.
intros w [? ?].
destruct H1 as [w1 [w2 [? [? ?]]]].
exists w1; exists w2; split; [|split]; auto.
apply join_unit1_e in H1; auto.
subst; auto.
apply H0 in H3; auto.
apply andp_right.
apply sepcon_derives; auto.
intros w [w1 [w2 [? [? ?]]]].
apply join_unit1_e in H1; auto.
subst; auto.
apply H0 in H2; auto.
Qed.

Lemma pure_sepcon_TT_andp' {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall P Q, pure P -> Q && (P * TT) = (Q*P).
Proof.
intros. rewrite andp_comm.
rewrite pure_sepcon_TT_andp; auto.
apply sepcon_comm.
Qed.

Hint Rewrite @pure_sepcon_TT_andp @pure_sepcon_TT_andp' using (solve [auto]): normalize.

Lemma pure_sepcon1' {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:

  forall P Q R, pure P -> P * Q |-- P * R -> P * Q |-- R.
Proof.
intros.
eapply derives_trans; try apply H0.
apply pure_sepcon1''; auto.
Qed.

Lemma pull_right {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
 forall P Q R,
   (Q * P * R) = (Q * R * P).
Proof.
intros. repeat rewrite sepcon_assoc. rewrite (sepcon_comm P); auto.
Qed.

Lemma pull_right0 {A}  {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}: forall P Q,
   (P * Q) = (Q * P).
Proof.
intros. rewrite (sepcon_comm P); auto.
Qed.

Ltac pull_left A := repeat (rewrite <- (pull_right A) || rewrite <- (pull_right0 A)).

Ltac pull_right A := repeat (rewrite (pull_right A) || rewrite (pull_right0 A)).

Lemma pure_modus {A} {JA: Join A}{PA: Perm_alg A}{SA: Sep_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall P Q,  P |-- Q -> pure Q -> P |-- Q && P.
Proof.
intros.
intros w ?.
split; auto.
Qed.


Lemma imp_exp_right {B A : Type} `{saA: ageable A}:
  forall (x: B) (p: pred A) (q: B -> pred A),
    p |-- q x ->
    p |-- exp q.
Proof.
intros.
eapply derives_trans; try apply H.
intros w ?; exists x; auto.
Qed.

Lemma derives_extract_prop {A} `{ageable A}:
  forall (P: Prop) (Q R: pred A), (P -> Q |-- R) ->  !!P && Q |-- R.
Proof.
unfold derives, prop, andp; hnf in *; intuition.
hnf in H1; intuition.
Qed.

Lemma derives_extract_prop' {A} `{ageable A}:
  forall (P: Prop) (Q R: pred A), (P -> Q |-- R) ->  Q && !!P|-- R.
Proof.
unfold derives, prop, andp; intuition; hnf in *; intuition.
hnf in *; intuition. apply H1; auto.
Qed.

Ltac normalize1 :=
             match goal with
                | |- _ => contradiction
                | |- context [(?P && ?Q) * ?R] => rewrite (corable_andp_sepcon1 P Q R) by (auto with normalize)
                | |- context [?Q * (?P && ?R)] => rewrite (corable_sepcon_andp1 P Q R) by (auto with normalize)
                | |- context [(?Q && ?P) * ?R] => rewrite (corable_andp_sepcon2 P Q R) by (auto with normalize)
                | |- context [?Q * (?R && ?P)] => rewrite (corable_sepcon_andp2 P Q R) by (auto with normalize)
                | |- _ => progress  (autorewrite with normalize); auto with typeclass_instances
                | |- _ = ?x -> _ => intro; subst x
                | |- ?x = _ -> _ => intro; subst x
                |  |- ?ZZ -> _ => match type of ZZ with
                                               | Prop =>
                                                    let H := fresh in
                                                       ((assert (H:ZZ) by auto; clear H; intros _) || intro H)
                                               | _ => intros _
                                              end
                | |- forall _, _ => let x := fresh "x" in (intro x; normalize1; try generalize dependent x)
                | |- exp _ |-- _ => apply imp_extract_exp_left
                | |- !! _ && _ |-- _ => apply derives_extract_prop
                | |- _ && !! _ |-- _ => apply derives_extract_prop'
                | |- _ |-- !! (?x = ?y) && _ =>
                            (rewrite prop_true_andp with (P:= (x=y))
                                            by (unfold y; reflexivity); unfold y in *; clear y) ||
                            (rewrite prop_true_andp with (P:=(x=y))
                                            by (unfold x; reflexivity); unfold x in *; clear x)
                | |- _ => solve [auto with typeclass_instances]
                end.

Ltac normalize1_in Hx :=
             match type of Hx with
                | app_pred (exp _) _ => destruct Hx
                | app_pred (!! _ && _) _ => let H1 := fresh in destruct Hx as [H1 Hx]; unfold prop in H1
                | context [ !! ?P ] =>
                                    rewrite (true_eq P) in Hx by auto with typeclass_instances
                | context [ !! ?P && ?Q ] =>
                                    rewrite (prop_true_andp P Q) in Hx by auto with typeclass_instances
                | context [(?P && ?Q) * ?R] => rewrite (corable_andp_sepcon1 P Q R) in Hx by (auto with normalize)
                | context [?Q * (?P && ?R)] => rewrite (corable_sepcon_andp1 P Q R) in Hx by (auto with normalize)
                | context [(?Q && ?P) * ?R] => rewrite (corable_andp_sepcon2 P Q R) in Hx by (auto with normalize)
                | context [?Q * (?R && ?P)] => rewrite (corable_sepcon_andp2 P Q R) in Hx by (auto with normalize)
                | _ => progress  (autorewrite with normalize in Hx); auto with typeclass_instances
                end.

Ltac normalize := repeat normalize1.

Tactic Notation "normalize" "in" hyp(H) := repeat (normalize1_in H).

Definition mark {A: Type} (i: nat) (j: A) := j.

Lemma swap_mark1 {A} {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall i j Pi Pj B, (i<j)%nat -> B * mark i Pi * mark j Pj = B * mark j Pj * mark i Pi.
Proof.
intros.
repeat rewrite sepcon_assoc.
f_equal.
apply sepcon_comm.
Qed.

Lemma swap_mark0 {A} {JA: Join A}{PA: Perm_alg A}{agA: ageable A}{AgeA: Age_alg A}:
  forall i j Pi Pj,  (i<j)%nat -> mark i Pi * mark j Pj = mark j Pj * mark i Pi.
Proof.
intros.
apply sepcon_comm.
Qed.

Ltac select_left n :=
  repeat match goal with
 | |- context [(_ * mark ?i _ * mark n _)%pred] =>
      rewrite (swap_mark1 i n); [ | solve [simpl; auto]]
 | |- context [(mark ?i _ * mark n _)%pred] =>
      rewrite (swap_mark0 i n); [ | solve [simpl; auto]]
end.
Ltac select_all n := match n with
                                | O => idtac
                                | S ?n' => select_left n; select_all n'
                              end.
Ltac markem n P :=
   match P with
   | (?Y * ?Z) =>
        (match goal with H: mark _ Z = Z |- _ => idtac end
        || assert (mark n Z = Z) by auto); markem (S n) Y
   | ?Z =>  match goal with H: mark _ Z = Z |- _ => idtac end
                || assert (mark n Z = Z) by auto
  end.

Ltac prove_assoc_commut :=
 clear;
 try (match goal with |- ?F _ -> ?G _ => replace G with F; auto end);
  (repeat rewrite <- sepcon_assoc;
   match goal with |- ?P = _ => markem O P end;
   let LEFT := fresh "LEFT" in match goal with |- ?P = _ => set (LEFT := P) end;
  match goal with H: mark ?n _ = _ |- _ =>
     repeat  match goal with H: mark ?n _ = ?P |- _ => rewrite <- H; clear H end;
     select_all n;
     reflexivity
   end).

Lemma test_prove_assoc_commut {T}{JA: Join T}{PA: Perm_alg T}{agA: ageable T}{AgeA: Age_alg T} : forall A B C D E : pred T,
   D * E * A * C * B = A * B * C * D * E.
Proof.
intros.
prove_assoc_commut.
Qed.

