Require Import VST.msl.base.
Require Import VST.msl.sepalg.
Require Import VST.msl.predicates_sa.

Definition covariant {B A : Type} (F: (B -> pred A) -> (B -> pred A)) : Prop :=
forall (P Q: B -> pred A), (forall x, P x |-- Q x) -> (forall x, F P x |-- F Q x).

Definition corec {B A: Type}  (F: (B -> pred A) -> (B -> pred A)) : B -> pred A :=
fun x w => forall P: B -> pred A, (forall x, F P x |-- P x) -> P x w.

Lemma corec_fold_unfold {B A}:
forall {F: (B -> pred A) -> (B -> pred A)},
       covariant F ->
        corec F = F (corec F).
Proof.
intros.
assert (forall x, F (corec F) x |-- corec F x).
2:{
extensionality x.
apply pred_ext; intros w ?.
apply H1. intros x' ? ?.
eapply H.  eapply H0.
replace (F (corec F)) with (fun (x : B) (w : A) => F (corec F) x w); auto.
apply H0; auto.
}
intros x ? ?.
intros ? ?.
specialize (H (corec F) P).
apply H1. apply H; auto.
intros x' ? ?.
apply H2; auto.
Qed.

Lemma corec_least_fixpoint {B A}:
forall {F: (B -> pred A) -> (B -> pred A)}, forall {P : B -> pred A},
  P = F P ->
  forall b, corec F b |-- P b.
Proof.
  intros. do 2 intro.
  apply H0 with (P := P). intros b' ? ?.
  rewrite H. apply H1.
Qed.

Lemma covariant_sepcon {B}{A} {JA: Join A}{PA: Perm_alg A}:
   forall P Q : (B -> pred A) -> (B -> pred A),
    covariant P -> covariant Q ->
    covariant (fun (x : B -> pred A) b => P x b * Q x b)%pred.
Proof.
intros. intros R S ? ?.
eapply sepcon_derives; auto.
Qed.

Lemma covariant_const {B A}:    forall P : B -> pred A, covariant (fun _ => P).
Proof.
intros. intros R S ?. auto.
Qed.

Lemma covariant_orp {B A}:  forall P Q: (B -> pred A)-> (B -> pred A),
      covariant P -> covariant Q -> covariant (fun x b => P x b || Q x b)%pred.
Proof.
intros. intros R S ? ?.
intros w [H2|H2]; [left; eapply H | right; eapply H0]; try apply H1; eauto.
Qed.

Lemma covariant_andp {B A}:  forall P Q: (B -> pred A) -> (B -> pred A),
      covariant P -> covariant Q -> covariant (fun x b => P x b && Q x b)%pred.
Proof.
intros. intros R S ? ?.
apply andp_derives; auto.
Qed.

Lemma covariant_exp {C B A}: forall F: C -> (B -> pred A) -> (B -> pred A),
  (forall c, covariant (F c)) ->
   covariant (fun P b => EX c:C, F c P b)%pred.
Proof.
intros.
repeat intro.
destruct H1 as [b ?].
exists b. specialize (H b).
unfold covariant in H.
apply (H P Q H0). auto.
Qed.


Lemma covariant_id {B A}: covariant (fun F: B -> pred A => F).
Proof.
unfold covariant; auto.
Qed.

Lemma covariant_const' {B A}:
  forall c:B,  covariant (fun (P: B -> pred A) _ => P c).
Proof.
repeat intro.
apply H; auto.
Qed.









