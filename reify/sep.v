Require Import MirrorShard.SepExpr.
Require Import floyd.proofauto.

Local Open Scope logic.

Module VericSepLogic <: SepTheory.SepTheory.

Definition hprop := mpred.
Definition himp := derives.
Definition heq := fun p1 p2 => derives p1 p2 /\ derives p2 p1.
Definition Refl_himp := derives_refl.
Definition Trans_himp := derives_trans.

Lemma Refl_heq : Reflexive heq.
Proof. 
intros. 
unfold heq; split; apply derives_refl; auto.
Qed.

Lemma Sym_heq : Symmetric heq.
Proof.
unfold heq, Symmetric. intros. intuition.
Qed.

Lemma Trans_heq : Transitive heq.
Proof.
unfold heq, Transitive; intros.
intuition; eapply derives_trans; eauto.
Qed.

Local Notation "a ===> b" := (himp a b) (at level 60).
Local Notation "a <===> b" := (heq a b) (at level 60).


Lemma heq_defn : forall a b, (a ===> b /\ b ===> a) <-> a <===> b.
Proof.
intros. unfold heq, himp; intuition.
Qed.

Lemma heq_himp : forall a b, a <===> b -> a ===> b.
Proof. intros.
unfold heq, himp in *; intuition.
Qed.

Definition emp := emp.


Definition inj := fun p => (prop p && emp).

Definition star := sepcon.

Definition ex := @exp mpred Nveric. 

Lemma himp_star_comm : forall P Q, 
    (star P Q) ===> (star Q P).
Proof.
intros. unfold star, himp. cancel. 
Qed.

Lemma heq_star_comm : forall P Q, 
    (star P Q) <===> (star Q P).
Proof.
intros. split; unfold star; cancel.
Qed.

Lemma heq_star_assoc : forall P Q R, 
  (star (star P Q) R) <===> (star P (star Q R)).
Proof.
split; unfold star; cancel.
Qed.

Lemma heq_star_emp_l : forall P, (star emp P) <===> P.
Proof.
split; unfold star; cancel.
Qed.

Lemma heq_star_emp_r : forall P, (star P emp) <===> P.
Proof.
split; unfold star; cancel.
Qed.

Lemma himp_star_frame : forall P Q R S, 
  P ===> Q -> R ===> S -> (star P R) ===> (star Q S).
Proof.
intros. unfold star. unfold himp in *. apply sepcon_derives; auto.
Qed.

Ltac sep_solve :=
  unfold star, himp, heq, emp, inj, ex in *; intuition; cancel; auto.

Lemma heq_star_frame : forall P Q R S, 
  P <===> Q -> R <===> S -> (star P R) <===> (star Q S).
Proof.
intros; sep_solve.
Qed.

Lemma himp_subst_p : forall P Q R S,
  P ===> S -> (star S Q) ===> R ->
  (star P Q) ===> R.
Proof.
sep_solve.
eapply derives_trans in H0. apply H0. cancel.
Qed.

Lemma himp_subst_c : forall P Q R S,
  S ===> Q -> P ===> (star S R) ->
  P ===> (star Q R).
Proof.
sep_solve.
eapply derives_trans; eauto; cancel.
Qed.

Lemma heq_subst : forall P Q R S,
  P <===> S -> (star S Q) <===> R ->
  (star P Q) <===> R.
Proof.
sep_solve.
eapply derives_trans in H; eauto; cancel.
eapply derives_trans; eauto; cancel.
Qed.

Lemma himp_star_cancel : forall P Q R,
  Q ===> R -> (star P Q) ===> (star P R).
Proof.
sep_solve.
Qed.

Lemma heq_star_cancel : forall P Q R, 
  Q <===> R -> (star P Q) <===> (star P R).
Proof.
sep_solve.
Qed.


(** pure lemmas **)
Lemma himp_star_pure_p : forall P Q F,
  (star (inj F) P) ===> Q -> (F -> P ===> Q).
Proof.
sep_solve.
eapply derives_trans in H; eauto; entailer!.
Qed.

Lemma himp_star_pure_c : forall P Q (F : Prop),
  (F -> P ===> Q) -> (star (inj F) P) ===> Q.
Proof.
intros.
sep_solve. entailer!.
Qed.

  Lemma himp_star_pure_cc : forall P Q (p : Prop),
    p ->
    P ===> Q ->
    P ===> (star (inj p) Q).
Proof.
sep_solve. entailer!.
Qed.

  (** ex lemmas **)
  Lemma himp_ex_p : forall T (P : T -> _) Q, 
            (forall v, (P v) ===> Q) -> (ex T P) ===> Q.
  Proof. sep_solve. apply exp_left. auto.
Qed.

  Lemma himp_ex_c : forall T (P : T -> _) Q, 
    (exists v, Q ===> (P v)) -> Q ===> (ex T P).
  Proof. 
 sep_solve. destruct H. eapply exp_right.  apply H.
Qed.

  Lemma heq_ex : forall T (P Q : T -> _), 
    (forall v, P v <===> Q v) ->
    ex T P <===> ex T Q.
Proof. 
sep_solve; apply exp_left;  intros;
specialize (H x); destruct H; apply (exp_right x);
auto.
Qed.

  Lemma himp_ex : forall T (P Q : T -> _), 
    (forall v, P v ===> Q v) ->
    ex T P ===> ex T Q.
Proof.
sep_solve. apply exp_left. intros.
specialize (H x). apply (exp_right x). auto.
Qed.

  Lemma heq_ex_star : forall T (P : T -> _) Q,
    (star (ex T P) Q) <===> (ex T (fun x => star (P x) Q)).
Proof.
sep_solve. entailer!.
entailer!. apply (exp_right x). auto.
Qed.

  Lemma himp_ex_star : forall T (P : T -> _) Q,
    (star (ex T P) Q) ===> (ex T (fun x => star (P x) Q)).
Proof.
sep_solve. entailer!.
Qed.

End VericSepLogic.

Module Sep := SepExpr.Make VericSepLogic.
