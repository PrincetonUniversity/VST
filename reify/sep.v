Require Import MirrorShard.SepExpr.
Require Import floyd.proofauto.

Local Open Scope logic.

Module VericSepLogic_Kernel <: SepTheory.SepTheory_Kernel.

Definition hprop := mpred.
Definition himp := derives.
Definition heq := fun p1 p2 => derives p1 p2 /\ derives p2 p1.
Definition Refl_himp := derives_refl.
Definition Trans_himp := derives_trans.

Definition emp := emp.

Definition inj := fun p => (prop p && emp).

Definition star := sepcon.

Definition ex := @exp mpred Nveric. 

Local Notation "a ===> b" := (himp a b) (at level 60).

Ltac sep_solve :=
  unfold star, himp, heq, emp, inj, ex in *; intuition; cancel; auto.


Lemma himp_star_comm : forall P Q, 
    (star P Q) ===> (star Q P).
Proof.
sep_solve.
Qed.

Lemma himp_star_assoc : forall P Q R, 
    (star (star P Q) R) ===> (star P (star Q R)).
Proof.
sep_solve.
Qed.

Lemma himp_star_emp_p : forall P, (star emp P) ===> P.
Proof.
sep_solve.
Qed.

Lemma himp_star_emp_c : forall P, P ===> (star emp P).
Proof.
sep_solve.
Qed. 

Lemma himp_star_frame : forall P Q R S, 
  P ===> Q -> R ===> S -> (star P R) ===> (star Q S).
Proof.
sep_solve.
Qed.

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

  Lemma himp_ex_p : forall T (P : T -> _) Q, 
            (forall v, (P v) ===> Q) -> (ex T P) ===> Q.
  Proof. sep_solve. apply exp_left. auto.
Qed.

  Lemma himp_ex_c : forall T (P : T -> _) Q, 
    (exists v, Q ===> (P v)) -> Q ===> (ex T P).
  Proof. 
 sep_solve. destruct H. eapply exp_right.  apply H.
Qed.

  Lemma himp_ex_star : forall T (P : T -> _) Q,
    (star (ex T P) Q) ===> (ex T (fun x => star (P x) Q)).
Proof.
sep_solve. entailer!.
Qed.

Lemma himp_star_ex : forall T (P : T -> _) Q,
     (ex T (fun x => star (P x) Q)) ===> (star (ex T P) Q).
Proof.
sep_solve.
entailer!.
apply (exp_right x).
cancel.
Qed. 

End VericSepLogic_Kernel.

Module VericSepLogic := SepTheory.SepTheory_From_Kernel VericSepLogic_Kernel.

Module Sep := SepExpr.Make VericSepLogic.
