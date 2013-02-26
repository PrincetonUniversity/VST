Load loadpath.
Require Import veric.SeparationLogic.
Require Import Coqlib msl.Coqlib2.
Require veric.SequentialClight.
Import SequentialClight.SeqC.CSL.
Require Import Clightdefs.
Require Import progs.client_lemmas.

Local Open Scope logic.

Lemma canon1: forall P1 B  P Q R,
   do_canon (prop P1 && B) (PROPx P (LOCALx Q (SEPx R))) = do_canon B  (PROPx (P1::P) (LOCALx Q (SEPx R))).
Proof.
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
extensionality rho.
simpl.
normalize.
rewrite andp_assoc.
f_equal.
Qed.

Lemma canon2: forall Q1 B P Q R,
    do_canon (local Q1 && B) (PROPx P (LOCALx Q (SEPx R))) = do_canon B (PROPx (P) (LOCALx (Q1::Q) (SEPx R))).
Proof.
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
extensionality rho.
simpl.
normalize.
rewrite andp_assoc.
f_equal.
Qed.

Definition nonlocal (Q: environ->mpred) := True.

Ltac check_nonlocal :=
  match goal with
  |  |- nonlocal (local _) => fail 1 
  |  |- nonlocal (prop _) => fail 1 
  |  |- nonlocal (andp _ _) => fail 1
  |  |- nonlocal (sepcon _ _) => fail 1
  | |- _ => apply I
 end.

Lemma canon3: forall R1 B P Q R,
    nonlocal R1 ->
    do_canon (B * R1) (PROPx P (LOCALx Q (SEPx R))) = do_canon B (PROPx (P) (LOCALx Q (SEPx (R1::R)))).
Proof.
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
clear H.
extensionality rho.
simpl.
rewrite sepcon_assoc.
f_equal.
rewrite sepcon_andp_prop.
f_equal.
normalize.
Qed.

Lemma canon3b: forall R1 B P Q R,
    nonlocal R1 ->
    do_canon (R1* B) (PROPx P (LOCALx Q (SEPx R))) = do_canon B (PROPx (P) (LOCALx Q (SEPx (R1::R)))).
Proof.
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
rewrite (sepcon_comm R1 B).
apply canon3. auto.
Qed.

Lemma canon4: forall P, do_canon emp P = P. 
Proof.
apply emp_sepcon.
Qed.

Lemma canon7: forall R1 P Q R, 
   nonlocal R1 -> 
   do_canon R1 (PROPx P (LOCALx Q (SEPx R))) = (PROPx P (LOCALx Q (SEPx (R1::R)))).
Proof.
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
extensionality rho.
simpl.
normalize.
Qed.
 
Lemma canon8: forall R1 R2 R3 PQR,
    do_canon ((R1 && R2) && R3) PQR = do_canon (R1 && (R2 && R3)) PQR.
Proof. intros; rewrite andp_assoc; auto. 
Qed.

Lemma start_canon: forall P, P  = do_canon P (PROPx nil (LOCALx nil (SEPx nil ))).
Proof.
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
extensionality rho; simpl.
normalize.
Qed.

Hint Rewrite canon1 canon2 canon4 canon8 : canon.
Hint Rewrite canon3 using check_nonlocal : canon.
Hint Rewrite canon3b using check_nonlocal : canon.
Hint Rewrite canon7 using check_nonlocal : canon.
Hint Rewrite <- (@sepcon_assoc (environ->mpred) _) : canon.

Lemma canon5: forall Q R S, 
       nonlocal Q ->
       Q && (local R && S) = local R && (Q && S).
Admitted.


Lemma canon5b: forall Q R S, 
       nonlocal Q ->
       Q && (S && local R) = local R && (Q && S).
Admitted.

Lemma canon5c: forall Q R, 
       nonlocal Q ->
       (Q && local R) = local R && Q.
Admitted.

Lemma canon6: forall Q R S, 
       nonlocal Q ->
       Q && (prop R && S) = prop R && (Q && S).
Admitted.

Lemma canon6b: forall Q R S, 
       nonlocal Q ->
       Q && (S && prop R) = prop R && (Q && S).
Admitted.

Lemma canon6c: forall Q R, 
       nonlocal Q ->
       (Q && prop R) = prop R && Q.
Admitted.

Hint Rewrite canon5 using check_nonlocal : canon.
Hint Rewrite canon5b using check_nonlocal : canon.
Hint Rewrite canon5c using check_nonlocal : canon.
Hint Rewrite canon6 using check_nonlocal : canon.
Hint Rewrite canon6b using check_nonlocal : canon.
Hint Rewrite canon6c using check_nonlocal : canon.

Lemma canon17 : forall (P: Prop) PP QR, prop P && (PROPx PP QR) = PROPx (P::PP) QR.
Proof.
intros. unfold PROPx. simpl. extensionality rho. apply pred_ext; normalize.
Qed.
Hint Rewrite canon17 : canon.


Lemma finish_canon: forall R1 P Q R, 
   do_canon R1 (PROPx P (LOCALx Q (SEPx R))) = (PROPx P (LOCALx Q (SEPx (R1::R)))).
Proof.
change SEPx with SEPx'.
unfold do_canon, PROPx, LOCALx, SEPx'; intros.
extensionality rho.
simpl.
normalize.
Qed.

Ltac canonicalize_pre :=
  match goal with |- semax _ ?P _ _ =>
      rewrite (start_canon P); autorewrite with canon
  end.    

Lemma restart_canon: forall P Q R, (PROPx P (LOCALx Q (SEPx R))) = do_canon emp (PROPx P (LOCALx Q (SEPx R))).
Proof.
intros.
unfold do_canon. rewrite emp_sepcon. auto.
Qed.

Lemma exp_do_canon:
   forall T (P: T -> environ->mpred) (Q: environ->mpred), do_canon (exp P) Q = EX x:_, do_canon (P x) Q.
Proof. apply exp_sepcon1. Qed.
Hint Rewrite exp_do_canon: canon.
Hint Rewrite exp_do_canon: normalize.

Lemma canon9: forall Q1 P Q R,
       local Q1 && (PROPx P (LOCALx Q R)) = 
         PROPx P (LOCALx (Q1::Q) R).
Proof.
intros; unfold PROPx, LOCALx; simpl.
extensionality rho.
normalize.
apply pred_ext; normalize;
repeat (rewrite prop_true_andp; auto).
Qed.
Hint Rewrite canon9: canon.


Lemma canon20: forall PQR, do_canon emp PQR = PQR.
Proof.
intros. apply emp_sepcon.
Qed.
Hint Rewrite canon20: canon.

