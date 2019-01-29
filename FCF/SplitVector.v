(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

Set Implicit Arguments.

Require Import FCF.FCF.
Require Import FCF.SemEquiv.
Require Import FCF.DetSem.

Fixpoint splitVector(A : Set)(n m : nat) : Vector.t A (n + m) -> (Vector.t A n * Vector.t A m) :=
  match n with
          | 0 => 
            fun (v : Vector.t A (O + m)) => (@Vector.nil A, v)
          | S n' => 
            fun (v : Vector.t A (S n' + m)) => 
              let (v1, v2) := splitVector _ _ (Vector.tl v) in
                (Vector.cons _ (Vector.hd v) _ v1, v2)
    end.

Theorem splitVector_append : 
  forall (A : Set) n1 (v1 : Vector.t A n1) n2 (v2 : Vector.t A n2),
    splitVector n1 n2 (Vector.append v1 v2) = (v1, v2).
  
  induction v1; intuition; simpl in *.
  remember ( splitVector n n2 (Vector.append v1 v2)) as z.
  destruct z.
  rewrite IHv1 in Heqz.
  inversion Heqz; subst.
  trivial.
Qed.

Theorem append_splitVector_h : 
  forall (A : Set) n1 n2 (x : Vector.t A (n1 + n2)),
   (Vector.append (fst (splitVector n1 n2 x)) (snd (splitVector n1 n2 x))) = x.

  induction n1; intuition; simpl in *.
  destruct (vector_S x).
  destruct H.
  subst.
  simpl.
  remember (splitVector n1 n2 x1) as z.
  destruct z.
  simpl.
  f_equal.
  specialize (IHn1 n2 x1).
  rewrite <- Heqz in IHn1.
  simpl in *.
  trivial.

Qed.

Theorem append_splitVector: 
  forall (A : Set) n1 n2 (x : Vector.t A (n1 + n2)) x1 x2,
    (x1, x2) = (splitVector n1 n2 x) -> 
   (Vector.append x1 x2) = x.

  intuition.
  specialize (append_splitVector_h _ _ x); intuition.
  rewrite <- H in H0.
  simpl in *.
  trivial.

Qed.


Theorem shiftOut_plus : 
  forall (n1 n2 : nat) s b s',
    shiftOut s (n1 + n2) = Some (b, s') ->
    exists b1 b2 s'',
      shiftOut s n1 = Some (b1, s'') /\
      shiftOut s'' n2 = Some (b2, s') /\
      splitVector n1 n2 b = (b1, b2).
  
  induction n1; intuition; simpl in *.
  rewrite shiftOut_0.
  econstructor.
  econstructor.
  econstructor.
  intuition.
  trivial.
  
  destruct s; simpl in *.
  discriminate.
  case_eq (shiftOut s (n1 + n2)); intuition.
  rewrite H0 in H.
  destruct p.
  inversion H; clear H; subst.
  edestruct IHn1.
  eauto.
  destruct H.
  destruct H.
  intuition.
  rewrite H1.
  econstructor.
  econstructor.
  econstructor.
  intuition.
  eauto.
  simpl.
  rewrite H3.
  trivial.
  
  rewrite H0 in H.
  discriminate.
  
Qed.

Theorem shiftOut_plus_None : 
  forall n1 n2 s,
    shiftOut s (n1 + n2) = None ->
    shiftOut s n1 = None \/
    (exists x s', shiftOut s n1 = Some (x, s') /\
      shiftOut s' n2 = None).
  
  induction n1; intuition; simpl in *.
  rewrite shiftOut_0.
  right.
  econstructor.
  econstructor.
  intuition.
  
  destruct s; simpl in *.
  intuition.
  
  case_eq (shiftOut s (n1 + n2)); intuition.
  rewrite H0 in H.
  destruct p.
  discriminate.
  edestruct IHn1.
  eauto.
  rewrite H1.
  intuition.
  
  destruct H1.
  destruct H1.
  intuition.
  
  rewrite H2.
  right.
      
  econstructor.
  econstructor.
  intuition.
Qed.

Theorem Vector_cons_app_assoc : 
  forall (A : Type)(a : A)(n1 n2 : nat)(v1 : Vector.t A n1)(v2 : Vector.t A n2),
    Vector.cons _ a _ (Vector.append v1 v2) = 
    Vector.append (Vector.cons _ a _ v1) v2.
  
  induction n1; intuition; simpl in *.
       
Qed.

Theorem shiftOut_plus_if :
  forall n1 n2 s s' s'' b1 b2,
    shiftOut s n1 = Some (b1, s') ->
    shiftOut s' n2 = Some (b2, s'') ->
    shiftOut s (n1 + n2) = Some (Vector.append b1 b2, s'').
  
  induction n1; intuition; simpl in *.
  rewrite shiftOut_0 in H.
  inversion H; clear H; subst.
  simpl in *.
  trivial.
  
  destruct s; simpl in *.
  discriminate.
  case_eq (shiftOut s n1); intuition.
  rewrite H1 in H.
  destruct p.
  inversion H; clear H; subst.
  erewrite IHn1; eauto.
  
  rewrite Vector_cons_app_assoc.
  trivial.
  
  rewrite H1 in H.
  discriminate.
Qed.

Theorem shiftOut_plus_None_if : 
  forall n1 n2 s,
    (shiftOut s n1 = None \/
      (exists b s', shiftOut s n1 = Some (b, s') /\
        shiftOut s' n2 = None)) ->
    shiftOut s (n1 + n2) = None.
  
  induction n1; intuition; simpl in *.
  rewrite shiftOut_0 in H0.
  discriminate.
  destruct H0.
  destruct H.
  intuition.
  rewrite shiftOut_0 in H0.
  inversion H0; clear H0; subst.
  trivial.
  
  destruct s; simpl in *.
  trivial.
  
  case_eq (shiftOut s n1); intuition.
  rewrite H in H0.
  destruct p.
  discriminate.
  
  rewrite H in H0.
  erewrite IHn1.
  trivial.
  intuition.
  
  destruct H0.
  destruct H.
  intuition.
  destruct s; simpl in *.
  discriminate.
  
  case_eq (shiftOut s n1); intuition.
  rewrite H in H0.
  destruct p.
  inversion H0; clear H0; subst.
  erewrite IHn1.
  trivial.
  right.
  econstructor.
  econstructor.
  intuition.
  eauto.
  trivial.
  
  rewrite H in H0.
  discriminate.
  
Qed.
    
Theorem Rnd_split_equiv : 
  forall n1 n2 z ,
    evalDist 
    (x <-$ {0, 1}^(n1 + n2);
      ret (splitVector n1 n2 x)) z ==
    evalDist 
    (x1 <-$ {0, 1}^n1;
      x2 <-$ {0, 1}^n2;
      ret (x1, x2)) z.
  
  intuition.
  
  eapply det_eq_impl_dist_sem_eq; wftac.
  unfold evalDet_equiv.
  intuition.
  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  simpl in *.
  case_eq (shiftOut s (plus n1 n2)); intuition.
  destruct p.
  specialize (shiftOut_plus _ _ _ H); intuition.
  destruct H0.
  destruct H0.
  destruct H0.
  intuition.    
  
  rewrite H in H4.
  inversion H4; clear H4; subst.
  simpl in *.
  inversion H8; clear H8; subst.
  simpl in *.
  inversion H7; clear H7; subst.
  econstructor.
  econstructor.
  eauto.
  simpl.
  rewrite H1.
  econstructor.
  eauto.
  simpl.
  econstructor.
  eauto.
  simpl.
  rewrite H0.
  econstructor.
  eauto.
  simpl.
  econstructor.
  eauto.
  rewrite H3.
  econstructor.
  
  rewrite H in H4.
  inversion H4; clear H4; subst.
  
  inversion H0; clear H0; subst.
  simpl in *.
  case_eq (shiftOut s (n1 + n2)); intuition.
  rewrite H in H4.
  destruct p.
  inversion H4; clear H4; subst.
  simpl in *.
  inversion H5; clear H5; subst.
  simpl in *.
  inversion H4.
      
  specialize (shiftOut_plus_None _ _ _ H); intuition.
  econstructor.
  econstructor.
  eauto.
  simpl.
  rewrite H1.
  econstructor.
  destruct H1.
  destruct H0.
  intuition.
  econstructor.
  econstructor.
  eauto.
  simpl.
  rewrite H1.
  econstructor.
  eauto.
  simpl.
  econstructor.
  eauto.
  simpl.
  rewrite H2.
  econstructor.
  
  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  simpl in *.
  case_eq (shiftOut s n1); intuition.
  rewrite H in H4.
  destruct p.
  inversion H4; clear H4; subst.
  inversion H5; clear H5; subst.
  simpl in *.
  case_eq (shiftOut b1 n2); intuition.
  rewrite H0 in H4.
  destruct p.
  inversion H4; clear H4; subst.
  simpl in *.
  inversion H6; clear H6; subst.
  simpl in *.
  inversion H5; clear H5; subst.
  econstructor.
  econstructor.
  eauto.
  simpl.

  erewrite shiftOut_plus_if; eauto.
  econstructor.
  eauto.
  simpl.
  econstructor.
  eauto.
  simpl. 
    
  rewrite splitVector_append.
  econstructor.
  
  rewrite H0 in H4.
  inversion H4; clear H4; subst.
  rewrite H in H4.
  inversion H4.
  
  inversion H0; clear H0; subst.
  simpl in *.
  case_eq (shiftOut s n1); intuition.
  rewrite H in H4.
  destruct p.
  inversion H4; clear H4; subst.
  simpl in *.
  inversion H5; clear H5; subst.
  simpl in *.
  case_eq (shiftOut b1 n2); intuition.
  rewrite H0 in H4.
  destruct p.
  inversion H4; clear H4; subst.
  simpl in *.
  inversion H6; clear H6; subst.
  simpl in *.
  inversion H5.
  
  econstructor.
  econstructor.
  eauto.
  simpl.
  
  erewrite shiftOut_plus_None_if.
  econstructor.
  right.
  econstructor.
  econstructor.
  intuition.
  eauto.
  trivial.
  
  rewrite H in H4.
  econstructor.
  econstructor.
  eauto.
  simpl.
  erewrite shiftOut_plus_None_if.
  econstructor.
  
  intuition.
Qed.