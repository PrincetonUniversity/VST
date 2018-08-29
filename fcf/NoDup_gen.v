(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
Set Implicit Arguments.

Require Import List.
Require Import fcf.Fold.

Section In_gen.
  Variable A : Type.
  Variable ea : A -> A -> Prop.

  Hypothesis ea_symm : 
    forall a1 a2, ea a1 a2 -> ea a2 a1.

  Hypothesis ea_trans : 
    forall a1 a2 a3,
      ea a1 a2 ->
      ea a2 a3 ->
      ea a1 a3.

  Fixpoint In_gen(a : A)(ls : list A) : Prop :=
    match ls with
      | nil => False
      | a' :: ls' =>
        ea a a' \/ In_gen a ls'
    end.

  Theorem In_gen_equiv_compat : 
    forall (ls : list A)(a1 a2 : A),
      ea a1 a2 ->
      In_gen a1 ls ->
      In_gen a2 ls.
    
    induction ls; intuition; simpl in *.
    intuition.
    left.
    eapply ea_trans.
    eapply ea_symm.
    eauto.
    trivial.

    right.
    eauto.
    
  Qed.

End In_gen.

Theorem In_gen_eq : 
  forall (A : Type)(a : A)(ls : list A),
    In a ls <-> In_gen eq a ls.
  
  induction ls; intuition; simpl in *.
  intuition.
  intuition.
  
Qed.

Section NoDup_gen.

  Variable A : Type.
  Variable ea : A -> A -> Prop.

  Inductive NoDup_gen : list A -> Prop :=
  | NoDup_gen_nil : NoDup_gen nil
  | NoDup_gen_cons : 
      forall (a : A)(ls : list A),
        (~In_gen ea a ls) -> 
        NoDup_gen ls ->
        NoDup_gen (a :: ls).

End NoDup_gen.

  
Theorem NoDup_gen_eq : 
  forall (A : Type)(ls : list A),
    NoDup ls <-> NoDup_gen eq ls.
  
  induction ls; intuition; simpl in *.
  econstructor.
  econstructor.
  
  inversion H1; clear H1; subst.
  econstructor.
  intuition.
  eapply H4.
  eapply  In_gen_eq.
  trivial.
  intuition.
  
  inversion H1; clear H1; subst.
  econstructor.
  intuition.
  eapply H4.
  eapply In_gen_eq.
  trivial.
  intuition.
  
Qed.

Section NoDup_gen_map.

  Variable A B : Type.
  Variable ea : A -> A -> Prop.
  Variable eb : B -> B -> Prop.
  Variable f : A -> B.

  Hypothesis ea_symm : 
    forall a1 a2,
      ea a1 a2 -> ea a2 a1.

  Hypothesis ea_trans : 
    forall a1 a2 a3,
      ea a1 a2 ->
      ea a2 a3 ->
      ea a1 a3.

  Hypothesis ea_func : 
    forall a1 a2, ea a1 a2 -> eb (f a1) (f a2).

  Hypothesis eb_symm : 
    forall b1 b2,
      eb b1 b2 -> eb b2 b1.

  Hypothesis eb_trans : 
    forall b1 b2 b3,
      eb b1 b2 ->
      eb b2 b3 ->
      eb b1 b3.

  Hypothesis ea_refl : 
    forall a y,
      eb (f a) y ->
      ea a a .

  Hypothesis eb_func : 
    forall a1 a2,
      eb (f a1) (f a2) -> ea a1 a2.

  Theorem In_gen_map_iff
  : forall (l : list A) (y : B),
      (In_gen eb y (map f l) <-> (exists x : A, eb (f x) y /\ In_gen ea x l)).
    
    induction l; intuition; simpl in *.
    intuition.
    destruct H.
    intuition.
    intuition.
    econstructor.
    intuition.
    eapply eb_symm.
    eauto.

    left.
    eapply ea_refl.
    eapply eb_symm.
    eauto.
    
    specialize (IHl y).
    intuition.
    destruct H2.
    intuition.
    econstructor.
    split.
    eauto.
    intuition.
    
    destruct H.
    intuition.
    left.
    eapply eb_trans.
    eapply eb_symm.
    eauto.
    eapply ea_func.
    trivial.
    
    right.       
    specialize (IHl y).
    intuition.
    eapply H2.
    econstructor.
    intuition.
    eauto.
    trivial.
  Qed.

  Theorem map_NoDup_gen : 
    forall (ls : list A),
      NoDup_gen ea ls ->
      NoDup_gen eb (map f ls).
    
    induction ls; intuition; simpl in *.
    econstructor.
    
    inversion H; clear H; subst.
    econstructor.
    intuition.
    eapply H2.
    eapply In_gen_map_iff in H.
    destruct H.
    intuition.
    eapply In_gen_equiv_compat; [ eauto | eauto | idtac | idtac].
    eapply eb_func.
    eauto.
    trivial.

    eauto.
    
  Qed.
  
End NoDup_gen_map.

Require Import fcf.RepeatCore.
 
Theorem In_gen_weaken : 
  forall (A : Type)(e1 e2 : A -> A -> Prop) ls a,
    In_gen e1 a ls ->
    (forall a', e1 a a' -> e2 a a') ->
    In_gen e2 a ls.
  
  induction ls; intuition; simpl in *.
  intuition.
  
Qed.

Lemma flatten_NoDup_gen : 
  forall (A : Set)(ls : list (list A)),
    NoDup_gen (fun a b => a <> nil /\ a = b) ls ->
    (forall x, In x ls -> NoDup x) ->
    (forall x1 x2, In x1 ls -> In x2 ls -> x1 <> x2 -> NoDup (x1 ++ x2)) ->
    NoDup (flatten ls).
  
  induction ls; intuition; simpl in *.
  econstructor.
  
  inversion H; clear H; subst.
  eapply app_NoDup; intuition.
  
  eapply in_flatten in H3.
  destruct H3.
  intuition.
  eapply app_NoDup_inv.
  eapply H1.
  right.
  eapply H6.
  left.
  reflexivity.
  intuition.
  subst.
  
  eapply H4.
  eapply In_gen_weaken.
  exact H6.
  intuition.
  subst.
  subst.
  simpl in *.
  intuition.
  eauto.
  eauto.
       
  eapply in_flatten in H2.
  destruct H2.
  intuition.
  eapply app_NoDup_inv.
  eapply H1.
  right.
  eapply H6.
  left.
  reflexivity.
  intuition.
  subst.
  eapply H4.
  eapply In_gen_weaken.
  exact H6.
  intuition.
  subst.
  subst.
  simpl in *.
  intuition.
  eauto.
  eauto.
  
Qed.

Theorem NoDup_gen_weaken : 
  forall (A : Type)(e1 e2 : A -> A -> Prop) ls,
    NoDup_gen e1 ls ->
    (forall a1 a2, e2 a1 a2 -> e1 a1 a2) ->
    NoDup_gen e2 ls.
  
  induction ls; intuition; simpl in *.
  econstructor.
  
  inversion H; clear H; subst.
  econstructor.
  intuition.
  eapply H3.
  eapply In_gen_weaken; eauto.
  
  eauto.
  
Qed.

Theorem In_gen_zip_fst : 
  forall (A B : Set)(ea : A -> A -> Prop)(lsa : list A)(lsb : list B) a b,   
    In_gen (fun a b => ea (fst a) (fst b)) (a, b) (zip lsa lsb) ->
    In_gen ea a lsa.
  
  induction lsa; intuition; simpl in *.
  destruct lsb;
    simpl in *;
    intuition.
  
  right.
  eauto.
Qed.


Theorem NoDup_gen_zip_fst : 
  forall (A B : Set)(ea : A -> A -> Prop)(lsa : list A)(lsb : list B),
    NoDup_gen ea lsa ->
    NoDup_gen (fun a b => ea (fst a) (fst b)) (zip lsa lsb).
  
  induction lsa; intuition; simpl in *.
  econstructor.
  
  inversion H; clear H; subst.
  destruct lsb; intuition; simpl in *.
  econstructor.
  
  econstructor.
  intuition.
  eapply H2.
  eapply In_gen_zip_fst.
  eauto.
  eauto.

Qed.

