(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* Type classes and theory for groups, including finite cyclic groups. *)

Set Implicit Arguments.

Require Import FCF.Rat.
Require Import FCF.StdNat.

Class Group_op(A : Set) := groupOp : A -> A -> A.
Infix "*" := groupOp : group_scope.
Delimit Scope group_scope with group.
Local Open Scope group_scope.

Class Group
      (GroupElement : Set)
      (groupOp : Group_op GroupElement)
      (ident : GroupElement)
      (inverse : GroupElement -> GroupElement) 
  :={
      
      associativity : 
        forall (x y z : GroupElement),
          (x * y) * z = x * (y * z);
      
      left_identity : 
        forall (a : GroupElement),
          ident * a = a;
      
      right_identity : 
        forall (a : GroupElement),
          a * ident = a;
      
      left_inverse : 
        forall (a : GroupElement),
          (inverse a) * a = ident;
                                                   
      right_inverse : 
        forall (a : GroupElement),
          a * (inverse a) = ident
                                                                                               
    }.

Fixpoint groupExp`{G : Group}(a : GroupElement)(n : nat) : GroupElement :=
  match n with
    | 0 => ident
      | S n' => groupOp a (groupExp a n')
  end.

Infix "^" := groupExp : group_scope.

Section GroupProperties.

  Context `{G : Group}.

  Lemma groupExp_identity : forall n,
    ident^n = ident.

    induction n; intuition; simpl in *.
    rewrite IHn.
    apply left_identity.

  Qed.

  Theorem groupExp_plus : forall n1 n2 x,
    x^(n1 + n2) = (x^n1) * (x^n2).

    induction n1; intuition; simpl in *.
    rewrite left_identity.
    trivial.

    rewrite IHn1.
    rewrite associativity.
    trivial.
  Qed.

  Theorem groupExp_mult : forall n2 n1 x, 
    ((x^n1)^n2) = (x^(n1 * n2)).

    induction n2; intuition; simpl in *.
    rewrite mult_0_r.
    trivial.

    rewrite mult_comm.
    simpl.

    rewrite groupExp_plus.
    f_equal.
    rewrite IHn2.
    rewrite mult_comm.
    trivial.
  Qed.

End GroupProperties.


Class FiniteCyclicGroup `{G: Group}
      (g : GroupElement)(order : posnat)(groupLog : GroupElement -> GroupElement -> nat) := {
                                                                             
  generator : GroupElement -> Prop;
  g_generator : generator g;
  group_cyclic: forall (g a : GroupElement),
    generator g ->
    g^(groupLog g a) = a;
  groupLog_correct: forall g x,
    generator g ->
    modNat (groupLog g (g^x)) order = modNat x order;
  groupIdent : forall g,
    generator g -> 
    g^0 = ident;
  groupOrder : forall g,
    generator g ->
    g^order = g^0
    
}.

Section FiniteCyclicGroupProperties.

  Context`{FCG : FiniteCyclicGroup}.

  Lemma groupExp_eq_h : forall g c1 v,
    generator g -> 
    v < order ->
    g^(c1 * order + v) = g^v.
    
    induction c1; intuition; simpl in *.
    rewrite <- plus_assoc.
    rewrite (groupExp_plus order).
    rewrite groupOrder; trivial.
    rewrite groupIdent; trivial.
    rewrite left_identity.
    rewrite IHc1;
    trivial.
  Qed.

  Theorem groupExp_eq_if : forall g x y,
    generator g ->
    modNat x order = modNat y order ->
    g^x = g^y.

    intuition.
    destruct (modNat_correct x order).
    destruct (modNat_correct y order).
    rewrite H1.
    rewrite H2.
    rewrite H0.
    
   repeat rewrite groupExp_eq_h; eauto using modNat_lt.
   
  Qed.

   Theorem commutativity : forall x y,
    x * y = y * x.

    intuition.
    rewrite <- (group_cyclic g x).
    rewrite <- (group_cyclic g y).
    repeat rewrite <- groupExp_plus.
    f_equal.
    omega.
    apply g_generator.
    apply g_generator.
  Qed.

  Theorem groupExp_distrib : forall n x y,
    (x * y)^n = x^n * y^n.

    induction n; intuition; simpl in *.
    rewrite left_identity.
    trivial.

    rewrite IHn.
    repeat rewrite associativity.
    f_equal.

    rewrite commutativity.
    repeat rewrite associativity.
    f_equal.
    apply commutativity.
    
  Qed.

  Theorem groupExp_eq : forall g x y,
    generator g ->
    g^x = g^y ->
    modNat x order = modNat y order.

    intuition.
    erewrite <- groupLog_correct; eauto.
    erewrite <- (groupLog_correct _ y); eauto.
    f_equal.
    f_equal.
    trivial.
  Qed.

  Theorem ident_l_unique : forall x y,
    x * y = y -> 
    x = ident.

    intuition.
    
    rewrite <- (group_cyclic g x).
    rewrite <- (@groupIdent _ groupOp ident _ G _ _ _ FCG g).
    eapply groupExp_eq_if; trivial.
    apply g_generator.
    
    rewrite <- (group_cyclic g y) in H; eauto.
    rewrite <- (group_cyclic g x) in H; eauto.
    rewrite <- groupExp_plus in H.
    apply groupExp_eq in H; trivial.

    eapply modNat_add_same_r.
    eauto.

    apply g_generator.
    apply g_generator.
    apply g_generator.
    apply g_generator.
    apply g_generator.
  Qed.  

  Theorem groupExp_mod : forall g n, 
    generator g ->
    g^n = g^(modNat n order).

    intuition.
    eapply groupExp_eq_if.
    trivial.
    rewrite (@modNat_eq _ (modNat n order)).
    trivial.
    eapply modNat_lt.
  Qed.


End FiniteCyclicGroupProperties.

