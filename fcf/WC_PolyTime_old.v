(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* An efficiency predicate that characterizes of non-uniform PPT turing machines.  *)

Require Import FCF.Crypto.
Set Implicit Arguments.

Definition CostModel := forall (A B : Type), (A -> B) -> nat -> Prop.

Local Open Scope nat_scope.

Class constant_cost_relation(cost : CostModel) :={

  constant_cost_const : 
  forall (A B : Type)(b : B),
    cost _ _ (fun (_ : A) => b) 0;

  constant_cost_pair_args : 
  forall (A B C : Type)
    (f : A -> B -> C) c,
    cost _ _ (fun p => f (fst p) (snd p)) c ->
    exists c1 c2,
    cost _ _ f c1 /\ (forall a, cost _ _ (f a) c2) /\ c1 + c2 <= c;

  constant_cost_unpair_args : 
  forall (A B C : Type)
    (f : (A * B) -> C) c,
    cost _ _ f c ->
    cost _ _ (fun a b => f (a, b)) 0 /\
    (forall a, cost _ _ (fun b => f (a, b)) c);

  constant_cost_compose : 
  forall (A B C : Type)
    (f1 : A -> B)(f2 : A -> B -> C) c1 c2 c3,
    cost _ _ f1 c1 ->
    cost _ _ f2 c2 -> 
    (forall a, cost _ _ (f2 a) c3) -> 
    cost _ _ (fun a => f2 a (f1 a)) (c1 + c2 + c3);

  constant_cost_bind :
    forall (Z : Type)(A B : Set)(f1 : Z -> Comp A) (f2 : Z -> A -> Comp B) c1 c2 c3,
      cost _ _ f1 c1 ->
      cost _ _ f2 c2 ->
      (forall z, cost _ _ (f2 z) c3) -> 
      cost _ _ (fun a => Bind (f1 a) (f2 a)) (c1 + c2 + c3);

  constant_cost_ret :
    forall (A : Set)(eqd : eq_dec A),
      cost _ _ (@Ret A eqd) 0;

  constant_cost_le :
    forall A B (f : A -> B) c1 c2,
      cost _ _ f c1 ->
      c1 <= c2 ->
      cost _ _ f c2;

  constant_cost_fst : 
    forall (A B : Type),
      cost _ _ (@fst A B) 0;

  constant_cost_snd : 
    forall (A B : Type),
      cost _ _ (@snd A B) 0;

  constant_cost_pair_1 : 
    forall (A B : Type),
      cost _ _ (@pair A B) 0;

  constant_cost_pair_2 : 
    forall (A B : Type) a,
      cost _ _ (@pair A B a) 0;

  constant_cost_pair : 
    forall (A B : Type),
      cost _ _ (fun p => @pair A B (fst p) (snd p)) 0;
  
  constant_cost_eqb_bool : 
    cost _ _ (fun p => @eqb bool _ (fst p) (snd p)) 1;

  constant_cost_bvxor : 
    forall eta, 
      cost _ _ (fun p => BVxor eta (fst p) (snd p)) eta;

  constant_cost_firstn : 
    forall k (A : Type),
      cost _ _ (@firstn A k) k;
  
  constant_cost_skipn : 
    forall k (A : Type),
      cost _ _ (@skipn A k) k;

  constant_cost_tl : 
    forall (A : Type),
      cost _ _ (@tl A) 1;
  
  constant_cost_hd : 
    forall (A : Type)(a : A),
      cost _ _ (hd a) 1;

  constant_cost_if_bool_f :
    forall (A B : Type)(f1 : A -> bool)(f2 f3 : A -> B) c1 c2 c3,
      cost _ _ f1 c1 ->
      cost _ _ f2 c2 ->
      cost _ _ f3 c3 ->
      cost _ _ (fun a => if (f1 a) then (f2 a) else (f3 a)) (c1 + c2 + c3)

}.


Section constant_cost_theory.
  Context `(constant_cost_relation).

  Theorem constant_cost_pair_args_weak : 
    forall (A B C : Type)
      (f : A -> B -> C) c,
      cost (fun p => f (fst p) (snd p)) c ->
      cost f c.
    
    intuition.
    
    apply constant_cost_pair_args in H0.
    destruct H0.
    destruct H0.
    intuition.
    eapply constant_cost_le.
    eauto.
    omega.

  Qed.

  Theorem constant_cost_compose_unary : 
  forall (A B C: Type)
    (f1 : A -> B)(f2 : B ->C) c1 c2,
    cost f1 c1 ->
    cost f2 c2 ->
    cost (fun a => f2 (f1 a)) (c1 + c2).

    intuition.
    eapply constant_cost_le.
    eapply (constant_cost_compose f1 _ ).
    eauto.
    eapply constant_cost_const.
    intuition.
    eauto.
    omega.

  Qed.


  Theorem constant_cost_compose_binary : 
  forall (A B C D: Type)
    (f1 : A -> B)(f2 : A ->C)(f3 : B -> C -> D) c1 c2 c3 c4,
    cost f1 c1 ->
    cost f2 c2 ->
    cost f3 c3 ->
    (forall b, cost (f3 b) c4) -> 
    cost (fun a => f3 (f1 a) (f2 a)) (c1 + c2 + c3 + c4).

    intuition.
    eapply constant_cost_le.
    eapply (constant_cost_compose f2 (fun a x => f3 (f1 a) x)).
    eauto.
    eapply (constant_cost_compose f1 (fun a y x => f3 y x)).
    eauto.
    eapply constant_cost_const.
    intuition.
    eauto.

    intuition.
    omega.
    
  Qed.

  Theorem constant_cost_compose_binary_const_r : 
  forall (A B C D: Type)
    (f1 : A -> B)(c : C)(f3 : B -> C -> D) c1 c2,
    cost f1 c1 ->
    cost (fun x => f3 x c) c2 ->
    cost (fun a => f3 (f1 a) c) (c1 + c2).

    intuition.
    eapply constant_cost_le.
    eapply (constant_cost_compose f1 (fun _ x => f3 x c)).
    eauto.
    eapply constant_cost_const.
    intuition.
    eauto.
    omega.
  Qed.

  Theorem constant_cost_compose_binary_const_l : 
  forall (A B C D: Type)
    (b : B)(f2 : A -> C)(f3 : B -> C -> D) c1 c2,
    cost f2 c1 ->
    cost (f3 b) c2 ->
    cost (fun a => f3 b (f2 a)) (c1 + c2).
    
    intuition.
    eapply constant_cost_le.
    eapply (constant_cost_compose f2 (fun _ x => f3 b x)).
    eauto.
    eapply constant_cost_const.
    intuition.
    eauto.
    omega.
    
  Qed.

  
  
  Theorem constant_cost_bind_const1 : 
      forall (A  : Type)(B C: Set)
        (f1 : Comp B)(f2 : A -> B -> Comp C) c1 c2,
        cost f2 c1 ->
        (forall a, cost (f2 a) c2) -> 
        cost (fun a => Bind f1 (f2 a)) (c1 + c2).
      
      intuition.
      eapply constant_cost_le.
      eapply constant_cost_bind; eauto.
      eapply constant_cost_const.
      omega.
    Qed.

    Theorem constant_cost_bind_const1_pair : 
      forall (A  : Type)(B C: Set)
        (f1 : Comp B)(f2 : A -> B -> Comp C) c,
        cost (fun p => f2 (fst p) (snd p)) c ->
        cost (fun a => Bind f1 (f2 a)) c.
      
      intuition.
      apply constant_cost_pair_args in H0.
      destruct H0.
      destruct H0.
      intuition.
      eapply constant_cost_le.
      eapply constant_cost_bind; eauto.
      eapply constant_cost_const.
      omega.
    Qed.

    Theorem constant_cost_bind_const2 : 
      forall (A  : Type)(B C: Set)
        (f1 : A -> (Comp B))(f2 : B -> Comp C) c1 c2,
        cost f1 c1 ->
        cost f2 c2 ->
        cost (fun a => Bind (f1 a) f2) (c1 + c2).
      
      intuition.
      eapply constant_cost_le.
      eapply constant_cost_bind; eauto.
      eapply constant_cost_const.
      omega.
    Qed.
    
    Theorem constant_cost_bind_pair : 
      forall (A  : Type)(B C: Set)
        (f1 : A -> Comp B)(f2 : A -> B -> Comp C) c1 c2,
        cost f1 c1 ->
        cost (fun p => f2 (fst p) (snd p)) c2 ->
        cost (fun a => Bind (f1 a) (f2 a)) (c1 + c2).

      intuition.
      apply constant_cost_pair_args in H1.
      destruct H1.
      destruct H1.
      intuition.
      eapply constant_cost_le.
      eapply constant_cost_bind; eauto.
      omega.
    Qed.

    Theorem constant_cost_compose_binary_pair : 
      forall (A B C D: Type)
        (f1 : A -> B)(f2 : A ->C)(f3 : B -> C -> D) c1 c2 c3,
        cost f1 c1 ->
        cost f2 c2 ->
        cost (fun p => f3 (fst p) (snd p)) c3 ->
        cost (fun a => f3 (f1 a) (f2 a)) (c1 + c2 + c3).

      intuition.
      apply constant_cost_pair_args in H2.
      destruct H2.
      destruct H2.
      intuition.
      eapply constant_cost_le.
      eapply (constant_cost_compose f2 (fun a x => f3 (f1 a) x)).
      eauto.
      eapply (constant_cost_compose f1 (fun a y x => f3 y x)).
      eauto.
      eapply constant_cost_const.
      intuition.
      eauto.
      
      intuition.
      omega.
      
    Qed.


  
End constant_cost_theory.

Require Import FCF.Asymptotic.

Definition poly_time_nonuniform(cost : CostModel)(A B : nat -> Type)(f : forall n, (A n) -> (B n)) :=
  exists x, polynomial x /\
  forall n, 
    (exists c, (cost _ _ (f n)) c /\ c <= x n).



