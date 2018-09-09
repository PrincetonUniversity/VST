(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)


Set Implicit Arguments.

Require Import fcf.FCF.
Require Import fcf.Admissibility.

Local Open Scope nat_scope.

Class function_cost_model(cost: FunctionCostModel) :={
  
  cost_ident : 
  forall (A : Type),
    cost _ _ (fun (a : A) => a) 0;
  
  cost_ext : 
    forall (A B : Type)(f1 f2 : A -> B) n,
      (forall a, f1 a = f2 a) ->
      cost _ _ f2 n ->
      cost _ _ f1 n;
  
  cost_const : 
    forall (A B : Type)(b : B),
      cost _ _ (fun (_ : A) => b) 0;
  
  cost_le :
    forall A B (f : A -> B) c1 c2,
      cost _ _ f c1 ->
      c1 <= c2  ->
      cost _ _ f c2;
  
  cost_compose : 
    forall (A B C : Type)
      (f1 : A -> B)(f2 : A -> B -> C) c1 c2 c3,
      cost _ _ f1 c1 ->
      cost _ _ f2 c2 ->
      (forall a, cost _ _ (f2 a) c3) -> 
      cost _ _ (fun a => f2 a (f1 a)) (c1 + c2 + c3);
  
  cost_uncurry_1 : 
    forall (A B C : Type)(f : A -> B -> C) n,
      cost _ _ (fun a => f (fst a) (snd a)) n ->
      cost _ _ f n;
  
  cost_uncurry_2 : 
    forall (A B C : Type)(f : A -> B -> C) n,
      cost _ _ (fun a => f (fst a) (snd a)) n ->
      forall a, cost _ _ (f a) n;
  
  cost_curry : 
    forall (A B C : Type)(f : A -> B -> C) c1 c2,
      cost _ _ f c1 ->
      (forall a, cost _ _ (f a) c2) ->
      cost _ _ (fun p => f (fst p) (snd p)) (c1 + c2);
  
  cost_fst : 
    forall (A B : Type),
      cost _ _ (@fst A B) 0;
  
  cost_snd : 
    forall (A B : Type),
      cost _ _ (@snd A B) 0;
  
  cost_BVxor : 
    forall n,
      cost _ _ (fun p => @BVxor n (fst p) (snd p)) n;
  
  cost_vec_head : 
    forall (A : Type) n,
      cost _ _ (@Vector.hd A n) 0;
  
  cost_eqb_bool : 
    cost _ _ (fun (p : bool * bool) => eqb (fst p) (snd p)) 1;
  
  cost_if_bool : 
    forall (A B : Type) (f : A -> bool) (f_so f_not : A -> B) c1 c2 c3,
      cost _ _ f c1 ->
      cost _ _ f_so c2 ->
      cost _ _ f_not c3 ->
      cost _ _ (fun p => if (f p) then (f_so p) else (f_not p)) (c1 + c2 + c3);
  
  cost_Ret : 
    forall (A : Set)(eqd : eq_dec A),
      cost _ _ (Ret eqd) 0;
  
  cost_OC_Ret : 
    forall (A B C: Set),
      cost _ _ (@OC_Ret A B C) 0;
  
  cost_OC_Bind : 
    forall (A B C C' : Set),
      cost _ _ (fun p => (@OC_Bind A B C C' (fst p) (snd p))) 0;
  
  cost_OC_Query : 
    forall (A B : Set),
      cost _ _ (@OC_Query A B) 0;
  
  cost_OC_Run_1 : 
    forall (A B C A' B' S : Set)(eqds : EqDec S)(eqda : EqDec A)(eqdb : EqDec B),
      cost _ _ 
      (@OC_Run A B C A' B' S eqds eqdb eqda)
      0;
  
  cost_OC_Run_2 : 
    forall (A B C A' B' S : Set)(eqds : EqDec S)(eqda : EqDec A)(eqdb : EqDec B) c,
      cost _ _ 
      (@OC_Run A B C A' B' S eqds eqdb eqda c)
      0;
  
  cost_OC_Run_3 : 
    forall (A B C A' B' S : Set)(eqds : EqDec S)(eqda : EqDec A)(eqdb : EqDec B) c o,
      cost _ _ 
      (@OC_Run A B C A' B' S eqds eqdb eqda c o)
      0 
      
}.

Inductive comp_cost(fm : FunctionCostModel) : CompCostModel :=
| comp_cost_Ret : 
  forall (A : Set)(eqd : eq_dec A)(a : A),
    comp_cost fm (Ret eqd a) 0
| comp_cost_Bind : 
  forall (A B : Set)(c : Comp A)(f : A -> Comp B) x1 x2 x3,
    comp_cost fm c x1 ->
    fm _ _ f x2 ->
    (forall a, comp_cost fm (f a) x3) ->
    comp_cost fm (Bind c f) (x1 + x2 + x3)
| comp_cost_Rnd : 
  forall n,
    comp_cost fm (Rnd n) n.


Inductive oc_cost(fm : FunctionCostModel)(cm : CompCostModel) : OC_CostModel :=
| oc_cost_Query : 
  forall (A B : Set)(a : A),
    oc_cost fm cm (OC_Query B a) (fun n => n)
| oc_cost_Run : 
  forall (A B C : Set)(c : OracleComp A B C) f1,
    oc_cost fm cm c f1 ->
    forall (A' B' S : Set)(eqds : EqDec S)(eqdb : EqDec B)(eqda : EqDec A) 
      (o : S -> A -> OracleComp A' B' (B * S)) x1 x2 f2,
      fm _ _ o x1 ->
      (forall x, fm _ _ (o x) x2) ->
      (forall x y, oc_cost fm cm (o x y) f2) ->
      forall s, 
        oc_cost fm cm (OC_Run _ _ _ c o s) (fun n => f1 (x1 + x2 + (f2 n)))
| oc_cost_Ret : 
  forall (A B C : Set)(c : Comp C) n,
    cm _ c n ->
    oc_cost fm cm (OC_Ret A B c) (fun _ => n)
| oc_cost_Bind :
  forall (A B C C' : Set)(c : OracleComp A B C)(f : C -> OracleComp A B C') f1 x f2,
    oc_cost fm cm c f1 ->
    fm _ _ f x->
    (forall y, oc_cost fm cm (f y) f2) ->
    oc_cost fm cm (OC_Bind c f) (fun n => (f1 n) + x + (f2 n))
| oc_cost_le : 
  forall (A B C : Set)(c : OracleComp A B C) f1 f2,
    oc_cost fm cm c f1 ->
    (forall x, f1 x <= f2 x) ->
    oc_cost fm cm c f2.

Section CostTheory.

  Context `{function_cost_model}.

  Theorem cost_compose_unary : 
    forall (A B C: Type)
      (f1 : A -> B)(f2 : B ->C) c1 c2,
      cost f1 c1 ->
      cost f2 c2 ->
      cost (fun a => f2 (f1 a)) (c1 + c2).
    
    intuition.
    eapply cost_le.
    eapply (cost_compose f1 _ ).
    eauto.
    intuition.
    eapply cost_const.
    intuition.
    eauto.
    omega.
    
  Qed.
  
  Theorem cost_compose_binary : 
    forall (A B C D: Type)
      (f1 : A -> B)(f2 : A ->C)(f3 : B -> C -> D) c1 c2 c3 c4,
      cost f1 c1 ->
      cost f2 c2 ->
      cost f3 c3 ->
      (forall a, cost (f3 a) c4) -> 
      cost (fun a => f3 (f1 a) (f2 a)) (c1 + c2 + c3 + c4).
    
    intuition.
    eapply cost_le.
    eapply (cost_compose f2 (fun a x => f3 (f1 a) x)).
    eauto.
    intuition.
    eapply (cost_compose f1 (fun a => f3)).
    eauto.
    intuition.
    eapply cost_const.
    intuition.
    eauto.
    intuition.
    
    omega.
    
  Qed.
  
  Theorem cost_pair_1 : 
    forall (A B : Type),
      cost (@pair A B) 0.
    
    intuition.
    eapply cost_uncurry_1.
    eapply cost_ext.
    2:{
      eapply cost_ident.
    }
    intuition.
  Qed.
  
  Theorem cost_pair_2 : 
    forall (A B : Type) a,
      cost (@pair A B a) 0.
    
    intuition.
    eapply cost_uncurry_2.
    eapply cost_ext.
    2:{
      eapply cost_ident.
    }
    intuition.
  Qed.

  Theorem cost_OC_Bind_1 : forall (A B C C' : Set),
    cost (@OC_Bind A B C C') 0.

    intuition.
    eapply cost_uncurry_1.
    eapply cost_OC_Bind.

  Qed.

  Theorem cost_OC_Bind_2 : forall (A B C C' : Set) (c : OracleComp A B C),
    cost (@OC_Bind A B C C' c) 0.

    intuition.
    eapply cost_uncurry_2.
    eapply cost_OC_Bind.

  Qed.   

End CostTheory.


Ltac costtac_one :=
  match goal with
(* function cost *)
    | [|- _ ] => eapply cost_const 
    | [|- ?f (Ret _ ) _ ] => eapply cost_Ret
    | [|- ?f (@fst _ _ ) _ ] => eapply cost_fst
    | [|- ?f (@snd _ _) _ ] => eapply cost_snd
    | [|- ?f (@OC_Query _ _) _ ] => eapply cost_OC_Query
    | [|- ?f (@OC_Ret _ _ _) _ ] => eapply cost_OC_Ret
    | [|- ?f (@OC_Bind _ _ _ _) _ ] => eapply cost_OC_Bind_1
    | [|- forall a, ?f (OC_Bind a) _ ] => eapply cost_OC_Bind_2 
    | [|- ?f (fun a => (?f1 a, ?f2 a)) _ ] => eapply cost_compose_binary
    | [|- ?f (@pair _ _ ) _ ] => eapply cost_pair_1 
    | [|- forall a, ?f (@pair _ _ a) _ ] => eapply cost_pair_2 
    | [|- ?f (fun a => ?f1 (?f2 a)) _ ] => eapply cost_compose_unary
    | [|- ?f (fun a => ?f1 (?f2 (?f3 a)))  _ ] => eapply cost_compose_unary
    | [|- ?f (fun a => ?f1 (?f2 (?f3 (?f4 a))))  _ ] => eapply cost_compose_unary
    | [|- ?f (fun a => ?f1 (?f2 (?f3 (?f4 (?f5 a)))))  _ ] => eapply cost_compose_unary
    | [|- ?f (fun a => ?f1 (?f2 (?f3 (?f4 (?f5 (?f6 a))))))  _ ] => eapply cost_compose_unary
        
(* Comp cost *)
    | [|- ?f1 ?f2 (Rnd _ ) _ ] => econstructor
    | [|- ?f1 ?f2 (Ret _ _ ) _ ] => econstructor
    | [|- ?f1 ?f2 (Bind _ _) _ ] => econstructor
      
(* OracleComp cost *)
    | [|- ?f1 ?f2 ?f3 (OC_Bind _ _) _ ] => econstructor
    | [|- ?f1 ?f2 ?f3 (OC_Run _ _ _ _ _ _ ) _ ] => econstructor
    | [|- ?f1 ?f2 ?f3 (@OC_Ret _ _ _ _  ) _ ] => econstructor
    | [|- ?f1 ?f2 ?f3 (OC_Query _ _ ) _ ] => econstructor
      
  end.

Ltac costtac := repeat (costtac_one).

Require Import fcf.Asymptotic.

Definition poly_time_nonuniform_oc(cost : FunctionCostModel)(A B C : nat -> Set)(c : forall n, OracleComp (A n) (B n) (C n)) := 
  exists (f : nat -> nat -> nat), 
    (forall o, polynomial o -> 
      polynomial (fun n => f n (o n))) /\
    forall n, (oc_cost cost (comp_cost cost)) _ _ _ (c n) (f n).

Definition polynomial_queries_oc(A B C : nat -> Set)(c : forall n, OracleComp (A n) (B n) (C n)) :=
  exists q, 
    polynomial q /\ 
    forall n, queries_at_most (c n) (q n).
    
Definition admissible_oc(cost : FunctionCostModel)(A B C : nat -> Set)(c : forall n, OracleComp (A n) (B n) (C n)) := 
  (forall n, well_formed_oc (c n)) /\
  poly_time_nonuniform_oc cost _ _ _ c /\
  polynomial_queries_oc _ _ _ c.
  
Definition poly_time_nonuniform_oc_func_2(cost : FunctionCostModel)(A B C D E: nat -> Set)(c : forall n, A n -> B n -> OracleComp (C n) (D n) (E n)) := 
  exists (f1 : nat -> nat -> nat), 
    exists (f2 : nat -> nat),
    (forall o, polynomial o -> 
      polynomial (fun n => f1 n (o n))) /\
    polynomial f2 /\
    forall n, 
      cost _ _ (fun p => @c n (fst p) (snd p)) (f2 n) /\
      (forall x y, (oc_cost cost (comp_cost cost)) _ _ _ (@c n x y) (f1 n)).

Definition polynomial_queries_oc_func_2(A B C D E : nat -> Set)(c : forall n, A n -> B n -> OracleComp (C n) (D n) (E n)) :=
  exists q, 
    polynomial q /\ 
    forall n a b, queries_at_most (c n a b) (q n).

Definition admissible_oc_func_2(cost : FunctionCostModel)(A B C D E : nat -> Set)(c : forall n, A n -> B n -> OracleComp (C n) (D n) (E n)) := 
  (forall n a b, well_formed_oc (c n a b)) /\
  poly_time_nonuniform_oc_func_2 cost _ _ _ _ _ c /\
  polynomial_queries_oc_func_2 _ _ _ _ _ c.