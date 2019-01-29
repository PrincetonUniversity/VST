(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* The syntax of computations.  *)

Set Implicit Arguments.

Require Export Bvector.
Require Export List.
Require Export FCF.Blist.
Require Export FCF.EqDec.
Require Import FCF.Fold.


Inductive Comp : Set -> Type :=
| Ret : forall (A : Set), eq_dec A -> A -> Comp A
| Bind : forall (A B : Set), Comp B -> (B -> Comp A) -> Comp A
| Rnd : forall n, Comp (Bvector n)
| Repeat : forall (A : Set), Comp A -> (A -> bool) -> Comp A.


(* syntactic equality for Comp *)
Inductive Comp_eq : forall (A : Set), Comp A -> Comp A -> Prop :=
  | Comp_eq_Ret : forall (A : Set)(pf1 pf2 : eq_dec A)(a : A),
    Comp_eq (Ret pf1 a) (Ret pf2 a)
  | Comp_eq_Bind : forall (A B : Set)(c1x c1y : Comp B)(c2x c2y : B -> Comp A),
    Comp_eq c1x c1y ->
    (forall b, (Comp_eq (c2x b) (c2y b))) ->
    Comp_eq (Bind c1x c2x) (Bind c1y c2y)
  | Comp_eq_Rnd : forall n,
    Comp_eq (Rnd n) (Rnd n)
  | Comp_eq_Repeat : forall (A : Set)(c1 c2 : Comp A)(P1 P2 : A -> bool),
    Comp_eq c1 c2 ->
    (forall a, P1 a = P2 a) ->
    Comp_eq (Repeat c1 P1) (Repeat c2 P2).

Hint Constructors Comp_eq : comp.

Theorem Comp_eq_refl : forall (A : Set)(c : Comp A),
  Comp_eq c c.

  induction c; intuition; eauto with comp.
Qed.

Lemma Bvector_exists : forall n,
  Bvector n.

  induction n; intuition.
  econstructor.
  econstructor.
  econstructor.
  eapply IHn.
Qed.

Lemma comp_base_exists : forall (A : Set),
  Comp A ->
  A.

  induction 1; intuition;
  eauto using Bvector_exists.
Qed.

Require Import FCF.EqDec. 

Lemma comp_EqDec : forall (A : Set),
  Comp A ->
  EqDec A.

  induction 1; intuition.
  exists (fun a1 a2 => if e a1 a2 then true else false).
  intuition.
  destruct (e x y); simpl in *; trivial. discriminate.
  subst.
  destruct (e y y); trivial; congruence.

  eapply H.
  eapply comp_base_exists; eauto.
Qed.

Lemma comp_eq_dec : forall (A : Set),
  Comp A ->
  eq_dec A.

  induction 1; intuition.
  eapply H.
  eapply comp_base_exists; eauto.
  specialize (@Bvector_eq_dec n); intuition.
Qed.

Lemma bind_EqDec : forall (A B : Set),
  Comp B ->
  (B -> Comp A) ->
  EqDec A.

  intuition.
  eapply comp_EqDec.
  eapply X0.
  eapply comp_base_exists.
  eauto.

Qed.

Lemma bind_eq_dec : forall (A B : Set),
  Comp B ->
  (B -> Comp A) ->
  eq_dec A.

  intuition.
  eapply comp_eq_dec.
  eapply X0.
  eapply comp_base_exists.
  eauto.

Qed.

(*
Instance comp_eq_dec : forall (A : Set),
  Comp A ->
  EqDec A.

eapply comp_base_EqDec.
Qed.

Instance bind_EqDec : forall (B A : Set),
  Comp B ->
  (B -> Comp A) ->
  EqDec A.

intuition.
eapply comp_EqDec.
eapply X0.
eapply comp_base_exists.
eauto.
Qed.

*)



Fixpoint getSupport(A : Set)(c : Comp A) : list A :=
  match c with
    | Ret _ a => a :: nil
    | Bind c1 c2 => getUnique (flatten (map (fun b => (getSupport (c2 b))) (getSupport c1))) (bind_eq_dec c1 c2)
    | Rnd n => getAllBvectors n
    | Repeat c1 P => (filter P (getSupport c1))
  end.

(* Only well-formed computations are guaranteed to terminate. *)
Inductive well_formed_comp : forall (A : Set), Comp A -> Prop :=
  | well_formed_Ret :
    forall (A : Set)(pf : eq_dec A)(a : A),
      well_formed_comp (Ret pf a)
  | well_formed_Bind : 
    forall (A B : Set)(c1 : Comp B)(c2 : B -> Comp A),
      well_formed_comp c1 ->
      (forall b, In b (getSupport c1) -> well_formed_comp (c2 b)) ->
      well_formed_comp (Bind c1 c2)
   | well_formed_Rnd : forall n,
     well_formed_comp (Rnd n)
   | well_formed_Repeat :
     forall (A : Set)(eqd : eq_dec A)(c : Comp A) P b,
      well_formed_comp c ->
      In b (filter P (getSupport c)) ->
      well_formed_comp (Repeat c P).

Delimit Scope comp_scope with comp.

Theorem lt_eq_false : 
  forall n,
    n < n -> False.

  destruct n; intuition.

Qed.

Lemma length_nz_exists : forall (A : Type)(ls : list A),
                           length ls > 0 ->
                           exists a, In a ls.
  
  destruct ls; intuition; simpl in *.
  exfalso.
  eapply lt_eq_false; eauto.
  
  econstructor; eauto.
Qed.


Theorem getSupport_length_nz : forall (A : Set)(c : Comp A),
  well_formed_comp c ->
  length (getSupport c) > 0.
  
  induction 1; intuition; simpl in *.
  
  apply length_getUnique_nz.
  apply length_nz_exists in IHwell_formed_comp.
  destruct IHwell_formed_comp.
  
  eapply length_flatten_nz.
  eapply in_map_iff.
  econstructor; intuition; eauto.
  eapply H1.
  trivial.

  apply getAllBvectors_length_nz.

  destruct (filter P (getSupport c)); simpl in *; intuition.
Qed.

Lemma filter_NoDup : forall (A : Set)(ls : list A)(P : A -> bool),
  NoDup ls ->
  NoDup (filter P ls).

  induction ls; intuition; simpl in *.
  inversion H; clear H; subst.
  case_eq (P a); intuition.
  econstructor; intuition.
  eapply H2.
  eapply filter_In; eauto.

Qed.

Lemma getSupport_NoDup : forall (A : Set)(c : Comp A),
  NoDup (getSupport c).

  induction c; intuition; simpl in *.

  econstructor.
  apply in_nil.
  econstructor.

  eapply getUnique_NoDup.

  eapply getAllBvectors_NoDup.

  eapply filter_NoDup.
  trivial.

Qed. 

Lemma getSupport_Bind_In : forall (A B : Set) (c : Comp B)(f : B -> Comp A) a,
  In a (getSupport (Bind c f)) ->
  exists b, 
    In b (getSupport c) /\
    In a (getSupport (f b)).
  
  intuition.
  simpl in *.
  apply in_getUnique_if in H.
  eapply in_flatten in H.
  destruct H.
  intuition.
  apply in_map_iff in H0.
  destruct H0.
  intuition.
  subst.
  econstructor.
  intuition;
    eauto.
  
Qed.

Ltac pairInv :=
  match goal with 
    | [H : (_, _) = (_, _) |-_ ] => inversion H; clear H; subst
  end.

Ltac destruct_exists :=
  match goal with
    | [H : exists x, _ |- _ ] =>
      destruct H
  end.

Theorem getSupport_In_Ret : 
  forall (A : Set)(eqd : eq_dec A) x a,
    In x (getSupport (Ret eqd a)) ->
    x = a.

  intuition.

  simpl in *.
  intuition.

Qed.


Theorem getSupport_In_Seq :
  forall (A B : Set)(c : Comp A)(f : A -> Comp B) b a,
    In a (getSupport c) ->
    In b (getSupport (f a)) ->
    In b (getSupport (Bind c f)).
  
  intuition.
  simpl.
  eapply in_getUnique.
  eapply in_flatten.
  econstructor.
  split.
  eapply in_map_iff.
  econstructor.
  split.
  eauto.
  eauto.
  trivial.
Qed.

Local Open Scope comp_scope.

Definition maybeBind(A B : Type)(opt_a : option A)(f : A -> B) : option B :=
  match opt_a with
    | None => None
    | Some a => Some (f a)
  end.

Inductive OracleComp : Set -> Set -> Set -> Type :=
| OC_Query : forall (A B : Set), A -> OracleComp A B B
| OC_Run : forall (A B C A' B' S : Set), 
  EqDec S ->
  EqDec B ->
  EqDec A ->
  OracleComp A B C ->
  (S -> A -> OracleComp A' B' (B * S)) ->
  S ->
  OracleComp A' B' (C * S)
| OC_Ret : forall A B C, Comp C -> OracleComp A B C
| OC_Bind : forall A B C C', OracleComp A B C -> (C -> OracleComp A B C') -> OracleComp A B C'.

Theorem oc_base_exists : forall (A B C : Set), OracleComp A B C -> (A -> B) -> C.

  induction 1; intuition; simpl in *.
  eapply comp_base_exists; intuition.

Qed.

Theorem oc_EqDec : forall (A B C: Set),  OracleComp A B C -> (A -> B) -> (A -> EqDec B) -> EqDec C.

  induction 1; intuition.
  eapply pair_EqDec; intuition.
  eapply IHX; intuition.
  apply oc_base_exists in X1;
  intuition.
  eapply comp_EqDec; intuition.

  eapply H.
  eapply oc_base_exists;
  eauto.
  intuition.
  intuition.
  
Qed.


Lemma well_formed_val_exists : 
  forall (A : Set)(c : Comp A),
    well_formed_comp c ->
    exists x, In x (getSupport c).
  
  induction 1; intuition; simpl in *.
  
  econstructor; intuition.
  
  destruct IHwell_formed_comp.
  edestruct H1; eauto.
  econstructor.
  eapply in_getUnique.
  eapply in_flatten.
  econstructor.
  split.
  eapply in_map_iff.
  econstructor.
  split.
  eauto.
  eauto.
  eauto.

  exists (oneVector n).
  eapply in_getAllBvectors.
  
  econstructor.
  eauto.
Qed.
