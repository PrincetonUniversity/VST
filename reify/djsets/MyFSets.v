(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** This file defines the finite sets and finite maps modules we need
   in this development.

   TODO: Coq standard library has evolved in v8.3, so that (parts of)
   this file might no longer be useful.  *)

Require Export FMaps FSets.
Require Import List.
Require Import NArith.

(** Functors to perform "transparent sealing". *)
Module FSetHide (X : FSetInterface.S).
  Include X.
End FSetHide.

Module FMapHide (X : FMapInterface.S).
  Include X.
End FMapHide.


(** Building efficient ordered types  *)
Module Type OrderedTypeAlt.
 Parameter t : Type.

 Parameter compare : t -> t -> comparison.
 Infix "?=" := compare (at level 70, no associativity).

 Parameter compare_sym : forall x y, (y?=x) = CompOpp (x?=y).
 Parameter compare_trans : forall c x y z, (x?=y) = c -> (y?=z) = c -> (x?=z) = c.
 Parameter reflect : forall x y, x ?= y = Eq -> x = y.
End OrderedTypeAlt. 

Module Nat_as_OTA <: OrderedTypeAlt.
  Definition t := nat.
  Fixpoint compare x y := 
    match x,y with 
      | O,O => Eq
      | O,_ => Lt
      | _,O => Gt
      | S x, S y => compare x y
    end.
  Lemma compare_sym: forall x y, compare y x = CompOpp (compare x y). 
  Proof. induction x; intros y; destruct y; simpl; auto. Qed.
  Lemma compare_trans: forall c x y z, compare x y = c -> compare y z = c -> compare x z = c. 
  Proof. 
    intros c x. revert c.
    induction x; intros c y z; destruct y; simpl; intro H; auto; subst; try discriminate H;
      destruct z; simpl; intro H'; eauto; try discriminate H'.
  Qed.
  Lemma reflect: forall x y, compare x y = Eq -> x = y.
  Proof. induction x; intros y; destruct y; simpl; intro H; auto; discriminate. Qed.
End Nat_as_OTA.


Module Pos_as_OTA <: OrderedTypeAlt.
  Definition t := positive.
  Fixpoint compare x y := 
    match x,y with 
      | xH, xH => Eq
      | xH, _ => Lt
      | _, xH => Gt
      | xO a, xO b => compare a b
      | xI a, xI b => compare a b
      | xI a, xO b => Gt
      | xO a, xI b => Lt
    end.
  Lemma compare_sym: forall x y, compare y x = CompOpp (compare x y). 
  Proof. induction x; intros y; destruct y; simpl; auto. Qed.
  Lemma compare_trans: forall c x y z, compare x y = c -> compare y z = c -> compare x z = c. 
  Proof. 
    intros c x. revert c.
    induction x; intros c y z; destruct y; simpl; intro H; auto; subst; try discriminate H;
      destruct z; simpl; intro H'; eauto; try discriminate H'.
  Qed.
  Lemma reflect: forall x y, compare x y = Eq -> x = y.
  Proof. 
    induction x; intros y; destruct y; simpl; intro H; auto; try discriminate.
    apply IHx in H. subst. reflexivity.
    apply IHx in H. subst. reflexivity.
  Qed.
End Pos_as_OTA.



(** Lexicographically ordered lists as [OrderedTypeAlt] *)
Module ListOrderedTypeAlt(O: OrderedTypeAlt) <: OrderedTypeAlt.
  Definition t := list O.t.
  Fixpoint compare (m n: t) :=
    match m,n with
      | nil,nil => Eq
      | nil,_ => Lt
      | _,nil => Gt
      | x::m, y::n => 
        match O.compare x y with
          | Eq => compare m n
          | r => r
        end
    end.
  Lemma compare_sym: forall x y, compare y x = CompOpp (compare x y).
  Proof.
    induction x; intros y; destruct y; simpl; auto.
    rewrite O.compare_sym.
    destruct (O.compare a t0); simpl; auto.  
  Qed.
  Lemma compare_trans: forall c x y z, compare x y = c -> compare y z = c -> compare x z = c. 
  Proof.
    intros c x. revert c.
    induction x; intros c y z; destruct y; simpl; intro H; auto; subst; try discriminate H;
      destruct z; simpl; intro H'; eauto; try discriminate H'.
    revert H'.
    case_eq (O.compare a t0); case_eq (O.compare t0 t1); intros Hat0 Ht01 H'; 
      (discriminate H' || (try rewrite <- H'));
      try rewrite (O.compare_trans _ _ _ _ Ht01 Hat0); eauto. 
     (* here we do not need the [reflect] lemma *)
     apply O.reflect in Ht01. subst. rewrite Hat0. trivial.
     apply O.reflect in Ht01. subst. rewrite Hat0. trivial.
     apply O.reflect in Hat0. subst. rewrite Ht01. trivial.
     apply O.reflect in Hat0. subst. rewrite Ht01. trivial.
  Qed.
  Lemma reflect: forall x y, compare x y = Eq -> x = y.
  Proof. 
    induction x; intros y; destruct y; simpl; intro H; auto; try discriminate.
    revert H.
    case_eq (O.compare a t0); intros H' H; try discriminate.
    apply O.reflect in H'. apply IHx in H.  congruence.
  Qed.
End ListOrderedTypeAlt.
 
Module PairOrderedTypeAlt(O U: OrderedTypeAlt) <: OrderedTypeAlt.
  Definition t := (O.t * U.t)%type.
  Definition compare (m n: t) :=
    let '(mo,mu) := m in
      let '(no,nu) := n in
        match O.compare mo no with
          | Eq => U.compare mu nu
          | r => r
        end.
  Lemma compare_sym: forall x y, compare y x = CompOpp (compare x y). 
  Proof.
    intros [x x'] [y y']; simpl.
    rewrite O.compare_sym, U.compare_sym. destruct (O.compare x y); reflexivity.
  Qed.
  Lemma compare_trans: forall c x y z, compare x y = c -> compare y z = c -> compare x z = c.
    intros c [x x'] [y y'] [z z']; simpl.
    case_eq (O.compare x y); case_eq (O.compare y z); intros xy yz; simpl;
      try rewrite (O.compare_trans _ _ _ _ yz xy); intros; subst; try discriminate; auto.
      eauto using U.compare_trans.
      apply O.reflect in yz; subst. rewrite xy. trivial.
      apply O.reflect in yz; subst. rewrite xy. trivial.
      apply O.reflect in xy; subst. rewrite yz. trivial.
      apply O.reflect in xy; subst. rewrite yz. trivial.
  Qed.
  Lemma reflect: forall x y, compare x y = Eq -> x = y.
  Proof.
    intros [x x'] [y y']. simpl.
    case_eq (O.compare x y); intro xy; try apply O.reflect in xy;
    case_eq (U.compare x' y'); intro xy'; try apply U.reflect in xy';
      intro; try discriminate; subst; auto.
  Qed.
End PairOrderedTypeAlt.




(** Here is an efficient definition of [OrderedType_from_Alt] : an
   [abstract] is used in the definition of compare, to avoid useless reductions.*)

 Module OrderedType_from_Alt (O:OrderedTypeAlt) <: OrderedType.  
 Import O.  
 Definition t := t.

 Definition eq x y := (x?=y) = Eq.
 Definition lt x y := (x?=y) = Lt.

 Lemma eq_refl : forall x, eq x x.
 Proof.
 intro x.
 unfold eq.
 assert (H:=compare_sym x x).
 destruct (x ?= x); simpl in *; try discriminate; auto.
 Qed.

 Lemma eq_sym : forall x y, eq x y -> eq y x.
 Proof. 
 unfold eq; intros.
 rewrite compare_sym.
 rewrite H; simpl; auto.
 Qed.

 Definition eq_trans := (compare_trans Eq).

 Definition lt_trans := (compare_trans Lt).

 Lemma lt_not_eq : forall x y, lt x y -> ~eq x y.
 Proof.
 unfold eq, lt; intros.
 rewrite H; discriminate.
 Qed.

 Definition compare : forall x y, Compare lt eq x y.
 Proof.
 intros.
 case_eq (x ?= y); intros.
 apply EQ; trivial.
 apply LT; trivial.
 (* Here the abstract prevent useless reductions *)
 apply GT; abstract (red; rewrite compare_sym; rewrite H; trivial). 
 Defined.

 Definition eq_dec : forall x y, { eq x y } + { ~ eq x y }.
 Proof.
 intros; unfold eq.
 case (x ?= y); [ left | right | right ]; auto; discriminate.
 Defined.

End OrderedType_from_Alt. 


Module PairOrderedType(O U: OrderedTypeAlt) <: OrderedType.
  Module P := PairOrderedTypeAlt O U.
  Include OrderedType_from_Alt P.
End PairOrderedType.



Module Nat_as_OT := OrderedType_from_Alt Nat_as_OTA.
Module Pos_as_OT := OrderedType_from_Alt Pos_as_OTA.

