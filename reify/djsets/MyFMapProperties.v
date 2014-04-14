(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** Handler for FMap properties, provides the [find_tac] tactic. *)

Require Import FMaps.
Require Import Common.
Require Import BoolView.

Module MyMapProps (X : FMapInterface.S).
  Include FMapFacts.Properties X.    
  Include F.

  Import X.
  
  Lemma mapsto_in: forall T x (y: T) d, MapsTo x y d -> In x d.
  Proof. intros. exists y. assumption. Qed.

  Lemma in_add_1: forall T x (y: T) d, In x (add x y d).
  Proof. intros. exists y. auto with map. Qed.

  Lemma in_add_2: forall T x y (z: T) d, In x d -> In x (add y z d).
  Proof.
    intros. destruct (E.eq_dec y x). 
     exists z. auto with map.  
     destruct H as [w ?]. exists w. auto with map. 
  Qed. 

  Hint Resolve mapsto_in in_add_1 in_add_2 : map.

  Inductive find_spec_ind A k s : option A -> Prop :=
  | find_spec_1 : forall x, MapsTo k x s -> find_spec_ind A k s (Some x)
  | find_spec_2 : ~In k s -> find_spec_ind A k s (None).

  Lemma find_spec : forall A k s, find_spec_ind A k s (find k s).
  Proof.
    intros. case_eq (find k s); intros; constructor; auto with map.
    intros [x Hx]. apply find_1 in Hx. rewrite H in Hx. discriminate.
  Qed.
  
  Instance find_view : Type_View find := {type_view := find_spec}. 
  
  (** * Destructor for find *)
  Ltac find_analyse :=
    repeat type_view find.
  
  Ltac find_tac :=
     repeat (
       match goal with 
         | |- ?x = ?x => reflexivity                 
           
         | H : @MapsTo _   ?s ?x1 ?eps, H' : @MapsTo _ ?s ?x2 ?eps |- _ => 
           let H'' := fresh in 
             assert (H'' : x1 = x2) by (eapply MapsTo_fun; eauto); clear H'; destruct H''
         | H : @MapsTo _ ?s ?x (@add _ ?t ?y ?eps) |- _ => 
           revert H; map_iff; intros [[? ?] | [? ?]] 
         | H : @MapsTo _ ?x ?b (@map _ _ ?f ?m) |- _ =>
           rewrite map_mapsto_iff in H; 
             destruct H as [?x [?H ?H]]
         | H : ~(@In _ ?x (@map _ _ ?f ?m)) |- _ => rewrite map_in_iff in H
         | H : @In _ ?x (map ?f ?m) |- _ => rewrite map_in_iff in H
         | H :  ~ (@In _ ?k (@add _ ?k ?y ?s)) |- _ => exfalso; apply H; clear H; map_iff; firstorder
         | H :  ~ (@In _ ?k (@add _ ?k' ?y ?s)), H' : @MapsTo _ ?k ?x ?s |- _ => 
           exfalso; apply H; clear H; map_iff; firstorder
         | H :  ~ (@In _ ?k ?s), H' : @MapsTo _ ?k ?x ?s |- _ => 
           exfalso; apply H; clear H; map_iff; firstorder
         | H :  ~ (@In _ ?k (@add  _ ?k' ?y ?s)) |- _ => revert H; rewrite add_in_iff; intro H
         | H : ?s = ?s |- _ => clear H
         | H : ?s <> ?s |- _ => elim H; reflexivity
         | H : ?s = ?t |- _ => subst                
       end); trivial.

End MyMapProps.
