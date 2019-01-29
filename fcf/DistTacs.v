(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)

(* Tactics used to manipulate and reason about distributions corresponding to computations. *)

Set Implicit Arguments.

Require Import FCF.Rat.
Require Import FCF.Comp.
Require Import FCF.DistRules.
Require Import FCF.DistSem.
Require Import FCF.StdNat.
Require Import FCF.Fold.
Require Import FCF.NotationV1.

Local Open Scope rat_scope.
Local Open Scope comp_scope.

Definition leftc := false.
Definition rightc := true.

(* wftac -- A tactic for deciding well-formedness *)
Hint Resolve posnat_pos : wftac.

Ltac pairInv := 
  match goal with
    | [H : (_, _) = (_, _) |- _] => 
      inversion H; clear H; subst
  end.

Ltac simp_ret := 
  match goal with
    | [H : In _ (getSupport (ret _)) |- _] => 
      simpl in H; intuition; pairInv
  end.

Ltac wftac_one :=
  match goal with
    | [|- well_formed_comp (Bind _ _) ] => eapply well_formed_Bind
    | [|- well_formed_comp (Ret _ _ ) ] => eapply well_formed_Ret
    | [|- well_formed_comp (Rnd _) ] => eapply well_formed_Rnd
    | [|- well_formed_comp (let (_,_) := ?y in _ ) ] => destruct y
    | [|- well_formed_comp (if ?x then _ else _) ] => destruct x
    | [|- @well_formed_oc _ _ _ _ ] => econstructor
  end.
  
Ltac wftac :=
  repeat (unfold setLet; intuition; eauto with wftac; try simp_ret; wftac_one).

Ltac destructLet_1 :=
  match goal with
    | [|- context[match ?x with | pair _ _ => _ end]] => destruct x
  end.

Ltac destructLet := repeat destructLet_1.


(* tactics *)

Ltac dist_ret_l :=
  match goal with
      | [ |- ?rel (evalDist (Bind (Ret _ _) ?f) _) _ ] => 
        eapply trans; [eapply (@evalDist_left_ident rel _ _ _ _ f); eauto with typeclass_instances | idtac]
  end.

Ltac dist_ret_r :=
  match goal with
      | [ |- ?rel _ (evalDist (Bind (Ret _ _) ?f) _) ] => 
        eapply trans; [idtac | eapply (@evalDist_left_ident (Basics.flip rel) _ _ _ _ f);  eauto with typeclass_instances]
  end.

Ltac dist_simp_1 := unfold setLet; try dist_ret_l; try dist_ret_r; cbv beta iota; destructLet. (* we only want to destruct identifiers, so we must cbv first*)

Ltac dist_simp := repeat dist_simp_1.

Ltac dist_simp_weak_1 := unfold setLet; try dist_ret_l.

Ltac dist_simp_weak := repeat dist_simp_weak_1.
    
Ltac dist_inline_l :=
  match goal with
      | [ |- ?rel _ _ ] => 
        eapply trans; [ eapply (@evalDist_assoc rel);  eauto with typeclass_instances | idtac]
  end; dist_simp_weak.

Ltac dist_inline_r :=
  match goal with
      | [ |- ?rel _ _ ] => 
        eapply trans; [ idtac | eapply (@evalDist_assoc (Basics.flip rel));  eauto with typeclass_instances]
  end; dist_simp_weak.

Ltac dist_inline s :=
  match s with
    | leftc => dist_inline_l
    | rightc => dist_inline_r
  end.

Ltac dist_ret s :=
  match s with
      | leftc => dist_ret_l
      | rightc => dist_ret_r
  end.

Ltac dist_inline_first_1 := try dist_inline_l; try dist_inline_r.
Ltac dist_inline_first := repeat (dist_simp_weak_1; dist_inline_first_1).

Ltac dist_swap_l :=
  match goal with
    | [ |- ?rel (evalDist (Bind ?c1 (fun x => (Bind ?c2 _))) _) _ ] => 
      eapply trans; [eapply (@evalDist_commute rel _ _ c1 c2); eauto with typeclass_instances | idtac]
  end.

Ltac dist_swap_r :=
  match goal with
    | [ |- ?rel _ (evalDist (Bind ?c1 (fun x => (Bind ?c2 _))) _) ] => 
      eapply trans; [ idtac | eapply (@evalDist_commute (Basics.flip rel) _ _ c1 c2);  eauto with typeclass_instances]
  end; dist_simp_weak.

Ltac dist_swap side :=
  match side with
    | leftc => dist_swap_l
    | rightc => dist_swap_r
  end.

Ltac dist_at_l tac line :=
  match line with
    | O => tac leftc
    | S ?line' => eapply trans; [ eapply rel_seq; intuition; dist_at_l tac line'; eapply refl; eapply eqRat_refl | idtac]
  end; dist_simp_weak.

Ltac dist_at_r tac line :=
  match line with
    | O => tac rightc
    | S ?line' =>
      eapply trans; [idtac |
                     eapply rel_seq; [ intuition | intuition; (dist_at_r tac line'); eapply refl; eapply eqRat_refl] ] 
  end; dist_simp.

Ltac dist_at tac side line :=
  match side with
    | leftc => dist_at_l tac (line)%nat
    | rightc => dist_at_r tac (line)%nat
  end.

Ltac dist_skip :=
  eapply evalDist_seq; [ idtac | eauto with typeclass_instances | idtac] ; intuition; subst; dist_simp_weak; intuition.

Ltac dist_irr_l :=
  eapply evalDist_irr_l; [  eauto with typeclass_instances | simpl | idtac] ; intuition; dist_simp_weak.

Ltac dist_irr_r :=
  eapply evalDist_irr_r; [  eauto with typeclass_instances | simpl | idtac] ; intuition; dist_simp_weak.


Lemma eqb_true_False : 
  forall (A : Set)(eqd : EqDec A) (a1 a2 : A),
    (eqb a1 a2 = true -> False) ->
    a1 <> a2.
  
  intuition.
  subst.
  eapply H.
  eapply eqb_refl.
  
Qed.

Ltac dist_compute_1 := 
  match goal with
    | [H : RatRel ?rel |- ?rel ?x ?x ] => eapply refl
    | [|- context[if ?a then _ else _ ]] => destruct a
    | [H : context[if ?a then _ else _ ] |- _] => destruct a
    | [H : eqb _ _ = true |- _ ] => rewrite eqb_leibniz in H; subst
    | [H : eqb _ _ = true -> False |- _] => apply eqb_true_False in H
    | [H1 : true = ?b -> False, H2 : false = ?b -> False |- _] => destruct b   
  end.

Ltac dist_compute_simp := simpl; unfold Fold.sumList; try rewrite <- ratAdd_0_l; try rewrite <- ratAdd_0_r; try rewrite ratMult_1_l; try rewrite ratMult_1_r; try rewrite ratMult_0_r; try rewrite ratMult_0_l.

Ltac dist_compute := repeat
  (dist_compute_simp; try dist_compute_1; try congruence; intuition).

Ltac dist_transitivity :=
  match goal with
    | [|- _ == _] => eapply eqRat_trans
    | [|- _ <= _] => eapply leRat_trans
  end.

Ltac dist_ident_expand_l :=
   dist_transitivity; [try apply eqRat_impl_leRat; symmetry; eapply evalDist_right_ident | idtac].

Ltac dist_ident_expand_r :=
   dist_transitivity; [idtac | eapply evalDist_right_ident].

