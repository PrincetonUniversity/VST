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
Require Import FCF.ProgramLogic.
Require Import FCF.DistTacs.
Require Import FCF.NotationV1.

Local Open Scope rat_scope.
Local Open Scope comp_scope.

Hint Resolve true : inhabited.

Ltac prog_ret_l :=
  eapply comp_spec_eq_trans_l; [eapply comp_spec_left_ident | idtac].

Ltac prog_ret_r :=
  eapply comp_spec_eq_trans_r; [idtac | eapply comp_spec_symm; eapply comp_spec_consequence; [eapply comp_spec_left_ident | intuition] ].

Ltac prog_ret s :=
  match s with
    | leftc => prog_ret_l
    | rightc => prog_ret_r
  end.

Ltac prog_irr_l := 
  eapply comp_spec_irr_l; 
  [ intuition | wftac | intuition].
  
Ltac prog_irr_r := 
  eapply comp_spec_irr_r; 
    [ intuition | wftac | intuition].


Ltac prog_simp_1 := unfold setLet; try prog_ret_l; try prog_ret_r; cbv beta iota; destructLet. (* we only want to destruct identifiers, so we must cbv first*)

Ltac prog_simp := repeat prog_simp_1.

Ltac prog_simp_weak_1 := unfold setLet; try prog_ret_l.

Ltac prog_simp_weak := repeat prog_simp_weak_1.

Ltac prog_skip :=
      eapply comp_spec_seq; [eauto with inhabited | eauto with inhabited | (try eapply comp_spec_eq_refl; intuition) | intuition]; intuition; subst; prog_simp_weak; intuition.

Ltac prog_skip_pred p :=
      eapply (@comp_spec_seq _ _ p); [eauto with inhabited | eauto with inhabited | (eauto; try eapply comp_spec_eq_refl; intuition) | intuition]; intuition; subst; prog_simp_weak; intuition.

Ltac prog_skip_eq :=
  eapply comp_spec_seq_eq; [eauto with inhabited | eauto with inhabited | (eauto; try eapply comp_spec_eq_refl; intuition) | intuition]; intuition; subst; prog_simp_weak; intuition.


Ltac prog_inline_l :=
  match goal with
    | [ |- comp_spec _ (Bind (Bind ?c1 _ ) _) _] =>
      eapply comp_spec_eq_trans_l; 
        [eapply eq_impl_comp_spec_eq; intros ;
          [eapply (evalDist_assoc c1); intuition ]
          | idtac]
  end.


Ltac prog_inline_r :=
  match goal with 
    | [ |- comp_spec _ _ (Bind (Bind ?c1 _ ) _)] =>
      eapply comp_spec_eq_trans_r; 
        [idtac |
          eapply eq_impl_comp_spec_eq; intros ;
            [symmetry;  eapply (evalDist_assoc c1); intuition ]
        ] 
        end.

Ltac prog_inline s :=
  match s with
    | leftc => prog_inline_l
    | rightc => prog_inline_r
  end.

Ltac prog_inline_first_1 := try prog_inline_l; try prog_inline_r.
Ltac prog_inline_first := repeat (prog_simp_weak_1; prog_inline_first_1).

Ltac prog_swap_l :=
  match goal with
    | [ |- comp_spec _ (Bind ?c1 (fun x => (Bind ?c2 _))) _ ] => 
      eapply comp_spec_eq_trans_l; 
        [eapply comp_spec_eq_swap | idtac]
  end.

Ltac prog_swap_r :=
  match goal with
    | [ |- comp_spec _ _ (Bind ?c1 (fun x => (Bind ?c2 _))) ] => 
      eapply comp_spec_eq_trans_r; 
        [idtac | eapply comp_spec_eq_swap]
  end.

Ltac prog_swap side :=
  match side with
    | leftc => prog_swap_l
    | rightc => prog_swap_r
  end.

Ltac prog_at_l tac line :=
  match line with
    | O => tac rightc
    | S ?line' =>
      eapply comp_spec_eq_trans_l; [
        eapply comp_spec_seq_eq; eauto with inhabited; [eapply comp_spec_eq_refl | idtac]; intros; prog_at_l tac line'; eapply comp_spec_eq_refl | 
        idtac ]
  end.

Ltac prog_at_r tac line :=
  match line with
      | O => tac rightc
    | S ?line' =>
      eapply comp_spec_eq_trans_r; [idtac | 
        eapply comp_spec_seq_eq; eauto with inhabited; [eapply comp_spec_eq_refl | idtac]; intros; prog_at_r tac line'; eapply comp_spec_eq_refl]
  end.

Ltac prog_at tac side line :=
  match side with
    | leftc => prog_at_l tac (line)%nat
    | rightc => prog_at_r tac (line)%nat
  end.

Ltac prog_transitivity := eapply comp_spec_eq_trans_l.

Ltac prog_transitivity_r := eapply comp_spec_eq_trans_r.

Ltac prog_symmetry :=
  match goal with
    | [|- comp_spec eq _ _ ] => eapply comp_spec_eq_symm
  end.

Ltac prog_ident_expand_l :=
  prog_transitivity; [prog_symmetry; eapply comp_spec_right_ident | idtac].

Ltac prog_ident_expand_r :=
  prog_transitivity; [idtac | eapply comp_spec_right_ident].