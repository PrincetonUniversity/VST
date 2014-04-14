(**************************************************************************)
(*  This is part of ATBR, it is distributed under the terms of the        *)
(*         GNU Lesser General Public License version 3                    *)
(*              (see file LICENSE for more details)                       *)
(*                                                                        *)
(*       Copyright 2009-2011: Thomas Braibant, Damien Pous.               *)
(**************************************************************************)

(** This file builds some machinery to deal with reflection and
   views.

   Through the development, we define several efficient comparison
   functions that produce results in [bool] or [comparison]. For
   example, [eq_nat_bool] efficiently computes the equality on [nat],
   but is not easy to manipulate.
   
   We provide some tools to deal with these kind of functions:

   - [*_analyse] tactics: using a "view" mechanism, we associate to
   boolean or comparison functions the relation they describe. The
   [*_analyse] tactics will perform case destructions.
   
   - [*_prop] tactics: Through the development, we declare several
   lemmas as hints for autorewrite libraries, in order to transform,
   e.g., [eq_nat_bool x y = true] into [x = y].
   
   - [bool_simpl] tactic: Through the development, we declare several
   simplification lemmas, in order to transform, e.g., [eq_nat_bool x x]
   into [true]
   
   *)


Require Import Common.
Require Export Bool.
Require Import Equality Program Sumbool Peano.


                               (***********)
                               (* analyse *)
                               (***********)

Class Type_View {A} (f : A) := { 
  type_view_ty : Type; 
  type_view : type_view_ty 
}.

(* TOTHINK: a-t'on vraiment besoin de passer par les instances, puisqu'on a toujours le lemme dans la main !? *)
Ltac type_view f :=
(** Find the view associated with [f] *)
  let prf := constr:(type_view (f:=f)) in
    on_call f ltac:(fun c =>
      match c with
          | context args [ f ] =>
            let ind_app := context args [ prf ] in
              destruct ind_app
      end).
  
Inductive compare_spec {A} eq lt (x y : A) : comparison -> Prop :=
| compare_spec_lt : lt x y -> compare_spec eq lt x y Lt
| compare_spec_eq : eq x y -> compare_spec eq lt x y Eq
| compare_spec_gt : lt y x -> compare_spec eq lt x y Gt.

(** computationally efficient equality and comparison of natural numbers *)
Fixpoint eq_nat_bool a b :=
  match (a,b) with 
    | (S n, S p) => eq_nat_bool n p
    | (O , O) => true
    | _ => false
  end.

Fixpoint le_lt_bool a b :=
  match (a,b) with 
    | (O , _) => true
    | (S n, S p) => le_lt_bool n p
    | _ => false
  end.

Lemma eq_nat_spec: forall a b, reflect (a=b) (eq_nat_bool a b).  
Proof.
  induction a; intros [|b]; simpl; try constructor; auto.
  case (IHa ( b));  intros H; subst;  constructor; auto.
Qed.

Lemma le_nat_spec : forall a b, reflect (le a b) (le_lt_bool a b).
Proof.  
  induction a; intros [|b]; simpl; try constructor; auto with arith.
  case (IHa ( b));  intros H; subst;  constructor; auto with arith.
Qed.

Instance eq_nat_view : Type_View eq_nat_bool := { type_view := eq_nat_spec }.
Instance le_nat_view : Type_View le_lt_bool := { type_view := le_nat_spec }.

Ltac nat_analyse := 
  repeat (
    try (type_view eq_nat_bool; try subst; try omega_false);
    try (type_view le_lt_bool; try subst; try omega_false)
  ).


(** same thing for positive numbers  *)
Fixpoint eq_pos_bool x y := 
  match x,y with 
    | xH, xH => true
    | xO a, xO b => eq_pos_bool a b
    | xI a, xI b => eq_pos_bool a b
    | _, _ => false
  end.

Lemma eq_pos_spec : forall n m, reflect (n=m) (eq_pos_bool n m). 
Proof. 
  induction n; intros [m|m|]; simpl; try constructor; try congruence.
  case (IHn m); intro; subst; constructor; congruence.
  case (IHn m); intro; subst; constructor; congruence.
Qed.

Instance eq_pos_view : Type_View eq_pos_bool := { type_view := eq_pos_spec }.

Ltac pos_analyse := repeat type_view eq_pos_bool.


(** same thing for booleans  *)
Definition eq_bool_bool := Bool.eqb.

Lemma eq_bool_spec : forall a b, reflect (a=b) (eq_bool_bool a b).
Proof.
  intros [|] [|]; simpl; constructor; firstorder.
Qed.

Instance eq_bool_view : Type_View eq_bool_bool := { type_view := eq_bool_spec }.

Ltac bool_analyse := repeat type_view eq_bool_bool.



                            (************)
                            (* nat_prop *)
                            (************)

Lemma eq_nat_bool_true : forall x y, eq_nat_bool x y = true <-> x = y. 
Proof. intros. nat_analyse; intuition discriminate. Qed.
Lemma eq_nat_bool_false : forall x y, eq_nat_bool x y = false <-> x <> y. 
Proof. intros. nat_analyse; intuition discriminate. Qed.
Lemma le_lt_bool_true : forall x y, le_lt_bool x y = true <-> x <= y. 
Proof. intros. nat_analyse; intuition. Qed.
Lemma le_lt_bool_false : forall x y, le_lt_bool x y = false <-> y < x. 
Proof. intros. nat_analyse; intuition. Qed.

Hint Rewrite eq_nat_bool_true eq_nat_bool_false le_lt_bool_true le_lt_bool_false : nat_prop.
Ltac nat_prop := autorewrite with nat_prop in *.



                           (**************)
                           (* bool_simpl *)
                           (**************)

(** * [bool_simpl] is a tactic that simplifies boolean operations in the context and in the goal
      The database bool_simpl should be enriched with lemmas such as [forall x, eqb x x = true], 
      which is done in Numbers.v
*)
Hint Rewrite 
  orb_false_r                    (** b || false -> b *)
  orb_false_l                    (** false || b -> b *)
  orb_true_r                     (** b || true  -> true *)
  orb_true_l                     (** true || b  -> true  *)
  andb_false_r                   (** b && false -> false *)
  andb_false_l                   (** false && b -> false *)
  andb_true_r                    (** b && true  -> b *)
  andb_true_l                    (** true && b  -> b  *)
  negb_orb                       (** negb (b || c) -> negb b && negb c *)
  negb_andb                      (** negb (b && c) -> negb b || negb c *)
  negb_involutive                (** negb (negb b) -> b *)
  : bool_simpl.

Hint Rewrite <- andb_lazy_alt : bool_simpl. (** a &&& b -> a && b *)
Hint Rewrite <- orb_lazy_alt : bool_simpl.  (** a ||| b -> a || b *)
 
Ltac bool_simpl := autorewrite with bool_simpl in *.

Lemma eq_nat_bool_refl: forall x, eq_nat_bool x x = true. 
Proof. intro. nat_prop. reflexivity. Qed.
Lemma le_lt_bool_refl: forall x, le_lt_bool x x = true. 
Proof. intro. nat_prop. auto with arith. Qed.

Hint Rewrite  eq_nat_bool_refl le_lt_bool_refl: bool_simpl.



                           (*******************)
                           (* bool_connectors *)
                           (*******************)

(** * [bool_connectors ] takes hypothesis like [((x && y) || negb z) = true] and transforms them into 
      [? : (x = true /\ y = true) \/ (~ z = true)]. *)

Lemma andb_false_iff : forall b1 b2:bool, b1 && b2 = false <-> (b1 = false \/ b2 = false). 
Proof. intros [|] [|]; firstorder. Qed.
Lemma andb_true_iff : forall b1 b2:bool, b1 && b2 = true <-> (b1 = true /\ b2 = true). 
Proof. intros [|] [|]; firstorder. Qed.

Lemma orb_false_iff : forall b1 b2:bool, b1 || b2 = false <-> (b1 = false /\ b2 = false). 
Proof. intros [|] [|]; firstorder. Qed.
Lemma orb_true_iff : forall b1 b2:bool, b1 || b2 = true <-> (b1 = true \/ b2 = true). 
Proof. intros [|] [|]; firstorder. Qed.

Lemma negb_true  : forall b, negb b = true <-> b = false. 
Proof. intros [|]; firstorder. Qed.
Lemma negb_false  : forall b, negb b = false <-> b = true. 
Proof. intros [|]; firstorder. Qed.
Lemma eq_not_negb  : forall b c, b = c <-> ~ (b = negb c). 
Proof. intros [|] [|]; firstorder. Qed.

Hint Rewrite andb_false_iff andb_true_iff orb_false_iff orb_true_iff negb_true negb_false : bool_connectors.

Ltac bool_connectors := autorewrite with bool_connectors in *.

Lemma bool_prop_iff : forall b1 b2, b1 = b2 <-> (b1 = true <-> b2 = true). 
Proof. intros [|] [|]; firstorder. Qed.


                           (*************)
                           (* decompose *)
                           (*************)

(** [completer tac] simplfies the layout of the hypothesis, and try to
   saturate the context with hypothesis. It is adapted from A. Chlipala
*)


Ltac notHyp P :=
  match goal with
    [ _ : P |- _ ] => fail 1
    | _ => match P with 
             | ?P1 /\ ?P2 => first [notHyp P1 | notHyp P2 | fail 2]
             | _ => idtac
           end
  end.

Ltac extend pf :=
  let t := type of pf in notHyp t; generalize pf; intro.

Ltac completer tac:=
  repeat match goal with 
    | H : False |- _ => apply False_ind; exact H
    | H : ?P \/ ?Q |- _ => destruct H as [?|?]
    | [ |- _ /\ _ ] => constructor 
    | [ |- _ <-> _ ] => constructor
    | [ |- _ -> _] => intro
    | [H : _ /\ _ |- _] => destruct H
    | [H : ?P -> ?Q, H' : ?P |- _] => generalize (H H'); clear H; intro H 
    | [ |- forall x, _] => intro
    | [H : forall x, ?P x -> _ , H' : ?P ?X |- _ ]=> extend (H X H')
    | [H : exists x, _ |- _ ] => destruct H
    | [H : ?x = ?y |- _ ]  => subst H
    | _ => tac
  end.

