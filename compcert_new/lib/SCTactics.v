Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.

(*+ Santiago's Tactics*)
(* This is a collection of tactics that I find convenient *)
(* Thay come in no particular order *)

(* Apply any hypothesis containing some term t*)
Ltac ez_eapply t:=
  match goal with
  | [ H:context[t] |- _ ] => eapply H
  end.

(*Duplicate a hypothesis H*)
Ltac dup H:=
  let HH:= fresh "HH" in
  assert (HH:=H).
Ltac dup_as H name:=
  assert (name:=H).
Tactic Notation "dup" hyp(H) "as" ident(name):= dup_as H name.



(* neq is reflexive. *)
Definition neq_rel (A:Type): relation A:=
  fun (x y:A) => x <> y.
Global Instance Symmetric_neq: forall A, @Symmetric A (neq_rel A).
Proof. intros ? ? ? H ?. apply H; auto. Qed.

(* Duplicate hypothesis *)
Ltac duplicate H:= let HH := fresh "HH" in assert (HH:=H).

(* "Normal form"  hypothesis*)
Ltac destruct_and:=
  repeat match goal with
         | [ H: _ /\ _  |- _ ] => destruct H
         end.
Ltac reduce_and:=
  repeat match goal with
         | [ |- _ /\ _  ] => split
         end.

(* Stronger form of inversion. Similar to inv (from CompCert) *)
(* It inverts and rewrites every *new* equality*)
Ltac invert_with_continuation HH continuation:=
  first[
      match goal with
      | [ H: _ |- _ ] =>
        progress
          match H with
          | HH => idtac
          | _ => revert H; invert_with_continuation HH ltac:(intros H; continuation)
          end
      end |
      inversion HH; subst; continuation].
Ltac invert HH:= invert_with_continuation HH idtac.


(*Here is a version without continuation. It might be lighter *)
(* with memory usage. But it has a caveat:         *)
(* NOTE!!: This changes the names of hypothesis!!! *)
(* I considere good practice to not depend on names*)
Ltac revert_but HH:=
  repeat match goal with
         | [ H: _ |- _ ] =>
           progress
             match H with
             | HH => idtac
             | _ => revert H
             end
         end.
Ltac invert_fast HH:=
  revert_but HH;
  inversion HH; subst;
  intros.


(* Solves goals of the form [Equivalence t] *)
(* It works often when term t is simpl.  *)
(* Fails when the variables appear in a negative position *)
Ltac solve_Equivalence:=
  match goal with
  | [  |-  Equivalence ?t ] =>
    do 2 econstructor; intros;
    first[ reflexivity |
           symmetry; ez_eapply t |
           etransitivity; ez_eapply t
         ]
  end.


(** *Bookkeeping tactics*)

(** Claim what the current goal looks like *)
Ltac print_goal:= match goal with [|- ?G] => idtac G end.
Ltac errors_for_current current:= 
  idtac "That's not the current goal. " ;
  idtac current;
  idtac " expected, but found";
  print_goal.
Ltac current_goal goal:= first[change goal| errors_for_current goal].
Tactic Notation "!goal " constr(goal) := current_goal goal.
