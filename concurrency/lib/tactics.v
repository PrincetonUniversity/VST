Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import compcert.lib.Coqlib. (*modus ponens*)

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

(* "Normal form"  hypothesis*)
Ltac destruct_and:=
  repeat match goal with [ H: _ /\ _  |- _ ] => destruct H end.
Ltac reduce_and:=
  repeat match goal with [ |- _ /\ _  ] => split end.

(* Stronger form of inversion. Similar to inv (from CompCert) *)
(* It inverts and rewrites every *new* equality*)
Ltac try_intros H:=
  first [ intros H |
          let HH:= fresh H in
          rename H into HH;
          intros H].

Ltac invert_with_continuation HH cont:=
  match goal with
  | H:_ |- _ =>
    progress
      match H with
      | HH => idtac
      | _ => revert H ;
            (* if the tactic fails, we don't want it to keep trying 
               so we force it to fail all the way. *)
            first [ invert_with_continuation
                      HH ltac:(try_intros H; cont) |
                    fail 3 "invert failed."]
      end
  | _ => inversion HH ; subst ; cont
  end.
        
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
(**
   Many of these tactics are very useful for exploration,
   but not efficient. Be careful if using on any script.
*)

(** Claim what the current goal looks like *)
(* Usefull for marking cases in a dynamic way *)
Ltac get_goal:=
  match goal with [|- ?goal] =>  goal end.
Ltac print_goal:= 
  let goal:= get_goal in idtac goal.
Ltac errors_for_current current:=
  let goal:= get_goal in 
  fail 1
    "That's not the current goal. "
    current
    " provided, but found"
    goal.
Ltac equate x y :=
  let dummy := constr:(eq_refl x : x = y) in idtac.
Ltac goal_is g:=
  match goal with |- ?g_targ => equate g g_targ end.
Ltac current_goal goal:= first[goal_is goal|change goal| errors_for_current goal].
Tactic Notation "!goal " uconstr(goal) := current_goal goal.

(*Sometimes !goal fails due dependencies in the arguements.
  It can be useful to use the tactic bellow, even though it allows no "_"
*)
Ltac my_context_match g :=
  match goal with
  | |- context[g] => idtac
  end.
Tactic Notation "!context_goal " constr(in_goal) := my_context_match in_goal.

(* simpler way to comment out tactics*)
Tactic Notation "dont" tactic(t):=
  idtac.
                
                

(* Print type for and ident*)
Ltac get_type x:= match type of x with ?T => T end. 
Ltac print_type x:= let t:= get_type x in idtac t.

(** *Unification variables*)


(* Make unification variable into a goal. 
   you can just use unshelve(instantiate(n:= _))
 *)
Tactic Notation "unshelve_one" constr(n):=
  (lazymatch n with
   | 1 => unshelve(instantiate(1:= _))
   | 2 => unshelve(instantiate(2:= _))
   | 3 => unshelve(instantiate(3:= _))
   | 4 => unshelve(instantiate(4:= _))
   | 5 => unshelve(instantiate(5:= _))
   | 6 => unshelve(instantiate(6:= _))
   | 7 => unshelve(instantiate(5:= _))
   | 8 => unshelve(instantiate(6:= _))
   | _ => fail "This tactic is not implemented for" n
   end).


(* Print name and type for all evars*)
(* This is an simpler version of Show Existentials. *)
Ltac get_evars tac:=
  multimatch goal with
    |- context[?x] => is_evar x; tac x; fail
  | _ => idtac
  end.
Ltac show_evars:= get_evars ltac:(fun x=> let t:=(get_type x) in idtac x ":" t).


(** *Exploit*)
(** Like 'cut' but breaks every hypotesis of the cut independently
   Similar to compCert's 'exploit', but not bounded by depth.
*)
Ltac exploit_in:=
  let H:= fresh in intros H;
  match type of H with
  | _ => refine (modusponens _ _ _ _);
                 [refine (H _);clear H| clear H; exploit_in]
  | _ => revert H; try clear H
  end; shelve_unifiable.
Ltac exploit H:=
  match type of H with
    ?T => cut T; [|exact H];exploit_in
  end.


(** *Making notes
    Good for keeping track of what subgoal you are in. 
    Mostly for proof exploration/debugging.
*)
Ltac Note str:=
  assert (str: True) by auto;
  move str at top.

(** *Split is too strong sometimes, since it just uses [constructor]*)
Ltac weak_split tac:=
  match goal with
    |- _ /\ _ => split; tac
  end.
Tactic Notation "weak_split" tactic(t):= weak_split t.
Tactic Notation "weak_split":= weak_split idtac.



Ltac destruct_lhs:=
  match goal with
  | |- ?LHS = ?RHS => destruct LHS eqn:?
  end.
Ltac destruct_rhs:=
  match goal with
  | |- ?LHS = ?RHS => destruct RHS eqn:?
  end.