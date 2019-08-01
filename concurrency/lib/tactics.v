Require Import Coq.Classes.RelationClasses.
Require Import Coq.Relations.Relation_Definitions.
Require Import compcert.lib.Coqlib. (*modus ponens*)

Require Import compcert.lib.Axioms. (* It imports proof irrelevance and functional ext.*)

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

(* left hand side and right hand side*)
Ltac LHS:= match goal with  |- ?lhs = ?rhs => lhs end.
Ltac RHS:= match goal with  |- ?lhs = ?rhs => rhs end.

(* get print goal*)

Ltac get_goal:=
  match goal with [|- ?goal] =>  goal end.
Ltac get_goal_type:=
  match goal with [|- ?goal] =>
                  match type of goal with
                    ?T => T
                  end
  end.
Ltac print_goal:= 
  let goal:= get_goal in idtac goal.

(* unfold the top definition *)
Ltac unfold_func T:=
  lazymatch T with
    ?term_to_unfold _ =>
    unfold term_to_unfold || unfold_func term_to_unfold
  end.
Ltac unfold_first:=
  let T:=get_goal in first[ unfold T| unfold_func T].
Tactic Notation "unfold":= unfold_first.

(* neq is reflexive. *)
Definition neq_rel (A:Type): relation A:=
  fun (x y:A) => x <> y.
Global Instance Symmetric_neq: forall A, @Symmetric A (neq_rel A).
Proof. intros ? ? ? H ?. apply H; auto. Qed.

(* "Normal form"  hypothesis*)
Ltac destruct_and:=
  repeat match goal with [ H: _ /\ _  |- _ ] => destruct H end.
Ltac normal_hyp:=
  repeat match goal with
           [ H: _ /\ _  |- _ ] => destruct H
           | [ H: exists _, _  |- _ ] => destruct H
         end.
Ltac reduce_and:=
  repeat match goal with [ |- _ /\ _  ] => split end.
Ltac normal_goal:=
  repeat match goal with
           [ |- _ /\ _  ] => split
         | [ |- exists _, _] => eexists
         end.
Ltac normal:= normal_hyp; normal_goal.

(*Do case analysis to simplify a match _ with*)
Ltac common_tacs_after_destruct H:=
  first [ congruence
        | solve[inversion H]
        | auto].
      
Ltac match_case_goal:=
  match goal with
    |- context[match ?x with _ => _ end] =>
    destruct x eqn:?; try congruence
  end.
Ltac match_case_hyp H:=
  match type of H with
    context[match ?x with _ => _ end] => destruct x eqn:?
  end; common_tacs_after_destruct H.
Tactic Notation "match_case":= match_case_goal.
Tactic Notation "match_case" "in" hyp(H):= (match_case_hyp H).

(* Like remember, but without the equation*)
Ltac forget_as a A :=
  let Heq:=fresh in
  remember a as A eqn:Heq; clear Heq.
Tactic Notation "forget" constr(a) "as" simple_intropattern(A):=
  forget_as a A.


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
(*subst for [x:= _] expressions *)
Ltac subst_set:=
  repeat match goal with [a:= _ |- _ ] => subst a end.

(*When repeating tactics, mark terms that haver been used. 
  for example, if you want to apply a tactic to each hypothesis, 
  recursively, you can mark the ones that you have done.
  then delete all marks when you are done.
*)
Inductive MARK (T:Type) (a:T):=
| Marked: MARK T a.
Ltac mark H a:=
  lazymatch goal with
  | [H: MARK _ a |- _] => fail "that is already marked"
  | _ => pose proof (Marked _ a)
  end.


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

(*+ About proofs *)

(** *Unify Proofs:
     - Takes any two proofs of the same thing and unifies them    
     - Notice: only works with "unstructured proofs. "
 *)
Ltac unify_proofs:=
  progress (repeat match goal with
                   | [A: ?T, B: ?T |- _] =>
                     match type of T with
                     | Prop => let HH:=fresh in
                           assert (HH: A = B) by apply Axioms.proof_irr;
                           first[subst A| subst B]; try clear HH
                     end
                   end).

(** *Abstract Proofs:
    This tactic turns every proof into a variable 
    and forgets its structure. Since we have assume 
    Proof Irrelevance, this doesn't lose information. 
    Notice: SLOW! *)
Ltac is_proof P:=
  match type of P with
    ?T => match type of T with Prop => idtac end
  end.
Ltac is_applied P:=
  match P with ?a ?b => idtac end.
Ltac abstract_proof P:=
  let abs_proof:= fresh "abs_proof" in
  let Heqabs_proof:= fresh "Heqabs_proof" in
  remember P as abs_proof eqn:Heqabs_proof;
  clear Heqabs_proof.
Ltac abstract_proofs_goal:=
  match goal with
    |- context[ ?P ]=>
    is_proof P; is_applied P; abstract_proof P
  end.
Ltac abstract_proofs_hyp:=
  match goal with
    [H: context[ ?P ] |- _ ] =>
    is_proof P; is_applied P; abstract_proof P
  end.
Ltac abstract_proofs:=
  repeat abstract_proofs_goal;
  repeat abstract_proofs_hyp.

Ltac abstract_proofs_goal_of is_T:=
  match goal with
    |- context[ ?P ]=>
    is_T P; is_applied P; abstract_proof P
  end.
Ltac abstract_proofs_hyp_of is_T:=
  match goal with
    [H: context[ ?P ] |- _ ] =>
    is_T P; is_applied P; abstract_proof P
  end.
Tactic Notation "equate_uconstr" constr(T) uconstr(goal) := equate T goal.
Ltac is_T_of pat P:= match type of P with ?T => equate_uconstr T pat end.
Ltac abstract_proofs_of' pat:= 
  repeat abstract_proofs_goal_of ltac:(is_T_of pat);
  repeat abstract_proofs_hyp_of ltac:(is_T_of pat).
Tactic Notation "abstract_proofs" "of" uconstr(pat):= abstract_proofs_of' pat.
(*Ltac abstract_proofs_of is_T:=
  repeat abstract_proofs_goal_of is_T;
  repeat abstract_proofs_hyp_of is_T.*)

(** *Clean Proofs:
    - Abstracts every proof into a variable
    - unifies all such proofs of the same thing.
 *)
Ltac clean_proofs:= abstract_proofs; repeat unify_proofs.
Ltac clean_proofs_goal:= repeat abstract_proofs_goal; repeat unify_proofs.
Tactic Notation "clean_proofs" "of" uconstr(pat):=
  abstract_proofs of pat; repeat unify_proofs.

(** *
    How to rewrite equalities when there are many dependencies.
 *)

Ltac dependent_rewrite Heq:=
  match type of Heq with
    ?LHS = ?RHS =>
    let AA:=fresh "AA" in
    let AAeq:=fresh "AAeq" in
    let BB:=fresh "BB" in
    let BBeq:=fresh "BBeq" in
    remember LHS as AA eqn:AAeq; clear AAeq;
    remember RHS as BB eqn:BBeq;
    subst AA; subst BB; try clear BBeq
  end.
Ltac dependent_subst A B:=
  let Heq:=fresh "Heq" in
  assert (Heq:A = B);
  [try solve [auto]|
   dependent_rewrite Heq].