(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
(* An oracle machine semantics for computations. *)

Set Implicit Arguments.

Require Export fcf.Comp.
Require Import fcf.Blist.
Require Import fcf.Fold.
Require Import Permutation.
Require Import Omega.

Local Open Scope list_scope. 
Local Open Scope comp_scope.

(* A type for keeping track of the state of the evaluation. *)
Inductive comp_state(A : Set) :=
  | cs_done : A -> Blist -> comp_state A
  | cs_eof : comp_state A
  | cs_more : Comp A -> Blist -> comp_state A.

(* a type for returning answers *)
Inductive comp_answer(A : Set) :=
  | ca_done : A -> comp_answer A
  | ca_eof : comp_answer A.

Lemma comp_answer_eq_dec : forall (A : Set),
      eq_dec A ->
      eq_dec (comp_answer A).

  intuition.
  unfold eq_dec in *.
  intuition.
  destruct a1; destruct a2.
  destruct (H a a0); subst.
  left.
  trivial.
  right.
  intuition.
  inversion H0; clear H0; subst.
  intuition.
  right; intuition; discriminate.
  right; intuition; discriminate.
  left.
  trivial.
Qed.

(* a functional form of the small-step semantics*)
Fixpoint evalDet_step(A : Set)(c : Comp A)(s : Blist) : comp_state A :=
  match c in Comp A return comp_state A with
    | Ret pf a => cs_done a s
    | Rnd n  => 
      match (shiftOut s n) with
        | Some (v, s') => cs_more (Ret (@Bvector_eq_dec n) v) s'
        | None => (@cs_eof (Bvector n))
      end
    | Bind c1 c2 =>     
      match (evalDet_step c1 s) with
        | cs_eof _ => (@cs_eof _)
        | cs_done b s' => cs_more (c2 b) s'
        | cs_more c1' s' => cs_more (Bind c1' c2) s'
      end
    | Repeat c P =>
      cs_more (Bind c (fun a => if (P a) then (Ret (comp_eq_dec c) a) else (Repeat c P))) s
   end.

Inductive evalDet_steps(A : Set) : comp_state A -> comp_state A -> Prop :=
  | evalDet_steps_refl : forall ans,
    evalDet_steps ans ans
  | evalDet_steps_step : 
    forall c s ans ans',
      (evalDet_step c s) = ans ->
      evalDet_steps ans ans' ->
      evalDet_steps (cs_more c s) ans'.

Hint Constructors evalDet_steps : evalDet.

Inductive evalDet(A : Set)(c : Comp A)(s : Blist) : comp_answer A -> Prop :=
  | evalDet_done : forall a s',
    evalDet_steps (cs_more c s) (cs_done a s') ->
    evalDet c s (ca_done a)
  | evalDet_eof :
    evalDet_steps (cs_more c s) (@cs_eof A) ->
    evalDet c s (@ca_eof A).
    

Theorem evalDet_steps_trans : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall z, 
  evalDet_steps y z ->
  evalDet_steps x z.

  induction 1; intuition; subst.
  econstructor.
  trivial.
  eapply IHevalDet_steps.
  trivial.

Qed.

Theorem evalDet_steps_bind_more_h : forall(A B : Set) x y,
  evalDet_steps x y ->
  forall (c1 : Comp B)(c2 : B -> Comp A) s c1' s',
  x = (cs_more c1 s) ->
  y =  (cs_more c1' s') ->
  evalDet_steps (cs_more (Bind c1 c2) s) (cs_more (Bind c1' c2) s').

  induction 1; intuition; subst.

  Ltac evalDet_tac1 :=
    match goal with
      | [H : cs_more _ _ = cs_more _ _ |- _ ] => inversion H; clear H; subst
      | [|- evalDet_steps ?c ?c ] => econstructor
      | [H : evalDet_steps (evalDet_step ?c ?s) _ |- evalDet_steps (cs_more (Bind ?c _) ?s) _ ] => inversion H; clear H; subst
      | [H : (evalDet_step ?c ?s) = _ |- evalDet_steps (cs_more (Bind ?c _) ?s) _ ] => econstructor; simpl
      | [|- context[match ?x with | cs_done _ _ => _ | cs_eof _ => _ | cs_more _ _ => _ end] ] => case_eq x; intuition

    end.


  repeat evalDet_tac1.

  inversion H0; clear H0; subst.
  inversion H1; clear H1; subst.
  econstructor.
  eauto.
  simpl.
  rewrite H3.
  econstructor.

  inversion H1; clear H1; subst.
  econstructor.
  eauto.
  simpl.
  rewrite <- H.
  eapply IHevalDet_steps.
  auto.
  trivial.

Qed.

Theorem evalDet_steps_bind_more : forall(A B : Set)(c1 : Comp B)(c2 : B -> Comp A) s c1' s',
  evalDet_steps (cs_more c1 s) (cs_more c1' s') ->
  evalDet_steps (cs_more (Bind c1 c2) s) (cs_more (Bind c1' c2) s').


  intuition.
  eapply evalDet_steps_bind_more_h; eauto.
Qed.


Lemma evalDet_steps_done_inv_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (c : Comp A)(a : A) s s',
  x = (cs_more c s) -> 
  y = (cs_done a s') ->
  exists c'' s'', evalDet_steps (cs_more c s) (cs_more c'' s'') /\ evalDet_step c'' s'' = (cs_done a s').

  induction 1; intuition; subst.
  discriminate.

  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  econstructor. econstructor.
  intuition.
  
  destruct (IHevalDet_steps c a s s'); eauto.
  destruct H0; intuition.
  exists x.
  exists x0.
  intuition.
  symmetry in H.
  econstructor.
  eapply H.
  trivial.
Qed.

Lemma evalDet_steps_done_inv : forall (A : Set)(c : Comp A)(a : A) s s',
  evalDet_steps (cs_more c s) (cs_done a s') ->
  exists c'' s'', evalDet_steps (cs_more c s) (cs_more c'' s'') /\ evalDet_step c'' s'' = (cs_done a s').

  intuition.
  eapply evalDet_steps_done_inv_h; eauto.
Qed.

Lemma evalDet_steps_eof_inv_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (c : Comp A) s,
  x = (cs_more c s) -> 
  y = (@cs_eof A) ->
  exists c'' s'', evalDet_steps (cs_more c s) (cs_more c'' s'') /\ evalDet_step c'' s'' = (@cs_eof A).

  induction 1; intuition; subst.
  discriminate.
  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  econstructor. econstructor.
  intuition.
  
  destruct (IHevalDet_steps c s); eauto.
  destruct H0; intuition.
  exists x.
  exists x0.
  intuition.
  econstructor.
  rewrite <- H.
  eauto.
  rewrite <- H.
  trivial.
Qed.

Lemma evalDet_steps_eof_inv : forall (A : Set)(c : Comp A) s,
  evalDet_steps (cs_more c s) (@cs_eof A) ->
  exists c'' s'', evalDet_steps (cs_more c s) (cs_more c'' s'') /\ evalDet_step c'' s'' = (@cs_eof A).

  intuition.
  eapply evalDet_steps_eof_inv_h; eauto.
Qed.

Theorem evalDet_steps_bind_done : forall(A B : Set)(c1 : Comp B)(c2 : B -> Comp A) a s s',
  evalDet_steps (cs_more c1 s) (cs_done a s') ->
  evalDet_steps (cs_more (Bind c1 c2) s) (cs_more (c2 a) s').

  intuition.
  apply evalDet_steps_done_inv in H.
  destruct H.
  destruct H.
  intuition.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_more.
  eauto.
  econstructor.
  simpl.
  rewrite H1.
  eauto.
  econstructor.
Qed.

Theorem evalDet_bind_eof : forall(A B : Set)(c1 : Comp B)(c2 : B -> Comp A) s,
  evalDet_steps (cs_more c1 s) (@cs_eof B) ->
  evalDet_steps (cs_more (Bind c1 c2) s) (@cs_eof A).

  intuition.
  apply evalDet_steps_eof_inv in H.
  destruct H.
  destruct H.
  intuition.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_more.
  eauto.
  econstructor.
  simpl.
  rewrite H1.
  eauto.
  econstructor.
Qed.

Inductive comp_state_eq(A : Set) : comp_state A -> comp_state A -> Prop :=
  | cse_done : 
    forall a s, 
      comp_state_eq (cs_done a s) (cs_done a s)
  | cse_eof : 
    comp_state_eq (@cs_eof A) (@cs_eof A)
  | cse_more : 
    forall c1 c2 s,
      Comp_eq c1 c2 ->
      comp_state_eq (cs_more c1 s) (cs_more c2 s).


Theorem comp_state_eq_refl : forall (A : Set)(c : comp_state A),
  comp_state_eq c c.

  destruct c; intuition;
  econstructor.
  eapply Comp_eq_refl.
Qed.

Lemma evalDet_steps_done_func_h : forall (A : Set)(x : comp_state A) y1,
  evalDet_steps x y1 ->
  forall a a' s s',
  y1 = (cs_done a s) ->
  evalDet_steps x (cs_done a' s') ->
  (a = a' /\ s = s').

  induction 1; intros; subst.
  inversion H0; clear H0; subst.
  intuition.

  inversion H2; clear H2; subst.
  eapply IHevalDet_steps;
  trivial.
Qed.

Theorem evalDet_steps_done_func : forall (A : Set) x (a a' : A) s s',
  evalDet_steps x (cs_done a s) ->
  evalDet_steps x (cs_done a' s') ->
  (a = a' /\ s = s').

  intros.
  eapply evalDet_steps_done_func_h.
  eapply H.
  eauto.
  eauto.
Qed.

Lemma evalDet_steps_done_eof_func_h : forall (A : Set)(x : comp_state A) y1,
  evalDet_steps x y1 ->
  forall a s,
  y1 = (cs_done a s) ->
  evalDet_steps x (@cs_eof A) ->
  False.

  induction 1; intros; subst.
  inversion H0.

  inversion H2; clear H2; subst.
  eapply IHevalDet_steps;
  trivial.
Qed.

Theorem evalDet_steps_done_eof_func : forall (A : Set) x (a : A) s,
  evalDet_steps x (cs_done a s) ->
  evalDet_steps x (@cs_eof A) ->
  False.

  intros.
  eapply evalDet_steps_done_eof_func_h.
  eapply H.
  eauto.
  eauto.
Qed.


Theorem evalDet_func : forall (A : Set)(c : Comp A)(s : Blist)(y1 y2 : comp_answer A),
  evalDet c s y1 ->
  evalDet c s y2 ->
  y1 = y2.

  intuition.
  inversion H; subst; clear H.
  inversion H0; subst; clear H0.
  f_equal.
  eapply evalDet_steps_done_func; eauto.

  exfalso.
  eapply evalDet_steps_done_eof_func; eauto.

  inversion H0; clear H0; subst.
  exfalso.
  eapply evalDet_steps_done_eof_func; eauto.

  trivial.
Qed.

Definition evalDet_equiv(A : Set)(c1 c2 : Comp A) :=
  (forall s y, evalDet c1 s y <-> evalDet c2 s y).

Lemma evalDet_equiv_symm : forall (A : Set)(c1 c2 : Comp A),
  evalDet_equiv c1 c2 ->
  evalDet_equiv c2 c1.
  
  unfold evalDet_equiv. intuition.
  eapply H; trivial.
  eapply H; trivial.
Qed.

Theorem evalDet_steps_bind_done_inv_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (B : Set)(c1 : Comp B)(c2 : B -> Comp A) s s' a,
    x = (cs_more (Bind c1 c2) s) ->
    y = (cs_done a s') ->
  exists b s'', evalDet_steps (cs_more c1 s) (cs_done b s'') /\
    evalDet_steps (cs_more (c2 b) s'') (cs_done a s').

  induction 1; intuition; subst.
  discriminate.
  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  case_eq (evalDet_step c1 s0); intuition;
  rewrite H in H2; discriminate.

  case_eq (evalDet_step c1 s0); intuition;
  rewrite H0 in H.
  inversion H; clear H; subst.
  econstructor. econstructor. intuition.
  econstructor.
  eapply H0.
  econstructor.
  econstructor; eauto.

  discriminate.

  inversion H; clear H; subst.
  edestruct IHevalDet_steps.
  simpl.
  rewrite H0.
  eauto.
  eauto.
  destruct H.
  intuition.
  
  econstructor. econstructor. intuition.
  econstructor.
  eapply H0.
  eauto.
  trivial.
Qed.

Theorem evalDet_steps_bind_done_inv : forall (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) s s' a,
  evalDet_steps (cs_more (Bind c1 c2) s) (cs_done a s') ->
  exists b s'', evalDet_steps (cs_more c1 s) (cs_done b s'') /\
    evalDet_steps (cs_more (c2 b) s'') (cs_done a s').

  intuition.
  eapply evalDet_steps_bind_done_inv_h; eauto.

Qed.

Theorem evalDet_steps_bind_eof_inv_h : 
  forall (A : Set)(x y : comp_state A),
    evalDet_steps x y ->
    forall (B : Set)(c1 : Comp B)(c2 : B -> Comp A) s,
      x = (cs_more (Bind c1 c2) s) ->
      y = (@cs_eof A) ->
      evalDet_steps (cs_more c1 s) (@cs_eof B) \/
      exists b s', evalDet_steps (cs_more c1 s) (cs_done b s') /\ 
        evalDet_steps (cs_more (c2 b) s') (@cs_eof A).

  induction 1; intuition; subst.
  discriminate.

  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  case_eq (evalDet_step c1 s0); intuition;
  rewrite H in H2.
  discriminate.
  left.
  econstructor.
  rewrite H.
  eauto.
  econstructor.
  discriminate.

  case_eq (evalDet_step c1 s0); intuition;
  rewrite H0 in H.
  inversion H; clear H; subst.
  right.
  econstructor. econstructor. intuition.
  econstructor.
  eauto.
  econstructor.
  econstructor.
  eauto.
  trivial.
  
  discriminate.
  
  inversion H; clear H; subst.
  edestruct (IHevalDet_steps).
  simpl.
  rewrite H0.
  eauto.
  trivial.
  left.
  econstructor; eauto.
  destruct H. destruct H. intuition.
  right.
  econstructor. econstructor. intuition.
  econstructor; eauto.
  trivial.

Qed.
  
Theorem evalDet_steps_bind_eof_inv : forall (A B : Set)(c1 : Comp B)(c2 : B -> Comp A) s,
  evalDet_steps (cs_more (Bind c1 c2) s) (@cs_eof A) ->
  evalDet_steps (cs_more c1 s) (@cs_eof B) \/
  exists b s', evalDet_steps (cs_more c1 s) (cs_done b s') /\ 
    evalDet_steps (cs_more (c2 b) s') (@cs_eof A).

  intuition.
  eapply evalDet_steps_bind_eof_inv_h; eauto.
Qed.


Theorem evalDet_bind_assoc : forall (A : Set)(c1 : Comp A)(B C : Set)(c2 : A -> Comp B)(c3 : B -> Comp C),
  evalDet_equiv (Bind (Bind c1 c2) c3) (Bind c1 (fun a => (Bind (c2 a) c3))).

  intuition.
  unfold evalDet_equiv.
  intuition.
  inversion H; clear H; subst.

  Ltac evalDet_tac :=
    match goal with
      | [H1 : evalDet_steps ?x (cs_done ?a1 ?s1), H2 : evalDet_steps ?x (@cs_eof _) |- _ ] => exfalso; eauto using evalDet_steps_done_eof_func; intuition
      | [H : evalDet_steps (cs_more (Bind _ _) _) (cs_done _ _) |- _ ] => apply evalDet_steps_bind_done_inv in H
      | [H : evalDet_steps (cs_more (Bind _ _) _) (@cs_eof _) |- _ ] => apply evalDet_steps_bind_eof_inv in H; intuition
      | [H : exists _ : _, _ |- _ ] => destruct H; intuition
      | [H1 : evalDet_steps ?x (cs_done ?a1 ?s1), H2 : evalDet_steps ?x (cs_done ?a2 ?s2) |- _ ] => assert (a1 = a2 /\ s1 = s2); eauto using evalDet_steps_done_func; intuition; subst; clear H1; eauto
    end.
  repeat evalDet_tac.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eauto.

  repeat evalDet_tac.
  econstructor.
  eapply evalDet_bind_eof; eauto.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eapply evalDet_bind_eof; eauto.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eauto.

  inversion H; clear H; subst.
  repeat evalDet_tac.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eauto.
  eauto.

  repeat evalDet_tac.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_bind_eof; eauto.
  eapply evalDet_bind_eof; eauto.
  econstructor.
  econstructor.
  eapply evalDet_bind_eof.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eauto.
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eauto.
  eauto.

Qed.

Theorem evalDet_done_eof_func:
  forall (A : Set) (c : Comp A) (a : A) (s : Blist),
    evalDet c s (ca_done a) -> evalDet c s (@ca_eof A) -> False.
  
  intuition.
  inversion H; clear H; subst.
  inversion H0; clear H0; subst.
  eapply evalDet_steps_done_eof_func; eauto.
Qed.

Lemma getSupport_In_evalDet_step_done : forall (A : Set)(c : Comp A) a s s',
  evalDet_step c s = cs_done a s' ->
  In a (getSupport c).
  
  induction c; intuition; simpl in *.
  
  inversion H; clear H; subst.
  intuition.
  
  destruct (evalDet_step c s); try discriminate.
  
  eapply in_getAllBvectors.

  discriminate.
Qed.

Lemma getSupport_In_evalDet_step_more : forall (A : Set)(c c' : Comp A) s s' a,
  evalDet_step c s = cs_more c' s' ->
  In a (getSupport c') ->
  In a (getSupport c).
  
  induction c; intuition; simpl in *.
  discriminate.
  
  case_eq (evalDet_step c s); intuition;
    rewrite H2 in H0.
  inversion H0; clear H0; subst.
  eapply in_getUnique.
  eapply in_flatten.
  exists (getSupport (c0 b)).
  intuition.
  eapply in_map_iff.
  exists b. 
  intuition.
  eapply getSupport_In_evalDet_step_done; eauto.
  
  discriminate.
  
  inversion H0; clear H0; subst.
  simpl in *.
  apply in_getUnique_if in H1.
  apply in_flatten in H1.
  destruct H1; intuition.
  eapply in_getUnique.
  eapply in_flatten.
  exists x.
  intuition.
  apply in_map_iff in H1.
  destruct H1; intuition.
  subst.
  eapply in_map_iff.
  exists x0.
  intuition.
  eapply IHc; eauto.
  
  eapply in_getAllBvectors.

  inversion H; clear H; subst.
  simpl in *.
  eapply in_getUnique_if in H0.
  eapply in_flatten in H0.
  destruct H0.
  intuition.
  eapply in_map_iff in H0.
  destruct H0.
  intuition.
  subst.
  case_eq (b x0); intuition;
  rewrite H in H1; simpl in *.
  intuition; subst.
  eapply filter_In; eauto.
  trivial.
  
Qed.

Lemma getSupport_In_evalDet_steps_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (c : Comp A) a s s',
    x = (cs_more c s)  ->
    y = (cs_done a s') -> 
    In a (getSupport c).
  
  induction 1; intuition; subst.
  discriminate.
  
  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  
  eapply getSupport_In_evalDet_step_done; eauto.
  
  eapply getSupport_In_evalDet_step_more.
  eauto.
  eapply IHevalDet_steps.
  eauto.
  eauto.
Qed.

Lemma getSupport_In_evalDet_steps : forall (A : Set)(c : Comp A) a s s',
  evalDet_steps (cs_more c s) (cs_done a s') -> 
  In a (getSupport c).
  
  intuition.
  eapply getSupport_In_evalDet_steps_h; eauto.
Qed.

Theorem getSupport_In_evalDet : forall (A : Set)(c : Comp A) a s,
  evalDet c s (ca_done a) -> 
  In a (getSupport c).
  
  intuition.
  inversion H; clear H; subst.
  
  eapply getSupport_In_evalDet_steps; eauto.
  
Qed.

(* The following predicate makes it easier for us to do induction on the number of loop iterations. *)
Inductive evalDet_repeat_steps (A : Set)(P : A -> bool) : comp_state A -> comp_state A -> Prop :=
| evalDet_repeat_steps_done : 
  forall c s a s',
    evalDet_steps (cs_more c s) (cs_done a s') ->
    P a = true ->
    evalDet_repeat_steps P (cs_more c s) (cs_done a s')
| evalDet_repeat_steps_eof :
  forall c s,
    evalDet_steps (cs_more c s) (@cs_eof A) ->
    evalDet_repeat_steps P (cs_more c s) (@cs_eof A)
| evalDet_repeat_steps_step :
  forall c s a s' y,
    evalDet_steps (cs_more c s) (cs_done a s') ->
    P a = false ->
    evalDet_repeat_steps P (cs_more c s') y ->
    evalDet_repeat_steps P (cs_more c s) y.

Inductive evalDet_repeat(A : Set)(P : A -> bool)(c : Comp A)(s : Blist) : comp_answer A -> Prop :=
  | evalDet_repeat_done : forall a s',
    evalDet_repeat_steps P (cs_more c s) (cs_done a s') ->
    evalDet_repeat P c s (ca_done a)
  | evalDet_repeat_eof :
    evalDet_repeat_steps P (cs_more c s) (@cs_eof A) ->
    evalDet_repeat P c s (@ca_eof A).

Lemma list_skipn_strong_ind_h : forall (A : Type) l (P : list A -> Prop) ,
  P nil -> 
  (forall x, (forall n, n > 0 -> P (skipn n x)) -> P x) ->
  (forall n, P (skipn n l)).

  induction l;
  intuition; simpl in *.

  destruct n; simpl in *; trivial.
  
  destruct n; simpl in *.
  eapply H0.
  intuition.
  destruct n; try omega; simpl in *.
  eapply IHl; intuition.

  eapply IHl; intuition.
Qed.

Lemma list_skipn_strong_ind : forall (A : Type) l (P : list A -> Prop) ,
  P nil -> 
  (forall x, (forall n, n > 0 -> P (skipn n x)) -> P x) ->
  P l.

  intuition.
  assert (l = skipn 0 l).
  simpl.
  trivial.
  rewrite H1.
  eapply list_skipn_strong_ind_h; trivial.

Qed.

Lemma evalDet_step_nil_inv : forall (A : Set)(c : Comp A)(a1 a2 : A) s2,
  evalDet_step c nil = (cs_done a2 s2) ->
  In a1 (getSupport c) ->
  a1 = a2.

  induction c; intuition; simpl in *; intuition; subst.

  inversion H; clear H; subst.
  trivial.

  destruct (evalDet_step c nil); discriminate.

  destruct n; try discriminate.
  
  discriminate.
  
Qed.

Lemma evalDet_step_done_nil_inv : forall (A : Set)(c : Comp A) a ls,
  evalDet_step c nil = (cs_done a ls) ->
  ls = nil.
  
  induction c; intuition; simpl in *.
  inversion H; clear H; subst.
  trivial.
  
  case_eq (evalDet_step c nil); intuition;
    rewrite H1 in H0;
      discriminate.
  
  destruct n;
    discriminate.

  discriminate.
Qed.

Lemma evalDet_step_more_nil_inv : forall (A : Set)(c c' : Comp A) ls,
  evalDet_step c nil = (cs_more c' ls) ->
  ls = nil.
  
  induction c; intuition; simpl in *.
  discriminate.
  
  case_eq (evalDet_step c nil); intuition;
    rewrite H1 in H0.
  inversion H0; clear H0; subst.
  eapply evalDet_step_done_nil_inv; eauto.
  discriminate.
  inversion H0; clear H0; subst.
  eauto.
  
  destruct n.
  inversion H; clear H; subst.
  trivial.
  discriminate.

  inversion H; clear H; subst.
  trivial.

Qed.

Lemma evalDet_step_done_support_singleton : forall (A : Set)(c : Comp A) s a,
  evalDet_step c s = cs_done a s ->
  getSupport c = (a :: nil).
  
  induction c; intuition; simpl in *.
  inversion H; clear H; subst.
  trivial.
  
  destruct (evalDet_step c s); discriminate.
  
  destruct (shiftOut s n).
  destruct p.
  discriminate.
  discriminate.

  discriminate.
Qed.

Lemma getUnique_NoDup_eq : forall (A : Set)(eqd : eq_dec A)(ls : list A),
  NoDup ls ->
  getUnique ls eqd = ls.

  induction ls; intuition; simpl in *.
  inversion H; clear H; subst.
  destruct (in_dec eqd a (getUnique ls eqd)).
  exfalso.
  apply H2.
  eapply in_getUnique_if.
  eauto.

  f_equal.
  eauto.

Qed.

Lemma getUnique_Permutation : forall (A : Set)(eqd1 eqd2 : eq_dec A)(ls1 ls2 : list A),
  Permutation ls1 ls2 ->
  Permutation (getUnique ls1 eqd1) (getUnique ls2 eqd2).

  induction 1; intuition; simpl in *.
  destruct (in_dec eqd1 x (getUnique l eqd1)).
  destruct (in_dec eqd2 x (getUnique l' eqd2)).
  eauto.
  exfalso.
  eapply n.
  eapply Permutation_in; eauto.

  destruct (in_dec eqd2 x (getUnique l' eqd2)).
  exfalso.
  eapply n.
  eapply Permutation_in.
  eapply Permutation_sym.
  eauto.
  eauto.
  eapply perm_skip.
  trivial.

  destruct (in_dec eqd1 x (getUnique l eqd1)).
  destruct (in_dec eqd1 y (getUnique l eqd1)).
  destruct (in_dec eqd2 y (getUnique l eqd2)).
  destruct (in_dec eqd2 x (getUnique l eqd2)).

  eapply NoDup_Permutation; eauto using getUnique_NoDup; intuition;
    eauto using in_getUnique, in_getUnique_if.
  
  exfalso.
  eauto using in_getUnique, in_getUnique_if.
  exfalso.
  eauto using in_getUnique, in_getUnique_if.

  destruct (in_dec eqd2 y (getUnique l eqd2)).
  exfalso.
  eauto using in_getUnique, in_getUnique_if.
  destruct (in_dec eqd2 x (y :: getUnique l eqd2)).
  eapply perm_skip.
  eapply NoDup_Permutation; eauto using getUnique_NoDup; intuition;
    eauto using in_getUnique, in_getUnique_if.
  simpl in *. intuition.
  exfalso.
  eauto using in_getUnique, in_getUnique_if.
  
  destruct (in_dec eqd1 y (x :: getUnique l eqd1)).
  destruct (in_dec eqd2 y (getUnique l eqd2)).
  destruct (in_dec eqd2 x (getUnique l eqd2)).
  exfalso.
  eauto using in_getUnique, in_getUnique_if.
  eapply perm_skip.
  eapply NoDup_Permutation; eauto using getUnique_NoDup; intuition;
    eauto using in_getUnique, in_getUnique_if.
  destruct (in_dec eqd2 x (y :: getUnique l eqd2)).
  simpl in *; intuition.
  clear H.
  subst.
  eapply perm_skip.
  eapply NoDup_Permutation; eauto using getUnique_NoDup; intuition;
    eauto using in_getUnique, in_getUnique_if.
  subst.
  exfalso.
  eauto using in_getUnique, in_getUnique_if.
  subst.
  exfalso.
  eauto using in_getUnique, in_getUnique_if.
  exfalso.
  eauto using in_getUnique, in_getUnique_if.

  simpl in *; intuition; subst.
  intuition.
  exfalso.
  eauto using in_getUnique, in_getUnique_if.

  destruct (in_dec eqd2 y (getUnique l eqd2)).
  destruct (in_dec eqd2 x (getUnique l eqd2)).
  exfalso.
  eauto using in_getUnique, in_getUnique_if.
  simpl in n0; intuition.
  exfalso.
  eauto using in_getUnique, in_getUnique_if.
  destruct (in_dec eqd2 x (y :: getUnique l eqd2)).
  simpl in *; intuition; subst.
  intuition.
  exfalso.
  eauto using in_getUnique, in_getUnique_if.

  eapply perm_trans.
  eapply perm_swap.
  eapply perm_skip.
  eapply perm_skip.
  eapply NoDup_Permutation; eauto using getUnique_NoDup; intuition;
    eauto using in_getUnique, in_getUnique_if.

  eapply perm_trans.
  eapply IHPermutation1.
  eapply (@perm_trans _ _ (getUnique l' eqd1)).
  eapply NoDup_Permutation; eauto using getUnique_NoDup; intuition;
    eauto using in_getUnique, in_getUnique_if.
  trivial.

Qed.

Lemma flatten_Permutation : forall (A : Type)(ls1 ls2 : list (list A)),
  Permutation ls1 ls2 ->
  Permutation (flatten ls1) (flatten ls2).

  induction 1; intuition; simpl in *.

  eapply Permutation_app.
  eapply Permutation_refl.
  trivial.

  repeat rewrite app_assoc.
  eapply Permutation_app.
  eapply Permutation_app_comm.
  eapply Permutation_refl.

  eapply perm_trans.
  eapply IHPermutation1.
  trivial.

Qed.

Lemma to_list_nil_inv : forall (A : Type)(n : nat)(v : Vector.t A n),
  Vector.to_list v = nil ->
  n = O.
  
  intuition.
  destruct v; simpl in *.
  trivial.
  unfold Vector.to_list in *.
  discriminate.
Qed.

Lemma app_second_eq :
  forall (A : Type) (ls2 ls1 ls3 : list A),
    ls1 = ls2 ++ ls3 -> length ls1 = length ls3 -> ls1 = ls3 /\ ls2 = nil.

  induction ls2; simpl in *; intuition;
  
  subst;
  simpl in *;
  rewrite app_length in H0;
  omega.

Qed.

Lemma shiftOut_same_inv : forall s n v,
  shiftOut s n = Some (v, s) ->
  n = O.
  
  intuition.
  eapply to_list_nil_inv.
  eapply app_second_eq.
  eapply shiftOut_correct_inv.
  eauto.
  trivial.
Qed.

Lemma filter_Permutation : forall (A : Set)(ls1 ls2 : list A)(P : A -> bool),
  Permutation ls1 ls2 ->
  Permutation (filter P ls1) (filter P ls2).
  
  induction 1; intuition; simpl in *.
  destruct (P x).
  eapply perm_skip.
  trivial.
  trivial.
  
  destruct (P x).
  destruct (P y).
  eapply perm_swap.
  eapply Permutation_refl.
  destruct (P y).
  eapply Permutation_refl.
  eapply Permutation_refl.
  
  eapply perm_trans;
    eauto.
Qed.

Lemma evalDet_step_more_support_preserved : forall (A : Set)(c c' : Comp A) s,
  evalDet_step c s = (cs_more c' s) ->
  Permutation (getSupport c) (getSupport c').

  induction c; intuition; simpl in *; try discriminate.
  subst.
  case_eq (evalDet_step c s); intuition;
  rewrite H1 in H0.
  inversion H0; clear H0; subst.

  erewrite evalDet_step_done_support_singleton; eauto.
  simpl.
  rewrite app_nil_r.

  rewrite getUnique_NoDup_eq.
  eapply Permutation_refl.
  eapply getSupport_NoDup.
  discriminate.
  inversion H0; clear H0; subst.
  simpl.

  eapply getUnique_Permutation.

  eapply flatten_Permutation.
  eapply Permutation_map.
  eauto.

  case_eq (shiftOut s n); intuition;
  rewrite H0 in H.
  destruct p.
  inversion H; clear H; subst.

  assert (n = O).
  eapply shiftOut_same_inv; eauto.
  subst.
  simpl.
  rewrite shiftOut_0 in H0.
  inversion H0; clear H0; subst.
  eapply Permutation_refl.
  discriminate.

  inversion H; clear H; subst.
  simpl.

  eapply NoDup_Permutation.
  eapply filter_NoDup.
  eapply getSupport_NoDup.
  eapply getUnique_NoDup.
  intuition.
  eapply in_getUnique.
  eapply in_flatten.
  econstructor.
  split.
  eapply in_map_iff.
  econstructor.
  split.
  2:{
    eapply filter_In; eauto.
  }
  assert (b x = true).
  eapply filter_In; eauto.
  rewrite H0.
  eauto.
  simpl.
  intuition.

  apply in_getUnique_if in H.
  eapply in_flatten in H.
  destruct H.
  intuition.
  eapply in_map_iff in H0.
  destruct H0.
  intuition.
  subst.
  case_eq (b x1); intuition;
  rewrite H in H1.
  simpl in *.
  intuition; subst.
  eapply filter_In; eauto.
  simpl in *.
  trivial.
  
Qed.


Lemma evalDet_steps_nil_eq_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (c : Comp A)(a1 a2 : A) s2,
  x = (cs_more c nil) -> 
  y = (cs_done a2 s2) ->
  In a1 (getSupport c) ->
  a1 = a2.

  induction 1; intuition; simpl in *; subst.
  discriminate.

  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  eapply evalDet_step_nil_inv; eauto.

  symmetry in H.
  specialize (evalDet_step_more_nil_inv _ H); intuition.
  subst.
  eapply IHevalDet_steps.
  eauto.
  eauto.
  eapply Permutation_in.
  eapply evalDet_step_more_support_preserved.
  eauto.
  trivial.
Qed.

Lemma evalDet_steps_nil_eq : forall (A : Set)(c : Comp A)(a1 a2 : A) s2,
  evalDet_steps (cs_more c nil) (cs_done a2 s2) ->
  In a1 (getSupport c) ->
  a1 = a2.

  intuition.
  eapply evalDet_steps_nil_eq_h; eauto.
Qed.

Lemma evalDet_step_done_val_eq : forall (A : Set)(c : Comp A)(a1 a2 : A) s1 s2,
  evalDet_step c s1 = (cs_done a2 s2) ->
  In a1 (getSupport c) ->
  a1 = a2.

  induction c; intuition; simpl in *.
  intuition; subst.
  inversion H; clear H; subst.
  trivial.

  destruct (evalDet_step c s1); discriminate.

  destruct (shiftOut s1 n); [ destruct p ; discriminate | discriminate ].
  
  discriminate.
Qed.

Lemma evalDet_step_done_ls_eq : forall (A : Set)(c : Comp A)(a2 : A) s1 s2,
  evalDet_step c s1 = (cs_done a2 s2) ->
  s1 = s2.

  induction c; intuition; simpl in *.
  inversion H; clear H; subst.
  trivial.

  destruct (evalDet_step c s1); discriminate.

  destruct (shiftOut s1 n); [ destruct p ; discriminate | discriminate ].
  
  discriminate.

Qed.

Lemma shiftOut_skipn : forall n (v : Bvector n) s s',
  shiftOut s n = Some (v, s') ->
  s' = skipn n s.
  
  induction n; intuition; simpl in *.
  rewrite shiftOut_0 in H.
  inversion H; clear H; subst.
  trivial.
  
  destruct s;
    simpl in *.
  discriminate.
  
  case_eq (shiftOut s n); intuition;
    rewrite H0 in H.
  destruct p.
  inversion H; clear H; subst.
  eauto.
  discriminate.
Qed.

Lemma evalDet_step_more_skipn_eq : forall (A : Set)(c c' : Comp A)(a1 : A) s1 s2,
  evalDet_step c s1 = (cs_more c' s2) ->
  In a1 (getSupport c) ->
  (s1 = s2 \/ (exists n, n > 0 /\ s2 = skipn n s1)).

  induction c; intuition; simpl in *; try discriminate.

  case_eq (evalDet_step c s1); intuition;
  rewrite H2 in H0.
  inversion H0; clear H0; subst.
  left.
  eapply evalDet_step_done_ls_eq.
  eauto.
  discriminate.
  inversion H0; clear H0; subst.
  
  eapply in_getUnique_if in H1.
  apply in_flatten in H1.
  destruct H1.
  intuition.
  apply in_map_iff in H1.
  destruct H1; intuition.
  eapply (IHc).
  eauto.
  eauto.
 
  case_eq (shiftOut s1 n); intuition;
  rewrite H1 in H.
  destruct p.
  inversion H; clear H; subst.
  destruct n.
  left.
  rewrite shiftOut_0 in H1.
  inversion H1; clear H1; subst.
  trivial.
  right.
  exists (S n).
  intuition.

  eapply shiftOut_skipn.
  eauto.
  
  discriminate.

  inversion H; clear H; subst.
  intuition.  
Qed.

Lemma evalDet_step_done_skipn : forall (A : Set)(c : Comp A) s a s',
  evalDet_step  c s = (cs_done a s') ->
  exists n, s' = skipn n s.
  
  induction c; intuition; simpl in *.
  
  inversion H; clear H; subst.
  exists O.
  simpl.
  trivial.

  destruct (evalDet_step c s); discriminate.

  destruct (shiftOut s n).
  destruct p.
  discriminate.
  discriminate.

  discriminate.
 
Qed.

Lemma skipn_sum : forall (A : Type)(n2 n1 : nat)(ls : list A),
  skipn n1 (skipn n2 ls) = skipn (n2 + n1) ls.
  
  induction n2; intuition; simpl in *.
  
  destruct ls.
  destruct n1; trivial.
  trivial.
Qed.

Lemma evalDet_step_more_skipn : forall (A : Set)(c c' : Comp A) s s',
  evalDet_step  c s = (cs_more c' s') ->
  exists n, s' = skipn n s.

  induction c; intuition; simpl in *.
  discriminate.

  case_eq (evalDet_step c s); intuition;
  rewrite H1 in H0.
  inversion H0; clear H0; subst.
  eapply evalDet_step_done_skipn.
  eauto.
  discriminate.
  inversion H0; clear H0; subst.
  eauto.

  case_eq (shiftOut s n); intuition;
  rewrite H0 in H.
  destruct p.
  inversion H; clear H; subst.
  exists n.

  eauto using shiftOut_skipn.
  discriminate.

  inversion H; clear H; subst.
  exists O.
  simpl.
  trivial.

Qed.

Lemma evalDet_steps_done_skipn_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (c : Comp A) s a s', 
    x = (cs_more c s) ->
    y = (cs_done a s') ->
  exists n, s' = skipn n s.

  induction 1; intuition; simpl in *; subst.
  discriminate.

  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  eapply evalDet_step_done_skipn; eauto.
  
  symmetry in H.
  specialize (evalDet_step_more_skipn _  _ H); intuition.
  destruct H0.
  subst.

  edestruct IHevalDet_steps.
  eauto.
  eauto.
  subst.
  exists (x + x0).
  apply skipn_sum.

Qed.

Lemma evalDet_steps_done_skipn : forall (A : Set)(c : Comp A) s a s',
  evalDet_steps (cs_more c s) (cs_done a s') ->
  exists n, s' = skipn n s.

  intuition.
  eapply evalDet_steps_done_skipn_h; eauto.
  
Qed.

Lemma evalDet_steps_skipn_h : forall (A : Set) a1 (x y : comp_state A),
  evalDet_steps x y ->
  forall (c : Comp A)(a2 : A) s1 s2,
  x = (cs_more c s1) -> 
  y = (cs_done a2 s2) ->
  In a1 (getSupport c) ->
  (a1 = a2 \/ (exists n, n > 0 /\ s2 = skipn n s1)).

  induction 1; subst; intuition; subst.
  discriminate.

  inversion H; clear H; subst.
  
  inversion H0; clear H0; subst.
  left.
  eapply evalDet_step_done_val_eq; eauto.

  symmetry in H.
  edestruct (evalDet_step_more_skipn_eq c0).
  eauto.
  eauto.
  subst.
  edestruct (IHevalDet_steps).
  eauto.
  eauto.
  eapply Permutation_in.
  eapply evalDet_step_more_support_preserved.
  eauto.
  eauto.
  intuition.
  intuition.

  destruct H0.
  intuition.
  subst.
  right.
  
  case_eq (evalDet_step c (skipn x s1)); intuition;
  rewrite H0 in H3.
  edestruct (evalDet_step_done_skipn).
  eauto.
  subst.
  
  inversion H3; clear H3; subst.

  exists (x + x0).
  intuition.
  eapply skipn_sum.

  inversion H3.

  edestruct (evalDet_step_more_skipn).
  eauto.
  subst.
  edestruct (evalDet_steps_done_skipn).
  eauto.
  subst.
  exists (x + (x0 + x1)).
  intuition.
  rewrite skipn_sum.
  rewrite skipn_sum.
  trivial.

Qed.

Lemma evalDet_steps_skipn : forall (A : Set)(c : Comp A)(a1 a2 : A) s1 s2,
  evalDet_steps (cs_more c s1) (cs_done a2 s2) ->
  In a1 (getSupport c) ->
  (a1 = a2 \/ (exists n, n > 0 /\ s2 = skipn n s1)).

  intuition.
  eapply evalDet_steps_skipn_h; eauto.

Qed.

Lemma evalDet_repeat_steps_dec : forall (s : Blist)(A : Set)(c : Comp A)(P : A -> bool),
  (exists a, In a (getSupport c) /\ P a = true) ->
  (forall s', (exists a s'', evalDet_steps (cs_more c s') (cs_done a s'')) \/ evalDet_steps (cs_more c s') (@cs_eof A)) ->
  exists y, evalDet_repeat_steps P (cs_more c s) y.

  intro.
  eapply (list_skipn_strong_ind s); intuition.
  destruct (H0 nil).
  destruct H1.
  destruct H1.
  destruct H.
  intuition.
  exists (cs_done x x0).
  econstructor.
  trivial.

  assert (x1 = x).
  eapply evalDet_steps_nil_eq; eauto.
  subst.
  trivial.

  exists (@cs_eof A).
  econstructor.
  trivial.

  destruct (H1 x).
  destruct H2. destruct H2.
  destruct H0; intuition.

  destruct (evalDet_steps_skipn _ H2 H3); subst.
  econstructor.
  econstructor; eauto.
  destruct H0; intuition; subst.

  case_eq (P x0); intuition.
  econstructor.
  econstructor; eauto.

  edestruct H; eauto.
  econstructor.
  eapply evalDet_repeat_steps_step.
  eapply H2.
  trivial.
  eauto.

  econstructor.
  eapply evalDet_repeat_steps_eof; eauto.
Qed.   

Lemma evalDet_repeat_steps_done_inv_h : forall (A : Set)(P : A -> bool) x y,
  evalDet_repeat_steps P x y ->
  forall c s,
  x = (cs_more c s) -> 
  evalDet_steps (cs_more (Repeat c P) s) y.

  induction 1; intuition; subst.

  inversion H1; clear H1; subst.
  econstructor.
  eauto.
  simpl.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eauto.
  rewrite H0.
  econstructor.
  eauto.
  simpl.
  econstructor.

  inversion H0; clear H0; subst.
  econstructor.
  eauto.
  simpl.
  eapply evalDet_bind_eof.
  trivial.
  
  inversion H2; clear H2; subst.
  econstructor.
  eauto.
  simpl.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eauto.
  rewrite H0.
  eauto.
  
Qed.

Lemma evalDet_repeat_steps_done_inv : forall (A : Set)(c : Comp A)(P : A -> bool) s y,
  evalDet_repeat_steps P (cs_more c s) y ->
  evalDet_steps (cs_more (Repeat c P) s) y.

  intuition.
  eapply evalDet_repeat_steps_done_inv_h; eauto.
Qed.

Lemma evalDet_repeat_steps_more_inv_h : forall (A : Set)(x y : comp_state A) P,
  evalDet_repeat_steps P x y ->
  forall (c: Comp A)(P : A -> bool) s,
  y = (cs_more c s) ->
  False.

  induction 1; intuition; subst; try discriminate.
Qed.

Lemma evalDet_repeat_steps_more_inv : forall (A : Set) x (c : Comp A)(P : A -> bool) s,
  evalDet_repeat_steps P x (cs_more c s) ->
  False.

  intuition.
  eapply evalDet_repeat_steps_more_inv_h; eauto.
Qed.

(* The result of evaluation is decidable. *)
Lemma evalDet_steps_dec : forall (A : Set)(c : Comp A),
  well_formed_comp c ->
  forall s, 
  (exists a s', evalDet_steps (cs_more c s) (cs_done a s')) \/ 
  (evalDet_steps (cs_more c s) (@cs_eof A)).
  
  induction 1; intros.
  
  left.
  exists a. exists s.
  econstructor.
  simpl.
  eauto.
  econstructor.
  
  destruct (IHwell_formed_comp s).
  destruct H2. destruct H2.
  edestruct (H1 x).
  eapply getSupport_In_evalDet_steps.
  eauto.

  destruct H3. destruct H3.
  left.
  exists x1.
  exists x2.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eauto.
  
  right.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  trivial.
  
  right.
  eapply evalDet_bind_eof; eauto.
  
  case_eq (shiftOut s n); intuition.
  left.
  destruct p.
  exists b.
  exists b0.
  econstructor.
  simpl.
  rewrite H.
  eauto.
  econstructor.
  simpl.
  eauto.
  econstructor.
  
  right.
  econstructor.
  simpl.
  rewrite H.
  eauto.
  econstructor.

  edestruct (evalDet_repeat_steps_dec).
  exists b.
  eapply filter_In; eauto.
  eauto.
  destruct x.
  left.
  econstructor.
  econstructor.
  eapply evalDet_repeat_steps_done_inv.
  eauto.

  right.
  eapply evalDet_repeat_steps_done_inv.
  eauto.

  exfalso.
  eauto using evalDet_repeat_steps_more_inv.
    
Qed.

Lemma evalDet_dec : forall (A : Set)(c : Comp A)(s : Blist),
  well_formed_comp c ->
  (exists a, evalDet c s (ca_done a)) \/ (evalDet c s (@ca_eof A)).
  
  intuition.
  edestruct (@evalDet_steps_dec _ c).
  trivial.
  destruct H0.
  destruct H0.
  left.
  econstructor.
  econstructor.
  eauto.

  right.
  econstructor.
  eauto.
  
Qed.


Lemma evalDet_step_app_done_eq : forall (A : Set)(c : Comp A) s s' s'' a,
  evalDet_step c s = (cs_done a s'') ->
  evalDet_step c (s ++ s') = (cs_done a (s'' ++ s')).
  
  induction c; intuition; simpl in *.
  inversion H; clear H; subst.
  trivial.
  
  case_eq (evalDet_step c s); intuition;
    rewrite H1 in H0; try discriminate.
  
  case_eq (shiftOut s n); intuition;
    rewrite H0 in H.
  destruct p.
  inversion H; clear H; subst.
  discriminate.

  discriminate.

Qed.

Lemma evalDet_step_app_more_eq : forall (A : Set)(c c': Comp A) s s' s'',
  evalDet_step c s = (cs_more c' s'') ->
  evalDet_step c (s ++ s') = (cs_more c' (s'' ++ s')).
  
  induction c; intuition; simpl in *.
  discriminate.
  
  case_eq (evalDet_step c s); intuition; 
    rewrite H1 in H0; try discriminate.
  inversion H0; clear H0; subst.
  erewrite evalDet_step_app_done_eq;
  eauto.
  inversion H0; clear H0; subst.
  erewrite IHc.
  eauto.
  trivial.
  
  case_eq (shiftOut s n); intuition;
    rewrite H0 in H.
  destruct p.
  inversion H; clear H; subst.
  erewrite shiftOut_app; eauto.
  discriminate.

  inversion H; clear H; subst.
  trivial.
Qed.

Lemma evalDet_steps_app_eq_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (c : Comp A) s s' s'' a,
    x = (cs_more c s) ->
    y = (cs_done a s'') ->
    evalDet_steps (cs_more c (s ++ s')) (cs_done a (s'' ++ s')).
  
  induction 1; intuition; subst.
  discriminate.
  
  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  
  econstructor.
  eapply evalDet_step_app_done_eq.
  eauto.
  econstructor.
  
  econstructor.
  
  eauto.
  erewrite evalDet_step_app_more_eq.
  eapply IHevalDet_steps.
  eauto.
  trivial.
  auto.
Qed.

Lemma evalDet_steps_app_eq : forall (A : Set)(c : Comp A) s s' s'' a,
  evalDet_steps (cs_more c s) (cs_done a s'') ->
  evalDet_steps (cs_more c (s ++ s')) (cs_done a (s'' ++ s')).
  
  intuition.
  eapply evalDet_steps_app_eq_h; eauto.
  
Qed.

Lemma evalDet_app_eq : forall (A : Set)(c : Comp A) s s' a,
  evalDet c s (ca_done a) ->
  evalDet c (s ++ s') (ca_done a).
  
  intuition.
  inversion H; clear H; subst.
  econstructor.
  eapply evalDet_steps_app_eq.
  eauto.
Qed.


Lemma evalDet_steps_done_nil_inv_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (c : Comp A) a ls,
    x = (cs_more c nil) ->
    y = (cs_done a ls) ->
    ls = nil.
  
  induction 1; intuition; subst.
  discriminate.
  
  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  eapply evalDet_step_done_nil_inv; eauto.
  assert (s = nil).
  eapply evalDet_step_more_nil_inv; eauto. subst.
  eauto.

Qed.

Lemma evalDet_steps_done_nil_inv : forall (A : Set)(c : Comp A) a ls,
  evalDet_steps (cs_more c nil) (cs_done a ls) ->
  ls = nil.
  
  intuition.
  eapply evalDet_steps_done_nil_inv_h; eauto.
Qed.

Lemma app_eq_nil_inv : forall (A : Set)(ls2 ls1 ls3 : list A),
  ls1 = ls2 ++ ls3 ->
  length ls1 = length ls2 ->
  ls3 = nil.
  
  induction ls2; intuition; simpl in *; subst.
  destruct ls3; simpl in *; trivial. omega.
  
  simpl in *.
  eapply IHls2.
  eauto.
  omega.
Qed.


Lemma evalDet_steps_repeat_done_inv_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (P : A -> bool)(c : Comp A) s a s',
  evalDet_steps x (cs_more (Repeat c P) s) ->
  y = (cs_done a s') ->
  evalDet_repeat_steps P (cs_more c s) (cs_done a s').


  induction 1; intuition; subst.
  inversion H.

  inversion H1; clear H1; subst.
  simpl in *.
  eapply evalDet_steps_bind_done_inv in H0.
  destruct H0. destruct H.
  intuition.
  case_eq (P x); intuition;
  rewrite H in H1.
  inversion H1; clear H1; subst.
  simpl in *.
  inversion H6; clear H6; subst.
  econstructor;
  eauto.
  eapply evalDet_repeat_steps_step.
  eauto.
  trivial.
  eapply IHevalDet_steps.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eauto.
  rewrite H.
  econstructor.
  trivial.

  case_eq (P a); intuition.

Qed.

Lemma evalDet_steps_repeat_done_inv : forall (A : Set)(P : A -> bool)(c : Comp A) s a s',
  evalDet_steps (cs_more (Repeat c P) s) (cs_done a s') ->
  evalDet_repeat_steps P (cs_more c s) (cs_done a s').
  
  intuition.
  eapply evalDet_steps_repeat_done_inv_h.
  eapply H.
  econstructor.
  trivial.
  
Qed.

Lemma evalDet_steps_repeat_eof_inv_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (P : A -> bool)(c : Comp A) s,
    evalDet_steps x (cs_more (Repeat c P) s) ->
    y = (cs_eof A) ->
  evalDet_repeat_steps P (cs_more c s) (cs_eof A).

  induction 1; intuition; subst.
  inversion H.

  inversion H1; clear H1; subst.
  simpl in *.
  eapply evalDet_steps_bind_eof_inv in H0.
  intuition.
  econstructor.
  trivial.
  destruct H. destruct H.
  intuition.
  case_eq (P x); intuition;
  rewrite H in H1.
  inversion H1; clear H1; subst.
  simpl in *.
  inversion H6.
  eapply evalDet_repeat_steps_step.
  eauto.
  trivial.
  eapply IHevalDet_steps.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done.
  eauto.
  rewrite H.
  econstructor.
  trivial.
  
  eauto.

Qed.

Lemma evalDet_steps_repeat_eof_inv : forall (A : Set)(P : A -> bool)(c : Comp A) s,
  evalDet_steps (cs_more (Repeat c P) s) (cs_eof A)->
  evalDet_repeat_steps P (cs_more c s) (cs_eof A).
  
  intuition.
  eapply evalDet_steps_repeat_eof_inv_h.
  eauto.
  econstructor.
  trivial.
Qed.

Lemma evalDet_repeat_steps_nil_inv_h : forall (A : Set) P (x y : comp_state A),
  evalDet_repeat_steps P x y ->
  forall (P : A -> bool) c a ls',
  x = (cs_more c nil) ->
  y = (cs_done a ls') ->
  ls' = nil.

  induction 1; intuition; subst.
  
  inversion H2; clear H2; subst.
  inversion H3; clear H3; subst.
  eapply evalDet_steps_done_nil_inv.
  eauto.

  discriminate.

  inversion H4; clear H4; subst.
  assert (s' = nil).
  eapply evalDet_steps_done_nil_inv.
  eauto.
  subst.
  eauto.

Qed.

Lemma evalDet_repeat_steps_nil_inv : forall (A : Set)(P : A -> bool) c a ls',
  evalDet_repeat_steps P (cs_more c nil) (cs_done a ls') ->
  ls' = nil.

  intuition.
  eapply evalDet_repeat_steps_nil_inv_h; eauto.

Qed.

Lemma evalDet_repeat_steps_app_nil_h : forall (A : Set) P (x y : comp_state A),
  evalDet_repeat_steps P x y ->
  forall c ls1 ls2 b a,
    x = (cs_more c ls1) ->
    y = (cs_eof A) ->
    evalDet_repeat_steps P (cs_more c (ls1 ++ b :: nil)) (cs_done a ls2)->
    (forall s s' b a,
      evalDet_steps (cs_more c s) (cs_eof A) ->
      evalDet_steps (cs_more c (s ++ b :: nil)) (cs_done a s') ->
      s' = nil) ->
    ls2 = nil.
  
  induction 1; intuition; subst.

  discriminate.

  inversion H0; clear H0; subst.
  inversion H2; clear H2; subst.
  eapply H3; eauto.

  assert (s' = nil).
  eapply H3; eauto.
  subst.  

  eapply evalDet_repeat_steps_nil_inv.
  eauto.

  inversion H2; clear H2; subst.
  inversion H4; clear H4; subst.
  assert (evalDet_steps (cs_more c0 (ls1 ++ b :: nil)) (cs_done a (s' ++ b :: nil))).
  eapply evalDet_steps_app_eq.
  trivial.
  specialize (evalDet_steps_done_func H7 H2); intuition; subst.
  congruence.

  assert (evalDet_steps (cs_more c0 (ls1 ++ b :: nil)) (cs_done a (s' ++ b :: nil))).
  eapply evalDet_steps_app_eq.
  trivial.
  specialize (evalDet_steps_done_func H6 H2); intuition; subst.
  clear H6.
  eapply IHevalDet_repeat_steps.
  eauto.
  eauto.
  eauto.
  trivial.

Qed.

Lemma evalDet_repeat_steps_app_nil : forall (A : Set)(c : Comp A) P ls1 ls2 b a,
  evalDet_repeat_steps P (cs_more c ls1) (cs_eof A) ->
  evalDet_repeat_steps P (cs_more c (ls1 ++ b :: nil)) (cs_done a ls2) ->
  (forall s s' b a,
    evalDet_steps (cs_more c s) (cs_eof A) ->
    evalDet_steps (cs_more c (s ++ b :: nil)) (cs_done a s') ->
    s' = nil) ->
  ls2 = nil.

  intuition.
  eapply evalDet_repeat_steps_app_nil_h.
  eapply H.
  eauto.
  trivial.
  eauto.
  trivial.
  
Qed.

Lemma evalDet_app_nil : forall (A : Set)(c : Comp A),
  well_formed_comp c ->
  forall ls1 ls2 b a,
  evalDet c ls1 (ca_eof A) ->
  evalDet_steps (cs_more c (ls1 ++ b :: nil)) (cs_done a ls2) ->
  ls2 = nil.
  
  induction 1; intuition; simpl in *.
  
  exfalso.
  eapply evalDet_done_eof_func; eauto.
  econstructor.
  econstructor.
  eauto.
  simpl.
  econstructor.

  apply evalDet_steps_bind_done_inv in H3.
  destruct H3. destruct H3. intuition.
  
  edestruct (@evalDet_dec _ c1 ls1).
  trivial.
  destruct H3.
  inversion H3; clear H3; subst.
  assert (evalDet_steps (cs_more c1 (ls1 ++ b :: nil)) (cs_done x1 (s' ++ b :: nil))).
  eapply evalDet_steps_app_eq.
  eauto.
  specialize (evalDet_steps_done_func H4 H3); intuition. subst.
  clear H3.
  
  edestruct (@evalDet_dec _ (c2 x1) s').
  eapply H0.
  eapply getSupport_In_evalDet_steps.
  eauto.
  destruct H3;
  inversion H3; clear H3; subst.
  exfalso.
  eapply evalDet_done_eof_func; [idtac | eapply H2].
  econstructor.
  eapply evalDet_steps_trans.
  eapply evalDet_steps_bind_done; eauto.
  eauto.
 
  eapply H1; eauto.
  eapply getSupport_In_evalDet_steps.
  eauto.
  
  assert (x0 = nil).
  eapply IHwell_formed_comp.
  eauto.
  eauto.
  subst.
  
  eapply evalDet_steps_done_nil_inv; eauto.
  
  case_eq (shiftOut ls1 n); intuition.
  destruct p.
  exfalso.
  eapply evalDet_done_eof_func; [idtac | eapply H].
  econstructor.
  econstructor.
  eauto.
  simpl.
  rewrite H1.
  econstructor.
  eauto.
  simpl.
  econstructor.
  
  inversion H0; clear H0; subst.
  simpl in *.
  apply shiftOut_None_inv in H1.
  case_eq (shiftOut (ls1 ++ b :: nil) n); intuition.
  destruct p.
  rewrite H0 in H6.
  inversion H6; clear H6; subst.
  simpl in *.
  inversion H7; clear H7; subst.
  specialize (shiftOut_Some_inv _ H0); intuition.
  apply shiftOut_correct_inv in H0.
  
  eapply app_eq_nil_inv.
  eapply H0.
  rewrite to_list_length.
  rewrite app_length in *; simpl in *.
  omega.
  
  rewrite H0 in H6.
  inversion H6.

  inversion H1; clear H1; subst.
  eapply evalDet_repeat_steps_app_nil.
  eapply evalDet_steps_repeat_eof_inv.
  eauto.
  eapply evalDet_steps_repeat_done_inv; eauto.
  intuition.
  eapply IHwell_formed_comp.
  econstructor.
  eauto.
  eauto.

Qed.

Lemma evalDet_step_done_inv : forall (A : Set)(c : Comp A) a ls ls',
  evalDet_step c ls = cs_done a ls' ->
  exists eqd, 
    c = Ret eqd a.
  
  intuition.
  destruct c; simpl in *.
  inversion H; clear H; subst.
  econstructor; eauto.
  
  case_eq (evalDet_step c ls); intuition; rewrite H0 in H; discriminate.
  
  destruct (shiftOut ls n). destruct p. discriminate.
  discriminate.

  discriminate.
  
Qed.

Lemma evalDet_step_more_sublist : forall (A : Set)(c : Comp A) c' ls ls',
  evalDet_step c ls = (cs_more c' ls') ->
  exists ls'', ls = ls'' ++ ls'.
  
  induction c; intuition; simpl in *; try discriminate.
  
  case_eq (evalDet_step c ls); intuition; rewrite H1 in H0.
  inversion H0; clear H0; subst.
  destruct (evalDet_step_done_inv _ _ H1); subst; simpl in *.
  inversion H1; clear H1; subst.
  exists nil. trivial.
  
  discriminate.
  
  inversion H0; clear H0; subst.
  eapply IHc.
  eauto.
  
  case_eq (shiftOut ls n); intuition; rewrite H0 in H.
  destruct p.
  inversion H; clear H; subst.
  exists (Vector.to_list b).
  eapply shiftOut_correct_inv.
  trivial.
  discriminate.

  inversion H; clear H; subst.
  exists nil.
  simpl.
  trivial.
      
Qed.
    
Lemma evalDet_sublist_h : forall (A : Set)(x y : comp_state A),
  evalDet_steps x y ->
  forall (c : Comp A) a ls ls' ,
    x = (cs_more c ls) ->
    y = (cs_done a ls') ->
    exists ls'', ls = ls'' ++ ls'.
  
  induction 1; intuition; subst; try discriminate.
  
  inversion H1; clear H1; subst.
  inversion H0; clear H0; subst.
  
  destruct (evalDet_step_done_inv _ _ H2). subst.
  simpl in *.
  inversion H2; clear H2; subst.
  exists nil. trivial.
  
  edestruct (IHevalDet_steps).
  symmetry. eauto.
  eauto.
  subst.
  
  symmetry in H.
  apply evalDet_step_more_sublist in H.
  destruct H.
  subst.
  exists (x0 ++ x).
  apply app_assoc.
  
Qed.

Lemma evalDet_sublist : forall (A : Set)(c : Comp A) a ls ls',
  evalDet_steps (cs_more c ls) (cs_done a ls') ->
  exists ls'', ls = ls'' ++ ls'.
  
  intuition. 
  eapply evalDet_sublist_h; eauto.
  
Qed.

Lemma evalDet_nil : forall (A : Set)(c : Comp A) a ls,
  evalDet_steps (cs_more c nil) (cs_done a ls) ->
  ls = nil.
  
  intuition.
  apply evalDet_sublist in H.
  destruct H.
  symmetry in H.
  apply app_eq_nil in H.
  intuition.
Qed.

Lemma evalDet_left_total : forall (A : Set)(c : Comp A) s,
  well_formed_comp c ->
  exists ans, evalDet c s ans.

  intuition.
  edestruct (evalDet_dec).
  eauto.
  destruct H0.
  econstructor.
  eauto.
  econstructor. 
  eauto.
Qed.
  
Lemma evalDet_steps_done_support_singleton_h : forall (A : Set)(x1 x2 : comp_state A),
  evalDet_steps x1 x2 ->
  forall (c : Comp A) a s,
    x1 = (cs_more c nil) ->
    x2 = (cs_done a s) ->
    getSupport c = a :: nil.
  
  induction 1; intuition; subst.
  discriminate.
  inversion H1; clear H1; subst.
  
  inversion H0; clear H0; subst.
  assert (s0 = nil).
  eapply evalDet_step_done_nil_inv.
  eauto.
  subst.
  eapply evalDet_step_done_support_singleton.
  eauto. 
  assert (s = nil).
  eapply evalDet_step_more_nil_inv.
  eauto.
  subst.
  
  assert (Permutation (getSupport c0) (getSupport c)).
  eapply evalDet_step_more_support_preserved.
  symmetry.
  eauto.
  assert (getSupport c = a :: nil).
  eapply IHevalDet_steps.
  eauto.
  eauto.
  rewrite H1 in H0.
  apply Permutation_sym in H0.
  apply Permutation_length_1_inv in H0.
  trivial.
  
Qed.

Lemma evalDet_steps_done_support_singleton : forall (A : Set)(c : Comp A) a s,
  evalDet_steps (cs_more c nil) (cs_done a s) ->
  getSupport c = a :: nil.
  
  intuition.
  eapply evalDet_steps_done_support_singleton_h; eauto.
  
Qed.


Lemma evalDet_step_well_formed_comp_preserved : forall (A : Set)(c : Comp A),
  well_formed_comp c ->
  forall c' s s',
    evalDet_step c s = (cs_more c' s') ->
    well_formed_comp c'.
  
  induction 1; intuition; simpl in *.
  
  discriminate.
  
  case_eq (evalDet_step c1 s); intuition;
    rewrite H3 in H2; try discriminate.
  inversion H2; clear H2; subst.
  eapply H0.
  eapply getSupport_In_evalDet_step_done; eauto.
  inversion H2; clear H2; subst.
  eapply well_formed_Bind.
  eapply IHwell_formed_comp.
  eauto.
  intuition.
  eapply H0.
  eapply getSupport_In_evalDet_step_more; eauto.
  
  case_eq (shiftOut s n); intuition;
      rewrite H0 in H; try discriminate.
  destruct p.
  inversion H; clear H; subst.
  econstructor.
  
  inversion H1; clear H1; subst.
  econstructor.
  trivial.
  intuition.
  case_eq (P b0); intuition.
  econstructor.
  econstructor.
  trivial.
  trivial.
  eauto.
  
Qed.


(*
Print OracleComp.

Definition OracleStep (A B S : Set) := 
  (S -> A -> Blist -> comp_state (B * S) -> Prop).

Inductive oracle_comp_state(A B C S : Set) :=
| ocs_oracle_running : 
  OracleComp A B C -> 
  OracleStep A B S ->
  comp_state (B * S) ->
  oracle_comp_state A B C S
| ocs_oracle_done : 
  OracleComp A B C -> 
  OracleStep A B S ->
  B * S ->
  Blist ->
  oracle_comp_state A B C S
| ocs_more : 
  OracleComp A B C -> 
  OracleStep A B S ->
  S ->
  Blist -> 
  oracle_comp_state A B C S
| ocs_done : 
  C * S ->
  Blist -> 
  oracle_comp_state A B C S
| ocs_eof : 
  oracle_comp_state A B C S.
    
Print OracleComp.

Inductive oc_det_step : forall (A B C S : Set), oracle_comp_state A B C S -> oracle_comp_state A B C S -> Prop :=
| oc_det_oracle_step : 
  forall (A B C S : Set)(c : OracleComp A B C)(o : OracleStep A B S)(c_o : Comp (B * S))(x : Blist) cs',
    evalDet_step c_o x = cs' ->
    oc_det_step (ocs_oracle_running c o (cs_more c_o x)) (ocs_oracle_running c o cs')
| oc_det_oracle_eof : 
  forall (A B C S : Set)(c : OracleComp A B C)(o : OracleStep A B S)(c_o : Comp (B * S))(x : Blist),
    oc_det_step (ocs_oracle_running c o (cs_eof _)) (ocs_eof A B C S)
| oc_det_query_start : 
  forall (A B S: Set)(a : A)(o : OracleStep A B S) (s : S) (r : Blist) cs_o,
    o s a r cs_o -> 
    oc_det_step (ocs_more (@OC_Query A B a) o s r) (ocs_oracle_running (@OC_Query A B a) o cs_o)
| oc_det_query_finish : 
  forall (A B S: Set)(a : A)(o : OracleStep A B S) (r : Blist) z,
    oc_det_step (ocs_oracle_running (@OC_Query A B a) o (cs_done z r)) (ocs_done _ _ z r) 
| oc_det_run_start : 
  forall (A A' B B' C S S' : Set)
    (eqds : EqDec S)(eqdb : EqDec B)(eqda : EqDec A)(c : OracleComp A B C)(o : S -> A -> OracleComp A' B' (B * S))(s : S)(o' : OracleStep A' B' S')(s' : S')(r : Blist),
    oc_det_step 
    (ocs_more (OC_Run c _ _ _ o s) o' s' r) 
    (ocs_more c (fun x y z => oc_det_step (ocs_more (o (fst x) y) o' (snd x) z)) (s, s') r).
    
*)