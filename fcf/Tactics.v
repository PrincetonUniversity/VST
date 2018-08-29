(* Copyright 2012-2015 by Adam Petcher.				*
 * Use of this source code is governed by the license described	*
 * in the LICENSE file at the root of the source tree.		*)
Set Implicit Arguments.

Require Import fcf.Crypto.
Require Import fcf.DistTacs.
Require Import fcf.ProgTacs.
Require Import fcf.GenTacs.
Require Import fcf.ProgramLogic.


(** * Tactics Overview *)
(** This file contains the most commonly-used tactics and theorems in FCF.  In most cases, tactics are provided which apply the appropriate theorem, but in a few cases the theorem from the FCF library must be applied directly.  In general, a single tactic is provided that can be used on goals related to probability as well as goals in the program logic.  The tactic will examine the goal and apply the appropriate form of the required theorem.  *)

(** * Basic One-sided Tactics *)
(** These tactics are used to perform simple transformations on a probabilistic program.  Each tactic expects the goal to be a relation on a pair of programs and the tactic takes a single argument (either fcf_left or fcf_right) to indicate whether the program on the left or the program on the right should be modified.  These tactics always modify the first instruction of the specified program, and the comp_at tactical can be used to modify statements at other positions. *)

Notation fcf_right := rightc.
Notation fcf_left := leftc.

(** ** fcf_inline *)
(** The fcf_inline tactic applies monad associativity to replace (x <- (y <- p1; p2); p3) with (y <- p1; x <- p2; p3).  Note that the fcf_inline_first will repeatedly invoke this tactic to inline the first nested program on both sides of the relation. *)
(** Supporting thoery: evalDist_assoc (probability), comp_spec_assoc (program logic) *)
Ltac fcf_inline := comp_inline.

(** ** fcf_swap *)
(** The fcf_swap tactic swaps the order of two independent statements in a program.  That is, it replaces (x <- p1; y <- p2; p3) with (y <- p2; x <- p1; p3) as long as x does not appear free in p2.  *)
(** Supporting theory: evalDist_commute (probability), comp_spec_eq_swap (program logic) *)
Ltac fcf_swap := comp_swap.

(** ** fcf_ret *)
(** The fcf_ret tactic applies monad left identity to replace (x <- ret y; (p1 x)) with (p1 y).  Note that the fcf_simp tactic will repeatedly invoke this tactic to simplify both programs in a relation. *)
(** Supporting theory: evalDist_left_ident (probability), comp_spec_left_ident (program logic) *)
Ltac fcf_ret := comp_ret.

(** * Other one-sided Tactics *)
(** ** fcf_irr *)
(** The fcf_irr_l/fcf_irr_r tactic simplifies the program on the left/right (respectively) by removing the first statement and the information related to the distribution on the values produced by the statement.  This tactic can be used when this distribution is irrelevant, and the only information necessary is that the value produced is in the support of the distribution.  The tactic introduces a variable containing the value produced by the statement, and a hypothesis stating that the value is in the support of the distribution corresponding with the statement that was removed.  Only well-formed program statements can be removed in this way, so the tactic will produce a goal to prove that the removed statement is well-formed.*)
(** Supporting theory: evalDist_irr_l and evalDist_irr_r (probability), comp_spec_irr_l and comp_spec_irr_r (program logic)  *)
Ltac fcf_irr_l := comp_irr_l.

Ltac fcf_irr_r := comp_irr_r.

(** ** fcf_inline_first *)
(** The fcf_inline_first tactic repeatedly applies the fcf_inline tactic to both programs to extract the first nested statement.  This tactic is useful for producing a statements that can be skipped over using fcf_skip or fcf_irr. *)
Ltac fcf_inline_first := inline_first.

(** ** fcf_simp *)
(** The fcf_simp tactic performs a number of simplifications to make programs easier to read and manipulate.  For example, the tactic applies fcf_ret to replace ret statements at the beginning of the programs.  *)
Ltac fcf_simp := comp_simp.

(** ** fcf_ident_expand *)
(** The fcf_ident_expand_l/fcf_ident_expand_r tactic replace the program on the left/right by expanding it using the monad right identity.  That is, it will replace the program (p1) with (x <- p1; ret x).  This operation can be used to put two programs into the same form so that fcf_skip can be employed. *)
(** Supporting theory:  evalDist_right_ident (probability), comp_spec_right_ident (program logic) *)
Ltac fcf_ident_expand_l :=
  dist_ident_expand_l || prog_ident_expand_l.

Ltac fcf_ident_expand_r :=
  dist_ident_expand_r || prog_ident_expand_r.

(** ** fcf_rewrite_expr *)
(** The fcf_rewrite_expr tactic takes and expression and rewrites the current goal using that expression.  The tactic then produces a goal to prove the expression.  This tactic is simular to Coq's cutrewrite tactic, except that it accepts expressions that are not primitive identities.  Note that several FCF relations are registered as setoids, and can therefore be used to rewrite using this tactic or Coq's rewrite tactic.  Setoid relations include equality and inequality for rational numbers, and (comp_spec eq). *)
Ltac fcf_rewrite_expr e :=
  let x := fresh "x" in
  assert e as x; [idtac | rewrite x; clear x].

(** ** fcf_rewrite *)
(** The fcf_rewrite_l/fcf_rewrite_r tactic accepts a program and attempts to rewrite the entire program on the left/right (respectively) to the specified program.  This tactic will produce an obligation to prove that the program is appropriately related to the specified program. *)
Ltac fcf_rewrite_l t :=
  match goal with 
    | [|- ?a == _ ] =>
      fcf_rewrite_expr (a == t)
    | [|- ?a <= _ ] =>
      fcf_rewrite_expr (a <= t)
  end.

Ltac fcf_rewrite_r t :=
  match goal with 
    | [|- _ == ?a ] =>
      fcf_rewrite_expr (a == t)
    | [|- _ <= ?a ] =>
      (* with a bit more work here, we could rewrite with (t <= a) *)
      fcf_rewrite_expr (a == t)
  end.

(** * Two-sided tactics *)

(** ** fcf_skip *)
(** The fcf_skip tactic removes the first pair of statements from both programs and replaces them with a relation on the values produced by those statements.  This tactic attempts to locate such a relation, and it produces a proof obligation to prove the relation when no such relation is found.  If the goal is in the program logic, then the relation in the produced goal will be a unification variable, allowing the developer to provide a proof of any relation of the appropriate type.  Note that this tactic is sometimes overly eager to determine the desired relation, and so it may sometimes be necessary to apply the underlying theory directly.  *)
(** Supporting theory: evalDist_seq (probability), comp_spec_seq (program logic) *)
Ltac fcf_skip := comp_skip.

(** ** fcf_skip_eq *)
(** The fcf_skip_eq tactic is a specialized version of fcf_skip that can only be used on program logic goals, and that asserts that the relation on the result of the first pair of statements is equality. *)
(** Supporting theory: comp_spec_seq_eq *)
Ltac fcf_skip_eq := prog_skip_eq.

(** ** fcf_to_prhl *)
(** The fcf_to_prhl tactic converts the current goal from probability expression to the equivalent program logic judgment. *)
(** Supporting theory: comp_spec_impl_eq (for equality goals), comp_spec_impl_le (for inequality goals) *)
Ltac fcf_to_prhl := 
  match goal with
    | [|- _ == _] => eapply comp_spec_impl_eq
    | [|- _ <= _] => eapply comp_spec_impl_le
  end.

(** ** fcf_to_prhl_eq *)
(** The fcf_to_prhl_eq is a variant of fcf_to_prhl that produces a stronger goal that is nonetheless often simpler to prove.  If the goal is an equality, then fcf_to_prhl with produce an obligation to prove a relation like (fun a b => a = x <-> b = y) for some particular values x and y.  In this circumstance, fcf_to_prhl_eq will prove the relation (eq), which implies the previous relation. *)
(** Supporting theory: comp_spec_seq_eq *)
Ltac fcf_to_prhl_eq := eapply comp_spec_eq_impl_eq.

(** ** fcf_to_probability *)
(** The fcf_to_probability tactic replaces certain program logic goals with the equivalent goals in probability theory.  In order to use this tactic, the relation must be one of the following: (eq), (fun a b, a = x <-> b = y) for any values x and y, or (fun a b => a = x -> b = y) for any values x and y. *)
(** Supporting theory: eq_impl_comp_spec, le_impl_comp_spec *)
Ltac fcf_to_probability :=
  match goal with 
    | [|- comp_spec (fun a b => a = _ -> b = _) _ _ ] => eapply le_impl_comp_spec
    | [|- comp_spec (fun a b => a = _ <-> b = _) _ _ ] => eapply eq_impl_comp_spec
    | [|- comp_spec eq _ _ ] => eapply comp_spec_consequence; [eapply eq_impl_comp_spec | idtac]
  end.

(** ** fcf_transitivity *)
(** The fcf_transitivity tactic will introduce an intermediate program and two goals to show that each of the initial pair of programs is appropriately related to the new program.  For probability goals, the required relation will be equality or inequality (depending on the relation in the original goal).  For program logic goals, the new proof obligations require that the program on the left is related to the new program by the relation (eq), and that the new program is related to the program on the right by the relation in the original goal. *)
(** Supporting theory: eqRat_trans and leqRat_trans (probability), comp_spec_eq_trans_l (program logic) *)
Ltac fcf_transitivity := dist_transitivity || prog_transitivity.

(** ** fcf_transitivity_r *)
(** The fcf_transitivity_r tactic is a variant of fcf_transitivity that only works on program logic goals, and swaps the order of the produced proof obligations.  That is, the program on the left must be related to the new program by the original relation, and the new program must be related to the program on the right by the relation (eq). *)
(** Supporting theory: comp_spec_eq_trans_l *)
Ltac fcf_transitivity_r := prog_transitivity_r.

(** ** fcf_reflexivity *)
(** The fcf_reflexivity tactic discharges a goal by stating that the programs are exactly equal.  The goal must be a probability (in)equality or (comp_spec eq), and both programs must be identical (according to Coq conversion). *)
Ltac fcf_reflexivity := reflexivity || apply comp_spec_eq_refl.
(** Supporting theory: eqRat_refl and leRat_refl (probability), comp_spec_eq_refl (program logic) *)


(** ** fcf_symmetry *)
(** The fcf_symmetry tactic replaces a proof obligation with two games with the equivalent obligation in which the order of the two games have been reversed.  This tactic applies to symmetric relations, and some non-symmetric relations for which the tactic is able to determine the correct relation to use for the new goal. *)
(** Supporting theory: eqRat_symm (probability), comp_spec_eq_symm and comp_spec_symm (program logic) *)
Ltac fcf_symmetry := symmetry || prog_symmetry.


(** ** fcf_spec_ret *)
(** The fcf_spec_ret tactic applies to program logic goals in which both programs are of the form (ret p1) for some p1.  The tactic replaces the current goal with the corresponding goal in the underlying logic.  The tactic will also simplify this goal and attempt to discharge it (if it is trivial). *)
(** Supporting theory: comp_spec_ret *)  
Ltac fcf_spec_ret :=
  eapply comp_spec_ret; trivial; intuition.



(** * Tacticals *)
(** ** fcf_at *)
(** The fcf_at tactical is used to apply some other tactic at a certain position in a program.   *)
(** *** Arguments *)
(** t -- any tactic that operates on the first statement in a program and accepts an argument indicating which program (fcf_left or fcf_right) should be modified.  Only the name of the tactic should be supplied *)
(** s -- the side of the relation (i.e. which program) should be modified.  Either fcf_left or fcf_right. *)
(** l -- the "line" number, or statement number where the tactic should be applied.  *)
Ltac fcf_at t s l := comp_at t s l.


(** ** fcf_with *)
(** The fcf_with tactical brings a fact in the environment and then invokes another tactic.  This tactical is useful for tactics like fcf_skip that look in the environment for an appropriate fact relating a pair of programs.  *)
(** *** Arguments *)
(** pf -- the name of some fact (theorem or hypothesis) that is not present in the current set of hypotheses.  *)
(** t -- the tactic to execute with the additional fact in the environment. *)
Ltac fcf_with pf t :=
    let x := fresh "x" in
    pose proof pf as x;
      t; 
      clear x.

(** * Other probabilistic tactics *)
(** ** fcf_fundamental_lemma *)
(** The fcf_fundamental_lemma tactic applies the fundamental lemma to prove that the distance between two terms is bounded by the probability of some "bad" event.  This tactic applies to goals of the form (| Pr[x <- p1; ret (fst x)] - Pr[x <- p2; ret (fst x)] | <= Pr[x <- p1; ret (snd x)]).  The programs p1 and p2 both return a pair of values, where the first is some value of interest, and the second is a bool indicating that some "bad" event occurred.  This tactic applies the fundamental lemma and produces two proof obligations.  The first obligation is to show that the probability of the "bad" event is the same in both games.  The second obligation is to show that the distributions on the events of interest are the same unless the "bad" event occurs. *)
(** Supporting theory: fundamental_lemma_h *)
Ltac fcf_fundamental_lemma := apply fundamental_lemma_h.


(** ** fcf_compute *)
(** The fcf_compute tactic will discharge simple goals related to the calculation of probability values.  The reasoning of this tactic is not very sophisticated---it merely applies the denotational semantics, simplifies, performs some case splits, and applies the underlying logic.  *)
(** Example:
Theorem fcf_compute_example :
  Pr[x <-$ {0, 1}; y <-$ {0, 1}; ret (x && y)] == 1/4.
  fcf_compute.
Qed. 
*)
Ltac fcf_compute := dist_compute.

(** * Other non-probabilistic tactics *)
(** ** fcf_well_formed *)
(** The fcf_well_formed tactic simplifies and attempts to automatically discharge goals related to the well-formedness of programs.  If the goal looks like "well_formed_comp p1" or "well_formed_oc p1", then this tactic can often be used to discharge the goal or make progress toward proving it.  *)
Ltac fcf_well_formed := wftac.

(** ** fcf_simp_in_support *)
(** Many FCF theorems and tactics will add assumptions to the environment stating that some value is in the support of some distribution defined by a probabilistic program.  This hypothesis carries no probabilistic information, but it may provide some useful set-theoretic information.  The simp_in_support tactic will automatically destruct these hypotheses and extract this set-theoretic information.  This extraction will often result in the introduction of new variables (e.g. destructing a sequence in this manner will introduce a variable describing the value after the first statement in the sequence is executed).  *)  
Ltac fcf_simp_in_support := repeat simp_in_support.

(** * Theorems *)
(** The theorems in this section are provided here because it may be more convenient to apply them directly, rather than invoking the tactic that applies them.  In some cases, no such tactic is provided.  This is due to way Coq handles implicit arguments and tactic invocation, and the fact that it is sometimes more convenient to simply apply the desired theorem directly.  *)

(** ** fcf_spec_seq *)
(** The fcf_spec_seq theorem behaves like the tactic fcf_skip.  Importantly, this theorem accepts the relational predicate that must hold after the first pair of games is executed.  It can often be valuable to specify this predicate in the sequence rule to avoid having to fill it in later.  *)
Theorem fcf_spec_seq : 
  forall {A B : Set} (P' : A -> B -> Prop) {C D : Set} P{eqda : EqDec A}{eqdb : EqDec B}{eqdc : EqDec C}{eqdd : EqDec D}(c1 : Comp A)(c2 : Comp B) (c : C) (d : D)
    (f1 : A -> Comp C)(f2 : B -> Comp D),
    comp_spec P' c1 c2 ->
    (forall a b, In a (getSupport c1) -> In b (getSupport c2) -> P' a b -> comp_spec P (f1 a) (f2 b)) ->
    comp_spec P (Bind c1 f1) (Bind c2 f2).

  intuition.
  eapply comp_spec_seq; intuition; eauto.

Qed.

(** ** fcf_oracle_eq *)
(** The fcf_oracl_eq theorem is used to replace an oracle with an observationally equivalent oracle.  This theorem accepts a relational predicate that specifies an invariant on the states of the oracles.  The resulting proof obligations will be to show that the invariant holds on the initial state, and the when the invariant holds on any state, the oracles produce identical output for all inputs and the invariant still holds on the resulting state. *)
Theorem fcf_oracle_eq :
  forall {S1 S2 : Set}(P : S1 -> S2 -> Prop)(A B C : Set) (c : OracleComp A B C) 
         (eqdb : EqDec B) (eqdc : EqDec C) 
         (o1 : S1 -> A -> Comp (B * S1)) (o2 : S2 -> A -> Comp (B * S2))
         (eqds1 : EqDec S1) (eqds2 : EqDec S2) (s1 : S1) 
         (s2 : S2),
    P s1 s2 ->
    (forall (a : A) (x1 : S1) (x2 : S2),
       P x1 x2 ->
       comp_spec
         (fun (y1 : B * S1) (y2 : B * S2) =>
            fst y1 = fst y2 /\ P (snd y1) (snd y2)) 
         (o1 x1 a) (o2 x2 a)) ->
    comp_spec
      (fun (a : C * S1) (b : C * S2) => fst a = fst b /\ P (snd a) (snd b))
      (c S1 eqds1 o1 s1) (c S2 eqds2 o2 s2).
  
  intuition.
  eapply oc_comp_spec_eq; intuition.
  
Qed.

(** ** fcf_oracle_eq_until_bad *)
(** The fcf_oracle_eq_until_bad theorem is similar to fcf_oracle_eq, except it allows the state of the oracles to go "bad", and the resulting fact is that the oracles are indistinguishable unless this bad event occurs.  This fact can be used with the fundamental lemma to bound the distance between a pair of program/oracle interactions. *)
Theorem fcf_oracle_eq_until_bad : 
  forall {S1 S2 : Set}(bad1 : S1 -> bool)
         (bad2 : S2 -> bool)(inv : S1 -> S2 -> Prop)(A B C : Set) (c : OracleComp A B C),
    well_formed_oc c ->
    forall (eqdb : EqDec B) (eqdc : EqDec C) 
           (o1 : S1 -> A -> Comp (B * S1)) (o2 : S2 -> A -> Comp (B * S2))
           (eqds1 : EqDec S1) (eqds2 : EqDec S2),
      (forall (a : S1) (b : A), bad1 a = true -> well_formed_comp (o1 a b)) ->
      (forall (a : S2) (b : A), bad2 a = true -> well_formed_comp (o2 a b)) ->
      (forall (x1 : S1) (x2 : S2) (a : A),
         inv x1 x2 ->
         bad1 x1 = bad2 x2 ->
         comp_spec
           (fun (y1 : B * S1) (y2 : B * S2) =>
              bad1 (snd y1) = bad2 (snd y2) /\
              (bad1 (snd y1) = false -> inv (snd y1) (snd y2) /\ fst y1 = fst y2))
           (o1 x1 a) (o2 x2 a)) ->
      (forall (a : B) (b c0 : S1) (d : A),
         bad1 c0 = true -> In (a, b) (getSupport (o1 c0 d)) -> bad1 b = true) ->
      (forall (a : B) (b c0 : S2) (d : A),
         bad2 c0 = true -> In (a, b) (getSupport (o2 c0 d)) -> bad2 b = true) ->
      forall (s1 : S1) (s2 : S2),
        inv s1 s2 ->
        bad1 s1 = bad2 s2 ->
        comp_spec
          (fun (y1 : C * S1) (y2 : C * S2) =>
             bad1 (snd y1) = bad2 (snd y2) /\
             (bad1 (snd y1) = false -> inv (snd y1) (snd y2) /\ fst y1 = fst y2))
          (c S1 eqds1 o1 s1) (c S2 eqds2 o2 s2).
  
  intuition.
  eapply oc_comp_spec_eq_until_bad; intuition.
  
Qed.











