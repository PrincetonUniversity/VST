(** A little module for doing naive congruence closure; we don't need anything
    much fancier because in practice, for spatial entailments, we only discover
    a few new equalities in each call to the superposition subsystem.

    Pure entailments are another matter entirely, but for now we seem to be fine
    on those (see, eg, test/test.pure.entailments.sf) *)

Load loadpath.
Require Import List veric.Coqlib2 msl.base.
Require Import VST.msl.predicates_sa.
Require Import veristar.datatypes veristar.clauses veristar.clause_lemmas
               veristar.list_denote veristar.basic veristar.compare.
Require Import veristar.model_type veristar.model.

Section cclosure.
Context (A B : Type).
Variables
  (A_cmp : A -> A -> comparison)
  (B_cmp : B -> B -> comparison)
  (fAB : A -> B).

Notation canons := (list (A*B)).

(*Definition isEq (c : comparison) := match c with Eq => true | _ => false end.*)

Fixpoint lookC (a: A) (cs: canons) : B :=
  match cs with nil => fAB a
  | (a1, b1)::cs' => if isEq (A_cmp a a1) then b1
                     else lookC a cs'
  end.

Fixpoint rewriteC (b1 b2 : B) (cs: canons) : canons :=
  match cs with nil => nil
  | (a1, b1')::cs' =>
    let new_cs := rewriteC b1 b2 cs' in
    if isEq (B_cmp b1 b1') then (a1, b2)::new_cs else (a1, b1')::new_cs end.

Definition mergeC (a1 a2 : A) (cs: canons) : canons :=
  match lookC a1 cs, lookC a2 cs with b1, b2 =>
    if isEq (B_cmp b1 b2) then cs
    else (a1, b2)::(a2, b2)::rewriteC b1 b2 cs end.

(* sanity lemmas *)
(*
Lemma lookC_cons a1 b cs : lookC a1 ((a1, b)::cs) = b.
Proof. unfold lookC; simpl. if_tac; auto. exfalso; apply H; auto. Qed.

Lemma lookC_cons2 a1 a2 b cs :
  lookC a1 ((a2, b)::cs) = if A_eq_dec a1 a2 then b else lookC a1 cs.
Proof. unfold lookC; simpl. if_tac; auto. Qed.

Lemma mergeC_lookC a1 a2 cs :
  lookC a1 (mergeC a1 a2 cs) = lookC a2 (mergeC a1 a2 cs).
Proof with simpl; auto; try solve[congruence].
induction cs... unfold mergeC. if_tac... if_tac... if_tac... if_tac...
unfold mergeC; if_tac; auto.
rewrite lookC_cons. rewrite lookC_cons2. if_tac; auto. rewrite lookC_cons...
Qed.
*)
End cclosure.

(*
Module TestCClosure.
Require Import NatOrderedType. Import Nat_as_DT.

Notation lookC := (lookC _ _ eq_dec (fun n => n)).
Notation rewriteC := (@rewriteC nat nat eq_dec).
Notation mergeC := (mergeC _ _ eq_dec eq_dec (fun n => n)).

Compute mergeC 1 2 nil.
Compute mergeC 1 2 (mergeC 3 4 nil).
Compute lookC 3 (mergeC 1 2 (mergeC 3 4 (mergeC 5 6 nil))).
Compute lookC 3 (mergeC 4 5 (mergeC 3 4 (mergeC 5 6 nil))).
Compute lookC 3 (mergeC 1 8 (mergeC 3 4 (mergeC 1 3 (mergeC 1 2 nil)))).

End TestCClosure.
*)

Notation expr_get := (lookC _ _ expr_cmp (@id _)).
Notation expr_merge := (mergeC _ _ expr_cmp expr_cmp (@id _)).

(* used internally *)
Local Notation expr_rewriteC := (rewriteC expr _ expr_cmp).

Fixpoint cclose_aux (l : list clause) : list (expr * expr) :=
  match l with
  | PureClause nil [Eqv s t] _ _ :: l' => expr_merge s t (cclose_aux l')
  | _ => nil
  end.

Definition cclose (l : list clause) : list clause :=
  map (fun p => match p with (e1, e2) => mkPureClause nil [Eqv e1 e2] end)
    (cclose_aux l).

(** Correctness proof *)

Module CCSound (VSM : VERISTAR_MODEL).
Import VSM VeriStarLogic.

Definition expr_eqs_denote (l : list (expr * expr)) :=
  listd (fun p => match p with (e1, e2) => (e1 === e2) end) inter TT l.

Lemma expr_get_sound e l s : expr_eqs_denote l s -> (e === expr_get e l) s.
Proof with simpl; auto.
induction l... unfold id... intros; apply var_eq_refl.
destruct a. intros [H1 H2]. remember (expr_cmp e e0) as b. destruct b...
assert (H3 : true = expr_eq e e0). unfold expr_eq. rewrite <-Heqb...
apply expr_eq_eq' in H3; subst...
Qed.

Lemma expr_rewriteC_sound e1 e2 l s :
  (e1 === e2) s -> expr_eqs_denote l s ->
  expr_eqs_denote (expr_rewriteC e1 e2 l) s.
Proof with simpl; auto.
intros H0; induction l... intros [H1 H2]; destruct a as [e e0].
spec IHl H2. remember (isEq (expr_cmp e1 e0)). destruct b...
split; auto.
apply var_eq_trans with (y:=e0)...
apply var_eq_trans with (y:=e1)...
do_comp expr_cspec e1 e0; try solve[simpl in Heqb; congruence].
split; auto.
Qed.

Lemma expr_merge_sound e1 e2 l s :
  expr_eqs_denote l s -> (e1 === e2) s ->
  expr_eqs_denote (expr_merge e1 e2 l) s.
Proof with simpl; auto.
induction l... unfold lookC, mergeC, id... if_tac... firstorder.
destruct a. intros [H1 H2]. unfold mergeC.
remember (isEq (expr_cmp (expr_get e1 ((e, e0) :: l))
                             (expr_get e2 ((e, e0) :: l)))) as b.
destruct b. simpl. intros H3. split; auto.
intros H3. unfold expr_eqs_denote. rewrite listd_cons.
split; auto.
assert (H4 : (e2 === expr_get e2 ((e, e0) :: l)) s).
  apply expr_get_sound. simpl. split; auto.
apply var_eq_trans with (y:=e2); auto.
rewrite listd_cons. split.
apply expr_get_sound. simpl. split; auto.
apply expr_rewriteC_sound.
assert (H4 : (e1 === expr_get e1 ((e, e0) :: l)) s).
  apply expr_get_sound... split...
apply var_eq_trans with (y:=e1). apply var_eq_sym; auto.
apply var_eq_trans with (y:=e2); auto. apply expr_get_sound.
split; auto.
simpl; split; auto.
Qed.

Lemma cclose_aux_sound l s :
  listd clause_denote inter TT l s -> expr_eqs_denote (cclose_aux l) s.
Proof with simpl; auto.
induction l...
destruct a... destruct gamma... destruct delta...
destruct p... destruct delta...
intros [H1 H2]. simpl in H1. spec H1. auto.
inversion H1 as [H3|H3]; [|inversion H3].
apply expr_merge_sound...
Qed.

Lemma cclose_sound l s :
  listd clause_denote inter TT l s -> listd clause_denote inter TT (cclose l) s.
Proof.
intros H1. unfold cclose. apply listd_map_pred
  with (f:=(fun p => match p with (e1, e2) => (e1 === e2) end)).
intros [a1 a2]; simpl; firstorder.
apply cclose_aux_sound; auto.
Qed.

End CCSound.