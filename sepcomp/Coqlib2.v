Require Export msl.Extensionality.
Require Import Coqlib.
Require Export msl.Coqlib2.


Ltac spec H :=
  match type of H with ?a -> _ => 
    let H1 := fresh in (assert (H1: a); [|generalize (H H1); clear H H1; intro H]) end.


Lemma f_equal_Some: forall A (x y: A), x=y -> Some x = Some y.
Proof.
intros; f_equal; auto.
Qed.

Lemma f_equal_prod: forall A B (x1 x2: A) (y1 y2: B), x1=x2 -> y1=y2 -> (x1,y1) = (x2,y2).
Proof.
intros; f_equal; auto.
Qed.

Hint Resolve f_equal_Some f_equal_prod.

Unset Implicit Arguments.

Lemma list_norepet_append_inv:
  forall (A : Set) (l1 l2 : list A),
   list_norepet (l1 ++ l2) -> 
  list_norepet l1 /\ list_norepet l2 /\ list_disjoint l1 l2.
Proof.
induction l1; simpl; intros.
repeat split; auto. constructor. do 3 intro.
contradiction H0.
inversion H; clear H; subst.
destruct (IHl1 l2 H3) as [? [? ?]].
repeat split; auto.
constructor 2.
intro. contradiction H2. apply in_or_app. auto.
auto.
do 4 intro. intro.
subst.
simpl in H4. destruct H4.
subst. contradiction H2.
apply in_or_app. auto.
unfold list_disjoint in H1.
contradiction (H1 y y H4 H5); auto.
Qed.

Set Implicit Arguments.

(*  The built-in "remember" tactic is weaker than this one!
  The built-in one can lead to "Error: The correctness of the conclusion relies on the body of a"
  where this one will succeed. 
  [this comment may be obsolete, perhaps from Coq 8.2 or before 
Tactic Notation "remember" constr(a) "as" ident(x) :=
   let x := fresh x in
  let H := fresh "Heq" x in
  (set (x:=a) in *; assert (H: x=a) by reflexivity; clearbody x).
*)

Tactic Notation "if_tac" := match goal with |- context [if ?a then _ else _] => destruct a as [?H | ?H] end.
Tactic Notation "if_tac" simple_intropattern(H) 
   := match goal with |- context [if ?a then _ else _] => destruct a as H end.
Tactic Notation "if_tac" "in" hyp(H0) 
 := match type of H0 with context [if ?a then _ else _] => destruct a as [?H | ?H] end.
Ltac if_tac_in H := match type of H with context [if ?a then _ else _] => destruct a as [?H0 | ?H0] end.
Tactic Notation "if_tac" simple_intropattern(H) "in" hyp(H1)
 := match type of H1 with context [if ?a then _ else _] => destruct a as H end.

Lemma predicate_max:
  forall (F: nat -> Prop) (Fdec: forall n, {F n}+{~ F n}) n,
  F 0%nat ->
  ~ F n ->
  exists i, F i /\ (i<n)%nat /\ ~ F (S i).
Proof.
intros.
assert (forall m, (m <= n)%nat ->
         (forall k, (k<m)%nat -> F k) \/ 
         (exists i, F i /\ (i<m)%nat /\ ~ F (S i))).
induction m.
left; intros.
omegaContradiction.
intro.
assert (m<=n)%nat; try omega.
destruct (IHm H2).
assert (m < n \/ m = n)%nat; try omega.
destruct H4.
destruct (Fdec m) as [?H|?H].
left.
intros.
assert (k < m \/ k = m)%nat; try omega.
destruct H7.
auto.
subst k; auto.
right.
exists (Peano.pred m).
destruct m.
contradiction.
replace (Peano.pred (S m)) with m; try omega.
split.
apply H3; try omega.
split; try omega.
auto.
subst m.
right.
destruct n.
contradiction.
exists n; repeat split; auto; try omega.
right.
destruct H3 as [i H4].
destruct H4.
destruct H4.
exists i; repeat split; auto; omega.
assert (n <= n)%nat; try omega.
destruct (H1 _ H2).
destruct n; try contradiction.
exists n; repeat split; auto; try omega.
auto.
Qed.
