(* moved to coqlib4

(** Additions to [if_tac]: when mature, move these upstream *)

Tactic Notation "if_tac" "eq:" simple_intropattern(E) :=
  match goal with
    |- context [if ?a then _ else _] =>
    destruct a as [?H | ?H] eqn:E
  end.

Tactic Notation "if_tac" simple_intropattern(H) "eq:" simple_intropattern(E):=
  match goal with
    |- context [if ?a then _ else _] =>
    destruct a as H eqn:E
  end.

Tactic Notation "if_tac" "in" hyp(H0) "eq:" simple_intropattern(E) :=
  match type of H0 with
    context [if ?a then _ else _] =>
    destruct a as [?H  | ?H] eqn:E
  end.

Tactic Notation "if_tac" simple_intropattern(H) "in" hyp(H1) "eq:" simple_intropattern(E) :=
  match type of H1 with
    context [if ?a then _ else _] =>
    destruct a as H eqn:E
  end.

(** Specializing a hypothesis with a newly created goal *)

Tactic Notation "assert_specialize" hyp(H) :=
  match type of H with
    forall x : ?P, _ =>
    let Htemp := fresh "Htemp" in
    assert P as Htemp; [ | specialize (H Htemp); try clear Htemp ]
  end.

Tactic Notation "assert_specialize" hyp(H) "by" tactic(tac) :=
  match type of H with
    forall x : ?P, _ =>
    let Htemp := fresh "Htemp" in
    assert P as Htemp by tac; specialize (H Htemp); try clear Htemp
  end.

Tactic Notation "assert_specialize" hyp(H) "as" simple_intropattern(Hnew) :=
  match type of H with
    forall x : ?P, _ =>
    assert P as Hnew; [ | specialize (H Hnew) ]
  end.

Tactic Notation "assert_specialize" hyp(H) "as" simple_intropattern(Hnew) "by" tactic(tac) :=
  match type of H with
    forall x : ?P, _ =>
    assert P as Hnew by tac;
    specialize (H Hnew)
  end.

(** Auto-specializing a hypothesis *)

Ltac autospec H := specialize (H ltac:(solve [eauto])).

(** When a hypothesis/term is provably equal, but not convertible, to
    your goal *)

Ltac exact_eq H :=
  revert H;
  match goal with
    |- ?p -> ?q => cut (p = q); [intros ->; auto | ]
  end.

(** Auto rewriting of a term *)

Tactic Notation "rewr" :=
  match goal with
  | H : ?f = _ |- context [?f] => rewrite H
  | H : ?f _ = ?f _ |- _ => try (injection H; repeat intros ->)
  end.

Tactic Notation "rewr" constr(e) :=
  match goal with
    E : e = _ |- _ => rewrite E
  | E : _ = e |- _ => rewrite <-E
  end.

Tactic Notation "rewr" constr(e) "in" "*" :=
  match goal with
    E : e = _ |- _ => rewrite E in *
  | E : _ = e |- _ => rewrite <-E in *
  end.

Tactic Notation "rewr" constr(e) "in" hyp(H) :=
  match goal with
    E : e = _ |- _ => rewrite E in H
  | E : _ = e |- _ => rewrite <-E in H
  end.


*)
