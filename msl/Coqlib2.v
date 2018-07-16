Require Import compcert.lib.Coqlib.
Require Import VST.msl.base.
Require Export VST.msl.Extensionality.

(*  These three hints are considered "dangerous"
   because they make proofs noncomputational, which is an issue
  for things we want to solve with "compute".
*)
(* Can't use "Hint Resolve" because a bug in "apply proof_irr" matches
   things that are not Props, which leads the Qed to fail (later) *)
Hint Extern 1 (@eq _ _ _) => exact (proof_irr _ _) : extensionality.

(* Can't use "Hint Resolve" because it doesn't seem to do anything... *)
Hint Extern 2 (eq _ _)  => apply exist_ext : extensionality.

(* Can't use "Hint Resolve" because it doesn't seem to do anything... *)
Hint Extern 2 (@eq _ (@existT _ _ _ _) (@existT _ _ _ _))  => apply existT_ext : extensionality.

Tactic Notation "forget" constr(X) "as" ident(y) :=
   set (y:=X) in *; clearbody y.

Ltac proof_irr := match goal with H: ?A, H' : ?A |- _ => generalize (proof_irr H H'); intro; subst H' end.

Ltac inversion2 H1 H2 :=
 rewrite H1 in H2; symmetry in H2; inv H2.

Ltac invT H :=
match type of H  with
  | existT _ ?a ?b = existT _ ?a ?c =>
     generalize (inj_pair2 _ _ a b c H); clear H; intro H; invT H
  | existT _ _ _ = existT _ _ _ =>
       let HH := fresh in (injection H; intros _ HH; invT HH; invT H)
  | _ => inv H
 end.

Ltac invSome :=
 match goal with
 | H: match ?A with Some _ =>  _ | None => None end = Some _ |- _ =>
        let Hx := fresh in
               (revert H; case_eq A; [intros ? H Hx | intros H Hx]; inv Hx)
 | H: match ?A with Some _ => _  | None => False end |- _ =>
             (revert H; case_eq A; [intros ? H ? | intros; contradiction])

 | H: match ?A return _ with Some _ =>  _ | None => _ end eq_refl = Some _ |- _ =>
 let Hx := fresh in
           (revert H; generalize (eq_refl A); pattern A at 1 3; destruct A;
            [ intros Hx H | intros ? H; discriminate H])
 end.

Ltac split3 := split; [|split].

Lemma if_true: forall (A: Prop) (E: {A}+{~A}) (T: Type) (B C: T), A -> (if E then B else C) = B.
Proof.
intros.
destruct E; auto.
contradiction.
Qed.

Lemma if_false: forall (A: Prop) (E: {A}+{~A}) (T: Type) (B C: T), ~A -> (if E then B else C) = C.
Proof.
intros.
destruct E; auto.
contradiction.
Qed.

(* END Tactics copied from ecm/Coqlib2.v *)

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

Ltac simple_if_tac := 
  match goal with |- context [if ?A then _ else _] => 
    lazymatch type of A with
    | bool => destruct A 
    | sumbool _ _ => fail "Use if_tac instead of simple_if_tac, since your expression "A" has type sumbool"
    | ?t => fail "Use simple_if_tac only for bool; your expression"A" has type" t
  end end.

Tactic Notation "if_tac" := 
  match goal with |- context [if ?a then _ else _] =>
    lazymatch type of a with
    | sumbool _ _ =>destruct a as [?H | ?H]
    | bool => fail "Use simple_if_tac instead of if_tac, since your expression"a" has type bool"
    | ?t => fail "Use if_tac only for sumbool; your expression"a" has type" t
   end end.

Tactic Notation "if_tac" simple_intropattern(H)
   := match goal with |- context [if ?a then _ else _] =>
    lazymatch type of a with
    | sumbool _ _ =>destruct a as H
    | bool => fail "Use simple_if_tac instead of if_tac, since your expression"a" has type bool"
    | ?t => fail "Use if_tac only for sumbool; your expression"a" has type" t
   end end.

Tactic Notation "if_tac" "in" hyp(H0)
 := match type of H0 with context [if ?a then _ else _] =>
    lazymatch type of a with
    | sumbool _ _ =>destruct a as [?H | ?H]
    | bool => fail "Use simple_if_tac instead of if_tac, since your expression"a" has type bool"
    | ?t => fail "Use if_tac only for sumbool; your expression"a" has type" t
   end end.

Tactic Notation "if_tac" simple_intropattern(H) "in" hyp(H1)
 := match type of H1 with context [if ?a then _ else _] => 
    lazymatch type of a with
    | sumbool _ _ =>destruct a as H
    | bool => fail "Use simple_if_tac instead of if_tac, since your expression"a" has type bool"
    | ?t => fail "Use if_tac only for sumbool; your expression"a" has type" t
   end end.

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

Lemma sumbool_dec_iff: forall A B, {A} + {~A} -> (A <-> B) -> {B} + {~B}.
Proof.
  intros.
  destruct H.
  + left. tauto.
  + right. tauto.
Qed.

Lemma sumbool_dec_and: forall A B, {A} + {~A} -> {B} + {~B} -> {A /\ B} + {~(A /\ B)}.
Proof.
  intros.
  destruct H, H0.
  + left; tauto.
  + right; tauto.
  + right; tauto.
  + right; tauto.
Qed.

Lemma sumbool_dec_or: forall A B, {A} + {~A} -> {B} + {~B} -> {A \/ B} + {~(A \/ B)}.
Proof.
  intros.
  destruct H, H0.
  + left. tauto.
  + left. tauto.
  + left. tauto.
  + right; tauto.
Qed.

Ltac super_pattern t x :=
  let t0 := fresh "t" in
  set (t0 := t);
  pattern x in t0;
  cbv beta in (type of t0);
  subst t0.

(* change (fun v => ?) into a form of (fun v => ? v x) *)
Ltac super_pattern_in_func t x :=
  let t0 := fresh "t" in
  let a := fresh "a" in
  match type of t with
  | ?type_of_t =>
    evar (t0 : type_of_t)
  end;
  assert (t = t0) as _;
  [
    extensionality a;
    cbv beta;
    match goal with
    | |- ?left = _ =>
      super_pattern left x
    end;
    match goal with
    | |- ?left _ = _ =>
      super_pattern left a
    end;
    match goal with
    | |- ?left _ _ = _ =>
      instantiate (1 := fun a => left a x) in (Value of t0)
    end;
    reflexivity
  |
    change t with t0;
    subst t0
  ].

(* proof goal: ?func arg = expr *)
Ltac build_func_abs_right :=
match goal with
| |- @eq ?typ_expr (_ ?arg) ?expr =>
     match type of arg with
     | ?typ_arg =>
       super_pattern expr arg;
       match goal with
       | |- @eq typ_expr _ (?func arg) =>
            exact (@eq_refl typ_expr
                    ((ltac:(clear arg; intros arg;
                            let res := eval cbv beta in (func arg) in
                            exact res): (typ_arg -> typ_expr))
                     arg)
                  )
(* This complicated line is designed for proper naming for binding variables. *)
       end
     end
end.

