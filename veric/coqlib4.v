Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relations.
Require Import Coq.Sorting.Permutation.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

Require Import VST.msl.Coqlib2.
Require Export VST.msl.eq_dec.

Lemma power_nat_divide: forall n m, two_power_nat n <= two_power_nat m -> Z.divide (two_power_nat n) (two_power_nat m).
Proof.
  intros.
  repeat rewrite two_power_nat_two_p in *.
  unfold Zdivide.
  exists (two_p (Z.of_nat m - Z.of_nat n)).
  assert ((Z.of_nat m) = (Z.of_nat m - Z.of_nat n) + Z.of_nat n) by omega.
  rewrite H0 at 1.
  assert (Z.of_nat m >= 0) by omega.
  assert (Z.of_nat n >= 0) by omega.
  assert (Z.of_nat n <= Z.of_nat m).
    destruct (Z_le_gt_dec (Z.of_nat n) (Z.of_nat m)).
    exact l.
    assert (Z.of_nat m < Z.of_nat n) by omega.
    assert (two_p (Z.of_nat m) < two_p (Z.of_nat n)) by (apply two_p_monotone_strict; omega).
    omega.
  apply (two_p_is_exp (Z.of_nat m - Z.of_nat n) (Z.of_nat n)); omega.
Qed.

Lemma power_nat_divide': forall n m: Z,
  (exists N, n = two_power_nat N) ->
  (exists M, m = two_power_nat M) ->
  n >= m ->
  (m | n).
Proof.
  intros.
  destruct H, H0.
  subst.
  apply power_nat_divide.
  omega.
Qed.

Lemma Z_of_nat_ge_O: forall n, Z.of_nat n >= 0.
Proof. intros.
change 0 with (Z.of_nat O).
apply inj_ge. clear; omega.
Qed.

Lemma nth_error_nth:
  forall A (al: list A) (z: A) i, (i < length al)%nat -> nth_error al i = Some (nth i al z).
Proof.
intros. revert al H; induction i; destruct al; simpl; intros; auto; try omega.
apply IHi. omega.
Qed.

Lemma nat_of_Z_eq: forall i, nat_of_Z (Z_of_nat i) = i.
Proof.
intros.
apply inj_eq_rev.
rewrite nat_of_Z_eq; auto.
omega.
Qed.

Lemma nth_error_length:
  forall {A} i (l: list A), nth_error l i = None <-> (i >= length l)%nat.
Proof.
induction i; destruct l; simpl; intuition.
inv H.
inv H.
rewrite IHi in H. omega.
rewrite IHi. omega.
Qed.

Lemma prop_unext: forall P Q: Prop, P=Q -> (P<->Q).
Proof. intros. subst; split; auto. Qed.

Lemma list_norepet_In_In: forall {K X} a x y (l:list (K*X)),
  list_norepet (map (@fst K X) l) -> In (a, x) l -> In (a, y) l -> x = y.
Proof.
  induction l; intros N Ix Iy.
   - inv Ix.
   - simpl in N; inv N.
     destruct Ix.
     + subst.
       simpl in Iy; destruct Iy as [|Iy]; [congruence|].
       exfalso; apply (in_map (@fst K X)) in Iy; tauto.
     + simpl in Iy; destruct Iy as [|Iy].
       subst. exfalso; apply (in_map (@fst K X)) in H; tauto.
       apply IHl; auto.
Qed.

Inductive sublist {A} : list A -> list A -> Prop :=
| sublist_nil : sublist nil nil
| sublist_cons a l1 l2 : sublist l1 l2 -> sublist (a :: l1) (a :: l2)
| sublist_drop a l1 l2 : sublist l1 l2 -> sublist l1 (a :: l2).

Lemma sublist_In {A} (a : A) l1 l2 : sublist l1 l2 -> In a l1 -> In a l2.
Proof.
  intros S; induction S; intros I.
  - inversion I.
  - simpl in I; destruct I.
    subst; left; auto.
    right; auto.
  - right; auto.
Qed.

Lemma sublist_norepet {A} (l1 l2 : list A) : sublist l1 l2 -> list_norepet l2 -> list_norepet l1.
Proof.
  intros S; induction S; intros N; auto.
  - inversion N; subst; constructor; auto.
    pose proof sublist_In a l1 l2; auto.
  - inversion N; auto.
Qed.

Require Import Coq.Sets.Ensembles.

Definition Ensemble_join {A} (X Y Z: Ensemble A): Prop :=
  (forall a, Z a <-> X a \/ Y a) /\ (forall a, X a -> Y a -> False).

Require Coq.Logic.ConstructiveEpsilon.

Lemma decidable_countable_ex_sig {A} (f : nat -> A)
      (Hf : forall a, exists n, a = f n)
      (P : A -> Prop)
      (Pdec : forall x, {P x} + {~ P x}) :
  (exists x : A, P x) -> {x : A | P x}.
Proof.
  intros E.
  cut ({n | P (f n)}). intros [n Hn]; eauto.
  apply ConstructiveEpsilon.constructive_indefinite_ground_description_nat.
  intro; apply Pdec.
  destruct E as [x Hx].
  destruct (Hf x) as [n ->].
  eauto.
Qed.

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

Lemma perm_search:
  forall {A} (a b: A) r s t,
     Permutation (a::t) s ->
     Permutation (b::t) r ->
     Permutation (a::r) (b::s).
Proof.
intros.
eapply perm_trans.
apply perm_skip.
apply Permutation_sym.
apply H0.
eapply perm_trans.
apply perm_swap.
apply perm_skip.
apply H.
Qed.

Lemma Permutation_concat: forall {A} (P Q: list (list A)),
  Permutation P Q ->
  Permutation (concat P) (concat Q).
Proof.
  intros.
  induction H.
  + apply Permutation_refl.
  + simpl.
    apply Permutation_app_head; auto.
  + simpl.
    rewrite !app_assoc.
    apply Permutation_app_tail.
    apply Permutation_app_comm.
  + eapply Permutation_trans; eauto.
Qed.    

Lemma Permutation_app_comm_trans:
 forall (A: Type) (a b c : list A),
   Permutation (b++a) c ->
   Permutation (a++b) c.
Proof.
intros.
eapply Permutation_trans.
apply Permutation_app_comm.
auto.
Qed.

Ltac solve_perm :=
    (* solves goals of the form (R ++ ?i = S)
          where R and S are lists, and ?i is a unification variable *)
  try match goal with
       | |-  Permutation (?A ++ ?B) _ =>
            is_evar A; first [is_evar B; fail 1| idtac];
            apply Permutation_app_comm_trans
       end;
  repeat first [ apply Permutation_refl
       | apply perm_skip
       | eapply perm_search
       ].

Goal exists e, Permutation ((1::2::nil)++e) (3::2::1::5::nil).
eexists.
solve_perm.
Qed.
