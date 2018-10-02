Require Import Coq.Arith.EqNat.
Require Import Coq.Relations.Relations.
Require Import Coq.Sorting.Permutation.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Integers.

Require Import VST.msl.Coqlib2.
Require Export VST.msl.eq_dec.

Lemma max_two_power_nat: forall n1 n2, Z.max (two_power_nat n1) (two_power_nat n2) = two_power_nat (Nat.max n1 n2).
Proof.
  intros.
  rewrite !two_power_nat_two_p.
  pose proof Zle_0_nat n1; pose proof Zle_0_nat n2.
  rewrite Nat2Z.inj_max.
  forget (Z.of_nat n1) as m1; forget (Z.of_nat n2) as m2.
  destruct (Z_le_dec m1 m2).
  + rewrite (Z.max_r m1 m2) by omega.
    apply Z.max_r.
    apply two_p_monotone; omega.
  + rewrite (Z.max_l m1 m2) by omega.
    apply Z.max_l.
    apply two_p_monotone; omega.
Qed.

Lemma Z_max_two_p: forall m1 m2, (exists n, m1 = two_power_nat n) -> (exists n, m2 = two_power_nat n) -> (exists n, Z.max m1 m2 = two_power_nat n).
Proof.
  intros ? ? [? ?] [? ?].
  subst.
  rewrite max_two_power_nat.
  eexists; reflexivity.
Qed.

Lemma power_nat_divide: forall n m, two_power_nat n <= two_power_nat m -> Z.divide (two_power_nat n) (two_power_nat m).
Proof.
  intros.
  repeat rewrite two_power_nat_two_p in *.
  unfold Z.divide.
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

Lemma power_nat_divide_ge: forall n m: Z,
  (exists N, n = two_power_nat N) ->
  (exists M, m = two_power_nat M) ->
  (n >= m <-> (m | n)).
Proof.
  intros.
  destruct H, H0.
  split; intros.
  + subst.
    apply power_nat_divide.
    omega.
  + destruct H1 as [k ?].
    rewrite H1.
    pose proof two_power_nat_pos x0.
    pose proof two_power_nat_pos x.
    assert (k > 0).
    {
      eapply Zmult_gt_0_reg_l.
      + exact H2.
      + rewrite <- H0, Z.mul_comm; omega.
    } 
    rewrite <- (Z.mul_1_l m) at 2.
    apply Zmult_ge_compat_r; omega.
Qed.

Lemma power_nat_divide_le: forall n m: Z,
  (exists N, n = two_power_nat N) ->
  (exists M, m = two_power_nat M) ->
  (m <= n <-> (m | n)).
Proof.
  intros.
  rewrite <- power_nat_divide_ge; auto.
  omega.
Qed.

Lemma two_p_max_divide: forall m1 m2 m, (exists n, m1 = two_power_nat n) -> (exists n, m2 = two_power_nat n) -> ((Z.max m1 m2 | m) <-> (m1 | m) /\ (m2 | m)).
Proof.
  intros.
  destruct (Z_le_dec m1 m2).
  + rewrite Z.max_r by omega.
    rewrite power_nat_divide_le in l by auto.
    pose proof Zdivides_trans m1 m2 m.
    tauto.
  + rewrite Z.max_l by omega.
    assert (m2 <= m1) by omega.
    rewrite power_nat_divide_le in H1 by auto.
    pose proof Zdivides_trans m2 m1 m.
    tauto.
Qed.

Lemma two_p_max_1: forall m1 m2, (exists n, m1 = two_power_nat n) -> (exists n, m2 = two_power_nat n) -> (Z.max m1 m2 = 1 <-> m1 = 1 /\ m2 = 1).
Proof.
  assert (forall x, (exists n : nat, x = two_power_nat n) -> (x = 1 <-> (x | 1))).
  + intros.
    split; intros.
    - subst.
      exists 1; auto.
    - rewrite <- power_nat_divide_le in H0 by (auto; exists 0%nat; auto).
      destruct H as [n ?]; subst x.
      pose proof two_power_nat_pos n.
      omega.
  + intros m1 m2 Hm1 Hm2.
    pose proof Z_max_two_p _ _ Hm1 Hm2 as Hmax.
    rewrite (H _ Hm1), (H _ Hm2), (H _ Hmax).
    apply two_p_max_divide; auto.
Qed.

Lemma two_power_nat_0: forall x, (exists n, x = two_power_nat n) -> x <> 0.
Proof.
  intros.
  destruct H.
  pose proof two_power_nat_pos x0.
  omega.
Qed.

Hint Rewrite andb_true_iff: align.
Hint Rewrite <- Zle_is_le_bool: align.
Hint Rewrite Z.eqb_eq: align.
Hint Rewrite power_nat_divide_le using (auto with align): align.
Hint Rewrite Z.mod_divide using (apply two_power_nat_0; auto with align): align.
Hint Rewrite two_p_max_divide using (auto with align): align.
Hint Rewrite two_p_max_1 using (auto with align): align.
Hint Resolve Z_max_two_p: align.

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

Tactic Notation "assert_specialize" hyp(H) "by" tactic1(tac) :=
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

Tactic Notation "assert_specialize" hyp(H) "as" simple_intropattern(Hnew) "by" tactic1(tac) :=
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

Lemma range_pred_dec: forall (P: nat -> Prop),
  (forall n, {P n} + {~ P n}) ->
  forall m,
    {forall n, (n < m)%nat -> P n} + {~ forall n, (n < m)%nat -> P n}.
Proof.
  intros.
  induction m.
  + left.
    intros; omega.
  + destruct (H m); [destruct IHm |].
    - left.
      intros.
      destruct (eq_dec n m).
      * subst; auto.
      * apply p0; omega.
    - right.
      intro.
      apply n; clear n.
      intros; apply H0; omega.
    - right.
      intro.
      apply n; clear n.
      apply H0.
      omega.
Qed.

Lemma Z2Nat_neg: forall i, i < 0 -> Z.to_nat i = 0%nat.
Proof.
  intros.
  destruct i; try reflexivity.
  pose proof Zgt_pos_0 p; omega.
Qed.

Lemma Zrange_pred_dec: forall (P: Z -> Prop),
  (forall z, {P z} + {~ P z}) ->
  forall l r,  
    {forall z, l <= z < r -> P z} + {~ forall z, l <= z < r -> P z}.
Proof.
  intros.
  assert ((forall n: nat, (n < Z.to_nat (r - l))%nat -> P (l + Z.of_nat n)) <-> (forall z : Z, l <= z < r -> P z)).
  {
    split; intros.
    + specialize (H0 (Z.to_nat (z - l))).
      rewrite <- Z2Nat.inj_lt in H0 by omega.
      spec H0; [omega |].
      rewrite Z2Nat.id in H0 by omega.
      replace (l + (z - l)) with z in H0 by omega.
      auto.
    + apply H0.
      rewrite Nat2Z.inj_lt in H1.
      destruct (zlt (r - l) 0).
      - rewrite Z2Nat_neg in H1 by omega.
        simpl in H1.
        omega.
      - rewrite Z2Nat.id in H1 by omega.
        omega.
  }
  eapply sumbool_dec_iff; [clear H0 | eassumption].
  apply range_pred_dec.
  intros.
  apply H.
Qed.

Definition eqb_list {A: Type} (eqb_A: A -> A -> bool): list A -> list A -> bool :=
  fix eqb_list (l1 l2: list A): bool :=
    match l1, l2 with
    | nil, nil => true
    | a1 :: l1, a2 :: l2 => eqb_A a1 a2 && eqb_list l1 l2
    | _, _ => false
    end.

Lemma eqb_list_spec: forall {A: Type} (eqb_A: A -> A -> bool),
  (forall a1 a2, eqb_A a1 a2 = true <-> a1 = a2) ->
  (forall l1 l2, eqb_list eqb_A l1 l2 = true <-> l1 = l2).
Proof.
  intros.
  revert l2; induction l1 as [| a1 l1]; intros; destruct l2 as [| a2 l2].
  + simpl.
    tauto.
  + simpl.
    split; intros; congruence.
  + simpl.
    split; intros; congruence.
  + simpl.
    rewrite andb_true_iff.
    rewrite  H.
    rewrite IHl1.
    split; intros.
    - destruct H0; subst; auto.
    - inv H0; auto.
Qed.


Lemma nat_ind2_Type:
forall P : nat -> Type,
((forall n, (forall j:nat, (j<n )%nat -> P j) ->  P n):Type) ->
(forall n, P n).
Proof.
intros.
assert (forall j , (j <= n)%nat -> P j).
induction n.
intros.
replace j with 0%nat ; try omega.
apply X; intros.
elimtype False; omega.
intros.  apply X. intros.
apply IHn.
omega.
apply X0.
omega.
Qed.

Lemma nat_ind2:
forall P : nat -> Prop,
(forall n, (forall j:nat, (j<n )%nat -> P j) ->  P n) ->
(forall n, P n).
Proof.
intros; apply Wf_nat.lt_wf_ind. auto.
Qed.

Lemma equiv_e2 : forall A B: Prop, A=B -> B -> A.
Proof.
intros.
rewrite H; auto.
Qed.
Arguments equiv_e2 [A B] _ _.

Definition opt2list (A: Type) (x: option A) :=
  match x with Some a => a::nil | None => nil end.
Arguments opt2list [A] _.

Definition isSome {A} (o: option A) := match o with Some _ => True | None => False end.

Definition isSome_dec: forall {A} (P: option A), isSome P + ~ isSome P.
Proof.
  intros.
  destruct P; simpl; auto.
Defined.
