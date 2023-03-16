(* modified from iris.algebra.view *)

From iris.algebra Require Export updates local_updates agree.
From iris.algebra Require Import proofmode_classes big_op.
From iris_ora.algebra Require Export ora agree.
From VST.veric Require Import dfrac.
From iris.prelude Require Import options.

(** The view camera with fractional authoritative elements *)
(** The view camera, which is reminiscent of the views framework, is used to
  provide a logical/"small-footprint" "view" of some "large-footprint" piece of
  data, which can be shared in the separation logic sense, i.e., different parts
  of the data can be separately owned by different functions or threads. This is
  achieved using the two elements of the view camera:

- The authoritative element [●V a], which describes the data under consideration.
- The fragment [◯V b], which provides a logical view of the data [a].

To enable sharing of the fragments, the type of fragments is equipped with a
camera structure so ownership of fragments can be split. Concretely, fragments
enjoy the rule [◯V (b1 ⋅ b2) = ◯V b1 ⋅ ◯V b2].

To enable sharing of the authoritative element [●V{dq} a], it is equipped with a
discardable fraction [dq]. Updates are only possible with the full authoritative
element [●V a] (syntax for [●V{#1} a]]), while fractional authoritative elements
have agreement, i.e., [✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) → a1 ≡ a2]. *)

(** * The view relation *)
(** To relate the authoritative element [a] to its possible fragments [b], the
view camera is parametrized by a (step-indexed) relation [view_rel n a b]. This
relation should be a.) closed under smaller step-indexes [n], b.) non-expansive
w.r.t. the argument [a], c.) closed under smaller [b] (which implies
non-expansiveness w.r.t. [b]), and d.) ensure validity of the argument [b].

Note 1: Instead of requiring both a step-indexed and a non-step-indexed version
of the relation (like cameras do for validity), we use [∀ n, view_rel n] as the
non-step-indexed version. This is anyway necessary when using [≼{n}] as the
relation (like the authoritative camera does) as its non-step-indexed version
is not equivalent to [∀ n, x ≼{n} y].

Note 2: The view relation is defined as a canonical structure so that given a
relation [nat → A → B → Prop], the instance with the laws can be inferred. We do
not use type classes for this purpose because cameras themselves are represented
using canonical structures. It has proven fragile for a canonical structure
instance to take a type class as a parameter (in this case, [viewR] would need
to take a class with the view relation laws). *)
Structure view_rel (A : ofe) (B : ucmra) := ViewRel {
  view_rel_holds :> nat → A → B → Prop;
  view_rel_mono n1 n2 a1 a2 b1 b2 :
    view_rel_holds n1 a1 b1 →
    a1 ≡{n2}≡ a2 →
    b2 ≼{n2} b1 →
    n2 ≤ n1 →
    view_rel_holds n2 a2 b2;
  view_rel_validN n a b :
    view_rel_holds n a b → ✓{n} b;
  view_rel_unit n :
    ∃ a, view_rel_holds n a ε
}.
Global Arguments ViewRel {_ _} _ _.
Global Arguments view_rel_holds {_ _} _ _ _ _.
Global Instance: Params (@view_rel_holds) 4 := {}.

Global Instance view_rel_ne {A B} (rel : view_rel A B) n :
  Proper (dist n ==> dist n ==> iff) (rel n).
Proof.
  intros a1 a2 Ha b1 b2 Hb.
  split=> ?; (eapply view_rel_mono; [done|done|by rewrite Hb|done]).
Qed.
Global Instance view_rel_proper {A B} (rel : view_rel A B) n :
  Proper ((≡) ==> (≡) ==> iff) (rel n).
Proof. intros a1 a2 Ha b1 b2 Hb. apply view_rel_ne; by apply equiv_dist. Qed.

Class ViewRelDiscrete {A B} (rel : view_rel A B) :=
  view_rel_discrete n a b : rel 0 a b → rel n a b.

(** * Definition of the view camera *)
(** To make use of the lemmas provided in this file, elements of [view] should
always be constructed using [●V] and [◯V], and never using the constructor
[View]. *)
Record view {A B} (rel : nat → A → B → Prop) :=
  View { view_auth_proj : option (dfrac * agree A) ; view_frag_proj : B }.
Add Printing Constructor view.
Global Arguments View {_ _ _} _ _.
Global Arguments view_auth_proj {_ _ _} _.
Global Arguments view_frag_proj {_ _ _} _.
Global Instance: Params (@View) 3 := {}.
Global Instance: Params (@view_auth_proj) 3 := {}.
Global Instance: Params (@view_frag_proj) 3 := {}.

Definition view_auth {A B} {rel : view_rel A B} (dq : dfrac) (a : A) : view rel :=
  View (Some (dq, to_agree a)) ε.
Definition view_frag {A B} {rel : view_rel A B} (b : B) : view rel := View None b.
Typeclasses Opaque view_auth view_frag.

Global Instance: Params (@view_auth) 3 := {}.
Global Instance: Params (@view_frag) 3 := {}.

Notation "●V dq a" := (view_auth dq a)
  (at level 20, dq custom dfrac at level 1, format "●V dq  a").
Notation "◯V a" := (view_frag a) (at level 20).

(** * The OFE structure *)
(** We omit the usual [equivI] lemma because it is hard to state a suitably
general version in terms of [●V] and [◯V], and because such a lemma has never
been needed in practice. *)
Section ofe.
  Context {A B : ofe} (rel : nat → A → B → Prop).
  Implicit Types a : A.
  Implicit Types ag : option (dfrac * agree A).
  Implicit Types b : B.
  Implicit Types x y : view rel.

  Local Instance view_equiv : Equiv (view rel) := λ x y,
    view_auth_proj x ≡ view_auth_proj y ∧ view_frag_proj x ≡ view_frag_proj y.
  Local Instance view_dist : Dist (view rel) := λ n x y,
    view_auth_proj x ≡{n}≡ view_auth_proj y ∧
    view_frag_proj x ≡{n}≡ view_frag_proj y.

  Global Instance View_ne : NonExpansive2 (@View A B rel).
  Proof. by split. Qed.
  Global Instance View_proper : Proper ((≡) ==> (≡) ==> (≡)) (@View A B rel).
  Proof. by split. Qed.
  Global Instance view_auth_proj_ne: NonExpansive (@view_auth_proj A B rel).
  Proof. by destruct 1. Qed.
  Global Instance view_auth_proj_proper :
    Proper ((≡) ==> (≡)) (@view_auth_proj A B rel).
  Proof. by destruct 1. Qed.
  Global Instance view_frag_proj_ne : NonExpansive (@view_frag_proj A B rel).
  Proof. by destruct 1. Qed.
  Global Instance view_frag_proj_proper :
    Proper ((≡) ==> (≡)) (@view_frag_proj A B rel).
  Proof. by destruct 1. Qed.

  Definition view_ofe_mixin : OfeMixin (view rel).
  Proof. by apply (iso_ofe_mixin (λ x, (view_auth_proj x, view_frag_proj x))). Qed.
  Canonical Structure viewO := Ofe (view rel) view_ofe_mixin.

  Global Instance View_discrete ag b :
    Discrete ag → Discrete b → Discrete (View ag b).
  Proof. by intros ?? [??] [??]; split; apply: discrete. Qed.
  Global Instance view_ofe_discrete :
    OfeDiscrete A → OfeDiscrete B → OfeDiscrete viewO.
  Proof. intros ?? [??]; apply _. Qed.
End ofe.

(** * The camera structure *)
Section cmra.
  Context {A B} (rel : view_rel A B).
  Implicit Types a : A.
  Implicit Types ag : option (dfrac * agree A).
  Implicit Types b : B.
  Implicit Types x y : view rel.
  Implicit Types q : share.
  Implicit Types dq : dfrac.

  Global Instance view_auth_ne dq : NonExpansive (@view_auth A B rel dq).
  Proof. solve_proper. Qed.
  Global Instance view_auth_proper dq : Proper ((≡) ==> (≡)) (@view_auth A B rel dq).
  Proof. solve_proper. Qed.
  Global Instance view_frag_ne : NonExpansive (@view_frag A B rel).
  Proof. done. Qed.
  Global Instance view_frag_proper : Proper ((≡) ==> (≡)) (@view_frag A B rel).
  Proof. done. Qed.

  Global Instance view_auth_dist_inj n :
    Inj2 (=) (dist n) (dist n) (@view_auth A B rel).
  Proof.
    intros dq1 a1 dq2 a2 [Hag ?]; inversion Hag as [?? [??]|]; simplify_eq/=.
    split; [done|]. by apply (inj to_agree).
  Qed.
  Global Instance view_auth_inj : Inj2 (=) (≡) (≡) (@view_auth A B rel).
  Proof.
    intros dq1 a1 dq2 a2 [Hag ?]; inversion Hag as [?? [??]|]; simplify_eq/=.
    split; [done|]. by apply (inj to_agree).
  Qed.
  Global Instance view_frag_dist_inj n : Inj (dist n) (dist n) (@view_frag A B rel).
  Proof. by intros ?? [??]. Qed.
  Global Instance view_frag_inj : Inj (≡) (≡) (@view_frag A B rel).
  Proof. by intros ?? [??]. Qed.

  Local Instance view_valid_instance : Valid (view rel) := λ x,
    match view_auth_proj x with
    | Some (dq, ag) =>
       ✓ dq ∧ (∀ n, ∃ a, ag ≡{n}≡ to_agree a ∧ rel n a (view_frag_proj x))
    | None => ∀ n, ∃ a, rel n a (view_frag_proj x)
    end.
  Local Instance view_validN_instance : ValidN (view rel) := λ n x,
    match view_auth_proj x with
    | Some (dq, ag) =>
       ✓{n} dq ∧ ∃ a, ag ≡{n}≡ to_agree a ∧ rel n a (view_frag_proj x)
    | None => ∃ a, rel n a (view_frag_proj x)
    end.
  Local Instance view_pcore_instance : PCore (view rel) := λ x,
    Some (View (core (view_auth_proj x)) (core (view_frag_proj x))).
  Local Instance view_op_instance : Op (view rel) := λ x y,
    View (view_auth_proj x ⋅ view_auth_proj y) (view_frag_proj x ⋅ view_frag_proj y).

  Local Definition view_valid_eq :
    valid = λ x,
      match view_auth_proj x with
      | Some (dq, ag) =>
         ✓ dq ∧ (∀ n, ∃ a, ag ≡{n}≡ to_agree a ∧ rel n a (view_frag_proj x))
      | None => ∀ n, ∃ a, rel n a (view_frag_proj x)
      end := eq_refl _.
  Local Definition view_validN_eq :
    validN = λ n x,
      match view_auth_proj x with
      | Some (dq, ag) => ✓{n} dq ∧ ∃ a, ag ≡{n}≡ to_agree a ∧ rel n a (view_frag_proj x)
      | None => ∃ a, rel n a (view_frag_proj x)
      end := eq_refl _.
  Local Definition view_pcore_eq :
      pcore = λ x, Some (View (core (view_auth_proj x)) (core (view_frag_proj x))) :=
    eq_refl _.
  Local Definition view_core_eq :
      core = λ x, View (core (view_auth_proj x)) (core (view_frag_proj x)) :=
    eq_refl _.
  Local Definition view_op_eq :
      op = λ x y, View (view_auth_proj x ⋅ view_auth_proj y)
                       (view_frag_proj x ⋅ view_frag_proj y) :=
    eq_refl _.

  Lemma view_cmra_mixin : CmraMixin (view rel).
  Proof.
    apply (iso_cmra_mixin_restrict
      (λ x : option (dfrac * agree A) * B, View x.1 x.2)
      (λ x, (view_auth_proj x, view_frag_proj x))); try done.
    - intros [x b]. by rewrite /= pair_pcore !cmra_pcore_core.
    - intros n [[[dq ag]|] b]; rewrite /= view_validN_eq /=.
      + intros (?&a&->&?). repeat split; simpl; [done|]. by eapply view_rel_validN.
      + intros [a ?]. repeat split; simpl. by eapply view_rel_validN.
    - rewrite view_validN_eq.
      intros n [x1 b1] [x2 b2] [Hx ?]; simpl in *;
        destruct Hx as [[q1 ag1] [q2 ag2] [??]|]; intros ?; by ofe_subst.
    - rewrite view_valid_eq view_validN_eq.
      intros [[[dq aa]|] b]; rewrite /= ?cmra_valid_validN; naive_solver.
    - rewrite view_validN_eq=> n [[[dq ag]|] b] /=.
      + intros [? (a&?&?)]; split; [done|].
        exists a; split; [by eauto using dist_le|].
        apply view_rel_mono with (S n) a b; auto with lia.
      + intros [a ?]. exists a. apply view_rel_mono with (S n) a b; auto with lia.
    - rewrite view_validN_eq=> n [[[q1 ag1]|] b1] [[[q2 ag2]|] b2] /=.
      + intros [?%cmra_validN_op_l (a & Haga & ?)]. split; [done|].
        assert (ag1 ≡{n}≡ ag2) as Ha12 by (apply agree_op_invN; by rewrite Haga).
        exists a. split; [by rewrite -Haga -Ha12 agree_idemp|].
        apply view_rel_mono with n a (b1 ⋅ b2); eauto using cmra_includedN_l.
      + intros [? (a & Haga & ?)]. split; [done|]. exists a; split; [done|].
        apply view_rel_mono with n a (b1 ⋅ b2); eauto using cmra_includedN_l.
      + intros [? (a & Haga & ?)]. exists a.
        apply view_rel_mono with n a (b1 ⋅ b2); eauto using cmra_includedN_l.
      + intros [a ?]. exists a.
        apply view_rel_mono with n a (b1 ⋅ b2); eauto using cmra_includedN_l.
  Qed.
  Canonical Structure viewC := Cmra (view rel) view_cmra_mixin.

  Global Instance view_auth_discrete dq a :
    Discrete a → Discrete (ε : B) → Discrete (●V{dq} a : view rel).
  Proof. intros. apply View_discrete; apply _. Qed.
  Global Instance view_frag_discrete b :
    Discrete b → Discrete (◯V b : view rel).
  Proof. intros. apply View_discrete; apply _. Qed.
  Global Instance view_cmra_discrete :
    OfeDiscrete A → CmraDiscrete B → ViewRelDiscrete rel →
    CmraDiscrete viewC.
  Proof.
    split; [apply _|]=> -[[[dq ag]|] b]; rewrite view_valid_eq view_validN_eq /=.
    - rewrite -cmra_discrete_valid_iff.
      setoid_rewrite <-(discrete_iff _ ag). naive_solver.
    - naive_solver.
  Qed.

  Local Instance view_empty_instance : Unit (view rel) := View ε ε.
  Lemma view_ucmra_mixin : UcmraMixin (view rel).
  Proof.
    split; simpl.
    - rewrite view_valid_eq /=. apply view_rel_unit.
    - by intros x; constructor; rewrite /= left_id.
    - do 2 constructor; [done| apply (core_id_core _)].
  Qed.
  Canonical Structure viewUC := Ucmra (view rel) view_ucmra_mixin.

  (** Operation *)
  Lemma view_auth_dfrac_op dq1 dq2 a : ●V{dq1 ⋅ dq2} a ≡ ●V{dq1} a ⋅ ●V{dq2} a.
  Proof.
    intros; split; simpl; last by rewrite left_id.
    by rewrite -Some_op -pair_op agree_idemp.
  Qed.
  Global Instance view_auth_dfrac_is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 → IsOp' (●V{dq} a) (●V{dq1} a) (●V{dq2} a).
  Proof. rewrite /IsOp' /IsOp => ->. by rewrite -view_auth_dfrac_op. Qed.

  Lemma view_frag_op b1 b2 : ◯V (b1 ⋅ b2) = ◯V b1 ⋅ ◯V b2.
  Proof. done. Qed.
  Lemma view_frag_mono b1 b2 : b1 ≼ b2 → ◯V b1 ≼ ◯V b2.
  Proof. intros [c ->]. rewrite view_frag_op. apply cmra_included_l. Qed.
  Lemma view_frag_core b : core (◯V b) = ◯V (core b).
  Proof. done. Qed.
  Lemma view_both_core_discarded a b :
    core (●V□ a ⋅ ◯V b) ≡ ●V□ a ⋅ ◯V (core b).
  Proof. rewrite view_core_eq view_op_eq /= !left_id //. Qed.
  Lemma view_both_core_frac q a b :
    core (●V{#q} a ⋅ ◯V b) ≡ ◯V (core b).
  Proof. rewrite view_core_eq view_op_eq /= !left_id //. Qed.

  Global Instance view_auth_core_id a : CoreId (●V□ a).
  Proof. do 2 constructor; simpl; auto. apply: core_id_core. Qed.
  Global Instance view_frag_core_id b : CoreId b → CoreId (◯V b).
  Proof. do 2 constructor; simpl; auto. apply: core_id_core. Qed.
  Global Instance view_both_core_id a b : CoreId b → CoreId (●V□ a ⋅ ◯V b).
  Proof. do 2 constructor; simpl; auto. rewrite !left_id. apply: core_id_core. Qed.
  Global Instance view_frag_is_op b b1 b2 :
    IsOp b b1 b2 → IsOp' (◯V b) (◯V b1) (◯V b2).
  Proof. done. Qed.
  Global Instance view_frag_sep_homomorphism :
    MonoidHomomorphism op op (≡) (@view_frag A B rel).
  Proof. by split; [split; try apply _|]. Qed.

  Lemma big_opL_view_frag {C} (g : nat → C → B) (l : list C) :
    (◯V [^op list] k↦x ∈ l, g k x) ≡ [^op list] k↦x ∈ l, ◯V (g k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_view_frag `{Countable K} {C} (g : K → C → B) (m : gmap K C) :
    (◯V [^op map] k↦x ∈ m, g k x) ≡ [^op map] k↦x ∈ m, ◯V (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_view_frag `{Countable C} (g : C → B) (X : gset C) :
    (◯V [^op set] x ∈ X, g x) ≡ [^op set] x ∈ X, ◯V (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_view_frag `{Countable C} (g : C → B) (X : gmultiset C) :
    (◯V [^op mset] x ∈ X, g x) ≡ [^op mset] x ∈ X, ◯V (g x).
  Proof. apply (big_opMS_commute _). Qed.

  (** Validity *)
  Lemma view_auth_dfrac_op_invN n dq1 a1 dq2 a2 :
    ✓{n} (●V{dq1} a1 ⋅ ●V{dq2} a2) → a1 ≡{n}≡ a2.
  Proof.
    rewrite /op /view_op_instance /= left_id -Some_op -pair_op view_validN_eq /=.
    intros (?&?& Eq &?). apply (inj to_agree), agree_op_invN. by rewrite Eq.
  Qed.
  Lemma view_auth_dfrac_op_inv dq1 a1 dq2 a2 : ✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) → a1 ≡ a2.
  Proof.
    intros ?. apply equiv_dist. intros n.
    by eapply view_auth_dfrac_op_invN, cmra_valid_validN.
  Qed.
  Lemma view_auth_dfrac_op_inv_L `{!LeibnizEquiv A} dq1 a1 dq2 a2 :
    ✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) → a1 = a2.
  Proof. by intros ?%view_auth_dfrac_op_inv%leibniz_equiv. Qed.

  Lemma view_auth_dfrac_validN n dq a : ✓{n} (●V{dq} a) ↔ ✓{n}dq ∧ rel n a ε.
  Proof.
    rewrite view_validN_eq /=. apply and_iff_compat_l. split; [|by eauto].
    by intros [? [->%(inj to_agree) ?]].
  Qed.
  Lemma view_auth_validN n a : ✓{n} (●V a) ↔ rel n a ε.
  Proof. rewrite view_auth_dfrac_validN. split; [naive_solver|done]. Qed.

  Lemma view_auth_dfrac_op_validN n dq1 dq2 a1 a2 :
    ✓{n} (●V{dq1} a1 ⋅ ●V{dq2} a2) ↔ ✓(dq1 ⋅ dq2) ∧ a1 ≡{n}≡ a2 ∧ rel n a1 ε.
  Proof.
    split.
    - intros Hval. assert (a1 ≡{n}≡ a2) as Ha by eauto using view_auth_dfrac_op_invN.
      revert Hval. rewrite Ha -view_auth_dfrac_op view_auth_dfrac_validN. naive_solver.
    - intros (?&->&?). by rewrite -view_auth_dfrac_op view_auth_dfrac_validN.
  Qed.
  Lemma view_auth_op_validN n a1 a2 : ✓{n} (●V a1 ⋅ ●V a2) ↔ False.
  Proof. rewrite view_auth_dfrac_op_validN.
    split; try done. intros ((? & ? & ? & [??]%join_Tsh)%share_valid2_joins & _); done.
  Qed.

  Lemma view_frag_validN n b : ✓{n} (◯V b) ↔ ∃ a, rel n a b.
  Proof. done. Qed.

  Lemma view_both_dfrac_validN n dq a b :
    ✓{n} (●V{dq} a ⋅ ◯V b) ↔ ✓dq ∧ rel n a b.
  Proof.
    rewrite view_validN_eq /=. apply and_iff_compat_l.
    setoid_rewrite (left_id _ _ b). split; [|by eauto].
    by intros [?[->%(inj to_agree)]].
  Qed.
  Lemma view_both_validN n a b : ✓{n} (●V a ⋅ ◯V b) ↔ rel n a b.
  Proof. rewrite view_both_dfrac_validN. split; [naive_solver|done]. Qed.

  Lemma view_auth_dfrac_valid dq a : ✓ (●V{dq} a) ↔ ✓dq ∧ ∀ n, rel n a ε.
  Proof.
    rewrite view_valid_eq /=. apply and_iff_compat_l. split; [|by eauto].
    intros H n. by destruct (H n) as [? [->%(inj to_agree) ?]].
  Qed.
  Lemma view_auth_valid a : ✓ (●V a) ↔ ∀ n, rel n a ε.
  Proof. rewrite view_auth_dfrac_valid. split; [naive_solver|done]. Qed.

  Lemma view_auth_dfrac_op_valid dq1 dq2 a1 a2 :
    ✓ (●V{dq1} a1 ⋅ ●V{dq2} a2) ↔ ✓(dq1 ⋅ dq2) ∧ a1 ≡ a2 ∧ ∀ n, rel n a1 ε.
  Proof.
    rewrite 1!cmra_valid_validN equiv_dist. setoid_rewrite view_auth_dfrac_op_validN.
    split; last naive_solver. intros Hv.
    split; last naive_solver. apply (Hv 0).
  Qed.
  Lemma view_auth_op_valid a1 a2 : ✓ (●V a1 ⋅ ●V a2) ↔ False.
  Proof. rewrite view_auth_dfrac_op_valid. split; try done.
    intros ((? & ? & ? & [??]%join_Tsh)%share_valid2_joins & _); done.
  Qed.

  Lemma view_frag_valid b : ✓ (◯V b) ↔ ∀ n, ∃ a, rel n a b.
  Proof. done. Qed.

  Lemma view_both_dfrac_valid dq a b : ✓ (●V{dq} a ⋅ ◯V b) ↔ ✓dq ∧ ∀ n, rel n a b.
  Proof.
    rewrite view_valid_eq /=. apply and_iff_compat_l.
    setoid_rewrite (left_id _ _ b). split; [|by eauto].
    intros H n. by destruct (H n) as [?[->%(inj to_agree)]].
  Qed.
  Lemma view_both_valid a b : ✓ (●V a ⋅ ◯V b) ↔ ∀ n, rel n a b.
  Proof. rewrite view_both_dfrac_valid. split; [naive_solver|done]. Qed.

  (** Inclusion *)
  Lemma view_auth_dfrac_includedN n dq1 dq2 a1 a2 b :
    ●V{dq1} a1 ≼{n} ●V{dq2} a2 ⋅ ◯V b ↔ (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2.
  Proof.
    split.
    - intros [[[[dqf agf]|] bf]
        [[?%(discrete_iff _ _) ?]%(inj Some) _]]; simplify_eq/=.
      + split; [left; apply: cmra_included_l|]. apply to_agree_includedN. by exists agf.
      + split; [right; done|]. by apply (inj to_agree).
    - intros [[[? ->]| ->] ->].
      + rewrite view_auth_dfrac_op -assoc. apply cmra_includedN_l.
      + apply cmra_includedN_l.
  Qed.
  Lemma view_auth_dfrac_included dq1 dq2 a1 a2 b :
    ●V{dq1} a1 ≼ ●V{dq2} a2 ⋅ ◯V b ↔ (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2.
  Proof.
    intros. split.
    - split.
      + by eapply (view_auth_dfrac_includedN 0), cmra_included_includedN.
      + apply equiv_dist=> n.
        by eapply view_auth_dfrac_includedN, cmra_included_includedN.
    - intros [[[dq ->]| ->] ->].
      + rewrite view_auth_dfrac_op -assoc. apply cmra_included_l.
      + apply cmra_included_l.
  Qed.
  Lemma view_auth_includedN n a1 a2 b :
    ●V a1 ≼{n} ●V a2 ⋅ ◯V b ↔ a1 ≡{n}≡ a2.
  Proof. rewrite view_auth_dfrac_includedN. naive_solver. Qed.
  Lemma view_auth_included a1 a2 b :
    ●V a1 ≼ ●V a2 ⋅ ◯V b ↔ a1 ≡ a2.
  Proof. rewrite view_auth_dfrac_included. naive_solver. Qed.

  Lemma view_frag_includedN n p a b1 b2 :
    ◯V b1 ≼{n} ●V{p} a ⋅ ◯V b2 ↔ b1 ≼{n} b2.
  Proof.
    split.
    - intros [xf [_ Hb]]; simpl in *.
      revert Hb; rewrite left_id. by exists (view_frag_proj xf).
    - intros [bf ->]. rewrite comm view_frag_op -assoc. apply cmra_includedN_l.
  Qed.
  Lemma view_frag_included p a b1 b2 :
    ◯V b1 ≼ ●V{p} a ⋅ ◯V b2 ↔ b1 ≼ b2.
  Proof.
    split.
    - intros [xf [_ Hb]]; simpl in *.
      revert Hb; rewrite left_id. by exists (view_frag_proj xf).
    - intros [bf ->]. rewrite comm view_frag_op -assoc. apply cmra_included_l.
  Qed.

  (** The weaker [view_both_included] lemmas below are a consequence of the
  [view_auth_included] and [view_frag_included] lemmas above. *)
  Lemma view_both_dfrac_includedN n dq1 dq2 a1 a2 b1 b2 :
    ●V{dq1} a1 ⋅ ◯V b1 ≼{n} ●V{dq2} a2 ⋅ ◯V b2 ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2.
  Proof.
    split.
    - intros. rewrite assoc. split.
      + rewrite -view_auth_dfrac_includedN. by etrans; [apply cmra_includedN_l|].
      + rewrite -view_frag_includedN. by etrans; [apply cmra_includedN_r|].
    - intros (?&->&?bf&->). rewrite (comm _ b1) view_frag_op assoc.
      by apply cmra_monoN_r, view_auth_dfrac_includedN.
  Qed.
  Lemma view_both_dfrac_included dq1 dq2 a1 a2 b1 b2 :
    ●V{dq1} a1 ⋅ ◯V b1 ≼ ●V{dq2} a2 ⋅ ◯V b2 ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2 ∧ b1 ≼ b2.
  Proof.
    split.
    - intros. rewrite assoc. split.
      + rewrite -view_auth_dfrac_included. by etrans; [apply cmra_included_l|].
      + rewrite -view_frag_included. by etrans; [apply cmra_included_r|].
    - intros (?&->&?bf&->). rewrite (comm _ b1) view_frag_op assoc.
      by apply cmra_mono_r, view_auth_dfrac_included.
  Qed.
  Lemma view_both_includedN n a1 a2 b1 b2 :
    ●V a1 ⋅ ◯V b1 ≼{n} ●V a2 ⋅ ◯V b2 ↔ a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2.
  Proof. rewrite view_both_dfrac_includedN. naive_solver. Qed.
  Lemma view_both_included a1 a2 b1 b2 :
    ●V a1 ⋅ ◯V b1 ≼ ●V a2 ⋅ ◯V b2 ↔ a1 ≡ a2 ∧ b1 ≼ b2.
  Proof. rewrite view_both_dfrac_included. naive_solver. Qed.

  (** Updates *)
  Lemma view_update a b a' b' :
    (∀ n bf, rel n a (b ⋅ bf) → rel n a' (b' ⋅ bf)) →
    ●V a ⋅ ◯V b ~~> ●V a' ⋅ ◯V b'.
  Proof.
    intros Hup; apply cmra_total_update=> n [[[dq ag]|] bf] [/=].
    { by intros []%(exclusiveN_l _ _). }
    intros _ (a0 & <-%(inj to_agree) & Hrel). split; simpl; [done|].
    exists a'; split; [done|]. revert Hrel. rewrite !left_id. apply Hup.
  Qed.

  Lemma view_update_alloc a a' b' :
    (∀ n bf, rel n a bf → rel n a' (b' ⋅ bf)) →
    ●V a ~~> ●V a' ⋅ ◯V b'.
  Proof.
    intros Hup. rewrite -(right_id _ _ (●V a)).
    apply view_update=> n bf. rewrite left_id. apply Hup.
  Qed.
  Lemma view_update_dealloc a b a' :
    (∀ n bf, rel n a (b ⋅ bf) → rel n a' bf) →
    ●V a ⋅ ◯V b ~~> ●V a'.
  Proof.
    intros Hup. rewrite -(right_id _ _ (●V a')).
    apply view_update=> n bf. rewrite left_id. apply Hup.
  Qed.

  Lemma view_update_auth a a' b' :
    (∀ n bf, rel n a bf → rel n a' bf) →
    ●V a ~~> ●V a'.
  Proof.
    intros Hup. rewrite -(right_id _ _ (●V a)) -(right_id _ _ (●V a')).
    apply view_update=> n bf. rewrite !left_id. apply Hup.
  Qed.
  Lemma view_update_auth_persist dq a : ●V{dq} a ~~> ●V□ a.
  Proof.
    apply cmra_total_update.
    move=> n [[[dq' ag]|] bf] [Hv ?]; last done. split; last done.
    by apply (dfrac_discard_update dq _ (Some dq')).
  Qed.

  Lemma view_update_frag b b' :
    (∀ a n bf, rel n a (b ⋅ bf) → rel n a (b' ⋅ bf)) →
    ◯V b ~~> ◯V b'.
  Proof.
    rewrite !cmra_total_update view_validN_eq=> ? n [[[dq ag]|] bf]; naive_solver.
  Qed.

  Lemma view_update_dfrac_alloc dq a b :
    (∀ n bf, rel n a bf → rel n a (b ⋅ bf)) →
    ●V{dq} a ~~> ●V{dq} a ⋅ ◯V b.
  Proof.
    intros Hup. apply cmra_total_update=> n [[[p ag]|] bf] [/=].
    - intros ? (a0 & Hag & Hrel). split; simpl; [done|].
      exists a0; split; [done|]. revert Hrel.
      assert (to_agree a ≼{n} to_agree a0) as <-%to_agree_includedN.
      { by exists ag. }
      rewrite !left_id. apply Hup.
    - intros ? (a0 & <-%(inj to_agree) & Hrel). split; simpl; [done|].
      exists a; split; [done|]. revert Hrel. rewrite !left_id. apply Hup.
  Qed.

  Lemma view_local_update a b0 b1 a' b0' b1' :
    (b0, b1) ~l~> (b0', b1') →
    (∀ n, view_rel_holds rel n a b0 → view_rel_holds rel n a' b0') →
    (●V a ⋅ ◯V b0, ●V a ⋅ ◯V b1) ~l~> (●V a' ⋅ ◯V b0', ●V a' ⋅ ◯V b1').
  Proof.
    rewrite !local_update_unital.
    move=> Hup Hrel n [[[qd ag]|] bf] /view_both_validN Hrel' [/=].
    - rewrite right_id -Some_op -pair_op => /Some_dist_inj [/= H1q _].
      by destruct (id_free_r (DfracOwn Tsh) qd).
    - rewrite !left_id=> _ Hb0.
      destruct (Hup n bf) as [? Hb0']; [by eauto using view_rel_validN..|].
      split; [apply view_both_validN; by auto|]. by rewrite -assoc Hb0'.
  Qed.

  Lemma view_validN_both : forall n (a : view rel), ✓{n} a -> ✓{n} view_auth_proj a /\ ✓{n} view_frag_proj a.
  Proof.
    rewrite view_validN_eq; intros.
    destruct (view_auth_proj a) as [(?, ?)|].
    - destruct H as (? & ? & -> & ?%view_rel_validN); done.
    - destruct H as (? & ?%view_rel_validN); done.
  Qed.

End cmra.

Section ora.

  Context {A} {B : uora} (rel : view_rel A B).

  Instance view_order : OraOrder (view rel) := λ x y, view_auth_proj x ≼ₒ view_auth_proj y ∧ view_frag_proj x ≼ₒ view_frag_proj y.
  Instance view_orderN : OraOrderN (view rel) := λ n x y, view_auth_proj x ≼ₒ{n} view_auth_proj y ∧ view_frag_proj x ≼ₒ{n} view_frag_proj y.

  (* having trouble phrasing an order that guarantees this, so adding it as a proof obligation instead *)
  Context (view_rel_order : ∀n a x y, x ≼ₒ{n} y → rel n a y → rel n a x).

  Lemma view_increasing : forall (a : view rel), Increasing a <-> Increasing (view_auth_proj a) /\ Increasing (view_frag_proj a).
  Proof.
    split.
    - split; intros y.
      + specialize (H (View y ε)); apply H.
      + specialize (H (View ε y)); apply H.
    - intros [Ha Hf] ?; split; [apply Ha | apply Hf].
  Qed.

  Definition view_ora_mixin : OraMixin (view rel).
  Proof using view_rel_order.
    apply ora_total_mixin; try done.
    - intros ??; split; apply ora_core_increasing.
    - intros ???? [??].
      apply view_increasing in H as [??].
      split; eapply ora_increasing_closed; eauto.
    - intros ? [??] [??] [??]; split; apply ora_core_monoN; done.
    - intros ???? [Hva Hvf]%view_validN_both [Ha Hf].
      eapply ora_op_extend in Ha as (a1 & a2 & ? & ? & ?); last done.
      eapply (ora_op_extend(A := B)) in Hf as (f1 & f2 & ? & ? & ?); last done.
      exists (View a1 f1), (View a2 f2); destruct y1, y2; done.
    - intros ??? [Hva Hvf]%view_validN_both [Ha Hf].
      eapply ora_extend in Ha as (a & ? & ?); last done.
      eapply (ora_extend(A := B)) in Hf as (f & ? & ?); last done.
      exists (View a f); destruct y; done.
    - intros ??? [??]; split; apply ora_dist_orderN; auto.
    - intros ??? [??]; split; apply ora_orderN_S; auto.
    - intros ???? [??] [??]; split; etrans; eauto.
    - intros ???? [??]; split; apply ora_orderN_op; auto.
    - intros ???? [Ha Hf].
      destruct (view_validN_both _ _ _ H) as [Hva Hvf].
      rewrite view_validN_eq in H |- *.
      destruct (view_auth_proj y) as [(?, ?)|].
      + destruct (view_auth_proj x) as [(?, ?)|]; try done.
        destruct H as (? & ? & ? & ?), Ha as [? Ha], Hva as [? Hva]; simpl in *.
        split; [eapply ora_validN_orderN; eauto|].
        apply agree_order_dist in Ha; last done.
        setoid_rewrite Ha.
        eexists; split; first done; eauto.
      + destruct (view_auth_proj x) as [(?, ?)|].
        * destruct H as (? & ? & ? & ?); eauto.
        * destruct H; eauto.
    - split.
      + intros [??] ?; split; by apply ora_order_orderN.
      + intros; split; apply ora_order_orderN; intros; apply H.
    - rewrite view_pcore_eq; inversion 1 as [?? [Ha Hf]|]; subst.
      eexists; split; first done.
      split; simpl in *; [rewrite -Ha; apply uora_core_order_op | ].
      eapply ora_order_proper; [symmetry; apply Hf | done |].
      apply uora_core_order_op.
  Qed.

  Local Canonical Structure viewR := Ora (view rel) view_ora_mixin.

  Global Instance view_auth_oracore_id a : OraCoreId (●V□ a).
  Proof. do 2 constructor; simpl; auto. apply: core_id_core. Qed.
  Global Instance view_frag_oracore_id (b : B) : OraCoreId b → OraCoreId (◯V b).
  Proof. do 2 constructor; simpl; auto. apply: core_id_core. Qed.
  Global Instance view_both_oracore_id a (b : B) : OraCoreId b → OraCoreId (●V□ a ⋅ ◯V b).
  Proof. do 2 constructor; simpl; auto. rewrite !left_id. apply: core_id_core. Qed.

  Global Instance view_ora_discrete :
    OfeDiscrete A → OraDiscrete B → ViewRelDiscrete rel →
    OraDiscrete viewR.
  Proof.
    split; [apply _|..]; [move=> -[[[dq ag]|] b]; rewrite ?view_valid_eq ?view_validN_eq /=|].
    - rewrite -ora_discrete_valid_iff.
      setoid_rewrite <-(discrete_iff _ ag). naive_solver.
    - naive_solver.
    - by intros ?? [??]; split; apply ora_discrete_order.
  Qed.

End ora.

Notation viewUR rel := (Uora (view rel) (view_ucmra_mixin rel)).


(** * Utilities to construct functors *)
(** Due to the dependent type [rel] in [view] we cannot actually define
instances of the functor structures [rFunctor] and [urFunctor]. Functors can
only be defined for instances of [view], like [auth]. To make it more convenient
to define functors for instances of [view], we define the map operation
[view_map] and a bunch of lemmas about it. *)
Definition view_map {A A' B B'}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A → A') (g : B → B') (x : view rel) : view rel' :=
  View (prod_map id (agree_map f) <$> view_auth_proj x) (g (view_frag_proj x)).
Lemma view_map_id {A B} {rel : nat → A → B → Prop} (x : view rel) :
  view_map id id x = x.
Proof. destruct x as [[[]|] ]; by rewrite // /view_map /= agree_map_id. Qed.
Lemma view_map_compose {A A' A'' B B' B''}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    {rel'' : nat → A'' → B'' → Prop}
    (f1 : A → A') (f2 : A' → A'') (g1 : B → B') (g2 : B' → B'') (x : view rel) :
  view_map (f2 ∘ f1) (g2 ∘ g1) x
  =@{view rel''} view_map f2 g2 (view_map (rel':=rel') f1 g1 x).
Proof. destruct x as [[[]|] ];  by rewrite // /view_map /= agree_map_compose. Qed.
Lemma view_map_ext  {A A' B B' : ofe}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f1 f2 : A → A') (g1 g2 : B → B')
    `{!NonExpansive f1, !NonExpansive g1} (x : view rel) :
  (∀ a, f1 a ≡ f2 a) → (∀ b, g1 b ≡ g2 b) →
  view_map f1 g1 x ≡@{view rel'} view_map f2 g2 x.
Proof.
  intros. constructor; simpl; [|by auto].
  apply option_fmap_equiv_ext=> a; by rewrite /prod_map /= agree_map_ext.
Qed.
Global Instance view_map_ne {A A' B B' : ofe}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A → A') (g : B → B') `{Hf : !NonExpansive f, Hg : !NonExpansive g} :
  NonExpansive (view_map (rel':=rel') (rel:=rel) f g).
Proof.
  intros n [o1 bf1] [o2 bf2] [??]; split; simpl in *; [|by apply Hg].
  apply option_fmap_ne; [|done]=> pag1 pag2 ?.
  apply prod_map_ne; [done| |done]. by apply agree_map_ne.
Qed.

Definition viewO_map {A A' B B' : ofe}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop}
    (f : A -n> A') (g : B -n> B') : viewO rel -n> viewO rel' :=
  OfeMor (view_map f g).
Lemma viewO_map_ne {A A' B B' : ofe}
    {rel : nat → A → B → Prop} {rel' : nat → A' → B' → Prop} :
  NonExpansive2 (viewO_map (rel:=rel) (rel':=rel')).
Proof.
  intros n f f' Hf g g' Hg [[[p ag]|] bf]; split=> //=.
  do 2 f_equiv. by apply agreeO_map_ne.
Qed.

Lemma view_map_cmra_morphism {A A' B B'}
    {rel : view_rel A B} {rel' : view_rel A' B'}
    (f : A → A') (g : B → B') `{!NonExpansive f, !CmraMorphism g} :
  (∀ n a b, rel n a b → rel' n (f a) (g b)) →
  CmraMorphism (view_map (rel:=rel) (rel':=rel') f g).
Proof.
  intros Hrel. split.
  - apply _.
  - rewrite !view_validN_eq=> n [[[p ag]|] bf] /=;
      [|naive_solver eauto using cmra_morphism_validN].
    intros [? [a' [Hag ?]]]. split; [done|]. exists (f a'). split; [|by auto].
    by rewrite -agree_map_to_agree -Hag.
  - intros [o bf]. apply Some_proper; rewrite /view_map /=.
    f_equiv; by rewrite cmra_morphism_core.
  - intros [[[dq1 ag1]|] bf1] [[[dq2 ag2]|] bf2];
      try apply View_proper=> //=; by rewrite cmra_morphism_op.
Qed.

Lemma view_map_ora_morphism {A A'} {B B' : uora}
    {rel : view_rel A B} {rel' : view_rel A' B'}
    (Hrel : ∀n a x y, x ≼ₒ{n} y → rel n a y → rel n a x) (Hrel' : ∀n a x y, x ≼ₒ{n} y → rel' n a y → rel' n a x)
    (f : A → A') (g : B → B') `{!NonExpansive f, !OraMorphism g} :
  (∀ n a b, rel n a b → rel' n (f a) (g b)) →
  OraMorphism(A := viewR rel Hrel)(B := viewR rel' Hrel') (view_map (rel:=rel) (rel':=rel') f g).
Proof.
  intros Hfrel.
  split; first apply (view_map_cmra_morphism f g Hfrel).
  - intros ??? [??]; split; simpl; apply ora_morphism_orderN; try done.
    apply _.
  - intros ??.
    apply view_increasing in H as [??]; apply view_increasing; split; simpl; apply ora_morphism_increasing; try done.
    apply _.
Qed.
