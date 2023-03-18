(* modified from iris.algebra.auth *)

From VST.veric Require Export share_alg dfrac view.
From iris.algebra Require Import proofmode_classes big_op.
From iris.prelude Require Import options.

(** The authoritative camera with fractional authoritative elements *)
(** The authoritative camera has 2 types of elements: the authoritative element
[●{dq} a] and the fragment [◯ b] (of which there can be several). To enable
sharing of the authoritative element [●{dq} a], it is equiped with a
discardable fraction [dq]. Updates are only possible with the full
authoritative element [● a] (syntax for [●{#1} a]]), while fractional
authoritative elements have agreement, i.e., [✓ (●{dq1} a1 ⋅ ●{dq2} a2) → a1 ≡
a2]. *)

(** * Definition of the view relation *)
(** The authoritative camera is obtained by instantiating the view camera. *)
Definition auth_view_rel_raw {A : ucmra} (n : nat) (a b : A) : Prop :=
  b ≼{n} a ∧ ✓{n} a.
Lemma auth_view_rel_raw_mono (A : ucmra) n1 n2 (a1 a2 b1 b2 : A) :
  auth_view_rel_raw n1 a1 b1 →
  a1 ≡{n2}≡ a2 →
  b2 ≼{n2} b1 →
  n2 ≤ n1 →
  auth_view_rel_raw n2 a2 b2.
Proof.
  intros [??] Ha12 ??. split.
  - trans b1; [done|]. rewrite -Ha12. by apply cmra_includedN_le with n1.
  - rewrite -Ha12. by apply cmra_validN_le with n1.
Qed.
Lemma auth_view_rel_raw_valid (A : ucmra) n (a b : A) :
  auth_view_rel_raw n a b → ✓{n} b.
Proof. intros [??]; eauto using cmra_validN_includedN. Qed.
Lemma auth_view_rel_raw_unit (A : ucmra) n :
  ∃ a : A, auth_view_rel_raw n a ε.
Proof. exists ε. split; [done|]. apply ucmra_unit_validN. Qed.
Canonical Structure auth_view_rel {A : ucmra} : view_rel A A :=
  ViewRel auth_view_rel_raw (auth_view_rel_raw_mono A)
          (auth_view_rel_raw_valid A) (auth_view_rel_raw_unit A).

Lemma auth_view_rel_unit {A : ucmra} n (a : A) : auth_view_rel n a ε ↔ ✓{n} a.
Proof. split; [by intros [??]|]. split; auto using ucmra_unit_leastN. Qed.
Lemma auth_view_rel_exists {A : ucmra} n (b : A) :
  (∃ a, auth_view_rel n a b) ↔ ✓{n} b.
Proof.
  split; [|intros; exists b; by split].
  intros [a Hrel]. eapply auth_view_rel_raw_valid, Hrel.
Qed.

Global Instance auth_view_rel_discrete {A : ucmra} :
  CmraDiscrete A → ViewRelDiscrete (auth_view_rel (A:=A)).
Proof.
  intros ? n a b [??]; split.
  - by apply cmra_discrete_included_iff_0.
  - by apply cmra_discrete_valid_iff_0.
Qed.

Lemma auth_view_rel_order : ∀ {A : uora} (H : ∀n (x y : A), x ≼ₒ{n} y → x ≼{n} y) n (a x y : A),
  x ≼ₒ{n} y → auth_view_rel n a y → auth_view_rel n a x.
Proof.
  inversion 3; split=> //.
  trans y; auto.
Qed.

(** * Definition and operations on the authoritative camera *)
(** The type [auth] is not defined as a [Definition], but as a [Notation].
This way, one can use [auth A] with [A : Type] instead of [A : ucmra], and let
canonical structure search determine the corresponding camera instance. *)
Notation auth A := (view (A:=A) (B:=A) auth_view_rel_raw).
Definition authO (A : ucmra) : ofe := viewO (A:=A) (B:=A) auth_view_rel.
Definition authC (A : ucmra) : cmra := viewC (A:=A) (B:=A) auth_view_rel.
Definition authUC (A : ucmra) : ucmra := viewUC (A:=A) (B:=A) auth_view_rel.
Definition authR (A : uora) (H : ∀n (x y : A), x ≼ₒ{n} y → x ≼{n} y) : ora := view.viewR (A:=A) (B:=A) auth_view_rel (auth_view_rel_order H).
Definition authUR (A : uora) (H : ∀n (x y : A), x ≼ₒ{n} y → x ≼{n} y) : uora :=
  (Uora' (auth A) (ofe_mixin (authO A)) (cmra_mixin (authC A)) (ora_mixin (authR A H)) (view_ucmra_mixin auth_view_rel)).

Definition auth_auth {A: ucmra} : dfrac → A → auth A := view_auth.
Definition auth_frag {A: ucmra} : A → auth A := view_frag.

#[export] Typeclasses Opaque auth_auth auth_frag.

Global Instance: Params (@auth_auth) 2 := {}.
Global Instance: Params (@auth_frag) 1 := {}.

Notation "● dq a" := (auth_auth dq a)
  (at level 20, dq custom dfrac at level 1, format "● dq  a").
Notation "◯ a" := (auth_frag a) (at level 20).

(** * Laws of the authoritative camera *)
(** We omit the usual [equivI] lemma because it is hard to state a suitably
general version in terms of [●] and [◯], and because such a lemma has never
been needed in practice. *)
Section auth.
  Context {A : ucmra}.
  Implicit Types a b : A.
  Implicit Types x y : auth A.
  Implicit Types q : share.
  Implicit Types dq : dfrac.

  Global Instance auth_auth_ne dq : NonExpansive (@auth_auth A dq).
  Proof. rewrite /auth_auth. apply _. Qed.
  Global Instance auth_auth_proper dq : Proper ((≡) ==> (≡)) (@auth_auth A dq).
  Proof. rewrite /auth_auth. apply _. Qed.
  Global Instance auth_frag_ne : NonExpansive (@auth_frag A).
  Proof. rewrite /auth_frag. apply _. Qed.
  Global Instance auth_frag_proper : Proper ((≡) ==> (≡)) (@auth_frag A).
  Proof. rewrite /auth_frag. apply _. Qed.

  Global Instance auth_auth_dist_inj n : Inj2 (=) (dist n) (dist n) (@auth_auth A).
  Proof. rewrite /auth_auth. apply _. Qed.
  Global Instance auth_auth_inj : Inj2 (=) (≡) (≡) (@auth_auth A).
  Proof. rewrite /auth_auth. apply _. Qed.
  Global Instance auth_frag_dist_inj n : Inj (dist n) (dist n) (@auth_frag A).
  Proof. rewrite /auth_frag. apply _. Qed.
  Global Instance auth_frag_inj : Inj (≡) (≡) (@auth_frag A).
  Proof. rewrite /auth_frag. apply _. Qed.

  Global Instance auth_ofe_discrete : OfeDiscrete A → OfeDiscrete (authO A).
  Proof. apply _. Qed.
  Global Instance auth_auth_discrete dq a :
    Discrete a → Discrete (ε : A) → Discrete (●{dq} a).
  Proof. rewrite /auth_auth. apply _. Qed.
  Global Instance auth_frag_discrete a : Discrete a → Discrete (◯ a).
  Proof. rewrite /auth_frag. apply _. Qed.
  Global Instance auth_cmra_discrete : CmraDiscrete A → CmraDiscrete (authC A).
  Proof. apply _. Qed.

  (** Operation *)
  Lemma auth_auth_dfrac_op dq1 dq2 a : ●{dq1 ⋅ dq2} a ≡ ●{dq1} a ⋅ ●{dq2} a.
  Proof. apply view_auth_dfrac_op. Qed.
  Global Instance auth_auth_dfrac_is_op dq dq1 dq2 a :
    IsOp dq dq1 dq2 → IsOp' (●{dq} a) (●{dq1} a) (●{dq2} a).
  Proof. rewrite /auth_auth. apply _. Qed.

  Lemma auth_frag_op a b : ◯ (a ⋅ b) = ◯ a ⋅ ◯ b.
  Proof. apply view_frag_op. Qed.
  Lemma auth_frag_mono a b : a ≼ b → ◯ a ≼ ◯ b.
  Proof. apply view_frag_mono. Qed.
  Lemma auth_frag_core a : core (◯ a) = ◯ (core a).
  Proof. apply view_frag_core. Qed.
  Lemma auth_both_core_discarded a b :
    core (●□ a ⋅ ◯ b) ≡ ●□ a ⋅ ◯ (core b).
  Proof. apply view_both_core_discarded. Qed.
  Lemma auth_both_core_frac q a b :
    core (●{#q} a ⋅ ◯ b) ≡ ◯ (core b).
  Proof. apply view_both_core_frac. Qed.

  Global Instance auth_auth_core_id a : CoreId (●□ a).
  Proof. rewrite /auth_auth. apply _. Qed.
  Global Instance auth_frag_core_id a : CoreId a → CoreId (◯ a).
  Proof. rewrite /auth_frag. apply _. Qed.
  Global Instance auth_both_core_id a1 a2 : CoreId a2 → CoreId (●□ a1 ⋅ ◯ a2).
  Proof. rewrite /auth_auth /auth_frag. apply _. Qed.
  Global Instance auth_frag_is_op a b1 b2 :
    IsOp a b1 b2 → IsOp' (◯ a) (◯ b1) (◯ b2).
  Proof. rewrite /auth_frag. apply _. Qed.
  Global Instance auth_frag_sep_homomorphism :
    MonoidHomomorphism op op (≡) (@auth_frag A).
  Proof. rewrite /auth_frag. apply _. Qed.

  Lemma big_opL_auth_frag {B} (g : nat → B → A) (l : list B) :
    (◯ [^op list] k↦x ∈ l, g k x) ≡ [^op list] k↦x ∈ l, ◯ (g k x).
  Proof. apply (big_opL_commute _). Qed.
  Lemma big_opM_auth_frag `{Countable K} {B} (g : K → B → A) (m : gmap K B) :
    (◯ [^op map] k↦x ∈ m, g k x) ≡ [^op map] k↦x ∈ m, ◯ (g k x).
  Proof. apply (big_opM_commute _). Qed.
  Lemma big_opS_auth_frag `{Countable B} (g : B → A) (X : gset B) :
    (◯ [^op set] x ∈ X, g x) ≡ [^op set] x ∈ X, ◯ (g x).
  Proof. apply (big_opS_commute _). Qed.
  Lemma big_opMS_auth_frag `{Countable B} (g : B → A) (X : gmultiset B) :
    (◯ [^op mset] x ∈ X, g x) ≡ [^op mset] x ∈ X, ◯ (g x).
  Proof. apply (big_opMS_commute _). Qed.

  (** Validity *)
  Lemma auth_auth_dfrac_op_invN n dq1 a dq2 b : ✓{n} (●{dq1} a ⋅ ●{dq2} b) → a ≡{n}≡ b.
  Proof. apply view_auth_dfrac_op_invN. Qed.
  Lemma auth_auth_dfrac_op_inv dq1 a dq2 b : ✓ (●{dq1} a ⋅ ●{dq2} b) → a ≡ b.
  Proof. apply view_auth_dfrac_op_inv. Qed.
  Lemma auth_auth_dfrac_op_inv_L `{!LeibnizEquiv A} dq1 a dq2 b :
    ✓ (●{dq1} a ⋅ ●{dq2} b) → a = b.
  Proof. by apply view_auth_dfrac_op_inv_L. Qed.

  Lemma auth_auth_dfrac_validN n dq a : ✓{n} (●{dq} a) ↔ ✓ dq ∧ ✓{n} a.
  Proof. by rewrite view_auth_dfrac_validN auth_view_rel_unit. Qed.
  Lemma auth_auth_validN n a : ✓{n} (● a) ↔ ✓{n} a.
  Proof. by rewrite view_auth_validN auth_view_rel_unit. Qed.

  Lemma auth_auth_dfrac_op_validN n dq1 dq2 a1 a2 :
    ✓{n} (●{dq1} a1 ⋅ ●{dq2} a2) ↔  ✓ (dq1 ⋅ dq2) ∧ a1 ≡{n}≡ a2 ∧ ✓{n} a1.
  Proof. by rewrite view_auth_dfrac_op_validN auth_view_rel_unit. Qed.
  Lemma auth_auth_op_validN n a1 a2 : ✓{n} (● a1 ⋅ ● a2) ↔ False.
  Proof. apply view_auth_op_validN. Qed.

  (** The following lemmas are also stated as implications, which can be used
  to force [apply] to use the lemma in the right direction. *)
  Lemma auth_frag_validN n b : ✓{n} (◯ b) ↔ ✓{n} b.
  Proof. by rewrite view_frag_validN auth_view_rel_exists. Qed.
  Lemma auth_frag_validN_1 n b : ✓{n} (◯ b) → ✓{n} b.
  Proof. apply auth_frag_validN. Qed.
  Lemma auth_frag_validN_2 n b : ✓{n} b → ✓{n} (◯ b).
  Proof. apply auth_frag_validN. Qed.
  Lemma auth_frag_op_validN n b1 b2 : ✓{n} (◯ b1 ⋅ ◯ b2) ↔ ✓{n} (b1 ⋅ b2).
  Proof. apply auth_frag_validN. Qed.
  Lemma auth_frag_op_validN_1 n b1 b2 : ✓{n} (◯ b1 ⋅ ◯ b2) → ✓{n} (b1 ⋅ b2).
  Proof. apply auth_frag_op_validN. Qed.
  Lemma auth_frag_op_validN_2 n b1 b2 : ✓{n} (b1 ⋅ b2) → ✓{n} (◯ b1 ⋅ ◯ b2).
  Proof. apply auth_frag_op_validN. Qed.

  Lemma auth_both_dfrac_validN n dq a b :
    ✓{n} (●{dq} a ⋅ ◯ b) ↔ ✓ dq ∧ b ≼{n} a ∧ ✓{n} a.
  Proof. apply view_both_dfrac_validN. Qed.
  Lemma auth_both_validN n a b : ✓{n} (● a ⋅ ◯ b) ↔ b ≼{n} a ∧ ✓{n} a.
  Proof. apply view_both_validN. Qed.

  Lemma auth_auth_dfrac_valid dq a : ✓ (●{dq} a) ↔ ✓ dq ∧ ✓ a.
  Proof.
    rewrite view_auth_dfrac_valid !cmra_valid_validN.
    by setoid_rewrite auth_view_rel_unit.
  Qed.
  Lemma auth_auth_valid a : ✓ (● a) ↔ ✓ a.
  Proof.
    rewrite view_auth_valid !cmra_valid_validN.
    by setoid_rewrite auth_view_rel_unit.
  Qed.

  Lemma auth_auth_dfrac_op_valid dq1 dq2 a1 a2 :
    ✓ (●{dq1} a1 ⋅ ●{dq2} a2) ↔ ✓ (dq1 ⋅ dq2) ∧ a1 ≡ a2 ∧ ✓ a1.
  Proof.
    rewrite view_auth_dfrac_op_valid !cmra_valid_validN.
    setoid_rewrite auth_view_rel_unit. done.
  Qed.
  Lemma auth_auth_op_valid a1 a2 : ✓ (● a1 ⋅ ● a2) ↔ False.
  Proof. apply view_auth_op_valid. Qed.

  (** The following lemmas are also stated as implications, which can be used
  to force [apply] to use the lemma in the right direction. *)
  Lemma auth_frag_valid b : ✓ (◯ b) ↔ ✓ b.
  Proof.
    rewrite view_frag_valid cmra_valid_validN.
    by setoid_rewrite auth_view_rel_exists.
  Qed.
  Lemma auth_frag_valid_1 b : ✓ (◯ b) → ✓ b.
  Proof. apply auth_frag_valid. Qed.
  Lemma auth_frag_valid_2 b : ✓ b → ✓ (◯ b).
  Proof. apply auth_frag_valid. Qed.
  Lemma auth_frag_op_valid b1 b2 : ✓ (◯ b1 ⋅ ◯ b2) ↔ ✓ (b1 ⋅ b2).
  Proof. apply auth_frag_valid. Qed.
  Lemma auth_frag_op_valid_1 b1 b2 : ✓ (◯ b1 ⋅ ◯ b2) → ✓ (b1 ⋅ b2).
  Proof. apply auth_frag_op_valid. Qed.
  Lemma auth_frag_op_valid_2 b1 b2 : ✓ (b1 ⋅ b2) → ✓ (◯ b1 ⋅ ◯ b2).
  Proof. apply auth_frag_op_valid. Qed.

  (** These lemma statements are a bit awkward as we cannot possibly extract a
  single witness for [b ≼ a] from validity, we have to make do with one witness
  per step-index, i.e., [∀ n, b ≼{n} a]. *)
  Lemma auth_both_dfrac_valid dq a b :
    ✓ (●{dq} a ⋅ ◯ b) ↔  ✓ dq ∧ (∀ n, b ≼{n} a) ∧ ✓ a.
  Proof.
    rewrite view_both_dfrac_valid. apply and_iff_compat_l. split.
    - intros Hrel. split.
      + intros n. by destruct (Hrel n).
      + apply cmra_valid_validN=> n. by destruct (Hrel n).
    - intros [Hincl Hval] n. split; [done|by apply cmra_valid_validN].
  Qed.
  Lemma auth_both_valid a b :
    ✓ (● a ⋅ ◯ b) ↔ (∀ n, b ≼{n} a) ∧ ✓ a.
  Proof. rewrite auth_both_dfrac_valid. split; [naive_solver|done]. Qed.

  (* The reverse direction of the two lemmas below only holds if the camera is
  discrete. *)
  Lemma auth_both_dfrac_valid_2 dq a b : ✓ dq → ✓ a → b ≼ a → ✓ (●{dq} a ⋅ ◯ b).
  Proof.
    intros. apply auth_both_dfrac_valid.
    naive_solver eauto using cmra_included_includedN.
  Qed.
  Lemma auth_both_valid_2 a b : ✓ a → b ≼ a → ✓ (● a ⋅ ◯ b).
  Proof. intros ??. by apply auth_both_dfrac_valid_2. Qed.

  Lemma auth_both_dfrac_valid_discrete `{!CmraDiscrete A} dq a b :
    ✓ (●{dq} a ⋅ ◯ b) ↔ ✓ dq ∧ b ≼ a ∧ ✓ a.
  Proof.
    rewrite auth_both_dfrac_valid. setoid_rewrite <-cmra_discrete_included_iff.
    naive_solver eauto using O.
  Qed.
  Lemma auth_both_valid_discrete `{!CmraDiscrete A} a b :
    ✓ (● a ⋅ ◯ b) ↔ b ≼ a ∧ ✓ a.
  Proof. rewrite auth_both_dfrac_valid_discrete. split; [naive_solver|done]. Qed.

  (** Inclusion *)
  Lemma auth_auth_dfrac_includedN n dq1 dq2 a1 a2 b :
    ●{dq1} a1 ≼{n} ●{dq2} a2 ⋅ ◯ b ↔ (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2.
  Proof. apply view_auth_dfrac_includedN. Qed.
  Lemma auth_auth_dfrac_included dq1 dq2 a1 a2 b :
    ●{dq1} a1 ≼ ●{dq2} a2 ⋅ ◯ b ↔ (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2.
  Proof. apply view_auth_dfrac_included. Qed.
  Lemma auth_auth_includedN n a1 a2 b :
    ● a1 ≼{n} ● a2 ⋅ ◯ b ↔ a1 ≡{n}≡ a2.
  Proof. apply view_auth_includedN. Qed.
  Lemma auth_auth_included a1 a2 b :
    ● a1 ≼ ● a2 ⋅ ◯ b ↔ a1 ≡ a2.
  Proof. apply view_auth_included. Qed.

  Lemma auth_frag_includedN n dq a b1 b2 :
    ◯ b1 ≼{n} ●{dq} a ⋅ ◯ b2 ↔ b1 ≼{n} b2.
  Proof. apply view_frag_includedN. Qed.
  Lemma auth_frag_included dq a b1 b2 :
    ◯ b1 ≼ ●{dq} a ⋅ ◯ b2 ↔ b1 ≼ b2.
  Proof. apply view_frag_included. Qed.

  (** The weaker [auth_both_included] lemmas below are a consequence of the
  [auth_auth_included] and [auth_frag_included] lemmas above. *)
  Lemma auth_both_dfrac_includedN n dq1 dq2 a1 a2 b1 b2 :
    ●{dq1} a1 ⋅ ◯ b1 ≼{n} ●{dq2} a2 ⋅ ◯ b2 ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2.
  Proof. apply view_both_dfrac_includedN. Qed.
  Lemma auth_both_dfrac_included dq1 dq2 a1 a2 b1 b2 :
    ●{dq1} a1 ⋅ ◯ b1 ≼ ●{dq2} a2 ⋅ ◯ b2 ↔
      (dq1 ≼ dq2 ∨ dq1 = dq2) ∧ a1 ≡ a2 ∧ b1 ≼ b2.
  Proof. apply view_both_dfrac_included. Qed.
  Lemma auth_both_includedN n a1 a2 b1 b2 :
    ● a1 ⋅ ◯ b1 ≼{n} ● a2 ⋅ ◯ b2 ↔ a1 ≡{n}≡ a2 ∧ b1 ≼{n} b2.
  Proof. apply view_both_includedN. Qed.
  Lemma auth_both_included a1 a2 b1 b2 :
    ● a1 ⋅ ◯ b1 ≼ ● a2 ⋅ ◯ b2 ↔ a1 ≡ a2 ∧ b1 ≼ b2.
  Proof. apply view_both_included. Qed.

  (** Updates *)
  Lemma auth_update a b a' b' :
    (a,b) ~l~> (a',b') → ● a ⋅ ◯ b ~~> ● a' ⋅ ◯ b'.
  Proof.
    intros Hup. apply view_update=> n bf [[bf' Haeq] Hav].
    destruct (Hup n (Some (bf ⋅ bf'))); simpl in *; [done|by rewrite assoc|].
    split; [|done]. exists bf'. by rewrite -assoc.
  Qed.

  Lemma auth_update_alloc a a' b' : (a,ε) ~l~> (a',b') → ● a ~~> ● a' ⋅ ◯ b'.
  Proof. intros. rewrite -(right_id _ _ (● a)). by apply auth_update. Qed.
  Lemma auth_update_dealloc a b a' : (a,b) ~l~> (a',ε) → ● a ⋅ ◯ b ~~> ● a'.
  Proof. intros. rewrite -(right_id _ _ (● a')). by apply auth_update. Qed.
  Lemma auth_update_auth a a' b' : (a,ε) ~l~> (a',b') → ● a ~~> ● a'.
  Proof.
    intros. etrans; first exact: auth_update_alloc.
    exact: cmra_update_op_l.
  Qed.
  Lemma auth_update_auth_persist dq a : ●{dq} a ~~> ●□ a.
  Proof. apply view_update_auth_persist. Qed.

  Lemma auth_update_dfrac_alloc dq a b `{!CoreId b} :
    b ≼ a → ●{dq} a ~~> ●{dq} a ⋅ ◯ b.
  Proof.
    intros Ha%(core_id_extract _ _). apply view_update_dfrac_alloc=> n bf [??].
    split; [|done]. rewrite Ha (comm _ a). by apply cmra_monoN_l.
  Qed.

  Lemma auth_local_update a b0 b1 a' b0' b1' :
    (b0, b1) ~l~> (b0', b1') → b0' ≼ a' → ✓ a' →
    (● a ⋅ ◯ b0, ● a ⋅ ◯ b1) ~l~> (● a' ⋅ ◯ b0', ● a' ⋅ ◯ b1').
  Proof.
    intros. apply view_local_update; [done|]=> n [??]. split.
    - by apply cmra_included_includedN.
    - by apply cmra_valid_validN.
  Qed.
End auth.

(*(** * Functor *)
Program Definition authURF (F : uorarFunctor) : uorarFunctor := {|
  uorarFunctor_car A _ B _ := authUR (uorarFunctor_car F A B);
  uorarFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (uorarFunctor_map F fg) (uorarFunctor_map F fg)
|}.
Next Obligation.
  intros F A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne; by apply urFunctor_map_ne.
Qed.
Next Obligation.
  intros F A ? B ? x; simpl in *. rewrite -{2}(view_map_id x).
  apply (view_map_ext _ _ _ _)=> y; apply urFunctor_map_id.
Qed.
Next Obligation.
  intros F A1 ? A2 ? A3 ? B1 ? B2 ? B3 ? f g f' g' x; simpl in *.
  rewrite -view_map_compose.
  apply (view_map_ext _ _ _ _)=> y; apply urFunctor_map_compose.
Qed.
Next Obligation.
  intros F A1 ? A2 ? B1 ? B2 ? fg; simpl.
  apply view_map_cmra_morphism; [apply _..|]=> n a b [??]; split.
  - by apply (cmra_morphism_monotoneN _).
  - by apply (cmra_morphism_validN _).
Qed.

Global Instance authURF_contractive F :
  urFunctorContractive F → urFunctorContractive (authURF F).
Proof.
  intros ? A1 ? A2 ? B1 ? B2 ? n f g Hfg.
  apply viewO_map_ne; by apply urFunctor_map_contractive.
Qed.

Program Definition authRF (F : urFunctor) : rFunctor := {|
  rFunctor_car A _ B _ := authR (urFunctor_car F A B);
  rFunctor_map A1 _ A2 _ B1 _ B2 _ fg :=
    viewO_map (urFunctor_map F fg) (urFunctor_map F fg)
|}.
Solve Obligations with apply authURF.

Global Instance authRF_contractive F :
  urFunctorContractive F → rFunctorContractive (authRF F).
Proof. apply authURF_contractive. Qed.*)
