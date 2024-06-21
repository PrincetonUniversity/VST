From iris.proofmode Require Export tactics.
From lithium Require Export base pure_definitions.

(** Definitions that are used by the Lithium automation. *)

(** * [iProp_to_Prop] *)
#[projections(primitive)]
Record iProp_to_Prop {PROP : bi} (P : PROP) : Type := i2p {
  i2p_P :> PROP;
  i2p_proof : i2p_P ⊢ P;
}.
Arguments i2p {_ _ _} _.
Arguments i2p_P {_ _} _.
Arguments i2p_proof {_ _} _.

(** * Checking if a hyp in the context
  The implementation can be found in interpreter.v *)
Class CheckOwnInContext {PROP : bi} (P : PROP) : Prop := { check_own_in_context : True }.

(** * [find_in_context] *)
Record find_in_context_info {PROP : bi} : Type := {
  fic_A : Type;
  fic_Prop : fic_A → PROP;
}.
(* The nat n is necessary to allow different options, they are tried starting from 0. *)
Definition find_in_context {PROP : bi} (fic : find_in_context_info) (T : fic.(fic_A) → PROP) : PROP :=
  (∃ b, fic.(fic_Prop) b ∗ T b).
Class FindInContext {PROP : bi} (fic : find_in_context_info) (key : Set) : Type :=
  find_in_context_proof T: iProp_to_Prop (PROP:=PROP) (find_in_context fic T)
.
Global Hint Mode FindInContext + + - : typeclass_instances.
Inductive FICSyntactic : Set :=.

(** The instance for searching with [FindDirect] is in [instances.v].  *)
Definition FindDirect {PROP : bi} {A} (P : A → PROP) := {| fic_A := A; fic_Prop := P; |}.
Global Typeclasses Opaque FindDirect.

(** ** [FindHypEqual]  *)
(** [FindHypEqual] is called with find_in_context key [key], an
hypothesis [Q] and a desired pattern [P], and then the instance
(usually a tactic) should try to generate a new pattern [P'] equal to
[P] that can be later unified with [Q]. *)
Class FindHypEqual {PROP : bi} (key : Type) (Q P P' : PROP) := find_hyp_equal_equal: P = P'.
Global Hint Mode FindHypEqual + + + ! - : typeclass_instances.

(** * [RelatedTo] *)
Class RelatedTo {PROP : bi} {A} (pat : A → PROP) : Type := {
  rt_fic : find_in_context_info (PROP:=PROP);
}.
Global Hint Mode RelatedTo + + + : typeclass_instances.
Global Arguments rt_fic {_ _ _} _.

(** * [IntroPersistent] *)
(** ** Definition *)
Class IntroPersistent {PROP : bi} (P P' : PROP) := {
  ip_persistent : P ⊢ □ P'
}.
Global Hint Mode IntroPersistent + + - : typeclass_instances.
(** ** Instances *)
Global Instance intro_persistent_intuit (PROP : bi) (P : PROP) : IntroPersistent (□ P) P.
Proof. constructor. iIntros "$". Qed.

(** * Simplification *)
(* n:
   None: no simplification
   Some 0: simplification which is always safe
   Some n: lower n: should be done before higher n (when compared with simplifyGoal)   *)
Definition simplify_hyp {PROP : bi} (P : PROP) (T : PROP) : PROP :=
  P -∗ T.
Class SimplifyHyp {PROP : bi} (P : PROP) (n : option N) : Type :=
  simplify_hyp_proof T : iProp_to_Prop (simplify_hyp P T).

Definition simplify_goal {PROP : bi} (P : PROP) (T : PROP) : PROP :=
  (P ∗ T).
Class SimplifyGoal {PROP : bi} (P : PROP) (n : option N) : Type :=
  simplify_goal_proof T : iProp_to_Prop (simplify_goal P T).

Global Hint Mode SimplifyHyp + + - : typeclass_instances.
Global Hint Mode SimplifyGoal + ! - : typeclass_instances.

(** * Subsumption *)
Definition subsume {PROP : bi} {A} (P1 : PROP) (P2 T : A → PROP) : PROP :=
  P1 -∗ ∃ x, P2 x ∗ T x.
Class Subsume {PROP : bi} {A} (P1 : PROP) (P2 : A → PROP) : Type :=
  subsume_proof T : iProp_to_Prop (subsume P1 P2 T).
Global Hint Mode Subsume + + + ! : typeclass_instances.

(** * case distinction *)
Definition case_if {PROP : bi} (P : Prop) (T1 T2 : PROP) : PROP :=
  (<affine> ⌜P⌝ -∗ T1) ∧ (<affine> ⌜¬ P⌝ -∗ T2).

Definition case_destruct {PROP : bi} {A} (a : A) (T : A → bool → PROP) : PROP :=
  ∃ b, T a b.

(** * [li_tactic] *)
Class LiTactic {PROP : bi} {A} (t : (A → PROP) → PROP) := {
  li_tactic_P : (A → PROP) → PROP;
  li_tactic_proof T : li_tactic_P T ⊢ t T;
}.
Arguments li_tactic_proof {_ _ _} _ _.
Arguments li_tactic_P {_ _ _} _ _.

Definition li_tactic {PROP : bi} {A} (t : (A → PROP) → PROP) (T : A → PROP) : PROP :=
  t T.
Arguments li_tactic : simpl never.

(** ** [li_vm_compute] *)
Definition li_vm_compute {PROP : bi} {A B} (f : A → option B) (x : A) (T : B → PROP) : PROP :=
  ∃ y, <affine> ⌜f x = Some y⌝ ∗ T y.
Arguments li_vm_compute : simpl never.
Global Typeclasses Opaque li_vm_compute.

Program Definition li_vm_compute_hint {PROP : bi} {A B} (f : A → option B) x a :
  f a = Some x →
  LiTactic (li_vm_compute (PROP:=PROP) f a) := λ H, {|
    li_tactic_P T := T x;
|}.
Next Obligation. move => ????????. iIntros "HT". iExists _. iFrame. iPureIntro. naive_solver. Qed.

Global Hint Extern 10 (LiTactic (li_vm_compute _ _)) =>
  eapply li_vm_compute_hint; evar_safe_vm_compute : typeclass_instances.

(** * [accu] *)
Definition accu {PROP : bi} (f : PROP → PROP) : PROP :=
  ∃ P, P ∗ □ f P.
Arguments accu : simpl never.
Global Typeclasses Opaque accu.

(** * trace *)
Definition li_trace {PROP : bi} {A} (t : A) (T : PROP) : PROP := T.

(** * [sep_list] *)
(** sep_list_id is a marker to link a sep_list in the goal to a
sep_list in the context. It also transfers the length between the two.
Values of type sep_list_id should always be opaque during the proof. *)
Record sep_list_id : Set := { sep_list_len : nat }.

(* TODO: use Z instead of nat for f such that one avoids adding a
Z.to_nat Z.of_nat roundtrip? It is a bit annoying since one needs to
introduce Z.of_nat for the list insert. *)
Definition sep_list {PROP : bi} (id : sep_list_id) A (ig : list nat) (l : list A) (f : nat → A → PROP) : PROP :=
  ⌜length l = sep_list_len id⌝ ∗ ([∗ list] i↦x∈l, if bool_decide (i ∈ ig) then True%I else f i x).
Global Typeclasses Opaque sep_list.

Definition FindSepList {PROP : bi} (id : sep_list_id) := {| fic_A := PROP; fic_Prop P := P; |}.
Global Typeclasses Opaque FindSepList.
