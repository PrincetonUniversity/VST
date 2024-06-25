From VST.lithium Require Export type.
From VST.lithium Require Import programs exist constrained.
From VST.lithium Require Import type_options.

Definition type_fixpoint_def `{!typeG Σ} {cs : compspecs} {A} : ((A -> type) → (A -> type)) → (A → type) :=
  λ T x, tyexists (λ ty, constrained (ty x) (⌜∀ x, ty x ⊑ T ty x⌝)).
Definition type_fixpoint_aux : seal (@type_fixpoint_def). Proof. by eexists. Qed.
Definition type_fixpoint := type_fixpoint_aux.(unseal).
Global Arguments type_fixpoint {Σ _ _ A} _ _.
Lemma type_fixpoint_unseal `{!typeG Σ} {cs : compspecs} {A} : type_fixpoint = @type_fixpoint_def Σ _ _ A.
Proof. rewrite -type_fixpoint_aux.(seal_eq) //. Qed.

Section fixpoint.
  Context `{!typeG Σ} {cs : compspecs} {A : Type}.
  Implicit Types (T : (A -> type) → (A -> type)).

  Local Lemma type_fixpoint_own_eq T x l β :
    l ◁ₗ{β} type_fixpoint T x ⊣⊢ ∃ ty, <affine>⌜∀ x, ty x ⊑ T ty x⌝ ∗ l ◁ₗ{β} ty x.
  Proof.
    rewrite type_fixpoint_unseal {1}/ty_own/=. f_equiv => ?.
    rewrite tyexists_eq. rewrite /own_constrained/persistent_own_constraint; simpl_type.
    iSplit.
    - iIntros "($ & %H2)". by iApply bi.intuitionistically_elim.
    - iIntros "(%H1 & $)". done.
  Qed.

  Local Lemma type_fixpoint_own_val_eq T x v :
    v ◁ᵥ type_fixpoint T x ⊣⊢ ∃ ty, <affine>⌜∀ x, ty x ⊑ T ty x⌝ ∗ v ◁ᵥ ty x.
  Proof.
    rewrite type_fixpoint_unseal {1}/ty_own_val/=. f_equiv => ?.
    rewrite tyexists_eq. rewrite /own_constrained/persistent_own_constraint; simpl_type.
    iSplit.
    - iIntros "($ & %H2)". by iApply bi.intuitionistically_elim.
    - iIntros "(%H1 & $)". done.
  Qed.

  Lemma type_fixpoint_greatest T ty :
    (∀ x, ty x ⊑ T ty x) →
    ∀ x, ty x ⊑ type_fixpoint T x.
  Proof.
    move => Hle. constructor.
    - iIntros (β l) "Hl". rewrite type_fixpoint_own_eq. iExists _. by iFrame.
    - iIntros (v) "Hv". rewrite type_fixpoint_own_val_eq. iExists _. by iFrame.
  Qed.

  Lemma type_fixpoint_unfold_1 T `{!TypeMono T}:
    ∀ x, type_fixpoint T x ⊑ T (type_fixpoint T) x.
  Proof.
    intros x. constructor => *.
    - rewrite type_fixpoint_own_eq.
      iIntros "Hle".
      iDestruct "Hle" as (ty) "(%Hle & HA)".
      destruct (Hle x) as [-> ?].
      edestruct (TypeMono0 ty (type_fixpoint T)) as [Hown2 ?]; [|by iApply Hown2].
      intros ?. by apply type_fixpoint_greatest.
    - rewrite type_fixpoint_own_val_eq. iIntros "[%ty [%Hle HA]]".
      destruct (Hle x) as [? ->].
      edestruct (TypeMono0 ty (type_fixpoint T)) as [? Hown2]; [|by iApply Hown2].
      intros ?. by apply type_fixpoint_greatest.
  Qed.

  Lemma type_fixpoint_unfold_2 T `{!TypeMono T} :
    ∀ x, T (type_fixpoint T) x ⊑ type_fixpoint T x.
  Proof.
    intros x. constructor => *.
    - rewrite type_fixpoint_own_eq. iIntros "?". iExists _. iSplit; [|done].
      iPureIntro. intros. apply TypeMono0. intros ?. by apply type_fixpoint_unfold_1.
    - rewrite type_fixpoint_own_val_eq. iIntros "?". iExists _. iSplit; [|done].
      iPureIntro. intros. apply TypeMono0. intros ?. by apply type_fixpoint_unfold_1.
  Qed.

  Lemma type_fixpoint_unfold T x `{!TypeMono T} :
    type_fixpoint T x ≡ T (type_fixpoint T) x.
  Proof. apply (anti_symm (⊑)); [by apply type_fixpoint_unfold_1 | by apply type_fixpoint_unfold_2]. Qed.

  Lemma type_fixpoint_unfold2 T x `{!TypeMono T}:
    T (type_fixpoint T) x ≡ T (T (type_fixpoint T)) x.
  Proof.
    apply (anti_symm (⊑)); apply TypeMono0;
      intros ?; [by apply type_fixpoint_unfold_1 | by apply type_fixpoint_unfold_2].
  Qed.
End fixpoint.

Section fixpoint.
  Context `{!typeG Σ} {cs : compspecs}.

  Lemma type_fixpoint_proper {A} x1 x2 (T1 T2 : (A → type) → (A → type)) :
    x1 = x2 → (∀ f x, T1 f x ≡ T2 f x) →
    type_fixpoint T1 x1 ≡ type_fixpoint T2 x2.
  Proof.
    move => -> HT.
    constructor => *.
    - rewrite !type_fixpoint_own_eq. by setoid_rewrite HT.
    - rewrite !type_fixpoint_own_val_eq. by setoid_rewrite HT.
  Qed.
End fixpoint.

Global Typeclasses Opaque type_fixpoint.

(*** Tests *)
Local Set Default Proof Using "Type*".
Section tests.
  Context `{!typeG Σ} {cs : compspecs}.
  Context (own_ptr : type → type) {HT: Proper ((⊑) ==> (⊑)) own_ptr}.

  Definition fixpoint_test_rec : (nat → type) → (nat → type) := (λ self, λ n, own_ptr (self (S n))).
  Arguments fixpoint_test_rec /.
  Global Instance fixpoint_test_rec_ne : TypeMono fixpoint_test_rec.
  Proof. solve_type_proper. Qed.

  Definition fixpoint_test : rtype nat := {|
    rty n := type_fixpoint fixpoint_test_rec n
  |}.

  Example test l :
    l◁ₗ 0%nat @ fixpoint_test -∗ True.
  Proof.
    simpl. rewrite /with_refinement/= type_fixpoint_unfold/=.
    change (type_fixpoint _ _) with (1%nat @ fixpoint_test)%I.
    iIntros "H". done.
  Qed.

End tests.
