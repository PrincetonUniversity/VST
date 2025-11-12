Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Export type.
From VST.typing Require Import programs.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
From VST.typing Require Import type_options.

Record global_type `{!typeG OK_ty Σ} {cs : compspecs} := GT {
  gt_A : Type;
  gt_type : gt_A → type;
}.
Arguments GT {_ _ _} _ _.

Class globalG `{!typeG OK_ty Σ} {cs : compspecs} := {
  global_initialized_types : gmap ident global_type;
}.
Arguments globalG _ _ {_ _}.

Section globals.
  Context `{!typeG OK_ty Σ} {cs : compspecs} `{!globalG OK_ty Σ} (ge : Genv.t Clight.fundef Ctypes.type).
  Import EqNotations.

  Definition global_with_type (name : ident) (β : own_state) (ty : type) : iProp Σ :=
    (∃ l, <affine> ⌜Genv.find_symbol ge name = Some l⌝ ∗ (l, Ptrofs.zero) ◁ₗ{β} ty)%I.

  (* A version of initialized that does not depend on globalG. This is
  a work-around to allow the type of one global to refer to another as
  long as there are no cycles (see t_adequacy). The proper solution
  would be to use higher-order ghost state instead of globalG. *)
  Definition initialized_raw {A} (name : ident) (x : A) (l' : option Values.block) (ty' : option global_type)  : iProp Σ :=
    (∃ l ty, <affine> ⌜l' = Some l⌝ ∗ <affine> ⌜ty' = Some ty⌝ ∗
          ∃ Heq : A = ty.(gt_A), (l, Ptrofs.zero) ◁ₗ{Shr} ty.(gt_type) (rew [λ x, x] Heq in x))%I.

  Definition initialized {A} (name : ident) (x : A) : iProp Σ :=
    initialized_raw name x (Genv.find_symbol ge name) (global_initialized_types !! name).

  Global Instance initialized_persistent A name (x : A) : Persistent (initialized name x).
  Proof. apply _. Qed.

  Global Instance initialized_intro_persistent A name (x : A) `{!Affine (initialized name x)}:
    IntroPersistent (initialized name x) (initialized name x).
  Proof. constructor.
         iIntros "H". 
         iApply bi.intuitionistically_intro; try done.
         apply _.
  Qed.

  Lemma simplify_global_with_type_hyp name β ty T:
    (∀ l, <affine> ⌜Genv.find_symbol ge name = Some l⌝ -∗ (l, Ptrofs.zero) ◁ₗ{β} ty -∗ T)
    ⊢ simplify_hyp (global_with_type name β ty) T.
  Proof. iIntros "HT". iDestruct 1 as (l) "(% & Hl)". by iApply "HT". Qed.
  Definition simplify_global_with_type_hyp_inst :=
    [instance simplify_global_with_type_hyp with 0%N].
  Global Existing Instance simplify_global_with_type_hyp_inst.

  Lemma simplify_global_with_type_goal name β ty l `{!TCFastDone (Genv.find_symbol ge name = Some l)} T:
    (l, Ptrofs.zero) ◁ₗ{β} ty ∗ T
    ⊢ simplify_goal (global_with_type name β ty) T.
  Proof. unfold TCFastDone in *. iIntros "[? $]". iExists _. by iFrame. Qed.
  Definition simplify_global_with_type_goal_inst := [instance simplify_global_with_type_goal with 0%N].
  Global Existing Instance simplify_global_with_type_goal_inst.

  Lemma simplify_initialized_hyp A (x : A) name ty l
    `{!TCFastDone (Genv.find_symbol ge name = Some l)}
    `{!TCFastDone (global_initialized_types !! name = Some ty)} T:
    (∃ (Heq : A = ty.(gt_A)), (l, Ptrofs.zero) ◁ₗ{Shr} ty.(gt_type) (rew [λ x, x] Heq in x) -∗ T)
    ⊢ simplify_hyp (initialized name x) T.
  Proof.
    unfold TCFastDone in *. iDestruct 1 as (?) "HT". iDestruct 1 as (l' ??? Heq2) "Hl". simplify_eq. iApply "HT" => /=.
    (** HERE WE USE AXIOM K! *)
    by rewrite (UIP_refl _ _ Heq2).
  Qed.
  Definition simplify_initialized_hyp_inst := [instance simplify_initialized_hyp with 0%N].
  Global Existing Instance simplify_initialized_hyp_inst.

  Lemma initialized_intro A ty name l (x : A) :
    Genv.find_symbol ge name = Some l →
    global_initialized_types !! name = Some ty →
    (∃ (Heq : A = ty.(gt_A)), (l, Ptrofs.zero) ◁ₗ{Shr} ty.(gt_type) (rew [λ x, x] Heq in x)) -∗
    initialized name x.
  Proof. iIntros (??) "Hl". iExists _, _. by iFrame. Qed.

  Lemma simplify_initialized_goal A (x : A) name l ty
    `{!TCFastDone (Genv.find_symbol ge name = Some l)}
    `{!TCFastDone (global_initialized_types !! name = Some ty)} T:
    (∃ (Heq : A = ty.(gt_A)), (l, Ptrofs.zero) ◁ₗ{Shr} ty.(gt_type) (rew [λ x, x] Heq in x) ∗ T)
    ⊢ simplify_goal (initialized name x) T.
  Proof.
    unfold TCFastDone in *. iIntros "[% [? $]]".
    iApply initialized_intro; [done..|]. by iExists _.
  Qed.
  Definition simplify_initialized_goal_inst := [instance simplify_initialized_goal with 0%N].
  Global Existing Instance simplify_initialized_goal_inst.


  (** Subsumption *)
  Definition FindInitialized (name : ident) (A : Type) :=
    {| fic_A := A; fic_Prop x := (initialized name x); |}.
  Global Instance related_to_initialized B name A (x : B → A) :
    RelatedTo (λ y : B, initialized name (x y)) :=
    {| rt_fic := FindInitialized name A |}.

  Lemma find_in_context_initialized name A T:
    (∃ x, initialized name x ∗ T x)
    ⊢ find_in_context (FindInitialized name A) T.
  Proof. iDestruct 1 as (x) "[Hinit HT]". iExists _. iFrame. Qed.
  Definition find_in_context_initialized_inst :=
    [instance find_in_context_initialized with FICSyntactic].
  Global Existing Instance find_in_context_initialized_inst | 1.

  Lemma subsume_initialized B name A (x1 : A) x2 T:
    (∃ y, <affine> ⌜x1 = x2 y⌝ ∗ T y)
    ⊢ subsume (initialized name x1) (λ y : B, initialized name (x2 y)) T.
  Proof. iIntros "H".
         iDestruct "H" as (y) "(-> & H)".
         iIntros "Hi". iExists _. iFrame. Qed.
  Definition subsume_initialized_inst := [instance subsume_initialized].
  Global Existing Instance subsume_initialized_inst.

End globals.

Global Typeclasses Opaque FindInitialized.
Global Typeclasses Opaque initialized global_with_type.
