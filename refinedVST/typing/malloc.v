Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Export type.
From VST.typing Require Import programs own.
From VST.typing Require Import type_options.
From VST.typing Require Export typing.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".

(* TODO: Should this also contain a persistent [malloc_initialized]? *)
Class mallocG Σ := {
  malloc_block : address → Z → iProp Σ
}.
Global Arguments malloc_block {_ _} _ _.

Section malloc_block.
  Context `{!typeG OK_ty Σ} `{!mallocG Σ}.

  Definition FindMallocBlock (l : address) :=
    {| fic_A := assert; fic_Prop P := P; |}.
  Global Instance related_to_malloc_block A l (n : A → Z) :
    RelatedTo (λ y : A, ⎡malloc_block l (n y)⎤%I) :=
    {| rt_fic := FindMallocBlock l |}.

  Lemma find_in_context_malloc_block l T:
    find_in_context (FindMallocBlock l) T :-
      pattern: n, ⎡malloc_block l n⎤; return T ⎡malloc_block l n⎤.
  Proof. iDestruct 1 as (n) "[Hb HT]". iExists ⎡malloc_block _ _⎤%I. iFrame. Qed.
  Definition find_in_context_malloc_block_inst :=
    [instance find_in_context_malloc_block with FICSyntactic].
  Global Existing Instance find_in_context_malloc_block_inst | 1.

  Lemma subsume_malloc_block A l n1 n2 (T : A -> assert) :
    (∃ x : A, <affine> ⌜n1 = n2 x⌝ ∗ T x)
    ⊢ subsume ⎡malloc_block l n1⎤ (λ x : A, ⎡malloc_block l (n2 x)⎤) T.
  Proof. iIntros "[% [-> ?]] ?". iExists _. iFrame. Qed.
  Definition subsume_malloc_block_inst := [instance subsume_malloc_block].
  Global Existing Instance subsume_malloc_block_inst.
End malloc_block.

Section malloced.
  Context `{!typeG OK_ty Σ} {cs : compspecs} `{!mallocG Σ}.

  (** [early] determines if the malloc_block should be proven before
  or after ty. This is important for instantiating existentials *)
  Program Definition malloced_gen (early : bool) (n : Z) (ty : type) : type := {|
    ty_has_op_type ot mt := False%type;
    ty_own β l := (if β is Own then l ◁ₗ{β} ty ∗ ⎡malloc_block l n⎤ else True)%I;
    ty_own_val v cty := True%I;
  |}.
  Solve Obligations with try done.
  Next Obligation. by iIntros (??????) "?". Qed.

  Lemma simplify_hyp_malloced_gen early l ty n T:
    (⎡malloc_block l n⎤ -∗ l ◁ₗ ty -∗ T) ⊢ simplify_hyp (l ◁ₗ malloced_gen early n ty) T.
  Proof. iIntros "HT [Hl HP]". by iApply ("HT" with "HP"). Qed.
  Definition simplify_hyp_malloced_gen_inst :=
    [instance simplify_hyp_malloced_gen with 0%N].
  Global Existing Instance simplify_hyp_malloced_gen_inst.

  Lemma simplify_goal_malloced_early l ty n T:
    ⎡malloc_block l n⎤ ∗ l ◁ₗ ty ∗ T  ⊢ simplify_goal (l ◁ₗ malloced_gen true n ty) T.
  Proof. by iIntros "[$ [$ $]] !>". Qed.
  Definition simplify_goal_malloced_early_inst :=
    [instance simplify_goal_malloced_early with 0%N].
  Global Existing Instance simplify_goal_malloced_early_inst.

  Lemma simplify_goal_malloced_late l ty n T:
    l ◁ₗ ty ∗ ⎡malloc_block l n⎤ ∗ T  ⊢ simplify_goal (l ◁ₗ malloced_gen false n ty) T.
  Proof. by iIntros "[$ [$ $]] !>". Qed.
  Definition simplify_goal_malloced_late_inst :=
    [instance simplify_goal_malloced_late with 0%N].
  Global Existing Instance simplify_goal_malloced_late_inst.
End malloced.

Global Typeclasses Opaque malloced_gen.
Notation malloced := (malloced_gen false).
Notation malloced_early := (malloced_gen true).
Notation "malloced< n , ty >" := (malloced n ty) (only printing, format "'malloced<' n ,  ty '>'") : printing_sugar.
Notation "malloced_early< n , ty >" := (malloced_early n ty) (only printing, format "'malloced_early<' n ,  ty '>'") : printing_sugar.
