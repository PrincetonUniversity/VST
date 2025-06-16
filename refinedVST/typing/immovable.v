From VST.typing Require Export type.
From VST.typing Require Import programs.
From VST.typing Require Import type_options.

Section immovable.
  Context `{!typeG Ok_ty Σ} {cs: compspecs}.

  Program Definition immovable (ty : address → type) : type := {|
    ty_own q l := (ty l).(ty_own) q l;
    ty_has_op_type _ _ := false;
    ty_own_val _ := True;
  |}.
  Solve Obligations with try done.
  Next Obligation. iIntros (????). by iApply ty_share. Qed.

  Global Instance immovable_le : Proper (pointwise_relation address (⊑) ==> (⊑)) immovable.
  Proof. solve_type_proper. Qed.
  Global Instance immovable_proper : Proper (pointwise_relation address (≡) ==> (≡)) immovable.
  Proof. solve_type_proper. Qed.

  Lemma simplify_hyp_place_immovable l β ty T:
    (l ◁ₗ{β} ty l -∗ T) ⊢ simplify_hyp (l◁ₗ{β} immovable ty) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Definition simplify_hyp_place_immovable_inst := [instance simplify_hyp_place_immovable with 0%N].
  Global Existing Instance simplify_hyp_place_immovable_inst.

  Lemma simplify_goal_place_immovable l β ty T:
    (l ◁ₗ{β} ty l) ∗ T ⊢ simplify_goal (l◁ₗ{β} immovable ty) T.
  Proof. iIntros "[$ $]". Qed.
  Definition simplify_goal_place_immovable_inst := [instance simplify_goal_place_immovable with 0%N].
  Global Existing Instance simplify_goal_place_immovable_inst.
End immovable.

Global Typeclasses Opaque immovable.
