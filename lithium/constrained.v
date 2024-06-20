From VST.lithium Require Export type.
From VST.lithium Require Import programs (* optional *).
From VST.lithium Require Import type_options.

Class OwnConstraint `{!typeG Σ} {cs : compspecs} (P : own_state → mpred) : Prop := {
  own_constraint_persistent : Persistent (P Shr);
  own_constraint_share E : ↑shrN ⊆ E → P Own ={E}=∗ P Shr;
}.

Global Existing Instance own_constraint_persistent.

Section own_constrained.
  Context `{!typeG Σ} {cs : compspecs}.

  Program Definition own_constrained (P : own_state → mpred) `{!OwnConstraint P} (ty : type) : type := {|
    ty_has_op_type ot mt := ty.(ty_has_op_type) ot mt;
    ty_own β l := (l ◁ₗ{β} ty ∗ P β)%I;
     ty_own_val v := (v ◁ᵥ ty ∗ P Own)%I;
  |}.
  Next Obligation.
    move => ty P ? l E ?. iIntros "[Hl HP]".
    iMod (ty_share with "Hl") as "$" => //.
    by iApply own_constraint_share.
  Qed.
  Next Obligation. iIntros (???????) "[? _]". by iApply ty_aligned. Qed.
  Next Obligation. iIntros (???????) "(H & H1)". iFrame "H1". iApply (ty_deref with "[H]"); done. Qed.
  Next Obligation. iIntros (?????????) "Hl [? $]". by iApply (ty_ref with "[//] [Hl]"). Qed.
  

  Global Instance own_constrained_rty_le P `{!OwnConstraint P} : Proper ((⊑) ==> (⊑)) (own_constrained P).
  Proof. solve_type_proper. Qed.
  Global Instance own_constrained_rty_proper P `{!OwnConstraint P} : Proper ((≡) ==> (≡)) (own_constrained P).
  Proof. solve_type_proper. Qed.

  (*
  Global Instance own_constrained_loc_in_bounds ty β n P `{!OwnConstraint P} `{!LocInBounds ty β n} :
    LocInBounds (own_constrained P ty) β n.
  Proof.
    constructor. iIntros (l) "[Hl _]". by iApply loc_in_bounds_in_bounds.
  Qed.
  *)
  
  Lemma copy_as_own_constrained l β P `{!OwnConstraint P} ty {HC: CopyAs l β ty} T:
    (P β -∗ (HC T).(i2p_P)) ⊢ copy_as l β (own_constrained P ty) T.
  Proof.
    iIntros "HT [Hty HP]". iDestruct (i2p_proof with "(HT HP)") as "HT". by iApply "HT".
  Qed.
  Definition copy_as_own_constrained_inst := [instance copy_as_own_constrained].
  Global Existing Instance copy_as_own_constrained_inst.

  Lemma simplify_hyp_place_own_constrained P l β ty `{!OwnConstraint P} T:
    (P β -∗ l ◁ₗ{β} ty -∗ T) ⊢ simplify_hyp (l◁ₗ{β} own_constrained P ty) T.
  Proof. iIntros "HT [Hl HP]". by iApply ("HT" with "HP"). Qed.
  Definition simplify_hyp_place_own_constrained_inst :=
    [instance simplify_hyp_place_own_constrained with 0%N].
  Global Existing Instance simplify_hyp_place_own_constrained_inst.

  Lemma simplify_goal_place_own_constrained P l β ty `{!OwnConstraint P} T:
    l ◁ₗ{β} ty ∗ P β ∗ T  ⊢ simplify_goal (l◁ₗ{β} own_constrained P ty) T.
  Proof. iIntros "[$ [$ $]]". Qed.
  Definition simplify_goal_place_own_constrained_inst :=
    [instance simplify_goal_place_own_constrained with 0%N].
  Global Existing Instance simplify_goal_place_own_constrained_inst.

  Lemma simplify_hyp_val_own_constrained P v ty `{!OwnConstraint P} T:
    (P Own -∗ v ◁ᵥ ty -∗ T) ⊢ simplify_hyp (v ◁ᵥ own_constrained P ty) T.
  Proof. iIntros "HT [Hl HP]". by iApply ("HT" with "HP"). Qed.
  Definition simplify_hyp_val_own_constrained_inst :=
    [instance simplify_hyp_val_own_constrained with 0%N].
  Global Existing Instance simplify_hyp_val_own_constrained_inst.

  Lemma simplify_goal_val_own_constrained P v ty `{!OwnConstraint P} T:
    v ◁ᵥ ty ∗ P Own ∗ T ⊢ simplify_goal (v ◁ᵥ own_constrained P ty) T.
  Proof. iIntros "[$ [$ $]]". Qed.
  Definition simplify_goal_val_own_constrained_inst :=
    [instance simplify_goal_val_own_constrained with 0%N].
  Global Existing Instance simplify_goal_val_own_constrained_inst.

  (*
  Global Program Instance own_constrained_optional ty P optty ot1 ot2 `{!OwnConstraint P} `{!Optionable ty optty ot1 ot2} : Optionable (own_constrained P ty) optty ot1 ot2 := {|
    opt_pre v1 v2 := opt_pre ty v1 v2
  |}.
  Next Obligation.
    iIntros (???????[]?????) "Hpre H1 H2". 1: iDestruct "H1" as "[H1 _]".
    - by iApply (opt_bin_op true with "Hpre H1 H2").
    - by iApply (opt_bin_op false with "Hpre H1 H2").
  Qed.

  Global Instance optionable_agree_own_constrained P (ty2 : type) `{!OwnConstraint P} `{!OptionableAgree ty1 ty2} : OptionableAgree (own_constrained P ty1) ty2.
  Proof. done. Qed.
  *)

  Definition tyown_constraint (l : address) (ty : type) (β : own_state) : iProp Σ := l ◁ₗ{β} ty.

  Global Program Instance tyown_constraint_own_constraint l ty: OwnConstraint (tyown_constraint l ty).
  Next Obligation. move => ???. apply: ty_share. Qed.

  Lemma simplify_hyp_place_tyown_constrained l β ty T:
    (l ◁ₗ{β} ty -∗ T) ⊢ simplify_hyp (tyown_constraint l ty β) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Definition simplify_hyp_place_tyown_constrained_inst :=
    [instance simplify_hyp_place_tyown_constrained with 0%N].
  Global Existing Instance simplify_hyp_place_tyown_constrained_inst.

  Lemma simplify_goal_place_tyown_constrained l β ty T:
    l ◁ₗ{β} ty ∗ T ⊢ simplify_goal (tyown_constraint l ty β) T.
  Proof. done. Qed.
  Definition simplify_goal_place_tyown_constrained_inst :=
    [instance simplify_goal_place_tyown_constrained with 0%N].
  Global Existing Instance simplify_goal_place_tyown_constrained_inst.
End own_constrained.
Notation "own_constrained< P , ty >" := (own_constrained P ty)
  (only printing, format "'own_constrained<' P ,  ty '>'") : printing_sugar.

Global Typeclasses Opaque own_constrained tyown_constraint.
Arguments tyown_constraint : simpl never.

Section constrained.
  Context `{!typeG Σ} {cs : compspecs}.

  Definition persistent_own_constraint (P : mpred) (β : own_state) : mpred := □ P.

  Global Instance persistent_own_constraint_inst P: OwnConstraint (persistent_own_constraint P).
  Proof. constructor; [by apply _ | by iIntros (??) "H !>"]. Qed.

  Lemma simplify_hyp_place_persistent_constrained P β T:
    (P -∗ T) ⊢ simplify_hyp (persistent_own_constraint P β) T.
  Proof. iIntros "HT #Hl". by iApply "HT". Qed.
  Definition simplify_hyp_place_persistent_constrained_inst :=
    [instance simplify_hyp_place_persistent_constrained with 0%N].
  Global Existing Instance simplify_hyp_place_persistent_constrained_inst.

  Lemma simplify_goal_place_persistent_constrained P `{!Persistent P} β T:
    P ∗ T ⊢ simplify_goal (persistent_own_constraint P β) T.
  (* Proof. iIntros "[#$ $]". Qed. *)
    (* require P is affine *)
  Admitted.
  Definition simplify_goal_place_persistent_constrained_inst :=
    [instance simplify_goal_place_persistent_constrained with 0%N].
  Global Existing Instance simplify_goal_place_persistent_constrained_inst.
End constrained.

Global Typeclasses Opaque persistent_own_constraint.
Arguments persistent_own_constraint : simpl never.

Notation constrained ty P := (own_constrained (persistent_own_constraint P) ty).

Notation "constrained< ty , P >" := (constrained ty P)
  (only printing, format "'constrained<' ty ,  P '>'") : printing_sugar.

Section nonshr_constrained.
  Context `{!typeG Σ} {cs : compspecs}.

  Definition nonshr_constraint (P : iProp Σ) (β : own_state) : iProp Σ :=
    match β with | Own => P | Shr => True end.

  Global Program Instance nonshr_constraint_own_constraint P: OwnConstraint (nonshr_constraint P).
  Next Obligation. iIntros (???) "?". done. Qed.

  Lemma simplify_hyp_place_nonshr_constrained P T:
    (P -∗ T) ⊢ simplify_hyp (nonshr_constraint P Own) T.
  Proof. iIntros "HT Hl". by iApply "HT". Qed.
  Definition simplify_hyp_place_nonshr_constrained_inst :=
    [instance simplify_hyp_place_nonshr_constrained with 0%N].
  Global Existing Instance simplify_hyp_place_nonshr_constrained_inst.

  Lemma simplify_goal_place_nonshr_constrained P T:
    P ∗ T ⊢ simplify_goal (nonshr_constraint P Own) T.
  Proof. done. Qed.
  Definition simplify_goal_place_nonshr_constrained_inst :=
    [instance simplify_goal_place_nonshr_constrained with 0%N].
  Global Existing Instance simplify_goal_place_nonshr_constrained_inst.

End nonshr_constrained.
Notation "nonshr_constraint< P , β >" := (nonshr_constraint P β)
  (only printing, format "'nonshr_constraint<' P ,  β '>'") : printing_sugar.

Global Typeclasses Opaque nonshr_constraint.
Arguments nonshr_constraint : simpl never.
