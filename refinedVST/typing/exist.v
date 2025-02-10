From VST.typing Require Export type.
From VST.typing Require Import programs optional.
From VST.typing Require Import type_options.

Definition ty_exists_rty_def `{!typeG Σ} {cs : compspecs} {A} (ty : A → type) (a : A) : type := ty a.
Definition ty_exists_rty_aux : seal (@ty_exists_rty_def). by eexists. Qed.
Definition ty_exists_rty := (ty_exists_rty_aux).(unseal).
Definition ty_exists_rty_eq : ty_exists_rty = @ty_exists_rty_def := (ty_exists_rty_aux).(seal_eq).
Arguments ty_exists_rty {_ _ _} _ _.

Section tyexist.
  Context `{!typeG Σ} {cs : compspecs} {A : Type}.
  (* rty has to be sealed as unification goes crazy otherwise (it will
  unify everything with tyexists). However rty_type must not use
  opaque as it cannot be unified with A otherwise by typeclass
  search. *)
  Check ty_exists_rty.
  Program Definition tyexists_type (ty : A → type) (x : A) : type := {|
    ty_has_op_type := (ty x).(ty_has_op_type);
    ty_own := (ty_exists_rty _ ty x).(ty_own); 
    ty_own_val := (ty_exists_rty _ ty x).(ty_own_val); 
  |}.
  Next Obligation. move => *. rewrite ty_exists_rty_eq. by apply: ty_share. Qed.
  Next Obligation. move => *. rewrite ty_exists_rty_eq. by apply: ty_aligned. Qed.
  Next Obligation. move => *. rewrite ty_exists_rty_eq. by eapply ty_deref. Qed.
  Next Obligation. move => *. rewrite ty_exists_rty_eq. by apply: ty_ref. Qed.

  Definition tyexists (ty : A → type) : rtype _ := RType (tyexists_type ty).

  Lemma tyexists_le_l ty (x : A) :
    (x @ tyexists ty)%I ⊑ ty x.
  Proof. rewrite /with_refinement/=/tyexists_type. by constructor => //=; simpl_type; rewrite ty_exists_rty_eq. Qed.
  Lemma tyexists_le_r ty (x : A) :
    ty x ⊑ (x @ tyexists ty)%I.
  Proof. rewrite /with_refinement/=/tyexists_type. by constructor => //=; simpl_type; rewrite ty_exists_rty_eq. Qed.
  Lemma tyexists_eq ty (x : A) :
    (x @ tyexists ty)%I ≡@{type} ty x.
  Proof. rewrite /with_refinement/=/tyexists_type. constructor => //=; simpl_type; by rewrite ty_exists_rty_eq. Qed.

  Global Instance ty_exists_rty_le : Proper (pointwise_relation A (⊑) ==> (=) ==> (⊑)) tyexists_type.
  Proof. move => ????? ->. etrans; [apply tyexists_le_l|]. etrans; [|apply tyexists_le_r]. done. Qed.
  Global Instance ty_exists_rty_proper : Proper (pointwise_relation A (≡) ==> (=) ==> (≡)) tyexists_type.
  Proof. move => ????? ->. etrans; [apply tyexists_eq|]. etrans; [|symmetry; apply tyexists_eq]. done. Qed.

  (*
  Global Instance tyexists_loc_in_bounds ty β n `{!∀ x, LocInBounds (ty x) β n} :
    LocInBounds (tyexists ty) β n.
  Proof.
    constructor. iIntros (l) "Hl". unfold ty_of_rty; simpl_type. iDestruct "Hl" as (x) "Hl".
    rewrite tyexists_eq. by iApply loc_in_bounds_in_bounds.
  Qed.
  *)
End tyexist.

Notation "'∃ₜ' x .. y , p" := (ty_of_rty (tyexists (fun x => .. (ty_of_rty (tyexists (fun y => p))) ..)))
  (at level 200, x binder, right associativity,
   format "'[' '∃ₜ'  '/  ' x  ..  y ,  '/  ' p ']'")
  : bi_scope.

Section tyexist.
  Context `{!typeG Σ} {cs : compspecs} {A : Type}.

  Lemma simplify_hyp_place_tyexists x l β (ty : A → _) T:
    (l ◁ₗ{β} ty x -∗ T) ⊢ simplify_hyp (l◁ₗ{β} x @ tyexists ty) T.
  Proof. iIntros "HT Hl". rewrite tyexists_eq. by iApply "HT". Qed.
  
  Definition simplify_hyp_place_tyexists_inst :=
    [instance simplify_hyp_place_tyexists with 0%N].
  Global Existing Instance simplify_hyp_place_tyexists_inst.

  Lemma simplify_goal_place_tyexists x l β (ty : A → _) T:
    l ◁ₗ{β} ty x ∗ T ⊢ simplify_goal (l◁ₗ{β} x @ tyexists ty) T.
  Proof. iIntros "[? $]". by rewrite tyexists_eq. Qed.

  Definition simplify_goal_place_tyexists_inst := [instance simplify_goal_place_tyexists with 0%N].
  Global Existing Instance simplify_goal_place_tyexists_inst.

  Lemma simplify_hyp_val_tyexists x v ty T :
    (v ◁ᵥ ty x -∗ T) ⊢ simplify_hyp (v◁ᵥ x @ tyexists (A:=A) ty) T.
  Proof. iIntros "HT Hl". rewrite tyexists_eq. by iApply "HT". Qed.

  Definition simplify_hyp_val_tyexists_inst := [instance simplify_hyp_val_tyexists with 0%N].
  Global Existing Instance simplify_hyp_val_tyexists_inst.

  Lemma simplify_goal_val_tyexists x v ty T:
    v ◁ᵥ ty x ∗ T ⊢ simplify_goal (v◁ᵥ x @ tyexists (A:=A) ty) T.
  Proof. iIntros "[? $]". by rewrite tyexists_eq. Qed.

  Definition simplify_goal_val_tyexists_inst := [instance simplify_goal_val_tyexists with 0%N].
  Global Existing Instance simplify_goal_val_tyexists_inst.

  Global Instance simple_subsume_place_tyexists_l (ty1 : A → _) x ty2
    `{!SimpleSubsumePlace (ty1 x) ty2 P}:
    SimpleSubsumePlace (x @ tyexists ty1) ty2 P.
  Proof. iIntros (l β) "HP Hl". rewrite ! tyexists_eq. iApply (@simple_subsume_place with "HP Hl"). Qed.

  Global Instance simple_subsume_place_tyexists_r (ty2 : A → _) x ty1
    `{!SimpleSubsumePlace ty1 (ty2 x) P}:
    SimpleSubsumePlace ty1 (x @ tyexists ty2) P.
  Proof. iIntros (l β) "HP Hl". rewrite ! tyexists_eq. iApply (@simple_subsume_place with "HP Hl"). Qed.

  Global Program Instance tyexist_optional x (ty : A → _) optty ot1 ot2
    `{!∀ x, Optionable (ty x) optty ot1 ot2} : Optionable (x @ tyexists ty) optty ot1 ot2 := {|
    opt_pre v1 v2 := opt_pre (ty x) v1 v2
  |}.
  Next Obligation.
    move => ????????????. rewrite {1}/ty_own_val/= ty_exists_rty_eq /ty_has_op_type/ty_own_val. apply opt_bin_op.
  Qed.
  
  Global Instance optionable_agree_tyexists (ty2 : A → type) ty1
    `{!∀ x, OptionableAgree (ty2 x) ty1} : OptionableAgree (tyexists ty2) ty1.
  Proof. done. Qed.

End tyexist.

Global Typeclasses Opaque tyexists_type tyexists.
