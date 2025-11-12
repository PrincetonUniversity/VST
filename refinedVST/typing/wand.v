Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Export type.
From VST.typing Require Import type_options.
From iris_ora.algebra Require Import frac_auth ext_order excl.
From VST.veric Require Import lifting.
From compcert.cfrontend Require Import Clight.
From VST.lithium Require Export proof_state.
From lithium Require Import hooks.
From VST.typing Require Export type.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
From VST.typing Require Import type_options.

Section wand.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  Context {A : Type}.
  Implicit Types (P : A → iProp Σ).

  Program Definition wand_ex P (ty : A → type) : type := {|
    ty_own β l := match β return _ with
                  | Own => ∀ x, P x -∗ l ◁ₗ (ty x)
                  | Shr => True
                  end;
    ty_has_op_type _ _ := False%type;
    ty_own_val _ _ := True;
  |}%I.
  Solve Obligations with try done.
  Next Obligation. iIntros (?????) "H". done. Qed.
  
  Lemma subsume_wand B l P1 (P2 : B → A → iProp Σ) ty1 ty2 T:
    (* The trick is that we prove the wand at the very end so it can
    use all leftover resources. This only works if there is at most
    one wand per block (but this is enough for iterating over linked
    lists). *)
    (∃ z, T z ∗ (∀ x, P2 z x -∗ ∃ y, P1 y ∗ (l ◁ₗ ty1 y -∗ l ◁ₗ ty2 z x ∗ <affine> True)))
    ⊢ subsume (l ◁ₗ wand_ex P1 ty1) (λ z : B, l ◁ₗ wand_ex (P2 z) (ty2 z)) T.
  Proof.
    iIntros "(%&?&Hwand) Hwand2". iExists _. iFrame.
    iIntros (x) "HP2". iDestruct ("Hwand" with "HP2") as (y) "[HP1 Hty]".
    iDestruct ("Hwand2" with "HP1") as "Hty1".
    iDestruct ("Hty" with "[$Hty1]") as "H".
    iDestruct "H" as "(H & ?)". iFrame.
  Qed.

  Definition subsume_wand_inst := [instance subsume_wand].
  Global Existing Instance subsume_wand_inst.

  Lemma simplify_hyp_resolve_wand l (P : A → _) ty T:
    (∃ x, P x ∗ (l ◁ₗ ty x -∗ T))
    ⊢ simplify_hyp (l ◁ₗ wand_ex P ty) T.
  Proof. iDestruct 1 as (x) "[HP HT]". iIntros "Hwand". iApply "HT". by iApply "Hwand". Qed.
  (* must be before [simplify_goal_place_refine_r] *)
  Definition simplify_hyp_resolve_wand_inst := [instance simplify_hyp_resolve_wand with 9%N].
  Global Existing Instance simplify_hyp_resolve_wand_inst.

  Lemma simplify_goal_wand l P ty T:
    simplify_goal (l ◁ₗ wand_ex P ty) T :-
    and:
    | drop_spatial; ∀ x, inhale P x; exhale l ◁ₗ ty x; done
    | return T.
  Proof. iIntros "[#Hwand $]".
         liFromSyntax.
         iIntros (?) "H1".
         iDestruct ("Hwand" with "[$H1]") as "H".
         iDestruct "H" as "(? & ?)". iFrame.
  Qed.
  Definition simplify_goal_wand_inst := [instance simplify_goal_wand with 50%N].
  Global Existing Instance simplify_goal_wand_inst | 50.

End wand.
Global Typeclasses Opaque wand_ex.
Notation wand P ty := (wand_ex (A:=unit) (λ _, P) (λ _, ty)).
Notation "wand< P , ty >" := (wand P ty)
  (only printing, format "'wand<' P ,  ty '>'") : printing_sugar.

Section wand_val.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  Context {A : Type}.
  Implicit Types (P : A → iProp Σ).

  Program Definition wand_val_ex P (cty: Ctypes.type) (ty : A → type) : type := {|
    ty_has_op_type ot mt := (ot = cty ∧ type_is_by_value cty = true)%type; 
    ty_own β l := ∃ v, <affine> ⌜l `has_layout_loc` cty⌝ ∗ <affine>⌜v `has_layout_val` cty⌝ ∗
                                   l ↦[β]|cty| v ∗
        match β return _ with
        | Own => ∀ x, P x -∗ v ◁ᵥ|cty| (ty x)
        | Shr => True
        end;
    ty_own_val cty v :=  <affine> ⌜v `has_layout_val` cty⌝ ∗
                                    ∀ x, P x -∗ v ◁ᵥ|cty| (ty x)%I;
  |}%I.
  Next Obligation.
    iIntros (??????) "H".
    iDestruct "H" as (v) "(%&%&Hly&Hl)".
    iMod (heap_mapsto_own_state_share with "Hly") as "Hly". eauto with iFrame.
  Qed. 
  Next Obligation.
    iIntros (??????(->&?)) "Hl".
    by iDestruct "Hl" as (?) "(% & _)".
  Qed.
  Next Obligation.
    iIntros (???????) "(? &?)"; done.
  Qed.
  Next Obligation.
    iIntros (??????(->&?)) "Hl".
    iDestruct "Hl" as (?) "(% & % & Hl & HP)".
    by iFrame.
  Qed.
  Next Obligation.
    iIntros (???????(-> & ?)?) "Hl".
    iIntros "(% & HP)".
    rewrite /heap_mapsto_own_state.
    iExists v_rep.
    do 2 (iSplit; try done).
    iFrame.
  Qed.
  
  (*
  Global Instance wand_val_loc_in_bounds P ly β (ty : A → type):
    LocInBounds (wand_val_ex ly P ty) β (ly_size ly).
  Proof.
    constructor. iIntros (l) "Hl". iDestruct "Hl" as (?) "(_&Hly&Hl&_)".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "H".
    by iDestruct "Hly" as %->.
  Qed.
  *)
  
  Lemma subsume_wand_val B v ly2 P1 (P2 : B → A → iProp Σ) cty ty1 ty2 T:
    (* The trick is that we prove the wand at the very end so it can
    use all leftover resources. This only works if there is at most
    one wand per block (but this is enough for iterating over linked
    lists). *)
    (∃ z, <affine> ⌜cty = ly2 z⌝ ∗ T z ∗ (∀ x, P2 z x -∗ ∃ y, P1 y ∗ (v ◁ᵥₐₗ|cty| ty1 y -∗ v ◁ᵥₐₗ|cty| ty2 z x ∗ <affine> True)))
      ⊢ subsume (v ◁ᵥₐₗ|cty| wand_val_ex P1 cty ty1) (λ z : B, v ◁ᵥₐₗ|cty| wand_val_ex  (P2 z) (ly2 z) (ty2 z)) T.
  Proof.
    iIntros "(%&->&?&Hwand) (%&Hty1)". iExists _. iFrame. iSplit; [done|].
    iIntros (x) "HP2". iDestruct ("Hwand" with "HP2") as (y) "[HP1 Hwand]".
    iDestruct ("Hty1" with "HP1") as "Hty1". iDestruct ("Hwand" with "Hty1") as "[$ _]". 
  Qed.
  Definition subsume_wand_val_inst := [instance subsume_wand_val].
  Global Existing Instance subsume_wand_val_inst.

  Lemma simplify_hyp_resolve_wand_val v cty P ty T:
    (∃ x, P x ∗ (v ◁ᵥₐₗ|cty| ty x -∗ T))
      ⊢ simplify_hyp (v ◁ᵥₐₗ|cty| wand_val_ex P cty ty) T.
  Proof.
    iDestruct 1 as (x) "[HP HT]". iIntros "[_ Hwand]".
    iApply "HT". by iApply "Hwand".
  Qed.
  (* must be before [simplify_goal_place_refine_r] *)
  Definition simplify_hyp_resolve_wand_val_inst := [instance simplify_hyp_resolve_wand_val with 9%N].
  Global Existing Instance simplify_hyp_resolve_wand_val_inst.

  Lemma simplify_goal_wand_val v P cty ty T:
    simplify_goal (v ◁ᵥₐₗ|cty| wand_val_ex P cty ty) T :-
    and:
  | drop_spatial; ∀ x, inhale P x; exhale v ◁ᵥₐₗ|cty| ty x; done
  | exhale (<affine> ⌜(valinject (val_type cty) v) `has_layout_val` (val_type cty)⌝); return T.
  Proof.
    iIntros "[#Hwand [% $]]". iSplit; [done|].
    iIntros (?) "?". iDestruct ("Hwand" with "[$]") as "[H1 H2]". iFrame "H1".
  Qed.
  Definition simplify_goal_wand_val_inst := [instance simplify_goal_wand_val with 50%N].
  Global Existing Instance simplify_goal_wand_val_inst | 50.

End wand_val.
Global Typeclasses Opaque wand_val_ex.
Notation wand_val ly P ty := (wand_val_ex (A:=unit) ly (λ _, P) (λ _, ty)).
Notation "wand_val< ly , P , ty >" := (wand_val ly P ty)
  (only printing, format "'wand_val<' ly ,  P ,  ty '>'") : printing_sugar.
