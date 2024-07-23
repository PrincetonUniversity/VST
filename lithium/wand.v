From VST.lithium Require Export type.
From VST.lithium Require Import programs.
From VST.lithium Require Import type_options.

Section wand.
  Context `{!typeG Σ} {cs : compspecs}.

  Context {A : Type}.
  Implicit Types (P : A → iProp Σ).

  Program Definition wand_ex P (ty : A → type) : type := {|
    ty_own β l := match β return _ with
                  | Own => ∀ x, P x -∗ l ◁ₗ (ty x)
                  | Shr => True
                  end;
    ty_has_op_type _ _ := False%type;
    ty_own_val _ := True;
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
  Context `{!typeG Σ} {cs : compspecs}.

  Context {A : Type}.
  Implicit Types (P : A → iProp Σ).

  Program Definition wand_val_ex ly P (ty : A → type) : type := {|
    ty_has_op_type ot mt := ot = ly; 
    ty_own β l :=
      ∃ v,  <affine> ⌜field_compatible ly [] l⌝ ∗
                        <affine> ⌜field_compatible ly [] v ⌝ ∗ l ↦_ly[β] v ∗
        match β return _ with
        | Own => ∀ x, P x -∗ v ◁ᵥ (ty x)
        | Shr => True
        end;
     ty_own_val v := (<affine> ⌜field_compatible ly [] v⌝ ∗ ∀ x, P x -∗ v ◁ᵥ (ty x))%I;
  |}%I.
  Next Obligation.
    iIntros (??????) "H". iDestruct "H" as (v) "(Hly1&Hly2&Hl&_)".
    iMod (heap_mapsto_own_state_share with "Hl") as "Hl". eauto with iFrame.
  Qed. 
  Next Obligation. iIntros (??????->) "Hl". iDestruct "Hl" as (?) "[$ _]". Qed.
  Next Obligation. iIntros (???????) "Hl".
                   iDestruct "Hl" as (v) "(% & % & Hl1 & Hl2)".
                   rewrite / heap_mapsto_own_state.
                   iExists _. iFrame.
                   simpl in H. rewrite H. by iFrame. Qed.
  Next Obligation. iIntros (?????????) "Hl".
                   iIntros "(% & H3)".
                   rewrite /heap_mapsto_own_state.
                   iExists _. iFrame.
                   simpl in H.
                   rewrite H. iFrame.
                   iPureIntro.
                   split; auto.
                   subst. done. Qed.

  (*
  Global Instance wand_val_loc_in_bounds P ly β (ty : A → type):
    LocInBounds (wand_val_ex ly P ty) β (ly_size ly).
  Proof.
    constructor. iIntros (l) "Hl". iDestruct "Hl" as (?) "(_&Hly&Hl&_)".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "H".
    by iDestruct "Hly" as %->.
  Qed.
  *)
  
  Lemma subsume_wand_val B v ly1 ly2 P1 (P2 : B → A → iProp Σ) ty1 ty2 T:
    (* The trick is that we prove the wand at the very end so it can
    use all leftover resources. This only works if there is at most
    one wand per block (but this is enough for iterating over linked
    lists). *)
    (∃ z, <affine> ⌜ly1 = ly2 z⌝ ∗ T z ∗ (∀ x, P2 z x -∗ ∃ y, P1 y ∗ (v ◁ᵥ ty1 y -∗ v ◁ᵥ ty2 z x ∗ <affine> True)))
    ⊢ subsume (v ◁ᵥ wand_val_ex ly1 P1 ty1) (λ z : B, v ◁ᵥ wand_val_ex (ly2 z) (P2 z) (ty2 z)) T.
  Proof.
    iIntros "(%&->&?&Hwand) (%&Hty1)". iExists _. iFrame. iSplit; [done|].
    iIntros (x) "HP2". iDestruct ("Hwand" with "HP2") as (y) "[HP1 Hwand]".
    iDestruct ("Hty1" with "HP1") as "Hty1". iDestruct ("Hwand" with "Hty1") as "[$ _]". 
  Qed.
  Definition subsume_wand_val_inst := [instance subsume_wand_val].
  Global Existing Instance subsume_wand_val_inst.

  Lemma simplify_hyp_resolve_wand_val v ly P ty T:
    (∃ x, P x ∗ (v ◁ᵥ ty x -∗ T))
    ⊢ simplify_hyp (v ◁ᵥ wand_val_ex ly P ty) T.
  Proof.
    iDestruct 1 as (x) "[HP HT]". iIntros "[_ Hwand]".
    iApply "HT". by iApply "Hwand".
  Qed.
  (* must be before [simplify_goal_place_refine_r] *)
  Definition simplify_hyp_resolve_wand_val_inst := [instance simplify_hyp_resolve_wand_val with 9%N].
  Global Existing Instance simplify_hyp_resolve_wand_val_inst.

  Lemma simplify_goal_wand_val v P ly ty T:
    simplify_goal (v ◁ᵥ wand_val_ex ly P ty) T :-
    and:
    | drop_spatial; ∀ x, inhale P x; exhale v ◁ᵥ ty x; done
    | exhale (<affine> ⌜field_compatible ly [] v⌝); return T.
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
