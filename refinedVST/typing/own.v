Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Export type.
From VST.typing Require Import programs optional boolean int singleton.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
From VST.typing Require Import type_options.
From compcert Require Import Ctypesdefs.

Section own.
  Context `{!typeG OK_ty Σ} {cs : compspecs} (ge : Genv.t Clight.fundef Ctypes.type).

  Local Typeclasses Transparent place.

  Program Definition frac_ptr_type (β : own_state) (ty : type) (l' : address) : type := {|
    ty_has_op_type ot mt := (match ot with | Tpointer t attr => ot = tptr t | _ => False end)%type;
    ty_own β' l := (<affine>⌜l `has_layout_loc` (tptr tvoid)⌝ ∗ l ↦[β']|tptr tvoid| l' ∗ (l' ◁ₗ{own_state_min β' β} ty))%I;
    ty_own_val cty v_rep := (<affine> ⌜repinject cty v_rep = adr2val l'⌝ ∗ l' ◁ₗ{β} ty)%I;
  |}.
  Next Obligation.
    iIntros (β ?????) "($&Hl&H)". rewrite left_id.
    iMod (heap_mapsto_own_state_share with "Hl") as "$".
    destruct β => //=. by iApply ty_share.
  Qed.
  Next Obligation.
    iIntros (β ty l ot mt l' ?). destruct ot; try done.
    rewrite /has_layout_loc !field_compatible_tptr.
    by iDestruct 1 as (?) "_". Qed.
  Next Obligation.
    iIntros (β ty l ot mt l' ?) "(%H1 & Hl)".
    rewrite /repinject /has_layout_val /= in H1; subst.
    iPureIntro.
    destruct ot; try done.
    inv H. 
    split; [|done].
    rewrite /value_fits => ? /=.
    simple_if_tac; done.
  Qed.
  Next Obligation.
    iIntros (β ty l ot mt l' ?) "(%&Hl&Hl')".
    rewrite left_id. unfold heap_mapsto_own_state.
    destruct ot; try done. inv H. simpl.
    rewrite /tptr.
    erewrite (mapsto_tptr _ _ tvoid ot).
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (β ty l ot mt l' v ? ?) "Hl [% Hl']".
    destruct ot; try done. inv H.
    simpl in H1. rewrite H1.
    unfold has_layout_loc in *. rewrite field_compatible_tptr in H0. unfold heap_mapsto_own_state.
    erewrite (mapsto_tptr _ _ tvoid ot). by iFrame.
  Qed.

  Global Instance frac_ptr_type_le : Proper ((=) ==> (⊑) ==> (=) ==> (⊑)) frac_ptr_type.
  Proof. solve_type_proper. Qed.
  Global Instance frac_ptr_type_proper : Proper ((=) ==> (≡) ==> (=) ==> (≡)) frac_ptr_type.
  Proof. solve_type_proper. Qed.

  Definition frac_ptr (β : own_state) (ty : type) : rtype _ := RType (frac_ptr_type β ty).

  (* this is at least true for Own, but not for Shr? *)
(*  Global Instance frac_ptr_loc_in_bounds l ty β1 β2 : LocInBounds (l @ frac_ptr β1 ty) β2.
  Proof.
    constructor. iIntros (?) "(_&Hl&_)".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    iApply loc_in_bounds_shorten; last done. by rewrite /val_of_loc.
  Qed. *)

  Global Instance frac_ptr_defined cty p β ty: DefinedTy cty (p @ frac_ptr β ty).
  Proof.
    iIntros (?) "(% & _)".
    destruct cty; try done; destruct v; try done.
  Qed.

  Lemma frac_ptr_mono A ty1 ty2 l β β' p p' T:
    (p ◁ₗ{own_state_min β β'} ty1 -∗ ∃ x, <affine> ⌜p = p' x⌝ ∗ p ◁ₗ{own_state_min β β'} (ty2 x) ∗ T x)
    ⊢ subsume (l ◁ₗ{β} p @ frac_ptr β' ty1) (λ x : A, l ◁ₗ{β} (p' x) @ frac_ptr β' (ty2 x)) T.
  Proof.
    iIntros "HT [% [? Hl]]". iDestruct ("HT" with "Hl") as (? ->) "[??]".
    iExists _. by iFrame.
  Qed.
  Definition frac_ptr_mono_inst := [instance frac_ptr_mono].
  Global Existing Instance frac_ptr_mono_inst.

  Global Instance frac_ptr_simple_mono ty1 ty2 p β P `{!SimpleSubsumePlace ty1 ty2 P}:
    SimpleSubsumePlace (p @ frac_ptr β ty1) (p @ frac_ptr β ty2) P.
  Proof. iIntros (l β') "HP [$ [$ Hl]]". iApply (@simple_subsume_place with "HP Hl"). Qed.

  Lemma type_place_frac p β K β1 ty1 l ot T:
    typed_place ge K p (own_state_min β1 β) ty1 (λ l2 β2 ty2 typ, T l2 β2 ty2 (λ t, (p @ (frac_ptr β (typ t)))))
    ⊢ typed_place ge (DerefPCtx (tptr ot) :: K) l β1 (p @ (frac_ptr β ty1)) T.
  Proof.
    iIntros "HP" (Φ) "(%&Hm&Hl) HΦ" => /=.
    iMod (heap_mapsto_own_state_to_mt with "Hm") as (q Hq ?) "Hm" => //.
    iModIntro; iExists _, _; iSplit => //.
    iSplitL "Hm".
    { rewrite (mapsto_tptr _ _ _ ot) /mapsto data_at_rec_eq /= simple_mapsto.mapsto_eq //; by iFrame. }
    iExists _; iSplit => //.
    iIntros "Hm"; iApply ("HP" with "Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]". iFrame. iSplitR => //.
    iMod "Hm"; iMod (heap_mapsto_own_state_from_mt with "[Hm]") as "H"; last iApply "H"; [done..|].
    rewrite (mapsto_tptr _ _ _ ot) /mapsto data_at_rec_eq -simple_mapsto.mapsto_eq //=.
  Qed.
  Definition type_place_frac_inst := [instance type_place_frac].
  Global Existing Instance type_place_frac_inst.

  (* typed_addr_of should probably involve wp_lvalue
  Lemma type_addr_of f e ot (T : val → _):
    typed_addr_of ge f e (λ l β ty, T l (l @ frac_ptr β ty))
    ⊢ typed_val_expr ge f (Eaddrof e ot) T.
  Proof.
    iIntros "Haddr" (Φ) "HΦ". rewrite -wp_addrof.
    Print typed_addr_of.
    iApply "Haddr". iIntros (l β ty) "Hl HT".
    iApply ("HΦ" with "[Hl] HT").
    iSplit => //.
  Qed. *)

  Lemma simplify_frac_ptr (v : val) (p : address) cty ty β T:
    (<affine> ⌜v = p⌝ -∗ p ◁ₗ{β} ty -∗ T)
      ⊢ simplify_hyp (v ◁ᵥₐₗ|tptr cty| p @ frac_ptr β ty) T.
  Proof.  iIntros "HT Hl".
          iDestruct "Hl" as (?) "Hl".
          iApply "HT"; try done.
  Qed.
  Definition simplify_frac_ptr_inst := [instance simplify_frac_ptr with 0%N].
  Global Existing Instance simplify_frac_ptr_inst.

  Lemma simplify_frac_ptr' (v : val) (p : address) cty ty β (T : assert):
    (<affine> ⌜v = p⌝ -∗ ⎡p ◁ₗ{β} ty⎤ -∗ T)
      ⊢ simplify_hyp ⎡v ◁ᵥₐₗ|tptr cty| p @ frac_ptr β ty⎤ T.
  Proof.  iIntros "HT Hl".
          iDestruct "Hl" as (?) "Hl".
          iApply "HT"; try done.
  Qed.
  Definition simplify_frac_ptr'_inst := [instance simplify_frac_ptr' with 0%N].
  Global Existing Instance simplify_frac_ptr'_inst.

  Lemma simplify_frac_ptr_unrefined (v : val) (p : address) cty ty β T:
    (∀ p : address, <affine> ⌜v = p⌝ -∗ p ◁ₗ{β} ty -∗ T)
      ⊢ simplify_hyp (v ◁ᵥₐₗ|tptr cty| frac_ptr β ty) T.
  Proof.  iIntros "HT Hl".
          rewrite /ty_own_val_at /ty_own_val /=.
          iDestruct "Hl" as (?) "Hl".
          by iApply (simplify_frac_ptr with "HT").
  Qed.
  Definition simplify_frac_ptr_unrefined_inst := [instance simplify_frac_ptr_unrefined with 0%N].
  Global Existing Instance simplify_frac_ptr_unrefined_inst.

  Lemma simplify_frac_ptr_unrefined' (v : val) (p : address) cty ty β (T : assert):
    (∀ p : address, <affine> ⌜v = p⌝ -∗ ⎡p ◁ₗ{β} ty⎤ -∗ T)
      ⊢ simplify_hyp ⎡v ◁ᵥₐₗ|tptr cty| p @ frac_ptr β ty⎤ T.
  Proof.  iIntros "HT Hl".
          iDestruct "Hl" as (?) "Hl".
          iApply (simplify_frac_ptr' _ p cty with "HT").
          rewrite /ty_own_val_at /ty_own_val /=; by iFrame.
  Qed.
  Definition simplify_frac_ptr_unrefined'_inst := [instance simplify_frac_ptr_unrefined' with 0%N].
  Global Existing Instance simplify_frac_ptr_unrefined'_inst.

  Lemma simplify_goal_frac_ptr_val cty ty (v : val) β (p : address) T:
    <affine> ⌜v = p⌝ ∗ p ◁ₗ{β} ty ∗ T
    ⊢ simplify_goal (v ◁ᵥₐₗ|tptr cty| p @ frac_ptr β ty) T.
  Proof.
    by iIntros "[-> [$ $]]".
  Qed.
  Definition simplify_goal_frac_ptr_val_inst := [instance simplify_goal_frac_ptr_val with 0%N].
  Global Existing Instance simplify_goal_frac_ptr_val_inst.

  Lemma simplify_goal_frac_ptr_val_unrefined cty ty (v : val) β T:
    (∃ p : address, <affine> ⌜v = p⌝ ∗ p ◁ₗ{β} ty ∗ T)
      ⊢ simplify_goal (v ◁ᵥₐₗ|tptr cty| frac_ptr β ty) T.
  Proof. iIntros "[% [-> [? $]]]".
         rewrite /ty_own_val_at /ty_own_val /=.
         iExists _. iSplit; auto.
  Qed.
  Definition simplify_goal_frac_ptr_val_unrefined_inst :=
    [instance simplify_goal_frac_ptr_val_unrefined with 0%N].
  Global Existing Instance simplify_goal_frac_ptr_val_unrefined_inst.

  Lemma simplify_frac_ptr_place_shr_to_own l p1 p2 β T:
    (⌜p1 = p2⌝ -∗ l ◁ₗ{β} p1 @ frac_ptr Own (place p2) -∗ T)
    ⊢ simplify_hyp (l ◁ₗ{β} p1 @ frac_ptr Shr (place p2)) T.
  Proof. iIntros "HT (%&Hl&%)". subst. iApply "HT" => //. by iFrame. Qed.
  Definition simplify_frac_ptr_place_shr_to_own_inst :=
    [instance simplify_frac_ptr_place_shr_to_own with 50%N].
  Global Existing Instance simplify_frac_ptr_place_shr_to_own_inst.

  (*
  TODO: revisit this comment
  Ideally we would like to have this version:
  Lemma own_val_to_own_place v l ty β T:
    val_to_loc v = Some l →
    l ◁ₗ{β} ty ∗ T
    ⊢ v ◁ᵥ l @ frac_ptr β ty ∗ T.
  Proof. by iIntros (->%val_of_to_loc) "[$ $]". Qed.
  But the sidecondition is a problem since solving it requires
  calling apply which triggers https://github.com/coq/coq/issues/6583
  and can make the application of this lemma fail if it tries to solve
  a Movable (tc_opaque x) in the context. *)

  Lemma own_val_to_own_place l cty ty β T:
    l ◁ₗ{β} ty ∗ T
      ⊢ l ◁ᵥₐₗ|tptr cty| l @ frac_ptr β ty ∗ T.
  Proof. by iIntros "[$ $]". Qed.

  Lemma own_val_to_own_place_singleton (l : address) cty β T:
    T ⊢ l ◁ᵥₐₗ|tptr cty| l @ frac_ptr β (place l) ∗ T.
  Proof. by iDestruct 1 as "$". Qed.

(*   Lemma type_offset_of_sub v1 l s m P ly t T:
    ⌜ly_size ly = 1%nat⌝ ∗ (
      (P -∗ loc_in_bounds l 0 ∗ True) ∧ (P -∗ T (val_of_loc l) (l @ frac_ptr Own (place l))))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ offsetof s m) (l at{s}ₗ m) P (PtrNegOffsetOp ly) size_t (tptr t) T.
  Proof.
    iDestruct 1 as (Hly) "HT". unfold offsetof, int, int_inner_type; simpl_type.
    iIntros ([n [Ho Hi]]) "HP". iIntros (Φ) "HΦ".
    iAssert (loc_in_bounds l 0) as "#Hlib".
    { iDestruct "HT" as "[HT _]". by iDestruct ("HT" with "HP") as "[$ _]". }
    iDestruct "HT" as "[_ HT]".
    iApply wp_ptr_neg_offset; [by apply val_to_of_loc|done|..].
    all: rewrite offset_loc_sz1 // /GetMemberLoc shift_loc_assoc Ho /= Z.add_opp_diag_r shift_loc_0.
    1: done.
    iModIntro. iApply "HΦ"; [ | by iApply "HT"]. done.
  Qed.
  Definition type_offset_of_sub_inst := [instance type_offset_of_sub].
  Global Existing Instance type_offset_of_sub_inst. *)

  Lemma type_cast_ptr_ptr f e ot β T:
    is_tptr (typeof e) = true →
    typed_val_expr ge f e (λ v ty, ⎡v ◁ᵥₐₗ|typeof e| ty⎤ -∗ match v with Vptr b o =>
      ⎡(b, o) ◁ₗ{β} ty⎤ ∗ T v ((b, o) @ frac_ptr β ty) | _ => False end)
    ⊢ typed_val_expr ge f (Ecast e (tptr ot)) T.
  Proof.
    intros; iIntros "He %Φ HΦ".
    iApply wp_cast0.
    iApply "He".
    iIntros (v ty) "own_v HT".
    iSpecialize ("HT" with "own_v").
    iExists v; destruct v; try done.
    iSplit.
    { iPureIntro; intros; destruct (typeof e); done. }
    iDestruct "HT" as "(Hp & HT)".
    iApply ("HΦ" with "[Hp] HT"). by iFrame.
  Qed.

  Lemma type_if_ptr_own (l : address) β ty t T1 T2:
    (l ◁ₗ{β} ty -∗ (*(loc_in_bounds l 0 ∗ True) ∧*) valid_val l ∧ T1)
    ⊢ typed_if (tptr t) l (l ◁ₗ{β} ty) (valid_val l) T1 T2.
  Proof.
    iIntros "HT1 Hl".
    iDestruct ("HT1" with "Hl") as "HT".
    iStopProof; f_equiv; iIntros "HT".
    rewrite /adr2val /bool_val /= andb_false_r /=; eauto.
  Qed.
  Definition type_if_ptr_own_inst := [instance type_if_ptr_own].
  Global Existing Instance type_if_ptr_own_inst.

  Lemma type_assert_ptr_own Espec l β ty t s f R:
    (⎡l ◁ₗ{β} ty⎤ -∗ (*(loc_in_bounds l 0 ∗ True) ∧*) typed_stmt Espec ge s f R)
    ⊢ typed_assert Espec ge (tptr t) l ⎡l ◁ₗ{β} ty⎤ s f R.
  Proof.
    iIntros "HT1 Hl".
    iDestruct ("HT1" with "Hl") as "$".
    rewrite /bool_val /= andb_false_r //.
  Qed.
  Definition type_assert_ptr_own_inst := [instance type_assert_ptr_own].
  (*Global Existing Instance type_assert_ptr_own_inst. not sure why this doesn't work *)
  Global Instance type_assert_ptr_own_inst' Espec (l: address) β ty t : TypedAssert Espec ge (tptr t) l ⎡l ◁ₗ{β} ty⎤ := type_assert_ptr_own_inst Espec l β ty t.

(*  Lemma type_cast_int_ptr n v it T:
    (⌜n ∈ it⌝ -∗ ∀ oid, T (val_of_loc (oid, n)) ((oid, n) @ frac_ptr Own (place (oid, n))))
    ⊢ typed_un_op v (v ◁ᵥ n @ int it) (CastOp PtrOp) (IntOp it) T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT" (Hn Φ) "HΦ".
    iDestruct ("HT" with "[%]") as "HT".
    { by apply: val_to_Z_in_range. }
    iApply wp_cast_int_ptr_weak => //.
    iIntros (i') "!>". by iApply ("HΦ" with "[] HT").
  Qed.
  Definition type_cast_int_ptr_inst := [instance type_cast_int_ptr].
  Global Existing Instance type_cast_int_ptr_inst | 50. *)

(*  Lemma type_copy_aid v a it l β ty T:
    (l ◁ₗ{β} ty -∗
      (loc_in_bounds (l.1, a) 0 ∗ True) ∧
      (alloc_alive_loc l ∗ True) ∧
      T (val_of_loc (l.1, a)) ((l.1, a) @ frac_ptr Own (place (l.1, a))))
    ⊢ typed_copy_alloc_id v (v ◁ᵥ a @ int it) l (l ◁ₗ{β} ty) (IntOp it) T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT %Hv Hl" (Φ) "HΦ". iDestruct ("HT" with "Hl") as "HT".
    rewrite !right_id. iDestruct "HT" as "[#Hlib HT]".
    iApply wp_copy_alloc_id; [ done | by rewrite val_to_of_loc | done | ].
    iSplit; [by iDestruct "HT" as "[$ _]" |].
    iDestruct "HT" as "[_ HT]".
    by iApply ("HΦ" with "[] HT").
  Qed.
  Definition type_copy_aid_inst := [instance type_copy_aid].
  Global Existing Instance type_copy_aid_inst. *)

  Open Scope Z.

  (* TODO: Is it a good idea to have this general rule or would it be
  better to have more specialized rules? *)

  Lemma type_relop_ptr_ptr (l1 l2 : address) op b β1 β2 ty1 ty2 t1 t2
    (Hop : match op with
           | Olt => Some (bool_decide (Ptrofs.unsigned l1.2 < Ptrofs.unsigned l2.2))
           | Ogt => Some (bool_decide (Ptrofs.unsigned l1.2 > Ptrofs.unsigned l2.2))
           | Ole => Some (bool_decide (Ptrofs.unsigned l1.2 <= Ptrofs.unsigned l2.2))
           | Oge => Some (bool_decide (Ptrofs.unsigned l1.2 >= Ptrofs.unsigned l2.2))
           | _ => None
           end = Some b) T:
    (⎡l1 ◁ₗ{β1} ty1⎤ -∗ ⎡l2 ◁ₗ{β2} ty2⎤ -∗ <affine> ⌜l1.1 = l2.1⌝ ∗ (
      ⎡expr.weak_valid_pointer l1⎤ ∧ ⎡expr.weak_valid_pointer l2⎤ ∧
      T (i2v (bool_to_Z b) tint) (b @ boolean tint)))
      ⊢ typed_bin_op ge l1 ⎡l1 ◁ₗ{β1} ty1⎤ l2 ⎡l2 ◁ₗ{β2} ty2⎤ op (tptr t1) (tptr t2) (tint) T.
  Proof.
    iIntros "HT Hl1 Hl2". iIntros (Φ) "HΦ".
    iDestruct ("HT" with "Hl1 Hl2") as (Heq) "HT".
    iIntros "!>" (?) "Hm !>".
    iDestruct (valid_pointer.weak_valid_pointer_dry with "[$Hm HT]") as %H1.
    { iDestruct "HT" as "($ & _)". }
    iDestruct (valid_pointer.weak_valid_pointer_dry with "[$Hm HT]") as %H2.
    { iDestruct "HT" as "(_ & $ & _)". }
    iFrame; iExists (i2v (bool_to_Z b) tint); iSplit.
    - iStopProof; split => rho; monPred.unseal.
      apply bi.pure_intro.
      assert (classify_cmp (tptr t1) (tptr t2) = cmp_case_pp) as Hclass by done.
      rewrite -val_of_bool_eq.
      destruct op => //; simplify_eq; simpl; rewrite /Cop.sem_cmp Hclass /cmp_ptr /= if_true // H1 H2 /=.
      + rewrite /Ptrofs.ltu //.
      + rewrite /Ptrofs.ltu //.
        case_bool_decide; destruct (zlt _ _); (done || lia).
      + rewrite /Ptrofs.ltu //.
        case_bool_decide; destruct (zlt _ _); (done || lia).
      + rewrite /Ptrofs.ltu //.
        case_bool_decide; destruct (zlt _ _); (done || lia).
    - iDestruct "HT" as "(_ & _ & HT)".
      iApply ("HΦ" with "[] HT") => //.
      rewrite /ty_own_val_at /ty_own_val /=.
      destruct b; iSplit; eauto; iExists _; try done.
  Qed.

  Definition type_lt_ptr_ptr_inst l1 l2 :=
    [instance type_relop_ptr_ptr l1 l2 Olt (bool_decide (Ptrofs.unsigned l1.2 < Ptrofs.unsigned l2.2))].
  Global Existing Instance type_lt_ptr_ptr_inst.
  Definition type_gt_ptr_ptr_inst l1 l2 :=
    [instance type_relop_ptr_ptr l1 l2 Ogt (bool_decide (Ptrofs.unsigned l1.2 > Ptrofs.unsigned l2.2))].
  Global Existing Instance type_gt_ptr_ptr_inst.
  Definition type_le_ptr_ptr_inst l1 l2 :=
    [instance type_relop_ptr_ptr l1 l2 Ole (bool_decide (Ptrofs.unsigned l1.2 <= Ptrofs.unsigned l2.2))].
  Global Existing Instance type_le_ptr_ptr_inst.
  Definition type_ge_ptr_ptr_inst l1 l2 :=
    [instance type_relop_ptr_ptr l1 l2 Oge (bool_decide (Ptrofs.unsigned l1.2 >= Ptrofs.unsigned l2.2))].
  Global Existing Instance type_ge_ptr_ptr_inst.

  (* Lemma type_roundup_frac_ptr v2 β ty P2 T p: *)
  (*   (P2 -∗ T (val_of_loc p) (t2mt (p @ frac_ptr β ty))) ⊢ *)
  (*     typed_bin_op p (p ◁ₗ{β} ty) v2 P2 RoundUpOp T. *)
  (* Proof. *)
  (*   iIntros "HT Hv1 Hv2". iIntros (Φ) "HΦ". *)
  (*   iApply wp_binop_det. by move => h /=; rewrite val_to_of_loc. *)
  (*   iApply ("HΦ" with "[Hv1]"); last by iApply "HT". *)
  (*   by iFrame. *)
  (* Qed. *)
  (* Global Instance type_roundup_frac_ptr_inst v2 β ty P2 T (p : address) : *)
  (*   TypedBinOp p (p ◁ₗ{β} ty) v2 P2 RoundUpOp T := *)
  (*   i2p (type_roundup_frac_ptr v2 β ty P2 T p). *)

  (* Lemma type_rounddown_frac_ptr v2 β ty P2 T p: *)
  (*   (P2 -∗ T (val_of_loc p) (t2mt (p @ frac_ptr β ty))) ⊢ *)
  (*     typed_bin_op p (p ◁ₗ{β} ty) v2 P2 RoundDownOp T. *)
  (* Proof. *)
  (*   iIntros "HT Hv1 Hv2". iIntros (Φ) "HΦ". *)
  (*   iApply wp_binop_det. by move => h /=; rewrite val_to_of_loc. *)
  (*   iApply ("HΦ" with "[Hv1]"); last by iApply "HT". *)
  (*   by iFrame. *)
  (* Qed. *)
  (* Global Instance type_rounddown_frac_ptr_inst v2 β ty P2 T (p : address) : *)
  (*   TypedBinOp p (p ◁ₗ{β} ty) v2 P2 RoundDownOp T := *)
  (*   i2p (type_rounddown_frac_ptr v2 β ty P2 T p). *)

(*  
  Global Program Instance shr_copyable p ty : Copyable (p @ frac_ptr Shr ty).
  Next Obligation.
    intros. rewrite /Affine /ty_own_val /=.
  Admitted.
  Next Obligation.
    iIntros (p ty E ot l) "Htm".
    iMod (heap_mapsto_own_state_to_mt with "Htm") as (q) "(? ?)".
    unfold has_layout_loc.
    rewrite field_compatible_tptr; erewrite mapsto_tptr; iSplitR => //.
    iExists _, _. iFrame. iModIntro. iSplit => //.
    - iIntros "!>"; by iSplit.
    - by iIntros "_".
  Qed.
*)
  Lemma find_in_context_type_loc_own l T:
    (∃ l1 β1 β ty, ⎡l1 ◁ₗ{β1} (l @ frac_ptr β ty)⎤ ∗ (⎡l1 ◁ₗ{β1} (l @ frac_ptr β (place l))⎤ -∗
      T (own_state_min β1 β, ty)))
    ⊢ find_in_context (FindLoc l) T.
  Proof.
    iDestruct 1 as (l1 β1 β ty) "[[% [Hmt Hl]] HT]".
    iExists (_, _) => /=. iFrame. iApply "HT".
    iSplit => //. by iFrame.
  Qed.
  Definition find_in_context_type_loc_own_inst :=
    [instance find_in_context_type_loc_own with FICSyntactic].
  Global Existing Instance find_in_context_type_loc_own_inst | 10.

  (* Should check it again *)
  Lemma find_in_context_type_val_own cty (l : address) T:
    (∃ ty : type, ⎡(adr2val l) ◁ᵥₐₗ| (tptr cty) | (l @ frac_ptr Own ty) ⎤ ∗ T (l @ frac_ptr Own ty))
    ⊢ find_in_context (FindVal (tptr cty) l) T.
  Proof. iDestruct 1 as (ty) "[Hl HT]". iExists _ => /=. iFrame. Qed.
  Definition find_in_context_type_val_own_inst :=
    [instance find_in_context_type_val_own with FICSyntactic].
  Global Existing Instance find_in_context_type_val_own_inst | 10.

  Lemma find_in_context_type_val_own_singleton cty (l : address) T:
    (emp ∗ T (l @ frac_ptr Own (place l)))
      ⊢ find_in_context (FindVal (tptr cty) l) T.
  Proof. iIntros "[_ HT]". iExists _ => /=. iFrame "HT".
         rewrite / ty_own_val_at /ty_own_val /=. done.
  Qed.
  Definition find_in_context_type_val_own_singleton_inst :=
    [instance find_in_context_type_val_own_singleton with FICSyntactic].
  Global Existing Instance find_in_context_type_val_own_singleton_inst | 20.

  (* We cannot use place here as it can easily lead to an infinite
  loop during type checking. Thus, we define place' that is not
  unfolded as eagerly as place. You probably should not add typing
  rules for place', but for place instead. *)
  Definition place' (l : address) : type := place l.
  Lemma find_in_context_type_val_P_own_singleton (l : address) (T:assert->assert):
    (emp ∗ T (⎡l ◁ₗ place' l⎤))
    ⊢ find_in_context (FindValP l) T.
  Proof. rewrite /place'. iIntros "[_ HT]". iExists _. iFrame "HT" => //=. Qed.
  Definition find_in_context_type_val_P_own_singleton_inst :=
    [instance find_in_context_type_val_P_own_singleton with FICSyntactic].
  Global Existing Instance find_in_context_type_val_P_own_singleton_inst | 30.
End own.

Global Typeclasses Opaque place'.
Notation "place'< l >" := (place' l) (only printing, format "'place'<' l '>'") : printing_sugar.

Notation "&frac{ β }" := (frac_ptr β) (format "&frac{ β }") : bi_scope.
Notation "&own" := (frac_ptr Own) (format "&own") : bi_scope.
Notation "&shr" := (frac_ptr Shr) (format "&shr") : bi_scope.

Notation "&frac< β , ty >" := (frac_ptr β ty) (only printing, format "'&frac<' β ,  ty '>'") : printing_sugar.
Notation "&own< ty >" := (frac_ptr Own ty) (only printing, format "'&own<' ty '>'") : printing_sugar.
Notation "&shr< ty >" := (frac_ptr Shr ty) (only printing, format "'&shr<' ty '>'") : printing_sugar.

Section ptr.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (* at present n doesn't do anything *)
  Program Definition ptr_type (n : nat) (l' : address) : type := {|
    ty_has_op_type ot mt := (match ot with | Tpointer t attr => ot = tptr t | _ => False end)%type;
    ty_own β l := (<affine> ⌜l `has_layout_loc` (tptr tvoid)⌝ ∗ (*valid_pointer l' (*n*) ∧*) l ↦[β]|tptr tvoid| l')%I;
    ty_own_val cty v := (<affine> ⌜repinject cty v = adr2val l'⌝ (*∗ loc_in_bounds l' n*))%I;
  |}.
  Next Obligation.
    iIntros (?????).
    iDestruct 1 as "[$ Hl]".
    iMod (heap_mapsto_own_state_share with "Hl") as "$"; done.
  Qed.
  Next Obligation.
    iIntros (??????) "(% & Hl)".
    rewrite /has_layout_loc in H |- *.
    destruct cty; try done.
    by rewrite field_compatible_tptr.
  Qed.
  Next Obligation.
    iIntros (???????).
    rewrite /repinject /= in H; subst.
    iPureIntro.
    rewrite /has_layout_val.
    destruct cty; try done. inv H.
    split; try done.
    rewrite /value_fits /=.
    rewrite /tc_val' /=.
    intros. 
    destruct v_rep; try done.
    simple_if_tac; try done.
  Qed.
  Next Obligation.
    iIntros (??????) "(% & Hl)".
    rewrite / heap_mapsto_own_state.
    destruct cty; try done; inv H.
    erewrite (mapsto_tptr _ _ tvoid cty).
    iExists _. iFrame.
    by iPureIntro.
  Qed.
  Next Obligation.
    iIntros (????????) "Hl".
    iIntros "%".
    unfold has_layout_loc in *.
    destruct cty; try done; inv H.
    rewrite /= in H1. rewrite H1.
    unfold has_layout_loc in *. rewrite field_compatible_tptr in H0. unfold heap_mapsto_own_state.
    erewrite (mapsto_tptr _ _ tvoid cty). by iFrame.
  Qed.

  Definition ptr (n : nat) : rtype _ := RType (ptr_type n).

(*   Instance ptr_loc_in_bounds l n β : LocInBounds (l @ ptr n) β bytes_per_addr.
  Proof.
    constructor. iIntros (?) "[_ [_ Hl]]".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    iApply loc_in_bounds_shorten; last done. by rewrite /val_of_loc.
  Qed. *)

   Lemma simplify_ptr_hyp_place (p:address) l t n T:
    ((*loc_in_bounds p n -∗*) l ◁ₗ value (tptr t) (adr2val p) -∗ T)
    ⊢ simplify_hyp (l ◁ₗ p @ ptr n) T.
  Proof.
    iIntros "HT [% Hl]". iApply "HT". unfold value; simpl_type.
    rewrite /heap_mapsto_own_state.
    erewrite (mapsto_tptr _ _ tvoid t).
    repeat iSplit => //.
    { rewrite /has_layout_loc in H |- *. by rewrite field_compatible_tptr. }
    { rewrite /has_layout_loc in H |- *. iPureIntro.
      split; auto.
      rewrite /value_fits /tc_val' /=.
      destruct t; try done.
    }
  Qed.
  Definition simplify_ptr_hyp_place_inst := [instance simplify_ptr_hyp_place with 0%N].
  Global Existing Instance simplify_ptr_hyp_place_inst.

  Lemma simplify_ptr_goal_val cty (p:address) l n T:
    <affine> ⌜l = p⌝ ∗ (*loc_in_bounds l n ∗*) T  ⊢ simplify_goal (p ◁ᵥₐₗ|tptr cty| l @ ptr n) T.
  Proof. by iIntros "[-> $]". Qed.
  Definition simplify_ptr_goal_val_inst := [instance simplify_ptr_goal_val with 10%N].
  Global Existing Instance simplify_ptr_goal_val_inst.

  Lemma subsume_own_ptr A p l1 l2 ty n T:
    (l1 ◁ₗ ty -∗ ∃ x, <affine> ⌜l1 = l2 x⌝ ∗ (*loc_in_bounds l1 (n x) ∗*) T x)
    ⊢ subsume (p ◁ₗ l1 @ &own ty)%I (λ x : A, p ◁ₗ (l2 x) @ ptr (n x))%I T.
  Proof.
    iIntros "HT Hp".
    iDestruct (ty_aligned _ (tptr tvoid) MCNone with "Hp") as %?; [eexists; eauto|].
    iDestruct (ty_deref _ (tptr tvoid) MCNone with "Hp") as (v) "(Hp & Hl)"; try done.
    rewrite /ty_own_val /=.
    iDestruct "Hl" as "(% & Hl)".
    rewrite H0.
    iDestruct ("HT" with "[$Hl]") as (? ->) "?".
    iExists _. by iFrame "∗".
  Qed.
  Definition subsume_own_ptr_inst := [instance subsume_own_ptr].
  Global Existing Instance subsume_own_ptr_inst.

End ptr.

(*   Lemma type_copy_aid_ptr v1 a it v2 l n T:
    (v1 ◁ᵥ a @ int it -∗
      v2 ◁ᵥ l @ ptr n -∗
      ⌜l.2 ≤ a ≤ l.2 + n⌝ ∗
      (alloc_alive_loc l ∗ True) ∧
      T (val_of_loc (l.1, a)) (value PtrOp (val_of_loc (l.1, a))))
    ⊢ typed_copy_alloc_id v1 (v1 ◁ᵥ a @ int it) v2 (v2 ◁ᵥ l @ ptr n) (IntOp it) T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT %Hv1 Hv2" (Φ) "HΦ". iDestruct "Hv2" as "[-> #Hlib]".
    iDestruct ("HT" with "[//] [$Hlib]") as ([??]) "HT"; [done|].
    rewrite !right_id.
    iApply wp_copy_alloc_id; [ done | by rewrite val_to_of_loc |  | ].
    { iApply (loc_in_bounds_offset with "Hlib"); simpl; [done | done | etrans; [|done]; lia ]. }
    iSplit; [by iDestruct "HT" as "[$ _]" |].
    iDestruct "HT" as "[_ HT]". iApply ("HΦ" with "[] HT"). unfold value; simpl_type.
    iSplit => //. iPureIntro. apply: mem_cast_id_loc.
  Qed.
  Definition type_copy_aid_ptr_inst := [instance type_copy_aid_ptr].
  Global Existing Instance type_copy_aid_ptr_inst. *)

Section null.
  Context `{!typeG OK_ty Σ} {cs : compspecs} (ge : genv).

  Program Definition null : type := {|
    ty_has_op_type ot mt := (match ot with | Tpointer t attr => ot = tptr t | _ => False end)%type;
    ty_own β l := (<affine> ⌜l `has_layout_loc` (tptr tvoid)⌝ ∗ l ↦[β]|tptr tvoid| nullval)%I;
    ty_own_val cty v := <affine> ⌜repinject cty v = nullval⌝%I;
  |}.
  Next Obligation.
    iIntros (???). iDestruct 1 as "[$ Hl]".
    by iApply (heap_mapsto_own_state_share with "[Hl]").
  Qed.
  Next Obligation.
    iIntros (????) "[% _]".
    destruct cty; try done; inv H.
    rewrite /has_layout_loc field_compatible_tptr //.
  Qed.
  Next Obligation.
    iIntros (?????).
    rewrite /repinject /= in H; subst.
    destruct cty; try done; inv H.
    simpl in H0. rewrite H0.
    iPureIntro. 
    hnf.
    split; auto.
    intros ?; apply Clight_mapsto_memory_block.tc_val_pointer_nullval.
  Qed.
  Next Obligation.
    iIntros (????) "(% & Hl)".
    destruct cty; try done; inv H.
    rewrite /heap_mapsto_own_state.
    erewrite (mapsto_tptr _ _ tvoid cty).
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (?????) "% Hl %Hl1".
    destruct cty; try done; inv H.
    rewrite /repinject /= in Hl1; subst.
    rewrite /heap_mapsto_own_state.
    erewrite (mapsto_tptr _ _ tvoid cty).
    iFrame.
    iPureIntro.
    by rewrite /has_layout_loc field_compatible_tptr in H0.
  Qed.

(*  Global Instance null_loc_in_bounds β : LocInBounds null β (Z.to_nat (expr.sizeof (tptr tvoid))).
  Proof.
    constructor. iIntros (l) "[_ Hl]".
    simpl.
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    by iApply loc_in_bounds_shorten.
  Qed. *)

  Lemma type_null cty T :
    T null
    ⊢ typed_value (tptr cty) nullval T.
  Proof. iIntros "HT". iExists _. iFrame. done. Qed.
  Definition type_null_inst := [instance type_null].
  Global Existing Instance type_null_inst.

  Global Program Instance null_copyable cty : Copyable (tptr cty) (null).
  Next Obligation.
    iIntros (? E l ?) "(% & Hl)".
    rewrite /has_layout_loc field_compatible_tptr; iSplitR => //.
    iInv "Hl" as ">(% & % & Hl)" "Hclose".
    exploit slice.split_readable_share; first done; intros (s & ? & ? & ? & ?).
    rewrite (mapsto_tptr _ _ _ cty) /mapsto.
    rewrite -{1}data_at_rec_share_join; last done.
    iDestruct "Hl" as "($ & H2)".
    iMod ("Hclose" with "[H2]").
    { rewrite /data_at_rec /=; erewrite mem_block_mapsto_tptr; by iFrame. }
    iModIntro. do 2 iSplit => //.
    iIntros "H"; iSplitR => //.
    iApply (heap_mapsto_own_state_from_mt _ _ _ _ _ s with "[H]"); [done..|].
    rewrite (mapsto_tptr _ _ _ cty) //.
  Qed.
  
  Global Program Instance null_defined cty : DefinedTy (tptr cty) (null).
  Next Obligation. by intros; iIntros (? ->). Qed.
  
  Definition heap_loc_eq l1 l2 m :=
    if Archi.ptr64 then Val.cmplu_bool (Mem.valid_pointer m) Ceq l1 l2
    else Val.cmpu_bool (Mem.valid_pointer m) Ceq l1 l2.

  Lemma eval_bin_op_ptr_cmp ce l1 l2 t1 t2 op h v b:
    match op with | Cop.Oeq | Cop.One => True | _ =>  False end →
    heap_loc_eq l1 l2 h = Some b →
    sem_binary_operation ce op l1 (tptr t1) l2 (tptr t2) h = Some v
     ↔ Val.of_bool (if op is Cop.Oeq then b else negb b) = v.
  Proof.
    rewrite /heap_loc_eq /=. move => ? Heq.
    rewrite /sem_binary_operation; destruct op => //; rewrite /Cop.sem_cmp /= /cmp_ptr /=.
    - rewrite Heq /=; split; congruence.
    - rewrite /Val.cmpu_bool /Val.cmplu_bool in Heq |- *;
        destruct l1 => //; destruct l2 => //; simpl in *; simple_if_tac; simpl;
        first [inv Heq; split; congruence | try if_tac in Heq; destruct (_ && _); inv Heq; simpl; split; congruence].
  Qed.

  Lemma type_binop_null_null cty v1 v2 t1 t2 op T:
    (<affine> ⌜match op with | Cop.Oeq | Cop.One => True | _ => False end⌝ ∗ ∀ v,
          T v ((if op is Cop.Oeq then true else false) @ boolean tint))
      ⊢ typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|tptr cty| null⎤ v2 ⎡v2 ◁ᵥₐₗ|tptr cty| null⎤ op (tptr t1) (tptr t2) (tint) T.
  Proof.
    iIntros "(% & HT)" (?) "%"; simpl in *; subst.
    iIntros (Φ) "HΦ".
    iIntros "!>" (?) "$ !>".
    iExists (Val.of_bool (if op is Oeq then true else false)); iSplit.
    - iPureIntro.
      eapply eval_bin_op_ptr_cmp with (b := true); eauto.
    - iApply "HΦ" => //.
      rewrite /ty_own_val_at /ty_own_val /=.
      iSplit; auto.
      iExists _. iSplit; iPureIntro => //.
      { by destruct op. }
      { split; auto; by destruct op. }
  Qed.
  Definition type_binop_null_null_inst := [instance type_binop_null_null].
  Global Existing Instance type_binop_null_null_inst.

  Lemma type_binop_ptr_null cty v op (l : address) t1 t2 ty β n `{!LocInBounds ty β n} T:
    (<affine> ⌜match op with | Cop.Oeq | Cop.One => True | _ => False end⌝ ∗ ∀ v, ⎡l ◁ₗ{β} ty⎤ -∗
          T v ((if op is Oeq then false else true) @ boolean tint))
      ⊢ typed_bin_op ge l ⎡l ◁ₗ{β} ty⎤ v ⎡v ◁ᵥₐₗ|tptr cty| null⎤ op (tptr t1) (tptr t2) tint T.
  Proof.
    iIntros "(% & HT) Hl" (?) "% HΦ"; simpl in *; subst.
    iApply (wp_binop_sc _ _ _ _ _ _ _ (Val.of_bool (if op is Oeq then false else true))).
    { by destruct op. }
    iSplit.
    - iPoseProof (loc_in_bounds_weak_valid_pointer with "Hl") as "Hl".
      destruct op; try done; rewrite /= /sc_cmp /= /sc_cmp_ptr /nullval /=; simple_if_tac; done.
    - iSpecialize ("HT" with "Hl").
      iApply "HΦ" => //.
      destruct op; try done.
      { rewrite /Val.of_bool /Vfalse /= /ty_own_val_at /ty_own_val /=.
        iSplit; auto. iExists _; done.
      }
      { rewrite /Val.of_bool /Vtrue /= /ty_own_val_at /ty_own_val /=.
        iSplit; auto. iExists _; done.
      }
  Qed.
  Definition type_binop_ptr_null_inst := [instance type_binop_ptr_null].
  Global Existing Instance type_binop_ptr_null_inst.

  Lemma type_binop_null_ptr cty v op (l : address) t1 t2 ty β n `{!LocInBounds ty β n}  T:
    (<affine> ⌜match op with | Cop.Oeq | Cop.One => True | _ => False end⌝ ∗ ∀ v, ⎡l ◁ₗ{β} ty⎤ -∗
     T v ((if op is Oeq then false else true) @ boolean tint))
      ⊢ typed_bin_op ge v ⎡v ◁ᵥₐₗ|tptr cty| null⎤ l ⎡(l ◁ₗ{β} ty)⎤ op (tptr t1) (tptr t2) tint T.
  Proof.
    iIntros "(% & HT)" (?) "Hl % HΦ"; simpl in *; subst.
    iApply (wp_binop_sc _ _ _ _ _ _ _ (Val.of_bool (if op is Oeq then false else true))).
    { by destruct op. }
    iSplit.
    - iPoseProof (loc_in_bounds_weak_valid_pointer with "Hl") as "Hl".
      destruct op; try done; rewrite /= /sc_cmp /= /sc_cmp_ptr /nullval /=; simple_if_tac; done.
    - iSpecialize ("HT" with "Hl").
      iApply "HΦ" => //.
      destruct op; try done.
      { rewrite /Val.of_bool /Vfalse /= /ty_own_val_at /ty_own_val /=.
        iSplit; auto. iExists _; done.
      }
      { rewrite /Val.of_bool /Vtrue /= /ty_own_val_at /ty_own_val /=.
        iSplit; auto. iExists _; done.
      }
  Qed.
  Definition type_binop_null_ptr_inst := [instance type_binop_null_ptr].
  Global Existing Instance type_binop_null_ptr_inst.

  (* hardcoding target type for now *)
  Lemma type_cast_null_int f s e T: is_tptr (typeof e) = true →
    typed_val_expr ge f e (λ v ty, ⎡v ◁ᵥₐₗ|typeof e| ty⎤ -∗ ⎡v ◁ᵥₐₗ|typeof e| null⎤ ∗
      T (i2v 0 (Tlong s noattr)) (0 @ int.int (Tlong s noattr)))
    ⊢ typed_val_expr ge f (Ecast e (Tlong s noattr)) T.
  Proof.
    intros; iIntros "He %Φ HΦ".
    iApply wp_cast0.
    iApply "He".
    iIntros (v ty) "own_v HT".
    iDestruct ("HT" with "own_v") as "(own_v & HT)".
    rewrite /null; simpl_type.
    iDestruct "own_v" as %Hv.
    iExists nullval; iSplit.
    { iPureIntro; intros.
      destruct (typeof e); try done; destruct v; try done; simpl in *.
      unfold nullval in Hv.
      change Archi.ptr64 with true in *; inv Hv; done. }
    iApply ("HΦ" with "[] HT").
    rewrite /int.int; simpl_type; iPureIntro.
    split3; auto.
    - split; auto.
      rewrite value_fits_eq //.
    - destruct s; done.
  Qed.

  Lemma type_cast_zero_ptr f e it ot T:
    typed_val_expr ge f e (λ v ty, ⎡v ◁ᵥₐₗ|typeof e| ty⎤ -∗ ⎡v ◁ᵥₐₗ|typeof e| 0 @ int.int it⎤ ∗
      T nullval null)
    ⊢ typed_val_expr ge f (Ecast e (tptr ot)) T.
  Proof.
    intros; iIntros "He %Φ HΦ".
    iApply wp_cast0.
    iApply "He".
    iIntros (v ty) "own_v HT".
    iDestruct ("HT" with "own_v") as "(own_v & HT)".
    rewrite /int.int; simpl_type.
    iDestruct "own_v" as %(<- & ? & Hv).
    iExists nullval; iSplit.
    { iPureIntro; intros.
      destruct (typeof e); try done; destruct v; try done; simpl in *.
      - change Archi.ptr64 with true; simpl.
        destruct s; simpl; injection Hv as ->; done.
      - rewrite /nullval; change Archi.ptr64 with true; simpl.
        do 2 f_equal.
        destruct s; inv Hv; apply (f_equal Int64.repr) in H1; by [rewrite Int64.repr_signed in H1 | rewrite Int64.repr_unsigned in H1]. }
    by iApply ("HΦ" with "[] HT").
  Qed.

  Lemma type_cast_null_ptr f e ot T: is_tptr (typeof e) = true →
    typed_val_expr ge f e (λ v ty, ⎡v ◁ᵥₐₗ|typeof e| ty⎤ -∗ ⎡v ◁ᵥₐₗ|typeof e| null⎤ ∗
      T v null)
    ⊢ typed_val_expr ge f (Ecast e (tptr ot)) T.
  Proof.
    intros; iIntros "He %Φ HΦ".
    iApply wp_cast0.
    iApply "He".
    iIntros (v ty) "own_v HT".
    iDestruct ("HT" with "own_v") as "(own_v & HT)".
    rewrite {1}/null; simpl_type.
    iDestruct "own_v" as %Hv.
    destruct (typeof e); try done.
    iExists v; iSplit.
    { iPureIntro; intros.
      destruct v; done. }
    iApply ("HΦ" with "[] HT").
    rewrite {1}/null; simpl_type; done.
  Qed.

  Lemma type_if_null cty v t T1 T2:
    valid_val v ∧ T2
    ⊢ typed_if (tptr t) v (v ◁ᵥₐₗ|tptr cty| null) (valid_val v) T1 T2.
  Proof.
    iIntros "Hv HT2".
    iSplit.
    { rewrite bi.and_elim_l; auto. }
    { iExists false; iFrame.
      rewrite /bool_val /= andb_false_r //.
      rewrite / ty_own_val_at /ty_own_val /=.
      iDestruct "HT2" as "%Hv"; subst.
      iSplit; last first; try done.
      by rewrite bi.and_elim_r.
    }
  Qed.
  Definition type_if_null_inst := [instance type_if_null].
  Global Existing Instance type_if_null_inst.
End null.

(* up *)
Lemma repinject_by_value : forall {cs : compspecs} t v,
  repinject t v ≠ Vundef → type_is_by_value t = true.
Proof. by destruct t. Qed.

Section optionable.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  Global Program Instance frac_ptr_optional p cty ty β t1 t2:
    Optionable cty (p @ frac_ptr β ty) null (tptr t1) (tptr t2) := {|
    opt_pre v1 v2 := (p ◁ₗ{β} ty -∗ expr.valid_pointer p)%I
  |}.
  Next Obligation.
    intros.
    iIntros "Hpre H1 %H2 Hctx".
    exploit repinject_by_value; first (by setoid_rewrite H2); intros Hcty.
    rewrite repinject_valinject // in H2; subst.
    destruct bty.
    - iDestruct "H1" as "(% & Hty)".
      rewrite repinject_valinject // in H; subst.
      iDestruct ("Hpre" with "Hty") as "Hlib".
      iDestruct (valid_pointer.valid_pointer_dry0 with "[$Hctx $Hlib]") as %Hvalid; iPureIntro.
      destruct beq => /=; rewrite /Cop.sem_cmp /= /cmp_ptr /nullval /=; change Archi.ptr64 with true; rewrite /= Hvalid /= /Vtrue /Vfalse /Int.zero /Int.one; split; congruence.
    - iDestruct "H1" as %H1.
      rewrite repinject_valinject // in H1; subst.
      rewrite eval_bin_op_ptr_cmp // /= ?Int.eq_true ?Int64.eq_true; destruct beq => //.
  Qed.
  
  Global Program Instance frac_ptr_optional_agree ty1 ty2 β : OptionableAgree (frac_ptr β ty1) (frac_ptr β ty2).
  Next Obligation.
    done.
  Qed.
  
  (* Global Program Instance ptr_optional : ROptionable ptr null PtrOp PtrOp := {| *)
  (*   ropt_opt x := {| opt_alt_sz := _ |} *)
  (* |}. *)
  (* Next Obligation. move => ?. done. Qed. *)
  (* Next Obligation. *)
  (*   iIntros (p bty beq v1 v2 σ v) "H1 -> Hctx". *)
  (*   destruct bty; [ iDestruct "H1" as %-> | iDestruct "H1" as %-> ]; iPureIntro. *)
  (*   - admit. (*by etrans; first apply (eval_bin_op_ptr_null (negb beq)); destruct beq => //.*) *)
  (*   - by etrans; first apply (eval_bin_op_null_null beq); destruct beq => //. *)
  (* Admitted. *)

  Lemma subsume_optional_place_val_null A cty ty l β b ty' T:
    (l ◁ₗ{β} ty' -∗ ∃ x, <affine> ⌜b x⌝ ∗ l ◁ᵥₐₗ|cty| (ty x) ∗ T x)
      ⊢ subsume (l ◁ₗ{β} ty') (λ x : A, l ◁ᵥₐₗ|cty| (b x) @ optional (ty x) null) T.
  Proof.
    iIntros "Hsub Hl". iDestruct ("Hsub" with "Hl") as (??) "[Hl ?]".
    iExists _. iFrame. unfold optional; simpl_type. iLeft. by iFrame.
  Qed.
  Definition subsume_optional_place_val_null_inst := [instance subsume_optional_place_val_null].
  Global Existing Instance subsume_optional_place_val_null_inst | 20.

  Lemma subsume_optionalO_place_val_null B A (ty : B → A → type) l β b cty ty' T:
    (l ◁ₗ{β} ty' -∗ ∃ y x, <affine> ⌜b y = Some x⌝ ∗ l ◁ᵥₐₗ|cty| ty y x ∗ T y)
      ⊢ subsume (l ◁ₗ{β} ty') (λ y, l ◁ᵥₐₗ|cty| (b y) @ optionalO cty (ty y) null) T.
  Proof.
    iIntros "Hsub Hl". iDestruct ("Hsub" with "Hl") as (?? Heq) "[? ?]".
    iExists _. iFrame. rewrite Heq. unfold optionalO; simpl_type. done.
  Qed.
  Definition subsume_optionalO_place_val_null_inst := [instance subsume_optionalO_place_val_null].
  Global Existing Instance subsume_optionalO_place_val_null_inst | 20.

  (* TODO: generalize this with a IsLoc typeclass or similar *)
  Lemma type_cast_optional_own_ptr ge f e ot b β T: is_tptr (typeof e) = true →
      typed_val_expr ge f e (λ v ty, ⎡v ◁ᵥₐₗ|typeof e| ty⎤ -∗ ⎡v ◁ᵥₐₗ|typeof e| b @ optional (&frac{β} ty) null⎤ ∗
      T v (b @ optional (&frac{β} ty) null))
    ⊢ typed_val_expr ge f (Ecast e (tptr ot)) T.
  Proof.
    intros; iIntros "He %Φ HΦ".
    iApply wp_cast0.
    iApply "He".
    iIntros (v ty) "own_v HT".
    iDestruct ("HT" with "own_v") as "(own_v & HT)".
    unfold optional at 1; simpl_type.
    destruct (typeof e); try done.
    iDestruct "own_v" as "[[% Hl]|[% %Hnull]]"; subst; iExists v.
    - rewrite {1}/frac_ptr {1}/ty_of_rty /frac_ptr_type; simpl_type.
      rewrite {1}/with_refinement /ty_own_val /=.
      iDestruct "Hl" as "(% & % & Hl)".
      iSplit.
      { iPureIntro; by destruct v. }
      iApply ("HΦ" with "[Hl] HT").
      rewrite /optional; simpl_type.
      iLeft. iSplit => //. iExists _. by iFrame.
    - iSplit.
      { iPureIntro; by destruct v. }
      iApply ("HΦ" with "[] HT").
      rewrite /optional; simpl_type. by iRight.
  Qed.

  Lemma type_cast_optionalO_own_ptr ge f A (b : option A) e ot β ty T: is_tptr (typeof e) = true →
      typed_val_expr ge f e (λ v ty0, ⎡v ◁ᵥₐₗ|typeof e| ty0⎤ -∗ ⎡v ◁ᵥₐₗ|typeof e| b @ optionalO (typeof e) (λ x, &frac{β} (ty x)) null⎤ ∗
      T v (b @ optionalO (tptr ot) (λ x, &frac{β} (ty x)) null))
    ⊢ typed_val_expr ge f (Ecast e (tptr ot)) T.
  Proof.
    intros; iIntros "He %Φ HΦ".
    iApply wp_cast0.
    iApply "He".
    iIntros (v ty0) "own_v HT".
    iDestruct ("HT" with "own_v") as "(own_v & HT)".
    unfold optionalO; simpl_type.
    destruct (typeof e); try done.
    iExists v; destruct b.
    - rewrite {1}/frac_ptr {1}/ty_of_rty /frac_ptr_type; simpl_type.
      rewrite /with_refinement /ty_own_val /=.
      iDestruct "own_v" as "(% & % & Hl)".
      iSplit.
      { iPureIntro; by destruct v. }
      iApply ("HΦ" with "[Hl] HT").
      rewrite /optionalO_type; simpl_type. iExists _. by iFrame.
    - iDestruct "own_v" as %Hv.
      iSplit.
      { iPureIntro; by destruct v. }
      iApply ("HΦ" with "[] HT").
      rewrite /optionalO_type; simpl_type. done.
  Qed.
End optionable.

Global Typeclasses Opaque ptr_type ptr.
Global Typeclasses Opaque frac_ptr.
Global Typeclasses Opaque null.

Section optional_null.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.
  Local Typeclasses Transparent optional_type optional.
  
  Lemma type_place_optional_null ge K l β1 b ty T:
    <affine> ⌜b⌝ ∗ typed_place ge K l β1 ty T
    ⊢ typed_place ge K l β1 (b @ optional ty null) T.
  Proof.
    iIntros "[% H]" (Φ) "[[_ Hl]|[% ?]] HH"; last done.
    by iApply ("H" with "Hl").
  Qed.
  (* This should have a lower priority than type_place_id *)
  Definition type_place_optional_null_inst := [instance type_place_optional_null].
  Global Existing Instance type_place_optional_null_inst | 100.

  Lemma type_place_optionalO_null ge A K l β1 b ot (ty : A → _) T:
    <affine> ⌜is_Some b⌝ ∗ (∀ x, <affine> ⌜b = Some x⌝ -∗ typed_place ge K l β1 (ty x) T)
    ⊢ typed_place ge K l β1 (b @ optionalO ot ty null) T.
  Proof.
    iDestruct 1 as ([? ->]) "Hwp".
    iIntros (Φ) "Hx". by iApply "Hwp".
  Qed.
  (* This should have a lower priority than type_place_id *)
  Definition type_place_optionalO_null_inst := [instance type_place_optionalO_null].
  Global Existing Instance type_place_optionalO_null_inst | 100.
End optional_null.
