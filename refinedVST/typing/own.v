From VST.typing Require Export type.
From VST.typing Require Import programs optional boolean int singleton.
From VST.typing Require Import type_options.

Section own.
  Context `{!typeG Σ} {cs : compspecs}.

  Local Typeclasses Transparent place.

  (* Separate definition such that we can make it typeclasses opaque later. *)
  Program Definition frac_ptr_type (β : own_state) (ty : type) (l' : address) : type := {|
    ty_has_op_type ot mt := (∃ t, ot = tptr t)%type;
    ty_own β' l := (<affine> ⌜field_compatible (tptr tvoid) [] l⌝ ∗ l ↦_(tptr tvoid)[β'] l' ∗ (l' ◁ₗ{own_state_min β' β} ty))%I;
    ty_own_val v := (<affine> ⌜v = adr2val l'⌝ ∗ l' ◁ₗ{β} ty)%I;
  |}.
  Next Obligation.
    iIntros (β ?????) "($&Hl&H)". rewrite left_id.
    iMod (heap_mapsto_own_state_share with "Hl") as "$".
    destruct β => //=. by iApply ty_share.
  Qed.
  Next Obligation. iIntros (β ty l ot mt l' (? & ->)). unfold has_layout_loc. rewrite !field_compatible_tptr. by iDestruct 1 as (?) "_". Qed.
  Next Obligation. Admitted.
  Next Obligation. iIntros (β ty l ot mt l' (? & ->)) "(%&Hl&Hl')". rewrite left_id. unfold heap_mapsto_own_state. erewrite mapsto_tptr. eauto with iFrame. Qed.
  Next Obligation. iIntros (β ty l ot mt l' v (? & ->) ?) "Hl [-> Hl']". unfold has_layout_loc in *. rewrite field_compatible_tptr in H. unfold heap_mapsto_own_state. erewrite mapsto_tptr. by iFrame. Qed.
(*   Next Obligation.
    iIntros (β ty l v ot mt st ?). apply: mem_cast_compat_loc; [done|].
    iIntros "[-> ?]". iPureIntro. naive_solver.
  Qed. *)
  Global Instance frac_ptr_type_le : Proper ((=) ==> (⊑) ==> (=) ==> (⊑)) frac_ptr_type.
  Proof. solve_type_proper. Qed.
  Global Instance frac_ptr_type_proper : Proper ((=) ==> (≡) ==> (=) ==> (≡)) frac_ptr_type.
  Proof. solve_type_proper. Qed.

  Definition frac_ptr (β : own_state) (ty : type) : rtype _ := RType (frac_ptr_type β ty).

(*   Global Instance frac_ptr_loc_in_bounds l ty β1 β2 : LocInBounds (l @ frac_ptr β1 ty) β2 bytes_per_addr.
  Proof.
    constructor. iIntros (?) "(_&Hl&_)".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    iApply loc_in_bounds_shorten; last done. by rewrite /val_of_loc.
  Qed. *)

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

(*   Lemma type_place_frac p β K β1 ty1 l mc T:
    typed_place K p (own_state_min β1 β) ty1 (λ l2 β2 ty2 typ, T l2 β2 ty2 (λ t, (p @ (frac_ptr β (typ t)))))
    ⊢ typed_place (DerefPCtx Na1Ord PtrOp mc :: K) l β1 (p @ (frac_ptr β ty1)) T.
  Proof.
    iIntros "HP" (Φ) "(%&Hm&Hl) HΦ" => /=.
    iMod (heap_mapsto_own_state_to_mt with "Hm") as (q Hq) "Hm" => //.
    iApply (wp_deref with "Hm") => //; [naive_solver| by apply val_to_of_loc|].
    iIntros "!# %st Hm". iExists p. rewrite mem_cast_id_loc. iSplit; [by destruct mc|].
    iApply ("HP" with "Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]". iFrame. iSplitR => //.
    by iApply heap_mapsto_own_state_from_mt.
  Qed.
  Definition type_place_frac_inst := [instance type_place_frac].
  Global Existing Instance type_place_frac_inst. *)

(*   Lemma type_addr_of e ot (T : val → _):
    typed_addr_of e (λ l β ty, T l (l @ frac_ptr β ty))
    ⊢ typed_val_expr (Eaddrof e ot) T.
  Proof.
    iIntros "Haddr" (Φ) "HΦ". rewrite /AddrOf.
    iApply "Haddr". iIntros (l β ty) "Hl HT".
    iApply ("HΦ" with "[Hl] HT").
    iSplit => //.
  Qed. *)

  Lemma simplify_frac_ptr (v : val) (p : address) ty β T:
    (<affine> ⌜v = p⌝ -∗ p ◁ₗ{β} ty -∗ T)
    ⊢ simplify_hyp (v◁ᵥ p @ frac_ptr β ty) T.
  Proof. iIntros "HT Hl". iDestruct "Hl" as (->) "Hl". by iApply "HT". Qed.
  Definition simplify_frac_ptr_inst := [instance simplify_frac_ptr with 0%N].
  Global Existing Instance simplify_frac_ptr_inst.

  Lemma simplify_goal_frac_ptr_val ty (v : val) β (p : address) T:
    <affine> ⌜v = p⌝ ∗ p ◁ₗ{β} ty ∗ T
    ⊢ simplify_goal (v ◁ᵥ p @ frac_ptr β ty) T.
  Proof. by iIntros "[-> [$ $]]". Qed.
  Definition simplify_goal_frac_ptr_val_inst := [instance simplify_goal_frac_ptr_val with 0%N].
  Global Existing Instance simplify_goal_frac_ptr_val_inst.

  Lemma simplify_goal_frac_ptr_val_unrefined ty (v : val) β T:
    (∃ p : address, <affine> ⌜v = p⌝ ∗ p ◁ₗ{β} ty ∗ T)
    ⊢ simplify_goal (v ◁ᵥ frac_ptr β ty) T.
  Proof. iIntros "[% [-> [? $]]]". iExists _. by iSplit. Qed.
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

  Lemma own_val_to_own_place (l : address) ty β T:
    l ◁ₗ{β} ty ∗ T
    ⊢ l ◁ᵥ l @ frac_ptr β ty ∗ T.
  Proof. by iIntros "[$ $]". Qed.

  Lemma own_val_to_own_place_singleton (l : address) β T:
    T
    ⊢ l ◁ᵥ l @ frac_ptr β (place l) ∗ T.
  Proof. by iIntros "$". Qed.

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

(*   Lemma type_cast_ptr_ptr p β ty T:
    (T (addr_to_val p) (p @ frac_ptr β ty))
    ⊢ typed_un_op p (p ◁ₗ{β} ty) (CastOp PtrOp) PtrOp T.
  Proof.
    iIntros "HT Hp" (Φ) "HΦ".
    iApply wp_cast_loc; [by apply val_to_of_loc|].
    iApply ("HΦ" with "[Hp] HT") => //. by iFrame.
  Qed.
  Definition type_cast_ptr_ptr_inst := [instance type_cast_ptr_ptr].
  Global Existing Instance type_cast_ptr_ptr_inst. *)

  Lemma type_if_ptr_own l β ty t T1 T2:
    (l ◁ₗ{β} ty -∗ (*(loc_in_bounds l 0 ∗ True) ∧*) T1)
    ⊢ typed_if (tptr t) l (l ◁ₗ{β} ty) T1 T2.
  Proof.
    iIntros "HT1 Hl".
    iDestruct ("HT1" with "Hl") as "HT".
    rewrite /adr2val /sem_cast /=.
    rewrite andb_false_r /=.
    eauto.
  Qed.
  Definition type_if_ptr_own_inst := [instance type_if_ptr_own].
  Global Existing Instance type_if_ptr_own_inst.

(*   Lemma type_assert_ptr_own l β ty t s fn ls R Q:
    (l ◁ₗ{β} ty -∗ (*(loc_in_bounds l 0 ∗ True) ∧*) typed_stmt s fn ls R Q)
    ⊢ typed_assert (tptr t) l (l ◁ₗ{β} ty) s fn ls R Q.
  Proof.
    iIntros "HT1 Hl".
    iDestruct ("HT1" with "Hl") as "[[#Hlib _] HT]".
    iDestruct (loc_in_bounds_has_alloc_id with "Hlib") as %[? H].
    iExists l. iSplit; first by rewrite val_to_of_loc.
    iSplit. { iPureIntro. move: l H => [??] /= -> //. }
    iSplitR. { by iApply wp_if_precond_alloc. }
    by iApply "HT".
  Qed.
  Definition type_assert_ptr_own_inst := [instance type_assert_ptr_own].
  Global Existing Instance type_assert_ptr_own_inst.

  Lemma type_place_cast_ptr_ptr K l ty β T:
    typed_place K l β ty T
    ⊢ typed_place (UnOpPCtx (CastOp PtrOp) :: K) l β ty T.
  Proof.
    iIntros "HP" (Φ) "Hl HΦ" => /=.
    iApply wp_cast_loc. { by apply val_to_of_loc. }
    iIntros "!#". iExists _. iSplit => //.
    iApply ("HP" with "Hl"). iIntros (l' ty2 β2 typ R) "Hl' Htyp HT".
    iApply ("HΦ" with "Hl' [-HT] HT"). iIntros (ty') "Hl'".
    iMod ("Htyp" with "Hl'") as "[? $]". by iFrame.
  Qed.
  Definition type_place_cast_ptr_ptr_inst := [instance type_place_cast_ptr_ptr].
  Global Existing Instance type_place_cast_ptr_ptr_inst.

  Lemma type_cast_int_ptr n v it T:
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
  Global Existing Instance type_cast_int_ptr_inst | 50.

  Lemma type_copy_aid v a it l β ty T:
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
           | Olt => Some (bool_decide (l1.2 < l2.2))
           | Ogt => Some (bool_decide (l1.2 > l2.2))
           | Ole => Some (bool_decide (l1.2 <= l2.2))
           | Oge => Some (bool_decide (l1.2 >= l2.2))
           | _ => None
           end = Some b) T:
    (⎡l1 ◁ₗ{β1} ty1⎤ -∗ ⎡l2 ◁ₗ{β2} ty2⎤ -∗ <affine> ⌜l1.1 = l2.1⌝ ∗ (
      ⌜0 ≤ l1.2 ≤ Ptrofs.max_unsigned ∧ 0 ≤ l2.2 ≤ Ptrofs.max_unsigned⌝ ∧
      ⎡weak_valid_pointer l1⎤ ∧ ⎡weak_valid_pointer l2⎤ ∧
      T (i2v (bool_to_Z b) tint) (b @ boolean tint)))
    ⊢ typed_bin_op l1 ⎡l1 ◁ₗ{β1} ty1⎤ l2 ⎡l2 ◁ₗ{β2} ty2⎤ op (tptr t1) (tptr t2) T.
  Proof.
    iIntros "HT Hl1 Hl2". iIntros (Φ) "HΦ". iDestruct ("HT" with "Hl1 Hl2") as (Heq (? & ?)) "HT".
    iIntros (?) "Hm".
    iDestruct (binop_lemmas4.weak_valid_pointer_dry with "[$Hm HT]") as %H1.
    { iDestruct "HT" as "($ & _)". }
    iDestruct (binop_lemmas4.weak_valid_pointer_dry with "[$Hm HT]") as %H2.
    { iDestruct "HT" as "(_ & $ & _)". }
    iFrame; iExists (i2v (bool_to_Z b) tint); iSplit.
    - iStopProof; split => rho; monPred.unseal.
      apply bi.pure_intro.
      assert (classify_cmp (tptr t1) (tptr t2) = cmp_case_pp) as Hclass by done.
      rewrite -val_of_bool_eq.
      destruct op => //; simplify_eq; simpl; rewrite /Cop.sem_cmp Hclass /cmp_ptr /= if_true // H1 H2 /=.
      + rewrite ltuptrofs_repr_zlt //.
      + rewrite ltuptrofs_repr_zlt //.
        case_bool_decide; destruct (zlt _ _); (done || lia).
      + rewrite ltuptrofs_repr_zlt //.
        case_bool_decide; destruct (zlt _ _); (done || lia).
      + rewrite ltuptrofs_repr_zlt //.
        case_bool_decide; destruct (zlt _ _); (done || lia).
    - iDestruct "HT" as "(_ & _ & HT)".
      iApply ("HΦ" with "[] HT") => //.
      iExists _; iSplit; iPureIntro; try done.
      by destruct b.
  Qed.
  Definition type_lt_ptr_ptr_inst l1 l2 :=
    [instance type_relop_ptr_ptr l1 l2 Olt (bool_decide (l1.2 < l2.2))].
  Global Existing Instance type_lt_ptr_ptr_inst.
  Definition type_gt_ptr_ptr_inst l1 l2 :=
    [instance type_relop_ptr_ptr l1 l2 Ogt (bool_decide (l1.2 > l2.2))].
  Global Existing Instance type_gt_ptr_ptr_inst.
  Definition type_le_ptr_ptr_inst l1 l2 :=
    [instance type_relop_ptr_ptr l1 l2 Ole (bool_decide (l1.2 <= l2.2))].
  Global Existing Instance type_le_ptr_ptr_inst.
  Definition type_ge_ptr_ptr_inst l1 l2 :=
    [instance type_relop_ptr_ptr l1 l2 Oge (bool_decide (l1.2 >= l2.2))].
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

  Global Program Instance shr_copyable p ty : Copyable (p @ frac_ptr Shr ty).
  Next Obligation.
  Admitted.
  Next Obligation.
    iIntros (p ty E ot l ? (t & ->)) "(%&#Hmt&#Hty)".
    iMod (heap_mapsto_own_state_to_mt with "Hmt") as (q) "[_ Hl]" => //.
    unfold has_layout_loc.
    rewrite field_compatible_tptr; erewrite mapsto_tptr; iSplitR => //.
    iExists _, _. iFrame. iModIntro. iSplit => //.
    - iIntros "!>"; by iSplit.
    - by iIntros "_".
  Qed.

  Lemma find_in_context_type_loc_own l T:
    (∃ l1 β1 β ty, l1 ◁ₗ{β1} (l @ frac_ptr β ty) ∗ (l1 ◁ₗ{β1} (l @ frac_ptr β (place l)) -∗
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

  Lemma find_in_context_type_val_own l T:
    (∃ ty : type, ⎡l ◁ₗ ty⎤ ∗ T (l @ frac_ptr Own ty))
    ⊢ find_in_context (FindVal l) T.
  Proof. iDestruct 1 as (ty) "[Hl HT]". iExists _ => /=. by iFrame. Qed.
  Definition find_in_context_type_val_own_inst :=
    [instance find_in_context_type_val_own with FICSyntactic].
  Global Existing Instance find_in_context_type_val_own_inst | 10.

  Lemma find_in_context_type_val_own_singleton (l : address) T:
    (emp ∗ T (l @ frac_ptr Own (place l)))
    ⊢ find_in_context (FindVal l) T.
  Proof. iIntros "[_ HT]". iExists _ => /=. iFrame "HT". simpl. done. Qed.
  Definition find_in_context_type_val_own_singleton_inst :=
    [instance find_in_context_type_val_own_singleton with FICSyntactic].
  Global Existing Instance find_in_context_type_val_own_singleton_inst | 20.

  (* We cannot use place here as it can easily lead to an infinite
  loop during type checking. Thus, we define place' that is not
  unfolded as eagerly as place. You probably should not add typing
  rules for place', but for place instead. *)
  Definition place' (l : address) : type := place l.
  Lemma find_in_context_type_val_P_own_singleton (l : address) T:
    (emp ∗ T (l ◁ₗ place' l))
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
  Context `{!typeG Σ} {cs : compspecs}.

  (* Should loc_in_bounds be replaced with valid_pointer'? But that would take a piece of ownership of l'. *)
  Program Definition ptr_type (n : nat) (l' : address) : type := {|
    ty_has_op_type ot mt := (∃ t, ot = tptr t)%type;
    ty_own β l := (<affine> ⌜field_compatible (tptr tvoid) [] l⌝ ∗ (*loc_in_bounds l' n ∗*) l ↦_(tptr tvoid)[β] l')%I;
    ty_own_val v := (<affine> ⌜v = adr2val l'⌝ (*∗ loc_in_bounds l' n*))%I;
  |}.
  Next Obligation. iIntros (????). iDestruct 1 as "[$ ?]". by iApply heap_mapsto_own_state_share. Qed.
  Next Obligation. iIntros (n l ot mt l' (? & ->)). iDestruct 1 as (?) "_". rewrite /has_layout_loc field_compatible_tptr //. Qed.
  Next Obligation. Admitted.
(*   Next Obligation. iIntros (n l ot mt v (? & ->)) "[Hv _]". by iDestruct "Hv" as %->. Qed. *)
  Next Obligation. iIntros (n l ot mt v (? & ->)) "[? Hl]". unfold heap_mapsto_own_state. erewrite mapsto_tptr. eauto with iFrame. Qed.
  Next Obligation. iIntros (n l ot mt l' v (? & ->) ?) "Hl ->". rewrite /has_layout_loc field_compatible_tptr in H; unfold heap_mapsto_own_state; erewrite mapsto_tptr; by iFrame. Qed.
(*   Next Obligation.
    iIntros (n l v ot mt st ?). apply mem_cast_compat_loc; [done|].
    iIntros "[-> ?]". iPureIntro. naive_solver.
  Qed. *)

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
    rewrite field_compatible_tptr; erewrite mapsto_tptr.
    repeat iSplit => //. iPureIntro. rewrite /tc_val' /= andb_false_r //.
  Qed.
  Definition simplify_ptr_hyp_place_inst := [instance simplify_ptr_hyp_place with 0%N].
  Global Existing Instance simplify_ptr_hyp_place_inst.

  Lemma simplify_ptr_goal_val (p:address) l n T:
    <affine> ⌜l = p⌝ ∗ (*loc_in_bounds l n ∗*) T  ⊢ simplify_goal (p ◁ᵥ l @ ptr n) T.
  Proof. by iIntros "[-> $]". Qed.
  Definition simplify_ptr_goal_val_inst := [instance simplify_ptr_goal_val with 10%N].
  Global Existing Instance simplify_ptr_goal_val_inst.

  Lemma subsume_own_ptr A p l1 l2 ty n T:
    (l1 ◁ₗ ty -∗ ∃ x, <affine> ⌜l1 = l2 x⌝ ∗ (*loc_in_bounds l1 (n x) ∗*) T x)
    ⊢ subsume (p ◁ₗ l1 @ &own ty)%I (λ x : A, p ◁ₗ (l2 x) @ ptr (n x))%I T.
  Proof.
    iIntros "HT Hp".
    iDestruct (ty_aligned _ (tptr tvoid) MCNone with "Hp") as %?; [eexists; eauto|].
    iDestruct (ty_deref _ (tptr tvoid) MCNone with "Hp") as (v) "[Hp [-> Hl]]"; [eexists; eauto|].
    iDestruct ("HT" with "Hl") as (? ->) "?". iExists _. by iFrame "∗".
  Qed.
  Definition subsume_own_ptr_inst := [instance subsume_own_ptr].
  Global Existing Instance subsume_own_ptr_inst.

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
End ptr.

Section null.
  Context `{!typeG Σ} {cs : compspecs}.
  Program Definition null : type := {|
    ty_has_op_type ot mt := (∃ t, ot = tptr t)%type;
    ty_own β l := (<affine> ⌜field_compatible (tptr tvoid) [] l⌝ ∗ l ↦_(tptr tvoid)[β] nullval)%I;
    ty_own_val v := <affine> ⌜v = nullval⌝%I;
  |}.
  Next Obligation. iIntros (???). iDestruct 1 as "[$ ?]". by iApply heap_mapsto_own_state_share. Qed.
  Next Obligation. iIntros (???(? & ->)) "[% _]". rewrite /has_layout_loc field_compatible_tptr //. Qed.
  Next Obligation. Admitted.
(*   Next Obligation. by iIntros (???(? & ->)->). Qed. *)
  Next Obligation. iIntros (???(? & ->)) "[% ?]". iExists _. unfold mapsto. erewrite mapsto_tptr. by iFrame. Qed.
  Next Obligation. iIntros (????(? & ->)?) "? ->". rewrite /has_layout_loc field_compatible_tptr in H; unfold mapsto; erewrite mapsto_tptr. by iFrame. Qed.
(*   Next Obligation. iIntros (v ot mt st ?). apply mem_cast_compat_loc; [done|]. iPureIntro. naive_solver. Qed. *)

(*   Global Instance null_loc_in_bounds β : LocInBounds null β bytes_per_addr.
  Proof.
    constructor. iIntros (l) "[_ Hl]".
    iDestruct (heap_mapsto_own_state_loc_in_bounds with "Hl") as "Hb".
    by iApply loc_in_bounds_shorten.
  Qed. *)

  Lemma type_null T :
    T null
    ⊢ typed_value nullval T.
  Proof. iIntros "HT". iExists  _. iFrame. done. Qed.
  Definition type_null_inst := [instance type_null].
  Global Existing Instance type_null_inst.

  Global Program Instance null_copyable : Copyable (null).
  Next Obligation.
    iIntros (E l ??(? & ->)) "[% Hl]".
    rewrite /has_layout_loc field_compatible_tptr.
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //. iSplitR => //.
    iExists _, _. erewrite mapsto_tptr. iFrame. iModIntro. iSplit => //.
    by iIntros "_".
  Qed.

  Definition heap_loc_eq l1 l2 m :=
    if Archi.ptr64 then Val.cmplu_bool (Mem.valid_pointer m) Ceq l1 l2
    else Val.cmpu_bool (Mem.valid_pointer m) Ceq l1 l2.

  Lemma eval_bin_op_ptr_cmp ce l1 l2 t1 t2 op h v b:
    match op with | Oeq | One => True | _ =>  False end →
    heap_loc_eq l1 l2 h = Some b →
    sem_binary_operation ce op l1 (tptr t1) l2 (tptr t2) h = Some v
     ↔ Val.of_bool (if op is Oeq then b else negb b) = v.
  Proof.
    rewrite /heap_loc_eq /=. move => ? Heq.
    rewrite /sem_binary_operation; destruct op => //; rewrite /Cop.sem_cmp /= /cmp_ptr /=.
    - rewrite Heq /=; split; congruence.
    - rewrite /Val.cmpu_bool /Val.cmplu_bool in Heq |- *; destruct l1 => //; destruct l2 => //; simpl in *;
          first [inv Heq; split; congruence | try if_tac in Heq; destruct (_ && _); inv Heq; simpl; split; congruence].
  Qed.

  Lemma type_binop_null_null v1 v2 t1 t2 op T:
    (<affine> ⌜match op with | Oeq | One => True | _ => False end⌝ ∗ ∀ v,
          T v ((if op is Oeq then true else false) @ boolean tint))
    ⊢ typed_bin_op v1 ⎡v1 ◁ᵥ null⎤ v2 ⎡v2 ◁ᵥ null⎤ op (tptr t1) (tptr t2) T.
  Proof.
    iIntros "[% HT]" (-> -> Φ) "HΦ".
    iIntros (?) "$".
    iExists (Val.of_bool (if op is Oeq then true else false)); iSplit.
    - iStopProof; split => rho; monPred.unseal.
      apply bi.pure_intro.
      intros; eapply eval_bin_op_ptr_cmp; done.
    - iApply "HΦ" => //. iExists _. iSplit; iPureIntro => //. by destruct op.
  Qed.
  Definition type_binop_null_null_inst := [instance type_binop_null_null].
  Global Existing Instance type_binop_null_null_inst.

(* need Mem.valid_pointer for this
  Lemma type_binop_ptr_null v op (l : address) t1 t2 ty β (*n `{!LocInBounds ty β n}*) T:
    (<affine> ⌜match op with Oeq | One => True | _ => False end⌝ ∗ ∀ v, ⎡l ◁ₗ{β} ty⎤ -∗
          T v ((if op is Oeq then false else true) @ boolean tint))
    ⊢ typed_bin_op l ⎡l ◁ₗ{β} ty⎤ v ⎡v ◁ᵥ null⎤ op (tptr t1) (tptr t2) T.
  Proof.
    iIntros "[% HT] Hl" (-> Φ) "HΦ".
    iIntros (?) "$".
    iExists (Val.of_bool (if op is Oeq then false else true)); iSplit.
    - iStopProof; split => rho; monPred.unseal.
      apply bi.pure_intro.
      intros; eapply (eval_bin_op_ptr_cmp _ _ _ _ _ _ _ _ false); try done.
      rewrite /heap_loc_eq /=.
    - iApply "HΦ" => //. iExists _. iSplit; iPureIntro => //. by destruct op.
  Qed.
  Definition type_binop_ptr_null_inst := [instance type_binop_ptr_null].
  Global Existing Instance type_binop_ptr_null_inst.

  Lemma type_binop_null_ptr v op (l : address) ty β n `{!LocInBounds ty β n} T:
    (⌜match op with EqOp rit | NeOp rit => rit = tint | _ => False end⌝ ∗ ∀ v, l ◁ₗ{β} ty -∗
          T v (((if op is EqOp _ then false else true) @ boolean tint)))
    ⊢ typed_bin_op v (v ◁ᵥ null) l (l ◁ₗ{β} ty) op PtrOp PtrOp T.
  Proof.
    iIntros "[% HT] -> Hl %Φ HΦ".
    iDestruct (loc_in_bounds_in_bounds with "Hl") as "#Hb".
    iDestruct (loc_in_bounds_shorten _ _ 0 with "Hb") as "#Hb0"; first by lia.
    have ?:= val_of_Z_bool (if op is EqOp _ then false else true) tint.
    iApply (wp_binop_det (i2v (bool_to_Z (if op is EqOp _ then false else true)) tint)).
    iIntros (σ) "Hctx". iApply fupd_mask_intro; [set_solver|]. iIntros "HE".
    iDestruct (loc_in_bounds_has_alloc_id with "Hb") as %[??].
    iDestruct (wp_if_precond_heap_loc_eq with "[] Hctx") as %Heq. { by iApply wp_if_precond_alloc. }
    rewrite heap_loc_eq_symmetric in Heq.
    iSplit.
    { iPureIntro => ?. rewrite eval_bin_op_ptr_cmp //. case_bool_decide => //; simplify_eq. naive_solver. }
    iModIntro. iMod "HE". iModIntro. iFrame.
    iApply "HΦ". 2: by iApply "HT". iExists _. iSplit; iPureIntro => //; by destruct op.
  Qed.
  Definition type_binop_null_ptr_inst := [instance type_binop_null_ptr].
  Global Existing Instance type_binop_null_ptr_inst. *)

(*  Lemma type_cast_null_int it v T:
    (T (i2v 0 it) (0 @ int it))
    ⊢ typed_un_op v (v ◁ᵥ null) (CastOp (IntOp it)) PtrOp T.
  Proof.
    iIntros "HT" (-> Φ) "HΦ".
    iApply wp_cast_null_int.
    { by apply: (val_of_Z_bool false). }
    iModIntro. iApply ("HΦ" with "[] HT").
    unfold int; simpl_type. iPureIntro. apply: (i2v_bool_Some false).
  Qed.
  Definition type_cast_null_int_inst := [instance type_cast_null_int].
  Global Existing Instance type_cast_null_int_inst.

  Lemma type_cast_zero_ptr v it T:
    (T (val_of_loc NULL_loc) null)
    ⊢ typed_un_op v (v ◁ᵥ 0 @ int it) (CastOp PtrOp) (IntOp it) T.
  Proof.
    unfold int; simpl_type.
    iIntros "HT" (Hv Φ) "HΦ".
    iApply wp_cast_int_null; first done.
    iModIntro. by iApply ("HΦ" with "[] HT").
  Qed.
  Definition type_cast_zero_ptr_inst := [instance type_cast_zero_ptr].
  Global Existing Instance type_cast_zero_ptr_inst | 10.

  Lemma type_cast_null_ptr v T:
    (T v null)
    ⊢ typed_un_op v (v ◁ᵥ null) (CastOp PtrOp) PtrOp T.
  Proof.
    iIntros "HT" (-> Φ) "HΦ".
    iApply wp_cast_loc; [by apply val_to_of_loc|].
    by iApply ("HΦ" with "[] HT").
  Qed.
  Definition type_cast_null_ptr_inst := [instance type_cast_null_ptr].
  Global Existing Instance type_cast_null_ptr_inst. *)

  Lemma type_if_null v t T1 T2:
    T2
    ⊢ typed_if (tptr t) v (v ◁ᵥ null) T1 T2.
  Proof.
    iIntros "HT2 -> /=". iExists (Vint Int.zero); iFrame; iPureIntro.
    rewrite /sem_cast /= andb_false_r //.
  Qed.
  Definition type_if_null_inst := [instance type_if_null].
  Global Existing Instance type_if_null_inst.
End null.

Section optionable.
  Context `{!typeG Σ} {cs : compspecs}.

  Global Program Instance frac_ptr_optional p ty β t1 t2: Optionable (p @ frac_ptr β ty) null (tptr t1) (tptr t2) := {|
    opt_pre v1 v2 := (p ◁ₗ{β} ty -∗ valid_pointer p)%I
  |}.
  Next Obligation.
    intros.
    iIntros "Hpre H1 -> Hctx".
    destruct bty; [ iDestruct "H1" as (->) "Hty" | iDestruct "H1" as %-> ].
    - iDestruct ("Hpre" with "Hty") as "Hlib".
      iDestruct (valid_pointer_dry0 with "[$Hctx $Hlib]") as %Hvalid; iPureIntro.
      destruct beq => /=; rewrite /Cop.sem_cmp /= /cmp_ptr /= Hvalid /= /Vtrue /Vfalse /Int.zero /Int.one; split; congruence.
    - rewrite eval_bin_op_ptr_cmp // /= ?Int.eq_true ?Int64.eq_true; destruct beq => //.
  Qed.
  Global Program Instance frac_ptr_optional_agree ty1 ty2 β : OptionableAgree (frac_ptr β ty1) (frac_ptr β ty2).
  Next Obligation. done. Qed.


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

  Lemma subsume_optional_place_val_null A ty l β b ty' T:
    (l ◁ₗ{β} ty' -∗ ∃ x, <affine> ⌜b x⌝ ∗ l ◁ᵥ (ty x) ∗ T x)
    ⊢ subsume (l ◁ₗ{β} ty') (λ x : A, l ◁ᵥ (b x) @ optional (ty x) null) T.
  Proof.
    iIntros "Hsub Hl". iDestruct ("Hsub" with "Hl") as (??) "[Hl ?]".
    iExists _. iFrame. unfold optional; simpl_type. iLeft. by iFrame.
  Qed.
  Definition subsume_optional_place_val_null_inst := [instance subsume_optional_place_val_null].
  Global Existing Instance subsume_optional_place_val_null_inst | 20.

  Lemma subsume_optionalO_place_val_null B A (ty : B → A → type) l β b ty' T:
    (l ◁ₗ{β} ty' -∗ ∃ y x, <affine> ⌜b y = Some x⌝ ∗ l ◁ᵥ ty y x ∗ T y)
    ⊢ subsume (l ◁ₗ{β} ty') (λ y, l ◁ᵥ (b y) @ optionalO (ty y) null) T.
  Proof.
    iIntros "Hsub Hl". iDestruct ("Hsub" with "Hl") as (?? Heq) "[? ?]".
    iExists _. iFrame. rewrite Heq. unfold optionalO; simpl_type. done.
  Qed.
  Definition subsume_optionalO_place_val_null_inst := [instance subsume_optionalO_place_val_null].
  Global Existing Instance subsume_optionalO_place_val_null_inst | 20.

(*   (* TODO: generalize this with a IsLoc typeclass or similar *)
  Lemma type_cast_optional_own_ptr b v β ty T:
    (T v (b @ optional (&frac{β} ty) null))
    ⊢ typed_un_op v (v ◁ᵥ b @ optional (&frac{β} ty) null) (CastOp PtrOp) PtrOp T.
  Proof.
    iIntros "HT Hv" (Φ) "HΦ". unfold optional, ty_of_rty at 2; simpl_type.
    iDestruct "Hv" as "[[% [%l [% Hl]]]|[% ->]]"; subst.
    all: iApply wp_cast_loc; [by apply val_to_of_loc|].
    - iApply ("HΦ" with "[Hl] HT"). simpl_type. iLeft. iSplitR; [done|]. iExists _. by iFrame.
    - iApply ("HΦ" with "[] HT"). simpl_type. by iRight.
  Qed.
  Definition type_cast_optional_own_ptr_inst := [instance type_cast_optional_own_ptr].
  Global Existing Instance type_cast_optional_own_ptr_inst.

  Lemma type_cast_optionalO_own_ptr A (b : option A) v β ty T:
    (T v (b @ optionalO (λ x, &frac{β} (ty x)) null))
    ⊢ typed_un_op v (v ◁ᵥ b @ optionalO (λ x, &frac{β} (ty x)) null) (CastOp PtrOp) PtrOp T.
  Proof.
    iIntros "HT Hv" (Φ) "HΦ". unfold optionalO; simpl_type.
    destruct b as [?|].
    - unfold ty_of_rty at 2; simpl_type. iDestruct "Hv" as "[%l [% Hl]]"; subst.
      iApply wp_cast_loc; [by apply val_to_of_loc|].
      iApply ("HΦ" with "[Hl] HT"). simpl_type. iExists _. by iFrame.
    - iDestruct "Hv" as "->".
      iApply wp_cast_loc; [by apply val_to_of_loc|].
      iApply ("HΦ" with "[] HT"). simpl_type. done.
  Qed.
  Definition type_cast_optionalO_own_ptr_inst := [instance type_cast_optionalO_own_ptr].
  Global Existing Instance type_cast_optionalO_own_ptr_inst. *)
End optionable.

Global Typeclasses Opaque ptr_type ptr.
Global Typeclasses Opaque frac_ptr_type frac_ptr.
Global Typeclasses Opaque null.

Section optional_null.
  Context `{!typeG Σ} {cs : compspecs}.

  Local Typeclasses Transparent optional_type optional.

(*   Lemma type_place_optional_null K l β1 b ty T:
    ⌜b⌝ ∗ typed_place K l β1 ty T
    ⊢ typed_place K l β1 (b @ optional ty null) T.
  Proof.
    iIntros "[% H]" (Φ) "[[_ Hl]|[% _]] HH"; last done.
    by iApply ("H" with "Hl").
  Qed.
  (* This should have a lower priority than type_place_id *)
  Definition type_place_optional_null_inst := [instance type_place_optional_null].
  Global Existing Instance type_place_optional_null_inst | 100.

  Lemma type_place_optionalO_null A K l β1 b (ty : A → _) T:
    ⌜is_Some b⌝ ∗ (∀ x, ⌜b = Some x⌝ -∗ typed_place K l β1 (ty x) T)
    ⊢ typed_place K l β1 (b @ optionalO ty null) T.
  Proof.
    iDestruct 1 as ([? ->]) "Hwp".
    iIntros (Φ) "Hx". by iApply "Hwp".
  Qed.
  (* This should have a lower priority than type_place_id *)
  Definition type_place_optionalO_null_inst := [instance type_place_optionalO_null].
  Global Existing Instance type_place_optionalO_null_inst | 100. *)
End optional_null.
