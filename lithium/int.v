From VST.lithium Require Export type.
From VST.lithium Require Import programs boolean.
From VST.lithium Require Import type_options.

Local Open Scope Z.

Section int.
  Context `{!typeG Σ} {cs : compspecs}.

  (* Separate definition such that we can make it typeclasses opaque
  later. We cannot call it int_type since that already exists.  *)
  Program Definition int_inner_type (it : Ctypes.type) (n : Z) : type := {|
    ty_has_op_type ot mt := (*is_bool_ot ot it stn*) ot = it;
    ty_own β l := ∃ v, ⌜val_to_Z v it = Some n⌝ ∧ ⌜field_compatible it [] l⌝ ∧ l ↦_it[β] v;
    ty_own_val v := <affine> ⌜val_to_Z v it = Some n⌝;
  |}%I.
  Next Obligation.
    iIntros (it n l ??) "(%v&%Hv&%Hl&H)". iExists v.
    by iMod (heap_mapsto_own_state_share with "H") as "$".
  Qed.
  Next Obligation. iIntros (????? ->) "(%&%&$&_)". Qed.
  Next Obligation. iIntros (????? ->) "(%v&%&%&Hl)". eauto with iFrame. Qed.
  Next Obligation. iIntros (????? v -> ?) "Hl %". iExists v. eauto with iFrame. Qed.
(*   Next Obligation. iIntros (???????). apply: mem_cast_compat_int; [naive_solver|]. iPureIntro. naive_solver. Qed. *)

  Definition int (it : Ctypes.type) : rtype _ := RType (int_inner_type it).

(*   Lemma int_loc_in_bounds l β n it:
     l ◁ₗ{β} n @ int it -∗ loc_in_bounds l (bytes_per_int it).
  Proof.
    iIntros "(%&%Hv&%&Hl)". move: Hv => /val_to_Z_length <-.
    by iApply heap_mapsto_own_state_loc_in_bounds.
  Qed.
  Global Instance loc_in_bounds_int n it β: LocInBounds (n @ int it) β (bytes_per_int it).
  Proof.
    constructor. iIntros (l) "Hl".
    iDestruct (int_loc_in_bounds with "Hl") as "Hlib".
    iApply loc_in_bounds_shorten; last done. lia.
  Qed.

  Global Instance alloc_alive_int n it β: AllocAlive (n @ int it) β True.
  Proof.
    constructor. iIntros (l ?) "(%&%&%&Hl)".
    iApply (heap_mapsto_own_state_alloc with "Hl").
    erewrite val_to_Z_length; [|done]. have := bytes_per_int_gt_0 it. lia.
  Qed.

  Global Program Instance learn_align_int β it n
    : LearnAlignment β (n @ int it) (Some (ly_align it)).
  Next Obligation. by iIntros (β it n ?) "(%&%&%&?)". Qed. *)

  Lemma ty_own_int_in_range l β n it : l ◁ₗ{β} n @ int it -∗ ⌜n ∈ it⌝.
  Proof.
    iIntros "Hl". destruct β.
    - iDestruct (ty_deref _ _ MCNone with "Hl") as (?) "[_ %]"; [done|].
      iPureIntro. by eapply val_to_Z_in_range.
    - iDestruct "Hl" as (?) "[% _]".
      iPureIntro. by eapply val_to_Z_in_range.
  Qed.

  (* TODO: make a simple type as in lambda rust such that we do not
  have to reprove this everytime? *)
  Global Program Instance int_copyable x it : Copyable (x @ int it).
  Next Obligation.
    iIntros (???????) "(%v&%Hv&%Hl&Hl)".
    simpl in *; subst.
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //.
    iSplitR => //. iExists q, v. iFrame. iModIntro. eauto with iFrame.
  Qed.

  Global Instance int_timeless l z it:
    Timeless (l ◁ₗ z @ int it)%I.
  Proof. apply _. Qed.
End int.
(* Typeclasses Opaque int. *)
Notation "int< it >" := (int it) (only printing, format "'int<' it '>'") : printing_sugar.

Definition int_lt it v1 v2 :=
  match it, v1, v2 with
  | Tint I32 Unsigned _, Vint i1, Vint i2 => Int.ltu i1 i2
  | Tint _ _ _, Vint i1, Vint i2 => Int.lt i1 i2
  | Tlong Unsigned _, Vlong i1, Vlong i2 => Int64.ltu i1 i2
  | Tlong Signed _, Vlong i1, Vlong i2 => Int64.lt i1 i2
  | _, _, _ => false
  end.

Section programs.
  Context `{!typeG Σ} {cs : compspecs}.

  (*** int *)
  Lemma type_val_int n it T :
    typed_value (i2v n it) T :-
      exhale (<affine> ⌜n ∈ it⌝);
      return T (n @ (int it)).
  Proof.
    iIntros "[%Hn HT]".
    iExists _. iFrame. iPureIntro.
    by apply i2v_to_Z.
  Qed.
  Definition type_val_int_inst := [instance type_val_int].
  Global Existing Instance type_val_int_inst.

  (* TODO: instead of adding it_in_range to the context here, have a
  SimplifyPlace/Val instance for int which adds it to the context if
  it does not yet exist (using check_hyp_not_exists)?! *)
  Lemma type_relop_int_int n1 n2 op b it v1 v2 T :
    match op with
    | Oeq => Some (bool_decide (n1 = n2))
    | One => Some (bool_decide (n1 ≠ n2))
    | Olt => Some (bool_decide (n1 < n2))
    | Ogt => Some (bool_decide (n1 > n2))
    | Ole => Some (bool_decide (n1 <= n2))
    | Oge => Some (bool_decide (n1 >= n2))
    | _ => None
    end = Some b →
    (⌜n1 ∈ it⌝ -∗ ⌜n2 ∈ it⌝ -∗ T (i2v (bool_to_Z b) tint) (b @ boolean tint))
    ⊢ typed_bin_op v1 ⎡v1 ◁ᵥ n1 @ int it⎤ v2 ⎡v2 ◁ᵥ n2 @ int it⎤ op it it T.
  Proof.
    iIntros "%Hop HT %Hv1 %Hv2 %Φ HΦ".
    iDestruct ("HT" with "[] []" ) as "HT".
    1-2: iPureIntro; by apply: val_to_Z_in_range.
    rewrite /wp_binop.
    iExists (i2v (bool_to_Z b) tint); iSplitL "".
    - rewrite /eval_binop_rel.
      iStopProof; split => rho; monPred.unseal.
      iIntros "_" (?) "Hm".
      assert (classify_cmp it it = cmp_default) as Hclass.
      { destruct it; try by destruct v1.
        by destruct i. }
      rewrite -val_of_bool_eq.
      destruct op; inv Hop; rewrite /= /Cop.sem_cmp Hclass /Cop.sem_binarith (* Heq *).
      + assert (bool_decide (n1 = n2) = int_eq v1 v2) as ->.
        { destruct it, v1; try done; destruct v2; try done; simpl in *.
        * pose proof (Int.eq_spec i0 i1) as Heq.
          destruct (Int.eq i0 i1).
          -- subst; destruct s; inv Hv1; case_bool_decide; simpl in *; congruence.
          -- destruct s; inv Hv1; case_bool_decide; try done;
               by (exploit (signed_inj i0 i1); congruence || exploit (unsigned_eq_eq i0 i1); congruence).
        * pose proof (Int64.eq_spec i i0) as Heq.
          destruct (Int64.eq i i0).
          -- subst; destruct s; inv Hv1; case_bool_decide; simpl in *; congruence.
          -- destruct s; inv Hv1; case_bool_decide; try done;
               by (exploit (signed_inj_64 i i0); congruence || exploit (unsigned_inj_64 i i0); congruence). }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
      + assert (bool_decide (n1 ≠ n2) = negb (int_eq v1 v2)) as ->.
        { admit. }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
      + assert (bool_decide (n1 < n2) = int_lt it v1 v2) as ->.
        { admit. }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
      + assert (bool_decide (n1 > n2) = int_lt it v2 v1) as ->.
        { admit. }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
      + assert (bool_decide (n1 ≤ n2) = negb (int_lt it v2 v1)) as ->.
        { admit. }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
      + assert (bool_decide (n1 >= n2) = negb (int_lt it v1 v2)) as ->.
        { admit. }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
    - iApply "HΦ"; last done. iExists (bool_to_Z b).
      iSplit; [by destruct b | done].
  Qed.

  Definition type_eq_int_int_inst n1 n2 :=
    [instance type_relop_int_int n1 n2 Oeq (bool_decide (n1 = n2))].
  Global Existing Instance type_eq_int_int_inst.
  Definition type_ne_int_int_inst n1 n2 :=
    [instance type_relop_int_int n1 n2 One (bool_decide (n1 ≠ n2))].
  Global Existing Instance type_ne_int_int_inst.
  Definition type_lt_int_int_inst n1 n2 :=
    [instance type_relop_int_int n1 n2 Olt (bool_decide (n1 < n2))].
  Global Existing Instance type_lt_int_int_inst.
  Definition type_gt_int_int_inst n1 n2 :=
    [instance type_relop_int_int n1 n2 Ogt (bool_decide (n1 > n2))].
  Global Existing Instance type_gt_int_int_inst.
  Definition type_le_int_int_inst n1 n2 :=
    [instance type_relop_int_int n1 n2 Ole (bool_decide (n1 ≤ n2))].
  Global Existing Instance type_le_int_int_inst.
  Definition type_ge_int_int_inst n1 n2 :=
    [instance type_relop_int_int n1 n2 Oge (bool_decide (n1 >= n2))].
  Global Existing Instance type_ge_int_int_inst.

  Lemma type_arithop_int_int n1 n2 n op it v1 v2
    (Hop : int_arithop_result it n1 n2 op = Some n) T :
    (⌜n1 ∈ it⌝ -∗ ⌜n2 ∈ it⌝ -∗ ⌜int_arithop_sidecond it n1 n2 n op⌝ ∗ T (i2v n it) (n @ int it))
    ⊢ typed_bin_op v1 (v1 ◁ᵥ n1 @ int it) v2 (v2 ◁ᵥ n2 @ int it) op it it T.
  Proof.
    iIntros "HT %Hv1 %Hv2 %Φ HΦ".
    iDestruct ("HT" with "[] []" ) as (Hsc) "HT".
    1-2: iPureIntro; by apply: val_to_Z_in_range.
    iApply wp_int_arithop; [done..|].
    iIntros (v Hv) "!>". rewrite /i2v Hv/=. iApply ("HΦ" with "[] HT").
    iPureIntro. by apply: val_to_of_Z.
  Qed.
  Definition type_add_int_int_inst n1 n2 := [instance type_arithop_int_int n1 n2 (n1 + n2) Oadd].
  Global Existing Instance type_add_int_int_inst.
  Definition type_sub_int_int_inst n1 n2 := [instance type_arithop_int_int n1 n2 (n1 - n2) Osub].
  Global Existing Instance type_sub_int_int_inst.
  Definition type_mul_int_int_inst n1 n2 := [instance type_arithop_int_int n1 n2 (n1 * n2) Omul].
  Global Existing Instance type_mul_int_int_inst.
  Definition type_div_int_int_inst n1 n2 := [instance type_arithop_int_int n1 n2 (n1 `quot` n2) Odiv].
  Global Existing Instance type_div_int_int_inst.
  Definition type_mod_int_int_inst n1 n2 := [instance type_arithop_int_int n1 n2 (n1 `rem` n2) Omod].
  Global Existing Instance type_mod_int_int_inst.
  Definition type_and_int_int_inst n1 n2 := [instance type_arithop_int_int n1 n2 (Z.land n1 n2) Oand].
  Global Existing Instance type_and_int_int_inst.
  Definition type_or_int_int_inst n1 n2 := [instance type_arithop_int_int n1 n2 (Z.lor n1 n2) Oor].
  Global Existing Instance type_or_int_int_inst.
  Definition type_xor_int_int_inst n1 n2 := [instance type_arithop_int_int n1 n2 (Z.lxor n1 n2) Oxor].
  Global Existing Instance type_xor_int_int_inst.
  Definition type_shl_int_int_inst n1 n2 := [instance type_arithop_int_int n1 n2 (n1 ≪ n2) Oshl].
  Global Existing Instance type_shl_int_int_inst.
  Definition type_shr_int_int_inst n1 n2 := [instance type_arithop_int_int n1 n2 (n1 ≫ n2) Oshr].
  Global Existing Instance type_shr_int_int_inst.

  Inductive trace_if_int :=
  | TraceIfInt (n : Z).

  Lemma type_if_int it (n : Z) v T1 T2:
    case_if (n ≠ 0)
      (li_trace (TraceIfInt n, true) T1)
      (li_trace (TraceIfInt n, false) T2)
    ⊢ typed_if it v (v ◁ᵥ n @ int it) T1 T2.
  Proof.
    iIntros "Hs %Hb" => /=.
    iExists (Val.of_bool (bool_decide (n ≠ 0))); iSplit.
    { iPureIntro.
      destruct v, it; try discriminate; destruct s; inv Hb; simpl.
      + pose proof (Int.eq_spec i Int.zero).
        case_bool_decide; simple_if_tac; subst; try done.
        assert (Int.repr (Int.signed i) = Int.repr 0) as Hz by congruence;
          rewrite Int.repr_signed // in Hz.
      + pose proof (Int.eq_spec i Int.zero).
        case_bool_decide; simple_if_tac; subst; try done.
        assert (Int.repr (Int.unsigned i) = Int.repr 0) as Hz by congruence;
          rewrite Int.repr_unsigned // in Hz.
      + pose proof (Int64.eq_spec i Int64.zero).
        case_bool_decide; simple_if_tac; subst; try done.
        assert (Int64.repr (Int64.signed i) = Int64.repr 0) as Hz by congruence;
          rewrite Int64.repr_signed // in Hz.
      + pose proof (Int64.eq_spec i Int64.zero).
        case_bool_decide; simple_if_tac; subst; try done.
        assert (Int64.repr (Int64.unsigned i) = Int64.repr 0) as Hz by congruence;
          rewrite Int64.repr_unsigned // in Hz. }
    case_bool_decide.
    - iDestruct "Hs" as "[Hs _]". by iApply "Hs".
    - iDestruct "Hs" as "[_ Hs]". iApply "Hs". naive_solver.
  Qed.
  Definition type_if_int_inst := [instance type_if_int].
  Global Existing Instance type_if_int_inst.

(*  Lemma type_assert_int it n v s fn ls R Q :
    (⌜n ≠ 0⌝ ∗ typed_stmt s fn ls R Q)
    ⊢ typed_assert (IntOp it) v (v ◁ᵥ n @ int it) s fn ls R Q.
  Proof. iIntros "[% Hs] %Hb". iExists _. by iFrame. Qed.
  Definition type_assert_int_inst := [instance type_assert_int].
  Global Existing Instance type_assert_int_inst.

  Inductive trace_switch_int :=
  | TraceSwitchIntCase (n : Z)
  | TraceSwitchIntDefault.

  Lemma type_switch_int v n it m ss def fn ls R Q:
    ([∧ map] i↦mi ∈ m, li_trace (TraceSwitchIntCase i) (
             ⌜n = i⌝ -∗ ∃ s, ⌜ss !! mi = Some s⌝ ∗ typed_stmt s fn ls R Q)) ∧
    (li_trace (TraceSwitchIntDefault) (
                     ⌜n ∉ (map_to_list m).*1⌝ -∗ typed_stmt def fn ls R Q))
    ⊢ typed_switch v (n @ int it) it m ss def fn ls R Q.
  Proof.
    unfold li_trace. iIntros "HT %Hv". iExists n. iSplit; first done.
    iInduction m as [] "IH" using map_ind; simplify_map_eq => //.
    { iDestruct "HT" as "[_ HT]". iApply "HT". iPureIntro.
      rewrite map_to_list_empty. set_solver. }
    rewrite big_andM_insert //. destruct (decide (n = i)); subst.
    - rewrite lookup_insert. iDestruct "HT" as "[[HT _] _]". by iApply "HT".
    - rewrite lookup_insert_ne//. iApply "IH". iSplit; first by iDestruct "HT" as "[[_ HT] _]".
      iIntros (Hn). iDestruct "HT" as "[_ HT]". iApply "HT". iPureIntro.
      rewrite map_to_list_insert //. set_solver.
  Qed.
  Definition type_switch_int_inst := [instance type_switch_int].
  Global Existing Instance type_switch_int_inst. *)

  Lemma type_neg_int n it v T:
    (⌜n ∈ it⌝ -∗ ⌜it.(it_signed)⌝ ∗ ⌜n ≠ min_int it⌝ ∗ T (i2v (-n) it) ((-n) @ int it))
    ⊢ typed_un_op v (v ◁ᵥ n @ int it)%I (NegOp) (IntOp it) T.
  Proof.
    iIntros "HT %Hv %Φ HΦ". move: (Hv) => /val_to_Z_in_range ?.
    iDestruct ("HT" with "[//]") as (Hs Hn) "HT".
    have [|v' Hv']:= val_of_Z_is_Some None it (- n). {
      unfold elem_of, int_elem_of_it, max_int, min_int in *.
      destruct it as [?[]] => //; simpl in *; lia.
    }
    rewrite /i2v Hv'/=.
    iApply wp_neg_int => //. iApply ("HΦ" with "[] HT").
    iPureIntro. by apply: val_to_of_Z.
  Qed.
  Definition type_neg_int_inst := [instance type_neg_int].
  Global Existing Instance type_neg_int_inst.

(*  Lemma type_cast_int n it1 it2 v T:
    (⌜n ∈ it1⌝ -∗ ⌜n ∈ it2⌝ ∗ ∀ v, T v (n @ int it2))
    ⊢ typed_un_op v (v ◁ᵥ n @ int it1)%I (CastOp (IntOp it2)) (IntOp it1) T.
  Proof.
    iIntros "HT %Hv %Φ HΦ".
    iDestruct ("HT" with "[]") as ([v' Hv']%(val_of_Z_is_Some (val_to_byte_prov v))) "HT".
    { iPureIntro. by apply: val_to_Z_in_range. }
    iApply wp_cast_int => //. iApply ("HΦ" with "[] HT") => //.
    iPureIntro. by apply: val_to_of_Z.
  Qed.
  Definition type_cast_int_inst := [instance type_cast_int].
  Global Existing Instance type_cast_int_inst. *)

  Lemma type_not_int n1 it v1 T:
    let n := if it_signed it then Z.lnot n1 else Z_lunot (bits_per_int it) n1 in
    (⌜n1 ∈ it⌝ -∗ T (i2v n it) (n @ int it))
    ⊢ typed_un_op v1 (v1 ◁ᵥ n1 @ int it)%I (NotIntOp) (IntOp it) T.
  Proof.
    iIntros "%n HT %Hv1 %Φ HΦ".
    move: (Hv1) => /val_to_Z_in_range Hn1.
    have : n ∈ it.
    { move: Hn1.
      rewrite /n /elem_of /int_elem_of_it /min_int /max_int.
      destruct (it_signed it).
      - rewrite /int_half_modulus /Z.lnot. lia.
      - rewrite /int_modulus => ?.
        have -> : ∀ a b, a ≤ b - 1 ↔ a < b by lia.
        have ? := bits_per_int_gt_0 it.
        apply Z_lunot_range; lia. }
    rewrite /n => /(val_of_Z_is_Some None) [v Hv]. rewrite /i2v Hv /=.
    iApply (wp_unop_det_pure v). {
      split.
      + by inversion 1; simplify_eq.
      + move => ->. by econstructor.
    }
    iIntros "!>". iApply ("HΦ" with "[] (HT [//])").
    iPureIntro. by apply: val_to_of_Z.
  Qed.
  Definition type_not_int_inst := [instance type_not_int].
  Global Existing Instance type_not_int_inst.

(*  (* TODO: replace this with a typed_cas once it is refactored to take E as an argument. *)
  Lemma wp_cas_suc_int it z1 z2 zd l1 l2 vd Φ E:
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    z1 = z2 →
    l1 ◁ₗ z1 @ int it -∗ l2 ◁ₗ z2 @ int it -∗ vd ◁ᵥ zd @ int it -∗
    ▷ (l1 ◁ₗ zd @ int it -∗ l2 ◁ₗ z2 @ int it -∗ Φ (val_of_bool true)) -∗
    wp NotStuck E (CAS (IntOp it) (Val l1) (Val l2) (Val vd)) Φ.
  Proof.
    iIntros (? ->) "(%v1&%&%&Hl1) (%v2&%&%&Hl2) % HΦ/=".
    iApply (wp_cas_suc with "Hl1 Hl2") => //.
    { by apply val_to_of_loc. }
    { by apply val_to_of_loc. }
    { by eapply val_to_Z_length. }
    iIntros "!# Hl1 Hl2". iApply ("HΦ" with "[Hl1] [Hl2]"); iExists _; by iFrame.
  Qed.

  Lemma wp_cas_fail_int it z1 z2 zd l1 l2 vd Φ E:
    (bytes_per_int it ≤ bytes_per_addr)%nat →
    z1 ≠ z2 →
    l1 ◁ₗ z1 @ int it -∗ l2 ◁ₗ z2 @ int it -∗ vd ◁ᵥ zd @ int it -∗
    ▷ (l1 ◁ₗ z1 @ int it -∗ l2 ◁ₗ z1 @ int it -∗ Φ (val_of_bool false)) -∗
    wp NotStuck E (CAS (IntOp it) (Val l1) (Val l2) (Val vd)) Φ.
  Proof.
    iIntros (? ?) "(%v1&%&%&Hl1) (%v2&%&%&Hl2) % HΦ/=".
    iApply (wp_cas_fail with "Hl1 Hl2") => //.
    { by apply val_to_of_loc. }
    { by apply val_to_of_loc. }
    { by eapply val_to_Z_length. }
    iIntros "!# Hl1 Hl2". iApply ("HΦ" with "[Hl1] [Hl2]"); iExists _; by iFrame.
  Qed. *)

  (*** int <-> bool *)
  Lemma subsume_int_boolean_place A l β n b it T:
    (∃ x, <affine> ⌜n = bool_to_Z (b x)⌝ ∗ T x)
    ⊢ subsume (l ◁ₗ{β} n @ int it) (λ x : A, l ◁ₗ{β} (b x) @ boolean it) T.
  Proof.
    iIntros "[% [-> ?]] Hint". iExists _. iFrame. iDestruct "Hint" as (???) "?".
    iExists _, _. iFrame. iSplit; first done. iSplit; last done. by destruct b.
  Qed.
  Definition subsume_int_boolean_place_inst := [instance subsume_int_boolean_place].
  Global Existing Instance subsume_int_boolean_place_inst.

  Lemma subsume_int_boolean_val A v n b it T:
    (∃ x, <affine> ⌜n = bool_to_Z (b x)⌝ ∗ T x)
    ⊢ subsume (v ◁ᵥ n @ int it) (λ x : A, v ◁ᵥ (b x) @ boolean it) T.
  Proof.
    iIntros "[%x [-> ?]] %". iExists _. iFrame. unfold boolean; simpl_type.
    iExists (bool_to_Z (b x)). iSplit; first done. by destruct b. Qed.
  Definition subsume_int_boolean_val_inst := [instance subsume_int_boolean_val].
  Global Existing Instance subsume_int_boolean_val_inst.

  Lemma type_binop_boolean_int it1 it2 it3 it4 v1 b1 v2 n2 op T:
    typed_bin_op v1 (v1 ◁ᵥ (bool_to_Z b1) @ int it1) v2 (v2 ◁ᵥ n2 @ int it2) op (IntOp it3) (IntOp it4) T
    ⊢ typed_bin_op v1 (v1 ◁ᵥ b1 @ boolean it1) v2 (v2 ◁ᵥ n2 @ int it2) op (IntOp it3) (IntOp it4) T.
  Proof.
    iIntros "HT H1 H2". iApply ("HT" with "[H1] H2"). unfold boolean; simpl_type.
    iDestruct "H1" as "(%&%H1&%H2)". iPureIntro.
    move: H1 H2 => /= -> ->. done.
  Qed.
  Definition type_binop_boolean_int_inst := [instance type_binop_boolean_int].
  Global Existing Instance type_binop_boolean_int_inst.

  Lemma type_binop_int_boolean it1 it2 it3 it4 v1 b1 v2 n2 op T:
    typed_bin_op v1 (v1 ◁ᵥ n2 @ int it2) v2 (v2 ◁ᵥ (bool_to_Z b1) @ int it1) op (IntOp it3) (IntOp it4) T
    ⊢ typed_bin_op v1 (v1 ◁ᵥ n2 @ int it2) v2 (v2 ◁ᵥ b1 @ boolean it1) op (IntOp it3) (IntOp it4) T.
  Proof.
    iIntros "HT H1 H2". iApply ("HT" with "H1 [H2]"). unfold boolean; simpl_type.
    iDestruct "H2" as "(%&%H1&%H2)". iPureIntro.
    move: H1 H2 => /= -> ->. done.
  Qed.
  Definition type_binop_int_boolean_inst := [instance type_binop_int_boolean].
  Global Existing Instance type_binop_int_boolean_inst.

(*  Lemma type_cast_int_builtin_boolean n it v T:
    (∀ v, T v ((bool_decide (n ≠ 0)) @ builtin_boolean))
    ⊢ typed_un_op v (v ◁ᵥ n @ int it)%I (CastOp BoolOp) (IntOp it) T.
  Proof.
    iIntros "HT %Hn %Φ HΦ". iApply wp_cast_int_bool => //.
    iApply ("HΦ" with "[] HT") => //=. unfold boolean; simpl_type. iPureIntro. naive_solver.
  Qed.
  Definition type_cast_int_builtin_boolean_inst := [instance type_cast_int_builtin_boolean].
  Global Existing Instance type_cast_int_builtin_boolean_inst. *)

  Lemma annot_reduce_int v n it T:
    (li_tactic (li_vm_compute Some n) (λ n', v ◁ᵥ n' @ int it -∗ T))
    ⊢ typed_annot_expr 1 (ReduceAnnot) v (v ◁ᵥ n @ int it) T.
  Proof.
    unfold li_tactic, li_vm_compute.
    iIntros "[%y [% HT]] Hv"; simplify_eq. iApply step_fupd_intro => //. iModIntro.
    by iApply "HT".
  Qed.
  Definition annot_reduce_int_inst := [instance annot_reduce_int].
  Global Existing Instance annot_reduce_int_inst.

End programs.
Global Typeclasses Opaque int_inner_type int.

Notation "'if' p ≠ 0 " := (TraceIfInt p) (at level 100, only printing).
(* Notation "'case' n " := (TraceSwitchIntCase n) (at level 100, only printing).
Notation "'default'" := (TraceSwitchIntDefault) (at level 100, only printing). *)

Section offsetof.
  Context `{!typeG Σ} {cs : compspecs}.

Check nested_field_offset.

  (*** OffsetOf *)
  Program Definition offsetof (s : members) (m : ident) : type := {|
    ty_has_op_type ot mt := ot = size_t;
    ty_own β l := ∃ n, <affine> ⌜in_members m s /\ field_offset _ m s = n⌝ ∗ l ◁ₗ{β} n @ int size_t;
    ty_own_val v := ∃ n, <affine> ⌜in_members m s /\ field_offset _ m s = n⌝ ∗ v ◁ᵥ n @ int size_t;
  |}%I.
  Next Obligation.
    iIntros (s m l E ?). iDestruct 1 as (n Hn) "H". iExists _. iSplitR => //. by iApply ty_share.
  Qed.
  Next Obligation. iIntros (s m ot mt l ?). iDestruct 1 as (??)"Hn". by iDestruct (ty_aligned with "Hn") as "$". Qed.
  Next Obligation.
    iIntros (s m ot mt l ?). iDestruct 1 as (??)"Hn".
    iDestruct (ty_deref with "Hn") as (v) "[Hl Hi]"; [done|]. iExists _. iFrame.
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (s m ? l v ???) "Hl". iDestruct 1 as (??)"Hn".
    iExists _. iSplit => //. by iApply (@ty_ref with "[] Hl").
  Qed.

  Global Program Instance offsetof_copyable s m : Copyable (offsetof s m).
  Next Obligation.
    iIntros (s m E l ?). iDestruct 1 as (n Hn) "Hl".
    iMod (copy_shr_acc with "Hl") as (???) "(Hl&H2&H3)" => //.
    iModIntro. iSplitR => //. iExists _, _. iFrame.
    iModIntro. done.
  Qed.

(*  Lemma type_offset_of s m T:
    ⌜Some m ∈ s.(sl_members).*1⌝ ∗ (∀ v, T v (offsetof s m))
    ⊢ typed_val_expr (OffsetOf s m) T.
  Proof.
    iIntros "[%Hin HT] %Φ HΦ". move: Hin => /offset_of_from_in [n Hn].
    iApply wp_offset_of => //. iIntros "%v %Hv". iApply "HΦ" => //.
    iExists _. iSplit; first done. unfold int; simpl_type. iPureIntro. by eapply val_to_of_Z.
  Qed. *)

End offsetof.
Global Typeclasses Opaque offsetof.

(*** Tests *)
Section tests.
  Context `{!typeG Σ} {cs : compspecs}.

  Definition Econst_size_t z := if Archi.ptr64 then Econst_long (Int64.repr z) size_t else Econst_int (Int.repr z) size_t .

  Example type_eq n1 n3 T:
    n1 ∈ size_t →
    n3 ∈ size_t →
    ⊢ typed_val_expr (Ebinop Oeq (Ebinop Oadd (Econst_size_t n1) (Econst_size_t 0) size_t) (Econst_size_t n3) tint) T.
  Proof.
    move => Hn1 Hn2.
    iApply type_bin_op.
    iApply type_bin_op.
    iApply type_val. iApply type_val_int. iSplit => //.
    iApply type_val. iApply type_val_int. iSplit => //.
    iApply type_arithop_int_int => //. iIntros (??). iSplit. {
      iPureIntro. unfold int_arithop_sidecond, elem_of, int_elem_of_it, min_int, max_int in *; lia.
    }
    iApply type_val. iApply type_val_int. iSplit => //.
    iApply type_relop_int_int => //.
  Abort.
End tests.
