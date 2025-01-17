From VST.typing Require Export type.
From VST.typing Require Import programs.
From VST.typing Require Import type_options.

(** A [Strict] boolean can only have value 0 (false) or 1 (true). A [Relaxed]
    boolean can have any value: 0 means false, anything else means true. *)
Inductive bool_strictness := StrictBool | RelaxedBool.

Definition represents_boolean (stn: bool_strictness) (n: Z) (b: bool) : Prop :=
  match stn with
  | StrictBool => n = bool_to_Z b
  | RelaxedBool => bool_decide (n ≠ 0) = b
  end.

(* Not sure what this would correspond to.
Definition is_bool_ot (ot : op_type) (it : int_type) (stn : bool_strictness) : Prop:=
  match ot with
  | BoolOp => it = u8 ∧ stn = StrictBool
  | IntOp it' => it = it'
  | UntypedOp ly => ly = it_layout it
  | _ => False
  end.*)

Section is_bool_ot.
  Context `{!typeG Σ}.

  Lemma represents_boolean_eq stn n b :
    represents_boolean stn n b → bool_decide (n ≠ 0) = b.
  Proof.
    destruct stn => //=. move => ->. by destruct b.
  Qed.

(*  Lemma is_bool_ot_layout ot it stn:
    is_bool_ot ot it stn → ot_layout ot = it.
  Proof. destruct ot => //=; naive_solver. Qed.

  Lemma mem_cast_compat_bool (P : val → iProp Σ) v ot stn it st mt:
    is_bool_ot ot it stn →
    (P v ⊢ ⌜∃ n b, val_to_Z v it = Some n ∧ represents_boolean stn n b⌝) →
    (P v ⊢ match mt with | MCNone => True | MCCopy => P (mem_cast v ot st) | MCId => ⌜mem_cast_id v ot⌝ end).
  Proof.
    move => ? HT. apply: mem_cast_compat_Untyped => ?.
    apply: mem_cast_compat_id. etrans; [done|]. iPureIntro => -[?[?[??]]].
    destruct ot => //; simplify_eq/=; destruct_and?; simplify_eq/=.
    - apply: mem_cast_id_bool. by apply val_to_bool_iff_val_to_Z.
    - by apply: mem_cast_id_int.
  Qed.*)
End is_bool_ot.

Section generic_boolean.
  Context `{!typeG Σ} {cs : compspecs}.

  Program Definition generic_boolean_type (stn: bool_strictness) (it: Ctypes.type) (b: bool) : type := {|
    ty_has_op_type ot mt := (*is_bool_ot ot it stn*) ot = it;
    ty_own β l :=
      ∃ v n, ⌜val_to_Z v it = Some n⌝ ∧
             ⌜represents_boolean stn n b⌝ ∧
             ⌜field_compatible it [] l⌝ ∧
             l ↦_it[β] v;
      ty_own_val v := ∃ n, <affine> ⌜val_to_Z v it = Some n⌝ ∗ <affine> ⌜represents_boolean stn n b⌝;
  |}%I.
  Next Obligation.
    iIntros (??????) "(%v&%n&%&%&%&Hl)". iExists v, n.
    by iMod (heap_mapsto_own_state_share with "Hl") as "$".
  Qed.
  Next Obligation.
    iIntros (??????->) "(%&%&_&_&H&_)" => //.
  Qed.
  Next Obligation.
    iIntros (??????->) "(%&%&%)". iPureIntro. destruct v; try done.
    - rewrite /has_layout_val /tc_val' =>?. destruct it; try done.
  Admitted.
  Next Obligation.
    iIntros (??????->) "(%&%&%&%&%&?)". eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (?????? v -> ?) "Hl (%n&%&%)". iExists v, n; eauto with iFrame.
  Qed.
(*  Next Obligation.
    iIntros (????????). apply: mem_cast_compat_bool; [naive_solver|]. iPureIntro. naive_solver.
  Qed.*)

  Definition generic_boolean (stn: bool_strictness) (it: Ctypes.type) : rtype _ :=
    RType (generic_boolean_type stn it).

  Global Program Instance generic_boolean_copyable b stn it : Copyable (b @ generic_boolean stn it).
  Next Obligation.
    iIntros (????????) "(%v&%n&%&%&%&Hl)".
    simpl in *; subst.
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[_ Hl]" => //.
    iSplitR; first done; iExists q, v; eauto 8 with iFrame.
  Qed.

(*  Global Instance alloc_alive_generic_boolean b stn it β: AllocAlive (b @ generic_boolean stn it) β True.
  Proof.
    constructor. iIntros (l ?) "(%&%&%&%&%&Hl)".
    iApply (heap_mapsto_own_state_alloc with "Hl").
    erewrite val_to_Z_length; [|done]. have := bytes_per_int_gt_0 it. lia.
  Qed.*)

  Global Instance generic_boolean_timeless l b stn it:
    Timeless (l ◁ₗ b @ generic_boolean stn it)%I.
  Proof. apply _. Qed.

End generic_boolean.
Notation "generic_boolean< stn , it >" := (generic_boolean stn it)
  (only printing, format "'generic_boolean<' stn ',' it '>'") : printing_sugar.

Notation boolean := (generic_boolean StrictBool).
Notation "boolean< it >" := (boolean it)
  (only printing, format "'boolean<' it '>'") : printing_sugar.

(* Type corresponding to [_Bool] (https://en.cppreference.com/w/c/types/boolean). *)
Notation u8 := (Tint I8 Unsigned noattr).
Notation builtin_boolean := (generic_boolean StrictBool u8).

Section generic_boolean.
  Context `{!typeG Σ} {cs : compspecs}.

  Inductive trace_if_bool :=
  | TraceIfBool (b : bool).

  Lemma type_if_generic_boolean stn it (b : bool) v T1 T2 :
     case_destruct b (λ b' _,
     li_trace (TraceIfBool b, b') (if b' then T1 else T2))
    ⊢ typed_if it v (v ◁ᵥ b @ generic_boolean stn it) T1 T2.
  Proof.
    unfold case_destruct, li_trace. iIntros "[% Hs] (%n&%Hv&%Hb)".
    apply represents_boolean_eq in Hb as <-.
    destruct it, v; try discriminate; eauto.
  Qed.
  Definition type_if_generic_boolean_inst := [instance type_if_generic_boolean].
  Global Existing Instance type_if_generic_boolean_inst.

(*  Lemma type_assert_generic_boolean v stn it (b : bool) s fn ls R Q :
    (<affine> ⌜b⌝ ∗ typed_stmt s fn ls R Q)
    ⊢ typed_assert it v (v ◁ᵥ b @ generic_boolean stn it) s fn ls R Q.
  Proof.
    iIntros "[% [% ?]] (%n&%&%Hb)". destruct b; last by exfalso.
    destruct ot; destruct_and? => //; simplify_eq/=.
    - iExists true. iFrame. iPureIntro. split; [|done]. by apply val_to_bool_iff_val_to_Z.
    - iExists n. iFrame. iSplit; first done. iPureIntro.
      by apply represents_boolean_eq, bool_decide_eq_true in Hb.
  Qed.
  Definition type_assert_generic_boolean_inst := [instance type_assert_generic_boolean].
  Global Existing Instance type_assert_generic_boolean_inst.*)
End generic_boolean.

Section boolean.
  Context `{!typeG Σ} {cs : compspecs}.

  Lemma type_relop_boolean b1 b2 op b it v1 v2
    (Hop : match op with
           | Oeq => Some (eqb b1 b2)
           | One => Some (negb (eqb b1 b2))
           | _ => None
           end = Some b) T:
    T (i2v (bool_to_Z b) tint) (b @ boolean tint)
    ⊢ typed_bin_op v1 ⎡v1 ◁ᵥ b1 @ boolean it⎤
                 v2 ⎡v2 ◁ᵥ b2 @ boolean it⎤ op it it T.
  Proof.
    iIntros "HT (%n1&%Hv1&%Hb1) (%n2&%Hv2&%Hb2) %Φ HΦ".
    rewrite /wp_binop.
    iIntros (?) "$".
    iExists (i2v (bool_to_Z b) tint); iSplit.
    - iStopProof; split => rho; monPred.unseal.
      apply bi.pure_intro.
      assert (classify_cmp it it = cmp_default) as Hclass.
      { destruct it; try by destruct v1.
        by destruct i. }
      rewrite -val_of_bool_eq.
      assert (eqb b1 b2 = int_eq v1 v2) as Heq.
      { destruct it, v1; try done; destruct v2; try done; simpl in *.
        * pose proof (Int.eq_spec i0 i1) as Heq.
          destruct (Int.eq i0 i1).
          -- subst; destruct s; inv Hv1; destruct b1, b2; simpl in *; congruence.
          -- destruct s; inv Hv1; destruct (eqb_spec b1 b2); try done; subst.
             ++ exploit (signed_inj i0 i1); congruence.
             ++ if_tac in H0; inv H0.
                if_tac in Hv2; inv Hv2.
                exploit (unsigned_eq_eq i0 i1); congruence.
        * pose proof (Int64.eq_spec i i0) as Heq.
          destruct (Int64.eq i i0).
          -- subst; destruct s; inv Hv1; destruct b1, b2; simpl in *; congruence.
          -- destruct s; inv Hv1; destruct b1, b2; try done;
               by (exploit (signed_inj_64 i i0); congruence || exploit (unsigned_inj_64 i i0); congruence). }
      destruct op; inv Hop; rewrite /= /Cop.sem_cmp Hclass /Cop.sem_binarith Heq.
      + destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
      + destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
    - iApply "HΦ"; last done. iExists (bool_to_Z b).
      iSplit; [by destruct b | done].
  Qed.
  Definition type_eq_boolean_inst b1 b2 :=
    [instance type_relop_boolean b1 b2 Oeq (eqb b1 b2)].
  Global Existing Instance type_eq_boolean_inst.
  Definition type_ne_boolean_inst b1 b2 :=
    [instance type_relop_boolean b1 b2 One (negb (eqb b1 b2))].
  Global Existing Instance type_ne_boolean_inst.

(*  (* TODO: replace this with a typed_cas once it is refactored to take E as an argument. *)
  Lemma wp_cas_suc_boolean it ot b1 b2 bd l1 l2 vd Φ E:
    ((ot_layout ot).(ly_size) ≤ bytes_per_addr)%nat →
    match ot with | BoolOp => it = u8 | IntOp it' => it = it' | _ => False end →
    b1 = b2 →
    l1 ◁ₗ b1 @ boolean it -∗
    l2 ◁ₗ b2 @ boolean it -∗
    vd ◁ᵥ bd @ boolean it -∗
    ▷ (l1 ◁ₗ bd @ boolean it -∗ l2 ◁ₗ b2 @ boolean it -∗ Φ (val_of_bool true)) -∗
    wp NotStuck E (CAS ot (Val l1) (Val l2) (Val vd)) Φ.
  Proof.
    iIntros (? Hot ->) "(%v1&%n1&%&%&%&Hl1) (%v2&%n2&%&%&%&Hl2) (%n&%&%) HΦ/=".
    iApply (wp_cas_suc with "Hl1 Hl2").
    { by apply val_to_of_loc. }
    { by apply val_to_of_loc. }
    { by destruct ot; simplify_eq. }
    { by destruct ot; simplify_eq. }
    { apply: val_to_Z_ot_to_Z; [done|]. destruct ot; naive_solver. }
    { apply: val_to_Z_ot_to_Z; [done|]. destruct ot; naive_solver. }
    { etrans; [by eapply val_to_Z_length|]. by destruct ot; simplify_eq. }
    { by simplify_eq/=. }
    { by simplify_eq/=. }
    iIntros "!# Hl1 Hl2". iApply ("HΦ" with "[Hl1] [Hl2]"); iExists _, _; by iFrame.
  Qed.

  Lemma wp_cas_fail_boolean ot it b1 b2 bd l1 l2 vd Φ E:
    ((ot_layout ot).(ly_size) ≤ bytes_per_addr)%nat →
    match ot with | BoolOp => it = u8 | IntOp it' => it = it' | _ => False end →
    b1 ≠ b2 →
    l1 ◁ₗ b1 @ boolean it -∗ l2 ◁ₗ b2 @ boolean it -∗ vd ◁ᵥ bd @ boolean it -∗
    ▷ (l1 ◁ₗ b1 @ boolean it -∗ l2 ◁ₗ b1 @ boolean it -∗ Φ (val_of_bool false)) -∗
    wp NotStuck E (CAS ot (Val l1) (Val l2) (Val vd)) Φ.
  Proof.
    iIntros (? Hot ?) "(%v1&%n1&%&%&%&Hl1) (%v2&%n2&%&%&%&Hl2) (%n&%&%) HΦ/=".
    iApply (wp_cas_fail with "Hl1 Hl2").
    { by apply val_to_of_loc. }
    { by apply val_to_of_loc. }
    { by destruct ot; simplify_eq. }
    { by destruct ot; simplify_eq. }
    { apply: val_to_Z_ot_to_Z; [done|]. destruct ot; naive_solver. }
    { apply: val_to_Z_ot_to_Z; [done|]. destruct ot; naive_solver. }
    { etrans; [by eapply val_to_Z_length|]. by destruct ot; simplify_eq. }
    { by simplify_eq/=. }
    { simplify_eq/=. by destruct b1, b2. }
    iIntros "!# Hl1 Hl2". iApply ("HΦ" with "[Hl1] [Hl2]"); iExists _, _; by iFrame.
  Qed.

  Lemma type_cast_boolean b it1 it2 v T:
    (∀ v, T v (b @ boolean it2))
    ⊢ typed_un_op v (v ◁ᵥ b @ boolean it1)%I (CastOp (IntOp it2)) (IntOp it1) T.
  Proof.
    iIntros "HT (%n&%Hv&%Hb) %Φ HΦ". move: Hb => /= ?. subst n.
    have [??] := val_of_Z_bool_is_Some (val_to_byte_prov v) it2 b.
    iApply wp_cast_int => //. iApply ("HΦ" with "[] HT") => //.
    iExists _. iSplit; last done. iPureIntro. by eapply val_to_of_Z.
  Qed.
  Definition type_cast_boolean_inst := [instance type_cast_boolean].
  Global Existing Instance type_cast_boolean_inst.*)

End boolean.

Notation "'if' p " := (TraceIfBool p) (at level 100, only printing).

Section builtin_boolean.
  Context `{!typeG Σ} {cs : compspecs}.

  Lemma type_val_builtin_boolean b T:
    (T (b @ builtin_boolean)) ⊢ typed_value (Val.of_bool b) T.
  Proof.
    iIntros "HT". iExists _. iFrame. iPureIntro. exists (if b then 1 else 0); destruct b; simpl; auto.
  Qed.
  Definition type_val_builtin_boolean_inst := [instance type_val_builtin_boolean].
  Global Existing Instance type_val_builtin_boolean_inst.

(*  Lemma type_cast_boolean_builtin_boolean b it v T:
    (∀ v, T v (b @ builtin_boolean))
    ⊢ typed_un_op v (v ◁ᵥ b @ boolean it)%I (CastOp BoolOp) (IntOp it) T.
  Proof.
    iIntros "HT (%n&%Hv&%Hb) %Φ HΦ". move: Hb => /= ?. subst n.
    iApply wp_cast_int_bool => //. iApply ("HΦ" with "[] HT") => //.
    iPureIntro => /=. exists (bool_to_Z b). by destruct b.
  Qed.
  Definition type_cast_boolean_builtin_boolean_inst := [instance type_cast_boolean_builtin_boolean].
  Global Existing Instance type_cast_boolean_builtin_boolean_inst.

  Lemma type_cast_builtin_boolean_boolean b it v T:
    (∀ v, T v (b @ boolean it))
    ⊢ typed_un_op v (v ◁ᵥ b @ builtin_boolean)%I (CastOp (IntOp it)) BoolOp T.
  Proof.
    iIntros "HT (%n&%Hv&%Hb) %Φ HΦ". move: Hb => /= ?. subst n.
    have [??] := val_of_Z_bool_is_Some None it b.
    iApply wp_cast_bool_int => //. { by apply val_to_bool_iff_val_to_Z. }
    iApply ("HΦ" with "[] HT") => //.
    iPureIntro => /=. eexists _. split;[|done]. by apply: val_to_of_Z.
  Qed.
  Definition type_cast_builtin_boolean_boolean_inst := [instance type_cast_builtin_boolean_boolean].
  Global Existing Instance type_cast_builtin_boolean_boolean_inst.*)

End builtin_boolean.
Global Typeclasses Opaque generic_boolean_type generic_boolean.
