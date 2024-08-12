From VST.typing Require Export type.
From VST.typing Require Import programs boolean.
From VST.typing Require Import type_options.

Open Scope Z.

Lemma bitsize_small : forall sz, sz ≠ I32 -> Z.pow 2 (bitsize_intsize sz) ≤ Int.half_modulus.
Proof.
  destruct sz; simpl; first [rep_lia | contradiction].
Qed.

Definition is_signed t :=
  match t with
  | Tint _ Signed _ | Tlong Signed _ => true
  | _ => false
  end.

Definition min_int t :=
  match t with
  | Tint _ Signed _ => Int.min_signed
  | Tlong Signed _ => Int64.min_signed
  | _ => 0
  end.

Definition int_size t :=
  match t with
  | Tint sz _ _ => bitsize_intsize sz
  | Tlong _ _ => 64
  | _ => 0
  end.

Lemma bitsize_wordsize : forall sz, bitsize_intsize sz <= Int.zwordsize.
Proof.
  destruct sz; simpl; rep_lia.
Qed.

(* assuming n ∈ it; see also https://gitlab.mpi-sws.org/iris/refinedc/-/blob/master/theories/caesium/lifting.v?ref_type=heads#L555 *)
Definition int_arithop_sidecond (it : Ctypes.type) (n1 n2 n : Z) op : Prop :=
  match op with
  | Oshl => 0 ≤ n2 < int_size it ∧ 0 ≤ n1
  | Oshr => 0 ≤ n2 < int_size it ∧ 0 ≤ n1 (* Result of shifting negative numbers is implementation defined. *)
  | Odiv => n2 ≠ 0
  | Omod => n2 ≠ 0 ∧ ¬(n1 = min_int it ∧ n2 = -1)(* divergence from Caesium: according to https://en.cppreference.com/w/c/language/operator_arithmetic,
                               INT_MIN%-1 is undefined *)
  | _     => True
  end.

Lemma testbit_add_over: forall x n m, 0 <= n < m ->
  Z.testbit (x + 2^m) n = Z.testbit x n.
Proof.
  intros.
  rewrite !Z.testbit_eqb; [|lia..].
  replace m with ((m - n) + n) by lia.
  rewrite Z.pow_add_r; [|lia..].
  rewrite Z.div_add; last lia.
  rewrite Z.add_mod // Zpow_facts.Zpower_mod // Z_mod_same_full Zplus_mod_idemp_l Z.pow_0_l; lia.
Qed.

Lemma testbit_unsigned_signed: forall x n, 0 <= n < Z.of_nat Int.wordsize ->
  Z.testbit (Int.unsigned x) n = Z.testbit (Int.signed x) n.
Proof.
  intros.
  rewrite Int.unsigned_signed /Int.lt; if_tac; last done.
  rewrite /Int.modulus two_power_nat_equiv testbit_add_over //.
Qed.

Lemma testbit_unsigned_signed_64: forall x n, 0 <= n < Z.of_nat Int64.wordsize ->
  Z.testbit (Int64.unsigned x) n = Z.testbit (Int64.signed x) n.
Proof.
  intros.
  rewrite Int64.unsigned_signed /Int64.lt; if_tac; last done.
  rewrite /Int64.modulus two_power_nat_equiv testbit_add_over //.
Qed.

Lemma and_signed:
  forall x y, Int.and x y = Int.repr (Z.land (Int.signed x) (Int.signed y)).
Proof.
  intros; unfold Int.and. apply Int.eqm_samerepr, Zbits.eqmod_same_bits; intros.
  rewrite !Z.land_spec !testbit_unsigned_signed //.
Qed.

Lemma or_signed:
  forall x y, Int.or x y = Int.repr (Z.lor (Int.signed x) (Int.signed y)).
Proof.
  intros; unfold Int.or. apply Int.eqm_samerepr, Zbits.eqmod_same_bits; intros.
  rewrite !Z.lor_spec !testbit_unsigned_signed //.
Qed.

Lemma xor_signed:
  forall x y, Int.xor x y = Int.repr (Z.lxor (Int.signed x) (Int.signed y)).
Proof.
  intros; unfold Int.xor. apply Int.eqm_samerepr, Zbits.eqmod_same_bits; intros.
  rewrite !Z.lxor_spec !testbit_unsigned_signed //.
Qed.

Lemma and_signed_64:
  forall x y, Int64.and x y = Int64.repr (Z.land (Int64.signed x) (Int64.signed y)).
Proof.
  intros; unfold Int64.and. apply Int64.eqm_samerepr, Zbits.eqmod_same_bits; intros.
  rewrite !Z.land_spec !testbit_unsigned_signed_64 //.
Qed.

Lemma or_signed_64:
  forall x y, Int64.or x y = Int64.repr (Z.lor (Int64.signed x) (Int64.signed y)).
Proof.
  intros; unfold Int64.or. apply Int64.eqm_samerepr, Zbits.eqmod_same_bits; intros.
  rewrite !Z.lor_spec !testbit_unsigned_signed_64 //.
Qed.

Lemma xor_signed_64:
  forall x y, Int64.xor x y = Int64.repr (Z.lxor (Int64.signed x) (Int64.signed y)).
Proof.
  intros; unfold Int64.xor. apply Int64.eqm_samerepr, Zbits.eqmod_same_bits; intros.
  rewrite !Z.lxor_spec !testbit_unsigned_signed_64 //.
Qed.

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

Definition unsigned_op sz sg :=
  match sz, sg with
  | I32, Unsigned => true
  | _, _ => false
  end.

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

  Lemma type_val_int_i32 (n:Integers.int) T :
    typed_value (Vint n) T :-
      exhale (<affine> ⌜(Int.signed n) ∈ tint⌝);
      return T ((Int.signed n) @ (int tint)).
  Proof.
    iIntros "[%Hn HT]".
    iExists _. iFrame. by iPureIntro.
  Qed.
  Definition type_val_int_i32_inst := [instance type_val_int_i32].
  Global Existing Instance type_val_int_i32_inst.

  Lemma Int_modulus_Z_pow_pos : Int.modulus = Z.pow_pos 2 32.
  Proof.
    rep_lia.
  Qed.

  (** Ke: TODO this rule should have a different triggering condition *)
  (* Lemma type_val_int_u32 (n:Integers.int) T :
    typed_value (Vint n) T :-
      exhale (<affine> ⌜(Int.unsigned n) ∈ tuint⌝);
      return T ((Int.unsigned n) @ (int tuint)).
  Proof.
    iIntros "[%Hn HT]".
    iExists _. iFrame.  iPureIntro. simpl.
    rewrite -Int_modulus_Z_pow_pos.
    pose proof (Int.unsigned_range n).
    erewrite zlt_true. -done. - lia.
  Qed.

  Definition type_val_int_u32_inst := [instance type_val_int_u32].
  Global Existing Instance type_val_int_u32_inst. *)

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
    iIntros (?) "$".
    iExists (i2v (bool_to_Z b) tint); iSplit.
    - iStopProof; split => rho; monPred.unseal.
      apply bi.pure_intro.
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
            -- destruct s; inv Hv1; case_bool_decide; try done.
               ++ exploit (signed_inj i0 i1); congruence.
               ++ if_tac in H0; inv H0.
                if_tac in Hv2; inv Hv2.
                exploit (unsigned_eq_eq i0 i1); congruence.
          * pose proof (Int64.eq_spec i i0) as Heq.
            destruct (Int64.eq i i0).
            -- subst; destruct s; inv Hv1; case_bool_decide; simpl in *; congruence.
            -- destruct s; inv Hv1; case_bool_decide; try done;
                 by (exploit (signed_inj_64 i i0); congruence || exploit (unsigned_inj_64 i i0); congruence). }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
      + assert (bool_decide (n1 ≠ n2) = negb (int_eq v1 v2)) as ->.
        { destruct it, v1; try done; destruct v2; try done; simpl in *.
          * pose proof (Int.eq_spec i0 i1) as Heq.
            destruct (Int.eq i0 i1).
            -- subst; destruct s; inv Hv1; case_bool_decide; simpl in *; congruence.
            -- destruct s; inv Hv1; case_bool_decide; try done.
               ++ exploit (signed_inj i0 i1); congruence.
               ++ if_tac in H0; inv H0.
                if_tac in Hv2; inv Hv2.
                exploit (unsigned_eq_eq i0 i1); congruence.
          * pose proof (Int64.eq_spec i i0) as Heq.
            destruct (Int64.eq i i0).
            -- subst; destruct s; inv Hv1; case_bool_decide; simpl in *; congruence.
            -- destruct s; inv Hv1; case_bool_decide; try done;
                 by (exploit (signed_inj_64 i i0); congruence || exploit (unsigned_inj_64 i i0); congruence). }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
      + assert (bool_decide (n1 < n2) = int_lt it v1 v2) as ->.
        { destruct it, v1; try done; destruct v2; try done; simpl in *.
          * destruct (unsigned_op i s) eqn: Hs.
            -- destruct i; try done; destruct s; inv Hv1.
               if_tac in H0; inv H0.
               if_tac in Hv2; inv Hv2.
               rewrite /Int.ltu; if_tac; case_bool_decide; done.
            -- trans (Int.lt i0 i1); last by destruct i, s.
               destruct s; inv Hv1; rewrite /Int.lt; try by if_tac; case_bool_decide.
               if_tac in H0; inv H0.
               if_tac in Hv2; inv Hv2.
               lapply (bitsize_small i); last by intros ->.
               intros; rewrite !Int.signed_eq_unsigned; [if_tac; case_bool_decide; done | rep_lia..].
          * destruct s; inv Hv1.
            -- rewrite /Int64.lt; if_tac; case_bool_decide; done.
            -- rewrite /Int64.ltu; if_tac; case_bool_decide; done. }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
      + assert (bool_decide (n1 > n2) = int_lt it v2 v1) as ->.
        { destruct it, v1; try done; destruct v2; try done; simpl in *.
          * destruct (unsigned_op i s) eqn: Hs.
            -- destruct i; try done; destruct s; inv Hv1.
               if_tac in H0; inv H0.
               if_tac in Hv2; inv Hv2.
               rewrite /Int.ltu; if_tac; case_bool_decide; lia.
            -- trans (Int.lt i1 i0); last by destruct i, s.
               destruct s; inv Hv1; rewrite /Int.lt; try by if_tac; case_bool_decide; lia.
               if_tac in H0; inv H0.
               if_tac in Hv2; inv Hv2.
               lapply (bitsize_small i); last by intros ->.
               intros; rewrite !Int.signed_eq_unsigned; [if_tac; case_bool_decide; lia | rep_lia..].
          * destruct s; inv Hv1.
            -- rewrite /Int64.lt; if_tac; case_bool_decide; lia.
            -- rewrite /Int64.ltu; if_tac; case_bool_decide; lia. }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
      + assert (bool_decide (n1 ≤ n2) = negb (int_lt it v2 v1)) as ->.
        { destruct it, v1; try done; destruct v2; try done; simpl in *.
          * destruct (unsigned_op i s) eqn: Hs.
            -- destruct i; try done; destruct s; inv Hv1.
               if_tac in H0; inv H0.
               if_tac in Hv2; inv Hv2.
               rewrite /Int.ltu; if_tac; case_bool_decide; lia.
            -- trans (negb (Int.lt i1 i0)); last by destruct i, s.
               destruct s; inv Hv1; rewrite /Int.lt; try by if_tac; case_bool_decide; lia.
               if_tac in H0; inv H0.
               if_tac in Hv2; inv Hv2.
               lapply (bitsize_small i); last by intros ->.
               intros; rewrite !Int.signed_eq_unsigned; [if_tac; case_bool_decide; lia | rep_lia..].
          * destruct s; inv Hv1.
            -- rewrite /Int64.lt; if_tac; case_bool_decide; lia.
            -- rewrite /Int64.ltu; if_tac; case_bool_decide; lia. }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
      + assert (bool_decide (n1 >= n2) = negb (int_lt it v1 v2)) as ->.
        { destruct it, v1; try done; destruct v2; try done; simpl in *.
          * destruct (unsigned_op i s) eqn: Hs.
            -- destruct i; try done; destruct s; inv Hv1.
               if_tac in H0; inv H0.
               if_tac in Hv2; inv Hv2.
               rewrite /Int.ltu; if_tac; case_bool_decide; lia.
            -- trans (negb (Int.lt i0 i1)); last by destruct i, s.
               destruct s; inv Hv1; rewrite /Int.lt; try by if_tac; case_bool_decide; lia.
               if_tac in H0; inv H0.
               if_tac in Hv2; inv Hv2.
               lapply (bitsize_small i); last by intros ->.
               intros; rewrite !Int.signed_eq_unsigned; [if_tac; case_bool_decide; lia | rep_lia..].
          * destruct s; inv Hv1.
            -- rewrite /Int64.lt; if_tac; case_bool_decide; lia.
            -- rewrite /Int64.ltu; if_tac; case_bool_decide; lia. }
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
    (Hop : match op with
    | Oadd => Some (n1 + n2)
    | Osub => Some (n1 - n2)
    | Omul => Some (n1 * n2)
    | Odiv => Some (n1 `quot` n2)
    | Omod => Some (n1 `rem` n2)
    | Oand => Some (Z.land n1 n2)
    | Oor => Some (Z.lor n1 n2)
    | Oxor => Some (Z.lxor n1 n2)
    | Oshl => Some (n1 ≪ n2)
    | Oshr => Some (n1 ≫ n2)
    | _ => None
    end = Some n) T :
    (<affine> ⌜n1 ∈ it⌝ -∗ <affine> ⌜n2 ∈ it⌝ -∗ <affine> ⌜in_range n it ∧ int_arithop_sidecond it n1 n2 n op⌝ ∗ T (i2v n it) (n @ int it))
    ⊢ typed_bin_op v1 ⎡v1 ◁ᵥ n1 @ int it⎤ v2 ⎡v2 ◁ᵥ n2 @ int it⎤ op it it T.
  Proof.
    iIntros "HT %Hv1 %Hv2 %Φ HΦ".
    iDestruct ("HT" with "[] []" ) as ((Hin & Hsc)) "HT".
    1-2: iPureIntro; by apply: val_to_Z_in_range.
    rewrite /wp_binop.
    iIntros (?) "$".
    iExists (i2v n it); iSplit.
    - iStopProof; split => rho; monPred.unseal.
      apply bi.pure_intro.
      destruct op; inv Hop; rewrite /=.
      + rewrite /Cop.sem_add.
        replace (classify_add it it) with add_default by (destruct it; try done; destruct i; done).
        rewrite /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1.
                rewrite Int.add_signed //.
             ++ if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- rewrite Int64.add_signed //.
          -- done.
      + rewrite /Cop.sem_sub.
        replace (classify_sub it it) with sub_default by (destruct it, v1; try done; destruct i; done).
        rewrite /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1.
                rewrite Int.sub_signed //.
             ++ if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- rewrite Int64.sub_signed //.
          -- done.
      + rewrite /Cop.sem_mul /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1.
                rewrite Int.mul_signed //.
             ++ if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- rewrite Int64.mul_signed //.
          -- done.
      + rewrite /Cop.sem_div /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2.
             rewrite /Int.eq; if_tac.
             { rewrite Int.unsigned_zero in H1; tauto. }
             rewrite /Int.divu Zquot.Zquot_Zdiv_pos //; rep_lia.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             rewrite /Int.eq; if_tac; simpl.
             { apply unsigned_eq_eq in H; subst; rewrite Int.signed_zero Int.unsigned_zero in Hv2.
               destruct s; [|if_tac in Hv2]; inv Hv2; tauto. }
             destruct (_ && _) eqn: Hm.
             { repeat (if_tac in Hm; try done).
               apply unsigned_eq_eq in H1; apply unsigned_eq_eq in H0; subst.
               inv Hin.
               ** rewrite Int.signed_mone Int.signed_repr in H1; rep_lia.
               ** rewrite Int.unsigned_mone in Hv2; if_tac in Hv2; inv Hv2.
                  lapply (bitsize_small i); last by intros ->. intros; rep_lia. }
             destruct s.
             ++ inv Hv1; done.
             ++ if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2.
                rewrite /Int.divs.
                lapply (bitsize_small i); last by intros ->. intros.
                rewrite !Int.signed_eq_unsigned //; rep_lia.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- rewrite /Int64.eq; if_tac.
             { apply unsigned_inj_64 in H; subst; rewrite Int64.signed_zero in Hsc; tauto. }
             destruct (_ && _) eqn: Hm.
             { repeat (if_tac in Hm; try done).
               apply unsigned_inj_64 in H1; apply unsigned_inj_64 in H0; subst.
               inv Hin.
               rewrite Int64.signed_mone Int64.signed_repr in H1; rep_lia. }
             done.
          -- rewrite /Int64.eq; if_tac.
             { apply unsigned_inj_64 in H; subst; rewrite Int64.unsigned_zero in Hsc; tauto. }
             rewrite /Int.divu Zquot.Zquot_Zdiv_pos //; rep_lia.
      + rewrite /Cop.sem_mod /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2.
             rewrite /Int.eq; if_tac.
             { rewrite Int.unsigned_zero in H1; tauto. }
             rewrite /Int.modu Zquot.Zrem_Zmod_pos //; rep_lia.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             rewrite /Int.eq; if_tac; simpl.
             { apply unsigned_eq_eq in H; subst; rewrite Int.signed_zero Int.unsigned_zero in Hv2.
               destruct s; [|if_tac in Hv2]; inv Hv2; tauto. }
             destruct (_ && _) eqn: Hm.
             { repeat (if_tac in Hm; try done).
               apply unsigned_eq_eq in H1; apply unsigned_eq_eq in H0; subst.
               inv Hin.
               ** rewrite Int.signed_mone Int.signed_repr in Hsc; rep_lia.
               ** rewrite Int.unsigned_mone in Hv2; if_tac in Hv2; inv Hv2.
                  lapply (bitsize_small i); last by intros ->. intros; rep_lia. }
             destruct s.
             ++ inv Hv1; done.
             ++ if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2.
                rewrite /Int.mods.
                lapply (bitsize_small i); last by intros ->. intros.
                rewrite !Int.signed_eq_unsigned //; rep_lia.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- rewrite /Int64.eq; if_tac.
             { apply unsigned_inj_64 in H; subst; rewrite Int64.signed_zero in Hsc; tauto. }
             destruct (_ && _) eqn: Hm.
             { repeat (if_tac in Hm; try done).
               apply unsigned_inj_64 in H1; apply unsigned_inj_64 in H0; subst.
               rewrite Int64.signed_mone Int64.signed_repr in Hsc; rep_lia. }
             done.
          -- rewrite /Int64.eq; if_tac.
             { apply unsigned_inj_64 in H; subst; rewrite Int64.unsigned_zero in Hsc; tauto. }
             rewrite /Int.modu Zquot.Zrem_Zmod_pos //; rep_lia.
      + rewrite /Cop.sem_and /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1.
                rewrite and_signed //.
             ++ if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- rewrite and_signed_64 //.
          -- done.
      + rewrite /Cop.sem_or /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1.
                rewrite or_signed //.
             ++ if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- rewrite or_signed_64 //.
          -- done.
      + rewrite /Cop.sem_xor /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1.
                rewrite xor_signed //.
             ++ if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- rewrite xor_signed_64 //.
          -- done.
      + rewrite /Cop.sem_shl /Cop.sem_shift; destruct it, v1; try done; destruct v2; try done.
        * assert (n1 = Int.unsigned i0) as ->.
          { destruct s; simpl in *.
            ** inv Hv1. apply Int.signed_eq_unsigned, Int.signed_positive; lia.
            ** if_tac in Hv1; inv Hv1; done. }
          assert (n2 = Int.unsigned i1) as ->.
          { destruct s; simpl in *.
            ** inv Hv2. apply Int.signed_eq_unsigned, Int.signed_positive; lia.
            ** if_tac in Hv2; inv Hv2; done. }
          rewrite /Int.ltu; if_tac.
          2: { rewrite Int.unsigned_repr_wordsize in H; simpl in *.
               pose proof (bitsize_wordsize i); rep_lia. }
          destruct i, s; done.
        * simpl in *.
          assert (n1 = Int64.unsigned i) as ->.
          { destruct s; inv Hv1; try done.
            apply Int64.signed_eq_unsigned, Int64.signed_positive; lia. }
          assert (n2 = Int64.unsigned i0) as ->.
          { destruct s; inv Hv2; try done.
            apply Int64.signed_eq_unsigned, Int64.signed_positive; lia. }
          rewrite /Int64.ltu; if_tac.
          2: { rewrite Int64.unsigned_repr_wordsize in H; simpl in *; rep_lia. }
          destruct i, s; done.
      + rewrite /Cop.sem_shr /Cop.sem_shift; destruct it, v1; try done; destruct v2; try done.
        * assert (n2 = Int.unsigned i1) as Heq.
          { destruct s; simpl in *.
            ** inv Hv2. apply Int.signed_eq_unsigned, Int.signed_positive; lia.
            ** if_tac in Hv2; inv Hv2; done. }
          rewrite /Int.ltu; if_tac.
          2: { rewrite Int.unsigned_repr_wordsize in H; simpl in *.
               pose proof (bitsize_wordsize i); rep_lia. }
          destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2; done.
          -- replace (classify_shift _ _) with (shift_case_ii Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1; done.
             ++ if_tac in Hv1; inv Hv1; if_tac in Hv2; inv Hv2.
                rewrite /Int.shr Int.signed_eq_unsigned //.
                { lapply (bitsize_small i); last by intros ->; intros.
                  rep_lia. }
        * simpl in *.
          assert (n2 = Int64.unsigned i0) as Heq.
          { destruct s; inv Hv2; try done.
            apply Int64.signed_eq_unsigned, Int64.signed_positive; lia. }
          rewrite /Int64.ltu; if_tac.
          2: { rewrite Int64.unsigned_repr_wordsize in H; simpl in *; rep_lia. }
          destruct s; inv Hv1; done.
    - iApply ("HΦ" with "[] HT").
      iPureIntro. by apply i2v_to_Z.
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
    iIntros "Hs %Hb".
    destruct it, v; try discriminate; iExists n; iSplit; auto;
      simpl; (case_bool_decide;
        [iDestruct "Hs" as "[Hs _]"; by iApply "Hs" | iDestruct "Hs" as "[_ Hs]"; iApply "Hs"; naive_solver]).
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
    (⌜n ∈ it⌝ -∗ <affine> ⌜is_signed it⌝ ∗ <affine> ⌜n ≠ min_int it⌝ ∗ T (i2v (-n) it) ((-n) @ int it))
    ⊢ typed_un_op v ⎡v ◁ᵥ n @ int it⎤%I Oneg it T.
  Proof.
    iIntros "HT %Hv %Φ HΦ". move: (Hv) => /val_to_Z_in_range Hin.
    iDestruct ("HT" with "[//]") as (Hs Hn) "HT".
    rewrite /wp_unop.
    iIntros (?) "$".
    iExists (i2v (- n) it); iSplit.
    - iStopProof; split => rho; monPred.unseal.
      apply bi.pure_intro.
      destruct it; try done; destruct s; try done; simpl in *.
      + rewrite /Cop.sem_neg.
        replace (classify_neg _) with (neg_case_i Signed) by (destruct i; done).
        destruct v; inv Hv.
        rewrite -Int.neg_repr Int.repr_signed //.
      + rewrite /Cop.sem_neg /=.
        destruct v; inv Hv.
        rewrite -Int64.neg_repr Int64.repr_signed //.
    - iApply "HΦ"; last done. iPureIntro. rewrite i2v_to_Z //.
      inv Hin; constructor; simpl in *; rep_lia.
  Qed.
  Definition type_neg_int_inst := [instance type_neg_int].
  Global Existing Instance type_neg_int_inst.

  Lemma wp_Ecast : forall e Φ ct, wp_expr e (λ v, ∃ v', ∀ m, <affine>⌜Some v' = Cop.sem_cast v (typeof e) ct m ⌝ ∗ Φ v')
    ⊢ wp_expr (Ecast e ct) Φ.
  Proof.
  intros.
  rewrite /wp_expr.
  iIntros "H" (?) "Hm".
  iDestruct ("H" with "Hm") as "(%v & H1 & Hm & %v' & H)".
  iDestruct ("H" $! m) as "[%Hcast HΦ]".
  iExists _; iFrame.
  iStopProof; split => rho; monPred.unseal.
  rewrite !monPred_at_affinely /local /lift1 /=.
  iIntros "%H1"; iPureIntro.
  split; auto; intros; econstructor; eauto.
  Qed.

(* Ke: the equivalent to Caesium's CastOp is Clight's Ecast, so use typed_val_expr *)
  Lemma type_Ecast_same_val e it2 T:
    typed_val_expr e (λ v ty,
      ∀ m (* Ke: for now only handle cases where m is irrelevant *),
        <affine>⌜Some v = Cop.sem_cast v (typeof e) it2 m⌝ ∗
        T v ty)
    ⊢ typed_val_expr (Ecast e it2) T.
  Proof.
    iIntros "typed %Φ HΦ".
    iApply wp_Ecast.
    unfold typed_val_expr.
    iApply "typed".
    iIntros (v ty) "own_v Hcast".
    iExists v. iIntros (m).
    iDestruct ("Hcast" $! m) as "(Hcast & T)". iFrame.
    iApply ("HΦ" with "[own_v]"); done.
  Qed.

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
    let n := if is_signed it then Z.lnot n1 else Z_lunot (int_size it) n1 in
    (⌜n1 ∈ it⌝ -∗ T (i2v n it) (n @ int it))
    ⊢ typed_un_op v1 ⎡v1 ◁ᵥ n1 @ int it⎤%I Onotint it T.
  Proof.
(*    iIntros "%n HT %Hv1 %Φ HΦ".
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
  Global Existing Instance type_not_int_inst. *) Abort.

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
    typed_bin_op v1 ⎡v1 ◁ᵥ (bool_to_Z b1) @ int it1⎤ v2 ⎡v2 ◁ᵥ n2 @ int it2⎤ op it3 it4 T
    ⊢ typed_bin_op v1 ⎡v1 ◁ᵥ b1 @ boolean it1⎤ v2 ⎡v2 ◁ᵥ n2 @ int it2⎤ op it3 it4 T.
  Proof.
    iIntros "HT H1 H2". iApply ("HT" with "[H1] H2"). unfold boolean; simpl_type.
    iDestruct "H1" as "(%&%H1&%H2)". iPureIntro.
    move: H1 H2 => /= -> ->. done.
  Qed.
  Definition type_binop_boolean_int_inst := [instance type_binop_boolean_int].
  Global Existing Instance type_binop_boolean_int_inst.

  Lemma type_binop_int_boolean it1 it2 it3 it4 v1 b1 v2 n2 op T:
    typed_bin_op v1 ⎡v1 ◁ᵥ n2 @ int it2⎤ v2 ⎡v2 ◁ᵥ (bool_to_Z b1) @ int it1⎤ op it3 it4 T
    ⊢ typed_bin_op v1 ⎡v1 ◁ᵥ n2 @ int it2⎤ v2 ⎡v2 ◁ᵥ b1 @ boolean it1⎤ op it3 it4 T.
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
  Definition Vsize_t z := if Archi.ptr64 then Vlong (Int64.repr z) else Vint (Int.repr z).

  Lemma type_const_size_t z T:
    typed_value (i2v z size_t) (T (i2v z size_t))
    ⊢ typed_val_expr (Econst_size_t z) T.
  Proof.
    rewrite /Econst_size_t /size_t; simple_if_tac; [apply type_const_long | apply type_const_int].
  Qed.

  Example type_eq n1 n3 T:
    n1 ∈ size_t →
    n3 ∈ size_t →
    ⊢ typed_val_expr (Ebinop Oeq (Ebinop Oadd (Econst_size_t n1) (Econst_size_t 0) size_t) (Econst_size_t n3) tint) T.
  Proof.
    move => Hn1 Hn2.
    iApply type_bin_op.
    iApply type_bin_op.
    iApply type_const_size_t. iApply type_val_int. iSplit => //.
    iApply type_const_size_t. iApply type_val_int. iSplit => //.
    { iPureIntro. rewrite /size_t; simple_if_tac; constructor; simpl; rep_lia. }
    iApply type_arithop_int_int => //. iIntros (??). iSplit. {
      iPureIntro. (*unfold int_arithop_sidecond, elem_of, int_elem_of_it, min_int, max_int in *; lia.*) rewrite Z.add_0_r //.
    }
    iApply type_const_size_t. iApply type_val_int. iSplit => //.
    iApply type_relop_int_int => //.
  Abort.
End tests.
