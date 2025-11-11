Set Warnings "-notation-overridden,-custom-entry-overridden,-hiding-delimiting-key".
From VST.typing Require Export type.
From VST.typing Require Import programs boolean.
Set Warnings "notation-overridden,custom-entry-overridden,hiding-delimiting-key".
From VST.typing Require Import type_options.

Open Scope Z.

Lemma bitsize_small : forall sz, sz ≠ I32 -> Z.pow 2 (bitsize_intsize sz) ≤ Int.half_modulus.
Proof.
  destruct sz; simpl; first [rep_lia | contradiction].
Qed.

Definition is_signed t :=
  match t with
  | Tint IBool _ _ => false (* no such thing as signed boolean *)
  | Tint _ Signed _ | Tlong Signed _ => true
  | _ => false
  end.

Definition int_size t :=
  match t with
  | Tint sz _ _ => bitsize_intsize sz
  | Tlong _ _ => 64
  | _ => 0
  end.

Definition min_int t :=
  match t with
  | Tint IBool _ _ => 0 (* no signed bool *)
  | Tint sz Signed _ => - Z.pow 2 (bitsize_intsize sz - 1)
  | Tlong Signed _ => Int64.min_signed
  | _ => 0
  end.

Definition max_int t :=
  match t with
  | Tint IBool _ _ => 1 (* no signed bool *)
  | Tint sz Signed _ => Z.pow 2 (bitsize_intsize sz - 1) - 1
  | Tint sz Unsigned _ => Z.pow 2 (bitsize_intsize sz) - 1
  | Tlong Signed _ => Int64.max_signed
  | Tlong Unsigned _ => Int64.max_unsigned
  | _ => -1
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
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (* Separate definition such that we can make it typeclasses opaque
  later. We cannot call it int_type since that already exists.  *)
  Program Definition int_inner_type (it : Ctypes.type) (n : Z) : type := {|
    ty_has_op_type ot mt := (*is_bool_ot ot it stn*) ot = it;
    ty_own β l := ∃ v, ⌜(valinject it v) `has_layout_val` it⌝ ∧
                       ⌜val_to_Z v it = Some n⌝ ∧
                       ⌜l `has_layout_loc` it⌝ ∧
                       l ↦[β]|it| (valinject it v);
    ty_own_val cty v := <affine> ⌜cty = it⌝ ∗
                        <affine> ⌜v `has_layout_val` cty⌝ ∗
                        <affine> ⌜val_to_Z (repinject cty v) cty = Some n⌝;
  |}%I.
  Next Obligation.
    iIntros (it n l ??) "(%v&%&%Hv&%Hl&H)". iExists v.
    by iMod (heap_mapsto_own_state_share with "H") as "$".
  Qed.
  Next Obligation. iIntros (????? ->) "(%&%&%&$&_)". Qed.
  Next Obligation. iIntros (????? -> (? & ? & ?)). done. Qed.
  Next Obligation. iIntros (????? ->) "(%v&%&%&%&Hl)". iFrame. 
    rewrite repinject_valinject //.
    by eapply val_to_Z_by_value. Qed.
  Next Obligation. iIntros (????? v -> ?) "Hl (% & % & %)".
    iExists (repinject it v). 
    rewrite /heap_mapsto_own_state.
    rewrite valinject_repinject //; last by eapply val_to_Z_by_value.
    iFrame. done. Qed.
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

  Global Instance int_defined it n: DefinedTy it (n @ int it).
  Proof.
    iIntros (?) "(_ & _ & %)".
    destruct it; try done; destruct v; try done.
  Qed.

  Lemma simplify_int it v n (T : assert):
    (<affine> ⌜v = valinject it (i2v n it)⌝ -∗
     <affine> ⌜n ∈ it⌝ -∗ T)
      ⊢ simplify_hyp ⎡v ◁ᵥ|it| n @ int it⎤ T.
  Proof.
    rewrite /simplify_hyp /ty_own_val_at /ty_own_val /=.
    iIntros "HT (_ & %H & %Hn)".
    destruct H as [Hv ?].
    iApply "HT"; iPureIntro.
    - destruct it; try done; unfold tc_val' in H;
      by apply val_to_Z_inv.
    - eapply val_to_Z_in_range; first done.
      rewrite value_fits_by_value // in Hv; by eapply val_to_Z_by_value.
  Qed.
  Definition simplify_int_inst := [instance simplify_int with 0%N].
  Global Existing Instance simplify_int_inst.

  Lemma simplify_goal_int_n it v n T `{Hv: !TCEq v (valinject it (i2v n it))}:
  (<affine> ⌜type_is_volatile it = false⌝ ∗ <affine> ⌜n ∈ it⌝ ∗ T)
    ⊢ simplify_goal (v ◁ᵥ|it| n @ int it) T.
  Proof.  iIntros "(% & %Hn & $)"; subst. inv Hv.
          iPureIntro; split3; auto.
          - destruct it; try done; rewrite /has_layout_val value_fits_by_value //.
            split; last done; intros ?; by apply in_range_i2v.
          - rewrite -(i2v_to_Z _ it) //; by destruct it.
  Qed.
  Definition simplify_goal_int_n_inst := [instance simplify_goal_int_n with 0%N].
  Global Existing Instance simplify_goal_int_n_inst.

  Lemma simplify_goal_int_n' it v n (T : assert) `{Hv: !TCEq v (valinject it (i2v n it))}:
    (<affine> ⌜type_is_volatile it = false⌝ ∗ <affine> ⌜n ∈ it⌝ ∗ T)
      ⊢ simplify_goal ⎡v ◁ᵥ|it| n @ int it⎤ T.
  Proof.  iIntros "(% & %Hn & $)"; subst. inv Hv.
          iPureIntro; split3; auto.
          - destruct it; try done; rewrite /has_layout_val value_fits_by_value //.
            split; last done; intros ?; by apply in_range_i2v.
          - rewrite -(i2v_to_Z _ it) //; by destruct it.
  Qed.
  Definition simplify_goal_int_n'_inst := [instance simplify_goal_int_n' with 0%N].
  Global Existing Instance simplify_goal_int_n'_inst.

  Lemma simplify_goal_int_unrefined it v T:
    (<affine> ⌜type_is_volatile it = false⌝ ∗ ∃ n, <affine> ⌜val_to_Z (repinject it v) it = Some n⌝ ∗ <affine> ⌜n ∈ it⌝ ∗ T)
      ⊢ simplify_goal (v ◁ᵥ|it| int it) T.
  Proof.  iIntros "(%H & %n & %Hv & %Hn & $)".
          iExists n.
          iPureIntro; split3; auto.
          destruct it; try done; destruct v; try done; rewrite /has_layout_val value_fits_by_value //.
          split; last done; intros ?.
          apply val_to_Z_inv in Hv as ->.
          by apply in_range_i2v.
  Qed.
  Definition simplify_goal_int_unrefined_inst := [instance simplify_goal_int_unrefined with 0%N].
  Global Existing Instance simplify_goal_int_unrefined_inst.

  Lemma simplify_goal_int_unrefined' it v (T : assert):
    (<affine> ⌜type_is_volatile it = false⌝ ∗ ∃ n, <affine> ⌜val_to_Z (repinject it v) it = Some n⌝ ∗ <affine> ⌜n ∈ it⌝ ∗ T)
      ⊢ simplify_goal ⎡v ◁ᵥ|it| int it⎤ T.
  Proof.  iIntros "(%H & %n & %Hv & %Hn & $)".
          iExists n.
          iPureIntro; split3; auto.
          destruct it; try done; destruct v; try done; rewrite /has_layout_val value_fits_by_value //.
          split; last done; intros ?.
          apply val_to_Z_inv in Hv as ->.
          by apply in_range_i2v.
  Qed.
  Definition simplify_goal_int_unrefined'_inst := [instance simplify_goal_int_unrefined' with 0%N].
  Global Existing Instance simplify_goal_int_unrefined'_inst.

  Lemma val_to_Z_not_Vundef it v n:
    val_to_Z v it = Some n -> v ≠ Vundef.
  Proof.
    intros.
    destruct v, it; done.
  Qed.

  Lemma has_layout_val_tc_val it v:
    v ≠ Vundef ->
    type_is_by_value it = true ->
    (valinject it v) `has_layout_val` it ->
    tc_val it v.
  Proof.
    intros.
    eapply has_layout_val_tc_val'2 in H1; eauto.
  Qed.

  Lemma ty_own_val_int_in_range v n it :
    v ◁ᵥₐₗ|it| n @ int it -∗ ⌜n ∈ it⌝.
  Proof.
    intros.
    iIntros "(% & % & %)".
    iPureIntro. eapply val_to_Z_in_range; try done.
    rewrite -> repinject_valinject in H1 |- *; [|by destruct it..].
    apply has_layout_val_tc_val'2; last done.
    eapply val_to_Z_by_value; done.
  Qed.

  Lemma ty_own_int_in_range l β n it :
    l ◁ₗ{β} n @ int it -∗ ⌜n ∈ it⌝.
  Proof.
    intros.
    iIntros "Hl". destruct β.
    - iDestruct (ty_deref _ _ MCNone with "Hl") as (?) "[_ (% & % & %)]"; [done|].
      iPureIntro. eapply val_to_Z_in_range; try done.
      pose proof (val_to_Z_by_value _ _ _ H1).
      apply has_layout_val_tc_val'2; try done.
      rewrite valinject_repinject //.
    - iDestruct "Hl" as (?) "(% & % & _)".
      iPureIntro. eapply val_to_Z_in_range; try done.
      apply has_layout_val_tc_val'2; try done.
      by eapply val_to_Z_by_value.
  Qed.

  (* TODO: make a simple type as in lambda rust such that we do not
  have to reprove this everytime? *)
  Global Program Instance int_copyable x it : Copyable it (x @ int it).
  Next Obligation.
    iIntros (?????) "(%v&%Hv&%&%Hl&Hl)".
    simpl in *; subst.
    iMod (heap_mapsto_own_state_to_mt with "Hl") as (q) "[% [% Hl]]" => //.
    iSplitR => //. iExists q, (valinject it v). iFrame. iModIntro.
    destruct Hv.
    apply val_to_Z_by_value in H0 as ?.
    rewrite /ty_own_val /ty_own /= repinject_valinject //.
    repeat iSplit => //.
    iIntros "↦".
    iExists _.
    iMod (heap_mapsto_own_state_from_mt with "↦") as "Hl'"; try done.
    iFrame. done.
  Qed.

   Global Instance int_timeless l z it:
    Timeless (l ◁ₗ z @ int it)%I.
  Proof. apply _. Qed.
End int.

Global Hint Resolve val_to_Z_not_Vundef : core.
Global Hint Resolve has_layout_val_tc_val' : core.  
Global Hint Resolve val_to_Z_by_value : core.

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

Lemma elem_of_by_value n it : 
  n ∈ it -> type_is_by_value it = true.
Proof.
  intros.
  destruct it; done.
Qed.

Section programs.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (*** int *)
  Lemma type_val_int n it T :
    typed_value it (i2v n it) T :-
      exhale (<affine> ⌜n ∈ it⌝);
      exhale (<affine> ⌜type_is_volatile it = false⌝);
      return T (n @ (int it)).
  Proof.
    iIntros "[%Hn [% HT]]".
    apply elem_of_by_value in Hn as Hbyv.
    iExists _. iFrame. iPureIntro.
    rewrite repinject_valinject //.
    split3; [done | | by apply i2v_to_Z].
    apply tc_val_has_layout_val2; auto.
    intros ?; by apply in_range_i2v.
  Qed.
  Definition type_val_int_inst := [instance type_val_int].
  Global Existing Instance type_val_int_inst.

  Lemma type_val_int_i32 (n:Integers.int) T :
    typed_value tint (Vint n) T :-
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

  Lemma type_val_int_u32 (n:Integers.int) T :
    typed_value tuint (Vint n) T :-
      exhale (<affine> ⌜(Int.unsigned n) ∈ tuint⌝);
      return T ((Int.unsigned n) @ (int tuint)).
  Proof.
    iIntros "[%Hn HT]".
    iExists _. iFrame. by iPureIntro.
  Qed.
  Definition type_val_int_u32_inst := [instance type_val_int_u32].
  Global Existing Instance type_val_int_u32_inst.

  Lemma type_val_long n T :
    typed_value tlong (Vlong n) T :-
      exhale (<affine> ⌜(Int64.signed n) ∈ tint⌝);
      return T ((Int64.signed n) @ (int tlong)).
  Proof.
    iIntros "[%Hn HT]".
    iExists _. iFrame. by iPureIntro.
  Qed.
  Definition type_val_long_inst := [instance type_val_long].
  Global Existing Instance type_val_long_inst.

  Lemma type_val_ulong n T :
    typed_value tulong (Vlong n) T :-
      exhale (<affine> ⌜(Int64.unsigned n) ∈ tint⌝);
      return T ((Int64.unsigned n) @ (int tulong)).
  Proof.
    iIntros "[%Hn HT]".
    iExists _. iFrame. by iPureIntro.
  Qed.
  Definition type_val_ulong_inst := [instance type_val_ulong].
  Global Existing Instance type_val_ulong_inst.

  (* TODO: instead of adding it_in_range to the context here, have a
  SimplifyPlace/Val instance for int which adds it to the context if
  it does not yet exist (using check_hyp_not_exists)?! *)
  Lemma type_relop_int_int ge n1 n2 op b it v1 v2 T :
    match op with
    | Cop.Oeq => Some (bool_decide (n1 = n2))
    | Cop.One => Some (bool_decide (n1 ≠ n2))
    | Cop.Olt => Some (bool_decide (n1 < n2))
    | Cop.Ogt => Some (bool_decide (n1 > n2))
    | Cop.Ole => Some (bool_decide (n1 <= n2))
    | Cop.Oge => Some (bool_decide (n1 >= n2))
    | _ => None
    end = Some b →
    (<affine> ⌜n1 ∈ it⌝ -∗ <affine> ⌜n2 ∈ it⌝ -∗ T (i2v (bool_to_Z b) tint) (b @ boolean tint))
    ⊢ typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|it| n1 @ int it⎤ v2 ⎡v2 ◁ᵥₐₗ|it| n2 @ int it⎤ op it it tint T.
  Proof.
    iIntros "%Hop HT (%H1 & [%H %Hv1]) (%H2 & [%H0 %Hv2]) %Φ HΦ".
    apply has_layout_val_volatile_false in H as Hit.
    apply val_to_Z_by_value in Hv1 as Hit2.
    rewrite !repinject_valinject // in Hv1, Hv2.
    eapply has_layout_val_tc_val in H; eauto.
    eapply has_layout_val_tc_val in H0; eauto.
    iDestruct ("HT" with "[] []" ) as "HT".
    1-2: iPureIntro; by apply: val_to_Z_in_range; first done; apply tc_val_tc_val'.
    rewrite /wp_binop.
    iIntros "!>" (?) "$ !>".
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
               ++ exploit (unsigned_eq_eq i0 i1); congruence.
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
               ++ exploit (unsigned_eq_eq i0 i1); congruence.
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
               rewrite /Int.ltu; if_tac; case_bool_decide; done.
            -- trans (Int.lt i0 i1); last by destruct i, s.
               destruct s; inv Hv1; rewrite /Int.lt; try by if_tac; case_bool_decide.
               lapply (bitsize_small i); last by intros ->.
               rewrite two_power_pos_equiv in H, H0.
               intros; rewrite !Int.signed_eq_unsigned; [if_tac; case_bool_decide; done | destruct i; try done; try rep_lia..].
               { destruct H0; subst; [rewrite Int.unsigned_zero | rewrite Int.unsigned_one]; rep_lia. }
               { destruct H; subst; [rewrite Int.unsigned_zero | rewrite Int.unsigned_one]; rep_lia. }
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
               rewrite /Int.ltu; if_tac; case_bool_decide; lia.
            -- trans (Int.lt i1 i0); last by destruct i, s.
               destruct s; inv Hv1; rewrite /Int.lt; try by if_tac; case_bool_decide; lia.
               lapply (bitsize_small i); last by intros ->.
               rewrite two_power_pos_equiv in H, H0.
               intros; rewrite !Int.signed_eq_unsigned; [if_tac; case_bool_decide; lia | destruct i; try done; try rep_lia..].
               { destruct H; subst; [rewrite Int.unsigned_zero | rewrite Int.unsigned_one]; rep_lia. }
               { destruct H0; subst; [rewrite Int.unsigned_zero | rewrite Int.unsigned_one]; rep_lia. }
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
               rewrite /Int.ltu; if_tac; case_bool_decide; lia.
            -- trans (negb (Int.lt i1 i0)); last by destruct i, s.
               destruct s; inv Hv1; rewrite /Int.lt; try by if_tac; case_bool_decide; lia.
               lapply (bitsize_small i); last by intros ->.
               rewrite two_power_pos_equiv in H, H0.
               intros; rewrite !Int.signed_eq_unsigned; [if_tac; case_bool_decide; lia | destruct i; try done; try rep_lia..].
               { destruct H; subst; [rewrite Int.unsigned_zero | rewrite Int.unsigned_one]; rep_lia. }
               { destruct H0; subst; [rewrite Int.unsigned_zero | rewrite Int.unsigned_one]; rep_lia. }
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
               rewrite /Int.ltu; if_tac; case_bool_decide; lia.
            -- trans (negb (Int.lt i0 i1)); last by destruct i, s.
               destruct s; inv Hv1; rewrite /Int.lt; try by if_tac; case_bool_decide; lia.
               lapply (bitsize_small i); last by intros ->.
               rewrite two_power_pos_equiv in H, H0.
               intros; rewrite !Int.signed_eq_unsigned; [if_tac; case_bool_decide; lia | destruct i; try done; try rep_lia..].
               { destruct H0; subst; [rewrite Int.unsigned_zero | rewrite Int.unsigned_one]; rep_lia. }
               { destruct H; subst; [rewrite Int.unsigned_zero | rewrite Int.unsigned_one]; rep_lia. }
          * destruct s; inv Hv1.
            -- rewrite /Int64.lt; if_tac; case_bool_decide; lia.
            -- rewrite /Int64.ltu; if_tac; case_bool_decide; lia. }
        destruct it; try by destruct v1; simpl.
        * destruct i, v1; try done; destruct v2; try done; destruct s; done.
        * destruct v1; try done; destruct v2; try done; destruct s; done.
    - iApply "HΦ"; last done.
      rewrite /ty_own_val_at /ty_own_val /=.
      iSplit => //.
      iExists (bool_to_Z b).
      iSplit => //.
      iSplit; [by destruct b | done ].
  Qed.

  Definition type_eq_int_int_inst ge n1 n2 :=
    [instance type_relop_int_int ge n1 n2 Cop.Oeq (bool_decide (n1 = n2))].
  Global Existing Instance type_eq_int_int_inst.
  Definition type_ne_int_int_inst ge n1 n2 :=
    [instance type_relop_int_int ge n1 n2 Cop.One (bool_decide (n1 ≠ n2))].
  Global Existing Instance type_ne_int_int_inst.
  Definition type_lt_int_int_inst ge n1 n2 :=
    [instance type_relop_int_int ge n1 n2 Cop.Olt (bool_decide (n1 < n2))].
  Global Existing Instance type_lt_int_int_inst.
  Definition type_gt_int_int_inst ge n1 n2 :=
    [instance type_relop_int_int ge n1 n2 Cop.Ogt (bool_decide (n1 > n2))].
  Global Existing Instance type_gt_int_int_inst.
  Definition type_le_int_int_inst ge n1 n2 :=
    [instance type_relop_int_int ge n1 n2 Cop.Ole (bool_decide (n1 ≤ n2))].
  Global Existing Instance type_le_int_int_inst.
  Definition type_ge_int_int_inst ge n1 n2 :=
    [instance type_relop_int_int ge n1 n2 Cop.Oge (bool_decide (n1 >= n2))].
  Global Existing Instance type_ge_int_int_inst.

  Class CtypeNotVolatile (cty : Ctypes.type) := {
    prf : type_is_volatile cty = false;
  }.

  Lemma type_arithop_int_int ge n1 n2 n op it v1 v2 v1_rep v2_rep
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
    TCEq v1_rep (valinject it v1) →
    TCEq v2_rep (valinject it v2) →
    (<affine> ⌜n1 ∈ it⌝ -∗ <affine> ⌜n2 ∈ it⌝ -∗ <affine> ⌜in_range n it ∧ int_arithop_sidecond it n1 n2 n op⌝ ∗ T (i2v n it) (n @ int it))
    ⊢ typed_bin_op ge v1 ⎡v1_rep ◁ᵥ|it| n1 @ int it⎤ v2 ⎡v2_rep ◁ᵥ|it| n2 @ int it⎤ op it it it T.
  Proof.
    iIntros (-> ->) "HT (H1 & [%Hv_layout1 %Hv1]) (H & [%Hv_layout2 %Hv2]) %Φ HΦ".
    apply has_layout_val_volatile_false in Hv_layout1 as Hit.
    apply val_to_Z_by_value in Hv1 as Hit2.
    rewrite !repinject_valinject // in Hv1, Hv2.
    eapply has_layout_val_tc_val in Hv_layout1 as H; eauto.
    eapply has_layout_val_tc_val in Hv_layout2 as H0; eauto.
    iDestruct ("HT" with "[] []" ) as ((Hin & Hsc)) "HT".
    1-2: iPureIntro; by apply: val_to_Z_in_range; first done; apply tc_val_tc_val'.
    rewrite /wp_binop.
    iIntros "!>" (?) "$ !>".
    iExists (i2v n it); iSplit.
    - iStopProof; split => rho; monPred.unseal.
      apply bi.pure_intro.
      destruct op; inv Hop; rewrite /=.
      + rewrite /Cop.sem_add.
        replace (classify_add it it) with add_default by (destruct it; try done; destruct i; done).
        rewrite /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             by inv Hv1.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             change Archi.ptr64 with true.
             destruct s.
             ++ inv Hv1.
                rewrite Int.add_signed //.
             ++ by inv Hv1.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- change Archi.ptr64 with true.
             rewrite /= Int64.add_signed //.
          -- done.
      + rewrite /Cop.sem_sub.
        replace (classify_sub it it) with sub_default by (destruct it, v1; try done; destruct i; done).
        rewrite /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             by inv Hv1.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1.
                change Archi.ptr64 with true.
                rewrite /= Int.sub_signed //.
             ++ by inv Hv1.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- change Archi.ptr64 with true.
             rewrite /= Int64.sub_signed //.
          -- done.
      + rewrite /Cop.sem_mul /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             by inv Hv1.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1.
                change Archi.ptr64 with true.
                rewrite /= Int.mul_signed //.
             ++ by inv Hv1.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- change Archi.ptr64 with true.
             rewrite /= Int64.mul_signed //.
          -- done.
      + rewrite /Cop.sem_div /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             inv Hv1.
             change Archi.ptr64 with true.
             rewrite /Int.eq; if_tac.
             { rewrite Int.unsigned_zero in H1; tauto. }
             rewrite /Int.divu Zquot.Zquot_Zdiv_pos //; rep_lia.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             change Archi.ptr64 with true.
             rewrite /= /Int.eq; if_tac; simpl.
             { apply unsigned_eq_eq in H1; subst; rewrite Int.signed_zero Int.unsigned_zero in Hv2.
               destruct s; inv Hv2; tauto. }
             destruct (_ && _) eqn: Hm.
             { repeat (if_tac in Hm; try done).
               apply unsigned_eq_eq in H2; apply unsigned_eq_eq in H3; subst.
               destruct s.
               ** inv Hv1. contradict Hin. rewrite Int.signed_mone Int.signed_repr; pose proof (bitsize_half_max i); destruct i; rep_lia.
               ** rewrite Int.unsigned_mone in Hv2; inv Hv2.
                lapply (bitsize_small i); last by intros ->. intros; destruct i; try done.
                destruct H0; done.
                }
             destruct s.
             ++ inv Hv1; done.
             ++ inv Hv1.
                rewrite /Int.divs.
                lapply (bitsize_small i); last by intros ->. intros.
                rewrite two_power_pos_equiv in H, H0.
                rewrite !Int.signed_eq_unsigned //; destruct i; try done; try rep_lia.
                { destruct H0; subst; computable. }
                { destruct H; subst; computable. }
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1; change Archi.ptr64 with true; simpl.
          -- rewrite /Int64.eq; if_tac.
             { apply unsigned_inj_64 in H1; subst; rewrite Int64.signed_zero in Hsc; tauto. }
             destruct (_ && _) eqn: Hm.
             { repeat (if_tac in Hm; try done).
               apply unsigned_inj_64 in H3; apply unsigned_inj_64 in H2; subst.
               inv Hin. }
             done.
          -- rewrite /Int64.eq; if_tac.
             { apply unsigned_inj_64 in H1; subst; rewrite Int64.unsigned_zero in Hsc; tauto. }
             rewrite /Int.divu Zquot.Zquot_Zdiv_pos //; rep_lia.
      + rewrite /Cop.sem_mod /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             inv Hv1.
             change Archi.ptr64 with true.
             rewrite /= /Int.eq; if_tac.
             { rewrite Int.unsigned_zero in H1; tauto. }
             rewrite /Int.modu Zquot.Zrem_Zmod_pos //; rep_lia.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             change Archi.ptr64 with true.
             rewrite /= /Int.eq; if_tac; simpl.
             { apply unsigned_eq_eq in H1; subst; rewrite Int.signed_zero Int.unsigned_zero in Hv2.
               destruct s; inv Hv2; tauto. }
             destruct (_ && _) eqn: Hm.
             { repeat (if_tac in Hm; try done).
               apply unsigned_eq_eq in H3; apply unsigned_eq_eq in H2; subst.
               destruct s.
               ** inv Hv1. rewrite Int.signed_mone Int.signed_repr // in Hsc.
                  rewrite Int.signed_repr // in H.
                  destruct i.
                  { rep_lia. }
                  { rewrite two_power_pos_equiv in H; rep_lia. }
                  { tauto. }
                  { by destruct H. }
               ** rewrite Int.unsigned_mone in Hv2; inv Hv2.
                  lapply (bitsize_small i); last by intros ->. intros; destruct i; try done; try rep_lia.
                  destruct H0; done. }
             destruct s.
             ++ inv Hv1; done.
             ++ inv Hv1.
                rewrite /Int.mods.
                lapply (bitsize_small i); last by intros ->. intros.
                rewrite two_power_pos_equiv in H, H0.
                rewrite !Int.signed_eq_unsigned //; destruct i; try done; try rep_lia.
                { destruct H0; subst; computable. }
                { destruct H; subst; computable. }
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1; change Archi.ptr64 with true; simpl.
          -- rewrite /Int64.eq; if_tac.
             { apply unsigned_inj_64 in H1; subst; rewrite Int64.signed_zero in Hsc; tauto. }
             destruct (_ && _) eqn: Hm.
             { repeat (if_tac in Hm; try done).
               apply unsigned_inj_64 in H3; apply unsigned_inj_64 in H2; subst.
               rewrite Int64.signed_mone Int64.signed_repr in Hsc; rep_lia. }
             done.
          -- rewrite /Int64.eq; if_tac.
             { apply unsigned_inj_64 in H1; subst; rewrite Int64.unsigned_zero in Hsc; tauto. }
             rewrite /Int.modu Zquot.Zrem_Zmod_pos //; rep_lia.
      + rewrite /Cop.sem_and /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             by inv Hv1.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1.
                change Archi.ptr64 with true.
                rewrite /= and_signed //.
             ++ by inv Hv1.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- change Archi.ptr64 with true.
             rewrite /= and_signed_64 //.
          -- done.
      + rewrite /Cop.sem_or /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             by inv Hv1.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1.
                change Archi.ptr64 with true.
                rewrite /= or_signed //.
             ++ by inv Hv1.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- change Archi.ptr64 with true.
             rewrite /= or_signed_64 //.
          -- done.
      + rewrite /Cop.sem_xor /Cop.sem_binarith; destruct it, v1; try done; destruct v2; try done.
        * destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             by inv Hv1.
          -- replace (classify_binarith _ _) with (bin_case_i Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1.
                change Archi.ptr64 with true.
                rewrite /= xor_signed //.
             ++ by inv Hv1.
        * rewrite /Cop.sem_cast /=.
          destruct s; simpl in *; inv Hv1.
          -- change Archi.ptr64 with true.
             rewrite /= xor_signed_64 //.
          -- done.
      + rewrite /Cop.sem_shl /Cop.sem_shift; destruct it, v1; try done; destruct v2; try done.
        * assert (n1 = Int.unsigned i0) as ->.
          { destruct s; simpl in *.
            ** inv Hv1. apply Int.signed_eq_unsigned, Int.signed_positive; lia.
            ** inv Hv1; done. }
          assert (n2 = Int.unsigned i1) as ->.
          { destruct s; simpl in *.
            ** inv Hv2. apply Int.signed_eq_unsigned, Int.signed_positive; lia.
            ** inv Hv2; done. }
          rewrite /Int.ltu; if_tac.
          2: { rewrite Int.unsigned_repr_wordsize in H1; simpl in *.
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
          2: { rewrite Int64.unsigned_repr_wordsize in H1; simpl in *; rep_lia. }
          destruct i, s; done.
      + rewrite /Cop.sem_shr /Cop.sem_shift; destruct it, v1; try done; destruct v2; try done.
        * assert (n2 = Int.unsigned i1) as Heq.
          { destruct s; simpl in *.
            ** inv Hv2. apply Int.signed_eq_unsigned, Int.signed_positive; lia.
            ** inv Hv2; done. }
          rewrite /Int.ltu; if_tac.
          2: { rewrite Int.unsigned_repr_wordsize in H1; simpl in *.
               pose proof (bitsize_wordsize i); rep_lia. }
          destruct (unsigned_op i s) eqn: Hs.
          -- destruct i; try done; destruct s; try done; simpl in *.
             by inv Hv1.
          -- replace (classify_shift _ _) with (shift_case_ii Signed) by (destruct i, s; done); simpl in *.
             destruct s.
             ++ inv Hv1; done.
             ++ inv Hv1.
                rewrite /Int.shr Int.signed_eq_unsigned //.
                { lapply (bitsize_small i); last by intros ->; intros.
                  rewrite two_power_pos_equiv in H, H0.
                  destruct i; try done; try rep_lia.
                  intros; destruct H; subst; computable. }
        * simpl in *.
          assert (n2 = Int64.unsigned i0) as Heq.
          { destruct s; inv Hv2; try done.
            apply Int64.signed_eq_unsigned, Int64.signed_positive; lia. }
          rewrite /Int64.ltu; if_tac.
          2: { rewrite Int64.unsigned_repr_wordsize in H1; simpl in *; rep_lia. }
          destruct s; inv Hv1; done.
    - iApply ("HΦ" with "[] HT").
      iPureIntro.
      rewrite repinject_valinject //.
      split3; [done| | by apply i2v_to_Z].
      apply tc_val_has_layout_val2; auto.
      intros ?; by apply in_range_i2v.
  Qed.
  Definition type_add_int_int_inst ge n1 n2 := [instance type_arithop_int_int ge n1 n2 (n1 + n2) Oadd].
  Global Existing Instance type_add_int_int_inst.
  Definition type_sub_int_int_inst ge n1 n2 := [instance type_arithop_int_int ge n1 n2 (n1 - n2) Osub].
  Global Existing Instance type_sub_int_int_inst.
  Definition type_mul_int_int_inst ge n1 n2 := [instance type_arithop_int_int ge n1 n2 (n1 * n2) Omul].
  Global Existing Instance type_mul_int_int_inst.
  Definition type_div_int_int_inst ge n1 n2 := [instance type_arithop_int_int ge n1 n2 (n1 `quot` n2) Odiv].
  Global Existing Instance type_div_int_int_inst.
  Definition type_mod_int_int_inst ge n1 n2 := [instance type_arithop_int_int ge n1 n2 (n1 `rem` n2) Omod].
  Global Existing Instance type_mod_int_int_inst.
  Definition type_and_int_int_inst ge n1 n2 := [instance type_arithop_int_int ge n1 n2 (Z.land n1 n2) Oand].
  Global Existing Instance type_and_int_int_inst.
  Definition type_or_int_int_inst ge n1 n2 := [instance type_arithop_int_int ge n1 n2 (Z.lor n1 n2) Oor].
  Global Existing Instance type_or_int_int_inst.
  Definition type_xor_int_int_inst ge n1 n2 := [instance type_arithop_int_int ge n1 n2 (Z.lxor n1 n2) Oxor].
  Global Existing Instance type_xor_int_int_inst.
  Definition type_shl_int_int_inst ge n1 n2 := [instance type_arithop_int_int ge n1 n2 (n1 ≪ n2) Oshl].
  Global Existing Instance type_shl_int_int_inst.
  Definition type_shr_int_int_inst ge n1 n2 := [instance type_arithop_int_int ge n1 n2 (n1 ≫ n2) Oshr].
  Global Existing Instance type_shr_int_int_inst.

  Inductive trace_if_int :=
  | TraceIfInt (n : Z).

  Lemma type_if_int  F it (n : Z) v T1 T2:
    F ∧ case_if (n ≠ 0)
      (li_trace (TraceIfInt n, true) T1)
      (li_trace (TraceIfInt n, false) T2)
    ⊢ typed_if it v (v ◁ᵥₐₗ|it| n @ int it) F T1 T2.
  Proof.
    iIntros "Hs (% & [% %Hb])".
    iStopProof; f_equiv; iIntros "Hs".
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
    (<affine> ⌜n ∈ it⌝ -∗ <affine> ⌜is_signed it⌝ ∗ <affine> ⌜n ≠ min_int it⌝ ∗ T (i2v (-n) it) ((-n) @ int it))
    ⊢ typed_un_op v ⎡v ◁ᵥₐₗ|it| n @ int it⎤%I Oneg it it T.
  Proof.
    iIntros "HT (%_ & [%H %Hv]) %Φ HΦ".
    apply has_layout_val_volatile_false in H as Hit.
    apply val_to_Z_by_value in Hv as Hit2.
    rewrite repinject_valinject // in Hv.
    eapply has_layout_val_tc_val in H as Htc; eauto.
    pose proof (val_to_Z_in_range _ _ _ Hv (tc_val_tc_val' _ _ Htc)) as Hin.
    iDestruct ("HT" with "[//]") as (Hs Hn) "HT".
    rewrite /wp_unop.
    iIntros "!>" (?) "$ !>".
    iExists (i2v (- n) it); iSplit.
    - iStopProof; split => rho; monPred.unseal.
      apply bi.pure_intro.
      destruct it; try done; destruct s; try done; simpl in *.
      + rewrite /Cop.sem_neg.
        replace (classify_neg _) with (neg_case_i Signed) by (destruct i; done).
        destruct v; inv Hv.
        rewrite -Int.neg_repr Int.repr_signed //.
      + destruct i; done.
      + rewrite /Cop.sem_neg /=.
        destruct v; inv Hv.
        rewrite -Int64.neg_repr Int64.repr_signed //.
    - iDestruct ("HΦ" $! _ _) as "HΦ".
      iApply "HΦ"; last done.
      iPureIntro.
      assert (in_range (- n) it).
      { hnf in Hin; destruct it; try done.
        * destruct i; try done; destruct s; simpl in *; rep_lia.
        * destruct s; simpl in *; rep_lia. }
      rewrite repinject_valinject //.
      split3; [done| | by apply i2v_to_Z].
      apply tc_val_has_layout_val2; auto.
      intros ?; by apply in_range_i2v.
  Qed.
  Definition type_neg_int_inst := [instance type_neg_int].
  Global Existing Instance type_neg_int_inst.

  Definition is_bool_type t := match t with Tint IBool _ _ => true | _ => false end.

  Lemma cast_int_type it1 it2 v n: val_to_Z v it1 = Some n → n ∈ it2 → is_bool_type it2 = false → type_is_volatile it2 = false →
    ⊢ ∃ v', <affine> ⌜sem_cast it1 it2 v = Some v'⌝ ∧ v' ◁ᵥₐₗ| it2 | n @ int it2.
  Proof.
    intros Hn Hin ?; iPureIntro.
    exists (i2v n it2).
    pose proof (i2v_to_Z _ _ Hin) as Hn2.
    pose proof (val_to_Z_by_value _ _ _ Hn2).
    split3; try done; last split.
    - rewrite /sem_cast.
      destruct (Cop.classify_cast it1 it2) eqn: Hclass;
        try by destruct v, it2; try done; destruct it1; try destruct i0.
      + rewrite /Cop.classify_cast in Hclass.
        destruct v, it1; try done; destruct it2; try done; simpl in *.
        * destruct i1; try done.
        * if_tac in Hclass; done.
        * destruct s; inv Hn; [rewrite Int64.repr_signed | rewrite Int64.repr_unsigned]; done.
      + destruct v, it1; try done; destruct it2; try done; simpl in * |-.
        2: { if_tac in Hclass; done. }
        rewrite sem_cast_i2i_correct_range.
        * simpl; destruct s; inv Hn; [rewrite Int.repr_signed | rewrite Int.repr_unsigned]; done.
        * apply in_range_i2v in Hin.
          rewrite /tc_val in Hin.
          destruct i1; inv Hclass; destruct s; inv Hn; simpl i2v in Hin;
            rewrite ?Int.repr_signed ?Int.repr_unsigned // in Hin.
      + destruct v, it1; try done; destruct it2; try done; simpl in *.
        * destruct i1; done.
        * inv Hclass.
          rewrite /cast_int_long.
          destruct si1; inv Hn; done.
        * if_tac in Hclass; done.
      + destruct v, it1; try done; destruct it2; try done; simpl in *.
        * destruct i1; done.
        * if_tac in Hclass; inv Hclass.
          apply in_range_i2v in Hin.
          rewrite -(sem_cast_i2i_correct_range sz2 si2 (Vint (Int.repr n))) //=.
          destruct s; inv Hn; try done.
          rewrite Int64.unsigned_signed /Int64.lt; if_tac; last done.
          do 3 f_equal; apply Int.eqm_samerepr.
          rewrite /Int.eqm.
          rewrite -{2}(Z.add_0_r (Int64.signed i)); apply Zbits.eqmod_add.
          { apply Zbits.eqmod_refl. }
          eapply Zbits.eqmod_trans; first apply Zbits.eqmod_mod; first done.
          rewrite /Int64.modulus /Int.modulus !two_power_nat_equiv.
          replace (2 ^ Int64.wordsize) with ((2 ^ Int.wordsize) * (2 ^ Int.wordsize)) by rep_lia.
          rewrite Z_mod_mult; apply Zbits.eqmod_refl.
    - rewrite /has_layout_val value_fits_by_value // repinject_valinject //.
      split; last done; intros ?.
      by apply in_range_i2v.
    - rewrite repinject_valinject //.
  Qed.

(*  (* Ke: the equivalent to Caesium's CastOp is Clight's Ecast, so use typed_val_expr *)
  Lemma type_Ecast_same_val ge f e it2 T:
    typed_val_expr ge f e (λ v ty,
        <affine>⌜typeof e = it2⌝ ∗
        ∀ m (* Ke: for now only handle cases where m is irrelevant *),
        <affine>⌜Some v = Cop.sem_cast v (typeof e) it2 m⌝ ∗
        T v ty)
    ⊢ typed_val_expr ge f (Ecast e it2) T.
  Proof.
    iIntros "He %Φ HΦ".
    iApply wp_Ecast.
    iApply "He".
    iIntros (v ty) "own_v (-> & Hcast)".
    iExists v. iIntros (m).
    iDestruct ("Hcast" $! m) as "(Hcast & T)". iFrame.
    iApply ("HΦ" with "[own_v]"); done.
  Qed.*)

  Lemma type_cast_same ge f e T:
    typed_val_expr ge f e (λ v ty, (<affine> ⌜val_casted v (typeof e)⌝ ∗ T v ty))
    ⊢ typed_val_expr ge f (Ecast e (typeof e)) T.
  Proof.
    iIntros "He %Φ HΦ".
    iApply wp_cast0.
    iApply "He".
    iIntros (v ty) "own_v (% & HT)".
    iExists v; iSplit.
    { iPureIntro; intros; by apply cast_val_casted. }
    iApply ("HΦ" with "own_v HT").
  Qed.

  Lemma type_cast_int_same ge f e T:
    typed_val_expr ge f e (λ v ty, ⎡v ◁ᵥₐₗ|typeof e| ty⎤ -∗ <affine> ⌜type_is_volatile (typeof e) = false⌝ ∗
      ∃ n, <affine> ⌜val_to_Z v (typeof e) = Some n⌝ ∗
      <affine> ⌜n ∈ typeof e⌝ ∗ T v (n @ int (typeof e)))
    ⊢ typed_val_expr ge f (Ecast e (typeof e)) T.
  Proof.
    rewrite -type_cast_same.
    iIntros "He %Φ HΦ"; iApply "He".
    iIntros (??) "own_v HT".
    iDestruct ("HT" with "own_v") as (?? Hn ?) "HT".
    pose proof (val_to_Z_by_value _ _ _ Hn).
    assert (tc_val (typeof e) v) as Htc.
    { apply val_to_Z_inv in Hn as ->.
      by apply in_range_i2v. }
    iApply ("HΦ" with "[] [$HT]").
    - iPureIntro; split3; auto.
      + split; last done.
        rewrite value_fits_by_value // repinject_valinject //.
        by intros ?.
      + rewrite repinject_valinject //.
    - iPureIntro; destruct v, (typeof e); try done; constructor.
      pose proof (sem_cast_i2i_correct_range _ _ _ Htc) as Hcast.
      by injection Hcast.
  Qed.

  Lemma type_cast_int ge f e it2 T:
    typed_val_expr ge f e (λ v ty, ⎡v ◁ᵥₐₗ|typeof e| ty⎤ -∗ <affine> ⌜type_is_volatile (typeof e) = false⌝ ∗
      ∃ n, <affine> ⌜val_to_Z v (typeof e) = Some n⌝ ∗ <affine> ⌜n ∈ typeof e⌝ ∗
      <affine> ⌜n ∈ it2⌝ ∗ <affine> ⌜is_bool_type it2 = false ∧ type_is_volatile it2 = false⌝ ∗
       ∀ v, T v (n @ int it2))
    ⊢ typed_val_expr ge f (Ecast e it2) T.
  Proof.
    iIntros "He %Φ HΦ".
    iApply wp_cast_sc.
    iApply "He".
    iIntros (v ty) "own_v HT".
    iDestruct ("HT" with "own_v") as "(% & % & %Hn & % & %Hit2 & (% & %) & HT)".
    pose proof (val_to_Z_by_value _ _ _ Hn).
    assert (tc_val (typeof e) v) as Htc.
    { apply val_to_Z_inv in Hn as ->.
      by apply in_range_i2v. }
    iSplit.
    { rewrite /sc_cast.
      destruct (Cop.classify_cast (typeof e) it2); try done; destruct v; done. }
    iDestruct cast_int_type as "(%v' & % & Hv')"; [done..|].
    iExists v'; iSplit => //.
    by iApply ("HΦ" with "Hv'").
  Qed.

  (*Lemma type_cast_int n it1 it2 v T:
    (⌜n ∈ it1⌝ -∗ ⌜n ∈ it2⌝ ∗ ∀ v, T v (n @ int it2))
    ⊢ typed_un_op v (v ◁ᵥ n @ int it1)%I (CastOp (IntOp it2)) (IntOp it1) T.
  Proof.
    iIntros "HT %Hv %Φ HΦ".
    iDestruct ("HT" with "[]") as ([v' Hv']%(val_of_Z_is_Some (val_to_byte_prov v))) "HT".
    { iPureIntro. by apply: val_to_Z_in_range. }
    iApply wp_cast_int => //. iApply ("HΦ" with "[] HT") => //.
    iPureIntro. by apply: val_to_of_Z.
  Qed.*)
  (*Definition type_cast_int_inst := [instance type_cast_int].
  Global Existing Instance type_cast_int_inst.*)

(*  Lemma type_not_int n1 it v1 T:
    let n := if is_signed it then Z.lnot n1 else Z_lunot (int_size it) n1 in
    (⌜n1 ∈ it⌝ -∗ T (i2v n it) (n @ int it))
    ⊢ typed_un_op v1 ⎡v1 ◁ᵥ n1 @ int it⎤%I Onotint it T.
  Proof.
    iIntros "%n HT (% & %Hv1) %Φ HΦ". pose proof (val_to_Z_in_range _ _ _ Hv1 H) as Hin.
    assert (n ∈ it).
    { admit. }
    rewrite /wp_unop.
    iIntros "!>" (?) "$ !>".
    iExists (i2v n it); iSplit.
    - iStopProof; split => rho; monPred.unseal.
      apply bi.pure_intro.
      destruct it; try done; destruct s; try done; simpl in *.
      + rewrite /Cop.sem_neg.
        replace (classify_neg _) with (neg_case_i Signed) by (destruct i; done).
        destruct v; inv Hv.
        rewrite -Int.neg_repr Int.repr_signed //.
      + destruct i; done.
      + rewrite /Cop.sem_neg /=.
        destruct v; inv Hv.
        rewrite -Int64.neg_repr Int64.repr_signed //.
    - iApply "HΦ"; last done. iPureIntro.
      assert (in_range (- n) it).
      { hnf in Hin; destruct it; try done.
        * destruct i; try done; destruct s; simpl in *; rep_lia.
        * destruct s; simpl in *; rep_lia. }
      split; [by apply in_range_i2v | by apply i2v_to_Z].
  Qed.
  Definition type_not_int_inst := [instance type_not_int].
  Global Existing Instance type_not_int_inst.  Abort.*)

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
    iIntros "[% [-> ?]] Hint". iExists _. iFrame. iDestruct "Hint" as (????) "?".
    iExists _, _. iFrame. iSplit; first done. iSplit; last done. by destruct b.
  Qed.
  Definition subsume_int_boolean_place_inst := [instance subsume_int_boolean_place].
  Global Existing Instance subsume_int_boolean_place_inst.

  Lemma subsume_int_boolean_val A v n b it T:
    (∃ x, <affine> ⌜n = bool_to_Z (b x)⌝ ∗ T x)
    ⊢ subsume ( v ◁ᵥₐₗ|it| n @ int it) (λ x : A, v ◁ᵥₐₗ|it| (b x) @ boolean it) T.
  Proof.
    iIntros "[%x [-> ?]] (%&%&%)". iExists _. iFrame. unfold boolean; simpl_type.
    eapply val_to_Z_by_value in H1 as Htc.
    rewrite repinject_valinject // in H1.
    rewrite /ty_own_val_at /ty_own_val /=.
    iSplit => //.
    iExists (bool_to_Z (b x)). iSplit => //. iSplit => //. rewrite repinject_valinject //. Qed.
  Definition subsume_int_boolean_val_inst := [instance subsume_int_boolean_val].
  Global Existing Instance subsume_int_boolean_val_inst.

  Lemma type_binop_boolean_int ge it1 it2 it3 it4 it5 v1 b1 v2 n2 op T:
    typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|it1| (bool_to_Z b1) @ int it1⎤ v2 ⎡v2 ◁ᵥₐₗ|it2| n2 @ int it2⎤ op it3 it4 it5 T
    ⊢ typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|it1| b1 @ boolean it1⎤ v2 ⎡v2 ◁ᵥₐₗ|it2| n2 @ int it2⎤ op it3 it4 it5 T.
  Proof.
    iIntros "HT H1 H2". iApply ("HT" with "[H1] H2"). unfold boolean; simpl_type.
    rewrite /ty_own_val_at /ty_own_val /=.
    iDestruct "H1" as "(% & (%&%&%&%))". iPureIntro.
    move: H1 H2 => /= -> ->. done.
  Qed.
  Definition type_binop_boolean_int_inst := [instance type_binop_boolean_int].
  Global Existing Instance type_binop_boolean_int_inst.

  Lemma type_binop_int_boolean ge it1 it2 it3 it4 it5 v1 b1 v2 n2 op T:
    typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|it2| n2 @ int it2⎤ v2 ⎡v2 ◁ᵥₐₗ|it1| (bool_to_Z b1) @ int it1⎤ op it3 it4 it5 T
    ⊢ typed_bin_op ge v1 ⎡v1 ◁ᵥₐₗ|it2| n2 @ int it2⎤ v2 ⎡v2 ◁ᵥₐₗ|it1| b1 @ boolean it1⎤ op it3 it4 it5 T.
  Proof.
    iIntros "HT H1 H2". iApply ("HT" with "H1 [H2]"). unfold boolean; simpl_type.
    rewrite /ty_own_val_at /ty_own_val /=.
    iDestruct "H2" as "(% & (%&%&%&%))". iPureIntro.
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
    (li_tactic (li_vm_compute Some n) (λ n', v ◁ᵥₐₗ|it| n' @ int it -∗ T))
    ⊢ typed_annot_expr 1 (ReduceAnnot) v (v ◁ᵥₐₗ|it| n @ int it) T.
  Proof.
    unfold li_tactic, li_vm_compute.
    iIntros "[%y [% HT]] Hv"; simplify_eq. iApply step_fupd_intro => //. iModIntro.
    by iApply "HT".
  Qed.
  Definition annot_reduce_int_inst := [instance annot_reduce_int].
  Global Existing Instance annot_reduce_int_inst.

End programs.
Global Typeclasses Opaque int_inner_type int.

Example CtypeNotVolatile_int_test_fail : CtypeNotVolatile (tint).
Proof. Fail solve [refine _]. Abort.
Hint Extern 0 (CtypeNotVolatile _) => done : typeclass_instances.
Example CtypeNotVolatile_int_test : CtypeNotVolatile (tint).
Proof. solve [refine _]. Qed.

Notation "'if' p ≠ 0 " := (TraceIfInt p) (at level 100, only printing).
(* Notation "'case' n " := (TraceSwitchIntCase n) (at level 100, only printing).
Notation "'default'" := (TraceSwitchIntDefault) (at level 100, only printing). *)

Section offsetof.
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  (*** OffsetOf *)
  Program Definition offsetof (s : members) (m : ident) : type := {|
    ty_has_op_type ot _ := ot = size_t;
    ty_own β l := ∃ n, <affine> ⌜fieldlist.in_members m s /\ fieldlist.field_offset _ m s = n⌝ ∗ l ◁ₗ{β} n @ int size_t;
    ty_own_val cty v := <affine> ⌜cty=size_t⌝ ∗ ∃ n, <affine> ⌜fieldlist.in_members m s /\ fieldlist.field_offset _ m s = n⌝ ∗ v ◁ᵥ|cty| n @ int size_t;
  |}%I.
  Next Obligation.
    iIntros (s m l E ?). iDestruct 1 as (n Hn) "H". iExists _. iSplitR => //. by iApply ty_share.
  Qed.
  Next Obligation. iIntros (s m ot mt l ?). iDestruct 1 as (??) "Hn". by iDestruct (ty_aligned with "Hn") as "$". Qed.
  Next Obligation. iIntros (s m ot mt l ->). iDestruct 1 as (??) "[% Hn]". by iApply (ty_size_eq _ _ mt with "Hn"). Qed.
  Next Obligation.
    iIntros (s m ot mt l ?). iDestruct 1 as (??) "Hn".
    iDestruct (ty_deref with "Hn") as (v) "[Hl Hi]"; [done|]. iExists _. iFrame.
    eauto with iFrame.
  Qed.
  Next Obligation.
    iIntros (s m ? l v ???) "Hl". iDestruct 1 as (??)"[% Hn]".
    iExists _. iSplit => //. by iApply (@ty_ref with "[] Hl").
    Unshelve. done.
  Qed.

  Global Program Instance offsetof_copyable s m : Copyable size_t (offsetof s m).
  Next Obligation.
    iIntros (s m E l ?). iDestruct 1 as (n Hn) "Hl".
    iMod (copy_shr_acc with "Hl") as (???) "(%&Hl&H2&H3)" => //.
    iModIntro. iSplitR => //. iExists _, _.
    iFrame "Hl".
    iSplit => //.
    rewrite /ty_own_val {2}/ty_own /offsetof /= /ty_own_val_at /ty_own_val /=.
    iDestruct "H2" as "(_ & % & %)".
    iSplitR => //.
    { iSplitR => //. iExists _. done. }
    iIntros "↦". iMod ("H3" with "↦") as "H3".
    iExists _. iFrame "H3". done.
  Qed.

  Global Instance offsetof_defined s m : DefinedTy size_t (offsetof s m).
  Proof.
    iIntros (?) "(% & % & % & H)".
    iApply (defined_ty with "H").
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
  Context `{!typeG OK_ty Σ} {cs : compspecs}.

  Definition Econst_size_t z := if Archi.ptr64 then Econst_long (Int64.repr z) size_t else Econst_int (Int.repr z) size_t .
  Definition Vsize_t z := if Archi.ptr64 then Vlong (Int64.repr z) else Vint (Int.repr z).

  Lemma type_const_size_t ge f z T:
    typed_value size_t (i2v z size_t) (T (i2v z size_t))
    ⊢ typed_val_expr ge f (Econst_size_t z) T.
  Proof.
    rewrite /Econst_size_t /size_t; simple_if_tac; [apply type_const_long | apply type_const_int].
  Qed.

  Example type_eq ge f n1 n3 T:
    n1 ∈ size_t →
    n3 ∈ size_t →
    ⊢ typed_val_expr ge f (Ebinop Oeq (Ebinop Oadd (Econst_size_t n1) (Econst_size_t 0) size_t) (Econst_size_t n3) tint) T.
  Proof.
    move => Hn1 Hn2.
    iApply type_bin_op.
    iApply type_bin_op.
    iApply type_const_size_t. iApply type_val_int. iSplit => //. iSplit => //.
    iApply type_const_size_t. iApply type_val_int. iSplit => //. iSplit => //.
    iApply type_arithop_int_int => //. iIntros (??). iSplit. {
      iPureIntro. (*unfold int_arithop_sidecond, elem_of, int_elem_of_it, min_int, max_int in *; lia.*) rewrite Z.add_0_r //.
    }
    iApply type_const_size_t. iApply type_val_int. iSplit => //. iSplit => //.
    iApply type_relop_int_int => //.
  Abort.
End tests.
