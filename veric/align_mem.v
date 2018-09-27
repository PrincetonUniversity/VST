Require Import Coq.Sorting.Permutation.
Require Import Coq.Sorting.Sorting.
Require Import Coq.Structures.Orders.
Require Import VST.veric.base.
Require Import compcert.cfrontend.Ctypes. (*Require Import VST.veric.Clight_lemmas.*)
Require Import VST.veric.type_induction.
Require Import VST.veric.composite_compute.

(* This file contains three computational align criteria.
   1: the hardware alignof is not larger than alignof (and additional criterion for array).
   2: all fields are aligned as hardware requires. size as a multiple of hardware alignof.
   3: all value is well-aligned stored.
   The third one is the final specification we want. *)

Section align_compatible_rec.

Context (cenv: composite_env).

Inductive align_compatible_rec: type -> Z -> Prop :=
| align_compatible_rec_by_value: forall t ch z, access_mode t = By_value ch -> (Memdata.align_chunk ch | z) -> align_compatible_rec t z
| align_compatible_rec_Tarray: forall t n a z, (forall i, 0 <= i < n -> align_compatible_rec t (z + sizeof cenv t * i)) -> align_compatible_rec (Tarray t n a) z
| align_compatible_rec_Tstruct: forall i a co z, cenv ! i = Some co -> (forall i0 t0 z0, field_type i0 (co_members co) = Errors.OK t0 -> field_offset cenv i0 (co_members co) = Errors.OK z0 -> align_compatible_rec t0 (z + z0)) -> align_compatible_rec (Tstruct i a) z
| align_compatible_rec_Tunion: forall i a co z, cenv ! i = Some co -> (forall i0 t0, field_type i0 (co_members co) = Errors.OK t0 -> align_compatible_rec t0 z) -> align_compatible_rec (Tunion i a) z.

Lemma align_compatible_rec_by_value_inv : forall t ch z,
  access_mode t = By_value ch ->
  align_compatible_rec t z -> (Memdata.align_chunk ch | z).
Proof.
  intros.
  inv H0.
  + rewrite H in H1; inv H1; auto.
  + inv H.
  + inv H.
  + inv H.
Qed.

Lemma align_compatible_rec_Tarray_inv: forall t n a z,
  align_compatible_rec (Tarray t n a) z ->
  (forall i : Z, 0 <= i < n -> align_compatible_rec t (z + sizeof cenv t * i)).
Proof.
  intros.
  inv H.
  + inv H1.
  + auto.
Qed.

Lemma align_compatible_rec_Tstruct_inv: forall i a co z,
  cenv ! i = Some co ->
  align_compatible_rec (Tstruct i a) z ->
  (forall i0 t0 z0, field_type i0 (co_members co) = Errors.OK t0 -> field_offset cenv i0 (co_members co) = Errors.OK z0 -> align_compatible_rec t0 (z + z0)).
Proof.
  intros.
  inv H0.
  + inv H3.
  + rewrite H in H5; inv H5.
    eauto.
Qed.
  
Lemma align_compatible_rec_Tunion_inv: forall i a co z,
  cenv ! i = Some co ->
  align_compatible_rec (Tunion i a) z ->
  (forall i0 t0, field_type i0 (co_members co) = Errors.OK t0 -> align_compatible_rec t0 z).
Proof.
  intros.
  inv H0.
  + inv H2.
  + rewrite H in H4; inv H4.
    eauto.
Qed.

End align_compatible_rec.

Lemma align_chunk_1248: forall ch, align_chunk ch = 1 \/ align_chunk ch = 2 \/ align_chunk ch = 4 \/ align_chunk ch = 8.
Proof.
  intros.
  destruct ch; simpl;
  auto.
Qed.

Lemma align_chunk_two_p:
  forall ch, exists n, align_chunk ch = two_power_nat n.
Proof.
  intros.
  pose proof align_chunk_1248 ch as [| [| [|]]]; rewrite H.
  + exists 0%nat; auto.
  + exists 1%nat; auto.
  + exists 2%nat; auto.
  + exists 3%nat; auto.
Qed.

Fixpoint hardware_alignof (ha_env: PTree.t Z) t: Z :=
  match t with
  | Tarray t' _ _ => hardware_alignof ha_env t'
  | Tstruct id _ =>
      match ha_env ! id with
      | Some ha => ha
      | None => 1
      end
  | Tunion id _ =>
      match ha_env ! id with
      | Some ha => ha
      | None => 1
      end
  | _ => match access_mode t with
         | By_value ch => Memdata.align_chunk ch
         | _ => 1
         end
  end.

Fixpoint hardware_alignof_composite (ha_env: PTree.t Z) (m: members): Z :=
  match m with
  | nil => 1
  | (_, t) :: m' => Z.max (hardware_alignof ha_env t) (hardware_alignof_composite ha_env m')
  end.

Definition hardware_alignof_env (cenv: composite_env): PTree.t Z :=
  let l := composite_reorder.rebuild_composite_elements cenv in
  fold_right (fun (ic: positive * composite) (T0: PTree.t Z) => let (i, co) := ic in let T := T0 in PTree.set i (hardware_alignof_composite T (co_members co)) T) (PTree.empty _) l.

Definition hardware_alignof_env_consistent (cenv: composite_env) (ha_env: PTree.t Z): Prop :=
  forall i co ha,
    cenv ! i = Some co ->
    ha_env ! i = Some ha ->
    ha = hardware_alignof_composite ha_env (co_members co).

Definition hardware_alignof_env_complete (cenv: composite_env) (ha_env: PTree.t Z): Prop :=
  forall i,
    (exists co, cenv ! i = Some co) <->
    (exists ha, ha_env ! i = Some ha).

Module Type HARDWARE_ALIGNOF_FACTS.

  Axiom hardware_alignof_consistency:
    forall (cenv: composite_env) (ha_env: PTree.t Z),
      composite_env_consistent cenv ->
      ha_env = hardware_alignof_env cenv ->
      hardware_alignof_env_consistent cenv ha_env.

  Axiom hardware_alignof_completeness:
    forall (cenv: composite_env) (ha_env: PTree.t Z),
      ha_env = hardware_alignof_env cenv ->
      hardware_alignof_env_complete cenv ha_env.

End HARDWARE_ALIGNOF_FACTS.

Module hardware_alignof_facts: HARDWARE_ALIGNOF_FACTS.

Lemma aux1: forall T co,
  (fix fm (l : list (ident * type * Z)) : Z :=
     match l with
     | nil => 1
     | (_, _, ha) :: l' => Z.max ha (fm l')
     end)
    (map
       (fun it0 : positive * type =>
        let (i0, t0) := it0 in
        (i0, t0,
        type_func.F
          (fun t : type =>
           match access_mode t with
           | By_value ch => align_chunk ch
           | By_reference => 1
           | By_copy => 1
           | By_nothing => 1
           end) (fun (ha : Z) (_ : type) (_: Z) (_ : attr) => ha)
          (fun (ha : Z) (_ : ident) (_ : attr) => ha)
          (fun (ha : Z) (_ : ident) (_ : attr) => ha) T t0)) (co_members co)) =
                    hardware_alignof_composite T (co_members co).
Proof.
  intros; unfold hardware_alignof_composite, hardware_alignof.
  induction (co_members co) as [| [i t] ?].
  + auto.
  + simpl.
    f_equal; auto.
    clear.
    induction t; auto.
Qed.

Lemma aux2: forall (cenv: composite_env),
  type_func.Env
          (fun t : type =>
           match access_mode t with
           | By_value ch => align_chunk ch
           | By_reference => 1
           | By_copy => 1
           | By_nothing => 1
           end) (fun (ha : Z) (_ : type) (_: Z) (_ : attr) => ha)
          (fun (ha : Z) (_ : ident) (_ : attr) => ha)
          (fun (ha : Z) (_ : ident) (_ : attr) => ha)
          (fun _ : struct_or_union =>
           fix fm (l : list (ident * type * Z)) : Z :=
             match l with
             | nil => 1
             | (_, _, ha) :: l' => Z.max ha (fm l')
             end) (composite_reorder.rebuild_composite_elements cenv) =
  hardware_alignof_env cenv.
Proof.
  intros.
  unfold type_func.Env, type_func.env_rec, hardware_alignof_env.
  f_equal.
  extensionality ic.
  destruct ic as [i co].
  extensionality T.
  f_equal.
  apply aux1.
Qed.

Lemma hardware_alignof_consistency (cenv: composite_env) (ha_env: PTree.t Z):
  composite_env_consistent cenv ->
  ha_env = hardware_alignof_env cenv ->
  forall i co ha,
    cenv ! i = Some co ->
    ha_env ! i = Some ha ->
    ha = hardware_alignof_composite ha_env (co_members co).
Proof.
  intros.
  pose proof @composite_reorder_consistent Z cenv
             (fun t =>
                match access_mode t with
                | By_value ch => Memdata.align_chunk ch
                | _ => 1
                end)
             (fun ha _ _ _ => ha)
             (fun ha _ _ => ha)
             (fun ha _ _ => ha)
             (fun _ =>
                fix fm (l: list (ident * type * Z)): Z :=
                match l with
                | nil => 1
                | (_, _, ha) :: l' => Z.max ha (fm l')
                end)
             H
    as HH.
  hnf in HH.
  subst ha_env.
  rewrite aux2 in HH.
  specialize (HH _ _ ha H1 H2).
  rewrite HH, aux1; auto.
Qed.

Lemma hardware_alignof_completeness (cenv: composite_env) (ha_env: PTree.t Z):
  ha_env = hardware_alignof_env cenv ->
  forall i,
    (exists co, cenv ! i = Some co) <->
    (exists ha, ha_env ! i = Some ha).
Proof.
  intros.
  pose proof @composite_reorder_complete Z cenv
             (fun t =>
                match access_mode t with
                | By_value ch => Memdata.align_chunk ch
                | _ => 1
                end)
             (fun ha _ _ _ => ha)
             (fun ha _ _ => ha)
             (fun ha _ _ => ha)
             (fun _ =>
                fix fm (l: list (ident * type * Z)): Z :=
                match l with
                | nil => 1
                | (_, _, ha) :: l' => Z.max ha (fm l')
                end)
    as HH.
  hnf in HH.
  subst.
  rewrite aux2 in HH.
  auto.
Qed.

End hardware_alignof_facts.

Export hardware_alignof_facts.

Lemma hardware_alignof_two_p: forall (cenv: composite_env) (ha_env: PTree.t Z),
  composite_env_consistent cenv ->
  hardware_alignof_env_consistent cenv ha_env ->
  hardware_alignof_env_complete cenv ha_env ->
  forall t, exists n,
  hardware_alignof ha_env t = two_power_nat n.
Proof.
  intros ? ? CENV_CONS HA_ENV_CONS HA_ENV_COMPL ?.
  type_induction t cenv CENV_CONS.
  + exists 0%nat; reflexivity.
  + destruct s, i; try solve [exists 0%nat; reflexivity | exists 1%nat; reflexivity | exists 2%nat; reflexivity | exists 3%nat; reflexivity].
  + destruct s; try solve [exists 0%nat; reflexivity | exists 1%nat; reflexivity | exists 2%nat; reflexivity | exists 3%nat; reflexivity].
  + destruct f; try solve [exists 0%nat; reflexivity | exists 1%nat; reflexivity | exists 2%nat; reflexivity | exists 3%nat; reflexivity].
  + simpl. unfold Mptr.
      destruct Archi.ptr64; [exists 3%nat | exists 2%nat]; reflexivity.
  + simpl.
    auto.
  + exists 0%nat; reflexivity.
  + simpl.
    pose proof HA_ENV_CONS id; pose proof HA_ENV_COMPL id.
    destruct (cenv ! id) as [co |] eqn:?H, (ha_env ! id) eqn:?H.
    2: { pose proof proj1 H0 (ex_intro _ _ eq_refl) as [? ?]; congruence. }
    2: { pose proof proj2 H0 (ex_intro _ _ eq_refl) as [? ?]; congruence. }
    - specialize (H _ _ eq_refl eq_refl).
      subst z.
      clear - IH.
      induction IH.
      * exists 0%nat; reflexivity.
      * destruct x as [i t], H as [n1 ?], IHIH as [n2 ?].
        simpl in H |- *.
        rewrite H, H0.
        rewrite max_two_power_nat.
        eexists; reflexivity.
    - exists 0%nat; reflexivity.
  + simpl.
    pose proof HA_ENV_CONS id; pose proof HA_ENV_COMPL id.
    destruct (cenv ! id) as [co |] eqn:?H, (ha_env ! id) eqn:?H.
    2: { pose proof proj1 H0 (ex_intro _ _ eq_refl) as [? ?]; congruence. }
    2: { pose proof proj2 H0 (ex_intro _ _ eq_refl) as [? ?]; congruence. }
    - specialize (H _ _ eq_refl eq_refl).
      subst z.
      clear - IH.
      induction IH.
      * exists 0%nat; reflexivity.
      * destruct x as [i t], H as [n1 ?], IHIH as [n2 ?].
        simpl in H |- *.
        rewrite H, H0.
        rewrite max_two_power_nat.
        eexists; reflexivity.
    - exists 0%nat; reflexivity.
Qed.

Lemma hardware_alignof_pos: forall (cenv: composite_env) (ha_env: PTree.t Z),
  composite_env_consistent cenv ->
  hardware_alignof_env_consistent cenv ha_env ->
  hardware_alignof_env_complete cenv ha_env ->
  forall t,
  hardware_alignof ha_env t > 0.
Proof.
  intros.
  pose proof hardware_alignof_two_p _ _ H H0 H1 t as [n ?].
  rewrite H2.
  apply two_power_nat_pos.
Qed.

Lemma hardware_alignof_composite_two_p: forall (cenv: composite_env) (ha_env: PTree.t Z),
  composite_env_consistent cenv ->
  hardware_alignof_env_consistent cenv ha_env ->
  hardware_alignof_env_complete cenv ha_env ->
  forall m, exists n,
    hardware_alignof_composite ha_env m = two_power_nat n.
Proof.
  intros.
  induction m as [| [i t] ?].
  + exists 0%nat.
    reflexivity.
  + destruct IHm as [n1 ?], (hardware_alignof_two_p _ _ H H0 H1 t) as [n2 ?].
    simpl.
    rewrite H2, H3.
    rewrite max_two_power_nat.
    eexists; reflexivity.
Qed.

Hint Resolve alignof_two_p: align.
Hint Resolve align_chunk_two_p: align.
Hint Extern 10 (exists n: nat, hardware_alignof _ _ = two_power_nat n) => (eapply hardware_alignof_two_p; eassumption): align.
Hint Extern 10 (exists n: nat, hardware_alignof_composite _ _ = two_power_nat n) => (eapply hardware_alignof_composite_two_p; eassumption): align.

Lemma hardware_alignof_by_value: forall ha_env t ch,
  access_mode t = By_value ch ->
  hardware_alignof ha_env t = align_chunk ch.
Proof.
  intros.
  destruct t as [| [| | |] [|] | [|] | [|] | | | | |]; inv H; auto.
Qed.

Lemma align_compatible_rec_hardware_alignof_divide: forall cenv ha_env t z1 z2,
  composite_env_consistent cenv ->
  composite_env_complete_legal_cosu_type cenv ->
  hardware_alignof_env_consistent cenv ha_env ->
  hardware_alignof_env_complete cenv ha_env ->
  complete_legal_cosu_type cenv t = true ->
  (hardware_alignof ha_env t | z1 - z2) ->
  (align_compatible_rec cenv t z1 <-> align_compatible_rec cenv t z2).
Proof.
  intros ? ? ? ? ? CENV_CONS CENV_COSU HA_ENV_CONS HA_ENV_COMPL.
  revert t z1 z2.
  assert (BY_VALUE: forall t z1 z2, (exists ch, access_mode t = By_value ch) -> (hardware_alignof ha_env t | z1 - z2) -> align_compatible_rec cenv t z1 <-> align_compatible_rec cenv t z2).
  {
    intros ? ? ? [? ?] ?.
    split; intros.
    + eapply align_compatible_rec_by_value_inv in H1; eauto.
      eapply align_compatible_rec_by_value; eauto.
      replace z2 with (z1 - (z1 - z2)) by omega.
      erewrite hardware_alignof_by_value in H0 by eauto.
      apply Z.divide_sub_r; auto.
    + eapply align_compatible_rec_by_value_inv in H1; eauto.
      eapply align_compatible_rec_by_value; eauto.
      replace z1 with (z2 + (z1 - z2)) by omega.
      erewrite hardware_alignof_by_value in H0 by eauto.
      apply Z.divide_add_r; auto.
  } 
  intro t; type_induction t cenv CENV_CONS; intros.
  + split; intros; inv H1; inv H2.
  + eapply BY_VALUE; auto.
    destruct s, i; eexists; reflexivity.
  + eapply BY_VALUE; auto.
    destruct s; eexists; reflexivity.
  + eapply BY_VALUE; auto.
    destruct f; eexists; reflexivity.
  + eapply BY_VALUE; auto.
    eexists; reflexivity.
  + simpl in H0.
    split; intros; apply align_compatible_rec_Tarray; intros;
    eapply align_compatible_rec_Tarray_inv in H1; eauto.
    - specialize (IH (z1 + sizeof cenv t0 * i) (z2 + sizeof cenv t0 * i)).
      replace (z1 + sizeof cenv t0 * i - (z2 + sizeof cenv t0 * i)) with (z1 - z2) in IH by omega.
      tauto.
    - specialize (IH (z1 + sizeof cenv t0 * i) (z2 + sizeof cenv t0 * i)).
      replace (z1 + sizeof cenv t0 * i - (z2 + sizeof cenv t0 * i)) with (z1 - z2) in IH by omega.
      tauto.
  + split; intros; inv H1; inv H2; econstructor.
  + simpl in H, H0.
    destruct (cenv ! id) as [co |] eqn:?H; [| inv H].
    destruct (co_su co) eqn:?H; inv H.
    assert (forall i0 t0 ofs0,
              field_type i0 (co_members co) = Errors.OK t0 ->
              field_offset cenv i0 (co_members co) = Errors.OK ofs0 ->
              (align_compatible_rec cenv t0 (z1 + ofs0) <->
               align_compatible_rec cenv t0 (z2 + ofs0))) as HH;
    [ | split; intros; eapply align_compatible_rec_Tstruct; eauto;
        intros; eapply align_compatible_rec_Tstruct_inv in H; eauto;
        eapply HH; eauto].
    pose proof proj1 (HA_ENV_COMPL id) (ex_intro _ co H1) as [ha ?].
    rewrite H in H0.
    pose proof HA_ENV_CONS _ _ _ H1 H.
    rewrite H3 in H0.
    pose proof CENV_COSU _ _ H1.
    clear H H1 H2 H3 ha.
    intros. clear H1.
    induction IH as [| [i t] ?].
    - inv H.
    - simpl in H, H0, H4.
      autorewrite with align in H0, H4.
      if_tac in H.
      * subst i; inv H.
        apply H1; [simpl; tauto |].
        replace (z1 + ofs0 - (z2 + ofs0)) with (z1 - z2) by omega; tauto.
      * apply IHIH; tauto.
  + simpl in H, H0.
    destruct (cenv ! id) as [co |] eqn:?H; [| inv H].
    destruct (co_su co) eqn:?H; inv H.
    assert (forall i0 t0,
              field_type i0 (co_members co) = Errors.OK t0 ->
              (align_compatible_rec cenv t0 z1 <->
               align_compatible_rec cenv t0 z2)) as HH;
    [ | split; intros; eapply align_compatible_rec_Tunion; eauto;
        intros; eapply align_compatible_rec_Tunion_inv in H; eauto;
        eapply HH; eauto].
    pose proof proj1 (HA_ENV_COMPL id) (ex_intro _ co H1) as [ha ?].
    rewrite H in H0.
    pose proof HA_ENV_CONS _ _ _ H1 H.
    rewrite H3 in H0.
    pose proof CENV_COSU _ _ H1.
    clear H H1 H2 H3 ha.
    intros.
    induction IH as [| [i t] ?].
    - inv H.
    - simpl in H, H0, H4.
      autorewrite with align in H0, H4.
      if_tac in H.
      * subst i; inv H.
        apply H1; simpl; tauto.
      * apply IHIH; tauto.
Qed.

Lemma align_compatible_rec_hardware_1: forall cenv ha_env t z,
  composite_env_consistent cenv ->
  composite_env_complete_legal_cosu_type cenv ->
  hardware_alignof_env_consistent cenv ha_env ->
  hardware_alignof_env_complete cenv ha_env ->
  complete_legal_cosu_type cenv t = true ->
  hardware_alignof ha_env t = 1 ->
  align_compatible_rec cenv t z.
Proof.
  intros ? ? ? ? CENV_CONS CENV_COSU HA_ENV_CONS HA_ENV_COMPL.
  revert z; type_induction t cenv CENV_CONS; intros.
  + inv H.
  + destruct s, i; inv H0;
    econstructor; try reflexivity; apply Z.divide_1_l.
  + destruct s; inv H0.
  + destruct f; inv H0.
  + inv H0.
  + apply align_compatible_rec_Tarray.
    intros.
    apply IH; auto.
  + inv H.
  + simpl in H, H0.
    destruct (cenv ! id) as [co |] eqn:?H; [| inv H].
    destruct (co_su co) eqn:?H; inv H.
    pose proof proj1 (HA_ENV_COMPL id) (ex_intro _ co H1) as [ha ?].
    rewrite H in H0.
    pose proof HA_ENV_CONS _ _ _ H1 H.
    rewrite H3 in H0.
    pose proof CENV_COSU _ _ H1.
    eapply align_compatible_rec_Tstruct; eauto.
    clear H H1 H2 H3 ha.
    intros; clear H1.
    induction IH as [| [i t] ?].
    - inv H.
    - simpl in H, H0, H4.
      autorewrite with align in H0, H4.
      destruct H0, H4.
      if_tac in H.
      * subst i; inv H.
        apply H1; auto.
      * apply IHIH; auto.
  + simpl in H, H0.
    destruct (cenv ! id) as [co |] eqn:?H; [| inv H].
    destruct (co_su co) eqn:?H; inv H.
    pose proof proj1 (HA_ENV_COMPL id) (ex_intro _ co H1) as [ha ?].
    rewrite H in H0.
    pose proof HA_ENV_CONS _ _ _ H1 H.
    rewrite H3 in H0.
    pose proof CENV_COSU _ _ H1.
    eapply align_compatible_rec_Tunion; eauto.
    clear H H1 H2 H3 ha.
    intros.
    induction IH as [| [i t] ?].
    - inv H.
    - simpl in H, H0, H4.
      autorewrite with align in H0, H4.
      destruct H0, H4.
      if_tac in H.
      * subst i; inv H.
        apply H1; auto.
      * apply IHIH; auto.
Qed.

Module Type LEGAL_ALIGNAS.

  Parameter legal_alignas_obs: Type.
  Parameter legal_alignas_type: composite_env -> PTree.t Z -> PTree.t legal_alignas_obs -> type -> legal_alignas_obs.
  Parameter legal_alignas_composite: composite_env -> PTree.t Z -> PTree.t legal_alignas_obs -> composite -> legal_alignas_obs.
  Parameter legal_alignas_env: composite_env -> PTree.t Z -> PTree.t legal_alignas_obs.
  Parameter is_aligned_aux: legal_alignas_obs -> Z -> Z -> bool.  

End LEGAL_ALIGNAS.

Module LegalAlignasDefsGen (LegalAlignas: LEGAL_ALIGNAS).

  Import LegalAlignas.

  Definition legal_alignas_env_consistent (cenv: composite_env) (ha_env: PTree.t Z) (la_env: PTree.t legal_alignas_obs): Prop :=
    forall i co la,
      cenv ! i = Some co ->
      la_env ! i = Some la ->
      la = legal_alignas_composite cenv ha_env la_env co.

  Definition legal_alignas_env_complete (cenv: composite_env) (la_env: PTree.t legal_alignas_obs): Prop :=
    forall i,
      (exists co, cenv ! i = Some co) <->
      (exists la, la_env ! i = Some la).

  Definition is_aligned cenv ha_env la_env (t: type) (ofs: Z): bool := is_aligned_aux (legal_alignas_type cenv ha_env la_env t) (hardware_alignof ha_env t) ofs.

  Definition legal_alignas_env_sound (cenv: composite_env) (ha_env: PTree.t Z) (la_env: PTree.t legal_alignas_obs): Prop :=
    forall ofs t,
      complete_legal_cosu_type cenv t = true ->
      is_aligned cenv ha_env la_env t ofs = true ->
      align_compatible_rec cenv t ofs.

End LegalAlignasDefsGen.

Module Type LEGAL_ALIGNAS_FACTS.

  Declare Module LegalAlignas: LEGAL_ALIGNAS.
  Module LegalAlignasDefs := LegalAlignasDefsGen (LegalAlignas).
  Export LegalAlignas LegalAlignasDefs.

  Axiom legal_alignas_env_consistency: forall cenv ha_env,
    composite_env_consistent cenv ->
    legal_alignas_env_consistent cenv ha_env (legal_alignas_env cenv ha_env).

  Axiom legal_alignas_env_completeness: forall cenv ha_env,
    legal_alignas_env_complete cenv (legal_alignas_env cenv ha_env).

  Axiom legal_alignas_soundness: forall cenv ha_env la_env,
    composite_env_consistent cenv ->
    composite_env_complete_legal_cosu_type cenv ->
    hardware_alignof_env_consistent cenv ha_env ->
    hardware_alignof_env_complete cenv ha_env ->
    legal_alignas_env_consistent cenv ha_env la_env ->
    legal_alignas_env_complete cenv la_env ->
    legal_alignas_env_sound cenv ha_env la_env.

End LEGAL_ALIGNAS_FACTS.

Module LegalAlignasStrict <: LEGAL_ALIGNAS.

Section legal_alignas.

Context (cenv: composite_env) (ha_env: PTree.t Z).

Definition legal_alignas_obs: Type := bool.

Fixpoint legal_alignas_type (la_env: PTree.t bool) t: bool :=
  (hardware_alignof ha_env t <=? alignof cenv t) &&
  match t with
  | Tarray t' _ _ => (sizeof cenv t' mod alignof cenv t' =? 0) && legal_alignas_type la_env t'
  | Tstruct id _ =>
      match la_env ! id with
      | Some la => la
      | None => false
      end
  | Tunion id _ =>
      match la_env ! id with
      | Some la => la
      | None => false
      end
  | _ => match access_mode t with
         | By_value ch => true
         | _ => false
         end
  end.

Fixpoint legal_alignas_members (la_env: PTree.t bool) (m: members): bool :=
  match m with
  | nil => true
  | (_, t) :: m' => (legal_alignas_type la_env t) && (legal_alignas_members la_env m')
  end.

Definition legal_alignas_composite (la_env: PTree.t bool) (co: composite): bool :=
  legal_alignas_members la_env (co_members co).

Definition legal_alignas_env: PTree.t bool :=
  let l := composite_reorder.rebuild_composite_elements cenv in
  fold_right (fun (ic: positive * composite) (T0: PTree.t bool) => let (i, co) := ic in let T := T0 in PTree.set i (legal_alignas_composite T co) T) (PTree.empty _) l.

Definition is_aligned_aux (b: bool) (ha: Z) (ofs: Z) := b && ((ofs mod ha) =? 0).

End legal_alignas.

End LegalAlignasStrict.

Module LegalAlignasStrictFacts: LEGAL_ALIGNAS_FACTS with Module LegalAlignas := LegalAlignasStrict.

Module LegalAlignas := LegalAlignasStrict.
Module LegalAlignasDefs := LegalAlignasDefsGen (LegalAlignas).
Export LegalAlignas LegalAlignasDefs.

Section legal_alignas.

Context (cenv: composite_env) (ha_env: PTree.t Z).

Lemma aux1: forall T co,
      (fix fm (l : list (ident * type * bool)) : bool :=
          match l with
          | nil => true
          | (_, _, la) :: l' => la && fm l'
          end)
         (map
            (fun it0 : positive * type =>
             let (i0, t0) := it0 in
             (i0, t0,
             type_func.F
               (fun t : type =>
                (hardware_alignof ha_env t <=? alignof cenv t) &&
                match access_mode t with
                | By_value _ => true
                | By_reference => false
                | By_copy => false
                | By_nothing => false
                end)
               (fun (la : bool) (t : type) (n : Z) (a0 : attr) =>
                (hardware_alignof ha_env (Tarray t n a0) <=? alignof cenv (Tarray t n a0)) && ((sizeof cenv t mod alignof cenv t =? 0) && la))
               (fun (la : bool) (id : ident) (a0 : attr) =>
                (hardware_alignof ha_env (Tstruct id a0) <=? alignof cenv (Tstruct id a0)) && la)
               (fun (la : bool) (id : ident) (a0 : attr) =>
                (hardware_alignof ha_env (Tunion id a0) <=? alignof cenv (Tunion id a0)) && la) T t0)) (co_members co)) =
      legal_alignas_composite cenv ha_env T co.
Proof.
  intros; unfold legal_alignas_composite, legal_alignas_members, legal_alignas_type.
  induction (co_members co) as [| [i t] ?].
  + auto.
  + simpl.
    f_equal; auto.
    clear.
    induction t; auto.
    - simpl.
      rewrite IHt.
      auto.
    - simpl.
      destruct (T ! i); auto.
    - simpl.
      destruct (T ! i); auto.
Qed.

Lemma aux2:
    (type_func.Env
          (fun t : type =>
           (hardware_alignof ha_env t <=? alignof cenv t) &&
           match access_mode t with
           | By_value _ => true
           | By_reference => false
           | By_copy => false
           | By_nothing => false
           end)
          (fun (la : bool) (t : type) (n : Z) (a0 : attr) =>
           (hardware_alignof ha_env (Tarray t n a0) <=? alignof cenv (Tarray t n a0)) && ((sizeof cenv t mod alignof cenv t =? 0) && la))
          (fun (la : bool) (id : ident) (a0 : attr) =>
           (hardware_alignof ha_env (Tstruct id a0) <=? alignof cenv (Tstruct id a0)) && la)
          (fun (la : bool) (id : ident) (a0 : attr) =>
           (hardware_alignof ha_env (Tunion id a0) <=? alignof cenv (Tunion id a0)) && la)
          (fun _ : struct_or_union =>
           fix fm (l : list (ident * type * bool)) : bool :=
             match l with
             | nil => true
             | (_, _, la) :: l' => la && fm l'
             end) (composite_reorder.rebuild_composite_elements cenv)) =
    legal_alignas_env cenv ha_env.
Proof.
  intros.
  unfold type_func.Env, type_func.env_rec, legal_alignas_env.
  f_equal.
  extensionality ic.
  destruct ic as [i co].
  extensionality T.
  f_equal.
  apply aux1.
Qed.

End legal_alignas.

Theorem legal_alignas_env_consistency:
  forall (cenv: composite_env) (ha_env: PTree.t Z),
    composite_env_consistent cenv ->
    legal_alignas_env_consistent cenv ha_env (legal_alignas_env cenv ha_env).
Proof.
  intros.
  pose proof @composite_reorder_consistent bool cenv
             (fun t => (hardware_alignof ha_env t <=? alignof cenv t) &&
                match access_mode t with
                | By_value _ => true
                | _ => false
                end)
             (fun la t n a => (hardware_alignof ha_env (Tarray t n a) <=? alignof cenv (Tarray t n a)) && ((sizeof cenv t mod alignof cenv t =? 0) && la))
             (fun la id a => (hardware_alignof ha_env (Tstruct id a) <=? alignof cenv (Tstruct id a)) && la)
             (fun la id a => (hardware_alignof ha_env (Tunion id a) <=? alignof cenv (Tunion id a)) && la)
             (fun _ =>
                fix fm (l: list (ident * type * bool)): bool :=
                match l with
                | nil => true
                | (_, _, la) :: l' => la && (fm l')
                end)
             H
    as HH.
  hnf in HH.
  rewrite aux2 in HH.
  hnf; intros.
  specialize (HH _ _ la H0 H1).
  rewrite HH, aux1; auto.
Qed.

Theorem legal_alignas_env_completeness:
  forall (cenv: composite_env) (ha_env: PTree.t Z),
    legal_alignas_env_complete cenv (legal_alignas_env cenv ha_env).
Proof.
  intros.
  pose proof @composite_reorder_complete bool cenv
             (fun t => (hardware_alignof ha_env t <=? alignof cenv t) &&
                match access_mode t with
                | By_value _ => true
                | _ => false
                end)
             (fun la t n a => (hardware_alignof ha_env (Tarray t n a) <=? alignof cenv (Tarray t n a)) && ((sizeof cenv t mod alignof cenv t =? 0) && la))
             (fun la id a => (hardware_alignof ha_env (Tstruct id a) <=? alignof cenv (Tstruct id a)) && la)
             (fun la id a => (hardware_alignof ha_env (Tunion id a) <=? alignof cenv (Tunion id a)) && la)
             (fun _ =>
                fix fm (l: list (ident * type * bool)): bool :=
                match l with
                | nil => true
                | (_, _, la) :: l' => la && (fm l')
                end)
    as HH.
  hnf in HH.
  rewrite aux2 in HH.
  auto.
Qed.

Section soundness.

Context (cenv: composite_env)
        (ha_env: PTree.t Z)
        (la_env: PTree.t bool)
        (CENV_CONSI: composite_env_consistent cenv)
        (CENV_COSU: composite_env_complete_legal_cosu_type cenv)
        (HA_ENV_CONSI: hardware_alignof_env_consistent cenv ha_env)
        (HA_ENV_COMPL: hardware_alignof_env_complete cenv ha_env)
        (LA_ENV_CONSI: legal_alignas_env_consistent cenv ha_env la_env)
        (LA_ENV_COMPL: legal_alignas_env_complete cenv la_env).

Lemma legal_alignas_type_divide: forall t,
  legal_alignas_type cenv ha_env la_env t = true ->
  (hardware_alignof ha_env t | alignof cenv t).
Proof.
  intros.
  assert (hardware_alignof ha_env t <=? alignof cenv t = true).
  {
    destruct t; simpl in H |- *;
    solve [inv H | rewrite andb_true_iff in H; tauto].
  }
  autorewrite with align in H0.
  auto.
Qed.

Lemma by_value_sound:
  forall t ofs,
    is_aligned cenv ha_env la_env t ofs = true ->
    (exists ch, access_mode t = By_value ch) ->
    align_compatible_rec cenv t ofs.
Proof.
  intros.
  unfold is_aligned, is_aligned_aux, legal_alignas_type, hardware_alignof in H.
  destruct H0 as [ch ?].
  assert ((align_chunk ch <=? alignof cenv t) && true && (ofs mod align_chunk ch =? 0) = true) by
    (destruct t; try solve [inversion H0]; rewrite H0 in H; auto); clear H.
  autorewrite with align in H1.
  destruct H1 as [_ ?].
  eapply align_compatible_rec_by_value; eauto.
Qed.

Theorem legal_alignas_soundness:
  legal_alignas_env_sound cenv ha_env la_env.
Proof.
  pose proof CENV_COSU.
  clear CENV_COSU H.
  intros.
  hnf; intros ? ? _ ?.
  revert ofs H; type_induction t cenv CENV_CONSI; intros.
  + inversion H.
  + eapply by_value_sound; eauto.
    destruct i, s; eexists; try reflexivity.
  + eapply by_value_sound; eauto.
    destruct s; eexists; try reflexivity.
  + eapply by_value_sound; eauto.
    destruct f; eexists; try reflexivity.
  + eapply by_value_sound; eauto.
    eexists; try reflexivity.
  + apply align_compatible_rec_Tarray; intros.
    apply IH; clear IH.
    unfold is_aligned, is_aligned_aux in H |- *.
    Opaque alignof. simpl in H |- *. Transparent alignof.
    autorewrite with align in H |- *.
    destruct H as [[? [? ?]] ?].
    split; auto.
    apply Z.divide_add_r; auto.
    apply Z.divide_mul_l.
    clear H H3.
    apply legal_alignas_type_divide in H2.
    eapply Z.divide_trans; try eassumption.
  + inv H.
  + unfold is_aligned, is_aligned_aux in H, IH.
    Opaque alignof. simpl in H, IH. Transparent alignof.
    destruct (la_env ! id) as [la |] eqn:?H.
    2: {
      rewrite (andb_comm _ false) in H.
      inv H.
    }
    pose proof proj2 (LA_ENV_COMPL id) (ex_intro _ _ H0) as [co ?].
    pose proof proj1 (HA_ENV_COMPL id) (ex_intro _ _ H1) as [ha ?].
    rewrite H1 in IH; rewrite H2 in H.
    rewrite (HA_ENV_CONSI id _ _ H1 H2) in H.
    rewrite (LA_ENV_CONSI id _ _ H1 H0) in H.
    eapply align_compatible_rec_Tstruct; [eassumption | intros].
    pose proof field_offset_aligned _ _ _ _ _ H4 H3.
    unfold field_offset in H4.
    clear H0 H1 H2 H4.
    unfold legal_alignas_composite in *.
    induction IH as [| [i t] ?].
    - inv H3.
    - Opaque alignof. simpl in H0, H3, H. Transparent alignof.
      if_tac in H3.
      * subst i0; inv H3.
        apply H0; simpl.
        autorewrite with align in H |- *.
        destruct H as [[_ [? ?]] [? ?]].
        split; auto.
        apply Z.divide_add_r; auto.
        apply legal_alignas_type_divide in H.
        apply Z.divide_trans with (alignof cenv t0); try eassumption.
      * apply IHIH; auto.
        autorewrite with align in H |- *.
        split; [split |]; tauto.
  + unfold is_aligned, is_aligned_aux in H, IH.
    Opaque alignof. simpl in H, IH. Transparent alignof.
    destruct (la_env ! id) as [la |] eqn:?H.
    2:{
      rewrite (andb_comm _ false) in H.
      inv H.
    }
    pose proof proj2 (LA_ENV_COMPL id) (ex_intro _ _ H0) as [co ?].
    pose proof proj1 (HA_ENV_COMPL id) (ex_intro _ _ H1) as [ha ?].
    rewrite H1 in IH; rewrite H2 in H.
    rewrite (HA_ENV_CONSI id _ _ H1 H2) in H.
    rewrite (LA_ENV_CONSI id _ _ H1 H0) in H.
    eapply align_compatible_rec_Tunion; [eassumption | intros].
    clear H0 H1 H2.
    unfold legal_alignas_composite in *.
    induction IH as [| [i t] ?].
    - inv H3.
    - Opaque alignof. simpl in H0, H3, H. Transparent alignof.
      if_tac in H3.
      * subst i0; inv H3.
        apply H0; simpl.
        autorewrite with align in H |- *.
        destruct H as [[_ [? ?]] [? ?]].
        split; auto.
      * apply IHIH; auto.
        autorewrite with align in H |- *.
        split; [split |]; tauto.
Qed.

End soundness.

End LegalAlignasStrictFacts.

Module LegalAlignasStrong <: LEGAL_ALIGNAS.

Section legal_alignas.

Context (cenv: composite_env) (ha_env: PTree.t Z).

Definition legal_alignas_obs: Type := bool.

Fixpoint legal_alignas_type (la_env: PTree.t bool) t: bool :=
  match t with
  | Tarray t' _ _ => (sizeof cenv t' mod hardware_alignof ha_env t' =? 0) && legal_alignas_type la_env t'
  | Tstruct id _ =>
      match la_env ! id with
      | Some la => la
      | None => false
      end
  | Tunion id _ =>
      match la_env ! id with
      | Some la => la
      | None => false
      end
  | _ => match access_mode t with
         | By_value ch => true
         | _ => false
         end
  end.

Fixpoint legal_alignas_struct_members_rec (la_env: PTree.t bool) (m: members) (pos: Z): bool :=
  match m with
  | nil => true
  | (_, t) :: m' => (align pos (alignof cenv t) mod hardware_alignof ha_env t =? 0) && (legal_alignas_type la_env t) && (legal_alignas_struct_members_rec la_env m' (align pos (alignof cenv t) + sizeof cenv t))
  end.

Fixpoint legal_alignas_union_members_rec (la_env: PTree.t bool) (m: members): bool :=
  match m with
  | nil => true
  | (_, t) :: m' => (legal_alignas_type la_env t) && (legal_alignas_union_members_rec la_env m')
  end.

Definition legal_alignas_composite (la_env: PTree.t bool) (co: composite): bool :=
  match co_su co with
  | Struct => legal_alignas_struct_members_rec la_env (co_members co) 0
  | Union => legal_alignas_union_members_rec la_env (co_members co)
  end.

Definition legal_alignas_env: PTree.t bool :=
  let l := composite_reorder.rebuild_composite_elements cenv in
  fold_right (fun (ic: positive * composite) (T0: PTree.t bool) => let (i, co) := ic in let T := T0 in PTree.set i (legal_alignas_composite T co) T) (PTree.empty _) l.

Definition is_aligned_aux (b: bool) (ha: Z) (ofs: Z) := b && ((ofs mod ha) =? 0).

End legal_alignas.

End LegalAlignasStrong.

Module LegalAlignasStrongFacts: LEGAL_ALIGNAS_FACTS with Module LegalAlignas := LegalAlignasStrong.

Module LegalAlignas := LegalAlignasStrong.
Module LegalAlignasDefs := LegalAlignasDefsGen (LegalAlignas).
Export LegalAlignas LegalAlignasDefs.

Section legal_alignas.

Context (cenv: composite_env) (ha_env: PTree.t Z).

Lemma aux1: forall T co,
  match co_su co with
  | Struct =>
      (fix fm (pos : Z) (l : list (ident * type * bool)) {struct l} : bool :=
         match l with
         | nil => true
         | (_, t, la) :: l' =>
             (align pos (alignof cenv t) mod hardware_alignof ha_env t =? 0) &&
             la && fm (align pos (alignof cenv t) + sizeof cenv t) l'
         end) 0
  | Union =>
      fix fm (l : list (ident * type * bool)) : bool :=
        match l with
        | nil => true
        | (_, _, la) :: l' => la && fm l'
        end
  end
    (map
       (fun it0 : positive * type =>
        let (i0, t0) := it0 in
        (i0, t0,
        type_func.F
          (fun t : type =>
           match access_mode t with
           | By_value _ => true
           | By_reference => false
           | By_copy => false
           | By_nothing => false
           end)
          (fun (la : bool) (t : type) (_ : Z) (_ : attr) =>
           (sizeof cenv t mod hardware_alignof ha_env t =? 0) && la)
          (fun (la : bool) (_ : ident) (_ : attr) => la)
          (fun (la : bool) (_ : ident) (_ : attr) => la) T t0)) 
       (co_members co)) = legal_alignas_composite cenv ha_env T co.
Proof.
  intros; unfold legal_alignas_composite, legal_alignas_type.
  destruct (co_su co).
  {
  generalize 0 at 2 4.
  induction (co_members co) as [| [i t] ?]; intros.
  + auto.
  + simpl.
    f_equal; [f_equal |]; auto.
    clear.
    induction t; auto.
    simpl.
    rewrite IHt.
    auto.
  }
  {
  induction (co_members co) as [| [i t] ?]; intros.
  + auto.
  + simpl.
    f_equal; [f_equal |]; auto.
    clear.
    induction t; auto.
    simpl.
    rewrite IHt.
    auto.
  }
Qed.

Lemma aux2:
    (type_func.Env
                  (fun t : type =>
                   match access_mode t with
                   | By_value _ => true
                   | By_reference => false
                   | By_copy => false
                   | By_nothing => false
                   end)
                  (fun (la : bool) (t : type) (_ : Z) (_ : attr) =>
                   (sizeof cenv t mod hardware_alignof ha_env t =? 0) && la)
                  (fun (la : bool) (_ : ident) (_ : attr) => la)
                  (fun (la : bool) (_ : ident) (_ : attr) => la)
                  (fun su : struct_or_union =>
                   match su with
                   | Struct =>
                       (fix
                        fm (pos : Z) (l : list (ident * type * bool)) {struct l} :
                          bool :=
                          match l with
                          | nil => true
                          | (_, t, la) :: l' =>
                              (align pos (alignof cenv t)
                               mod hardware_alignof ha_env t =? 0) && la &&
                              fm (align pos (alignof cenv t) + sizeof cenv t) l'
                          end) 0
                   | Union =>
                       fix fm (l : list (ident * type * bool)) : bool :=
                         match l with
                         | nil => true
                         | (_, _, la) :: l' => la && fm l'
                         end
                   end) (composite_reorder.rebuild_composite_elements cenv)) =
    legal_alignas_env cenv ha_env.
Proof.
  intros.
  unfold type_func.Env, type_func.env_rec, legal_alignas_env.
  f_equal.
  extensionality ic.
  destruct ic as [i co].
  extensionality T.
  f_equal.
  apply aux1.
Qed.

End legal_alignas.

Theorem legal_alignas_env_consistency:
  forall (cenv: composite_env) (ha_env: PTree.t Z),
    composite_env_consistent cenv ->
    legal_alignas_env_consistent cenv ha_env (legal_alignas_env cenv ha_env).
Proof.
  intros.
  pose proof @composite_reorder_consistent bool cenv
             (fun t =>
                match access_mode t with
                | By_value _ => true
                | _ => false
                end)
             (fun la t n a => ((sizeof cenv t mod hardware_alignof ha_env t =? 0) && la))
             (fun la id a => la)
             (fun la id a => la)
             (fun su =>
                match su with
                | Struct =>
                   (fix fm (pos: Z) (l: list (ident * type * bool)) : bool :=
                    match l with
                    | nil => true
                    | (_, t, la) :: l' => (align pos (alignof cenv t) mod hardware_alignof ha_env t =? 0) && la && (fm (align pos (alignof cenv t) + sizeof cenv t) l')
                    end) 0
                | Union =>
                   (fix fm (l: list (ident * type * bool)) : bool :=
                    match l with
                    | nil => true
                    | (_, t, la) :: l' => la && (fm l')
                    end)
                end)
             H
    as HH.
  hnf in HH.
  rewrite aux2 in HH.
  hnf; intros.
  specialize (HH _ _ la H0 H1).
  rewrite HH, <- aux1; auto.
Qed.

Theorem legal_alignas_env_completeness:
  forall (cenv: composite_env) (ha_env: PTree.t Z),
    legal_alignas_env_complete cenv (legal_alignas_env cenv ha_env).
Proof.
  intros.
  pose proof @composite_reorder_complete bool cenv
             (fun t =>
                match access_mode t with
                | By_value _ => true
                | _ => false
                end)
             (fun la t n a => ((sizeof cenv t mod hardware_alignof ha_env t =? 0) && la))
             (fun la id a => la)
             (fun la id a => la)
             (fun su =>
                match su with
                | Struct =>
                   (fix fm (pos: Z) (l: list (ident * type * bool)) : bool :=
                    match l with
                    | nil => true
                    | (_, t, la) :: l' => (align pos (alignof cenv t) mod hardware_alignof ha_env t =? 0) && la && (fm (align pos (alignof cenv t) + sizeof cenv t) l')
                    end) 0
                | Union =>
                   (fix fm (l: list (ident * type * bool)) : bool :=
                    match l with
                    | nil => true
                    | (_, t, la) :: l' => la && (fm l')
                    end)
                end)
    as HH.
  hnf in HH.
  rewrite aux2 in HH.
  auto.
Qed.

Section soundness.

Context (cenv: composite_env)
        (ha_env: PTree.t Z)
        (la_env: PTree.t bool)
        (CENV_CONSI: composite_env_consistent cenv)
        (CENV_COSU: composite_env_complete_legal_cosu_type cenv)
        (HA_ENV_CONSI: hardware_alignof_env_consistent cenv ha_env)
        (HA_ENV_COMPL: hardware_alignof_env_complete cenv ha_env)
        (LA_ENV_CONSI: legal_alignas_env_consistent cenv ha_env la_env)
        (LA_ENV_COMPL: legal_alignas_env_complete cenv la_env).

Lemma by_value_sound:
  forall t ofs,
    is_aligned cenv ha_env la_env t ofs = true ->
    (exists ch, access_mode t = By_value ch) ->
    align_compatible_rec cenv t ofs.
Proof.
  intros.
  unfold is_aligned, is_aligned_aux, legal_alignas_type, hardware_alignof in H.
  destruct H0 as [ch ?].
  assert ((ofs mod align_chunk ch =? 0) = true) by
    (destruct t; try solve [inversion H0]; rewrite H0 in H; auto); clear H.
  autorewrite with align in H1.
  eapply align_compatible_rec_by_value; eauto.
Qed.

Theorem legal_alignas_soundness:
  legal_alignas_env_sound cenv ha_env la_env.
Proof.
  intros.
  hnf; intros.
  revert ofs H H0; type_induction t cenv CENV_CONSI; intros.
  + inversion H0.
  + eapply by_value_sound; eauto.
    destruct i, s; eexists; try reflexivity.
  + eapply by_value_sound; eauto.
    destruct s; eexists; try reflexivity.
  + eapply by_value_sound; eauto.
    destruct f; eexists; try reflexivity.
  + eapply by_value_sound; eauto.
    eexists; try reflexivity.
  + apply align_compatible_rec_Tarray; intros.
    apply IH; clear IH; [auto |].
    unfold is_aligned, is_aligned_aux in H0 |- *.
    simpl in H0 |- *.
    autorewrite with align in H0 |- *.
    destruct H0 as [[? ?] ?].
    split; auto.
    apply Z.divide_add_r; auto.
    apply Z.divide_mul_l; auto.
  + inv H.
  + unfold is_aligned, is_aligned_aux in H0, IH.
    simpl in H, H0, IH.
    destruct (la_env ! id) as [la |] eqn:?H; [| inv H0].
    pose proof proj2 (LA_ENV_COMPL id) (ex_intro _ _ H1) as [co ?].
    pose proof proj1 (HA_ENV_COMPL id) (ex_intro _ _ H2) as [ha ?].
    pose proof CENV_COSU _ _ H2.
    rewrite H2 in IH, H; rewrite H3 in H0.
    rewrite (HA_ENV_CONSI id _ _ H2 H3) in H0.
    rewrite (LA_ENV_CONSI id _ _ H2 H1) in H0.
    autorewrite with align in H0 |- *.
    destruct H0.
    unfold legal_alignas_composite in H0.
    destruct (co_su co); [| inv H].
    eapply align_compatible_rec_Tstruct; [eassumption | intros].
    unfold field_offset in H7.
    clear H H1 H2 H3.
    revert H0 H4 H5 H6 H7; generalize 0;
    induction IH as [| [i t] ?]; intros.
    - inv H6.
    - simpl in H, H0, H4, H5, H6, H7.
      if_tac in H6.
      * subst i0; inv H6; inv H7.
        autorewrite with align in H4, H5, H0 |- *.
        destruct H0 as [[? ?] ?], H4 as [? ?], H5 as [? ?].
        apply H; simpl; [tauto |].
        autorewrite with align.
        split; auto.
        apply Z.divide_add_r; auto.
      * autorewrite with align in H0, H4, H5.
        destruct H4, H5.
        apply (IHIH (align z (alignof cenv t) + sizeof cenv t)); auto.
        tauto.
  + unfold is_aligned, is_aligned_aux in H0, IH.
    simpl in H, H0, IH.
    destruct (la_env ! id) as [la |] eqn:?H; [| inv H0].
    pose proof proj2 (LA_ENV_COMPL id) (ex_intro _ _ H1) as [co ?].
    pose proof proj1 (HA_ENV_COMPL id) (ex_intro _ _ H2) as [ha ?].
    pose proof CENV_COSU _ _ H2.
    rewrite H2 in IH, H; rewrite H3 in H0.
    rewrite (HA_ENV_CONSI id _ _ H2 H3) in H0.
    rewrite (LA_ENV_CONSI id _ _ H2 H1) in H0.
    autorewrite with align in H0 |- *.
    destruct H0.
    unfold legal_alignas_composite in H0.
    destruct (co_su co); [inv H |].
    eapply align_compatible_rec_Tunion; [eassumption | intros].
    clear H H1 H2 H3.
    revert H0 H4 H5 H6;
    induction IH as [| [i t] ?]; intros.
    - inv H6.
    - simpl in H, H0, H4, H5, H6.
      if_tac in H6.
      * subst i0; inv H6.
        autorewrite with align in H4, H5, H0 |- *.
        destruct H0 as [? ?], H4 as [? ?], H5 as [? ?].
        apply H; simpl; [tauto |].
        autorewrite with align.
        split; auto.
      * autorewrite with align in H0, H4, H5.
        destruct H4, H5.
        apply IHIH; auto.
        tauto.
Qed.

End soundness.

End LegalAlignasStrongFacts.

Module Export LegalAlignasFacts := LegalAlignasStrongFacts.



