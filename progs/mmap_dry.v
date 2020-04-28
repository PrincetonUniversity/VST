Require Import VST.progs.mmap_specs.
Require Import VST.floyd.proofauto.
Require Import VST.sepcomp.extspec.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.initial_world.
Require Import VST.veric.ghost_PCM.
Require Import VST.veric.SequentialClight.
Require Import VST.progs.conclib.
Require Import VST.progs.dry_mem_lemmas.
Require Import VST.veric.mem_lessdef.

Section Mmap_Dry.

Definition bytes_to_memvals li := concat (map (fun i => encode_val Mint8unsigned (Vubyte i)) li).

Lemma bytes_to_memvals_length : forall li, Zlength (bytes_to_memvals li) = Zlength li.
Proof.
  intros.
  rewrite !Zlength_correct; f_equal.
  unfold bytes_to_memvals.
  rewrite <- map_map, encode_vals_length, map_length; auto.
Qed.

Definition mmap_pre (m : mem) (len : Z) := 0 <= len <= Ptrofs.max_unsigned.

Definition mmap_post (m0 m : mem) r (len : Z) :=
  let res := Mem.alloc m0 0 len in m = fst res /\ r = Vptr (snd res) Ptrofs.zero.

Context {CS : compspecs} (ext_link : String.string -> ident).

Instance Espec : OracleKind := mmap_Espec ext_link.

Definition mmap_ext_spec := OK_spec.

Program Definition mmap_dry_spec : external_specification mem external_function unit.
Proof.
  unshelve econstructor.
  - intro e.
    pose (ext_spec_type mmap_ext_spec e) as T; simpl in T.
    destruct (oi_eq_dec _ _); [|exact False];
      match goal with T := (_ * ?A)%type |- _ => exact (mem * A)%type end.
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|contradiction].
    destruct X as (m0 & _ & w).
    exact ((X1 = [nullval; Vint (Int.repr w); Vint (Int.repr 6); Vint (Int.repr 32); Vint (Int.repr (-1)); Vint (Int.repr 0)]) /\
      m0 = X2 /\ mmap_pre X2 w).
  - simpl; intros.
    destruct (oi_eq_dec _ _); [|contradiction].
    destruct X as (m0 & _ & w).
    destruct X1; [|exact False].
    exact (mmap_post m0 X2 v w).
  - intros; exact True.
Defined.

Definition dessicate : forall ef (jm : juicy_mem), ext_spec_type mmap_ext_spec ef -> ext_spec_type mmap_dry_spec ef.
Proof.
  simpl; intros.
  destruct (oi_eq_dec _ _); [|assumption].
  destruct X as [_ X]; exact (m_dry jm, X).
Defined.

Theorem juicy_dry_specs : juicy_dry_ext_spec _ mmap_ext_spec mmap_dry_spec dessicate.
Proof.
  split; [|split]; try reflexivity; simpl.
  - unfold funspec2pre, dessicate; simpl.
    intros ?; if_tac; [|contradiction].
    intros; subst.
    destruct t as (? & ? & len); simpl in *.
    destruct H1 as (? & phi0 & phi1 & J & Hpre & Hr & Hext).
    destruct e; inv H; simpl in *.
    destruct vl; try contradiction; simpl in *.
    destruct H0, vl; try contradiction; simpl in *.
    destruct H0, vl; try contradiction; simpl in *.
    destruct H1, vl; try contradiction; simpl in *.
    destruct H3, vl; try contradiction; simpl in *.
    destruct H4, vl; try contradiction; simpl in *.
    destruct H5, vl; try contradiction; simpl in *.
    destruct Hpre as ([Hbounds _] & Hargs & Hemp).
    repeat (let H := fresh "Harg" in destruct Hargs as ([H _] & Hargs); hnf in H).
    split.
    { rewrite Harg, Harg0, Harg1, Harg2, Harg3, Harg4.
      rewrite eval_id_same.
      repeat (rewrite !eval_id_other by discriminate; rewrite eval_id_same); auto. }
    split; auto.
  - unfold funspec2pre, funspec2post, dessicate; simpl.
    intros ?; if_tac; [|contradiction].
    intros; subst.
    destruct H0 as (_ & vl & z0 & ? & _ & phi0 & phi1' & J & Hpre & ? & ?).
    destruct t as (phi1 & t); subst; simpl in *.
    destruct t as (? & len); simpl in *.
    destruct Hpre as ([Hbounds _] & Hargs & Hemp).
    destruct v; try contradiction.
    destruct H4 as [Hmem ?]; subst.
    assert (forall ofs : Z, phi0 @ (Mem.nextblock (m_dry jm0), ofs) = NO Share.bot bot_unreadable) as Hno.
    { intros.
      destruct jm0; simpl in *.
      apply (resource_at_join _ _ _ (Mem.nextblock m, ofs)) in J.
      rewrite JMalloc in J by (simpl; Lia.lia).
      inv J; auto.
      apply join_Bot in RJ as []; subst.
      f_equal; apply proof_irr. }
    exists (age_to.age_to (level jm) (after_alloc 0 len (Mem.nextblock (m_dry jm0)) phi0 Hno)),
        (age_to.age_to (level jm) phi1').
    destruct (join_level _ _ _ J).
    split.
    + apply resource_at_join2.
      * rewrite age_to.level_age_to; auto.
        unfold after_alloc; rewrite level_make_rmap.
        rewrite level_juice_level_phi; lia.
      * rewrite age_to.level_age_to; auto.
        rewrite level_juice_level_phi; lia.
      * intros.
        eapply rebuild_alloc; eauto.
        rewrite Hmem; apply mem_equiv_refl.
      * rewrite !age_to_resource_at.age_to_ghost_of.
        unfold after_alloc; rewrite ghost_of_make_rmap.
         rewrite H3. admit.
    + split3.
      * exists (Vptr (Mem.nextblock (m_dry jm0)) Ptrofs.zero).
        split3; simpl.
        { split; auto. }
        { split; auto; split; unfold liftx; simpl; unfold lift; auto; discriminate. }
        unfold SEPx in *; simpl in *.
        eapply semax_call.after_alloc_block in Hemp.
        assert (predicates_hered.derives (seplog.emp * mapsto_memory_block.memory_block Share.top len (Vptr (Mem.nextblock (m_dry jm0)) Ptrofs.zero))
          (data_at_ Tsh (tarray tuchar len) (Vptr (Mem.nextblock (m_dry jm0)) Ptrofs.zero) * seplog.emp)) as Hentails.
        { rewrite sepcon_comm; apply sepcon_derives; auto.
          rewrite <- memory_block_data_at_.
          simpl sizeof.
          rewrite Z.max_r, Z.mul_1_l by lia; auto.
          { repeat split; auto; simpl.
            * rewrite Z.max_r, Z.mul_1_l, Ptrofs.unsigned_zero by lia; rep_lia.
            * constructor; intros.
              econstructor; simpl; eauto; simpl.
              apply Z.divide_1_l. } }
        eapply Hentails, age_to.age_to_pred; eauto.
        { rep_lia. }
      * eapply necR_trans; eauto; apply age_to.age_to_necR.
      * rewrite H3; eexists; constructor; constructor.
        instantiate (1 := (_, _)).
        constructor; simpl; [|constructor; auto].
        apply ext_ref_join.
Admitted.

Instance mem_evolve_refl : Reflexive mem_evolve.
Proof.
  repeat intro.
  destruct (access_at x loc Cur); auto.
  destruct p; auto.
Qed.

Lemma dry_spec_mem : ext_spec_mem_evolve _ mmap_dry_spec.
Proof.
  intros ??????????? Hpre Hpost.
  simpl in Hpre, Hpost.
  simpl in *.
  if_tac in Hpre; [|contradiction].
  destruct w as (m0 & _ & ?).
  destruct Hpre as (_ & ? & Hpre); subst.
  destruct v; try contradiction.
  destruct Hpost; subst.
  intros (b0, ofs0).
  destruct (Mem.alloc m 0 z0) eqn: Halloc; simpl.
  destruct (adr_range_dec (b1, 0) z0 (b0, ofs0)).
  - destruct a; subst; erewrite (alloc_access_same _ _ _ m0) by eauto.
    rewrite nextblock_access_empty; auto.
    erewrite <- Mem.alloc_result by eauto; Lia.lia.
  - assert (b0 <> b1 \/ ofs0 < 0 \/ ofs0 >= z0).
    { destruct (eq_dec b0 b1); auto.
      destruct (zlt ofs0 0); auto.
      destruct (zlt ofs0 z0); auto.
      contradiction n; unfold adr_range; repeat split; auto; lia. }
    erewrite <- !(alloc_access_other _ _ _ m0) by eauto.
    destruct access_at; auto.
    destruct p; auto.
Qed.

End Mmap_Dry.
