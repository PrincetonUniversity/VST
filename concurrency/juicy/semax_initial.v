Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import VST.msl.Coqlib2.
Require Import VST.msl.eq_dec.
Require Import VST.msl.seplog.
Require Import VST.msl.age_to.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_mem.
Require Import VST.veric.juicy_mem_lemmas.
Require Import VST.veric.semax_prog.
Require Import VST.veric.compcert_rmaps.
Require Import VST.veric.Clight_core.
Require Import VST.veric.Clightcore_coop.
Require Import VST.veric.semax.
Require Import VST.veric.semax_ext.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.initial_world.
Require Import VST.veric.juicy_extspec.
Require Import VST.veric.tycontext.
Require Import VST.veric.semax_ext.
Require Import VST.veric.res_predicates.
Require Import VST.veric.mem_lessdef.
Require Import VST.veric.seplog.
Require Import VST.veric.juicy_safety.
Require Import VST.floyd.coqlib3.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.juicy.semax_conc_pred.
Require Import VST.concurrency.juicy.semax_conc.
Require Import VST.concurrency.juicy.juicy_machine.
Require Import VST.concurrency.compiler.mem_equiv.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.scheduler.
Require Import VST.concurrency.common.addressFiniteMap.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.juicy.JuicyMachineModule.
Require Import VST.concurrency.juicy.sync_preds_defs.
Require Import VST.concurrency.juicy.semax_invariant.
Require Import VST.concurrency.juicy.sync_preds.

Set Bullet Behavior "Strict Subproofs".

(*+ Initial state *)

Lemma initmem_maxedmem:
  forall prog m, @Genv.init_mem Clight.fundef type  prog = Some m -> 
    mem_equiv.mem_equiv (maxedmem m) m.
Proof.
intros.
unfold Genv.init_mem in H.
assert (mem_equiv.mem_equiv (maxedmem Mem.empty) Mem.empty).
{ constructor; auto; intros ?; reflexivity. }
forget Mem.empty as m0.
revert m0 m H H0; induction (AST.prog_defs prog); intros.
{ simpl in H. inv H; auto. }
simpl in H.
destruct (Genv.alloc_global (Genv.globalenv prog) m0 a) eqn:?H; try discriminate.
apply IHl in H; auto.
clear - H1 H0.
destruct a.
destruct g; simpl in H1.
- destruct (Mem.alloc m0 0 1) eqn:?H.
  constructor; auto; intros ?; try reflexivity.
  + extensionality o.
    rewrite !getCurPerm_correct.
    unfold maxedmem.
    rewrite restrPermMap_Cur, getMaxPerm_correct.
    destruct (adr_range_dec (b, 0) 1 (b0, o)).
    * destruct a; subst.
      pose proof (access_drop_1 _ _ _ _ _ _ H1 _ H3) as Hm1.
      pose proof (Hm1 Cur) as [? Hm1c]; pose proof (Hm1 Max) as [? Hm1m].
      unfold access_at in *; unfold permission_at; simpl in *.
      rewrite Hm1c, Hm1m; auto.
    * pose proof (access_drop_3 _ _ _ _ _ _ H1 b0 o) as Hm1.
      pose proof (Hm1 Cur) as Hm1c; pose proof (Hm1 Max) as Hm1m.
      unfold adr_range in *; spec Hm1c; [lia|]; spec Hm1m; [lia|].
      unfold access_at in *; unfold permission_at; simpl in *.
      rewrite <- Hm1c, <- Hm1m.
      pose proof (alloc_access_other _ _ _ _ _ H b0 o) as Hm.
      pose proof (Hm Cur) as Hmc; pose proof (Hm Max) as Hmm.
      unfold adr_range in *; spec Hmc; [lia|]; spec Hmm; [lia|].
      unfold access_at in *; simpl in *.
      rewrite <- Hmc, <- Hmm.
      destruct H0.
      specialize (cur_eqv b0).
      apply equal_f with o in cur_eqv.
      rewrite !getCurPerm_correct in cur_eqv.
      unfold maxedmem in cur_eqv.
      rewrite restrPermMap_Cur, getMaxPerm_correct in cur_eqv.
      auto.
  + extensionality o.
    rewrite !getMaxPerm_correct.
    unfold maxedmem.
    rewrite restrPermMap_Max, getMaxPerm_correct.
    auto.
- destruct (Mem.alloc m0 0 (init_data_list_size (gvar_init v))) eqn:?H.
  destruct (store_zeros m b 0 (init_data_list_size (gvar_init v))) eqn:?H; try discriminate.
  destruct (Genv.store_init_data_list (Genv.globalenv prog) m2 b 0 (gvar_init v)) eqn:?H; try discriminate.
  apply initialize.store_init_data_list_access in H3.
  apply store_zeros_access in H2.
  rewrite H2 in H3; clear dependent m2.
  constructor; auto; intros ?; try reflexivity.
  + extensionality o.
    rewrite !getCurPerm_correct.
    unfold maxedmem.
    rewrite restrPermMap_Cur, getMaxPerm_correct.
    destruct (adr_range_dec (b, 0) (init_data_list_size (gvar_init v)) (b0, o)).
    * destruct a; subst.
      pose proof (access_drop_1 _ _ _ _ _ _ H1 _ H4) as Hm1.
      pose proof (Hm1 Cur) as [? Hm1c]; pose proof (Hm1 Max) as [? Hm1m].
      unfold access_at in *; unfold permission_at; simpl in *.
      rewrite Hm1c, Hm1m; auto.
    * pose proof (access_drop_3 _ _ _ _ _ _ H1 b0 o) as Hm1.
      pose proof (Hm1 Cur) as Hm1c; pose proof (Hm1 Max) as Hm1m.
      unfold adr_range in *; spec Hm1c; [lia|]; spec Hm1m; [lia|].
      unfold access_at in *; unfold permission_at; simpl in *.
      rewrite <- Hm1c, <- Hm1m.
      apply equal_f with (b0, o) in H3.
      pose proof (equal_f H3 Cur) as Hm3c; pose proof (equal_f H3 Max) as Hm3m; simpl in *.
      rewrite <- Hm3c, <- Hm3m.
      pose proof (alloc_access_other _ _ _ _ _ H b0 o) as Hm.
      pose proof (Hm Cur) as Hmc; pose proof (Hm Max) as Hmm.
      unfold adr_range in *; spec Hmc; [lia|]; spec Hmm; [lia|].
      unfold access_at in *; simpl in *.
      rewrite <- Hmc, <- Hmm.
      destruct H0.
      specialize (cur_eqv b0).
      apply equal_f with o in cur_eqv.
      rewrite !getCurPerm_correct in cur_eqv.
      unfold maxedmem in cur_eqv.
      rewrite restrPermMap_Cur, getMaxPerm_correct in cur_eqv.
      auto.
  + extensionality o.
    rewrite !getMaxPerm_correct.
    unfold maxedmem.
    rewrite restrPermMap_Max, getMaxPerm_correct.
    auto.
Qed.

Section Initial_State.
  Variables
    (CS : compspecs) (V : varspecs) (G : funspecs)
    (ext_link : string -> ident) (prog : Clight.program)
    (all_safe : semax_prog.semax_prog (Concurrent_Espec unit CS ext_link) prog tt V G)
    (init_mem_not_none : Genv.init_mem prog <> None).

  Definition Jspec := @OK_spec (Concurrent_Espec unit CS ext_link).

  Definition init_m : { m | Genv.init_mem prog = Some m } :=
    match Genv.init_mem prog as y return (y <> None -> {m : mem | y = Some m}) with
    | Some m => fun _ => exist _ m eq_refl
    | None => fun H => (fun Heq => False_rect _ (H Heq)) eq_refl
    end init_mem_not_none.

  Definition initial_state (n : nat) (sch : schedule) : cm_state :=
    (proj1_sig init_m,
     (nil, sch,
      let spr := semax_prog_rule
                   (Concurrent_Espec unit CS ext_link) V G prog
                   (proj1_sig init_m) 0 tt (allows_exit ext_link) all_safe (proj2_sig init_m) in
      let q := projT1 (projT2 spr) in
      let jm : juicy_mem := proj1_sig (snd (projT2 (projT2 spr)) n) in
      @OrdinalPool.mk LocksAndResources (ClightSemanticsForMachines.ClightSem (globalenv prog))
        (pos.mkPos (le_n 1))
        (* (fun _ => Kresume q Vundef) *)
        (fun _ => Krun q)
        (fun _ => m_phi jm)
        (addressFiniteMap.AMap.empty _)
        (wsat_rmap (m_phi jm))
     )
    ).

  Lemma personal_mem_of_same_jm (tp : jstate (globalenv prog)) jm i (cnti : ThreadPool.containsThread tp i) mc :
    (ThreadPool.getThreadR cnti = m_phi jm) ->
    m_dry (@personal_mem (m_dry jm) (getThreadR cnti) mc) = m_dry jm.
  Proof.
    unfold personal_mem in *.
    simpl.
    intros E.
    apply mem_ext; auto.
    apply juicyRestrictCur_unchanged.
    rewrite E.
    symmetry.
    destruct jm; simpl; auto.
  Qed.

  Theorem initial_invariant n sch : state_invariant Jspec G n (initial_state n sch).
  Proof.
    unfold initial_state.
    destruct init_m as [m Hm]; simpl proj1_sig; simpl proj2_sig.
    set (spr := semax_prog_rule (Concurrent_Espec unit CS ext_link) V G prog m 0 tt (allows_exit ext_link) all_safe Hm).
    set (q := projT1 (projT2 spr)).
    destruct (snd (projT2 (projT2 spr))) as (jm & D & H & E & (z & W & Hdry & Hext) & A & NL & MFS & FA).
    match goal with |- _ _ _ (_, (_, ?TP)) => set (tp := TP) end.

    (*! compatibility of memories *)
    assert (compat : mem_compatible_with tp m (m_phi z)).
    {
      constructor.
      + apply AllJuice with (m_phi jm) None (m_phi jm).
        * unfold join_threads.
          unfold getThreadsR; simpl.
          exists (id_core (m_phi jm)). {
            split.
            - apply join_comm.
              apply id_core_unit.
            - apply id_core_identity.
          }
        * reflexivity.
        * constructor.
        * apply W.
      + subst m.
        rewrite Hdry.
        apply mem_cohere'_juicy_mem.
      + intros b ofs.
        match goal with |- context [ssrbool.isSome ?x] => destruct x as [ phi | ] eqn:Ephi end.
        intros _.
        unfold tp in Ephi; simpl in Ephi.
        discriminate.
        { unfold is_true. simpl. congruence. }
      + intros loc L. (* sh psh P z *)
        pose proof (NL loc) as NL'.
        specialize (L 0). spec L. pose proof lksize.LKSIZE_pos; lia. destruct L as [sh [psh [P L]]].
        specialize (NL' sh psh lksize.LKSIZE 0 P). rewrite fst_snd0 in L.
        simpl in *.
        apply rmap_order in Hext as (? & Hr & _); rewrite Hr in *; contradiction.
      + hnf.
        simpl.
        intros ? F.
        inversion F.
    } (* end of mcompat *)

    assert (En : level (m_phi z) = n). {
      clear dependent tp. rewrite level_juice_level_phi in *; apply join_level in W as []; congruence.
    }

    apply state_invariant_c with (mcompat := compat).
    - (*! level *)
      auto.

    - (*! env_coherence *)
      split.
      + eapply pred_upclosed, MFS; auto.
      + exists prog, tt, CS, V; split3; auto.
        eapply pred_upclosed; eauto.
(*    - clear - Hm.
      split.
      pose proof ( Genv.initmem_inject _ Hm).
      apply initmem_maxedmem in Hm.
      red. rewrite Hm. apply H.
      apply Genv.init_mem_genv_next in Hm. rewrite <- Hm.
     unfold globalenv. simpl. apply Ple_refl. *)
    - (*! external coherence *)
      subst tp; clear - W E.
      apply ghost_of_join in W.
      unfold wsat_rmap in W; rewrite ghost_of_make_rmap in W.
      inv W.
      { rewrite <- H0 in E; discriminate. }
      assert (a3 = a1) by (inv H3; auto); subst.
      rewrite <- H in E; inv E.
      unfold ext_compat; rewrite <- H2; eexists; constructor; constructor.
      instantiate (1 := (_, _)).
      split; simpl; [apply ext_ref_join | split; eauto].

    - (*! lock sparsity (no locks at first) *)
      intros l1 l2.
      rewrite find_empty.
      tauto.

    - (*! lock coherence (no locks at first) *)
      intros lock.
      rewrite find_empty.
      clear - Hext NL.
      apply rmap_order in Hext as (_ & <- & _).
      intros (? & ? & ? & ? & ?); eapply NL; eauto.

    - (*! safety of the only thread *)
      intros i cnti ora.
      destruct (getThreadC cnti) as [c|c|c v|v1 v2] eqn:Ec; try discriminate; [].
      destruct i as [ | [ | i ]]; [| now inversion cnti | now inversion cnti].
      (* the initial juicy has got to be the same as the one given in initial_mem *)
      assert (Ejm: jm = jm_ cnti compat).
      {
        apply juicy_mem_ext; [|reflexivity].
        - unfold jm_.
          subst; symmetry; apply personal_mem_of_same_jm; auto.
      }
      rewrite <-Ejm.
      simpl in Ec. replace c with q in * by congruence.
      destruct ora; apply A.

    - (* well-formedness *)
      intros i cnti.
      constructor.

    - (* only one thread running *)
      intros F; exfalso. simpl in F. lia.

    - (* inv_compatible (wsat is set up) *)
      exists (id_core (m_phi jm)), (wsat_rmap (m_phi jm)).
      split; [eexists; apply id_core_unit|].
      split; [|apply wsat_rmap_wsat].
      destruct (join_assoc (join_comm (id_core_unit (m_phi jm))) W) as (? & ? & ?).
      apply identity_unit; eauto.
      apply id_core_identity.
  Qed.

End Initial_State.
