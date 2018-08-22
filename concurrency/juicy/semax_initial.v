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
Require Import VST.veric.Clight_new.
Require Import VST.veric.Clightnew_coop.
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

Section Initial_State.
  Variables
    (CS : compspecs) (V : varspecs) (G : funspecs)
    (ext_link : string -> ident) (prog : Clight.program)
    (all_safe : semax_prog.semax_prog (Concurrent_Espec unit CS ext_link) prog V G)
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
      let spr := semax_prog_rule'
                   (Concurrent_Espec unit CS ext_link) V G prog
                   (proj1_sig init_m) 0 all_safe (proj2_sig init_m) in
      let q : corestate := projT1 (projT2 spr) in
      let jm : juicy_mem := proj1_sig (snd (projT2 (projT2 spr)) n tt) in
      @OrdinalPool.mk LocksAndResources (ClightSemanticsForMachines.Clight_newSem (globalenv prog))
        (pos.mkPos (le_n 1))
        (* (fun _ => Kresume q Vundef) *)
        (fun _ => Krun q)
        (fun _ => m_phi jm)
        (addressFiniteMap.AMap.empty _)
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
    set (spr := semax_prog_rule' (Concurrent_Espec unit CS ext_link) V G prog m 0 all_safe Hm).
    set (q := projT1 (projT2 spr)).
    set (jm := proj1_sig (snd (projT2 (projT2 spr)) n tt)).
    match goal with |- _ _ _ (_, (_, ?TP)) => set (tp := TP) end.

    (*! compatibility of memories *)
    assert (compat : mem_compatible_with tp m (m_phi jm)).
    {
      constructor.
      + apply AllJuice with (m_phi jm) None.
        * change (proj1_sig (snd (projT2 (projT2 spr)) n tt)) with jm.
          unfold join_threads.
          unfold getThreadsR.

          match goal with |- _ ?l _ => replace l with (m_phi jm :: nil) end; swap 1 2. {
            simpl.
            set (a := m_phi jm).
            match goal with |- context [m_phi ?jm] => set (b := m_phi jm) end.
            replace b with a by reflexivity. clear. clearbody a.
            reflexivity.
            (* unfold fintype.ord_enum, eqtype.insub, seq.iota in *.
            simpl.
            destruct ssrbool.idP as [F|F]. reflexivity. exfalso. auto. *)
          }
          exists (core (m_phi jm)). {
            split.
            - apply join_comm.
              apply core_unit.
            - apply core_identity.
          }

        * reflexivity.
        * constructor.
      + destruct (snd (projT2 (projT2 spr))) as [jm' [D H]]; unfold jm; clear jm; simpl.
        subst m.
        apply mem_cohere'_juicy_mem.
      + intros b ofs.
        match goal with |- context [ssrbool.isSome ?x] => destruct x as [ phi | ] eqn:Ephi end; swap 1 2.
        { unfold is_true. simpl. congruence. } intros _.
        unfold tp in Ephi; simpl in Ephi.
        discriminate.
      + intros loc L. (* sh psh P z *)
        destruct (snd (projT2 (projT2 spr))) as (jm' & D & H & E & A & NL & MFS).
        unfold jm in *; clear jm; simpl in L |- *.
        pose proof (NL loc) as NL'.
        specialize (L 0). spec L. pose proof lksize.LKSIZE_pos; omega. destruct L as [sh [psh [P L]]].
        specialize (NL' sh psh lksize.LKSIZE 0 P). rewrite fst_snd0 in L.
        rewrite L in NL'. contradiction NL'; auto.
      + hnf.
        simpl.
        intros ? F.
        inversion F.
    } (* end of mcompat *)

    assert (En : level (m_phi jm) = n). {
      unfold jm; clear.
      match goal with
        |- context [proj1_sig ?x] => destruct x as (jm' & jmm & lev & S & nolocks)
      end; simpl.
      rewrite level_juice_level_phi in *.
      auto.
    }

    apply state_invariant_c with (PHI := m_phi jm) (mcompat := compat).
    - (*! level *)
      auto.

    - (*! env_coherence *)
      destruct (snd (projT2 (projT2 spr))) as (jm' & D & H & E & A & NL & MFS & FA).
      simpl in jm. unfold jm.
      split.
      + apply MFS.
      + exists prog, CS, V. auto.

    - (*! external coherence *)
      destruct (snd (projT2 (projT2 spr))) as (jm' & D & H & E & A & NL & MFS & FA).
      simpl in jm. unfold jm.
      subst jm tp; clear - E.
      assert (@ghost.valid (ext_PCM unit) (Some (Tsh, Some tt), Some (Some tt))).
      { simpl; split; [apply Share.nontrivial|].
        eexists; apply join_comm, core_unit. }
      eexists; apply join_comm, own.singleton_join_gen with (k := O).
      erewrite nth_error_nth in E by (apply nth_error_Some; rewrite E; discriminate).
      inversion E as [Heq]; rewrite Heq.
      instantiate (1 := (_, _)); constructor; constructor; simpl; [|repeat constructor].
      unshelve constructor; [| apply H | repeat constructor].

    - (*! lock sparsity (no locks at first) *)
      intros l1 l2.
      rewrite find_empty.
      tauto.

    - (*! lock coherence (no locks at first) *)
      intros lock.
      rewrite find_empty.
      (* split; *) intros (sh & sh' & z & P & E); revert E; unfold jm;
      match goal with
        |- context [proj1_sig ?x] => destruct x as (jm' & jmm & lev & S & nolocks)
      end; simpl; apply nolocks.

    - (*! safety of the only thread *)
      intros i cnti ora.
      destruct (getThreadC cnti) as [c|c|c v|v1 v2] eqn:Ec; try discriminate; [].
      destruct i as [ | [ | i ]]. 2: now inversion cnti. 2:now inversion cnti.
      (* the initial juicy has got to be the same as the one given in initial_mem *)
      assert (Ejm: jm = jm_ cnti compat).
      {
        apply juicy_mem_ext; swap 1 2.
        - reflexivity.
        - unfold jm_.
          symmetry.
          unfold jm.
          destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *.
          destruct (JS n) as (jm' & jmm & lev & S & notlock); simpl projT1 in *; simpl projT2 in *.
          subst m.
          setoid_rewrite personal_mem_of_same_jm; eauto.
      }
      subst jm. rewrite <-Ejm.
      simpl in Ec. replace c with q in * by congruence.
      destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *.
      destruct (JS n tt) as (jm' & jmm & lev & ? & Safe & notlock); simpl projT1 in *; simpl projT2 in *.
      subst q.
      simpl proj1_sig in *; simpl proj2_sig in *. subst n.
      destruct ora; apply Safe.

    - (* well-formedness *)
      intros i cnti.
      constructor.

    - (* only one thread running *)
      intros F; exfalso. simpl in F. omega.
  Qed.

End Initial_State.
