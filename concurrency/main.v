(** * Putting Everything Together*)

(** **Semax Imports*)
From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrnat.
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
Require Import VST.veric.coqlib4.
Require Import VST.sepcomp.semantics.
Require Import VST.sepcomp.step_lemmas.
Require Import VST.sepcomp.event_semantics.
Require Import VST.concurrency.semax_conc_pred.
Require Import VST.concurrency.semax_conc.
Require Import VST.concurrency.juicy_machine.
Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.scheduler.
Require Import VST.concurrency.addressFiniteMap.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.HybridMachine_lemmas.

Require Import VST.concurrency.semax_invariant.
Require Import VST.concurrency.semax_initial.
(* Require Import VST.concurrency.semax_to_juicy_machine. *)

(** ** Erasure Imports*)
Require Import VST.concurrency.erasure_signature.
Require Import VST.concurrency.erasure_proof.
Require Import VST.concurrency.erasure_safety.

(* Require Import VST.concurrency.fineConc_safe. *)

(** ** Compiler simulation*)
Require Import VST.concurrency.lifting.
Require Import VST.concurrency.lifting_safety.

(** ** Target machine*)
Require Import VST.concurrency.x86_context.

Require Import VST.concurrency.executions.
Require Import VST.concurrency.spinlocks.
Require Import VST.concurrency.fineConc_x86.
Require Import VST.concurrency.x86_safe.
Require Import VST.concurrency.SC_erasure.

Module MainSafety .

  Module ErasureProof := erasure_proof.Parching.
  Module Erasure := ErasureFnctr ErasureProof.
  Import ErasureProof.
  Import Erasure.


    (*To use the result we must go back to the normal safety (from safety of bounded states)*)


  (*Module lifting_this := lifting ErasureProof.SEM.*)
  Module lifting_safety_this:= lifting_safety X86SEM X86Machines.
  Import lifting_safety_this.
  (*Module lifting_this:= lifting X86SEM X86Machines. *)
  (*Lifting_this is imported as lftng. *)


  Module ThreadPoolX86 := ThreadPoolWF X86SEM X86Machines.

  (** Safety of FineConc for X86*)
  Import fineConc_x86.FineConcX86Safe.

  (** Safety of SC machine*)
  Module X86SC := SCErasure X86SEM X86SEMAxioms X86Machines X86Context X86CoreErasure.

  Module ErasureSafety := ErasureSafety.
  Import ErasureSafety.

  Definition step_diagram:= ErasureProof.core_diagram.


  Section Initil.
   (*The following variables represent a program satisfying some CSL*)
    Variables
      (CS : compspecs)
      (V : varspecs)
      (G : funspecs)
      (ext_link : string -> ident)
      (ext_link_inj : forall s1 s2, ext_link s1 = ext_link s2 -> s1 = s2)
      (prog : Ctypes.program _)
      (all_safe : semax_prog.semax_prog (Concurrent_Espec unit CS ext_link) prog V G)
      (init_mem_not_none : Genv.init_mem (Ctypes.program_of_program prog) <> None)
      (x: block)
      (block: (Genv.find_symbol (globalenv prog) (prog_main (Ctypes.program_of_program prog)) = Some x)).


    Definition js_initial n := initial_machine_state CS V G ext_link prog all_safe
                                                     init_mem_not_none n.
    Definition dry_initial_perm :=
      getCurPerm( proj1_sig (init_m prog init_mem_not_none)).

    Definition dry_initial_core:=
      initial_core (juicy_core_sem cl_core_sem)
                   (globalenv prog) (Vptr x Int.zero) nil.

    Definition initial_cstate :=
      initial_corestate CS V G ext_link prog all_safe init_mem_not_none.

    Definition ds_initial := DMS.initial_machine
                               dry_initial_perm initial_cstate.


    Lemma erasure_match: forall n,
        ErasureProof.match_st (js_initial n) ds_initial.
    Proof. intros.
           constructor.
           - intro i.
             unfold js_initial, initial_machine_state, ErasureProof.JTP.containsThread; simpl;
             unfold ds_initial ,DMS.initial_machine, ErasureProof.DTP.containsThread; simpl; auto.
           - intro i.
             unfold js_initial, initial_machine_state, ErasureProof.JTP.containsThread; simpl;
             unfold ds_initial ,DMS.initial_machine, ErasureProof.DTP.containsThread; simpl; auto.
           - unfold ErasureProof.JTP.getThreadC, ErasureProof.DTP.getThreadC; simpl.
             intros.
             transitivity (Krun initial_cstate).
             + reflexivity.
             + reflexivity.
           - intros.
             unfold ErasureProof.JTP.getThreadR;
               unfold ErasureProof.DTP.getThreadR; simpl.
             pose proof initial_invariant as INV.
             do 7 autospec INV.
             specialize (INV n nil).
             remember (initial_state CS V G ext_link prog all_safe init_mem_not_none tid nil) as cm.
             destruct cm as ((m, ge), (sch, tp)).
             unfold initial_jm in *.
             unfold initial_state in *.
             unfold spr in *.
             remember
              (semax_prog_rule (Concurrent_Espec unit CS ext_link) V G
                       prog (proj1_sig (init_mem prog init_mem_not_none)) all_safe
                       (proj2_sig (init_mem prog init_mem_not_none))) as spr.
             unfold init_mem in *.
             rewrite <- Heqspr in Heqcm.
             unfold dry_initial_perm in *.
             rewrite <- Heqspr in *.
             destruct spr as (b' & q' & Hb & JS); simpl proj1_sig in *; simpl proj2_sig in *.
             clear Heqspr.
             simpl projT1 in *; simpl projT2 in *.
             injection Heqcm as -> -> -> -> .
             simpl in *.
             destruct (JS n) as [[m phi CON ACC MAX All] [E HYPS]]; simpl.
             simpl in E. rewrite <-E.
             rewrite <-ACC.
             unfold Memory.access_at in *.
             rewrite getCurPerm_correct.
             simpl.
             unfold permission_at in *.
             reflexivity.
           - intros.
             simpl. rewrite empty_map_spec.
             unfold initial_jm; simpl.
             destruct spr as (b' & q & [e INIT'] & f); simpl.
             destruct f;
               simpl proj1_sig in *; simpl proj2_sig in *.
             destruct a as (_ & _ & _ & nLOCKS & _).
             Lemma no_locks_perm_locks: forall rm l,
                 no_locks rm -> perm_of_res_lock (rm @ l) = None.
             Proof.
               move=> rm l /( _ l).
               destruct (rm @ l); eauto.
               destruct k; eauto;
               move=> /(_ t0 p z p0) [] A B; exfalso.
               - apply A; auto.
               - apply B; auto.
             Qed.
             apply no_locks_perm_locks; assumption.
           - intros.
             unfold ErasureProof.DMS.ThreadPool.lockRes;
               unfold ErasureProof.DMS.ThreadPool.lockRes.
             auto.
           - unfold ErasureProof.DMS.ThreadPool.lockRes.
             simpl. intros.  rewrite threadPool.find_empty in H0; inversion H0.
           - unfold ErasureProof.DMS.ThreadPool.lockRes.
             simpl. intros.  rewrite threadPool.find_empty in H0; inversion H0.
           - unfold ErasureProof.DMS.ThreadPool.lockRes.
             simpl. intros.  rewrite threadPool.find_empty in H0; inversion H0.
    Qed.

    Definition initial_memory:= (proj1_sig (init_mem prog init_mem_not_none)).

    (** * Safety of the dry Clight concurrent semantics*)
    Theorem dry_clight_safety: forall n sch,
        DryMachine.csafe (globalenv prog) (sch, nil, ds_initial) initial_memory n.
    Proof.
      intros.
      assert (AA:=safety_initial_state CS V G ext_link ext_link_inj prog all_safe init_mem_not_none sch n).
      assert (BB:= erasure_match).
      assert (CC:= erasure_safety' n).
      eapply CC in BB.
      - eapply BB.
      - unfold ds_initial.
        eapply DryMachineSource.THE_DRY_MACHINE_SOURCE.DryMachineLemmas.initial_invariant0.
      - eapply AA.
    Qed.

    (** * New Safety of the dry Clight concurrent semantics*)

    (*This is the result I need from the juicy semantics*)
    Axiom juicy_initial_safety: forall (CS : compspecs) (V : varspecs) (G : funspecs)
         (ext_link : string -> ident),
       (forall s1 s2 : string, ext_link s1 = ext_link s2 -> s1 = s2) ->
       forall (prog : program)
         (all_safe : semax_prog (Concurrent_Espec unit CS ext_link)
                       prog V G)
         (init_mem_not_none : Genv.init_mem
                                (Ctypes.program_of_program prog) <> None)
         (sch : schedule) (n : nat),
          JuicyMachine.ksafe_new_step
         (globalenv prog)
         (sch, nil,
         initial_machine_state CS V G ext_link prog all_safe
           init_mem_not_none n)
         (proj1_sig (init_mem prog init_mem_not_none)) n.

   Axiom juicy_initial_all_valid: forall n sch,
        (ErasureProof.JuicyMachine.valid
          (sch, nil,
         initial_machine_state CS V G ext_link prog all_safe
           init_mem_not_none n)).

    Theorem new_dry_clight_safety: forall n sch,
        DryMachine.ksafe_new_step  (globalenv prog) (sch, nil, ds_initial) initial_memory n.
    Proof.
      intros.
      eapply new_erasure_safety'; eauto.
      - eapply juicy_initial_all_valid.
      - eapply erasure_match.
      - eapply DryMachineSource.THE_DRY_MACHINE_SOURCE.DryMachineLemmas.initial_invariant0.
      - intros sch0. eapply juicy_initial_safety; auto.
    Qed.

    (*Before going from ksafe to safe, we neet to show, that our execution is mem_bounded*)
    Lemma ksafe_new_step_ksafe_new_step_bounded: forall ge ds m,
        (forall (n : nat) (sch : ErasureProof.DryMachine.Sch),
            DryMachine.new_valid  (DryMachine.mk_nstate (sch, nil, ds) m) sch ->
          DryMachine.ksafe_new_step ge
                                    (sch, [::], ds) m n) ->
      forall (n : nat) (sch : ErasureProof.DryMachine.Sch),
        DryMachine.new_valid_bound (DryMachine.mk_nstate (sch, nil, ds) m) sch ->
        safety.ksafe DryMachine.new_state ErasureProof.DryMachine.Sch
                     (DryMachine.new_step ge) DryMachine.new_valid_bound (*Notice the stronger validity*)
                     (DryMachine.mk_nstate (sch, nil, ds) m) sch n.
    Proof.
      move => ge ds m KSAFE n.
      specialize (KSAFE n).
      move : ds m KSAFE.
      induction n.
      - move => ds m KSAFE sch.
        specialize (KSAFE sch).
        constructor 1.

      - move => ds m KSAFE sch [] VAL BOUND.
        specialize (KSAFE sch VAL).
        inversion KSAFE.
        econstructor ; eauto.
        move => U'' [] VAL'' BOUND''.
        unfold DryMachine.mk_nstate in IHn; simpl in IHn.
        destruct st' as [[tr' ds'] m'].
        cut (tr' = (@nil DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryMachine.Events.machine_event)).
        + intros HH; subst tr'.
          eapply IHn; eauto.
          split; eauto.
        + inversion H0.
          * auto.
          * simpl in *; subst.
            inversion H2; simpl in *; auto.
    Qed.

    Theorem new_dry_clight_infinite_safety': forall sch,
        DryMachine.new_valid_bound (nil, ds_initial, initial_memory) sch  ->
        DryMachine.safe_new_step_bound  (globalenv prog) (sch, nil, ds_initial) initial_memory.
    Proof.
      move => sch VAL.
      apply: safety.ksafe_safe' => //.
      - exact Classical_Prop.classic.
      - move => ds.
        simpl.
        eapply DryMachineSource.THE_DRY_MACHINE_SOURCE.FiniteBranching.finite_branching.
      - move => n U.
        rewrite /DryMachine.mk_nstate /=.
        simpl; eapply ksafe_new_step_ksafe_new_step_bounded.
        + intros.
          simpl; apply: new_dry_clight_safety.
    Qed.

    (*To use the result we must go back to the normal safety (from safety of bounded states)*)


    Lemma bounded_mem_step:
            forall ge sm m sm' m',
          DryMachine.MachStep ge sm m sm' m' ->
          DryMachine.bounded_mem m ->
          DryMachine.bounded_mem m'.
    Proof.
      intros.
      inversion H; eauto; simpl in *; subst; eauto.
      - (*thread step *)
        clear - H0 Htstep .
        inversion Htstep; subst.
        move : Hcorestep=> /=.
        simpl.
        rewrite /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryMachine.ThreadPool.SEM.Sem
              /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.SEM.Sem
              /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.SEM.CLN_evsem.

        move=> HH.
        eapply ev_step_ax1 in HH.
        simpl in HH.
        unfold corestep in HH.
        rewrite SEM.CLN_msem in HH.
        simpl in HH.
        eapply Clight_bounds.CLight_step_mem_bound in HH; eauto.
        eapply Clight_bounds.bounded_getMaxPerm in H0; eauto.

      - inversion Htstep; eauto; simpl in *; subst; auto;
        eapply Clight_bounds.store_bounded; try eapply Hstore;
        eapply Clight_bounds.bounded_getMaxPerm; eauto.
    Qed.

    Lemma safe_new_step_bound_safe_new_step: forall sch ds m,
        DryMachine.new_valid_bound (nil, ds, m) sch ->
        DryMachine.safe_new_step_bound  (globalenv prog) (sch, nil, ds) m ->
            DryMachine.safe_new_step  (globalenv prog) (sch, nil, ds) m.
    Proof.
      rewrite /DryMachine.safe_new_step
              /DryMachine.safe_new_step_bound
              /DryMachine.mk_nstate /=.
      cofix.
      move=> sch ds m [] VAL BOUND SAFE.
      inversion SAFE.
      econstructor; eauto.
      intros.
      assert (DryMachine.new_valid_bound st' U'').
      { split; eauto.
        destruct st' as [[? ?] m']; simpl in *.
        inversion H.
        - simpl in *; subst; auto.
        - simpl in *; subst.
          unfold DryMachine.mk_ostate in H2; simpl in *.
          eapply bounded_mem_step; eauto. }

      destruct st' as [[tr' ds'] m']; simpl in *.

      assert (tr' = nil).
      { inversion H; auto.
        simpl in *; subst.
        inversion H3; simpl in *; subst; auto.
      }

      subst tr'.
      eapply safe_new_step_bound_safe_new_step; eauto.
      Guarded.
    Qed.

    Lemma bounded_empty_mem:
           DryMachine.bounded_mem Mem.empty.
        Proof. intros b0 f.
               intros HH.
               exists 0%Z. exists 0%Z.
               split.
               - intros.
                 unfold getMaxPerm, PMap.map in HH.
                 simpl in HH.
                 rewrite PTree.gleaf in HH; inversion HH.
               - intros.
                 unfold getMaxPerm, PMap.map in HH.
                 simpl in HH.
                 rewrite PTree.gleaf in HH; inversion HH.
        Qed.
    Lemma bounded_initial_mem:
      DryMachine.bounded_mem initial_memory.
        rewrite /initial_memory /init_mem /init_m.

        destruct (Genv.init_mem (Ctypes.program_of_program prog)) eqn:HH;
          [ |exfalso; apply init_mem_not_none; auto].
        move: HH => /=.
        rewrite /Genv.init_mem.
        pose (K:= (prog_defs (Ctypes.program_of_program prog))).
        pose (m':= Mem.empty).
        assert ( DryMachine.bounded_mem m').
        { subst; apply bounded_empty_mem. }


        move : (H).
        fold K m'.
        move: (m').
        induction K.
        - intros ? ? HH; inversion HH. subst; eauto.

        - move=> M BM.
          simpl.



          destruct (Genv.alloc_global (Genv.globalenv (Ctypes.program_of_program prog))
                                      M a) eqn: AA;
            try solve[intros HH; inversion HH].
          intros HH.
          pose (@Clight_bounds.alloc_global_bounded
                  _ _
                  (Genv.globalenv (Ctypes.program_of_program prog))
               M m0 a).
          eapply b in BM; eauto.
    Qed.

    Theorem new_dry_clight_infinite_safety_valid': forall sch,
        DryMachine.new_valid (nil, ds_initial, initial_memory) sch  ->
        DryMachine.safe_new_step  (globalenv prog) (sch, nil, ds_initial) initial_memory.
    Proof.
      intros.
      eapply safe_new_step_bound_safe_new_step.
      - split; eauto.
        simpl.
        apply bounded_initial_mem.
      - eapply new_dry_clight_infinite_safety'.
        split; eauto.
        apply bounded_initial_mem.
    Qed.

    Theorem new_dry_clight_infinite_safety: forall sch,
        DryMachine.safe_new_step  (globalenv prog) (sch, nil, ds_initial) initial_memory.
    Proof.
      cofix.
      move=> U.
      destruct (DryMachineSource.THE_DRY_MACHINE_SOURCE.SCH.schedPeek U) eqn:Us.
      destruct (DryMachineSource.THE_DRY_MACHINE_SOURCE.SCH.TID.eq_tid_dec 0 t0) eqn:AA.
      - eapply new_dry_clight_infinite_safety_valid'.
        rewrite /DryMachine.new_valid /DryMachine.correct_schedule /=.
        subst. rewrite Us.
        rewrite /ds_initial /dry_initial_perm /initial_cstate /DMS.initial_machine /=.
        rewrite /DryMachine.unique_Krun /=.
        rewrite /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryMachine.ThreadPool.containsThread /= => j cntj.
        intros.
        move: (cntj) => /ltP /NPeano.Nat.lt_1_r -> .
        destruct (DryMachineSource.THE_DRY_MACHINE_SOURCE.SCH.TID.eq_tid_dec 0 0); auto.

      - econstructor.
        eapply DryMachine.step_with_halt.
        rewrite /DryMachine.mk_ostate /DryMachine.mk_nstate /DryMachine.MachStep /=.
        instantiate (2:= (nil, ds_initial, initial_memory) ).
        eapply DryMachine.schedfail => //.
        eassumption.
        rewrite /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryMachine.ThreadPool.containsThread.
        simpl. clear - n.
        move => /ltP HH . apply n.
        destruct (NPeano.Nat.lt_1_r t0) as [H H0].
        symmetry; apply: H HH.

        simpl.
        rewrite /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryMachine.invariant /ds_initial.

        eapply DryMachineSource.THE_DRY_MACHINE_SOURCE.DryMachineLemmas.initial_invariant0.

        (* This comees from using the old initial_invariant lemma:
        with (the_ge:=(globalenv prog) ) (pmap:=Some (dry_initial_perm, empty_map)).



        intros.
        rewrite /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryMachine.init_mach /=.
        rewrite /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryMachine.ThreadPool.SEM.Sem /=.
        rewrite /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.SEM.Sem
                ClightSemantincsForMachines.ClightSEM.CLN_msem /=.
        (*Something about initial core!*)

        rewrite /dry_initial_perm.


        /init_m /=.
        destruct (Genv.init_mem (Ctypes.program_of_program prog)) eqn:HH.
        instantiate (1:=(Ctypes.program_of_program prog)).
        a dmit. *)

        intros.
        eapply new_dry_clight_infinite_safety.

      - eapply new_dry_clight_infinite_safety_valid'.
        rewrite /DryMachine.new_valid /DryMachine.correct_schedule /=.
        subst. rewrite Us.
        auto.
    Qed.

    Require Import VST.concurrency.dry_context.
    (*Definition dry_initial_core_2:=
      initial_core (coarse_semantics)
                   (the_ge) (Vptr x Int.zero) nil.
    Definition initial_cstate_2 :=
      initial_core coarse_semantics the_ge (Vptr x Int.zero) nil. *)
    (* Definition ds_initial_2 := DryMachine.SIG.init_mach
                                 init_perm ge
                                 (Vptr x Int.zero) nil. *)

    Definition compiled_machine_simulation:= lftng.concur_sim.

    Definition gTx86 := X86Context.the_ge.
    Parameter b: Values.block.
    Definition main: val:= (Vptr x Int.zero).
    Definition p: option HybridMachine.LocksAndResources.res:=
      Some (dry_initial_perm, empty_map).
    Parameter sch : X86Machines.SC.Sch.

    Definition this_simulation:=
      compiled_machine_simulation gTx86 (globalenv prog) main p X86Context.init_perm sch.

      (*destruct this_simulation.*)
      (*assert (HH:= wholeprog_simulations.Wholeprog_sim.match_state
                     _ _ _ _ _ _ _ _
                     this_simulation). *)
      Definition compiler_match:=
        machine_simulation.Machine_sim.match_state
          _ _ _ _ _ _ _ _
          this_simulation.

      Definition initial_target_state :=
        initial_corestate CS V G ext_link prog all_safe init_mem_not_none.




      (*Definition ds_initial := X86Machines.DryMachine.initial_machine
                                 dry_initial_perm initial_corestate.*)

        (** *The comiler preserves safety*)
      Definition core_init:=
        machine_simulation.Machine_sim.core_initial
          _ _ _ _ _ _ _ _
          this_simulation.

      Lemma compilation_safety_step:
        forall p U Sg Tg Sds Sm Tds Tm cd j,
          (match_st Tg Sg main p X86Context.init_perm U cd j Sds Sm Tds Tm) ->
       (forall sch : ErasureProof.DryMachine.Sch,
        DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryConc.valid
          (sch, [::], Sds) ->
        DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryConc.safe_new_step
          Sg (sch, [::], Sds) Sm) ->
       forall sch : foo.SC.Sch,
       X86Machines.DryConc.valid (sch, [::], Tds) ->
       X86Machines.DryConc.safe_new_step Tg (sch, [::], Tds) Tm.
      Proof. intros. eapply safety_preservation; eauto. Qed.

      Lemma compilation_safety_preservation_aux:
        forall j (c1 : ErasureProof.dstate)
          (vals2 : seq.seq val)
         (m2 : mem),
       machine_semantics.initial_machine
         (DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryConc.new_MachineSemantics
            sch p) (globalenv prog) main nil =
       Some c1 ->
       lftng.init_inv j (globalenv prog) nil initial_memory gTx86 vals2 m2 ->
       exists
       (c2 : foo.FineConc.machine_state),
         machine_semantics.initial_machine
           (X86Machines.DryConc.new_MachineSemantics sch X86Context.init_perm) gTx86 main
           vals2 = Some c2 /\
         forall sch : foo.SC.Sch,
           X86Machines.DryConc.valid (sch, nil, c2) ->
           X86Machines.DryConc.safe_new_step gTx86 (sch, nil, c2) m2.
      Proof.
        move=> ? c1 vals2 ? /= INIT.
        move: (INIT)=> /core_init HH /HH [] cd [] c2 [] AA MATCH.
        move: (MATCH)=> /compilation_safety_step BB.
        exists c2; split; [assumption|].
        intros sch; eapply compilation_safety_step; eauto.
        + move => sch' VAL.

          assert (source_safety:=new_dry_clight_infinite_safety).

          assert (c1 = ds_initial).
          { move: INIT.
            rewrite /ds_initial /initial_cstate /initial_corestate.
            destruct spr as (b & q & [e INIT'] & f); simpl.
            replace (initial_core (juicy_core_sem cl_core_sem)) with cl_initial_core in INIT' by reflexivity.
            rewrite /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryConc.init_machine'
                    /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryMachine.init_mach
                    /DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.SEM.Sem
                    /DryMachineSource.THE_DRY_MACHINE_SOURCE.SEM.Sem.
            rewrite DryMachineSource.THE_DRY_MACHINE_SOURCE.SEM.CLN_msem.
            assert (HH':initial_core CLN_memsem = cl_initial_core) by
                reflexivity.
            rewrite HH' /main.
            rewrite block in e; inversion e; subst.
            move INIT' at bottom.

            rewrite INIT' => EQ; inversion EQ.
            reflexivity. }
          subst c1; apply source_safety.
      Qed.


      Lemma compilation_ksafety_preservation_aux:
        forall j (c1 : ErasureProof.dstate)
          (vals2 : seq.seq val)
         (m2 : mem),
       machine_semantics.initial_machine
         (DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryConc.new_MachineSemantics
            sch p) (globalenv prog) main nil =
       Some c1 ->
       lftng.init_inv j (globalenv prog) nil initial_memory gTx86 vals2 m2 ->
       exists
       (c2 : foo.FineConc.machine_state),
         machine_semantics.initial_machine
           (X86Machines.DryConc.new_MachineSemantics sch X86Context.init_perm) gTx86 main
           vals2 = Some c2 /\
         forall sch : foo.SC.Sch,
           X86Machines.DryConc.valid (sch, nil, c2) ->
           forall k, X86Machines.DryConc.ksafe_new_step gTx86 (sch, nil, c2) m2 k.
      Proof.
        move => j c vals m /compilation_safety_preservation_aux
                 HH /HH [] cd [] AA BB.
        exists cd. split; [exact AA|].
          by move=> sch VAL; apply: safety.safe_ksafe'.
      Qed.

      Lemma compilation_csafety_preservation_aux:
        forall j (c1 : ErasureProof.dstate)
          (vals2 : seq.seq val)
         (m2 : mem),
       machine_semantics.initial_machine
         (DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryConc.new_MachineSemantics
            sch p) (globalenv prog) main nil =
       Some c1 ->
       lftng.init_inv j (globalenv prog) nil initial_memory gTx86 vals2 m2 ->
       exists
       (c2 : foo.FineConc.machine_state),
         machine_semantics.initial_machine
           (X86Machines.DryConc.new_MachineSemantics sch X86Context.init_perm) gTx86 main
           vals2 = Some c2 /\
         forall sch : foo.SC.Sch,
           X86Machines.DryConc.valid (sch, nil, c2) ->
           forall k, X86Machines.DryConc.csafe gTx86 (sch, nil, c2) m2 k.
      Proof.
        move => j c vals m /compilation_ksafety_preservation_aux
                 HH /HH [] cd [] AA BB.
        exists cd. split; [exact AA|].
        by move=> sch VAL k; eapply X86Machines.DryConc.safety_equivalence'; auto.
      Qed.


      Lemma initial_safety_reduction:
        forall sch m c vals,
        machine_semantics.initial_machine
           (X86Machines.DryConc.new_MachineSemantics sch X86Context.init_perm) gTx86 main
           vals = Some c ->
        (forall sch : foo.SC.Sch,
           X86Machines.DryConc.valid (sch, nil, c) ->
           forall k, X86Machines.DryConc.csafe gTx86 (sch, nil, c) m k) ->
        forall sch : foo.SC.Sch,
           forall k, X86Machines.DryConc.csafe gTx86 (sch, nil, c) m k.
      Proof.
        rewrite /= => _.
        rewrite /X86Machines.DryConc.init_machine'
                /X86Machines.DryMachine.init_mach
                /p
                /X86Machines.DryMachine.initial_machine.
        replace (initial_core X86Machines.DryMachine.ThreadPool.SEM.Sem)
        with Asm_coop.Asm_initial_core by reflexivity.
        move => m c vals;
          destruct (Asm_coop.Asm_initial_core gTx86 main vals);
          move=> HH IF_VAL sch k ; try solve[inversion HH].
        move : c m HH  IF_VAL sch .
        induction k.
        - by constructor.
        - move=> c m HH  IF_VAL sch.
          pose (valid_dec:= X86Machines.DryConc.valid (sch, [::], c)).
          destruct (Classical_Prop.classic valid_dec) as [VAL|NVAL].
          + by apply: IF_VAL.
          + destruct (HybridMachine.Concur.mySchedule.schedPeek sch) eqn:SCH.
            - eapply X86Machines.DryConc.AngelSafe.
              eapply X86Machines.DryConc.schedfail.
              + exact SCH.
              + simpl.
                move=> HHH.
                apply NVAL.
                rewrite /valid_dec
                        / X86Machines.DryConc.valid
                        /X86Machines.DryConc.correct_schedule.
                simpl.
                rewrite SCH.
                intros j cntj q _ _.
                clear - HH cntj HHH.
                move : cntj HHH.
                rewrite /X86Machines.DryMachine.ThreadPool.containsThread.
                destruct (X86Context.init_perm); try discriminate.
                inversion HH; subst; simpl.
                clear.
                move => /ltP AA /ltP BB .
                assert (j =0). destruct j; auto; omega.
                assert (t0 =0). destruct t0; auto; omega.
                subst; auto.
                destruct (HybridMachine.Concur.mySchedule.TID.eq_tid_dec 0 0).
                auto.
                exfalso; apply n; auto.
              + simpl.
                (*apply initial inveraint of X86*)
                destruct (X86Context.init_perm); try discriminate.
                inv HH.
                now eapply ThreadPoolX86.initial_invariant0.
              + reflexivity.
              + intros. apply IHk; eauto.
            - eapply X86Machines.DryConc.HaltedSafe.
                by rewrite /X86Machines.DryConc.halted SCH.
      Qed.

      (** *Safety of the dry x86 concurrent semantics,*)
    (** *whit a cooperative schedule*)
      Lemma dry_x86_coarse_safety:
        forall j (c1 : ErasureProof.dstate)
          (vals2 : seq.seq val) m2,
          X86Context.init_mem = Some m2 ->
       machine_semantics.initial_machine
         (DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryConc.new_MachineSemantics
            sch p) (globalenv prog) main nil =
       Some c1 ->
       lftng.init_inv j (globalenv prog) nil initial_memory gTx86 vals2 m2 ->
       exists
       (c2 : foo.FineConc.machine_state),
         machine_semantics.initial_machine
           (X86Machines.DryConc.new_MachineSemantics X86Context.initU X86Context.init_perm) gTx86 main
           vals2 = Some c2 /\
         forall sch : foo.SC.Sch,
           forall k, X86Machines.DryConc.csafe gTx86 (sch, nil, c2) m2 k.
      Proof.
        move => j c vals m ? /compilation_csafety_preservation_aux
                 HH /HH [] cd [] AA BB.
        exists cd. split; [exact AA|].
        move=> sch k.
        apply: initial_safety_reduction; eauto.
      Qed.

    (** *Safety of the x86 FineConc Machine*)

    Theorem x86_fine_safe:
      forall tpc tpf vals m,
        machine_semantics.initial_machine
        (X86Machines.DryConc.new_MachineSemantics sch X86Context.init_perm) gTx86 main
        vals = Some tpc ->
        (forall sch : foo.SC.Sch,
            forall k, X86Machines.DryConc.csafe gTx86 (sch, nil, tpc) m k) ->
        (X86Context.init_mem = Some m) ->
        (mem_obs_eq.ValueWD.valid_val_list (mem_obs_eq.Renamings.id_ren m) vals) ->
        X86Machines.FineConc.init_machine X86Context.initU X86Context.init_perm
                                          gTx86 main vals = Some (sch, [::], tpf) ->
    forall sch,
      X86Machines.FineConc.fsafe gTx86 tpf (X86Machines.DryMachine.diluteMem m)
                                 sch ((seq.size sch).+1).
    Proof.
      intros.
      unfold gTx86.
      eapply init_fine_safe with (U := sch) (f := main); eauto.
      intros.
      assert (tpc0 = tpc).
      { clear - H5 H.
        unfold X86Context.tpc_init, machine_semantics.initial_machine in *.
        simpl in *.
        unfold X86Machines.DryConc.init_machine, X86Machines.DryConc.init_machine' in *.
        unfold gTx86 in *.
        destruct (X86Machines.DryMachine.init_mach X86Context.init_perm X86Context.the_ge main vals);
          inv H5; inv H; auto.
      }
      subst.
      assert (m = mem)
        by (rewrite H4 in H1; inv H1; auto); subst.
      auto.
    Qed.

End Initil.
End MainSafety.
