(** *Semax Imports*)
From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrnat.
Require Import Coq.Strings.String.

Require Import compcert.lib.Integers.
Require Import compcert.common.AST.
Require Import compcert.cfrontend.Clight.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Memdata.
Require Import compcert.common.Values.

Require Import msl.Coqlib2.
Require Import msl.eq_dec.
Require Import veric.initial_world.
Require Import veric.juicy_mem.
Require Import veric.juicy_mem_lemmas.
Require Import veric.semax_prog.
Require Import veric.compcert_rmaps.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.
Require Import veric.semax.
Require Import veric.semax_ext.
Require Import veric.juicy_extspec.
Require Import veric.initial_world.
Require Import veric.juicy_extspec.
Require Import veric.tycontext.
Require Import veric.semax_ext.
Require Import veric.coqlib4.
Require Import sepcomp.semantics.
Require Import sepcomp.step_lemmas.
Require Import sepcomp.event_semantics.
Require Import concurrency.semax_conc.
Require Import concurrency.juicy_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.scheduler.
Require Import concurrency.addressFiniteMap.
Require Import concurrency.permissions.

Require Import concurrency.semax_invariant.
Require Import concurrency.semax_initial.
Require Import concurrency.semax_to_juicy_machine.

(** *Erasure Imports*)
Require Import concurrency.erasure_signature.
Require Import concurrency.erasure_proof.
Require Import concurrency.erasure_safety.

Require Import concurrency.fineConc_safe.


(** *Compiler simulation*)
Require Import concurrency.lifting.
Require Import concurrency.lifting_safety.

(** *Target machine*)
Require Import concurrency.x86_context.


Module MainSafety .

  Module ErasureProof := erasure_proof.Parching.
  Module Erasure := ErasureFnctr ErasureProof.
  Import ErasureProof.
  Import Erasure.

  (*Module lifting_this := lifting ErasureProof.SEM.*)
  Module lifting_safety_this:= lifting_safety X86SEM X86Machines.
  Import lifting_safety_this.
  (*Module lifting_this:= lifting X86SEM X86Machines. *)
  (*Lifting_this is imported as lftng. *)

  
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
    
    Definition ds_initial := DSEM.initial_machine
                               dry_initial_perm initial_cstate.

    
    Lemma erasure_match: forall n,
        ErasureProof.match_st (js_initial n) ds_initial.
    Proof. intros.
           constructor.
           - intro i.
             unfold js_initial, initial_machine_state, ErasureProof.JTP.containsThread; simpl;
             unfold ds_initial ,DSEM.initial_machine, ErasureProof.DTP.containsThread; simpl; auto.
           - intro i.
             unfold js_initial, initial_machine_state, ErasureProof.JTP.containsThread; simpl;
             unfold ds_initial ,DSEM.initial_machine, ErasureProof.DTP.containsThread; simpl; auto.
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
             unfold ErasureProof.JSEM.ThreadPool.lockRes;
               unfold ErasureProof.DSEM.ThreadPool.lockRes.
             auto.
           - unfold ErasureProof.DSEM.ThreadPool.lockRes.
             simpl. intros.  rewrite threadPool.find_empty in H0; inversion H0.
           - unfold ErasureProof.DSEM.ThreadPool.lockRes.
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
      - eapply DSEM.DryMachineLemmas.initial_invariant.
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
        is_true
          (JuicyMachine.valid
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
      - eapply DSEM.DryMachineLemmas.initial_invariant.
      - intros sch0. eapply juicy_initial_safety; auto.
    Qed.

    Theorem new_dry_clight_infinite_safety': forall sch,
        DryMachine.valid (sch, nil, ds_initial) ->
        DryMachine.safe_new_step  (globalenv prog) (sch, nil, ds_initial) initial_memory.
    Proof.
      move => sch VAL.
      apply: safety.ksafe_safe' => //.
      - exact Classical_Prop.classic.
      - move => ds.
        simpl.
        eapply DryMachine.finite_branching.
      - move => n U VAL'.
        rewrite /DryMachine.mk_nstate /=.
        simpl; apply: new_dry_clight_safety.
    Qed.

    Theorem new_dry_clight_infinite_safety: forall sch,
        DryMachine.safe_new_step  (globalenv prog) (sch, nil, ds_initial) initial_memory.
    Proof.
      cofix.
      move=> U.
      destruct (DryMachineSource.THE_DRY_MACHINE_SOURCE.SCH.schedPeek U) eqn:Us.
      destruct (DryMachineSource.THE_DRY_MACHINE_SOURCE.SCH.TID.eq_tid_dec 0 t0) eqn:AA.
      - eapply new_dry_clight_infinite_safety'.
        rewrite / DryMachine.valid /=.
          by rewrite Us AA.

      - econstructor.
        eapply DryMachine.step_with_halt.
        rewrite /DryMachine.mk_ostate /DryMachine.mk_nstate /DryMachine.MachStep /=.
        instantiate (2:= (nil, ds_initial, initial_memory) ).
        eapply DryMachine.schedfail => //.
        eassumption.
        rewrite /DryMachineSource.THE_DRY_MACHINE_SOURCE.DSEM.ThreadPool.containsThread.
        simpl. clear - n.
        move => /ltP HH . apply n.
        destruct (NPeano.Nat.lt_1_r t0) as [H H0].
        symmetry; apply: H HH.
        simpl.
        rewrite /DryMachineSource.THE_DRY_MACHINE_SOURCE.DSEM.invariant /ds_initial.
        eapply erasure_safety.ErasureSafety.ErasureProof.DSEM.DryMachineLemmas.initial_invariant.
        intros. eapply new_dry_clight_infinite_safety.

      -  eapply new_dry_clight_infinite_safety'.
         rewrite / DryMachine.valid /=.
           by rewrite Us.
    Qed.
    
    Require Import concurrency.dry_context. 
    (*Definition dry_initial_core_2:=
      initial_core (coarse_semantics) 
                   (the_ge) (Vptr x Int.zero) nil.
    Definition initial_cstate_2 :=
      initial_core coarse_semantics the_ge (Vptr x Int.zero) nil. *)
    (* Definition ds_initial_2 := DryMachine.SIG.init_mach
                                 init_perm ge
                                 (Vptr x Int.zero) nil. *)

    Definition compiled_machine_simulation:= lftng.concur_sim.

    Parameter gTx86:  X86SEM.G.
    Parameter b: Values.block.
    Definition main: val:= (Vptr x Int.zero).
    Definition p: option ErasureProof.DSEM.perm_map:=
      Some dry_initial_perm.
    Parameter sch : X86Machines.SC.Sch.
    
    Definition this_simulation:=
      compiled_machine_simulation gTx86 (globalenv prog) main p sch.
    
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
          (match_st Tg Sg main p U cd j Sds Sm Tds Tm) ->
       (forall sch : ErasureProof.DryMachine.Sch,
        DryMachineSource.THE_DRY_MACHINE_SOURCE.DryMachine.valid
          (sch, [::], Sds) ->
        DryMachineSource.THE_DRY_MACHINE_SOURCE.DryMachine.safe_new_step
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
         (DryMachineSource.THE_DRY_MACHINE_SOURCE.DryMachine.new_MachineSemantics
            sch p) (globalenv prog) main nil = 
       Some c1 ->
       lftng.init_inv j (globalenv prog) nil initial_memory gTx86 vals2 m2 ->
       exists 
       (c2 : foo.FineConc.machine_state),
         machine_semantics.initial_machine
           (X86Machines.DryConc.new_MachineSemantics sch p) gTx86 main
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
            rewrite /DryMachineSource.THE_DRY_MACHINE_SOURCE.DryMachine.init_machine' /DryMachineSource.THE_DRY_MACHINE_SOURCE.DSEM.init_mach /DryMachineSource.THE_DRY_MACHINE_SOURCE.DSEM.ThreadPool.SEM.Sem
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
         (DryMachineSource.THE_DRY_MACHINE_SOURCE.DryMachine.new_MachineSemantics
            sch p) (globalenv prog) main nil = 
       Some c1 ->
       lftng.init_inv j (globalenv prog) nil initial_memory gTx86 vals2 m2 ->
       exists 
       (c2 : foo.FineConc.machine_state),
         machine_semantics.initial_machine
           (X86Machines.DryConc.new_MachineSemantics sch p) gTx86 main
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
         (DryMachineSource.THE_DRY_MACHINE_SOURCE.DryMachine.new_MachineSemantics
            sch p) (globalenv prog) main nil = 
       Some c1 ->
       lftng.init_inv j (globalenv prog) nil initial_memory gTx86 vals2 m2 ->
       exists 
       (c2 : foo.FineConc.machine_state),
         machine_semantics.initial_machine
           (X86Machines.DryConc.new_MachineSemantics sch p) gTx86 main
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
           (X86Machines.DryConc.new_MachineSemantics sch p) gTx86 main
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
        destruct (X86Machines.DryConc.valid (sch, [::], c)) eqn: VAL.
          + by apply: IF_VAL.
          + rewrite /X86Machines.DryConc.safe_new_step /X86Machines.DryConc.new_state
                    /X86Machines.DryConc.mk_nstate /=.
            {
            destruct (dry_machine.Concur.mySchedule.schedPeek sch) eqn:SCH.
            - eapply X86Machines.DryConc.AngelSafe.
              eapply X86Machines.DryConc.schedfail.
              + exact SCH.
              + simpl. move: VAL.
                inversion HH.
                rewrite /X86Machines.DryConc.valid SCH
                        /X86Machines.DryConc.running_thread
                        /X86Machines.DryMachine.ThreadPool.find_thread
                        /X86Machines.DryMachine.ThreadPool.containsThread /=.
                move => HHH; auto.
                destruct (dry_machine.Concur.mySchedule.TID.eq_tid_dec 0 t0); inversion HHH.
                move => AA; eapply n.
                move : AA. compute; simpl.
                destruct t0; [trivial| move=>BB; inversion BB].
              + simpl. pose X86Machines.DryMachine.DryMachineLemmas.initial_invariant.
                specialize (i dry_initial_perm s); simpl in i.
                inversion HH. eapply i.
              + reflexivity.
              + intros. apply IHk; eauto.
            - eapply X86Machines.DryConc.HaltedSafe.
                by rewrite /X86Machines.DryConc.halted SCH.
            }
      Qed.

      (** *Safety of the dry x86 concurrent semantics,*)
    (** *whit a cooperative schedule*)
      Lemma dry_x86_coarse_safety:
        forall j (c1 : ErasureProof.dstate)
          (vals2 : seq.seq val) 
         (m2 : mem),
       machine_semantics.initial_machine
         (DryMachineSource.THE_DRY_MACHINE_SOURCE.DryMachine.new_MachineSemantics
            sch p) (globalenv prog) main nil = 
       Some c1 ->
       lftng.init_inv j (globalenv prog) nil initial_memory gTx86 vals2 m2 ->
       exists 
       (c2 : foo.FineConc.machine_state),
         machine_semantics.initial_machine
           (X86Machines.DryConc.new_MachineSemantics sch p) gTx86 main
           vals2 = Some c2 /\
         forall sch : foo.SC.Sch,
           forall k, X86Machines.DryConc.csafe gTx86 (sch, nil, c2) m2 k.
      Proof.
        move => j c vals m /compilation_csafety_preservation_aux
                 HH /HH [] cd [] AA BB.
        exists cd. split; [exact AA|].
        move=> sch k.
        apply: initial_safety_reduction; eauto.
      Qed.
      
    (** *Safety of the dry x86 concurrent semantics,*)
      (** *with a preemptive schedule*)
      
(* (* commented out because does not build *)
    Theorem x86_fine_safe:
    forall U tpf m,
    forall sch,
      X86Machines.FineConc.fsafe (globalenv prog) tpf (diluteMem m) sch (seq.size sch + 1).
    Proof.
      intros.
      replace (seq.size sched + 1) with (S (seq.size sched)) by omega.
      eapply FineConcSafe.init_fine_safe.
      intros.
      - assert (HH:= dry_x86_coarse_safety n sched0 mem H).
        destruct HH as [c [initC safe ]].
        replace tpc with c.
        auto.
        + unfold ds_initial_2 in initC.
          unfold FineConcSafe.tpf_init, fine_semantics in Hinit.
          unfold initial_core in Hinit.
          unfold FineConc.MachineSemantics in Hinit.
          unfold FineConc.init_machine in Hinit.
          rewrite initC in Hinit.
          inversion Hinit.

          unfold FineConcSafe.tpc_init in H0.
          unfold FineConcSafe.SimProofs.SimDefs.CoarseSem in H0.
          unfold DryConc.MachineSemantics in H0; simpl in H0.
          unfold DryConc.init_machine in H0.
          rewrite initC in H0; inversion H0.
          subst; auto.
      - assumption.
      - eassumption.
      - constructor.
    Qed.
*)    
End Initil.
End MainSafety.