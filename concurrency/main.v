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
Require Import veric.semax_ext_oracle.
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

Require Import concurrency.semax_to_juicy_machine.

(** *Erasure Imports*)
Require Import concurrency.erasure_signature.
Require Import concurrency.erasure_proof.
Require Import concurrency.erasure_safety.

Require Import concurrency.fineConc_safe.


(** *Compiler simulation*)
Require Import concurrency.lifting.

(** *Target machine*)
Require Import concurrency.x86_context.


Module MainSafety .

  Module ErasureProof := erasure_proof.Parching.
  Module Erasure := ErasureFnctr ErasureProof.
  Import ErasureProof.
  Import Erasure.

  (*Module lifting_this := lifting ErasureProof.SEM.*)
  Module lifting_this:= lifting X86SEM X86Machines.

  
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
      (all_safe : semax_prog.semax_prog (Concurrent_Oracular_Espec CS ext_link) prog V G)
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
    
    Definition initial_corestate :=
      initial_corestate CS V G ext_link prog all_safe init_mem_not_none.
    
    Definition ds_initial := DSEM.initial_machine
                               dry_initial_perm initial_corestate.

    
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
             transitivity (Krun initial_corestate).
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
              (semax_prog_rule (Concurrent_Oracular_Espec CS ext_link) V G
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
         (all_safe : semax_prog (Concurrent_Oracular_Espec CS ext_link)
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

    Theorem new_dry_clight_infinite_safety: forall sch,
        DryMachine.safe_new_step  (globalenv prog) (sch, nil, ds_initial) initial_memory.
    Proof.
      move => sch.
      apply: safety.ksafe_safe => //.
      - admit. (*EM*)
      - move => ds.
        admit. (*Finite branchin!*)
      - admit. (*all_valid in the dry machine (I can probably carry this from the juicym)*)
      - apply: new_dry_clight_safety.
    Admitted.
    
    Require Import concurrency.dry_context. 
    (*Definition dry_initial_core_2:=
      initial_core (coarse_semantics) 
                   (the_ge) (Vptr x Int.zero) nil.
    Definition initial_corestate_2 :=
      initial_core coarse_semantics the_ge (Vptr x Int.zero) nil. *)
    (* Definition ds_initial_2 := DryMachine.SIG.init_mach
                                 init_perm ge
                                 (Vptr x Int.zero) nil. *)

    Definition compiled_machine_simulation:= lifting_this.concur_sim.

    Parameter gTx86:  X86SEM.G.
    Parameter main: val.
    Parameter p: option ErasureProof.DSEM.perm_map.
    Parameter sch : X86Machines.SC.Sch.
    
    Definition this_simulation:=
      compiled_machine_simulation gTx86 (globalenv prog) main p sch.
    Goal True.
      (*destruct this_simulation.*)
      assert (HH:= wholeprog_simulations.Wholeprog_sim.match_state
                     _ _ _ _ _ _ _ _
                     this_simulation).
      Definition compiler_match:=
        wholeprog_simulations.Wholeprog_sim.match_state
          _ _ _ _ _ _ _ _
          this_simulation.
      
      Lemma new_target_safety: forall
          (exists cd j, compiler_match  )
      exists c, X86Machines.DryMachine.ThreadPool.SEM.Sem
      X86Machines.DryConc.safe_new_step gTx86 
X86Machines.DryMachine.ThreadPool.SEM.Sem
      
    
    (** *The comiler preserves safety*)
    Lemma compilation_safety_preservation: forall n sch m,
        dry_context.init_mem = Some m -> 
        DryMachine.csafe (globalenv prog) (sch, nil, ds_initial) initial_memory n ->
        exists c, ds_initial_2 = Some c /\
        DryConc.csafe the_ge (sch, nil, c) m n.
    Admitted.

    (** *Safety of the dry x86 concurrent semantics,*)
    (** *whit a cooperative schedule*)
    Theorem dry_x86_coarse_safety: forall n sch m,
        dry_context.init_mem = Some m -> 
        exists c, ds_initial_2 = Some c /\
             DryConc.csafe the_ge (sch, nil, c) m n.
    Proof.
      intros. 
      eapply compilation_safety_preservation.
      auto.
      eapply dry_clight_safety.
    Qed.

    (** *Safety of the dry x86 concurrent semantics,*)
    (** *with a preemptive schedule*)
    Theorem x86_fine_safe:
    forall U (tpf : FineConc.machine_state) m
      (Hmem: dry_context.init_mem = Some m)
      (Hinit: FineConcSafe.tpf_init (Vptr x Int.zero) nil = Some (U, nil, tpf))
      (ARG: mem_obs_eq.ValueWD.valid_val_list (mem_obs_eq.Renamings.id_ren m) nil),
    forall (sched : X86SC.Sch),
      FineConc.fsafe the_ge tpf (DryMachine.diluteMem m) sched (seq.size sched + 1).
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
    
End Initil.
End MainSafety.