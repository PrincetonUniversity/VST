Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.common.Compcert_lemmas.
Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.advanced_permissions.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.
Require Import VST.concurrency.compiler.synchronisation_symulations.




Require Import VST.concurrency.lib.Coqlib3.

Require Import VST.concurrency.memsem_lemmas.
Import BinNums.

Import BinInt.
Import List.
Import Integers.
Import Ptrofs.
Import Basics.
Import FunctionalExtensionality.

Require Import VST.concurrency.compiler.Clight_self_simulation.
Require Import VST.concurrency.compiler.Asm_self_simulation.
Require Import VST.concurrency.compiler.diagrams.
Require Import VST.concurrency.compiler.mem_equiv.
Require Import VST.concurrency.compiler.pair.
Require Import VST.concurrency.compiler.inject_virtue.
Require Import VST.concurrency.compiler.concur_match.
Require Import VST.concurrency.lib.Coqlib3.


Set Nested Proofs Allowed.
Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.
Import bounded_maps.


(* migration: MOVE TO OTHER FILES: *)

      (* Propers for Clight and Asm *)

(* End MIGRATION! *)







Module ThreadedSimulation (CC_correct: CompCert_correctness)(Args: ThreadSimulationArguments).

  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  
  Module MySyncSimulation:= SyncSimulation CC_correct Args.
  Import MySyncSimulation.
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  (* Module MyConcurMatch := ConcurMatch CC_correct Args.*)

  

  
  Section ThreadedSimulation.
    Import MySimulationTactics.MyConcurMatch.
    
    
    
    Section CompileOneThread.
      Import OrdinalPool.
      Context (hb: nat).
      (*Instantiate definitions in Concur with the current hybridbound*)
      Notation concur_match:= (concur_match hb).
      Notation match_thread:= (match_thread hb).
      Notation match_thread_source:= (match_thread_source hb).
      Notation match_thread_target:= (match_thread_target hb).
      
      Notation memcompat2:= (memcompat2 hb).
      Notation memcompat1:= (memcompat1 hb).
      Notation contains12:= (contains12 hb).
      Notation mtch_target:= (mtch_target hb).
      Notation mtch_compiled:= (mtch_compiled hb).
      Notation mtch_source:= (mtch_source hb).
      Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
      Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)).

Definition cast_t {Sem}:
                @OrdinalPool.t _ Sem -> @ThreadPool.t _ Sem (@OrdinalThreadPool dryResources _):=
  fun X => X.
Lemma Asm_preserves_invariant:
  forall g i (st: @t dryResources (HybridSem (@Some nat (S hb))))
    cnt st' (th_st: Smallstep.state (Asm.part_semantics g)) c2 m Hlt t0,
    invariant (cast_t st) ->
    @getThreadC _ (HybridSem _) _ _ cnt =
    (Krun (TST c2)) ->
    let th_perm:= @getThreadR _ _ i st cnt in
    let th_m:= @restrPermMap (fst th_perm) m Hlt in
    Asm.step Asm_g (Asm.set_mem c2 th_m) t0 th_st ->
    st' = updThread cnt (Krun (TST th_st))
                    (getCurPerm (Smallstep.get_mem th_st),
                     snd (getThreadR cnt)) ->
    invariant (cast_t st').
Proof.
  intros.
  (* This is proven somwhere *)
Admitted.

  Lemma Asm_preserves_compat:
  forall g i (st: @t dryResources (HybridSem (@Some nat (S hb))))
    cnt st' (th_st: Smallstep.state (Asm.part_semantics g)) c2 m Hlt t0,
    mem_compatible (cast_t st) m ->
    @getThreadC _ (HybridSem _) _ _ cnt =
    (Krun (TST c2)) ->
    let th_perm:= @getThreadR _ _ i st cnt in
    let th_m:= @restrPermMap (fst th_perm) m Hlt in
    Asm.step Asm_g (Asm.set_mem c2 th_m) t0 th_st ->
    st' = updThread cnt (Krun (TST th_st))
                    (getCurPerm (Smallstep.get_mem th_st),
                     snd (getThreadR cnt)) ->
    mem_compatible (cast_t st') (Asm.get_mem th_st).
Proof.
  intros.
  (* This is proven somwhere *)
Admitted.

      (* Where to move this:*)
      
      (*
        ConcurMatch used to be here. 
       *)

      
      (* The following tactics are also in permissions.v  
         but for some reason that one doesn't work...
       *)
      Ltac unfold_getCurPerm:=
        repeat rewrite getCurPerm_correct in *;
        unfold permission_at in *.
      Ltac unfold_getMaxPerm:=
        repeat rewrite getMaxPerm_correct in *;
        unfold permission_at in *.
      Ltac unfold_getPerm:=
        try unfold_getMaxPerm; try unfold_getMaxPerm.
      
      (** *Tactics
         These tactics are here becasue they must be outside a section.
         they also must be after concur_match definition.
       *)

      (*Do I have to reppeat the LTAC from the section? *)


      Inductive opt_rel' {A} (ord: A -> A -> Prop): option A -> option A -> Prop:=
      | Some_ord:
          forall x y, ord x y -> opt_rel' ord (Some x) (Some y).
      
      Lemma option_wf:
        forall A (ord: A -> A -> Prop),
          well_founded ord ->
          well_founded (opt_rel' ord).
      Proof.
        unfold well_founded.
        intros.
        destruct a.
        2: econstructor; intros; inversion H0.
        specialize (H a).
        induction H.
        econstructor; intros.
        inversion H1; subst.
        eapply H0; eauto.
      Qed.


      Lemma simulation_equivlanence:
        forall s3 t s2 cd cd0,
          (Smallstep.plus (Asm.step (Genv.globalenv Asm_program)) 
                          s3 t s2 \/
           Smallstep.star (Asm.step (Genv.globalenv Asm_program)) 
                          s3 t s2 /\ InjorderX compiler_sim cd cd0) ->
          Smallstep.plus (Asm.step (Genv.globalenv Asm_program)) 
                         s3 t s2 \/
          t = Events.E0 /\
          s2 = s3 /\
          InjorderX compiler_sim cd cd0.
      Proof.
        intros. destruct H; eauto.
        destruct H.
        inversion H; subst; eauto.
        left. econstructor; eauto.
      Qed.
      


      (*This lemma is used when the compiled thread steps*)
      
      Ltac exploit_match tac:=  
        unfold match_thread_target,match_thread_source in *;
        repeat match goal with
               | [ H: ThreadPool.getThreadC ?i = _ ?c |- _] => simpl in H
               end;
        match goal with
        | [ H: getThreadC ?i = _ ?c,
               H0: context[match_thread] |- _ ] =>
          match type of H0 with
          | forall (_: ?Hlt1Type) (_: ?Hlt2Type), _ =>
            assert (Hlt1:Hlt1Type); [
              first [eassumption | tac | idtac]|
              assert (Hlt2:Hlt2Type); [
                first [eassumption | tac | idtac]|
                specialize (H0 Hlt1 Hlt2);
                rewrite H in H0; inversion H0; subst; simpl in *; clear H0
            ]]
          end

        | [ H: getThreadC ?i = _ ?c,
               H0: context[match_thread_compiled] |- _ ] =>
          match type of H0 with
          | forall (_: ?Hlt1Type) (_: ?Hlt2Type), _ =>
            assert (Hlt1:Hlt1Type); [
              first [eassumption | tac | idtac]|
              assert (Hlt2:Hlt2Type); [
                first [eassumption | tac | idtac]|
                specialize (H0 Hlt1 Hlt2);
                rewrite H in H0; inversion H0; subst; simpl in *; clear H0
            ]]
          end
        end;
        fold match_thread_target in *;
        fold match_thread_source in *.

      (* Build the concur_match *)
      Ltac destroy_ev_step_sum:=
        match goal with
        | [ H: ev_step_sum _ _ _ _ _ _ _ |- _ ] => inversion H; clear H
        end.
      
      Lemma break_existensial_of_thread_stepN:
        forall G TID SCH TR C M res, 
        forall Sem ge U c1 m1 c2 m2 c3 m3,
        @machine_semantics.thread_step G TID SCH TR C M res Sem ge U c1 m1 c2 m2 ->
        (exists n : nat, machine_semantics_lemmas.thread_stepN Sem ge n U c2 m2 c3 m3) ->
        exists n : nat, machine_semantics_lemmas.thread_stepN Sem ge (S n) U c1 m1 c3 m3.
      Proof.
        intros; normal.
        repeat (econstructor; eauto).
      Qed.
      Lemma thread_step_plus_from_corestep':
        forall NN m tge U i st2 m2
          (Hinv: @invariant (HybridSem _) (@OrdinalThreadPool dryResources _) st2)
          (code2 : Asm.state)
          (s4' : Smallstep.state (Asm.part_semantics Asm_g))
          (cnt2: containsThread st2 i)
          (Hcmpt: mem_compatible st2 m2)
          (m4' : mem) m2_i Hlt2
          (Hm_eq: m2_i =  (@restrPermMap (fst (getThreadR cnt2)) m2 Hlt2)),
          corestepN (Asm_core.Asm_core_sem Asm_g) (S NN) code2 m2_i s4' m4' ->
          getThreadC cnt2 = Krun (TST code2) ->
            HybridMachineSig.schedPeek U = Some i ->
            machine_semantics_lemmas.thread_step_plus
              (HybConcSem (Some (S hb)) m) tge U st2
              m2 (updThread cnt2 (Krun (TState Clight.state Asm.state s4'))
                            (getCurPerm m4', snd (getThreadR cnt2))) m4'.
      Proof.
        simpl; induction NN; intros.
        - subst; destruct H as (c2 & m3 & STEP & Heq). inv Heq.
          simpl in STEP. inv STEP.
          exists O; simpl; do 2 eexists. split; try reflexivity.
          replace (Asm.get_mem s4') with (HybridMachineSig.diluteMem  (Asm.get_mem s4'))
            by reflexivity.
          exploit Asm_event.asm_ev_ax2.
          econstructor; simpl in *; eassumption.
          intros (T&HH).
          econstructor; try eassumption; simpl.
          do 2 (econstructor; eauto); try reflexivity.
          + clean_proofs; eauto.
            
        - simpl in H; normal.
          simpl in H. inv H; simpl in *.
          eapply break_existensial_of_thread_stepN.
          + (* first step *)
            replace (Asm.get_mem s4') with
                (HybridMachineSig.diluteMem  (Asm.get_mem s4'))
              by reflexivity.
            exploit Asm_event.asm_ev_ax2.
            { econstructor; simpl in *; eassumption. }
            intros (T&HH).
            do 2 (econstructor; eauto); try reflexivity.
            * constructor;clean_proofs; eauto.
          + (* The rest of the steps (inductively) *)
            match goal with
              |- exists x, machine_semantics_lemmas.thread_stepN _ _ _ _ ?upd_st2
                                                           _ _ _ =>
              remember upd_st2 as st2'
            end.
            assert (cnt2': containsThread st2' i).
            { subst. eapply cntUpdate; auto. }
            assert (HH:(thread_perms i st2' cnt2') = (getCurPerm (Asm.get_mem x))).
            { subst st2'; pose proof (@gssThreadRR dryResources _ i st2).
              simpl in *; rewrite H; auto. }
            assert (Hinv':invariant st2').
            { eapply Asm_preserves_invariant; eauto. }
            exploit IHNN.
            * apply Hinv'.
            * eapply Asm_preserves_compat; eauto.
            * pose proof (mem_is_restr_eq (Asm.get_mem x)).
              clean_proofs.
              remember (getCurPerm (Asm.get_mem x))  as TEMP.
              rewrite <- HH in HeqTEMP; subst TEMP.
              erewrite restr_proof_irr.
              eapply H.
              
            * normal; [apply H2 | apply H3]. 
            * subst st2'.
              pose proof @gssThreadCC.
              specialize (H dryResources _ i st2 cnt2
                            (Krun (TState (@semC CSem) (@semC AsmSem) x)) cnt2').
              simpl in *; apply H.
            * eassumption.
            (* * erewrite (mem_is_restr_eq (Asm.get_mem x)).
              clean_proofs.
              remember ( getCurPerm (Asm.get_mem x))  as TEMP.
              rewrite <- HH in HeqTEMP; subst TEMP.
              unshelve (apply restr_proof_irr). *)
      
            * intros (n&c3&m3&one_step&many_steps).
            eexists (S n); simpl.
            exists c3, m3. split.
            -- eassumption.
            -- simpl in *.
              instantiate(1:= tge) in many_steps.
              instantiate(1:= m) in many_steps.
              match goal with
                [H: machine_semantics_lemmas.thread_stepN _ _ _ _ _ _ ?S _
                 |- machine_semantics_lemmas.thread_stepN _ _ _ _ _ _ ?S' _ ]=>
                replace S' with S; eauto
              end.
              subst st2'.
              rewrite updThread_twice.
              do 2 f_equal.
              unfold lock_perms.
              pose proof (@gssThreadRR dryResources _ i st2).
              simpl in *.
              rewrite H; reflexivity.

              Unshelve.
              apply Asm_genv_safe.
              assumption.
              apply Asm_genv_safe.
              assumption.

              { eapply tge. }
              { eapply tge. }
              { assert (HH:(thread_perms i st2' cnt2') = (getCurPerm (Asm.get_mem x))).
                { subst st2'; pose proof (@gssThreadRR dryResources _ i st2).
                  simpl in *; rewrite H; auto. }
                rewrite HH.
                eapply mem_cur_lt_max. }
      Qed.
              
      Lemma thread_step_plus_from_corestep:
        forall (m : option mem) (tge : ClightSemanticsForMachines.G * Asm.genv)
          (U : list nat) (st1 : t) (m1 : mem) (Htid : containsThread st1 hb) 
          (st2 : t) (mu : meminj) (m2 : mem) (cd0 : compiler_index)
          (CMatch : concur_match (Some cd0) mu st1 m1 st2 m2) (code2 : Asm.state)
          (s4' : Smallstep.state (Asm.part_semantics Asm_g)) 
          (m4' : mem) (cnt2 : containsThread st2 hb),
          corestep_plus (Asm_core.Asm_core_sem Asm_g) code2
                        (restrPermMap
                           (proj1 ((memcompat2 CMatch) hb (contains12 CMatch Htid))))
                        s4' m4' ->
            machine_semantics_lemmas.thread_step_plus
              (HybConcSem (Some (S hb)) m) tge U st2
              m2 (updThread cnt2 (Krun (TState Clight.state Asm.state s4'))
                            (getCurPerm m4', snd (getThreadR cnt2))) m4'.
      Proof.
        (** NOTE: This might be missing that the corestep never reaches an at_external
                  If this is the case, we might need to thread that through the compiler...
                  although it should be easy, I would prefere if there is any other way...
         *)
        intros.
        destruct H as (NN& H).
        clean_proofs.
        eapply thread_step_plus_from_corestep'; eauto;
          try apply CMatch.
      Admitted.
      (** *Need an extra fact about simulations*)
      Lemma step2corestep_plus:
        forall (s1 s2: Smallstep.state (Asm.part_semantics Asm_g)) m1 t,
          Smallstep.plus
            (Asm.step (Genv.globalenv Asm_program))
            (Smallstep.set_mem s1 m1) t s2 ->
          (corestep_plus (Asm_core.Asm_core_sem Asm_g))
            s1 m1 s2 (Smallstep.get_mem s2).
      (* This in principle is not provable. We should get it somehow from the simulation.
              Possibly, by showing that the (internal) Clight step has no traces and allo
              external function calls have traces, so the "matching" Asm execution must be
              all internal steps (because otherwise the traces wouldn't match).
       *)
      Admitted.
      
      
      (* When a thread takes an internal step (i.e. not changing the schedule) *)
      Lemma internal_step_diagram:
        forall (m : option mem) (sge tge : HybridMachineSig.G) (U : list nat) tr1
          (st1 : ThreadPool (Some hb)) m1 (st1' : ThreadPool (Some hb)) m1',
          machine_semantics.thread_step (HybConcSem (Some hb) m) sge U st1 m1 st1' m1' ->
          forall cd tr2 (st2 : ThreadPool (Some (S hb))) mu m2,
            concur_match cd mu st1 m1 st2 m2 ->
            forall (Hmatch_event : List.Forall2 (inject_mevent mu) tr1 tr2),
            exists (st2' : ThreadPool (Some (S hb))) m2' cd' mu',
              concur_match cd' mu' st1' m1' st2' m2' /\
              List.Forall2 (inject_mevent mu') tr1 tr2 /\
              (machine_semantics_lemmas.thread_step_plus
                 (HybConcSem (Some (S hb)) m) tge U st2 m2 st2' m2' \/
               machine_semantics_lemmas.thread_step_star
                 (HybConcSem (Some (S hb)) m) tge U st2 m2 st2' m2' /\
               opt_rel' (InjorderX compiler_sim) cd' cd).
      Proof.
        intros.
        inversion H; subst.
        inversion Htstep; subst.
        destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].  
        - (* tid < hb *)
          pose proof (mtch_target _ _ _ _ _ _ H0 _ l Htid (contains12 H0 Htid)) as HH.
          simpl in *.

          exploit_match ltac:(apply H0).
          destroy_ev_step_sum; subst; simpl in *; simpl.
          eapply Asm_event.asm_ev_ax1 in H2.
          instantiate (1:=Asm_genv_safe) in H2.
          
          eapply Aself_simulation in H5; eauto.
          destruct H5 as (c2' & f' & t' & m2' & (CoreStep & MATCH & Hincr & is_ext & inj_trace)).

          eapply Asm_event.asm_ev_ax2 in CoreStep; try eapply Asm_genv_safe.
          destruct CoreStep as (?&?); eauto.
          
          (* contains.*)
          pose proof (@contains12  H0 _ Htid) as Htid'.

          (* Construct the new thread pool *)
          exists (updThread Htid' (Krun (TState Clight.state Asm.state c2'))
                       (getCurPerm m2', snd (getThreadR Htid'))).
          (* new memory is given by the self_simulation. *)
          exists m2', cd, f'. split; [|split; [|left]].
          
          + (*Reestablish the concur_match *)
            simpl.
            move H0 at bottom.
            dup H0 as Hcmpt2.
            eapply memcompat2 in Hcmpt2.
            
            eapply concur_match_update1; eauto.
            { eapply semantics.corestep_mem in H2. eapply H2. }
            { instantiate(1:=Hcmpt2).
              eapply Asm_event.asm_ev_ax1 in H1.
              eapply semantics.corestep_mem.
              instantiate(1:=c2').
              instantiate(1:=code2).
              repeat abstract_proofs; unify_proofs; eauto.
            }
            
            { apply H0. }

            (*The compiler match*)
            econstructor 2; eauto.
            simpl in MATCH.
            unfold match_thread_target; simpl.
            constructor.
            exact MATCH.
            
          + (* Reestablish inject_mevent *)
            eapply inject_incr_trace; eauto.
          + (* Construct the step *)
            exists 0%nat; simpl.
            do 2 eexists; split; [|reflexivity].
            replace m2' with (HybridMachineSig.diluteMem m2') by reflexivity.
            econstructor; eauto; simpl.
            econstructor; eauto.
            * simpl in *.
              eapply H0.
            * simpl; erewrite restr_proof_irr; econstructor; eauto.
            * simpl; repeat (f_equal; try eapply Axioms.proof_irr).
          + erewrite restr_proof_irr; eassumption.
            
            
        - (*  tid = hb*)
          pose proof (mtch_compiled _ _ _ _ _ _ H0 _ e Htid (contains12 H0 Htid)) as HH.
          subst.
          simpl in *.

          exploit_match ltac:(apply H0).

          
          (* This takes three steps:
           1. Simulation of the Clight semantics  
           2. Simulation of the compiler (Clight and Asm) 
           3. Simulation of the Asm semantics 
           *)

          rename H6 into Compiler_Match; simpl in *.
          
          (* (1) Clight step *)
          destroy_ev_step_sum. subst m'0 t0 s.
          eapply (event_semantics.ev_step_ax1 (@semSem CSem)) in H2; eauto.
          
          (* (2) Compiler step/s *)
          rename H2 into CoreStep.
          inversion CoreStep. subst s1 m0 s2.
          eapply compiler_sim in H1; simpl in *; eauto.
          2: { erewrite restr_proof_irr; eassumption. }
          destruct H1 as (cd' & s2' & j2' & t'' & step & comp_match & Hincr2 & inj_event).

          eapply simulation_equivlanence in step.
          assert ( HH: Asm.state =
                       Smallstep.state (Asm.part_semantics Asm_g)) by
              reflexivity.
          remember (@Smallstep.get_mem (Asm.part_semantics Asm_g) s2') as m2'.
          pose proof (contains12 H0 Htid) as Htid'.

          destruct step as [plus_step | (? & ? & ?)].
          + exists (updThread Htid' (Krun (TState Clight.state Asm.state s2'))
                         (getCurPerm m2', snd (getThreadR Htid'))), m2', (Some i), mu.
            split; [|split].
            * assert (CMatch := H0). inversion H0; subst.
              simpl. admit. (*reestablish concur*)
            * eapply inject_incr_trace; try eassumption.
              apply inject_incr_refl.
            * left.
              eapply thread_step_plus_from_corestep; eauto.
              eauto; simpl.
              subst m2'.
              instantiate(1:=Htid).
              instantiate(21:=code2).
              instantiate (5:=H0).
              erewrite restr_proof_irr; eauto.
              eapply step2corestep_plus; eassumption.
              
          + exists st2, m2, (Some cd'), mu.
            split; [|split].
            * assert (CMatch := H0). inversion H0; subst.
              admit. (*reestablish concur*)
            * eapply inject_incr_trace; try eassumption.
              apply inject_incr_refl.
            * right; split.
              { (*zero steps*)
                exists 0%nat; simpl; auto. }
              { (*order of the index*)
                constructor; auto.  }
              
        - (* tid > hb *)
          pose proof (mtch_source _ _ _ _ _ _ H0 _ l Htid (contains12 H0 Htid)) as HH.
          simpl in *.
          exploit_match ltac:(apply H0).
          destroy_ev_step_sum; subst; simpl in *.
          simpl.
          eapply (event_semantics.ev_step_ax1 (@semSem CSem)) in H2; eauto.
          replace Hcmpt with (memcompat1 H0) in H2
            by eapply Axioms.proof_irr.
          
          eapply Cself_simulation in H5; eauto.
          destruct H5 as (c2' & f' & t' & m2' & (CoreStep & MATCH & Hincr & His_ext & Htrace)).
          
          eapply (event_semantics.ev_step_ax2 (@semSem CSem)) in CoreStep.
          destruct CoreStep as (?&?); eauto.
          
          (* contains.*)
          pose proof (contains12 H0 Htid) as Htid'.

          (* Construct the new thread pool *)
          exists (updThread Htid' (Krun (SState Clight.state Asm.state c2'))
                       (getCurPerm m2', snd (getThreadR Htid'))).
          (* new memory is given by the self_simulation. *)
          exists m2', cd, f'. split; [|split; [|left]].
          
          + (*Reestablish the concur_match *)
            simpl.
            move H0 at bottom.
            eapply concur_match_update1; eauto.
            { eapply semantics.corestep_mem in H2.
              eapply H2. }
            { eapply (event_semantics.ev_step_ax1 (@semSem CSem)) in H1.
              eapply semantics.corestep_mem in H1.
              clean_proofs.
              erewrite restr_proof_irr.
              eassumption.
            }
            { apply H0. }
            
            econstructor 1; eauto.
            simpl in MATCH.
            unfold match_thread_source; simpl.
            constructor.
            exact MATCH.
          + eapply inject_incr_trace; try eassumption. 
          + (* Construct the step *)
            exists 0%nat; simpl.
            do 2 eexists; split; [|reflexivity].
            replace m2' with (HybridMachineSig.diluteMem m2') by reflexivity.
            econstructor; eauto; simpl.
            econstructor; eauto.
            * simpl in *.
              eapply H0.
            * simpl. 
              erewrite restr_proof_irr.
              econstructor; eauto.
            * simpl; repeat (f_equal; try eapply Axioms.proof_irr).
          + erewrite restr_proof_irr.
            eassumption.


            Unshelve. all: auto.
            (*This shouldn't be her e*) 
            all: try (exact nil).
            all: try (eapply H0).
            eapply Asm_genv_safe.
            
      Admitted. (* TODO: there is only one admit: reestablish the concur_match*)


      (** *Diagrams for machine steps*)
      
      (*Here 1*)
















      














      
      

      
      (* What to do with this? *)
      Hint Resolve inject_incr_refl.
      
      Lemma external_step_diagram:
        forall (U : list nat) (tr1 tr2 : HybridMachineSig.event_trace) (st1 : ThreadPool.t) 
               (m1 : mem) (st1' : ThreadPool.t) (m1' : mem) (tid : nat) (ev : Events.sync_event),
        forall (cd : option compiler_index) (st2 : ThreadPool.t) (mu : meminj) (m2 : mem),
          concur_match cd mu st1 m1 st2 m2 ->
          List.Forall2 (inject_mevent mu) tr1 tr2 ->
          forall (cnt1 : ThreadPool.containsThread st1 tid) (Hcmpt : mem_compatible st1 m1),
            HybridMachineSig.schedPeek U = Some tid ->
            syncStep true cnt1 Hcmpt st1' m1' ev ->
            exists ev' (st2' : t) (m2' : mem) (cd' : option compiler_index) 
                   (mu' : meminj),
              concur_match cd' mu' st1' m1' st2' m2' /\
              List.Forall2 (inject_mevent mu') (tr1 ++ (Events.external tid ev :: nil)) (tr2 ++ (Events.external tid ev' :: nil)) /\
              HybridMachineSig.external_step
                (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler) U tr2 st2 m2 (HybridMachineSig.schedSkip U)
                (seq.cat tr2 (Events.external tid ev' :: nil)) st2' m2'.
      Proof.
        intros.
        match goal with
          |- exists (a:?A) (b:?B) (c:?C) (d:?D) (e:?E),
            ?H1 /\
            (Forall2 (inject_mevent e) (_ ++ (?ev1::nil)) (_ ++ (?ev1'::nil))) /\
            ?H3 =>
          cut (exists (a:A) (b:B) (c:C) (d:D) (e:E), H1 /\ 
                                                     inject_incr mu e /\
                                                     (inject_mevent e ev1 ev1') /\
                                                     H3)
        end.
        { intros (a&b&c&d&e&(HH1 & HH2 & HH3 & HH4)).
          exists a, b, c, d, e; repeat weak_split (try assumption).
          eapply List.Forall2_app; auto.
          eapply inject_incr_trace; eauto. }
        
        assert (thread_compat1:thread_compat _ _ cnt1 m1) by
            (apply mem_compatible_thread_compat; assumption).
        assert (cnt2: ThreadPool.containsThread st2 tid) by
            (eapply contains12; eauto).
        assert (thread_compat2:thread_compat _ _ cnt2 m2) by
            (apply mem_compatible_thread_compat; eapply H).
        inversion H2; subst.
        - (*Acquire*)
          rename m1 into m1_base.
          remember (fst (thread_mems thread_compat1)) as m1.
          rename m2 into m2_base.
          remember (fst (thread_mems thread_compat2)) as m2.
          assert (Hmax_equiv1: Max_equiv m1_base m1).
          { subst. symmetry.  eapply restr_Max_equiv. }
          assert (Hnb1: Mem.nextblock m1_base = Mem.nextblock m1).
          { subst;reflexivity. }
          assert (Hmem_compat: mem_compatible st1 m1).
          { eapply mem_compat_Max; try eapply Hcmpt; eauto. }

          remember (Build_virtue virtueThread (getThreadR cnt1)) as angel'.
          edestruct (acquire_step_diagram hb angel' m1) as
              (?&?&?&?&?&?); subst angel'; simpl in *; eauto;
            try rewrite (restr_proof_irr _ (proj1 (Hcmpt tid cnt1)));
            eauto.
          + !goal(access_map_equiv _ (_ m1) ).
            subst. symmetry; apply getCur_restr.
          + !goal(access_map_equiv _ (_ m2) ).
            subst. symmetry; apply getCur_restr.
          + !goal(concur_match _ _ _ _ _ _).
            eapply concur_match_perm_restrict in H.
            instantiate (1:= mu).
            instantiate (1:= cd).
            subst m1 m2. eapply H.
          + !goal(pair21_prop sub_map _ _).
            move Hbounded at bottom.
            unfold Max_equiv in *.
            repeat (autounfold with pair);
              unfold pair_prop; simpl.
            unfold sub_map in Hbounded.
            (*Hmax_equiv is not enough here.
              m1 and m1_base have the same max (even the structure)
              
             *)
            admit.
          + simpl. admit. (* at_external up to mem_equiv*)
          + instantiate(1:= m1').
            assert (Hlock_update_mem_strict_load:
                      lock_update_mem_strict_load
                        b (unsigned ofs) (lock_perms _ _ cnt1)
                        m1_base m1' vone vzero).
            { econstructor; eauto. }
            subst m1; eapply lock_update_mem_strict_load_restr; eauto.
          + econstructor; eauto.
          + unfold Max_equiv in *.
            rewrite <- Hmax_equiv1.
            eapply Hlt_new.
          + unfold fullThUpd_comp, fullThreadUpdate in *.
            subst newThreadPerm.
            simpl in H3.
            do 5 econstructor; repeat (weak_split eauto).
            econstructor; eauto.
            instantiate(1:=tr2) in H5.

            (*Can I prove HybridMachineSig.external_step works 
              "up to cur. " 
             *)
            
            admit. (* sync up to cur *)
            
            
        - (*Release*)
          (*Shifting to the threads cur.*)
          rename m1 into m1_base.
          remember (fst (thread_mems thread_compat1)) as m1.
          rename m2 into m2_base.
          remember (fst (thread_mems thread_compat2)) as m2.
          remember (Build_virtue virtueThread virtueLP) as angel'.
          assert (Hmax_equiv1: Max_equiv m1_base m1).
          { subst. symmetry.  eapply restr_Max_equiv. }
          assert (Hnb1: Mem.nextblock m1_base = Mem.nextblock m1).
          { subst;reflexivity. }
          assert (Hmem_compat: mem_compatible st1 m1).
          { eapply mem_compat_Max; try eapply Hcmpt; eauto. }
          
          unshelve edestruct (release_step_diagram hb angel' m1 m1') as
              (?&?&?&?&?&?); subst angel';
            try apply HisLock;
            simpl in *; eauto.
          + !goal(access_map_equiv _ (_ m1) ).
            subst. symmetry. apply getCur_restr.
          + !goal(access_map_equiv _ (_ m2) ).
            subst. symmetry; apply getCur_restr.
          + !goal(concur_match _ _ _ _ _ _).
            eapply concur_match_perm_restrict in H.
            do 2 rewrite <- mem_is_restr_eq in H.
            subst m1 m2; apply concur_match_perm_restrict.
            assumption.
          + !goal(sub_map_virtue _ _).
            unfold Max_equiv in *;
              rewrite <- Hmax_equiv1.
            constructor; eauto.
          + !context_goal(at_external_sum).
            simpl. subst m1; simpl.
            rewrite <- Hat_external.
            repeat f_equal; eapply Axioms.proof_irr.
          + (* instantiate(1:= m1'). *)
            assert (Hlock_update_mem_strict_load:
                      lock_update_mem_strict_load
                        b (unsigned ofs) (lock_perms _ _ cnt1)
                        m1_base m1' vzero vone).
            { econstructor; eauto. }
            subst m1; eapply lock_update_mem_strict_load_restr; auto.
          + eapply empty_map_useful; auto.
          + econstructor; eauto.
          + do 5 econstructor; repeat (weak_split; eauto).
            econstructor; eauto.
            admit. (* sync up to cur *)

            Unshelve.
            
        - (*Create/Spawn*)
          admit.
        - (*Make Lock*)
          pose proof (memcompat2 H) as Hcmpt2.
          remember (restrPermMap (proj1 (Hcmpt2 tid cnt2))) as m2'.
          simpl in *.
          rename m1 into m1_base.
          remember  (restrPermMap (proj1 (Hcmpt tid cnt1))) as m1.
          edestruct (make_step_diagram hb m1) as (?&?&?&?&?&?);
            eauto; simpl; try solve[subst; eauto].
          + econstructor; eauto.
          + subst. symmetry; apply getCur_restr.
          + symmetry; apply getCur_restr.
          + !goal(concur_match _ _ st1 m1 _ _).
            admit. (*concur_match up to restr. *)
          + do 5 econstructor; repeat (weak_split eauto).
          + econstructor; eauto.
            * subst; eauto.
            * subst; eauto.
          + do 5 econstructor; repeat (weak_split eauto).
            * instantiate(1:=x1).
              instantiate(1:=x0).
              match goal with
                [ H : concur_match _ _ ?s _ _ _ |- concur_match _ _ ?s' _ _ _] =>
                replace s' with s
              end; eauto.
              unfold fullThreadUpdate in *; simpl in *.
              repeat f_equal.
              destruct pmap_tid' as [A B].
              simpl in Hdata_perm, Hlock_perm. 
              clear - Hdata_perm Hlock_perm.
              subst A B.
              repeat autounfold with pair; simpl.
              reflexivity.
            *  econstructor; eassumption.
            * clear - H5.
              !goal (HybridMachineSig.external_step _ _ _ _ _ _ _ _ ).
              (* up to mem_equiv. *)
              admit.
        - (*Free Lock*)
          simpl in Hlock_perm.
          simpl in Hfreeable.
          set (m_restr:= restrPermMap (proj1 (Hcmpt tid cnt1))).
          edestruct (free_step_diagram hb m_restr) as (?&?&?&?&?&?);
            eauto; simpl; try solve[subst; eauto]; simpl in *;
              try eassumption.
          + constructor; eassumption.
          + subst m_restr; symmetry.
            eapply getCur_restr.
          + symmetry; eapply getCur_restr.
          + eapply concur_match_perm_restrict; eauto.
          + repeat (autounfold with pair; simpl).
            clear - Hrmap.
            intros b ofs. specialize (Hrmap b ofs) as [A B].
            unfold pair0.
            f_equal; assumption.
          + subst m_restr.
            unfold perm_interval.
            rewrite RPM.
            rewrite <- restrPermMap_idempotent; eassumption.
          + do 5 econstructor; repeat (weak_split; eauto).
            admit.
            admit.
            admit.
            
        - (*AcquireFail*)
          set (m_restr:= restrPermMap (proj1 (Hcmpt tid cnt1))).
          
          edestruct (acquire_fail_step_diagram hb m_restr) as (?&?&?&?);
            eauto; simpl; try solve[subst; eauto]; simpl in *;
              try eassumption.
          + econstructor; eauto.
          + eapply concur_match_perm_restrict; eauto.
          + subst m_restr; symmetry.
            eapply getCur_restr.
          + symmetry; eapply getCur_restr.
          + subst m_restr.
            rewrite <- restrPermMap_idempotent; eauto.
          + subst m_restr. unfold perm_interval.
            rewrite <- restrPermMap_idempotent; eauto.
          + match type of H5 with
              HybridMachineSig.external_step _ _ ?st2 ?m _ _ ?st2' ?m2' =>
              eexists; exists st2', m2', cd, mu
            end; repeat (weak_split eauto).
            * subst m_restr.
              (* TODO: change acq_fail to say "any restr mem. "*)
              rewrite (mem_is_restr_eq m1').
              eapply concur_match_perm_restrict; eauto.
              rewrite (mem_is_restr_eq m1').
              eapply concur_match_perm_restrict; eauto.
            * econstructor; eauto.
            * eauto. instantiate(5:=tr2) in H5.
              erewrite <- restrPermMap_idempotent_eq.
              rewrite <- (mem_is_restr_eq m2).
              rewrite (mem_is_restr_eq m2).
              erewrite <- restrPermMap_idempotent_eq in H5.
              eauto.

              
              
              Unshelve.
              all: try eassumption.
              

              
      Admitted.


      
      Lemma start_step_diagram:
        forall (m : option mem) (tge : HybridMachineSig.G) 
               (U : list nat) (st1 : ThreadPool (Some hb)) 
               (m1 : mem) (tr1 tr2 : HybridMachineSig.event_trace)
               (st1' : ThreadPool (Some hb)) (m' : mem)
               (cd : option compiler_index) (st2 : ThreadPool (Some (S hb)))
               (mu : meminj) (m2 : mem) (tid : nat)
               (Htid : ThreadPool.containsThread st1 tid),
          concur_match cd mu st1 m1 st2 m2 ->
          List.Forall2 (inject_mevent mu) tr1 tr2 ->
          HybridMachineSig.schedPeek U = Some tid ->
          HybridMachineSig.start_thread m1 Htid st1' m' ->
          exists
            (st2' : ThreadPool (Some (S hb))) (m2' : mem) 
            (cd' : option compiler_index) (mu' : meminj),
            concur_match cd' mu' st1' (HybridMachineSig.diluteMem m') st2'
                         m2' /\
            List.Forall2 (inject_mevent mu') tr1 tr2 /\
            machine_semantics.machine_step(HybConcSem (Some (S hb)) m) tge
                                          U tr2 st2 m2 (HybridMachineSig.yield
                                                          (Scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
                                                          U) tr2 st2' m2'.
      Proof.
      Admitted.

      
      Lemma resume_step_diagram:
        forall (m : option mem) (tge : HybridMachineSig.G) 
               (U : list nat) (st1 : ThreadPool (Some hb))
               (tr1 tr2 : HybridMachineSig.event_trace)
               (st1' : ThreadPool (Some hb)) (m1' : mem)
               (cd : option compiler_index) (st2 : ThreadPool (Some (S hb)))
               (mu : meminj) (m2 : mem) (tid : nat)
               (Htid : ThreadPool.containsThread st1 tid),
          concur_match cd mu st1 m1' st2 m2 ->
          List.Forall2 (inject_mevent mu) tr1 tr2 ->
          HybridMachineSig.schedPeek U = Some tid ->
          HybridMachineSig.resume_thread m1' Htid st1' ->
          exists
            (st2' : ThreadPool (Some (S hb))) (m2' : mem) 
            (cd' : option compiler_index) (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            List.Forall2 (inject_mevent mu') tr1 tr2 /\
            machine_semantics.machine_step (HybConcSem (Some (S hb)) m) tge
                                           U tr2 st2 m2
                                           (HybridMachineSig.yield(Scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
                                                                  U) tr2 st2' m2'.
      Proof.
        intros.

        assert (Hcnt2: containsThread st2 tid).
        { eapply contains12; eauto. }
        
        (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
        destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].
        - (* tid < hb *)
          admit.
          
        - (* tid = hb *)
          subst.
          inversion H2; subst.
          inversion H. simpl in *.
          clean_proofs.
          assert (m1_restr: permMapLt (thread_perms _ _ ctn) (getMaxPerm m1')) by
              eapply memcompat1.
          assert (m2_restr: permMapLt (thread_perms _ _ Hcnt2) (getMaxPerm m2)) by
              eapply memcompat2.
          specialize (mtch_compiled hb ltac:(reflexivity) ctn Hcnt2
                                                          m1_restr
                                                          m2_restr).
          rewrite Hcode in mtch_compiled.
          inv mtch_compiled.
          
          (* TODO: Add the precondition of H10 to the concur match.
             that means: assert all the preconditions for the current state,
             and also have the precondition for all future states that satisfy the hyps.
             
             WAIT: Maybe not, I think you just need to instantiate it with the 
             current values. All the precontidions are refelxive.

           *)
          simpl in H10.
          inv Hafter_external.
          erewrite (restr_proof_irr m1_restr) in H10.
          destruct ((Clight.after_external None code1 m')) eqn:Hafter_x1; inv H4.
          rewrite Hperm in Hafter_x1.
          specialize (H10 mu s (restrPermMap _) (restrPermMap m2_restr) nil nil
                          ltac:(constructor)
                                 ltac:(constructor)
                                        ltac:(constructor)
                                               Hafter_x1
                     ).
          destruct H10 as (cd' & mu' & s2' & Hafter_x2 & INJ1 & Hcompiler_match).
          remember 
            (updThreadC Hcnt2 (Krun (TState Clight.state Asm.state s2'))) as st2'.
          exists st2',m2,(Some cd'), mu'. 
          split; [|split].
          + !goal (concur_match _ mu' _ _ _ _).
            admit.
          + !goal (Forall2 (inject_mevent mu') tr1 tr2).
            admit.
          + (* Step *)
            !goal (HybridMachineSig.external_step _ _ _ _ _ _ _ _).

            
            assert (HH: U = (HybridMachineSig.yield
                               (Scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler) U))
              by reflexivity.
            rewrite HH at 2.
            eapply HybridMachineSig.resume_step'; eauto.
            admit.
        (* econstructor; eauto. *)

        - (* hb < tid *)
          admit.
      Admitted.

      
      
      
      Lemma suspend_step_diagram:
        forall (m : option mem) (tge : HybridMachineSig.G) 
               (U : list nat) (st1 : ThreadPool (Some hb))
               (tr1 tr2 : HybridMachineSig.event_trace)
               (st1' : ThreadPool (Some hb)) (m1' : mem)
               (cd : option compiler_index) (st2 : ThreadPool (Some (S hb)))
               (mu : meminj) (m2 : mem) (tid : nat)
               (Htid : ThreadPool.containsThread st1 tid),
          concur_match cd mu st1 m1' st2 m2 ->
          List.Forall2 (inject_mevent mu) tr1 tr2 ->
          HybridMachineSig.schedPeek U = Some tid ->
          HybridMachineSig.suspend_thread m1' Htid st1' ->
          exists
            (st2' : ThreadPool (Some (S hb))) (m2' : mem) 
            (cd' : option compiler_index) (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            List.Forall2 (inject_mevent mu') tr1 tr2 /\
            machine_semantics.machine_step (HybConcSem (Some (S hb)) m) tge
                                           U tr2 st2 m2 (HybridMachineSig.schedSkip U) tr2 st2' m2'.
      Proof.
        admit. (* Easy  since there is no changes to memory. *)
      Admitted.

      Lemma schedfail_step_diagram:
        forall (m : option mem) (tge : HybridMachineSig.G) 
               (U : list nat) (tr1 tr2 : HybridMachineSig.event_trace)
               (st1' : ThreadPool (Some hb)) (m1' : mem)
               (st2 : ThreadPool (Some (S hb))) (m2 : mem) 
               (tid : nat) cd mu,
          concur_match cd mu st1' m1' st2 m2 ->
          List.Forall2 (inject_mevent mu) tr1 tr2 ->
          HybridMachineSig.schedPeek U = Some tid ->
          ~ ThreadPool.containsThread st1' tid ->
          HybridMachineSig.invariant st1' ->
          HybridMachineSig.mem_compatible st1' m1' ->
          exists
            (st2' : ThreadPool (Some (S hb))) (m2' : mem) 
            (cd' : option compiler_index) (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            List.Forall2 (inject_mevent mu') tr1 tr2 /\
            machine_semantics.machine_step (HybConcSem (Some (S hb)) m) tge
                                           U tr2 st2 m2 (HybridMachineSig.schedSkip U) tr2 st2' m2'.
      Proof.
        admit.
        (* Easy  since there is no changes to memory. *)
      Admitted.
      
      Lemma machine_step_diagram:
        forall (m : option mem) (sge tge : HybridMachineSig.G) (U : list nat)
               (tr1 : HybridMachineSig.event_trace) (st1 : ThreadPool (Some hb)) 
               (m1 : mem) (U' : list nat) (tr1' : HybridMachineSig.event_trace)
               (st1' : ThreadPool (Some hb)) (m1' : mem),
          machine_semantics.machine_step (HybConcSem (Some hb) m) sge U tr1 st1 m1 U' tr1' st1' m1' ->
          forall (cd : option compiler_index) tr2 (st2 : ThreadPool (Some (S hb))) 
                 (mu : meminj) (m2 : mem),
            concur_match cd mu st1 m1 st2 m2 ->
            List.Forall2 (inject_mevent mu) tr1 tr2 ->
            exists
              tr2' (st2' : ThreadPool (Some (S hb))) (m2' : mem) (cd' : option compiler_index) 
              (mu' : meminj),
              concur_match cd' mu' st1' m1' st2' m2' /\
              List.Forall2 (inject_mevent mu') tr1' tr2' /\
              machine_semantics.machine_step (HybConcSem (Some (S hb)) m) tge U tr2 st2 m2 U' tr2' st2'
                                             m2'.
      Proof.
        intros.
        simpl in H.
        inversion H; subst.
        - (* Start thread. *)
          exists tr2; eapply start_step_diagram; eauto.
          
        - (* resume thread. *)
          exists tr2; eapply resume_step_diagram; eauto.
          
        - (* suspend thread. *)
          exists tr2; eapply suspend_step_diagram; eauto.
          
        - (* sync step. *)
          edestruct external_step_diagram as (? & ? & ? & ? & ? & ? & ? & ?); eauto 8.

        - (*schedfail. *)
          exists tr2; eapply schedfail_step_diagram; eauto.
      Qed.


      
      Lemma initial_diagram:
        forall (m : option mem) (s_mem s_mem' : mem) (main : val) (main_args : list val)
               (s_mach_state : ThreadPool (Some hb)) (r1 : option res),
          machine_semantics.initial_machine (HybConcSem (Some hb) m) r1 s_mem s_mach_state s_mem'
                                            main main_args ->
          exists
            (j : meminj) (cd : option compiler_index) (t_mach_state : ThreadPool (Some (S hb))) 
            (t_mem t_mem' : mem) (r2 : option res),
            machine_semantics.initial_machine (HybConcSem (Some (S hb)) m) r2 t_mem t_mach_state
                                              t_mem' main main_args /\ concur_match cd j s_mach_state s_mem' t_mach_state t_mem'.
      Proof.
        intros m.
        
        simpl; unfold HybridMachineSig.init_machine''.
        intros ? ? ? ? ? ? (?&?).
        destruct r1; try solve[inversion H0].
        simpl in H0.
        destruct H0 as (init_thread&?&?); simpl in *.
        unfold initial_core_sum in *.
        destruct init_thread; destruct H0 as (LT&H0); simpl in LT.
        + admit. (*identical start!*)
        + admit. (*should follow from compiler simulation*)
      Admitted.
      
      Lemma compile_one_thread:
        forall m,
          HybridMachine_simulation_properties
            (HybConcSem (Some hb) m)
            (HybConcSem (Some (S hb)) m)
            (concur_match).
      Proof.
        intros.
        econstructor.
        - eapply option_wf.
          eapply (Injfsim_order_wfX compiler_sim). (*well_founded order*)

        (*Initial Diagram*)
        - eapply initial_diagram.

        (* Internal Step diagram*)
        - eapply internal_step_diagram.

        (* Machine Step diagram *)
        - eapply machine_step_diagram.

        (* Halted *)
        - simpl; unfold HybridMachineSig.halted_machine; simpl; intros.
          destruct (HybridMachineSig.schedPeek U); inversion H0.
          eexists; reflexivity.

        (*Same running *)
        - eapply concur_match_same_running.
          
      Qed.
      
      
    End CompileOneThread.

    
    Section CompileNThreads.
      
      Definition nth_index:= list (option compiler_index).
      Definition list_lt: nth_index -> nth_index -> Prop.
      Admitted.
      Lemma list_lt_wf:
        well_founded list_lt.
      Admitted.
      Inductive match_state:
        forall n,
          nth_index ->
          Values.Val.meminj ->
          ThreadPool (Some 0)%nat -> Memory.Mem.mem -> ThreadPool (Some n) -> Memory.Mem.mem -> Prop:=
      | refl_match: forall j tp m,
          match_state 0 nil j tp m tp m
      | step_match_state:
          forall n ocd ils jn jSn tp0 m0 tpn mn tpSn mSn,
            match_state n ils jn tp0 m0 tpn mn ->
            concur_match n ocd jSn tpn mn tpSn mSn ->
            match_state (S n) (cons ocd ils) (compose_meminj jn jSn) tp0 m0 tpSn mSn.

      Lemma trivial_self_injection:
        forall m : option mem,
          HybridMachine_simulation_properties (HybConcSem (Some 0)%nat m)
                                              (HybConcSem (Some 0)%nat m) (match_state 0).
      Proof.
      (* NOTE: If this lemma is not trivial, we can start the induction at 1,
         an the first case follow immediately by lemma
         compile_one_thread
       *)
      Admitted.

      Lemma simulation_inductive_case:
        forall n : nat,
          (forall m : option mem,
              HybridMachine_simulation_properties (HybConcSem (Some 0)%nat m)
                                                  (HybConcSem (Some n) m) (match_state n)) ->
          (forall m : option mem,
              HybridMachine_simulation_properties (HybConcSem (Some n) m)
                                                  (HybConcSem (Some (S n)) m) (concur_match n)) ->
          forall m : option mem,
            HybridMachine_simulation_properties (HybConcSem (Some 0)%nat m)
                                                (HybConcSem (Some (S n)) m) (match_state (S n)).
      Proof.
        intros n.
      Admitted.
      
      Lemma compile_n_threads:
        forall n m,
          HybridMachine_simulation.HybridMachine_simulation_properties
            (HybConcSem (Some 0)%nat m)
            (HybConcSem (Some n) m)
            (match_state n).
      Proof.
        induction n.
        - (*trivial reflexive induction*)
          apply trivial_self_injection.
        - eapply simulation_inductive_case; eauto.
          eapply compile_one_thread.
      Qed.

    End CompileNThreads.

    Section CompileInftyThread.

      Parameter lift_state: forall on, ThreadPool on -> forall on', ThreadPool on' -> Prop.
      
      Inductive infty_match:
        nth_index -> meminj ->
        ThreadPool (Some 0)%nat -> mem ->
        ThreadPool None -> mem -> Prop:=
      | Build_infty_match:
          forall n cd j st0 m0 stn mn st,
            match_state n cd j st0 m0 stn mn ->
            lift_state (Some n) stn None st ->
            infty_match cd j st0 m0 st mn.


      Lemma initial_infty:
        forall (m : option mem) (s_mem s_mem' : mem) 
          (main : val) (main_args : list val)
          (s_mach_state : ThreadPool (Some 0)%nat) (r1 : option res),
          machine_semantics.initial_machine (HybConcSem (Some 0)%nat m) r1
                                            s_mem s_mach_state s_mem' main main_args ->
          exists
            (j : meminj) (cd : nth_index) (t_mach_state : ThreadPool None) 
            (t_mem t_mem' : mem) (r2 : option res),
            machine_semantics.initial_machine (HybConcSem None m) r2 t_mem
                                              t_mach_state t_mem' main main_args /\
            infty_match cd j s_mach_state s_mem' t_mach_state t_mem'.
      Proof.
      (* Follows from any initial diagram and a missing lemma showing that the initial state
        can be "lifted" (lift_state) *)
      Admitted.

      Lemma infinite_step_diagram:
        forall (m : option mem) (sge tge : HybridMachineSig.G)
          (U : list nat) tr1 (st1 : ThreadPool (Some 0)%nat) 
          (m1 : mem) (st1' : ThreadPool (Some 0)%nat) 
          (m1' : mem),
          machine_semantics.thread_step (HybConcSem (Some 0)%nat m) sge U st1
                                        m1 st1' m1' ->
          forall (cd : nth_index) tr2 (st2 : ThreadPool None) 
            (mu : meminj) (m2 : mem),
            infty_match cd mu st1 m1 st2 m2 ->
            List.Forall2 (inject_mevent mu) tr1 tr2 ->
            exists
              (st2' : ThreadPool None) (m2' : mem) (cd' : nth_index) 
              (mu' : meminj),
              infty_match cd' mu' st1' m1' st2' m2' /\
              List.Forall2 (inject_mevent mu') tr1 tr2 /\
              (machine_semantics_lemmas.thread_step_plus 
                 (HybConcSem None m) tge U st2 m2 st2' m2' \/
               machine_semantics_lemmas.thread_step_star 
                 (HybConcSem None m) tge U st2 m2 st2' m2' /\ 
               list_lt cd' cd).
      Proof.
      (*Proof sketch:
            infty_match defines an intermediate machine Mn at level n, matching the 0 machine.
            All threads of machine Mn are in Asm. A lemma should show that all hier machines 
            (Mk, for k>n) also match the machine at 0. 
            lemma [compile_n_threads] shows that machine M(S n) can step and reestablish 
            [match_states]. Since we increased the hybrid bound (n -> S n) then the new thread 
            is in Asm and [match_states] can be lifted to [infty_match].
       *)
      Admitted.
      Lemma infinite_machine_step_diagram:
        forall (m : option mem) (sge tge : HybridMachineSig.G)
          (U : list nat) (tr1 : HybridMachineSig.event_trace)
          (st1 : ThreadPool (Some 0)%nat) (m1 : mem) (U' : list nat)
          (tr1' : HybridMachineSig.event_trace)
          (st1' : ThreadPool (Some 0)%nat) (m1' : mem),
          machine_semantics.machine_step (HybConcSem (Some 0)%nat m) sge U tr1
                                         st1 m1 U' tr1' st1' m1' ->
          forall (cd : nth_index) tr2 (st2 : ThreadPool None) 
                 (mu : meminj) (m2 : mem),
            infty_match cd mu st1 m1 st2 m2 ->
            List.Forall2 (inject_mevent mu) tr1 tr2 ->
            exists
              tr2' (st2' : ThreadPool None) (m2' : mem) (cd' : nth_index) 
              (mu' : meminj),
              infty_match cd' mu' st1' m1' st2' m2' /\
              List.Forall2 (inject_mevent mu') tr1' tr2' /\
              machine_semantics.machine_step (HybConcSem None m) tge U tr2 st2
                                             m2 U' tr2' st2' m2'.
      Proof.
        (* Same as the other step diagram.*)
      Admitted.

      Lemma infinite_halted:
        forall (m : option mem) (cd : nth_index) (mu : meminj)
          (U : list nat) (c1 : ThreadPool (Some 0)%nat) 
          (m1 : mem) (c2 : ThreadPool None) (m2 : mem) 
          (v1 : val),
          infty_match cd mu c1 m1 c2 m2 ->
          machine_semantics.conc_halted (HybConcSem (Some 0)%nat m) U c1 =
          Some v1 ->
          exists v2 : val,
            machine_semantics.conc_halted (HybConcSem None m) U c2 =
            Some v2.
      Proof.
        intros m.
        (* Should follow easily from the match. *)
      Admitted.

      Lemma infinite_running:
        forall (m : option mem) (cd : nth_index) (mu : meminj)
          (c1 : ThreadPool (Some 0)%nat) (m1 : mem) (c2 : ThreadPool None)
          (m2 : mem),
          infty_match cd mu c1 m1 c2 m2 ->
          forall i : nat,
            machine_semantics.running_thread (HybConcSem (Some 0)%nat m) c1 i <->
            machine_semantics.running_thread (HybConcSem None m) c2 i.
      Proof.
        intros m.
      (* Should follow from the match relation. And there should be a similar lemma 
             for the [match_states]
       *)
      Admitted.
      Lemma compile_all_threads:
        forall m,
          HybridMachine_simulation.HybridMachine_simulation_properties
            (HybConcSem (Some 0)%nat m)
            (HybConcSem None m)
            infty_match.
      Proof.
        intros. 
        (*All the proofs use the following lemma*)
        pose proof compile_n_threads as HH.
        econstructor.
        - eapply list_lt_wf.
        - apply initial_infty.
        - apply infinite_step_diagram.
        - apply infinite_machine_step_diagram.
        - apply infinite_halted.
        - apply infinite_running.

      Qed.

    End CompileInftyThread.
    
  End ThreadedSimulation.
End ThreadedSimulation.
