Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.



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

Set Nested Proofs Allowed.
Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.

(* MOVE TO PERMISSIONS.V*)

Ltac unify_injection:=
  match goal with
    [H: ?mu ?x = _,H0: ?mu ?x = _ |- _] =>
    match type of mu with
    | meminj => rewrite H in H0; invert H0
    | block -> option (block * Z) => rewrite H in H0; invert H0
    end
  end.


              Ltac abstract_proofs_goal_of is_T:=
                match goal with
                  |- context[ ?P ]=>
                  is_T P; is_applied P; abstract_proof P
                end.
              Ltac abstract_proofs_hyp_of is_T:=
                match goal with
                  [H: context[ ?P ] |- _ ] =>
                  is_T P; is_applied P; abstract_proof P
                end.
              Ltac abstract_proofs_of is_T:=
                repeat abstract_proofs_goal_of is_T;
                repeat abstract_proofs_hyp_of is_T.
              

Notation delta_perm_map:=(PTree.t (Z -> option (option permission))).
Module ThreadedSimulation (CC_correct: CompCert_correctness)(Args: ThreadSimulationArguments).

  Module MyThreadSimulationDefinitions := ThreadSimulationDefinitions CC_correct Args.
  Export MyThreadSimulationDefinitions.
  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation. 

  (* TODO TODO : Things to move *)
  
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  Module MyConcurMatch := ConcurMatch CC_correct Args.
      
  
  Section ThreadedSimulation.
    Definition restrPermMap' a b H:= @restrPermMap a b H.
    Lemma RPM: restrPermMap = restrPermMap'. Proof. reflexivity. Qed.
    Import MyConcurMatch.
    
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
      Notation mem_interference:= (mem_interference hb).
      Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
      Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)).

      
      (* Propers for Clight and Asm *)
      
      Instance Asm_get_extcall_arg:
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq ==> Logic.eq) 
               Asm.get_extcall_arg.
      Proof.                      
        intros ??? ??? ???; subst.
        destruct y1; auto.
        destruct sl; auto.
        simpl.
        eapply loadv_Proper; auto.             
      Qed.
      Instance Asm_get_extcall_arguments:
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq ==> Logic.eq) 
               Asm.get_extcall_arguments.
      Proof.
        intros ??? ??? ???; subst.
        induction y1; auto.
        destruct a; simpl.
        rewrite IHy1; try rewrite H0; reflexivity.
        rewrite IHy1; repeat rewrite H0.
        destruct (Asm.get_extcall_arg y y0 rhi); auto.
        rewrite H0; reflexivity.
      Qed.
      Instance  Asm_at_external_proper Asm_g:
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
               (semantics.at_external (Asm_core.Asm_core_sem Asm_g)).
      Proof.
        intros ??? ???; subst.
        unfold semantics.at_external,
        Asm_core.Asm_core_sem,
        core_semantics.sem2coresem.
        simpl.
        unfold Asm.at_external; destruct y; simpl.
        destruct (r Asm.PC); auto.
        destruct (eq_dec i zero); auto.
        destruct ( Genv.find_funct_ptr Asm_g0 b); auto.
        destruct f; auto.
        subst.
        rewrite H0; reflexivity.
      Qed.

      Instance C_at_external_proper Clight_g:
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
               (semantics.at_external (Clight_core.cl_core_sem Clight_g)).
      Proof.
        intros ??? ???; subst; simpl.
        unfold Clight.at_external.
        destruct y; simpl; auto.
      Qed.

      Instance Sum_at_external_proper shb (c_gen: Clight.genv):
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
               (semantics.at_external (sem_coresem (HybridSem shb))).
      Proof.
        intros ??? ???; subst; simpl.
        unfold at_external_sum, sum_func.
        destruct y.
        - eapply C_at_external_proper; auto.
        - eapply Asm_at_external_proper; auto.

          Unshelve.
          eassumption.
      Qed.


      Instance Sum_at_external_proper':
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
               (semantics.at_external (sem_coresem (HybridSem (Some hb)))).
      Proof.
        intros ??? ???; subst; simpl.
        unfold at_external_sum, sum_func.
        destruct y.
        - eapply C_at_external_proper; auto.
        - eapply Asm_at_external_proper; auto.

          Unshelve.
          exact Clight_g.
      Qed.
      
      Ltac is_cnt P:=
        match type of P with
          containsThread _ _ => idtac
        end.
      Ltac abstract_cnt:=
        abstract_proofs_of is_cnt.
      Ltac is_permMapLt P:=
        match type of P with
          permMapLt _ _ => idtac
        end.
      Ltac abstract_permMapLt:=
        abstract_proofs_of is_permMapLt.
      
      (*
      Inductive match_thread
                {sem1 sem2: Semantics}
                (state_type1: @semC sem1 -> state_sum (@semC CSem) (@semC AsmSem))
                (state_type2: @semC sem2 -> state_sum (@semC CSem) (@semC AsmSem))
                (match_state : meminj -> @semC sem1 -> mem -> @semC sem2 -> mem -> Prop) :
        meminj ->
        @ctl (@semC SemTop) -> mem ->
        @ctl (@semC SemBot) -> mem -> Prop  :=
      | Thread_Running: forall j code1 m1 code2 m2,
          match_state j code1 m1 code2 m2 ->
          match_thread state_type1 state_type2 match_state j (Krun (state_type1 code1)) m1
                       (Krun (state_type2 code2)) m2
      | Thread_Blocked: forall j code1 m1 code2 m2,
          match_state j code1 m1 code2 m2 ->
          match_thread state_type1 state_type2 match_state j (Kblocked (state_type1 code1)) m1
                       (Kblocked (state_type2 code2)) m2
      | Thread_Resume: forall j code1 m1 code2 m2 v v',
          match_state j code1 m1 code2 m2 ->
          match_thread state_type1 state_type2 match_state j (Kresume (state_type1 code1) v) m1
                       (Kresume (state_type2 code2) v') m2
      | Thread_Init: forall j m1 m2 v1 v1' v2 v2',
          Val.inject j v1 v2 ->
          Val.inject j v1' v2' ->
          match_thread state_type1 state_type2 match_state j (Kinit v1 v1') m1
                       (Kinit v1 v1') m2.
      
      Definition SST := SState (@semC CSem) (@semC AsmSem).
      Definition TST := TState (@semC CSem) (@semC AsmSem).
      
      Definition match_thread_source:
        meminj -> @ctl (@semC SemTop) -> mem -> @ctl (@semC SemBot) -> mem -> Prop:=
        match_thread SST SST Clight_match.
      Definition match_thread_target:
        meminj -> @ctl (@semC SemTop) -> mem -> @ctl (@semC SemBot) -> mem -> Prop:=
        match_thread TST TST Asm_match.

      Definition loc_readable_cur (m: mem) (b: block) (ofs: Z) : Prop :=
        Mem.perm m b ofs Cur Readable.

      (* Propers for Clight and Asm *)
      
      Instance Asm_get_extcall_arg:
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq ==> Logic.eq) 
               Asm.get_extcall_arg.
      Proof.                      
        intros ??? ??? ???; subst.
        destruct y1; auto.
        destruct sl; auto.
        simpl.
        eapply loadv_Proper; auto.             
      Qed.
      Instance Asm_get_extcall_arguments:
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq ==> Logic.eq) 
               Asm.get_extcall_arguments.
      Proof.
        intros ??? ??? ???; subst.
        induction y1; auto.
        destruct a; simpl.
        rewrite IHy1; try rewrite H0; reflexivity.
        rewrite IHy1; repeat rewrite H0.
        destruct (Asm.get_extcall_arg y y0 rhi); auto.
        rewrite H0; reflexivity.
      Qed.
      Instance  Asm_at_external_proper Asm_g:
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
               (semantics.at_external (Asm_core.Asm_core_sem Asm_g)).
      Proof.
        intros ??? ???; subst.
        unfold semantics.at_external,
        Asm_core.Asm_core_sem,
        core_semantics.sem2coresem.
        simpl.
        unfold Asm.at_external; destruct y; simpl.
        destruct (r Asm.PC); auto.
        destruct (eq_dec i zero); auto.
        destruct ( Genv.find_funct_ptr Asm_g0 b); auto.
        destruct f; auto.
        subst.
        rewrite H0; reflexivity.
      Qed.

      Instance C_at_external_proper Clight_g:
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
               (semantics.at_external (Clight_core.cl_core_sem Clight_g)).
      Proof.
        intros ??? ???; subst; simpl.
        unfold Clight.at_external.
        destruct y; simpl; auto.
      Qed.

      Instance Sum_at_external_proper shb (c_gen: Clight.genv):
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
               (semantics.at_external (sem_coresem (HybridSem shb))).
      Proof.
        intros ??? ???; subst; simpl.
        unfold at_external_sum, sum_func.
        destruct y.
        - eapply C_at_external_proper; auto.
        - eapply Asm_at_external_proper; auto.

          Unshelve.
          eassumption.
      Qed.


      Instance Sum_at_external_proper':
        Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
               (semantics.at_external (sem_coresem (HybridSem (Some hb)))).
      Proof.
        intros ??? ???; subst; simpl.
        unfold at_external_sum, sum_func.
        destruct y.
        - eapply C_at_external_proper; auto.
        - eapply Asm_at_external_proper; auto.

          Unshelve.
          exact Clight_g.
      Qed.

      (** *mem_interference with mem_effect *)
      Section MemInterference.
        Definition mem_effect_forward: mem -> Events.mem_effect -> mem -> Prop.
        (* Definition mem_effect_forward m ev m':= 
         execute ev in m, without checking for permissions.
         *)
        Admitted.
        
        Inductive mem_interference: mem -> list Events.mem_effect -> mem -> Prop:=
        | Nil_mem_interference: forall m, mem_interference m nil m
        | Build_mem_interference: forall m m' m'' ev lev,
            mem_effect_forward m ev m' ->
            mem_interference m' lev m'' ->
            mem_interference m (ev::lev) m''.
        (* OLD_mem_interference:= Mem.unchanged_on (loc_readable_cur m) m *)

        Lemma mem_interference_one:
          forall m m' ev, 
            mem_effect_forward m ev m' ->
            mem_interference m (ev::nil) m'.
        Proof. intros; econstructor; [eauto| econstructor].
        Qed.

        Lemma mem_interference_trans:
          forall lev lev' m m' m'', 
            mem_interference m lev m' ->
            mem_interference m' lev' m'' ->
            mem_interference m (lev ++ lev') m''.
        Proof.
          induction lev.
          - simpl; intros.
            inversion H; subst; auto.
          - simpl; intros.
            inversion H; subst; auto.
            econstructor; eauto.
        Qed.

        Lemma mem_effect_forward_determ:
          forall eff m m1' m2',
            mem_effect_forward m eff m1' -> 
            mem_effect_forward m eff m2' ->
            m1' = m2'.
        Proof.
          intros. 
        Admitted.
        Lemma mem_interference_determ:
          forall lev m m1' m2',
            mem_interference m lev m1' -> 
            mem_interference m lev m2' ->
            m1' = m2'.
        Proof.
          intros lev; induction lev; intros.
          - inversion H; subst;
              inversion H0; subst; reflexivity.
          - inversion H; subst; inversion H0; subst.
            pose proof (mem_effect_forward_determ
                          _ _ _ _
                          H4 H5); subst.
            eapply IHlev; eassumption.
        Qed.

      End MemInterference.

      
      (* This definition is similar to Events.list_inject_mem_effect but stronger:
       it specifies that j' is just an increment to j by adding the newly 
       allocated blocks (in lev1). It also implies that:
       Events.list_inject_mem_effect j' lev1 lev2. 
       But most importantly it implies that j' is sub_injection of all
       injections that map lev1 to lev2 and increment j.
       *)

      Inductive match_thread_compiled:
        option compiler_index ->
        meminj ->
        @ctl (@semC SemTop) -> mem ->
        @ctl (@semC SemBot) -> mem -> Prop  :=
      | CThread_Running: forall i j code1 m1 code2 m2,
          compiler_match i j code1 m1 code2 m2 ->
          match_thread_compiled (Some i) j (Krun (SST code1)) m1
                                (Krun (TST code2)) m2
      | CThread_Blocked: forall i j j' code1 m1 m1' code2 m2 m2' lev1 lev2,
          compiler_match i j code1 m1 code2 m2 ->
          strict_injection_evolution j j' lev1 lev2 ->
          (*Events.list_inject_mem_effect j lev1 lev2 -> *)
          mem_interference m1 lev1 m1' ->
          mem_interference m2 lev2 m2' ->
          match_thread_compiled (Some i) j' (Kblocked (SST code1)) m1'
                                (Kblocked (TST code2)) m2'
      | CThread_Resume: forall j' cd code1 m1 code2 m2 v v',
          (* there are some extra conditions  
           for the next steps.
           *)
          (forall  j'' s1' m1' m2' lev1'' lev2'',
              strict_injection_evolution j' j'' lev1'' lev2'' ->
              mem_interference m1 lev1'' m1' ->
              mem_interference m2 lev2'' m2' ->
              Smallstep.after_external
                (Smallstep.part_sem (Clight.semantics2 C_program))
                None code1 m1' = Some s1' ->
              exists cd' j''' s2',
                (Smallstep.after_external
                   (Asm.part_semantics Asm_g)
                   None code2 m2' = Some s2' /\
                 inject_incr j' j''' /\
                 compiler_match cd' j''' s1' (*Smallstep.get_mem s1'*) m1' s2' (*Smallstep.get_mem s2'*) m2' )) ->
          match_thread_compiled (Some cd) j' (Kresume (SST code1) v) m1
                                (Kresume (TST code2) v') m2
      | CThread_Init: forall j m1 m2 v1 v1' v2 v2',
          Val.inject j v1 v2 ->
          Val.inject j v1' v2' ->
          match_thread_compiled None j (Kinit v1 v1') m1
                                (Kinit v1 v1') m2.
      (* Inject the value in lock locations *)
      Definition inject_lock' size mu (b_lock:block) (ofs_lock: Z) (m1 m2:mem):=
        exists b_lock' delt,
          mu b_lock = Some (b_lock', delt) /\ 
          ( forall ofs0,
              Intv.In ofs0 (ofs_lock, (ofs_lock + size)%Z) ->
              memval_inject mu
                            (ZMap.get ofs0 (Mem.mem_contents m1) !! b_lock)
                            (ZMap.get (ofs0 + delt)%Z
                                      (Mem.mem_contents m2) !! b_lock')).
      
      Definition inject_lock := inject_lock' LKSIZE.
      Lemma inject_lock_morphism':
        Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==>
                         content_equiv ==> content_equiv ==> Basics.impl) inject_lock.
      Proof.
        intros ??????????????? (b' & delt & Hinj & HH) ; subst.
        repeat (econstructor; eauto).
        intros ? H. eapply HH in H.
        rewrite <- H2, <- H3; assumption.
      Qed.
      Instance inject_lock_morphism:
        Proper (Logic.eq ==> Logic.eq ==> Logic.eq ==>
                         content_equiv ==> content_equiv ==> iff) inject_lock.
      Proof. split; eapply inject_lock_morphism'; eauto; symmetry; auto. Qed.

      
      Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
      Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)).
      Record thread_compat {Sem} st i
             (cnt:containsThread(resources:=dryResources)(Sem:=Sem) st i) m:=
        { th_comp: permMapLt (thread_perms _ _ cnt) (getMaxPerm m);
          lock_comp: permMapLt (lock_perms _ _ cnt) (getMaxPerm m)}.
      Arguments th_comp {_ _ _ _ _}.
      Arguments lock_comp {_ _ _ _ _}.
      
      Lemma mem_compatible_thread_compat:
        forall n (st1 : ThreadPool.t(ThreadPool:=TP n)) (m1 : mem) (tid : nat)
          (cnt1 : containsThread st1 tid),
          mem_compatible st1 m1 -> thread_compat _ _ cnt1 m1.
      Proof. intros * H; constructor; apply H. Qed.

      
      Section ConcurMatch. (* 360 *)
        Record concur_match (ocd: option compiler_index)
               (j:meminj) (cstate1: ThreadPool (Some hb)) (m1: Mem.mem) (cstate2: ThreadPool(Some (S hb))) (m2: mem):=
          { same_length: num_threads cstate1 = num_threads cstate2
            ; full_inj: Events.injection_full j m1 (* this is needed until we can prove 
                                                    permission transfer is not deleted*)
            ; memcompat1: mem_compatible cstate1 m1
            ; memcompat2: mem_compatible cstate2 m2
            (*; INJ: Mem.inject j m1 m2 *)
            ; lock_perm_preimage:
                forall i (cnt1: ThreadPool.containsThread cstate1 i)
                  (cnt2: ThreadPool.containsThread cstate2 i),
                  perm_preimage j (lock_perms _ _ cnt1) (lock_perms _ _  cnt2)
            ; INJ_threads:
                forall i (cnt1: ThreadPool.containsThread cstate1 i)
                  (cnt2: ThreadPool.containsThread cstate2 i)
                  Hlt1 Hlt2,
                  Mem.inject j
                             (@restrPermMap (fst (ThreadPool.getThreadR cnt1)) m1 Hlt1)
                             (@restrPermMap (fst (ThreadPool.getThreadR cnt2)) m2 Hlt2)
            ; INJ_locks:
                forall i (cnt1: ThreadPool.containsThread cstate1 i)
                  (cnt2: ThreadPool.containsThread cstate2 i)
                  Hlt1 Hlt2,
                  Mem.inject j
                             (@restrPermMap (snd (ThreadPool.getThreadR cnt1)) m1 Hlt1)
                             (@restrPermMap (snd (ThreadPool.getThreadR cnt2)) m2 Hlt2)
            ; INJ_lock_permissions:
                forall b b' delt opt_rmap,
                  j b = Some (b', delt) ->
                  forall ofs, lockRes cstate1 (b, unsigned ofs) = opt_rmap ->
                         lockRes cstate2 (b', unsigned (add ofs (repr delt))) =
                         (option_map (virtueLP_inject m2 j) opt_rmap)
            ; INJ_lock_content:
                forall b ofs rmap,
                  lockRes cstate1 (b, ofs) = Some rmap ->
                  inject_lock j b ofs m1 m2    
            ; source_invariant: invariant cstate1    
            ; target_invariant: invariant cstate2
            ; mtch_source:
                forall (i:nat),
                  (i > hb)%nat ->
                  forall  (cnt1: ThreadPool.containsThread cstate1 i)
                     (cnt2: ThreadPool.containsThread cstate2 i)
                     Hlt1 Hlt2,
                    match_thread_source j
                                        (getThreadC cnt1)
                                        (@restrPermMap (fst (ThreadPool.getThreadR cnt1)) m1 Hlt1)
                                        (getThreadC cnt2)
                                        (@restrPermMap (fst (ThreadPool.getThreadR cnt2)) m2 Hlt2)
            ; mtch_target:
                forall (i:nat),
                  (i < hb)%nat ->
                  forall (cnt1: ThreadPool.containsThread cstate1 i)
                    (cnt2: ThreadPool.containsThread cstate2 i)
                    Hlt1 Hlt2,
                    match_thread_target  j
                                         (getThreadC cnt1)
                                         (@restrPermMap (fst (ThreadPool.getThreadR cnt1)) m1 Hlt1)
                                         (getThreadC cnt2)
                                         (@restrPermMap (fst (ThreadPool.getThreadR cnt2)) m2 Hlt2)
            ; mtch_compiled:
                forall (i:nat),
                  (i = hb)%nat ->
                  forall (cnt1: ThreadPool.containsThread cstate1 i)
                    (cnt2: ThreadPool.containsThread cstate2 i)
                    Hlt1 Hlt2,
                    match_thread_compiled ocd j
                                          (getThreadC cnt1)
                                          (@restrPermMap (fst (ThreadPool.getThreadR cnt1)) m1 Hlt1)
                                          (getThreadC cnt2)
                                          (@restrPermMap (fst (ThreadPool.getThreadR cnt2)) m2 Hlt2) }.
        Arguments INJ_locks {ocd j cstate1 m1 cstate2 m2}.
        Arguments memcompat1 {ocd j cstate1 m1 cstate2 m2}. 
        Arguments memcompat2 {ocd j cstate1 m1 cstate2 m2}.


        Lemma INJ_lock_permissions_Some:
          forall ocd j cstate1 m1 cstate2 m2,
            concur_match ocd j cstate1 m1 cstate2 m2 -> 
            forall b b' delt rmap,
              j b = Some (b', delt) ->
              forall ofs, lockRes cstate1 (b, unsigned ofs) = Some rmap ->
                     lockRes cstate2 (b', unsigned (add ofs (repr delt))) =
                     Some ( (virtueLP_inject m2 j) rmap).
        Proof. intros. eapply INJ_lock_permissions in H1; eauto. Qed.
        
        Lemma INJ_lock_permissions_None:
          forall ocd j cstate1 m1 cstate2 m2,
            concur_match ocd j cstate1 m1 cstate2 m2 -> 
            forall b b' delt,
              j b = Some (b', delt) ->
              forall ofs, lockRes cstate1 (b, unsigned ofs) = None ->
                     lockRes cstate2 (b', unsigned (add ofs (repr delt))) = None.
        Proof. intros. eapply INJ_lock_permissions in H1; eauto. Qed.
        Lemma virtueLP_inject_max_eq:
          forall m m' mu AA,
            getMaxPerm m = getMaxPerm m' ->
            virtueLP_inject m mu AA =
            virtueLP_inject m' mu AA.
        Proof.
          intros.
          unfold virtueLP_inject, inject_access_map, tree_map_inject_over_mem.
          rewrite H; reflexivity.
        Qed.
        Lemma virtueLP_inject_max_eq_exteny:
          forall m m',
            getMaxPerm m = getMaxPerm m' ->
            virtueLP_inject m =
            virtueLP_inject m'.
        Proof.
          intros.
          extensionality mu.
          extensionality AA.
          apply virtueLP_inject_max_eq; assumption.
        Qed.
        
        Lemma map_compose:
          forall {A B C} (f1: _ -> B -> C) (f2: _ -> A -> B) t,
            PTree.map f1 (PTree.map f2 t) =
            PTree.map (fun ofs a => f1 ofs (f2 ofs a)) t.
        Proof.
          clear.
          intros. unfold PTree.map.
          remember 1%positive as p.
          generalize p.
          induction t0; auto; simpl.
          intros. f_equal.
          - eapply IHt0_1.
          - simpl; destruct o; simpl; f_equal.
          - eapply IHt0_2.
        Qed.
        Lemma map1_map:
          forall A B (f: A -> B) t,
            PTree.map1 f t = PTree.map (fun _ => f) t.
        Proof.
          intros. unfold PTree.map.
          remember 1%positive as p.
          generalize p.
          induction t0; auto; simpl.
          intros. f_equal.
          - eapply IHt0_1.
          - eapply IHt0_2.
        Qed.
        Lemma map1_map_compose:
          forall {A B C} (f1: B -> C) (f2: _ -> A -> B) t,
            PTree.map1 f1 (PTree.map f2 t) =
            PTree.map (fun ofs a => f1 (f2 ofs a)) t.
        Proof. intros; rewrite map1_map, map_compose; reflexivity. Qed.
        Lemma getMax_restr_eq:
          forall perm m (Hlt: permMapLt perm (getMaxPerm m)),
            (getMaxPerm (restrPermMap Hlt)) = (getMaxPerm m) .
        Proof.
          intros.
          pose proof (Cur_isCanonical m) as Hcanon. 
          unfold restrPermMap, getMaxPerm; simpl.
          unfold PMap.map; simpl.
          f_equal.
          rewrite map1_map_compose.
          rewrite map1_map.
          reflexivity.
        Qed.
        Lemma easy_mem_eq:
          forall m1 m2,
            Mem.mem_contents m1 = Mem.mem_contents m2 ->
            Mem.mem_access m1 = Mem.mem_access m2 ->
            Mem.nextblock m1 = Mem.nextblock m2 ->
            m1 = m2.
        Proof.
          intros. destruct m1, m2; simpl in *.
          subst. f_equal;
                   apply Axioms.proof_irr.
        Qed.
        Lemma restrPermMap_idempotent_eq:
          forall {perm0 perm1 m1}
            (Hlt0 : permMapLt perm0 (getMaxPerm m1))
            (Hlt1 : permMapLt perm1 (getMaxPerm m1))
            (Hlt2 : permMapLt perm1 (getMaxPerm (restrPermMap Hlt0))),
            (restrPermMap Hlt1) = (restrPermMap Hlt2).
        Proof.
          intros.
          destruct m1; simpl in *.
          eapply easy_mem_eq; try reflexivity.
          simpl.
          f_equal; simpl.
          - extensionality ofs.
            extensionality k.
            destruct k; auto.
          - rewrite map_compose; reflexivity.
        Qed.
        Lemma concur_match_perm_restrict:
          forall cd j st1 m1 st2 m2,
            concur_match cd j st1 m1 st2 m2 ->
            forall perms1 perms2 (permMapLt1: permMapLt perms1 (getMaxPerm m1))
              (permMapLt2: permMapLt perms2 (getMaxPerm m2)),
              concur_match cd j st1 (restrPermMap permMapLt1) st2 (restrPermMap permMapLt2).
        Proof.
          intros.
          inversion H.
          assert (memcompat3': mem_compatible st1 (restrPermMap permMapLt1)) by
              (eapply mem_compat_restrPermMap; eauto).
          assert (memcompat4': mem_compatible st2 (restrPermMap permMapLt2)) by
              (eapply mem_compat_restrPermMap; eauto).
          unshelve eapply Build_concur_match; eauto.
          - intros; simpl.
            erewrite <- (restrPermMap_idempotent _ _ Hlt1) .
            erewrite <- (restrPermMap_idempotent _ _ Hlt2) .
            eapply INJ_threads0.
          - intros; simpl.
            (
              erewrite <- (restrPermMap_idempotent _ _ Hlt1),
              <- (restrPermMap_idempotent _ _ Hlt2)).
            eapply INJ_locks0. 
            
          - erewrite virtueLP_inject_max_eq_exteny; eauto.
            eapply getMax_restr_eq.
          - simpl; intros.
            erewrite <- (restrPermMap_idempotent_eq _ _ Hlt1).
            erewrite <- (restrPermMap_idempotent_eq _ _ Hlt2).
            eapply mtch_source0; auto.
          - simpl; intros.
            erewrite <- (restrPermMap_idempotent_eq _ _ Hlt1).
            erewrite <- (restrPermMap_idempotent_eq _ _ Hlt2).
            eapply mtch_target0; auto.
          - simpl; intros.
            erewrite <- (restrPermMap_idempotent_eq _ _ Hlt1).
            erewrite <- (restrPermMap_idempotent_eq _ _ Hlt2).
            eapply mtch_compiled0; auto.


            Unshelve.
            all: 
              try (erewrite <- getMax_restr; eauto).
        Qed.
        

        Inductive state_indicator:=
        | Krun_indi
        | Kblocked_indi
        | Kresume_indi
        | Kinit_indi.
        Definition get_indicator {T: Type} (st:@ctl T): state_indicator:=
          match st with
          | Krun _ => Krun_indi
          | Kblocked _ => Kblocked_indi
          | Kresume _ _ => Kresume_indi
          | Kinit _ _ => Kinit_indi
          end.
        Definition thread_indicator {Res Sem} i st cnt:=
          get_indicator (@getThreadC Res Sem i st cnt).          
        Lemma concur_match_same_indicator:
          forall cd mu m1 c1 m2 c2,
            concur_match cd mu c1 m1 c2 m2 ->  
            forall i cnt1 cnt2,
              thread_indicator i c1 cnt1 = thread_indicator i c2 cnt2.
        Proof.
          intros.
          rename H into CMatch.
          pose proof (memcompat1 CMatch) as Hcmpt1.
          pose proof (memcompat2 CMatch) as Hcmpt2.
          destruct (Compare_dec.lt_eq_lt_dec i hb) as [[?|?]|?]; simpl in *. 
          - eapply CMatch in l.
            unfold thread_indicator.
            inv l; repeat match goal with
                            [H: _ = _ |- _] => rewrite <- H   
                          end; reflexivity.
          - eapply CMatch in e.
            unfold thread_indicator.
            inv e; repeat match goal with
                            [H: _ = _ |- _] => rewrite <- H   
                          end; reflexivity.
          - eapply CMatch in l.
            unfold thread_indicator.
            inv l; repeat match goal with
                            [H: _ = _ |- _] => rewrite <- H   
                          end; reflexivity.
            Unshelve.
            all: try eapply Hcmpt1.
            all: try eapply Hcmpt2.
        Qed.

        
        

        Lemma contains12:
          forall {data j cstate1 m1 cstate2 m2},
            concur_match data j cstate1 m1 cstate2 m2 ->
            forall {i:nat} (cnti1: containsThread cstate1 i),
              containsThread cstate2 i.
        Proof.
          unfold containsThread.
          intros ? ? ? ? ? ? H. destruct H.
          rewrite same_length0; auto.
        Qed.

        Lemma contains21:
          forall {data j cstate1 m1 cstate2 m2},
            concur_match data j cstate1 m1 cstate2 m2 ->
            forall {i:nat} (cnti1: containsThread cstate2 i),
              containsThread cstate1 i.
        Proof.
          unfold containsThread.
          intros ? ? ? ? ? ? H. destruct H.
          rewrite same_length0; auto.
        Qed.
        
        
        Lemma concur_match_same_running:
          forall (m : option mem) (cd : option compiler_index) (mu : meminj)
            (c1 : ThreadPool (Some hb)) (m1 : mem) (c2 : ThreadPool (Some (S hb))) 
            (m2 : mem),
            concur_match cd mu c1 m1 c2 m2 ->
            forall i : nat,
              machine_semantics.running_thread (HybConcSem (Some hb) m) c1 i <->
              machine_semantics.running_thread (HybConcSem (Some (S hb)) m) c2 i.
        Proof.
          intros.
          unfold machine_semantics.running_thread; simpl.
          unfold HybridMachineSig.unique_Krun.
          cut (
              (forall (j : nat) (cnti : ThreadPool.containsThread c1 j),
                  thread_indicator j c1 cnti = Krun_indi ->
                  Datatypes.is_true (ssrbool.is_left (Nat.eq_dec i j))) <->
              (forall (j : nat) (cnti : ThreadPool.containsThread c2 j),
                  thread_indicator j c2 cnti = Krun_indi ->
                  Datatypes.is_true (ssrbool.is_left (Nat.eq_dec i j)))
            ).
          { intros (A & B).
            split; intros; simpl in *.
            - eapply A.
              + intros. 
                unfold thread_indicator in *.
                destruct (getThreadC cnti0) eqn:HH; inversion H2.
                eapply H0; eauto.
              + unfold thread_indicator; rewrite H1; auto.
            - intros. eapply B.
              + intros. 
                unfold thread_indicator in *.
                destruct (getThreadC cnti0) eqn:HH; inversion H2.
                eapply H0; eauto.
              + unfold thread_indicator; rewrite H1; auto.
          }
          split; intros;
            first [erewrite concur_match_same_indicator in *|
                                                             erewrite <- concur_match_same_indicator in *]; eauto.

          Unshelve.
          all: simpl in *.
          eapply (contains21); eassumption.
          eapply (contains12); eassumption.
        Qed.
        
        Inductive individual_match i:
          meminj -> ctl -> mem -> ctl -> mem -> Prop:= 
        |individual_mtch_source:
           (i > hb)%nat ->
           forall j s1 m1 s2 m2,
             match_thread_source j s1 m1 s2 m2 ->
             individual_match i j s1 m1 s2 m2
        |individual_mtch_target:
           (i < hb)%nat ->
           forall j s1 m1 s2 m2,
             match_thread_target j s1 m1 s2 m2 ->
             individual_match i j s1 m1 s2 m2
        | individual_mtch_compiled:
            (i = hb)%nat ->
            forall cd j s1 m1 s2 m2,
              match_thread_compiled cd j s1 m1 s2 m2 ->
              individual_match i j s1 m1 s2 m2.
        Definition computeMap_pair:= pair2 computeMap.
        Hint Unfold computeMap_pair: pair.

        
        Inductive lock_update {hb}: nat -> ThreadPool hb -> Address.address ->
                                    (Pair access_map) -> lock_info -> _ -> ThreadPool hb -> Prop:=
        | Build_lock_update:
            forall st st' i add th_perms lock_perms c
              (cnt : containsThread st i),
              st' = updLockSet
                      (updThread(resources:=dryResources) cnt c th_perms)
                      add lock_perms ->
              @lock_update hb i st add th_perms lock_perms c st'.
        
        Notation sstate:= (state_sum (@semC CSem) (@semC AsmSem)).
        Inductive one_thread_match  (hb i:nat): option compiler_index ->
                                              meminj -> @ctl sstate -> mem -> @ctl sstate -> mem -> Prop:=
        | build_match_source:
            forall ocd f c1 m1 c2 m2,
              (i > hb)%nat ->
              match_thread_source f c1 m1 c2 m2 ->
              one_thread_match hb i ocd f c1 m1 c2 m2
        | build_match_target:
            forall ocd f c1 m1 c2 m2,
              (i < hb)%nat ->
              match_thread_target f c1 m1 c2 m2 ->
              one_thread_match hb i ocd f c1 m1 c2 m2
        | build_match_compiled:
            forall ocd f c1 m1 c2 m2,
              (i = hb)%nat ->
              match_thread_compiled ocd f c1 m1 c2 m2 ->
              one_thread_match hb i ocd f c1 m1 c2 m2.
        
        Inductive lock_update' {hb}:
          nat -> ThreadPool hb -> Address.address ->
          (Pair access_map) -> @lock_info dryResources -> _ -> ThreadPool hb -> Prop:=
        | Build_lock_update':
            forall (st st': ThreadPool hb)
              i add th_perms th_lock_perms lk_perms c
              (* contains *)
              (Hcnt_iff: forall i, ThreadPool.containsThread st i ->
                              ThreadPool.containsThread st' i)
              (Hcnt_iff': forall i, ThreadPool.containsThread st' i ->
                               ThreadPool.containsThread st i)
              
              (* Code  *)
              (gcs: forall (cnt':ThreadPool.containsThread st' i), 
                  ThreadPool.getThreadC cnt' = c )
              (gco: forall j (cnt:ThreadPool.containsThread st j) (cnt':ThreadPool.containsThread st' j), 
                  j<>i -> ThreadPool.getThreadC cnt' = ThreadPool.getThreadC cnt)

              (* Thread Perms and Thread lock perms *)
              (gts: forall (cnt':ThreadPool.containsThread st' i), 
                  ThreadPool.getThreadR(resources:=dryResources) cnt' = (th_perms,th_lock_perms))
              (gto: forall j (cnt:ThreadPool.containsThread st j) (cnt':ThreadPool.containsThread st' j), 
                  j<>i -> ThreadPool.getThreadR cnt' = ThreadPool.getThreadR cnt)

              (* Thread Perms *)
              (gtts: forall (cnt':ThreadPool.containsThread st' i), 
                  fst (ThreadPool.getThreadR(resources:=dryResources) cnt') = th_perms)
              (gtto: forall j (cnt:ThreadPool.containsThread st j) (cnt':ThreadPool.containsThread st' j), 
                  j<>i -> fst (ThreadPool.getThreadR cnt') = fst  (ThreadPool.getThreadR cnt))

              (* Thread lock Perms*) 
              (gtls: forall (cnt':ThreadPool.containsThread st' i), 
                  snd (ThreadPool.getThreadR(resources:=dryResources) cnt') = th_lock_perms)
              (gtlo: forall j (cnt:ThreadPool.containsThread st j) (cnt':ThreadPool.containsThread st' j), 
                  j<>i -> snd (ThreadPool.getThreadR cnt') = snd (ThreadPool.getThreadR cnt))
              
              (* Lock perms *)
              (gls: ThreadPool.lockRes st' add  = Some lk_perms)
              (glo: forall add', add<>add' -> ThreadPool.lockRes st' add' = ThreadPool.lockRes st add'),
              @lock_update' hb i st add (th_perms,th_lock_perms) lk_perms  c st'.
        
        Lemma lock_update_getters:
          forall {hb  i st b ofs th_perms th_lock_perms lock_perms c st'},
            @lock_update hb i st (b,ofs) (th_perms,th_lock_perms)
                         lock_perms  c st' ->
            @lock_update' hb i st (b,ofs) (th_perms,th_lock_perms)
                          lock_perms  c st'.
        Proof.
          intros * H; inversion H.
          subst i0 st0 add0 th_perms0 c0 st'0.
          
          assert (gcs: forall (cnt': ThreadPool.containsThread st' i) , ThreadPool.getThreadC cnt' = c).
          { intros; subst st'; eapply gssThreadCC. }

          assert (gco: forall j (neq:j <> i)
                         (cnt: ThreadPool.containsThread st j)
                         (cnt': ThreadPool.containsThread st' j),
                     ThreadPool.getThreadC cnt' = ThreadPool.getThreadC cnt).
          { intros; subst st'; etransitivity.
            eapply gLockSetCode.
            symmetry; eapply gsoThreadCC.
            symmetry; assumption.
          }

          assert (gts: forall (cnt': ThreadPool.containsThread st' i) ,
                     ThreadPool.getThreadR cnt' = (th_perms, th_lock_perms)).
          { intros; subst st'; eapply gssThreadRR. }

          assert (gto: forall j (neq:j <> i)
                         (cnt: ThreadPool.containsThread st j)
                         (cnt': ThreadPool.containsThread st' j),
                     ThreadPool.getThreadR cnt' = ThreadPool.getThreadR cnt).
          { intros; subst st'; etransitivity.
            eapply gLockSetRes.
            symmetry; eapply gsoThreadRR.
            symmetry; eassumption.
          }
          
          
          
          subst st'.
          econstructor; intros *; eauto.
          - rewrite gts; auto.
          - intros; erewrite gto; auto.
          - rewrite gts; auto.
          - intros; erewrite gto; auto.
          - simpl; rewrite gssLockRes; reflexivity.
          - intros. simpl.
            rewrite gsoLockRes, gsoThreadLPool; auto.
            
            Unshelve.
            all: unshelve( eapply cntUpdateR; eauto);
              eauto.
            
        Qed.

        
        Definition same_content_in m m' ofs b:=
          ZMap.get ofs (Mem.mem_contents m') !! b =
          ZMap.get ofs (Mem.mem_contents m) !! b.
        Definition content_almost_same m m' adr:=
          forall  b ofs,
            (* b <> fst adr \/ ~ Intv.In ofs (snd adr,snd adr+ LKSIZE) -> *)
            (b, ofs) <> adr ->  same_content_in m m' ofs b.
        Definition contnet_same_intval m m' adr SIZE:=
          forall b ofs,
            b = fst adr /\ Intv.In ofs (snd adr, snd adr + SIZE) ->
            same_content_in m m' ofs b.
        
        Definition get_val_at (m:mem) (adr: block * Z):=
          (ZMap.get (snd adr) (Mem.mem_contents m) !! (fst adr)).
        Inductive lock_update_mem: mem -> Address.address -> memval -> mem -> Prop:=
        | Build_lock_update_mem:
            forall m m' adr v
              (Hcontent_almost_equiv: content_almost_same m m' adr)
              (Hnew_val: get_val_at m' adr = v)
              (Hcur_equiv: Cur_equiv m m')
              (Hmax_equiv: Max_equiv m m')
              (Hmax_wrt: Mem.perm m (fst adr) (snd adr) Max Writable)
              (Hnb_equiv: Mem.nextblock m = Mem.nextblock m'),
              lock_update_mem m adr v m'.
        Instance content_almost_same_proper:
          Proper (content_equiv ==> content_equiv ==> Logic.eq ==> iff)
                 content_almost_same.
        Proof.
          unfold content_almost_same, same_content_in.
          setoid_help.proper_iff;
            setoid_help.proper_intros; subst.
          rewrite <- H, <- H0; eauto.
        Qed.
        Ltac destruct_lock_update_getters:=
          match goal with
          | [ H: lock_update _ _ _ _ _ _ _ |- _ ] =>
            apply lock_update_getters in H; inv H
          | [H: lock_update_mem _ _ _ _ |- _ ] => inv H
          end.
        Ltac lock_update_contains:=
          match goal with
          | [ H: containsThread ?st ?i  |- _ ] =>
            match goal with
            | [ H: forall x,  ThreadPool.containsThread st ?j ->
                         ThreadPool.containsThread ?st' _ |- _ ] =>
              match goal with
              | [ H: ThreadPool.containsThread st' i  |- _ ] => fail 1
              | [ H: containsThread st' i  |- _ ] => fail 1
              | _ => let cnt:=fresh "cnt" in
                    assert (cnt:containsThread st' i); try eapply H; auto;
                    simpl in cnt
              end
            end
          end.
        
        Ltac super_rewrite:=
          match goal with
          | [ H: _ |- _ ] => erewrite H by solve[eauto] 
          end.
        Ltac lock_update_rewrite:=
          repeat lock_update_contains;
          simpl in *;
          unshelve (repeat (super_rewrite)); try eassumption.

        Definition meminj_no_overlap_one (f: meminj) (m: mem) (adr1 adr2: block * Z) := 
          forall delta1 b1 delta2 ofs1,
            f (fst adr1) = Some (fst adr2, delta1) ->
            f b1 = Some (fst adr2, delta2) ->
            Mem.perm m b1 ofs1 Max Nonempty ->
            ofs1 + delta2 = (snd adr1) + delta1 ->
            b1 = (fst adr1).
        Lemma meminj_no_overlap_to_on:
          forall f m adr1 adr2,
            Mem.perm m (fst adr1) (snd adr1) Max Nonempty ->
            Mem.meminj_no_overlap f m ->
            meminj_no_overlap_one f m adr1 adr2.
        Proof.
          intros ** ? **.
          destruct (Clight_lemmas.block_eq_dec b1 (fst adr1)); auto.
          exploit H0; eauto.
          intros [ ? | ? ].
          - contradict H5; reflexivity.
          - contradict H5; assumption. 
        Qed.
        Lemma adddress_eq_dec:
          forall (a b: block * Z), {a = b} + {a <> b}.
        Proof.
          intros. destruct a as (a1& a2);
                    destruct b as (b1& b2).
          destruct (Clight_lemmas.block_eq_dec a1 b1) as [eq|n];
            destruct (Z.eq_dec a2 b2)as [eq'|n']; try subst;
              simpl in *; auto;
                try (right; intros HH; inv HH; try apply n; try apply n'; auto). 
        Qed.
        
        Lemma perm_order_trans101:
          forall oa b c, Mem.perm_order' oa b ->
                    perm_order b c -> Mem.perm_order' oa c.
        Proof.
          intros. eapply (perm_order_trans211 _ (Some b));
                    simpl; auto.
        Qed.
        Lemma mem_inj_update:
          forall (f:meminj) m1 m2 m1' m2' adr1 adr2
            (Hno_overlap:
               meminj_no_overlap_one f m1 adr1 adr2)
            (Hmax_eq1: Max_equiv m1 m1')
            (Hmax_eq2: Max_equiv m2 m2')
            (Hcur_eq1: Cur_equiv m1 m1')
            (Hcur_eq2: Cur_equiv m2 m2')
            (Hadr_inj: inject_address f adr1 adr2)
            (Halmost1: content_almost_same m1 m1' adr1)
            (Halmost2: content_almost_same m2 m2' adr2)
            (Hsame12: memval_inject f (get_val_at m1' adr1) (get_val_at m2' adr2))
            (Hmem_inj: Mem.mem_inj f m1 m2),
            Mem.mem_inj f m1' m2'.
        Proof.
          econstructor; intros.
          - destruct k;
              first [rewrite <- Hmax_eq2 |rewrite <- Hcur_eq2];
              eapply Hmem_inj; eauto;
                first [rewrite Hmax_eq1 |rewrite Hcur_eq1];
                assumption.
          - eapply Hmem_inj; eauto.
            rewrite Hmax_eq1; eassumption.
          - rewrite <- Hcur_eq1 in H0.
            unfold get_val_at in Hsame12.
            destruct (adddress_eq_dec (b1, ofs) adr1).
            + subst adr1; eauto.
              inv Hadr_inj. unify_injection.
              simpl in *. eapply Hsame12.
            + rewrite Halmost1; auto.
              destruct (adddress_eq_dec (b2, ofs + delta) adr2).
              * subst adr2. inv Hadr_inj.
                move Hno_overlap at bottom.
                unfold meminj_no_overlap_one in *; simpl in *.
                exploit (Hno_overlap delt b1 delta ofs);
                  try reflexivity; try eassumption.
                -- simpl. cut (Mem.perm m1 b1 ofs Cur Nonempty).
                   eapply Mem.perm_cur_max.
                   eapply perm_order_trans101.
                   eapply H0. constructor.
                -- intros HH; subst b0. eauto.
                   unify_injection. assert (ofs1 = ofs) by omega. subst ofs.
                   contradict n; reflexivity.
              * rewrite Halmost2; auto. eapply Hmem_inj; auto.
        Qed.
        
        Lemma injection_update:
          forall f m1 m2 m1' m2' adr1 adr2
            (Hnonempty: Mem.perm m1 (fst adr1) (snd adr1) Max Nonempty)
            (Hsame_nb1: Mem.nextblock m1 = Mem.nextblock m1')
            (Hsame_nb2: Mem.nextblock m2 = Mem.nextblock m2')
            (Hmax_eq1: Max_equiv m1 m1')
            (Hmax_eq2: Max_equiv m2 m2')
            (Hcur_eq1: Cur_equiv m1 m1')
            (Hcur_eq2: Cur_equiv m2 m2')
            (Hadr_inj: inject_address f adr1 adr2)
            (Halmost1: content_almost_same m1 m1' adr1)
            (Halmost2: content_almost_same m2 m2' adr2)
            (Hsame12: memval_inject f (get_val_at m1' adr1) (get_val_at m2' adr2))
            (Hmem_inj: Mem.inject f m1 m2),
            Mem.inject f m1' m2'.
        Proof.
          econstructor; intros.
          - eapply mem_inj_update; try eassumption. 2: apply Hmem_inj.
            eapply meminj_no_overlap_to_on. 2: apply Hmem_inj.
            auto.
          - eapply Hmem_inj.
            unfold Mem.valid_block in *. rewrite Hsame_nb1; assumption.
          - unfold Mem.valid_block; rewrite <- Hsame_nb2.
            eapply Hmem_inj; eassumption.
          - rewrite <- Hmax_eq1. apply Hmem_inj.
          - eapply Hmem_inj; eauto.
            rewrite Hmax_eq1; auto.
          - destruct k;
              first [rewrite <- Hmax_eq2 in H0 |rewrite <- Hcur_eq2 in H0];
              eapply Hmem_inj in H0; eauto.
            + rewrite <- Hmax_eq1; auto.
            + destruct H0; 
                first [left; rewrite <- Hcur_eq1;assumption |right; rewrite <- Hmax_eq1; assumption].
        Qed.
        

        Lemma lock_update_mem_restr:
          forall m adr1 v1 m',
            lock_update_mem m adr1 v1 m' ->
            forall p p' Hlt Hlt',
              access_map_equiv p p' ->
              lock_update_mem (@restrPermMap p m Hlt)
                              adr1 v1 (@restrPermMap p' m' Hlt').
        Proof.
          intros. inv H; econstructor; auto.
          - unfold Cur_equiv. do 2 rewrite getCur_restr; assumption.
          - unfold Max_equiv. do 2 rewrite getMax_restr; assumption.
          - rewrite restr_Max_equiv; assumption.
        Qed.
        Lemma max_equiv_restr:
          forall m m' perm perm' Hlt Hlt',
            Max_equiv m m' ->
            Max_equiv (@restrPermMap perm m  Hlt )
                      (@restrPermMap perm' m' Hlt').
        Proof.
          intros. unfold Max_equiv.
          etransitivity; [|symmetry].
          eapply restr_Max_equiv.
          etransitivity; [eapply restr_Max_equiv|].
          symmetry; eapply H.
        Qed.
        Lemma cur_equiv_restr:
          forall m m' perm Hlt Hlt',
            Cur_equiv (@restrPermMap perm m  Hlt )
                      (@restrPermMap perm m' Hlt').
        Proof.
          intros; unfold Cur_equiv;
            etransitivity; [|symmetry]; eapply getCur_restr.
        Qed.
        
        
        Lemma permMapLt_Max_equiv:
          forall p m m',
            Max_equiv m m' ->
            permMapLt p (getMaxPerm m) ->
            permMapLt p (getMaxPerm m').
        Proof. unfold Max_equiv; intros * <-; auto. Qed.
        
        Inductive update_mem (m m':mem) (adr:block * Z): Prop:=
        | Build_update_mem:
            Max_equiv m m' ->
            Cur_equiv m m' ->
            Mem.nextblock m = Mem.nextblock m' ->
            content_almost_same m m' adr ->
            update_mem m m' adr.
        Lemma injection_update_restrict:
          forall f m1 m1' m2 m2' p1 p2 adr1 adr2,
            Mem.perm m1 (fst adr1) (snd adr1) Max Writable ->
            update_mem m1 m1' adr1 ->
            update_mem m2 m2' adr2 ->
            inject_address f adr1 adr2 ->
            memval_inject f (get_val_at m1' adr1) (get_val_at m2' adr2) ->
            forall Hlt1' Hlt2',
              (forall Hlt1 Hlt2,
                  Mem.inject f (@restrPermMap p1 m1 Hlt1) (@restrPermMap p2 m2 Hlt2)) ->
              Mem.inject f (@restrPermMap p1 m1' Hlt1') (@restrPermMap p2 m2' Hlt2').
        Proof.
          intros. inv H0; inv H1.
          eapply permMapLt_Max_equiv in Hlt1' as Hlt1; try (symmetry;eassumption). 
          eapply permMapLt_Max_equiv in Hlt2' as Hlt2; try (symmetry;eassumption). 
          eapply (injection_update f (restrPermMap Hlt1) (restrPermMap Hlt2));
            simpl; first [ reflexivity
                         | simpl; eassumption
                         | simpl; symmetry; eassumption
                         | eapply max_equiv_restr; eassumption
                         | eapply cur_equiv_restr
                         | eauto].
          - rewrite restr_Max_equiv; simpl in *.
            eapply Mem.perm_implies; eauto. constructor.
        Qed.
        Lemma concur_match_update_lock:
          forall i f ocd st1 m1 st2 m2,
            concur_match ocd f st1 m1 st2 m2 ->
            forall ocd' (st1':t) m1' st2' m2' b_lock1 b_lock2 ofs_lock delta,
            forall th_perms1 th_perms2 v1 v2
              (Hupdate_mem1: lock_update_mem m1 (b_lock1, ofs_lock) v1 m1')
              (Hupdate_mem2: lock_update_mem m2 (b_lock2, ofs_lock+delta) v2 m2')
              (* Hinj: Mem.inject f m1' m2' *)
              (Hlt1 : permMapLt th_perms1 (getMaxPerm m1'))
              (Hlt2 : permMapLt th_perms2 (getMaxPerm m2'))
              (Hinj_perms:
                 Mem.inject f (restrPermMap Hlt1) (restrPermMap Hlt2))
              
              (Hinv1: invariant(tpool:=OrdinalThreadPool) st1')
              (Hinv2: invariant(tpool:=OrdinalThreadPool) st2')
              
              (Hmem_compat1: mem_compatible(tpool:=OrdinalThreadPool) st1' m1')
              (Hmem_compat2: mem_compatible(tpool:=OrdinalThreadPool) st2' m2')
              
              th_lock_perms1 th_lock_perms2
              (Hlock_ppimage: perm_preimage f th_lock_perms1 th_lock_perms2)
              (Hlt_lock1 : permMapLt th_lock_perms1 (getMaxPerm m1'))
              (Hlt_lock2 : permMapLt th_lock_perms2 (getMaxPerm m2'))
              (Hinj_locks: Mem.inject f (restrPermMap Hlt_lock1) (restrPermMap Hlt_lock2))
              (Hinj_lock: f b_lock1 = Some (b_lock2, delta)) c1 c2
              (Hthread_match: one_thread_match hb i ocd f  
                                               c1 (restrPermMap Hlt1)
                                               c2 (restrPermMap Hlt2))
              (Hval_inj: memval_inject f v1 v2),
            forall lock_perms1
              (cnt1 : containsThread st1 i)
              (cnt2 : containsThread st2 i),
              lock_update i st1 (b_lock1,ofs_lock) (th_perms1,th_lock_perms1)
                          lock_perms1 c1 st1' ->
              lock_update i st2 (b_lock2,ofs_lock+delta) (th_perms2,th_lock_perms2)
                          (virtueLP_inject m2' f lock_perms1) c2 st2' ->
              concur_match ocd' f st1' m1' st2' m2'.
        Proof.
          intros.
          
          assert (Hsame_lenght1: num_threads st1 = num_threads st1').
          { inv H0; reflexivity. }
          assert (Hsame_lenght2: num_threads st2 = num_threads st2').
          { inv H1; reflexivity. }

          repeat destruct_lock_update_getters. 
          eapply Build_concur_match; simpl; eauto.
          - rewrite <- Hsame_lenght1, <- Hsame_lenght2; apply H.
          - !goal(Events.injection_full _ _ ).
            intros b ?. eapply H. unfold Mem.valid_block.
            rewrite Hnb_equiv0; eauto.
          - !context_goal perm_preimage.
            intros i0 ??; destruct (Nat.eq_dec i0 i); subst.
            + lock_update_rewrite.
            + lock_update_rewrite. eapply H.
          - !context_goal Mem.inject.
            intros i0 ??; destruct (Nat.eq_dec i i0); subst.
            + lock_update_rewrite.
              intros; repeat unify_proofs; assumption.
            + intros; simpl in *.
              eapply injection_update_restrict; 
                eauto; simpl; eauto; try solve [econstructor; eauto].
              intros.
              eapply mem_inject_equiv;
                try eapply INJ_threads; try reflexivity;
                  try eapply restrPermMap_equiv; eauto;
                    try reflexivity; simpl.
              erewrite gto0; eauto; reflexivity.
              erewrite gto; eauto; reflexivity.

              
          - intros i0 ??; destruct (Nat.eq_dec i i0); subst.
            + lock_update_rewrite; simpl.
              intros. unify_proofs. assumption. 
            + intros; simpl in *.
              eapply injection_update_restrict; 
                eauto; simpl; eauto; try solve [econstructor; eauto].
              intros.
              eapply mem_inject_equiv;
                try eapply INJ_locks; try reflexivity;
                  try eapply restrPermMap_equiv; eauto;
                    try reflexivity; simpl.
              erewrite gtlo0; eauto; reflexivity.
              erewrite gtlo; eauto; reflexivity.

          - intros until ofs.
            lock_update_rewrite; simpl.
            (* TODO: Change INJ_lock_permissions 
               1. it is wrong:
                  If two blocks point to the same one (f b1 = f b1' = Some (b2, _))
                  and one of them is a lock (lockres st1 b1 = Some _) then the other isnt,
                  and INJ_permissions is contradicting (lockres st1 b2 = Some _ = None)
               2. Need to rewrite it in two parts: 
                  If lockres st1 l1 = Some -> lockres st2 l2 = Some
                  and
                  If lockres st2 l2 = Some -> lockres st1 l1 = Some
             *)
            replace (unsigned (add ofs (repr delt))) with (unsigned ofs + delt).
            2: { admit. }
            destruct (addressFiniteMap.AMap.E.eq_dec (b_lock1, ofs_lock) (b, unsigned ofs) ).
            + inv e. unify_injection.
              lock_update_rewrite.
              intros HH; inv HH; reflexivity.
            + lock_update_rewrite.
              rewrite glo; auto.
              * admit.
              * admit.
          - !context_goal inject_lock.
            intros.
            destruct (addressFiniteMap.AMap.E.eq_dec (b,ofs) (b_lock1, ofs_lock)).
            + inv e.
              unfold inject_lock,inject_lock'.
              do 2 eexists. repeat weak_split eauto.
              admit. (* Check do we need this property? *)
            + unfold inject_lock, inject_lock'.
              admit.
          - intros ? Hneq ??.
            assert (Hneq': i0 <> hb) by omega.
            lock_update_rewrite.
            admit.
          - intros ? Hneq ??.
            assert (Hneq': i0 <> hb) by omega.
            lock_update_rewrite.
            admit.
          - intros. admit.
        Admitted.
        
        Lemma concur_match_update1:
          forall (st1: ThreadPool.t) (m1 m1' : mem) (tid : nat) (Htid : ThreadPool.containsThread st1 tid)
            c1 (cd cd' : option compiler_index) (st2 : ThreadPool.t) 
            (mu : meminj) (m2 : mem)
            c2
            (f' : meminj) (m2' : mem) (Htid' : ThreadPool.containsThread st2 tid)
            (mcompat1: mem_compatible st1 m1)
            (mcompat2: mem_compatible st2 m2),
            semantics.mem_step
              (restrPermMap (proj1 (mcompat1 tid Htid))) m1' ->
            semantics.mem_step
              (restrPermMap (proj1 (mcompat2 tid Htid'))) m2' ->
            invariant st1 ->
            invariant st2 ->
            concur_match cd mu st1 m1 st2 m2 ->
            individual_match tid f' c1 m1' c2 m2' ->
            self_simulation.is_ext mu (Mem.nextblock m1) f' (Mem.nextblock m2) ->
            concur_match cd' f'
                         (updThread Htid c1
                                    (getCurPerm m1', snd (getThreadR Htid))) m1'
                         (updThread Htid' c2
                                    (getCurPerm m2', snd (getThreadR Htid'))) m2'.
        Proof.
          (* TODO! *)
        Admitted.
        
        (* concur_match *)


      End ConcurMatch. (* 1273 360  *) 
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
      Ltac forget_memcompat1:=
        match goal with
        | [ H: context[memcompat1 ?CM] |- _ ] =>
          let HH:= fresh "HH" in
          let Hcmpt:= fresh "Hcmpt" in
          remember (memcompat1 CM) as Hcmpt eqn:HH; clear HH 
        | [ |-  context[memcompat1 ?CM] ] =>
          let HH:= fresh "HH" in
          let Hcmpt:= fresh "Hcmpt" in
          remember (memcompat1 CM) as Hcmpt eqn:HH; clear HH 
        end.
      Ltac forget_memcompat2:=
        match goal with
        | [ H: context[memcompat2 ?CM] |- _ ] =>
          let HH:= fresh "HH" in
          let Hcmpt:= fresh "Hcmpt" in
          remember (memcompat2 CM) as Hcmpt eqn:HH; clear HH
        | [  |- context[memcompat2 ?CM] ] =>
          let HH:= fresh "HH" in
          let Hcmpt:= fresh "Hcmpt" in
          remember (memcompat2 CM) as Hcmpt eqn:HH; clear HH 
        end.
      Ltac unify_mem_compatible:=
        repeat match goal with
               | [ H1: mem_compatible ?st ?m,
                       H2: mem_compatible ?st ?m |- _ ] =>
                 replace H2 with H1 in * by ( apply Axioms.proof_irr); clear H2
               end.

      Ltac clean_cmpt:=
        try forget_memcompat1;
        try forget_memcompat2;
        unify_mem_compatible.
      
      
      Ltac clean_cmpt':=
        match goal with
        | [ CMatch: concur_match _ _ _ _ _ _,
                    Hcmpt:mem_compatible ?st ?m |- _ ] =>
          repeat(
              match goal with
              | [   |- context[Hcmpt] ] =>
                replace Hcmpt with (memcompat1 CMatch)
                  by apply Axioms.proof_irr
              | [ HH:context[Hcmpt]  |- _ ] =>
                replace Hcmpt with (memcompat1 CMatch) in HH
                  by apply Axioms.proof_irr
              end)
        end.

      
      Ltac forget_contains12:=
        match goal with
        | [ H: context[@contains12 _ _ _ _ _ _ ?CM ?i ?cnt1] |- _ ] =>
          let HH:= fresh "HH" in
          let Hcnt:= fresh "Hcnt" in
          remember (@contains12 _ _ _ _ _ _ CM i cnt1) as Hcnt eqn:HH; clear HH 
        | [ |- context[@contains12 _ _ _ _ _ _ ?CM ?i ?cnt1] ] =>
          let HH:= fresh "HH" in
          let Hcnt:= fresh "Hcnt" in
          remember (@contains12 _ _ _ _ _ _ CM i cnt1) as Hcnt eqn:HH; clear HH 
        end.

      Ltac forget_contains21:=
        match goal with
        | [ H: context[@contains21 _ _ _ _ _ _ ?CM ?i ?cnt1] |- _ ] =>
          let HH:= fresh "HH" in
          let Hcnt:= fresh "Hcnt" in
          remember (@contains21 _ _ _ _ _ _ CM i cnt1) as Hcnt eqn:HH; clear HH 
        | [ |- context[@contains21 _ _ _ _ _ _ ?CM ?i ?cnt1] ] =>
          let HH:= fresh "HH" in
          let Hcnt:= fresh "Hcnt" in
          remember (@contains21 _ _ _ _ _ _ CM i cnt1) as Hcnt eqn:HH; clear HH 
        end.
      
      Ltac unify_containsThread:=
        repeat match goal with
               | [ H1: containsThread ?st ?i,
                       H2: containsThread ?st ?i |- _ ] =>
                 replace H2 with H1 in * by ( apply Axioms.proof_irr); clear H2
               end.
      (* Ltac clean_cnt:=
        try forget_contains12;
        try forget_contains21;
        unify_containsThread. *)
      Ltac forget_as a A :=
        let Heq:=fresh in
        remember a as A eqn:Heq; clear Heq.
      Tactic Notation "forget" constr(a) "as" simple_intropattern(A):=
        forget_as a A.
      Ltac clean_cnt_goal:=
        match goal with
          |- context[?c] =>
          match type of c with
            containsThread _ _ =>
            is_applied c;
            let Hcnt:=fresh "Hcnt" in
            forget c as Hcnt
          end
        end.
      Ltac clean_cnt_hyp:=
        match goal with
          [H:context[?c] |- _] =>
          match type of c with
            containsThread _ _ =>
            is_applied c;
            let Hcnt:=fresh "Hcnt" in
            forget c as Hcnt
          end
        end.
      Ltac clean_cnt:=
        repeat match goal with
               | [ H: ThreadPool.containsThread _ _ |- _ ] =>
                 simpl in H
               end;
        repeat clean_cnt_goal;
        repeat clean_cnt_hyp;
        unify_containsThread.

      Ltac clean_cnt':=
        match goal with
        | [ CMatch: concur_match _ _ ?st1 _ ?st2 _ |- _] =>
          match goal with
          | [ Hcnt1: containsThread st1 ?i,
                     Hcnt2: containsThread st2 ?i |- _ ] =>
            (*Check if contains12 or contains21 is already used. *)
            first [match goal with
                   | [ HH: context[contains21] |- _ ] =>  idtac
                   | [  |- context[contains21] ] =>  idtac
                   | _ => fail 1
                   end; 
                   repeat(
                       match goal with
                       | [   |- context[Hcnt1] ] =>
                         replace Hcnt1 with (contains21 CMatch Hcnt2)
                           by apply Axioms.proof_irr
                       | [ HH:context[Hcnt1]  |- _ ] =>
                         replace Hcnt1 with (contains21 CMatch Hcnt2) in HH
                           by apply Axioms.proof_irr
                       end) |
                   repeat(
                       match goal with
                       | [   |- context[Hcnt2] ] =>
                         replace Hcnt2 with (contains12 CMatch Hcnt1)
                           by apply Axioms.proof_irr
                       | [ HH:context[Hcnt2]  |- _ ] =>
                         replace Hcnt2 with (contains12 CMatch Hcnt1) in HH
                           by apply Axioms.proof_irr
                       end) ]
          end
        end.

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
      
        
      Lemma thread_step_plus_from_corestep':
          forall NN (m : option mem) (tge : ClightSemanticsForMachines.G * Asm.genv)
            (U : list nat) (st1 : t) (m1 : mem) (Htid : containsThread st1 hb) 
            (st2 : t) (mu : meminj) (m2 : mem) (cd0 : compiler_index)
            (CMatch : concur_match (Some cd0) mu st1 m1 st2 m2) (code2 : Asm.state)
            (s4' : Smallstep.state (Asm.part_semantics Asm_g)) 
            (m4' : mem),
            corestepN (Asm_core.Asm_core_sem Asm_g) (S NN) code2
                      (restrPermMap
                         (proj1 ((memcompat2 CMatch) hb (contains12 CMatch Htid))))
                      s4' m4' ->
            forall Htid' : containsThread st2 hb,
              machine_semantics_lemmas.thread_step_plus
                (HybConcSem (Some (S hb)) m) tge U st2
                m2 (updThread Htid' (Krun (TState Clight.state Asm.state s4'))
                              (getCurPerm m4', snd (getThreadR Htid'))) m4'.
        Proof.
          simpl; induction NN; simpl; intros .
          - destruct H as (c2 & m3 & STEP & Heq). inv Heq.
            simpl in STEP. inv STEP.
            exists O; simpl; do 2 eexists. split; try reflexivity.
            replace (Asm.get_mem s4') with (HybridMachineSig.diluteMem  (Asm.get_mem s4'))
              by reflexivity.
            exploit Asm_event.asm_ev_ax2.
            econstructor; simpl; eauto; [eapply H | eapply H0].
            intros (T&HH).
            econstructor; eauto.
            
            
            2 : { econstructor; simpl; eauto.
                  - eapply CMatch. 
                  - admit. (* USE CONCUR*)
                  - right. unfold Asm_g in *. unfold the_ge in *.
                    eauto. simpl in HH.
                    clean_cnt'. eapply HH. }

            !goal (HybridMachineSig.schedPeek U = Some hb).
            admit.
          -admit.
        Admitted.
      Lemma thread_step_plus_from_corestep:
        forall (m : option mem) (tge : ClightSemanticsForMachines.G * Asm.genv)
          (U : list nat) (st1 : t) (m1 : mem) (Htid : containsThread st1 hb) 
          (st2 : t) (mu : meminj) (m2 : mem) (cd0 : compiler_index)
          (H0 : concur_match (Some cd0) mu st1 m1 st2 m2) (code2 : Asm.state)
          (s4' : Smallstep.state (Asm.part_semantics Asm_g)) 
          (m4' : mem),
          corestep_plus (Asm_core.Asm_core_sem Asm_g) code2
                        (restrPermMap
                           (proj1 ((memcompat2 H0) hb (contains12 H0 Htid))))
                        s4' m4' ->
          forall Htid' : containsThread st2 hb,
            machine_semantics_lemmas.thread_step_plus
              (HybConcSem (Some (S hb)) m) tge U st2
              m2 (updThread Htid' (Krun (TState Clight.state Asm.state s4'))
                            (getCurPerm m4', snd (getThreadR Htid'))) m4'.
      Proof.
        (** NOTE: This might be missing that the corestep never reaches an at_external
                  If this is the case, we might need to thread that through the compiler...
                  although it should be easy, I would prefere if there is any other way...
         *)
        intros.
        destruct H as (NN& H).
        eapply thread_step_plus_from_corestep'; eauto.
      Qed.
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
      
      Inductive same_cnt {hb1 hb2} i (st1: ThreadPool hb1) (st2: ThreadPool hb2):
        containsThread st1 i ->
        containsThread st2 i -> Prop :=
      | Build_same_cnt:
          forall (cnt1: containsThread(Sem:=HybridSem hb1) st1 i)
            (cnt2: containsThread(Sem:=HybridSem hb2) st2 i),
            same_cnt i st1 st2 cnt1 cnt2.
      
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
          clean_cmpt.
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
            eapply MyConcurMatch.memcompat2 in Hcmpt2.
            
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
          clean_cmpt.
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
              clean_cnt.
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



      (** *Lemmas about map, map1, bounded_maps.strong_tree_leq *)
      Lemma map_map1:
        forall {A B} f m,
          @PTree.map1 A B f m = PTree.map (fun _=> f) m.
      Proof.
        intros. unfold PTree.map.
        remember 1%positive as p eqn:Heq.
        clear Heq; revert p.
        induction m; try reflexivity.
        intros; simpl; rewrite <- IHm1.
        destruct o; simpl; (*2 goals*)
          rewrite <- IHm2; auto.
      Qed.
      Lemma strong_tree_leq_xmap:
        forall {A B} f1 f2 t (leq: option B -> option A -> Prop),
          (forall a p, leq (Some (f1 p a)) (Some (f2 p a))) ->
          leq None None ->
          forall p,
            bounded_maps.strong_tree_leq
              (PTree.xmap f1 t p)
              (@PTree.xmap A A f2 t p)
              leq.
      Proof.
        intros; revert p.
        induction t0; simpl; auto.
        repeat split; eauto.
        - destruct o; auto.
      Qed.
      Lemma strong_tree_leq_map:
        forall {A B} f1 f2 t (leq: option B -> option A -> Prop),
          (forall a p, leq (Some (f1 p a)) (Some (f2 p a))) ->
          leq None None ->
          bounded_maps.strong_tree_leq
            (@PTree.map A B f1 t)
            (@PTree.map A A f2 t)
            leq.
      Proof. intros; eapply strong_tree_leq_xmap; eauto. Qed.

      Lemma strong_tree_leq_xmap':
        forall {A B} f1 f2 t (leq: option B -> option A -> Prop),
        forall p,
          (forall a p0,
              PTree.get p0 t = Some a ->
              leq (Some (f1 (PTree.prev_append p p0)%positive a))
                  (Some (f2 (PTree.prev_append p p0)%positive a))) ->
          leq None None ->
          bounded_maps.strong_tree_leq
            (@PTree.xmap A B f1 t p)
            (@PTree.xmap A A f2 t p)
            leq.
      Proof.
        intros. revert p H.
        induction t0. simpl; auto.
        intros.
        repeat split.
        - destruct o; auto.
          move H at bottom.
          assert ((PTree.Node t0_1 (Some a) t0_2) ! 1%positive = Some a)
            by reflexivity.
          eapply H in H1. auto.
        -  eapply IHt0_1.
           intros; specialize (H a (p0~0)%positive).
           eapply H; auto.
        -  eapply IHt0_2.
           intros; specialize (H a (p0~1)%positive).
           eapply H; auto.
      Qed.
      
      Lemma strong_tree_leq_map':
        forall {A B} f1 f2 t (leq: option B -> option A -> Prop),
          (forall a p0,
              PTree.get p0 t = Some a ->
              leq (Some (f1 (PTree.prev_append 1 p0)%positive a))
                  (Some (f2 (PTree.prev_append 1 p0)%positive a))) ->
          leq None None ->
          bounded_maps.strong_tree_leq
            (@PTree.map A B f1 t)
            (@PTree.map A A f2 t)
            leq.
      Proof. intros; eapply strong_tree_leq_xmap'; eauto. Qed.




      
      (** * Lemmas for relase diagram*)
      
      Lemma setPermBlock_inject_permMapLt':
        forall {Sem1 Sem2} (n:nat) (NZ: (0 < n)%nat) 
          (st1 : t(resources:=dryResources)(Sem:=Sem1)) (m1 : mem) (tid : nat) 
          (st2 : t(resources:=dryResources)(Sem:=Sem2)) (mu : meminj) (m2 : mem) (Htid1 : containsThread st1 tid)
          (b : block) ofs,
          permMapLt
            (setPermBlock (Some Writable) b (ofs) (snd (getThreadR Htid1)) n)
            (getMaxPerm m1) ->
          Mem.inject mu m1 m2 ->
          forall (b' : block) (delt : Z),
            mu b = Some (b', delt) ->
            forall Htid2 : containsThread st2 tid,
              permMapLt (snd (getThreadR Htid2)) (getMaxPerm m2) ->
              permMapLt
                (setPermBlock (Some Writable) b' (ofs + delt)
                              (snd (getThreadR Htid2)) n) (getMaxPerm m2).
      Proof.

        intros; intros b0 ofs0. 
        destruct (Clight_lemmas.block_eq_dec b' b0);
          [destruct (Intv.In_dec ofs0 ((ofs + delt)%Z, (ofs + delt + (Z.of_nat n))%Z))|
          ].
        - subst. unfold Intv.In in i; simpl in *.
          rewrite setPermBlock_same; auto.
          replace ofs0 with ((ofs0 - delt) + delt)%Z by omega.
          eapply juicy_mem.perm_order''_trans.

          + rewrite getMaxPerm_correct; unfold permission_at.
            eapply mem_lemmas.inject_permorder; eauto.

          + specialize (H b (ofs0 - delt)%Z).
            rewrite getMaxPerm_correct in H; unfold permission_at in H.
            rewrite setPermBlock_same in H.
            assumption.
            omega.
        - subst.
          rewrite setPermBlock_other_1; eauto.
          eapply Intv.range_notin in n0; auto; simpl.
          eapply inj_lt in NZ. rewrite Nat2Z.inj_0 in NZ.
          omega.
        - subst.
          rewrite setPermBlock_other_2; eauto.
      Qed.

      Lemma permMapLt_extensional1:
        forall p1 p2 p3,
          (forall b, p2 !! b = p3 !! b) -> 
          permMapLt p1 p2 ->
          permMapLt p1 p3.
      Proof. intros; intros ??. rewrite <- H. eapply H0. Qed.
      Lemma permMapLt_extensional2:
        forall p1 p2 p3,
          (forall b, p1 !! b = p2 !! b) -> 
          permMapLt p1 p3 ->
          permMapLt p2 p3.
      Proof. intros; intros ??. rewrite <- H. eapply H0. Qed.
      
      Lemma cat_app:
        forall {T} (l1 l2:list T),
          seq.cat l1 l2 = app l1 l2.
      Proof. intros. induction l1; eauto. Qed.

      (* MAPS! *)
      Lemma strong_tree_leq_spec:
        forall {A B} (leq: option A -> option B -> Prop),
          leq None None ->
          forall t1 t2,
            bounded_maps.strong_tree_leq t1 t2 leq ->
            forall b, leq (@PTree.get A b t1) 
                     (@PTree.get B b t2).
      Proof.
        intros A B leq Hleq t1.
        induction t1; eauto.
        - intros.
          destruct t2; try solve[inversion H].
          destruct b; simpl; auto.
        - intros t2 HH.
          destruct t2; try solve[inversion HH].
          destruct HH as (INEQ&L&R).
          destruct b; simpl; eauto.
      Qed.
      Lemma trivial_map1:
        forall {A} (t : PTree.t A),
          PTree.map1 (fun (a : A) => a) t = t.
      Proof.
        intros ? t; induction t; auto.
        simpl; f_equal; eauto.
        destruct o; reflexivity.
      Qed.
      Lemma trivial_map:
        forall {A} (t : PTree.t A),
          PTree.map (fun (_ : positive) (a : A) => a) t = t.
      Proof.
        intros; rewrite <- map_map1; eapply trivial_map1.
      Qed.

      Lemma inject_virtue_sub_map:
        forall (m1 m2 : mem)
               (mu : meminj)
               {A} (virtue1 : PTree.t (Z -> option A))
               perm1 perm2 Hlt1 Hlt2,
          Mem.inject mu (@restrPermMap perm1 m1 Hlt1 ) 
                     (@restrPermMap perm2 m2 Hlt2 ) ->
          bounded_maps.sub_map virtue1 (snd (getMaxPerm m1)) ->
          bounded_maps.sub_map (tree_map_inject_over_mem m2 mu virtue1)
                               (snd (getMaxPerm m2)).
      Proof.
        intros m1 m2 mu AT virtue1 perm1 perm2 Hlt1 Hlt2 injmem A.
        pose proof (Mem.mi_inj _ _ _ injmem) as injmem'.
        clear injmem.
        rename injmem' into injmem.
        
        replace  (snd (getMaxPerm m2)) with
            (PTree.map (fun _ a => a)  (snd (getMaxPerm m2)))
          by eapply trivial_map.
        unfold tree_map_inject_over_mem, tree_map_inject_over_tree.


        pose proof (@strong_tree_leq_map') as HHH.
        specialize (HHH _ (Z -> option AT)
                        (fun (b : positive) _ =>
                           build_function_for_a_block mu b (PTree.elements virtue1))
                        (fun (_ : positive) a => a)
                        (snd (getMaxPerm m2))
                        bounded_maps.fun_leq
                   ).
        unfold bounded_maps.sub_map.
        eapply HHH; eauto; try constructor.
        clear HHH.
        
        intros; simpl. intros p HH.
        
        pose proof (PTree.elements_complete virtue1).
        remember (PTree.elements virtue1) as Velmts.
        clear HeqVelmts.
        induction Velmts as [|[b0 fb]]; try solve[inversion HH].
        simpl in HH.
        destruct (mu b0) as [[b1 delt]|] eqn:Hinj.
        * unfold merge_func in HH.

          destruct (PMap.elt_eq p0 b1); subst.
          destruct (fb (p-delt)%Z) eqn:Hfbp.
          
          -- specialize (H0 b0 fb ltac:(left; auto)).
             clear HH.
             cbv beta zeta iota delta[fst] in A.
             pose proof (strong_tree_leq_spec
                           bounded_maps.fun_leq
                           ltac:(simpl; auto)
                                  virtue1 (snd (getMaxPerm m1)) A b0).
             rewrite H0 in H1.
             unfold bounded_maps.fun_leq in H1.
             destruct ((snd (getMaxPerm m1)) ! b0) eqn:Heqn;
               try solve[inversion H1].
             specialize (H1 (p - delt)%Z ltac:(rewrite Hfbp; auto)).
             eapply injmem in Hinj.

             2: {
               
               clear IHVelmts Velmts Hinj.
               clear Hfbp A a b1 H.

               instantiate (2:= Max).
               instantiate (2:= (p - delt)%Z).
               instantiate (1:= Nonempty).
               unfold Mem.perm.
               pose proof restrPermMap_Max as H3.
               unfold permission_at in H3.
               rewrite H3; clear H3.
               unfold PMap.get.
               rewrite Heqn.
               
               destruct (o (p - delt)%Z); try solve[inversion H1].
               destruct p; try constructor.
             }

             
             unfold Mem.perm in Hinj.
             pose proof restrPermMap_Max as H2.
             unfold permission_at in H2.
             rewrite H2 in Hinj.
             unfold PMap.get in Hinj.
             rewrite H in Hinj.
             replace (p - delt + delt)%Z with p in Hinj by omega.
             destruct (a p); inversion Hinj; auto.

          -- eapply IHVelmts in HH; auto.
             intros; eapply H0; right.
             auto.

          -- eapply IHVelmts in HH; auto.
             intros; eapply H0.
             right; auto.

        * (* mu b0 = None *)
          eapply IHVelmts in HH; auto.
          intros; eapply H0.
          right; auto.
      Qed.

      
      Lemma setPermBlock_extensionality:
        forall perm b ofs perm_map1 perm_map2 n,
          (0 < n)%nat ->
          (forall b0, perm_map1 !! b0 = perm_map2 !! b0) -> 
          forall b0, (setPermBlock perm b ofs perm_map1 n) !! b0=
                (setPermBlock perm b ofs perm_map2 n) !! b0.
      Proof.
        intros.
        extensionality ofs0.
        destruct_address_range b ofs b0 ofs0 n.
        - do 2 (rewrite setPermBlock_same; auto).
        - eapply Intv.range_notin in Hrange;
            try (simpl; omega).
          do 2 (erewrite setPermBlock_other_1; auto).
          rewrite (H0 b); auto.
        - do 2 (rewrite setPermBlock_other_2; auto).
          rewrite H0; auto.
      Qed.
      Lemma LKSIZE_nat_pos: (0 < LKSIZE_nat)%nat.
      Proof.
        replace 0%nat with (Z.to_nat 0)%Z by reflexivity.
        unfold LKSIZE_nat, LKSIZE.
        rewrite size_chunk_Mptr.
        destruct Archi.ptr64;
          eapply Z2Nat.inj_lt; eauto; try omega.
      Qed.
      Hint Resolve LKSIZE_nat_pos.

      (** * The following lemmas prove the injection 
                  of memories unfer setPermBlock.
       *)


      Lemma setPermBlock_mi_perm_Cur:
        forall (mu : meminj) (m1 m2 : mem) (b b' : block) (ofs delt : Z) 
          (n : nat),
          (0 < n)%nat ->
          forall (Hno_overlap:Mem.meminj_no_overlap mu m1)
            (Hlt1 : permMapLt (setPermBlock (Some Writable)
                                            b ofs (getCurPerm m1) n) (getMaxPerm m1))
            (Hlt2 : permMapLt (setPermBlock (Some Writable)
                                            b' (ofs + delt) (getCurPerm m2) n)
                              (getMaxPerm m2)),
            mu b = Some (b', delt) ->
            Mem.mem_inj mu m1 m2 ->
            forall (b1 b2 : block) (delta ofs0 : Z) (p : permission),
              mu b1 = Some (b2, delta) ->
              Mem.perm_order' ((getCurPerm (restrPermMap Hlt1)) !! b1 ofs0) p ->
              Mem.perm_order' ((getCurPerm (restrPermMap Hlt2)) !! b2 (ofs0 + delta)%Z) p.
      Proof.
        intros mu m1 m2 b b' ofs delt n Neq
               Hno_overlap Hlt1 Hlt2 H0 H1 b1 b2 delta ofs0 p H2 H3.
        
        rewrite getCur_restr in *.
        destruct_address_range b1 ofs b ofs0 n.
        - rewrite setPermBlock_same in H3; auto.
          rewrite H2 in H0; inversion H0; subst.
          rewrite setPermBlock_same; auto.
          unfold Intv.In in Hrange; simpl in Hrange.
          omega.
        - eapply Intv.range_notin in Hrange;
            try (simpl; omega).
          erewrite setPermBlock_other_1 in H3; auto.
          rewrite H2 in H0; inversion H0; subst.
          erewrite setPermBlock_other_1; auto.
          + rewrite getCurPerm_correct in *.
            eapply H1; eauto.
          + destruct Hrange; simpl in *; [left | right]; omega.
            
        - rewrite setPermBlock_other_2 in H3; auto.
          
          pose proof (Classical_Prop.classic
                        (Mem.perm_order'' (Some p) (Some Nonempty))) as [HH|HH].
          2: { destruct p; try solve[contradict HH; constructor]. }
          
          assert (HNoneempty:Mem.perm m1 b1 ofs0 Max Nonempty).
          { unfold Mem.perm. rewrite mem_lemmas.po_oo in *.
            eapply juicy_mem.perm_order''_trans; eauto.
            eapply juicy_mem.perm_order''_trans; eauto.
            rewrite getCurPerm_correct.
            eapply Mem.access_max. }

          assert (Hrange_no_overlap := Hneq).
          eapply setPermBLock_no_overlap in Hrange_no_overlap; eauto.
          
          destruct Hrange_no_overlap as [H | [H H']]; eauto.
          
          --  erewrite setPermBlock_other_2; auto.
              rewrite getCurPerm_correct.
              eapply H1; eauto.
              unfold Mem.perm. rewrite_getPerm; auto.
          -- subst; erewrite setPermBlock_other_1; auto.
             rewrite getCurPerm_correct.
             eapply H1; eauto.
             unfold Mem.perm. rewrite_getPerm; auto.
             eapply Intv.range_notin in H'; auto.
             simpl; omega.
      Qed.

      Definition inject_lock_simpl
                 size mu (b_lock:block) (ofs_lock: Z) (m1 m2:mem):=
        forall b_lock' delt,
          mu b_lock = Some (b_lock', delt) -> 
          ( forall ofs0,
              Intv.In ofs0 (ofs_lock, (ofs_lock + size)%Z) ->
              memval_inject mu
                            (ZMap.get ofs0 (Mem.mem_contents m1) !! b_lock)
                            (ZMap.get (ofs0 + delt)%Z
                                      (Mem.mem_contents m2) !! b_lock')).
      Lemma inject_lock_simplification:
        forall n mu b_lock ofs_lock m1 m2,
          inject_lock' n mu b_lock ofs_lock m1 m2 ->
          inject_lock_simpl n mu b_lock ofs_lock m1 m2.
      Proof. intros. destruct H as (? &? &?&HH).
             unfold inject_lock_simpl; intros.
             rewrite H in H0; inversion H0; subst.
             eauto.
      Qed.
      Lemma setPermBlock_mem_inj:
        forall mu m1 m2 b b' ofs delt n,
          (0 < n)%nat ->
          forall (Hinject_lock: inject_lock' (Z.of_nat n) mu b ofs m1 m2)
            (Hno_overlap:Mem.meminj_no_overlap mu m1)
            (Hlt1: permMapLt
                     (setPermBlock (Some Writable) b ofs
                                   (getCurPerm m1)
                                   n) (getMaxPerm m1))
            
            (Hlt2: permMapLt
                     (setPermBlock (Some Writable) b' (ofs + delt)
                                   (getCurPerm m2)
                                   n) (getMaxPerm m2)),
            mu b = Some (b', delt) ->
            Mem.mem_inj mu m1 m2 ->
            Mem.mem_inj mu (restrPermMap Hlt1) (restrPermMap Hlt2).
      Proof.
        intros; econstructor.
        - unfold Mem.perm; intros.
          destruct k.
          + repeat rewrite_getPerm.
            rewrite getMax_restr in *.
            rewrite getMaxPerm_correct in *.
            eapply H1; eauto.
          + repeat rewrite_getPerm.
            eapply setPermBlock_mi_perm_Cur; eauto.
        - intros.
          eapply H1; eauto.
          unfold Mem.range_perm, Mem.perm in *.
          intros.
          specialize (H3 _ H4).
          repeat rewrite_getPerm.
          rewrite getMax_restr in H3; eauto.
        - intros; simpl.
          unfold Mem.perm in *. 
          repeat rewrite_getPerm.
          rewrite getCur_restr in H3.
          destruct_address_range b ofs b1 ofs0 n.

          + eapply inject_lock_simplification; eauto.

          + eapply H1; auto.
            rewrite setPermBlock_other_1 in H3; auto.
            unfold Mem.perm; rewrite_getPerm; auto.
            eapply Intv.range_notin in Hrange; simpl; auto.
            omega.
            
          + eapply H1; auto.
            rewrite setPermBlock_other_2 in H3; auto.
            unfold Mem.perm; rewrite_getPerm; auto.
      Qed.

      (* Last case for Mem.inject,
                       using setPermBlock with Cur
                       Helper lemma for setPermBlock_mem_inject
       *)
      Lemma setPermBlock_mi_perm_inv_Cur:
        forall b1 b1' ofs delt1 m1 m2 n mu,
          (0 < n)%nat -> 
          forall (Hlt1: permMapLt
                     (setPermBlock (Some Writable)
                                   b1 ofs (getCurPerm m1) n)
                     (getMaxPerm m1))
            (Hlt2: permMapLt
                     (setPermBlock (Some Writable)
                                   b1' (ofs + delt1) (getCurPerm m2) n)
                     (getMaxPerm m2))
            (Hinject:Mem.inject mu m1 m2)
          ,                           mu b1 = Some (b1', delt1) -> 
                                      forall b2 b2' ofs0 delt2 p,
                                        let m1_restr := (restrPermMap Hlt1) in
                                        let m2_restr := (restrPermMap Hlt2) in
                                        mu b2 = Some (b2', delt2) ->
                                        Mem.perm m2_restr b2' (ofs0 + delt2) Cur p ->
                                        Mem.perm m1_restr b2 ofs0 Cur p \/
                                        ~ Mem.perm m1_restr b2 ofs0 Max Nonempty.
      Proof.
        intros.
        unfold Mem.perm in *.
        repeat rewrite_getPerm.
        subst m1_restr m2_restr; rewrite getCur_restr in *.
        rewrite getMax_restr.
        (* try to do it backwards: destruct source blocks first*)
        destruct_address_range
          b1 (ofs)%Z b2 (ofs0)%Z n.
        - rewrite H0 in H1; inversion H1; subst.
          rewrite setPermBlock_same.
          2: { unfold Intv.In in *; auto. }
          rewrite setPermBlock_same in H2.
          2: { unfold Intv.In in *; simpl in *; omega. } 
          auto.
        - rewrite H0 in H1; inversion H1; subst.
          rewrite setPermBlock_other_1.
          2: { eapply Intv.range_notin in Hrange; eauto.
               simpl; omega. }
          rewrite setPermBlock_other_1 in H2.
          2: { eapply Intv.range_notin in Hrange; eauto;
               simpl in *; omega. }
          rewrite getCurPerm_correct, getMaxPerm_correct in *.
          eapply Hinject; eauto.
        - pose proof (Classical_Prop.classic
                        (Mem.perm_order' ((getMaxPerm m1) !! b2 ofs0) Nonempty))
            as [HH|HH]; try eauto.
          rewrite setPermBlock_other_2; eauto.
          rewrite getCurPerm_correct, getMaxPerm_correct in *.
          eapply Hinject; eauto.
          unfold Mem.perm in *; rewrite_getPerm.
          
          (* now destruct the addresses for the target blocks*)
          destruct_address_range
            b1' (ofs+delt1)%Z b2' (ofs0 + delt2)%Z n.
          + exploit (@range_no_overlap mu m1 b2 b1' b1 b1');
              try apply Hneq; eauto.
            * eapply Hinject.
            * eapply setPermBlock_range_perm in Hlt1.
              eapply range_perm_trans; eauto.
              constructor.
            * intros [?|[? ?]].
              -- contradict H3; auto.
              -- contradict H4; eassumption.
          + rewrite setPermBlock_other_1 in H2; eauto.
            eapply Intv.range_notin in Hrange; simpl in *; omega.
          + rewrite setPermBlock_other_2 in H2; eauto.
      Qed.
      
      Lemma setPermBlock_mem_inject:
        forall mu m1 m2 b b' ofs delt LKSIZE_nat,
          (0 < LKSIZE_nat)%nat ->
          forall (Hinject_lock: inject_lock' (Z.of_nat LKSIZE_nat) mu b ofs m1 m2)
            (Hlt1: permMapLt
                     (setPermBlock (Some Writable) b ofs
                                   (getCurPerm m1)
                                   LKSIZE_nat) (getMaxPerm m1))
            
            (Hlt2: permMapLt
                     (setPermBlock (Some Writable) b' (ofs + delt)
                                   (getCurPerm m2)
                                   LKSIZE_nat) (getMaxPerm m2)),
            mu b = Some (b', delt) ->
            Mem.inject mu m1 m2 ->
            Mem.inject mu (restrPermMap Hlt1) (restrPermMap Hlt2).
      Proof.
        intros.
        intros; econstructor.
        - eapply setPermBlock_mem_inj; auto; eapply H1.
        - intros ?; rewrite restrPermMap_valid.
          eapply H1. 
        - intros. apply restrPermMap_valid.
          eapply H1; eauto.
        - pose proof (restr_Max_equiv Hlt1).
          eapply Proper_no_overlap_max_equiv; eauto.
          eapply H1.
        - intros ????? ?. 
          eapply H1; eauto.
          pose proof (restr_Max_equiv Hlt1) as HH.
          destruct H3 as [H3|H3];
            eapply (Proper_perm_max) in H3;
            try (symmetry; apply restr_Max_equiv);
            try eassumption;
            try solve[econstructor];
            auto.
        - intros.
          pose proof (restr_Max_equiv Hlt1) as HH1.
          pose proof (restr_Max_equiv Hlt2) as HH2.
          destruct k.
          + eapply (Proper_perm_max) in H3;
              try (symmetry; apply restr_Max_equiv);
              try eassumption;
              eauto.
            eapply H1 in H3; eauto.
            destruct H3 as [H3|H3].
            * left; eapply Proper_perm_max;
                try eassumption;
                try solve[econstructor];
                auto.
            * right; intros ?; apply H3.
              eapply (Proper_perm_max) in H4;
                try eassumption; eauto.
              symmetry; apply restr_Max_equiv.
          + eapply setPermBlock_mi_perm_inv_Cur; eauto.
      Qed.

      

      Definition mi_perm_perm (f:meminj) perm1 perm2:=
        forall (b1 b2 : block) (delta ofs : Z)(p : permission),
          f b1 = Some (b2, delta) ->
          Mem.perm_order' (perm1 !! b1 ofs) p ->
          Mem.perm_order' (perm2 !! b2 (ofs + delta)) p.
      Instance proper_mi_perm_perm:
        Proper (Logic.eq ==> access_map_equiv ==> access_map_equiv ==> iff)
               mi_perm_perm.
      Proof.
        unfold mi_perm_perm.
        setoid_help.proper_iff;
          setoid_help.proper_intros; subst.
        rewrite <- H1. eapply H2; eauto.
        rewrite H0; eassumption.
      Qed.
      Definition mi_memval_perm (f:meminj) (perm1:access_map) cont1 cont2:=
        forall b1 b2 delta ofs,
          f b1 = Some (b2, delta) ->
          Mem.perm_order' (perm1 !! b1 ofs) Readable ->
          memval_inject f (ZMap.get ofs cont1 !! b1)
                        (ZMap.get (ofs + delta) cont2 !! b2).
      Instance proper_mi_memval_perm:
        Proper (Logic.eq ==> access_map_equiv ==>
                         Logic.eq ==> Logic.eq ==> iff)
               mi_memval_perm.
      Proof.
        unfold mi_memval_perm.
        setoid_help.proper_iff;
          setoid_help.proper_intros; subst.
        eapply H3; auto.
        rewrite H0; assumption.
      Qed.
      
      Lemma mem_inj_restr:
        forall mu m1 m2 perm1 perm2,
        forall (Hlt1: permMapLt perm1 (getMaxPerm m1))
          (Hlt2: permMapLt perm2 (getMaxPerm m2)),
          mi_perm_perm mu perm1 perm2 ->
          mi_memval_perm mu perm1 (Mem.mem_contents m1) (Mem.mem_contents m2) ->
          Mem.mem_inj mu m1 m2 ->
          Mem.mem_inj mu (restrPermMap Hlt1) (restrPermMap Hlt2).
      Proof.
        intros * Hmi_perm Hmi_align H; econstructor.
        - unfold Mem.perm; intros.
          destruct k; repeat rewrite_getPerm.
          + (* Max *)
            rewrite getMax_restr in *.
            eapply H with (k:=Max) in H0;
              unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
          + rewrite getCur_restr in *.
            eapply Hmi_perm; eassumption.
        - intros * ?. 
          rewrite restr_Max_equiv.
          eapply H; eassumption.
        - intros *; simpl.
          unfold Mem.perm.
          rewrite_getPerm.
          rewrite getCur_restr.
          apply Hmi_align.
      Qed.
      
      Definition mi_perm_inv_perm f perm1 perm2 m1:=
        forall (b1 : block) (ofs : Z) (b2 : block) 
               (delta : Z) (p : permission),
          f b1 = Some (b2, delta) ->
          Mem.perm_order' (perm2 !! b2 (ofs + delta)) p ->
          Mem.perm_order' (perm1 !! b1 ofs) p
          \/ ~ Mem.perm m1 b1 ofs Max Nonempty.
      
      Instance proper_mi_perm_inv_perm:
        Proper (Logic.eq ==> access_map_equiv ==> access_map_equiv ==>
                         Max_equiv ==> iff) mi_perm_inv_perm.
      Proof.
        unfold mi_perm_inv_perm.
        setoid_help.proper_iff;
          setoid_help.proper_intros; subst.
        rewrite <- H0, <- H2.
        eapply H3; eauto.
        rewrite H1; assumption.
      Qed.
      Lemma inject_restr:
        forall mu m1 m2 perm1 perm2,
        forall (Hlt1: permMapLt perm1 (getMaxPerm m1))
          (Hlt2: permMapLt perm2 (getMaxPerm m2)),
          mi_perm_perm mu perm1 perm2 ->
          mi_memval_perm mu perm1 (Mem.mem_contents m1) (Mem.mem_contents m2) ->
          mi_perm_inv_perm mu perm1 perm2 m1 ->
          Mem.inject mu m1 m2 ->
          Mem.inject mu (restrPermMap Hlt1) (restrPermMap Hlt2).
      Proof.
        intros * Hmi_perm Hmi_align Hmi_perm_inv; econstructor.
        - apply mem_inj_restr; try assumption. apply H.
        - intros ? Hnot_valid; apply H.
          eauto using restrPermMap_valid.
        - intros.
          eapply restrPermMap_valid. eapply H. eassumption.
        - rewrite restr_Max_equiv. apply H.
        - intros. rewrite restr_Max_equiv in H1.
          eapply H; eauto.
        - intros until delta.
          intros [] *.
          + repeat rewrite restr_Max_equiv.
            eapply H; eauto.
          + unfold Mem.perm; repeat rewrite_getPerm.
            repeat rewrite getCur_restr;
              rewrite getMax_restr.
            rewrite getMaxPerm_correct.
            eapply Hmi_perm_inv.
      Qed.
      
      Lemma setPermBlock_mem_inject_lock:
        forall mu m1 m2 b b' ofs delt LKSIZE_nat,
          (0 < LKSIZE_nat)%nat ->
          forall (Hinject_lock: inject_lock' (Z.of_nat LKSIZE_nat) mu b ofs m1 m2)
            (Hlt1: permMapLt
                     (setPermBlock (Some Writable) b ofs
                                   (getCurPerm m1)
                                   LKSIZE_nat) (getMaxPerm m1))
            
            (Hlt2: permMapLt
                     (setPermBlock (Some Writable) b' (ofs + delt)
                                   (getCurPerm m2)
                                   LKSIZE_nat) (getMaxPerm m2)),
            mu b = Some (b', delt) ->
            Mem.inject mu m1 m2 ->
            Mem.inject mu (restrPermMap Hlt1) (restrPermMap Hlt2).
      Proof.
        intros; econstructor.
        - eapply setPermBlock_mem_inj; auto;
            eapply H1.
        - intros ?.
          rewrite restrPermMap_valid.
          eapply H1. 
        - intros. apply restrPermMap_valid.
          eapply H1; eauto.
        - 
          
          pose proof (restr_Max_equiv Hlt1).
          eapply Proper_no_overlap_max_equiv; eauto.
          eapply H1.
        - intros ?????.
          

          intros ?.
          eapply H1; eauto.

          pose proof (restr_Max_equiv Hlt1) as HH.
          destruct H3 as [H3|H3];
            eapply (Proper_perm_max) in H3;
            try (symmetry; apply restr_Max_equiv);
            try eassumption;
            try solve[econstructor];
            auto.

        - intros.
          pose proof (restr_Max_equiv Hlt1) as HH1.
          pose proof (restr_Max_equiv Hlt2) as HH2.
          destruct k.
          + eapply (Proper_perm_max) in H3;
              try (symmetry; apply restr_Max_equiv);
              try eassumption;
              eauto.
            eapply H1 in H3; eauto.
            destruct H3 as [H3|H3].
            * left; eapply Proper_perm_max;
                try eassumption;
                try solve[econstructor];
                auto.
            * right; intros ?; apply H3.
              eapply (Proper_perm_max) in H4;
                try eassumption; eauto.
              symmetry; apply restr_Max_equiv.
          + eapply setPermBlock_mi_perm_inv_Cur; eauto.
      Qed.
      
      Definition perm_meminj_no_overlap {A} (f:meminj) (perm: PMap.t (Z -> option A)):=
        forall (b1 b1' : block) (delta1 : Z) (b2 b2' : block) (delta2 ofs1 ofs2 : Z),
          b1 <> b2 ->
          f b1 = Some (b1', delta1) ->
          f b2 = Some (b2', delta2) ->
          at_least_Some (perm !! b1 ofs1) ->
          at_least_Some  (perm !! b2 ofs2) ->
          b1' <> b2' \/ ofs1 + delta1 <> ofs2 + delta2.
      
      (* Move to Self_simulation*)
      Lemma at_least_perm_order:
        forall x, at_least_Some x <-> Mem.perm_order' x Nonempty.
      Proof.
        intros; unfold at_least_Some, Mem.perm_order'.
        destruct x; split; simpl; auto.
        intros; apply perm_any_N.
      Qed.
      Lemma no_overlap_mem_perm:
        forall mu m1, 
          Mem.meminj_no_overlap mu m1 ->
          perm_meminj_no_overlap mu (getMaxPerm m1).
      Proof.
        intros * H ? **; eapply H; eauto;
          unfold Mem.perm; rewrite_getPerm;
            apply  at_least_perm_order; assumption.
      Qed.
      Definition perm_meminj_no_overlap_range (f:meminj) (perm: access_map):=
        forall (b1 b1' : block) (delta1 : Z) (b2 b2' : block) (delta2 ofs1 ofs2 SZ : Z),
          0 < SZ ->
          b1 <> b2 ->
          f b1 = Some (b1', delta1) ->
          f b2 = Some (b2', delta2) ->
          Mem.perm_order' (perm !! b1 ofs1) Nonempty ->
          (forall ofs2', 0 <= ofs2' < SZ ->
                    Mem.perm_order' (perm !! b2 (ofs2 + ofs2')) Nonempty) ->
          b1' <> b2' \/ ~ Intv.In (ofs1 + delta1) (ofs2 + delta2, ofs2 + delta2 + SZ).

      Lemma perm_no_over_point_to_range:
        forall f p,
          perm_meminj_no_overlap f p ->
          perm_meminj_no_overlap_range f p.
      Proof.
        intros ** ? **.
        destruct (Clight_lemmas.block_eq_dec b1' b2');
          auto; (* solevs the case b1' <> b2' *) subst.
        remember ((ofs1 + delta1)-(ofs2 + delta2)) as ofs2'.
        right; intros [LEFT RIGHT]; simpl in *.
        exploit (H5 (ofs2')).
        { subst; omega. }
        intros Hperm.
        exploit H; eauto; try apply at_least_perm_order; eauto.
        intros [? | Hcontra]; try congruence.
        apply Hcontra. subst.
        omega.
      Qed.
      
      
      Lemma set_perm_block_mi_perm_perm:
        forall (mu:meminj) b ofs p p_max perm1 perm2 LS b' delt
          (HLSpos: 0 < Z.of_nat LS),
          perm_meminj_no_overlap mu p_max ->
          mu b = Some (b', delt) ->
          permMapLt perm1 p_max ->
          (forall ofs2' : Z,
              0 <= ofs2' < Z.of_nat LS ->
              Mem.perm_order' (p_max !! b (ofs + ofs2')) Nonempty) ->
          mi_perm_perm mu perm1 perm2 ->
          mi_perm_perm mu
                       (setPermBlock p b ofs perm1 LS)
                       (setPermBlock p b' (ofs + delt) perm2 LS).
      Proof.
        intros ** ? * Hinj.
        pose proof (H2 0 ltac:(omega)).
        unfold Mem.perm_order'.
        destruct_address_range b ofs b1 ofs0 LS.
        - unify_injection.
          repeat rewrite (@setPermBlock_same); auto.
          unfold Intv.In in *; simpl in *; omega.
        - unify_injection.
          repeat rewrite (@setPermBlock_other_1).
          apply H3; auto.
          eapply Intv.range_notin in Hrange; simpl in *; omega.
          eapply Intv.range_notin in Hrange; simpl in *; omega.
        - rewrite (@setPermBlock_other_2); auto.
          destruct (Clight_lemmas.block_eq_dec b' b2); try subst.  
          2: { rewrite (@setPermBlock_other_2); auto.
               eapply H3; auto . }
          + match_case; try solve[intros HH; inv HH].
            exploit H; eauto; try apply at_least_perm_order; eauto.
            eapply perm_order_trans211; eauto.
            rewrite Heqo; constructor.
            
            intros [?| ?].
            * congruence.
            * rewrite (@setPermBlock_other_1).
              intros. eapply H3; eauto.
              rewrite Heqo; auto.
              eapply (Intv.range_notin _ (ofs + delt, ofs + delt + _ )).
              2: simpl; omega.
              apply not_eq_sym in Hneq.
              exploit perm_no_over_point_to_range; eauto.
              eapply perm_order_trans211; eauto.
              rewrite Heqo; constructor.
              intros [?|?]; auto.
      Qed.

      Lemma inject_mi_perm_inv_perm_Max:
        forall f m1 m2,
          Mem.inject f m1 m2 ->
          mi_perm_inv_perm f (getMaxPerm m1)
                           (getMaxPerm m2) m1.
      Proof.
        intros ** ? **.
        eapply Mem.mi_perm_inv with (k:=Max) in H; eauto;
          unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
      Qed.
      Lemma inject_mi_perm_inv_perm_Cur:
        forall f m1 m2,
          Mem.inject f m1 m2 ->
          mi_perm_inv_perm f (getCurPerm m1)
                           (getCurPerm m2) m1.
      Proof.
        intros ** ? **.
        eapply Mem.mi_perm_inv with (k:=Cur) in H; eauto;
          unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
      Qed.
      Lemma mi_inj_mi_memval_perm:
        forall f m1 m2,
          Mem.mem_inj f m1 m2 ->
          mi_memval_perm f (getCurPerm m1)
                         (Mem.mem_contents m1) (Mem.mem_contents m2).
      Proof.
        intros ** ? **.
        eapply Mem.mi_memval in H; eauto;
          unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
      Qed.
      Lemma mi_inj_mi_perm_perm_Max:
        forall f m1 m2,
          Mem.mem_inj f m1 m2 ->
          mi_perm_perm f (getMaxPerm m1) (getMaxPerm m2).
      Proof.
        intros ** ? **.
        eapply Mem.mi_perm with(k:=Max) in H; eauto;
          unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
      Qed.
      Lemma mi_inj_mi_perm_perm_Cur:
        forall f m1 m2,
          Mem.mem_inj f m1 m2 ->
          mi_perm_perm f (getCurPerm m1) (getCurPerm m2).
      Proof.
        intros ** ? **.
        eapply Mem.mi_perm with(k:=Cur) in H; eauto;
          unfold Mem.perm in *; repeat rewrite_getPerm; eauto.
      Qed.
      
      Record virtue:=
        { virtueThread:
            PTree.t (Z -> option (option permission)) *
            PTree.t (Z -> option (option permission));
          virtueLP: access_map * access_map }.
      Definition inject_virtue (m: mem) (mu: meminj) (angel:virtue):=
        Build_virtue
          (virtueThread_inject m mu (virtueThread angel))
          (virtueLP_inject m mu (virtueLP angel)).
      Definition build_release_event addr dmap m:=
        Events.release addr (Some (build_delta_content dmap m)).
      Definition build_acquire_event addr dmap m:=
        Events.acquire addr (Some (build_delta_content dmap m)).

      Definition pair21 {A B C} (f: A -> B -> C) (aa:Pair A) (b: B): Pair C :=
        pair1 (fun a => f a b) aa.
      Hint Unfold pair21: pair.
      Definition pair21_prop {A B} (f: A -> B -> Prop) (aa:Pair A) (b: B):Prop :=
        pair1_prop (fun a => f a b) aa.
      Hint Unfold pair21_prop: pair.
      Definition permMapLt_pair1:= pair21_prop permMapLt.
      Hint Unfold permMapLt_pair1: pair.
      
      (*Take just the tree*)
      Definition sub_map' {A A' B} (a:A'* _) b:=
        @bounded_maps.sub_map A B (snd a) b. 
      Record sub_map_virtue (v:virtue)(m:access_map):=
        { virtueThread_sub_map:
            pair21_prop bounded_maps.sub_map (virtueThread v) (snd m);
          virtueLP_sub_map:
            bounded_maps.map_empty_def (fst (virtueLP v)) /\
            bounded_maps.map_empty_def (snd (virtueLP v)) /\
            pair21_prop sub_map' (virtueLP v) (snd m)
        }.

      Definition sub_map_pair {A B} :=
        (pair21_prop (@bounded_maps.sub_map A B)).
      
      (*  *)
      Definition writable_lock b ofs perm1 m1:=
        permMapLt (setPermBlock (Some Writable) b ofs perm1 LKSIZE_nat) (getMaxPerm m1).
      
      Lemma writable_lock_inject:
        forall b1 ofs cperm1 cperm2 m1 m2 f  b2 delt LKS,  
          (0 < LKS)%nat ->
          writable_lock b1 ofs cperm1 m1 ->
          Mem.inject f m1 m2 ->
          f b1 = Some (b2, delt) ->
          permMapLt cperm2 (getMaxPerm m2) ->
          writable_lock b2 (ofs + delt)%Z cperm2 m2.
      Proof.
        intros.
        eapply setPermBlock_inject_permMapLt; simpl in *; eauto.
        apply access_map_injected_getMaxPerm; auto.
      Qed.
      Instance writable_lock_proper:
        Proper (Logic.eq ==> Logic.eq ==> access_map_equiv ==> Max_equiv ==> iff) writable_lock.
      Proof.
        setoid_help.proper_iff;
          setoid_help.proper_intros; subst.
        unfold writable_lock in *.
        unfold Max_equiv in *.
        rewrite <- H2, <- H1; auto.
      Qed.
      Lemma writable_lock_inject_restr:
        forall b1 ofs cperm1 cperm2 m1 m2 f  b2 delt LKS,  
          (0 < LKS)%nat ->
          writable_lock b1 ofs cperm1 m1 ->
          forall p1 p2 Hlt1 Hlt2,
            Mem.inject f (@restrPermMap p1 m1 Hlt1) (@restrPermMap p2 m2 Hlt2) ->
            f b1 = Some (b2, delt) ->
            permMapLt cperm2 (getMaxPerm m2) ->
            writable_lock b2 (ofs + delt)%Z cperm2 m2.
      Proof.
        intros.
        erewrite <- restr_Max_equiv.
        erewrite <- restr_Max_equiv in H0.
        eapply writable_lock_inject; eauto.
        rewrite getMax_restr; auto.
      Qed.
      Lemma writable_lock_perm:
        forall b ofs perm m,
          writable_lock b ofs perm m ->
          forall ofs2,
            0 <= ofs2 < LKSIZE ->
            Mem.perm m b (ofs+ofs2) Max Writable.
      Proof.
        unfold writable_lock, Mem.perm; intros.
        specialize (H b (ofs+ofs2)).
        rewrite_getPerm.
        eapply perm_order_trans211; eauto.
        rewrite setPermBlock_same; try solve [constructor].
        unfold LKSIZE_nat; rewrite Z2Nat.id;
          omega.
      Qed.
      Definition thread_mems {Sem st i m}
                 {cnt:containsThread(resources:=dryResources)(Sem:=Sem) st i}
                 (th_compat: thread_compat _ _ cnt m):=
        (restrPermMap (th_comp th_compat),restrPermMap (lock_comp th_compat)).
      Definition permMapJoin_pair:= pair3_prop permMapJoin.
      Hint Unfold permMapJoin_pair: pair.
      
      Definition is_empty_map (am:access_map):=
        forall b ofs, am !! b ofs = None.
      Definition empty_doublemap:=
        pair1_prop is_empty_map.
      Hint Unfold empty_doublemap: pair.


      Lemma is_empty_map_is_canon:
        forall perms,
          is_empty_map perms ->
          isCanonical perms.
      Proof.
        unfold is_empty_map, isCanonical; destruct perms as (deflt, perms).
        induction perms.
        - simpl. intros H; specialize (H 1%positive).
          extensionality ofs.
          unfold PMap.get in *; eauto.
        - simpl in *.
          intros. eapply IHperms1.
          intros.
          specialize (H (xO b) ofs). simpl in *.
          unfold PMap.get in *.
          simpl in *; auto.
      Qed.
      
      Lemma inject_is_empty_map:
        forall  m mu empty_perms
                (Hempty_map : is_empty_map empty_perms),
          is_empty_map (inject_access_map m mu empty_perms).
      Proof.
        intros ** b ofs.
        unfold inject_access_map,
        tree_map_inject_over_mem,
        tree_map_inject_over_tree.
        unfold PMap.get; simpl.
        rewrite PTree.gmap, PTree.gmap1.
        destruct ((snd (Mem.mem_access m)) ! b); simpl; auto.
        - 
          unfold build_function_for_a_block,merge_func.
          remember (PTree.elements (snd empty_perms)) as elemts eqn:HH.
          assert (forall b1 f, In (b1, f) elemts -> forall ofs, f ofs = None).
          { intros * Hin ofs0. subst; eapply PTree.elements_complete in Hin.
            specialize (Hempty_map b1 ofs0).
            unfold PMap.get in *; match_case in Hempty_map.  }
          clear Hempty_map HH. revert H.
          induction elemts.
          + simpl; auto.
          + simpl.
            intros.
            repeat match_case; subst; auto.
            * specialize (H p o0 ltac:(auto) ).
              rewrite H in Heqo0; try congruence.
            * eapply IHelemts. intros. eapply H; eauto.
            * eapply IHelemts. intros. eapply H; eauto.
            * eapply IHelemts. intros. eapply H; eauto.
      Qed.
      
      Lemma inject_empty_maps:
        forall  m mu empty_perms
           (Hempty_map : empty_doublemap empty_perms),
          empty_doublemap (virtueLP_inject m mu empty_perms).
      Proof. intros ??. solve_pair.
             eapply inject_is_empty_map.
      Qed.
      
      Lemma empty_map_useful:
        (* Transforms empty_doublemap into the 
               form used by step *)
        forall am, empty_doublemap am <->
              forall b ofs, (fst am) !! b ofs = None /\ (snd am) !! b ofs = None.
      Proof. split; intros HH; split; try intros ??; eapply HH. Qed.
      
      Inductive coerce_state_type  {a b T}: forall t, @state_sum a b -> t -> T -> T -> T ->  Prop:=
      | SourceCoerce_T: forall t1 t2 c, coerce_state_type a (@SState _ _ c) c t1 t2 t1
      | TargetCoerce_T: forall t1 t2 c, coerce_state_type b (@TState _ _ c) c t1 t2 t2.
      Definition mach_state n:= ThreadPool (Some n).

      Lemma atx_injection Sem: 
        let CoreSem := sem_coresem Sem in
        forall (SelfSim: (self_simulation semC CoreSem))
          mu b1 b2 delt th_state1 th_state2 m1 m2 FUN ofs,
          mu b1 = Some (b2, delt) ->
          match_self (code_inject semC CoreSem SelfSim) mu th_state1 m1 th_state2 m2 ->
          semantics.at_external CoreSem th_state1 m1 =
          Some (FUN, (Vptr b1 ofs) :: nil) ->
          semantics.at_external CoreSem th_state2 m2 =
          Some (FUN, Vptr b2 (add ofs (repr delt)) :: nil).
      Proof.
        intros * Hinj Hmatch_self Hat_external.
        eapply ssim_preserves_atx in Hat_external as
            (args' & Hatx2 & Hval_inj); eauto.
        - (* unify arg's *)
          inv Hval_inj. inv H3. inv H1.
          rewrite Hinj in H2; inv H2.
          eauto.
      Qed.
      Lemma coerse_state_atx:
        forall shb Sem SemC sum_state (th_state:@semC Sem) m,
          coerce_state_type
            semC sum_state th_state
            (CSem, Clight.state)
            (AsmSem, Asm.state) (Sem, SemC) ->
          semantics.at_external (sem_coresem Sem) th_state m =
          semantics.at_external (sem_coresem (HybridSem shb)) sum_state m.
      Proof.
        intros * Hcoerce. inv Hcoerce; simpl.
        all: replace th_state with c; try reflexivity.
        all: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
      Qed.
      Definition no_overlap_perms' (mu:meminj) (p p': access_map):=
        forall b1 b1' b2 delt delt',
          mu b1 = Some(b2, delt) ->
          mu b1' = Some(b2, delt') ->
          forall ofs ofs',
            at_least_Some (p !! b1 ofs) ->
            at_least_Some (p' !! b1' ofs') ->
            ofs + delt = ofs' + delt' ->
            b1 = b1'.
      Definition no_overlap_perms (mu:meminj) (p p': access_map):=
        forall b1 b1' b2 delt delt',
          mu b1 = Some(b2, delt) ->
          mu b1' = Some(b2, delt') ->
          forall ofs ofs',
            at_least_Some (p !! b1 ofs) ->
            at_least_Some (p' !! b1' ofs') ->
            ofs + delt = ofs' + delt' ->
            b1 = b1' /\ ofs = ofs' /\ delt = delt' .
      
      Lemma no_overlap_perms_iff:
        forall mu p1 p2,
          no_overlap_perms' mu p1 p2 <-> no_overlap_perms mu p1 p2.
      Proof.
        intros; unfold no_overlap_perms, no_overlap_perms';
          split; intros HH b1 b1' **; exploit (HH b1 b1');
            eauto; intros HH'; destruct_and; eauto.
        - !goal (_/\_/\_).
          subst. rewrite H in H0; inversion H0; subst.
          reduce_and; auto; omega.
      Qed.
      (* Use no_overlap_perms when possible*)
      Definition perm_image_full (f:meminj) (a1 a2: access_map): Prop:=
        forall b1 ofs, at_least_Some (a1 !! b1 ofs) ->
                  (* Mem.perm_order' (a1 !! b1 ofs) (Nonempty) -> *)
                  exists b2 delta,
                    f b1 = Some (b2, delta) /\
                    a1 !! b1 ofs = a2 !! b2 (ofs + delta).
      Definition perfect_image (f:meminj) (a1 a2: access_map): Prop:=
        forall b1 b2 delt,
          f b1 = Some (b2, delt) ->
          forall ofs, a1 !! b1 ofs = a2 !! b2 (ofs + delt).
      (* TODO: change the names 
             perm_image_full -> perm_inj
             perm_preimage -> perm_surj
             pimage -> pimage  
             p_image -> prem_inj
             ppre_perfect_image -> prem_surj
       *)
      
      Record perm_perfect_image mu a1 a2:=
        { (* pimage: perfect_image mu a1 a2; *) (* Too strong*)
          p_image: perm_image_full mu a1 a2;
          ppre_perfect_image: perm_preimage mu a1 a2}.
      Arguments pimage {_ _ _}.
      Arguments p_image {_ _ _}.
      Arguments ppre_perfect_image {_ _ _}.

      Local Ltac exploit_p_image H:=
        let b:=fresh "b" in
        let delt:=fresh "delt" in
        let Hinj:=fresh "Hinj" in
        destruct
          (p_image H _ _ ltac:(eapply at_least_Some_trivial; eauto))
          as (b&delt&Hinj&?); subst.
      Local Ltac exploit_ppre_image H:=
        let b:=fresh "b" in
        let ofs:=fresh "ofs" in
        let delt:=fresh "delt" in
        let Hinj:=fresh "Hinj" in
        destruct
          (ppre_perfect_image H _ _ ltac:(eapply at_least_Some_trivial; eauto))
          as (b&ofs&delt&Hinj&?&?); subst.
      Local Ltac exploit_perfect_image H:=
        first [exploit_p_image H | exploit_ppre_image H]. (*
            progress (try (exploit_p_image H); try (exploit_ppre_image H)). *) 
      Local Ltac exploit_no_overlap_perm H:=
        (* TODO: remove coqlib*)
        ( Coqlib.exploit H;
          try (eapply at_least_Some_trivial; eauto);
          eauto;
          intros ?; destruct_and; subst
        ).
      
      
      Local Ltac unify_mapping:=
        match goal with
          [H: ?a !! ?x ?y = Some _ ,
              H0: ?a !! ?x ?y = _ |- _] => rewrite H in H0
        | [H: ?a !! ?x ?y = None ,
              H0: ?a !! ?x ?y = _ |- _] => rewrite H in H0
        | [H: ?a !! ?x ?y = Some _ ,
              H0: _ = ?a !! ?x ?y |- _] => rewrite H in H0
        | [H: ?a !! ?x ?y = None ,
              H0: _ = ?a !! ?x ?y |- _] => rewrite H in H0
        end.
      
      
      Lemma permMapJoin_inject:
        forall mu a1 a2 b1 b2 c1 c2,
          no_overlap_perms mu a1 b1 ->
          no_overlap_perms mu b1 c1 ->
          no_overlap_perms mu c1 a1 ->
          perm_perfect_image mu a1 a2 ->
          perm_perfect_image mu b1 b2 ->
          perm_perfect_image mu c1 c2 ->
          permMapJoin a1 b1 c1 ->
          permMapJoin a2 b2 c2.
      Proof.
        intros * H12 H23 H31 Ha Hb Hc HH ??.
        destruct (a2 !! b ofs) eqn:AA; 
          destruct (b2 !! b ofs) eqn:BB; 
          destruct (c2 !! b ofs) eqn:CC;
          try exploit_perfect_image Ha;
          try exploit_perfect_image Hb;
          try exploit_perfect_image Hc;
          repeat unify_mapping;
          
          (* use no_pverlap_mem to set which blocks and ofsets are equal*)
          try (exploit_no_overlap_perm H12);
          try (exploit_no_overlap_perm H23);
          try (exploit_no_overlap_perm H31);
          !goal (permjoin_def.permjoin _ _ _);
          

          (* inistantiate hypothesis wiith permMapJoin *)
          try (match goal with
               |[H: mu ?b = _, _:Some _ = ?a !! ?b ?ofs |-_] => specialize (HH b ofs)
               end;
               (*rewriite the values ini the joiin*)
               repeat match goal with
                      | [ H: Some _ = _ |- _] => rewrite <- H in HH
                      end; auto);
          

          
          (*destruct the parts that are not mapped*)
          repeat match type of HH with
                   context[?a !! ?b ?ofs] =>
                   destruct (a !! b ofs) eqn:?
                 end; try eassumption;

            (* map the ones that are not mapped yet (and show a contradictoni)*)
            try exploit_perfect_image Ha;
            try exploit_perfect_image Hb;
            try exploit_perfect_image Hc;
            repeat unify_injection;
            repeat unify_mapping;
            try discriminate.
        - !goal (permjoin_def.permjoin None None None).
          constructor.
      Qed.

      
      Definition perm_perfect_image_pair mu:=
        pair2_prop (perm_perfect_image mu).
      Hint Unfold perm_perfect_image_pair: pair.
      
      Definition no_overlap_perms_pair mu:=
        pair2_prop (no_overlap_perms mu).
      Hint Unfold no_overlap_perms_pair: pair.
      
      Definition permMapLt_pair2:= pair2_prop permMapLt.
      Hint Unfold permMapLt_pair2: pair.
      
      Lemma permMapJoin_lt_pair1:
        forall p1 p2 p3 (Hjoin: permMapJoin_pair p1 p2 p3), permMapLt_pair2 p1 p3.
      Proof. solve_pair; eapply permMapJoin_lt. Qed.

      
      Lemma permMapJoin_lt_pair2:
        forall p1 p2 p3
               (Hjoin: permMapJoin_pair p1 p2 p3), permMapLt_pair2 p2 p3.
      Proof.
        solve_pair;intros.
        eapply permMapJoin_comm in H;
          eapply permMapJoin_lt; eauto.
      Qed.

      Lemma permMapJoin_pair_inject:
        forall mu a1 a2 b1 b2 c1 c2,
          no_overlap_perms_pair mu a1 b1 -> 
          no_overlap_perms_pair mu b1 c1 ->
          no_overlap_perms_pair mu c1 a1 ->
          perm_perfect_image_pair mu a1 a2 ->
          perm_perfect_image_pair mu b1 b2 ->
          perm_perfect_image_pair mu c1 c2 ->
          permMapJoin_pair a1 b1 c1 ->
          permMapJoin_pair a2 b2 c2.
      Proof.
        intros ?; solve_pair.
        apply permMapJoin_inject.
      Qed.

      Definition permMapLt_pair pp1 p2:=
        permMapLt_pair2 pp1 (pair0 p2).
      Hint Unfold permMapLt_pair: pair.
      Instance permMapLt_pair_proper : 
        Proper (Logic.eq ==> access_map_equiv ==> iff) permMapLt_pair.
      Proof.
        setoid_help.proper_iff;
          setoid_help.proper_intros; subst.
        split; simpl; rewrite <- H0; eapply H1.
      Qed.
      
      Lemma permMapLt_trans:
        transitive _ permMapLt.
      Proof. unfold permMapLt; intros ? **.
             eapply mem_lemmas.po_trans; eauto.
      Qed.
      Lemma permMapLt_pair_trans211:
        forall pa pb c,
          permMapLt_pair2 pa pb ->
          permMapLt_pair pb c ->
          permMapLt_pair pa c.
      Proof.
        unfold permMapLt_pair; intros;
          eapply impr_rel_trans; eauto.
        eapply permMapLt_trans.
      Qed.
      
      Lemma no_overlap_perms_under_mem:
        forall mu a1 a2 m,
          Mem.meminj_no_overlap mu m ->
          permMapLt a1 (getMaxPerm m) ->
          permMapLt a2 (getMaxPerm m) ->
          no_overlap_perms mu a1 a2.
      Proof.
        intros ** ????????????.
        destruct (Clight_lemmas.block_eq_dec b1 b1').
        - subst; unify_injection.
          repeat (split; auto); omega.
        - exfalso.
          exploit H; eauto; unfold Mem.perm.
          + try (rewrite_getPerm_goal; eapply perm_order_trans211).
            2: eapply at_least_perm_order; exact H4.
            apply H0.
          + try (rewrite_getPerm_goal; eapply perm_order_trans211).
            2: eapply at_least_perm_order; exact H5.
            apply H1.
          + intros [?| ?]; tauto.
      Qed.
      Lemma no_overlap_perms_under_mem_pair:
        forall mu a1 a2 m,
          Mem.meminj_no_overlap mu m ->
          permMapLt_pair a1 (getMaxPerm m) ->
          permMapLt_pair a2 (getMaxPerm m) ->
          no_overlap_perms_pair mu a1 a2.
      Proof.
        intros; split;
          eapply no_overlap_perms_under_mem; eauto;
            first [eapply H0 | eapply H1].
      Qed.
      Lemma compat_permMapLt:
        forall Sem st i cnt m,
          @thread_compat Sem st i cnt m <->
          permMapLt_pair (getThreadR cnt) (getMaxPerm m).
      Proof. intros; split; intros [X1 X2]; split; auto. Qed.
      
      Lemma permMapJoin_pair_comm:
        forall AA BB CC,
          permMapJoin_pair AA BB CC ->
          permMapJoin_pair BB AA CC.
      Proof. solve_pair; apply permMapJoin_comm. Qed.
      
      Lemma permMapLt_pair_trans:
        transitive _ permMapLt_pair2.
      Proof. unfold transitive; solve_pair.
             eapply permMapLt_trans.
      Qed.

      (*Definition dmap_get (dm:delta_map) b ofs:=
        match dm ! b with
          Some f =>
          match f ofs with
            Some p => Some p
          | None => None 
          end
        |None => None
        end.
      Lemma dmap_get_Some:
        forall dm b ofs p,
          dmap_get dm b ofs = Some p ->
          exists f, dm ! b = Some f /\
               f ofs = Some p.
      Proof.
        intros * H.
        unfold dmap_get in *.
        destruct (dm ! b) eqn:HH1; try solve[inversion H].
        destruct (o ofs) eqn: HH2; inv H.
        do 2 econstructor; eauto.
      Qed.
      Lemma dmap_get_copmute_Some:
        forall C A b ofs p,
          dmap_get A b ofs = Some p ->
          (computeMap C A) !! b ofs = p.
      Proof.
        intros; unfold dmap_get in H.
        destruct (A ! b) eqn:Ab; try solve[inversion H].
        destruct (o ofs) eqn:oofs; try solve[inversion H].
        erewrite computeMap_1; eauto.
        rewrite oofs; assumption.
      Qed.
      Lemma dmap_get_copmute_None:
        forall C A b ofs,
          dmap_get A b ofs = None ->
          (computeMap C A) !! b ofs = C !! b ofs.
      Proof.
        intros.
        unfold dmap_get in H.
        destruct (A ! b) eqn:Ab.
        destruct (o ofs) eqn:oofs; try solve[inversion H].
        - erewrite computeMap_2; eauto.
        - erewrite computeMap_3; eauto.
      Qed.*)
      

      (* Why is subsummed different to submap?*)
      Inductive subsumed: option permission -> option permission -> Prop:=
      | subsumedNone: forall x, subsumed None x
      | subsumedNENE: subsumed (Some Nonempty) (Some Nonempty)
      | subsumedNER: subsumed (Some Nonempty) (Some Readable)
      | subsumedNEW: subsumed (Some Nonempty) (Some Writable)
      | subsumedRR: subsumed (Some Readable) (Some Readable)
      | subsumedRW: subsumed (Some Readable) (Some Writable).

      
      Lemma subsumed_order:
        forall b c, subsumed b c -> Mem.perm_order'' c b.
      Proof. intros b c H; destruct b, c; inv H; constructor. Qed.

      Lemma subsume_same_join:
        forall x y, subsumed x y <->
               permjoin_def.permjoin y x y.
      Proof.
        intros x y; split;
          intros HH; inversion HH; subst; constructor.
      Qed.

      
      Inductive option_join :
        option (option permission) ->
        option permission ->
        option permission -> Prop :=
      | NoneJoin: forall l c,
          subsumed l c -> (* why subsumed? *)
          option_join None l c
      | SomeJoin: forall a b c,
          permjoin_def.permjoin a b c ->
          option_join (Some a) b c.
      
      Definition delta_map_join
                 (A: delta_map)
                 (B: access_map)
                 (C: access_map):=
        forall b ofs,
          option_join (dmap_get A b ofs)
                      (B !! b ofs)
                      (C !! b ofs).
      Definition delta_map_join_pair:= pair3_prop delta_map_join.
      Hint Unfold delta_map_join_pair: pair.

      
      Lemma compute_map_join:
        forall A B C,
          delta_map_join A B C <->
          permMapJoin
            (computeMap C A) B C.
      Proof.
        split;
          intros ** b ofs.
        
        { !goal(permjoin_def.permjoin _ _ _).
          specialize (H b ofs); inversion H; subst.
          - unfold dmap_get, PMap.get in H0; simpl in *.
            destruct (A ! b) eqn:Ab.
            + destruct (o ofs) eqn:oofs; try inversion H0.
              erewrite computeMap_2; eauto.
              eapply subsume_same_join; auto.
            + erewrite computeMap_3; eauto.
              eapply subsume_same_join; auto. 
          - unfold dmap_get, PMap.get in H0; simpl in *.
            destruct (A ! b) eqn:HH; try solve[inversion H0].
            erewrite computeMap_1.
            1, 2: eauto.
            destruct (o ofs) eqn:HH'; inversion H0; auto. }
        
        { !goal (option_join _ _ _ ).
          destruct (dmap_get A b ofs) eqn:HH.
          - eapply dmap_get_copmute_Some in HH.
            rewrite <- HH.
            econstructor; eauto.
          - eapply dmap_get_copmute_None in HH.
            econstructor.
            specialize (H b ofs).
            rewrite HH in H.
            eapply subsume_same_join; assumption.
        }
      Qed.
      Lemma compute_map_join_fwd:
        forall A B C,
          delta_map_join A B C ->
          permMapJoin
            (computeMap C A) B C.
      Proof. intros; apply compute_map_join; assumption. Qed.
      Lemma compute_map_join_bkw:
        forall A B C,
          permMapJoin
            (computeMap C A) B C ->
          delta_map_join A B C.
      Proof. intros; apply compute_map_join; assumption. Qed.
      Lemma compute_map_join_pair:
        forall AA BB CC,
          delta_map_join_pair AA BB CC <->
          permMapJoin_pair
            (computeMap_pair CC AA) BB CC.
      Proof. solve_pair; apply compute_map_join. Qed.
      Lemma compute_map_join_fwd_pair:
        forall AA BB CC,
          delta_map_join_pair AA BB CC ->
          permMapJoin_pair
            (computeMap_pair CC AA) BB CC.
      Proof. solve_pair; apply compute_map_join_fwd. Qed.
      Lemma compute_map_join_bkw_pair:
        forall AA BB CC,
          permMapJoin_pair
            (computeMap_pair CC AA) BB CC ->
          delta_map_join_pair AA BB CC.
      Proof. solve_pair; apply compute_map_join_bkw. Qed.
      (* Definition at_least_Some {A} (x:option A):=
        option_implication (Some tt) x. *)
      Definition perm_image_full_dmap f dm1 dm2:=
        forall b1 ofs,
          at_least_Some (dmap_get dm1 b1 ofs) ->
          exists b2 delta,
            f b1 = Some (b2, delta) /\
            (dmap_get dm1 b1 ofs) = (dmap_get dm2 b2 (ofs + delta)).
      Definition dmap_preimage f dm1 dm2:=
        forall b2 ofs_delt,
          at_least_Some (dmap_get dm2 b2 ofs_delt) ->
          exists (b1 : block) (ofs delt : Z),
            f b1 = Some (b2, delt) /\
            ofs_delt = ofs + delt /\
            (dmap_get dm2 b2 ofs_delt) = (dmap_get dm1 b1 ofs).
      Definition perfect_image_dmap (f:meminj) (a1 a2: delta_map): Prop:=
        forall b1 b2 delt,
          f b1 = Some (b2, delt) ->
          forall ofs, dmap_get a1 b1 ofs = dmap_get a2 b2 (ofs + delt).
      (* TODO: change the names 
             perm_image_full -> perm_inj
             perm_preimage -> perm_surj
             pimage_dmap -> pimage  
             p_image_dmap -> prem_inj
             ppre_perfect_image__dmap -> prem_surj
       *) 
      Record perm_perfect_image_dmap (mu : meminj) (a1 a2 : delta_map) : Prop
        := { p_image_dmap : perm_image_full_dmap mu a1 a2;
             ppre_perfect_image_dmap : dmap_preimage mu a1 a2 }.
      Arguments p_image_dmap {_ _ _}.
      Arguments ppre_perfect_image_dmap {_ _ _}.
      Lemma perm_order_from_dmap:
        forall dmap b (ofs : Z) p,
          dmap_get  dmap b ofs  = Some (Some p) ->
          opt_rel Mem.perm_order''  (dmap_get  dmap b ofs)
                          (Some (Some Nonempty)).
      Proof. intros * H; rewrite H; repeat constructor. Qed.
      Lemma perm_order_from_dmap':
        forall dmap b (ofs : Z) p,
          dmap_get  dmap b ofs  = Some p ->
          at_least_Some (dmap_get  dmap b ofs).
      Proof. intros * H; rewrite H;  destruct p; repeat constructor. Qed.
      Local Ltac exploit_p_image_dmap H:=
        let b:=fresh "b" in
        let delt:=fresh "delt" in
        let Hinj:=fresh "Hinj" in
        destruct
          (p_image_dmap H _ _ ltac:(eapply perm_order_from_dmap'; eauto))
          as (b&delt&Hinj&?); subst.
      Local Ltac exploit_ppre_image_dmap H:=
        let b:=fresh "b" in
        let ofs:=fresh "ofs" in
        let delt:=fresh "delt" in
        let Hinj:=fresh "Hinj" in
        destruct
          (ppre_perfect_image_dmap H _ _ ltac:(eapply perm_order_from_dmap'; eauto))
          as (b&ofs&delt&Hinj&?&?); subst.
      Local Ltac exploit_perfect_image_dmap H:=
        first [exploit_p_image_dmap H| exploit_ppre_image_dmap H]. (*
            progress (try (exploit_p_image_dmap H); try (exploit_ppre_image_dmap H)).*)

      
      Definition no_overlap_contrapositive f m:=
        forall (b1 b1':block) delta1 b2 b2' delta2 ofs1 ofs2,
          b1' = b2' /\ ofs1 + delta1 = ofs2 + delta2 ->
          f b1 = Some (b1', delta1) ->
          f b2 = Some (b2', delta2) ->
          Mem.perm m b1 ofs1 Max Nonempty ->
          Mem.perm m b2 ofs2 Max Nonempty -> b1 = b2. 
      
      
      Lemma no_overlap_contrapositive_iff:
        forall f m,
          Mem.meminj_no_overlap f m <-> no_overlap_contrapositive f m.
      Proof.
        intros **. split; intros H.
        - intros ? **. destruct H0; subst.
          destruct (Clight_lemmas.block_eq_dec b1 b2); auto.
          exploit H; eauto.
          intros [? | ?]; congruence.
        - intros ? **. 
          destruct (Clight_lemmas.block_eq_dec b1' b2'); auto.
          destruct (Z_noteq_dec (ofs1 + delta1) (ofs2 + delta2)); auto.
          exploit H; eauto.
      Qed.
      Definition deltaMapLt2 (dmap: delta_map) (pmap : access_map) : Prop :=
        forall b ofs,
          opt_rel
            Mem.perm_order''
            (Some (Maps.PMap.get b pmap ofs))
            (dmap_get dmap b ofs).
      
      Definition almost_perfect_image mu (max a1 a2: access_map):=
        forall b1 b2 delt,
          mu b1 = Some (b2, delt) ->
          forall ofs,
            Mem.perm_order'' (max !! b1 ofs) (Some Nonempty) ->
            a1 !! b1 ofs = a2 !! b2 (ofs + delt).
      Lemma injection_perfect_image:
        forall mu m1 m2,
          Mem.inject mu m1 m2 ->
          almost_perfect_image mu (getMaxPerm m1) (getCurPerm m1) (getCurPerm m2).
      Proof.
        intros * Hinj ??? Hmu ? Hmax.
        dup Hmu as Hmu'.
        pose proof (Mem.mi_perm_inv _ _ _ Hinj) as H1.
        assert (H2:
                  forall p,
                    Mem.perm m2 b2 (ofs + delt) Cur p ->
                    Mem.perm m1 b1 ofs Cur p \/ ~ Mem.perm m1 b1 ofs Max Nonempty).
        { intros ?; eapply H1; eauto. } clear H1.
        assert (Hr: forall p,
                   Mem.perm m2 b2 (ofs + delt) Cur p ->
                   Mem.perm m1 b1 ofs Cur p).
        { intros ? HHH. eapply H2 in HHH. destruct HHH; auto.
          contradict H. unfold Mem.perm.
          repeat rewrite getMaxPerm_correct in *; unfold permission_at in *.
          rewrite mem_lemmas.po_oo; auto.
          
        } clear H2.
        assert (Hl: forall p,
                   Mem.perm m1 b1 ofs Cur p ->
                   Mem.perm m2 b2 (ofs + delt) Cur p).
        { intros ?. eapply Mem.mi_perm; eauto; try apply Hinj. }
        
        match goal with
          |- ?L = ?R =>
          destruct L as [pl|] eqn:LHS;
            destruct R as [pr|] eqn:RHS; auto;
              try (specialize (Hl pl);
                   unfold Mem.perm in Hl;
                   unfold_getCurPerm;
                   rewrite LHS in *
                   ;specialize (Hl ltac:(simpl; eapply perm_refl))
                  );
              try (specialize (Hr pr);
                   unfold Mem.perm in Hr;
                   unfold_getCurPerm;
                   rewrite RHS in *;
                   specialize (Hr ltac:(eapply perm_refl))
                  );
              try rewrite LHS in *;
              try rewrite RHS in *;
              try solve[inv Hl];
              try solve [inv Hr]
        end.
        - simpl in *; clear - Hr Hl.
          destruct pl, pr; auto;
            inversion Hr; inversion Hl.
      Qed.

      Lemma r_dmap_join_lt:
        forall A B C,
          delta_map_join A B C->
          permMapLt B C.
      Proof.
        intros ??? H b ofs. specialize (H b ofs).
        inv H.
        - apply subsumed_order; assumption.
        - apply permjoin_def.permjoin_order in H1 as [? ?]; auto.
      Qed.
      Definition dmap_vis_filtered (dmap:delta_map) (m:mem) :=
        forall b ofs p,
          dmap_get dmap b ofs = Some p ->
          Mem.perm m b ofs Max Nonempty. 
      Lemma delta_map_join_inject:
        forall m f A1 A2 B1 B2 C1 C2,
          Mem.meminj_no_overlap f m ->
          dmap_vis_filtered A1 m ->
          (*deltaMapLt2 A1 (getMaxPerm m) ->
              permMapLt B1  (getMaxPerm m) -> *)
          permMapLt C1  (getMaxPerm m) ->
          perm_perfect_image_dmap f A1 A2 ->
          perm_perfect_image f B1 B2 ->
          almost_perfect_image f (getMaxPerm m) C1 C2 ->
          (* perm_perfect_image f C1 C2 -> *)
          delta_map_join A1 B1 C1 ->
          delta_map_join A2 B2 C2.
      Proof.
        intros * Hno_overlap Hfilter HltC  HppiA HppiB HppiC Hjoin b2 ofs_delta.
        assert (HltB : permMapLt B1 (getMaxPerm m)).
        { intros b ofs. eapply perm_order''_trans.
          - eapply HltC.
          - revert b ofs.
            apply r_dmap_join_lt with A1; assumption. }
        
        
        
        (* Ltacs for this goal *)
        

        Local Ltac rewrite_double:=
          match goal with
          | [ H: ?L = ?R, H0: ?L = Some _  |- _ ] =>
            rewrite H0 in H; try rewrite <- H in *; symmetry in H
          | [ H: ?R = ?L, H0: ?L = Some _  |- _ ] =>
            rewrite H0 in H; try rewrite H in *
          | [ H: ?L = ?R, H0: ?L = None  |- _ ] =>
            rewrite H0 in H; try rewrite <- H in *; symmetry in H
          | [ H: ?R = ?L, H0: ?L = None  |- _ ] =>
            rewrite H0 in H; try rewrite H in *
          end.
        
        Ltac auto_exploit_pimage :=
          match goal with
          | [ H: perm_perfect_image_dmap _ _ _ |- _ ] =>
            exploit_perfect_image_dmap H; clear H
          | [ H: perm_perfect_image _ _ _ |- _ ] => 
            exploit_perfect_image H; clear H
          end ; repeat rewrite_double. 
        
        
        (* Case analysis on first term*)
        match goal with
        | [ |- option_join _ ?B _ ] => destruct B as [o|] eqn:HB2 
        end.
        - (*B2 -> Some *)
          Note B2_Some.
          auto_exploit_pimage.
          dup Hinj as Hinj'.
          assert (Hmax: Mem.perm_order' ((getMaxPerm m) !! b ofs) Nonempty).
          { eapply perm_order_trans211.
            specialize (HltB b ofs).
            eapply HltB. rewrite H0; constructor.
          }

          (* new try*)
          destruct (dmap_get A2 b2 (ofs + delt)) eqn:HA2.
          + exploit (ppre_perfect_image_dmap HppiA); eauto.
            { rewrite HA2; constructor. }
            intros; normal. rewrite HA2 in H2.

            assert (x = b).
            { destruct (Clight_lemmas.block_eq_dec x b); auto.
              exploit Hno_overlap; eauto.
              unfold Mem.perm. rewrite_getPerm; eauto. 
              intros [HH | HH]; contradict HH; auto.
            }

            subst; unify_injection.
            assert (x0 = ofs) by omega; subst.
            
            specialize (Hjoin b ofs).
            rewrite <- H2, H0 in Hjoin.
            inv Hjoin. constructor.
            exploit HppiC; eauto.
            intros <-; auto.

          + specialize (Hjoin b ofs).
            destruct (dmap_get A1 b ofs) eqn:HA1.
            * exploit (p_image_dmap HppiA); eauto.
              { rewrite HA1. constructor. }
              intros; normal. unify_injection.
              rewrite HA1, HA2 in H1; congruence.
            * rewrite H0 in Hjoin. 
              inv Hjoin. constructor.
              exploit HppiC; eauto.
              intros <-; auto.
              
              
        (* end of new try*)
        (*
          eapply pimage_dmap in Hinj'; [rewrite <- Hinj'; clear Hinj'|]; eauto.

          assert (Mem.perm_order'' ((getMaxPerm m) !! b ofs) (Some Nonempty)).
          { eapply perm_order_trans211.
            - eapply HltC.
            - eapply perm_order_trans211.
              + eapply r_dmap_join_lt; eauto.
              + rewrite H0; constructor. }
          match goal with
          | [ |- option_join _ _ ?C ] => destruct C eqn:HC2 
          end.
          * (*C2 Some *)
            eapply HppiC in H; eauto.
            rewrite_double.
            specialize (Hjoin b ofs).
            rewrite H0, H in Hjoin; auto.
          * eapply HppiC in H; eauto.
            rewrite_double.
            specialize (Hjoin b ofs).
            rewrite H0, H in Hjoin; auto. *)
        - match goal with
          | [ |- option_join ?A _ _ ] => destruct A as [o|] eqn:HA2 
          end.
          + auto_exploit_pimage.
            specialize (Hjoin b ofs).
            assert (HB1:B1 !! b ofs = None).
            { match goal with
                |- ?L = ?R => destruct L eqn:HB1 end; auto.
              auto_exploit_pimage.
              inv Hinj.
              rewrite_double; auto. }
            rewrite H0, HB1 in Hjoin.
            inv Hjoin. assert ((C1 !! b ofs) = o) by (inv H1; auto).
            constructor.
            exploit HppiC; eauto.  
            * rewrite <- mem_lemmas.po_oo. 
              eapply Hfilter in H0.
              unfold Mem.perm in H0.
              rewrite_getPerm; eauto.
            * intros <-; auto.
          + do 2 constructor.
      Qed.       
      

      Definition perm_perfect_image_dmap_pair f:=
        pair2_prop (perm_perfect_image_dmap f).
      Hint Unfold perm_perfect_image_dmap_pair: pair.

      Definition deltaMapLt2_pair1:= pair21_prop deltaMapLt2.
      Hint Unfold deltaMapLt2_pair1: pair.
      Definition dmap_vis_filtered_pair:= pair21_prop dmap_vis_filtered.
      Hint Unfold dmap_vis_filtered_pair: pair.
      Definition almost_perfect_image_pair f max_perm:=
        pair2_prop (almost_perfect_image f max_perm).
      Hint Unfold almost_perfect_image_pair: pair.
      Lemma delta_map_join_inject_pair (m:mem) f:
        forall A1 A2 B1 B2 C1 C2,
          Mem.meminj_no_overlap f m ->
          dmap_vis_filtered_pair A1 m ->
          (*deltaMapLt2_pair1 A1 (getMaxPerm m) ->
              permMapLt_pair1 B1 (getMaxPerm m) -> *)
          permMapLt_pair C1 (getMaxPerm m) ->
          perm_perfect_image_dmap_pair f A1 A2 ->
          perm_perfect_image_pair f B1 B2 ->
          almost_perfect_image_pair f (getMaxPerm m) C1 C2 -> 
          delta_map_join_pair A1 B1 C1 ->
          delta_map_join_pair A2 B2 C2.
      Proof. solve_pair; eapply delta_map_join_inject. Qed.
      
      
      Inductive injects (mu:meminj) (b:block): Prop:=
      | InjectsBlock: forall b2 delta,
          mu b = Some (b2, delta) -> injects mu b.
      Definition injects_map mu (m:access_map): Prop := forall b ofs p,
          m !! b ofs = Some p ->
          injects mu b.
      Definition injects_map_pair mu:= pair1_prop (injects_map mu).
      Hint Unfold injects_map_pair: pair.
      Definition injects_dmap mu (m:delta_map) := forall b ofs p,
          dmap_get m b ofs = Some p -> injects mu b.
      Definition injects_dmap_pair mu:= pair1_prop (injects_dmap mu).
      Hint Unfold injects_dmap_pair: pair.


      
      Lemma sub_map_implictaion:
        forall {A B} x y, @bounded_maps.sub_map A B x y ->
                          forall b, option_implication (x ! b) (y ! b).
      Proof.
        intros *.
        unfold bounded_maps.sub_map; intros HH b.
        eapply strong_tree_leq_spec in HH.
        - instantiate(1:=b) in HH.
          unfold option_implication.
          repeat match_case; auto.
        - constructor.
      Qed.
      Lemma option_implication_trans:
        forall {A B C} a b c,
          @option_implication A B a b ->
          @option_implication B C b c ->
          @option_implication A C a c.
      Proof.
        unfold option_implication.
        intros *; repeat match_case.
      Qed.

      Lemma no_overla_dmap_mem:
        forall mu m dmap,
          (forall (b : positive) (ofs : Z),
              option_implication
                (dmap_get dmap b ofs)
                ((getMaxPerm m) !! b ofs)) ->
          Mem.meminj_no_overlap mu m ->
          dmap_no_overlap mu dmap.
      Proof.
        intros ** ? **.
        eapply H0; eauto.
        + specialize (H b1 ofs1).
          unfold Mem.perm; rewrite_getPerm.
          unfold option_implication in *.
          repeat match_case in H.
          constructor.
          unfold dmap_get in *.
          rewrite Heqo in H4.
          inversion H4.
        + specialize (H b2 ofs2).
          unfold Mem.perm; rewrite_getPerm.
          unfold option_implication in *.
          repeat match_case in H.
          constructor.
          unfold dmap_get in *.
          rewrite Heqo in H5.
          inv H5.
      Qed.
      Lemma no_overla_perm_mem:
        forall {A} mu m perm,
          (forall (b : positive) (ofs : Z),
              option_implication
                (perm !! b ofs)
                ((getMaxPerm m) !! b ofs)) ->
          Mem.meminj_no_overlap mu m ->
          @perm_meminj_no_overlap A mu perm.
      Proof.
        intros ** ? **.
        eapply H0; eauto.
        + specialize (H b1 ofs1).
          unfold Mem.perm; rewrite_getPerm.
          unfold option_implication in *.
          repeat match_case in H.
          constructor.
          inversion H4.
        + specialize (H b2 ofs2).
          unfold Mem.perm; rewrite_getPerm.
          unfold option_implication in *.
          repeat match_case in H.
          constructor.
          inversion H5. 
      Qed.
      Lemma canon_mem_access:
        forall m1 ofs k, fst (Mem.mem_access m1) ofs k = None.
      Proof.
        intros.
        destruct k.
        - pose proof (Max_isCanonical m1).
          unfold getMaxPerm in *.
          unfold isCanonical in *; simpl in *.
          match type of H with
            ?a = ?b => remember a as A eqn:HH;
                        assert (A ofs = b ofs) by (rewrite H;auto);
                        subst A; auto
          end.
          
        - pose proof (Cur_isCanonical m1).
          unfold getMaxPerm in *.
          unfold isCanonical in *; simpl in *.
          match type of H with
            ?a = ?b => remember a as A eqn:HH;
                        assert (A ofs = b ofs) by (rewrite H;auto);
                        subst A; auto
          end.
      Qed.
      
      Definition isCanonical' {A} (pmap: PMap.t (Z-> option A)):=
        fst pmap = (fun _ : Z => None).
      Lemma option_implication_injection:
        forall {A} mu m1 m2 b1 b2 ofs (perm:PMap.t (Z -> option A) ) o delta
          (Hcanon: isCanonical' perm)
          (Hdmap: perm !! b1 ofs = Some o)
          (Himpl: option_implication
                    (perm !! b1 ofs)
                    ((getMaxPerm m1) !! b1 ofs))
          (Hmi_inj:Mem.mem_inj mu m1 m2),
          mu b1 = Some (b2, delta) ->
          option_implication
            (snd perm) ! b1 (snd (getMaxPerm m2)) ! b2.
      Proof.
        intros.
        unfold PMap.get in *; simpl in *.
        repeat match_case in Hdmap.
        2: { rewrite Hcanon in Hdmap. congruence. } 
        eapply option_implication_trans.
        - instantiate(1:= (snd (getMaxPerm m1)) ! b1).
          unfold option_implication,PMap.get,getMaxPerm in *.
          simpl. 
          rewrite Hdmap in Himpl.
          repeat match_case; auto.
          repeat match_case in Himpl; auto.
          rewrite canon_mem_access in Heqo2.
          congruence.
        - pose proof (Mem.mi_perm
                        _ _ _ Hmi_inj b1 b2 delta
                        ofs Max Nonempty H); eauto.
          unfold Mem.perm in *.
          repeat rewrite_getPerm.
          rewrite Hdmap in *.
          unfold PMap.get in *.
          repeat match_case in Himpl.
          2:{ rewrite canon_mem_access in *; inv Himpl. }
          rewrite PTree.gmap1.
          repeat match_case in H0; simpl; auto.
          + unfold getMaxPerm in Heqo3; simpl in *.
            rewrite PTree.gmap1 in  Heqo3.
            rewrite  Heqo3; auto.
          + rewrite PTree.gmap1 in  Heqo1.
            unfold getMaxPerm in *; simpl in *.
            rewrite PTree.gmap1 in *.
            destruct ((snd (Mem.mem_access m1)) ! b1) eqn:HH;
              simpl in *; inv Heqo1; inv Heqo2.
            unfold option_implication in *.
            rewrite canon_mem_access in H0.
            match_case in Himpl.
            exploit H0; try (intros HHH; inv HHH).
            constructor.
            
      Qed.
      Lemma option_implication_injection_dmap:
        forall mu m1 m2 b1 b2 ofs dmap o delta
          (Hdmap: dmap_get dmap b1 ofs = Some o)
          (Himpl: option_implication
                    (dmap_get dmap b1 ofs)
                    ((getMaxPerm m1) !! b1 ofs))
          (Hmi_inj:Mem.mem_inj mu m1 m2),
          mu b1 = Some (b2, delta) ->
          option_implication
            dmap ! b1 (snd (getMaxPerm m2)) ! b2.
      Proof.
        intros.
        exploit (@option_implication_injection (option permission)); eauto.
        reflexivity.
      Qed.
      Lemma inject_perm_image_full_dmap':
        forall mu m1 m2 dmap
               (Hinj_dmap: injects_dmap mu dmap)
               (Himpl:
                  forall b1 b2 delta ofs o,
                    mu b1 = Some (b2, delta) ->
                    dmap_get dmap b1 ofs = Some o ->
                    option_implication dmap ! b1 (snd (getMaxPerm m2)) ! b2)
               (Hmi_inj:Mem.mem_inj mu m1 m2)
               (Hnon_over: dmap_no_overlap mu dmap),
          perm_image_full_dmap
            mu dmap (tree_map_inject_over_mem m2 mu dmap).
      Proof.
        intros ** b1 ** .
        destruct (dmap_get dmap b1 ofs) eqn:Hdmap; try solve[inv H].
        specialize (Hinj_dmap _ _ _ Hdmap).
        inv Hinj_dmap. normal; eauto.
        erewrite tree_map_inject_over_mem_correct_forward; eauto.
      Qed.
      Lemma inject_perm_image_full':
        forall mu m1 m2 perm
          (Hcanon: isCanonical perm)
          (Hinj_dmap: injects_map mu perm)
          (Himpl:
             forall b1 b2 delta ofs o,
               mu b1 = Some (b2, delta) ->
               perm !! b1 ofs = Some o ->
               option_implication (snd perm) ! b1 (snd (getMaxPerm m2)) ! b2)
          (Hmi_inj:Mem.mem_inj mu m1 m2)
          (Hnon_over: no_overlap mu perm),
          perm_image_full
            mu perm (inject_access_map m2 mu perm).
      Proof.
        unfold inject_access_map; intros ** b1 **. 
        destruct (perm !! b1 ofs) eqn:Hdmap; try solve[inv H].
        specialize (Hinj_dmap _ _ _ Hdmap).
        inv Hinj_dmap. normal; eauto.
        
        exploit Himpl; eauto; intros HH.
        unfold option_implication in *.
        unfold PMap.get in *; simpl.
        repeat match_case in Hdmap.
        2:{ rewrite Hcanon in Hdmap; congruence. }
        exploit tree_map_inject_over_mem_correct_forward_perm; eauto.
        - unfold PMap.get; rewrite Heqo; auto.
        - match_case in HH. unfold option_implication; match_case.
      Qed.
      Lemma inject_perm_image_full_dmap:
        forall mu m1 m2 dmap
          (Hinj_dmap: injects_dmap mu dmap)
          (Himpl: forall b ofs,
              option_implication
                (dmap_get dmap b ofs)
                ((getMaxPerm m1) !! b ofs))
          (Hmi_inj:Mem.inject mu m1 m2),
          perm_image_full_dmap
            mu dmap (tree_map_inject_over_mem m2 mu dmap).
      Proof.
        intros.
        eapply inject_perm_image_full_dmap'; intros; eauto.
        - eapply option_implication_injection_dmap; eauto.
          eapply Hmi_inj.
        - eapply Hmi_inj.
        - eapply no_overla_dmap_mem; auto.
          eapply Hmi_inj.
      Qed.
      Lemma option_implication_fst:
        forall {A B} (perm1 perm2:PMap.t (A -> option B)),
          (forall b ofs,
              option_implication (perm1 !! b ofs) (perm2 !! b ofs)) ->
          forall ofs, option_implication ((fst perm1) ofs) ((fst perm2) ofs).
      Proof.
        Lemma finite_ptree:
          forall {A} (t:PTree.t A), exists b, forall b', (b < b')%positive -> (t ! b') = None.
        Proof.
          intros ? t; induction t.
          - exists xH; intros; simpl. eapply PTree.gleaf.
          - normal_hyp.
            exists (Pos.max (x0~0) (x~1)); intros.
            destruct b'; simpl;
              first [eapply H0| eapply H| idtac].
            + cut (x~1 <  b'~1)%positive.
              * unfold Pos.lt, Pos.compare in *; auto.
              * eapply Pos.max_lub_lt_iff in H1 as [? ?].
                auto.
            + cut (x0~0 <  b'~0)%positive.
              * unfold Pos.lt, Pos.compare in *; auto.
              * eapply Pos.max_lub_lt_iff in H1 as [? ?]; auto.
            + exfalso. eapply Pos.nlt_1_r; eassumption.
        Qed.
        intros *.
        pose proof (finite_ptree (snd perm1)).
        pose proof (finite_ptree (snd perm2)).
        normal_hyp.
        remember (Pos.max (x0 + 1) (x+1)) as bound.
        intros.
        specialize (H1 bound ofs). unfold PMap.get in *.
        rewrite H, H0 in H1; auto; xomega.
      Qed.
      Lemma option_impl_isCanon:
        forall perm m1,
          (forall (b : positive) (ofs : Z),
              option_implication (perm !! b ofs) ((getMaxPerm m1) !! b ofs)) ->
          isCanonical perm.
      Proof.
        intros * Himpl; unfold.
        extensionality ofs.
        eapply option_implication_fst in Himpl.
        instantiate(1:= ofs) in Himpl.
        rewrite Max_isCanonical in Himpl.
        unfold option_implication in Himpl. match_case in Himpl.
      Qed.
      Lemma inject_perm_image_full:
        forall mu m1 m2 perm
               (Hinj_dmap: injects_map mu perm)
               (Himpl: forall b ofs,
                   option_implication
                     (perm !! b ofs)
                     ((getMaxPerm m1) !! b ofs))
               (Hmi_inj:Mem.inject mu m1 m2),
          perm_image_full
            mu perm (inject_access_map m2 mu perm).
      Proof.
        intros.
        eapply inject_perm_image_full'; intros; eauto.
        - eapply option_impl_isCanon; eauto.
        - eapply option_implication_injection; eauto.
          + unfold isCanonical'. extensionality ofs0.
            eapply option_implication_fst in Himpl.
            instantiate(1:=ofs0) in Himpl.
            rewrite Max_isCanonical in Himpl.
            unfold option_implication in *.
            match_case in Himpl.
          + eapply Hmi_inj.
        - eapply Hmi_inj.
        - eapply no_overla_perm_mem; auto.
          eapply Hmi_inj.
      Qed.
      Lemma inject_dmap_preimage:
        forall mu m2 dmap,
          dmap_preimage
            mu dmap (tree_map_inject_over_mem m2 mu dmap).
      Proof.
        unfold dmap_preimage; intros.
        unfold at_least_Some, option_implication in *.
        match_case in H.
        apply dmap_inject_correct_backwards in Heqo.
        normal; eauto.
      Qed.
      Lemma inject_preimage:
        forall mu m2 perm,
          perm_preimage
            mu perm (inject_access_map m2 mu perm).
      Proof.
        unfold perm_preimage; intros.
        unfold at_least_Some, option_implication in *.
        match_case in H.
        eapply inject_access_map_correct_backwards in Heqo.
        normal; eauto.
      Qed.
      Definition option_implication_dmap_access (dmap:delta_map)(map: access_map) :=
        forall b ofs, option_implication (dmap_get dmap b ofs) (map !! b ofs).
      Definition option_implication_dmap_access_pair :=
        pair21_prop option_implication_dmap_access.
      Hint Unfold option_implication_dmap_access_pair: pair.
      Definition option_implication_access (a1 a2: access_map) :=
        forall b ofs, option_implication (a1 !! b ofs) (a2 !! b ofs).
      Definition option_implication_access_pair :=
        pair21_prop option_implication_access.
      Hint Unfold option_implication_access_pair: pair.
      
      Lemma inject_perm_perfect_image_dmap:
        forall mu m1 m2 dmap
               (Hmi_inj:Mem.inject mu m1 m2)
               (Himpl: option_implication_dmap_access
                         dmap (getMaxPerm m1))
               (Hinj_dmap: injects_dmap mu dmap),
          perm_perfect_image_dmap
            mu dmap (tree_map_inject_over_mem m2 mu dmap).
      Proof.
        intros; constructor.
        - eapply inject_perm_image_full_dmap; auto.
        - eapply inject_dmap_preimage.
      Qed.

      
      Lemma inject_perm_perfect_image:
        forall mu m1 m2 (m : access_map),
          Mem.inject mu m1 m2 ->
          injects_map mu m ->
          perm_perfect_image mu m (inject_access_map m2 mu m).
      Proof.
        intros; constructor.
        - eapply inject_perm_image_full; auto.
      Admitted.
      

      Lemma inject_virtue_perm_perfect_image_dmap:
        forall mu m1 m2 angel ,
          Mem.inject mu m1 m2 ->
          (option_implication_dmap_access_pair
             (virtueThread angel) (getMaxPerm m1)) ->
          injects_dmap_pair mu (virtueThread angel) ->
          perm_perfect_image_dmap_pair mu
                                       (virtueThread angel)
                                       (virtueThread (inject_virtue m2 mu angel)).
      Proof.
        intros *. 
        replace (virtueThread (inject_virtue m2 mu angel)) with
            (virtueThread_inject m2 mu (virtueThread angel)) by reflexivity.
        remember (virtueThread angel) as virt. clear - hb virt; revert virt.
        solve_pair.
        eapply inject_perm_perfect_image_dmap.
      Qed.

      
      Definition dmap_valid (m:mem) (dm:delta_map) :=
        forall b ofs p,
          dmap_get dm b ofs = Some p ->
          Mem.valid_block m b.
      
      Definition map_valid (m:mem) (am:access_map) :=
        forall b ofs p,
          am !! b ofs = Some p ->
          Mem.valid_block m b.
      
      Lemma full_inject_dmap:
        forall f m dm,
          Events.injection_full f m ->
          dmap_valid m dm ->
          injects_dmap f dm.
      Proof.
        intros ** ? **.
        eapply H0 in H1.
        eapply H in H1.
        destruct (f b) as [[? ?]|] eqn:HHH; try contradiction.
        econstructor; eauto.
      Qed.
      Definition dmap_valid_pair m:=
        pair1_prop (dmap_valid m).
      Hint Unfold dmap_valid_pair: pair.
      Lemma full_inject_dmap_pair:
        forall f m dm,
          Events.injection_full f m ->
          dmap_valid_pair m dm ->
          injects_dmap_pair f dm.
      Proof. intros ??; solve_pair; eapply full_inject_dmap. Qed.
      
      Lemma join_dmap_valid:
        forall m (a:delta_map),
          bounded_maps.sub_map a (snd (getMaxPerm m)) ->
          dmap_valid m a.
      Proof.
        intros ** ? **.
        
        unfold bounded_maps.sub_map in H.
        eapply strong_tree_leq_spec in H; try constructor.
        instantiate (1:=b) in H.
        eapply dmap_get_Some in H0;
          destruct H0 as [f [H0 ?]].
        rewrite H0 in H.
        destruct ((snd (getMaxPerm m)) ! b) eqn:HH1; try solve[ inversion H].
        specialize (H ofs ltac:(rewrite H1; auto)).
        destruct (o ofs) eqn:HH2; try solve[inversion H].
        assert ((getMaxPerm m) !! b ofs = Some p0).
        { unfold PMap.get; rewrite HH1; assumption. }
        rewrite getMaxPerm_correct in H2.
        unfold permission_at in H2.

        destruct (mem_lemmas.valid_block_dec m b); auto.
        eapply m in n.
        rewrite H2 in n; congruence.
      Qed.
      Lemma join_dmap_valid_pair:
        forall m (aa:Pair delta_map),
          pair1_prop
            (fun a => bounded_maps.sub_map a (snd (getMaxPerm m))) aa ->
          dmap_valid_pair m aa.
      Proof.
        intros ?; solve_pair. apply join_dmap_valid.
      Qed.
      
      
      Hint Unfold injects_map_pair: pair.
      Hint Unfold perm_perfect_image_pair: pair.
      Lemma inject_virtue_perm_perfect_image:
        forall mu m1 m2 angel,
          Mem.inject mu m1 m2 ->
          injects_map_pair mu (virtueLP angel) ->
          perm_perfect_image_pair mu (virtueLP angel)
                                  (virtueLP (inject_virtue m2 mu angel)).
      Proof.
        intros mu m1 m2 angel.
        unfold inject_virtue; simpl.
        remember (virtueLP angel) as VLP; generalize VLP.
        solve_pair.

        pose proof inject_virtue_perm_perfect_image_dmap; eauto.

      Admitted.

      
      Record perm_perfect_virtue f (angel1 angel2:virtue):=
        { permp: perm_perfect_image_pair f (virtueLP angel1) (virtueLP angel2);
          pperm_dmap: perm_perfect_image_dmap_pair
                        f (virtueThread angel1) (virtueThread angel2)
        }.

      Record injects_angel mu angel:=
        { Hinj_map : injects_map_pair mu (virtueLP angel);
          Hinj_dmap : injects_dmap_pair mu (virtueThread angel)}.

      
      Lemma delta_map_join_inject_pair' (m:mem) f:
        forall angel1 angel2 C1 C2
          (Hvirtue_inject: perm_perfect_virtue f angel1 angel2),
          Mem.meminj_no_overlap f m ->
          dmap_vis_filtered_pair (virtueThread angel1) m ->
          permMapLt_pair C1 (getMaxPerm m) ->
          almost_perfect_image_pair f (getMaxPerm m) C1 C2 -> 
          delta_map_join_pair (virtueThread angel1) (virtueLP angel1) C1 ->
          delta_map_join_pair (virtueThread angel2) (virtueLP angel2) C2.
      Proof.
        intros; destruct Hvirtue_inject.
        eapply delta_map_join_inject_pair; eauto.
      Qed.
      Lemma inject_virtue_perm_perfect:
        forall f angel1 m1 m2,
          Mem.inject f m1 m2 ->
          injects_angel f angel1 ->
          option_implication_dmap_access_pair (virtueThread angel1) (getMaxPerm m1) ->
          perm_perfect_virtue f angel1 (inject_virtue m2 f angel1).
      Proof.
        intros ? ? ? ? Hinj [? ?]; econstructor.
        - eapply inject_virtue_perm_perfect_image; eauto.
        - eapply inject_virtue_perm_perfect_image_dmap; eauto.
      Qed.



      
      Definition map_valid_pair m:= pair1_prop (map_valid m).
      Hint Unfold map_valid_pair: pair.
      Lemma full_inject_map:
        forall f m dm,
          Events.injection_full f m ->
          map_valid m dm ->
          injects_map f dm.
      Proof.
        intros ** ? **.
        eapply H0 in H1.
        eapply H in H1.
        destruct (f b) as [[? ?]| ?] eqn:HHH; try contradiction.
        econstructor; eauto.
      Qed.
      Lemma full_inject_map_pair:
        forall f m dm,
          Events.injection_full f m ->
          map_valid_pair m dm ->
          injects_map_pair f dm.
      Proof.
        intros ??; solve_pair. eapply full_inject_map.
      Qed.
      
      (** * End of Lemmas for relase diagram*)
      
      Definition same_visible: mem -> mem -> Prop.
      Admitted.
      Instance same_vis_equiv: (Equivalence same_visible).
      Admitted.

      Infix "++":= seq.cat.

      
      (* Already proven as permMapLt_equiv in mem_equiv.v

        Instance permMapLt_proper :
        Proper (access_map_equiv ==> access_map_equiv ==> iff) permMapLt.
      Proof. solve_proper. Qed.*)
      
      Instance proper_perm_image:
        Proper (Logic.eq ==> access_map_equiv ==> iff) perm_image.
      Proof.
        unfold perm_image.
        setoid_help.proper_iff; setoid_help.proper_intros; subst.
        rewrite <- H0 in *; eauto.
      Qed.
      Instance proper_match_mem:
        Proper (Logic.eq ==> mem_equiv ==> mem_equiv ==> iff) match_mem.
      Proof.
        setoid_help.proper_iff; setoid_help.proper_intros; subst.
        inversion H2; econstructor.
        - rewrite <- H1, <- H0; assumption.
        - pose proof (cur_eqv _ _ H0).
          unfold Cur_equiv in *.
          rewrite <- H; assumption.
        - inv H0; inv H1.
          unfold Cur_equiv in *.
          rewrite <- cur_eqv, <- cur_eqv0; assumption.
      Qed.
      Instance thread_compat_proper sem st i: Proper (Logic.eq ==> Max_equiv ==> iff) (@thread_compat sem st i).
      Proof. setoid_help.proper_iff;
               setoid_help.proper_intros; subst.
             constructor.
             - eapply permMapLt_equiv.
               reflexivity.
               symmetry; apply H0.
               eapply H1.
             - eapply permMapLt_equiv.
               reflexivity.
               symmetry; apply H0.
               eapply H1.
      Qed.
      Lemma cur_equiv_restr_mem_equiv:
        forall (m:mem) p
               (Hlt: permMapLt p (getMaxPerm m)),
          access_map_equiv p (getCurPerm m) ->
          mem_equiv (restrPermMap Hlt) m.
      Proof.
        intros. constructor; eauto.
        - unfold Cur_equiv. etransitivity; eauto.
          eapply getCur_restr.
        - eapply getMax_restr.
        - eapply restr_content_equiv.
      Qed.

      Lemma sub_map_valid:
        forall m (a:access_map),
          (fun a => bounded_maps.sub_map (snd a) (snd (getMaxPerm m))) a ->
          map_valid m a.
      Proof.
        intros ** ? **.
        unfold bounded_maps.sub_map in H.
        eapply strong_tree_leq_spec in H; try constructor.
        instantiate (1:=b) in H.
      (*
                        eapply map_get_Some in H0;
                          destruct H0 as [f [H0 ?]].
                        rewrite H0 in H.
                        destruct ((snd (getMaxPerm m)) ! b) eqn:HH1; try solve[ inversion H].
                        specialize (H ofs ltac:(rewrite H1; auto)).
                        destruct (o ofs) eqn:HH2; try solve[inversion H].
                        assert ((getMaxPerm m) !! b ofs = Some p0).
                        { unfold PMap.get; rewrite HH1; assumption. }
                        rewrite getMaxPerm_correct in H2.
                        unfold permission_at in H2.

                        destruct (mem_lemmas.valid_block_dec m b); auto.
                        eapply m in n.
                        rewrite H2 in n; congruence.*)
      Admitted.
      Lemma sub_map_valid_pair:
        forall m (aa:Pair access_map),
          pair1_prop
            (fun a => bounded_maps.sub_map (snd a) (snd (getMaxPerm m))) aa ->
          map_valid_pair m aa.
      Proof.
        intros m; solve_pair. eapply sub_map_valid.
      Qed.
      
      Lemma full_injects_angel:
        forall mu m1 angel,
          Events.injection_full mu m1 -> 
          sub_map_virtue angel (getMaxPerm m1) ->
          injects_angel mu angel.
      Proof.
        intros * Hfull Hsub_map.
        constructor.
        - eapply full_inject_map_pair; try eassumption.
          eapply sub_map_valid_pair, Hsub_map.
        - eapply full_inject_dmap_pair; try eassumption.
          apply join_dmap_valid_pair, Hsub_map.
      Qed.
      Lemma inject_almost_perfect:
        forall f m1 m2,
          Mem.inject f m1 m2 ->
          almost_perfect_image f
                               (getMaxPerm m1) (getCurPerm m1) (getCurPerm m2).
      Admitted.
      Lemma almost_perfect_image_proper:
        Proper (Logic.eq ==> access_map_equiv
                         ==> access_map_equiv
                         ==> access_map_equiv
                         ==> iff) almost_perfect_image.
      Proof.
        setoid_help.proper_iff;
          setoid_help.proper_intros; subst.
        intros ? **.
        rewrite <- H0, <- H1, <- H2  in *; auto.
      Qed.

      
      Lemma inject_almost_perfect_pair
        : forall (f : meminj) (m1 m2 : mem)
            p11 p12 p21 p22 Hlt11 Hlt12 Hlt21 Hlt22,
          Mem.inject f (@restrPermMap p12 m1 Hlt12) (@restrPermMap p22 m2 Hlt22) ->
          Mem.inject f (@restrPermMap p11 m1 Hlt11) (@restrPermMap p21 m2 Hlt21) ->
          almost_perfect_image_pair f (getMaxPerm m1) (p11,p12) (p21,p22). 
      Proof.
        constructor; simpl.
        - eapply inject_almost_perfect in H0.
          eapply almost_perfect_image_proper; eauto.
          + symmetry. eapply getMax_restr.
          + symmetry. eapply getCur_restr.
          + symmetry. eapply getCur_restr.
        - eapply inject_almost_perfect in H.
          eapply almost_perfect_image_proper; eauto.
          + symmetry. eapply getMax_restr.
          + symmetry. eapply getCur_restr.
          + symmetry. eapply getCur_restr.
      Qed.

      Lemma mem_access_max_equiv:
        forall m1 m2, Mem.mem_access m1 =
                 Mem.mem_access m2 ->
                 Max_equiv m1 m2.
      Proof. intros ** ?.
             unfold getMaxPerm; simpl.
             rewrite H; reflexivity.
      Qed.
      Lemma mem_access_cur_equiv:
        forall m1 m2, Mem.mem_access m1 =
                 Mem.mem_access m2 ->
                 Cur_equiv m1 m2.
      Proof. intros ** ?.
             unfold getCurPerm; simpl.
             rewrite H; reflexivity.
      Qed.
      Lemma sub_map_filtered:
        forall m a,
          bounded_maps.sub_map a (snd (getMaxPerm m)) ->
          dmap_vis_filtered a m.
      Proof.
        unfold dmap_vis_filtered, Mem.perm.
        Lemma sub_map_lt:
          forall {A B} dmap amap,
            @bounded_maps.sub_map A B dmap (amap) ->
            forall b,
              bounded_maps.fun_leq (dmap ! b) (amap ! b).
        Proof.
          intros. eapply strong_tree_leq_spec; try constructor.
          eapply H.
        Qed.
        intros. 
        intros; eapply sub_map_lt in H.
        instantiate(1:=b) in H.
        rewrite_getPerm.
        unfold PMap.get.
        unfold dmap_get, PMap.get in H0.
        simpl in H0.
        match_case in H0.
        destruct ((snd (getMaxPerm m)) ! b) eqn:HMax;
          try solve[inv H].
        simpl in H.
        exploit H.
        - destruct (o ofs) eqn:HH; try congruence.
          rewrite HH; auto.
        - intros HH; destruct (o0 ofs); inv HH.
          constructor.
      Qed.
      Lemma sub_map_filtered_pair:
        forall m a,
          pair21_prop bounded_maps.sub_map a (snd (getMaxPerm m)) ->
          dmap_vis_filtered_pair a m.
      Proof. intros m; solve_pair.
             eapply sub_map_filtered. Qed.

      
      
      Lemma interference_same_visible:
        forall m m' lev, mem_interference m lev m' ->
                         same_visible m m'.
      Admitted.
      Lemma asm_step_determ:
        forall g_env s1 lev s2 s2',
          Asm.step g_env s1 lev s2 -> 
          Asm.step g_env s1 lev s2' ->
          s2 = s2'.
      Admitted.
      
      (* this lemma should be included in the self simulation. *)
      Lemma same_visible_at_external:
        forall C (sem: semantics.CoreSemantics C mem), 
          self_simulation _ sem ->
          forall c m m' f_and_args,
            same_visible m m' ->
            semantics.at_external sem c m = Some f_and_args->
            semantics.at_external sem c m' = Some f_and_args.
      Admitted.
      
      
      Definition permMapLt_range (perms:access_map) b lo hi p:=
        forall ofs : Z, lo <= ofs < hi ->
                        Mem.perm_order'' (perms !! b ofs) p.

      (*Lookup : 
                setPermBlock_range_perm  *)
      Lemma permMapLt_setPermBlock:
        forall perm1 perm2 op b ofs sz,
          permMapLt_range perm2 b ofs (ofs + Z.of_nat sz) op  ->
          permMapLt perm1 perm2 ->
          permMapLt (setPermBlock op b ofs perm1 sz) perm2.
      Proof. Admitted.
      
      (* Lemma mem_compatible_lock_writable:
        (* This might need to be included into mem_compatible.
                   That would break many things, but all those things should be
                   easy to fix.
       *)
        forall {sem TP} tp m,
          @mem_compatible sem TP tp m ->
          forall (l : Address.address) (rmap : lock_info),
            ThreadPool.lockRes tp l = Some rmap ->
            permMapLt_range (getMaxPerm m) (fst l) (snd l)
                            ((snd l) + LKSIZE) (Some Writable).
      Proof.
      Admitted.*)
      
      Lemma address_inject_max:
        forall f m1 m2 b1 ofs1 b2 delta p,
          Mem.inject f m1 m2 ->
          Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Max p ->
          f b1 = Some (b2, delta) ->
          unsigned (add ofs1 (Ptrofs.repr delta)) =
          unsigned ofs1 + delta.
      Proof.
        intros.
        assert (Mem.perm m1 b1 (Ptrofs.unsigned ofs1) Max Nonempty)
          by eauto with mem.
        exploit Mem.mi_representable; eauto. intros [A B].
        assert (0 <= delta <= Ptrofs.max_unsigned).
        generalize (Ptrofs.unsigned_range ofs1). omega.
        unfold Ptrofs.add. repeat rewrite Ptrofs.unsigned_repr; omega.
      Qed.
      Lemma Cur_equiv_restr:
        forall p1 p2 m1 m2 Hlt1 Hlt2,
          access_map_equiv p1 p2 ->
          Cur_equiv (@restrPermMap p1 m1 Hlt1)
                    (@restrPermMap p2 m2 Hlt2).
      Proof. unfold Cur_equiv; intros.
             do 2 rewrite getCur_restr; assumption. Qed.
      Lemma Max_equiv_restr:
        forall p1 p2 m1 m2 Hlt1 Hlt2,
          Max_equiv m1 m2 ->
          Max_equiv (@restrPermMap p1 m1 Hlt1)
                    (@restrPermMap p2 m2 Hlt2).
      Proof. unfold Max_equiv; intros.
             do 2 rewrite getMax_restr; assumption. Qed.

      

      Lemma mem_compat_Max:
        forall Sem Tp st m m',
          Max_equiv m m' ->
          Mem.nextblock m = Mem.nextblock m' ->
          @mem_compatible Sem Tp st m ->
          @mem_compatible Sem Tp st m'.
      Proof.
        intros * Hmax Hnb H.
        assert (Hmax':access_map_equiv (getMaxPerm m) (getMaxPerm m'))
          by eapply Hmax.
        constructor; intros;
          repeat rewrite <- Hmax';
          try eapply H; eauto.
        unfold Mem.valid_block; rewrite <- Hnb;
          eapply H; eauto.
      Qed.
      Lemma store_max_equiv:
        forall sz m b ofs v m',
          Mem.store sz m b ofs v = Some m' ->
          Max_equiv m m'.
      Proof.
        intros. intros ?.
        extensionality ofs'.
        eapply memory_lemmas.MemoryLemmas.mem_store_max.
        eassumption.
      Qed.
      Lemma mem_compatible_updLock:
        forall Sem Tp m st st' l lock_info,
          permMapLt_pair lock_info (getMaxPerm m) ->
          Mem.valid_block m (fst l) ->
          st' = ThreadPool.updLockSet(resources:=dryResources) st l lock_info ->
          @mem_compatible Sem Tp st m ->
          @mem_compatible Sem Tp st' m.
      Proof.
        intros * Hlt Hvalid HH Hcmpt.
        subst st'; constructor; intros.
        - erewrite ThreadPool.gLockSetRes. apply Hcmpt.
        - (*Two cases, one of which goes by Hlt*)
          admit.
        - (*Two cases, one of which goes by Hvalid*)
          admit.
      Admitted.
      Lemma mem_compatible_updthread:
        forall Sem Tp m st st' i (cnt:ThreadPool.containsThread st i) c res,
          permMapLt_pair res (getMaxPerm m) ->
          st' = ThreadPool.updThread(resources:=dryResources) cnt c res ->
          @mem_compatible Sem Tp st m ->
          @mem_compatible Sem Tp st' m.
      Proof.
        intros * Hlt HH Hcmpt.
        subst st'; constructor; intros.
        - (*Two cases, one of which goes by Hlt*)
          admit.
        - rewrite ThreadPool.gsoThreadLPool in H.
          eapply Hcmpt; eassumption.
        -  rewrite ThreadPool.gsoThreadLPool in H.
           eapply Hcmpt; eassumption.
      Admitted.
      
      Ltac same_types H1 H2:=
        match type of H1 with
        | ?T1 =>
          match type of H2 with
          | ?T2 =>
            let HH:=fresh "HH" in 
            assert (HH:T1 = T2) by reflexivity;
            try (dependent rewrite HH in H1;
                 clear HH)
          end
        end.

      Notation vone:= (Vint Int.one).
      Notation vzero:= (Vint Int.zero).
      
      Inductive release: val -> mem -> delta_perm_map ->  mem -> Prop  :=
      | ReleaseAngel:
          forall b ofs m dpm m' m_release
            (* change the permission to be able to lock *)
            lock_perms Hlt,
            Mem.store AST.Mint32 (@restrPermMap lock_perms m Hlt)
                      b (unsigned ofs) vone = Some m_release ->
            (* return to the new, transfered permissions*)
            forall new_perms Hlt',
              (* Need to relate new_perms and dpm *)
              new_perms = computeMap (getCurPerm m) dpm ->
              m' = @restrPermMap new_perms m_release Hlt' ->
              release (Vptr b ofs) m dpm m'.
      Inductive acquire: val -> mem -> delta_perm_map ->  mem -> Prop  :=
      | AcquireAngel:
          forall b ofs m dpm m' m_release
                 (* change the permission to be able to lock *)
                 lock_perms Hlt,
            Mem.store AST.Mint32 (@restrPermMap lock_perms m Hlt)
                      b (unsigned ofs) vzero = Some m_release ->
            (* return to the new, transfered permissions*)
            forall new_perms Hlt',
              (* Need to relate new_perms and dpm *)
              new_perms = computeMap (getCurPerm m) dpm ->
              m' = @restrPermMap new_perms m_release Hlt' ->
              acquire (Vptr b ofs) m dpm m'.

      Inductive extcall_release: Events.extcall_sem:=
      | ExtCallRelease:
          forall ge m m' m'' m''' b ofs e dpm e',
            mem_interference m e m' ->
            release (Vptr b ofs) m' dpm m'' ->
            mem_interference m'' e' m''' ->
            extcall_release ge (Vptr b ofs :: nil) m
                            (Events.Event_acq_rel e dpm e' :: nil)
                            Vundef m'''.
      
      Inductive extcall_acquire: Events.extcall_sem:=
      | ExtCallAcquire:
          forall ge m m' m'' m''' b ofs e dpm e',
            mem_interference m e m' ->
            acquire (Vptr b ofs) m' dpm m'' ->
            mem_interference m'' e' m''' ->
            extcall_acquire ge (Vptr b ofs :: nil) m
                            (Events.Event_acq_rel e dpm e' :: nil)
                            Vundef m'''.
      Lemma extcall_properties_release:
        Events.extcall_properties extcall_release UNLOCK_SIG.
      Proof.
      (* this is given axiomatically in compcert, 
                     but we must prove it*)
      Admitted.
      Lemma extcall_properties_acquire:
        Events.extcall_properties extcall_acquire LOCK_SIG.
      Proof.
      (* this is given axiomatically in compcert, 
                     but we must prove it*)
      Admitted. 
      Axiom ReleaseExists:
        forall ge args m ev r m',
          Events.external_functions_sem "release" UNLOCK_SIG
                                        ge args m ev r m' =
          extcall_release ge args m ev r m'. 
      Axiom AcquireExists:
        forall ge args m ev r m',
          Events.external_functions_sem "acquire" LOCK_SIG
                                        ge args m ev r m' =
          extcall_acquire ge args m ev r m'.

      Lemma interference_consecutive: forall m lev m',
          mem_interference m lev m' ->
          consecutive (Mem.nextblock m) lev.
      Proof.
        intros. induction lev; try econstructor.
      Admitted.

      Lemma at_external_mem_interference:
        forall C Sem m lev m' th_state,
          self_simulation C Sem ->
          mem_interference m lev m' ->
          semantics.at_external Sem th_state m =
          semantics.at_external Sem th_state m'.
      Proof.
        intros.
        destruct_lhs.
        - exploit same_visible_at_external; eauto.
          + eapply interference_same_visible; eassumption.
        - destruct_rhs; auto.
          exploit same_visible_at_external; eauto.
          + symmetry. eapply interference_same_visible; eassumption.
          + intros HH; rewrite HH in Heqo; congruence.
      Qed.
      Definition all_threads_inject_perm
                 (f:meminj) {n m} (st1: ThreadPool n) (st2: ThreadPool m) m1 m2:=
        forall (i : nat) (cnt1 : containsThread st1 i) (cnt2 : containsThread st2 i)
          (Hlt1 : permMapLt (thread_perms  _ _ cnt1) (getMaxPerm m1))
          (Hlt2 : permMapLt (thread_perms  _ _ cnt2) (getMaxPerm m2)),
          Mem.inject f (restrPermMap Hlt1) (restrPermMap Hlt2).

      Definition all_threads_lock_perm_preimage
                 (f:meminj) {n m} (st1: ThreadPool n) (st2: ThreadPool m):=
        forall (i : nat) (cnt1 : containsThread st1 i) (cnt2 : containsThread st2 i),
          perm_preimage f (lock_perms  _ _ cnt1) (lock_perms  _ _ cnt2).
      Lemma perm_preimage_updLockSet:
        forall f n m st1 st2 adr1 adr2 lock_perms1 lock_perms2,
          @all_threads_lock_perm_preimage f n m st1 st2 ->
          all_threads_lock_perm_preimage f
                                         (updLockSet st1 adr1 lock_perms1)
                                         (updLockSet st2 adr2 lock_perms2).
      Proof.
        intros ** ???.
        unfold CompileOneThread.lock_perms.
        unshelve (do 2 erewrite gLockSetRes); try eapply H.
        all : unshelve eapply cntUpdateL'; auto.
      Qed.
      
      Lemma perm_preimage_updThread:
        forall f n m st1 st2 c1 c2 thred_perms1 thred_perms2,
          @all_threads_lock_perm_preimage f n m st1 st2 ->
          perm_preimage f (snd thred_perms1) (snd thred_perms2) ->
          forall j cntj1 cntj2,
            all_threads_lock_perm_preimage f
                                           (@updThread _ _ j st1 cntj1 c1 thred_perms1)
                                           (@updThread _ _ j st2 cntj2 c2 thred_perms2).
      Proof.
        intros ** ???.
        unfold CompileOneThread.lock_perms.
        destruct (Nat.eq_dec i j).
        - subst.
          do 2 erewrite gssThreadRes; auto.
        - unshelve (do 2 (erewrite gsoThreadRes; auto)); try eapply H.
          all : unshelve eapply cntUpdate'; auto.
      Qed.
      
      Lemma perm_preimage_compute:
        forall (f:meminj) perm1 perm2 dmap1 dmap2,
          perm_preimage f perm1 perm2 ->
          perm_perfect_image_dmap f dmap1 dmap2 ->
          perm_preimage f (computeMap perm1 dmap1) (computeMap perm2 dmap2).
      Proof.
        unfold perm_preimage; intros.
        destruct (dmap_get dmap2 b2 ofs_delt) eqn:HH.
        - exploit (ppre_perfect_image_dmap H0).
          { rewrite HH; constructor. }
          intros (?&?&?&?&?&?).
          repeat (econstructor; eauto).
          rewrite HH in H4; symmetry in H4.
          eapply dmap_get_copmute_Some in HH.
          eapply dmap_get_copmute_Some in H4.
          rewrite HH, H4; reflexivity.
        - eapply dmap_get_copmute_None in HH as HH';
            rewrite HH' in H1.
          eapply H in H1 as (b1&ofs&delt&?&?&?).
          repeat (econstructor; eauto).
          rewrite HH', H3.
          symmetry.
          destruct (dmap_get dmap1 b1 ofs) eqn: HH1.
          + revert HH; subst ofs_delt.
            intros.
            destruct (dmap_get dmap1 b1 ofs) eqn:Heq1.
            { exploit (p_image_dmap H0).
              rewrite Heq1; repeat constructor.
              intros; normal. unify_injection. inv HH1.
              rewrite Heq1 in H4. rewrite <- H4 in HH; congruence. }
            congruence.
            
          + eapply dmap_get_copmute_None; eassumption.
      Qed.

      Lemma injection_full_nextblock:
        forall f m m',
          Mem.nextblock m = Mem.nextblock m' ->
          Events.injection_full f m ->
          Events.injection_full f m'.
      Proof.
        intros ** ? **.
        eapply H0. unfold Mem.valid_block.
        rewrite H; auto.
      Qed.
      
      (* Lemmas end *)
      
      
      Definition expl_restrPermMap p m Hlt:=
        @restrPermMap p m Hlt.
      Lemma expl_restr:
        forall p m Hlt,
          restrPermMap Hlt = expl_restrPermMap p m Hlt.
      Proof. reflexivity. Qed.


      Lemma list_inject_weaken: 
        forall j lev1 lev2,
          Events.list_inject_mem_effect_strong j lev1 lev2 ->
          Events.list_inject_mem_effect j lev1 lev2.
      Proof.
        intros. inversion H; subst; constructor.
      Admitted.

      Lemma Asm_step_consecutive:
        forall ge st m t st',
          Asm.step ge (Asm.set_mem st m) t st' ->
          forall lev dpm lev' t',
            t = Events.Event_acq_rel lev dpm lev' :: t' ->
            consecutive (Mem.nextblock m) (lev++lev').
      Admitted.
      
      Lemma permMapLt_range_mem:
        forall perm b lo hi p m,
          permMapLt_range perm b lo hi (Some p) ->
          forall (Hlt:permMapLt perm (getMaxPerm m)),
            Mem.range_perm (restrPermMap Hlt) b lo hi Cur p.
      Proof.
        unfold Mem.range_perm, Mem.perm; intros.
        rewrite_getPerm. rewrite getCur_restr.
        eapply H; assumption.
      Qed.

      Lemma load_inject':
        forall (f : meminj) (m1 m2 : mem) (chunk : AST.memory_chunk)
               (b1 : block) (ofs : Z) (b2 : block) (delta : Z) 
               (v1 v2 : val),
          Mem.inject f m1 m2 ->
          Mem.load chunk m1 b1 ofs = Some v1 ->
          f b1 = Some (b2, delta) ->
          Val.inject f v1 v2 ->
          v1 <> Vundef ->
          Mem.load chunk m2 b2 (ofs + delta) = Some v2.
      Proof.
        intros. exploit Mem.load_inject; eauto.
        intros (?&?&?).
        replace v2 with x; auto.
        clear - H3 H5 H2.
        inv H5; inv H2; auto.
        - unify_injection; reflexivity.
        -  congruence.
      Qed.
      Lemma restr_proof_irr':
        forall (perm1 perm2 : access_map) (m1 m2 : mem)
               (Hlt1 : permMapLt perm1 (getMaxPerm m1))
               (Hlt2 : permMapLt perm2 (getMaxPerm m2)),
          perm1 = perm2 ->
          m1 = m2 ->
          restrPermMap Hlt1 = restrPermMap Hlt2.
      Proof. intros. subst. apply restr_proof_irr. Qed.

      
      Inductive lock_update_mem_strict b ofs m m': val -> Prop :=
      | Build_lock_update_mem_strict:
          forall vstore
                 (Haccess: Mem.range_perm m b ofs (ofs + LKSIZE) Cur Writable)
                 (Hstore: Mem.store AST.Mint32 m b ofs vstore = Some m'),
            lock_update_mem_strict b ofs m m' vstore.
      
      Inductive lock_update_mem_strict_load b ofs lock_perm m m': val -> val -> Prop :=
      | Build_lock_update_mem_strict_load:
          forall lock_mem_lt vload vstore
                 (Hwritable_lock1 : writable_lock b ofs lock_perm m),
            let lock_mem:= @restrPermMap lock_perm m lock_mem_lt in
            let m_writable_lock_1:= restrPermMap Hwritable_lock1 in
            forall (Haccess: Mem.range_perm lock_mem b ofs (ofs + LKSIZE) Cur Readable)
                   (Hload: Mem.load AST.Mint32 lock_mem b ofs = Some vload)
                   (Hstore: Mem.store AST.Mint32 m_writable_lock_1 b ofs vstore = Some m'),
              lock_update_mem_strict_load b ofs lock_perm m m' vload vstore.
      
      Definition fullThreadUpdate {sem} st i cnt th_st new_perms adr  :=
        (updLockSet
           (@updThread dryResources sem i st cnt th_st (fst new_perms)) adr (snd new_perms)).
      Definition fullThUpd_comp {sem} st i cnt th_st (angel: virtue) adr  :=
        @fullThreadUpdate
          sem st i cnt th_st
          (computeMap_pair (getThreadR cnt) (virtueThread angel), virtueLP angel) adr.
      
      Lemma inject_virtue_sub_map_pair:
        forall (m1 m2 : mem)
          (mu : meminj)
          (angel : virtue)
          perm1 perm2 Hlt1 Hlt2,
          Mem.inject mu (@restrPermMap perm1 m1 Hlt1 ) 
                     (@restrPermMap perm2 m2 Hlt2 ) ->
          sub_map_pair (virtueThread angel) (snd (getMaxPerm m1)) ->
          sub_map_pair (virtueThread (inject_virtue m2 mu angel)) (snd (getMaxPerm m2)).
      Proof.
        intros.
        remember (snd (getMaxPerm m2)) as TEMP.
        destruct angel as (virtueT&?); destruct virtueT as (virtueT_A & virtueT_B).
        simpl; subst.
        constructor; eapply inject_virtue_sub_map; first [eapply H0|eassumption].
      Qed.

      Lemma lock_update_mem_strict_inject:
        forall f b b' ofs delt m1 m2 m1' vl,
        forall (Hinj_b : f b = Some (b', delt))
          (Hinj_lock: Mem.inject f m1 m2),
          lock_update_mem_strict b ofs m1 m1' (Vint vl) ->
          exists m2',
            lock_update_mem_strict b' (ofs+ delt) m2 m2' (Vint vl) /\
            Mem.inject f m1' m2'.
      Proof.
        intros; inv H.
        eapply Mem.store_mapped_inject in Hstore as (m2'&Hstore2&Hinj'); eauto.
        eexists; split; eauto.
        econstructor; eauto.
        replace (ofs + delt + LKSIZE) with ((ofs + LKSIZE) + delt).
        - eapply Mem.range_perm_inject; eauto.
        - omega.
      Qed.

      Lemma address_inj_store':
        forall mu m1 m2' m1' b1 b2 ofs delt v,
          mu b1 = Some (b2, delt) ->
          Mem.inject mu m1' m2' ->
          Mem.store AST.Mint32 m1 b1 (unsigned ofs) v = Some m1' ->
          unsigned (add ofs (repr delt)) = unsigned ofs + delt.
      Proof.
        intros * Hinj_b1 Hinj Hstore.
        eapply Mem.address_inject; eauto.
        
        eapply Mem.perm_store_1; eauto.
        eapply Mem.store_valid_access_3 in Hstore.
        destruct Hstore as [Hperm ?].
        specialize (Hperm (unsigned ofs)).
        eapply Hperm.
        replace unsigned with unsigned by reflexivity.
        pose proof (size_chunk_pos AST.Mint32).
        omega.
      Qed.
      Lemma address_inj_store:
        forall mu m1 m2 m1' b1 b2 ofs delt v,
          mu b1 = Some (b2, delt) ->
          Mem.inject mu m1 m2 ->
          Mem.store AST.Mint32 m1 b1 (unsigned ofs) (Vint v) = Some m1' ->
          unsigned (add ofs (repr delt)) = unsigned ofs + delt.
      Proof.
        intros * Hinj_b1 Hinj Hstore.
        exploit Mem.store_mapped_inject; eauto.
        intros (?&_&?). clear Hinj.
        eapply address_inj_store'; eauto.
      Qed.
      Lemma address_inj_lock_update:
        forall f b b' ofs delt m1 m1' m2' vs,
        forall (Hinj_b : f b = Some (b', delt)),
        forall (Hinj_lock: Mem.inject f m1' m2'),
          lock_update_mem_strict b (unsigned ofs) m1 m1' (Vint vs) ->
          unsigned (add ofs (repr delt)) = unsigned ofs + delt.
      Proof.
        intros * Hinj_b Minj HH.
        inv HH; eapply address_inj_store'; eassumption.
      Qed.
      Lemma address_inj_lock_update_load:
        forall f b b' ofs delt perms1 m1 m1' m2' vl vs,
        forall (Hinj_b : f b = Some (b', delt)),
        forall (Hinj_lock: Mem.inject f m1' m2'),
          lock_update_mem_strict_load b (unsigned ofs) perms1 m1 m1' (Vint vl) (Vint vs) ->
          unsigned (add ofs (repr delt)) = unsigned ofs + delt.
      Proof.
        intros * Hinj_b Minj HH.
        inv HH; eapply address_inj_store'; eassumption.
      Qed.
      
      Lemma permMapLt_setPermBlock2:
        forall op b ofs perm1 perm2 sz,
          (0 < sz)%nat-> 
          permMapLt perm1 perm2 ->
          permMapLt (setPermBlock op b ofs perm1 sz) (setPermBlock op b ofs perm2 sz).
      Proof.
        intros ** b0 ofs0.
        destruct_address_range b ofs b0 ofs0 sz.
        - do 2 (rewrite setPermBlock_same; auto); apply po_refl.
        - eapply Intv.range_notin in Hrange;
            try (simpl; omega).
          do 2 (erewrite setPermBlock_other_1; auto).
        - do 2 (rewrite setPermBlock_other_2; auto).
      Qed.
      
      Lemma lock_update_mem_strict_load_inject:
        forall f b b' ofs delt perms1 perms2 m1 m2 m1' vl vs,
        forall (Hinj_b : f b = Some (b', delt))
               Hlt1 Hlt2
               (Hinj_lock: Mem.inject f (restrPermMap' perms1 m1 Hlt1)
                                      (restrPermMap' perms2 m2 Hlt2)),
          lock_update_mem_strict_load b ofs perms1 m1 m1' (Vint vl) (Vint vs) ->
          inject_lock' LKSIZE f b ofs m1 m2 ->
          exists m2',
            lock_update_mem_strict_load b' (ofs+ delt) perms2 m2 m2' (Vint vl) (Vint vs) /\
            Mem.inject f m1' m2'.
      Proof.
        intros. inv H.
        rewrite <- (restr_proof_irr_equiv _ _ lock_mem_lt),
        <- (restr_proof_irr_equiv _ _ Hlt2) in Hinj_lock.
        assert (writable_lock b' (ofs + delt) perms2 m2).
        { eapply writable_lock_inject_restr; eauto. }

        
        eapply Mem.store_mapped_inject in Hstore; eauto.
        - destruct Hstore as (m2'&Hstore2&Hinj2).
          exists m2'; split; auto.
          unshelve econstructor; eauto.
          + match goal with
              |- context[?a + ?b + ?c]=>
              replace (a + b + c) with ((a + c) + b) by omega   
            end.
            eapply Mem.range_perm_inject; eauto.
          + eapply Mem.load_inject in Hload; eauto.
            * destruct Hload as (v2 & ? & HH).
              inv HH; eauto.
        - simpl.
          eapply mem_inject_equiv; 
            try (eapply setPermBlock_mem_inject; try eapply Hinj_lock);
            eauto.
          { subst m_writable_lock_1 lock_mem.
            etransitivity; [|eapply restrPermMap_idempotent].
            apply restrPermMap_equiv; try reflexivity.
            eapply setPermBlock_access_map_equiv; eauto.
            rewrite getCur_restr. reflexivity.
            econstructor; auto.  }
          { etransitivity; [|eapply restrPermMap_idempotent].
            apply restrPermMap_equiv; try reflexivity.
            eapply setPermBlock_access_map_equiv; eauto.
            simpl; rewrite getCur_restr. reflexivity.
            econstructor; auto. }
          
          Unshelve.
          all: unfold writable_lock in *;
            try rewrite getCur_restr;
            try rewrite getMax_restr;
            try assumption.
      Qed.
      

      Inductive strict_evolution_diagram cd mu code1 m1 m1' code2 m2':=
      | build_stric_diagram:
          forall lev1 lev2 j m2
                 (Hcomp_match : compiler_match cd j code1 m1 code2 m2)
                 (Hstrict_evolution : strict_injection_evolution j mu lev1 lev2)
                 (Hinterference1 : mem_interference m1 lev1 m1')
                 (Hinterference2 : mem_interference m2 lev2 m2'),
            strict_evolution_diagram cd mu code1 m1 m1' code2 m2'.

      
      
      Inductive interference_diagram_atx i code1 code2 m1 f' m1' m2' :=
      | build_inter_diagram_atx:
          forall f FUN m2 args1 args2  lev1 lev2
                 (Hinj: Mem.inject f m1 m2)
                 (Hinj': Mem.inject f' m1' m2')
                 (Hstrict_evolution: strict_injection_evolution f f' lev1 lev2)
                 (Hmatch_states: compiler_match i f code1 m1 code2 m2)
                 (*Hmatch_states': compiler_match i f' code1 m1' code2 m2'*)
                 (* Probably can also add this, but seems like I don't need it*)
                 (Hinterference1 : mem_interference m1 lev1 m1')
                 (Hinterference2 : mem_interference m2 lev2 m2')
                 (Hat_external1: Clight.at_external (Clight.set_mem code1 m1) =
                                 Some (FUN, args1))
                 (Hat_external1': Clight.at_external (Clight.set_mem code1 m1') =
                                  Some (FUN, args1))
                 (Hat_external2: Asm.at_external Asm_g (Asm.set_mem code2 m2) =
                                 Some (FUN, args2))
                 (Hat_external2': Asm.at_external Asm_g (Asm.set_mem code2 m2') =
                                  Some (FUN, args2))
                 (Hinj_args: Val.inject_list f args1 args2)
          , interference_diagram_atx i code1 code2 m1 f' m1' m2'.

      Lemma lock_update_mem_strict_mem_update:
        forall b ofs m m' vstore,
          lock_update_mem_strict b ofs m m' vstore ->
          lock_update_mem m (b, ofs) (Fragment vstore Q32 1) m'.
      Proof.
        intros. inv H.
        econstructor.
        - intros ? ? HH. unfold same_content_in.
          eapply Mem.store_mem_contents in Hstore.
          rewrite Hstore.
          simpl in HH.
          admit.
      Admitted.
      Lemma lock_update_mem_strict_load_mem_update:
        forall b ofs p m m' vload vstore,
          lock_update_mem_strict_load b ofs p m m' vload vstore ->
          lock_update_mem m (b, ofs) (Fragment vstore Q32 1) m'.
      Proof.
        intros. inv H.
        econstructor.
        - intros ? ? HH. unfold same_content_in.
          eapply Mem.store_mem_contents in Hstore.
          rewrite Hstore.
          simpl in HH.
          admit.
      Admitted.
      Inductive strict_evolution_diagram' cd mu code1 m1 m1' code2 m2':=
      | build_stric_diagram':
          forall lev1 lev2 j m2
                 (Hcomp_match : compiler_match cd j code1 m1 code2 m2)
                 (Hstrict_evolution : strict_injection_evolution j mu lev1 lev2)
                 (Hinterference1 : mem_interference m1 lev1 m1')
                 (Hinterference2 : mem_interference m2 lev2 m2'),
            strict_evolution_diagram' cd mu code1 m1 m1' code2 m2'.
      Lemma retroactive_int_diagram_atx:
        forall  i code1 code2 m1 f' m1' m2' FUN 
                (Hstrict: strict_evolution_diagram i f' code1 m1 m1' code2 m2')
                (Hinj': Mem.inject f' m1' m2')
                args1
                (Hat_external1': Clight.at_external (Clight.set_mem code1 m1') =
                                 Some (FUN, args1)),
          interference_diagram_atx i code1 code2 m1 f' m1' m2'.
      Proof.
        intros.
        inversion Hstrict.
        pose proof (same_visible_at_external _ _ Cself_simulation) as Hsame1.
        pose proof (same_visible_at_external _ _ Aself_simulation) as Hsame2.
        eapply Hsame1 in Hat_external1' as Hat_external1.
        2: { symmetry. eapply interference_same_visible. eassumption. }
        eapply (Injsim_atxX compiler_sim) in Hat_external1 as HH; eauto.
        evar (args2: list val).

        assert (Hat_external2: Smallstep.at_external
                                 (Smallstep.part_sem (Asm.semantics Asm_program))
                                 (Smallstep.set_mem code2 m2) = Some (FUN, args2)).
        { (* this comes from HH, but cant destruct existensials *)
          admit. } simpl in Hat_external2.
        assert (Hinj: Val.inject_list j args1 args2).
        { (* this comes from HH, but cant destruct existensials *)
          admit. }
        clear HH.
        eapply Hsame2 in Hat_external2 as Hat_external2'.
        2: { eapply interference_same_visible; eassumption. }
        econstructor; eauto.
        - !goal (Mem.inject j m1 m2).
          eapply (Injfsim_match_meminjX compiler_sim)
            in Hcomp_match.
          destruct code1, code2; eapply Hcomp_match.

          Unshelve.
          assumption.
      Admitted.
      
      
      Lemma xmap_compose:
        forall A B C t f1 f2 p,
          @PTree.xmap B C f2 (@PTree.xmap A B f1 t p) p =
          (@PTree.xmap A C (fun p x => f2 p (f1 p x)) t p).
      Proof. induction t0.
             - reflexivity.
             - simpl; intros.
               f_equal.
               + eapply IHt0_1.
               + destruct o; reflexivity.
               + eapply IHt0_2.
      Qed.
      Lemma store_max_eq:
        forall cnk  m b ofs v m',
          Mem.store cnk  m b ofs v = Some m' ->
          getMaxPerm m = getMaxPerm m'.
      Proof.
        intros.
        Transparent Mem.store.
        unfold Mem.store in H; simpl in *.
        destruct (Mem.valid_access_dec m cnk b ofs Writable); try discriminate.
        inversion H. reflexivity.
      Qed.
      Lemma cur_lt_max:
        forall m, permMapLt (getCurPerm m) (getMaxPerm m).
      Proof.
        intros ** ??.
        rewrite getCurPerm_correct, getMaxPerm_correct; eapply m.
      Qed.
      Lemma restr_Max_eq:
        forall p m Hlt,
          getMaxPerm (@restrPermMap p m Hlt) = getMaxPerm m.  
      Proof.
        intros.
        unfold getMaxPerm, restrPermMap.
        simpl. unfold PMap.map; simpl.
        f_equal.
        repeat rewrite map_map1; simpl.
        unfold PTree.map.
        rewrite xmap_compose.
        reflexivity.
      Qed.
      Definition setPermBlock_pair b ofs:=
        pair3 (fun p => setPermBlock p b ofs).
      Hint Unfold setPermBlock_pair: pair.
      
      Inductive set_new_mems: block -> Z -> (Pair access_map) -> nat -> (Pair access_map) -> Prop:=
      | Build_set_new_mems:
          forall b ofs res LKSIZE new_perms
                 (Hset_block: setPermBlock_pair
                                b ofs (Some Nonempty, Some Writable)
                                res (pair0 LKSIZE) = new_perms),
            set_new_mems b ofs res LKSIZE new_perms.
      
      Definition perm_interval m b ofs size k p:=
        Mem.range_perm m b ofs (ofs+size) k p.
      
      Definition setPermBlock_var_pair b ofs size:=
        pair2 (fun p pmap => setPermBlock_var p b ofs pmap size).
      Hint Unfold setPermBlock_var_pair: pair.
      
      Lemma setPermBlock_setPermBlock_var:
        forall v, setPermBlock v = setPermBlock_var (fun _ : nat => v).
      Proof.
        intros v.
        extensionality b.
        extensionality ofs.
        extensionality pmap.
        extensionality n.
        unfold setPermBlock, setPermBlock_var.
        induction n; auto.
        simpl. rewrite IHn. reflexivity.
      Qed.
      
      Definition remLockfFullUpdate {sem} st i cnt th_st new_perms adr  :=
        (remLockSet
           (@updThread dryResources sem i st cnt th_st (new_perms)) adr).
      
      (** *step_diagram_Self*)

      (* TODO: move these to the definition of concur? *)
      Ltac get_mem_compatible:=
        match goal with
          [CMatch : concur_match _ ?mu ?st1 ?m1 ?st2 ?m2,
                    cnt1 : containsThread ?st1 ?tid,
                           cnt2 : containsThread ?st2 ?tid |- _ ] =>
          let Hcmpt1:=fresh "Hcmpt1" in 
          let Hcmpt2:=fresh "Hcmpt2" in 
          pose proof (memcompat1 CMatch) as Hcmpt1;
          pose proof (memcompat2 CMatch) as Hcmpt2;
          (* the thread compat *)
          let thread_compat1:=fresh "thread_compat1" in 
          let thread_compat2:=fresh "thread_compat2" in 
          assert (thread_compat1:thread_compat _ _ cnt1 m1)
            by (apply mem_compatible_thread_compat; auto);
          assert (thread_compat2:thread_compat _ _ cnt2 m2)
            by (apply mem_compatible_thread_compat; auto)
        end.
      
      Ltac get_thread_mems:=
        match goal with
          [CMatch : concur_match _ ?mu ?st1 ?m1 ?st2 ?m2,
                    thread_compat1:thread_compat _ _ ?cnt1 ?m1,
                                   thread_compat2:thread_compat _ _ ?cnt2 ?m2 |- _ ] =>
          (* Inequalities for the four perms*)
          let Hlt_th1:=fresh "Hlt_th1" in 
          let Hlt_th2:=fresh "Hlt_th2" in 
          let Hlt_lk1:=fresh "Hlt_lk1" in 
          let Hlt_lk2:=fresh "Hlt_lk2" in
          assert (Hlt_th1: permMapLt (thread_perms _ _ cnt1) (getMaxPerm m1))
            by eapply (memcompat1 CMatch);
          assert (Hlt_th2: permMapLt (thread_perms _ _ cnt2) (getMaxPerm m2))
            by eapply (memcompat2 CMatch);
          assert (Hlt_lk1: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1))
            by eapply (memcompat1 CMatch);
          assert (Hlt_lk2: permMapLt (lock_perms _ _ cnt2) (getMaxPerm m2))
            by eapply (memcompat2 CMatch);
          (* remember the four mems *)
          let lk_mem1:=fresh "lk_mem1" in 
          let lk_mem2:=fresh "lk_mem2" in
          let th_mem1:=fresh "th_mem1" in
          let th_mem2:=fresh "th_mem2" in
          remember (snd (thread_mems thread_compat1)) as lk_mem1;
          remember (snd (thread_mems thread_compat2)) as lk_mem2;
          remember (fst (thread_mems thread_compat1)) as th_mem1;
          remember (fst (thread_mems thread_compat2)) as th_mem2;
          (* Now the injections*)
          assert (Hinj_lock: Mem.inject mu lk_mem1 lk_mem2 )
            by (subst lk_mem2 lk_mem1; eapply CMatch);
          assert (Hinj_th: Mem.inject mu th_mem1 th_mem2)
            by (subst th_mem2 th_mem1; eapply CMatch)
        end.
      
      Lemma lock_update_mem_strict_Max_equiv:
        forall b ofs m m' v1,
          lock_update_mem_strict b ofs m m' v1 ->
          Max_equiv m m'.
      Proof.
        intros * HH; inversion HH; subst vstore.
        symmetry; eapply mem_access_max_equiv,  Mem.store_access.
        eauto.
      Qed.
      Lemma lock_update_mem_strict_load_Max_equiv:
        forall b ofs perms m m' v1 v2,
          lock_update_mem_strict_load b ofs perms m m' v1 v2 ->
          Max_equiv m m'.
      Proof.
        intros * HH.
        inversion HH; subst vload vstore.
        subst m_writable_lock_1; eauto.
        etransitivity.
        - symmetry.
          eapply restr_Max_equiv.
        - apply mem_access_max_equiv.
          symmetry; eapply Mem.store_access; eauto.
      Qed.
      
      Lemma permMapLt_computeMap:
        forall c a b,
          deltaMapLt2 b c ->
          permMapLt a c ->
          permMapLt (computeMap a b) c.
      Proof.
        intros ** ??.
        destruct (dmap_get b b0 ofs) eqn:HH.
        - erewrite dmap_get_copmute_Some; try eassumption.
          unfold deltaMapLt2 in *.
          specialize (H b0 ofs). rewrite HH in H.
          inv H; auto.
        - erewrite dmap_get_copmute_None; try eassumption.
          eapply H0.
      Qed.
      Lemma permMapLt_computeMap_pair:
        forall c a b,
          deltaMapLt2_pair1 b c ->
          permMapLt_pair a c ->
          permMapLt_pair (computeMap_pair a b) c.
      Proof.
        intros ?. solve_pair. apply permMapLt_computeMap.
      Qed.
      Lemma deltaMapLt2_inject:
        forall p1 p2 m1 m2 Hlt1 Hlt2 mu virtue,
          Mem.inject mu (@restrPermMap p1 m1 Hlt1) (@restrPermMap p2 m2 Hlt2) ->
          deltaMapLt2 virtue (getMaxPerm m1) ->
          deltaMapLt2 (tree_map_inject_over_mem m2 mu virtue) (getMaxPerm m2).
      Proof.
      Admitted.
      Lemma deltaMapLt2_inject_pair:
        forall p1 p2 m1 m2 Hlt1 Hlt2 mu virtue,
          Mem.inject mu (@restrPermMap p1 m1 Hlt1) (@restrPermMap p2 m2 Hlt2) ->
          deltaMapLt2_pair1 virtue (getMaxPerm m1) ->
          deltaMapLt2_pair1 (virtueThread_inject m2 mu virtue) (getMaxPerm m2).
      Proof.
        intros until mu. unfold virtueThread_inject.
        destruct virtue0.
        solve_pair.
        split; eapply deltaMapLt2_inject.
      Qed.
      
      Lemma permMapLt_computeMap':
        forall c a b,
          permMapLt (computeMap a b) c ->
          deltaMapLt2 b c.
      Proof.
        intros ** ??.
        specialize (H b0 ofs).
        destruct (dmap_get b b0 ofs) eqn:HH.
        - erewrite dmap_get_copmute_Some in H; try eassumption.
          constructor; auto.
        - constructor.
      Qed.
      Lemma permMapLt_computeMap_pair':
        forall c a b,
          permMapLt_pair (computeMap_pair a b) c ->
          deltaMapLt2_pair1 b c.
      Proof.
        intros ?.
        solve_pair. eapply permMapLt_computeMap'.
      Qed.
      
      (* 4490 *)
      Lemma acquire_step_diagram_self Sem:
        let CoreSem:= sem_coresem Sem in
        forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
               (st1 : mach_state hb) (st2 : mach_state (S hb))
               (m1 m1' m2 : mem) (mu : meminj) tid i b b' ofs delt
               (Hinj_b : mu b = Some (b', delt))
               cnt1 cnt2 (* Threads are contained *)
               (CMatch: concur_match i mu st1 m1 st2 m2)
               
               (* Thread states *)
               (th_state1: @semC Sem) th_state2 sum_state1 sum_state2
               (HState1: coerce_state_type _ sum_state1 th_state1  
                                           (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
               (HState2: coerce_state_type _ sum_state2 th_state2
                                           (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
               (Hget_th_state1: @getThreadC _ _ tid st1 cnt1 = Kblocked sum_state1)
               (Hget_th_state2: @getThreadC _ _ tid st2 cnt2 = Kblocked sum_state2)
               
               (* angel,lock permissions and new thread permissions *)
               (angel: virtue) lock_perm
               (HisLock: lockRes st1 (b, Integers.Ptrofs.unsigned ofs) = Some lock_perm)
               (*Hangel_bound: sub_map_virtue angel (getMaxPerm m1)*)
               (Hangel_bound:
                  pair21_prop bounded_maps.sub_map (virtueThread angel) (snd (getMaxPerm m1)))
               (Hthread_mem1: access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
               (Hthread_mem2: access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2)),
          let Hcmpt2:= memcompat2 CMatch in
          let newThreadPerm1:= (computeMap_pair (getThreadR cnt1) (virtueThread angel)) in
          forall (Hjoin_angel: permMapJoin_pair lock_perm (getThreadR cnt1) newThreadPerm1)
                 (Hlt_new: permMapLt_pair newThreadPerm1 (getMaxPerm m1))
                 (Hlock_update_mem_strict_load:
                    lock_update_mem_strict_load b (unsigned ofs)  (snd (getThreadR cnt1))
                                                m1 m1' vone vzero)
                 (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
                 (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                                Some (LOCK, (Vptr b ofs :: nil)%list)),
            let event1 := build_acquire_event (b, unsigned ofs) (fst (virtueThread angel)) m1' in
            exists event2 (m2' : mem),
              match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2 /\
              inject_sync_event mu event1 event2 /\
              (* (inject_mevent mu) (Events.external tid event1) (Events.external tid event2) /\ *)
              let angel2:= inject_virtue m2 mu angel in
              let new_perms2:= Build_virtue (virtueThread angel2) (empty_map, empty_map) in
              let st2'':= fullThUpd_comp st2 tid cnt2 (Kresume sum_state2 Vundef)
                                         new_perms2 (b', unsigned (add ofs (repr delt))) in
              syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2'' m2' event2.
      Proof.
        (*  4535 - 4490 = 45 *)
        intros; simpl in *.
        (*Add all the memories and theeir relations *)
        get_mem_compatible.
        get_thread_mems.
        
        (*inversion Amatch; clear Amatch. *)

        (* Build the new angel *)
        remember (inject_virtue m2 mu angel) as angel2.
        remember (virtueThread angel2) as angelThread2.
        remember (virtueLP angel2) as angelLP2.

        (* Inject the loads/stores/mem_range*)
        unshelve( exploit lock_update_mem_strict_load_inject;
                  eauto; try (eapply CMatch; eauto)); eauto;
          intros (m2'&Hlock_update_mem_strict_load2&Hinj2).

        assert (Hmax_equiv: Max_equiv m1 m1')
          by (eapply lock_update_mem_strict_load_Max_equiv; eassumption).

        (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
        exploit address_inj_lock_update_load; eauto; intros Heq.
        
        remember (build_acquire_event (b', unsigned ofs + delt ) (fst angelThread2) m2')
          as event2. 
        
        (* Instantiate some of the existensials *)
        exists event2; exists m2'.  
        split; [|split]. (* 3 goal*)
        
        - !goal( match_self _ _ _ _ _ _). 
          inversion Amatch.
          constructor; eassumption.
          
        - !goal (inject_sync_event mu event1 event2).
          (*Goal: Inject the trace*)
          subst event1 event2.
          do 2 econstructor; auto. assumption.
          
        - !goal (syncStep _ _ _ _ _ _).
          (* Goal: show the source-external-step*)
          (* get the memory and injection *)
          subst event2 ; unfold build_release_event.
          rewrite <-  Heq.

          (*Prove that the new ThreadVirtue Joins in the right way:
                old_thread "+" delta_map = new_thread.
           *)
          set (newThreadPerm2 := computeMap_pair (getThreadR cnt2) (virtueThread angel2)).
          assert (Hjoin_angel2: permMapJoin_pair
                                  (virtueLP_inject m2 mu lock_perm)
                                  (getThreadR cnt2)
                                  newThreadPerm2).
          { clear -CMatch Hangel_bound Heqangel2 Hmax_equiv Hinj2 thread_compat1 Hjoin_angel.
            (* exploit full_injects_angel; eauto; try apply CMatch. intros Hinject_angel.
            subst newThreadPerm2; simpl. *)

            (* Look at how its done on release *)
            !goal(permMapJoin_pair _ _ _).
            admit.
          }
          rewrite <- Heq in Hlock_update_mem_strict_load2.
          inversion Hlock_update_mem_strict_load2 as [lock_mem_lt2'
                                                        vload vstore
                                                        Hwritable_lock2 
                                                        lock_mem2 m_writable_lock_2
                                                        lock_mem_lt2 
                                                        Hload2 
                                                        Hstore2];
            subst vload vstore.
          subst angelThread2.
          eapply step_acquire with
              (b0:= b')(m':=m2')
              (virtueThread:=(virtueThread angel2))
              (pmap:= virtueLP_inject m2 mu lock_perm)
          ; eauto; try reflexivity.
          
          (* 10 goals produced. *)
          
          + subst  angel2 lk_mem1 lk_mem2.
            eapply inject_virtue_sub_map_pair; eauto.
            * apply Hinj_lock.
            * apply Hangel_bound.
          + apply CMatch. 
          + !goal (semantics.at_external _ _ _ = Some (LOCK, _)).
            { clean_cnt.
              eapply ssim_preserves_atx in Hat_external.
              2: { inversion Amatch; constructor; eauto. }
              destruct Hat_external as (args' & Hat_external2 & val_inj).
              replace ( Vptr b' (add ofs (repr delt)) :: nil) with args'.
              
              simpl; unfold at_external_sum, sum_func.
              subst CoreSem. 
              rewrite <- (restr_proof_irr (th_comp thread_compat2)).
              rewrite <- Hat_external2; simpl.
              clear - Hthread_mem2 HState2.
              
              inversion HState2; subst.
              - !goal ( Clight.at_external _ = _ _ m2).
                replace c with th_state2; auto.
                2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
                (* why can't I rewrite?*)
                eapply C_at_external_proper; auto.
                eapply cur_equiv_restr_mem_equiv; auto.
              - !goal ( Asm.at_external _ _ = _ _ m2).
                replace c with th_state2; auto.
                2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
                simpl.
                (* why can't I rewrite?*)
                eapply Asm_at_external_proper; auto.
                eapply cur_equiv_restr_mem_equiv; auto.
              - clear - val_inj Hinj_b.
                inversion val_inj; subst.
                inversion H3; f_equal.
                inversion H1; subst.
                rewrite Hinj_b in H4; inversion H4; subst.
                reflexivity. }
          + simpl.
            exploit (permMapLt_computeMap_pair (getMaxPerm m2));
              try (intros HH; eapply HH).
            2:{ eapply Hcmpt2. }
            subst angel2. simpl.
            eapply deltaMapLt2_inject_pair.
            * eapply CMatch.
            * eapply permMapLt_computeMap_pair'.
              eapply Hlt_new.
          + !goal (lockRes _ (b',_) = Some _).
            eapply INJ_lock_permissions_Some; eauto.
          + (* Claims the transfered resources join in the appropriate way *)
            subst newThreadPerm2 angelLP2; eapply Hjoin_angel2.
          + (* Claims the transfered resources join in the appropriate way *)
            subst newThreadPerm2 angelLP2; eapply Hjoin_angel2.
          + subst angel2; unfold fullThUpd_comp, fullThreadUpdate; simpl.
            repeat (f_equal; simpl).

            (*Only onethreee admit: join.*)
      Admitted. (* END acquire_step_diagram_self *)
      


      Lemma release_step_diagram_self Sem:
        let CoreSem:= sem_coresem Sem in
        forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
               (st1 : mach_state hb) (st2 : mach_state (S hb))
               (m1 m1' m2 : mem) (mu : meminj) tid i b b' ofs delt
               (Hinj_b : mu b = Some (b', delt))
               cnt1 cnt2 (* Threads are contained *)
               (CMatch: concur_match i mu st1 m1 st2 m2)

               (* Thread states *)
               (th_state1: @semC Sem) th_state2 sum_state1 sum_state2
               (HState1: coerce_state_type _ sum_state1 th_state1  
                                           (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
               (HState2: coerce_state_type _ sum_state2 th_state2
                                           (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
               (Hget_th_state1: @getThreadC _ _ tid st1 cnt1 = Kblocked sum_state1)
               (Hget_th_state2: @getThreadC _ _ tid st2 cnt2 = Kblocked sum_state2)
               
               (* angel, lock permissions and new thread permissions *)
               (angel: virtue) empty_perms
               (Hempty_map: empty_doublemap empty_perms)
               (HisLock: lockRes st1 (b, Integers.Ptrofs.unsigned ofs) = Some empty_perms)
               (Hangel_bound: sub_map_virtue angel (getMaxPerm m1))
               (Hthread_mem1: access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
               (Hthread_mem2: access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2)),
          let Hcmpt2:= memcompat2 CMatch in
          let newThreadPerm1:= (computeMap_pair (getThreadR cnt1) (virtueThread angel)) in
          forall (Hjoin_angel: permMapJoin_pair newThreadPerm1 (virtueLP angel) (getThreadR cnt1))
                 (Hlock_update_mem_strict_load: lock_update_mem_strict_load b (unsigned ofs)
                                                                            (snd (getThreadR cnt1))
                                                                            m1 m1' vzero vone)
                 (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
                 (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                                Some (UNLOCK, (Vptr b ofs :: nil)%list)),
            let event1 := build_release_event (b, unsigned ofs) (fst (virtueThread angel)) m1' in
            exists event2 (m2' : mem),
              match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2 /\
              inject_sync_event mu event1 event2 /\
              let angel2:= inject_virtue m2 mu angel in
              let st2':= fullThUpd_comp st2 tid cnt2 (Kresume sum_state2 Vundef)
                                        angel2 (b', unsigned (add ofs (repr delt))) in
              syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2' m2' event2.
      Proof.
        intros; simpl in *.

        
        (*Add all the memories and theeir relations *)
        get_mem_compatible.
        get_thread_mems.
        
        (* Build the new angel *)
        remember (inject_virtue m2 mu angel) as angel2.
        remember (virtueThread angel2) as angelThread2.
        remember (virtueLP angel2) as angelLP2.

        (* Inject the loads/stores/mem_range*)
        unshelve (exploit lock_update_mem_strict_load_inject;
                  eauto; try (eapply CMatch; eauto)); eauto;
          intros (m2'&Hlock_update_mem_strict_load2&Hinj2).

        assert (Hmax_equiv: Max_equiv m1 m1')
          by (eapply lock_update_mem_strict_load_Max_equiv; eassumption).

        (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
        exploit address_inj_lock_update_load; eauto; intros Heq.
        
        remember (build_release_event (b', unsigned ofs + delt ) (fst (virtueThread angel2)) m2')
          as event2. 
        
        (* Instantiate some of the existensials *)
        exists event2; exists m2'.  
        split; [|split]. (* 3 goal*)
        
        - !goal( match_self _ _ _ _ _ _). 
          inversion Amatch; constructor; eassumption.
          
        - !goal (inject_sync_event mu event1 event2).
          subst event2; do 2 econstructor; auto. assumption.
          
        - !goal (syncStep _ _ _ _ _ _).
          
          (* Goal: show the source-external-step*)
          (* get the memory and injection *)

          subst event2 ; unfold build_release_event.
          rewrite <-  Heq.

          (*Prove that the new ThreadVirtue Joins in the right way:
                old_thread "+" delta_map = new_thread.
           *)
          set (newThreadPerm2 := computeMap_pair (getThreadR cnt2) (virtueThread angel2)).
          
          assert (Hjoin_angel2: permMapJoin_pair newThreadPerm2
                                                 (virtueLP angel2)
                                                 (getThreadR cnt2)).
          { clear - Hinj_th Hlt_th1 Hlt_th2 Hlt_lk1 Hlt_lk2
                            CMatch Hangel_bound Heqangel2
                            Hmax_equiv Hinj2 thread_compat1 Hjoin_angel.
            exploit full_injects_angel; eauto; try apply CMatch; intros Hinject_angel.
            
            subst newThreadPerm2; simpl.
            apply compute_map_join_fwd_pair.
            eapply delta_map_join_inject_pair';
              try match goal with
                    |- delta_map_join_pair _ _ _ =>
                    eapply compute_map_join_bkw_pair; eassumption
                  end; eauto.
            - !goal (perm_perfect_virtue mu angel angel2).
              subst angel2.
              replace (inject_virtue m2 mu angel) with
                  (inject_virtue th_mem2 mu angel).
              eapply inject_virtue_perm_perfect; eauto.
              admit. (*by join*)
              admit. (* same max structure.*)  
              
            - !goal(Mem.meminj_no_overlap _ m1).
              rewrite Hmax_equiv; apply Hinj2.
            - !goal (dmap_vis_filtered_pair (virtueThread angel) m1).
              eapply sub_map_filtered_pair, virtueThread_sub_map, Hangel_bound.
            - !goal (permMapLt_pair1 (getThreadR cnt1) _).
              apply compat_permMapLt; assumption.
            - !goal (almost_perfect_image_pair _ _ _ _).
              eapply inject_almost_perfect_pair; eapply CMatch.
              
              Unshelve.
              all: assumption.
          }

          
          rewrite <- Heq in Hlock_update_mem_strict_load2.
          inversion Hlock_update_mem_strict_load2 as [lock_mem_lt2'
                                                        vload vstore
                                                        Hwritable_lock2 
                                                        lock_mem2 m_writable_lock_2
                                                        lock_mem_lt2 
                                                        Hload2 
                                                        Hstore2];
            subst vload vstore.
          
          eapply step_release with
              (b0:= b')(m':=m2')
              (virtueThread:=(virtueThread angel2))
              (virtueLP:=angelLP2)
              (rmap:=virtueLP_inject m2 mu empty_perms)
          ; eauto; try reflexivity.
          
          (* 10 goals produced. *)
          
          + subst angelThread2 angel2 lk_mem1 lk_mem2.
            eapply inject_virtue_sub_map_pair; eauto.
            * apply Hinj_lock.
            * apply Hangel_bound.
              
          + unfold HybridMachineSig.isCoarse,
            HybridMachineSig.HybridCoarseMachine.scheduler.
            destruct Hangel_bound as (?&(?&?&?&?)).
            subst; eapply (proj1 (Logic.and_assoc _ _ _)).
            split.
            * unfold virtueLP_inject,
              bounded_maps.map_empty_def, inject_access_map; auto.
            * split; eapply inject_virtue_sub_map; eauto;
                try eapply Hinj_lock; eauto.
          + eapply CMatch.
          + !goal (semantics.at_external _ _ _ = Some (UNLOCK, _)).
            (* Make this into a lemma !!! *)
            { clean_cnt.
              eapply ssim_preserves_atx in Hat_external.
              2: { inversion Amatch. constructor; eauto. }
              destruct Hat_external as (args' & Hat_external2 & val_inj).
              replace ( Vptr b' (add ofs (repr delt)) :: nil) with args'.
              simpl; unfold at_external_sum, sum_func.
              (* subst CoreSem. *) 
              rewrite <- (restr_proof_irr (th_comp thread_compat2)).
              rewrite <- Hat_external2; simpl.
              (* clear - Hthread_mem2 HState2. *)
              
              inversion HState2; subst.
              - !goal ( Clight.at_external _ = _ _ m2).
                replace c with th_state2; auto.
                2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
                (* why can't I rewrite?*)
                eapply C_at_external_proper; auto.
                eapply cur_equiv_restr_mem_equiv; auto.
              - !goal ( Asm.at_external _ _ = _ _ m2).
                replace c with th_state2; auto.
                2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
                simpl.
                (* why can't I rewrite?*)
                eapply Asm_at_external_proper; auto.
                eapply cur_equiv_restr_mem_equiv; auto.
              - (*clear - val_inj Hinj_b. *)
                inversion val_inj; subst.
                inversion H3; f_equal.
                inversion H1; subst.
                rewrite Hinj_b in H4; inversion H4; subst.
                reflexivity. }
          + !goal (lockRes _ (b',_) = Some _).
            eapply INJ_lock_permissions_Some; eauto.
          + (* new lock is empty *)
            eapply empty_map_useful.
            eapply inject_empty_maps; assumption.
            
          + (* Claims the transfered resources join in the appropriate way *)
            subst newThreadPerm2 angelLP2; eapply Hjoin_angel2.
            
          + (* Claims the transfered resources join in the appropriate way *)
            subst newThreadPerm2 angelLP2; eapply Hjoin_angel2.

          + subst; unfold fullThUpd_comp, fullThreadUpdate; auto.

      Admitted.  (* release_step_diagram_self *)

      Lemma make_step_diagram_self Sem: (*5336*) 
        let CoreSem:= sem_coresem Sem in
        forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
          (st1 : mach_state hb) (st2 : mach_state (S hb))
          (m1 m1' m2 : mem) (mu : meminj) tid i b1 b2 ofs delt
          (Hinj_b : mu b1 = Some (b2, delt)) new_perms1 new_perms2
          cnt1 cnt2 (* Threads are contained *)
          (CMatch: concur_match i mu st1 m1 st2 m2)

          (* Thread states *)
          (th_state1: @semC Sem) th_state2 sum_state1 sum_state2
          (HState1: coerce_state_type _ sum_state1 th_state1  
                                      (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
          (HState2: coerce_state_type _ sum_state2 th_state2
                                      (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
          (Hget_th_state1: @getThreadC _ _ tid st1 cnt1 = Kblocked sum_state1)
          (Hget_th_state2: @getThreadC _ _ tid st2 cnt2 = Kblocked sum_state2)

          (* The following two things are not needed *)
          (HH1: set_new_mems b1 (unsigned ofs) (getThreadR cnt1) LKSIZE_nat new_perms1)
          (HH1: set_new_mems b2 (unsigned ofs+delt) (getThreadR cnt2) LKSIZE_nat new_perms2)
          
          (* angel, lock permissions and new thread permissions *)
          (HisLock: lockRes st1 (b1, Integers.Ptrofs.unsigned ofs) = None )
          (Hthread_mem1: access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
          (Hthread_mem2: access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2)),
          let Hcmpt2:= memcompat2 CMatch in
          forall (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
                 (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                                Some (MKLOCK, (Vptr b1 ofs :: nil)%list))
                 (Hlock_update_mem_strict: lock_update_mem_strict b1 (unsigned ofs) m1 m1' vzero),
            let evnt1:= Events.mklock (b1, unsigned ofs) in
            exists event2 (m2' : mem),
              let st2':= fullThreadUpdate st2 tid cnt2 (Kresume sum_state2 Vundef)
                                          (new_perms2, pair0 empty_map) (b2, unsigned ofs + delt) in
              match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2 /\
              inject_sync_event mu evnt1 event2 /\
              syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2' m2' event2.
      Proof. (* 5374 - 5336 = 38 *)
        intros; simpl in *.
        (*Add all the memories and theeir relations *)
        get_mem_compatible.
        get_thread_mems.

        assert (Hmem_equiv1: mem_equiv m1 th_mem1).
        { subst th_mem1; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
        assert (Hmem_equiv2: mem_equiv m2 th_mem2).
        { subst th_mem2; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
        
        (* Inject the loads/stores/mem_range*)
        unshelve (exploit lock_update_mem_strict_inject;
                  try apply Hlock_update_mem_strict;
                  eauto; try (eapply CMatch; eauto)); eauto.
        rewrite Hmem_equiv1; assumption.
        intros (m2'&Hlock_update_mem_strict2&Hinj2).
        
        assert (Hmax_equiv: Max_equiv m1 m1')
          by (eapply lock_update_mem_strict_Max_equiv; eassumption).

        (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
        exploit address_inj_lock_update;
          try apply Hlock_update_mem_strict; eauto; intros Heq.
        
        assert (Hinj: Mem.inject mu m1 m2).
        { rewrite Hmem_equiv1, Hmem_equiv2; auto. }
        
        remember (Events.mklock (b2, unsigned ofs + delt ))
          as event2. 
        
        (* Instantiate some of the existensials *)
        exists event2; exists m2'.  
        split; [|split]. (* 3 goal*)
        
        - !goal(match_self _ _ _ _ _ _).
          inversion Amatch. constructor; eassumption.
          
        - !goal(inject_sync_event mu evnt1 event2).
          subst event2; do 2 econstructor; auto. assumption.
          
        - !goal (syncStep _ _ _ _ _ _).
          (* Goal: show the source-external-step*)
          (* get the memory and injection *)
          subst event2.
          rewrite <-  Heq.

          (*Prove that the new ThreadVirtue Joins in the right way:
                old_thread "+" delta_map = new_thread.
           *)
          inversion Hlock_update_mem_strict2 as [vstore
                                                   lock_mem_lt2 
                                                   Hstore2];
            subst vstore.

          
          eapply (step_mklock _ _ _ _ _ )
            with (pmap_tid':= new_perms2);
            eauto; try reflexivity; try solve[apply CMatch].
          
          (* 8 goals produced. *)
          + !goal (semantics.at_external _ _ _ = Some (MKLOCK, _)).
            abstract_proofs; unify_proofs.
            rewrite (cur_equiv_restr_mem_equiv m2 _ abs_proof Hthread_mem2).
            erewrite <- coerse_state_atx; eauto.
            eapply atx_injection; eauto.

          + !goal(Mem.range_perm _ _ _ _ _ _).
            inversion Hlock_update_mem_strict2; subst th_mem2.
            replace (intval (add ofs (repr delt))) with (unsigned ofs + delt).
            eauto.
          + move Hstore2 at bottom.
            match goal with |- Mem.store _ ?m' _ _ _ = _ => (replace m' with th_mem2) end.
            replace (intval (add ofs (repr delt))) with (unsigned ofs + delt).
            assumption.
            * subst th_mem2.
              simpl; f_equal.
              apply Axioms.proof_irr.
          + inv HH0; simpl.
            f_equal; eauto.
          + inv HH0; simpl.
            f_equal; eauto.
          + !goal (lockRes _ (b2,_) = None).
            eapply INJ_lock_permissions_None; eauto.
            (* 6925 - 6883 = 42*)

      Qed. (* make_step_diagram_self *)
      Lemma perm_range_perm:
        forall m b low high k p,
          Mem.range_perm m b low high k p ->
          forall ofs', Intv.In ofs' (low,high) ->
                       Mem.perm m b ofs' k p.
      Proof.
        unfold Mem.range_perm, Mem.perm; intros.
        eapply H; eauto.
      Qed.
      Lemma free_step_diagram_self Sem:
        let CoreSem:= sem_coresem Sem in
        forall (SelfSim: (self_simulation (@semC Sem) CoreSem))
               (st1 : mach_state hb) (st2 : mach_state (S hb))
               (m1 m2 : mem) (mu : meminj) tid i b1 b2 ofs delt
               lock_data pdata
               (Hinj_b : mu b1 = Some (b2, delt))
               cnt1 cnt2 (* Threads are contained *)
               (CMatch: concur_match i mu st1 m1 st2 m2)

               (* Thread states *)
               (th_state1: @semC Sem) th_state2 sum_state1 sum_state2
               (HState1: coerce_state_type _ sum_state1 th_state1  
                                           (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
               (HState2: coerce_state_type _ sum_state2 th_state2
                                           (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
               (Hget_th_state1: @getThreadC _ _ tid st1 cnt1 = Kblocked sum_state1)
               (Hget_th_state2: @getThreadC _ _ tid st2 cnt2 = Kblocked sum_state2)
               
               (* angel, lock permissions and new thread permissions *)
               (Hnone_beyond : bounded_maps.bounded_nat_func' pdata LKSIZE_nat)
               (Hthread_mem1: access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
               (Hthread_mem2: access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2))
               (Hlock_map: lockRes st1 (b1, Integers.Ptrofs.unsigned ofs) = Some lock_data)
               (Hempty_lock: forall b ofs, pair1 (fun map => map !! b ofs) lock_data = pair0 None)
               (HlocksLt: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1) )
               (Hrange_perm: perm_interval (restrPermMap HlocksLt)
                                           b1 (unsigned ofs) LKSIZE Cur Writable)
               (HH: forall i, 0 <= (Z.of_nat i) < LKSIZE ->
                              Mem.perm_order'' (pdata (S i)) (Some Writable))
               (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
               (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                              Some (FREE_LOCK, (Vptr b1 ofs :: nil)%list)),
          let ofs2:=  unsigned ofs + delt in
          let new_perms2:=
              setPermBlock_var_pair b2 ofs2 LKSIZE_nat
                                    (pdata, fun _:nat => None) (getThreadR cnt2) in
          let evnt1:= Events.freelock (b1, unsigned ofs) in
          exists event2 (m2' : mem),
            let Hcmpt2:= memcompat2 CMatch in
            let st2':= remLockfFullUpdate st2 tid cnt2 (Kresume sum_state2 Vundef)
                                          new_perms2 (b2, unsigned ofs + delt) in
            match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2 /\
            inject_sync_event mu evnt1 event2 /\
            syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2' m2' event2.
      Proof.
        intros; simpl in *.
        (*Add all the memories and theeir relations *)
        get_mem_compatible.
        get_thread_mems.

        replace (restrPermMap HlocksLt) with lk_mem1 in * by
            (subst lk_mem1; simpl; f_equal; apply Axioms.proof_irr).
        clear HlocksLt.
        
        assert (Hmem_equiv1: mem_equiv m1 th_mem1).
        { subst th_mem1; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
        assert (Hmem_equiv2: mem_equiv m2 th_mem2).
        { subst th_mem2; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
        
        (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
        assert (Heq:unsigned (add ofs (repr delt)) = unsigned ofs + delt).
        { eapply Mem.address_inject; try apply Hinj_lock; eauto.
          unfold perm_interval in Hrange_perm.
          eapply perm_range_perm; eauto.
          { clear. unfold Intv.In; simpl.
            pose proof LKSIZE_pos; omega. }
        }
        
        
        assert (Hinj: Mem.inject mu m1 m2).
        { rewrite Hmem_equiv1, Hmem_equiv2; auto. }
        
        remember (Events.freelock (b2, unsigned ofs + delt )) as event2. 
        
        (* Instantiate some of the existensials *)
        exists event2; exists m2.  
        split; [|split]. (* 3 goal*)
        
        - !goal(match_self _ _ _ _ _ _).
          inversion Amatch. constructor; eassumption.
          
        - !goal(inject_sync_event mu evnt1 event2).
          subst event2; do 2 econstructor; auto. assumption.
          
        - !goal (syncStep _ _ _ _ _ _).
          (* Goal: show the source-external-step*)
          (* get the memory and injection *)
          subst event2. rewrite <-  Heq.

          eapply (step_freelock _ _ _ _ _ )
            with (b:=b2)
                 (pmap_tid':= new_perms2);
            eauto; try reflexivity; try solve[apply CMatch].
          
          (* 8 goals produced. *)
          + !goal (semantics.at_external _ _ _ = Some (FREE_LOCK, _)).
            erewrite (cur_equiv_restr_mem_equiv _ _ _ Hthread_mem2).
            erewrite <- coerse_state_atx; eauto.
            eapply atx_injection; eauto.
            
            
          + !goal (lockRes _ (b2,_) = Some _).
            eapply INJ_lock_permissions_Some; eauto.
            

          + clear - Hempty_lock hb.
            
            assert (empty_doublemap lock_data).
            { unfold empty_doublemap.
              repeat autounfold with pair in *; simpl in *.
              split; simpl; intros b ofs;
                specialize (Hempty_lock b ofs);
                inv Hempty_lock; auto.
            }
            
            pose proof inject_empty_maps.
            split; eapply inject_empty_maps; auto.
            
          + !goal(Mem.range_perm _ _ _ _ _ _).
            match goal with |- Mem.range_perm ?m _ ?ofs2 _ _ _ =>
                            replace m with lk_mem2;
                              replace ofs2 with (unsigned ofs + delt)
            end.
            replace (unsigned ofs + delt + LKSIZE)
              with (unsigned ofs + LKSIZE + delt) by omega.
            eapply Mem.range_perm_inj; eauto; eapply Hinj_lock.
            subst lk_mem2; simpl; f_equal; apply Axioms.proof_irr.
            
          + !goal(setPermBlock _ _ _ _ _ = _).
            subst new_perms2; simpl.
            rewrite setPermBlock_setPermBlock_var.
            f_equal. subst ofs2; auto.

          + !goal(setPermBlock_var _ _ _ _ _ = _).
            simpl; f_equal.
            subst ofs2. eauto.

      Qed. (* free_step_diagram_self *)

      Lemma acquire_fail_step_diagram_self Sem:
        let CoreSem:= sem_coresem Sem in
        forall (m1 m2: mem)
               (SelfSim: (self_simulation (@semC Sem) CoreSem))
               (st1 : mach_state hb) (st2 : mach_state (S hb))
               (mu : meminj) tid i b b' ofs delt
               (Hinj_b : mu b = Some (b', delt))
               cnt1 cnt2 (* Threads are contained *)
               (CMatch: concur_match i mu st1 m1 st2 m2)
               
               (* Thread states *)
               (th_state1: @semC Sem) th_state2 sum_state1 sum_state2
               (HState1: coerce_state_type _ sum_state1 th_state1  
                                           (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
               (HState2: coerce_state_type (@semC Sem) sum_state2 th_state2
                                           (CSem, Clight.state) (AsmSem,Asm.state) (Sem,@semC Sem))
               (Hget_th_state1: @getThreadC _ _ tid st1 cnt1 = Kblocked sum_state1)
               (Hget_th_state2: @getThreadC _ _ tid st2 cnt2 = Kblocked sum_state2)
               
               (* angel,lock permissions and new thread permissions *)
               (Hthread_mem1: access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
               (Hthread_mem2: access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2))
               (Amatch : match_self (code_inject _ _ SelfSim) mu th_state1 m1 th_state2 m2)
               (Hat_external: semantics.at_external CoreSem th_state1 m1 =
                              Some (LOCK, (Vptr b ofs :: nil)%list))
               (Hlock_lt: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1)),
          let m1_locks:= restrPermMap Hlock_lt in
          forall (Hload: Mem.load AST.Mint32 m1_locks b (unsigned ofs) = Some vzero)
                 (Hrange_perm: perm_interval m1_locks b (unsigned ofs) LKSIZE Cur Readable),
            let evnt1 := Events.failacq (b, unsigned ofs) in
            exists evnt2,
              inject_sync_event mu evnt1 evnt2 /\
              forall perm Hlt_perm,
                let m2_any:= @restrPermMap perm m2 Hlt_perm in
                forall (Hcmpt2: mem_compatible st2 m2_any),
                  syncStep(Sem:=HybridSem (Some (S hb))) true cnt2 Hcmpt2 st2 m2_any evnt2.
      Proof.
        
        intros; simpl in *.
        (*Add all the memories and theeir relations *)
        get_mem_compatible.
        get_thread_mems.
        
        replace (m1_locks) with lk_mem1 in * by
            (subst m1_locks lk_mem1; simpl; f_equal; apply Axioms.proof_irr).
        clear m1_locks Hlock_lt.
        
        assert (Hmem_equiv1: mem_equiv m1 th_mem1).
        { subst th_mem1; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
        assert (Hmem_equiv2: mem_equiv m2 th_mem2).
        { subst th_mem2; symmetry; eapply cur_equiv_restr_mem_equiv; eauto. }
        
        (* unsigned (add ofs (repr delt)) = unsigned ofs + delt *)
        assert (Heq:unsigned (add ofs (repr delt)) = unsigned ofs + delt).
        { eapply Mem.address_inject; try apply Hinj_lock; eauto.
          unfold perm_interval in Hrange_perm.
          eapply perm_range_perm; eauto.
          move Hrange_perm at bottom.
          { clear. unfold Intv.In; simpl.
            pose proof LKSIZE_pos; omega. }
        }
        
        assert (Hinj: Mem.inject mu m1 m2).
        { rewrite Hmem_equiv1, Hmem_equiv2; auto. }
        
        remember (Events.failacq (b', unsigned ofs + delt )) as evnt2. 
        
        (* Instantiate some of the existensials *)
        exists evnt2; split. (* 3 goal*)
        
        - !goal(inject_sync_event mu evnt1 evnt2).
          subst evnt1 evnt2; do 2 econstructor; auto. assumption.
          
        - intros; !goal (syncStep _ _ _ _ _ _).
          (* Goal: show the source-external-step*)
          (* get the memory and injection *)
          subst evnt2; rewrite <- Heq.
          
          eapply (step_acqfail); eauto; try reflexivity; try solve[apply CMatch].
          
          (* 8 goals produced. *)
          + !goal (semantics.at_external _ _ _ = Some (LOCK, _)).
            
            pose proof (cur_equiv_restr_mem_equiv
                          _ _ (fst (ssrfun.pair_of_and (Hcmpt0 tid cnt2)))).
            erewrite <- coerse_state_atx; eauto.
            (* The following proof comes from acquire_step_diagram ...
               Should probably be turned into a lemm
             *)
            
            { clean_cnt.
              eapply ssim_preserves_atx in Hat_external.
              2: { inversion Amatch; constructor; eauto. }
              destruct Hat_external as (args' & Hat_external2 & val_inj).
              replace ( Vptr b' (add ofs (repr delt)) :: nil) with args'.
              
              simpl; unfold at_external_sum, sum_func.
              subst CoreSem; rewrite <- (restr_proof_irr (proj1 (Hcmpt0 tid cnt2))).
              rewrite <- Hat_external2; simpl.
              clear - Hthread_mem2 HState2 Hthread_mem1.
              
              inversion HState2; subst.
              - !goal ( Clight.at_external _ = _ _ m2).
                replace c with th_state2; auto.
                2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
                (* why can't I rewrite?*)
                
                eapply C_at_external_proper; auto.
                etransitivity.
                
                + symmetry; unshelve eapply restrPermMap_idempotent.
                  rewrite Hthread_mem2; exact (cur_lt_max _).
                + rewrite RPM.
                  eapply cur_equiv_restr_mem_equiv.
                  eassumption.
              - !goal ( Asm.at_external _ _ = _ _ m2).
                replace c with th_state2; auto.
                2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
                simpl.
                (* why can't I rewrite?*)
                eapply Asm_at_external_proper; auto.
                etransitivity.
                
                + symmetry; unshelve eapply restrPermMap_idempotent.
                  rewrite Hthread_mem2; exact (cur_lt_max _).
                  
                + rewrite RPM.
                  eapply cur_equiv_restr_mem_equiv.
                  eassumption.
              - clear - val_inj Hinj_b.
                inversion val_inj; subst.
                inversion H3; f_equal.
                inversion H1; subst.
                rewrite Hinj_b in H4; inversion H4; subst.
                reflexivity. }
            
          + !goal(Mem.range_perm _ _ _ _ _ _).
            
            unshelve erewrite <- restrPermMap_idempotent_eq.
            { eapply Hcmpt2. }
            match goal with |- Mem.range_perm ?m _ ?ofs2 _ _ _ =>
                            replace m with lk_mem2;
                              replace ofs2 with (unsigned ofs + delt)
            end.
            replace (unsigned ofs + delt + LKSIZE)
              with (unsigned ofs + LKSIZE + delt) by omega.
            eapply Mem.range_perm_inj; eauto; eapply Hinj_lock.
            subst lk_mem2; simpl; repeat f_equal.
            eapply Axioms.proof_irr.
            

          + !context_goal Mem.load.
            unshelve erewrite <- restrPermMap_idempotent_eq.
            eapply Hcmpt2.
            eapply Mem.load_inject in Hload; eauto.
            destruct Hload as (?&Hload2&Hinj_v).
            inv Hinj_v.
            replace (intval (add ofs (repr delt))) with (unsigned ofs + delt).
            eassumption.
      Qed.  (* acquire_fail_step_diagram_self *)
      

      (** *Compiled diagrams*)

      Lemma C_large_step_as_compcert_step:
        forall Clight_g code1 m1 rel_trace s1' m1''' args
               func fname fsig
               (Hfunc: func = AST.EF_external fname fsig)
               (Hexternal_step: Events.external_call
                                  func (Clight.genv_genv Clight_g)
                                  args m1 rel_trace Vundef m1''')
               (Hafter_ext: Clight.after_external None code1 m1''' = Some s1')
               (Hat_external1: Clight.at_external (Clight.set_mem code1 m1) =
                               Some (func, args)),
          Clight.step2 (Clight_g)
                       (Clight.set_mem code1 m1)
                       rel_trace
                       (Clight.set_mem s1' m1''').
      Proof.
        intros.
        unfold Clight.after_external in Hafter_ext.
        unfold Clight.at_external in Hat_external1.
        simpl.
        destruct code1 eqn:Hcallstate; try discriminate.
        destruct fd eqn:Hext_func; try discriminate.
        inversion Hat_external1.
        inversion Hafter_ext.
        subst e args. simpl in *.
        eapply Clight.step_external_function; eauto.
      Qed.
      Definition consecutive_until: block -> list Events.mem_effect -> block -> Prop.
      Admitted.

      Lemma consecutive_until_cat:
        forall lev lev' b b' b'',
          consecutive_until b lev b' ->
          consecutive_until b' lev' b'' ->
          consecutive_until b (lev ++ lev') b''.
      Proof.
      Admitted.
      Lemma consecutive_until_consecutive:
        forall lev b b',
          consecutive_until b lev b' ->
          consecutive b lev.
      Proof.
      Admitted.
      
      Lemma interference_consecutive_until:
        forall {m lev m'},
          mem_interference m lev m' ->
          consecutive_until (Mem.nextblock m) lev (Mem.nextblock m').
      Proof. Admitted.
      Lemma thread_step_from_external:
        forall ge c2 m args c2' rel_trace2 m' FUN
               (Hfun_dsnt_ret: (AST.sig_res (AST.ef_sig FUN)) = None)
               (Hat_x : Asm.at_external ge (Asm.set_mem c2 m) =
                        Some (FUN, args))
               (Hafter_x : Asm.after_external
                             ge None c2 (Asm.get_mem c2') = Some c2')
               (Hext_rel: Events.external_call FUN
                                               ge args m
                                               rel_trace2 Vundef m'),
          Asm.step ge (Asm.set_mem c2 m) rel_trace2
                   (Asm.set_mem c2' m').
      Proof.
        intros.
        unfold Asm.after_external in *.
        unfold Asm.after_external_regset in *.
        destruct c2.
        destruct c2' eqn:Hs2'; simpl.
        unfold Asm.at_external in *.
        simpl in Hat_x.
        destruct (r Asm.PC) eqn:rPC; try discriminate.
        destruct (eq_dec i zero) eqn:i0_0; try discriminate.
        unfold Asm_g. 
        destruct (Genv.find_funct_ptr ge b)
                 eqn:func_lookup; try discriminate.
        destruct f; try discriminate.
        unfold Asm.after_external.
        unfold Asm.after_external_regset.
        unfold Asm_g, the_ge in *.
        match type of Hat_x with
        | match ?x with _ => _ end = _ =>
          destruct x eqn:HH; try discriminate
        end.
        invert Hat_x; subst i.
        eapply Asm.exec_step_external; eauto.
        - apply Asm_core.get_extcall_arguments_spec; eauto.
        - inv Hafter_x; f_equal.
          unfold Asm.loc_external_result, Conventions1.loc_result.
          rewrite Archi.splitlong_ptr32.
          unfold Conventions1.loc_result_32.
          rewrite Hfun_dsnt_ret; simpl. reflexivity.
          reflexivity.
      Qed.
      Lemma after_x_mem:
        forall ge code2 m s2',
          Asm.after_external ge None code2 m = Some s2' ->
          Asm.get_mem s2' = m.
      Proof.
        unfold Asm.after_external, Asm.get_mem.
        intros.
        destruct code2.
        destruct (Asm.after_external_regset ge None r);
          try discriminate.
        inv H. reflexivity.
      Qed.
      Lemma asm_set_mem_get_mem:
        forall s,
          Asm.set_mem s (Asm.get_mem s) = s.
      Proof. Admitted.
      Lemma strict_inj_evolution_cat:
        forall j j' j'' lev1 lev1' lev2 lev2' nb nb' nb'',
          strict_injection_evolution j j' lev1 lev2 ->
          strict_injection_evolution j' j'' lev1' lev2' ->
          consecutive_until nb lev2 nb' ->
          consecutive_until nb' lev2' nb'' ->
          strict_injection_evolution j j'' (lev1++lev1') (lev2++lev2').
      Proof.
      Admitted.
      Lemma list_inject_mem_effect_cat:
        forall j l1 l1' l2 l2',
          Events.list_inject_mem_effect j l1 l2 ->
          Events.list_inject_mem_effect j l1' l2' ->
          Events.list_inject_mem_effect j (l1++l1') (l2++l2').
      Proof.
      Admitted.
      Definition doesnt_return FUN:=
        forall (res : val) (ge : Senv.t) (args : list val) (m : mem) 
               (ev : Events.trace) (m' : mem),
          Events.external_call FUN ge args m ev res m' -> res = Vundef.
      
      Lemma unlock_doesnt_return:
        doesnt_return UNLOCK.
      Proof.
        intros ? * Hext_call.
        unfold Events.external_call in Hext_call.
        rewrite ReleaseExists in Hext_call.
        inversion Hext_call; reflexivity.
      Qed.
      Lemma asm_after_external_when_external_step:
        forall (ge:Asm.genv) c2 m ev c2' args FUN name sig
               (HeqFUN: FUN = (AST.EF_external name sig))
               (HnoReturn : AST.sig_res sig = None)
               (Hno_return: doesnt_return FUN)
               (Hstep: Asm.step ge (Asm.set_mem c2 m) (ev::nil) c2')
               (Hat_x: Asm.at_external ge (Asm.set_mem c2 m) = Some (FUN, args)),
          Asm.after_external ge None c2 (Asm.get_mem c2') = Some c2'.
      Proof.
        intros.
        
        (*Build the after_external, from the at_external. *)
        unfold Asm.at_external in *.
        destruct c2 eqn:Code.
        simpl in Hat_x.
        destruct (r Asm.PC) eqn:rPC; try discriminate.
        destruct (eq_dec i zero) eqn:i0_0; try discriminate.
        unfold Asm_g. 
        destruct (Genv.find_funct_ptr ge b) eqn:func_lookup; try discriminate.
        destruct f; try discriminate.
        unfold Asm.after_external.
        unfold Asm.after_external_regset.
        unfold Asm_g, the_ge in *.
        rewrite rPC, i0_0, func_lookup.
        
        (* subst rel_trace2;*)

        inversion Hstep; subst; try solve[inversion H4].
        - unfold Asm.at_external in Hat_x.
          rewrite rPC in H1; inversion H1; subst.
          unfold Asm_g, the_ge in *.
          rewrite func_lookup in H2.
          inversion H2; discriminate.
        - rename m' into m21'''.
          unfold Asm.loc_external_result,Conventions1.loc_result.
          replace Archi.ptr64 with false by reflexivity; simpl. 
          

          (* NOTE: 
                       - the s2' (i.e. target state) in comp_match, 
                       results from inverting the step.
                       - the st'2 (i.e. target state) in the goal,
                       results from Asm.after_external. 
           *)
          (* Show that target program is executing the same function*)
          
          assert (FUNeq: e0 = ef ).
          { assert (BB0: b0 = b)
              by (rewrite rPC in H1; inversion H1; reflexivity).
            subst b0. unfold Asm_g, the_ge in *.
            rewrite func_lookup in H2; inversion H2; reflexivity.
          } subst e0.
          
          (* Show that the function is UNLOCK*)
          match type of Hat_x with
          | match ?x with _ => _ end = _ =>
            destruct x eqn:HH; try discriminate
          end.

          inv Hat_x.
          erewrite (Hno_return res) by eauto.
          simpl. unfold Conventions1.loc_result_32.
          rewrite HnoReturn.
          reflexivity.
      Qed.

      Inductive principled_diagram':
        block -> meminj -> meminj -> list Events.mem_effect -> Prop :=
      |build_pd': forall  nb j j0 lev1 lev20,
          principled_diagram nb j j0 lev1 lev20 ->
          principled_diagram' nb j j0 lev1.
      Inductive diagram':
        block -> meminj -> meminj -> list Events.mem_effect -> Prop :=
      |build_d': forall nb j j' lev1 lev2,
          diagram nb j j' lev1 lev2 ->
          diagram' nb j j' lev1.
      Lemma principled_diagram_correct':
        forall (nb : block)
               (j j' j0 : meminj)
               (lev1: list Events.mem_effect),
          principled_diagram' nb j j0 lev1 ->
          diagram' nb j j' lev1 ->
          inject_incr j0 j'.
      Proof.
        intros * H1 H2; inv H1; inv H2;
          eapply principled_diagram_correct; eassumption.
      Qed.
      Lemma principled_diagram_exists':
        forall (nb : block) (j j' : meminj) (lev1 lev2 : list Events.mem_effect),
          strict_injection_evolution j j' lev1 lev2 ->
          consecutive nb lev2 ->
          principled_diagram' nb j j' lev1.
      Proof.
        intros.
        exploit principled_diagram_exists; eauto.
        intros (?&?&?).
        econstructor; eauto.
      Qed.

      
      (*TODO: 
              1. Find a better name
              2. Simplify / Clean it?        
       *)

      Lemma lock_doesnt_return:
        doesnt_return LOCK.
      Proof.
        intros ? * Hext_call.
        unfold Events.external_call in Hext_call.
        rewrite AcquireExists in Hext_call.
        inversion Hext_call; reflexivity.
      Qed.
      
      Lemma large_external_diagram:
        forall cd f mu j'' code1 code2 cge age args1 rel_trace m1 m1'''
               args2 rel_trace2 FUN
               m2 m2' m2'' m2''' lev1 lev1' lev2 lev2' s1'
               p Hlt dpm1 dpm2 name signature
               (Hfun: FUN = AST.EF_external name signature)
               (Hun_dsnt_ret: doesnt_return FUN)
               (Hun_dsnt_ret_sig: AST.sig_res signature = None)
               (Hinj_delts: Events.inject_delta_map mu dpm1 dpm2)
               (Heqrel_trace1 : rel_trace = Events.Event_acq_rel lev1 dpm1 lev1' :: nil)
               (Heqrel_trace : rel_trace2 = Events.Event_acq_rel lev2 dpm2 lev2' :: nil)
               (HAge: age =  (Genv.globalenv Asm_program))
               (HCge: cge = (Clight.globalenv C_program) )
               (Hext_rel1 : Events.external_call
                              FUN (Clight.genv_genv cge) 
                              args1 m1 rel_trace Vundef m1''')
               (Hext_rel2 : Events.external_call
                              FUN age 
                              args2 m2 rel_trace2 Vundef m2''')
               (Hnb_eq : Mem.nextblock m2'' = Mem.nextblock m2')
               (Hstrict_evolution : strict_injection_evolution f mu lev1 lev2)
               (Hstrict_evolution' : strict_injection_evolution mu j'' lev1' lev2')
               (Hafter_ext : Clight.after_external None code1 m1''' = Some s1')
               (Hmatch_states : compiler_match cd f code1 m1 code2 m2)
               (Hat_external1 : Clight.at_external (Clight.set_mem code1 m1) =
                                Some (FUN, args1))
               (Hat_external2 : Asm.at_external Asm_g (Asm.set_mem code2 m2) =
                                Some (FUN, args2))
               (Hinterference2' : mem_interference (@restrPermMap p m2'' Hlt) lev2' m2''')
               (Hconsecutive : consecutive_until (Mem.nextblock m2) lev2 (Mem.nextblock m2'))
               (Hconsecutive' : consecutive_until (Mem.nextblock m2'') lev2' (Mem.nextblock m2''')),
        exists (cd' : compiler_index) (j''' : meminj) (s2' : Asm.state),
          Asm.after_external Asm_g None code2 m2''' = Some s2' /\
          inject_incr mu j''' /\ compiler_match cd' j''' s1' m1''' s2' m2'''.
      Proof.
        intros; subst FUN.
        
        
        (** *1. Prove that this is a CompCert step (en external step).
         *)
        exploit C_large_step_as_compcert_step; eauto.
        replace Values.Vundef with Vundef; eauto; simpl.
        intros Hstep.
        
        
        (** *2. Apply the simulation
                To construct the step in Asm
         *)
        subst cge;
          eapply (Injsim_simulation_atxX compiler_sim) in Hstep; eauto.
        specialize (Hstep _ _ _ Hmatch_states).
        destruct Hstep as (j2'&Hincr&Hstep_str&Hstep).
        clear Hat_external1 Hafter_ext.

        (* Notice that memories before and after stroe have same next_block*)
        
        (** *3. Following steps we prove each of the things we need. *)

        move Hstep_str at bottom.
        destruct Hstep_str as
            (i2_str & s2_str & t_str &
             Hstep_str & Hmatch_str & Hinj_trace_str).
        
        assert (Hincr_j'': inject_incr j'' j2').
        { (*
                    ( ) ---- lev1 + lev1' ---> ( )
                     |                          |  \
                     f     regular diagram      j'' \
                     |                          |    \
                    ( ) ---- lev2 + lev2' ---> ( )    \
                      \                                \
                      =eq=  strong/principled diagram  j2'
                        \                                \
                        ( )---- lev2_str + lev2_str --->( )
           *)
          eapply principled_diagram_correct'.
          - (** *Full strong diagram *)
            rewrite Hnb_eq in Hconsecutive'.
            eapply principled_diagram_exists'.
            + exploit (strict_inj_evolution_cat f mu j''); eauto.
            + exploit (consecutive_until_cat lev2 lev2');
                try eassumption.
              eapply consecutive_until_consecutive.
          - subst rel_trace.
            inv Hinj_trace_str. clear H3; inv H1. 
            do 2 econstructor; eauto.
            + eapply list_inject_mem_effect_cat;
                eapply list_inject_weaken;
                eassumption.
            + eapply Asm_step_consecutive; simpl in *; eauto.
        }

        
        assert (Hincr_mu : inject_incr mu j2').
        { eapply inject_incr_trans.
          eapply (evolution_inject_incr).
          all: eassumption. }
        

        (* remember
            (Events.Event_acq_rel lev2 dpm1 (*fst virtueThread2*) lev2' :: nil)  as
                rel_trace2. *)

        assert (Hinj_trace: Events.inject_trace j2' rel_trace rel_trace2).
        { subst rel_trace rel_trace2.
          econstructor; try solve[constructor].
          econstructor.
          - emonotonicity; eauto.
            emonotonicity; eauto.
            eapply evolution_list_inject_mem; eauto.
          - emonotonicity; eauto.
          - emonotonicity; try apply Hincr_j''.
            eapply evolution_list_inject_mem in Hstrict_evolution'; assumption.
        }
        clear Hstrict_evolution'.

        subst rel_trace.
        destruct  (Hstep _ Hinj_trace)
          as (cd' & s2' & step & comp_match ).
        

        (* Assert the after_external we know:
               Given from 
               Hat_external2: Asm.at_externalge (c2, m2) = Blah
               step: (c2, m2) --> s2'
         *)
        exploit asm_after_external_when_external_step;
          subst rel_trace2; simpl in *; eauto; try reflexivity.
        intros Hafter_x.

        (* Now change the mem to the one we need *)
        replace (Asm.get_mem s2') with m2''' in Hafter_x.
        2:{ !goal (m2''' = _).
            clear - Hun_dsnt_ret_sig HAge hb step Hat_external2 Hafter_x Hext_rel2.
            replace m2''' with (Asm.get_mem (Asm.set_mem s2' m2'''))
              by (destruct s2'; auto); f_equal. 
            eapply asm_step_determ; try eassumption.
            eapply thread_step_from_external; simpl; eauto.
            - simpl; eauto.
            - subst age; eauto.  }
        
        do 3 eexists; repeat (split; eauto).
        unfold compiler_match; simpl.
        eapply after_x_mem in Hafter_x.
        rewrite <- Hafter_x, asm_set_mem_get_mem.
        eassumption.
      Qed.
      Ltac unify_at_ext:=
        repeat match goal with
                 [H: semantics.at_external _ _ _ = Some _ |- _] =>
                 simpl in H
               end;
        match goal with
          [H1: Clight.at_external ?X = _,
               H2: Clight.at_external ?X = _ |- _] =>
          rewrite H1 in H2; invert H2
        end.
      Ltac inj_args_inv:=
        match goal with
          [Hinj_args: Val.inject_list ?f (Vptr ?b1 ?ofs :: nil) _  |- _ ]=>
          invert Hinj_args;
          match goal with
          | [ Hinj_ptr: Val.inject _ (Vptr b1 ofs) _,
                        Hinj_nil: Val.inject_list _ nil _ |- _ ] =>
            invert Hinj_ptr; invert Hinj_nil;
            match goal with
            | [Hinj_b_badname: f b1 = Some _ |- _ ] =>
              let Hinj_b:= fresh "Hinj_b" in rename Hinj_b_badname into Hinj_b;
                                             try (let Hinj_b':= fresh "Hinj_b'" in
                                                  eapply evolution_inject_incr in Hinj_b as Hinj_b';
                                                  eauto; [idtac] (*check only one goal left.*) )
            end
          end
        end.
      Ltac inject_lock_update_mem_strict_load:=
        lazymatch goal with
          [CMatch: concur_match _ ?mu ?st1 ?m1' ?st2 ?m2',
                   Hlock: lock_update_mem_strict_load _ _ _ _ _ _ _ |- _ ] =>
          let Hlock_update_mem_strict_load1:= fresh "Hlock_update_mem_strict_load1" in
          dup Hlock as Hlock_update_mem_strict_load1;
          let m2'':=fresh "m2''" in 
          let Hlock_update_mem_strict_load2:=fresh "Hlock_update_mem_strict_load2" in 
          let Hinj2:=fresh "Hinj2" in 
          eapply lock_update_mem_strict_load_inject in Hlock
            as (m2''&Hlock_update_mem_strict_load2&Hinj2);
          eauto; try (eapply CMatch; eauto); [idtac]
        end.
      Ltac get_injection_thread_mem:=
        match goal with
          [CMatch: concur_match _ ?mu ?st1 ?m1' ?st2 ?m2' |- _ ] =>
          let Hinj':= fresh "Hinj'" in
          assert (Hinj': Mem.inject mu m1' m2') by
              (rewrite <- (cur_equiv_restr_mem_equiv m1') by eassumption;
               rewrite <- (cur_equiv_restr_mem_equiv m2') by eassumption;
               eapply INJ_threads; eauto)
        end.
      Ltac use_retroactive_int_diagram_atx:=
        match goal with
          [Hstrict: strict_evolution_diagram _ _ _ _ _ _ _  |- _] =>
          eapply retroactive_int_diagram_atx in Hstrict;
          eauto; [idtac]; (* This checks there is only one goal left! *)
          inversion Hstrict; unify_at_ext      
        end.
      
      Ltac inject_lock_update_mem_strict:=
        lazymatch goal with
          [CMatch: concur_match _ ?mu ?st1 ?m1' ?st2 ?m2',
                   Hlock: lock_update_mem_strict _ _ _ _ _ |- _ ] =>
          let Hlock_update_mem_strict1:= fresh "Hlock_update_mem_strict1" in
          dup Hlock as Hlock_update_mem_strict1;
          let m2'':=fresh "m2''" in 
          let Hlock_update_mem_strict2:=fresh "Hlock_update_mem_strict2" in 
          let Hinj2:=fresh "Hinj2" in 
          eapply lock_update_mem_strict_inject in Hlock
            as (m2''&Hlock_update_mem_strict2&Hinj2);
          eauto; try (eapply CMatch; eauto); [ ]
        end.
      Ltac left_diagram:=
        (* 1. Set up the injection*)
        get_injection_thread_mem;
        (* 2. Now we expand the diagram backwards *)
        use_retroactive_int_diagram_atx;
        inj_args_inv;
        (* There are different types of left diagram.
`            each case is a different type. *)
        first 
          [inject_lock_update_mem_strict_load
          | inject_lock_update_mem_strict].
      

      (*+ tactics to push 
         mem_compat
         forward (in diagrams) *)
      
      Lemma mem_compatible_fullThreadUpdate:
        forall Sem Tp m st st' st'' l lock_info
          i (cnt:ThreadPool.containsThread st i) c res,
          @mem_compatible Sem Tp st m ->
          permMapLt_pair res (getMaxPerm m) ->
          permMapLt_pair lock_info (getMaxPerm m) ->
          Mem.valid_block m (fst l) ->
          st'' = ThreadPool.updLockSet st' l lock_info ->
          st' = ThreadPool.updThread cnt c res ->
          @mem_compatible Sem Tp st'' m.
      Proof.
        intros.
        eapply mem_compatible_updLock; eauto. clear H1 H2 H3.
        eapply mem_compatible_updthread; eauto.
      Qed.
      Lemma mem_compatible_fullThreadUpdate_join1:
        forall {Sem Tp} st c m st' st'' b ofs th_perm lock_perm
               i (cnt:ThreadPool.containsThread st i) ,
          @mem_compatible Sem Tp st m ->
          permMapJoin_pair th_perm lock_perm (ThreadPool.getThreadR cnt) ->
          Mem.valid_block m b ->
          st'' = ThreadPool.updLockSet st' (b, ofs) lock_perm ->
          st' = ThreadPool.updThread cnt c th_perm ->
          @mem_compatible Sem Tp st'' m.
      Proof.
        intros. eapply mem_compatible_fullThreadUpdate; simpl; eauto.
        - apply (permMapLt_pair_trans211 _ (ThreadPool.getThreadR cnt)).
          * eapply permMapJoin_lt_pair1; eassumption.
          * eapply H.
        - apply (permMapLt_pair_trans211 _ (ThreadPool.getThreadR cnt)).
          * eapply permMapJoin_lt_pair2; eassumption.
          * eapply H.
        - simpl; auto.
      Qed.
      
      Lemma store_cmpt:
        forall Sem Tp st chunk b ofs v m m' p Hlt ,
          Mem.store chunk (@restrPermMap p m Hlt ) b ofs v = Some m' ->
          @mem_compatible Sem Tp st m -> 
          @mem_compatible Sem Tp st m'.
      Proof.
        intros. 
        eapply mem_compat_Max in H0;
          try (symmetry; etransitivity).
        - eassumption.
        - symmetry; eapply store_max_equiv; eassumption.
        - apply restr_Max_equiv.
        - eapply Mem.nextblock_store; eassumption.
        - reflexivity.
      Qed.

      Ltac unfold_state_forward:=
        match goal with
        | H:?st' = fullThUpd_comp ?st _ _ _ _ (?b, ?ofs)
          |- _ => unfold fullThUpd_comp, fullThreadUpdate in H
        | H:= fullThUpd_comp ?st _ _ _ _ (?b, ?ofs)
              |- _ => unfold fullThUpd_comp, fullThreadUpdate in H
            | H:?st' = fullThreadUpdate ?st _ _ _ _ (?b, ?ofs)
              |- _ => unfold fullThreadUpdate in H
            | H:= fullThreadUpdate ?st _ _ _ _ (?b, ?ofs)
                  |- _ => unfold fullThreadUpdate in H
        end.
      
      Lemma permMapLt_empty_pair:
        forall a, permMapLt_pair (pair0 empty_map) a.
      Proof.
        intros ?. solve_pair; apply empty_LT.
      Qed.
      Lemma permMapLt_compute_inject_pair:
        forall mu p1 p2 m1 m2 Hlt1 Hlt2,
          Mem.inject mu (@restrPermMap p1 m1 Hlt1) (@restrPermMap p2 m2 Hlt2) ->
          forall a1 a2 b1 b2,
            permMapLt_pair (computeMap_pair a1 b1) (getMaxPerm m1) ->
            permMapLt_pair a2 (getMaxPerm m2) ->
            b2 = virtueThread_inject m2 mu b1 ->
            permMapLt_pair (computeMap_pair a2 b2) (getMaxPerm m2).
      Proof.
        intros **.
        eapply permMapLt_computeMap_pair; eauto.
        subst b2; eapply deltaMapLt2_inject_pair;
          try eassumption.
        eapply permMapLt_computeMap_pair'.
        eassumption.
      Qed.
      Lemma permMapLt_compute_inject_pair_useful':
        forall ocd mu st1 st2 m1 m2,
          concur_match ocd mu st1 m1 st2 m2 ->
          forall a1 i (cnt1: containsThread st1 i) cnt2 b1 b2 ,
            permMapLt_pair (computeMap_pair a1 b1) (getMaxPerm m1) ->
            (*permMapLt_pair (@getThreadR _ _ i st2 cnt2) (getMaxPerm m2) -> *)
            b2 = virtueThread_inject m2 mu b1 ->
            permMapLt_pair (computeMap_pair (@getThreadR _ _ i st2 cnt2) b2)
                           (getMaxPerm m2).
      Proof.
        intros **.
        pose proof (memcompat1 H) as Hcmpt1.
        pose proof (memcompat2 H) as Hcmpt2.
        eapply permMapLt_compute_inject_pair; eauto.
        eapply H.
        eapply Hcmpt2.

        Unshelve.
        all: eauto.
        eapply Hcmpt1.
        eapply Hcmpt2.
      Qed.
      
      Lemma permMapLt_compute_inject_pair_useful:
        forall ocd mu st1 st2 m1 m2,
          concur_match ocd mu st1 m1 st2 m2 ->
          forall a1 i (cnt1: containsThread st1 i) cnt2 b1 ,
            permMapLt_pair (computeMap_pair a1 b1) (getMaxPerm m1) ->
            permMapLt_pair (computeMap_pair (@getThreadR _ _ i st2 cnt2)
                                            (virtueThread_inject m2 mu b1))
                           (getMaxPerm m2).
      Proof. intros; eapply permMapLt_compute_inject_pair_useful'; eauto. Qed.
      
      Definition permMapLt_range_pair perm b lo hi:=
        pair1_prop  (permMapLt_range perm b lo hi).
      Hint Unfold permMapLt_range_pair: pair.
      
      Lemma permMapLt_setPermBlock_pair:
        forall perm2 b ofs sz perm1 op,
          permMapLt_range_pair perm2 b ofs (ofs + Z.of_nat sz) op  ->
          permMapLt_pair perm1 perm2 ->
          permMapLt_pair (setPermBlock_pair b ofs op perm1 (pair0 sz)) perm2.
      Proof.
        intros ? ? ? ?; solve_pair.
        intros; eapply permMapLt_setPermBlock; assumption.
      Qed.
      Lemma permMapLt_range_pair_left:
        forall a b lo hi perm1 perm2,
          permMapLt_range a b lo hi perm1 ->
          Mem.perm_order'' perm1 perm2 ->
          permMapLt_range_pair a b lo hi (perm1, perm2).
      Proof.
      Admitted.
      Lemma permMapLt_range_pair_right:
        forall a b lo hi perm1 perm2,
          permMapLt_range a b lo hi perm2 ->
          Mem.perm_order'' perm2 perm1 ->
          permMapLt_range_pair a b lo hi (perm1, perm2).
      Proof.
      Admitted.

      Ltac permMapLt_range_pair_simpl:=
        first [eapply permMapLt_range_pair_left; [|constructor]
              |eapply permMapLt_range_pair_right; [|constructor]].
      Lemma permMapLt_range_trans:
        forall perms1 perms2 b lo hi perm,
          permMapLt_range perms1  b lo hi perm ->
          permMapLt perms1 perms2 ->                                
          permMapLt_range perms2  b lo hi perm.
      Proof.
      Admitted.
      Lemma range_mem_permMapLt:
        forall b lo hi p m,
          Mem.range_perm m b lo hi Cur p ->
          permMapLt_range (getCurPerm m) b lo hi (Some p).
      Proof.
      Admitted.

      
      Ltac apply_permMapLt_compute_inject_pair:=
        match goal with
        | |- permMapLt_pair (computeMap_pair _ _) _ =>
          eapply permMapLt_compute_inject_pair_useful; eauto
        | |- permMapLt_pair (computeMap _ _ , computeMap _ _) _ =>
          eapply permMapLt_compute_inject_pair_useful; eauto
        end.
      
      Lemma lock_update_mem_permMapLt_range_Cur:
        forall b ofs m m' v,
          lock_update_mem_strict b ofs m m' v -> 
          permMapLt_range (getCurPerm m) b ofs (ofs + LKSIZE) (Some Writable).
      Proof.
        intros * HH; inv HH.
        eapply range_mem_permMapLt;  eassumption.
      Qed.
      Lemma lock_update_mem_permMapLt_range_Max:
        forall b ofs m m' v,
          lock_update_mem_strict b ofs m m' v -> 
          permMapLt_range (getMaxPerm m) b ofs (ofs + LKSIZE) (Some Writable).
      Proof.
        intros; eapply permMapLt_range_trans; try eapply cur_lt_max.
        eapply lock_update_mem_permMapLt_range_Cur; eassumption.
      Qed.

      (** *solve_permMapLt_easy
          for all those permMapLt_pair that can be solved "directly"
       *)
      Ltac solve_permMapLt_lock_update_mem:=
        first [eapply lock_update_mem_permMapLt_range_Cur; eassumption
              |eapply lock_update_mem_permMapLt_range_Max; eassumption].
      Ltac solve_permMapLt_cmpt:=
        match goal with
          [Hcmpt: mem_compatible ?st ?m
           |- permMapLt_pair (@getThreadR _ _ _ ?st _) (getMaxPerm ?m)] =>
          eapply Hcmpt
        |[Hcmpt: mem_compatible ?st ?m,
                 Hlock_perm: ThreadPool.lockRes ?st _ = Some ?pmaps
          |- permMapLt_pair ?pmaps (getMaxPerm ?m)] =>
         eapply Hcmpt
        end.
      
      Ltac solve_permMapLt_join:=
        match goal with
        | H:permMapJoin_pair ?b _ _ |- permMapLt_pair2 ?b _ =>
          now apply (permMapJoin_lt_pair1 _ _ _ H)
        | H:permMapJoin_pair _ ?b _ |- permMapLt_pair2 ?b _ =>
          now apply (permMapJoin_lt_pair2 _ _ _ H)
        end.
      Ltac solve_permMapLt_empty_pair:=
        match goal with
        | |- permMapLt_pair (pair0 empty_map) _ =>
          eapply permMapLt_empty_pair
        | |- permMapLt_pair (empty_map,empty_map) _ =>
          eapply permMapLt_empty_pair
        end.
      Ltac solve_permMapLt_easy:=
        (* for those goals that can be solved directly*)
        first
          [ eassumption
          | solve_permMapLt_empty_pair
          | solve_permMapLt_lock_update_mem
          | solve_permMapLt_join
          (* slower :*)
          | solve_permMapLt_cmpt ].
      Ltac solve_permMapLt_set_new_perms:=
        match goal with
          [Hnp: set_new_mems _ _ _ _ ?new_perms
           |- permMapLt_pair ?new_perms (getMaxPerm _)] =>
          inv Hnp; eapply permMapLt_setPermBlock_pair;
          [ permMapLt_range_pair_simpl|];
          solve_permMapLt_easy
        end.
      Ltac solve_permMapLt_pair:=
        try eassumption;
        subst_set; try subst;
        first
          [ solve_permMapLt_easy
          | eapply permMapLt_pair_trans211;
            [solve_permMapLt_easy  
            |solve_permMapLt_cmpt]
          | solve_permMapLt_set_new_perms
          (* inject one sometimes gets stuck. *)
          | solve[ apply_permMapLt_compute_inject_pair]
          | idtac "permMapLt_pair cant be solved:"; print_goal].
      (*We can use the previous to solve regular permMapLt *)
      Ltac solve_permMapLt:=
        let H:= fresh in
        match goal with
        | [ |- permMapLt (fst ?a) ?b] =>
          assert (H:permMapLt_pair a b) by solve_permMapLt_pair
        | [|- permMapLt (snd ?a) ?b] =>
          assert (H:permMapLt_pair a b) by solve_permMapLt_pair
        end; apply H.
      Ltac solve_valid_block:=
        subst_set; subst;
        match goal with
        |  |- Mem.valid_block ?m ?b =>
           solve[simpl; eapply Mem.valid_block_inject_1; eauto]
        (* destruct (mem_l emmas.valid_block_dec m b) as [n|n]; eauto;
            eapply Mem.mi_freeblocks in n; eauto;
            unify_injection *)
        | |- Mem.valid_block ?m ?b =>
          solve[simpl; eapply Mem.valid_block_inject_2; eauto]
        end.
      Ltac forward_cmpt' H:=
        let Hcmpt_update_state:= fresh "Hcmpt_update" in
        eapply (@mem_compatible_fullThreadUpdate _ (TP _)) in H
          as Hcmpt_update_state; try reflexivity; simpl;
        [ idtac
        | eassumption
        | solve_permMapLt_pair 
        | solve_permMapLt_pair
        | solve_valid_block ];
        idtac.
      
      Ltac forward_state_cmpt_all :=
        let Hcmpt_fwd:= fresh "Hcmpt_update" in
        repeat unfold_state_forward;
        (* Find the states and the mems.*)
        match goal with
        |[ H: ?st' = updLockSet (@updThread _ _ _ ?st _ _ _) _ _ |- _ ] =>
         let M:= fresh in mark M st';
                          forward_cmpt' H;
                          try forward_state_cmpt_all;
                          clear M
        |[ st':= updLockSet (@updThread _ _ _ ?st _ _ _) _ _ |- _ ] =>
         let M:= fresh in mark M st';
                          let H:= fresh in
                          match goal with
                            [st':= ?ST' |- _] => assert (H: st' = ST') by (subst st'; reflexivity)
                          end; forward_cmpt' H;
                          (try forward_state_cmpt_all);
                          clear M H
        end.

      (* TODO move this to the highest place possible (there the lmmas are defined?)*)
      Ltac solve_max_equiv:=
        (* solves the following cases:
               - reflexivity
               - just a restriction.
               - after a Mem.store.
               - a compbination of two of the previous ones. *)
        solve[ etransitivity;
               (* try Mem.store; *)
               first [(eapply store_max_equiv; eassumption)|
                      (symmetry; eapply store_max_equiv; eassumption)|
                      idtac];
               (*try straight restrictions*)
               first [(eapply restr_Max_equiv)|
                      (symmetry; eapply restr_Max_equiv)|
                      idtac];
               (*try restrictions of another hypothesis*)
               first [(eapply Max_equiv_restr; eassumption)|
                      (symmetry; eapply Max_equiv_restr; eassumption)|
                      idtac];
               (*finally, if there are goals left, reflexivity*)
               try reflexivity].
      Ltac solve_nextblock_eq:=
        (* solves the following cases:
               - reflexivity
               - just a restriction.
               - after a Mem.store.
               - a compbination of two of the previous ones. *)
        solve[ etransitivity;
               (* try Mem.store; *)
               first [(eapply Mem.nextblock_store; eassumption)|
                      (symmetry; eapply Mem.nextblock_store; eassumption)|
                      idtac];
               (*finally, if there are goals left, reflexivity*)
               try reflexivity].
      Ltac pose_max_equiv:=
        match goal with
          [H:lock_update_mem_strict_load _ _ _ ?m ?m' _ _ |- _] =>
          try match goal with [Hmax_eq: Max_equiv m m'|- _]=> fail 2 end;
          let Hmax_eq:= fresh "Hmax_eq" in
          let Hnb_eq:= fresh "Hnb_eq" in
          assert (Hmax_eq: Max_equiv m m') by (inv H; solve_max_equiv);
          assert (Hnb_eq: Mem.nextblock m = Mem.nextblock m')
            by (inv H; solve_nextblock_eq)
        | [H:lock_update_mem_strict _ _ ?m ?m' _ |- _] =>
          try match goal with [Hmax_eq: Max_equiv m m'|- _]=> fail 2 end;
          let Hmax_eq:= fresh "Hmax_eq" in
          let Hnb_eq:= fresh "Hnb_eq" in
          assert (Hmax_eq: Max_equiv m m') by (inv H; solve_max_equiv);
          assert (Hnb_eq: Mem.nextblock m = Mem.nextblock m')
            by (inv H; solve_nextblock_eq)
        end.
      Ltac forward_mem_cmpt_all :=
        match goal with
        |[ Hmax_equiv: Max_equiv ?m ?m',
                       Hnb_eq:  Mem.nextblock ?m =  Mem.nextblock ?m',
                                Hcmpt: mem_compatible ?st ?m |- _ ] =>
         try match goal with [H: mem_compatible st m' |- _ ] => fail 2 end;
         let Hcmpt_mem_fwd:= fresh "Hcmpt_mem_fwd" in 
         try eapply mem_compat_Max in Hcmpt as Hcmpt_mem_fwd;
         [| eassumption| eassumption]
        end.
      Ltac forward_cmpt_all:=
        forward_state_cmpt_all;
        repeat forward_mem_cmpt_all.
      (*+ End forward CMPT*)


      
      Lemma mem_cur_lt_max:
        forall m, permMapLt (getCurPerm m) (getMaxPerm m).
      Proof.
        intros.
        intros ??.
        rewrite getCurPerm_correct, getMaxPerm_correct.
        unfold permission_at.
        eapply Mem.access_max.
      Qed.
      
      Lemma make_mem_eq:
        forall m m',
          Mem.mem_contents m = Mem.mem_contents m' ->
          Mem.mem_access m = Mem.mem_access m' ->
          Mem.nextblock m = Mem.nextblock m' ->
          m = m'.
      Proof.
        intros ??.
        destruct m, m'; simpl.
        intros **; subst.
        assert (access_max = access_max0).
        { apply Axioms.proof_irr. }
        assert (nextblock_noaccess = nextblock_noaccess0).
        { apply Axioms.proof_irr. }
        assert (contents_default = contents_default0).
        { apply Axioms.proof_irr. }
        intros **; subst.
        reflexivity.
      Qed.
      Lemma restrPermMap_equiv_eq:
        forall perm perm' m m' Hlt Hlt',
          access_map_equiv perm perm' ->
          m = m' ->
          @restrPermMap perm  m  Hlt =
          @restrPermMap perm' m' Hlt'.
      Proof.
        intros. subst m.
        unfold restrPermMap.
        eapply make_mem_eq; simpl; auto.
        remember (snd (Mem.mem_access m')) as T.
        f_equal.
        unfold PTree.map.
        remember 1%positive as i eqn:HH.
        clear HH; revert i; clear -H.
        induction T; auto.
        intro; simpl.
        f_equal; eauto.
        destruct o; f_equal.
        extensionality ofs.
        extensionality k.
        destruct k; auto.
        erewrite H; reflexivity.
      Qed.
      
      Definition pos_descend p: positive:=
        match p with
        | xI p' => p'
        | xO p' => p'
        | xH => xH
        end.
      Definition pos_descend_rev p:=
        PTree.prev (pos_descend (PTree.prev p)).
      Definition pos_ascend p b: positive:=
        match p with
        | xI p' => (xI b)
        | xO p' => (xO b)
        | xH => b
        end.
      Lemma xmap_step:
        forall {A B} t f p,
          @PTree.xmap A B f t p =
          PTree.xmap (fun b => f (PTree.prev_append p b)) t 1.
      Proof.
        intros A B t; induction t.
        - reflexivity.
        - intros; simpl.
          f_equal.
          + rewrite IHt1.
            symmetry.
            rewrite IHt1.
            f_equal.
          + rewrite IHt2.
            symmetry.
            rewrite IHt2.
            f_equal.
      Qed.
      
      Lemma trivial_map':
        forall {A} t F,
          (forall b f, t ! b = Some f -> F b f = f) ->
          @PTree.map A A F t = t.
      Proof.
        intros ? ?.
        unfold PTree.map.
        (* remember 1%positive as p eqn:HH; clear HH; revert p.*)
        induction t0; try reflexivity.
        unfold PTree.map; simpl.
        intros. f_equal.
        - intros.
          erewrite xmap_step.
          erewrite <- IHt0_1 at 2.
          reflexivity.
          intros; simpl. rewrite H; auto.
        - destruct o; eauto.
          
        - intros.
          erewrite xmap_step.
          erewrite <- IHt0_2 at 2.
          reflexivity.
          intros; simpl. rewrite H; auto.
      Qed.
      Lemma mem_is_restr_eq:
        forall m, m = restrPermMap (mem_cur_lt_max m).
      Proof.
        intros.
        pose proof (Clight_bounds.Mem_canonical_useful m) as Hbound.
        

        rewrite RPM.
        destruct m; simpl in *.
        eapply easy_mem_eq; try reflexivity.
        simpl. simpl.
        clear - hb Hbound.
        destruct mem_access; f_equal; simpl.
        - extensionality ofs.
          extensionality k.
          destruct k; auto.
        - match goal with
            |- context[
                   PTree.map ?access _
                 ] => replace access with
              (fun b f ofs k => match k with
                                | Max => f ofs Max
                                | Cur => (o, t0) !! b ofs Cur
                                end)
              
          end.
          2: { extensionality b.
               extensionality f.
               extensionality ofs.
               extensionality k.
               destruct k; auto.
               symmetry; apply getCurPerm_correct.
          }
          rewrite trivial_map'; auto.
          intros.
          extensionality ofs.
          extensionality k.
          destruct k; auto.
          unfold PMap.get; simpl.
          rewrite H; reflexivity.
      Qed.



      
      
      (* Line: 5367 *)
      Lemma release_step_diagram_compiled:
        let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
        forall (angel: virtue) (cd : compiler_index) mu (*tr2*)
               st1 (m1 m1' m1'' : mem) Hcnt1 st2 (m2' : mem) Hcnt2
               (Hsame_cnt: same_cnt hb st1 st2 Hcnt1 Hcnt2)
               b1 ofs lock_map (code1 : semC)  (code2 : Asm.state)
               (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
               (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
               (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
               (Hangel_bound: sub_map_virtue angel (getMaxPerm m1'))
               (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
               (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
               (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                                Some (UNLOCK, (Vptr b1 ofs :: nil)%list))
               (Hlock_update_mem_strict_load:
                  lock_update_mem_strict_load b1 (unsigned ofs)  (snd (getThreadR Hcnt1))
                                              m1' m1'' vzero vone)
               (HisLock: lockRes st1 (b1, unsigned ofs) = Some lock_map)
               (Hrmap: empty_doublemap lock_map),
          let newThreadPerm1:= (computeMap_pair (getThreadR Hcnt1) (virtueThread angel)) in
          forall (Hjoin_angel: permMapJoin_pair newThreadPerm1 (virtueLP angel) (getThreadR Hcnt1))
                 (Hlt1 : permMapLt (thread_perms _ _ Hcnt1) (getMaxPerm m1'))
                 (Hlt2 : permMapLt (thread_perms _ _ Hcnt2) (getMaxPerm m2'))
                 (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
          exists evnt2 (st2' : t) (m2'' : mem),
            let evnt:= build_release_event
                         (b1, unsigned ofs) (fst (virtueThread angel)) m1'' in 
            let st1':= fullThUpd_comp
                         st1 hb Hcnt1 (Kresume (SST code1) Vundef)
                         angel (b1, unsigned ofs)  in
            concur_match (Some cd) mu st1' m1'' st2' m2'' /\
            inject_sync_event mu evnt evnt2 /\
            let Hcmpt2:= memcompat2 CMatch in
            syncStep(Sem:=HybridSem (Some (S hb)))
                    true Hcnt2 Hcmpt2 st2' m2'' evnt2.
      Proof.
        intros; simpl in *.
        (*Add all the memories and theeir relations *)
        get_mem_compatible.
        get_thread_mems.
        clean_proofs. rename abs_proof into Hcmpt2.

        (* NOTE: this proof has three diagrams:
               - Left Diagram:      Generated by interference by other threads 
               - Middle Diagram:    The compiler diagram
               - Right Diagram:     Generated by interference by other threads

              m1 -lev1-> m1' -dpm-> m1'' -lev1'-> m1'''
              |          |          |             |
              |   Left   |          |    Right    |
              |          |          |             |
              m2 -lev2-> m2' -dpm-> m2'' -lev2'-> m2'''
              !          !          !             !     
              m2 -lev2-> m21'-dpm-> m21''-lev2'-> m21'''

              TODO: the last layer might not be needed?
         *)
        
        (** * 0. Stablish facts about m2' *)

        
        (** * 1. Set all the at_externals for LEFT diagram m1 m1' m2 m2' *)
        left_diagram.
        set (virtueThread1:= virtueThread angel).
        set (virtueLP1 :=   virtueLP angel   ).
        set (virtueThread2  :=   virtueThread_inject m2' mu  virtueThread1).
        set (virtueLP2 :=   virtueLP_inject m2'' mu virtueLP1).
        set (ofs2      :=   add ofs (repr delta)).
        set (new_cur2:=(computeMap (fst (getThreadR Hcnt2)) (fst virtueThread2),
                        computeMap (snd (getThreadR Hcnt2)) (snd virtueThread2))).
        set (st2':=(updLockSet
                      (updThread Hcnt2 (Kresume (TST code2) Vundef) new_cur2)
                      (b2, unsigned ofs2) virtueLP2)).
        remember (fullThUpd_comp
                    st1 hb Hcnt1 (Kresume (SST code1) Vundef) angel
                    (b1, unsigned ofs)) as st1'.

        
        (* assert (H: ThreadPool (Some (S hb)) = @t dryResources (HybridSem (@Some nat (S hb))))
          by reflexivity.
        dependent rewrite <- H in st2'. clear H. *) 
        
        assert (Hjoin_angel2:permMapJoin_pair new_cur2 virtueLP2 (getThreadR Hcnt2)).
        { admit. }
        repeat pose_max_equiv.
        forward_cmpt_all.
        rename Hcmpt_mem_fwd into Hcmpt2'.
        rename Hcmpt_mem_fwd0 into Hcmpt1'.
        
        

        (** * 4. Finally we proceed with the goal: existentials. *)
        
        eexists.
        exists st2', m2''.
        split; [|split].
        
        - assert (Hlt11 : permMapLt (fst newThreadPerm1) (getMaxPerm m1'')).
          { unfold Max_equiv in *; rewrite <- Hmax_eq0; solve_permMapLt. }
          assert (Hlt21 : permMapLt (fst new_cur2) (getMaxPerm m2'')).
          { unfold Max_equiv in *; rewrite <- Hmax_eq; solve_permMapLt. }
          
          cut (concur_match (Some cd) mu st1' m1'' st2' m2''); [subst st1'; auto|].
          
          eapply concur_match_update_lock; eauto.
          + !context_goal lock_update_mem.
            eapply lock_update_mem_strict_load_mem_update.
            eapply Hlock_update_mem_strict_load1.
          + !context_goal (lock_update_mem).
            eapply lock_update_mem_strict_load_mem_update.
            eapply Hlock_update_mem_strict_load2.
          + !context_goal Mem.inject.
            rewrite RPM.
            instantiate(2:=fst new_cur2);
              instantiate(3:=fst newThreadPerm1).
            apply inject_restr; auto.
            * !goal (mi_perm_perm mu (fst newThreadPerm1) (fst new_cur2)).
              admit.
            * !goal (mi_memval_perm mu (fst newThreadPerm1)
                                    (Mem.mem_contents m1'') (Mem.mem_contents m2'')).
              admit.
            * !goal (mi_perm_inv_perm mu (fst newThreadPerm1) (fst new_cur2) m1'').
              admit.
          + !goal (@invariant (HybridSem _) _ st1'). admit.
          + !goal (@invariant (HybridSem _ ) _ st2'). admit.
          + !goal(perm_preimage mu _ _).
            instantiate(1:=snd new_cur2); instantiate (1:=snd newThreadPerm1).
            subst newThreadPerm1 new_cur2; simpl.
            eapply perm_preimage_compute.
            ++ eapply CMatch.
            ++ subst virtueThread2.
               cut (perm_perfect_image_dmap_pair
                      mu virtueThread1 (virtueThread_inject m2' mu virtueThread1)).
               { intros HH; apply HH. }
               subst virtueThread1.
               eapply inject_virtue_perm_perfect_image_dmap; eauto.
               admit. (*from join 1*)
               eapply full_inject_dmap_pair.
               ** !goal (Events.injection_full mu _ ).
                  eapply CMatch.
               ** !goal (dmap_valid_pair _ _).
                  apply join_dmap_valid_pair.
                  eapply Hangel_bound.
          + !goal (Mem.inject mu _ _).
            apply inject_restr; auto.
            * !goal (mi_perm_perm mu (snd newThreadPerm1) (snd new_cur2)).
              admit.
            * !goal (mi_memval_perm mu (snd newThreadPerm1)
                                    (Mem.mem_contents m1'') (Mem.mem_contents m2'')).
              admit.
            * !goal (mi_perm_inv_perm mu (snd newThreadPerm1) (snd new_cur2) m1'').
              admit.
          +  (* Proof of match goes after the comment *)
            
            { !context_goal one_thread_match.
              eapply build_match_compiled; auto.
              instantiate(1:= Hlt21).
              instantiate(1:=(Kresume (TST code2) Vundef)).
              instantiate(1:= Hlt11).
              instantiate(1:=(Kresume (SST code1) Vundef)).
              subst st1' st2'.
              clean_cnt.
              eapply CThread_Resume.
              intros j'' s1' m1''' m2''' lev1' lev2'.
              intros Hstrict_evolution' (*Hincr'*) Hinterference1' Hinterference2'
                     Hafter_ext.
              remember (fst virtueThread1) as dpm1.
              remember (Events.Event_acq_rel lev1 dpm1 lev1' :: nil) as rel_trace.
              Tactic Notation "dont" tactic(t):= idtac. 
              


              (** *0 . Simplifications to do outside the l emma*)

              assert (Hext_rel1': extcall_release
                                    (Genv.globalenv (Ctypes.program_of_program C_program)) 
                                    (Vptr b1 ofs :: nil) m1
                                    (Events.Event_acq_rel lev1 (fst virtueThread1) lev1' :: nil)
                                    Vundef m1''').
              { inversion Hlock_update_mem_strict_load1; subst vload vstore.
                subst rel_trace; econstructor; try eassumption.
                econstructor; eauto.
                subst newThreadPerm1; simpl.
                (* need to replace the way we construct virtue 1:
                 do it by replacein thread_perms with (getCurperm m1')
                 they are the same by hypothesis
                 *)
                rewrite RPM.
                admit.
              } 
              assert (Hext_rel1: Events.external_call UNLOCK
                                                      (Clight.genv_genv Clight_g)
                                                      (Vptr b1 ofs :: nil)
                                                      m1 rel_trace Vundef m1''').
              { simpl; rewrite ReleaseExists.
                subst rel_trace dpm1; eauto. }
              clear Hext_rel1'.
              
              assert (Hext_rel2: extcall_release
                                   Asm_g (Vptr b2 ofs2 :: nil) m2
                                   (Events.Event_acq_rel lev2 (fst virtueThread2) lev2' :: nil)
                                   Vundef m2''').
              { inversion Hlock_update_mem_strict_load2; subst vload vstore.
                econstructor; eauto.
                subst m_writable_lock_1; econstructor.
                3: { reflexivity. }
                - rewrite <- Hstore; f_equal.
                  admit.
                - subst new_cur2; simpl.
                  !goal (computeMap (thread_perms hb st2 Hcnt2) _ =
                         computeMap (getCurPerm m2') _).
                  (* They are equiv but not equal... *)
                  admit. (* TODO*)
              }
              
              assert (Hnb_eq': Mem.nextblock (restrPermMap Hlt21) =
                               Mem.nextblock m2').
              { symmetry; etransitivity; eauto. }
              
              subst rel_trace.
              eapply large_external_diagram; try reflexivity; eauto.
              - exact unlock_doesnt_return.
              - reflexivity.
              - !goal(Events.inject_delta_map _ _ _ ).
                admit. (* by constructions the birtues inject*)
              - simpl; rewrite ReleaseExists; eauto.
              - exploit (interference_consecutive_until Hinterference2).
                rewrite <- Hnb_eq'; simpl; auto.
              - exploit (interference_consecutive_until Hinterference2').
                simpl; auto.
            }

          + !context_goal memval_inject.
            repeat econstructor.
          + !goal(lock_update _ st1 _ _ _ _ st1').
            econstructor;
              subst st1' newThreadPerm1 virtueThread1;
              unfold fullThUpd_comp, fullThreadUpdate.
            reflexivity.

            
          + !goal(lock_update _ st2 _ _ _ _ st2').
            econstructor;
              subst st2' new_cur2 virtueLP2  ofs2 virtueLP1;
              unfold fullThUpd_comp, fullThreadUpdate.
            repeat f_equal.
            * f_equal.
              !goal (unsigned (add ofs (repr delta)) = unsigned ofs + delta);
                admit.
              
        - econstructor.
          + econstructor; eauto.
          + instantiate (1:= Some (build_delta_content (fst virtueThread2) m2'')).
            simpl.  
            admit. (*TODO define inject_delta_content *)
            
        (* injection of the event*)
        (* Should be obvious by construction *)
        - (* HybridMachineSig.external_step *)
          assert (Hofs2: intval ofs2 = unsigned ofs + delta).
          { admit. }
          intros.
          rewrite <- Hofs2.
          
          eapply step_release with
              (b:= b2)
              (virtueThread:=virtueThread2)
              (virtueLP:=virtueLP2);
            eauto; try reflexivity;
              try unfold HybridMachineSig.isCoarse,
              HybridMachineSig.HybridCoarseMachine.scheduler.
          rename m2' into MMM.
          rename m2 into MMM2.
          
          + (* bounded_maps.sub_map *)
            
            subst virtueThread2.
            unfold virtueThread_inject.
            destruct (virtueThread angel) as (virtue11, virtue12)
                                               eqn:HeqvirtueThread1.
            cbv iota beta delta[fst] in *.
            destruct Hangel_bound as [Hbounded HboundedLP].
            destruct Hbounded as [Hbound1 Hbound2].
            split.
            -- eapply inject_virtue_sub_map.
               eapply CMatch.
               inversion HeqvirtueThread1.
               destruct angel; simpl in H0.
               subst virtueThread0.
               eassumption.
            -- eapply inject_virtue_sub_map.
               eapply CMatch.
               inversion HeqvirtueThread1.
               destruct angel; simpl in H0.
               subst virtueThread0.
               eassumption.
               
          + (* bounded_maps.sub_map *)
            
            destruct Hangel_bound as [Hbounded HboundedLP].
            destruct HboundedLP as (?&?&Hbound).
            move Hbound at bottom.
            subst virtueLP2; simpl.
            
            
            eapply (proj1 (Logic.and_assoc _ _ _)).
            split.

            (*Easy ones: the default is trivial:
                  bounded_maps.map_empty_def
             *)
            unfold virtueLP_inject,
            bounded_maps.map_empty_def, inject_access_map;
              simpl; auto.

            assert (HboundedLP':
                      bounded_maps.sub_map (snd (fst virtueLP1)) (snd (getMaxPerm m1')) /\
                      bounded_maps.sub_map (snd (snd virtueLP1)) (snd (getMaxPerm m1'))
                   ) by (subst virtueLP1; eassumption).
            
            destruct virtueLP1 as (virtueLP_fst, virtueLP_snd).
            revert HboundedLP'.
            unfold virtueLP_inject, inject_access_map.
            simpl (fst _).
            simpl (snd _) at 3 6 9.
            

            (* eapply self_simulation.minject in matchmem. *)

            (* strong version of preserving max
               Not only preserves max, but also preserves the structure!
             *)
            
            (* replace m2'' with m2'*)
            inversion Hlock_update_mem_strict_load2; subst vload vstore.
            eapply store_max_eq in Hstore.
            move Hstore at bottom.
            subst m_writable_lock_1.
            unfold tree_map_inject_over_mem.
            repeat rewrite <- Hstore.
            repeat erewrite restr_Max_eq.
            
            intros (Hl & Hr); split;
              eapply inject_virtue_sub_map;
              try eapply CMatch; eauto.
            
          + (*invariant st2 *)
            eapply CMatch.
            
          + (* at_external for code 4. *)
            simpl in *.
            clean_cmpt.
            clean_cnt.
            rewrite RPM.
            admit.  (* at_external up to mem_equiv*)
            
          + (* Mem.range_perm *)
            (* Can read the lock *)
            !goal(Mem.range_perm _ _ _ (intval ofs2 + LKSIZE) Cur Readable).
            simpl.
            rewrite RPM.
            eapply permMapLt_range_mem.
            admit.

          + (* The load. *)
            inversion Hlock_update_mem_strict_load2; subst vload vstore.
            !goal ( Mem.load AST.Mint32 _ _ _ = Some _ ).
            rewrite <- Hload; f_equal; try assumption.
            * subst lock_mem; f_equal.
              clear; clean_proofs; reflexivity.
          + (* the store *)
            inversion Hlock_update_mem_strict_load2; subst vload vstore.
            !goal ( Mem.store AST.Mint32 _ _ _ _ = Some _ ).
            rewrite <- Hstore.
            f_equal; auto.
            * subst m_writable_lock_1.
              eapply restr_proof_irr'; auto; f_equal; auto.
          + (* content of lockres*)
            (* ThreadPool.lockRes st4 (b4', ofs4') *)
            (* NOTE: why is it rmap? It should be an injection of rmap 
                   ANSWER: the 'RMAP' is empty, so its injection is also empty... 
             *)
            !goal (ThreadPool.lockRes _ _ = Some _).
            subst ofs2.
            eapply INJ_lock_permissions_Some; eauto.

          + eapply empty_map_useful; eauto.
            apply inject_empty_maps; auto.
          + (* permissions join FST*)
            !goal(permMapJoin _ _ _ ).
            subst new_cur2.
            clear - Hjoin_angel2.
            clean_cnt; apply Hjoin_angel2.
            
          + (* permissions join SND *)
            !goal(permMapJoin _ _ _ ).
            subst new_cur2.
            clear - Hjoin_angel2.
            clean_cnt; apply Hjoin_angel2.
            
            
      Admitted. (* release_step_diagram_compiled *)
      (* Line: 5877 *)
      (* Lines: 5877 - 5367 = 510 *)
      
      
      
      
      (* angel,lock permissions and new thread permissions *)
      
      Lemma acquire_step_diagram_compiled:
        let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
        forall (angel: virtue) (cd : compiler_index)
               mu (*tr2*)
               st1 (m1 m1' m1'' : mem) Hcnt1 
               st2 (m2' : mem) Hcnt2
               (Hsame_cnt: same_cnt hb st1 st2 Hcnt1 Hcnt2)
               b1 ofs lock_perms (code1 : semC)  (code2 : Asm.state)
               (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
               (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
               (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
               (*Hangel_bound: sub_map_virtue angel (getMaxPerm m1')*)
               (Hangel_bound: pair21_prop bounded_maps.sub_map (virtueThread angel)
                                          (snd (getMaxPerm m1')))
               (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
               (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
               (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                                Some (LOCK, (Vptr b1 ofs :: nil)%list))
               (Hlock_update_mem_strict_load:
                  lock_update_mem_strict_load b1 (unsigned ofs)  (snd (getThreadR Hcnt1))
                                              m1' m1'' vone vzero)
               (HisLock: lockRes st1 (b1, unsigned ofs) = Some lock_perms),
          let newThreadPerm1:= (computeMap_pair (getThreadR Hcnt1) (virtueThread angel)) in
          let new_perms:= Build_virtue (virtueThread angel) (empty_map, empty_map) in
          forall (Hjoin_angel: permMapJoin_pair lock_perms (getThreadR Hcnt1) newThreadPerm1)
                 (Hlt_new: permMapLt_pair newThreadPerm1 (getMaxPerm m1'))
                 (Hlt1 : permMapLt (thread_perms _ _ Hcnt1) (getMaxPerm m1'))
                 (Hlt2 : permMapLt (thread_perms _ _ Hcnt2) (getMaxPerm m2'))
                 (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
          exists evnt2 (st2' : t) (m2'' : mem),
            let evnt:= build_acquire_event (b1, unsigned ofs) (fst (virtueThread angel)) m1'' in 
            let st1':= fullThUpd_comp st1 hb Hcnt1 (Kresume (SST code1) Vundef) new_perms (b1, unsigned ofs)  in
            concur_match (Some cd) mu st1' m1'' st2' m2'' /\
            inject_sync_event mu evnt evnt2 /\
            let Hcmpt2:= memcompat2 CMatch in
            syncStep(Sem:=HybridSem (Some (S hb)))
                    true Hcnt2 Hcmpt2 st2' m2'' evnt2.
      Proof.
        
        intros.
        (*Add all the memories and theeir relations *)
        get_mem_compatible.
        get_thread_mems.
        clean_proofs. rename abs_proof into Hcmpt2.
        
        remember (virtueThread angel) as virtueThread1.
        remember (virtueLP angel) as virtueLP1.
        
        (* NOTE: this proof has three diagrams:
               - Left Diagram:      Generated by interference by other threads 
               - Middle Diagram:    The compiler diagram
               - Right Diagram:     Generated by interference by other threads

              m1 -lev1-> m1' -dpm-> m1'' -lev1'-> m1'''
              |          |          |             |
              |   Left   |          |    Right    |
              |          |          |             |
              m2 -lev2-> m2' -dpm-> m2'' -lev2'-> m2'''
              !          !          !             !     
              m2 -lev2-> m21'-dpm-> m21''-lev2'-> m21'''

              TODO: the last layer might not be needed?
         *)
        
        (** * 0. Stablish facts about m2' *)
        
        (** * 1. Set all the at_externals for LEFT diagram m1 m1' m2 m2' *)
        left_diagram.
        set (virtueThread2:= virtueThread_inject m2' mu virtueThread1).
        set (virtueLP2:=virtueLP_inject m2'' mu virtueLP1).
        set (ofs2:= add ofs (repr delta)).
        set (new_cur2:= (computeMap_pair (getThreadR Hcnt2) virtueThread2)).
        set (st2':= (updLockSet
                       (updThread Hcnt2 (Kresume (TST code2) Vundef) new_cur2)
                       (b2, unsigned ofs2) (pair0 empty_map))).
        remember (fullThUpd_comp st1 hb Hcnt1 (Kresume (SST code1) Vundef) new_perms
                                 (b1, unsigned ofs)) as st1'.

        
        assert (H: ThreadPool (Some (S hb)) =
                   @t dryResources (HybridSem (@Some nat (S hb)))).
        { reflexivity. }
        dependent rewrite <- H in st2'. clear H.

        assert (Hjoin_angel2: permMapJoin_pair virtueLP2 (getThreadR Hcnt2)  new_cur2).
        { admit. }
        repeat pose_max_equiv.
        forward_cmpt_all.
        rename Hcmpt_mem_fwd into Hcmpt2'.
        rename Hcmpt_mem_fwd0 into Hcmpt1'.
        
        (** * 4. Finally we proceed with the goal: existentials. *)
        
        eexists.
        exists st2', m2''.
        split; [|split].
        
        - assert (Hlt11 : permMapLt (fst newThreadPerm1) (getMaxPerm m1'')).
          { unfold Max_equiv in *; rewrite <- Hmax_eq0; solve_permMapLt. }

          assert (Hlt21 : permMapLt (fst new_cur2) (getMaxPerm m2'')).
          { unfold Max_equiv in *; rewrite <- Hmax_eq; solve_permMapLt. }
          
          eapply concur_match_update_lock; eauto; try solve[subst st1'; eauto].
          + !context_goal lock_update_mem.
            eapply lock_update_mem_strict_load_mem_update.
            eapply Hlock_update_mem_strict_load1.
          + !context_goal (lock_update_mem).
            eapply lock_update_mem_strict_load_mem_update.
            eapply Hlock_update_mem_strict_load2.
          + !context_goal Mem.inject.
            rewrite RPM.
            instantiate(2:=fst new_cur2);
              instantiate(3:=fst newThreadPerm1).
            apply inject_restr; auto.
            * !goal (mi_perm_perm mu (fst newThreadPerm1) (fst new_cur2)).
              admit.
            * !goal (mi_memval_perm mu (fst newThreadPerm1)
                                    (Mem.mem_contents m1'') (Mem.mem_contents m2'')).
              admit.
            * !goal (mi_perm_inv_perm mu (fst newThreadPerm1) (fst new_cur2) m1'').
              admit.
          + !goal (@invariant (HybridSem _) _ _). admit.
          + !goal (invariant st2'). admit.
          + !goal(perm_preimage mu _ _).
            instantiate(1:=snd new_cur2); instantiate (1:=snd newThreadPerm1).
            subst newThreadPerm1 new_cur2; simpl.
            eapply perm_preimage_compute.
            ++ eapply CMatch.
            ++ subst virtueThread2.
               cut (perm_perfect_image_dmap_pair
                      mu virtueThread1 (virtueThread_inject m2' mu virtueThread1)).
               { intros HH; apply HH. }
               subst virtueThread1.
               eapply inject_virtue_perm_perfect_image_dmap; eauto.
               admit. (* from join but using a stronger one:
                         lockres + th_res = (th_res | virtue)
                         if virtue = Some, then one of the things that joins 
                         (lockres or th_res) is Some... and that is smaller 
                         than max.
                         
                       *)
               eapply full_inject_dmap_pair.
               ** !goal (Events.injection_full mu _ ).
                  eapply CMatch.
               ** !goal (dmap_valid_pair _ _).
                  apply join_dmap_valid_pair.
                  eapply Hangel_bound.
          + !goal (Mem.inject mu _ _).
            apply inject_restr; auto.
            * !goal (mi_perm_perm mu (snd newThreadPerm1) (snd new_cur2)).
              admit.
            * !goal (mi_memval_perm mu (snd newThreadPerm1)
                                    (Mem.mem_contents m1'') (Mem.mem_contents m2'')).
              admit.
            * !goal (mi_perm_inv_perm mu (snd newThreadPerm1) (snd new_cur2) m1'').
              admit.
          +  (* Proof of match goes after the comment *)
            
            (* LINE: 6135 *) 
            { !context_goal one_thread_match.
              eapply build_match_compiled; auto.
              instantiate(1:= Hlt21).
              instantiate(1:=(Kresume (TST code2) Vundef)).
              instantiate(1:= Hlt11).
              instantiate(1:=(Kresume (SST code1) Vundef)).
              subst st1' st2'.
              clean_cnt.
              

              
              eapply CThread_Resume.
              intros j'' s1' m1''' m2''' lev1' lev2'.
              intros Hstrict_evolution' (*Hincr'*) Hinterference1' Hinterference2'
                     Hafter_ext.
              remember (fst virtueThread1) as dpm1.
              remember (Events.Event_acq_rel lev1 dpm1 lev1' :: nil) as rel_trace.
              Tactic Notation "dont" tactic(t):= idtac. 
              


              (** *0 . Simplifications to do outside the l emma*)

              assert (Hext_rel1': extcall_acquire
                                    (Genv.globalenv (Ctypes.program_of_program C_program)) 
                                    (Vptr b1 ofs :: nil) m1
                                    (Events.Event_acq_rel lev1 (fst virtueThread1) lev1' :: nil)
                                    Vundef m1''').
              { inversion Hlock_update_mem_strict_load1; subst vload vstore.
                subst rel_trace; econstructor; try eassumption.
                econstructor; eauto.
                subst newThreadPerm1; simpl.
                (* need to replace the way we construct virtue 1:
                 do it by replacein thread_perms with (getCurperm m1')
                 they are the same by hypothesis
                 *)
                admit.
              } 
              assert (Hext_rel1: Events.external_call LOCK
                                                      (Clight.genv_genv Clight_g)
                                                      (Vptr b1 ofs :: nil)
                                                      m1 rel_trace Vundef m1''').
              { simpl; rewrite AcquireExists.
                subst rel_trace dpm1; eauto. }
              clear Hext_rel1'.
              
              assert (Hext_rel2: extcall_acquire
                                   Asm_g (Vptr b2 ofs2 :: nil) m2
                                   (Events.Event_acq_rel lev2 (fst virtueThread2)
                                                         lev2' :: nil)
                                   Vundef m2''').
              { inversion Hlock_update_mem_strict_load2; subst vload vstore.
                econstructor; eauto.
                subst m_writable_lock_1; econstructor.
                3: { reflexivity. }
                - clear - Hstore.
                  move Hstore at bottom.
                  replace (unsigned ofs2) with (unsigned ofs + delta) by admit.
                  eassumption.
                - subst new_cur2; simpl.
                  !goal (computeMap (thread_perms hb st2 Hcnt2) _ =
                         computeMap (getCurPerm m2') _).
                  (* They are equiv but not equal... *)
                  admit. (* TODO*)
              }

              
              assert (Hnb_eq': Mem.nextblock (restrPermMap Hlt21) = Mem.nextblock m2')
                by auto.
              

              subst rel_trace.
              eapply large_external_diagram; try reflexivity; eauto.
              - exact lock_doesnt_return.
              - reflexivity.
              - !goal(Events.inject_delta_map _ _ _ ).
                admit. (* by constructions the birtues inject*)
              - simpl; rewrite AcquireExists; eauto.
              - exploit (interference_consecutive_until Hinterference2).
                rewrite <- Hnb_eq; simpl; auto.
              - exploit (interference_consecutive_until Hinterference2').
                simpl; auto.
            }

          + !context_goal memval_inject.
            repeat econstructor.
          + !goal(lock_update _ st1 _ _ _ _ _).
            econstructor;
              subst st1' newThreadPerm1 virtueThread1;
              unfold fullThUpd_comp, fullThreadUpdate.
            reflexivity.

            
          + !goal(lock_update _ st2 _ _ _ _ st2').
            (* replace (virtueLP new_perms) with (virtueLP angel). *)
            econstructor;
              subst st2' new_cur2 virtueLP2  ofs2 virtueLP1;
              unfold fullThUpd_comp, fullThreadUpdate.
            repeat f_equal.
            * f_equal.
              !goal (unsigned (add ofs (repr delta)) = unsigned ofs + delta);
                admit.
            * simpl.
              !goal (pair0 empty_map = virtueLP_inject m2'' mu (empty_map, empty_map)).
              admit. (*These are equivalente but not equal... 
                       since they will have the shape of m2''
                      *)
              
              
        - econstructor.
          + econstructor; eauto.
          + instantiate (1:= Some (build_delta_content (fst virtueThread2) m2'')).
            simpl.
            admit. (*TODO define inject_delta_content *)
            
        (* injection of the event*)
        (* Should be obvious by construction *)
        - (* HybridMachineSig.external_step *)
          assert (Hofs2: intval ofs2 = unsigned ofs + delta).
          { admit. }
          rewrite <- Hofs2.
          
          eapply step_acquire;
            eauto; try reflexivity;
              try unfold HybridMachineSig.isCoarse,
              HybridMachineSig.HybridCoarseMachine.scheduler.
          
          + (* bounded_maps.sub_map *)
            subst virtueThread2.
            unfold virtueThread_inject.
            destruct virtueThread1 as (virtue11, virtue12).
            cbv iota beta delta[fst] in *.
            destruct Hangel_bound as [Hbound1 Hbound2].
            split.
            -- eapply inject_virtue_sub_map.
               eapply CMatch.
               inversion HeqvirtueThread1.
               destruct angel; simpl in H0.
               subst virtueThread0.
               eassumption.
            -- eapply inject_virtue_sub_map.
               eapply CMatch.
               inversion HeqvirtueThread1.
               destruct angel; simpl in H0.
               subst virtueThread0.
               eassumption.
               
          + (*invariant st4 *)
            !goal (@invariant (HybridSem _) _ st2).
            eapply CMatch.
            
          + (* at_external for code 4. *)
            move Hat_external2' at bottom.
            match goal with
              |- context [restrPermMap ?Hlt]=>
              pose proof (cur_equiv_restr_mem_equiv _ _ Hlt Hthread_mem2)
            end.
            pose proof (Asm_at_external_proper Asm_g code2 _ eq_refl _ _ H).
            simpl in H0; simpl. unfold Asm_g in H0.
            rewrite H0. eauto.
            
          + (* Mem.range_perm *)
            (* Can read the lock *)
            !goal(Mem.range_perm _ _ _ (intval ofs2 + LKSIZE) Cur Readable).
            inversion Hlock_update_mem_strict_load2; subst vload vstore.
            rewrite Hofs2.
            eapply range_perm_mem_equiv_Cur; try apply eq_refl; eauto.
            * eapply Cur_equiv_restr; reflexivity.
              
          + (* The load. *)
            inversion Hlock_update_mem_strict_load1; subst vload vstore.
            !goal ( Mem.load AST.Mint32 _ _ _ = Some _ ).
            
            replace (intval ofs2) with (unsigned ofs + delta) by assumption.
            eapply (load_inject' mu); eauto; try congruence.
            unfold thread_mems; simpl.
            unshelve eapply INJ_locks; eauto.
            
          + !goal(permMapLt _ _ /\ _).
            simpl.  admit.
          (* Solve: make a lemma for permMapLt and compose_map 
             the first part is solved by mem_compat.
             second part is solved by an injection lemma.
           *)
            
          + (* the store *)
            inversion Hlock_update_mem_strict_load2; subst vload vstore.
            
            !goal ( Mem.store AST.Mint32 _ _ _ _ = Some _ ).
            rewrite <- Hstore.
            
            subst m_writable_lock_1.
            f_equal; eauto.
            * eapply restr_proof_irr'; auto; f_equal; auto.
              
          + (* content of lockres*)
            (* ThreadPool.lockRes st4 (b4', ofs4') *)
            (* NOTE: why is it rmap? It should be an injection of rmap 
                   ANSWER: the 'RMAP' is empty, so its injection is also empty... 
             *)
            !goal (ThreadPool.lockRes _ _ = Some _).
            subst ofs2.
            eapply INJ_lock_permissions_Some; eauto.

          + (* permissions join FST*)
            !goal(permMapJoin _ _ _ ). 
            subst virtueLP2 new_cur2; simpl.
            admit. (* almost have it, except wrong mem (m2' m2'') 
                      The structure of the two should be the same...
                      so we could replace...
                      TODO: think about this
                    *)
          (*
            clean_cnt; apply Hjoin_angel2.
           *)
          + (* permissions join SND *)
            !goal(permMapJoin _ _ _ ).
            subst new_cur2.
            clear - Hjoin_angel2.
            
            admit. (* almost have it, except wrong mem (m2' m2'') 
                      The structure of the two should be the same...
                      so we could replace...
                      TODO: think about this
                    *)
            (* clean_cnt; apply Hjoin_angel2. *)
      (* 
          + simpl. 
            subst; repeat f_equal; try eapply Axioms.proof_irr.*)
            
      Admitted. (* acquire_step_diagram_compiled *)


      Lemma make_step_diagram_compiled:
        let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
        forall (U : list nat) (cd : compiler_index) (mu:meminj) tr2 
               (st1 : ThreadPool (Some hb)) (m1 m1' m1'' : mem) new_perms1
               (st2 : ThreadPool (Some (S hb))) (m2' : mem) Hcnt1 Hcnt2
               (Hsame_cnt: same_cnt hb st1 st2 Hcnt1 Hcnt2)
               b1 ofs (code1 : semC)  (code2 : Asm.state)
               (*Hinj_b : mu b1 = Some (b2, delt)*)
               (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
               (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
               (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
               (*Hangel_bound: sub_map_virtue angel (getMaxPerm m1')*)
               (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
               (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
               
               (HH1: set_new_mems b1 (unsigned ofs) (getThreadR Hcnt1) LKSIZE_nat new_perms1)
               (*HH2: set_new_mems b2 (unsigned ofs+delt) (getThreadR Hcnt2) LKSIZE_nat new_perms2*)
               
               (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                                Some (MKLOCK, (Vptr b1 ofs :: nil)%list))
               (Hlock_update_mem_strict: lock_update_mem_strict b1 (unsigned ofs) m1' m1'' vzero)
               (HisLock: lockRes st1 (b1, unsigned ofs) = None)
               (Hlt1 : permMapLt (thread_perms _ _ Hcnt1) (getMaxPerm m1'))
               (Hlt2 : permMapLt (thread_perms _ _ Hcnt2) (getMaxPerm m2'))
               (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
        exists evnt2 (st2' : t) (m2'' : mem),
          let evnt:= Events.mklock (b1, unsigned ofs) in 
          let st1':= fullThreadUpdate
                       st1 hb Hcnt1 (Kresume (SST code1) Vundef)
                       (new_perms1, pair0 empty_map) (b1, unsigned ofs)  in
          concur_match (Some cd) mu st1' m1'' st2' m2'' /\
          inject_sync_event mu evnt evnt2 /\
          HybridMachineSig.external_step
            (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
            U tr2 st2 m2' (HybridMachineSig.schedSkip U)
            (tr2 ++ (Events.external hb evnt2 :: nil)) st2' m2'' /\
          let Hcmpt2:= memcompat2 CMatch in
          syncStep(Sem:=HybridSem (Some (S hb)))
                  true Hcnt2 Hcmpt2 st2' m2'' evnt2.
      Proof.
        intros.

        (*Add all the memories and theeir relations *)
        get_mem_compatible.
        get_thread_mems.
        clean_proofs.
        
        (* NOTE: this proof has three diagrams:
               - Left Diagram:      Generated by interference by other threads 
               - Middle Diagram:    The compiler diagram
               - Right Diagram:     Generated by interference by other threads

              m1 -lev1-> m1' -dpm-> m1'' -lev1'-> m1'''
              |          |          |             |
              |   Left   |          |    Right    |
              |          |          |             |
              m2 -lev2-> m2' -dpm-> m2'' -lev2'-> m2'''
              !          !          !             !     
              m2 -lev2-> m21'-dpm-> m21''-lev2'-> m21'''

              TODO: the last layer might not be needed?
         *)
        
        (** * 0. Stablish facts about m2' *)
        
        (** * 1. Set all the at_externals for LEFT diagram m1 m1' m2 m2' *)
        left_diagram.
        set (ofs2:= add ofs (repr delta)).
        assert (HH2:exists new_perms2,
                   set_new_mems b2 (unsigned ofs + delta)
                                (getThreadR Hcnt2) LKSIZE_nat new_perms2).
        { admit. }
        destruct HH2 as [new_perms2 HH2].
        set (st2':= fullThreadUpdate st2 hb Hcnt2 (Kresume (TST code2) Vundef)
                                     (new_perms2, pair0 empty_map) (b2, unsigned ofs2)).
        remember (fullThreadUpdate st1 hb Hcnt1 (Kresume (SST code1) Vundef)
                                   (new_perms1, pair0 empty_map)
                                   (b1, unsigned ofs)) as st1'.

        assert (H: ThreadPool (Some (S hb)) =
                   @t dryResources (HybridSem (@Some nat (S hb)))).
        { reflexivity. }
        dependent rewrite <- H in st2'. clear H.
        
        repeat pose_max_equiv.
        forward_cmpt_all.
        rename Hcmpt_mem_fwd into Hcmpt2'.
        rename Hcmpt_mem_fwd0 into Hcmpt1'.
        
        (** * 4. Finally we proceed with the goal: existentials. *)
        set (evnt2:= (Events.mklock (b2, unsigned ofs2))).
        
        exists evnt2, st2', m2''.
        split; [|split].
        - eapply concur_match_update_lock; eauto; try solve[subst st1'; eauto].
          + !context_goal lock_update_mem.
            eapply lock_update_mem_strict_mem_update.
            eapply Hlock_update_mem_strict1.
          + !context_goal (lock_update_mem).
            eapply lock_update_mem_strict_mem_update.
            eapply Hlock_update_mem_strict2.
          + !context_goal Mem.inject.
            rewrite RPM.
            instantiate(2:=fst new_perms2);
              instantiate(3:=fst new_perms1).
            apply inject_restr; auto.
            * !goal (mi_perm_perm mu _ _).
              admit.
            * !goal (mi_memval_perm mu _ _ _).
              admit.
            * !goal (mi_perm_inv_perm mu _ _ _).
              admit.
          + !goal (@invariant (HybridSem _) _ _). admit.
          + !goal (invariant st2'). admit.
          + !goal(perm_preimage mu _ _).
            instantiate(1:=snd new_perms2); instantiate(1:=snd new_perms1).
            simpl in *. admit.
          + !goal (Mem.inject mu _ _).
            apply inject_restr; auto.
            * !goal (mi_perm_perm mu (snd new_perms1) (snd new_perms2)).
              admit.
            * !goal (mi_memval_perm mu (snd new_perms1)
                                    (Mem.mem_contents m1'') (Mem.mem_contents m2'')).
              admit.
            * !goal (mi_perm_inv_perm mu (snd new_perms1) (snd new_perms2) m1'').
              admit.
          +  (* Proof of match goes after the comment *)
            { !context_goal one_thread_match.
              eapply build_match_compiled; auto.
              admit.
            }
          + constructor; constructor.
          + simpl in *. econstructor.
            subst st1'; destruct new_perms1; reflexivity.
          + simpl in *. econstructor.
            subst st2' ofs2; destruct new_perms2. repeat f_equal.
            !goal (unsigned (add ofs (repr delta)) = unsigned ofs + delta).
            admit.
            !goal (pair0 empty_map = virtueLP_inject _ _ (pair0 empty_map)).
            admit.

        - subst evnt2. replace (unsigned ofs2) with (unsigned ofs + delta).
          repeat econstructor; eassumption.
          admit.
        - split; [admit|].

          assert (Hofs2: intval ofs2 = unsigned ofs + delta).
          { admit. }
          rewrite <- Hofs2 in *.

          eapply step_mklock;
            eauto; try reflexivity;
              try unfold HybridMachineSig.isCoarse,
              HybridMachineSig.HybridCoarseMachine.scheduler.
          + !goal (@invariant (HybridSem _) _ st2).
            eapply CMatch.
            
          + (* at_external for code 4. *)
            move Hat_external2' at bottom.
            match goal with
              |- context [restrPermMap ?Hlt]=>
              pose proof (cur_equiv_restr_mem_equiv _ _ Hlt Hthread_mem2)
            end.
            pose proof (Asm_at_external_proper Asm_g code2 _ eq_refl _ _ H).
            simpl in H0; simpl. unfold Asm_g in H0.
            rewrite H0. eauto.
            
          + (* Mem.range_perm *)
            (* Can write the lock *) simpl.
            !goal(Mem.range_perm _ _ _ (intval ofs2 + LKSIZE) Cur Writable).
            inversion Hlock_update_mem_strict2; subst vstore.
            rewrite Hofs2.
            eapply range_perm_mem_equiv_Cur; try apply eq_refl; eauto.
            * eapply Cur_equiv_restr; reflexivity.
            * eapply permMapLt_range_mem.
              admit. (*by injecting from above*)
              
          + (* the store *)
            inversion Hlock_update_mem_strict2; subst vstore.
            rewrite (mem_is_restr_eq m2') in Hstore.
            erewrite restrPermMap_equiv_eq; eauto.
          + simpl; inv HH2; auto.
          + simpl; inv HH2; auto.
          + !goal (lockRes _ (b2,_) = None).
            eapply INJ_lock_permissions_None; eauto.
            
      Admitted. (* make_step_diagram_compiled*)

      
      (** *Full Machine diagrams *)
      
      Lemma release_step_diagram:
        let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
        forall (angel: virtue) (m1 m1' : mem)  (U : list nat) (tid : nat) cd tr2 mu
               (HSched: HybridMachineSig.schedPeek U = Some tid)
               (st1 : ThreadPool (Some hb)) 
               (st2 : ThreadPool (Some (S hb))) (m2 : mem)
               (cnt1 : containsThread(Sem:=HybridSem _) st1 tid)
               (cnt2 : containsThread(Sem:=HybridSem _) st2 tid)
               (c : semC) (b : block) (ofs : int)
               (rmap : lock_info)
               (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
               (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
               (CMatch: concur_match cd mu st1 m1 st2 m2)
               (Hangel_bound: sub_map_virtue angel (getMaxPerm m1))
               (Hcode: getThreadC cnt1 = Kblocked c)
               (Hat_external: semantics.at_external hybrid_sem c m1 =
                              Some (UNLOCK, (Vptr b ofs :: nil)%list))
               (Hlock_update_mem_strict_load:
                  lock_update_mem_strict_load
                    b (unsigned ofs) (snd (getThreadR cnt1)) m1 m1' vzero vone)
               (HisLock: lockRes st1 (b, unsigned ofs) = Some rmap)
               (Hrmap: empty_doublemap rmap),
          let newThreadPerm1:= (computeMap_pair (getThreadR cnt1) (virtueThread angel)) in
          forall (Hjoin_angel: permMapJoin_pair newThreadPerm1 (virtueLP angel) (getThreadR cnt1)),
          exists evnt' (st2' : t) (m2' : mem),
            let evnt:= build_release_event (b, unsigned ofs) (fst (virtueThread angel)) m1' in
            let st1':= fullThUpd_comp
                         st1 tid cnt1 (Kresume c Vundef) angel (b, unsigned ofs) in
            concur_match cd mu st1' m1' st2' m2' /\
            inject_sync_event mu evnt evnt' /\
            (* (inject_mevent mu (Events.external tid evnt) (Events.external tid evnt')) /\ *)
            HybridMachineSig.external_step
              (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
              U tr2 st2 m2 (HybridMachineSig.schedSkip U)
              (tr2 ++ (Events.external tid evnt' :: nil)) st2' m2'.
      Proof.
        intros; simpl in *.
        pose proof (memcompat1 CMatch) as Hcmpt1.
        assert (thread_compat1: thread_compat _ _ cnt1 m1) by
            (apply mem_compatible_thread_compat; apply CMatch).
        pose proof (cur_equiv_restr_mem_equiv _ _ (th_comp thread_compat1) Hthread_mem1) as
            Hmem_equiv.
        inversion Hlock_update_mem_strict_load. subst vload vstore.
        
        (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
        destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].
        
        (** * tid < hb *)
        
        - rename m1 into MM1.
          pose proof (mtch_target _ _ _ _ _ _ CMatch _ l cnt1
                                  (contains12 CMatch cnt1)) as match_thread.
          simpl in Hcode; exploit_match ltac:(apply CMatch).
          inversion H3. (* Asm_match *)
          
          (*Destruct the values of the self simulation *)
          pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
          assert (Hinj':=Hinj).
          pose proof (self_simulation.ssim_external _ _ Aself_simulation) as sim_atx.
          eapply sim_atx in Hinj'; eauto.
          2: { (*at_external*)
            idtac.
            clean_cmpt. 
            erewrite restr_proof_irr.
            rewrite Hmem_equiv; simpl; eassumption.
          }
          clear sim_atx.
          destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.
          
          (edestruct (release_step_diagram_self AsmSem) as
              (e' & m2' & Hthread_match & Htrace_inj & external_step);
           first[ eassumption|
                  econstructor; eassumption|
                  solve[econstructor; eauto] |
                  eauto]).
          + clean_cnt; eassumption.
          (* + (*at external *)
            clean_cmpt. unfold thread_mems.
            rewrite Hmem_equiv; simpl; assumption.*)
          + (*match_self*)
            econstructor.
            * eapply H3.
            * simpl; clean_cmpt.
              move matchmem at bottom.
              admit. (* match_mem proper with mem_equiv*)
          (* erewrite <- (restr_proof_irr Hlt1).
              erewrite <- (restr_proof_irr Hlt2).
              assumption. *)
          + exists e'. eexists. exists m2'.
            split ; [|split].
            * (* reestablish concur *)
              Search concur_match.
              rename b into BB.
              admit.
              
            * clear - Htrace_inj. 
              unfold build_release_event in *. eauto.
            * econstructor; eauto.
              
        (** *tid = hb*)
        - subst tid. 
          (* rename the memories, to show that they have been modified, 
               since the execution of this thread stopped. *)
          rename m1' into m1''.
          rename m1 into m1'.
          rename m2 into m2'.
          
          (* Retrieve the match relation for this thread *)
          pose proof (mtch_compiled _ _ _ _ _ _ CMatch _ ltac:
                      (reflexivity)
                        cnt1 (contains12 CMatch cnt1)) as Hmatch.
          exploit_match ltac:(apply CMatch).
          
          rename H5 into Hinterference1.
          rename H7 into Hinterference2.
          rename H1 into Hcomp_match.
          rename H2 into Hstrict_evolution.
          
          rename cnt1 into Hcnt1.
          (*rename Hlt' into Hlt_setbBlock1. *)
          remember (virtueThread angel) as virtueThread1.
          remember (virtueLP angel) as virtueLP1.
          rename Hat_external into Hat_external1.
          rename b into b1.
          rename Hstore into Hstore1.
          
          (* to remove until 'end to remove'*)
          rename rmap into lock_map.
          (* end to remove *)
          



          rewrite RPM in Hinterference1.
          symmetry in H0.
          clean_cnt.
          exploit release_step_diagram_compiled;
            try eapply Hthread_mem1;
            try eapply Hthread_mem2;
            try eapply CMatch;
            eauto;
            try reflexivity.
          
          + econstructor; eauto.
          + subst newThreadPerm1 virtueThread1 virtueLP1; eassumption.
          + econstructor; eauto.
            * !goal(mem_interference m1 lev1 m1'). admit.   
            * !goal(mem_interference m2 lev2 m2'). admit.
          + clear. subst virtueThread1.
            intros (?&?&?&?&?&?).
            do 3 eexists; repeat weak_split eauto.
            econstructor; eauto.
            
            
        - (* hb < tid *)
          pose proof (mtch_source _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1)) as match_thread.
          simpl in Hcode; exploit_match ltac:(apply CMatch).
          inversion H3.
          
          (*Destruct the values of the self simulation *)
          pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
          assert (Hinj':=Hinj).
          pose proof (self_simulation.ssim_external _ _ Cself_simulation) as sim_atx.
          eapply sim_atx in Hinj'; eauto.
          2: { clean_cmpt. 
               erewrite restr_proof_irr.
               rewrite Hmem_equiv; simpl; eassumption.
               
          }
          clear sim_atx.
          destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

          
          (edestruct (release_step_diagram_self CSem) as
              (e' & m2' & Hthread_match & Htrace_inj & external_step);
           first[ eassumption|
                  econstructor; eassumption|
                  solve[econstructor; eauto] |
                  eauto]).
          
          + clean_cnt; eassumption.

          (*  + (*Mem.inject *)
            eapply CMatch.
           (* + (*at external *)
            clean_cmpt. unfold thread_mems.
            rewrite Hmem_equiv; simpl; assumption.  *)*)
          + (*match_self*)
            econstructor.
            * eapply H3.
            * simpl; clean_cmpt.
              move matchmem at bottom.
              admit. (*match_mem Proper mem_equiv*)
          + exists e'. eexists. exists m2'.
            split ; [|split].
            * (* reestablish concur *)
              admit.
            *  clear - Htrace_inj.
               unfold build_release_event in *. auto.
            (*
              (* eapply List.Forall2_app.
              -- eapply inject_incr_trace; eauto. *)     
              -- simpl. econstructor; try solve[constructor]; eauto. *)
            * econstructor; eauto.

              
              (** *Shelve *)
              Unshelve.
              all: eauto.
              all: try econstructor; eauto.
              all: try apply CMatch.
              
      Admitted.

      Lemma acquire_step_diagram:
        let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
        forall (angel: virtue) (m1 m1' : mem)  (U : list nat) (tid : nat) cd tr2
               (HSched: HybridMachineSig.schedPeek U = Some tid)
               (mu : meminj) (st1 : ThreadPool (Some hb)) 
               (st2 : ThreadPool (Some (S hb))) (m2 : mem)
               (cnt1 : containsThread(Sem:=HybridSem _) st1 tid)
               (cnt2 : containsThread(Sem:=HybridSem _) st2 tid)
               (c : semC) (b : block) (ofs : int) lock_perms
               (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
               (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
               (CMatch: concur_match cd mu st1 m1 st2 m2)
               (*Hangel_bound: sub_map_virtue angel (getMaxPerm m1)*)
               (Hangel_bound: pair21_prop bounded_maps.sub_map (virtueThread angel)
                                          (snd (getMaxPerm m1)))
               (Hcode: getThreadC cnt1 = Kblocked c)
               (Hat_external: semantics.at_external hybrid_sem c m1 =
                              Some (LOCK, (Vptr b ofs :: nil)%list))
               (Hlock_update_mem_strict_load: lock_update_mem_strict_load b (unsigned ofs)
                                                                          (snd (getThreadR cnt1))
                                                                          m1 m1' vone vzero )
               (HisLock: lockRes st1 (b, unsigned ofs) = Some lock_perms),
          let newThreadPerm1:= (computeMap_pair (getThreadR cnt1) (virtueThread angel)) in
          let new_perms:= Build_virtue (virtueThread angel) (empty_map, empty_map) in
          forall (Hjoin_angel: permMapJoin_pair lock_perms (getThreadR cnt1) newThreadPerm1)
                 (Hlt_new: permMapLt_pair newThreadPerm1 (getMaxPerm m1)),
          exists evnt' (st2' : t) (m2' : mem),
            let evnt:= build_acquire_event (b, unsigned ofs) (fst (virtueThread angel)) m1' in
            let st1':= fullThUpd_comp st1 tid cnt1 (Kresume c Vundef) new_perms (b, unsigned ofs) in
            concur_match cd mu st1' m1' st2' m2' /\
            inject_sync_event mu evnt evnt' /\
            (* (inject_mevent mu (Events.external tid evnt) (Events.external tid evnt')) /\ *)
            HybridMachineSig.external_step
              (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
              U tr2 st2 m2 (HybridMachineSig.schedSkip U)
              (tr2 ++ (Events.external tid evnt' :: nil)) st2' m2'.
      Proof.
        intros; simpl in *.
        pose proof (memcompat1 CMatch) as Hcmpt1.
        assert (thread_compat1: thread_compat _ _ cnt1 m1) by
            (apply mem_compatible_thread_compat; apply CMatch).
        pose proof (cur_equiv_restr_mem_equiv _ _ (th_comp thread_compat1) Hthread_mem1) as
            Hmem_equiv1.
        inversion Hlock_update_mem_strict_load. subst vload vstore.

        (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
        destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].

        (* tid < hb *)
        - pose proof (mtch_target _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1)) as match_thread.
          simpl in Hcode; exploit_match ltac:(apply CMatch).
          inversion H3. (* Asm_match *)
          
          (*Destruct the values of the self simulation *)
          pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
          assert (Hinj':=Hinj).
          pose proof (self_simulation.ssim_external _ _ Aself_simulation) as sim_atx.
          eapply sim_atx in Hinj'; eauto.
          2: { (*at_external*)
            clean_cmpt. 
            erewrite restr_proof_irr.
            rewrite Hmem_equiv1; simpl; eassumption.
          }
          clear sim_atx.
          destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.
          
          (edestruct (acquire_step_diagram_self AsmSem) as
              (e' & m2' & Hthread_match & Htrace_inj & external_step);
           first[ eassumption|
                  econstructor; eassumption|
                  solve[econstructor; eauto] |
                  eauto]).
          + clean_cnt; eassumption.
          + clean_cnt; eauto.
          + (*match_self*)
            econstructor.
            * eapply H3.
            * rewrite <- Hmem_equiv1.
              assert (Hmem_equiv2: mem_equiv m2 (restrPermMap Hlt2)).
              { symmetry; eapply cur_equiv_restr_mem_equiv.
                clean_cnt; auto. }
              rewrite Hmem_equiv2.
              clear - matchmem.
              erewrite <- (restr_proof_irr Hlt1).
              assumption.
          + exists e'. eexists. exists m2'.
            split ; [|split].
            * (* reestablish concur *)
              rename b into BB.
              !goal (concur_match _ _ (fullThUpd_comp _ _ _ _ _ _ ) _ _ _).
              admit. (* Haven't proven this? *)
            * clear - Htrace_inj. 
              unfold build_release_event in *. (*subst virtueThread0; *) eauto.
            * econstructor; eauto.
              
        (* tid = hb *)
        - subst tid. 
          (* rename the memories, to show that they have been modified, 
               since the execution of this thread stopped. *)
          rename m1' into m1''.
          rename m1 into m1'.
          rename m2 into m2'.
          
          (* Retrieve the match relation for this thread *)
          pose proof (mtch_compiled _ _ _ _ _ _ CMatch _ ltac:
                      (reflexivity)
                        cnt1 (contains12 CMatch cnt1)) as Hmatch.
          exploit_match ltac:(apply CMatch).
          
          rename H5 into Hinterference1.
          rename H7 into Hinterference2.
          rename H1 into Hcomp_match.
          rename H2 into Hstrict_evolution.
          
          rename cnt1 into Hcnt1.
          (*rename Hlt' into Hlt_setbBlock1. *)
          remember (virtueThread angel) as virtueThread1.
          remember (virtueLP angel) as virtueLP1.
          rename Hat_external into Hat_external1.
          rename b into b1.
          rename Hstore into Hstore1.
          
          rewrite RPM in Hinterference1.
          symmetry in H0.
          clean_cnt.
          exploit acquire_step_diagram_compiled;
            try eapply Hthread_mem1;
            try eapply Hthread_mem2;
            try solve[eapply CMatch; eauto; try reflexivity];
            eauto; try reflexivity.
          + econstructor; eassumption.
          + subst virtueThread1; eassumption.
          + subst newThreadPerm1 virtueThread1 virtueLP1; eassumption.
          + subst newThreadPerm1 virtueThread1 virtueLP1; eassumption.
          + econstructor; eauto; simpl.
            * !goal(mem_interference m1 lev1 m1'). admit.   
            * !goal(mem_interference m2 lev2 m2'). admit.
          + subst virtueThread1.
            clear. 
            intros (?&?&?&?&?&?).
            do 3 eexists; repeat weak_split eauto.
            econstructor; eauto.
            
        (* tid > hb *)
        - pose proof (mtch_source _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
            as match_thread.
          simpl in Hcode; exploit_match ltac:(apply CMatch).
          inversion H3. (* Clight_match *)
          
          (*Destruct the values of the self simulation *)
          pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
          assert (Hinj':=Hinj).
          pose proof (self_simulation.ssim_external _ _ Cself_simulation) as sim_atx.
          eapply sim_atx in Hinj'; eauto.
          2: { (*at_external*)
            clean_cmpt. 
            erewrite restr_proof_irr.
            rewrite Hmem_equiv1; simpl; eassumption.
          }
          clear sim_atx.
          destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.
          
          (edestruct (acquire_step_diagram_self CSem) as
              (e' & m2' & Hthread_match & Htrace_inj & external_step);
           first[ eassumption|
                  econstructor; eassumption|
                  solve[econstructor; eauto] |
                  eauto]).
          + eassumption.
          + clean_cnt; eassumption.
          + (*match_self*)
            econstructor.
            * eapply H3.
            * simpl; clean_cmpt.
              move matchmem at bottom.
              admit. (* match_mem proper with mem_equiv*)
          (* erewrite <- (restr_proof_irr Hlt1).
              erewrite <- (restr_proof_irr Hlt2).
              assumption. *)
          + exists e'. eexists. exists m2'.
            split ; [|split].
            * (* reestablish concur *)
              rename b into BB.
              !goal (concur_match _ _ (fullThUpd_comp _ _ _ _ _ _ ) _ _ _).
              admit.
            * clear - Htrace_inj. 
              unfold build_release_event in *. (*subst virtueThread0; *) eauto.
            (*
              (* eapply List.Forall2_app.
              -- eapply inject_incr_trace; eauto. *)     
              -- simpl. econstructor; try solve[constructor]; eauto. *)
            * econstructor; eauto.
              
      Admitted. (* acquire_step_diagram *)

      Lemma make_step_diagram:
        let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
        forall (m1 m1' m2 : mem)  (U : list nat) (tid : nat) cd tr2 (mu : meminj)
               (HSched: HybridMachineSig.schedPeek U = Some tid)
               (st1 : ThreadPool (Some hb)) cnt1
               (st2 : ThreadPool (Some (S hb))) cnt2
               (Hsame_sch: same_cnt tid st1 st2 cnt1 cnt2)
               (c : semC) (b : block) (ofs : int) new_perms
               (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
               (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
               (CMatch: concur_match cd mu st1 m1 st2 m2)
               (Hcode: getThreadC cnt1 = Kblocked c)
               (Hat_external: semantics.at_external hybrid_sem c m1 =
                              Some (MKLOCK, (Vptr b ofs :: nil)%list))
               (Hset_block: set_new_mems b (unsigned ofs) (getThreadR cnt1) LKSIZE_nat new_perms)
               (Hlock_update_mem_strict: lock_update_mem_strict b (unsigned ofs) m1 m1' vzero),
          lockRes st1 (b, unsigned ofs) = None ->
          exists evnt' (st2' : t) (m2' : mem),
            let evnt:= Events.mklock (b, unsigned ofs) in
            let st1':= fullThreadUpdate st1 tid cnt1 (Kresume c Vundef)
                                        (new_perms, pair0 empty_map) (b, unsigned ofs) in
            concur_match cd mu st1' m1' st2' m2' /\
            inject_sync_event mu evnt evnt' /\
            HybridMachineSig.external_step
              (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
              U tr2 st2 m2 (HybridMachineSig.schedSkip U)
              (seq.cat tr2 (Events.external tid evnt' :: nil)) st2' m2'.
      Proof.
        intros; simpl in *.
        inv Hsame_sch.
        pose proof (memcompat1 CMatch) as Hcmpt1.
        assert (thread_compat1: thread_compat _ _ cnt1 m1) by
            (apply mem_compatible_thread_compat; apply CMatch).
        pose proof (cur_equiv_restr_mem_equiv _ _ (th_comp thread_compat1) Hthread_mem1) as
            Hmem_equiv.
        
        (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
        destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].

        - (* (tid < hb) *)
          (* 6883*) 
          
          pose proof (mtch_target _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
            as match_thread.
          simpl in Hcode; exploit_match ltac:(apply CMatch).
          inversion H4. (* Asm_match *)
          
          (*Destruct the values of the self simulation *)
          pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
          assert (Hinj':=Hinj).
          pose proof (self_simulation.ssim_external _ _ Aself_simulation) as sim_atx.
          eapply sim_atx in Hinj'; eauto.
          2: { (*at_external*)
            clean_cmpt. 
            erewrite restr_proof_irr.
            rewrite Hmem_equiv; simpl; eassumption.
          }
          clear sim_atx.
          destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

          (edestruct (make_step_diagram_self AsmSem) as
              (e' & m2' & Hthread_match & Htrace_inj & external_step)); eauto;
            first[ eassumption|
                   econstructor; eassumption|
                   solve[econstructor; eauto] |
                   eauto].
          + clean_cnt; eassumption.
          + (*match_self*)
            econstructor.
            * eapply cinject.
            * simpl; clean_cmpt.
              move matchmem at bottom.
              admit. (* match_mem proper with mem_equiv*)
          (* erewrite <- (restr_proof_irr Hlt1).
              erewrite <- (restr_proof_irr Hlt2).
              assumption. *)
          + exists e'. eexists. exists m2'.
            split ; [|split].
            * (* reestablish concur *)
              rename b into BB.
              !goal (concur_match _ _ (fullThreadUpdate _ _ _ _ _ _ ) _ _ _).
              admit.
            * clear - Htrace_inj. 
              unfold build_release_event in *. (*subst virtueThread0; *) eauto.
            (*
              (* eapply List.Forall2_app.
              -- eapply inject_incr_trace; eauto. *)     
              -- simpl. econstructor; try solve[constructor]; eauto. *)
            * econstructor; eauto.
        - (* (tid = hb) *)
          subst tid. 
          (* rename the memories, to show that they have been modified, 
               since the execution of this thread stopped. *)
          rename m1' into m1''.
          rename m1 into m1'.
          rename m2 into m2'.
          
          (* Retrieve the match relation for this thread *)
          pose proof (mtch_compiled _ _ _ _ _ _ CMatch _ ltac:
                      (reflexivity)
                        cnt1 (contains12 CMatch cnt1)) as Hmatch.
          exploit_match ltac:(apply CMatch).
          
          rename H8 into Hinterference1.
          rename H6 into Hinterference2.
          rename H2 into Hcomp_match.
          rename H3 into Hstrict_evolution.
          
          rename cnt1 into Hcnt1.
          rename Hat_external into Hat_external1.
          rename b into b1.
          (* rename Hstore into Hstore1. *)
          
          rewrite RPM in Hinterference1.
          symmetry in H1.
          clean_cnt.
          exploit make_step_diagram_compiled;
            try reflexivity;
            try solve[eapply CMatch]; eauto.
          + econstructor; eassumption.
          + !goal (strict_evolution_diagram _ _ _ _ _ _ _).
            econstructor; eauto; simpl.
            * !goal(mem_interference m1 lev1 m1'). admit.   
            * !goal(mem_interference m2 lev2 m2'). admit.
          + intros (?&?&?&?&?&?&?).
            do 3 eexists; repeat weak_split eauto.
            
        - (* tid > hb  *)
          pose proof (mtch_source _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
            as match_thread.
          simpl in Hcode; exploit_match ltac:(apply CMatch).
          inversion H4. (* Clight_match *)
          
          (*Destruct the values of the self simulation *)
          pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
          assert (Hinj':=Hinj).
          pose proof (self_simulation.ssim_external _ _ Cself_simulation) as sim_atx.
          eapply sim_atx in Hinj'; eauto.
          2: { (*at_external*)
            clean_cmpt. 
            erewrite restr_proof_irr.
            rewrite Hmem_equiv; simpl; eassumption.
          }
          clear sim_atx.
          destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

          (edestruct (make_step_diagram_self CSem) as
              (e' & m2' & Hthread_match & Htrace_inj & external_step)); eauto;
            first[ eassumption|
                   econstructor; eassumption|
                   solve[econstructor; eauto] |
                   eauto].
          + clean_cnt; eassumption.
          + (*match_self*)
            econstructor.
            * eapply cinject.
            * simpl; clean_cmpt.
              move matchmem at bottom.
              admit. (* match_mem proper with mem_equiv*)
          (* erewrite <- (restr_proof_irr Hlt1).
              erewrite <- (restr_proof_irr Hlt2).
              assumption. *)
          + exists e'. eexists. exists m2'.
            split ; [|split].
            * (* reestablish concur *)
              rename b into BB.
              !goal (concur_match _ _ (fullThreadUpdate _ _ _ _ _ _ ) _ _ _).
              admit.
            * clear - Htrace_inj. 
              unfold build_release_event in *. (*subst virtueThread0; *) eauto.
            (*
              (* eapply List.Forall2_app.
              -- eapply inject_incr_trace; eauto. *)     
              -- simpl. econstructor; try solve[constructor]; eauto. *)
            * econstructor; eauto.
              
      Admitted.

      
      

      
      Lemma free_step_diagram_compiled:
        let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
        forall (m1 m1' m1'': mem) (U : list nat) (cd : compiler_index) mu tr2 pdata
               (st1 : ThreadPool (Some hb))  new_perms1
               (st2 : ThreadPool (Some (S hb))) (m2' : mem) Hcnt1 Hcnt2
               (Hsame_cnt: same_cnt hb st1 st2 Hcnt1 Hcnt2)
               b1 ofs (code1 : semC)  (code2 : Asm.state) lock_data
               (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
               (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
               (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
               (*Hangel_bound: sub_map_virtue angel (getMaxPerm m1')*)
               (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
               (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
               (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                                Some (FREE_LOCK, (Vptr b1 ofs :: nil)%list))
               (Hlock_update_mem_strict: lock_update_mem_strict b1 (unsigned ofs) m1' m1'' vzero)
               (Hlock_map: lockRes st1 (b1, Integers.Ptrofs.unsigned ofs) = Some lock_data)
               (Hempty_lock: forall b ofs, pair1 (fun map => map !! b ofs) lock_data = pair0 None)
               (HlocksLt: permMapLt (lock_perms _ _ Hcnt1) (getMaxPerm m1') )
               (Hrange_perm: perm_interval (restrPermMap HlocksLt)
                                           b1 (unsigned ofs) LKSIZE Cur Writable)
               (HH: forall i, 0 <= (Z.of_nat i) < LKSIZE ->
                         Mem.perm_order'' (pdata (S i)) (Some Writable))
               (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
          let new_perms2:=
              setPermBlock_var_pair b1 (unsigned ofs) LKSIZE_nat
                                    (pdata, fun _:nat => None) (getThreadR Hcnt1) in
          exists evnt' (st2' : t) (m2'' : mem),
            let evnt:= (Events.freelock (b1, unsigned ofs)) in
            let st1':= remLockfFullUpdate st1 hb Hcnt1
                                          (Kresume (SST code1) Vundef) new_perms1
                                          (b1, unsigned ofs) in
            concur_match (Some cd) mu st1' m1' st2' m2'' /\
            inject_sync_event mu evnt evnt' /\
            (* (inject_mevent mu (Events.external hb evnt) (Events.external hb evnt')) /\ *)
            HybridMachineSig.external_step
              (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
              U tr2 st2 m2' (HybridMachineSig.schedSkip U)
              (tr2 ++ (Events.external hb evnt' :: nil)) st2' m2''.
      Proof.
        
        intros.

        (*Add all the memories and theeir relations *)
        get_mem_compatible.
        get_thread_mems.
        clean_proofs.
        
        (* NOTE: this proof has three diagrams:
               - Left Diagram:      Generated by interference by other threads 
               - Middle Diagram:    The compiler diagram
               - Right Diagram:     Generated by interference by other threads

              m1 -lev1-> m1' -dpm-> m1'' -lev1'-> m1'''
              |          |          |             |
              |   Left   |          |    Right    |
              |          |          |             |
              m2 -lev2-> m2' -dpm-> m2'' -lev2'-> m2'''
              !          !          !             !     
              m2 -lev2-> m21'-dpm-> m21''-lev2'-> m21'''

              TODO: the last layer might not be needed?
         *)
        
        (** * 0. Stablish facts about m2' *)
        
        (** * 1. Set all the at_externals for LEFT diagram m1 m1' m2 m2' *)
        left_diagram.
      Admitted.
      (*

        unify_injection. rename b0 into b2.
        set (ofs2:= add ofs (repr delta)).
        set (st2':= fullThreadUpdate st2 hb Hcnt2 (Kresume (TST code2) Vundef)
                                     (new_perms2, pair0 empty_map) (b2, unsigned ofs2)).
        remember (fullThreadUpdate st1 hb Hcnt1 (Kresume (SST code1) Vundef)
                                   (new_perms1, pair0 empty_map)
                                   (b1, unsigned ofs)) as st1'.

        assert (H: ThreadPool (Some (S hb)) =
                   @t dryResources (HybridSem (@Some nat (S hb)))).
        { reflexivity. }
        dependent rewrite <- H in st2'. clear H.
        
        repeat pose_max_equiv.
        forward_cmpt_all.
        rename Hcmpt_mem_fwd into Hcmpt2'.
        rename Hcmpt_mem_fwd0 into Hcmpt1'.
        
        (** * 4. Finally we proceed with the goal: existentials. *)

        set (evnt2:= (Events.mklock (b2, unsigned ofs2))).
        
        exists evnt2, st2', m2''.
        split; [|split].
        - eapply concur_match_update_lock; eauto; try solve[subst st1'; eauto].
          + !context_goal lock_update_mem.
            eapply lock_update_mem_strict_mem_update.
            eapply Hlock_update_mem_strict1.
          + !context_goal (lock_update_mem).
            eapply lock_update_mem_strict_mem_update.
            eapply Hlock_update_mem_strict2.
          + !context_goal Mem.inject.
            rewrite RPM.
            instantiate(2:=fst new_perms2);
              instantiate(3:=fst new_perms1).
            apply inject_restr; auto.
            * !goal (mi_perm_perm mu _ _).
              admit.
            * !goal (mi_memval_perm mu _ _ _).
              admit.
            * !goal (mi_perm_inv_perm mu _ _ _).
              admit.
          + !goal (@invariant (HybridSem _) _ _). admit.
          + !goal (invariant st2'). admit.
          + !goal(perm_preimage mu _ _).
            instantiate(1:=snd new_perms2); instantiate(1:=snd new_perms1).
            simpl in *. admit.
          + !goal (Mem.inject mu _ _).
            apply inject_restr; auto.
            * !goal (mi_perm_perm mu (snd new_perms1) (snd new_perms2)).
              admit.
            * !goal (mi_memval_perm mu (snd new_perms1)
                                    (Mem.mem_contents m1'') (Mem.mem_contents m2'')).
              admit.
            * !goal (mi_perm_inv_perm mu (snd new_perms1) (snd new_perms2) m1'').
              admit.
          +  (* Proof of match goes after the comment *)
            { !context_goal one_thread_match.
              eapply build_match_compiled; auto.
              admit.
            }
          + constructor; constructor.
          + simpl in *. econstructor.
            subst st1'; destruct new_perms1; reflexivity.
          + simpl in *. econstructor.
            subst st2' ofs2; destruct new_perms2. repeat f_equal.
            !goal (unsigned (add ofs (repr delta)) = unsigned ofs + delta).
            admit.
            !goal (pair0 empty_map = virtueLP_inject _ _ (pair0 empty_map)).
            admit.

        - subst evnt2. replace (unsigned ofs2) with (unsigned ofs + delta).
          repeat econstructor; eassumption.
          admit.
        - split; [admit|].

          assert (Hofs2: intval ofs2 = unsigned ofs + delta).
          { admit. }
          rewrite <- Hofs2 in *.

          eapply step_mklock;
            eauto; try reflexivity;
              try unfold HybridMachineSig.isCoarse,
              HybridMachineSig.HybridCoarseMachine.scheduler.
          + !goal (@invariant (HybridSem _) _ st2).
            eapply CMatch.
            
          + (* at_external for code 4. *)
            move Hat_external2' at bottom.
            match goal with
              |- context [restrPermMap ?Hlt]=>
            pose proof (cur_equiv_restr_mem_equiv _ _ Hlt Hthread_mem2)
            end.
            pose proof (Asm_at_external_proper Asm_g code2 _ eq_refl _ _ H).
            simpl in H0; simpl. unfold Asm_g in H0.
            rewrite H0. eauto.
            
          + (* Mem.range_perm *)
            (* Can write the lock *) simpl.
            !goal(Mem.range_perm _ _ _ (intval ofs2 + LKSIZE) Cur Writable).
            inversion Hlock_update_mem_strict2; subst vstore.
            rewrite Hofs2.
            eapply range_perm_mem_equiv_Cur; try apply eq_refl; eauto.
            * eapply Cur_equiv_restr; reflexivity.
            * eapply permMapLt_range_mem.
              admit. (*by injecting from above*)
              
          + (* the store *)
            inversion Hlock_update_mem_strict2; subst vstore.
            rewrite (mem_is_restr_eq m2') in Hstore.
            erewrite restrPermMap_equiv_eq; eauto.
          + simpl; inv HH0; auto.
          + simpl; inv HH0; auto.
          + !goal (lockRes _ (b2,_) = None).
            eapply INJ_lock_permissions_None; eauto.

        
      Admitted.*) (* free_step_diagram_compiled *)
      
      Lemma free_step_diagram:
        let hybrid_sem:= (sem_coresem (HybridSem(Some hb))) in 
        forall (m1 m2: mem) (U : list nat) tid cd tr2 (mu : meminj)
          (HSched: HybridMachineSig.schedPeek U = Some tid)
          (st1 : ThreadPool (Some hb)) cnt1
          (st2 : ThreadPool (Some (S hb))) cnt2
          (Hsame_sch: same_cnt tid st1 st2 cnt1 cnt2)
          (c : semC) (b : block) (ofs : int)
          (new_perms : Pair access_map)
          (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
          (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
          (CMatch: concur_match cd mu st1 m1 st2 m2)
          (pdata : nat -> option permission) (lock_data : lock_info)
          (Hnone_beyond: bounded_maps.bounded_nat_func' pdata LKSIZE_nat)
          (Hcode: getThreadC cnt1 = Kblocked c)
          (Hat_external: semantics.at_external hybrid_sem c m1  =
                         Some (FREE_LOCK, (Vptr b ofs :: nil)%list))
          (Hlock_map: lockRes st1 (b, Integers.Ptrofs.unsigned ofs) = Some lock_data)
          (Hempty_lock: forall b ofs, pair1 (fun map => map !! b ofs) lock_data = pair0 None)
          (HlocksLt: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1) )
          (Hrange_perm: perm_interval (restrPermMap HlocksLt)
                                      b (unsigned ofs) LKSIZE Cur Writable)
          (HsetPerms:
             setPermBlock_var_pair b (unsigned ofs) LKSIZE_nat
                                   (pdata, fun _:nat => None) (getThreadR cnt1) = new_perms)
          (HH: forall i, 0 <= (Z.of_nat i) < LKSIZE ->
                    Mem.perm_order'' (pdata (S i)) (Some Writable)),
        exists evnt' (st2' : t) (m2' : mem),
          let evnt:= (Events.freelock (b, unsigned ofs)) in
          let st1':= remLockfFullUpdate st1 tid cnt1
                                        (Kresume c Vundef) new_perms (b, unsigned ofs) in
          concur_match cd mu st1' m1 st2' m2' /\
          inject_sync_event mu evnt evnt' /\
          HybridMachineSig.external_step
            (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
            U tr2 st2 m2
            (HybridMachineSig.schedSkip U)
            (tr2 ++ (Events.external tid evnt' :: nil)) st2' m2'.
      Proof.
        
        intros; simpl in *.
        inv Hsame_sch.
        pose proof (memcompat1 CMatch) as Hcmpt1.
        assert (thread_compat1: thread_compat _ _ cnt1 m1) by
            (apply mem_compatible_thread_compat; apply CMatch).
        pose proof (cur_equiv_restr_mem_equiv _ _ (th_comp thread_compat1) Hthread_mem1) as
            Hmem_equiv.
        
        (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
        destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].

        - (* (tid < hb) *)
          pose proof (mtch_target _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
            as match_thread.
          simpl in Hcode; exploit_match ltac:(apply CMatch).
          inversion H3. (* Asm_match *)
          
          (*Destruct the values of the self simulation *)
          pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
          assert (Hinj':=Hinj).
          pose proof (self_simulation.ssim_external _ _ Aself_simulation) as sim_atx.
          eapply sim_atx in Hinj'; eauto.
          2: { (*at_external*)
            clean_cmpt. 
            erewrite restr_proof_irr.
            rewrite Hmem_equiv; simpl; eassumption.
          }
          clear sim_atx.
          destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.
          (* bounded_maps.bounded_nat_func' pdata LKSIZE_nat *)
          (edestruct (free_step_diagram_self AsmSem) as
              (e' & m2' & Hthread_match & Htrace_inj & external_step)); eauto;
            first[ eassumption|
                   econstructor; eassumption|
                   solve[econstructor; eauto] |
                   eauto].
          + clean_cnt; eassumption.
          + (*match_self*)
            econstructor.
            * eapply cinject.
            * simpl; clean_cmpt.
              move matchmem at bottom.
              admit. (* match_mem proper with mem_equiv*)
          + exists e'; eexists; exists m2'.
            split; [|split].
            * (* reestablish concur *)
              rename b into BB.
              !goal (concur_match _ _ (remLockfFullUpdate _ _ _ _ _ _ ) _ _ _).
              admit.
            * clear - Htrace_inj; auto.
            * econstructor; eauto.
              
        - (* tid = hb *)
          subst tid. 
          (* rename the memories, to show that they have been modified, 
               since the execution of this thread stopped. *)
          rename m1 into m1'.
          rename m2 into m2'.
          
          (* Retrieve the match relation for this thread *)
          pose proof (mtch_compiled _ _ _ _ _ _ CMatch _ ltac:
                      (reflexivity)
                        cnt1 (contains12 CMatch cnt1)) as Hmatch.
          exploit_match ltac:(apply CMatch).
          
          rename H5 into Hinterference1.
          rename H7 into Hinterference2.
          rename H1 into Hcomp_match.
          rename H2 into Hstrict_evolution.
          
          rename cnt1 into Hcnt1.
          rename Hat_external into Hat_external1.
          rename b into b1.
          (* rename Hstore into Hstore1. *)
          
          rewrite RPM in Hinterference1.
          symmetry in H0.
          clean_cnt.
          exploit (free_step_diagram_compiled m1 m1');
            try eapply CMatch;
            eauto; try reflexivity.
          + econstructor; eassumption.
          + admit.
          + !goal (strict_evolution_diagram _ _ _ _ _ _ _).
            econstructor; eauto.
            admit. (* There is some problem here with equivalences *)
            admit. (* There is some problem here with equivalences *)
            
        - (* hb < tid *)
          pose proof (mtch_source _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
            as match_thread.
          simpl in Hcode; exploit_match ltac:(apply CMatch).
          inversion H3. (* Asm_match *)
          
          (*Destruct the values of the self simulation *)
          pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
          assert (Hinj':=Hinj).
          pose proof (self_simulation.ssim_external _ _ Cself_simulation) as sim_atx.
          eapply sim_atx in Hinj'; eauto.
          2: { (*at_external*)
            clean_cmpt. 
            erewrite restr_proof_irr.
            rewrite Hmem_equiv; simpl; eassumption.
          }
          clear sim_atx.
          destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.
          
          (edestruct (free_step_diagram_self CSem) as
              (e' & m2' & Hthread_match & Htrace_inj & external_step)); eauto;
            first[ eassumption|
                   econstructor; eassumption|
                   solve[econstructor; eauto] |
                   eauto].
          + clean_cnt; eassumption.
          + (*match_self*)
            econstructor.
            * eapply cinject.
            * simpl; clean_cmpt.
              move matchmem at bottom.
              admit. (* match_mem proper with mem_equiv*)
          + exists e'; eexists; exists m2'.
            split; [|split].
            * (* reestablish concur *)
              rename b into BB.
              !goal (concur_match _ _ (remLockfFullUpdate _ _ _ _ _ _ ) _ _ _).
              admit.
            * clear - Htrace_inj; auto.
            * econstructor; eauto.
              
              
      Admitted.


      (*TODO move to Mem_equiv*)
      
      Lemma acquire_fail_step_diagram_compiled:
        let hybrid_sem:= (sem_coresem (HybridSem (Some hb))) in 
        forall (m1 m1' m1'' : mem) (U : list nat) (cd : compiler_index)
          mu tr2 st1  
          st2 (m2' : mem) Hcnt1 Hcnt2
          (Hsame_sch: same_cnt hb st1 st2 Hcnt1 Hcnt2)
          b1 ofs (code1 : semC)  (code2 : Asm.state)
          (Hthread_mem1: access_map_equiv (thread_perms hb st1 Hcnt1) (getCurPerm m1'))
          (Hthread_mem2: access_map_equiv (thread_perms hb st2 Hcnt2) (getCurPerm m2'))
          (CMatch: concur_match (Some cd) mu st1 m1' st2 m2')
          (Hcode1: getThreadC Hcnt1 = Kblocked (SST code1))
          (Hcode2 : getThreadC Hcnt2 = Kblocked (TST code2))
          (Hat_external1': semantics.at_external hybrid_sem (SST code1) m1' =
                           Some (LOCK, (Vptr b1 ofs :: nil)%list))
          (Hlock_lt: permMapLt (lock_perms _ _ Hcnt1) (getMaxPerm m1')),
          let m1_locks:= restrPermMap Hlock_lt in
          forall (Hload: Mem.load AST.Mint32 m1_locks b1 (unsigned ofs) = Some vzero)
                 (Hrange_perm: perm_interval m1_locks b1 (unsigned ofs) LKSIZE Cur Readable)
                 (Hstrict: strict_evolution_diagram cd mu code1 m1 m1' code2 m2'),
          exists evnt2,
          forall m2_any (Hcmpt2: mem_compatible st2 m2_any),
            let evnt:= (Events.failacq (b1, unsigned ofs)) in
            concur_match (Some cd) mu st1 m1'' st2 m2_any /\
            inject_sync_event mu evnt evnt2 /\
            HybridMachineSig.external_step
              (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
              U tr2 st2 m2_any (HybridMachineSig.schedSkip U)
              (tr2 ++ (Events.external hb evnt2 :: nil)) st2 m2_any.
      Proof.
        (* TODO SUNDAY: *)
      Admitted.
      




      


      
      Lemma acquire_fail_step_diagram:
        let hybrid_sem:= (sem_coresem (HybridSem(Some hb))) in 
        forall (m1 m2: mem) (U : list nat) tr2 tid mu cd b ofs c
               (HSched: HybridMachineSig.schedPeek U = Some tid)
               (st1 : ThreadPool (Some hb)) cnt1
               (st2 : ThreadPool (Some (S hb))) cnt2
               (Hsame_sch: same_cnt tid st1 st2 cnt1 cnt2)
               (CMatch: concur_match cd mu st1 m1 st2 m2)
               (Hthread_mem1: access_map_equiv (thread_perms _ _ cnt1) (getCurPerm m1))
               (Hthread_mem2: access_map_equiv (thread_perms _ _ cnt2) (getCurPerm m2))
               (Hat_external: semantics.at_external hybrid_sem c m1  =
                              Some (LOCK, (Vptr b ofs :: nil)%list))
               (Hlock_lt: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1)),
          let m1_locks:= restrPermMap Hlock_lt in
          forall (Hload: Mem.load AST.Mint32 m1_locks b (unsigned ofs) = Some vzero)
                 (Hrange_perm: perm_interval m1_locks b (unsigned ofs) LKSIZE Cur Readable)
                 (Hcode: getThreadC cnt1 = Kblocked c),
          forall perm Hlt_perm,
            let any_mem:= @restrPermMap perm m2 Hlt_perm in
            exists evnt',
              concur_match cd mu st1 m1 st2 any_mem /\
              let evnt:= (Events.failacq (b, unsigned ofs)) in
              inject_sync_event mu evnt evnt' /\
              HybridMachineSig.external_step
                (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
                U tr2 st2 any_mem (HybridMachineSig.schedSkip U)
                (seq.cat tr2 (Events.external tid evnt' :: nil)) st2 any_mem.
      Proof.
        intros; simpl in *.
        inv Hsame_sch.
        pose proof (memcompat1 CMatch) as Hcmpt1.
        assert (thread_compat1: thread_compat _ _ cnt1 m1) by
            (apply mem_compatible_thread_compat; apply CMatch).
        pose proof (cur_equiv_restr_mem_equiv _ _ (th_comp thread_compat1) Hthread_mem1) as
            Hmem_equiv.
        
        (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
        destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].
        
        - (* (tid < hb) *)
          pose proof (mtch_target _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
            as match_thread.
          simpl in Hcode; exploit_match ltac:(apply CMatch).
          inversion H3. (* Asm_match *)
          
          (*Destruct the values of the self simulation *)
          pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
          assert (Hinj':=Hinj).
          pose proof (self_simulation.ssim_external _ _ Aself_simulation) as sim_atx.
          eapply sim_atx in Hinj'; eauto.
          2: { (*at_external*)
            clean_cmpt. 
            erewrite restr_proof_irr.
            rewrite Hmem_equiv; simpl; eassumption.
          }
          clear sim_atx.
          destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

          assert (Hth_lt1: permMapLt (thread_perms tid st1 cnt1) (getMaxPerm m1))
            by eapply CMatch.
          assert (Hth_lt2: permMapLt (thread_perms tid st2 cnt2) (getMaxPerm m2))
            by eapply CMatch.
          remember (restrPermMap Hth_lt1) as m1_thread.
          remember (restrPermMap Hth_lt2) as m2_thread.
          
          unshelve (edestruct (acquire_fail_step_diagram_self
                                 AsmSem m1_thread m2_thread) as
                       (e' & Htrace_inj & external_step);
                    eauto; try eapply Hlock_lt;
                    first[ eassumption|
                           econstructor; eassumption|
                           solve[econstructor; eauto] |
                           eauto]); subst m1_thread m2_thread.
          1,2,3: shelve.
          + rewrite getMax_restr; assumption.
          + eapply concur_match_perm_restrict; eassumption.
          + rewrite getCur_restr; reflexivity.
          + rewrite getCur_restr; clean_cnt; reflexivity.
          + (* match_self*)
            inv H3; econstructor; eauto.
            repeat clean_cnt.
            replace (restrPermMap Hth_lt1) with (restrPermMap Hlt1).
            replace (restrPermMap Hth_lt2) with (restrPermMap Hlt2).
            assumption.
            assert (Hcnt = cnt2). { eapply Axioms.proof_irr. }
                                  subst Hcnt.
            eapply restr_proof_irr.
            eapply restr_proof_irr.
            
          + simpl. !goal(Asm.at_external _ _ = _).
            instantiate(1:=ofs).
            pose proof (Asm_at_external_proper
                          Asm_g code1 _ eq_refl
                          (restrPermMap Hth_lt1) m1).
            unfold Asm_g in *. simpl in H; rewrite H; eauto.
            eapply cur_equiv_restr_mem_equiv; assumption.
          + rewrite <- restrPermMap_idempotent; eauto.
          + unfold perm_interval.
            rewrite <- restrPermMap_idempotent; eauto.
          + eexists.
            repeat (weak_split eauto).
            * rewrite (mem_is_restr_eq m1); subst any_mem.
              eapply concur_match_perm_restrict; eauto.
            * unshelve econstructor; eauto.
              apply mem_compat_restrPermMap; apply CMatch.
              simpl. subst any_mem.
              specialize (external_step perm ).
              unshelve (exploit external_step); intros.
              -- do 2 apply mem_compat_restrPermMap.
                 eapply CMatch.
              -- rewrite getMax_restr. assumption.
              -- revert H; clear. clean_proofs.
                 pose proof (restrPermMap_idempotent_eq _ Hlt_perm abs_proof) as Heq.
                 dependent_rewrite Heq.
                 clear. clean_proofs; auto.


        - (* tid = hb *)
          subst tid. 
          (* rename the memories, to show that they have been modified, 
               since the execution of this thread stopped. *)
          rename m1 into m1'.
          rename m2 into m2'.
          
          (* Retrieve the match relation for this thread *)
          pose proof (mtch_compiled _ _ _ _ _ _ CMatch _ ltac:
                      (reflexivity)
                        cnt1 (contains12 CMatch cnt1)) as Hmatch.
          exploit_match ltac:(apply CMatch).
          
          rename H5 into Hinterference1.
          rename H7 into Hinterference2.
          rename H1 into Hcomp_match.
          rename H2 into Hstrict_evolution.
          
          rename cnt1 into Hcnt1.
          (*rename Hlt' into Hlt_setbBlock1. *)
          rename Hat_external into Hat_external1.
          rename b into b1.
          rename Hload into Hload1.
          
          symmetry in H0; clean_cnt.
          exploit (acquire_fail_step_diagram_compiled m1 m1' m2') ;
            try eapply CMatch; eauto;
              try reflexivity.
          + econstructor; eassumption.
          + econstructor; debug eauto.
            * !goal(mem_interference m1 lev1 m1'). admit.   
            * !goal(mem_interference m2 lev2 m2'). admit.
          + instantiate(1:=tr2).
            clear - CMatch Hcnt1 Hcnt.
            intros (?&?&?&?).
            { apply mem_compat_restrPermMap; apply CMatch. }

            eexists; eauto.
            repeat weak_split eauto.
            * rewrite (mem_is_restr_eq m1'); subst any_mem.
              eapply concur_match_perm_restrict; eauto.

              
        - (* hb < tid *)
          pose proof (mtch_source _ _ _ _ _ _ CMatch _ l cnt1 (contains12 CMatch cnt1))
            as match_thread.
          simpl in Hcode; exploit_match ltac:(apply CMatch).
          inversion H3. (* Asm_match *)
          
          (*Destruct the values of the self simulation *)
          pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
          assert (Hinj':=Hinj).
          pose proof (self_simulation.ssim_external _ _ Cself_simulation) as sim_atx.
          eapply sim_atx in Hinj'; eauto.
          2: { (*at_external*)
            clean_cmpt. 
            erewrite restr_proof_irr.
            rewrite Hmem_equiv; simpl; eassumption.
          }
          clear sim_atx.
          destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

          assert (Hth_lt1: permMapLt (thread_perms tid st1 cnt1) (getMaxPerm m1))
            by eapply CMatch.
          assert (Hth_lt2: permMapLt (thread_perms tid st2 cnt2) (getMaxPerm m2))
            by eapply CMatch.
          remember (restrPermMap Hth_lt1) as m1_thread.
          remember (restrPermMap Hth_lt2) as m2_thread.
          
          
          unshelve (edestruct (acquire_fail_step_diagram_self
                                 CSem m1_thread m2_thread) as
                       (e' & Htrace_inj & external_step);
                    eauto; try eapply Hlock_lt;
                    first[ eassumption|
                           econstructor; eassumption|
                           solve[econstructor; eauto] |
                           eauto]); subst m1_thread m2_thread.
          1,2,3: shelve.
          + rewrite getMax_restr; assumption.
          + eapply concur_match_perm_restrict; eassumption.
          + rewrite getCur_restr; reflexivity.
          + rewrite getCur_restr; clean_cnt; reflexivity.
          + (* match_self*)
            inv H3; econstructor; eauto.
            repeat clean_cnt.
            replace (restrPermMap Hth_lt1) with (restrPermMap Hlt1).
            replace (restrPermMap Hth_lt2) with (restrPermMap Hlt2).
            assumption.
            assert (Hcnt = cnt2). { eapply Axioms.proof_irr. }
                                  subst Hcnt.
            eapply restr_proof_irr.
            eapply restr_proof_irr.
            
          + simpl. !goal(Clight.at_external _ = _).
            instantiate(1:=ofs).
            pose proof (C_at_external_proper
                          Clight_g code1 _ eq_refl
                          (restrPermMap Hth_lt1) m1).
            unfold Clight_g in *. simpl in H; rewrite H; eauto.
            eapply cur_equiv_restr_mem_equiv; assumption.
          + rewrite <- restrPermMap_idempotent; eauto.
          + unfold perm_interval.
            rewrite <- restrPermMap_idempotent; eauto.
          + eexists.
            repeat (weak_split eauto).
            * rewrite (mem_is_restr_eq m1); subst any_mem.
              eapply concur_match_perm_restrict; eauto.
            * unshelve econstructor; eauto.
              apply mem_compat_restrPermMap; apply CMatch.
              simpl. subst any_mem.
              specialize (external_step perm ).
              unshelve (exploit external_step); intros.
              -- do 2 apply mem_compat_restrPermMap.
                 eapply CMatch.
              -- rewrite getMax_restr. assumption.
              -- revert H; clear. clean_proofs.
                 pose proof (restrPermMap_idempotent_eq _ Hlt_perm abs_proof) as Heq.
                 dependent_rewrite Heq.
                 clear. clean_proofs; auto.

                 Unshelve.
                 eapply CMatch.
                 eapply CMatch. 
                 
      Admitted.
      
      Instance sub_map_virtue_proper:
        Proper (Logic.eq ==> access_map_equiv ==> iff) sub_map_virtue.
      Admitted.
      
      Lemma lock_update_mem_strict_load_restr:
        forall b ofs l_perms m m' lval sval p Hlt,
          lock_update_mem_strict_load b ofs l_perms m m' lval sval ->
          lock_update_mem_strict_load b ofs l_perms (@restrPermMap p m Hlt) m' lval sval.
      Proof.
      Admitted.
      
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

          remember (Build_virtue virtueThread0 (getThreadR cnt1)) as angel'.
          edestruct (acquire_step_diagram angel' m1) as
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
          + !goal(pair21_prop bounded_maps.sub_map _ _).
            move Hbounded at bottom.
            unfold Max_equiv in *.
            repeat (autounfold with pair);
              unfold pair_prop; simpl.
            unfold bounded_maps.sub_map in Hbounded.
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
          remember (Build_virtue virtueThread0 virtueLP0) as angel'.
          assert (Hmax_equiv1: Max_equiv m1_base m1).
          { subst. symmetry.  eapply restr_Max_equiv. }
          assert (Hnb1: Mem.nextblock m1_base = Mem.nextblock m1).
          { subst;reflexivity. }
          assert (Hmem_compat: mem_compatible st1 m1).
          { eapply mem_compat_Max; try eapply Hcmpt; eauto. }
          
          unshelve edestruct (release_step_diagram angel' m1 m1') as
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
          edestruct (make_step_diagram m1) as (?&?&?&?&?&?);
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
          edestruct (free_step_diagram m_restr) as (?&?&?&?&?&?);
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
          
          edestruct (acquire_fail_step_diagram m_restr) as (?&?&?&?);
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
          subst. inversion H2; subst.
          inversion H. simpl in *.
          clean_cnt.
          assert (m1_restr: permMapLt (thread_perms _ _ Htid) (getMaxPerm m1')) by
              eapply memcompat1.
          assert (m2_restr: permMapLt (thread_perms _ _ Hcnt2) (getMaxPerm m2)) by
              eapply memcompat2.
          specialize (mtch_compiled hb ltac:(reflexivity) Htid Hcnt2
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
