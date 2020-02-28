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
Require Import VST.concurrency.compiler.advanced_permissions.
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.

Require Import VST.concurrency.compiler.Clight_self_simulation.
Require Import VST.concurrency.compiler.Asm_self_simulation.
Require Import VST.concurrency.compiler.diagrams.
Require Import VST.concurrency.common.mem_equiv.
Require Import VST.concurrency.lib.pair.
Require Import VST.concurrency.compiler.inject_virtue.
Require Import VST.concurrency.common.Compcert_lemmas.

Require Import VST.sepcomp.Address.


Require Import VST.concurrency.memsem_lemmas.
Import BinNums.

Import BinInt.
Import List.
Import Integers.
Import Ptrofs.
Import Basics.
Import FunctionalExtensionality.

Set Nested Proofs Allowed.
Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.

(* MOVE TO PERMISSIONS.V*)

Import HybridMachineSig.
Import DryHybridMachine.
Import self_simulation.

Existing Instance OrdinalPool.OrdinalThreadPool.
Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.


Import OrdinalPool.

Section ConcurMatch.
  Context {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}.

  (*Module MyThreadSimulationDefinitions :=
    ThreadSimulationDefinitions CC_correct Args.*)

  Section OneThread.
    Context (hb: nat).
    Definition SemTop: Semantics:= (HybridSem (Some hb)).
    Definition SemBot: Semantics:= (HybridSem (Some (S hb))).
    
    Notation thread_perms st i cnt:= (fst (@getThreadR dryResources _ i st cnt)).
    Notation lock_perms st i cnt:= (snd (@getThreadR dryResources _ i st cnt)).
    
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
    | Thread_Resume: forall j code1 m1 code2 m2,
        match_state j code1 m1 code2 m2 ->
        match_thread state_type1 state_type2 match_state j
                     (Kresume (state_type1 code1) Vundef) m1
                     (Kresume (state_type2 code2) Vundef) m2
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

    Section LockUpdate.
      (*There is a similar one in common/Compcert_lemmas.v *)
      (* Some lemmas that might be better put somewhere else *)
      Inductive lock_update {hb}: nat -> ThreadPool hb -> Address.address ->
                                  (Pair access_map) -> lock_info -> _ -> ThreadPool hb -> Prop:=
      | Build_lock_update:
          forall st st' i add th_perms lock_perms c
            (cnt : containsThread st i),
            st' = updLockSet
                    (updThread(resources:=dryResources) cnt c th_perms)
                    add lock_perms ->
            @lock_update hb i st add th_perms lock_perms c st'.
      
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
        - unfold Max_equiv. do 2 rewrite getMax_restr_eq; assumption.
        - rewrite restr_Max_equiv; assumption.
      Qed.
      
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

    End  LockUpdate.

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

    Ltac lock_update_rewrite:=
      repeat lock_update_contains;
      simpl in *;
      unshelve (repeat (super_rewrite)); try eassumption.

    


    
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
    | CThread_Resume: forall j' cd code1 m1 code2 m2,
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
        match_thread_compiled (Some cd) j' (Kresume (SST code1) Vundef) m1
                              (Kresume (TST code2) Vundef) m2
    | CThread_Init: forall j m1 m2 v1 v1' v2 v2',
        Val.inject j v1 v2 ->
        Val.inject j v1' v2' ->
        match_thread_compiled None j (Kinit v1 v1') m1
                              (Kinit v1 v1') m2.
    (* Inject the value in lock locations *)

    
    
    Section ConcurMatch. (* 360 *)
      Definition option_map_prop := 
        fun {A B : Type} (f : A -> B -> Prop) (x : option A) (y : option B) =>
          match x,y with
          | Some x', Some y'  => f x' y'
          | None, None => True
          | _, _ => False
          end.
      
      
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
                perm_surj j (lock_perms _ _ cnt1) (lock_perms _ _  cnt2)
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
          ; writable_locks:
              forall b ofs rec1, lockRes cstate1 (b, ofs) = Some rec1 ->
                                 Mem.perm m1 b ofs Max Writable
          ; INJ_lock_permissions_image:
              forall b b' delt,
                j b = Some (b', delt) ->
                forall ofs rec1, lockRes cstate1 (b, ofs) = Some rec1 ->
                                 exists rec2,
                                   lockRes cstate2 (b', ofs + delt) = Some rec2 /\
                                   access_map_equiv_pair (virtueLP_inject m2 j rec1) rec2            
          ; INJ_lock_permissions_preimage:
              forall b2 ofs_delt rec2, lockRes cstate2 (b2, ofs_delt) = Some rec2 ->
                                       exists rec1 b1 ofs delt,
                                         j b1 = Some (b2, delt) /\
                                         lockRes cstate1 (b1, ofs) = Some rec1 /\
                                         (pair2_prop access_map_equiv) (virtueLP_inject m2 j rec1) rec2 /\
                                         ofs_delt = ofs + delt          
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
                        exists X, lockRes cstate2 (b', unsigned ofs + delt) =
                                  Some  X /\
                                  pair2_prop access_map_equiv X
                                             ((virtueLP_inject m2 j) rmap).
      Proof. intros. eapply INJ_lock_permissions_image in H1; eauto.
             destruct H1 as (?&?&?&?); simpl in *.
             eexists; split; try eassumption.
             split; simpl; symmetry; eauto.
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
        - intros *; erewrite restr_Max_equiv.
          apply writable_locks0.
        - erewrite virtueLP_inject_max_eq_exteny. eauto.
          eapply getMax_restr_eq.
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
      
      Lemma concur_match_perm_restrict1:
        forall cd j st1 m1 st2 m2,
          concur_match cd j st1 m1 st2 m2 ->
          forall perms1 (permMapLt1: permMapLt perms1 (getMaxPerm m1)),
            concur_match cd j st1 (restrPermMap permMapLt1) st2 m2.
      Proof.
        intros;
          rewrite (mem_is_restr_eq m2). apply concur_match_perm_restrict; auto.
      Qed.
      Lemma concur_match_perm_restrict2:
        forall cd j st1 m1 st2 m2,
          concur_match cd j st1 m1 st2 m2 ->
          forall perms2
                 (permMapLt2: permMapLt perms2 (getMaxPerm m2)),
            concur_match cd j st1 m1 st2 (restrPermMap permMapLt2).
      Proof.
        intros;
          rewrite (mem_is_restr_eq m1). apply concur_match_perm_restrict; auto.
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
      
      
      (*Lemma concur_match_same_running:
        forall (m : option mem) (cd : option compiler_index) (mu : meminj)
               (c1 : ThreadPool (Some hb)) (m1 : mem) (c2 : ThreadPool (Some (S hb))) 
               (m2 : mem),
          concur_match cd mu c1 m1 c2 m2 ->
          forall i : nat, False ->
                          machine_semantics.running_thread (HybConcSem (Some hb) m) c1 i <->
                          machine_semantics.running_thread (HybConcSem (Some (S hb)) m) c2 i.
      Proof. (*
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
      Qed. *)
      Admi tted. *)
      
      Inductive individual_match i:
        (option compiler_index) -> meminj -> ctl -> mem -> ctl -> mem -> Prop:= 
      |individual_mtch_source:
         (i > hb)%nat ->
         forall j s1 m1 s2 m2 cd,
           match_thread_source j s1 m1 s2 m2 ->
           individual_match i cd j s1 m1 s2 m2
      |individual_mtch_target:
         (i < hb)%nat ->
         forall j s1 m1 s2 m2 cd,
           match_thread_target j s1 m1 s2 m2 ->
           individual_match  i cd j s1 m1 s2 m2
      | individual_mtch_compiled:
          (i = hb)%nat ->
          forall cd j s1 m1 s2 m2,
            match_thread_compiled cd j s1 m1 s2 m2 ->
            individual_match i cd j s1 m1 s2 m2.

      
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
      
      
      
      (* DONT HAVE TO Change 4 to something that depends the architecture 32-64 
           In both architectures we store only 32 bites.
       *)


      
      
      
      Inductive update_mem (m m':mem) (adr:block * Z): Prop:=
      | Build_update_mem:
          Max_equiv m m' ->
          Cur_equiv m m' ->
          Mem.nextblock m = Mem.nextblock m' ->
          content_almost_same m m' adr ->
          update_mem m m' adr.
      Lemma injection_update_restrict:
        forall f m1 m1' m2 m2' p1 p2 adr1 adr2,
          max_valid_perm m1 AST.Mint32 (fst adr1) (snd adr1) Writable ->
          update_mem m1 m1' adr1 ->
          update_mem m2 m2' adr2 ->
          inject_address f adr1 adr2 ->
          Forall2 (memval_inject f) (get_vals_at m1' adr1) (get_vals_at m2' adr2) ->
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
        - unfold max_valid_perm, Mem.range_perm; intros.
          rewrite restr_Max_equiv; simpl in *.
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
                 (Hlock_ppimage: perm_surj f th_lock_perms1 th_lock_perms2)
                 (Hlt_lock1 : permMapLt th_lock_perms1 (getMaxPerm m1'))
                 (Hlt_lock2 : permMapLt th_lock_perms2 (getMaxPerm m2'))
                 (Hinj_locks: Mem.inject f (restrPermMap Hlt_lock1) (restrPermMap Hlt_lock2))
                 (Hinj_lock: f b_lock1 = Some (b_lock2, delta)) c1 c2
                 (Hthread_match: one_thread_match hb i ocd f  
                                                  c1 (restrPermMap Hlt1)
                                                  c2 (restrPermMap Hlt2))
                 (Hval_inj: Forall2 (memval_inject f) v1 v2),
          forall lock_perms1
                 (cnt1 : containsThread st1 i)
                 (cnt2 : containsThread st2 i) pmap
                 (Hpmap_equiv: access_map_equiv_pair (virtueLP_inject m2' f lock_perms1) pmap),
            lock_update i st1 (b_lock1,ofs_lock) (th_perms1,th_lock_perms1)
                        lock_perms1 c1 st1' ->
            lock_update i st2 (b_lock2,ofs_lock+delta) (th_perms2,th_lock_perms2)
                        pmap c2 st2' ->
            concur_match ocd' f st1' m1' st2' m2'.
      Proof.
        intros. 
        
        assert (Hsame_lenght1: num_threads st1 = num_threads st1').
        { inv H0; reflexivity. }
        assert (Hsame_lenght2: num_threads st2 = num_threads st2').
        { inv H1; reflexivity. }
        
        repeat destruct_lock_update_getters.
        assert (Hmax_equiv0': Max_equiv m1 m1').
        { intros ?; rewrite Hmax_equiv0; auto. }

        eapply Build_concur_match; simpl; eauto.
        - rewrite <- Hsame_lenght1, <- Hsame_lenght2; apply H.
        - !goal(Events.injection_full _ _ ).
          intros b ?. eapply H. unfold Mem.valid_block.
          rewrite Hnb_equiv0; eauto.
        - !context_goal perm_surj.
          intros i0 ??; destruct (Nat.eq_dec i0 i); subst.
          + lock_update_rewrite.
          + lock_update_rewrite. eapply H.
        - !context_goal Mem.inject.
          intros i0 ??; destruct (Nat.eq_dec i i0); subst.
          + lock_update_rewrite.
            intros; repeat unify_proofs; assumption.
          + !context_goal  Mem.inject.
            intros; simpl in *.
            eapply injection_update_restrict; 
              eauto; simpl; eauto; try solve [econstructor; eauto];
                try solve[ econstructor; eauto;
                           intros ?; first [rewrite Hmax_equiv0 | rewrite Hmax_equiv]; auto].
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
              eauto; simpl; eauto; try solve [econstructor; eauto];
                try solve[ econstructor; eauto;
                           intros ?; first [rewrite Hmax_equiv0 | rewrite Hmax_equiv]; auto].
            intros.
            eapply mem_inject_equiv;
              try eapply INJ_locks; try reflexivity;
                try eapply restrPermMap_equiv; eauto;
                  try reflexivity; simpl.
            erewrite gtlo0; eauto; reflexivity.
            erewrite gtlo; eauto; reflexivity.
        - intros *.
          rewrite  <- Hmax_equiv0'.
          destruct (addressFiniteMap.AMap.E.eq_dec (b_lock1, ofs_lock) (b, ofs) ) as [e|n].
          + inv e; intros _.
            eapply Hmax_wrt0; eauto. simpl; omega.
          + simpl in *; rewrite glo0; auto.
            eapply writable_locks; eauto. 
        - intros until rec1.
          lock_update_rewrite; simpl.
          destruct (addressFiniteMap.AMap.E.eq_dec (b_lock1, ofs_lock) (b, ofs) ) as [e|n].
          
          2: exploit Coqlib3.neq_prod; try eassumption;
            try exact Classical_Prop.classic;
            intros [?| [? ?]]; swap 1 2.
          + inv e. rewrite gls0. intros HH; inv HH. unify_injection.
            rewrite gls; eexists; split; try reflexivity.
            auto.
          + subst; rewrite glo0 by assumption. unify_injection.
            intros HH; eapply INJ_lock_permissions_image in HH as
                (?&?&?); try eassumption.
            eexists; split.
            2: now (erewrite virtueLP_inject_max_eq_exteny; eauto).
            rewrite glo; eauto.
            intros HH; inv HH.
            eapply H2; clear - H5. omega.
          + subst; rewrite glo0 by assumption.
            intros HH.
            move Hinj_lock at bottom.
            destruct (peq b' b_lock2); swap 1 2.
            * erewrite <- virtueLP_inject_max_eq_exteny; try eassumption.
              rewrite glo. eapply INJ_lock_permissions_image; eauto.
              intros Hcontra; apply n0; inv Hcontra; eauto.
            * subst.
              
              assert (Mem.perm (restrPermMap Hlt1) b_lock1 ofs_lock Max Nonempty).
              {  rewrite restr_Max_equiv,  <- Hmax_equiv0'; eapply Mem.perm_implies;
                   [eapply Hmax_wrt0| constructor]; simpl; omega. }
              assert (Mem.perm (restrPermMap Hlt1) b ofs Max Nonempty).
              {  rewrite restr_Max_equiv , <- Hmax_equiv0'; eapply Mem.perm_implies.
                 eapply writable_locks; eauto. constructor. }
              
              exploit Mem.mi_no_overlap; try eapply Hinj_perms;
                try eassumption.

              intros. destruct H5 as [H5|H5]; try now (contradict H5; eauto).
              
              erewrite glo by ( intros AA; inv AA; auto).
              erewrite <- virtueLP_inject_max_eq_exteny; try eassumption.
              eapply INJ_lock_permissions_image; eauto.
        - intros *; simpl in *.
          destruct (addressFiniteMap.AMap.E.eq_dec (b_lock2, ofs_lock + delta) (b2, ofs_delt) ) as [e|n]. 
          + inv e.
            rewrite gls.
            intros HH;inv HH; do 4 econstructor.
            repeat (split; eauto; simpl).
          + erewrite glo; auto.
            intros HH; eapply INJ_lock_permissions_preimage in HH as
                (?&?&?&?&?&?&?&?); try eassumption.
            do 5 econstructor; eauto.
            split; swap 1 2.
            split; eauto; simpl.
            erewrite <- virtueLP_inject_max_eq_exteny; eassumption.
            rewrite glo0; eauto.
            intros HH; inv HH. unify_injection; auto.
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
      Admitted. (* concur_match_update_lock *)
      

      Lemma concur_match_add_thread: 
        forall i f (ocd: option (@compiler_index CC_correct Args))
               st1 m1 st2 m2
               (cnt1 : containsThread st1 i)
               (cnt2 : containsThread st2 i)
               c1 c2 th_perms11 th_perms12 th_perms21 th_perms22
               new_th_perms11 new_th_perms12 new_th_perms21 new_th_perms22
               b1 b2 ofs1 ofs2 arg1 arg2 delta,
          concur_match ocd f st1 m1 st2 m2 ->

          
          let st1' := updThread cnt1 c1 (th_perms11, th_perms12) in
          let st1'' := addThread st1' (Vptr b1 ofs1) arg1 (new_th_perms11,new_th_perms12) in
          let st2' := updThread cnt2 c2 (th_perms21,th_perms22) in
          let st2'' := addThread st2' (Vptr b2 ofs2) arg2 (new_th_perms21,new_th_perms22) in
          
          forall (Hmem_compat1: mem_compatible(tpool:=OrdinalThreadPool) st1'' m1)
                 (Hmem_compat2: mem_compatible(tpool:=OrdinalThreadPool) st2'' m2)
                 
                 (Hlock_ppimage: perm_surj f (th_perms12) (th_perms22))
                 (Hlock_ppimage: perm_surj f (new_th_perms12) (new_th_perms22))

                 (* Two mem injects for the OLD thread *)
                 (Hlt1 : permMapLt (th_perms11) (getMaxPerm m1))
                 (Hlt2 : permMapLt (th_perms21) (getMaxPerm m2))
                 (Hinj_perms: Mem.inject f (restrPermMap Hlt1) (restrPermMap Hlt2))
                 
                 (Hlt1_lk : permMapLt (th_perms12) (getMaxPerm m1))
                 (Hlt2_lk : permMapLt (th_perms22) (getMaxPerm m2))
                 (Hinj_lock: Mem.inject f (restrPermMap Hlt1_lk) (restrPermMap Hlt2_lk))

                 (* Two mem injects for the NEW thread *)
                 (Hlt1_new : permMapLt (new_th_perms11) (getMaxPerm m1))
                 (Hlt2_new : permMapLt (new_th_perms21) (getMaxPerm m2))
                 (Hinj_new_perms: Mem.inject f (restrPermMap Hlt1_new) (restrPermMap Hlt2_new))
                 
                 (Hlt1_lk_new : permMapLt (new_th_perms12) (getMaxPerm m1))
                 (Hlt2_lk_new : permMapLt (new_th_perms22) (getMaxPerm m2))
                 (Hinj_lock_new: Mem.inject f (restrPermMap Hlt1_lk_new) (restrPermMap Hlt2_lk_new))
                 
                 (Hinv1: invariant(tpool:=OrdinalThreadPool) st1'')
                 (Hinv2: invariant(tpool:=OrdinalThreadPool) st2'')

                 (* Match NEW thread *)
                 (Hthread_match: one_thread_match hb i ocd f  
                                                  c1 (restrPermMap Hlt1)
                                                  c2 (restrPermMap Hlt2))

                 (* Match NEW thread *)
                 (Hinj_args: Val.inject f arg1 arg2)
                 (Hinj_ptr: f b1 = Some (b2 , delta))
                 (Hinj_ptr: ofs2 = add ofs1 (repr delta)),
            concur_match ocd f st1'' m1 st2'' m2.
      Proof.
        (*This should go in concur_match *)
      Admitted. (* concur_match_add_thread *)
      
      Lemma mem_compat_upd:
        forall hb tid st cnt c m,
          @mem_compatible (HybridSem hb) _ st m ->
          @mem_compatible (HybridSem hb) _
                          (@updThreadC _ (HybridSem hb) tid st cnt c) m.
      Proof.
        intros * Hcmpt. 
        econstructor; intros.
        - erewrite <- ThreadPool.gThreadCR.
          eapply Hcmpt.
        - eapply Hcmpt.
          erewrite <- ThreadPool.gsoThreadCLPool; eauto.
        - eapply Hcmpt.
          erewrite <- ThreadPool.gsoThreadCLPool; eauto.
          Unshelve.
          all: eauto.
      Qed.

      Lemma invariant_updateC:
        forall hb st1 tid Htid c1,
          @invariant (HybridSem hb) _ st1 ->
          @invariant (HybridSem hb) _
                     (@updThreadC _ (HybridSem hb) tid st1 Htid c1).
      Proof.
        intros * Hinv.
        econstructor; intros; try solve[eapply Hinv].
        - pose proof (ThreadPool.cntUpdateC' _ _ cnti) as cnti'.
          pose proof (ThreadPool.cntUpdateC' _ _ cntj) as cntj'. 
          pose proof (ThreadPool.gThreadCR _ cnti' _ cnti) as Hi.
          pose proof (ThreadPool.gThreadCR _ cntj' _ cntj) as Hj.
          match goal with
            |- permMapsDisjoint2 ?X ?Y =>
            replace X with (ThreadPool.getThreadR cnti');
              replace Y with (ThreadPool.getThreadR cntj')
          end.
          apply Hinv; auto.
        - eapply Hinv; eauto.
        - eapply no_race in Hinv.
          eapply Hinv.
          eapply Hres.
        - eapply Hinv.
          eapply Hres.
      Qed.
      Definition thmem_from_concur1 { cd mu st1 m1 st2 m2 i}
                 (Hconcur: concur_match cd mu st1 m1 st2 m2)
                 (cnt: ThreadPool.containsThread st1 i) 
        : mem.
        unshelve (eapply restrPermMap, th_comp, 
                  mem_compatible_thread_compat, memcompat1;  eassumption).
        2: eassumption.
      Defined.
      Definition thmem_from_concur2 { cd mu st1 m1 st2 m2 i}
                 (Hconcur: concur_match cd mu st1 m1 st2 m2)
                 (cnt: ThreadPool.containsThread st2 i) 
        : mem.
        unshelve (eapply restrPermMap, th_comp, 
                  mem_compatible_thread_compat, memcompat2;  eassumption).
        2: eassumption.
      Defined.
      Definition upd_cd tid (cd cd': option compiler_index):=
        if Nat.eq_dec hb tid then cd' else cd. 
      Lemma concur_match_updateC:
        forall (st1: ThreadPool.t) (m1 : mem) (tid : nat)
               (Htid : ThreadPool.containsThread st1 tid)
               c1 (cd cd': option compiler_index) (st2 : ThreadPool.t) 
               (mu : meminj) (m2 : mem)
               c2 (Htid' : ThreadPool.containsThread st2 tid)
               updated_cd (Hconcur:concur_match cd mu st1 m1 st2 m2),
          individual_match tid cd' mu c1 (thmem_from_concur1 Hconcur Htid)
                           c2 (thmem_from_concur2 Hconcur Htid') ->
          updated_cd = (upd_cd tid cd cd') ->
          concur_match updated_cd mu
                       (updThreadC Htid  c1) m1
                       (updThreadC Htid' c2) m2.
      Proof.
        intros **. subst updated_cd.
        (econstructor; try solve[simpl; eauto]);
          try (simpl; eapply Hconcur).
        - eapply mem_compat_upd; apply Hconcur.
        - eapply mem_compat_upd; apply Hconcur.
        - apply invariant_updateC, Hconcur.
        - apply invariant_updateC, Hconcur.
        - intros.
          destruct (Nat.eq_dec i tid).
          + subst.
            do 2 erewrite (gssThreadCC).
            move H at bottom.
            inv H; try omega.
            unfold thmem_from_concur1,
            thmem_from_concur2 in *.
            clean_proofs.
            assumption.
          + do 2 (erewrite <- gsoThreadCC; auto).
            eapply Hconcur; auto.
        - intros.
          destruct (Nat.eq_dec i tid).
          + subst.
            do 2 erewrite (gssThreadCC).
            move H at bottom.
            inv H; try omega.
            unfold thmem_from_concur1,
            thmem_from_concur2 in *.
            clean_proofs.
            assumption.
          + do 2 (erewrite <- gsoThreadCC; auto).
            eapply Hconcur; auto.
        - intros.
          destruct (Nat.eq_dec i tid).
          + subst i; subst tid.
            do 2 erewrite (gssThreadCC).
            move H at bottom.
            inv H; try omega.
            unfold thmem_from_concur1,
            thmem_from_concur2 in *.
            clean_proofs.
            simpl.
            unfold upd_cd. match_case; eauto. 
          + do 2 (erewrite <- gsoThreadCC; auto).
            eapply Hconcur in H0.
            (* TODO! *)
      Admitted. (* concur_match_updateC *)
      
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
          individual_match tid cd' f' c1 m1' c2 m2' ->
          self_simulation.is_ext mu (Mem.nextblock m1) f' (Mem.nextblock m2) ->
          concur_match cd' f'
                       (updThread Htid c1
                                  (getCurPerm m1', snd (getThreadR Htid))) m1'
                       (updThread Htid' c2
                                  (getCurPerm m2', snd (getThreadR Htid'))) m2'.
      Proof.
        (* TODO! *)
      Admitted. (* concur_match_update1 *)

      
      (* concur_match *)

      
    End ConcurMatch.

    
    
  End OneThread.
  Arguments INJ_locks hb { ocd j cstate1 m1 cstate2 m2}.
  Arguments memcompat1 hb { ocd j cstate1 m1 cstate2 m2}. 
  Arguments memcompat2 hb { ocd j cstate1 m1 cstate2 m2}.
  Arguments th_comp {_ _ _ _ _}.
  Arguments lock_comp {_ _ _ _ _}.

  Local Notation thread_perms st i cnt:= (fst (@getThreadR dryResources _ i st cnt)).
  Local Notation lock_perms st i cnt:= (snd (@getThreadR dryResources _ i st cnt)).




  Lemma permMapLt_compute_inject_pair_useful':
    forall hb ocd mu st1 st2 m1 m2,
      (concur_match hb) ocd mu st1 m1 st2 m2 ->
      forall a1 i (cnt1: containsThread st1 i) cnt2 b1 b2 ,
        permMapLt_pair (computeMap_pair a1 b1) (getMaxPerm m1) ->
        (*permMapLt_pair (@getThreadR _ _ i st2 cnt2) (getMaxPerm m2) -> *)
        b2 = virtueThread_inject m2 mu b1 ->
        permMapLt_pair (computeMap_pair (@getThreadR _ _ i st2 cnt2) b2)
                       (getMaxPerm m2).
  Proof.
    intros **.
    pose proof (memcompat1 _ H) as Hcmpt1.
    pose proof (memcompat2 _ H) as Hcmpt2.
    eapply permMapLt_compute_inject_pair; eauto.
    eapply H.
    eapply Hcmpt2.

    Unshelve.
    all: eauto.
    eapply Hcmpt1.
    eapply Hcmpt2.
  Qed.
  Lemma permMapLt_compute_inject_pair_useful:
    forall hb ocd mu st1 st2 m1 m2,
      (concur_match hb) ocd mu st1 m1 st2 m2 ->
      forall a1 i (cnt1: containsThread st1 i) cnt2 b1 ,
        permMapLt_pair (computeMap_pair a1 b1) (getMaxPerm m1) ->
        permMapLt_pair (computeMap_pair (@getThreadR _ _ i st2 cnt2)
                                        (virtueThread_inject m2 mu b1))
                       (getMaxPerm m2).
  Proof. intros; eapply permMapLt_compute_inject_pair_useful'; eauto. Qed.


  Lemma concur_match_perm_restrict' perms1 perms2:
    forall (hb : nat) (cd : option compiler_index) (j : meminj)
      (st1 : ThreadPool (Some hb)) (m1 : mem) (st2 : ThreadPool (Some (S hb)))
      (m2 : mem)(permMapLt1 : permMapLt perms1 (getMaxPerm m1))
      (permMapLt2 : permMapLt perms2 (getMaxPerm m2)),
      concur_match hb cd j st1 (restrPermMap permMapLt1) st2
                   (restrPermMap permMapLt2) ->
      concur_match hb cd j st1 m1 st2 m2.
  Proof.
    intros.
    rewrite (mem_is_restr_eq m1), (mem_is_restr_eq m2).
    erewrite (@restrPermMap_idempotent_eq _ _ m1).
    erewrite (@restrPermMap_idempotent_eq _ _ m2).
    eapply concur_match_perm_restrict; eauto.

    Unshelve.
    all: rewrite getMax_restr; apply mem_cur_lt_max.
  Qed.

End ConcurMatch.

Notation thread_perms st i cnt:= (fst (@OrdinalPool.getThreadR dryResources _ i st cnt)).
Notation lock_perms st i cnt:= (snd (@OrdinalPool.getThreadR dryResources _ i st cnt)).


Notation sstate:= (state_sum (@semC CSem) (@semC AsmSem)).

Arguments INJ_locks {_ _} hb { ocd j cstate1 m1 cstate2 m2}.
Arguments memcompat1 {_ _} hb { ocd j cstate1 m1 cstate2 m2}. 
Arguments memcompat2 {_ _} hb { ocd j cstate1 m1 cstate2 m2}.
Arguments th_comp {_ _ _ _ _ _}.
Arguments lock_comp {_ _ _ _ _ _}.

(** *Tactics:*)

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


Ltac get_mem_compatible:=
  match goal with
  | CMatch:concur_match _ _ ?mu ?st1 ?m1 ?st2 ?m2,
           cnt1:containsThread ?st1 ?tid,
                cnt2:containsThread ?st2 ?tid
    |- _ => let Hcmpt1 := fresh "Hcmpt1" in
          let Hcmpt2 := fresh "Hcmpt2" in
          pose proof (memcompat1 _ CMatch) as Hcmpt1;
          (pose proof (memcompat2 _ CMatch) as Hcmpt2;
           (let thread_compat1 := fresh "thread_compat1" in
            let thread_compat2 := fresh "thread_compat2" in
            assert (thread_compat1 : thread_compat(tpool:=OrdinalThreadPool) _ _ cnt1 m1) by
                (apply mem_compatible_thread_compat; auto);
            assert (thread_compat2 : thread_compat(tpool:=OrdinalThreadPool) _ _ cnt2 m2) by
                (apply mem_compatible_thread_compat; auto)))
  end.

Definition thread_mems {Sem st i m}
           {cnt:containsThread(resources:=dryResources)(Sem:=Sem) st i}
           (th_compat: thread_compat _ _ cnt m):=
  (restrPermMap (th_comp th_compat),restrPermMap (lock_comp th_compat)).

Ltac get_thread_mems:=
  match goal with
    [CMatch : concur_match _ _ ?mu ?st1 ?m1 ?st2 ?m2,
              thread_compat1:thread_compat _ _ ?cnt1 ?m1,
                             thread_compat2:thread_compat _ _ ?cnt2 ?m2 |- _ ] =>
    (* Inequalities for the four perms*)
    let Hlt_th1:=fresh "Hlt_th1" in 
    let Hlt_th2:=fresh "Hlt_th2" in 
    let Hlt_lk1:=fresh "Hlt_lk1" in 
    let Hlt_lk2:=fresh "Hlt_lk2" in
    assert (Hlt_th1: permMapLt (thread_perms _ _ cnt1) (getMaxPerm m1))
      by eapply (memcompat1 _ CMatch);
    assert (Hlt_th2: permMapLt (thread_perms _ _ cnt2) (getMaxPerm m2))
      by eapply (memcompat2 _ CMatch);
    assert (Hlt_lk1: permMapLt (lock_perms _ _ cnt1) (getMaxPerm m1))
      by eapply (memcompat1 _ CMatch);
    assert (Hlt_lk2: permMapLt (lock_perms _ _ cnt2) (getMaxPerm m2))
      by eapply (memcompat2 _ CMatch);
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


Lemma match_same_state_type
  {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}:
  forall hb dp j tp1 m1 tp2 m2,
    concur_match hb dp j tp1 m1 tp2 m2 ->
    forall i (cnti1 : ThreadPool.containsThread tp1 i)
      (cnti2 : ThreadPool.containsThread tp2 i),
      get_state_type (ThreadPool.getThreadC cnti1) =
      get_state_type (ThreadPool.getThreadC cnti2).
Proof.
  intros.
  inv H. 
  destruct (gt_eq_gt_dec hb i) as [[?|?]|?].
  - unshelve exploit mtch_source0; eauto;
      try eapply memcompat3;
            try eapply memcompat4; simpl.
    intros HH. inv HH; reflexivity.
  - unshelve exploit mtch_compiled0; eauto;
      try eapply memcompat3;
      try eapply memcompat4. simpl.
    intros HH. inv HH; reflexivity.
  - unshelve exploit mtch_target0; eauto;
      try eapply memcompat3;
      try eapply memcompat4. simpl.
    intros HH. inv HH; reflexivity.
Qed.
Lemma concur_match_same_running
      {CC_correct : CompCert_correctness}
      {Args : ThreadSimulationArguments}:
  forall hb m (cd : option compiler_index) (mu : meminj)
    (c1 : ThreadPool (Some hb)) (m1 : mem)
    (c2 : ThreadPool (Some (S hb))) (m2 : mem),
    concur_match hb cd mu c1 m1 c2 m2 ->
    forall i : nat,
      machine_semantics.running_thread (HybConcSem (Some hb) m) c1 i <->
      machine_semantics.running_thread (HybConcSem (Some (S hb)) m)
                                       c2 i.
Proof.
  unfold machine_semantics.running_thread; simpl.
  intros.
  unfold HybridMachineSig.unique_Krun.
  split; intros.
  + assert (cnti': containsThread c1 j).
    { eapply contains21; eauto. }
    unshelve exploit match_same_state_type;
      try eapply H; eauto.
    erewrite H1; simpl.
    unfold get_state_type; match_case.
    intros.
    unshelve eapply H0; eauto.
  + assert (cnti': containsThread c2 j).
    { eapply contains12; eauto. }
    unshelve exploit match_same_state_type;
      try eapply H; eauto.
    erewrite H1; simpl.
    unfold get_state_type; match_case.
    intros.
    unshelve eapply H0; eauto.
Qed.

