Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.

Require Import VST.concurrency.compiler.Clight_self_simulation.
Require Import VST.concurrency.compiler.Asm_self_simulation.
Require Import VST.concurrency.compiler.diagrams.
Require Import VST.concurrency.compiler.mem_equiv.


Require Import VST.concurrency.memsem_lemmas.
Import BinNums.
Import BinInt.
Import List.
Import Integers.
Import Ptrofs.
Import FunctionalExtensionality.

Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.

Instance inject_delta_map_monotonic:
  Inject_Monotonic Events.inject_delta_map.
Proof.
  intros ??????.
Admitted.

(** *One thread simulation*)
Module ThreadedSimulation (CC_correct: CompCert_correctness).
   
  Import HybridMachineSig.
  Import DryHybridMachine.

  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.

  Section ThreadedSimulation.
  (** *C Semantics*)
  Context (C_program: Clight.program).
  Definition Clight_g : Clight.genv := Clight.globalenv C_program.
  Definition CSem : Semantics := ClightSemanticsForMachines.ClightSem Clight_g.
  Definition Cself_simulation := clight_self_simulation Clight_g.
  Definition Clight_code_inject := self_simulation.code_inject _ _ Cself_simulation.
  Definition Clight_match := self_simulation.match_self Clight_code_inject.
  
  (** *Asm Semantics*)
  Import X86Context.
  (*Import the Asm Hybrid Machine*)
  Context (Asm_program: Asm.program).
  Definition Asm_g := (@the_ge Asm_program).
  Context (Asm_genv_safe: Asm_core.safe_genv (@the_ge Asm_program)).
  Definition Aself_simulation := Asm_self_simulation Asm_g.
  Definition Asm_code_inject := self_simulation.code_inject _ _ Aself_simulation.
  Definition Asm_match := self_simulation.match_self Asm_code_inject.

  
  (** *AsHybrid Semantics and Machine*)
  Definition AsmSem : Semantics := @X86Sem Asm_program Asm_genv_safe.

  (** The hybrid semantics*)
  Instance HybridSem h : Semantics := CoreSem_Sum h CSem AsmSem.
  Existing Instance dryResources.
  Notation TP h := (threadPool.OrdinalPool.OrdinalThreadPool(Sem:=HybridSem h)).
  Existing Instance DryHybridMachineSig.
  Definition HybMachine h:=
    HybridMachineSig.HybridCoarseMachine.HybridCoarseMachine
      (ThreadPool:= TP h).
  Definition HybConcSem h:=
    HybridMachineSig.ConcurMachineSemantics(HybridMachine:=HybMachine h).
  Notation ThreadPool n :=
    (ThreadPool.t(Sem:= HybridSem n)).


  (** *Extracting index and match relation from CompCert*)
  Context (compiled: 
             CC_correct.CompCert_compiler C_program = Some Asm_program).
  Definition compiler_sim:= CC_correct.simpl_clight_semantic_preservation _ _ compiled.
  Definition compiler_index: Type:= InjindexX compiler_sim.
  Definition compiler_match (i:compiler_index) (j:meminj)
       (c1:  Smallstep.state (Smallstep.part_sem (Clight.semantics2 C_program)))
       (m1: mem)
       (c2: Smallstep.state (Asm.part_semantics Asm_g))
       (m2: mem): Prop
    := Injmatch_statesX compiler_sim i j
                       (Smallstep.set_mem c1 m1)
                       (Smallstep.set_mem c2 m2).

  (* Compiler match that holds under interference of other threads. *)
  Inductive compiler_match_padded:
    compiler_index -> meminj -> Smallstep.state (Smallstep.part_sem (Clight.semantics2 C_program)) ->
    mem -> Smallstep.state (Asm.part_semantics Asm_g) -> mem -> Prop
    :=
    | BuildCompilerMatch: forall cd j1 j2 j3 j s1 m1 s2 m2 s3 m3 s4 m4,
        Clight_match j1 s1 m1 s2 m2 ->
        compiler_match cd j2 s2 m2 s3 m3 ->
        Asm_match j3 s3 m3 s4 m4 ->
        compose_meminj (compose_meminj j1 j2) j3 = j ->
        compiler_match_padded cd j s1 m1 s4 m4.

  (* When the compiling thread is at Kresume the match is different:
     The memories have change according to the synchronization operation
     but the thread state has not resumed (taken the external step, according
     to the CompCert semantics). So, when the state is at Kresume the match
     states that there will be a match, when the states change:
     "When the source thread steps, the target thread will be able to step 
     and reestablish the match"
     This is also padded above and bellow as in compiler_match_padded.
   *)

  (* generalize None to option val and inject it. *)
  Inductive compiler_match_resume:
    compiler_index -> meminj ->
    Smallstep.state (Smallstep.part_sem (Clight.semantics2 C_program)) ->
    mem -> Smallstep.state (Asm.part_semantics Asm_g) -> mem -> Prop
    :=
    | BuildCompilerResumeMatch: forall cd j s2 m2 s3 m3,
        (forall s2', Smallstep.after_external
           (Smallstep.part_sem (Clight.semantics2 C_program))
           None s2 m2 = Some s2' ->
         exists s3',
           (Smallstep.after_external
              (Asm.part_semantics Asm_g)
              None s3 m3 = Some s3') /\
           compiler_match cd j s2' (Smallstep.get_mem s2') s3' (Smallstep.get_mem s3')) ->
        compiler_match_resume  cd j s2 m2 s3 m3.
    
  Inductive compiler_match_resume_padded:
    compiler_index -> meminj -> Smallstep.state (Smallstep.part_sem (Clight.semantics2 C_program)) ->
    mem -> Smallstep.state (Asm.part_semantics Asm_g) -> mem -> Prop
    :=
    | BuildCompilerResumeMatchPadded:
        forall cd j1 j2 j3 j s1 m1 s2 m2 s3 m3 s4 m4,
        Clight_match j1 s1 m1 s2 m2 ->
        compiler_match_resume cd j2 s2 m2 s3 m3 ->
        Asm_match j3 s3 m3 s4 m4 ->
        compose_meminj (compose_meminj j1 j2) j3 = j ->
        compiler_match_resume_padded cd j s1 m1 s4 m4.

  
  Section CompileOneThread.
    Import OrdinalPool.

    Context (hb: nat).
    Definition SemTop: Semantics:= (HybridSem (Some hb)).
    Definition SemBot: Semantics:= (HybridSem (Some (S hb))).
 
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

        (* Call this match_thread *) 
    (*Inductive match_thread_compiled'
              {sem1 sem2: Semantics}
              (state_type1: @semC sem1 -> state_sum (@semC CSem) (@semC AsmSem))
              (state_type2: @semC sem2 -> state_sum (@semC CSem) (@semC AsmSem))
              (match_state : meminj -> @semC sem1 -> mem -> @semC sem2 -> mem -> Prop)
              (match_state_resume : meminj -> @semC sem1 -> mem -> @semC sem2 -> mem -> Prop) :
    meminj ->
    @ctl (@semC SemTop) -> mem ->
    @ctl (@semC SemBot) -> mem -> Prop  :=
  | CThread_Compiled_Running: forall j code1 m1 code2 m2,
      match_state j code1 m1 code2 m2 ->
      match_thread_compiled' state_type1 state_type2 match_state match_state_resume  j (Krun (state_type1 code1)) m1
                            (Krun (state_type2 code2)) m2
  | CThread_Compiled_Blocked: forall j code1 m1 code2 m2,
      match_state j code1 m1 code2 m2 ->
      match_thread_compiled' state_type1 state_type2 match_state  match_state_resume j (Kblocked (state_type1 code1)) m1
                            (Kblocked (state_type2 code2)) m2
  | CThread_Compiled_Resume: forall j code1 m1 code2 m2 v v',
      match_state_resume j code1 m1 code2 m2 ->
      match_thread_compiled' state_type1 state_type2 match_state  match_state_resume j (Kresume (state_type1 code1) v) m1
                            (Kresume (state_type2 code2) v') m2
  | CThread_Compiled_Init: forall j m1 m2 v1 v1' v2 v2',
      Val.inject j v1 v2 ->
      Val.inject j v1' v2' ->
      match_thread_compiled' state_type1 state_type2 match_state  match_state_resume j (Kinit v1 v1') m1
                               (Kinit v1 v1') m2. *)
    
    Definition SST := SState (@semC CSem) (@semC AsmSem).
    Definition TST := TState (@semC CSem) (@semC AsmSem).
    
    Definition match_thread_source:
      meminj -> @ctl (@semC SemTop) -> mem -> @ctl (@semC SemBot) -> mem -> Prop:=
      match_thread SST SST
                               Clight_match.
    Definition match_thread_target:
      meminj -> @ctl (@semC SemTop) -> mem -> @ctl (@semC SemBot) -> mem -> Prop:=
      match_thread TST TST
                   Asm_match.

    Definition loc_readable_cur (m: mem) (b: block) (ofs: Z) : Prop :=
      Mem.perm m b ofs Cur Readable.

    (** *mem_interference with mem_effect *)
    
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
          inversion H0; subst;
            reflexivity.
      - inversion H; subst;
          inversion H0; subst.
        pose proof (mem_effect_forward_determ
                      _ _ _ _
                      H4 H5); subst.
        eapply IHlev; eassumption.
    Qed.

    

    
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
            inject_incr j' j'' -> (*TODO: this needs to be stronger: 
                                 increase in the most strict way.
                                 This should be derivable from 
                                 strict_inject_evolution.
                                *)
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
    
    Definition merge_func {A} (f1 f2:Z -> option A):
      (BinNums.Z -> option A):=
      fun ofs =>
        match f1 ofs with
          None => f2 ofs
        | _ => f1 ofs
        end.
    (* PTree.map: forall A B : Type, (positive -> A -> B) -> PTree.t A -> PTree.t B *)

    Fixpoint build_function_for_a_block
             (mu:meminj) {A} (b: positive) (ls: list (positive * (Z -> option A))):
      Z -> option A:=
      match ls with
      | nil => (fun _ => None)
      | (b0, fb)::ls' =>
        match mu b0 with
        | Some (b1, delt) =>
          if PMap.elt_eq b b1 then
            merge_func (fun p => (fb (p - delt)%Z)) (build_function_for_a_block mu b ls')
          else  (build_function_for_a_block mu b ls')
        | None => (build_function_for_a_block mu b ls') 
        end
      end.
    
    Definition tree_map_inject_over_tree {A B} (t:PTree.t (Z -> option B))(mu:meminj) (map:PTree.t (Z -> option A)):
      PTree.t (Z -> option A):=
      PTree.map (fun b _ => build_function_for_a_block mu b (PTree.elements map)) t.

    Definition tree_map_inject_over_mem {A} m mu map:
      PTree.t (Z -> option A) :=
      tree_map_inject_over_tree (snd (getMaxPerm m)) mu map.
    
    (* apply an injections to the elements of a tree. *)
    Fixpoint apply_injection_elements
             {A}
             (mu:meminj) (ls: list (positive * (Z -> option A)))
      : list (positive * (Z -> option A)) :=
      match ls with
        nil => nil
      | cons (b, ofs_f) ls' =>
        match (mu b) with
        | None => apply_injection_elements mu ls'
        | Some (b',d) =>
          cons
            (b', fun ofs => ofs_f (ofs-d)%Z)
            (apply_injection_elements mu ls')
        end
      end.
    Fixpoint extract_function_for_block
             {A} (b: positive) (ls: list (positive * (Z -> option A)))
      : Z -> option A :=
      match ls with
        nil => fun _ => None
      | cons (b', ofs_f') ls' =>
        if (Pos.eq_dec b b') then
          merge_func ofs_f' (extract_function_for_block b ls')
        else (extract_function_for_block b ls')
      end.

    Fixpoint map_from_list
             {A:Type}
             (mu:meminj) (ls: list (positive * (Z -> option A))):
      PTree.t (Z -> option A) :=
      match ls with
        nil => @PTree.empty (BinNums.Z -> option A)
      | cons (b, ofs_f) ls =>
        let t:= map_from_list mu ls in
        match mu b with
          None => t
        | Some (b',d) =>
          match PTree.get b' t with
            None => PTree.set b' (fun ofs => ofs_f (ofs-d)%Z) t
          | Some f_old =>
            PTree.set b' (merge_func (fun ofs => ofs_f (ofs-d)%Z) f_old) t
          end
        end
      end.

    
    Definition tree_map_inject {A}(mu:meminj) (map:PTree.t (Z -> option A)):
      PTree.t (Z -> option A):=
      map_from_list mu (PTree.elements map).
    Definition virtueThread_inject m (mu:meminj) (virtue:delta_map * delta_map):
      delta_map * delta_map:=
      let (m1,m2):= virtue in
      (tree_map_inject_over_mem m mu m1, tree_map_inject_over_mem m mu m2).
    
    
    (* Second construct the virtueLP:
               the permissions transfered to the Lock pool
     *)
    Definition access_map_injected m (mu:meminj) (map:access_map):
      access_map:=
      (fst map, tree_map_inject_over_mem m mu (snd map)).
    Definition virtueLP_inject m (mu:meminj) (virtue:access_map * access_map):
      access_map * access_map:=
      (access_map_injected m mu (fst virtue), access_map_injected m mu (snd virtue)).

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
    
    Record concur_match (ocd: option compiler_index)
           (j:meminj) (cstate1: ThreadPool (Some hb)) (m1: Mem.mem) (cstate2: ThreadPool(Some (S hb))) (m2: mem):=
      { same_length: num_threads cstate1 = num_threads cstate2
        ; memcompat1: mem_compatible cstate1 m1
        ; memcompat2: mem_compatible cstate2 m2
        ; INJ: Mem.inject j m1 m2
        ; INJ_threads:
            forall i (cnti1: containsThread cstate1 i) (cnti2: containsThread cstate2 i),
              Mem.inject j
                         (restrPermMap (proj1 (memcompat1 i cnti1)))
                         (restrPermMap (proj1 (memcompat2 i cnti2)))
        ; INJ_locks:
            forall i (cnti1: containsThread cstate1 i) (cnti2: containsThread cstate2 i),
              Mem.inject j
                         (restrPermMap (proj2 (memcompat1 i cnti1)))
                         (restrPermMap (proj2 (memcompat2 i cnti2)))
        ; INJ_lock_permissions:
            forall b b' delt rmap,
              j b = Some (b', delt) ->
              forall ofs, lockRes cstate1 (b, intval ofs) = Some rmap ->
                     lockRes cstate2 (b', intval (add ofs (repr delt))) =
                     Some (virtueLP_inject m2 j rmap)
        ; INJ_lock_content:
            forall b ofs rmap,
              lockRes cstate1 (b, ofs) = Some rmap ->
              inject_lock j b ofs m1 m2    
        ; target_invariant: invariant cstate2
        ; mtch_source:
            forall (i:nat),
              (i > hb)%nat ->
              forall (cnti1: containsThread cstate1 i)
                (cnti2: containsThread cstate2 i),
                match_thread_source j
                                    (getThreadC cnti1)
                                    (restrPermMap (proj1 (memcompat1 i cnti1)))
                                    (getThreadC cnti2)
                                    (restrPermMap (proj1 (memcompat2 i cnti2)))
        ; mtch_target:
            forall (i:nat),
              (i < hb)%nat ->
              forall (cnti1: containsThread cstate1 i)
                (cnti2: containsThread cstate2 i),
                match_thread_target  j
                                     (getThreadC cnti1)
                                     (restrPermMap (proj1(memcompat1 i cnti1)))
                                     (getThreadC cnti2)
                                     (restrPermMap (proj1(memcompat2 i cnti2)))
        ; mtch_compiled:
            forall (i:nat),
              (i = hb)%nat ->
              forall (cnti1: containsThread cstate1 i)
                (cnti2: containsThread cstate2 i),
              match_thread_compiled ocd j
                                    (getThreadC cnti1)
                                    (restrPermMap (proj1 (memcompat1 i cnti1)))
                                    (getThreadC cnti2)
                                    (restrPermMap (proj1 (memcompat2 i cnti2))) }.
    Arguments memcompat1 {ocd j cstate1 m1 cstate2 m2}. 
    Arguments memcompat2 {ocd j cstate1 m1 cstate2 m2}.

    
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

    Ltac consolidate_mem_compatible:=
      repeat match goal with
             | [ H1: mem_compatible ?st ?m,
                     H2: mem_compatible ?st ?m |- _ ] =>
               replace H2 with H1 in * by ( apply Axioms.proof_irr); clear H2
             end.

    Ltac clean_cmpt:=
      try forget_memcompat1;
      try forget_memcompat2;
      consolidate_mem_compatible.
    
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

    Lemma mem_compat_restrPermMap:
      forall sem tpool m perms st (permMapLt: permMapLt perms (getMaxPerm m)),
        (mem_compatible(Sem:=sem)(tpool:=tpool) st m) ->
        (mem_compatible st (restrPermMap permMapLt)).
    Proof.
      intros.
      inversion H.
      econstructor.
      - intros; unfold permissions.permMapLt.
        split; intros;
          erewrite getMax_restr; 
          eapply compat_th0.
      - intros; unfold permissions.permMapLt.
        split; intros;
          erewrite getMax_restr; 
          eapply compat_lp0; eauto.
      - intros. eapply restrPermMap_valid; eauto.
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

      (* Move this lemma to where mem_compatible is defined. *)
      
      assert (memcompat3': mem_compatible st1 (restrPermMap permMapLt1)) by
      (eapply mem_compat_restrPermMap; eauto).
      assert (memcompat4': mem_compatible st2 (restrPermMap permMapLt2)) by
          (eapply mem_compat_restrPermMap; eauto).
      eapply Build_concur_match with memcompat3' memcompat4'; eauto.
      - intros; simpl.
        destruct memcompat3';
        destruct memcompat4';
        destruct memcompat3;
        destruct memcompat4; simpl in *.
        
    Admitted.

    

    
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

    Ltac consolidate_containsThread:=
      repeat match goal with
             | [ H: ThreadPool.containsThread _ _ |- _ ] => simpl in H
             end;
      repeat match goal with
             | [ H1: containsThread ?st ?i,
                     H2: containsThread ?st ?i |- _ ] =>
               replace H2 with H1 in * by ( apply Axioms.proof_irr); clear H2
             end.

    Ltac clean_cnt:=
      try forget_contains12;
      try forget_contains21;
      consolidate_containsThread.
    
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
      pose proof (@contains12 _ _ _ _ _ _ H) as CNT12.
      pose proof (@contains21 _ _ _ _ _ _ H) as CNT21.
      inversion H; simpl.
      split; intros H0 ? ? ? ?.
      - destruct (Compare_dec.lt_eq_lt_dec j hb) as [[?|?]|?].  
        + specialize (mtch_target0 j l (CNT21 _ cnti) cnti).
    Admitted.

    Inductive ord_opt {A} (ord: A -> A -> Prop): option A -> option A -> Prop:=
    | Some_ord:
        forall x y, ord x y -> ord_opt ord (Some x) (Some y).
    
    Lemma option_wf:
      forall A (ord: A -> A -> Prop),
        well_founded ord ->
        well_founded (ord_opt ord).
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
    
    (* This lemma is only used when updating non compiled threads *)
    Lemma Concur_update:
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
    Admitted.

    (*This lemma is used when the compiled thread steps*)
    
    Lemma Concur_update_compiled:
      forall (st1 : ThreadPool.t) (m1 m1' : mem) (Htid : ThreadPool.containsThread st1 hb) 
        (st2 : ThreadPool.t) (mu : meminj) (m2 : mem) (cd : option compiler_index),
        concur_match (cd) mu st1 m1 st2 m2 ->
        forall (s' : Clight.state) (j1' : meminj) (cd' : InjindexX compiler_sim)
          (j2' : meminj) (s4' : Asm.state) (j3' : meminj) (m2' : mem)
          (Htid' : containsThread st2 hb)
        (mcompat1: mem_compatible st1 m1)
        (mcompat2: mem_compatible st2 m2),
        semantics.mem_step
          (restrPermMap (proj1 (mcompat1 hb Htid))) m1' ->
        semantics.mem_step
          (restrPermMap (proj1 (mcompat2 hb Htid'))) m2' ->
        invariant st1 ->
        invariant st2 ->
        match_thread_compiled cd (compose_meminj (compose_meminj j1' j2') j3')
                              (Krun (SState Clight.state Asm.state s')) m1'
                              (Krun (TState Clight.state Asm.state s4')) m2' ->
        concur_match (Some cd') (compose_meminj (compose_meminj j1' j2') j3')
                     (updThread Htid (Krun (SState Clight.state Asm.state s'))
                                (getCurPerm m1', snd (getThreadR Htid))) m1'
                     (updThread Htid' (Krun (TState Clight.state Asm.state s4'))
                                (getCurPerm m2', snd (getThreadR Htid'))) m2'.
    Proof.
      (*There is probably a relation missing from m1 m' m2 m2' *)
      (* Probably it's mem_step which is provable from where this lemma is used. *)
    Admitted.

       
    Lemma Concur_update_compiled':
      forall (st1 : ThreadPool.t) (m1 m1' : mem) (Htid : ThreadPool.containsThread st1 hb) 
        (st2 : ThreadPool.t) (mu : meminj) (m2 : mem) (cd : option compiler_index),
        concur_match (cd) mu st1 m1 st2 m2 ->
        forall (s' : Clight.state) (j1' : meminj) (cd' : InjindexX compiler_sim)
          (j2' : meminj) (s4 : Asm.state) (j3' : meminj)
          (Htid' : containsThread st2 hb)
        (mcompat1: mem_compatible st1 m1)
        (mcompat2: mem_compatible st2 m2),
        semantics.mem_step
          (restrPermMap (proj1 (mcompat1 hb Htid))) m1' ->
        invariant st1 ->
        invariant st2 ->
        match_thread_compiled cd (compose_meminj (compose_meminj j1' j2') j3')
                              (Krun (SState Clight.state Asm.state s')) m1'
                              (Krun (TState Clight.state Asm.state s4))
                              (restrPermMap (proj1 (mcompat2 hb Htid'))) ->
        concur_match (Some cd') (compose_meminj (compose_meminj j1' j2') j3')
                     (updThread Htid (Krun (SState Clight.state Asm.state s'))
                                (getCurPerm m1', snd (getThreadR Htid))) m1'
                     st2 m2.
    Proof.
      (*There is probably a relation missing from m1 m' m2 m2' *)
      (* Probably it's mem_step which is provable from where this lemma is used. *)
    Admitted.
    
    Ltac exploit_match:=
      unfold match_thread_target,match_thread_source in *;
      try match goal with
          | [ H: ThreadPool.getThreadC ?i = _ ?c |- _] => simpl in H
          end;
      match goal with
      | [ H: getThreadC ?i = _ ?c,
             H0: context[match_thread] |- _ ] =>
        rewrite H in H0; inversion H0; subst; simpl in *; clear H0
      | [ H: getThreadC ?i = _ ?c,
             H0: context[match_thread_compiled] |- _ ] =>
        rewrite H in H0; inversion H0; subst; simpl in *; clear H0
      end;
      fold match_thread_target in *;
      fold match_thread_source in *.

    (* Build the concur_match *)
    Ltac destroy_ev_step_sum:=
      match goal with
      | [ H: ev_step_sum _ _ _ _ _ _ _ |- _ ] => inversion H; clear H
      end.

    Lemma self_simulation_plus:
      forall state coresem
        (SIM: self_simulation.self_simulation state coresem),
      forall (f : meminj) (t : Events.trace) (c1 : state) 
        (m1 : mem) (c2 : state) (m2 : mem),
        self_simulation.match_self (self_simulation.code_inject _ _ SIM) f c1 m1 c2 m2 ->
        forall (c1' : state) (m1' : mem),
          (corestep_plus coresem) c1 m1 c1' m1' ->
          exists (c2' : state) (f' : meminj) (t' : Events.trace) 
            (m2' : mem),
                (corestep_plus coresem) c2 m2 c2' m2' /\
                self_simulation.match_self (self_simulation.code_inject _ _ SIM) f' c1' m1' c2' m2' /\
                inject_incr f f' /\
                self_simulation.is_ext f (Mem.nextblock m1) f' (Mem.nextblock m2) /\
                Events.inject_trace f' t t'.
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
                  machine_semantics_lemmas.thread_step_plus (HybConcSem (Some (S hb)) m) tge U st2
                                                            m2
                                                            (updThread Htid' (Krun (TState Clight.state Asm.state s4'))
                                                                       (getCurPerm m4', snd (getThreadR Htid'))) m4'.
            Proof.
              (** NOTE: This might be missing that the corestep never reaches an at_external
                  If this is the case, we might need to thread that through the compiler...
                  although it should be easy, I would prefere if there is any other way...
              *)
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

    Lemma Forall2_impl: forall {A B} (P Q : A -> B -> Prop) l1 l2,
      (forall a b, P a b -> Q a b) -> List.Forall2 P l1 l2 -> List.Forall2 Q l1 l2.
    Proof.
      induction 2; constructor; auto.
    Qed.

    
    Lemma inject_incr_trace:
      forall (tr1 tr2 : list Events.machine_event) (mu f' : meminj),
        inject_incr mu f' ->
        List.Forall2 (inject_mevent mu) tr1 tr2 ->
        List.Forall2 (inject_mevent f') tr1 tr2.
    Proof.
      intros. eapply Forall2_impl; try eassumption.
      - intros. admit.
    Admitted.
    
    (* When a thread takes an internal step (i.e. not changing the schedule) *)
    Lemma internal_step_diagram:
      forall (m : option mem) (sge tge : HybridMachineSig.G) (U : list nat)
        tr1 (st1 : ThreadPool (Some hb)) (m1 : mem) (st1' : ThreadPool (Some hb)) 
        (m1' : mem),
        machine_semantics.thread_step (HybConcSem (Some hb) m) sge U st1 m1 st1' m1' ->
        forall (cd : option compiler_index) tr2 (st2 : ThreadPool (Some (S hb))) 
          (mu : meminj) (m2 : mem),
          concur_match cd mu st1 m1 st2 m2 ->
          forall (Hmatch_event : List.Forall2 (inject_mevent mu) tr1 tr2),
          exists
            (st2' : ThreadPool (Some (S hb))) (m2' : mem) (cd' : option compiler_index) 
            (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            List.Forall2 (inject_mevent mu') tr1 tr2 /\
            (machine_semantics_lemmas.thread_step_plus
               (HybConcSem (Some (S hb)) m) tge U st2 m2
               st2' m2' \/
             machine_semantics_lemmas.thread_step_star
               (HybConcSem (Some (S hb)) m) tge U st2 m2
               st2' m2' /\ ord_opt (InjorderX compiler_sim) cd' cd).
    Proof.
      intros.
      inversion H; subst.
      inversion Htstep; subst.
      destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].  
      - (* tid < hb *)
        pose proof (mtch_target _ _ _ _ _ _ H0 _ l Htid (contains12 H0 Htid)) as HH.
        simpl in *.
        exploit_match.

        destroy_ev_step_sum; subst; simpl in *.
        simpl.
        eapply Asm_event.asm_ev_ax1 in H2.
        clean_cmpt.
        instantiate (1:=Asm_genv_safe) in H2.
        
        eapply Aself_simulation in H5; eauto.
        destruct H5 as (c2' & f' & t' & m2' & (CoreStep & MATCH & Hincr & is_ext & inj_trace)).

        eapply Asm_event.asm_ev_ax2 in CoreStep; try eapply Asm_genv_safe.
        destruct CoreStep as (?&?); eauto.
         
        (* contains.*)
        pose proof (@contains12  _ _ _ _ _ _  H0 _ Htid) as Htid'.

        (* Construct the new thread pool *)
        exists (updThread Htid' (Krun (TState Clight.state Asm.state c2'))
           (getCurPerm m2', snd (getThreadR Htid'))).
        (* new memory is given by the self_simulation. *)
        exists m2', cd, f'. split; [|split; [|left]].
        
        + (*Reestablish the concur_match *)
          simpl.
          move H0 at bottom.
          
          eapply Concur_update; eauto.
          { eapply semantics.corestep_mem in H2.
            eapply H2. }
          { eapply Asm_event.asm_ev_ax1 in H1.
            
            eapply semantics.corestep_mem.
            clean_cnt.
            eassumption.
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
          * simpl. econstructor; eauto.
          * simpl; repeat (f_equal; try eapply Axioms.proof_irr).

         
            
      - (*  tid = hb*)
        pose proof (mtch_compiled _ _ _ _ _ _ H0 _ e Htid (contains12 H0 Htid)) as HH.
        subst.
        simpl in *. exploit_match.

        
        (* This takes three steps:
           - Simulation of the Clight semantics  
           - Simulation of the compiler (Clight and Asm) 
           - Simulation of the Asm semantics 
         *)

        rename H6 into Compiler_Match.
        simpl in *.

        
        (* (1) Clight step *)
        destroy_ev_step_sum. subst m'0 t0 s.
        eapply (event_semantics.ev_step_ax1 (@semSem CSem)) in H2; eauto.
        (* assert (original_CoreStep:=H3).
        replace Hcmpt with (memcompat1 H0) in H3
          by eapply Axioms.proof_irr.
        
        eapply Cself_simulation in H3; eauto.
        destruct H3 as (c2' & j1' & t' & m2' & (CoreStep & MATCH & Hincr & His_ext & Htrace)).  *)
        
        (* (2) Compiler step/s *)
        rename H2 into CoreStep.
        inversion CoreStep. subst s1 m0 s2.
        clean_cmpt.
        eapply compiler_sim in H1; simpl in *; eauto.
        destruct H1 as (cd' & s2' & j2' & t'' & step & comp_match & Hincr2 & inj_event).

        eapply simulation_equivlanence in step.
        assert ( HH: Asm.state =
                     Smallstep.state (Asm.part_semantics Asm_g)) by
            reflexivity.
        remember (@Smallstep.get_mem (Asm.part_semantics Asm_g) s2') as m2'.
        pose proof (@contains12  _ _ _ _ _ _  H0 _ Htid) as Htid'.

        destruct step as [plus_step | (? & ? & ?)].
        +
          
          exists (updThread Htid' (Krun (TState Clight.state Asm.state s2'))
                     (getCurPerm m2', snd (getThreadR Htid'))), m2', (Some i), mu.
          split; [|split].
          * assert (CMatch := H0). inversion H0; subst.
            admit. (*reestablish concur*)
          * eapply inject_incr_trace; try eassumption.
            apply inject_incr_refl.
          * left.
            eapply thread_step_plus_from_corestep; eauto.
            clear - plus_step.
            eapply step2corestep_plus in plus_step; eauto; simpl.
            subst m2'.
            instantiate(1:=Htid).
            instantiate(21:=code2).
            instantiate (5:=H0).
            clean_cmpt; clean_cnt; eauto.

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
        exploit_match.
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
        pose proof (@contains12  _ _ _ _ _ _  H0 _ Htid) as Htid'.

        (* Construct the new thread pool *)
        exists (updThread Htid' (Krun (SState Clight.state Asm.state c2'))
           (getCurPerm m2', snd (getThreadR Htid'))).
        (* new memory is given by the self_simulation. *)
        exists m2', cd, f'. split; [|split; [|left]].
        
        + (*Reestablish the concur_match *)
          simpl.
          move H0 at bottom.
          eapply Concur_update; eauto.
          { eapply semantics.corestep_mem in H2.
            eapply H2. }
          { eapply (event_semantics.ev_step_ax1 (@semSem CSem)) in H1.
            eapply semantics.corestep_mem in H1.
            clean_cnt.
            eauto.
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
          * simpl. econstructor; eauto.
          * simpl; repeat (f_equal; try eapply Axioms.proof_irr).



            Unshelve. all: auto.
            (*This shouldn't be her e*) 
            all: exact nil.
    Admitted. (* TODO: ther e is only one admit: reestablish the match*)


    (** *Diagrams for machine steps*)

    Lemma acquire_step_diagram:
          forall (cd : option compiler_index) (m1 : mem) (st1 : ThreadPool (Some hb)) (st2 : ThreadPool.t) (mu : meminj) (m2 : mem)
            (tr1 tr2 : HybridMachineSig.event_trace)
            (Hmatch : concur_match cd mu st1 m1 st2 m2) (Htr : List.Forall2 (inject_mevent mu) tr1 tr2)
            (U : list nat)
            (m1' : mem) (tid : nat)
            (Htid : ThreadPool.containsThread st1 tid) (Hpeek : HybridMachineSig.schedPeek U = Some tid) (c : semC) (b : block)
            (ofs : Integers.Ptrofs.int) (virtueThread : delta_map * delta_map)
            (newThreadPerm : access_map * access_map) (pmap : lock_info)
            (Hcmpt: mem_compatible st1 m1)
          (Hlt': permMapLt
           (setPermBlock (Some Writable) b (Integers.Ptrofs.intval ofs)
              (snd (ThreadPool.getThreadR Htid)) LKSIZE_nat) (getMaxPerm m1))
          (Hbounded : bounded_maps.sub_map (fst virtueThread) (snd (getMaxPerm m1)) /\
             bounded_maps.sub_map (snd virtueThread) (snd (getMaxPerm m1)))
          (Hinv : invariant st1),
            semantics.at_external (semantics.csem (event_semantics.msem semSem))
                   c (restrPermMap (fst (ssrfun.pair_of_and (Hcmpt tid Htid)))) =
                 Some (LOCK, (Vptr b ofs :: nil)%list) ->
            getThreadC Htid = Kblocked c ->
            Mem.load AST.Mint32 (restrPermMap (snd (ssrfun.pair_of_and (Hcmpt tid Htid)))) b
                     (Integers.Ptrofs.intval ofs) = Some (Vint Integers.Int.one) ->
             Mem.range_perm (restrPermMap (snd (ssrfun.pair_of_and (Hcmpt tid Htid)))) b
              (Integers.Ptrofs.intval ofs) (BinInt.Z.add (Integers.Ptrofs.intval ofs) LKSIZE)
              Cur Readable ->
             Mem.store AST.Mint32 (restrPermMap Hlt') b (Integers.Ptrofs.intval ofs)
             (Vint Integers.Int.zero) = Some m1' ->
            ThreadPool.lockRes st1 (b, Integers.Ptrofs.intval ofs) = Some pmap ->
            permMapJoin (fst pmap) (fst (ThreadPool.getThreadR Htid)) (fst newThreadPerm) ->
            permMapJoin (snd pmap) (snd (ThreadPool.getThreadR Htid)) (snd newThreadPerm) ->
            exists e' (st2' : ThreadPool.t) (m2' : mem) (cd' : option compiler_index) (mu' : meminj),
              concur_match cd' mu'
                           (ThreadPool.updLockSet (ThreadPool.updThread Htid (Kresume c Vundef) newThreadPerm)
                                                  (b, Integers.Ptrofs.intval ofs) (empty_map, empty_map)) m1' st2' m2' /\
              List.Forall2 (inject_mevent mu')
                           (seq.cat tr1
                                    (Events.external tid
                                                     (Events.acquire
                                                        (b, Integers.Ptrofs.intval ofs)
                                                     (Some (build_delta_content (fst virtueThread) m1'))) :: nil))
                                               (seq.cat tr2 (Events.external tid e' :: nil)) /\
              HybridMachineSig.external_step(scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
                                            U tr2 st2 m2 (HybridMachineSig.schedSkip U)
                                            (seq.cat tr2
                                                     (Events.external tid e' :: nil)) st2'
                                            m2'.
    Proof.

      intros.

      (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
      destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].

      (* tid < hb *)
      -



                                       
        pose proof (mtch_target _ _ _ _ _ _ Hmatch _ l Htid (contains12 Hmatch Htid)) as match_thread.
        exploit_match.
        inversion H11; clear H11.
        inversion matchmem.
    (*            2: {
                  econstructor; auto.
              econstructor; auto.
              * simpl.
              Check Hbounded.
              simpl.
        (* contains.*)
        pose proof (@contains12  _ _ _ _ _ _  H0 _ Htid) as Htid'.

        (* Construct the new thread pool *)
        exists (updThread Htid' (Krun (TState Clight.state Asm.state c2'))
           (getCurPerm m2', snd (getThreadR Htid'))).
        (* new memory is given by the self_simulation. *)
        exists m2', cd, f'. split; [|left].
        
        + (*Reestablish the concur_match *)
          simpl.
          move H0 at bottom.
          
          eapply Concur_update; eauto.
          { eapply semantics.corestep_mem in H2.
            eapply H2. }
          { eapply Asm_event.asm_ev_ax1 in H1.

            replace Htid' with (contains12 H0 Htid) by apply Axioms.proof_irr.
            eapply semantics.corestep_mem.
            eassumption.
          }
          { apply H0. }

          (*The compiler match*)
          econstructor 2; eauto.
          simpl in MATCH.
          unfold match_thread_target; simpl.
          constructor.
          exact MATCH.
        + (* Construct the step *)
          exists 0; simpl.
          do 2 eexists; split; [|reflexivity].
          replace m2' with (HybridMachineSig.diluteMem m2') by reflexivity.
          econstructor; eauto; simpl.
          econstructor; eauto.
          * simpl in *.
            eapply H0.
          * simpl. econstructor; eauto.
          * simpl; repeat (f_equal; try eapply Axioms.proof_irr).

            *)

        Admitted.


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
        
        Lemma release_step_diagram:
          forall (U : list nat) (tr1 tr2 : HybridMachineSig.event_trace)
            (st1 : ThreadPool (Some hb)) (m1 m1' : mem) 
            (tid : nat) (cd : option compiler_index)
            (st2 : ThreadPool (Some (S hb))) (mu : meminj) 
            (m2 : mem) (Htid : ThreadPool.containsThread st1 tid)
            (c : semC) (b : block) (ofs : Integers.Ptrofs.int)
            (virtueThread : PTree.t
                              (BinNums.Z -> option (option permission)) *
                            PTree.t
                              (BinNums.Z -> option (option permission)))
            (virtueLP : PMap.t (BinNums.Z -> option permission) *
                        PMap.t (BinNums.Z -> option permission))
            (rmap : lock_info) (newThreadPerm : access_map * access_map)
            (HSched: HybridMachineSig.schedPeek U = Some tid)
            (Hcmpt : mem_compatible st1 m1)
            (CMatch:concur_match cd mu st1 m1 st2 m2)
            (HTraceInj: List.Forall2 (inject_mevent mu) tr1 tr2)
            (Hlt' : permMapLt
                         (setPermBlock (Some Writable) b
                                       (Integers.Ptrofs.intval ofs)
                                       (snd (getThreadR Htid)) LKSIZE_nat)
                         (getMaxPerm m1))
            (Hbounded: bounded_maps.sub_map (fst virtueThread) (snd (getMaxPerm m1)) /\
                       bounded_maps.sub_map (snd virtueThread) (snd (getMaxPerm m1)))
            (HboundedLP: bounded_maps.map_empty_def (fst virtueLP) /\
                         bounded_maps.map_empty_def (snd virtueLP) /\
                         bounded_maps.sub_map (snd (fst virtueLP)) (snd (getMaxPerm m1)) /\
                         bounded_maps.sub_map (snd (snd virtueLP)) (snd (getMaxPerm m1)))
            (Hinv: invariant st1)
            (Hcode: ThreadPool.getThreadC Htid = Kblocked c)
            (Hat_external: semantics.at_external
                             (semantics.csem (event_semantics.msem semSem)) c
                             (restrPermMap (fst (ssrfun.pair_of_and (Hcmpt tid Htid)))) =
                           Some (UNLOCK, (Vptr b ofs :: nil)%list))
            (Hload: Mem.load AST.Mint32
                             (restrPermMap (snd (ssrfun.pair_of_and (Hcmpt tid Htid)))) b
                             (Integers.Ptrofs.intval ofs) = Some (Vint Integers.Int.zero))
            (Haccess: Mem.range_perm
                        (restrPermMap (snd (ssrfun.pair_of_and (Hcmpt tid Htid)))) b
                        (Integers.Ptrofs.intval ofs)
                        (BinInt.Z.add (Integers.Ptrofs.intval ofs) LKSIZE) Cur Readable)
            (Hstore: Mem.store AST.Mint32 (restrPermMap Hlt') b
                               (Integers.Ptrofs.intval ofs) (Vint Integers.Int.one) = 
                     Some m1')
            (HisLock: ThreadPool.lockRes st1 (b, Integers.Ptrofs.intval ofs) =
                      Some rmap)
            (Hrmap: (forall (b0 : BinNums.positive) (ofs0 : BinNums.Z),
                        (fst rmap) !! b0 ofs0 = None /\ (snd rmap) !! b0 ofs0 = None))
            (Hangel1: permMapJoin (fst newThreadPerm) (fst virtueLP)
                                  (fst (getThreadR Htid)))
            (Hangel2: permMapJoin (snd newThreadPerm) (snd virtueLP)
                                  (snd (getThreadR Htid))),
          exists
            e' (st2' : t) (m2' : mem) (cd' : option compiler_index) 
            (mu' : meminj),
            concur_match cd' mu'
                         (ThreadPool.updLockSet
                            (ThreadPool.updThread Htid (Kresume c Vundef)
                                                  (computeMap (fst (getThreadR Htid))
                                                              (fst virtueThread),
                                                   computeMap (snd (getThreadR Htid))
                                                              (snd virtueThread))) (b, Integers.Ptrofs.intval ofs)
                            virtueLP) m1' st2' m2' /\
            List.Forall2 (inject_mevent mu') (seq.cat tr1 (Events.external tid (Events.release (b, Integers.Ptrofs.intval ofs) (Some (build_delta_content (fst virtueThread) m1'))) :: nil))
                         (seq.cat tr2 (Events.external tid e' :: nil)) /\
            HybridMachineSig.external_step
              (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
              U tr2 st2 m2 (HybridMachineSig.schedSkip U)
              (seq.cat tr2
                       (Events.external tid e' :: nil)) st2' m2'.
        Proof.
          intros.

          (* destruct {tid < hb} + {tid = hb} + {hb < tid}  *)
          destruct (Compare_dec.lt_eq_lt_dec tid hb) as [[?|?]|?].

          (** * tid < hb *)
          -

            (** * Lemmas for relase diagram*)
            Definition access_map_inject (f:meminj) (pmap1 pmap2: access_map):=
            forall (b1 b2 : block) (delt ofs: Z),
              f b1 = Some (b2, delt) ->
              Mem.perm_order'' (pmap2 !! b2 (ofs+delt)%Z) (pmap1 !! b1 ofs).
            Lemma access_map_injected_extentional1:
              forall f pm1 pm1' pm2,
                access_map_inject f pm1 pm2 ->
            (forall b, pm1 !! b = pm1' !! b) ->
            access_map_inject f pm1' pm2.
            Proof.
              intros. intros ????. rewrite <- H0. auto. Qed.
            Lemma access_map_injected_extentional2:
              forall f pm1 pm2 pm2',
                access_map_inject f pm1 pm2 ->
            (forall b , pm2 !! b = pm2' !! b) ->
            access_map_inject f pm1 pm2'.
            Proof.
              intros. intros ????. rewrite <- H0. auto. Qed.
            Lemma access_map_injected_getMaxPerm:
              forall f m1 m2,
                Mem.inject f m1 m2 ->
                access_map_inject f (getMaxPerm m1) (getMaxPerm m2).
              intros. intros ?????.
              do 2 rewrite getMaxPerm_correct.
              destruct (permission_at m1 b1 ofs Max) eqn:HH.
              - rewrite <- mem_lemmas.po_oo.
                eapply Mem.mi_perm; eauto.
                + apply H.
                + unfold Mem.perm.
                  unfold permission_at in HH;
                    rewrite HH.
                  simpl.
                  apply perm_refl.
              - apply event_semantics.po_None.
            Qed.
            Lemma access_map_injected_getCurPerm:
              forall f m1 m2,
                Mem.inject f m1 m2 ->
                access_map_inject f (getCurPerm m1) (getCurPerm m2).
              intros. intros ?????.
              do 2 rewrite getCurPerm_correct.
              destruct (permission_at m1 b1 ofs Cur) eqn:HH.
              - rewrite <- mem_lemmas.po_oo.
                eapply Mem.mi_perm; eauto.
                + apply H.
                + unfold Mem.perm.
                  unfold permission_at in HH;
                    rewrite HH.
                  simpl.
                  apply perm_refl.
              - apply event_semantics.po_None.
            Qed.
            
            Lemma setPermBlock_inject_permMapLt:
              forall n (NZ: (0 < n)%nat)
                (m1 m2 : mem) 
                (mu : meminj) cur_perm1 cur_perm2 max_perm1 max_perm2
                (b : block) (ofs : ptrofs) P,
                permMapLt
                  (setPermBlock P b (intval ofs) cur_perm1 n)
                  max_perm1 ->
                Mem.inject mu m1 m2 ->
                access_map_inject mu max_perm1 max_perm2 -> 
                forall (b' : block) (delt : Z),
                  mu b = Some (b', delt) ->
                  permMapLt cur_perm2 max_perm2 ->
                  permMapLt
                    (setPermBlock P b' (intval ofs + delt)
                                  cur_perm2 n) max_perm2.
            Proof.
              intros; intros b0 ofs0.
              destruct (Clight_lemmas.block_eq_dec b' b0);
                [destruct (Intv.In_dec ofs0 ((intval ofs + delt)%Z, (intval ofs + delt + (Z.of_nat n))%Z))|
                ].
              - subst. unfold Intv.In in i; simpl in *.
                rewrite setPermBlock_same; auto.
                replace ofs0 with ((ofs0 - delt) + delt)%Z by omega.
                eapply juicy_mem.perm_order''_trans.

                2:{ unfold permMapLt in H.
                    specialize (H b (ofs0 - delt)%Z).
                    rewrite setPermBlock_same in H; auto; try omega.
                    eauto. }
                
                + eapply H1; auto.
              - subst.
                rewrite setPermBlock_other_1; eauto.
                eapply Intv.range_notin in n0; auto; simpl.
                eapply inj_lt in NZ. rewrite Nat2Z.inj_0 in NZ.
                omega.
              - subst.
                rewrite setPermBlock_other_2; eauto.
            Qed.
            Lemma setPermBlock_inject_permMapLt':
              forall {Sem1 Sem2} (n:nat) (NZ: (0 < n)%nat) 
                (st1 : t(resources:=dryResources)(Sem:=Sem1)) (m1 : mem) (tid : nat) 
                (st2 : t(resources:=dryResources)(Sem:=Sem2)) (mu : meminj) (m2 : mem) (Htid1 : containsThread st1 tid)
                (b : block) (ofs : ptrofs),
                permMapLt
                  (setPermBlock (Some Writable) b (intval ofs) (snd (getThreadR Htid1)) n)
                  (getMaxPerm m1) ->
                Mem.inject mu m1 m2 ->
                forall (b' : block) (delt : Z),
                  mu b = Some (b', delt) ->
                  forall Htid2 : containsThread st2 tid,
                    permMapLt (snd (getThreadR Htid2)) (getMaxPerm m2) ->
                    permMapLt
                      (setPermBlock (Some Writable) b' (intval ofs + delt)
                                    (snd (getThreadR Htid2)) n) (getMaxPerm m2).
            Proof.
              intros; intros b0 ofs0. 
              destruct (Clight_lemmas.block_eq_dec b' b0);
                [destruct (Intv.In_dec ofs0 ((intval ofs + delt)%Z, (intval ofs + delt + (Z.of_nat n))%Z))|
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
                forall {Sem1 Sem2}
                  (st1 : ThreadPool.t(resources:=dryResources)(Sem:=Sem1))
                  (m1 : mem) (tid : nat)
                  (st2 : ThreadPool.t(resources:=dryResources)(Sem:=Sem2))
                  (mu : meminj) (m2 : mem)
                  (Htid1 : ThreadPool.containsThread st1 tid)
                  (Htid2 : ThreadPool.containsThread st2 tid)
                  {A} (virtue1 : PTree.t (Z -> option A))
                  (Hcmpt1: mem_compatible st1 m1)(Hcmpt2: mem_compatible st2 m2),
                  Mem.inject mu (restrPermMap (proj1 (Hcmpt1 tid Htid1)))
                             (restrPermMap (proj1 (Hcmpt2 tid Htid2))) ->
                  bounded_maps.sub_map virtue1 (snd (getMaxPerm m1)) ->
                  bounded_maps.sub_map (tree_map_inject_over_mem m2 mu virtue1) (snd (getMaxPerm m2)).
              Proof.
                intros ?? st1 m1 tid st2 mu m2 Htid1 Htid2
                       AT virtue1 Hcmpt1 Hcmpt2 injmem A.

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
                     eapply Mem.mi_perm in Hinj; try apply injmem.
                     
                     
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

              (** * End of Lemmas for relase diagram*)

              
              (* The release diagram where only a compiled thread is stepping *)
              Lemma release_step_diagram_target:
                forall (U : list nat) (tr1 tr2 : HybridMachineSig.event_trace)
                  (st1 : ThreadPool (Some hb)) (m1 m1' : mem) 
                  (tid : nat) (cd : option compiler_index)
                  (st2 : ThreadPool (Some (S hb))) (mu : meminj) 
                  (m2 : mem)
                  (Htid1 : ThreadPool.containsThread st1 tid)
                  (Htid2 : ThreadPool.containsThread st2 tid)
                  (code1: Asm.state) (b : block) (ofs : Integers.Ptrofs.int)
                  (virtueThread : PTree.t
                                    (BinNums.Z -> option (option permission)) *
                                  PTree.t
                                    (BinNums.Z -> option (option permission)))
                  (virtueLP : PMap.t (BinNums.Z -> option permission) *
                              PMap.t (BinNums.Z -> option permission))
                  (rmap : lock_info) (newThreadPerm : access_map * access_map)
                  (HSched: HybridMachineSig.schedPeek U = Some tid)
                  (Hcmpt1 : mem_compatible st1 m1)
                  (CMatch:concur_match cd mu st1 m1 st2 m2)
                  (target_inv: invariant st2)
                  (HTraceInj: List.Forall2 (inject_mevent mu) tr1 tr2)
                  (Hlt1 : permMapLt
                            (setPermBlock (Some Writable) b
                                          (Integers.Ptrofs.intval ofs)
                                          (snd (ThreadPool.getThreadR Htid1)) LKSIZE_nat)
                            (getMaxPerm m1))
                  (Hbounded: bounded_maps.sub_map (fst virtueThread) (snd (getMaxPerm m1)) /\
                             bounded_maps.sub_map (snd virtueThread) (snd (getMaxPerm m1)))
                  (HboundedLP: bounded_maps.map_empty_def (fst virtueLP) /\
                               bounded_maps.map_empty_def (snd virtueLP) /\
                               bounded_maps.sub_map (snd (fst virtueLP)) (snd (getMaxPerm m1)) /\
                               bounded_maps.sub_map (snd (snd virtueLP)) (snd (getMaxPerm m1)))
                  (Hinv: invariant st1)
                  (Hcode: ThreadPool.getThreadC Htid1 = Kblocked (TST code1))
                  (Hat_external: semantics.at_external
                                   (semantics.csem (event_semantics.msem (@semSem AsmSem) )) (code1)
                                   (restrPermMap (fst (ssrfun.pair_of_and (Hcmpt1 tid Htid1)))) =
                                 Some (UNLOCK, (Vptr b ofs :: nil)%list))
                  (Hload: Mem.load AST.Mint32
                                   (restrPermMap (snd (ssrfun.pair_of_and (Hcmpt1 tid Htid1)))) b
                                   (Integers.Ptrofs.intval ofs) = Some (Vint Integers.Int.zero))
                  (Haccess: Mem.range_perm
                              (restrPermMap (snd (ssrfun.pair_of_and (Hcmpt1 tid Htid1)))) b
                              (Integers.Ptrofs.intval ofs)
                              (BinInt.Z.add (Integers.Ptrofs.intval ofs) LKSIZE) Cur Readable)
                  (Hstore: Mem.store AST.Mint32 (restrPermMap Hlt1) b
                                     (Integers.Ptrofs.intval ofs) (Vint Integers.Int.one) = 
                           Some m1')
                  (HisLock: ThreadPool.lockRes st1 (b, Integers.Ptrofs.intval ofs) =
                            Some rmap)
                  (Hrmap: (forall (b0 : BinNums.positive) (ofs0 : BinNums.Z),
                              (fst rmap) !! b0 ofs0 = None /\ (snd rmap) !! b0 ofs0 = None))
                  (Hangel1: permMapJoin (fst newThreadPerm) (fst virtueLP)
                                        (fst (ThreadPool.getThreadR Htid1)))
                  (Hangel2: permMapJoin (snd newThreadPerm) (snd virtueLP)
                                        (snd (ThreadPool.getThreadR Htid1)))
                  code2 (Hcmpt2: mem_compatible st2 m2)
                  (Amatch : Asm_match mu code1
                                      (restrPermMap (proj1 (Hcmpt1 tid Htid1)))
                                      code2
                                      (restrPermMap
                                         (proj1
                                            (Hcmpt2 tid (Htid2)))) )
                  (getCode2 : Kblocked (TST code2) = ThreadPool.getThreadC Htid2)
                  (Hinj_lock: 
                     Mem.inject mu (restrPermMap (proj2 (Hcmpt1 tid Htid1)))
                                (restrPermMap (proj2 (Hcmpt2 tid Htid2))))
                  b' delt (Hinj_b : mu b = Some (b', delt)),
                  let code1' := (Kresume (TST code1) Vundef) in
                  exists e' (m2' : mem) Htid2
                    (mu' : meminj),
                    Asm_code_inject mu code1 code2 /\
                    self_simulation.match_mem mu (restrPermMap (proj1 (Hcmpt1 tid Htid1)))
                                              (restrPermMap (proj1 (Hcmpt2 tid Htid2)))
                    /\
                    List.Forall2 (inject_mevent mu')
                                 (seq.cat tr1 (Events.external tid (Events.release (b, Integers.Ptrofs.intval ofs) (Some (build_delta_content (fst virtueThread) m1'))) :: nil))
                                 (seq.cat tr2 (Events.external tid e' :: nil)) /\
                    let virtueThread2:= (virtueThread_inject m2 mu virtueThread)  in
                    let virtueLP2:= virtueLP_inject m2 mu virtueLP  in
                    let st2':=
                        (ThreadPool.updLockSet
                           (ThreadPool.updThread
                              (tp:=st2)
                              (tid:=tid)
                              (Sem:=HybridSem (Some (S hb)))
                              (resources:=dryResources)
                              Htid2 (Kresume (TST code2) Vundef)
                              (computeMap (fst (ThreadPool.getThreadR Htid2)) (fst virtueThread2),
                               computeMap (snd (ThreadPool.getThreadR Htid2)) (snd virtueThread2))) 
                           (b', intval (add ofs (repr delt))) virtueLP2) in 
                    HybridMachineSig.external_step
                      (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
                      U tr2 st2 m2 (HybridMachineSig.schedSkip U)
                      (seq.cat tr2
                               (Events.external tid e' :: nil)) st2' m2'.
              Proof.
                intros.

                
                
                
                inversion Amatch; clear Amatch.
                remember (virtueThread_inject m2 mu virtueThread)  as virtueThread2.
                remember (virtueLP_inject m2 mu virtueLP) as virtueLP2.
                
                assert (Hstore': exists (Hlt2': permMapLt
                                             (setPermBlock (Some Writable) b' (intval ofs + delt)
                                                           (snd (getThreadR Htid2)) LKSIZE_nat) (getMaxPerm m2)),
                           exists n2, Mem.store AST.Mint32 (restrPermMap Hlt2') b' 
                                           (intval ofs + delt) (Vint Int.one) = Some n2 /\ 
                                 Mem.inject mu m1' n2).
                {
                  
                  (** *Constructing the target objects: events, thread_pool, mem, meminj and index*)

                  (** *virtueThread*)
                  (*First construct the virtueThread:
                the permissions passed from the thread to the lock. *)

                  (* Construct the memory with permissions to write in the lock*)
                  assert (Hlt2':
                            permMapLt
                              (setPermBlock (Some Writable) b' (intval ofs + delt)%Z
                                            (snd (getThreadR Htid2)) LKSIZE_nat) (getMaxPerm m2)).
                  {
                    eapply setPermBlock_inject_permMapLt; simpl in *; eauto.
                    - eapply access_map_injected_extentional1; try eapply getMax_restr.
                      eapply access_map_injected_extentional2; try eapply getMax_restr.
                      eapply access_map_injected_getMaxPerm; eassumption.
                    - eapply Hcmpt2; eauto.
                  }
                  exists Hlt2'.
                  
                  (* Construct new memory and new injection *)
                  eapply Mem.store_mapped_inject in Hstore; eauto.
                  { 

                    (* Lemmas start here *)

                    
                    (* This lemma *)
                    Lemma setPermBlock_range_perm:
                      forall (m1 : mem) (b : block) (ofs : Z) (n : nat)
                        perm perm_map,
                        permMapLt
                          (setPermBlock (Some perm) b ofs
                                        perm_map n) (getMaxPerm m1) ->
                        Mem.range_perm m1 b ofs (ofs + Z.of_nat n) Max
                                       perm.
                    Proof.
                      intros m1 b ofs n perm perm_map H0.
                      intros ? ?.
                      specialize (H0 b ofs0).
                      rewrite setPermBlock_same in H0; auto.
                      unfold Mem.perm.
                      rewrite mem_lemmas.po_oo.
                      rewrite_getPerm; auto.
                    Qed.
                    
                    Lemma range_no_overlap:
                      forall (mu : meminj) (m1 : mem) (b1 b1' b2 b2': block)
                        (ofs delt delta ofs0 : Z) (n : nat),
                        Mem.meminj_no_overlap mu m1 ->
                        mu b1 = Some (b1', delt) ->
                        mu b2 = Some (b2', delta) ->
                        b1 <> b2 ->
                        Mem.perm m1 b1 ofs0 Max Nonempty ->
                        Mem.range_perm m1 b2 ofs (ofs + Z.of_nat n) Max Nonempty ->
                        b1' <> b2' \/ b1' = b2' /\
                        ~ Intv.In (ofs0 + delt)
                          ((ofs + delta)%Z, (ofs + delta + Z.of_nat n)%Z).
                    Proof.
                      intros ??????????? Hno_overlap Hinj1
                             Hinj2 Hneq Hperm1 Hrange_perm2.
                      
                      (* The key is to do an induction over the length of the range
                       *)
                      assert(H: forall m, (m <= n)%nat -> b1' <> b2' \/
                                             (~ Intv.In (ofs0 + delt)
                                                (ofs + delta, ofs + delta + Z.of_nat m))%Z).
                      { induction m.
                        - intros ?. simpl; right.
                          unfold Intv.In; simpl. clear.
                          intros ?; omega.
                        -  intros ?.
                           specialize (Hno_overlap
                                         _ _ _ _ _ _
                                         ofs0 (ofs+Z.of_nat m)%Z
                                         Hneq Hinj1 Hinj2).
                           apply Hno_overlap in Hperm1.
                           2: { eapply Hrange_perm2. omega. }
                           destruct Hperm1 as [Hperm1|Hperm1]; auto.
                           specialize (IHm ltac:(omega)).
                           destruct IHm as [IHm|IHm]; auto.
                           right; clear - IHm Hperm1.
                           intros [? ?]; eapply IHm.
                           split; auto.
                           unfold Intv.In; simpl in *.
                           clear IHm H.
                           rewrite Zpos_P_of_succ_nat in H0.
                           omega. }

                      specialize (H _ ltac:(reflexivity)).
                      destruct H; auto.
                      destruct (Clight_lemmas.block_eq_dec b1' b2'); subst; auto.
                    Qed.
                    
                    Lemma setPermBLock_no_overlap:
                      forall (mu : meminj) (m1 : mem) (b b' b1 b2 : block)
                        (ofs delt delta ofs0 : Z) (n : nat),
                        Mem.meminj_no_overlap mu m1 ->
                        permMapLt (setPermBlock (Some Writable)
                                                b ofs (getCurPerm m1) n)
                                  (getMaxPerm m1) ->
                        mu b = Some (b', delt) ->
                        mu b1 = Some (b2, delta) ->
                        b1 <> b ->
                        Mem.perm m1 b1 ofs0 Max Nonempty ->
                        b2 <> b' \/
                        b2 = b' /\
                        ~ Intv.In (ofs0 + delta)
                          ((ofs + delt)%Z, (ofs + delt + Z.of_nat n)%Z).
                    Proof.
                      intros; eapply range_no_overlap; eauto.
                      clear H4.
                      eapply setPermBlock_range_perm in H0; eauto.
                      unfold Mem.range_perm, Mem.perm in *; intros.
                      rewrite mem_lemmas.po_oo in *.
                      
                      specialize (H0 _ H4).
                      rewrite mem_lemmas.po_oo in H0.
                      eapply mem_lemmas.po_trans; eauto.
                      constructor.
                    Qed.

                    (* this lemma is the first clause for proving 
                             Mem.mem_inj (mi_perm)
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

                        +
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
                          eapply inject_lock_simplification; eauto.

                        + eapply H1; auto.
                          rewrite setPermBlock_other_1 in H3; auto.
                          unfold Mem.perm; rewrite_getPerm; auto.
                          eapply Intv.range_notin in Hrange; simpl; auto.
                          omega.
                          
                        + eapply H1; auto.
                          rewrite setPermBlock_other_2 in H3; auto.
                          unfold Mem.perm; rewrite_getPerm; auto.
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
                          (* 2 goals solved by the following*)
                        eapply (Proper_perm_max') in H3;
                          try eassumption;
                          try solve[econstructor];
                          auto.
                      - intros.
                        pose proof (restr_Max_equiv Hlt1) as HH1.
                        pose proof (restr_Max_equiv Hlt2) as HH2.
                        destruct k.
                        + eapply (Proper_perm_max') in H3;
                            try eassumption;
                          eauto.
                          eapply H1 in H3; eauto.
                          destruct H3 as [H3|H3].
                          * left; eapply Proper_perm_max';
                            try eassumption;
                            try solve[econstructor];
                            auto.
                            symmetry; auto.
                          * right; intros ?; apply H3.
                            eapply (Proper_perm_max') in H4;
                            try eassumption;
                            eauto.
                        + (* Separeate in lemma? *)
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
                              + exploit (range_no_overlap mu m1 b2 b1' b1 b1');
                                  try apply Hneq; eauto.
                                * eapply Hinject.
                                * eapply setPermBlock_range_perm in Hlt1.
                                  Lemma range_perm_trans:
                                    forall m b ofs0 ofs1 k p1 p2,
                                    Mem.range_perm m b ofs0 ofs1 k p1 ->
                                    perm_order p1 p2 ->
                                    Mem.range_perm m b ofs0 ofs1 k p2.
                                  Proof.
                                    unfold Mem.range_perm, Mem.perm; intros.
                                    eapply H in H1.
                                    rewrite mem_lemmas.po_oo in *.
                                    eapply juicy_mem.perm_order''_trans; eauto.
                                  Qed.
                                  eapply range_perm_trans; eauto.
                                  constructor.
                                * intros [?|[? ?]].
                                  -- contradict H3; auto.
                                  -- contradict H4; eassumption.
                              + rewrite setPermBlock_other_1 in H2; eauto.
                                eapply Intv.range_notin in Hrange; simpl in *; omega.
                              + rewrite setPermBlock_other_2 in H2; eauto.
                          Qed.

                          eapply setPermBlock_mi_perm_inv_Cur; eauto.
                    Qed.

                    (* Need to replace the [restrPermMap Hlt1] with the equivalent one 
                      that matches setPermBlock_mem_inject. This can be done with the following 
                      definition: [access_map_equiv]
                      
                     *)
                    pose proof (LKSIZE_nat_pos).
                    remember (restrPermMap (proj2 (Hcmpt1 tid Htid1))) as m1_restr.
                    remember (restrPermMap (proj2 (Hcmpt2 tid Htid2))) as m2_restr.

                    

                    remember (useful_permMapLt_trans (proj2 (Hcmpt1 tid Htid1)) Hlt1)
                      as Hlt10.
                    remember (useful_permMapLt_trans (proj2 (Hcmpt2 tid Htid2)) Hlt2')
                      as Hlt20.
                    
                    rewrite (restrPermMap_idempotent _ _ _
                                                      _ Hlt1 Hlt10).
                    rewrite (restrPermMap_idempotent _ _ _
                                                      _ Hlt2' Hlt20).

                    (* m1 *)
                    assert (Hlt1'':
                              permMapLt
                                (setPermBlock (Some Writable) b (intval ofs)
                                              (getCurPerm m1_restr) LKSIZE_nat)
                                (getMaxPerm m1_restr)
                           ).
                    { intros; subst.
                      rewrite getMax_restr, getCur_restr; eauto.
                    }
                    
                    assert (HH:mem_equiv (restrPermMap Hlt10) (restrPermMap Hlt1'')).
                    { eapply restrPermMap_equiv.
                      - subst; reflexivity.
                      - eapply setPermBlock_access_map_equiv; try reflexivity.
                        + subst; symmetry.
                          apply getCur_restr.
                        + econstructor; auto.
                    }
                    rewrite HH.

                    
                    (* m2 *)
                    assert (Hlt2'':
                              permMapLt
                                (setPermBlock (Some Writable) b' (intval ofs + delt)
                                              (getCurPerm m2_restr) LKSIZE_nat)
                                (getMaxPerm m2_restr)
                           ).
                    { intros; subst.
                      rewrite getMax_restr, getCur_restr; eauto.
                    }
                    assert (mem_equiv (restrPermMap Hlt20) (restrPermMap Hlt2'')).
                    { eapply restrPermMap_equiv.
                      - subst; reflexivity.
                      - eapply setPermBlock_access_map_equiv; try reflexivity.
                        + subst; symmetry.
                          apply getCur_restr.
                        + econstructor; auto.
                    }
                    rewrite H0.

                    eapply setPermBlock_mem_inject; eauto.
                    - unfold LKSIZE_nat. rewrite Z2Nat.id.
                      2: { pose proof LKSIZE_pos; omega. }
                      subst m1_restr;
                        rewrite (restr_content_equiv (proj2 (Hcmpt1 tid Htid1))).
                      subst m2_restr;
                        rewrite (restr_content_equiv (proj2 (Hcmpt2 tid Htid2))).
                      eapply CMatch; auto.
                      simpl in *; eassumption. }

                  }

                    
                    (* Might not need. Erase?*)
                    Lemma meminj_restrictPermMap:
                      forall mu m1 m2,
                         Mem.mem_inj mu m1 m2 ->
                        forall perm1 perm2
                          (Hlt1: permMapLt perm1 (getMaxPerm m1))
                          (Hlt2: permMapLt perm2 (getMaxPerm m2))
                          (mi_memval:
                             forall (b1 : block) (ofs : Z) (b2 : block) (delta : Z),
                               mu b1 = Some (b2, delta) ->
                               Mem.perm_order' (perm1 !! b1 ofs) Readable ->
                               memval_inject mu (ZMap.get ofs (Mem.mem_contents m1) !! b1)
                                             (ZMap.get (ofs + delta)%Z (Mem.mem_contents m2) !! b2)),
                          access_map_inject mu perm1 perm2 ->
                           Mem.mem_inj mu (restrPermMap Hlt1) (restrPermMap Hlt2).
                      Proof.
                        intros.
                        inversion H.
                        econstructor.
                        - unfold Mem.perm; intros.
                          destruct k.
                          + do 2 rewrite_getPerm.
                            rewrite getMax_restr in *;
                              rewrite getMaxPerm_correct in *.
                            eapply mi_perm; eassumption.
                          + do 2 rewrite_getPerm.
                            rewrite getCur_restr in *.
                            specialize (H0 b1 b2 delta).
                            rewrite mem_lemmas.po_oo in *.
                            eapply juicy_mem.perm_order''_trans; eauto.
                        - intros.
                          eapply mi_align; eauto.
                          unfold Mem.range_perm, Mem.perm in *.
                          intros ofs0 Hofs.
                          specialize (H2 _ Hofs).
                          rewrite_getPerm.
                          erewrite <- getMax_restr.
                          rewrite getMaxPerm_correct.
                          eassumption.
                        - intros.
                          eapply mi_memval; auto.
                          unfold Mem.perm in H2.
                          rewrite_getPerm.
                          rewrite getCur_restr in H2.
                          assumption.
                      Qed.
                      
                  
                }
                
                
                (* Here *)
                
                destruct Hstore' as (Hlt2' & m2' & Hstore2 & Hinj2).
                
                

                (* Instantiate some of the existensials *)
                econstructor. exists m2'. econstructor. exists mu.
                split; [|split; [|split]].
                
                + (* reestablish the code_inject*)
                  eassumption.
                  
                + (*match _mem *)
                  eassumption.
                  
                + simpl.
                  rewrite cat_app.
                  rewrite (cat_app tr2).
                  eapply List.Forall2_app.
                  * eassumption.                  
                  * econstructor; try solve[constructor].
                    simpl.
                    (* injection of the event*)
                    admit. (* Should be obvious by construction *)
                    
                + (* get the memory and injection *)
                  econstructor; eauto.
                  eapply step_release with
                      (b0:= b')
                      (virtueThread0:=virtueThread2)
                      (virtueLP0:=virtueLP2)
                      (m':=m2')
                      (rmap0:=virtueLP_inject m2 mu rmap)
                  ; eauto; try reflexivity.
                  
                  (* 10 goals produced. *)

                  
                  * unfold HybridMachineSig.isCoarse,
                    HybridMachineSig.HybridCoarseMachine.scheduler.
                    destruct Hbounded as (A&B).
                    subst; destruct virtueThread as (virtue1, virtue2).
                    split;
                      eapply inject_virtue_sub_map;
                      try (eapply matchmem); eauto.
                    
                  * unfold HybridMachineSig.isCoarse,
                    HybridMachineSig.HybridCoarseMachine.scheduler.
                    destruct HboundedLP as (?&?&?&?).
                    subst.
                    eapply (proj1 (Logic.and_assoc _ _ _)).
                    
                    split.
                    -- unfold virtueLP_inject,
                       bounded_maps.map_empty_def, access_map_injected; auto.
                    -- split; eapply inject_virtue_sub_map; try (eapply matchmem); eauto.
                       
                  * clean_cnt.
                    simpl in *.
                    (* This should follow from the simulation *)
                    move Hat_external at bottom.
                    admit.
                    
                  * (* Prove I can read the lock. *)
                    
                    move Haccess at bottom.
                    clean_cmpt.
                    
                    assert (Hperm_range:=Hinj_lock).
                    eapply Mem.range_perm_inject in Hperm_range; eauto.
                    simpl.
                    clean_cnt.
                    erewrite Mem.address_inject; try eapply Hinj_lock; eauto.
                    2: {
                      
                      specialize(Haccess (unsigned ofs)).
                      eapply Haccess.
                      unfold unsigned; split; try omega.
                      eapply Z.lt_add_pos_r.
                      unfold LKSIZE.
                      rewrite size_chunk_Mptr.
                      destruct Archi.ptr64; omega.
                    }
                    unfold unsigned; eauto.
                    replace (intval ofs + delt + LKSIZE)%Z with (intval ofs + LKSIZE + delt)%Z
                      by omega.
                    eassumption.

                  * (* Prove the load succeeds. *)
                    move Hload at bottom.
                    clean_cmpt.
                    eapply Mem.load_inject in Hload; eauto.
                    destruct Hload as (v2& Hload & Hval_inj).
                    simpl.
                    inversion Hval_inj; subst.
                    eauto.
                    erewrite Mem.address_inject; try eapply Hinj_lock; eauto.

                    {
                      specialize(Haccess (unsigned ofs)).
                      eapply Haccess.
                      unfold unsigned; split; try omega.
                      eapply Z.lt_add_pos_r.
                      unfold LKSIZE.
                      rewrite size_chunk_Mptr.
                      destruct Archi.ptr64; omega.
                    }
                    

                  * move Hstore2 at bottom.
                    assert(Heq: intval (add ofs (repr delt)) = (intval ofs + delt)%Z ).
                    {
                      unfold add.
                      Check unsigned_repr.
                      (* look for the lemma with unsigned instead of intval. *)
                      (* write proofs so that you never see intval, instead use unsigned and repr. *)
                      admit. (*using Mem.mi_representable you get delta>= 0 and 
                               (unsigned ofs + delt) < max_unsigned.*)
                    }

                    
                    match goal with
                    | [  |- context[restrPermMap ?X] ] =>
                      replace (restrPermMap X) with (restrPermMap Hlt2')
                    end.
                    -- rewrite Heq; assumption.
                    -- (*Set Printing Implicit. *) 
                      
                      admit. (* dependet type mess *)
                      
                  * (* ThreadPool.lockRes *)
                    eapply INJ_lock_permissions; eauto.
                  * (* new lock is empty *)
                    clear - Hrmap.
                    intros.
                    destruct rmap as (rmap1 &rmap2).
                    unfold virtueLP_inject; simpl.
                    unfold access_map_injected; simpl.
                    unfold tree_map_inject_over_mem; simpl.
                    unfold tree_map_inject_over_tree.
                     admit. (* lemma about construction *)
                    
                  * (* Claims the transfered resources join in the appropriate way *)
                    simpl.
                    move Hangel1 at bottom.
                    move Hangel2 at bottom.
                      
                      
                    (*
                      Sketch: 
                      Should follow from the constructions of the transfered permissions and
                      Hangel1.
                     *)
                    admit.

                    
                  * (* Claims the transfered resources join in the appropriate way *)
                    simpl. move Hangel2 at bottom.
                
                (*
                  Sketch: 
                  Should follow from the constructions of the transfered permissions and
                  Hangel2.
                 *)
                admit.

            Admitted.
            
            pose proof (mtch_target _ _ _ _ _ _ CMatch _ l Htid (contains12 CMatch Htid)) as match_thread.
            simpl in Hcode; exploit_match.
            inversion H3.
            
            (*Destruct the values of the self simulation *)
            pose proof (self_simulation.minject _ _ _ matchmem) as Hinj.
            assert (Hinj':=Hinj).
            pose proof (self_simulation.ssim_external _ _ Aself_simulation) as sim_atx.
            eapply sim_atx in Hinj'; eauto.
            2: { clean_cmpt.
                 eauto.
            }
            clear sim_atx.
            destruct Hinj' as (b' & delt & Hinj_b & Hat_external2); eauto.

            edestruct release_step_diagram_target as
            (e' & m2' & Htid2' & mu' & Hcode_inj & matchmem' & Htrace_inj & external_step)
            ; eauto; simpl; try eassumption.

            { (* invariant st2 *) 
              eapply CMatch. }

            { (*at external *)
              clean_cmpt; assumption. }

            { (* Mem.inject mu restrict restrict*)
              eapply CMatch.
              }

            exists e'. eexists. exists m2', cd, mu'.
            split ; [|split].

            + (* reestablish concur *)
              admit.

            + eassumption.
            + eassumption.
            
            

          (** *tid = hb*)
          - subst tid.

            assert (Hcmpt2: mem_compatible st2 m2).
            { inversion CMatch. assumption. }

            (* rename the memories, to show that they have been modified, 
               since the execution of this thread stopped. *)
            rename m1' into m1''.
            rename m1 into m1'.
            rename m2 into m2'.
            
            (* Retrieve the match relation for this thread *)
            pose proof (mtch_compiled _ _ _ _ _ _ CMatch _ ltac:
                        (reflexivity)
                          Htid (contains12 CMatch Htid)) as Hmatch.
            simpl in Hcode; rewrite Hcode in Hmatch.
            inversion Hmatch; subst.

            rename H5 into Hinterference1.
            rename H7 into Hinterference2.
            rename H1 into Hcomp_match.
            rename H2 into Hstrict_evolution.
            
            rename Htid into Hcnt1.
            rename Hlt' into Hlt_setbBlock.
            rename virtueThread into virtueThread1.
            rename virtueLP into virtueLP1.
            rename Hat_external into Hat_external1.
            rename b into b1.
            rename Hstore into Hstore1.
            
            assert (Hcnt2: containsThread st2 hb).
            { eapply contains12; eauto. }
            
            (** *Diagram No.0*)
            
            assert (Hinj2:= Injfsim_match_meminjX compiler_sim _ _ _ _ Hcomp_match).
            simpl in Hinj2.
            
            (* Show that one can install Writable permissions for the lock in m3. *)
            (*assert (Hlt2':
                      permMapLt
                        (setPermBlock (Some Writable) b (intval ofs) (getCurPerm m2) LKSIZE_nat)
                        (getMaxPerm m2)). 
            { move Hlt2 at bottom.
              move Hinj2 at bottom.
              admit. (* HLT3 *)
            }*)
            assert (Hlt2': permMapLt
           (setPermBlock (Some Writable) b1 (intval ofs)
              (snd (getThreadR Hcnt2)) LKSIZE_nat) 
           (getMaxPerm m2')).
            { move Hlt_setbBlock at bottom.
              move Hinj2 at bottom.
              admit. (* HLT2 *)
            }
            
            remember (virtueThread_inject m2' mu virtueThread1)  as virtueThread2.
            remember (virtueLP_inject m2' mu virtueLP1) as virtueLP2.
            
            simpl in Hat_external1.
            assert (Hat_external1': Smallstep.at_external
                        (Smallstep.part_sem (Clight.semantics2 C_program))
                        (Smallstep.set_mem code1 m1) = Some (UNLOCK, Vptr b1 ofs :: nil)).
              { (* This follows from self simulation:
                   interferences, preserves at_external.
                 *) admit.
              }
            assert (H: exists b2 delt2,
                       mu b1 = Some (b2, delt2) /\
                       semantics.at_external (semantics.csem (event_semantics.msem (@semSem AsmSem) ))
                                             (code2) m2 =
                       Some (UNLOCK, Vptr b2 (add ofs (repr delt2)) :: nil)
                                                 
                   ).
              {
                pose proof (Injsim_atxX compiler_sim _ _ _ _ Hcomp_match Hat_external1')
                as Hatx.
                destruct Hatx as (args' & Hat_external2 & list_inj).
                inversion list_inj; subst.
                inversion H2; inversion H4; subst.
                exists b2, delta; repeat (split; auto).
                eapply evolution_inject_incr; eassumption.
              }
            destruct H as (b2&delt2&Hinj_b2&Hat_external2).
            assert (Hat_external2': 
                      semantics.at_external
                        (semantics.csem (event_semantics.msem (@semSem AsmSem) ))
                        code2
                        (restrPermMap (proj1 (Hcmpt2 hb (contains12 CMatch Hcnt1)))) =
                      Some (UNLOCK, Vptr b2 (add ofs (repr delt2)) :: nil)
                                                 
                   ).

            { (* This follows from self simulation:
                 interferences, preserves at_external.
               *) admit.
            }
            
            
            (* build m2' *)
            assert (Hstore2:=Hstore1).
            eapply Mem.store_mapped_inject in Hstore2; eauto.
            2: {
              instantiate (1:= (restrPermMap Hlt2')).
              (* This goal requires that the injection holds 
                 even after the lock's Cur permission is set 
                 to Writable (in both memories). 
                 This is probably a simple general lemma, about
                 changing Cur memories in two injected memories.
               *)
              admit.
            (*This and the previous admit (marked with HLT2)
              Should both come from the same lemma. *)
            }
            destruct Hstore2 as (m2''& Hstore2 & Hinj2').
            
            remember (add ofs (repr delt2)) as ofs2.
            remember (computeMap (fst (getThreadR Hcnt2)) (fst virtueThread2),
                                               computeMap (snd (getThreadR Hcnt2)) (snd virtueThread2)) as new_cur2.
            remember ((updLockSet
                        (updThread Hcnt2 (Kresume (TST code2) Vundef) new_cur2)
                        (b2, intval ofs2) virtueLP2)) as st2'.
            
            match goal with
              [|- context[concur_match _ _ ?st1 ?m1 _ _] ] =>
              remember st1 as st1'
            end. 

            assert (Hcmpt1': mem_compatible st1' m1'').
            {
              admit. (*TODO: from Hcmpt1 *)
            }
            assert (H: ThreadPool (Some (S hb)) =
                    @t dryResources (HybridSem (@Some nat (S hb)))).
            { reflexivity. }
            dependent rewrite <- H in st2'. clear H.
            assert (Hcmpt2': mem_compatible st2' m2'').
            {
              admit. (*TODO: from Hcmpt2 *)
            }


            
            eexists.
            exists st2', m2'', (Some i), mu.
            split; [|split].
            
            + eapply Build_concur_match
                     with (memcompat1:=Hcmpt1')(memcompat2:=Hcmpt2')
              ; simpl;
                try assumption;
                try (subst st2' st1'; apply CMatch).
              * admit. (*inject threads*)
              * admit. (*inject locks*)
              * admit. (*inject lock content*)
              * admit. (* invariant is preserved! *)
              * admit. (* thread_match source*)
              * admit. (* thread_match target. *)
              * (* thread_match compiled. *)

                intros thread HH Hcnt1_dup Hcnt2_dup. subst thread.
                
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
                subst st1'.
                same_types Hcnt1_dup Hcnt1.
                subst st2'.
                same_types Hcnt2_dup Hcnt2.
                clean_cnt.

                match goal with
                | [|- match_thread_compiled _ _ ?X _ ?Y _] =>
                  let HH1:= fresh "HH1" in
                  assert (HH1: X = Kresume (SST code1) Vundef)
                     by
                      (simpl; rewrite eqtype.eq_refl; reflexivity);
                    let HH2:= fresh "HH2" in
                    assert (HH2: Y = Kresume (TST code2) Vundef) by
                        (simpl; rewrite eqtype.eq_refl; reflexivity)
                   
                end.
                
                rewrite HH1; clear HH1.
                rewrite HH2; clear HH2.
                
                econstructor.
                intros j'' s1' m1''' m2''' lev1' lev2'.
                intros Hstrict_evolution' Hincr' Hinterference1' Hinterference2'
                Hafter_ext.
                remember (fst virtueThread1) as dpm1.
                remember (Events.Event_acq_rel lev1 dpm1 lev1' :: nil) as rel_trace.
                  
              (*
                Prove that this is a CompCert step (en external step).
               *)
                assert (Hstep: Smallstep.step
                          (Clight.part_semantics2 Clight_g)
                          (Smallstep.set_mem code1 m1)
                          rel_trace
                          (Clight.set_mem s1' m1''')).
                {
                  simpl in Hafter_ext. unfold Clight.after_external in Hafter_ext.
                  move Hat_external1 at bottom.
                  unfold Clight.at_external in Hat_external1.
                  destruct code1 eqn:Hcallstate; try discriminate.
                  simpl in Hat_external1.
                  destruct fd eqn:Hext_func; try discriminate.
                  (* inversion Hat_external1; clear Hat_external1; subst. *)
                  inversion Hat_external1. subst e args.
                  simpl.
                  pose proof (Clight.step_external_function
                                Clight_g (Clight.function_entry2 Clight_g)
                                UNLOCK t0 t1 c (Vptr b1 ofs :: nil) k m1 Vundef
                                rel_trace
                                m1''') as HH.
                  assert (Hextcall: Events.external_call
                                      UNLOCK (Clight.genv_genv Clight_g)
                                      (Vptr b1 ofs :: nil) m1
                                      rel_trace
                                      Vundef m1''').
                  { simpl.
                    
                    Notation delta_perm_map:=(PTree.t (Z -> option (option permission))).
                    
                    Inductive release: val -> mem -> delta_perm_map ->  mem -> Prop  :=
                    | ReleaseAngel:
                        forall b ofs m dpm m',
                          True ->
                          (* This shall codify, the change in permissions
                       and changing the  lock value to 1.
                           *)
                          release (Vptr b ofs) m dpm m'.

                    Inductive extcall_release: Events.extcall_sem:=
                    | ExtCallRelease:
                        forall ge m m' m'' m''' b ofs e dpm e',
                          mem_interference m e m' ->
                          release (Vptr b ofs) m' dpm m'' ->
                          mem_interference m'' e' m''' ->
                          extcall_release ge (Vptr b ofs :: nil) m
                                          (Events.Event_acq_rel e dpm e' :: nil)
                                          Vundef m'''.
                    Lemma extcall_properties_release:
                      Events.extcall_properties extcall_release UNLOCK_SIG.
                    Proof.
                    (* this is given axiomatically in compcert, 
                     but we    must prove it*)
                    Admitted.
                    
                    Axiom ReleaseExists:
                      forall ge args m ev r m',
                        Events.external_functions_sem "release" UNLOCK_SIG
                                                  ge args m ev r m' =
                        extcall_release ge args m ev r m'.
                    (* This function is given axiomaticall in CompCert. *)
                    
                    rewrite ReleaseExists.
                    subst rel_trace; econstructor.
                    - eassumption.
                    - constructor; auto. (*TODO*)
                    - eassumption.
                      (* 
                      replace (Clight.get_mem s1') with m1'''.
                      eassumption.
                      rename m into MM.
                      inversion Hafter_ext; reflexivity.*)
                  }
                 
                  eapply HH in Hextcall; auto.
                  inversion Hafter_ext.
                  
                  (* replace m1''' with (Clight.get_mem s1') by (subst s1'; reflexivity). *)
                  unfold Clight.step2. 
                  auto.
                  
                }

                unfold compiler_match in Hcomp_match.
                eapply (Injsim_simulation_atxX compiler_sim) in Hstep; simpl in *; eauto.
                specialize (Hstep _ _ _ Hcomp_match).
                destruct Hstep as (j2'&Hincr&Hstep_str&Hstep).
                destruct Hstep_str as
                    (i2_str&s2_str&t_str&Hstep_str&Hmatch_str&Hinj_trace_str).
                remember 
                  (Events.Event_acq_rel lev2 (fst virtueThread2) lev2' :: nil)  as rel_trace2.
                assert (Htrace_str : exists lev2_str dpm_str lev2_str',
                           t_str =
                           Events.Event_acq_rel lev2_str
                                                dpm_str
                                                lev2_str' :: nil).
                { subst. inversion Hinj_trace_str; subst.
                  inversion H4; subst.
                  inversion H2; subst.
                  do 3 eexists. f_equal.
                }
                destruct Htrace_str as (lev2_str&dpm_str&lev2_str'&Htrace_str).

                assert (Hconsecutive:
                          consecutive (Mem.nextblock m2) lev2).
                { admit. (* this follows from Hinterference2*) }

                assert (Hconsecutive': consecutive (Mem.nextblock m2'') lev2').
                { admit. (* this follows from Hinterference2*) }

                (** *Left Diagrams *)
                pose proof (principled_diagram_exists
                              _ _ _ _ _
                              Hstrict_evolution Hconsecutive) as
                    Pdiagram.
                destruct Pdiagram as (lev20&Hprincipled&Hlessdef).
                assert (Hdiagram: diagram (Mem.nextblock m2) j j2' lev1 lev2_str).
                { econstructor.
                  - eauto.
                  - subst rel_trace t_str;
                      inversion Hinj_trace_str; subst.
                    inversion H3; subst. auto.
                    Lemma list_inject_weaken: 
                      forall j lev1 lev2,
                      Events.list_inject_mem_effect_strong j lev1 lev2 ->
                      Events.list_inject_mem_effect j lev1 lev2.
                    Proof.
                      intros. inversion H; subst; constructor.
                      -
                    Admitted.

                    eapply list_inject_weaken; auto.
                  - admit. (* follows from the syntas. *)
                }
                destruct (principled_diagram_correct
                            _ _ _ _ _ _ _ Hprincipled Hdiagram)
                  as (Hincr_mu & lessdef_str).

                (** *Right Diagrams*)
                pose proof (principled_diagram_exists
                              _ _ _ _ _
                              Hstrict_evolution' Hconsecutive') as
                    Pdiagram'.
                destruct Pdiagram' as (lev20'&Hprincipled'&Hlessdef').

                
                assert (Hdiagram':
                          diagram (Mem.nextblock m2'') mu j2' lev1' lev2_str').
                { econstructor.
                  - eauto.
                  - subst rel_trace t_str;
                      inversion Hinj_trace_str; subst.
                    inversion H3; subst. 
                    eapply list_inject_weaken; auto.
                  - admit. (* follows from the syntax. *)
                }
                destruct (principled_diagram_correct
                            _ _ _ _ _ _ _ Hprincipled' Hdiagram')
                  as (Hincr_mu_j2' & lessdef_str').
                
                    
                assert (Hinj_trace: Events.inject_trace j2' rel_trace rel_trace2).
                { subst rel_trace rel_trace2.
                  econstructor; try solve[constructor].
                  econstructor; try eassumption.
                  - emonotonicity; eauto.
                    emonotonicity; eauto.
                    eapply evolution_list_inject_mem; eauto.
                  - emonotonicity; eauto.
                    subst dpm1. admit. (* proof constructions correct*)
                  - emonotonicity; eauto.
                    eapply evolution_list_inject_mem in Hstrict_evolution'; eauto.
                }
                    
                    (*HERE*)
                       
                (*
                assert (
                  exists res,
                    extcall_release (Genv.globalenv Asm_program)
                                    (Vptr b2 (add ofs (repr delt2)) :: nil)
                                    m2
                                    t_str
                                    res (Asm.get_mem s2_str)).
                {
                  pose ReleaseExists as release_func.
                  clear - Hstep_str Hat_external2 release_func.
                  destruct code2 eqn:HHH.
                  inversion Hstep_str; subst.
                  + (* Builtin is wrong*)
                    simpl in Hat_external2.
                    rewrite H1 in Hat_external2.
                    destruct (eq_dec ofs0 zero) eqn:ieq0; try congruence.
                    unfold the_ge in Hat_external2.
                    destruct (Genv.find_funct_ptr (Genv.globalenv Asm_program) b) eqn:HH; try congruence.
                    destruct f0; try congruence.
                  + (* External is UNLOCK *)
                    simpl in Hat_external2.
                    rewrite H1 in Hat_external2.
                    destruct (eq_dec zero zero) eqn:ieq0; try congruence.
                    unfold the_ge in Hat_external2.
                    destruct (Genv.find_funct_ptr (Genv.globalenv Asm_program) b) eqn:HH; try congruence.
                    destruct f; try congruence.
                    inversion H2; subst.
                    apply Asm_core.get_extcall_arguments_spec in H3.
                    rewrite H3 in Hat_external2.
                    inversion Hat_external2; subst.
                    simpl in H4.
                    rewrite ReleaseExists in H4.
                    inversion H4; subst.
                    
                    simpl.
                    eexists; eassumption. }
                 *)
                    
                destruct  (Hstep _ Hinj_trace)
                  as (cd' & s2' & step & comp_match ).


                (* We prove that code2 must do an external step. *)
                (* Note: no need for a { here. 
                 TODO: better formating *)
                { move Hat_external2' at bottom.
                  unfold Asm.at_external in Hat_external2'.
                  destruct code2 eqn:Code.
                  simpl in Hat_external2'.
                  destruct (r Asm.PC) eqn:rPC; try discriminate.
                  destruct (eq_dec i0 zero) eqn:i0_0; try discriminate.
                  unfold Asm_g.
                  destruct (Genv.find_funct_ptr the_ge b) eqn:func_lookup; try discriminate.
                  destruct f; try discriminate.
                   
                   
                  inversion step; subst; try solve[inversion H5] .
                  - rewrite rPC in H2; inversion H2; subst.
                    unfold the_ge in func_lookup.
                    rewrite func_lookup in H3.
                    inversion H3; discriminate.
                 (*  - rewrite rPC in H2; inversion H2; subst.
                    unfold the_ge in func_lookup.
                    rewrite func_lookup in H3.
                    inversion H3 discriminate. *)
                  - rename m' into m21'''.
                    (* NOTE: 
                       - the s2' (i.e. target state) in comp_match, 
                       results from inverting the step.
                       - the st'2 (i.e. target state) in the goal,
                       results from Asm.after_external. 
                     *)
                    unfold Asm.after_external.
                    unfold Asm.after_external_regset.
                    rewrite rPC, i0_0, func_lookup.
                    (* Show that target program is executing the same function*)
                    assert (FUNeq:e0 = ef ).
                    { assert (BB0: b0 = b)
                        by (rewrite rPC in H2; inversion H2; reflexivity).
                      subst b0. unfold the_ge in func_lookup.
                      rewrite func_lookup in H3; inversion H3.
                      reflexivity.
                    } subst e0.
                    
                    (* Show that the function is UNLOCK*)
                    match type of Hat_external2' with
                    | match ?x with _ => _ end = _ =>
                      destruct x eqn:HH; try discriminate
                    end.

                    inversion Hat_external2'. subst.
                    do 3 eexists; repeat split; eauto.
                    unfold compiler_match.
                    move comp_match at bottom.
                    simpl.
                     
                     instantiate(1:=cd').
                     replace (Clight.set_mem s1' (Clight.get_mem s1')) with s1'
                       by (destruct s1'; reflexivity).
                     simpl in comp_match.
                     
                     (*This should be generalizable*)
                     unfold Asm.loc_external_result,Conventions1.loc_result in comp_match.
                     replace Archi.ptr64 with false in comp_match by reflexivity. 
                     simpl in comp_match.
                     
                     repeat f_equal.

                     assert (Hres: res = Vundef).
                     { unfold Events.external_call in *.
                       rewrite ReleaseExists in H5.
                       inversion H5. reflexivity.
                     }
                     subst res.

                     replace m2''' with m21'''. auto.
                     
                     (*  m21''' = m2''' *)
                     simpl in H5.
                     rewrite ReleaseExists in H5.
                     inversion H5; subst.
                     rename m' into m21'.
                     rename m'' into m21''.
                     rename H10 into Hinterference21.
                     rename H11 into Hrelease.
                     
                     move Hinterference2' at bottom.

                     (*
                     m1 -lev1-> m1' -dpm-> m1'' -lev1'-> m1'''
                     |          |         |            |
                     |          |         |            |
                     m2 -lev2-> m2' -dpm-> m2'' -lev2'-> m2'''
                     !          !         !            !     
                     m2 -lev2-> m21'-dpm-> m21''-lev2'-> m21'''
                      *)
                     
                     assert (m21' =
                             (restrPermMap (proj1 ((memcompat2 CMatch) hb Hcnt2)))).
                     { move Hinterference2 at bottom.
                       move Hinterference21 at bottom.
                       eapply mem_interference_determ; eassumption.
                     }
                     
                     assert (m21'' = (restrPermMap (proj1 (Hcmpt2' hb Hcnt2)))).
                     { move Hstore2 at bottom.
                       move Hrelease at bottom.
                       admit.
                       (* Sketch: release has to be defined.
                          it should modify content without touching permissions.
                          then show: 
                          m2' -release-> m2''
                          (or their restrictions to the cur)
                          release is deterministic and so the result follows. *)
                     }

                     (*  m21''' = m2''' *)
                     eapply mem_interference_determ; subst; try eassumption.
                }


                (* SEEMS like this was an old attempt.
                   REMOVE

                move Hat_external2 at bottom.
              unfold Asm.after_external.
              unfold Asm.at_external,Asm.set_mem in Hat_external2.
              destruct code2.
              unfold Asm.after_external_regset.
              destruct (r Asm.PC) eqn:rPC; try discriminate.
              destruct (eq_dec i0 zero) eqn:i0_0; try discriminate.
              unfold Asm_g.
              destruct (Genv.find_funct_ptr the_ge b) eqn:func_lookup; try discriminate.
              destruct f; try discriminate.
              
                   eexists. split; try reflexivity.
                --
                   reflexivity.
                --
                
                destruct (Clight.set_mem code1 (restrPermMap (proj1 (Hcmpt hb Hcnt1)))) eqn:Hcalstate;
                  simpl in Hat_external1; try solve[inversion Hat_external1].
              rewrite Hcalstate in Hat_external1.



              admit. (*reestablish the concur match. *)
              *)
              
            + (*
                GOAL: 
                Forall2 (inject_mevent mu)
                (seq.cat tr1
                (Events.external hb
                (Events.release (b1, intval ofs)
                (Some (build_delta_content (fst virtueThread1) m1''))) :: nil))
                (seq.cat tr2 (Events.external hb ?e' :: nil))
               *)

              rewrite cat_app.
              rewrite (cat_app tr2).
              eapply List.Forall2_app.
              * eauto.
              * econstructor; try solve[constructor].
                simpl.
                econstructor.
                admit.
                (* injection of the event*)
                (* Should be obvious by construction *)
            + (* HybridMachineSig.external_step *)

              econstructor; eauto.
              eapply step_release with
                    (b:= b2)
                    (virtueThread:=virtueThread2)
                    (virtueLP:=virtueLP2);
                eauto; try reflexivity;
              try unfold HybridMachineSig.isCoarse,
              HybridMachineSig.HybridCoarseMachine.scheduler.
              rename m2' into MMM.
              rename m2 into MMM2.
              
              * (* bounded_maps.sub_map *)
                
                subst virtueThread2.
                unfold virtueThread_inject.
                destruct virtueThread1 as (virtue11, virtue12).
                cbv iota beta delta[fst] in *.
                destruct Hbounded.
                split.
                -- eapply inject_virtue_sub_map;
                     try eapply matchmem.
                   2: eassumption.
                   eapply CMatch. 
                  
                -- eapply inject_virtue_sub_map;
                     try eapply matchmem.
                   2: eassumption.
                   eapply CMatch. 
                
              * (* bounded_maps.sub_map *)
                
                destruct HboundedLP as (?&?&?).
                
                eapply (proj1 (Logic.and_assoc _ _ _)).
                split.

                (*Easy ones: the default is trivial:
                  bounded_maps.map_empty_def
                 *)
                subst virtueLP2.
                unfold virtueLP_inject,
                bounded_maps.map_empty_def, access_map_injected;
                  simpl.
                split; auto.

                assert (HboundedLP':
                    bounded_maps.sub_map (snd (fst virtueLP1)) (snd (getMaxPerm m1')) /\
                    bounded_maps.sub_map (snd (snd virtueLP1)) (snd (getMaxPerm m1'))
                  ) by assumption.
                

                subst virtueLP2.
                destruct virtueLP1 as (virtueLP_fst, virtueLP_snd).
                revert HboundedLP'.
                unfold virtueLP_inject, access_map_injected.
                simpl (fst _).
                simpl (snd _) at 3 6 9.
                

                (* eapply self_simulation.minject in matchmem. *)
                intros (Hl & Hr); split;
                  eapply inject_virtue_sub_map;
                  try eapply CMatch; eauto.

                
              * (*invariant st4 *)
                admit.

                
              * (* at_external for code 4. *)
                simpl in *; eassumption.
                
              * (* Mem.range_perm *)
                (* Can read the lock *)
                admit.

              * (* The load. *)
                admit.
                
              * (* the store *)
                admit.

              * (* content of lockres*)
                (* ThreadPool.lockRes st4 (b4', ofs4') *)
                (* NOTE: why is it rmap? It should be an injection of rmap 
                   ANSWER: the 'RMAP' is empty, so its injection is also empty... 
                 *)

                admit.
                
              * (* permissions join FST*)
                admit.
                
              * (* permissions join SND *)
                admit.
                
              * admit. (* Wrong machine state *)      
                
          - (* hb < tid *)
            pose proof (mtch_source _ _ _ _ _ _ CMatch _ l Htid (contains12 CMatch Htid)) as HH.
            admit.


            
        Admitted.


        Lemma make_step_diagram:
          forall (U : list nat) (tr1 tr2 : HybridMachineSig.event_trace)
                 (st1 : ThreadPool (Some hb)) (m1 m1' : mem) 
                 (tid : nat) (cd : option compiler_index)
                 (st2 : ThreadPool (Some (S hb))) (mu : meminj) 
                 (m2 : mem) (Htid : ThreadPool.containsThread st1 tid)
                 (c : semC) (b : block) (ofs : Integers.Ptrofs.int)
                 (pmap_tid' : access_map * access_map),
            concur_match cd mu st1 m1 st2 m2 ->
            List.Forall2 (inject_mevent mu) tr1 tr2 ->
            forall Hcmpt : mem_compatible st1 m1,
              HybridMachineSig.schedPeek U = Some tid ->
              invariant st1 ->
              ThreadPool.getThreadC Htid = Kblocked c ->
              semantics.at_external
                (semantics.csem (event_semantics.msem semSem)) c
                (restrPermMap (fst (ssrfun.pair_of_and (Hcmpt tid Htid)))) =
              Some (MKLOCK, (Vptr b ofs :: nil)%list) ->
              Mem.store AST.Mint32
                        (restrPermMap (fst (ssrfun.pair_of_and (Hcmpt tid Htid)))) b
                        (Integers.Ptrofs.intval ofs) (Vint Integers.Int.zero) =
              Some m1' ->
              Mem.range_perm
                (restrPermMap (fst (ssrfun.pair_of_and (Hcmpt tid Htid)))) b
                (Integers.Ptrofs.intval ofs)
                (BinInt.Z.add (Integers.Ptrofs.intval ofs) LKSIZE) Cur Writable ->
              setPermBlock (Some Nonempty) b (Integers.Ptrofs.intval ofs)
                           (fst (ThreadPool.getThreadR Htid)) LKSIZE_nat = 
              fst pmap_tid' ->
              setPermBlock (Some Writable) b (Integers.Ptrofs.intval ofs)
                           (snd (ThreadPool.getThreadR Htid)) LKSIZE_nat = 
              snd pmap_tid' ->
              ThreadPool.lockRes st1 (b, Integers.Ptrofs.intval ofs) = None ->
              exists
                e' (st2' : t) (m2' : mem) (cd' : option compiler_index) 
                (mu' : meminj),
                concur_match cd' mu'
                             (ThreadPool.updLockSet
                                (ThreadPool.updThread Htid (Kresume c Vundef) pmap_tid')
                                (b, Integers.Ptrofs.intval ofs) (empty_map, empty_map))
                             m1' st2' m2' /\
                List.Forall2 (inject_mevent mu') (seq.cat tr1 (Events.external tid (Events.mklock (b, Integers.Ptrofs.intval ofs)) :: nil))
                  (seq.cat tr2 (Events.external tid e' :: nil)) /\
                HybridMachineSig.external_step
                  (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
                  U tr2 st2 m2 (HybridMachineSig.schedSkip U)
                  (seq.cat tr2
                           (Events.external tid e' :: nil))
                  st2' m2'.
        Proof.
        Admitted.

        Lemma free_step_diagram:
          forall (U : list nat) (tr1 tr2 : HybridMachineSig.event_trace)
                 (st1 : ThreadPool (Some hb)) (m1' : mem) 
                 (tid : nat) (cd : option compiler_index)
                 (st2 : ThreadPool (Some (S hb))) (mu : meminj) 
                 (m2 : mem) (Htid : ThreadPool.containsThread st1 tid)
                 (c : semC) (b : block) (ofs : Integers.Ptrofs.int)
                 (pmap_tid' : access_map * access_map)
                 (pdata : nat -> option permission) (rmap : lock_info),
            concur_match cd mu st1 m1' st2 m2 ->
            List.Forall2 (inject_mevent mu) tr1 tr2 ->
            forall Hcmpt : mem_compatible st1 m1',
              HybridMachineSig.schedPeek U = Some tid ->
              bounded_maps.bounded_nat_func' pdata LKSIZE_nat ->
              invariant st1 ->
              ThreadPool.getThreadC Htid = Kblocked c ->
              semantics.at_external
                (semantics.csem (event_semantics.msem semSem)) c
                (restrPermMap (fst (ssrfun.pair_of_and (Hcmpt tid Htid)))) =
              Some (FREE_LOCK, (Vptr b ofs :: nil)%list) ->
              ThreadPool.lockRes st1 (b, Integers.Ptrofs.intval ofs) =
              Some rmap ->
              (forall (b0 : BinNums.positive) (ofs0 : BinNums.Z),
                  (fst rmap) !! b0 ofs0 = None /\ (snd rmap) !! b0 ofs0 = None) ->
              Mem.range_perm
                (restrPermMap (snd (ssrfun.pair_of_and (Hcmpt tid Htid)))) b
                (Integers.Ptrofs.intval ofs)
                (BinInt.Z.add (Integers.Ptrofs.intval ofs) LKSIZE) Cur Writable ->
              setPermBlock None b (Integers.Ptrofs.intval ofs)
                           (snd (ThreadPool.getThreadR Htid)) LKSIZE_nat = 
              snd pmap_tid' ->
              (forall i : nat,
                  BinInt.Z.le 0 (BinInt.Z.of_nat i) /\
                  BinInt.Z.lt (BinInt.Z.of_nat i) LKSIZE ->
                  Mem.perm_order'' (pdata (S i)) (Some Writable)) ->
              setPermBlock_var pdata b (Integers.Ptrofs.intval ofs)
                               (fst (ThreadPool.getThreadR Htid)) LKSIZE_nat = 
              fst pmap_tid' ->
              exists
                e' (st2' : t) (m2' : mem) (cd' : option compiler_index) 
                (mu' : meminj),
                concur_match cd' mu'
                             (ThreadPool.remLockSet
                                (ThreadPool.updThread Htid (Kresume c Vundef) pmap_tid')
                                (b, Integers.Ptrofs.intval ofs)) m1' st2' m2' /\
                List.Forall2 (inject_mevent mu') (seq.cat tr1 (Events.external tid (Events.freelock (b, Integers.Ptrofs.intval ofs)) :: nil))
                  (seq.cat tr2 (Events.external tid e' :: nil)) /\
                HybridMachineSig.external_step
                  (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
                  U tr2 st2 m2
                  (HybridMachineSig.schedSkip U)
                  (seq.cat tr2 (Events.external tid e' :: nil)) st2' m2'.
        Proof.
        Admitted.

        Lemma acquire_fail_step_diagram:
          forall (U : list nat) (tr1 tr2 : HybridMachineSig.event_trace)
                 (st1' : ThreadPool (Some hb)) (m1' : mem) 
                 (tid : nat) (cd : option compiler_index)
                 (st2 : ThreadPool (Some (S hb))) (mu : meminj) 
                 (m2 : mem) (Htid : ThreadPool.containsThread st1' tid)
                 (b : block) (ofs : Integers.Ptrofs.int) 
                 (c : semC) (Hcmpt : mem_compatible st1' m1'),
            concur_match cd mu st1' m1' st2 m2 ->
            List.Forall2 (inject_mevent mu) tr1 tr2 ->
            HybridMachineSig.schedPeek U = Some tid ->
            semantics.at_external
              (semantics.csem (event_semantics.msem semSem)) c
              (restrPermMap (fst (ssrfun.pair_of_and (Hcmpt tid Htid)))) =
            Some (LOCK, (Vptr b ofs :: nil)%list) ->
            Mem.load AST.Mint32
                     (restrPermMap (snd (ssrfun.pair_of_and (Hcmpt tid Htid)))) b
                     (Integers.Ptrofs.intval ofs) = Some (Vint Integers.Int.zero) ->
            Mem.range_perm
              (restrPermMap (snd (ssrfun.pair_of_and (Hcmpt tid Htid)))) b
              (Integers.Ptrofs.intval ofs)
              (BinInt.Z.add (Integers.Ptrofs.intval ofs) LKSIZE) Cur Readable ->
            ThreadPool.getThreadC Htid = Kblocked c ->
            invariant st1' ->
            exists
              e' (st2' : t) (m2' : mem) (cd' : option compiler_index) 
              (mu' : meminj),
              concur_match cd' mu' st1' m1' st2' m2' /\
              List.Forall2 (inject_mevent mu') (seq.cat tr1 (Events.external tid (Events.failacq (b, Integers.Ptrofs.intval ofs)) :: nil))
                (seq.cat tr2 (Events.external tid e' :: nil)) /\
              HybridMachineSig.external_step
                (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler)
                U tr2 st2 m2
                (HybridMachineSig.schedSkip U)
                (seq.cat tr2 (Events.external tid e' :: nil))
                st2' m2'.
        Proof.
        Admitted.
        
    Lemma external_step_diagram:
      forall (U : list nat) (tr1 tr2 : HybridMachineSig.event_trace) (st1 : ThreadPool.t) 
        (m1 : mem) (st1' : ThreadPool.t) (m1' : mem) (tid : nat) (ev : Events.sync_event),
      forall (cd : option compiler_index) (st2 : ThreadPool.t) (mu : meminj) (m2 : mem),
        concur_match cd mu st1 m1 st2 m2 ->
        List.Forall2 (inject_mevent mu) tr1 tr2 ->
        forall (Htid : ThreadPool.containsThread st1 tid) (Hcmpt : mem_compatible st1 m1),
          HybridMachineSig.schedPeek U = Some tid ->
          syncStep true Htid Hcmpt st1' m1' ev ->
          exists ev' (st2' : t) (m2' : mem) (cd' : option compiler_index) 
            (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            List.Forall2 (inject_mevent mu') (seq.cat tr1 (Events.external tid ev :: nil)) (seq.cat tr2 (Events.external tid ev' :: nil)) /\
            HybridMachineSig.external_step
              (scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler) U tr2 st2 m2 (HybridMachineSig.schedSkip U)
              (seq.cat tr2 (Events.external tid ev' :: nil)) st2' m2'.
    Proof.
      intros.
      inversion H2; subst.
      - (*Acquire*)
        eapply acquire_step_diagram; eauto.
      - (*Release*)
        eapply release_step_diagram; eauto.
      - (*Create/Spawn*)
        eapply Create_step_diagram; eauto.
      - (*Make Lock*)
        eapply make_step_diagram; eauto.
      - (*Free Lock*)
        eapply free_step_diagram; eauto.
      - (*AcquireFail*)
        eapply acquire_fail_step_diagram; eauto.
    Qed.


    
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
        destruct (mtch_compiled0 hb ltac:(reflexivity) Htid Hcnt2) as
            (cd0 & Hcd0 & MTCH_thread_compiled).
        rewrite Hcode in MTCH_thread_compiled.
        inversion MTCH_thread_compiled; subst.
        inversion H9. subst cd0 j s1 s4.

        rename code2 into code4.
        rename s2 into code2.
        rename s3 into code3.
        
        inversion H4. subst cd0 j s2 m5 s3 m6.
        move Hafter_external at bottom. simpl in *.
        unfold state_sum_options in Hafter_external.
        destruct (Clight.after_external None code1 m') eqn:Hafter_external1;
          inversion Hafter_external; subst.

        (* Prove of the Diagram No.1 *)
        assert (Hafter_external2: exists j1' code2',
                   Clight.after_external None code2 m0 = Some code2' /\
                   Clight_match j1' code1 m' code2
                                (@Smallstep.get_mem (Smallstep.part_sem (Clight.semantics2 C_program)) code2') ).
        {
          clear - Hafter_external1 H3.
          (* This should be proven about Clight OR in self_simulation
             just like ssim_external *)
         
          admit.
        }

        destruct Hafter_external2 as (j1' & code2' & Hafter_external2 & Cmatch').
        eapply H7 in Hafter_external2. clear H7.
        destruct Hafter_external2 as (code3' & Hafter_external3 & compiler_match).

        (* Prove of the Diagram No.3 *)
        assert (Hafter_external4: exists j3' (code4': Smallstep.state (Asm.part_semantics Asm_g)),
                   Asm.after_external Asm_g  None code4 m0 = Some code4' /\
                   Asm_match j3' code3 m' code3
                                (@Smallstep.get_mem (Asm.part_semantics Asm_g) code4') ).
        {
          clear - Hafter_external1 H3.
          (* This should be proven about Clight OR in self_simulation
             just like ssim_external *)
         
          admit.
        }

        destruct Hafter_external4 as (j3' & code4' & Hafter_external4 & Amatch').
        
        remember 
        (updThread Hcnt2 (Krun (TState Clight.state Asm.state code4'))
                   (getCurPerm (Smallstep.get_mem code4'), snd (getThreadR Htid))) as st2'.

        exists st2', m2, (Some cd), (compose_meminj (compose_meminj j1' j2) j3'). 
        split; [|split].
        + admit. (* Reestablish the concur_match *)
        + admit. (* Inject of traces *)
        + (* Step *)
          assert (HH: U = (HybridMachineSig.yield(Scheduler:=HybridMachineSig.HybridCoarseMachine.scheduler) U))
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
        eapply (Injfsim_order_wf compiler_sim). (*well_founded order*)

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
        ThreadPool (Some 0) -> Memory.Mem.mem -> ThreadPool (Some n) -> Memory.Mem.mem -> Prop:=
    | refl_match: forall j tp m,
        match_state 0 nil j tp m tp m
    | step_match_state:
        forall n ocd ils jn jSn tp0 m0 tpn mn tpSn mSn,
          match_state n ils jn tp0 m0 tpn mn ->
          concur_match n ocd jSn tpn mn tpSn mSn ->
          match_state (S n) (cons ocd ils) (compose_meminj jn jSn) tp0 m0 tpSn mSn.

    Lemma trivial_self_injection:
          forall m : option mem,
            HybridMachine_simulation_properties (HybConcSem (Some 0) m)
                                                (HybConcSem (Some 0) m) (match_state 0).
    Proof.
      (* NOTE: If this lemma is not trivial, we can start the induction at 1,
         an the first case follow immediately by lemma
         compile_one_thread
       *)
    Admitted.

    Lemma simulation_inductive_case:
      forall n : nat,
        (forall m : option mem,
            HybridMachine_simulation_properties (HybConcSem (Some 0) m)
                                                (HybConcSem (Some n) m) (match_state n)) ->
        (forall m : option mem,
            HybridMachine_simulation_properties (HybConcSem (Some n) m)
                                                (HybConcSem (Some (S n)) m) (concur_match n)) ->
        forall m : option mem,
          HybridMachine_simulation_properties (HybConcSem (Some 0) m)
                                              (HybConcSem (Some (S n)) m) (match_state (S n)).
    Proof.
      intros n.
    Admitted.
    
    Lemma compile_n_threads:
      forall n m,
        HybridMachine_simulation.HybridMachine_simulation_properties
          (HybConcSem (Some 0) m)
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
             ThreadPool (Some 0) -> mem ->
             ThreadPool None -> mem -> Prop:=
   | Build_infty_match:
       forall n cd j st0 m0 stn mn st,
         match_state n cd j st0 m0 stn mn ->
         lift_state (Some n) stn None st ->
         infty_match cd j st0 m0 st mn.


   Lemma initial_infty:
          forall (m : option mem) (s_mem s_mem' : mem) 
                 (main : val) (main_args : list val)
                 (s_mach_state : ThreadPool (Some 0)) (r1 : option res),
            machine_semantics.initial_machine (HybConcSem (Some 0) m) r1
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
                 (U : list nat) tr1 (st1 : ThreadPool (Some 0)) 
                 (m1 : mem) (st1' : ThreadPool (Some 0)) 
                 (m1' : mem),
            machine_semantics.thread_step (HybConcSem (Some 0) m) sge U st1
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
                 (st1 : ThreadPool (Some 0)) (m1 : mem) (U' : list nat)
                 (tr1' : HybridMachineSig.event_trace)
                 (st1' : ThreadPool (Some 0)) (m1' : mem),
            machine_semantics.machine_step (HybConcSem (Some 0) m) sge U tr1
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
                 (U : list nat) (c1 : ThreadPool (Some 0)) 
                 (m1 : mem) (c2 : ThreadPool None) (m2 : mem) 
                 (v1 : val),
            infty_match cd mu c1 m1 c2 m2 ->
            machine_semantics.conc_halted (HybConcSem (Some 0) m) U c1 =
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
                 (c1 : ThreadPool (Some 0)) (m1 : mem) (c2 : ThreadPool None)
                 (m2 : mem),
            infty_match cd mu c1 m1 c2 m2 ->
            forall i : nat,
              machine_semantics.running_thread (HybConcSem (Some 0) m) c1 i <->
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
          (HybConcSem (Some 0) m)
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

 Section TrivialSimulations.
   Lemma trivial_clight_simulation:
   (HybridMachine_simulation
    (ClightMachine.DMS.ClightConcurSem(ge:=Clight_g)
       (Genv.init_mem (Ctypes.program_of_program C_program)))
    (HybConcSem (Some 0) (Genv.init_mem (Ctypes.program_of_program C_program)))).
   Admitted.
   Lemma trivial_asm_simulation:
     (HybridMachine_simulation
        (HybConcSem None (Genv.init_mem Asm_program))
        (X86Context.AsmConcurSem
           (the_program:=Asm_program)
           (Hsafe:=Asm_genv_safe)
           (Genv.init_mem Asm_program))).
   Admitted.
   End TrivialSimulations.


 (* NOTE: This section could be moved to where the simulations are defined. *) 
 Section SimulationTransitivity.
   Lemma HBSimulation_transitivity:
     forall G1 G2 G3 TID SCH C1 C2 C3 res,
     forall (Machine1 : @machine_semantics.ConcurSemantics G1 TID SCH _ C1 mem res)
       (Machine2 : @machine_semantics.ConcurSemantics G2 TID SCH _ C2 mem res)
       (Machine3 : @machine_semantics.ConcurSemantics G3 TID SCH _ C3 mem res),
     HybridMachine_simulation Machine1 Machine2 -> 
     HybridMachine_simulation Machine2 Machine3 ->
     HybridMachine_simulation Machine1 Machine3.
   Proof.
    destruct 1 as [index1 match_state1 SIM1].
    destruct 1 as [index2 match_state2 SIM2].
    eapply Build_HybridMachine_simulation with (index := (index1 * index2)%type)
      (match_state := fun a j c1 m1 c3 m3 => exists j1 j2 c2 m2, j = compose_meminj j1 j2 /\
         match_state1 (fst a) j1 c1 m1 c2 m2 /\ match_state2 (snd a) j2 c2 m2 c3 m3).
    inversion SIM1; inversion SIM2; econstructor.
    - apply Coqlib.wf_lex_ord; eauto.
    - intros.
      destruct (initial_setup _ _ _ _ _ _ H) as (? & ? & ? & ? & ? & ? & H2 & ?).
      destruct (initial_setup0 _ _ _ _ _ _ H2) as (? & ? & ? & ? & ? & ? & ? & ?).
      eexists; eexists (_, _); eauto 12.
    - intros.
      (* Where should the second ge come from?
      destruct (thread_diagram _ _ _ _ _ _ _ H _ _ _ _ H0) as (? & ? & ? & ? & ? & ?). *)
      admit.
(*      edestruct thread_diagram0 as (? & ? & ? & ? & ? & ?); eauto.*)
    - intros.
      (* Where should the second ge come from?
      destruct (machine_diagram _ _ _ _ _ _ _ _ _ _ H _ _ _ _ H0) as (? & ? & ? & ? & ? & ?). *)
      admit.
    - intros ???????? (? & ? & ? & ? & ? & ? & ?) ?.
      edestruct thread_halted; eauto.
    - intros ?????? (? & ? & ? & ? & ? & ? & ?) ?.
      erewrite thread_running; eauto.
   Admitted.
 End SimulationTransitivity.
 
(*  Lemma ConcurrentCompilerCorrectness:
    forall (p:Clight.program) (tp:Asm.program),
      CC_correct.CompCert_compiler p = Some tp ->
      forall asm_genv_safety,
        ConcurrentCompilerCorrectness_specification
          (Clight.globalenv p) tp asm_genv_safety
          (Genv.init_mem (Ctypes.program_of_program p)) (Genv.init_mem tp)
  .
  Proof.
    unfold ConcurrentCompilerCorrectness_specification.
    intros.
    apply CC_correct.simpl_clight_semantic_preservation in H.
    unfold ClightMachine.ClightMachine.DMS.ClightConcurSem, HybridMachineSig.HybridMachineSig.ConcurMachineSemantics, ClightMachine.ClightMachine.DMS.ClightMachine, HybridMachineSig.HybridMachineSig.HybridCoarseMachine.HybridCoarseMachine.
    econstructor.
 *)
 End ThreadedSimulation.
End ThreadedSimulation.

Module Concurrent_correctness (CC_correct: CompCert_correctness).
  Module TSim:= (ThreadedSimulation CC_correct).
  Import TSim.

  Lemma initial_memories_are_equal:
              forall (p : Clight.program) (tp : Asm.program),
                Genv.init_mem tp = Genv.init_mem (Ctypes.program_of_program p).
        Proof.
          intros p tp.
        Admitted.
  
  Lemma ConcurrentCompilerCorrectness:
    forall (p:Clight.program) (tp:Asm.program),
      CC_correct.CompCert_compiler p = Some tp ->
      forall asm_genv_safety,
        ConcurrentCompilerCorrectness_specification
          (Clight.globalenv p) tp asm_genv_safety
          (Genv.init_mem (Ctypes.program_of_program p)) (Genv.init_mem tp)
  .
  Proof.
    unfold ConcurrentCompilerCorrectness_specification.
    intros.
    eapply HBSimulation_transitivity; eauto.
    - eapply trivial_clight_simulation; eauto.
    -
      eapply HBSimulation_transitivity.
      + eauto.
      + eauto.
      + econstructor.
        eapply compile_all_threads.
      + replace (Genv.init_mem (Ctypes.program_of_program p)) with (Genv.init_mem tp) by
            eapply initial_memories_are_equal.
        eapply trivial_asm_simulation; eauto.
        
      Unshelve. auto.
  Qed.

        
End Concurrent_correctness.
