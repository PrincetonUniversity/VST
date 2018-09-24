Require Import compcert.common.AST.
Require Import Coq.omega.Omega.
Require Import Clight.
Require Import Memory.
Require Import Values.
Require Import Globalenvs.

Require Import Coq.Classes.Morphisms.

Require Import compcert.driver.Compiler.
Require Import compcert.lib.Coqlib.

Require Import msl.Coqlib2.

Require veric.Clight_core. Import Clight_core.

Require Import Smallstep.
Require Import ExposedSmallstep.
Require Import VST.concurrency.SantiagosTactics.
Require Import VST.concurrency.MemoryEquivalences.
Require Import VST.concurrency.x86_context.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.HybridMachine_simulation.
(*Require Import VST.concurrency.compiler_correct.*)
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.self_simulation.

(*
Require Import VST.concurrency.Clight_self_simulation.
Require Import VST.concurrency.Asm_self_simulation.
*)

Require Import VST.concurrency.common.permissions.

(*This should be removed, change for some _core.v *)
Require Import VST.concurrency.ClightCoreSemantincsForMachines.

Set Bullet Behavior "Strict Subproofs".

(** *These are all the possible external calls:*)


Section HybridProofs.

  Variable p: program.
  Variable tp: ia32.Asm.program. 
  Variable compiled: (simpl_transf_clight_program p = Errors.OK tp).

  Definition Clight_semantics2 (p: program) : semantics:=
    Clight.semantics2 p.

  Definition Asm_semantics (tp: Asm.program) : semantics:=
    Asm.semantics tp.

  
  Definition Sems:= ClightSEM_rec.
  Definition Semt:= X86SEM_rec. 


Section OneThreadCompiled.
  Variable (hb': nat).
  Notation hb1:= (Some hb').
  Notation hb2:= (Some (S hb')).
  Variable U: seq.seq nat.
  
  Notation C1:= (t_ (HybridMachine.ThreadPool hb1 Sems Semt)).
  Notation C2:= (t_ (HybridMachine.ThreadPool hb2 Sems Semt)).
  Notation G1:= (semG (HybridMachine.Sem hb1 Sems Semt)) .
  Notation G2:= (semG (HybridMachine.Sem hb2 Sems Semt)).

  (*The two following globals must be taken from the program...*)


  (*and they are probaly the smae global??? *)
  Definition genvS:= Clight.globalenv p.
  Definition genvT:= (Genv.globalenv tp).
  Definition genv:= (genvS, genvT).

  
  Section OneThreadCompiledProofs.

    (* we extract match_source from the self_simulation of Clight*)

    Parameter Clight_core_inject: meminj -> CC_core -> CC_core -> Prop.
    Parameter Clight_self_simulation:
      self_simulation (Clight.semantics2 p) _ CC_core_to_CC_state.
    Definition code_inject_source:=
      match_self (code_inject Clight_self_simulation).
    Parameter Asm_core_inject: meminj -> Asm.regset -> Asm.regset -> Prop.
    Parameter Asm_self_simulation:
      self_simulation (Asm_semantics tp) _ (Asm.State).  
    Definition code_inject_target:=
      match_self (code_inject Asm_self_simulation).
    

    Instance mem_Proper_match_perm_image:
      Proper (eq ==> mem_equiv ==> mem_equiv ==> iff) perm_image.
    Proof.
      proper_iff_tac; intros; subst.
      intros ??; rewrite <- H0; eapply H2.
    Qed.
    Instance mem_Proper_match_perm_preimage:
      Proper (eq ==> mem_equiv ==> mem_equiv ==> iff) perm_preimage.
    Proof.
      proper_iff_tac; intros; subst.
      intros ???; rewrite <- H1 in *.
      destruct (H2 _ _ H) as (b1 & delta & ofs & ?).
      do 3 eexists.
      rewrite <- H0; eauto.
    Qed.

    Instance mem_Proper_match_mem:
        Proper (eq ==> mem_equiv ==> mem_equiv ==> iff) match_mem.
      Proof.
        proper_iff_tac; intros; subst.
        inversion H2.
        econstructor; eauto;
          rewrite <- H0, <- H1; auto.
      Qed.
    
    Instance mem_Proper_code_inject_target:
      Proper (eq ==> eq ==> mem_equiv ==> eq ==> mem_equiv ==> iff) code_inject_target.
    Proof.
      proper_iff_tac; intros; subst.
      econstructor; try rewrite <- H1, <- H3;
        ez_eapply code_inject_target.
    Qed.

    
    Instance mem_Proper_code_inject_source:
      Proper (eq ==> eq ==> mem_equiv ==> eq ==> mem_equiv ==> iff) code_inject_source.
    Proof.
      proper_iff_tac; intros; subst.
      econstructor; try rewrite <- H1, <- H3;
        ez_eapply code_inject_source.
    Qed.
                      
                        
                  
                  
          
    
    
    (* Definition code_inject_source:=
      self_simulation.code_inject _ _ (Clight_self_simulation p). *)

    (* we extract match_target from the self_simulation of Asm*)
    (*Definition code_inject_target:=
      self_simulation.code_inject _  _ (Asm_self_simulation tp).*)
    Definition make_state_Clight: CC_core -> mem -> Clight.state:=
      CC_core_to_CC_state.
    Definition get_state_Clight c:=
      fst (CC_state_to_CC_core c).
    Definition make_state_Asm
              (reg: X86Machines.ErasedMachine.ThreadPool.code)
              (m: mem): ia32.Asm.state:=
      ia32.Asm.State reg m.
    Definition get_state_Asm (st:Asm.state): X86Machines.ErasedMachine.ThreadPool.code:=
      match st with
        Asm.State reg _ => reg
      end.

    
    Definition compiler_simulation: fsim_properties_inj ( Clight.semantics2 p) (ia32.Asm.semantics tp)
                                                        ( Clight.get_mem) (ia32.Asm.get_mem):=
    simpl_clight_semantic_preservation p tp compiled.
    
    Definition compiler_index := Injindex compiler_simulation.
    Definition compiler_order := Injorder compiler_simulation.
    Definition compiler_match := Injmatch_states compiler_simulation.
    
    Definition match_compiled_states :=
      fun i f c1 m1 c2 m2 =>
        exists c1' m1' c2' m2' f1 f12 f2,
          code_inject_source f1 c1 m1 c1' m1' /\
          compiler_match i f12 (make_state_Clight c1' m1') (make_state_Asm c2' m2') /\
          code_inject_target f2 c2 m2 c2' m2' /\
          inject_incr (compose_meminj f1 (compose_meminj f12 f2)) f.
    Notation source_match f st1 m1 st2 m2 :=
      (code_inject_source f st1 m1 st2 m2).
    Notation target_match f st1 m1 st2 m2 :=
      (code_inject_target f st1 m1 st2 m2).
          
Section OneThreadCompiledMatch.

  Definition HM1:=HybridMachine hb1 Sems Semt.
  Definition HM2:=HybridMachine hb2 Sems Semt.

  Notation Sem1:=(ConcurMachineSemantics _ _ _ HM1 U None).
  Notation Sem2:=(ConcurMachineSemantics _ _ _ HM2 U None) .

  Inductive condition: Set :=
    running | blocked | resuming | initializing.

  Definition get_condition {cT} (c:@ctl cT):=
    match c with
    | Krun _ => running
    | Kblocked _ => blocked
    | Kresume _ _ => resuming
    | Kinit _ _ =>  initializing
    end.

  Definition get_state_inside {cT} (c:@ctl cT):=
    match c with
    | Krun c => Some c
    | Kblocked c => Some c
    | Kresume c _ => Some c
    | Kinit _ _ =>  None
    end.

  (*This will probably need reworking*)

  Lemma same_length_contains:
    forall {ms1: C1} {ms2: C2} {i},
      num_threads ms1 = num_threads ms2 ->
      containsThread ms1 i ->
      containsThread ms2 i.
  Proof.
    intros ? ? ? H; unfold containsThread.
    rewrite H; trivial.
  Qed.
  
  Notation CoreSem Sem :=(semantics.csem(event_semantics.msem (semSem Sem))).

  Inductive match_thread_source:
    meminj -> @ctl (state_sum (semC Sems) (semC Semt)) -> mem -> @ctl (state_sum (semC Sems) (semC Semt)) -> mem -> Prop  :=
  | SThread_Running: forall j code1 m1 code2 m2,
      source_match j code1 m1 code2 m2 ->
      match_thread_source
        j (Krun (SState _ _ code1)) m1
        (Krun (SState _ _ code2)) m2
  | SThread_Blocked: forall j code1 m1 code2 m2 ls1 ls2 f f',
      semantics.at_external (CoreSem Sems) genvS code1 m1 = Some (f,ls1) ->
      semantics.at_external (CoreSem Sems) genvS code2 m2 = Some (f',ls2) ->
      Val.inject_list j ls1 ls2 ->
      source_match j code1 m1 code2 m2 ->
      match_thread_source  j (Kblocked (SState _ _ code1)) m1
                          (Kblocked (SState _ _ code2)) m2
  | SThread_Resume: forall j code1 m1 code2 m2 ls1 ls2 f f' v v' code1' code2',
      (*Do I need to keep this two? Probanly not*)
    semantics.at_external (CoreSem Sems) genvS code1 m1 = Some (f,ls1) ->
    semantics.at_external (CoreSem Sems) genvS code2 m2 = Some (f',ls2) ->
    Val.inject_list j ls1 ls2 ->
    semantics.after_external (CoreSem Sems) genvS None code1 = Some code1' ->
    semantics.after_external (CoreSem Sems) genvS None code2 = Some code2' ->
    source_match j code1' m2 code2' m2 ->
    match_thread_source j (Kresume (SState _ _ code1) v) m1
                        (Kresume (SState _ _ code2) v') m2
| SThread_Init: forall j m1 m2 v1 v1' v2 v2',
    Val.inject j v1 v2 ->
    Val.inject j v1' v2' ->
    match_thread_source j (Kinit v1 v1') m1
                        (Kinit v2 v2') m2.

  Inductive match_thread_target :
    meminj -> @ctl (state_sum (semC Sems) (semC Semt)) -> mem -> @ctl (state_sum (semC Sems) (semC Semt)) -> mem -> Prop  :=
  | TThread_Running: forall j code1 m1 code2 m2,
      target_match j code1 m1 code2 m2 ->
      match_thread_target  j (Krun (TState _ _ code1)) m1
                          (Krun (TState _ _ code2)) m2
  | TThread_Blocked: forall j code1 m1 code2 m2 ls1 ls2 f f',
      semantics.at_external (CoreSem Semt) genvT code1 m1 = Some (f,ls1) ->
      semantics.at_external (CoreSem Semt) genvT code2 m2 = Some (f',ls2) ->
      Val.inject_list j ls1 ls2 ->
      target_match j code1 m1 code2 m2 ->
      match_thread_target j (Kblocked (TState _ _ code1)) m1
                          (Kblocked (TState _ _ code2)) m2
  | TThread_Resume: forall j code1 m1 code2 m2 ls1 ls2 f f' v v' code1' code2',
      (*Do I need to keep this two? Probanly not*)
      semantics.at_external (CoreSem Semt) genvT code1 m1 = Some (f,ls1) ->
      semantics.at_external (CoreSem Semt) genvT code2 m2 = Some (f',ls2) ->
      Val.inject_list j ls1 ls2 ->
      semantics.after_external (CoreSem Semt) genvT None code1 = Some code1' ->
      semantics.after_external (CoreSem Semt) genvT None code2 = Some code2' ->
      target_match j code1' m2 code2' m2 ->
      match_thread_target j (Kresume (TState _ _ code1) v) m1
                          (Kresume (TState _ _ code2) v') m2
  | TThread_Init: forall j m1 m2 v1 v1' v2 v2',
      Val.inject j v1 v2 ->
      Val.inject j v1' v2' ->
      match_thread_target j (Kinit v1 v1') m1
                          (Kinit v2 v2') m2.

  (* match_compiled_states *)
  
  Inductive match_thread_compiled:
    compiler_index -> meminj ->
    @ctl (state_sum (semC Sems) (semC Semt)) -> mem ->
    @ctl (state_sum (semC Sems) (semC Semt)) -> mem -> Prop  :=
  | CThread_Running: forall cd j code1 m1 code2 m2,
      match_compiled_states cd j code1 m1 code2 m2 ->
      match_thread_compiled cd j (Krun (SState _ _ code1)) m1
                            (Krun (TState _ _ code2)) m2
  | CThread_Blocked: forall cd j code1 m1 code2 m2 ls1 ls2 f f',
      semantics.at_external (CoreSem Sems) genvS code1 m1  = Some (f,ls1) ->
      semantics.at_external (CoreSem Semt) genvT code2 m2 = Some (f',ls2) ->
      Val.inject_list j ls1 ls2 ->
      match_compiled_states cd j code1 m1 code2 m2 ->
      match_thread_compiled  cd j (Kblocked (SState _ _ code1)) m1
                            (Kblocked (TState _ _ code2)) m2
  | CThread_Resume: forall cd j code1 m1 code2 m2 ls1 ls2 f f' v v' code1' code2',
      (*Do I need to keep this two? Probanly not*)
      semantics.at_external (CoreSem Sems) genvS code1 m1 = Some (f,ls1) ->
      semantics.at_external (CoreSem Semt) genvT code2 m2 = Some (f',ls2) ->
      Val.inject_list j ls1 ls2 ->
      semantics.after_external (CoreSem Sems) genvS None code1 = Some code1' ->
      semantics.after_external (CoreSem Semt) genvT None code2 = Some code2' ->
      match_compiled_states cd j code1' m1 code2' m2 ->
      match_thread_compiled cd j (Kresume (SState _ _ code1) v) m1
                            (Kresume (TState _ _ code2) v') m2
  | CThread_Init: forall cd j m1 m2 v1 v1' v2 v2',
      Val.inject j v1 v2 ->
      Val.inject j v1' v2' ->
      match_thread_compiled cd j (Kinit v1 v1') m1
                            (Kinit v2 v2') m2.

  Definition FST {A B} (HH : A /\ B):=
    fst (ssrfun.pair_of_and HH).

  Definition SND {A B} (HH : A /\ B):=
    snd (ssrfun.pair_of_and HH).
  
(*
  Definition FST {A B} (HH : A /\ B) : A:=
    match HH with
    | conj H _ => H
    end. *)

  

  Record concur_match (ocd: option compiler_index)
       (j:meminj) (cstate1: C1) (m1: mem) (cstate2: C2) (m2: mem):=
  { same_length: num_threads cstate1 = num_threads cstate2
    ; memcompat1: HybridMachine.mem_compatible _ _ _ cstate1 m1
    ; memcompat2: HybridMachine.mem_compatible _ _ _ cstate2 m2
    ; mtch_source:
        forall (i:nat),
          (i > hb')%nat ->
          forall (cnti1: containsThread cstate1 i)
            (cnti2: containsThread cstate2 i),
          match_thread_source  j
                              (getThreadC cnti1)
                              (restrPermMap (FST (memcompat1 i cnti1)))
                              (getThreadC cnti2)
                              (restrPermMap (FST (memcompat2 i cnti2)))
    ; mtch_target:
        forall (i:nat),
          (i < hb')%nat ->
          forall (cnti1: containsThread cstate1 i)
            (cnti2: containsThread cstate2 i),
          match_thread_target  j
                              (getThreadC cnti1)
                              (restrPermMap (FST(memcompat1 i cnti1)))
                              (getThreadC cnti2)
                              (restrPermMap (FST(memcompat2 i cnti2)))
    ; mtch_compiled:
        forall (i:nat),
          (i = hb')%nat ->
          forall (cnti1: containsThread cstate1 i)
            (cnti2: containsThread cstate2 i),
            exists cd, ocd = Some cd /\
          match_thread_compiled cd j
                                (getThreadC cnti1)
                                (restrPermMap (FST(memcompat1 i cnti1)))
                                (getThreadC cnti2)
                                (restrPermMap (FST(memcompat2 i cnti2))) }.

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

End OneThreadCompiledMatch.

Arguments same_length_contains {ms1 ms2}.
Arguments memcompat1 {ocd j cstate1 m1 cstate2 m2}.
Arguments memcompat2 {ocd j cstate1 m1 cstate2 m2}.
    
  Section HybridThreadDiagram.
    Notation the_simulation := compiler_simulation.

    Parameter option_compiler_order: option (Injindex the_simulation) -> option (Injindex the_simulation) -> Prop.

    (* automatic rewrite gsoThreadCode *)
    Ltac auto_gsoThreadCode:=
      match goal with
      | [ |- context[getThreadC ?cntJ'] ] =>
        match type of cntJ' with
        | containsThread (updThread ?cntI _ _) ?J =>
          match type of cntI with
          | containsThread ?hb ?I =>
            match goal with
            | [ cntJ: containsThread hb J |- _ ] => 
              rewrite gsoThreadCode with
                  (cnti:= cntI)
                  (cntj:= cntJ)
                  (cntj':= cntJ') by eassumption
            end
          end
        end  
      end.
    Ltac simpl_getThreadC':=
      first[ rewrite gssThreadCode |
             auto_gsoThreadCode
           ].

    (*Produces all the "containThreads" that might be missing "*)
    Ltac containsThread_helper:=
      match goal with
      | [ cntj': containsThread (updThread ?cntj _ _) ?i  |- _ ] =>
        match type of cntj with
        | containsThread ?hb ?j =>
          progress (
              first [match goal with
                     | [ cnti: containsThread hb i |- _ ] => idtac
                     end |
                     let CNTI:= fresh "cnti" in
                     assert (CNTI: containsThread hb i)
                       by
                         (eapply cntUpdate'; eapply cntj') ])
        | _ => fail
        end 
      end.
    
    Ltac simpl_getThreadC:=
      match goal with
      | [  |- context [@getThreadC _ _ ?j (@updThread _ _ _ ?hb _ _ _) _ ] ] =>
        let cntJ:= fresh "cntj" in
        evar (cntj : containsThread hb j);
        let cntJ':= eval unfold cntJ in cntJ in
            rewrite gsoThreadCode with
            (tp := hb)
            (cntj:= cntJ')
          by eassumption;
                                        instantiate (cntJ:= ltac:(eauto));
                                        clear cntJ
      end.
    
    Ltac containsThread_cleanup:=
      repeat match goal with
             | [H1: containsThread ?TP ?M,
                    H2: containsThread (@updThread _ _ _ ?TP _ _ _) ?M |- _] =>
               replace H2 with H1 in * by apply proof_irr; clear H2
             | [H1: containsThread ?TP ?M,
                    H2: containsThread ?TP ?M |- _] =>
               replace H2 with H1 in * by apply proof_irr; clear H2
             end.

    Lemma mem_step_same_visible:
                  forall hb Sems Semt i j tp1 tp2 m1 m2
                    (cnti1: containsThread tp1 i)
                    (cntj1: containsThread tp1 j)
                    (cnti2: containsThread tp2 i)
                  (compat1: HybridMachine.mem_compatible hb Sems Semt tp1 m1)
                  (compat2: HybridMachine.mem_compatible hb Sems Semt tp2 m2),
                    j <> i ->
                    semantics.mem_step (restrPermMap (FST (compat1 j cntj1))) m2 ->
                  same_visible (restrPermMap (FST (compat1 i cnti1)))
                               (restrPermMap (FST (compat2 i cnti2))).
                Proof.
                  (*SKETCH:
                   * mem_step ensures only writable memory is modified.
                   * mem_compatible (compat1) ensures that the writable memory 
                   * for thread j is disjoint from the visible memory for thread i
                   * Concluding that visible memory for i is unmodified.  
                   *)
                Admitted.
                
                Lemma match_thread_source_same_vis:
                  forall f f' m1 m1' m2 m2' cs ct,
                  same_visible m1 m1' ->
                  same_visible m2 m2' ->
                   is_ext f (Mem.nextblock m1) f' (Mem.nextblock m2) ->
                  match_thread_source f cs m1 ct m2 ->
                  match_thread_source f' cs m1' ct m2'.
                Proof.
                  (*SKETCH:
                   * There are some holes with regards to at_ext and after_ext
                   * Otherwise, source_match is invariant under changes to non_visible memory.
                   *)
                Admitted.
                Lemma match_thread_compiled_same_vis:
                  forall f f' m1 m1' m2 m2' cs ct cd,
                  same_visible m1 m1' ->
                  same_visible m2 m2' ->
                  is_ext f (Mem.nextblock m1) f' (Mem.nextblock m2) ->
                  match_thread_compiled cd f cs m1 ct m2 ->
                  match_thread_compiled cd f' cs m1' ct m2'.
                Proof.
                  (*SKETCH:
                   * There are some holes with regards to at_ext and after_ext
                   * Otherwise, source_match is invariant under changes to non_visible memory.
                   *)
                Admitted.
                Lemma match_thread_target_same_vis:
                  forall f f' m1 m1' m2 m2' cs ct,
                  same_visible m1 m1' ->
                  same_visible m2 m2' ->
                   is_ext f (Mem.nextblock m1) f' (Mem.nextblock m2) ->
                  match_thread_target f cs m1 ct m2 ->
                  match_thread_target f' cs m1' ct m2'.
                Proof.
                  (*SKETCH:
                   * There are some holes with regards to at_ext and after_ext
                   * Otherwise, source_match is invariant under changes to non_visible memory.
                   *)
                Admitted.

                
            Lemma mem_step_compatible:
                forall hb1 Sems Semt c m m' code_i i
                  (cnti: containsThread c i) 
                  (Hcmpt1: HybridMachine.mem_compatible hb1 Sems Semt c m),
                  semantics.mem_step (restrPermMap (FST (Hcmpt1 i cnti))) m'->
                  HybridMachine.mem_compatible hb1 Sems Semt
                                               (updThread cnti
                                                          code_i
                                                          (getCurPerm m', (snd (getThreadR cnti)))) m'.
            Admitted.
            Lemma gss_restrPermMap:
              forall Sems Semt hb i (tp: t_ (ThreadPool hb Sems Semt)) m c
                (cnti: containsThread tp i)
                (COMPT: HybridMachine.mem_compatible hb Sems Semt
                        (updThread cnti c (getCurPerm m, snd (getThreadR cnti))) m),
                mem_equiv (restrPermMap (FST (COMPT i cnti))) m.
            Proof.
              intros; constructor.
              - intros.
                pose proof (restrPermMap_contents (FST (COMPT i cnti))).
                unfold juicy_mem.contents_at in H.
                match type of H with
                  ?LHS = ?RHS =>
                  let lhs:= fresh lhs in
                  remember LHS as lhs;
                    let rhs:= fresh rhs in
                    remember RHS as rhs;
                      assert (forall b ofs,
                                 (lhs) (b, ofs) = (rhs) (b,ofs))
                      by (intros; rewrite H; reflexivity);
                      subst lhs rhs
                end.
                apply H0.
              - intros.
                destruct kind.
                + pose proof (restrPermMap_Max (FST (COMPT i cnti))) as HH.
                  unfold permission_at in HH; rewrite HH; auto.
                  rewrite getMaxPerm_correct; reflexivity.
                + pose proof (restrPermMap_Cur (FST (COMPT i cnti))) as HH.
                  unfold permission_at in HH; rewrite HH.
                  cbv delta[getThreadR_ ThreadPool OrdinalThreadPool_rec] zeta iota beta.
                  simpl.
                  match goal with
                  | [ |- context[if ?DEC then _ else _] ] =>
                    destruct DEC eqn:DECC
                  end.
                  * simpl; rewrite getCurPerm_correct; reflexivity.
                  * clear -DECC; exfalso.
                    unfold eqtype.eq_op,eqtype.Equality.op in DECC; simpl in DECC.
                    rewrite <- ssrnat.eqnE in DECC.
                    pose proof (@ssrnat.eqnP i i) as HH.
                    rewrite DECC in HH.
                    inversion HH.
                    apply H; auto.
              - reflexivity.
            Qed.
            Lemma concur_stable_thread_step_target:
              forall  cd f (c1:C1) m1 c2 m2 f' ts1' m1' ts2' m2' tid,
              forall (Htid1: containsThread c1 tid)
                (Htid2: containsThread c2 tid)
                (LT : (tid < hb')%nat)
                (Hcmpt1: HybridMachine.mem_compatible hb1 Sems Semt c1 m1)
                (Hcmpt2: HybridMachine.mem_compatible hb2 Sems Semt c2 m2),
                concur_match cd f c1 m1 c2 m2 ->
                is_ext f (Mem.nextblock m1) f' (Mem.nextblock m2) ->
                semantics.mem_step (restrPermMap (FST (Hcmpt1 _ Htid1))) m1' ->
                semantics.mem_step (restrPermMap (FST (Hcmpt2 _ Htid2))) m2' ->
                match_self (code_inject Asm_self_simulation) f' ts1' m1' ts2' m2' ->
                concur_match cd f'
                             (updThread Htid1  (Krun (TState _ _ ts1')) (getCurPerm m1', (snd (getThreadR Htid1))))  m1'
                             (updThread Htid2 (Krun (TState _ _ ts2')) (getCurPerm m2', (snd (getThreadR Htid2)))) m2'.
            Proof.
              (*Oct 9: Sketching the proof... *)
              intros.
              (*First set up some results *)
              remember (updThread Htid1 (Krun (TState (semC Sems) Asm.regset ts1'))
                                  (getCurPerm m1', (snd (getThreadR Htid1)))) as cstates1'.
              remember (updThread Htid2 (Krun (TState (semC Sems) Asm.regset ts2'))
                                  (getCurPerm m2', (snd(getThreadR Htid2)))) as cstates2'.
              assert (SAME: num_threads cstates1' = num_threads cstates2') by (subst; apply H).
              assert (COMPAT1: HybridMachine.mem_compatible hb1 Sems Semt cstates1' m1').
              subst cstates1'.
              (*mem_step preserves coherence *)
              
              eapply mem_step_compatible; eauto.
              assert (COMPAT2:HybridMachine.mem_compatible hb2 Sems Semt cstates2' m2').
              subst cstates2'.
              eapply mem_step_compatible; eauto.
              eapply (Build_concur_match _ _ _ _ _ _ SAME COMPAT1 COMPAT2).
              (*In each of the following cases, one should look at {i = tid} + {i <> tid}*)
              - (* (i > hb') *)
                intros.
                assert (tid <> i) by omega.
                
                subst.
                repeat containsThread_helper.
                assert (cnti1 = cnti0) by apply proof_irr.
                subst cnti1.
                assert (cnti2 = cnti) by apply proof_irr.
                subst cnti2.
                do 2 simpl_getThreadC.
                
                eapply match_thread_source_same_vis.

                {
                eapply mem_step_same_visible.
                + eassumption.
                + eapply H1.
                }
                {  
                eapply mem_step_same_visible.
                + eassumption.
                + eapply H2.
                }
                eauto.
                
                assert (Hcmpt1 = memcompat1 H) by apply proof_irr; subst Hcmpt1.
                assert (Hcmpt2 = memcompat2 H) by apply proof_irr; subst Hcmpt2.
                eapply H; auto.
                
                
              - (* (i < hb') *)
                intros.
                destruct (NPeano.Nat.eq_dec i tid).
                
                + (* i = tid *)
                  subst tid.
                  subst cstates1' cstates2'.
                  do 2 rewrite gssThreadCode.
                  econstructor.
                  clear - H3.
                  fold code_inject_target in H3.
                  
                  dup COMPAT1.
                  containsThread_cleanup.
                  do 2 rewrite gss_restrPermMap; auto.

                  
                + (* i <> tid *)
                  assert (tid <> i) by omega.

                  subst.
                  repeat containsThread_helper.
                  assert (cnti1 = cnti0) by apply proof_irr.
                  subst cnti1.
                  assert (cnti2 = cnti) by apply proof_irr.
                  subst cnti2.
                  do 2 simpl_getThreadC.
                  
                  eapply match_thread_target_same_vis.
                  

                  
                {
                eapply mem_step_same_visible.
                + eassumption.
                + eapply H1.
                }
                {  
                eapply mem_step_same_visible.
                + eassumption.
                + eapply H2.
                }
                eauto.
                
                assert (Hcmpt1 = memcompat1 H) by apply proof_irr; subst Hcmpt1.
                assert (Hcmpt2 = memcompat2 H) by apply proof_irr; subst Hcmpt2.
                eapply H; auto.
                  
              - (* (i = hb') *)
                intros.
                assert (tid <> i) by omega.

                subst.
                repeat containsThread_helper.
                assert (cnti1 = cnti) by apply proof_irr.
                subst cnti1.
                assert (cnti2 = cnti0) by apply proof_irr.
                subst cnti2.
                do 2 simpl_getThreadC.

                exploit (mtch_compiled _ _ _ _ _ _ H).
                reflexivity.
                intros [cd' [? ?]].
                exists (cd'); split; eauto.
                
                eapply match_thread_compiled_same_vis.
                {
                eapply mem_step_same_visible.
                + eassumption.
                + eapply H1.
                }
                {  
                eapply mem_step_same_visible.
                + eassumption.
                + eapply H2.
                }
                eauto.

                assert (Hcmpt1 = memcompat1 H) by apply proof_irr; subst Hcmpt1.
                assert (Hcmpt2 = memcompat2 H) by apply proof_irr; subst Hcmpt2.

                eapply H6.
            Qed.
            Lemma Asm_mem_semantics:
              forall genv c1 m1 t c2 m2
                (Astep: Asm.step genv (Asm.State c1 m1) t (Asm.State c2 m2)),
                semantics.mem_step m1 m2.
            Proof. intros. 
            Admitted.
            
            
                
    Lemma hybrid_thread_diagram:
      forall (U0 : list nat) (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
        machine_semantics.thread_step (HCSem Sems Semt hb1 U) genv U0 st1 m1 st1' m1' ->
        forall cd (st2 : C2) (mu : meminj) (m2 : mem),
          concur_match cd mu st1 m1 st2 m2 ->
          exists (st2' : C2) (m2' : mem) cd' (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            (machine_semantics_lemmas.thread_step_plus
               (HCSem Sems Semt hb2 U) genv U0 st2 m2 st2' m2' \/
             machine_semantics_lemmas.thread_step_star
               (HCSem Sems Semt hb2 U) genv U0 st2 m2 st2' m2'
             /\ option_compiler_order cd' cd).
    Proof.
      intros.
      destruct U0; simpl in H.
      - inversion H; subst.
        inversion HschedN.
      - inversion H; subst.
        inversion HschedN; subst.
        destruct (Compare_dec.lt_eq_lt_dec (tid) hb') as [[LT | EQ] | LT ].
        
        + (* tid < hb' *)
          (*This case it's all in target (the step is in target?) *)
          assert (LT':=LT).
          inversion Htstep. subst tp' m' ev0.
          eapply event_semantics.ev_step_ax1 in Hcorestep.
          assert (MSTEP:= semantics.corestep_mem _ _ _ _ _ _ Hcorestep). 
          simpl in Hcorestep.
          simpl in Hcode.
          assert (cnti2: containsThread st2 tid).
          eapply same_length_contains; simpl in Htid; eauto; eapply H0.
          
          eapply H0 in LT.  
          
          instantiate (1:=cnti2) in LT.
          instantiate (1:=Htid) in LT.
          

          rewrite Hcode in LT.
          assert (Htid':= contains12 H0 Htid).
          inv LT. 
          

          rename H5 into SSIM.
          (*Use the source self_simulations*)
          inversion Hcorestep; subst.
          eapply (ssim_diagram) in SSIM; eauto; simpl in SSIM.
          2:{
            (*SHOW the step*)
            replace (memcompat1 H0) with Hcmpt by (apply proof_irr); simpl; eauto.
            clear - H4.
            
            unfold make_state_Asm.
            inversion H4;
              try solve[eapply Asm.exec_step_internal; eauto];
              try solve[eapply Asm.exec_step_builtin; eauto].
          }
          
          simpl in SSIM.
          destruct SSIM as [c2' [f' [t' [m2' [STEP [SMATCH [EXT TINJ]]]]]]].
         

        exists (@updThread_ _ _ _ _ st2 Htid'
                       (Krun (TState CC_core X86Machines.ErasedMachine.ThreadPool.code
                                     c2'))
                      (permissions.getCurPerm m2',
                       snd (getThreadR Htid'))).
        exists m2'.
        exists cd. (*This should be updated with the new value!*)
        exists f'; simpl.
        
        split.
          * (*Reestablish the match*)
            eapply concur_stable_thread_step_target; eauto.
            containsThread_cleanup.
            eapply Asm_mem_semantics; eauto.

          (*Prove the machine step*)
          * left.
            eapply machine_semantics_lemmas.thread_step_plus_one.
            econstructor; simpl; eauto.
            econstructor; eauto.
            -- admit. (*Invariant: going to need to add this to the match relation *)
            -- inversion TINJ; subst.
               econstructor; simpl. 
               instantiate (3 := (memcompat2 H0)).
               simpl in SMATCH.
               (*Have the step STEP, but have to show it's an internal step!*)
               (*This can be a lemma or an axiom of self-simulation*)
               admit.
               (*NOTE: acctually, look at ssim_diagram, used to get SSIM.*)
            (*And look at the SHOW the step proof above.  *)
               (* The simulation semantics should have the propery of mantaining*)
               (* internall-external steps *)
            -- simpl; repeat f_equal. apply proof_irr. apply proof_irr.

        
        + (* tid = hb' *)
          (* equal: one machine in source one in target!!*)
          inversion Htstep. subst tp' m' ev0.
          eapply event_semantics.ev_step_ax1 in Hcorestep.
          assert (MSTEP:= semantics.corestep_mem _ _ _ _ _ _ Hcorestep). 
          simpl in Hcorestep.
          assert (Hcode':= Hcode).
          simpl in Hcode.
          eapply H0 in EQ. 
          rewrite Hcode in EQ.
          assert (Htid':= contains12 H0 Htid).
          destruct EQ as [cd0 [cd_eq EQ]]; inv EQ.
          destruct H6 as (st1_ & m1_ & st2_ & m2_ &
                          f1 & f2 & f3 &
                          INJsrc & INJcomp & INJtgt &
                          compose).
          
          
          Lemma compiled_thread_diagram:
            forall (U0 : list nat) (st1 : C1) (m1 m1' : mem) (tid : nat)
                   (Htid : containsThread_ (ThreadPool hb1 Sems Semt) st1 tid) (c' : semC (Sem hb1 Sems Semt))
                   (st2 : C2) (mu : meminj) (m2 : mem) (cd0 : compiler_index)
                   (H0 : concur_match (Some cd0) mu st1 m1 st2 m2) (code1 : CC_core) 
                   (code2 : Asm.regset) (st1_ : CC_core) (m1_ : mem)
                   (st2_ : X86Machines.ErasedMachine.ThreadPool.code) (m2_ : mem) 
                   (f1 f2 f3 : meminj) cnti2,
              source_match f1 code1 (restrPermMap (FST ((memcompat1 H0) tid Htid))) st1_ m1_ ->
              compiler_match cd0 f2 (make_state_Clight st1_ m1_) (make_state_Asm st2_ m2_) ->
              target_match f3 code2
                           (restrPermMap
                              (FST
                                 ((memcompat2 H0) tid
                                                  cnti2))) st2_
                           m2_ ->
              exists (st2' : C2) (m2' : mem) (cd' : option compiler_index) (mu' : meminj),
                concur_match cd' mu'
                             (updThread_ (ThreadPool hb1 Sems Semt) Htid (Krun c')
                                         (getCurPerm m1', snd (getThreadR_ (ThreadPool hb1 Sems Semt) Htid))) m1' st2' m2' /\
                (machine_semantics_lemmas.thread_step_plus (HCSem Sems Semt hb2 U) genv 
                                                           (tid :: U0) st2 m2 st2' m2' \/
                 machine_semantics_lemmas.thread_step_star (HCSem Sems Semt hb2 U) genv 
                                                           (tid :: U0) st2 m2 st2' m2' /\ option_compiler_order cd' (Some cd0)).
          Proof.
            intros.
            
          
          
          (*LOOK HERE!!! *)
          (*Have to apply a self simulation, then the compiler simulation
            and then a self simulation again. *)
          admit. (*TODO: Make this a Lemma compiled_thread_diagram*)
          
       + (*hb' < tid*)
         (*This case it's all in source*)
         inversion Htstep. subst tp' m' ev0.
         eapply event_semantics.ev_step_ax1 in Hcorestep.
         assert (MSTEP:= semantics.corestep_mem _ _ _ _ _ _ Hcorestep).
         simpl in Hcorestep.
         simpl in Hcode.
         eapply H0 in LT. instantiate (1 := Htid) in LT.
         rewrite Hcode in LT.
         assert (Htid':= contains12 H0 Htid).
         inv LT. 
         
          (*Use the source self_simulations*)
          inversion Hcorestep; subst.
          eapply (ssim_diagram) in H5; eauto; simpl in H5.
          2:{
          replace (memcompat1 H0) with Hcmpt by (apply proof_irr); simpl; eauto.
          clear - H4.
          unfold make_state_Clight.
          unfold ClightCoreSEM.Sem in H4; rewrite ClightCoreSEM.CLC_msem in H4;
            simpl in H4.
          destruct H4; eauto.
          }
          
          simpl in H5.
          destruct H5 as [c2' [f' [t' [m2' [STEP [SMATCH [EXT TINJ]]]]]]].
         
        exists (@updThread_ _ _ _ _ st2 Htid'
                       (Krun (SState CC_core X86Machines.ErasedMachine.ThreadPool.code
                                     c2'))
                      (permissions.getCurPerm m2',
                       snd (getThreadR Htid'))).
        exists m2'.
        exists cd. (*This should be updated with the new value!*)
        exists f'; simpl.
        
        split.
        (*Reestablish the match*)
        Lemma concur_stable_thread_step_source:
              forall  cd f (c1:C1) m1 c2 m2 f' c1' m1' c2' m2' tid,
              forall (Htid1: containsThread c1 tid)
                (Htid2: containsThread c2 tid)
                (Hcmpt1: HybridMachine.mem_compatible hb1 Sems Semt c1 m1)
                (Hcmpt2: HybridMachine.mem_compatible hb2 Sems Semt c2 m2),
                concur_match cd f c1 m1 c2 m2 ->
                is_ext f (Mem.nextblock m1) f' (Mem.nextblock m2) ->
                semantics.mem_step (restrPermMap (Hcmpt1 _ Htid1)#1) m1' ->
                semantics.mem_step (restrPermMap (Hcmpt2 _ Htid2)#1) m2' ->
                match_self (code_inject Clight_self_simulation) f' c1' m1' c2' m2' ->
                concur_match cd f'
                             (updThread Htid1  (Krun (SState _ _ c1')) (getCurPerm m1', (getThreadR Htid1)#2))  m1'
                             (updThread Htid2 (Krun (SState _ _ c2')) (getCurPerm m2', (getThreadR Htid2)#2)) m2'.
            Admitted.
        eapply concur_stable_thread_step_source; eauto.
        
         -- admit. (*Follows from mem_sem and the step proven in the follwoing goal*)
        
        (*Prove the machine step*)
        -- left.
        eapply machine_semantics_lemmas.thread_step_plus_one.
        econstructor; simpl; eauto.
        econstructor; eauto.
         * admit. (*Invariant: going to need to add this to the match relation *)
         * econstructor; simpl. 
           instantiate (3 := (memcompat2 H0)).
           inversion TINJ; subst.
           (*Have the step STEP, but have to show it's an internal step!*)
           admit.
         * simpl; repeat f_equal. apply proof_irr. apply proof_irr.
    Admitted.
    
  End HybridThreadDiagram.

  Section MachineThreadDiagram.

    (*One threas takes a "machine step" (or synchronization-step) *)
    Lemma machine_thread_diagram:
      forall (U0 : seq.seq nat) (tr : seq.seq machine_event) (st1 : C1) 
    (m1 : mem) (U' : seq.seq nat) (tr' : seq.seq machine_event) (st1' : C1) 
    (m1' : mem),
        machine_semantics.machine_step (HCSem Sems Semt hb1 U) genv U0 tr st1 m1 U' tr' st1' m1' ->
        forall (cd : option (Injindex compiler_simulation)) (st2 : C2) (mu : meminj) (m2 : mem),
          concur_match cd mu st1 m1 st2 m2 ->
          exists (st2' : C2) (m2' : mem) (cd' : option (Injindex compiler_simulation)),
            concur_match cd' mu st1' m1' st2' m2' /\
            machine_semantics.machine_step (HCSem Sems Semt hb2 U) genv U0 tr st2 m2 U' tr' st2' m2'.
    Proof.
      intros.
      destruct U0 as [|i U0]; simpl in H.
      - inv H;
          match goal with
          | [ H: HybridMachine.schedPeek nil = Some _  |- _ ] => inv H
          end.
      - simpl in H; inv H. (*Case by case of all the sync_calls*)
        + (*start*)
          inv Htstep.
          simpl in Hinitial.
          admit. (*REVIEW*)
        + (*resume*)
          (*This should follow almost directly from the match!*)
          admit.
        + (*suspend*)
          intros.
          inv Htstep.
          assert (ctn':=contains12 H0 ctn).
          simpl in Hcode. 
          (*proof identical for all cases*)
          destruct (Compare_dec.lt_eq_lt_dec (tid) hb') as [[HH | HH] | HH ];
            (*In all cases discard non-running threads*)
            eapply H0 in HH; instantiate (1:= ctn) in HH;
              try (destruct HH as [cd' [cd_eq HH]]);
              inv HH;  rewrite Hcode in H; inv H.
          (*then instantitates the same thing*)
          * exists (updThreadC_ (ThreadPool hb2 Sems Semt) ctn' (Kblocked (TState ClightCoreSEM.C Asm.regset code2))), m2, cd; split.
            admit. (*reestablish the match (should be easy*)
            econstructor; eauto.
            admit. (* Add this to the match*)
            econstructor; eauto.
            admit. (* should follow from the simulations *)
            admit. (* Add this to the match? *)
          * exists (updThreadC_ (ThreadPool hb2 Sems Semt) ctn' (Kblocked (TState ClightCoreSEM.C Asm.regset code2))), m2, ( some cd'); split.
            admit. (*reestablish the match (should be easy*)
            econstructor; eauto.
            admit. (* Add this to the match*)
            econstructor; eauto.
            admit. (* should follow from the simulations *)
            admit. (* Add this to the match? *)
          * exists (updThreadC_ (ThreadPool hb2 Sems Semt) ctn' (Kblocked (SState ClightCoreSEM.C Asm.regset code2))), m2, cd; split.
            admit. (*reestablish the match (should be easy*)
            econstructor; eauto.
            admit. (* Add this to the match*)
            econstructor; eauto.
            admit. (* should follow from the simulations *)
            admit. (* Add this to the match? *)
        + (*sync*)
          inv Htstep.
          (*LOCK*)
          * inv HschedN.
            Lemma Lock_HybridStep_simulation:
              forall (U0 : seq.seq nat)
                (st1 : t Resources (Sem hb1 Sems Semt))
                (m1 m1' : mem)
                (cd : option (Injindex compiler_simulation))
                (st2 : t Resources (Sem hb2 Sems Semt))
                (mu : meminj)
                (m2 : mem)
                (H0 : concur_match cd mu st1 m1 st2 m2)
                (tid : nat)
                (Htid : containsThread st1 tid)
                (Hcmpt : HybridMachine.mem_compatible hb1 Sems Semt st1 m1)
                (c : state_sum ClightCoreSEM.C X86Machines.ErasedMachine.ThreadPool.code)
                (b : block)
                (ofs : Integers.Int.int)
                (pmap : access_map * access_map)
                (virtueThread : delta_map * delta_map),
                let newThreadPerm := (computeMap (getThreadR Htid)#1 virtueThread#1,
                                      computeMap (getThreadR Htid)#2 virtueThread#2) : 
                                       access_map * access_map in
                forall (Hlt' : permMapLt
                            (setPermBlock (Some Writable) b (Integers.Int.intval ofs)
                                          (getThreadR_ (ThreadPool hb1 Sems Semt) Htid)#2 LKSIZE_nat) 
                            (getMaxPerm m1))
                  (Hbounded : bounded_maps.sub_map virtueThread#1
                                                   (PTree.map1 (fun f : Z -> perm_kind -> option permission => f^~ Max)
                                                               (Mem.mem_access m1)#2) /\
                              bounded_maps.sub_map virtueThread#2
                                                   (PTree.map1 (fun f : Z -> perm_kind -> option permission => f^~ Max)
                                                               (Mem.mem_access m1)#2))
                  (Hinv : HybridMachine.invariant hb1 Sems Semt st1)
                  (Hcode : getThreadC Htid = Kblocked c)
                  (Hat_external : at_external_sum ClightCoreSEM.G X86SEM.G ClightCoreSEM.C
                                                  X86Machines.ErasedMachine.ThreadPool.code mem
                                                  (semantics.at_external
                                                     (semantics.csem (event_semantics.msem ClightCoreSEM.Sem)))
                                                  Asm_core.cl_at_external genv c m1 = Some (LOCK, [:: Vptr b ofs]))
                  (Hload : Mem.load Mint32 (restrPermMap (proj2 (Hcmpt tid Htid))) b (Integers.Int.intval ofs) =
                           Some (Vint Integers.Int.one))
                  (Haccess : Mem.range_perm (restrPermMap (proj2 (Hcmpt tid Htid))) b 
                                            (Integers.Int.intval ofs) (Integers.Int.intval ofs + LKSIZE) Cur Readable)
                  (Hstore : Mem.store Mint32 (restrPermMap Hlt') b (Integers.Int.intval ofs)
                                      (Vint Integers.Int.zero) = Some m1')
                  (HisLock : lockRes st1 (b, Integers.Int.intval ofs) = Some pmap)
                  (Hangel1 : permMapJoin pmap#1 (getThreadR Htid)#1
                                         (computeMap (getThreadR Htid)#1 virtueThread#1))
                  (Hangel2 : permMapJoin pmap#2 (getThreadR Htid)#2
                                         (computeMap (getThreadR Htid)#2 virtueThread#2)),
                exists
                  (st2' : t Resources (Sem hb2 Sems Semt)) (m2' : mem) (cd' : option (Injindex compiler_simulation)),
                  concur_match cd' mu
                               (updLockSet (updThread Htid (Kresume c Vundef) newThreadPerm)
                                           (b, Integers.Int.intval ofs) (empty_map, empty_map)) m1' st2' m2' /\
                  HybridMachine.external_step hb2 Sems Semt genv (tid :: U0) [::] st2 m2 U0 [::] st2' m2'.
         Proof.
           intros.
           (*Steps:*)
           (*Case analysis over the type of the threads *)
           
           destruct (Compare_dec.lt_eq_lt_dec (tid) hb') as [[LT | EQ] | LT ].
           Focus 3.
           - (*tid > hb' Both threads on source*) 
             (*Prove the comcert external_call step for thread i*)
             eapply H0 in LT. instantiate (1:= Htid) in LT; inv LT;
                                (rewrite Hcode in H; inversion H).
             move Hat_external at bottom.
             unfold at_external_sum,sum_func in Hat_external; simpl in Hat_external.
             rewrite <- H6 in Hat_external.
             rewrite ClightCoreSEM.CLC_msem in Hat_external.
             simpl in Hat_external; unfold cl_at_external in Hat_external.
             destruct (code1) eqn:cPC; try solve[inv Hat_external].
             destruct (f0) eqn:func_kind; try solve[inv Hat_external].
             inversion Hat_external; subst e l; clear Hat_external.
             assert (
                 exists events m2',
                 step (semantics2 p) genvS
                      (Callstate (Ctypes.External LOCK t t0 c1) ls1 c0
                       (restrPermMap
                          ((memcompat2 H0) tid
                          (same_length_contains tid (same_length cd mu st1 m1 st2 m2 H0) Htid))#1))
                      events (Returnstate Vundef c0  m2')
             ).
             do 2 eexists; econstructor.
             simpl.
(*
             (*tid < hb' Noth threads on taret*) 
             (*Prove the comcert external_call step for thread i*)
             eapply H0 in LT. instantiate (1:= Htid) in LT; inv LT;
                                (rewrite Hcode in H; inversion H).
             simpl in H2;
               unfold Asm_core.cl_at_external in H2.
             destruct (code1 Asm.PC) eqn:cPC; try solve[inv H2].
             if_tac in H2; try solve[inv H2].
             destruct (Genv.find_funct_ptr genvT b0)
             
             
             assert (
                 step (semantics2 p) genvT
                      (CC_core_to_CC_state c
                       (restrPermMap
                          ((memcompat2 H0) tid
                          (same_length_contains tid (same_length cd mu st1 m1 st2 m2 H0) Htid))#1))
                    t (CC_core_to_CC_state c2' m2')
             ).
           assert (external_Step: ).
           (*Use the simulation to propagate it down.*)
           (*Use the machine step in the target machine, *)
           (* From the Comcert step, get the match*)
            *)
           
           
         Admitted.
         eapply Lock_HybridStep_simulation; eauto.

         * admit. * admit.  * admit.  * admit.  * admit.  
        + (*haltd*)
          admit.
        + (*schedfail'*)
          admit.
    Admitted. 
    
  End MachineThreadDiagram.

  (** *The one_compiled_thread_simulation*)
    
  Lemma one_compiled_thread_simulation:
    exists v:val,
            HybridMachine_simulation
              Sems Semt hb1 hb2 U genv
              _ option_compiler_order
              (concur_match)  v.
  Proof.
  exists Vundef.
  econstructor.
  - admit. (*eapply Injfsim_order_wf *)
  - (* core_initial*)
    admit.
    (*
    intros.
    destruct (NPeano.Nat.eq_dec hb' 0).
    + pose proof (Injfsim_match_initial_states compiler_simulation).
      unfold initial_state in H2; simpl in H2.
      unfold Clight.initial_state in H2.
      
    + (*Easy case where the first thread is compiled already *)  exists None.
      exists (mk _ (Sem hb2 Sems Semt) (num_threads c1) (pool c1) (perm_maps c1) (lset c1) ).
      exists m1'.
      split.
      simpl in *; unfold HybridMachine.init_machine',
                  HybridMachine.init_mach in *; simpl in *.
      unfold initial_core_sum in *. admit. (*Could be lemma *)
     *)
    
  - (*thread_diagram*)
    intros.
    eapply hybrid_thread_diagram; eauto.
  - (*machine_diagram*)
     eapply machine_thread_diagram; eauto.
  - (*thread_halted *)
    admit.
    
  - (*thread_running*)
    admit.
  Admitted.

End OneThreadCompiledyesProofs.

End OneThreadCompiled.

Section NThredCompiled.
  Notation hb0:= (Some 0%nat).
  Notation hb n:= (Some n).
  Variable U: seq.seq nat.

  Notation C0:= (t_ (HybridMachine.ThreadPool hb0 Sems Semt)).
  Notation C n:= (t_ (HybridMachine.ThreadPool (Some n) Sems Semt)).
  Notation G:= (semG (HybridMachine.Sem hb0 Sems Semt)) .
  (*Notation G n:= (semG (HybridMachine.Sem (hb n) Sems Semt)). *)


  (*Need to make the data/order correct: that is a list of cds'*)
  Inductive  Nconcur_match: forall n, list (option compiler_index) -> meminj -> C0 -> mem -> C n -> mem -> Prop :=
  | ZeroOneSimulation:
      forall st0 m0,
        Nconcur_match 0 nil inject_id st0 m0 st0 m0
  | ZeroNSimulation:
      forall n ls_cd cd jn jn' st0 m0 stn mn stn' mn',
        Nconcur_match n ls_cd jn st0 m0 stn mn ->
        concur_match n cd jn' stn mn stn' mn' ->
        Nconcur_match (S n) (cd::ls_cd) (compose_meminj jn jn') st0 m0 stn' mn'.

  Parameter list_order: list compiler_index -> list compiler_index -> Prop.
  Parameter option_list_order: list (option compiler_index) ->
                               list (option compiler_index) -> Prop.


  
  Variable v:val.
  Lemma N_compiled_thread_simulation:
    forall n,
          HybridMachine_simulation
            Sems Semt hb0 (hb n) U genv
            (list (option compiler_index)) option_list_order 
            (Nconcur_match n) v.  
  Proof.
    induction n.
    - simpl.
      admit. (*Trivial self simulation.*)
    - econstructor.
      + admit.
      + admit. (*init*)
      + admit. (* regular composition diagram (needs the star lemma... ) *)
      + admit. (* easy one step machine diagram *)
      + admit. (* haltd*)
      + admit.
  Admitted.
  
End NThredCompiled.


Section AllThredCompiled.
  Notation hb0:= (Some 0%nat).
  Notation hball:= None.
  Variable U: seq.seq nat.

  Notation C0:= (t_ (HybridMachine.ThreadPool hb0 Sems Semt)).
  Notation Call:= (t_ (HybridMachine.ThreadPool hball Sems Semt)).
  Notation G0:= (semG (HybridMachine.Sem hb0 Sems Semt)) .
  Notation Gall:= (semG (HybridMachine.Sem hball Sems Semt)).

  (*Remember to use (match_states compiler_match) insted of compiler_match directly*)
  Definition All_concur_match':
    list compiler_index -> meminj -> C0 -> mem -> Call -> mem -> Prop.
  Admitted. 

  Notation Nconcur_match:=(All_concur_match').

  Lemma All_compiled_thread_simulation:
          HybridMachine_simulation
            Sems Semt hb0 hball U genv
            (list compiler_index) (list_order) 
            (Nconcur_match) Vundef.  
  Proof.
  Admitted.
  
End AllThredCompiled.


End HybridProofs.
      
