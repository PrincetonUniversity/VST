From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrfun.
Require Import Coq.omega.Omega.
Require Import Clight.
Require Import Memory.
Require Import Values.
Require Import Globalenvs.
Require Import Compiler.
Require Import compcert.lib.Coqlib.

Require Import msl.Coqlib2.

Require veric.Clight_core. Import Clight_core.

Require Import Smallstep.
Require Import ExposedSmallstep2 ExposedSmallstep.
Require Import concurrency.x86_context.
Require Import concurrency.HybridMachine.
Require Import concurrency.HybridMachineSig.
Require Import concurrency.HybridMachine_simulation.
(*Require Import concurrency.compiler_correct.*)
Require Import concurrency.CoreSemantics_sum.
Require Import concurrency.self_simulation.
Require Import concurrency.Clight_self_simulation.
Require Import concurrency.Asm_self_simulation.


Require Import concurrency.permissions.

Require Import concurrency.ClightCoreSemantincsForMachines.

Set Bullet Behavior "Strict Subproofs".

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
    Definition code_inject_source:= code_inject _ _ (Clight_self_simulation p).

    (* we extract match_target from the self_simulation of Asm*)
    Definition code_inject_target:= code_inject _  _ (Asm_self_simulation tp).

    Parameter make_state_Clight: CC_core -> mem -> Clight.state.
    Parameter make_state_Asm: X86Machines.ErasedMachine.ThreadPool.code -> mem -> ia32.Asm.state.

    
    Definition compiler_simulation: fsim_properties_inj ( Clight.semantics2 p) (ia32.Asm.semantics tp)
                                                        ( Clight.get_mem) (ia32.Asm.get_mem):=
    simpl_clight_semantic_preservation p tp compiled.
    
    Definition compiler_index := Injindex compiler_simulation.
    Definition compiler_order := Injorder compiler_simulation.
    Definition compiler_match := Injmatch_states compiler_simulation.
    
    Definition match_compiled_states :=
      fun i f c1 m1 c2 m2 =>
        exists st1 st2 f1 f12 f2,
          code_inject_source f1 (make_state_Clight c1 m1) st1 /\
          compiler_match i f12 st1 st2 /\
          code_inject_target f2 (make_state_Asm c2 m2) st2 /\
          f = compose_meminj f1 (compose_meminj f12 f2).
    Definition source_match f st1 m1 st2 m2 :=
      code_inject_source f (make_state_Clight st1 m1)
                         (make_state_Clight st2 m2).
    Definition target_match f st1 m1 st2 m2 :=
      code_inject_target f (make_state_Asm st1 m1)
                         (make_state_Asm st2 m2).
          
Section OneThreadCompiledMatch.

  Definition HM1:=HybridMachine hb1 Sems Semt.
  Definition HM2:=HybridMachine hb2 Sems Semt.

  Notation Sem1:=(ConcurMachineSemantics _ _ _ HM1 U None).
  Notation Sem2:=(ConcurMachineSemantics _ _ _ HM2 U None) .

  Inductive condition: Set :=
    running | blocked | resuming | initializing .

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
      semantics.at_external (CoreSem Sems) code1 = Some (f,ls1) ->
      semantics.at_external (CoreSem Sems) code2 = Some (f',ls2) ->
      Val.inject_list j ls1 ls2 ->
      source_match j code1 m1 code2 m2 ->
      match_thread_source  j (Kblocked (SState _ _ code1)) m1
                          (Kblocked (SState _ _ code2)) m2
  | SThread_Resume: forall j code1 m1 code2 m2 ls1 ls2 f f' v v' code1' code2',
      (*Do I need to keep this two? Probanly not*)
    semantics.at_external (CoreSem Sems) code1 = Some (f,ls1) ->
    semantics.at_external (CoreSem Sems) code2 = Some (f',ls2) ->
    Val.inject_list j ls1 ls2 ->
    semantics.after_external (CoreSem Sems) None code1 = Some code1' ->
    semantics.after_external (CoreSem Sems) None code2 = Some code2' ->
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
      semantics.at_external (CoreSem Semt) code1 = Some (f,ls1) ->
      semantics.at_external (CoreSem Semt) code2 = Some (f',ls2) ->
      Val.inject_list j ls1 ls2 ->
      target_match j code1 m1 code2 m2 ->
      match_thread_target j (Kblocked (TState _ _ code1)) m1
                          (Kblocked (TState _ _ code2)) m2
  | TThread_Resume: forall j code1 m1 code2 m2 ls1 ls2 f f' v v' code1' code2',
      (*Do I need to keep this two? Probanly not*)
      semantics.at_external (CoreSem Semt) code1 = Some (f,ls1) ->
      semantics.at_external (CoreSem Semt) code2 = Some (f',ls2) ->
      Val.inject_list j ls1 ls2 ->
      semantics.after_external (CoreSem Semt) None code1 = Some code1' ->
      semantics.after_external (CoreSem Semt) None code2 = Some code2' ->
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
      semantics.at_external (CoreSem Sems) code1 = Some (f,ls1) ->
      semantics.at_external (CoreSem Semt) code2 = Some (f',ls2) ->
      Val.inject_list j ls1 ls2 ->
      match_compiled_states cd j code1 m1 code2 m2 ->
      match_thread_compiled  cd j (Kblocked (SState _ _ code1)) m1
                            (Kblocked (TState _ _ code2)) m2
  | CThread_Resume: forall cd j code1 m1 code2 m2 ls1 ls2 f f' v v' code1' code2',
      (*Do I need to keep this two? Probanly not*)
      semantics.at_external (CoreSem Sems) code1 = Some (f,ls1) ->
      semantics.at_external (CoreSem Semt) code2 = Some (f',ls2) ->
      Val.inject_list j ls1 ls2 ->
      semantics.after_external (CoreSem Sems) None code1 = Some code1' ->
      semantics.after_external (CoreSem Semt) None code2 = Some code2' ->
      match_compiled_states cd j code1' m1 code2' m2 ->
      match_thread_compiled cd j (Kresume (SState _ _ code1) v) m1
                            (Kresume (TState _ _ code2) v') m2
  | CThread_Init: forall cd j m1 m2 v1 v1' v2 v2',
      Val.inject j v1 v2 ->
      Val.inject j v1' v2' ->
      match_thread_compiled cd j (Kinit v1 v1') m1
                            (Kinit v2 v2') m2.

  Record concur_match (cd: compiler_index)
       (j:meminj) (cstate1: C1) (m1: mem) (cstate2: C2) (m2: mem):=
  { same_length: num_threads cstate1 = num_threads cstate2
    ; memcompat1: HybridMachine.mem_compatible _ _ _ cstate1 m1
    ; memcompat2: HybridMachine.mem_compatible _ _ _ cstate2 m2
    ; mtch_source:
        forall (i:nat),
          (i > hb')%nat ->
          forall (cnti1: containsThread cstate1 i),
          match_thread_source  j
                              (getThreadC cnti1)
                              (restrPermMap (memcompat1 i cnti1).1)
                              (getThreadC (same_length_contains same_length cnti1))
                              (restrPermMap (memcompat2 i (same_length_contains same_length cnti1)).1)
    ; mtch_target:
        forall (i:nat),
          (i < hb')%nat ->
          forall (cnti1: containsThread cstate1 i),
          match_thread_target  j
                              (getThreadC cnti1)
                              (restrPermMap (memcompat1 i cnti1).1)
                              (getThreadC (same_length_contains same_length cnti1))
                              (restrPermMap (memcompat2 i (same_length_contains same_length cnti1)).1)
    ; mtch_compiled:
        forall (i:nat),
          (i = hb')%nat ->
          forall (cnti1: containsThread cstate1 i),
          match_thread_compiled cd j
                                (getThreadC cnti1)
                                (restrPermMap (memcompat1 i cnti1).1)
                                (getThreadC (same_length_contains same_length cnti1))
                                (restrPermMap (memcompat2 i (same_length_contains same_length cnti1)).1) }.

Lemma contains12:
  forall {data j cstate1 m1 cstate2 m2},
  concur_match data j cstate1 m1 cstate2 m2 ->
  forall {i:nat} {cnti1: containsThread cstate1 i},
    containsThread cstate2 i.
Proof.
  unfold containsThread.
  intros ? ? ? ? ? ? H. destruct H.
  rewrite same_length0; auto.
Qed.

Lemma contains21:
  forall {data j cstate1 m1 cstate2 m2},
  concur_match data j cstate1 m1 cstate2 m2 ->
  forall {i:nat} {cnti1: containsThread cstate2 i},
    containsThread cstate1 i.
Proof.
  unfold containsThread.
  intros ? ? ? ? ? ? H. destruct H.
  rewrite same_length0; auto.
Qed.

End OneThreadCompiledMatch.

Arguments same_length_contains {ms1 ms2}.
Arguments memcompat1 {cd j cstate1 m1 cstate2 m2}.
Arguments memcompat2 {cd j cstate1 m1 cstate2 m2}.
    
  Section HybridThreadDiagram.

    (*
    Variable core_data : Type.
    Variable order : core_data -> core_data -> Prop.
    Variable compiler_match : core_data -> meminj -> state (Clight_semantics2 p)  -> state (Asm_semantics tp) -> Prop.
    Variable props : fsim_properties_inj (Clight_semantics2 p) (Asm_semantics tp)
                                         Clight_get_mem Asm_get_mem order compiler_match.
    Notation match_states:=(match_states compiler_match).
    Notation concur_match:=(@concur_match Sems Semt core_data match_source match_target match_states).
     *)

    (*
    Lemma hybrid_thread_diagramc:
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
             /\ compiler_order cd' cd).
    Proof.
      intros.
      destruct U0; simpl in H.
      - inversion H; subst.
        inversion HschedN.
      - inversion H; subst.
        inversion HschedN; subst.
        destruct (Compare_dec.lt_eq_lt_dec (tid) hb') as [[LT | EQ] | LT ].
        
        + (* tid < hb' *)
          (*This case it's all in target*)
          inversion Htstep. subst tp' m' ev0.
          eapply event_semantics.ev_step_ax1 in Hcorestep.
          simpl in Hcorestep.
          simpl in Hcode.
          eapply H0 in LT. instantiate (1 := Htid) in LT.
          rewrite Hcode in LT.
          assert (Htid':= contains12 H0 Htid).
          inv LT. 
          
          
          (*Use the source self_simulations*)
          inversion Hcorestep; subst.
          eapply Asm_self_simulation in H5; eauto.
          2: replace (memcompat1 H0) with Hcmpt by (apply proof_irr); simpl; eauto.
          simpl in H5; destruct H5 as [c2' [m2' [f' [STEP [SMATCH EXT]]]]].
       
        exists (@updThread_ _ _ _ _ st2 Htid'
                       (Krun (TState CC_core X86Machines.ErasedMachine.ThreadPool.code  c2'))
                      (permissions.getCurPerm m2',
                       snd (getThreadR Htid'))).
        exists m2'.
        exists cd. (*This should be updated with the new value!*)
        exists f'; simpl.
        
        split.
        (*Reestablish the match*)
        admit.
        
        (*Prove the machine step*)
        left.
        eapply machine_semantics_lemmas.thread_step_plus_one.
        econstructor; simpl; auto.
        econstructor; eauto.
        admit. (*going to need to add this to the match relation *)

        instantiate (3 := (memcompat2 H0)).
        simpl; econstructor; eauto.
        simpl. eauto.
        admit. (*something about the semantics*)

        simpl; repeat f_equal. apply proof_irr. apply proof_irr.

        
        + (* tid = hb' *)
          (* equal: one machine in source one in target!!*)
          inversion Htstep. subst tp' m' ev0.
          eapply event_semantics.ev_step_ax1 in Hcorestep.
          simpl in Hcorestep.
          assert (Hcode':= Hcode).
          simpl in Hcode.
          eapply H0 in EQ. instantiate (1 := Htid) in EQ.
          rewrite Hcode in EQ.
          assert (Htid':= contains12 H0 Htid).
          inv EQ. 

          inv Hcorestep.
          destruct H4 as [NotAtExt step].

        
          assert (TOPROVE: forall ge c m t c' m',
                     Clight.step ge (function_entry2 ge) (CC_core_to_CC_state c m) t (CC_core_to_CC_state c' m') ->
                     Smallstep.step
                       (Clight_semantics2 p)
                       ge (c, m) t (c',m')) by admit.
          apply TOPROVE in step.
          
          assert (TOPROVE2: fst genv = ((globalenv (Clight_semantics2 p)))) by admit.
          simpl in TOPROVE2.
          rewrite TOPROVE2 in step.

          eapply props in step.
          Focus 2.
          unfold match_states, make_state_source, make_state_target in H5; simpl in H5. 
          replace (Hcmpt tid Htid) with ((memcompat1 H0) tid Htid) by apply proof_irr.
          eauto.

          destruct step as [i[[s2' m2'] [mu' [t' [STEP' [MATCH [INCR INJTRACE]]]]]]].
          
          exists (@updThread_ _ _ _ _ st2 Htid'
                       (Krun (TState CC_core X86Machines.ErasedMachine.ThreadPool.code  s2'))
                      (permissions.getCurPerm m2',
                       snd (getThreadR Htid'))).
          exists m2'.
          exists i. (*This should be updated with the new value!*)
          exists mu'.
          split.

          
          { (*THE match relation*)
            clear STEP'.

          (*
          econstructor.
          - simpl. apply H0.
          - intros.
            destruct (NPeano.Nat.eq_dec tid i0).
            + subst i0.
              admit. (*wrong type of states*)
            + erewrite gsoThreadCode in H1; auto.
              simpl in cnti2.
              unfold updThread_ in H3.
              erewrite gsoThreadCode in H3; auto.
              simpl.
              unfold HybridMachine.compat_th.
              Parameter same_visible:
                mem -> mem -> Prop.
              destruct H0.
              eapply match_source_forward.
              * eapply Clight.
              * admit. 
              * admit. (*this should come from concur_match... missing right now*)  
              * admit. (*again... from concur_match*)
              * admit.
              * admit. (*again... from concur_match*)
              * admit. (*again... from concur_match*)

          - intros.
            destruct (NPeano.Nat.eq_dec tid i0).
            + subst i0.
              admit. (*wrong type of states*)
            + erewrite gsoThreadCode in H1; auto.
              simpl in cnti2.
              unfold updThread_ in H3.
              erewrite gsoThreadCode in H3; auto.
              simpl.
              unfold HybridMachine.compat_th.
              destruct H0.
              eapply match_source_forward.
              * eapply X86SEM_rec.
              * admit. 
              * admit. (*this should come from concur_match... missing right now*)  
              * admit. (*again... from concur_match*)
              * admit.
              * admit. (*again... from concur_match*)
              * admit. (*again... from concur_match*)
          - intros.
            destruct (NPeano.Nat.eq_dec tid i0).
            + subst tid.
              admit. (*Follows directly from MATCH and the correct update to the list of data*)
            + admit. (*wrong type of states*)
          - admit.
          - admit.
          - admit.
          - admit.
          - admit.*)
            admit. 
          }
        
        { (*THE MACHINE STEP.*)
          admit. (*This should be standard.*)
        }
        
       + (*hb' < tid*)
        (*This case it's all in source*)
         inversion Htstep. subst tp' m' ev0.
          eapply event_semantics.ev_step_ax1 in Hcorestep.
          simpl in Hcorestep.
          simpl in Hcode.
          eapply H0 in LT. instantiate (1 := Htid) in LT.
          rewrite Hcode in LT.
          assert (Htid':= contains12 H0 Htid).
          inv LT. 
          
          
          (*Use the source self_simulations*)
          inversion Hcorestep; subst.
          eapply Clight_self_simulation in H5; eauto.
          2: replace (memcompat1 H0) with Hcmpt by (apply proof_irr); simpl; eauto.
          simpl in H5; destruct H5 as [c2' [m2' [f' [STEP [SMATCH EXT]]]]].
       
          exists (@updThread_ _ _ _ _ st2 Htid'
                         (Krun (SState CC_core X86Machines.ErasedMachine.ThreadPool.code  c2'))
                      (permissions.getCurPerm m2',
                       snd (getThreadR Htid'))).
        exists m2'.
        exists cd. 
        exists f'; simpl.
        
        split.
        (*Reestablish the match*)
        admit.
        
        (*Prove the machine step*)
        left.
        eapply machine_semantics_lemmas.thread_step_plus_one.
        econstructor; simpl; auto.
        econstructor; eauto.
        admit. (*going to need to add this to the match relation *)

        instantiate (3 := (memcompat2 H0)).
        simpl; econstructor; eauto.
        simpl. eauto.
        admit. (*something about the semantics*)

        simpl; repeat f_equal. apply proof_irr. apply proof_irr.

        Unshelve.
        eauto.
        eauto.
    Admitted. *)
    
  End HybridThreadDiagram.

  Section MachineThreadDiagram.
    
    (*Lemma machine_thread_diagram:
      forall (U0 : list nat) (tr : list HybridMachineSig.machine_event) (st1 : C1) (m1 : mem) 
        (U' : list nat) (tr' : list HybridMachineSig.machine_event) (st1' : C1) (m1' : mem),
        machine_semantics.machine_step (HCSem Sems Semt hb1 U) genv U0 tr st1 m1 U' tr' st1' m1' ->
        forall (cd : core_data) (st2 : C2) (mu : meminj) (m2 : mem),
          concur_match cd mu st1 m1 st2 m2 ->
          exists (st2' : C2) (m2' : mem) (cd' : core_data),
            concur_match cd' mu st1' m1' st2' m2' /\
            machine_semantics.machine_step (HCSem Sems Semt hb2 U) genv U0 tr st2 m2 U' tr' st2' m2'.
    Proof.
      intros.
      destruct U0; simpl in H.
      + inv H;
          match goal with
          | [ H: HybridMachine.schedPeek nil = Some _  |- _ ] => inv H
          end.
      + simpl in H; inv H. (*Case by case of all the sync_calls*)
        * (*start*)
          inv Htstep.
          simpl in Hinitial.
          admit. (*REVIEW*)
        * (*resume*)
          admit.
        * (*suspend*)
          admit.
        * (*sync*)
          admit.
        * (*haltd*)
          admit.
        * (*schedfail'*)
          admit.
    Admitted. *)
    
  End MachineThreadDiagram.

  (** *The one_compiled_thread_simulation*)

  (*Fake genv while we fix Asm*)
  Parameter genv':(semG Sems * semG Semt)%type.
    
  Lemma one_compiled_thread_simulation:
    exists v:val,
            HybridMachine_simulation
              Sems Semt hb1 hb2 U genv'
              _ compiler_order
              (concur_match)  v.
  Proof.
    
  exists Vundef.
  econstructor.
  - eapply Injfsim_order_wf.
  - (* core_initial*)
    intros.
    (* intros.
    simpl in H.
    destruct (
        HybridMachine.init_mach hb1 Sems Semt (@None (prod permissions.access_map permissions.access_map))
            genv Vundef vals1
      ) eqn:INIT; 
    unfold HybridMachine.init_machine' in H;
    rewrite INIT in H; inversion H; subst. (*solves one case*)
    unfold HybridMachine.init_mach in INIT.  *)
    admit.
  - (*thread_diagram*)
    admit.
    (* eapply hybrid_thread_diagramc; eauto. *)
    
  - (*machine_diagram*)
    (* eapply machine_thread_diagram; eauto. *)
    admit.
  - (*thread_halted *)
    admit.
    
  - (*thread_running*)
    admit.
  Admitted.

End OneThreadCompiledProofs.

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
  Inductive  Nconcur_match: forall n, list compiler_index -> meminj -> C0 -> mem -> C n -> mem -> Prop :=
  | ZeroOneSimulation:
      forall st0 m0,
        Nconcur_match 0 nil inject_id st0 m0 st0 m0
  | ZeroNSimulation:
      forall n ls_cd cd jn jn' st0 m0 stn mn stn' mn',
        Nconcur_match n ls_cd jn st0 m0 stn mn ->
        concur_match n cd jn' stn mn stn' mn' ->
        Nconcur_match (S n) (cd::ls_cd) (compose_meminj jn jn') st0 m0 stn' mn'.

  Parameter list_order: list compiler_index -> list compiler_index -> Prop.

  Variable v:val.
  Lemma N_compiled_thread_simulation:
    forall n,
          HybridMachine_simulation
            Sems Semt hb0 (hb n) U genv'
            (list compiler_index) list_order 
            (Nconcur_match n)  v.  
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
    exists v:val,
          HybridMachine_simulation
            Sems Semt hb0 hball U genv'
            (list compiler_index) (list_order) 
            (Nconcur_match)  v.  
  Proof.
  Admitted.
  
End AllThredCompiled.


End HybridProofs.
      
