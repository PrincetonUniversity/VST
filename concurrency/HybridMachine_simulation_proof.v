From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrfun.
Require Import Coq.omega.Omega.
Require Import Clight.
Require Import Memory.
Require Import Values.
Require Import Compiler.
Require Import compcert.lib.Coqlib.

Require Import msl.Coqlib2.

Require veric.Clight_core. Import Clight_core.

Require Import Smallstep.
Require Import ExposedSmallstep2.
Require Import concurrency.x86_context.
Require Import concurrency.HybridMachine.
Require Import concurrency.HybridMachineSig.
Require Import concurrency.HybridMachine_simulation.
(*Require Import concurrency.compiler_correct.*)
Require Import concurrency.CoreSemantics_sum.
Require Import concurrency.self_simulation.

Require Import concurrency.permissions.

Set Bullet Behavior "Strict Subproofs".



Section Clight_Sem.
  Variable p: program.
  
  Notation genv:=genv. (*from Clight_core*)
  Notation state:=CC_core.
  
  Program Definition Clight_memSem: semantics.MemSem genv state:=
    semantics.Build_MemSem _ _ cl_core_sem _.
  Next Obligation.
  Admitted.

  Program Definition Clight_EvSem: event_semantics.EvSem:=
    event_semantics.Build_EvSem _ _ Clight_memSem _ _ _ _ _.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
  Next Obligation.
  Admitted.
    
  Definition Clight: Semantics_rec:=
    Build_Semantics_rec
      genv (*semG*)
      state (*semC*)
      Clight_EvSem (*semSem EvSem*).
End Clight_Sem.

Section HybridProofs.

  Variable p: program.
  Variable tp: ia32.Asm.program. 
  Variable compiled: (simpl_transf_clight_program p = Errors.OK tp).

  (*Lemma programs_match : simpl_match_prog p tp.
  Proof. apply transf_clight_program_match; assumption. Qed.

  Lemma program_forward_sim:
    Smallstep.forward_simulation (semantics2 p) (Asm.semantics tp).
  Proof. apply simpl_clight_semantic_preservation; apply programs_match; eauto. Qed. *)

  Parameter Clight_step: Clight.genv -> CC_core * mem -> Events.trace -> CC_core * mem -> Prop.
  Parameter Clight_init: CC_core * mem -> Prop.
  Parameter Clight_final: CC_core * mem -> Integers.Int.int -> Prop.
  Parameter Clight_genv: program -> Clight.genv.
  Parameter Clight_symbolenv: Globalenvs.Senv.t.
  Definition Clight_semantics2 (p: program) : semantics:=
    @Semantics_gen
      (CC_core * mem)
      Clight.genv
      Clight_step
      Clight_init
      Clight_final
      (Clight_genv p)
      Clight_symbolenv.
  Definition Clight_get_mem (cs: (CC_core * mem)):= match cs with ( _ , m ) => m end.

  Parameter Clight_code_inject: CC_core -> meminj -> CC_core -> Prop.
  Lemma Clight_self_simulation: self_simulation _ _ (event_semantics.msem (semSem (Clight p))) Clight_code_inject.
  Admitted.

  Notation ASM_core:=X86Machines.ErasedMachine.ThreadPool.code.
  Parameter Asm_step: X86SEM.G -> ASM_core * mem -> Events.trace -> ASM_core * mem -> Prop.
  Parameter Asm_init: ASM_core * mem -> Prop.
  Parameter Asm_final: ASM_core * mem -> Integers.Int.int -> Prop.
  Parameter Asm_genv: ia32.Asm.program -> X86SEM.G.
  Parameter Asm_symbolenv: Globalenvs.Senv.t.
  Definition Asm_semantics (tp: ia32.Asm.program) : semantics:=
    @Semantics_gen
      (X86Machines.ErasedMachine.ThreadPool.code * mem)
      X86SEM.G
      Asm_step
      Asm_init
      Asm_final
      (Asm_genv tp)
      Asm_symbolenv.
  Definition Asm_get_mem (cs: (X86Machines.ErasedMachine.ThreadPool.code  * mem)):= match cs with ( _ , m ) => m end.

  Parameter Asm_code_inject: ASM_core -> meminj -> ASM_core -> Prop.
  Lemma Asm_self_simulation: self_simulation _ _
                                             (event_semantics.msem (semSem (X86SEM_rec)))
                                             Asm_code_inject.
  Admitted.

  
  Lemma program_forward_sim:
    forward_injection (Clight_semantics2 p) (Asm_semantics tp) Clight_get_mem Asm_get_mem.
  Proof. Admitted.

  Definition Sems:= Clight p.
  Definition Semt:= X86SEM_rec.  (*How do I pass p to this?*)


Section OneThreadCompiled.
  Variable (hb': nat).
  Notation hb1:= (Some hb').
  Notation hb2:= (Some (S hb')).
  Variable U: seq.seq nat.

  (* Definition Resources : Resources_rec:=
    Build_Resources_rec (access_map * access_map)%type (access_map * access_map)%type. *)

  
  Notation C1:= (t_ (HybridMachine.ThreadPool hb1 Sems Semt)).
  Notation C2:= (t_ (HybridMachine.ThreadPool hb2 Sems Semt)).
  Notation G1:= (semG (HybridMachine.Sem hb1 Sems Semt)) .
  Notation G2:= (semG (HybridMachine.Sem hb2 Sems Semt)).

  (*The two following globals must be taken from the program...*)
  (*and they are probaly the smae global??? *)
  Variable genv: (semG Sems * semG Semt)%type.


  (*What are these!!!*)
  Variable (ge_inv: G1 -> G2 -> Prop).
  Variable init_inv : meminj -> G1 -> list val -> mem -> G2 -> list val -> mem -> Prop.
  Variable halt_inv : (*SM_Injection*)meminj -> G1 -> val -> mem -> G2 -> val -> mem -> Prop.
  
  Section OneThreadCompiledProofs.
  Definition match_source:= match_self (semC (Clight p)) Clight_code_inject.
  Definition match_target:= match_self (semC (X86SEM_rec)) Asm_code_inject.
  Definition make_state_source (c:semC Sems) (m:mem): state (Clight_semantics2 p):= (c, m).
  Definition make_state_target (c:semC Semt) (m:mem): state (Asm_semantics tp):= (c,m).
  Definition match_states {core_data: Type}
             (compiler_match : core_data -> meminj -> state (Clight_semantics2 p)  -> state (Asm_semantics tp) -> Prop):=
      fun i j c m c' m' => compiler_match i j (make_state_source c m) (make_state_target c' m').
    
  
  
Section OneThreadCompiledMatch.

  Variable (Sems Semt : Semantics_rec).
  Definition HM1:=HybridMachine hb1 Sems Semt.
  Definition HM2:=HybridMachine hb2 Sems Semt.

  Notation Sem1:=(ConcurMachineSemantics _ _ _ HM1 U None).
  Notation Sem2:=(ConcurMachineSemantics _ _ _ HM2 U None) .

  Notation C1:= (t_ (ThreadPool hb1 Sems Semt)).
  Notation C2:= (t_ (ThreadPool hb2 Sems Semt)).
  Definition G:= (semG Sems * semG Semt)%type.

  
  Variable ge:G.
  Variable (ge_inv': G -> G -> Prop).

  (*
  Variable init_inv' : meminj -> G -> list val -> mem -> G -> list val -> mem -> Prop.
  Variable halt_inv' : (*SM_Injection*)meminj -> G -> val -> mem -> G -> val -> mem -> Prop.
   *)
  
  Variable core_data: Type.
  Variable core_ord : core_data -> core_data -> Prop.
  Variable core_ord_wf : well_founded core_ord.
  Variable thread_match : core_data -> (*SM_Injection*)meminj -> (semC Sems) -> mem -> (semC Semt) -> mem -> Prop.
  Variable source_match : (*SM_Injection*)meminj -> (semC Sems) -> mem -> (semC Sems) -> mem -> Prop.
  Variable target_match : (*SM_Injection*)meminj -> (semC Semt) -> mem -> (semC Semt) -> mem -> Prop.

  Variable compiler_match : core_data -> meminj -> semC Sems -> mem -> semC Semt -> mem -> Prop.
  
Definition order_option (d1 d2: (option core_data)):=
  match d1, d2 with
  | None, None => True
  | None, _ => True
  | Some d1', Some d2' => core_ord d1' d2'
  | _, _ => False
  end.
Fixpoint core_ord_list (ls1 ls2: list (option core_data)): Prop:=
    match ls1, ls2 with
    | nil, nil => True
    | d1::ls1',d2::ls2' => order_option d1 d2 /\ core_ord_list ls1' ls2' 
    | _, _ => False
    end.

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

Inductive match_thread_source (source_match: meminj -> (semC Sems) -> mem -> (semC Sems) -> mem -> Prop):
  meminj -> @ctl (state_sum (semC Sems) (semC Semt)) -> mem -> @ctl (state_sum (semC Sems) (semC Semt)) -> mem -> Prop  :=
| SThread_Running: forall j code1 m1 code2 m2,
                     source_match j code1 m1 code2 m2 ->
                     match_thread_source source_match j (Krun (SState _ _ code1)) m1
                     (Krun (SState _ _ code2)) m2
| SThread_Blocked: forall j code1 m1 code2 m2 ls1 ls2 f f',
    semantics.at_external (CoreSem Sems) code1 = Some (f,ls1) ->
    semantics.at_external (CoreSem Sems) code2 = Some (f',ls2) ->
    Val.inject_list j ls1 ls2 ->
    source_match j code1 m1 code2 m2 ->
    match_thread_source source_match j (Kblocked (SState _ _ code1)) m1
                        (Kblocked (SState _ _ code2)) m2
| SThread_Resume: forall j code1 m1 code2 m2 ls1 ls2 f f' v v' code1' code2',
    (*Do I need to keep this two? Probanly not*)
    semantics.at_external (CoreSem Sems) code1 = Some (f,ls1) ->
    semantics.at_external (CoreSem Sems) code2 = Some (f',ls2) ->
    Val.inject_list j ls1 ls2 ->
    semantics.after_external (CoreSem Sems) None code1 = Some code1' ->
    semantics.after_external (CoreSem Sems) None code2 = Some code2' ->
    source_match j code1' m2 code2' m2 ->
    match_thread_source source_match j (Kresume (SState _ _ code1) v) m1
                        (Kresume (SState _ _ code2) v') m2
| SThread_Init: forall j m1 m2 v1 v1' v2 v2',
    Val.inject j v1 v2 ->
    Val.inject j v1' v2' ->
    match_thread_source source_match j (Kinit v1 v1') m1
                        (Kinit v2 v2') m2.

Inductive match_thread_target (target_match: meminj -> (semC Semt) -> mem -> (semC Semt) -> mem -> Prop):
  meminj -> @ctl (state_sum (semC Sems) (semC Semt)) -> mem -> @ctl (state_sum (semC Sems) (semC Semt)) -> mem -> Prop  :=
| TThread_Running: forall j code1 m1 code2 m2,
                     target_match j code1 m1 code2 m2 ->
                     match_thread_target target_match j (Krun (TState _ _ code1)) m1
                     (Krun (TState _ _ code2)) m2
| TThread_Blocked: forall j code1 m1 code2 m2 ls1 ls2 f f',
    semantics.at_external (CoreSem Semt) code1 = Some (f,ls1) ->
    semantics.at_external (CoreSem Semt) code2 = Some (f',ls2) ->
    Val.inject_list j ls1 ls2 ->
    target_match j code1 m1 code2 m2 ->
    match_thread_target target_match j (Kblocked (TState _ _ code1)) m1
                        (Kblocked (TState _ _ code2)) m2
| TThread_Resume: forall j code1 m1 code2 m2 ls1 ls2 f f' v v' code1' code2',
    (*Do I need to keep this two? Probanly not*)
    semantics.at_external (CoreSem Semt) code1 = Some (f,ls1) ->
    semantics.at_external (CoreSem Semt) code2 = Some (f',ls2) ->
    Val.inject_list j ls1 ls2 ->
    semantics.after_external (CoreSem Semt) None code1 = Some code1' ->
    semantics.after_external (CoreSem Semt) None code2 = Some code2' ->
    target_match j code1' m2 code2' m2 ->
    match_thread_target target_match j (Kresume (TState _ _ code1) v) m1
                        (Kresume (TState _ _ code2) v') m2
| TThread_Init: forall j m1 m2 v1 v1' v2 v2',
    Val.inject j v1 v2 ->
    Val.inject j v1' v2' ->
    match_thread_target target_match j (Kinit v1 v1') m1
                        (Kinit v2 v2') m2.

Inductive match_thread_compiled (compiler_match: meminj -> (semC Sems) -> mem -> (semC Semt) -> mem -> Prop):
  meminj -> @ctl (state_sum (semC Sems) (semC Semt)) -> mem -> @ctl (state_sum (semC Sems) (semC Semt)) -> mem -> Prop  :=
| CThread_Running: forall j code1 m1 code2 m2,
                     compiler_match j code1 m1 code2 m2 ->
                     match_thread_compiled compiler_match j (Krun (SState _ _ code1)) m1
                     (Krun (TState _ _ code2)) m2
| CThread_Blocked: forall j code1 m1 code2 m2 ls1 ls2 f f',
    semantics.at_external (CoreSem Sems) code1 = Some (f,ls1) ->
    semantics.at_external (CoreSem Semt) code2 = Some (f',ls2) ->
    Val.inject_list j ls1 ls2 ->
    compiler_match j code1 m1 code2 m2 ->
    match_thread_compiled compiler_match j (Kblocked (SState _ _ code1)) m1
                        (Kblocked (TState _ _ code2)) m2
| CThread_Resume: forall j code1 m1 code2 m2 ls1 ls2 f f' v v' code1' code2',
    (*Do I need to keep this two? Probanly not*)
    semantics.at_external (CoreSem Sems) code1 = Some (f,ls1) ->
    semantics.at_external (CoreSem Semt) code2 = Some (f',ls2) ->
    Val.inject_list j ls1 ls2 ->
    semantics.after_external (CoreSem Sems) None code1 = Some code1' ->
    semantics.after_external (CoreSem Semt) None code2 = Some code2' ->
    compiler_match j code1' m1 code2' m2 ->
    match_thread_compiled compiler_match j (Kresume (SState _ _ code1) v) m1
                        (Kresume (TState _ _ code2) v') m2
| CThread_Init: forall j m1 m2 v1 v1' v2 v2',
    Val.inject j v1 v2 ->
    Val.inject j v1' v2' ->
    match_thread_compiled compiler_match j (Kinit v1 v1') m1
                        (Kinit v2 v2') m2.

Record concur_match (index: core_data)
       (j:meminj) (cstate1: C1) (m1: mem) (cstate2: C2) (m2: mem):=
  { same_length: num_threads cstate1 = num_threads cstate2
    ; memcompat1: HybridMachine.mem_compatible _ _ _ cstate1 m1
    ; memcompat2: HybridMachine.mem_compatible _ _ _ cstate2 m2
    ; mtch_source:
        forall (i:nat),
          (i > hb')%nat ->
          forall (cnti1: containsThread cstate1 i),
          match_thread_source (source_match) j
                              (getThreadC cnti1)
                              (restrPermMap (memcompat1 i cnti1).1)
                              (getThreadC (same_length_contains same_length cnti1))
                              (restrPermMap (memcompat2 i (same_length_contains same_length cnti1)).1)
    ; mtch_target:
        forall (i:nat),
          (i < hb')%nat ->
          forall (cnti1: containsThread cstate1 i),
          match_thread_target (target_match) j
                              (getThreadC cnti1)
                              (restrPermMap (memcompat1 i cnti1).1)
                              (getThreadC (same_length_contains same_length cnti1))
                              (restrPermMap (memcompat2 i (same_length_contains same_length cnti1)).1)
    ; mtch_compiled:
        forall (i:nat),
          (i = hb')%nat ->
          forall (cnti1: containsThread cstate1 i),
          match_thread_compiled (compiler_match index) j
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

Arguments same_length_contains {Sems Semt ms1 ms2 }.
Arguments memcompat1 {Sems Semt core_data source_match target_match compiler_match index j cstate1 m1 cstate2 m2}.
Arguments memcompat2 {Sems Semt core_data source_match target_match compiler_match index j cstate1 m1 cstate2 m2}.
Arguments contains12 {Sems Semt core_data source_match target_match compiler_match data j cstate1 m1 cstate2 m2} _ {i}.
Arguments contains21 {Sems Semt core_data source_match target_match compiler_match data j cstate1 m1 cstate2 m2} _ {i}.

    
  Section HybridThreadDiagram.
    
    Variable core_data : Type.
    Variable order : core_data -> core_data -> Prop.
    Variable compiler_match : core_data -> meminj -> state (Clight_semantics2 p)  -> state (Asm_semantics tp) -> Prop.
    Variable props : fsim_properties_inj (Clight_semantics2 p) (Asm_semantics tp)
                                         Clight_get_mem Asm_get_mem order compiler_match.
    Notation match_states:=(match_states compiler_match).
    Notation concur_match:=(@concur_match Sems Semt core_data match_source match_target match_states).
    
    Lemma hybrid_thread_diagramc:
      forall (U0 : list nat) (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
        machine_semantics.thread_step (Sem1 Sems Semt hb1 U) genv U0 st1 m1 st1' m1' ->
        forall (cd : core_data) (st2 : C2) (mu : meminj) (m2 : mem),
          concur_match cd mu st1 m1 st2 m2 ->
          exists (st2' : C2) (m2' : mem) (cd' : core_data) (mu' : meminj),
            concur_match cd' mu' st1' m1' st2' m2' /\
            (machine_semantics_lemmas.thread_step_plus (Sem2 Sems Semt hb2 U) genv U0 st2 m2 st2' m2' \/
     machine_semantics_lemmas.thread_step_star (Sem2 Sems Semt hb2 U) genv U0 st2 m2 st2' m2' /\
             order cd' cd).
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
    Admitted.
    
    End HybridThreadDiagram.

  Section MachineThreadDiagram.
    
    Variable core_data : Type.
    Variable order : core_data -> core_data -> Prop.
    Variable compiler_match : core_data -> meminj -> state (Clight_semantics2 p)  -> state (Asm_semantics tp) -> Prop.
    Variable props : fsim_properties_inj (Clight_semantics2 p) (Asm_semantics tp)
                                         Clight_get_mem Asm_get_mem order compiler_match.
    Notation match_states:=(match_states compiler_match).
    Notation concur_match:=(@concur_match Sems Semt core_data match_source match_target match_states).

    Lemma machine_thread_diagram:
      forall (U0 : list nat) (tr : list HybridMachineSig.machine_event) (st1 : C1) (m1 : mem) 
        (U' : list nat) (tr' : list HybridMachineSig.machine_event) (st1' : C1) (m1' : mem),
        machine_semantics.machine_step (Sem1 Sems Semt hb1 U) genv U0 tr st1 m1 U' tr' st1' m1' ->
        forall (cd : core_data) (st2 : C2) (mu : meminj) (m2 : mem),
          concur_match cd mu st1 m1 st2 m2 ->
          exists (st2' : C2) (m2' : mem) (cd' : core_data),
            concur_match cd' mu st1' m1' st2' m2' /\
            machine_semantics.machine_step (Sem2 Sems Semt hb2 U) genv U0 tr st2 m2 U' tr' st2' m2'.
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
    Admitted.
    
  End MachineThreadDiagram.

  (** *The one_compiled_thread_simulation*)
  Lemma one_compiled_thread_simulation:
    exists (core_data: Type), exists (core_ord : core_data -> core_data -> Prop),
        exists compiler_match, exists v:val,
            HybridMachine_simulation
              Sems Semt hb1 hb2 U genv ge_inv init_inv halt_inv
              core_data core_ord
              (concur_match _ _ core_data match_source
                            match_target compiler_match)  v.
  Proof.
  pose proof program_forward_sim as HH.
  inversion HH.
  exists (index).
  exists (order).
  exists (match_states match_states0).
  exists Vundef. (*THIS SHOULD DISAPEAR*)
  constructor.
  - (*ge_inv*)
    admit.
  - (* core_initial*)
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
    eapply hybrid_thread_diagramc; eauto.
    
  - (*machine_diagram*)
    eapply machine_thread_diagram; eauto.

  - (*thread_halted *)
    admit.
    
  - (*thread_running*)
    admit.
  Admitted.

End OneThreadCompiledProofs.

End OneThreadCompiled.

Section NThredCompiled.
  Variable (hb': nat).
  Notation hb0:= (Some 0%nat).
  Notation hbn:= (Some hb').
  Variable U: seq.seq nat.

  Notation C0:= (t_ (HybridMachine.ThreadPool hb0 Sems Semt)).
  Notation Cn:= (t_ (HybridMachine.ThreadPool hbn Sems Semt)).
  Notation G0:= (semG (HybridMachine.Sem hb0 Sems Semt)) .
  Notation Gn:= (semG (HybridMachine.Sem hbn Sems Semt)).

  (*The two following globals must be taken from the program...*)
  (*and they are probaly the smae global??? *)
  Variable genv: (semG Sems * semG Semt)%type.
  
  (*What are these!!!*)
  Variable (ge_inv: G0 -> Gn -> Prop).
  Variable init_inv : meminj -> G0 -> list val -> mem -> Gn -> list val -> mem -> Prop.
  Variable halt_inv : (*SM_Injection*)meminj -> G0 -> val -> mem -> Gn -> val -> mem -> Prop.

  Variable source_match : (*SM_Injection*)meminj -> (semC Sems) -> mem -> (semC Sems) -> mem -> Prop.
  Variable target_match : (*SM_Injection*)meminj -> (semC Semt) -> mem -> (semC Semt) -> mem -> Prop.
  
  Definition Nconcur_match':
    (meminj -> semC Sems -> mem -> semC Sems -> mem -> Prop) ->
    (meminj -> semC Semt -> mem -> semC Semt -> mem -> Prop) ->
    forall (core_data: Type) (core_ord:core_data -> core_data -> Prop),
    (core_data -> meminj -> semC Sems -> mem -> semC Semt -> mem -> Prop) ->
    core_data -> meminj -> C0 -> mem -> Cn -> mem -> Prop.
  Admitted. 

  Notation Nconcur_match:=(Nconcur_match' match_source match_target).
  
  Lemma N_compiled_thread_simulation:
    exists (core_data: Type), exists (core_ord : core_data -> core_data -> Prop),
      exists compiler_match, exists v:val,
          HybridMachine_simulation
            Sems Semt hb0 hbn U genv ge_inv init_inv halt_inv
            core_data core_ord 
            (Nconcur_match core_data core_ord (match_states compiler_match))  v.  
  Proof.
  Admitted.
  
End NThredCompiled.


Section AllThredCompiled.
  Notation hb0:= (Some 0%nat).
  Notation hball:= None.
  Variable U: seq.seq nat.

  Notation C0:= (t_ (HybridMachine.ThreadPool hb0 Sems Semt)).
  Notation Cn:= (t_ (HybridMachine.ThreadPool hball Sems Semt)).
  Notation G0:= (semG (HybridMachine.Sem hb0 Sems Semt)) .
  Notation Gn:= (semG (HybridMachine.Sem hball Sems Semt)).

  (*The two following globals must be taken from the program...*)
  (*and they are probaly the smae global??? *)
  Variable genv: (semG Sems * semG Semt)%type.
  
  (*What are these!!!*)
  Variable (ge_inv: G0 -> Gn -> Prop).
  Variable init_inv : meminj -> G0 -> list val -> mem -> Gn -> list val -> mem -> Prop.
  Variable halt_inv : (*SM_Injection*)meminj -> G0 -> val -> mem -> Gn -> val -> mem -> Prop.

  Variable source_match : (*SM_Injection*)meminj -> (semC Sems) -> mem -> (semC Sems) -> mem -> Prop.
  Variable target_match : (*SM_Injection*)meminj -> (semC Semt) -> mem -> (semC Semt) -> mem -> Prop.
  
  Definition All_concur_match':
    (meminj -> semC Sems -> mem -> semC Sems -> mem -> Prop) ->
    (meminj -> semC Semt -> mem -> semC Semt -> mem -> Prop) ->
    forall (core_data: Type) (core_ord:core_data -> core_data -> Prop),
    (core_data -> meminj -> semC Sems -> mem -> semC Semt -> mem -> Prop) ->
    core_data -> meminj -> C0 -> mem -> Cn -> mem -> Prop.
  Admitted. 

  Notation Nconcur_match:=(All_concur_match' match_source match_target).
  
  Lemma All_compiled_thread_simulation:
    exists (core_data: Type), exists (core_ord : core_data -> core_data -> Prop),
      exists compiler_match, exists v:val,
          HybridMachine_simulation
            Sems Semt hb0 hball U genv ge_inv init_inv halt_inv
            core_data core_ord 
            (Nconcur_match core_data core_ord (match_states compiler_match))  v.  
  Proof.
  Admitted.
  
End AllThredCompiled.


End HybridProofs.
