Require Import Coq.omega.Omega.
Require Import Clight.
Require Import Memory.
Require Import Values.

Require Import msl.Coqlib2.

Require veric.Clight_core. Import Clight_core.

Require Import concurrency.Smallstep.
Require Import concurrency.x86_context.
Require Import concurrency.HybridMachine_simulation.
Require Import concurrency.compiler_correct.
Require Import concurrency.CoreSemantics_sum.

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


Section HybridStepProof.

  Variable p: program.
  Variable tp: Asm.program. 
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
      CC_core
      Clight.genv
      Clight_step
      Clight_init
      Clight_final
      (Clight_genv p)
      Clight_symbolenv.

  Notation ASM_core:=X86Machines.ErasedMachine.ThreadPool.code.
  Parameter Asm_step: X86SEM.G -> ASM_core * mem -> Events.trace -> ASM_core * mem -> Prop.
  Parameter Asm_init: ASM_core * mem -> Prop.
  Parameter Asm_final: ASM_core * mem -> Integers.Int.int -> Prop.
  Parameter Asm_genv: Asm.program -> X86SEM.G.
  Parameter Asm_symbolenv: Globalenvs.Senv.t.
  Definition Asm_semantics (tp: Asm.program) : semantics:=
    @Semantics_gen
      X86Machines.ErasedMachine.ThreadPool.code
      X86SEM.G
      Asm_step
      Asm_init
      Asm_final
      (Asm_genv tp)
      Asm_symbolenv.

  
  Lemma program_forward_sim:
    Smallstep.forward_simulation (Clight_semantics2 p) (Asm_semantics tp).
  Proof. Admitted.
  
  Lemma program_forward_properties:
    exists (index : Type) (order : index -> index -> Prop)
      (match_states : index -> meminj -> state (Clight_semantics2 p) * mem -> state (Asm_semantics tp) * mem -> Prop
                        ),
                         Smallstep.fsim_properties (Clight_semantics2 p) (Asm_semantics tp) index order match_states .
  Proof. pose proof program_forward_sim as HH.
         inversion HH. exists index, order, match_states; eauto.
  Qed.

  Definition Sems:= Clight p.
  Definition Semt:= X86SEM_rec.  (*How do I pass p to this?*)
  
  Variable hb': nat. (*The hybrid bound!*)
  Definition hb1:= Some hb'.
  Definition hb2:= Some (S hb').

  Variable U: seq.seq nat. (*The schedule*)

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

  (* Variable core_ord_wf : well_founded core_ord.
  Variable thread_match : core_data -> (*SM_Injection*)meminj -> (semC Sems) -> mem -> (semC Semt) -> mem -> Prop. *)

  Definition list_order {A:Type} (order: A -> A -> Prop): list A -> list A -> Prop.
  Admitted.
  Lemma list_order_wf: forall {A} ord, @well_founded A ord -> well_founded (list_order ord).
  Admitted.

  (*Definition list_match
             {index}
            (match_states : index -> meminj ->
                            state (Clight_semantics2 p) * mem ->
                            state (Asm_semantics tp) * mem -> Prop)
    (match_source : meminj ->
                            state (Clight_semantics2 p) -> mem ->
                            state (Clight_semantics2 p) -> mem -> Prop)
    (match_target : meminj ->
                            state (Asm_semantics tp) -> mem ->
                            state (Asm_semantics tp) -> mem -> Prop):
    list index -> meminj -> semC Sems -> mem -> semC Semt -> mem -> Prop.
  (*  |LIST_MATCH: forall lsi j  correct_type: *)
  Admitted. *)

  Context (match_source : meminj ->
                            state (Clight_semantics2 p) -> mem ->
                            state (Clight_semantics2 p) -> mem -> Prop)
    (match_target : meminj ->
                            state (Asm_semantics tp) -> mem ->
                            state (Asm_semantics tp) -> mem -> Prop).
  
  Lemma step_hybrid_simulation:
    exists (core_data: Type), exists (core_ord : core_data -> core_data -> Prop),
        exists thread_match, exists v:val,
    HybridMachine_simulation Sems Semt hb1 hb2 U genv ge_inv init_inv halt_inv
  core_data core_ord thread_match match_source match_target v.  
  pose proof program_forward_sim as HH.
  inversion HH.
  exists (index).
  exists (order).
  exists (fun ls mu c1 m1 c2 m2 => match_states ls mu (c1,m1) (c2,m2)).
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
    intros.
    destruct U0; simpl in H.
    + inversion H; subst.
      inversion HschedN.
    + inversion H; subst.
      inversion HschedN; subst.
      destruct (Compare_dec.lt_eq_lt_dec (S tid) hb') as [[LT | EQ] | LT ].
      * (*S tid < hb'*)
      (*This case it's all in source*)
        inversion Htstep. subst tp' m' ev0.
        eapply event_semantics.ev_step_ax1 in Hcorestep.
        unfold hb1 in *.
        simpl in Hcorestep.
        simpl in Hcode.
        assert (Hcode':=Hcode).
        assert (cnti2:= contains12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H0 _ Htid).
        assert (HHH:= Krun_correct_type_source1  _ _ _ _ _ _ _ _ _ _ _ _ _ _
                                                 H0 _ Htid c).
        eapply HHH in Hcode'.
        2: eapply NPeano.Nat.ltb_lt; omega.
        destruct Hcode' as [c_ Hcode'].
        subst c; clear HHH.

        
        assert (TOPROVE: exists c2_, getThreadC cnti2 =
                                Krun (SState (semC Sems) (semC Semt) c2_)).
        { eapply correct_type_source1.
        destruct TOPROVE as [c2_ Hcode2].
        eapply mtch_source in H0; eauto.
        
        
        (*
        Unfocus.
        destruct Hcode as [Hcode c0]; subst c.
        inversion Hcorestep. subst g s m c' m'.
        destruct H3 as [NotAtExt step].*)
        admit.

        
      * (* S tid = hb' *)
        (* equal: one machine in source one in target!!*)
        inversion Htstep. subst tp' m' ev0.
        eapply event_semantics.ev_step_ax1 in Hcorestep.
        unfold hb1 in *.
        simpl in Hcorestep.
        assert (Hcode':= Hcode).
        eapply Hinv in Hcode.
        Focus 2.
        { subst hb'. eapply NPeano.Nat.ltb_lt; omega. }
        Unfocus.
        destruct Hcode as [Hcode c0]; subst c.
        inversion Hcorestep. subst g s m c' m'.
        destruct H3 as [NotAtExt step].
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
        Focus 2. admit. (*previous match. This follows from concur match *)

        destruct step as [i[[s2' m2'] [mu' [STEP' MATCH]]]].
        assert (TOPROVE3: containsThread_ (HybridMachine.ThreadPool hb2 Sems Semt) st2 tid) by admit.
        simpl in Htp'.
        exists (@updThread_ _ _ _ _ st2 TOPROVE3
                       (Krun (TState CC_core X86Machines.ErasedMachine.ThreadPool.code  s2'))
                      (permissions.getCurPerm m2',
                       snd (getThreadR TOPROVE3))).
        exists m2'.
        exists cd. (*This should be updated with the new value!*)
        exists mu'.
        split.
        
        { (*THE match relation*)
          clear STEP'.
          subst st1'; constructor.
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
              Lemma match_source_forward:
                forall mu c1 m1 c2 m2,
                  match_source mu c1 m1 c2 m2 ->
                  forall mu' m1' m2',
                    inject_incr mu mu' ->
                    same_visible m1 m1' ->
                    same_visible m2 m2' ->
                    match_source mu' c1 m1' c2 m2'.
              Admitted.
              eapply match_source_forward.
              * eapply mtch_source; eauto.  
               admit. (* should be provided by the fsim (compcert simulation)*)
              * admit. (* should follwo from some combination of memsem steps. *)
              * admit. (* should follwo from some combination of memsem steps. *)
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
              Lemma match_target_forward:
                forall mu c1 m1 c2 m2,
                  match_target mu c1 m1 c2 m2 ->
                  forall mu' m1' m2',
                    inject_incr mu mu' ->
                    same_visible m1 m1' ->
                    same_visible m2 m2' ->
                    match_target mu' c1 m1' c2 m2'.
              Admitted.
              eapply match_target_forward.
              * eapply mtch_target; eauto.  
               admit. (* should be provided by the fsim (compcert simulation)*)
              * admit. (* should follwo from some combination of memsem steps. *)
              * admit. (* should follwo from some combination of memsem steps. *)
          - intros.
            destruct (NPeano.Nat.eq_dec tid i0).
            + subst tid.
              admit. (*Follows directly from MATCH and the correct update to the list of data*)
            + admit. (*wrong type of states*)
           
        }
        { (*THE MACHINE STEP.*)
          admit. (*This should be standard.*)
        }

      * (* S tid <> hb' ... homogeneous thread is running *)
        inversion Htstep. subst tp' m' ev0.
        eapply event_semantics.ev_step_ax1 in Hcorestep.
        unfold hb1 in *.
        simpl in Hcorestep.
        assert (Hcode':= Hcode).
        eapply Hinv in Hcode.
        
        Focus 2.
        { rewrite <- e; simpl.
          clear. induction tid; auto. }
        Unfocus.
        destruct Hcode as [Hcode c0]; subst c.
        inversion Hcorestep. subst g s m c' m'.
        destruct H3 as [NotAtExt step].
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
        Focus 2. admit. (*previous match. This follows from concur match *)

        destruct step as [i[[s2' m2'] [mu' [STEP' MATCH]]]].
        assert (TOPROVE3: containsThread_ (HybridMachine.ThreadPool hb2 Sems Semt) st2 tid) by admit.
        simpl in Htp'.
        exists (@updThread_ _ _ _ _ st2 TOPROVE3
                       (Krun (TState CC_core X86Machines.ErasedMachine.ThreadPool.code  s2'))
                      (permissions.getCurPerm m2',
                       snd (getThreadR TOPROVE3))).
        
        
        unfold Step in fsim_simulation.
        eapply fsim_simulation in step.
        eapply props0 in step.
        eapply HH in step.
        

        
      * (*not equal: uncompiled thread is running!!*)
        admit. (*Use an injection mem_sem argumetn*)
        
      
    