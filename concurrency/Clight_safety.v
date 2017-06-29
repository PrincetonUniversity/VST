
Require Import Coq.Strings.String.

Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.cfrontend.Clight.

Require Import veric.tycontext.
Require Import veric.semax_prog.

(** *Juicy safetyn*)
Require Import concurrency.semax_initial.
Require Import concurrency.semax_conc.
Require Import concurrency.semax_to_juicy_machine.
Require Import concurrency.permissions.

(** *Erasure Imports*)
Require Import concurrency.erasure_signature.
Require Import concurrency.erasure_proof.
Require Import concurrency.erasure_safety.


Set Bullet Behavior "Strict Subproofs".


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

    (** The initial Juicy Machine *)
    Definition js_initial n := initial_machine_state CS V G ext_link prog all_safe
                                                     init_mem_not_none n.

    Definition Juicy_safety:=
      safety_initial_state CS V G ext_link ext_link_inj prog all_safe init_mem_not_none.

    Import JuicyMachineModule.THE_JUICY_MACHINE.JuicyMachine.
    Import JuicyMachineModule.THE_JUICY_MACHINE.SCH.

    Lemma Clight_csafe2ksafe':
      forall ge st_ m,
        (forall U n, new_valid (nil, st_, m) U ->  csafe ge (U, nil, st_) m n) ->
        (forall U n, new_valid (nil, st_, m) U -> ksafe_new_step ge (U, nil, st_) m n).
    Proof.
      intros.
      assert (HH: forall (U : Sch), new_valid (nil, st_, m) U -> csafe ge (U, nil, st_) m n) by
      (intros; apply H; eauto). clear H.
      generalize ge st_ m HH U H0. clear.
      induction n.
      - econstructor.
      - intros.
        assert (VALID:= H0).
        eapply HH in H0.
        inversion H0; subst.
        + econstructor.
          * econstructor; eauto.
          * intros.
            unfold mk_nstate in *; simpl in *.
            eapply IHn; eauto.
            intros.
            apply csafe_monotone; auto.
        + econstructor.
          unfold new_step, mk_nstate, mk_ostate; simpl.
          econstructor 2.
          instantiate (1:= (nil, tp', m')); eauto.
          intros. eapply IHn; eauto.
          intros.
          simpl in Hsafe.
          clear H.
          unfold new_valid, correct_schedule in H1; simpl in *.
          destruct (schedPeek U0) eqn:PEEK0.
          2: econstructor; unfold halted; simpl;
            rewrite PEEK0; auto.
          
          
          eapply csafe_first_tid; eauto.
          simpl in Hstep.
          assert (new_valid (nil, tp', m') U).
          { eapply step_new_valid in Hstep.
            unfold mk_nstate in Hstep; simpl in *; eauto.
            unfold mk_nstate; simpl; eauto. }
          unfold new_valid, correct_schedule in H; simpl in *.
          inversion Hstep; subst; simpl in *;
            try match goal with
                | [ H: schedPeek ?U = Some _, H0: schedSkip U = U |- _ ] =>
                  symmetry in H0;
                    rewrite end_of_sch in H0;
                    rewrite H in H0; inversion H0
                end.
          (*All three cases are identical*)
          * (*init*)
            rewrite HschedN in *.
            rewrite PEEK0; f_equal.
            inversion Htstep; subst.
            symmetry.
            assert (HH2:forall i j, is_true (ssrbool.is_left (TID.eq_tid_dec i j)) -> i = j).
            { clear. intros. destruct (TID.eq_tid_dec i j); inversion H; auto. }
            apply HH2. eapply H1.
            -- eapply ErasureSafety.ErasureProof.JTP.gssThreadCC.
            -- intros HHH.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.threadHalted in HHH.
               inversion HHH.
               simpl in Hcant.
               unfold ErasureSafety.ErasureProof.JMS.the_sem in Hcant; simpl in *.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.Sem in Hcant.
               rewrite JuicyMachineModule.THE_JUICY_MACHINE.SEM.CLN_msem in Hcant.
               inversion Hcant.
          * rewrite PEEK0, HschedN in *.
            f_equal.
            inversion Htstep; subst.
            symmetry.
            assert (HH2:forall i j, is_true (ssrbool.is_left (TID.eq_tid_dec i j)) -> i = j).
            { clear. intros. destruct (TID.eq_tid_dec i j); inversion H; auto. }
            apply HH2. eapply H1.
            -- eapply ErasureSafety.ErasureProof.JTP.gssThreadCC.
            -- intros HHH.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.threadHalted in HHH.
               inversion HHH.
               simpl in Hcant.
               unfold ErasureSafety.ErasureProof.JMS.the_sem in Hcant; simpl in *.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.Sem in Hcant.
               rewrite JuicyMachineModule.THE_JUICY_MACHINE.SEM.CLN_msem in Hcant.
               inversion Hcant.
          * rewrite PEEK0, HschedN in *.
            f_equal.
            inversion Htstep; subst.
            symmetry.
            assert (HH2:forall i j, is_true (ssrbool.is_left (TID.eq_tid_dec i j)) -> i = j).
            { clear. intros. destruct (TID.eq_tid_dec i j); inversion H; auto. }
            apply HH2. eapply H1.
            -- eapply ErasureSafety.ErasureProof.JTP.gssThreadCC.
            -- intros HHH.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.threadHalted in HHH.
               inversion HHH.
               simpl in Hcant.
               unfold ErasureSafety.ErasureProof.JMS.the_sem in Hcant; simpl in *.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.Sem in Hcant.
               rewrite JuicyMachineModule.THE_JUICY_MACHINE.SEM.CLN_msem in Hcant.
               inversion Hcant.
        + (*machine step*)
          simpl in *.
          econstructor.
          unfold new_step, mk_nstate, mk_ostate; simpl.
          econstructor 2.
          instantiate (1:= (nil, tp', m')); eauto.
          intros. eapply IHn; eauto.


          Unshelve.
          eapply ErasureSafety.ErasureProof.JTP.cntUpdateC; eauto.
          eapply ErasureSafety.ErasureProof.JTP.cntUpdateC; eauto.
          eapply ErasureSafety.ErasureProof.JTP.cntUpdate; eauto.
          rewrite semax_invariant.containsThread_age_tp_to_eq; eauto.
          
    Qed.

    Lemma Clight_csafe2ksafe:
      forall ge st_ m,
        (forall U n, new_valid (nil, st_, m) U ->  csafe ge (U, nil, st_) m n) ->
        (forall U n, new_valid (nil, st_, m) U -> ksafe_new_step ge (U, nil, st_) m n).
    Proof.
      intros.
      assert (HH: forall (U : Sch), new_valid (nil, st_, m) U -> csafe ge (U, nil, st_) m n) by
      (intros; apply H; eauto). clear H.
      generalize ge st_ m HH U H0. clear.
      induction n.
      - econstructor.
      - intros.
        assert (VALID:= H0).
        eapply HH in H0.
        inversion H0; subst.
        + econstructor.
          * econstructor; eauto.
          * intros.
            unfold mk_nstate in *; simpl in *.
            eapply IHn; eauto.
            intros.
            apply csafe_monotone; auto.
        + econstructor.
          unfold new_step, mk_nstate, mk_ostate; simpl.
          econstructor 2.
          instantiate (1:= (nil, tp', m')); eauto.
          intros. eapply IHn; eauto.
          intros.
          simpl in Hsafe.
          clear H.
          unfold new_valid, correct_schedule in H1; simpl in *.
          destruct (schedPeek U0) eqn:PEEK0.
          2: econstructor; unfold halted; simpl;
            rewrite PEEK0; auto.
          
          
          eapply csafe_first_tid; eauto.
          simpl in Hstep.
          assert (new_valid (nil, tp', m') U).
          { eapply step_new_valid in Hstep.
            unfold mk_nstate in Hstep; simpl in *; eauto.
            unfold mk_nstate; simpl; eauto. }
          unfold new_valid, correct_schedule in H; simpl in *.
          inversion Hstep; subst; simpl in *;
            try match goal with
                | [ H: schedPeek ?U = Some _, H0: schedSkip U = U |- _ ] =>
                  symmetry in H0;
                    rewrite end_of_sch in H0;
                    rewrite H in H0; inversion H0
                end.
          (*All three cases are identical*)
          * (*init*)
            rewrite HschedN in *.
            rewrite PEEK0; f_equal.
            inversion Htstep; subst.
            symmetry.
            assert (HH2:forall i j, is_true (ssrbool.is_left (TID.eq_tid_dec i j)) -> i = j).
            { clear. intros. destruct (TID.eq_tid_dec i j); inversion H; auto. }
            apply HH2. eapply H1.
            -- eapply ErasureSafety.ErasureProof.JTP.gssThreadCC.
            -- intros HHH.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.threadHalted in HHH.
               inversion HHH.
               simpl in Hcant.
               unfold ErasureSafety.ErasureProof.JMS.the_sem in Hcant; simpl in *.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.Sem in Hcant.
               rewrite JuicyMachineModule.THE_JUICY_MACHINE.SEM.CLN_msem in Hcant.
               inversion Hcant.
          * rewrite PEEK0, HschedN in *.
            f_equal.
            inversion Htstep; subst.
            symmetry.
            assert (HH2:forall i j, is_true (ssrbool.is_left (TID.eq_tid_dec i j)) -> i = j).
            { clear. intros. destruct (TID.eq_tid_dec i j); inversion H; auto. }
            apply HH2. eapply H1.
            -- eapply ErasureSafety.ErasureProof.JTP.gssThreadCC.
            -- intros HHH.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.threadHalted in HHH.
               inversion HHH.
               simpl in Hcant.
               unfold ErasureSafety.ErasureProof.JMS.the_sem in Hcant; simpl in *.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.Sem in Hcant.
               rewrite JuicyMachineModule.THE_JUICY_MACHINE.SEM.CLN_msem in Hcant.
               inversion Hcant.
          * rewrite PEEK0, HschedN in *.
            f_equal.
            inversion Htstep; subst.
            symmetry.
            assert (HH2:forall i j, is_true (ssrbool.is_left (TID.eq_tid_dec i j)) -> i = j).
            { clear. intros. destruct (TID.eq_tid_dec i j); inversion H; auto. }
            apply HH2. eapply H1.
            -- eapply ErasureSafety.ErasureProof.JTP.gssThreadCC.
            -- intros HHH.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.threadHalted in HHH.
               inversion HHH.
               simpl in Hcant.
               unfold ErasureSafety.ErasureProof.JMS.the_sem in Hcant; simpl in *.
               unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.Sem in Hcant.
               rewrite JuicyMachineModule.THE_JUICY_MACHINE.SEM.CLN_msem in Hcant.
               inversion Hcant.
        + (*machine step*)
          simpl in *.
          econstructor.
          unfold new_step, mk_nstate, mk_ostate; simpl.
          econstructor 2.
          instantiate (1:= (nil, tp', m')); eauto.
          intros. eapply IHn; eauto.


          Unshelve.
          eapply ErasureSafety.ErasureProof.JTP.cntUpdateC; eauto.
          eapply ErasureSafety.ErasureProof.JTP.cntUpdateC; eauto.
          eapply ErasureSafety.ErasureProof.JTP.cntUpdate; eauto.
          rewrite semax_invariant.containsThread_age_tp_to_eq; eauto.
          
    Qed.

    (*this is showing the similarity between JM's initial machine and CoreSemantics initial machine*)
    Definition CoreInitial U r := (semantics.initial_core (MachineSemantics U r)).
    Lemma initial_equivalence: forall u r n
             (g:JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.G)
             b,
          genv_genv g = Genv.globalenv (Ctypes.program_of_program prog) ->
          b =  projT1 ((spr CS V G ext_link prog all_safe init_mem_not_none)) ->
          r = Some (juicy_mem.m_phi (initial_jm CS V G ext_link prog all_safe init_mem_not_none n)) ->
          CoreInitial u r n g (Vptr b Integers.Int.zero) nil =
                             Some (u, nil, initial_machine_state CS V G ext_link prog all_safe init_mem_not_none n).
        intros.
        unfold CoreInitial; simpl.
        unfold init_machine, JuicyMachineModule.THE_JUICY_MACHINE.JSEM.init_mach.
        unfold semantics.initial_core.
        unfold ErasureSafety.ErasureProof.JMS.the_sem.
        unfold JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.Sem.
        rewrite JuicyMachineModule.THE_JUICY_MACHINE.SEM.CLN_msem.
        simpl.
        Lemma BLAHH:
          forall CS V G ext_link prog all_safe init_mem_not_none n,
            JuicyMachineModule.THE_JUICY_MACHINE.JSEM.initial_machine
              (juicy_mem.m_phi
                 (initial_jm CS V G ext_link prog all_safe
                             init_mem_not_none n))
              (initial_corestate CS V G ext_link prog all_safe
                                 init_mem_not_none) =
            initial_machine_state CS V G ext_link prog all_safe init_mem_not_none n.
        Proof.
          intros; simpl.
          unfold initial_machine_state, JuicyMachineModule.THE_JUICY_MACHINE.JSEM.initial_machine.
          f_equal.
        Qed.
        rewrite <- BLAHH.
        subst r; simpl.  
        rewrite H.
        f_equal.
        f_equal; simpl.
        f_equal; simpl.
        

        unfold initial_corestate.
        subst b.
        
        
        destruct spr as (b' & q & [e INIT'] & f'); simpl in *.
        simpl in INIT'.
        rewrite <- H in *.
        destruct (Genv.find_funct_ptr g b') eqn:find_f; inversion INIT'.
        f_equal.
    Qed.

    
    Lemma initial_equivalence': forall U n
             (g:JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.SEM.G)
             ,
          genv_genv g = Genv.globalenv (Ctypes.program_of_program prog) ->
          (semantics.initial_core (MachineSemantics U (Some (juicy_mem.m_phi (initial_jm CS V G ext_link prog all_safe init_mem_not_none n)))))
            n g
            (Vptr (projT1 ((spr CS V G ext_link prog all_safe init_mem_not_none))) Integers.Int.zero) nil =
                             Some (U, nil, initial_machine_state CS V G ext_link prog all_safe init_mem_not_none n).
        intros.
        eapply initial_equivalence; eauto.
    Qed.

    Notation init_jmem n:= (initial_jm CS V G ext_link prog all_safe init_mem_not_none n).
    Notation init_rmap n:=(Some (juicy_mem.m_phi (init_jmem n) )).
    Notation init_genv:=(globalenv prog).
    Notation init_point:=(Vptr (projT1 ((spr CS V G ext_link prog all_safe init_mem_not_none))) Integers.Int.zero).
    Lemma CoreInitial_juicy_safety:
      forall (U : semax_invariant.schedule) (n : nat),
      exists init_st,
        (semantics.initial_core (MachineSemantics U (init_rmap n))) n init_genv init_point nil =
        Some (U, nil, init_st) /\
       csafe (globalenv prog) (U, nil, init_st)
         (proj1_sig (init_mem prog init_mem_not_none)) n.
    Proof.
      eexists; split.
      rewrite initial_equivalence'; eauto.
      eapply Juicy_safety.
    Qed.


    Check ErasureSafety.initial_safety.

    
    Import DryMachineSource.THE_DRY_MACHINE_SOURCE.DMS.DryConc.
    Lemma CoreInitial_dry_safety:
      forall (U : semax_invariant.schedule) (n : nat),
      exists init_mach,
        (semantics.initial_core (MachineSemantics U (Some ( getCurPerm (juicy_mem.m_dry (init_jmem n)), empty_map)))) n init_genv init_point nil =
        Some init_mach /\
       csafe (globalenv prog) init_mach
         (proj1_sig (init_mem prog init_mem_not_none)) n.
    Proof.
      intros U n.
      pose proof (CoreInitial_juicy_safety U n).
      destruct H as (init_jmach & INIT_ok & CSAFE).
      eapply ErasureSafety.initial_safety in INIT_ok; eauto.
      - destruct INIT_ok as (_ & ds & INIT_ok & INV & MATCH); eauto.
        eexists; split; eauto.
        eapply ErasureSafety.erasure_safety; eauto; simpl.
        econstructor; eauto.
      - admit. (*remove*)
      - simpl; unfold ErasureSafety.ErasureProof.match_rmap_perm; intros.
        split; auto; simpl.
        rewrite getCurPerm_correct.
        admit.
      - unfold ErasureSafety.ErasureProof.no_locks_perm.
        intros.
        

          
        erewrite INIT_ok.
        
      pose proof ErasureSafety.initial_safety. in INIT_ok.
      rewrite initial_equivalence'; eauto.
      eapply Juicy_safety.
    Qed.
      
      
      
      unfold (JuicyMachineModule.THE_JUICY_MACHINE.JSEM.ThreadPool.getThreadC).
           
      
    Lemma BLAH: 
      forall (sch : semax_invariant.schedule) (n : nat),
        ksafe_new_step (globalenv prog)
         (sch, nil, initial_machine_state CS V G ext_link prog all_safe init_mem_not_none n)
         (proj1_sig (init_mem prog init_mem_not_none)) n.
    Proof.
      intros.
      eapply Clight_csafe2ksafe.
      simpl.
      
      simpl.
      unfold JuicyMachineModule.THE_JUICY_MACHINE.JuicyMachine.ksafe_new_step;
        simpl.
      
      unfold safety.ksafe.
      
      
      
    (** The initial Dry Machine *)
    Definition dry_initial_perm :=
      getCurPerm( proj1_sig (init_m prog init_mem_not_none)).
    Definition initial_cstate :=
      initial_corestate CS V G ext_link prog all_safe init_mem_not_none.

    Definition ds_initial := DMS.initial_machine
                               dry_initial_perm initial_cstate.