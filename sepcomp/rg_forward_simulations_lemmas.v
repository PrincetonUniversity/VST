Require Import Coqlib.
Require Import ListSet.
Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import AST.
Require Import Globalenvs.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.rg_semantics.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.rg_forward_simulations.


Section Sim_EXT_SIMU_DIAGRAMS.
  Context {G1 C1 G2 C2:Type}
          {Sem1 : RelyGuaranteeSemantics G1 C1}
          {Sem2 : RelyGuaranteeSemantics G2 C2}

          {ge1:G1}
          {ge2:G2}
          {entry_points : list (val * val * signature)}.

  Let core_data := C1.

  Variable match_states: core_data -> C1 -> mem -> C2 -> mem -> Prop.

  Hypothesis match_initial_cores: forall v1 v2 sig,
      In (v1,v2,sig) entry_points ->
        forall vals vals' m1 m2,
          Forall2 Val.lessdef vals vals' ->
          Forall2 (Val.has_type) vals' (sig_args sig) ->
          Mem.extends m1 m2 ->
          exists c1, exists c2,
            initial_core Sem1 ge1 v1 vals = Some c1 /\
            initial_core Sem2 ge2 v2 vals' = Some c2 /\
            match_states c1 c1 m1 c2 m2.

  Hypothesis ext_halted:
      forall cd st1 m1 st2 m2 v1,
        match_states cd st1 m1 st2 m2 ->
        halted Sem1 st1 = Some v1 ->
        exists v2, Val.lessdef v1 v2 /\
            halted Sem2 st2 = Some v2 /\
            Mem.extends m1 m2.

  Hypothesis ext_at_external: 
        forall d st1 m1 st2 m2 e vals1 sig,
          (d = st1 /\ match_states d st1 m1 st2 m2) ->
         at_external Sem1 st1 = Some (e, sig, vals1) ->
         exists vals2,
          Mem.extends m1 m2 /\
          Forall2 Val.lessdef vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args sig) /\
          at_external Sem2 st2 = Some (e,sig,vals2).

  Hypothesis ext_after_external:
      forall d st1 st2 m1 m2 e vals1 vals2 ret1 ret2 m1' m2' sig,
        (d=st1 /\ match_states d st1 m1 st2 m2) ->
        at_external Sem1 st1 = Some (e,sig,vals1) ->
        at_external Sem2 st2 = Some (e,sig,vals2) ->

        Forall2 Val.lessdef vals1 vals2 ->
        Forall2 (Val.has_type) vals2 (sig_args sig) ->
        mem_forward m1 m1' ->
        mem_forward m2 m2' ->

        Mem.unchanged_on (fun b ofs => 
          loc_out_of_bounds m1 b ofs /\ private_block Sem1 st1 b) m2 m2' -> 
       (*ie spill-locations didn't change*)        
        Val.lessdef ret1 ret2 ->
        Mem.extends m1' m2' ->

        Val.has_type ret2 (proj_sig_res sig) ->

        exists st1', exists st2', exists d',
          after_external Sem1 (Some ret1) st1 = Some st1' /\
          after_external Sem2 (Some ret2) st2 = Some st2' /\
          d' = st1' /\ match_states d' st1' m1' st2' m2'. 

Section EXT_SIMULATION_STAR_WF.
Variable order: C1 -> C1 -> Prop.
Hypothesis order_wf: well_founded order.

Hypothesis ext_simulation:
  forall c1 m1 c1' m1',  corestep Sem1 ge1 c1 m1 c1' m1' ->
    forall c2 m2, match_states c1 c1 m1 c2 m2 ->
      exists c2', exists m2', 
        match_states c1' c1' m1' c2' m2' /\
        Mem.unchanged_on (fun b ofs => 
          loc_out_of_bounds m1 b ofs /\ ~private_block Sem1 c1 b) m2 m2' /\
        (corestep_plus Sem2 ge2  c2 m2 c2' m2' \/ 
          (corestep_star Sem2 ge2 c2 m2 c2' m2' /\ order c1' c1)).

Lemma ext_simulation_star_wf: 
  RGForward_simulation_ext.RGForward_simulation_extends Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply RGForward_simulation_ext.Build_RGForward_simulation_extends with
        (core_ord := order)
        (match_state := fun d c1 m1 c2 m2 => d = c1 /\ match_states d c1 m1 c2 m2).
   apply order_wf.
   intros. destruct H0; subst.
              destruct (ext_simulation _ _ _ _ H _ _ H1) as [c2' [m2' [MC' Step]]].
              exists c2'. exists m2'. exists st1'.  split; eauto.
   intros. destruct (match_initial_cores _ _ _ H _ _ _ _ H0 H1 H2) 
    as [c1' [c2' [MIC1 [MIC2 MC]]]].
                 exists c1'. exists c1'. exists c2'. split; eauto.
   intros. destruct H; subst. eapply ext_halted; eauto.
   intros.  destruct H. eapply ext_at_external; eauto.
   intros. destruct H. eapply ext_after_external; eauto.
Qed.

End EXT_SIMULATION_STAR_WF.

Section EXT_SIMULATION_STAR.
  Variable measure: C1 -> nat.
  
  Hypothesis ext_star_simulation:
    forall (c1 : C1) (m1 : mem) (c1' : C1) (m1' : mem),
      corestep Sem1 ge1 c1 m1 c1' m1' ->
      forall (c2 : C2) (m2 : mem),
        match_states c1 c1 m1 c2 m2 ->
        exists c2' : C2,
          exists m2' : mem,
            match_states c1' c1' m1' c2' m2' /\
            Mem.unchanged_on
            (fun (b : block) (ofs : Z) =>
              loc_out_of_bounds m1 b ofs /\ ~ private_block Sem1 c1 b) m2 m2' /\
            (corestep_plus Sem2 ge2 c2 m2 c2' m2' \/ 
             corestep_star Sem2 ge2 c2 m2 c2' m2' /\ ltof C1 measure c1' c1).

Lemma ext_simulation_star: 
  RGForward_simulation_ext.RGForward_simulation_extends Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply ext_simulation_star_wf.
  apply  (well_founded_ltof _ measure).
  intros.
  destruct (ext_star_simulation _ _ _ _ H _ _ H0) as [c2' [m2' [CSP [? MC']]]].
  exists c2'; exists m2'; split; auto.
Qed.

End EXT_SIMULATION_STAR.

Section EXT_SIMULATION_PLUS.
  Variable measure: C1 -> nat. 
  Hypothesis ext_plus_simulation:
    forall c1 m1 c1' m1', corestep Sem1 ge1 c1 m1 c1' m1'  -> 
    forall c2 m2, match_states c1 c1 m1 c2 m2 ->
      exists c2', exists m2', 
        corestep_plus Sem2 ge2 c2 m2 c2' m2' /\ 
        match_states c1' c1' m1' c2' m2' /\
        Mem.unchanged_on
        (fun (b : block) (ofs : Z) =>
          loc_out_of_bounds m1 b ofs /\ ~ private_block Sem1 c1 b) m2 m2'.

Lemma ext_simulation_plus: 
  RGForward_simulation_ext.RGForward_simulation_extends Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  apply ext_simulation_star with (measure:=measure).
  intros. destruct (ext_plus_simulation _ _ _ _ H _ _ H0) as [c2' [m2' [MC [UNC STEP]]]].
  eexists; eexists; split; eauto.
Qed.

End EXT_SIMULATION_PLUS.

End Sim_EXT_SIMU_DIAGRAMS.


Section Sim_INJ_SIMU_DIAGRAMS.
  Context {F1 V1 C1 G2 C2:Type}
          {Sem1 : RelyGuaranteeSemantics (Genv.t F1 V1) C1}
          {Sem2 : RelyGuaranteeSemantics G2 C2}

          {ge1: Genv.t F1 V1} 
          {ge2:G2}
          {entry_points : list (val * val * signature)}. 

  Let core_data := C1.

  Variable match_states: core_data -> meminj -> C1 -> mem -> C2 -> mem -> Prop.

  Hypothesis match_initial_cores: forall v1 v2 sig,
        In (v1,v2,sig) entry_points -> 
       forall vals1 c1 m1 j vals2 m2,
          initial_core Sem1 ge1 v1 vals1 = Some c1 ->
          Mem.inject j m1 m2 -> 
          (*Is this line needed?? 
             (forall w1 w2 sigg,  In (w1,w2,sigg) entry_points -> val_inject j w1 w2) ->*)
          Forall2 (val_inject j) vals1 vals2 ->

          Forall2 (Val.has_type) vals2 (sig_args sig) ->
          exists c2, 
            initial_core Sem2 ge2 v2 vals2 = Some c2 /\
            match_states c1 j c1 m1 c2 m2. 

  Hypothesis inj_halted:forall cd j c1 m1 c2 m2 v1 rty,
      match_states cd j c1 m1 c2 m2 ->
      halted Sem1 c1 = Some v1 ->
      Val.has_type v1 rty -> 
      exists v2, val_inject j v1 v2 /\ 
        halted Sem2 c2 = Some v2 /\
        Val.has_type v2 rty /\
        Mem.inject j m1 m2.

  Hypothesis inj_at_external: 
      forall d j st1 m1 st2 m2 e vals1 sig,
        d = st1 /\ match_states d j st1 m1 st2 m2 ->
        at_external Sem1 st1 = Some (e,sig,vals1) ->
        ( Mem.inject j m1 m2 /\
          meminj_preserves_globals ge1 j /\ (*LENB: also added meminj_preserves_global HERE*)
          exists vals2, Forall2 (val_inject j) vals1 vals2 /\
          Forall2 (Val.has_type) vals2 (sig_args (ef_sig e)) /\
          at_external Sem2 st2 = Some (e,sig,vals2)).

  Hypothesis inj_after_external:
      forall d j j' st1 st2 m1 e vals1 (*vals2*) ret1 m1' m2 m2' ret2 sig c1 c2,
        (d=st1 /\ match_states d j st1 m1 st2 m2) ->
        at_external Sem1 st1 = Some (e,sig,vals1) ->

    (* LENB: we may want to add meminj_preserves_globals ge1 j as another
      asumption here, to get rid of
      meminj_preserved_globals_inject_incr below. But this would
      require spaeicaliing G1 to Genv.t....  Maybe we can specialize
      G1 and G2 of CompCertCoreSem's to Genv F1 V1/Genv F2 V2, but not
      specialize CoreSem's?*)

        meminj_preserves_globals ge1 j -> 

        inject_incr j j' ->
        inject_separated j j' m1 m2 ->
        Mem.inject j' m1' m2' ->
        val_inject_opt j' ret1 ret2 ->

         mem_forward m1 m1'  -> 
         Mem.unchanged_on (fun b ofs => 
           loc_unmapped j b ofs /\ private_block Sem1 c1 b) m1 m1' ->
         mem_forward m2 m2' -> 
         Mem.unchanged_on (fun b ofs => 
           loc_out_of_reach j m1 b ofs /\ private_block Sem2 c2 b) m2 m2' ->
         val_has_type_opt' ret1 (proj_sig_res (ef_sig e)) ->
         val_has_type_opt' ret2 (proj_sig_res (ef_sig e)) ->

      exists st1', exists st2', exists d',
          after_external Sem1 ret1 st1 = Some st1' /\
          after_external Sem2 ret2 st2 = Some st2' /\
          d' = st1' /\ match_states d' j' st1' m1' st2' m2'. 

Section INJ_SIMULATION_STAR_WF.
Variable order: C1 -> C1 -> Prop.
Hypothesis order_wf: well_founded order.

  Hypothesis inj_simulation:
     forall c1 m1 c1' m1',  corestep Sem1 ge1 c1 m1 c1' m1' ->
     forall j c2 m2, match_states c1 j c1 m1 c2 m2 ->
      exists c2', exists m2', exists j', 
        inject_incr j j' /\
        inject_separated j j' m1 m2 /\
        match_states c1' j' c1' m1' c2' m2' /\
        Mem.unchanged_on
        (fun (b : block) (ofs : Z) =>
          loc_unmapped j b ofs /\ ~ private_block Sem1 c1 b) m1 m1' /\
        Mem.unchanged_on
        (fun (b : block) (ofs : Z) =>
          loc_out_of_reach j m1 b ofs /\ ~ private_block Sem2 c2 b) m2 m2' /\
        (corestep_plus Sem2 ge2  c2 m2 c2' m2' \/ 
          (corestep_star Sem2 ge2 c2 m2 c2' m2' /\ order c1' c1)).

Lemma  inj_simulation_star_wf: 
  RGForward_simulation_inj.RGForward_simulation_inject Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply RGForward_simulation_inj.Build_RGForward_simulation_inject with
    (core_ord := order)
    (match_state := fun d j c1 m1 c2 m2 => d = c1 /\ match_states d j c1 m1 c2 m2).
  apply order_wf.
  intros. destruct H0; subst.
  destruct (inj_simulation _ _ _ _ H _ _ _ H1) as 
    [c2' [m2' [j' [INC [SEP [MC' [UNCH1 [UNCH2 Step]]]]]]]].
  exists c2'. exists m2'. exists st1'. exists j'. split; auto. 
  intros. destruct (match_initial_cores _ _ _ H _ _ _ _ _ _ H0 H1 H2 H3) as 
    [c2' [MIC MC]].
  exists c1.  exists c2'. split; eauto.
  intros. destruct H; subst. eapply inj_halted; eauto.
  intros.  destruct H; subst. eapply inj_at_external; eauto.
  intros.  (*destruct H0; subst.*) clear inj_simulation .
  specialize (inj_after_external _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 
    H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12).
  destruct inj_after_external as [c1' [c2' [d' [X1 [X2 [X3 X4]]]]]]. subst.
  exists c1'. exists c1'. exists c2'. split; auto.
Qed.

End INJ_SIMULATION_STAR_WF.

Section INJ_SIMULATION_STAR.
  Variable measure: C1 -> nat.
  
  Hypothesis inj_star_simulation:
    forall c1 m1 c1' m1', corestep Sem1 ge1 c1 m1 c1' m1'  -> 
    forall c2 m2 j, match_states c1 j c1 m1 c2 m2 ->
      (exists c2', exists m2', exists j', 
        inject_incr j j' /\
        inject_separated j j' m1 m2 /\ 
        Mem.unchanged_on
        (fun (b : block) (ofs : Z) =>
          loc_unmapped j b ofs /\ ~ private_block Sem1 c1 b) m1 m1' /\
        Mem.unchanged_on
        (fun (b : block) (ofs : Z) =>
          loc_out_of_reach j m1 b ofs /\ ~ private_block Sem2 c2 b) m2 m2' /\
        match_states c1' j' c1' m1' c2' m2' /\
        (corestep_plus Sem2 ge2 c2 m2 c2' m2' 
          \/ ((measure c1' < measure c1)%nat /\ corestep_star Sem2 ge2 c2 m2 c2' m2'))).

Lemma inj_simulation_star: 
  RGForward_simulation_inj.RGForward_simulation_inject Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  eapply inj_simulation_star_wf.
  apply  (well_founded_ltof _ measure).
  intros. destruct (inj_star_simulation _ _ _ _ H _ _ _ H0) as [c2' H1].
  destruct H1 as [m2' [j' [INC [SEP [UNCH1 [UNCH2 [MC' STEP]]]]]]]. 
  exists c2'. exists m2'. exists j'. split; trivial. split; trivial. split; trivial. 
  split; auto. split; auto.
  destruct STEP as [X1|X1]; subst. left; auto. 
  right. destruct X1. split; auto.
Qed.

End INJ_SIMULATION_STAR.

Section INJ_SIMULATION_PLUS.
  Variable measure: C1 -> nat. 
  Hypothesis inj_plus_simulation:
    forall c1 m1 c1' m1', corestep Sem1 ge1 c1 m1 c1' m1'  -> 
    forall c2 m2 j, match_states c1 j c1 m1 c2 m2 ->
      exists c2', exists m2',  exists j', 
        inject_incr j j' /\
        inject_separated j j' m1 m2 /\ 
        corestep_plus Sem2 ge2 c2 m2 c2' m2' /\ 
        match_states c1' j' c1' m1' c2' m2' /\ 
        Mem.unchanged_on
        (fun (b : block) (ofs : Z) =>
          loc_unmapped j b ofs /\ ~ private_block Sem1 c1 b) m1 m1' /\
        Mem.unchanged_on
        (fun (b : block) (ofs : Z) =>
          loc_out_of_reach j m1 b ofs /\ ~ private_block Sem2 c2 b) m2 m2'.
  
Lemma inj_simulation_plus: 
  RGForward_simulation_inj.RGForward_simulation_inject Sem1 Sem2 ge1 ge2 entry_points.
Proof.
  apply inj_simulation_star with (measure:=measure).
  intros. destruct (inj_plus_simulation _ _ _ _ H _ _ _ H0) 
    as [? [? [? [? [? [? [? [? ?]]]]]]]].
  do 3 eexists. split; eauto. split; eauto.
Qed.

End INJ_SIMULATION_PLUS.

End Sim_INJ_SIMU_DIAGRAMS.