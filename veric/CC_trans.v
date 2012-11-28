Load loadpath.
Require Import veric.base.
Require Import compcert.Events.
Require Import veric.sim.
Require Import veric.MemoryPushouts.

Definition main_sig : signature := 
       mksignature (nil) (Some AST.Tint).

Definition entrypoints_compose (ep12 ep23 ep13 : list (val * val * signature)): Prop :=
   forall v1 v3 sig, In (v1,v3,sig) ep13 = exists v2, In (v1,v2,sig) ep12 /\ In (v2,v3,sig) ep23.

Lemma cc_trans_CaseEq: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globvar V1)))
     (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globvar V2)))
     (Sem3 : CoreSemantics (Genv.t F3 V3) C3 mem (list (ident * globvar V3)))
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3)
     (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
     (e12 : prog_main P1 = prog_main P2)
     (g12: CompilerCorrectness.GenvHyp P1 P2)
     (Eq_init12 : forall m1 : mem,
          initial_mem Sem1 (Genv.globalenv P1) m1 (prog_vars P1) ->
          exists m2 : mem,
            initial_mem Sem2 (Genv.globalenv P2) m2 (prog_vars P2) /\ m1 = m2)
     (SimEq12 : Sim_eq.Forward_simulation_equals mem (list (ident * globvar V1))
                                (list (ident * globvar V2)) Sem1 Sem2 (Genv.globalenv P1)
                               (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_sim I ExternIdents epts23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
     (i1: I F1 C1 V1 Sem1 P1),
forall entrypoints13 : list (val * val * signature),
entrypoints_compose epts12 epts23 entrypoints13 ->
In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents ->
prog_main P1 = prog_main P2 ->
In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents ->
prog_main P2 = prog_main P3 ->
CompilerCorrectness.cc_sim I ExternIdents entrypoints13 F1 C1 V1 F3 C3 V3
  Sem1 Sem3 P1 P3.
Proof. 
intros F1 C1 V1 F2 C2 V2 F3 C3 V3 Sem1 Sem2 Sem3 ExternIdents epts12 epts23 I  
          P1 P2 P3 ePts12_ok e12 g12 Eq_init12 SimEq12 SIM23 i1.
induction SIM23; intros; subst.
     (*equality pass Sem2 -> Sem3*)  
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2. rename Sem0 into Sem2.
        clear H1 H3. rename Eq_init into Eq_init23. rename e into e23. rename g into g23. rename R into SimEq23.
                               rename H0 into Extern1. rename H2 into Extern2. rename ePts_ok into ePts23_ok. rename H into EPC.
                                rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_eq with (entrypoints:=entrypoints13); try assumption.
         intros m1 Ini1.
           destruct (Eq_init12 _ Ini1) as [m2 [Ini2 XX]]. subst.
           apply (Eq_init23 _ Ini2).
         unfold CompilerCorrectness.entryPts_ok; intros e d EXT.
            destruct (ePts12_ok _ _ EXT) as [b [Find_b1 [Find_bb2 Hb]]].
            exists b; split; trivial.
            destruct (ePts23_ok _ _ EXT) as [bb [Find_b2 [Find_b3 Hbb]]].
            rewrite Find_b2 in Find_bb2. inv Find_bb2.
            split; trivial.
            destruct d. destruct Hb as [X1 [f1 [f2 [Hf1 Hf2]]]].
                 destruct Hbb as [X2 [ff2 [f3 [Hff2 Hf3]]]].
                  rewrite Hff2 in Hf2. inv Hf2.
                  split. rewrite (EPC (Vptr b Int.zero) (Vptr b Int.zero) s). exists  (Vptr b Int.zero). split; assumption.
                  exists f1. exists f3. split; assumption.
         destruct Hb as [v1 [v2 [Hv1 [Hv2 GV12]]]].
           destruct Hbb as [vv2 [v3 [Hvv2 [Hv3 GV23]]]].
           rewrite Hvv2 in Hv2. inv Hv2.
           exists v1. exists v3. split; trivial. split; trivial.
             destruct v1; simpl in *.
              destruct v2; simpl in *.
                destruct v3; simpl in *. 
                destruct GV12 as [? [? ?]].
                rewrite  H. rewrite H0. rewrite H1. assumption.
         destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
           destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
           eapply Sim_eq.Build_Forward_simulation_equals with
                 (core_data:= prod core_data12 core_data23)
                 (match_core := fun d c1 c3 => match d with (d1,d2) => exists c2, match_core12 d1 c1 c2 /\ match_core23 d2 c2 c3 end).
             eapply wf_lex_ord. apply core_ord_wf12. apply core_ord_wf23.
             admit. (*core_diagram
             intros c1 m1 c1' m1' CS1 [d12 d23] c3 [c2 [MC12 MC23]].
                 destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' X]]].
                 destruct X as [CS2 | CS2 ord12'].
                     destruct (core_diagram23 _ _ _ _ H3*)
             (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ H0) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
                  destruct (core_initial23 _ _ _ EP23 _ H0) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,d23). exists c1. exists c3. split; trivial. split; trivial. exists c2. split; trivial.
             (*safely_halted*)
                    intros. rename c2 into c3. destruct cd as [d12 d23]. destruct H as [c2 [MC12 MC23]].
                    apply (core_halted12 _ _ _ _ MC12) in H0.
                    apply (core_halted23 _ _ _ _ MC23) in H0. assumption.
             (*atexternal*)
                    intros. rename st2 into st3. destruct d as [d12 d23]. destruct H as [st2 [MC12 MC23]].
                    apply (core_at_external12 _ _ _ _ _ _ MC12) in H0. destruct H0.
                    apply (core_at_external23 _ _ _ _ _ _ MC23) in H. assumption.  
             (*after_external*)
                    intros. rename st2 into st3. destruct d as [d12 d23]. destruct H as [st2 [MC12 MC23]].
                    destruct (core_at_external12 _ _ _ _ _ _ MC12 H0)  as [AtExt2 _].
                    destruct (core_after_external12 _ _ _ _ _ _ _ MC12 H0 AtExt2 H2 H3) as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    destruct (core_after_external23 _ _ _ _ _ _ _ MC23 AtExt2 H1 H2 H3) as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists c1'. exists c3'. exists (d12',d23'). split; trivial. split; trivial. exists c2'. split; trivial.
             (*prog_main*)
                   rewrite e12; assumption.
             (*GenvHyp*) 
                   destruct g23 as [Hyp2A Hyp2B].
                   split; intros. rewrite Hyp2A. apply g12. 
                                        rewrite Hyp2B. apply g12.
     (*extension pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2. rename Sem0 into Sem2.
        clear H1 H3. rename Extends_init into Ext_init23. rename e into e23. rename g into g23. rename R into SimExt23.
                               rename H0 into Extern1. rename H2 into Extern2. rename ePts_ok into ePts23_ok. rename H into EPC.
                                rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_ext with (entrypoints:=entrypoints13); try assumption.
         intros m1 Ini1.
           destruct (Eq_init12 _ Ini1) as [m2 [Ini2 XX]]. subst.
           apply (Ext_init23 _ Ini2).
         unfold CompilerCorrectness.entryPts_ok; intros e d EXT.
            destruct (ePts12_ok _ _ EXT) as [b [Find_b1 [Find_bb2 Hb]]].
            exists b; split; trivial.
            destruct (ePts23_ok _ _ EXT) as [bb [Find_b2 [Find_b3 Hbb]]].
            rewrite Find_b2 in Find_bb2. inv Find_bb2.
            split; trivial.
            destruct d. destruct Hb as [X1 [f1 [f2 [Hf1 Hf2]]]].
                 destruct Hbb as [X2 [ff2 [f3 [Hff2 Hf3]]]].
                  rewrite Hff2 in Hf2. inv Hf2.
                 split. rewrite (EPC (Vptr b Int.zero) (Vptr b Int.zero) s). exists  (Vptr b Int.zero). split; assumption.
                 exists f1. exists f3. split; assumption.
         destruct Hb as [v1 [v2 [Hv1 [Hv2 GV12]]]].
           destruct Hbb as [vv2 [v3 [Hvv2 [Hv3 GV23]]]].
           rewrite Hvv2 in Hv2. inv Hv2.
           exists v1. exists v3. split; trivial. split; trivial.
             destruct v1; simpl in *.
              destruct v2; simpl in *.
                destruct v3; simpl in *. 
                destruct GV12 as [? [? ?]].
                rewrite  H. rewrite H0. rewrite H1. assumption.
         destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
          destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
           eapply Sim_ext.Build_Forward_simulation_extends with
                 (core_data:= prod core_data12 core_data23)
                 (match_state := fun d c1 m1 c3 m3 => match d with (d1,d2) => exists c2, match_core12 d1 c1 c2 /\ match_core23 d2 c2 m1 c3 m3 end).
             eapply wf_lex_ord. apply core_ord_wf12. apply core_ord_wf23.
             admit. (*core_diagram
             intros c1 m1 c1' m1' CS1 [d12 d23] c3 [c2 [MC12 MC23]].
                 destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' X]]].
                 destruct X as [CS2 | CS2 ord12'].
                     destruct (core_diagram23 _ _ _ _ H3*)
             (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  assert (HT: Forall2 Val.has_type vals (sig_args sig)). eapply forall_lessdef_hastype; eauto.
                  destruct (core_initial12 _ _ _ EP12 _ HT) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ H0 H1 H2) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,d23). exists c1. exists c3. split; trivial. split; trivial. exists c2. split; trivial.
             (*safely_halted*)
                    intros. rename st2 into c3. destruct cd as [d12 d23]. destruct H as [c2 [MC12 MC23]].
                    apply (core_halted12 _ _ _ _ MC12) in H0.
                    apply (core_halted23 _ _ _ _ _ _ MC23) in H0. assumption.
             (*atexternal*)
                    intros. rename st2 into st3. destruct cd as [d12 d23]. destruct H as [st2 [MC12 MC23]].
                    apply (core_at_external12 _ _ _ _ _ _ MC12) in H0. destruct H0.
                    apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in H. assumption.  
             (*after_external*)
                    intros. rename st2 into st3. destruct cd as [d12 d23]. destruct H as [st2 [MC12 MC23]].
                    destruct (core_at_external12 _ _ _ _ _ _ MC12 H0)  as [AtExt2 _].
                    assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). eapply forall_lessdef_hastype; eauto.
                    assert (HRet1:   Val.has_type ret1 (proj_sig_res ef_sig)). eapply lessdef_hastype; eauto.
                    destruct (core_after_external12 _ _ _ _ _ _ _ MC12 H0 AtExt2 HVals1 HRet1) as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    destruct (core_after_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ MC23 AtExt2 H1 H2 H3 H4 H5 H6 H7 H8 H9) as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists c1'. exists c3'. exists (d12',d23'). split; trivial. split; trivial. exists c2'. split; trivial.
             (*prog_main*)
                   rewrite e12; assumption.
             (*GenvHyp*) 
                   destruct g23 as [Hyp2A Hyp2B].
                   split; intros. rewrite Hyp2A. apply g12. 
                                        rewrite Hyp2B. apply g12.
     (*injection pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2. rename Sem0 into Sem2.
        clear H1 H3. rename Inj_init into Inj_init23. rename e into e23. rename g into g23. rename R into SimInj23.
                               rename H0 into Extern1. rename H2 into Extern2. rename ePts_ok into ePts23_ok. rename H into EPC.
                                rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_inj with (entrypoints:=entrypoints13)(jInit:=jInit); try assumption.
         intros m Ini1.
           destruct (Eq_init12 _ Ini1) as [m2 [Ini2 XX]]. subst.
           apply (Inj_init23 _ Ini2).
         unfold CompilerCorrectness.entryPts_inject_ok; intros e d EXT.
            destruct (ePts12_ok _ _ EXT) as [b1 [Find_b1 [Find_bb2 Hb]]].
            destruct (ePts23_ok _ _ EXT) as [b2 [b3 [Find_b2 [Find_b3 [initB2 Hbb]]]]].
            rewrite Find_b2 in Find_bb2. inv Find_bb2.
            exists b1. exists b3.
            split; trivial.  split; trivial.  split; trivial.
            destruct d. destruct Hb as [X1 [f1 [f2 [Hf1 Hf2]]]].
                 destruct Hbb as [X2 [ff2 [f3 [Hff2 Hf3]]]].
                  rewrite Hff2 in Hf2. inv Hf2.
                 split. rewrite (EPC (Vptr b1 Int.zero) (Vptr b3 Int.zero) s). exists  (Vptr b1 Int.zero). split; assumption.
                 exists f1. exists f3. split; assumption.
         destruct Hb as [v1 [v2 [Hv1 [Hv2 GV12]]]].
           destruct Hbb as [vv2 [v3 [Hvv2 [Hv3 GV23]]]].
           rewrite Hvv2 in Hv2. inv Hv2.
           exists v1. exists v3. split; trivial. split; trivial.
             destruct v1; simpl in *.
              destruct v2; simpl in *.
                destruct v3; simpl in *. 
                destruct GV12 as [? [? ?]].
                rewrite  H. rewrite H0. rewrite H1. assumption.
         admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) jInit  from meminj_preserves_globals (Genv.globalenv P2) jInit*)
         destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
         destruct SimInj23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
           eapply Sim_inj.Build_Forward_simulation_inject with
                 (core_data:= prod core_data12 core_data23)
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,d2) => exists c2, match_core12 d1 c1 c2 /\ match_core23 d2 j c2 m1 c3 m3 end).
             eapply wf_lex_ord. apply core_ord_wf12. apply core_ord_wf23.
             admit. (*core_diagram
             intros c1 m1 c1' m1' CS1 [d12 d23] c3 [c2 [MC12 MC23]].
                 destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' X]]].
                 destruct X as [CS2 | CS2 ord12'].
                     destruct (core_diagram23 _ _ _ _ H3*)
             (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). eapply forall_valinject_hastype; eauto.
                  destruct (core_initial12 _ _ _ EP12 _ HT) as [d12 [c11 [c2 [Ini1 [Ini2 MC12]]]]]. rewrite Ini1 in H0. inv H0.
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2 H3) as [d23 [c3 [Ini3 MC23]]].
                  exists (d12,d23). exists c3. split; trivial. exists c2. split; trivial.
             (*safely_halted*)
                    intros. rename c2 into c3. destruct cd as [d12 d23]. destruct H as [c2 [MC12 MC23]].
                    apply (core_halted12 _ _ _ _ MC12) in H0.
                    apply (core_halted23 _ _ _ _ _ _ _ MC23) in H0. assumption.
             (*atexternal*)
                    intros. rename st2 into st3. destruct cd as [d12 d23]. destruct H as [st2 [MC12 MC23]].
                    apply (core_at_external12 _ _ _ _ _ _ MC12) in H0. destruct H0.
                    apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in H. 
                    destruct H as [MInj12 [PG2 X]]. 
                    split. trivial. 
                    split; try assumption. 
                    admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) j  from meminj_preserves_globals (Genv.globalenv P2) j for any j*)  
             (*after_external*)
                    intros. rename st2 into st3. destruct cd as [d12 d23]. destruct H0 as [st2 [MC12 MC23]].
                    destruct (core_at_external12 _ _ _ _ _ _ MC12 H1)  as [AtExt2 HVals1].
                    assert (HRet1:   Val.has_type ret1 (proj_sig_res ef_sig)). eapply valinject_hastype; eassumption.
                    destruct (core_after_external12 _ _ _ _ _ _ _ MC12 H1 AtExt2 HVals1 HRet1) as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    assert (PG2: meminj_preserves_globals (Genv.globalenv P2) j). admit.
                    destruct (core_after_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H MC23 AtExt2 PG2 H3 H4 H5 H6 H7 H8 H9 H10 H11) as [d23' [c22' [c3' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',d23'). exists c1'. exists c3'. split; trivial. split; trivial. exists c2'. split; trivial.
             (*prog_main*)
                   rewrite e12; assumption.
             (*GenvHyp*) 
                   destruct g23 as [Hyp2A Hyp2B].
                   split; intros. rewrite Hyp2A. apply g12. 
                                        rewrite Hyp2B. apply g12.
             (*externvars*) admit. (*preservation of externvars by equality phases even if V1->V2 etc*)
Qed.

Lemma cc_trans_CaseExtends: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globvar V1)))
     (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globvar V2)))
     (Sem3 : CoreSemantics (Genv.t F3 V3) C3 mem (list (ident * globvar V3)))
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3)
     (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
     (e12 : prog_main P1 = prog_main P2)
     (g12: CompilerCorrectness.GenvHyp P1 P2)
     (Ext_init12 : forall m1 : mem,
               initial_mem Sem1 (Genv.globalenv P1) m1 (prog_vars P1) ->
               exists m2 : mem,
                 initial_mem Sem2 (Genv.globalenv P2) m2 (prog_vars P2) /\
                 Mem.extends m1 m2)
     (SimExt12 :  Sim_ext.Forward_simulation_extends (list (ident * globvar V1))
                                (list (ident * globvar V2)) Sem1 Sem2 (Genv.globalenv P1)
                              (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_sim I ExternIdents epts23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
     (i1: I F1 C1 V1 Sem1 P1),
forall entrypoints13 : list (val * val * signature),
entrypoints_compose epts12 epts23 entrypoints13 ->
In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents ->
prog_main P1 = prog_main P2 ->
In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents ->
prog_main P2 = prog_main P3 ->
CompilerCorrectness.cc_sim I ExternIdents entrypoints13 F1 C1 V1 F3 C3 V3
  Sem1 Sem3 P1 P3.
Proof. 
intros F1 C1 V1 F2 C2 V2 F3 C3 V3 Sem1 Sem2 Sem3 ExternIdents epts12 epts23 I  
          P1 P2 P3 ePts12_ok e12 g12 Ext_init12 SimExt12 SIM23 i1.
induction SIM23; intros; subst.
     (*equality pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2.  rename Sem0 into Sem2.
        clear H1 H3. rename Eq_init into Eq_init23. rename e into e23. rename g into g23. rename R into SimEq23.
                               rename H0 into Extern1. rename H2 into Extern2. rename ePts_ok into ePts23_ok. rename H into EPC.
                                rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_ext with (entrypoints:=entrypoints13); try assumption.
         intros m1 Ini1.
           destruct (Ext_init12 _ Ini1) as [m2 [Ini2 XX]].
           apply Eq_init23 in Ini2. destruct Ini2 as [m3 [Ini3 Y]]; subst. exists m3; split; assumption.
         unfold CompilerCorrectness.entryPts_ok; intros e d EXT.
            destruct (ePts12_ok _ _ EXT) as [b [Find_b1 [Find_bb2 Hb]]].
            destruct (ePts23_ok _ _ EXT) as [bb [Find_b2 [Find_b3 Hbb]]].
            rewrite Find_b2 in Find_bb2. inv Find_bb2.
            exists b; split; trivial.
            split; trivial.
            destruct d. destruct Hb as [X1 [f1 [f2 [Hf1 Hf2]]]].
                 destruct Hbb as [X2 [ff2 [f3 [Hff2 Hf3]]]].
                  rewrite Hff2 in Hf2. inv Hf2.
                 split. rewrite (EPC (Vptr b Int.zero) (Vptr b Int.zero) s). exists  (Vptr b Int.zero). split; assumption.
                 exists f1. exists f3. split; assumption.
         destruct Hb as [v1 [v2 [Hv1 [Hv2 GV12]]]].
           destruct Hbb as [vv2 [v3 [Hvv2 [Hv3 GV23]]]].
           rewrite Hvv2 in Hv2. inv Hv2.
           exists v1. exists v3. split; trivial. split; trivial.
             destruct v1; simpl in *.
              destruct v2; simpl in *.
                destruct v3; simpl in *. 
                destruct GV12 as [? [? ?]].
                rewrite  H. rewrite H0. rewrite H1. assumption.
         destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
         destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
           eapply Sim_ext.Build_Forward_simulation_extends with
                 (core_data:= prod core_data12 core_data23)
                 (match_state := fun d c1 m1 c3 m3 => match d with (d1,d2) => exists c2, match_core12 d1 c1 m1 c2 m3 /\ match_core23 d2 c2 c3 end).
             eapply wf_lex_ord. apply core_ord_wf12. apply core_ord_wf23.
             admit. (*core_diagram
             intros c1 m1 c1' m1' CS1 [d12 d23] c3 [c2 [MC12 MC23]].
                 destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' X]]].
                 destruct X as [CS2 | CS2 ord12'].
                     destruct (core_diagram23 _ _ _ _ H3*)
             (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ H0 H1 H2) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
                  destruct (core_initial23 _ _ _ EP23 _ H1) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,d23). exists c1. exists c3. split; trivial. split; trivial. exists c2. split; trivial.
             (*safely_halted*)
                    intros. rename st2 into c3. destruct cd as [d12 d23]. destruct H as [c2 [MC12 MC23]].
                    apply (core_halted12 _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [LD [SH2 Ext]]].
                    apply (core_halted23 _ _ _ _ MC23) in SH2. exists v2. split; trivial. split; trivial.
             (*atexternal*)
                    intros. rename st2 into st3. destruct cd as [d12 d23]. destruct H as [st2 [MC12 MC23]].
                    apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [vals2 [Ext [LD [HT2 AtExt2]]]].
                    destruct (core_at_external23 _ _ _ _ _ _ MC23 AtExt2). exists vals2. split; trivial. split; trivial. split; assumption.  
             (*after_external*)
                    intros. rename st2 into st3. destruct cd as [d12 d23]. destruct H as [st2 [MC12 MC23]].
                     rename vals2 into vals3. rename ret2 into ret3.
                    assert (X:=core_at_external12 _ _ _ _ _ _ _ _ MC12 H0). destruct X as [vals2 [Ext [LD [HT2 AtExt2]]]].
                    assert (X:=core_at_external23 _ _ _ _ _ _ MC23 AtExt2). destruct X as [AtExt3 HTargs2]. rewrite AtExt3 in H1. inv H1.
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ _ MC12 H0 AtExt2 LD HT2 H4 H5 H6 H7 H8 H9) as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    destruct (core_after_external23 _ _ _ _ _ _ _ MC23 AtExt2 AtExt3 HT2 H9) as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists c1'. exists c3'. exists (d12',d23'). split; trivial. split; trivial. exists c2'. split; trivial.
             (*prog_main*)
                   rewrite e12; assumption.
             (*GenvHyp*) 
                   destruct g23 as [Hyp2A Hyp2B].
                   split; intros. rewrite Hyp2A. apply g12. 
                                        rewrite Hyp2B. apply g12.
     (*extension pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2.  rename Sem0 into Sem2.
        clear H1 H3. rename Extends_init into Ext_init23. rename e into e23. rename g into g23. rename R into SimExt23.
                               rename H0 into Extern1. rename H2 into Extern2. rename ePts_ok into ePts23_ok. rename H into EPC.
                                rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_ext with (entrypoints:=entrypoints13); try assumption.
         intros m1 Ini1.
           destruct (Ext_init12 _ Ini1) as [m2 [Ini2 MExt12]].
           destruct (Ext_init23 _ Ini2) as [m3 [Ini3 MExt23]]. 
           exists m3; split. assumption.
               eapply extends_trans; eassumption.
         unfold CompilerCorrectness.entryPts_ok; intros e d EXT.
            destruct (ePts12_ok _ _ EXT) as [b [Find_b1 [Find_bb2 Hb]]].
            destruct (ePts23_ok _ _ EXT) as [bb [Find_b2 [Find_b3 Hbb]]].
            rewrite Find_b2 in Find_bb2. inv Find_bb2.
            exists b; split; trivial.
            split; trivial.
            destruct d. destruct Hb as [X1 [f1 [f2 [Hf1 Hf2]]]].
                 destruct Hbb as [X2 [ff2 [f3 [Hff2 Hf3]]]].
                  rewrite Hff2 in Hf2. inv Hf2.
                 split. rewrite (EPC (Vptr b Int.zero) (Vptr b Int.zero) s). exists  (Vptr b Int.zero). split; assumption.
                 exists f1. exists f3. split; assumption.
         destruct Hb as [v1 [v2 [Hv1 [Hv2 GV12]]]].
           destruct Hbb as [vv2 [v3 [Hvv2 [Hv3 GV23]]]].
           rewrite Hvv2 in Hv2. inv Hv2.
           exists v1. exists v3. split; trivial. split; trivial.
             destruct v1; simpl in *.
              destruct v2; simpl in *.
                destruct v3; simpl in *. 
                destruct GV12 as [? [? ?]].
                rewrite  H. rewrite H0. rewrite H1. assumption.
         destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
         destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
           eapply Sim_ext.Build_Forward_simulation_extends with
                 (core_data:= prod core_data12 core_data23)
                 (match_state := fun d c1 m1 c3 m3 => match d with (d1,d2) => exists c2, exists m2, match_core12 d1 c1 m1 c2 m2 /\ match_core23 d2 c2 m2 c3 m3 end).
             eapply wf_lex_ord. apply core_ord_wf12. apply core_ord_wf23.
             admit. (*core_diagram
             intros c1 m1 c1' m1' CS1 [d12 d23] c3 [c2 [MC12 MC23]].
                 destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' X]]].
                 destruct X as [CS2 | CS2 ord12'].
                     destruct (core_diagram23 _ _ _ _ H3*)
             (*initial_core*)
                  intros. rename m2 into m3. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  assert (HT: Forall2 Val.has_type vals (sig_args sig)). eapply forall_lessdef_hastype; eassumption.
                  destruct (core_initial12 _ _ _ EP12 _ _ m1 _ (forall_lessdef_refl vals) HT (extends_refl _)) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ H0 H1 H2) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,d23). exists c1. exists c3. split; trivial. split; trivial. exists c2. exists m1. split; trivial.
             (*safely_halted*)
                    intros. rename st2 into c3. rename m2 into m3. destruct cd as [d12 d23]. destruct H as [c2 [m2 [MC12 MC23]]].
                    apply (core_halted12 _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [V12 [SH2 Ext12]]].
                    apply (core_halted23 _ _ _ _ _ _ MC23) in SH2. destruct SH2 as [v3 [V23 [SH3 Ext23]]].
                    exists v3. split. eapply Val.lessdef_trans; eassumption.
                       split; trivial. eapply extends_trans; eassumption.
             (*atexternal*)
                    intros. rename st2 into st3. rename m2 into m3. destruct cd as [d12 d23]. destruct H as [st2 [m2 [MC12 MC23]]].
                    apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [vals2 [Ext12 [LD12 [HT2 AtExt2]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in AtExt2. destruct AtExt2 as [vals3 [Ext23 [LS23 [HT3 AtExt3]]]]. 
                    exists vals3. split.  eapply extends_trans; eassumption.
                       split. eapply forall_lessdef_trans; eassumption.
                        split; assumption.
             (*after_external*)
                    intros. rename st2 into st3. rename m2 into m3. rename m2' into m3'.  rename vals2 into vals3. rename ret2 into ret3. 
                    destruct cd as [d12 d23]. destruct H as [st2 [m2 [MC12 MC23]]].
                    destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 H0)  as [vals2 [Ext12 [ValsLD12 [HTVals2 AtExt2]]]].
                    destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)  as [vals33 [Ext23 [ValsLD23 [HTVals3 AtExt3]]]].
                    rewrite AtExt3 in H1. inv H1.
                   assert (HTR1: Val.has_type ret1 (proj_sig_res ef_sig)). eapply lessdef_hastype; eassumption.
                    destruct (PUSHOUTS.pushout_EE _ _ _ Ext12 H4) as [m2' [Fwd2 [Ext12' [UnchOn2 Ext23']]]].
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ ret1 ret1 _ _ _ MC12 H0 AtExt2 
                            ValsLD12 HTVals2 H4 Fwd2 UnchOn2 (Val.lessdef_refl _) Ext12' HTR1) as [c1' [c2' [d12' [AftExt1 [AftExt2 MC12']]]]].
                    assert (UnchOn3 :  mem_unchanged_on (loc_out_of_bounds m2) m3 m3').
                        split; intros; eapply H6; trivial.
                                 eapply extends_loc_out_of_bounds; eassumption.
                                 intros. apply H in H10. eapply extends_loc_out_of_bounds; eassumption.
                    specialize (Ext23' _ Ext23 _ H5 H6).
                    destruct (core_after_external23 _ _ _ _ _ _ _ _ ret1 ret3 _ _ _ MC23  AtExt2 AtExt3
                            ValsLD23 HTVals3 Fwd2 H5 UnchOn3 H7 Ext23' H9) as [cc2' [c3' [d23' [AftExt22 [AftExt3 MC23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists c1'. exists c3'. exists (d12',d23'). split; trivial. split; trivial. exists c2'. exists m2'.  split; trivial.
             (*prog_main*)
                   rewrite e12; assumption.
             (*GenvHyp*) 
                   destruct g23 as [Hyp2A Hyp2B].
                   split; intros. rewrite Hyp2A. apply g12. 
                                        rewrite Hyp2B. apply g12.
     (*injection pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3.  rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2. rename Sem0 into Sem2.
        clear H1 H3. rename Inj_init into Inj_init23. rename e into e23. rename g into g23. rename R into SimInj23.
                               rename H0 into Extern1. rename H2 into Extern2. rename ePts_ok into ePts23_ok. rename H into EPC.
                                rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_inj with (entrypoints:=entrypoints13)(jInit:=jInit); try assumption.
         intros m1 Ini1.
           destruct (Ext_init12 _ Ini1) as [m2 [Ini2 MExt12]]. 
           destruct (Inj_init23 _ Ini2) as [m3 [Ini3 MIn23]].
           exists m3; split.
                    assumption.
                    eapply  extends_inject_compose; eassumption.
         unfold CompilerCorrectness.entryPts_inject_ok; intros e d EXT.
            destruct (ePts12_ok _ _ EXT) as [b1 [Find_b1 [Find_bb2 Hb]]].
            destruct (ePts23_ok _ _ EXT) as [b2 [b3 [Find_b2 [Find_b3 [initB2 Hbb]]]]].
            rewrite Find_b2 in Find_bb2. inv Find_bb2.
            exists b1. exists b3.
            split; trivial.  split; trivial.  split; trivial.
            destruct d. destruct Hb as [X1 [f1 [f2 [Hf1 Hf2]]]].
                 destruct Hbb as [X2 [ff2 [f3 [Hff2 Hf3]]]].
                  rewrite Hff2 in Hf2. inv Hf2.
                 split. rewrite (EPC (Vptr b1 Int.zero) (Vptr b3 Int.zero) s). exists  (Vptr b1 Int.zero). split; assumption.
                 exists f1. exists f3. split; assumption.
         destruct Hb as [v1 [v2 [Hv1 [Hv2 GV12]]]].
           destruct Hbb as [vv2 [v3 [Hvv2 [Hv3 GV23]]]].
           rewrite Hvv2 in Hv2. inv Hv2.
           exists v1. exists v3. split; trivial. split; trivial.
             destruct v1; simpl in *.
              destruct v2; simpl in *.
                destruct v3; simpl in *. 
                destruct GV12 as [? [? ?]].
                rewrite  H. rewrite H0. rewrite H1. assumption.
         admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) jInit  from meminj_preserves_globals (Genv.globalenv P2) jInit*)
         destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
         destruct SimInj23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
           eapply Sim_inj.Build_Forward_simulation_inject with
                 (core_data:= prod core_data12 core_data23)
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,d2) => exists c2, exists m2, match_core12 d1 c1 m1 c2 m2 /\ match_core23 d2 j c2 m2 c3 m3 end).
             eapply wf_lex_ord. apply core_ord_wf12. apply core_ord_wf23.
             admit. (*core_diagram
             intros c1 m1 c1' m1' CS1 [d12 d23] c3 [c2 [MC12 MC23]].
                 destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' X]]].
                 destruct X as [CS2 | CS2 ord12'].
                     destruct (core_diagram23 _ _ _ _ H3*)
             (*initial_core*)
                  intros. rename v2 into v3. rename vals2 into vals3. rename m2 into m3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). eapply forall_valinject_hastype; eassumption.
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ ( forall_lessdef_refl _) HT (Mem.extends_refl m1)) as [d12 [c11 [c2 [Ini1 [Ini2 MC12]]]]]. rewrite Ini1 in H0. inv H0.
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2 H3) as [d23 [c3 [Ini3 MC23]]].
                  exists (d12,d23). exists c3. split; trivial. exists c2. exists m1. split; trivial.
             (*safely_halted*)
                    intros. rename c2 into c3. rename m2 into m3.  destruct cd as [d12 d23]. destruct H as [c2 [m2 [MC12 MC23]]].
                    apply (core_halted12 _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [LD12 [SH2 Ext12]]].
                    apply (core_halted23 _ _ _ _ _ _ _ MC23) in SH2. destruct SH2 as [v3 [InjV23 [SH3 InjM23]]].
                    exists v3. split. eapply   val_lessdef_inject_compose; eassumption.
                          split. trivial. eapply extends_inject_compose; eassumption.
             (*atexternal*)
                    intros. rename st2 into st3. rename m2 into m3.  destruct cd as [d12 d23]. destruct H as [st2 [m2 [MC12 MC23]]].
                    apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [vals2 [Ext12 [LD12 [HTVals2 AtExt2]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2. destruct AtExt2 as [Inj23 [PG2 [vals3 [InjVals23 [HTVals3 AtExt3]]]]].
                    split. eapply extends_inject_compose; eassumption.
                    split. admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) j  from meminj_preserves_globals (Genv.globalenv P2) j for any j*)  
                    exists vals3. 
                    split. eapply forall_val_lessdef_inject_compose; eassumption. 
                    split; assumption.
             (*after_external*)
                    intros. rename st2 into st3. rename m2 into m3. rename ret2 into ret3. rename m2' into m3'. 
                    destruct cd as [d12 d23]. destruct H0 as [st2 [m2 [MC12 MC23]]].
                    destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 H1)  as [vals2 [Ext12 [LDVals12 [HTVals2 AtExt2]]]].
                    destruct (core_at_external23 _ _ _ _ _ _ _ _ _  MC23 AtExt2)  as [Inj23 [PG2 [vals3 [InjVals23 [HTVals3 AtExt3]]]]].
                    assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). eapply forall_lessdef_hastype; eassumption.
                    assert (HRet1:   Val.has_type ret1 (proj_sig_res ef_sig)). eapply valinject_hastype; eassumption.
                    destruct (PUSHOUTS.pushout_EI _ _ _ Ext12 H7) as [m2' [Fwd2 [Ext12' [UnchOn2 X]]]].
                    destruct (X _ H8) as [UnchOn2j Ext23']; clear X.
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ ret1 ret1 _ _ _ MC12 H1 AtExt2 
                            LDVals12 HTVals2 H7 Fwd2 UnchOn2 (Val.lessdef_refl _) Ext12' HRet1) as [c1' [c2' [d12' [AftExt1 [AftExt2 MC12']]]]].
                    assert (UnchOn3 :  mem_unchanged_on (loc_out_of_reach j m2) m3 m3').
                        split; intros; eapply H10; trivial.
                                 eapply extends_loc_out_of_reach; eassumption.
                                 intros. apply H0 in H13. eapply extends_loc_out_of_reach; eassumption.
                    specialize (Ext23' _ Inj23 _ H9 H10 _ H3 H4 H5).
                    assert (Sep23: inject_separated j j' m2 m3).
                         intros b. intros. destruct (H4 _ _ _ H0 H12). split; trivial. intros N. apply H13.  inv Ext12. unfold Mem.valid_block. rewrite mext_next. apply N.
                    destruct (core_after_external23 _ j j' _ _ _ _ vals2 ret1 _ _ _ ret3 _ Inj23 MC23 AtExt2 PG2 H3 Sep23 Ext23' H6 Fwd2
                             UnchOn2j H9 UnchOn3 H11)  as [d23' [cc2' [c3' [AftExt22 [AftExt3 MC23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',d23'). exists c1'. exists c3'. split; trivial. split; trivial. exists c2'. exists m2'.  split; trivial.
             (*prog_main*)
                   rewrite e12; assumption.
             (*GenvHyp*) 
                   destruct g23 as [Hyp2A Hyp2B].
                   split; intros. rewrite Hyp2A. apply g12. 
                                        rewrite Hyp2B. apply g12.
             (*externvars*) admit. (*preservation of externvars by extension phases even if V1->V2 etc*)
Qed.


Lemma val_inject_split: forall v1 v3 j1 j2 (V:val_inject (compose_meminj j1 j2) v1 v3),
         exists v2, val_inject j1 v1 v2 /\ val_inject j2 v2 v3.
Proof. intros.
    inv V; unfold compose_meminj in *.
      exists (Vint i). split; constructor.
      exists (Vfloat f). split; constructor.
      remember (j1 b1) as s. destruct s; inv H. destruct p.
           remember (j2 b) as ss. destruct ss; inv H1. destruct p. inv H0.
           exists (Vptr b (Int.add ofs1 (Int.repr z))).
               split. econstructor. rewrite <- Heqs. trivial. trivial.
                         econstructor. rewrite <- Heqss. trivial. rewrite Int.add_assoc. rewrite Int.add_unsigned.  rewrite Int.add_unsigned.   rewrite Int.add_unsigned.  
(*I think in oirder to ensure that the addresses are good we have to require that function return valkues
never return pointers that are not in the domain of the returned memory.
Then we can pull in Mem.inject j1' m1' m2' and use mi_representable*)
Admitted. 

Axioms inj_incr_compose_split: forall j1 j2 j',
             inject_incr (compose_meminj j1 j2) j' ->
             exists j1', exists j2',  inject_incr j1 j1' /\ inject_incr j2 j2' /\ j'=compose_meminj j1' j2'.
(*Probably wrong - maybe we can enforce it together with pushout_II? (unlikely...)*)

Lemma cc_trans_CaseInject: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globvar V1)))
     (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globvar V2)))
     (Sem3 : CoreSemantics (Genv.t F3 V3) C3 mem (list (ident * globvar V3)))
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3)
     (e12 : prog_main P1 = prog_main P2)
     (g12: CompilerCorrectness.GenvHyp P1 P2)
     (VarsOK1: CompilerCorrectness.externvars_ok P1 ExternIdents)
     (j12 : meminj)
     (ePts12_ok : CompilerCorrectness.entryPts_inject_ok P1 P2 j12 ExternIdents epts12)
     (Inj_init12 : forall m1 : mem,
           initial_mem Sem1 (Genv.globalenv P1) m1 (prog_vars P1) ->
           exists m2 : mem,
             initial_mem Sem2 (Genv.globalenv P2) m2 (prog_vars P2) /\
             Mem.inject j12 m1 m2)
     (PG1: meminj_preserves_globals (Genv.globalenv P1) j12)
     (SimInj12: Sim_inj.Forward_simulation_inject (list (ident * globvar V1))
                                 (list (ident * globvar V2)) Sem1 Sem2 (Genv.globalenv P1)
                                 (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_sim I ExternIdents epts23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
     (i1: I F1 C1 V1 Sem1 P1),
forall entrypoints13 : list (val * val * signature),
entrypoints_compose epts12 epts23 entrypoints13 ->
In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents ->
prog_main P1 = prog_main P2 ->
In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents ->
prog_main P2 = prog_main P3 ->
CompilerCorrectness.cc_sim I ExternIdents entrypoints13 F1 C1 V1 F3 C3 V3
  Sem1 Sem3 P1 P3.
Proof.
intros F1 C1 V1 F2 C2 V2 F3 C3 V3 Sem1 Sem2 Sem3 ExternIdents epts12 epts23 I  
          P1 P2 P3 e12 g12 VarsOK1 j12 ePts12_ok Inj_init12 PG1 SimInj12 SIM23 i1.
induction SIM23; intros; subst.
     (*equality pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2.  rename Sem0 into Sem2.
        clear H1 H3. rename Eq_init into Eq_init23. rename e into e23. rename g into g23. rename R into SimEq23.
                               rename H0 into Extern1. rename H2 into Extern2. rename ePts_ok into ePts23_ok. rename H into EPC.
                                rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_inj with (entrypoints:=entrypoints13)(jInit:=j12); try assumption.
         intros m1 Ini1.
           destruct (Inj_init12 _ Ini1) as [m2 [Ini2 MInj12]].
           destruct (Eq_init23 _ Ini2) as [m3 [Ini3 MEq23]]; subst. exists m3; split; assumption.
         unfold CompilerCorrectness.entryPts_inject_ok; intros e d EXT.
            destruct (ePts12_ok _ _ EXT) as [b1 [b2 [Find_b1 [Find_bb2 [Jb1 Hb1]]]]].
            destruct (ePts23_ok _ _ EXT) as [b3 [Find_b2 [Find_b3 Hb2]]].
            rewrite Find_b2 in Find_bb2. inv Find_bb2.
            exists b1; exists b2. split; trivial.
            split; trivial. split; trivial.
            destruct d. destruct Hb1 as [X1 [f1 [f2 [Hf1 Hf2]]]].
                 destruct Hb2 as [X2 [ff2 [f3 [Hff2 Hf3]]]].
                  rewrite Hff2 in Hf2. inv Hf2.
                  split. rewrite (EPC (Vptr b1 Int.zero) (Vptr b2 Int.zero) s). exists  (Vptr b2 Int.zero). split; assumption.
                 exists f1. exists f3. split; assumption.
         destruct Hb1 as [v1 [v2 [Hv1 [Hv2 GV12]]]].
           destruct Hb2 as [vv2 [v3 [Hvv2 [Hv3 GV23]]]].
           rewrite Hvv2 in Hv2. inv Hv2.
           exists v1. exists v3. split; trivial. split; trivial.
             destruct v1; simpl in *.
              destruct v2; simpl in *.
                destruct v3; simpl in *. 
                destruct GV12 as [? [? ?]].
                rewrite  H. rewrite H0. rewrite H1. assumption.
         destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
(*               assert (YY := @eq_simulation_star _ _ _ _ _ _ _ Sem2 Sem3 (Genv.globalenv P2)  (Genv.globalenv P3) entrypoints0).*)
           destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
           eapply Sim_inj.Build_Forward_simulation_inject with
                 (core_data:= prod core_data12 core_data23)
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,d2) => exists c2, match_core12 d1 j c1 m1 c2 m3 /\ match_core23 d2 c2 c3 end).
             eapply wf_lex_ord. apply core_ord_wf12. apply core_ord_wf23.
             admit. (*core_diagram
             intros c1 m1 c1' m1' CS1 [d12 d23] c3 [c2 [MC12 MC23]].
                 destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' X]]].
                 destruct X as [CS2 | CS2 ord12'].
                     destruct (core_diagram23 _ _ _ _ H3*)
             (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 H1 H2 H3) as [d12 [c2 [Ini2 MC12]]].
                  destruct (core_initial23 _ _ _ EP23 _ H3) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,d23). exists c3. split; trivial. exists c2. split; trivial.
             (*safely_halted*)
                    intros. rename c2 into c3. destruct cd as [d12 d23]. destruct H as [c2 [MC12 MC23]].
                    apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [VInj12 [SH2 MInj12]]].
                    apply (core_halted23 _ _ _ _ MC23) in SH2. exists v2. split; trivial. split; trivial.
             (*atexternal*)
                    intros. rename st2 into st3. destruct cd as [d12 d23]. destruct H as [st2 [MC12 MC23]].
                    apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [Minj12 [PG1j [vals2 [VInj12 [HT2 AtExt2]]]]].
                    destruct (core_at_external23 _ _ _ _ _ _ MC23 AtExt2).
                     split; trivial.
                     split; trivial.
                     exists vals2. split; trivial. split; trivial.
             (*after_external*)
                    intros. rename st2 into st3. destruct cd as [d12 d23]. destruct H0 as [st2 [MC12 MC23]].
                    assert (X:=core_at_external12 _ _ _ _ _ _ _ _ _ MC12 H1). destruct X as [MInj12 [PG1j [vals2 [VInj12 [HT2 AtExt2]]]]].
                    assert (X:=core_at_external23 _ _ _ _ _ _ MC23 AtExt2). destruct X as [AtExt3 HTargs2]. 
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ MInj12 MC12 H1 PG1j H3 H4 H5 H6 H7 H8 H9 H10 H11)
                                        as [d12' [c1' [c2' [AftExt1 [AftExt2 MS12']]]]].
                    destruct (core_after_external23 _ _ _ _ _ _ _ MC23 AtExt2 AtExt3 HT2 H11) as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',d23'). exists c1'. exists c3'. split; trivial. split; trivial. exists c2'. split; trivial.
             (*prog_main*)
                   rewrite e12; assumption.
             (*GenvHyp*) 
                   destruct g23 as [Hyp2A Hyp2B].
                   split; intros. rewrite Hyp2A. apply g12. 
                                        rewrite Hyp2B. apply g12.
     (*extension pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2.  rename Sem0 into Sem2.
        clear H1 H3. rename Extends_init into Ext_init23. rename e into e23. rename g into g23. rename R into SimExt23.
                               rename H0 into Extern1. rename H2 into Extern2. rename ePts_ok into ePts23_ok. rename H into EPC.
                                rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_inj with (entrypoints:=entrypoints13)(jInit:=j12); try assumption.
         intros m1 Ini1.
           destruct (Inj_init12 _ Ini1) as [m2 [Ini2 MIni12]].
           destruct (Ext_init23 _ Ini2) as [m3 [Ini3 MExt23]]. exists m3. split. assumption.
           eapply inject_extends_compose; eassumption.
         unfold CompilerCorrectness.entryPts_inject_ok; intros e d EXT.
            destruct (ePts12_ok _ _ EXT) as [b1 [b2 [Find_b1 [Find_bb2 [Jb1 Hb1]]]]].
            destruct (ePts23_ok _ _ EXT) as [b3 [Find_b2 [Find_b3 Hb2]]].
            rewrite Find_b2 in Find_bb2. inv Find_bb2.
            exists b1. exists b2. split; trivial.
            split; trivial.
            destruct d. destruct Hb1 as [X1 [f1 [f2 [Hf1 Hf2]]]].
                 destruct Hb2 as [X2 [ff2 [f3 [Hff2 Hf3]]]].
                  rewrite Hff2 in Hf2. inv Hf2.
                  split; trivial.
                  split. rewrite (EPC (Vptr b1 Int.zero) (Vptr b2 Int.zero) s). exists  (Vptr b2 Int.zero). split; assumption.
                 exists f1. exists f3. split; assumption.
         destruct Hb1 as [v1 [v2 [Hv1 [Hv2 GV12]]]].
           destruct Hb2 as [vv2 [v3 [Hvv2 [Hv3 GV23]]]].
           rewrite Hvv2 in Hv2. inv Hv2.
           split; trivial.
           exists v1. exists v3. split; trivial. split; trivial.
             destruct v1; simpl in *.
              destruct v2; simpl in *.
                destruct v3; simpl in *. 
                destruct GV12 as [? [? ?]].
                rewrite  H. rewrite H0. rewrite H1. assumption.
         destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
           destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
           eapply Sim_inj.Build_Forward_simulation_inject with
                 (core_data:= prod core_data12 core_data23)
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,d2) => exists c2, exists m2, match_core12 d1 j c1 m1 c2 m2 /\ match_core23 d2 c2 m2 c3 m3 end).
             eapply wf_lex_ord. apply core_ord_wf12. apply core_ord_wf23.
             admit. (*core_diagram
             intros c1 m1 c1' m1' CS1 [d12 d23] c3 [c2 [MC12 MC23]].
                 destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' X]]].
                 destruct X as [CS2 | CS2 ord12'].
                     destruct (core_diagram23 _ _ _ _ H3*)
             (*initial_core*)
                  intros. rename m2 into m3. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 H1 H2 H3) as [d12 [c2 [Ini2 MC12]]].
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ (forall_lessdef_refl _) H3 (extends_refl m3)) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,d23). exists c3. split; trivial. exists c2. exists m3. split; trivial.
             (*safely_halted*)
                    intros. rename c2 into c3. rename m2 into m3. destruct cd as [d12 d23]. destruct H as [c2 [m2 [MC12 MC23]]].
                    apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [V12 [SH2 MInj12]]].
                    apply (core_halted23 _ _ _ _ _ _ MC23) in SH2. destruct SH2 as [v3 [V23 [SH3 Ext23]]].
                    exists v3. split. eapply valinject_lessdef; eassumption. 
                       split; trivial. eapply inject_extends_compose; eassumption.
             (*atexternal*)
                    intros. rename st2 into st3. rename m2 into m3. destruct cd as [d12 d23]. destruct H as [st2 [m2 [MC12 MC23]]].
                    apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [Minj12 [PG1j [vals2 [VInj12 [HT2 AtExt2]]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in AtExt2. destruct AtExt2 as [vals3 [Mext23 [LD23 [HT3 AtExt3]]]].
                    split. eapply inject_extends_compose; eassumption.
                    split; trivial. 
                    exists vals3.  split. eapply forall_valinject_lessdef; eassumption.
                        split; assumption.
             (*after_external*)
                    intros. rename st2 into st3. rename m2 into m3. rename m2' into m3'. rename ret2 into ret3. 
                    destruct cd as [d12 d23]. destruct H0 as [st2 [m2 [MC12 MC23]]].
                    destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 H1)  as [Minj12 [PG1j [vals2 [ValsLD12 [HTVals2 AtExt2]]]]].
                    destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)  as [vals3 [MExt23 [ValsLD23 [HTVals3 AtExt3]]]].
                    assert (Sep12: inject_separated j j' m1 m2).
                         intros b; intros. destruct (H4 _ _ _ H0 H12). split; trivial.
                            intros N. apply H14. inv MExt23. unfold Mem.valid_block. rewrite <- mext_next. apply N.
                    destruct (PUSHOUTS.pushout_IE _ _ _ _ Minj12  H7 _ H3 Sep12 H8) as [m2' [Minj12' [Fwd2 [UnchLOORj1_2 MExt23']]]].
                    specialize (MExt23' _ _ MExt23 H9 H10).
                    destruct (core_after_external12 _ j j' _ _ _ _ _ ret1 m1' _ m2' ret3 _ Minj12 MC12 H1 PG1j H3 
                                         Sep12 Minj12' H6 H7 H8 Fwd2 UnchLOORj1_2 H11) as  [d12' [c1' [c2' [AftExt1 [AftExt2 MC12']]]]].
                    assert (UnchLOOB23_3': mem_unchanged_on (loc_out_of_bounds m2) m3 m3'). 
                         eapply inject_LOOR_LOOB; eassumption.
                    destruct (core_after_external23 _ _ _ _ _ _ _ _ ret3 ret3 _ _ _ MC23 AtExt2 AtExt3 ValsLD23 HTVals3 Fwd2  H9 
                                     UnchLOOB23_3' (Val.lessdef_refl _) MExt23' H11) as [cc2' [c3' [d23' [AftExt22 [AftExt3 MC23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',d23'). exists c1'. exists c3'. split; trivial. split; trivial. exists c2'. exists m2'.  split; trivial.
             (*prog_main*)
                   rewrite e12; assumption.
             (*GenvHyp*) 
                   destruct g23 as [Hyp2A Hyp2B].
                   split; intros. rewrite Hyp2A. apply g12. 
                                        rewrite Hyp2B. apply g12.
     (*injection pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3.  rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2. rename Sem0 into Sem2.
        clear H1 H3. rename Inj_init into Inj_init23. rename e into e23. rename g into g23. rename R into SimInj23.
                               rename H0 into Extern1. rename H2 into Extern2. rename ePts_ok into ePts23_ok. rename H into EPC.
                                rename i into i2. rename i0 into i3. rename jInit into j23.
       apply CompilerCorrectness.ccs_inj with (entrypoints:=entrypoints13)(jInit:=compose_meminj j12 j23); try assumption.
         intros m1 Ini1.
           destruct (Inj_init12 _ Ini1) as [m2 [Ini2 Minj12]]. 
           destruct (Inj_init23 _ Ini2) as [m3 [Ini3 Minj23]].
           exists m3; split. assumption.
              eapply Mem.inject_compose; eassumption.
         unfold CompilerCorrectness.entryPts_inject_ok; intros e d EXT.
            destruct (ePts12_ok _ _ EXT) as [b1 [b2 [Find_b1 [Find_bb2 [j12b1 Hb]]]]].
            destruct (ePts23_ok _ _ EXT) as [bb2 [b3 [Find_b2 [Find_b3 [j23b2 Hbb]]]]].
            rewrite Find_b2 in Find_bb2. inv Find_bb2.
            exists b1. exists b3.
            split; trivial.  split; trivial.  split. unfold compose_meminj. rewrite j12b1. rewrite j23b2. rewrite Zplus_0_l. trivial.
            destruct d. destruct Hb as [X1 [f1 [f2 [Hf1 Hf2]]]].
                 destruct Hbb as [X2 [ff2 [f3 [Hff2 Hf3]]]].
                  rewrite Hff2 in Hf2. inv Hf2.
                 split. rewrite (EPC (Vptr b1 Int.zero) (Vptr b3 Int.zero) s). exists  (Vptr b2 Int.zero). split; assumption.
                 exists f1. exists f3. split; assumption.
         destruct Hb as [v1 [v2 [Hv1 [Hv2 GV12]]]].
           destruct Hbb as [vv2 [v3 [Hvv2 [Hv3 GV23]]]].
           rewrite Hvv2 in Hv2. inv Hv2.
           exists v1. exists v3. split; trivial. split; trivial.
             destruct v1; simpl in *.
              destruct v2; simpl in *.
                destruct v3; simpl in *. 
                destruct GV12 as [? [? ?]].
                rewrite  H. rewrite H0. rewrite H1. assumption.
         admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) jInit  from meminj_preserves_globals (Genv.globalenv P2) jInit*)
         destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
           destruct SimInj23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
           eapply Sim_inj.Build_Forward_simulation_inject with
                 (core_data:= prod core_data12 core_data23)
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,d2) => exists c2, exists m2, exists j1, exists j2, j = compose_meminj j1 j2 /\
                                                                                                 match_core12 d1 j1 c1 m1 c2 m2 /\ match_core23 d2 j2 c2 m2 c3 m3 
                                                                                     end).
             eapply wf_lex_ord. apply core_ord_wf12. apply core_ord_wf23.
             admit. (*core_diagram
             intros c1 m1 c1' m1' CS1 [d12 d23] c3 [c2 [MC12 MC23]].
                 destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' X]]].
                 destruct X as [CS2 | CS2 ord12'].
                     destruct (core_diagram23 _ _ _ _ H3*)
             (*initial_core*)
                  intros. rename v2 into v3. rename vals2 into vals3. rename m2 into m3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). eapply forall_valinject_hastype; eassumption.
assert (WD1: MEM_WD.mem_wd m1). admit.
                  assert (X: Mem.inject (Mem.flat_inj (Mem.nextblock m1)) m1 m1 /\ j = compose_meminj (Mem.flat_inj (Mem.nextblock m1)) j ).
                      split. apply (MEM_WD.mem_wd_E _ WD1).
                                eapply (MEM_WD.meminj_split_flatinjL _ _ _ H1 WD1).
                  destruct X as [Flat1 XX]. rewrite XX.
                  assert (ValInjFlat1 := forall_val_inject_flat _ _ _ H1 _ _ H2).
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 Flat1 ValInjFlat1 HT) as [d12 [c2 [Ini2 MC12]]].
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2 H3) as [d23 [c3 [Ini3 MC23]]].
                  exists (d12,d23). exists c3. split; trivial. exists c2. exists m1. exists  (Mem.flat_inj (Mem.nextblock m1)). exists j. 
                  split; trivial. split; trivial.
             (*safely_halted*)
                    intros. rename c2 into c3. rename m2 into m3.  destruct cd as [d12 d23].
                    destruct H as [c2 [m2 [j1 [j2 [J [MC12 MC23]]]]]]; subst.
                    apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [ValsInj12 [SH2 Minj12]]].
                    apply (core_halted23 _ _ _ _ _ _ _ MC23) in SH2. destruct SH2 as [v3 [ValsInj23 [SH3 MInj23]]].
                    exists v3. split. apply (val_inject_compose _ _ _ _ _ ValsInj12 ValsInj23).
                          split. trivial. eapply Mem.inject_compose; eassumption.
             (*atexternal*)
                    intros. rename st2 into st3. rename m2 into m3.  destruct cd as [d12 d23].
                    destruct H as [st2 [m2 [j1 [j2 [J [MC12 MC23]]]]]]. subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [MInj12 [PGj1 [vals2 [ValsInj12 [HTVals2 AtExt2]]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2. destruct AtExt2 as [MInj23 [PGj2 [vals3 [ValsInj23 [HTVals3 AtExt3]]]]].
                    split. eapply Mem.inject_compose; eassumption.
                    split. admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) (compose_meminj j1 j2)meminj_preserves_globals (Genv.globalenv P1) j1  and meminj_preserves_globals (Genv.globalenv P2) j2*)  
                    exists vals3. 
                    split.  eapply forall_val_inject_compose; eassumption.
                    split; assumption.
             (*after_external*)
                    intros. rename st2 into st3. rename m2 into m3. rename ret2 into ret3. rename m2' into m3'. 
                    destruct cd as [d12 d23]. destruct H0 as [st2 [m2 [j1 [j2 [J [MC12 MC23]]]]]]. subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H1. destruct H1 as [MInj12 [PGj1 [vals2 [ValsInj12 [HTVals2 AtExt2]]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2. destruct AtExt2 as [MInj23 [PGj2 [vals3 [ValsInj23 [HTVals3 AtExt3]]]]].
                     assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). eapply forall_valinject_hastype; eassumption.
                    assert (HRet1: Val.has_type ret1 (proj_sig_res ef_sig)). eapply valinject_hastype; eassumption.
                    destruct (inj_incr_compose_split _ _ _ H3) as [j1' [j2' [Jinc1 [Jinc2 J']]]]. subst. 
(*Continue here once other pushouts have been proven
ss
specialize (core_after_external12 cd12 j1 j1' st1 st2 m1 e vals1 ret1 m1' m2 m2'
                    destruct (pushout_II _ _ j1 MInj12 _ H7 j1') as [m2' [Fwd2 [Ext12' [UnchOn2 X]]]].
                    destruct (X _ H12) as [UnchOn2j Ext23']; clear X.
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ ret1 ret1 _ _ _ MC12 H5 AtExt2 
                            LDVals12 HTVals2 H11 Fwd2 UnchOn2 (Val.lessdef_refl _) Ext12' HRet1) as [c1' [c2' [d12' [AftExt1 [AftExt2 MC12']]]]].
                    assert (UnchOn3 :  mem_unchanged_on (loc_out_of_reach j m2) m3 m3').
                        split; intros; eapply H14; trivial.
                                 eapply extends_loc_out_of_reach; eassumption.
                                 intros. apply H4 in H17. eapply extends_loc_out_of_reach; eassumption.
                    specialize (Ext23' _ Inj23 _ H13 H14 _ H7 H8 H9).
                    assert (Sep23: inject_separated j j' m2 m3).
                         intros b. intros. destruct (H8 _ _ _ H4 H16). split; trivial. intros N. apply H17.  inv Ext12. unfold Mem.valid_block. rewrite mext_next. apply N.
                    destruct (core_after_external23 _ j j' _ _ _ _ vals2 ret1 _ _ _ ret3 _ Inj23 MC23 AtExt2 PG2 H7 Sep23 Ext23' H10 Fwd2
                             UnchOn2j H13 UnchOn3 H15)  as [cc2' [c3' [d23' [AftExt22 [AftExt3 MC23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists c1'. exists c3'. exists (d12',d23'). split; trivial. split; trivial. exists c2'. exists m2'.  split; trivial.
             (*prog_main*)
                   rewrite e; assumption.
             (*GenvHyp*) 
                   destruct g0 as [Hyp2A Hyp2B].
                   split; intros. rewrite Hyp2A. apply g. 
                                        rewrite Hyp2B. apply g.
             (*externvars*) admit. (*preservation of externvars by extension phases even if V1->V2 etc*)
*)     
       Admitted. 

Theorem cc_trans:
     forall ExternIdents entrypoints12 I F1 C1 V1 F2 C2 V2
        (Sem1: CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globvar V1)))
        (Sem2: CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globvar V2)))
        P1 P2 
        (SIM12: CompilerCorrectness.cc_sim I ExternIdents entrypoints12 F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2)
        F3 V3 C3
        (Sem3: CoreSemantics (Genv.t F3 V3) C3 mem (list (ident * globvar V3)))
        entrypoints23 P3 (SIM23:CompilerCorrectness.cc_sim I ExternIdents entrypoints23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
       entrypoints13 (EPC:entrypoints_compose entrypoints12 entrypoints23 entrypoints13),
        In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  -> P1.(prog_main) = P2.(prog_main) ->
                 In (P2.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  -> P2.(prog_main) = P3.(prog_main) ->
                 CompilerCorrectness.cc_sim I ExternIdents entrypoints13 F1 C1 V1 F3 C3 V3 Sem1 Sem3 P1 P3.
Proof.
  intros  ExternIdents epts12 I F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 SIM12.
  induction SIM12; intros F3 V3 C3 Sem3 epts23 P3 SIM23.
  eapply (cc_trans_CaseEq Sem1 Sem2 Sem3); assumption.
  eapply (cc_trans_CaseExtends Sem1 Sem2 Sem3); assumption.
  eapply (cc_trans_CaseInject Sem1 Sem2 Sem3) with (j12:=jInit); assumption.
Qed.