(*CompCert imports*)
Require Import Events.
Require Import Memory.
Require Import AST.
Require Import Coqlib.
Require Import compcert.common.Values.
Require Import Maps.
Require Import Integers.
Require Import Globalenvs.

Require Import sepcomp.Coqlib2. 

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.mem_interpolants.
Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.compiler_correctness.

Require Import sepcomp.forward_simulations_trans.

Require Import sepcomp.compiler_correctness_trans.

Section cc_sim_trans.
Lemma cc_trans_CaseEq: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : CoopCoreSem (Genv.t F1 V1) C1)
     (Sem2 : CoopCoreSem (Genv.t F2 V2) C2)
     (Sem3 : CoopCoreSem (Genv.t F3 V3) C3)
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3)
     (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
     (e12 : prog_main P1 = prog_main P2)
     (g12: CompilerCorrectness.GenvHyp P1 P2)
     (Eq_init12 : forall m1 : mem,
            Genv.init_mem P1 = Some m1 -> Genv.init_mem P2 = Some m1)
 (*    (Eq_init12 : forall m1 : mem,
          initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
          exists m2 : mem,
            initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\ m1 = m2)
 *)
    (SimEq12 : Forward_simulation_eq.Forward_simulation_equals Sem1 Sem2 (Genv.globalenv P1)
                               (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_sim I ExternIdents epts23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
     (i1: I F1 C1 V1 Sem1 P1),
forall entrypoints13 : list (val * val * signature),
entrypoints_compose epts12 epts23 entrypoints13 ->
In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents ->
In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents ->
CompilerCorrectness.cc_sim I ExternIdents entrypoints13 F1 C1 V1 F3 C3 V3
  Sem1 Sem3 P1 P3.
Proof. 
intros F1 C1 V1 F2 C2 V2 F3 C3 V3 Sem1 Sem2 Sem3 ExternIdents epts12 epts23 I  
          P1 P2 P3 ePts12_ok e12 g12 Eq_init12 SimEq12 SIM23 i1.
induction SIM23; intros; subst.
 (*equality pass Sem2 -> Sem3*)  
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2. rename Sem0 into Sem2.
        rename Eq_init into Eq_init23. rename e into e23. rename g into g23. rename R into SimEq23.
                               rename H0 into Extern1. rename H1 into Extern2. rename ePts_ok into ePts23_ok.
                               rename H into EPC. rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_eq with (entrypoints:=entrypoints13);try assumption.
       (*init_mem*)
         intros m1 Ini1. apply Eq_init12 in Ini1.
           apply Eq_init23 in Ini1. apply Ini1.
           (*destruct (Eq_init12 _ Ini1) as [m2 [Ini2 XX]]. subst.
           apply (Eq_init23 _ Ini2). *)
       (*entrypoints_ok*)
           apply ePts_compose1 with (Prg2:=P2)(Epts12:=epts12)(Epts23:=epts23); assumption.
       (*sim_eqeq*)
           eapply Forward_simulation_trans.eqeq; try eassumption.
       (*prog_main*)
           rewrite e12; assumption.
       (*GenvHyp*) 
                   destruct g23 as [Hyp2A Hyp2B].
                   split; intros. rewrite Hyp2A. apply g12. 
                                        rewrite Hyp2B. apply g12.
 (*extension pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2. rename Sem0 into Sem2.
        rename Ext_init into Ext_init23. rename e into e23. rename g into g23. rename R into SimExt23.
                               rename H0 into Extern1. rename H1 into Extern2. rename ePts_ok into ePts23_ok.
                               rename H into EPC. rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_ext with (entrypoints:=entrypoints13); try assumption.
       (*init_mem*)
         intros m1 Ini1. apply Eq_init12 in Ini1.
           apply Ext_init23. apply Ini1.
           (*destruct (Eq_init12 _ Ini1) as [m2 [Ini2 XX]]. subst.
           apply (Ext_init23 _ Ini2).*)
       (*entrypoints_ok*)
           apply ePts_compose1 with (Prg2:=P2)(Epts12:=epts12)(Epts23:=epts23); assumption.
       (*sim_eqext*) 
           eapply Forward_simulation_trans.eqext; try eassumption.
       (*prog_main*)
           rewrite e12; assumption.
       (*GenvHyp*) 
                   destruct g23 as [Hyp2A Hyp2B].
                   split; intros. rewrite Hyp2A. apply g12. 
                                        rewrite Hyp2B. apply g12.
   (*injection pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2. rename Sem0 into Sem2.
        rename Inj_init into Inj_init23. rename e into e23. rename g into g23. rename R into SimInj23.
                               rename H0 into Extern1. rename H1 into Extern2. rename ePts_ok into ePts23_ok.
                               rename H into EPC. rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_inj with (entrypoints:=entrypoints13)(jInit:=jInit); try assumption.
       (*init_mem*)
         intros m Ini1. apply (Inj_init23).
           apply Eq_init12. apply Ini1.
           (*destruct (Eq_init12 _ Ini1) as [m2 [Ini2 XX]]. subst.
           apply (Inj_init23 _ Ini2).*)
       (*entrypoints_ok*)
           eapply ePts_compose2; eassumption.
       (*preserves_globals*) 
         apply meminj_preserves_genv2blocks.
         apply meminj_preserves_genv2blocks in preserves_globals.
         eapply genvs_domain_eq_preserves.
         eapply SimEq12.
         assumption.
       (*sim_eqinj*) 
           eapply Forward_simulation_trans.eqinj; try eassumption.
       (*prog_main*)
             rewrite e12; assumption.
       (*GenvHyp*) 
             destruct g23 as [Hyp2A Hyp2B].
             split; intros. rewrite Hyp2A. apply g12. 
                                   rewrite Hyp2B. apply g12.
       (*externvars*) intros b; intros. 
        specialize (e0 b). (*rewrite Genv.find_var_info_transf in e0.
             specialize (e _ H0). destruct e as [x X].
             rewrite Genv.find_symbol_transf in X.
             exists x. apply X.*)
        admit.
Qed.

Lemma cc_trans_CaseExtends: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : CoopCoreSem (Genv.t F1 V1) C1)
     (Sem2 : CoopCoreSem (Genv.t F2 V2) C2)
     (Sem3 : CoopCoreSem (Genv.t F3 V3) C3)
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3)
     (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
     (e12 : prog_main P1 = prog_main P2)
     (g12: CompilerCorrectness.GenvHyp P1 P2)
     (Ext_init12 : forall m1 : mem,
             Genv.init_mem P1 = Some m1 ->
             exists m2 : mem,
               Genv.init_mem P2 = Some m2 /\ Mem.extends m1 m2)
     (*(Ext_init12 : forall m1 : mem,
               initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
               exists m2 : mem,
                 initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
                 Mem.extends m1 m2)*)
     (SimExt12 :  Forward_simulation_ext.Forward_simulation_extends Sem1 Sem2 (Genv.globalenv P1)
                              (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_sim I ExternIdents epts23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
     (i1: I F1 C1 V1 Sem1 P1),
forall entrypoints13 : list (val * val * signature),
          entrypoints_compose epts12 epts23 entrypoints13 ->
          In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents ->
          In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents ->
CompilerCorrectness.cc_sim I ExternIdents entrypoints13 F1 C1 V1 F3 C3 V3 Sem1 Sem3 P1 P3.
Proof. 
intros F1 C1 V1 F2 C2 V2 F3 C3 V3 Sem1 Sem2 Sem3 ExternIdents epts12 epts23 I  
          P1 P2 P3 ePts12_ok e12 g12 Ext_init12 SimExt12 SIM23 i1.
induction SIM23; intros; subst.
  (*equality pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2.  rename Sem0 into Sem2.
        rename Eq_init into Eq_init23. rename e into e23. rename g into g23. rename R into SimEq23.
                               rename H0 into Extern1. rename H1 into Extern2. rename ePts_ok into ePts23_ok.
                               rename H into EPC. rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_ext with (entrypoints:=entrypoints13); try assumption.
       (*init_mem*)
         intros m1 Ini1.
           destruct (Ext_init12 _ Ini1) as [m2 [Ini2 XX]].
           apply Eq_init23 in Ini2.
           (*destruct Ini2 as [m3 [Ini3 Y]]; subst. *)
           exists m2; split; assumption.
       (*entrypoints_ok*)
           eapply ePts_compose1; eassumption.
       (*sim_exteq*) 
           eapply Forward_simulation_trans.exteq; try eassumption.
       (*prog_main*)
             rewrite e12; assumption.
       (*GenvHyp*) 
             destruct g23 as [Hyp2A Hyp2B].
             split; intros. rewrite Hyp2A. apply g12. 
                                   rewrite Hyp2B. apply g12.
  (*extension pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2.  rename Sem0 into Sem2.
        rename Ext_init into Ext_init23. rename e into e23. rename g into g23. rename R into SimExt23.
                               rename H0 into Extern1. rename H1 into Extern2. rename ePts_ok into ePts23_ok. 
                               rename H into EPC. rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_ext with (entrypoints:=entrypoints13); try assumption.
       (*init_mem*)
         intros m1 Ini1.
           destruct (Ext_init12 _ Ini1) as [m2 [Ini2 MExt12]].
           destruct (Ext_init23 _ Ini2) as [m3 [Ini3 MExt23]]. 
           exists m3; split. assumption.
               eapply extends_trans; eassumption.
       (*entrypoints_ok*)
           eapply ePts_compose1; eassumption.
       (*sim_extext*) 
           eapply Forward_simulation_trans.extext; try eassumption.
       (*prog_main*)
             rewrite e12; assumption.
       (*GenvHyp*) 
             destruct g23 as [Hyp2A Hyp2B].
             split; intros. rewrite Hyp2A. apply g12. 
                                   rewrite Hyp2B. apply g12.
 (*injection pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3.  rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2. rename Sem0 into Sem2.
        rename Inj_init into Inj_init23. rename e into e23. rename g into g23. rename R into SimInj23.
                               rename H0 into Extern1. rename H1 into Extern2. rename ePts_ok into ePts23_ok. 
                               rename H into EPC. rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_inj with (entrypoints:=entrypoints13)(jInit:=jInit); try assumption.
       (*init_mem*)
         intros m1 Ini1.
           destruct (Ext_init12 _ Ini1) as [m2 [Ini2 MExt12]]. 
           destruct (Inj_init23 _ Ini2) as [m3 [Ini3 MIn23]].
           exists m3; split.
                    assumption.
                    eapply Mem.extends_inject_compose; eassumption.
       (*entrypoints_ok*)
           eapply ePts_compose2; eassumption.
       (*preserves_globals*) 
         apply meminj_preserves_genv2blocks.
         apply meminj_preserves_genv2blocks in preserves_globals.
         eapply genvs_domain_eq_preserves.
         eapply SimExt12.
         assumption.
       (*sim_extinj*) 
           eapply Forward_simulation_trans.extinj; try eassumption.
       (*prog_main*)
             rewrite e12; assumption.
       (*GenvHyp*) 
             destruct g23 as [Hyp2A Hyp2B].
             split; intros. rewrite Hyp2A. apply g12. 
                                  rewrite Hyp2B. apply g12.
       (*externvars*) admit. (*preservation of externvars by extension phases even if V1->V2 etc*)
Qed.


Lemma cc_trans_CaseInject: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : CoopCoreSem (Genv.t F1 V1) C1)
     (Sem2 : CoopCoreSem (Genv.t F2 V2) C2)
     (Sem3 : CoopCoreSem (Genv.t F3 V3) C3)
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3)
     (e12 : prog_main P1 = prog_main P2)
     (g12: CompilerCorrectness.GenvHyp P1 P2)
     (VarsOK1: CompilerCorrectness.externvars_ok P1 ExternIdents)
     (j12 : meminj)
     (ePts12_ok : CompilerCorrectness.entryPts_inject_ok P1 P2 j12 ExternIdents epts12) 
     (Inj_init12 : forall m1 : mem,
             Genv.init_mem P1 = Some m1 ->
             exists m2 : mem,
               Genv.init_mem P2 = Some m2 /\ Mem.inject j12 m1 m2)
(*    (Inj_init12 : forall m1 : mem,
           initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
           exists m2 : mem,
             initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
             Mem.inject j12 m1 m2)
*)
     (PG1: meminj_preserves_globals (Genv.globalenv P1) j12)
     (SimInj12: Forward_simulation_inj.Forward_simulation_inject Sem1 Sem2 (Genv.globalenv P1)
                                 (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_sim I ExternIdents epts23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
     (i1: I F1 C1 V1 Sem1 P1),
forall entrypoints13 : list (val * val * signature),
           entrypoints_compose epts12 epts23 entrypoints13 ->
            In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents ->
            In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents ->
CompilerCorrectness.cc_sim I ExternIdents entrypoints13 F1 C1 V1 F3 C3 V3 Sem1 Sem3 P1 P3.
Proof.
intros F1 C1 V1 F2 C2 V2 F3 C3 V3 Sem1 Sem2 Sem3 ExternIdents epts12 epts23 I  
          P1 P2 P3 e12 g12 VarsOK1 j12 ePts12_ok Inj_init12 PG1 SimInj12 SIM23 i1.
induction SIM23; intros; subst.
 (*equality pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2.  rename Sem0 into Sem2.
        rename Eq_init into Eq_init23. rename e into e23. rename g into g23. rename R into SimEq23.
                               rename H0 into Extern1. rename H1 into Extern2. rename ePts_ok into ePts23_ok.
                               rename H into EPC. rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_inj with (entrypoints:=entrypoints13)(jInit:=j12); try assumption.
       (*init_mem*)
         intros m1 Ini1.
           destruct (Inj_init12 _ Ini1) as [m2 [Ini2 MInj12]].
           exists m2. split; trivial.
           apply Eq_init23. apply Ini2.
       (*entrypoints_ok*)
           eapply ePts_compose3; eassumption.
       (*sim_injeq*) 
            eapply Forward_simulation_trans.injeq; try eassumption.
       (*prog_main*)
             rewrite e12; assumption.
       (*GenvHyp*) 
             destruct g23 as [Hyp2A Hyp2B].
             split; intros. rewrite Hyp2A. apply g12. 
                                  rewrite Hyp2B. apply g12.
 (*extension pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3. rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2.  rename Sem0 into Sem2.
        rename Ext_init into Ext_init23. rename e into e23. rename g into g23. rename R into SimExt23.
                               rename H0 into Extern1. rename H1 into Extern2. rename ePts_ok into ePts23_ok. 
                               rename H into EPC. rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_inj with (entrypoints:=entrypoints13)(jInit:=j12); try assumption.
       (*init_mem*)
         intros m1 Ini1.
           destruct (Inj_init12 _ Ini1) as [m2 [Ini2 MIni12]].
           destruct (Ext_init23 _ Ini2) as [m3 [Ini3 MExt23]]. exists m3. split. assumption.
           eapply Mem.inject_extends_compose; eassumption.
       (*entrypoints_ok*)
           eapply ePts_compose3; eassumption.
       (*sim_injext*) 
            eapply Forward_simulation_trans.injext; try eassumption.
       (*prog_main*)
             rewrite e12; assumption.
       (*GenvHyp*) 
             destruct g23 as [Hyp2A Hyp2B].
             split; intros. rewrite Hyp2A. apply g12. 
                                  rewrite Hyp2B. apply g12.
 (*injection pass Sem2 -> Sem3*) 
        rename C2 into C3. rename V2 into V3. rename F2 into F3. rename P2 into P3.  rename Sem2 into Sem3.
        rename C0 into C2. rename V0 into V2. rename F0 into F2. rename P0 into P2. rename Sem0 into Sem2.
        rename Inj_init into Inj_init23. rename e into e23. rename g into g23. rename R into SimInj23.
                               rename H0 into Extern1. rename H1 into Extern2. rename ePts_ok into ePts23_ok.
                               rename H into EPC. rename i into i2. rename i0 into i3. rename jInit into j23.
       apply CompilerCorrectness.ccs_inj with 
             (entrypoints:=entrypoints13)(jInit:=compose_meminj j12 j23); try assumption.
       (*init_mem*)
         intros m1 Ini1.
           destruct (Inj_init12 _ Ini1) as [m2 [Ini2 Minj12]]. 
           destruct (Inj_init23 _ Ini2) as [m3 [Ini3 Minj23]].
           exists m3; split. assumption.
              eapply Mem.inject_compose; eassumption.
       (*entrypoints_ok*)
           eapply ePts_compose4; eassumption.
       (*preserves_globals*) 
         apply meminj_preserves_genv2blocks.
         apply meminj_preserves_genv2blocks in preserves_globals.
         apply meminj_preserves_genv2blocks in PG1.
         eapply meminj_preserves_globals_ind_compose; try eassumption.
           apply SimInj12.
       (*core_diagram*)
           eapply Forward_simulation_trans.injinj; try eassumption.
       (*prog_main*)
             rewrite e12; assumption.
       (*GenvHyp*) 
             destruct g23 as [Hyp2A Hyp2B].
             split; intros. rewrite Hyp2A. apply g12. 
                                  rewrite Hyp2B. apply g12.
Qed.     

Theorem cc_sim_trans:
     forall ExternIdents entrypoints12 I F1 C1 V1 F2 C2 V2
        (Sem1: CoopCoreSem (Genv.t F1 V1) C1)
        (Sem2: CoopCoreSem (Genv.t F2 V2) C2)
        P1 P2 
        (SIM12: CompilerCorrectness.cc_sim I ExternIdents entrypoints12 F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2)
        F3 V3 C3
        (Sem3: CoopCoreSem (Genv.t F3 V3) C3)
        entrypoints23 P3 
        (SIM23:CompilerCorrectness.cc_sim I ExternIdents entrypoints23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
        entrypoints13 (EPC:entrypoints_compose entrypoints12 entrypoints23 entrypoints13),
        In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  -> 
        In (P2.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  ->
      CompilerCorrectness.cc_sim I ExternIdents entrypoints13 F1 C1 V1 F3 C3 V3 Sem1 Sem3 P1 P3.
Proof.
  intros  ExternIdents epts12 I F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 SIM12.
  induction SIM12; intros F3 V3 C3 Sem3 epts23 P3 SIM23.
  eapply (cc_trans_CaseEq Sem1 Sem2 Sem3); try assumption.
  eapply (cc_trans_CaseExtends Sem1 Sem2 Sem3); assumption.
  eapply (cc_trans_CaseInject Sem1 Sem2 Sem3) with (j12:=jInit); assumption.
Qed.

End cc_sim_trans.

