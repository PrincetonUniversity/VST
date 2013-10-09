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
Definition main_sig : signature := mksignature nil (Some AST.Tint).

Lemma cc_sim_coop_sim: forall {F1 C1 V1 F2 C2 V2:Type}
  (Sem1 : CoopCoreSem (Genv.t F1 V1) C1)
  (Sem2 : CoopCoreSem(Genv.t F2 V2) C2)
  (P1 : AST.program F1 V1)
  (P2 : AST.program F2 V2) I epts ExternIdents
  (CCSim: CompilerCorrectness.cc_sim I ExternIdents  epts F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2),
  Forward_simulation.coop_sim Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) epts.
Proof. intros.
  induction CCSim.
  eapply Forward_simulation.coop_sim_eq. apply R.
  eapply Forward_simulation.coop_sim_ext. apply R.
  eapply Forward_simulation.coop_sim_inj. apply R.
Qed.

Lemma coop_sim_cc_sim: forall {F1 C1 V1 F2 C2 V2:Type}
  (Sem1 : CoopCoreSem (Genv.t F1 V1) C1)
  (Sem2 : CoopCoreSem(Genv.t F2 V2) C2)
  (P1 : AST.program F1 V1)
  (P2 : AST.program F2 V2)
  (I: forall F C V
          (Sem : CoopCoreSem (Genv.t F V) C)
          (P : AST.program F V), Prop)
  epts ExternIdents
  (InitMem: forall m1 : mem, Genv.init_mem P1 = Some m1 -> Genv.init_mem P2 = Some m1)
  (Epts: CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts)
  (Main: prog_main P1 = prog_main P2)
  (GENV: CompilerCorrectness.GenvHyp P1 P2)
  (HP1: I F1 C1 V1 Sem1 P1)
  (HP2: I F2 C2 V2 Sem2 P2)
  (Externs: CompilerCorrectness.externvars_ok P1 ExternIdents)
  m (IM: Genv.init_mem P1 = Some m),
  Forward_simulation.coop_sim Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) epts ->
  CompilerCorrectness.cc_sim I ExternIdents  epts F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2.
Proof. intros.
  induction X.
  eapply CompilerCorrectness.ccs_eq;
    try assumption.

  eapply CompilerCorrectness.ccs_ext;
    try assumption. 
    intros. rewrite (InitMem _ H).
    rewrite IM in H. inv H.
    exists m1; split; trivial.
    apply Mem.extends_refl.
  
  eapply CompilerCorrectness.ccs_inj with
    (jInit := Mem.flat_inj (Mem.nextblock m));
    try assumption.

    intros. rewrite (InitMem _ H).
    exists m1; split; trivial.
    rewrite IM in H. inv H.
    eapply Genv.initmem_inject. apply IM.

    intros e; intros.
    destruct (Epts _ _ H) as [b [HB1 [HB2 HB3]]].
    exists b. exists b.
    split; trivial.
    split; trivial.
    split; trivial.
    apply flatinj_I.
    eapply Genv.find_symbol_not_fresh. apply IM. apply HB1.
     
    split; intros.
      apply flatinj_I.
      eapply Genv.find_symbol_not_fresh. apply IM. apply H.
    split; intros.
      apply flatinj_I.
      eapply Genv.find_var_info_not_fresh. apply IM. apply H.
    apply flatinj_E in H0. apply H0.
Qed.

(*It's not quite possible to obtain a transtivity proof for
  cc_sim from the above lemmas plus forward_simulation_trans,
  since the additional condititions on programs also need to
  be transitive*)
Goal  forall ExternIdents entrypoints12 I F1 C1 V1 F2 C2 V2
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
Proof. intros.
  apply cc_sim_coop_sim in SIM12.
  apply cc_sim_coop_sim in SIM23.
  eapply coop_sim_cc_sim.
Focus 9. eapply (Forward_simulation_trans.coop_sim_trans Sem1 Sem2 Sem3).
           apply EPC. apply SIM12. apply SIM23.
Admitted. (*admit is ok - claim is an unnamed "goal".*)

Require Import Wellfounded.
Require Import Relations.

Declare Module MEMAX : MemoryInterpolationAxioms.
(*Now defined in forward_simulations_trans
Definition entrypoints_compose 
  (ep12 ep23 ep13 : list (val * val * signature)): Prop :=
  forall v1 v3 sig, 
  In (v1,v3,sig) ep13 = exists v2, In (v1,v2,sig) ep12 /\ In (v2,v3,sig) ep23.
*)
Lemma ePts_compose1: forall {F1 V1 F2 V2 F3 V3} 
     (Prg1 : AST.program F1 V1) (Prg2 : AST.program F2 V2) 
     (Prg3 : AST.program F3 V3)
     Epts12 Epts23 ExternIdents entrypoints13 
    (EPC : entrypoints_compose Epts12 Epts23 entrypoints13)
    (ePts12_ok : @CompilerCorrectness.entryPts_ok F1 V1 F2 V2 Prg1 Prg2 
                 ExternIdents Epts12)
    (ePts23_ok : @CompilerCorrectness.entryPts_ok F2 V2 F3 V3 Prg2 Prg3
                 ExternIdents Epts23),
CompilerCorrectness.entryPts_ok Prg1 Prg3 ExternIdents entrypoints13.
Proof. 
  intros.
  unfold CompilerCorrectness.entryPts_ok; intros e d EXT.
  destruct (ePts12_ok _ _ EXT) as [b [Find_b1 [Find_bb2 Hb]]].
  exists b; split; trivial.
  destruct (ePts23_ok _ _ EXT) as [bb [Find_b2 [Find_b3 Hbb]]].
  rewrite Find_b2 in Find_bb2. inv Find_bb2.
  split; trivial.
  destruct d. destruct Hb as [X1 [f1 [f2 [Hf1 Hf2]]]].
  destruct Hbb as [X2 [ff2 [f3 [Hff2 Hf3]]]].
  rewrite Hff2 in Hf2. inv Hf2.
  split. rewrite (EPC (Vptr b Int.zero) (Vptr b Int.zero) s). 
  exists  (Vptr b Int.zero). split; assumption.
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
Qed.

Lemma ePts_compose2: forall {F1 V1 F2 V2 F3 V3} 
     (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) 
     (P3 : AST.program F3 V3)
     Epts12 Epts23 ExternIdents entrypoints13 jInit
    (EPC : entrypoints_compose Epts12 Epts23 entrypoints13)
    (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents Epts12)
    (ePts23_ok : CompilerCorrectness.entryPts_inject_ok P2 P3 jInit
                    ExternIdents Epts23),
    CompilerCorrectness.entryPts_inject_ok P1 P3 jInit ExternIdents
                     entrypoints13.
Proof. 
  intros.
  unfold CompilerCorrectness.entryPts_inject_ok; intros e d EXT.
  destruct (ePts12_ok _ _ EXT) as [b1 [Find_b1 [Find_bb2 Hb]]].
  destruct (ePts23_ok _ _ EXT) as [b2 [b3 [Find_b2 [Find_b3 [initB2 Hbb]]]]].
  rewrite Find_b2 in Find_bb2. inv Find_bb2.
  exists b1. exists b3.
  split; trivial.  split; trivial.  split; trivial.
  destruct d. destruct Hb as [X1 [f1 [f2 [Hf1 Hf2]]]].
  destruct Hbb as [X2 [ff2 [f3 [Hff2 Hf3]]]].
  rewrite Hff2 in Hf2. inv Hf2.
  split. rewrite (EPC (Vptr b1 Int.zero) (Vptr b3 Int.zero) s). exists  (Vptr b1 Int.zero). 
  split; assumption.
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
Qed.

Lemma ePts_compose3: forall {F1 V1 F2 V2 F3 V3} 
  (Prg1 : AST.program F1 V1) (Prg2 : AST.program F2 V2) 
  (Prg3 : AST.program F3 V3)
  Epts12 Epts23 ExternIdents entrypoints13 j12
  (EPC : entrypoints_compose Epts12 Epts23 entrypoints13)
  (ePts12_ok : @CompilerCorrectness.entryPts_inject_ok F1 V1 F2 V2 Prg1 
               Prg2 j12 ExternIdents Epts12)
  (ePts23_ok : @CompilerCorrectness.entryPts_ok F2 V2 F3 V3 Prg2
                Prg3 ExternIdents Epts23),
CompilerCorrectness.entryPts_inject_ok Prg1 Prg3 j12 ExternIdents entrypoints13.
Proof. 
  intros.
  unfold CompilerCorrectness.entryPts_inject_ok; intros e d EXT.
  destruct (ePts12_ok _ _ EXT) as [b1 [b2 [Find_b1 [Find_bb2 [Jb1 Hb1]]]]].
  destruct (ePts23_ok _ _ EXT) as [b3 [Find_b2 [Find_b3 Hb2]]].
  rewrite Find_b2 in Find_bb2. inv Find_bb2.
  exists b1; exists b2. split; trivial.
  split; trivial. split; trivial.
  destruct d. destruct Hb1 as [X1 [f1 [f2 [Hf1 Hf2]]]].
  destruct Hb2 as [X2 [ff2 [f3 [Hff2 Hf3]]]].
  rewrite Hff2 in Hf2. inv Hf2.
  split. rewrite (EPC (Vptr b1 Int.zero) (Vptr b2 Int.zero) s). 
  exists  (Vptr b2 Int.zero). 
  split; assumption.
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
Qed.

Lemma ePts_compose4: forall {F1 V1 F2 V2 F3 V3} 
  (Prg1 : AST.program F1 V1) (Prg2 : AST.program F2 V2) 
  (Prg3 : AST.program F3 V3)
  Epts12 Epts23 ExternIdents entrypoints13 j12 j23
  (EPC: entrypoints_compose Epts12 Epts23 entrypoints13)
  (ePts12_ok: @CompilerCorrectness.entryPts_inject_ok F1 V1 F2 V2 Prg1
              Prg2 j12 ExternIdents Epts12)
  (ePts23_ok: @CompilerCorrectness.entryPts_inject_ok F2 V2 F3 V3 Prg2
              Prg3 j23 ExternIdents Epts23),
  CompilerCorrectness.entryPts_inject_ok Prg1 Prg3 
     (compose_meminj j12 j23) ExternIdents entrypoints13.
Proof. 
  intros.
  unfold CompilerCorrectness.entryPts_inject_ok; intros e d EXT.
  destruct (ePts12_ok _ _ EXT) as [b1 [b2 [Find_b1 [Find_bb2 [j12b1 Hb]]]]].
  destruct (ePts23_ok _ _ EXT) as [bb2 [b3 [Find_b2 [Find_b3 [j23b2 Hbb]]]]].
  rewrite Find_b2 in Find_bb2. inv Find_bb2.
  exists b1. exists b3.
  split; trivial.  split; trivial.  split. unfold compose_meminj. 
  rewrite j12b1. rewrite j23b2. rewrite Zplus_0_l. trivial.
  destruct d. destruct Hb as [X1 [f1 [f2 [Hf1 Hf2]]]].
  destruct Hbb as [X2 [ff2 [f3 [Hff2 Hf3]]]].
  rewrite Hff2 in Hf2. inv Hf2.
  split. rewrite (EPC (Vptr b1 Int.zero) (Vptr b3 Int.zero) s). 
  exists  (Vptr b2 Int.zero). 
  split; assumption.
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
Qed.

(*Now defined in forward_simulations_trans
Inductive sem_compose_ord_eq_eq {D12 D23:Type} 
  (ord12: D12 -> D12 -> Prop) (ord23: D23 -> D23 -> Prop) (C2:Type):
  (D12 * option C2 * D23) ->  (D12 * option C2 * D23) ->  Prop := 
| sem_compose_ord1 :
  forall (d12 d12':D12) (c2:C2) (d23:D23),
    ord12 d12 d12' -> sem_compose_ord_eq_eq ord12 ord23 C2 (d12,Some c2,d23) (d12',Some c2,d23)
| sem_compose_ord2 :
  forall (d12 d12':D12) (c2 c2':C2) (d23 d23':D23),
    ord23 d23 d23' -> sem_compose_ord_eq_eq ord12 ord23 C2 (d12,Some c2,d23) (d12',Some c2',d23').
*)

(*Now proven in forward_simulations_trans
Lemma well_founded_sem_compose_ord_eq_eq: forall {D12 D23:Type}
  (ord12: D12 -> D12 -> Prop) (ord23: D23 -> D23 -> Prop)  (C2:Type)
  (WF12: well_founded ord12) (WF23: well_founded ord23),
  well_founded (sem_compose_ord_eq_eq ord12 ord23 C2). 
Proof. 
  intros. intro. destruct a as [[d12 c2] d23].
  revert d12. 
  destruct c2. 
  2: constructor; intros. 2: inv H.
  revert c. 
  induction d23 using (well_founded_induction WF23).
  intros.
  induction d12 using (well_founded_induction WF12).
  constructor; intros. inv H1.
  generalize (H0 d0). simpl. intros.
  apply H1. auto.
  generalize (H d1). 
  intros. 
  spec H1. auto. 
  apply H1. 
Qed.
*)

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
         admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) jInit  from meminj_preserves_globals (Genv.globalenv P2) jInit*)
       (*sim_eqinj*) 
           eapply Forward_simulation_trans.eqinj; try eassumption.
       (*prog_main*)
             rewrite e12; assumption.
       (*GenvHyp*) 
             destruct g23 as [Hyp2A Hyp2B].
             split; intros. rewrite Hyp2A. apply g12. 
                                   rewrite Hyp2B. apply g12.
       (*externvars*) intros b; intros. admit. (*genv's not yet updated preservation of externvars by equality phases even if V1->V2 etc*)
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
       (*meminj_preserves_globals*)
           admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) jInit  from meminj_preserves_globals (Genv.globalenv P2) jInit*)
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
       (*meminj_perserved_globals*)
         admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) jInit  from meminj_preserves_globals (Genv.globalenv P2) jInit*)
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

Lemma transform_compose: forall 
      {F1 F2 F3 V:Type} (P: AST.program F1 V)
                        (transf12: F1 -> F2) (transf23 : F2 -> F3),
      transform_program transf23 (transform_program transf12 P) =
      transform_program (fun f : F1 => transf23 (transf12 f)) P.
Proof. intros. destruct P; simpl.
  unfold transform_program. simpl. 
   rewrite list_map_compose. f_equal. 
   apply map_ext. intros.
   destruct a; simpl.
   destruct g; trivial.
Qed.

Section cc_simT_trans.
Lemma ccT_trans_CaseEq: forall {F1 C1 V F2 C2 F3 C3} 
     (Sem1 : CoopCoreSem (Genv.t F1 V) C1)
     (Sem2 : CoopCoreSem (Genv.t F2 V) C2)
     (Sem3 : CoopCoreSem (Genv.t F3 V) C3)
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V) (P2 : AST.program F2 V) (P3 : AST.program F3 V)
     transf12 (HP12: P2=transform_program transf12 P1) transf23
     (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
     (SimEq12 : Forward_simulation_eq.Forward_simulation_equals Sem1 Sem2 (Genv.globalenv P1)
                               (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_simT I ExternIdents epts23 F2 C2 V F3 C3 Sem2 Sem3 P2 P3 transf23)
     (i1: I F1 C1 V Sem1 P1),
forall entrypoints13 : list (val * val * signature),
       entrypoints_compose epts12 epts23 entrypoints13 ->
CompilerCorrectness.cc_simT I ExternIdents entrypoints13 F1 C1 V F3 C3
  Sem1 Sem3 P1 P3 (fun f => transf23 (transf12 f)).
Proof. 
intros F1 C1 V F2 C2 F3 C3 Sem1 Sem2 Sem3 
       ExternIdents epts12 epts23 I P1 P2 P3 
       transf12 HP12 transf23 ePts12_ok SimEq12 SIM23 i1.
induction SIM23; intros; subst.
 (*equality pass Sem2 -> Sem3*)  
   rename F2 into F3. rename F0 into F2. 
   rename C2 into C3. rename C0 into C2. 
   rename Sem2 into Sem3. rename Sem0 into Sem2.
   rename i into i2. rename i0 into i3.
   rename transf into transf23.
       apply CompilerCorrectness.ccs_eqT with 
          (entrypoints:=entrypoints13);try assumption.
       apply transform_compose.
       (*entrypoints_ok*)
           apply ePts_compose1 with (Prg2:=(transform_program transf12 P1))
             (Epts12:=epts12)(Epts23:=epts23); assumption.
       (*sim_eqeq*)
           eapply Forward_simulation_trans.eqeq; try eassumption.
 (*extension pass Sem2 -> Sem3*)
   rename F2 into F3. rename F0 into F2. 
   rename C2 into C3. rename C0 into C2. 
   rename Sem2 into Sem3. rename Sem0 into Sem2.
   rename i into i2. rename i0 into i3.
   rename transf into transf23.
       apply CompilerCorrectness.ccs_extT with 
          (entrypoints:=entrypoints13); try assumption.
       apply transform_compose.
       (*entrypoints_ok*)
           apply ePts_compose1 with (Prg2:=(transform_program transf12 P1))
             (Epts12:=epts12)(Epts23:=epts23); assumption.
       (*sim_eqext*)
           eapply Forward_simulation_trans.eqext; try eassumption.
   (*injection pass Sem2 -> Sem3*) 
   rename F2 into F3. rename F0 into F2. 
   rename C2 into C3. rename C0 into C2. 
   rename Sem2 into Sem3. rename Sem0 into Sem2.
   rename i into i2. rename i0 into i3.
   rename transf into transf23.
       eapply CompilerCorrectness.ccs_injT with 
          (entrypoints:=entrypoints13); try assumption.
       apply transform_compose.
       (*init_mem*)
         intros m1 Ini1.
          eapply ePts_compose2; try eassumption.
            eapply ePts_ok. 
              apply (Genv.init_mem_transf transf12 P1).
              assumption.
       (*sim_eqinj*)
           eapply Forward_simulation_trans.eqinj; try eassumption.
       (*externvars*) intros b; intros.
             specialize (e b). rewrite Genv.find_var_info_transf in e.
             specialize (e _ H0). destruct e as [x X].
             rewrite Genv.find_symbol_transf in X.
             exists x. apply X.
Qed.

Lemma ccT_trans_CaseExtends: forall {F1 C1 V F2 C2 F3 C3} 
     (Sem1 : CoopCoreSem (Genv.t F1 V) C1)
     (Sem2 : CoopCoreSem (Genv.t F2 V) C2)
     (Sem3 : CoopCoreSem (Genv.t F3 V) C3)
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V) (P2 : AST.program F2 V) (P3 : AST.program F3 V)
     transf12 (HP12: P2=transform_program transf12 P1) transf23
     (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
     (SimExt12 :  Forward_simulation_ext.Forward_simulation_extends Sem1 Sem2 (Genv.globalenv P1)
                              (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_simT I ExternIdents epts23 F2 C2 V F3 C3 Sem2 Sem3 P2 P3 transf23)
     (i1: I F1 C1 V Sem1 P1),
forall entrypoints13 : list (val * val * signature),
          entrypoints_compose epts12 epts23 entrypoints13 ->
CompilerCorrectness.cc_simT I ExternIdents entrypoints13 F1 C1 V F3 C3 Sem1 Sem3 P1 P3 (fun f => transf23 (transf12 f)).
Proof. 
intros F1 C1 V F2 C2 F3 C3 Sem1 Sem2 Sem3 
       ExternIdents epts12 epts23 I P1 P2 P3 
       transf12 HP12 transf23 ePts12_ok SimExt12 SIM23 i1.
induction SIM23; intros; subst.
 (*equality pass Sem2 -> Sem3*) 
   rename F2 into F3. rename F0 into F2. 
   rename C2 into C3. rename C0 into C2. 
   rename Sem2 into Sem3. rename Sem0 into Sem2.
   rename i into i2. rename i0 into i3.
   rename transf into transf23.
       apply CompilerCorrectness.ccs_extT with 
          (entrypoints:=entrypoints13);try assumption.
       apply transform_compose.
       (*entrypoints_ok*)
           apply ePts_compose1 with (Prg2:=(transform_program transf12 P1))
             (Epts12:=epts12)(Epts23:=epts23); assumption.
       (*sim_eqeq*)
           eapply Forward_simulation_trans.exteq; try eassumption.
 (*extension pass Sem2 -> Sem3*)
   rename F2 into F3. rename F0 into F2. 
   rename C2 into C3. rename C0 into C2. 
   rename Sem2 into Sem3. rename Sem0 into Sem2.
   rename i into i2. rename i0 into i3.
   rename transf into transf23.
       apply CompilerCorrectness.ccs_extT with 
          (entrypoints:=entrypoints13); try assumption.
       apply transform_compose.
       (*entrypoints_ok*)
           apply ePts_compose1 with (Prg2:=(transform_program transf12 P1))
             (Epts12:=epts12)(Epts23:=epts23); assumption.
       (*sim_eqext*)
           eapply Forward_simulation_trans.extext; try eassumption.
   (*injection pass Sem2 -> Sem3*) 
   rename F2 into F3. rename F0 into F2. 
   rename C2 into C3. rename C0 into C2. 
   rename Sem2 into Sem3. rename Sem0 into Sem2.
   rename i into i2. rename i0 into i3.
   rename transf into transf23.
       eapply CompilerCorrectness.ccs_injT with 
          (entrypoints:=entrypoints13); try assumption.
       apply transform_compose.
       (*init_mem*)
         intros m1 Ini1.
          eapply ePts_compose2; try eassumption.
            eapply ePts_ok. 
              apply (Genv.init_mem_transf transf12 P1).
              assumption.
       (*sim_eqinj*)
           eapply Forward_simulation_trans.extinj; try eassumption.
       (*externvars*) intros b; intros.
             specialize (e b). rewrite Genv.find_var_info_transf in e.
             specialize (e _ H0). destruct e as [x X].
             rewrite Genv.find_symbol_transf in X.
             exists x. apply X.
Qed.

Lemma ccT_trans_CaseInject: forall {F1 C1 V F2 C2 F3 C3} 
     (Sem1 : CoopCoreSem (Genv.t F1 V) C1)
     (Sem2 : CoopCoreSem (Genv.t F2 V) C2)
     (Sem3 : CoopCoreSem (Genv.t F3 V) C3)
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V) (P2 : AST.program F2 V) (P3 : AST.program F3 V)
     transf12 (HP12: P2=transform_program transf12 P1) transf23
     (ePts12_ok: forall m, Genv.init_mem P1 = Some m ->
         CompilerCorrectness.entryPts_inject_ok P1 P2 (Mem.flat_inj (Mem.nextblock m)) ExternIdents epts12)
     (VarsOK1: CompilerCorrectness.externvars_ok P1 ExternIdents)
     (SimInj12: Forward_simulation_inj.Forward_simulation_inject Sem1 Sem2 (Genv.globalenv P1)
                                 (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_simT I ExternIdents epts23 F2 C2 V F3 C3 Sem2 Sem3 P2 P3 transf23)
     (i1: I F1 C1 V Sem1 P1),
forall entrypoints13 : list (val * val * signature),
       entrypoints_compose epts12 epts23 entrypoints13 ->
CompilerCorrectness.cc_simT I ExternIdents entrypoints13 F1 C1 V F3 C3 Sem1 Sem3 P1 P3 (fun f => transf23 (transf12 f)).
Proof.
intros F1 C1 V F2 C2 F3 C3 Sem1 Sem2 Sem3 
       ExternIdents epts12 epts23 I P1 P2 P3 
       transf12 HP12 transf23 ePts12_ok VarsOK SimExt12 SIM23 i1.
induction SIM23; intros; subst.
 (*equality pass Sem2 -> Sem3*) 
   rename F2 into F3. rename F0 into F2. 
   rename C2 into C3. rename C0 into C2. 
   rename Sem2 into Sem3. rename Sem0 into Sem2.
   rename i into i2. rename i0 into i3.
   rename transf into transf23.
       apply CompilerCorrectness.ccs_injT with 
          (entrypoints:=entrypoints13);try assumption.
       apply transform_compose.
       (*entrypoints_ok*)
          intros.
           eapply ePts_compose3; try eassumption.
           apply ePts12_ok. apply H0.
       (*sim_injeq*)
           eapply Forward_simulation_trans.injeq; try eassumption.
 (*extension pass Sem2 -> Sem3*)
   rename F2 into F3. rename F0 into F2. 
   rename C2 into C3. rename C0 into C2. 
   rename Sem2 into Sem3. rename Sem0 into Sem2.
   rename i into i2. rename i0 into i3.
   rename transf into transf23.
       apply CompilerCorrectness.ccs_injT with 
          (entrypoints:=entrypoints13); try assumption.
       apply transform_compose.
       (*entrypoints_ok*)
           intros.
           eapply ePts_compose3; try eassumption.
           apply ePts12_ok. apply H0.
       (*sim_eqext*)
           eapply Forward_simulation_trans.injext; try eassumption.
   (*injection pass Sem2 -> Sem3*) 
   rename F2 into F3. rename F0 into F2. 
   rename C2 into C3. rename C0 into C2. 
   rename Sem2 into Sem3. rename Sem0 into Sem2.
   rename i into i2. rename i0 into i3.
   rename transf into transf23.
       eapply CompilerCorrectness.ccs_injT with 
          (entrypoints:=entrypoints13); try assumption.
       apply transform_compose.
       (*init_mem*)
         intros m1 Ini1.
          assert (Mem.flat_inj (Mem.nextblock m1) =
                    compose_meminj (Mem.flat_inj (Mem.nextblock m1)) (Mem.flat_inj (Mem.nextblock m1))).
             admit. (*admit ok -- initial mems not yet adapted to modules*)
          rewrite H0.
          eapply ePts_compose4; try eassumption.
            eapply ePts12_ok. apply Ini1.
            eapply ePts_ok. apply Genv.init_mem_transf. apply Ini1.           
       (*sim_eqinj*)
           eapply Forward_simulation_trans.injinj; try eassumption.
       (*externvars*) 
Qed.

Theorem ccT_sim_trans:
     forall ExternIdents entrypoints12 I F1 C1 V F2 C2
        (Sem1: CoopCoreSem (Genv.t F1 V) C1)
        (Sem2: CoopCoreSem (Genv.t F2 V) C2)
        P1 P2 
        transf12 (HP12: P2=transform_program transf12 P1) 
        (SIM12: CompilerCorrectness.cc_simT I ExternIdents entrypoints12 
             F1 C1 V F2 C2 Sem1 Sem2 P1 P2 transf12)
        F3 C3 transf23
        (Sem3: CoopCoreSem (Genv.t F3 V) C3)
        entrypoints23 P3 
        (SIM23:CompilerCorrectness.cc_simT I ExternIdents entrypoints23 F2 C2 V F3 C3 Sem2 Sem3 P2 P3 transf23)
        entrypoints13 (EPC:entrypoints_compose entrypoints12 entrypoints23 entrypoints13),
      CompilerCorrectness.cc_simT I ExternIdents entrypoints13 F1 C1 V F3 C3 Sem1 Sem3 P1 P3 (fun f => transf23 (transf12 f)).
Proof.
  intros  ExternIdents epts12 I F1 C1 V1 F2 C2 Sem1 Sem2 P1 P2 transf12 HP12 SIM12.
  induction SIM12; intros.
  eapply (ccT_trans_CaseEq Sem1 Sem2 Sem3); try eassumption.
  eapply (ccT_trans_CaseExtends Sem1 Sem2 Sem3); eassumption.
  eapply (ccT_trans_CaseInject Sem1 Sem2 Sem3); eassumption.
Qed.

End cc_simT_trans.

Lemma coop_correctnessT_implies_cc_simT: 
  forall ExternIdents entrypoints I F1 C1 V F2 C2
        (Sem1: CoopCoreSem (Genv.t F1 V) C1)
        (Sem2: CoopCoreSem (Genv.t F2 V) C2)
        P1 P2 trans
        (EPC:entrypoints_compose entrypoints entrypoints entrypoints)
        (MAIN: In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents),
        CompilerCorrectness.coop_correctnessT I ExternIdents entrypoints 
           F1 C1 V F2 C2 Sem1 Sem2 P1 P2 trans -> 
        CompilerCorrectness.cc_simT I ExternIdents entrypoints F1 C1 V F2 C2 Sem1 Sem2 P1 P2 trans.
Proof. intros.
  induction X.
  subst. eapply CompilerCorrectness.ccs_eqT; try eassumption. reflexivity.
  subst. eapply CompilerCorrectness.ccs_extT; try eassumption. reflexivity.
  subst. eapply CompilerCorrectness.ccs_injT; try eassumption. reflexivity.
  subst. eapply ccT_sim_trans; try eassumption. reflexivity.
      apply IHX1. eassumption. apply IHX2. eassumption.
Qed.