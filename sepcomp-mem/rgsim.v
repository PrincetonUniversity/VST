Require Import Events.
Require Import Memory.
Require Import Coqlib.
Require Import Values.
Require Import Maps.
Require Import Integers.
Require Import AST.
Require Import Globalenvs.

Require Import Axioms.
Require Import Wellfounded.
Require Import Relations.
Require Import sepcomp.core_semantics.
Require Import sepcomp.core_semantics_lemmas.
Require Import sepcomp.mem_lemmas.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.rg_forward_simulations.
Require Import sepcomp.mem_interpolation_defs. (*For definition of my_mem_unchanged_on*)
Require Import sepcomp.RG_interpolants.

Declare Module RGMEMAX : RGInterpolationAxioms.

Section RGSIM.
Context  
(F1 C1 V1 F2 C2 V2:Type)
(Sem1 : EffectfulSemantics  (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
(Sem2 : EffectfulSemantics  (Genv.t F2 V2)  C2 (list (ident * globdef F2 V2))).

Inductive sim g1 g2 entrypoints: Type :=
(*Later: add constructors for eq and extends, maybe the latter with RG
  simeq : forall  
      (R:Forward_simulation_eq.Forward_simulation_equals _ _ _ Sem1 Sem2 
            g1 g2  entrypoints), 
      sim  g1 g2 entrypoints
 | simext : forall 
     (R:Coop_forward_simulation_ext.Forward_simulation_extends _ _ Sem1 Sem2 
           g1 g2  entrypoints),
     sim g1 g2  entrypoints
  | siminj: forall (R:Coop_forward_simulation_inj.Forward_simulation_inject _ _ Sem1 Sem2 
           g1 g2 entrypoints),
   sim g1 g2 entrypoints*)
  | sim_inj: forall  cd (matchstate:cd -> reserve -> meminj -> C1 -> mem -> C2 -> mem -> Prop)
                              coreord
        (RG: @RelyGuaranteeSimulation.Sig _ _ _ _ _ _ _ Sem1 Sem2
               g1 cd matchstate)
        (R: Forward_simulation_inj_exposed.Forward_simulation_inject _ _ Sem1 Sem2 
               g1 g2 entrypoints cd matchstate coreord),
   sim g1 g2 entrypoints.
End RGSIM.

(*************************From compiler_correctness_trans******************)
Definition main_sig : signature := mksignature nil (Some AST.Tint).

Definition entrypoints_compose 
  (ep12 ep23 ep13 : list (val * val * signature)): Prop :=
  forall v1 v3 sig, 
  In (v1,v3,sig) ep13 = exists v2, In (v1,v2,sig) ep12 /\ In (v2,v3,sig) ep23.

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

Inductive sem_compose_ord_eq_eq {D12 D23:Type} 
  (ord12: D12 -> D12 -> Prop) (ord23: D23 -> D23 -> Prop) (C2:Type):
  (D12 * option C2 * D23) ->  (D12 * option C2 * D23) ->  Prop := 
| sem_compose_ord1 :
  forall (d12 d12':D12) (c2:C2) (d23:D23),
    ord12 d12 d12' -> sem_compose_ord_eq_eq ord12 ord23 C2 (d12,Some c2,d23) (d12',Some c2,d23)
| sem_compose_ord2 :
  forall (d12 d12':D12) (c2 c2':C2) (d23 d23':D23),
    ord23 d23 d23' -> sem_compose_ord_eq_eq ord12 ord23 C2 (d12,Some c2,d23) (d12',Some c2',d23').

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
apply H1. auto.
Qed.

Lemma guarantee_initial: forall {G C D}
    (Sem: EffectfulSemantics G C D) ge v vs c
    (Ini: make_initial_core Sem ge v vs = Some c) r m,
    guarantee Sem r c m.
Proof. intros. intros b; intros. exfalso.
   apply (effects_initial Sem _ _ _ _ _ _ _ Ini H1).
Qed. 

Require Import msl.Coqlib2.

Section RGSIM_TRANS.
Context  (F1 C1 V1 F2 C2 V2 F3 C3 V3:Type)
               (Sem1 : EffectfulSemantics (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
               (Sem2 : EffectfulSemantics (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
               (Sem3 : EffectfulSemantics (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
              (G1 : Genv.t F1 V1) (G2 : Genv.t F2 V2) (G3 : Genv.t F3 V3)
               (entrypoints12 : list (val * val * signature))
               (entrypoints23 : list (val * val * signature))
               (entrypoints13 : list (val * val * signature))
               (EPC : entrypoints_compose entrypoints12  entrypoints23 entrypoints13).

Lemma sim_trans: forall 
        (SIM12: sim F1 C1 V1 F2 C2 V2 Sem1 Sem2 G1 G2 entrypoints12)
        (SIM23: sim  F2 C2 V2 F3 C3 V3 Sem2 Sem3 G2 G3 entrypoints23),
        sim  F1 C1 V1 F3 C3 V3 Sem1 Sem3 G1 G3 entrypoints13.
Proof. intros.
  induction SIM12.
  rename cd into cd12. rename matchstate into matchstate12.
  rename coreord into coreord12. 
  rename RG into RG12.
  rename R into R12.
  induction SIM23.
  rename cd into cd23. 
  rename matchstate into matchstate23. 
  rename coreord into coreord23.
  rename RG into RG23.
  rename R into R23.
  specialize (Forward_simulation_inj_exposed.core_diagramN R12).
  specialize (Forward_simulation_inj_exposed.core_diagramN R23).
  intros Diag23 Diag12.
  eapply sim_inj with
    (coreord := sem_compose_ord_eq_eq coreord12 (clos_trans _ coreord23) C2)
    (matchstate := fun d (r:reserve) j c1 m1 c3 m3 => 
      match d with (d1,X,d2) => 
        exists c2, exists m2, exists j12, exists j23, 
          X=Some c2 /\ j = compose_meminj j12 j23 /\ 
          matchstate12 d1 r j12 c1 m1 c2 m2 /\
          matchstate23 d2 (inject_reserve_ j12 r) j23 c2 m2 c3 m3 /\
          guarantee Sem1 r c1 m1 /\
          guarantee Sem2 (inject_reserve j12 r) c2 m2 /\ 
          guarantee Sem3 (inject_reserve j23 ((inject_reserve j12 r))) c3 m3
      end).
    (*RG*) clear R12 R23.
         destruct RG12 as [match_state_runnable12 match_state_inj12
                                        match_state_preserves_globals12].
         destruct RG23 as [match_state_runnable23 match_state_inj23 
                                         match_state_preserves_globals23 ].
        econstructor; intros.
        (*match_state_runnable*) 
        destruct cd as [[d1 d2] d3]. rename c2 into c3. rename m2 into m3.
        destruct H as [c2 [m2 [j12 [j23 [? [J [MS12 [MS23 Guars]]]]]]]]; subst.
        rewrite (match_state_runnable12 _ _ _ _ _ _  _ MS12).
        solve[apply (match_state_runnable23 _ _ _ _ _ _ _ MS23)].
        (*match_state_inj*) 
        destruct cd as [[d1 d2] d3]. rename c2 into c3. rename m2 into m3.
         destruct H as [c2 [m2 [j12 [j23 [? [J [MS12 [MS23 Guars]]]]]]]]; subst. 
         eapply Mem.inject_compose.
         apply (match_state_inj12 _ _ _ _ _ _ _ MS12).
         apply (match_state_inj23 _ _ _ _ _ _ _ MS23).
         (*match_state_preserves_globals*)
         admit. 
  destruct R12
    as [core_ord_wf12 match_memwd12 res_valid12  
           effects_valid12 allocs_shrink12 (*match_mono12*)
           match_validblocks12 core_diagram12 core_initial12
           core_halted12 core_at_external12 core_after_external12].  
  destruct R23 
    as [core_ord_wf23 match_memwd23  res_valid23
           effects_valid23 allocs_shrink23 (*match_mono23*)
           match_validblocks23 core_diagram23 core_initial23
           core_halted23 core_at_external23 core_after_external23].  
  constructor. 
 (*well_founded*)
     eapply well_founded_sem_compose_ord_eq_eq.
         assumption.
         eapply wf_clos_trans. assumption. 
 (*match_memwd*)
    clear core_diagram12 core_initial23 
      core_halted23 core_at_external23 core_after_external23 
      core_initial12  core_halted12 core_at_external12 core_after_external12
      core_diagram23 core_ord_wf23 core_ord_wf12 res_valid12 res_valid23
      (* match_mono12 *) (* match_mono23 *) effects_valid12 effects_valid23
      allocs_shrink12 allocs_shrink23 match_validblocks12 match_validblocks23.
    clear Diag12 Diag23.
    intros. 
    destruct cd as [[d12 cc2] d23]. rename c2 into st3. rename m2 into m3.
    destruct H as [c2 [m2 [j12 [j23 [? [J [MS12 [MS23 Guars]]]]]]]]; subst.
    split. apply (match_memwd12 _ _ _ _ _ _ _ MS12).
    solve[apply (match_memwd23 _ _ _ _ _ _ _ MS23)].
  (*reserve_valid*) 
    clear core_diagram12 core_initial23  core_halted23 
      core_at_external23 core_after_external23 core_initial12 
      core_halted12 core_at_external12 core_after_external12
      core_diagram23 core_ord_wf23 core_ord_wf12  match_validblocks12
      (* match_mono12 *) (* match_mono23 *) effects_valid12 effects_valid23
      allocs_shrink12 allocs_shrink23 match_memwd12 match_memwd23.
     clear Diag12 Diag23.
     intros. rename c2 into c3. rename m2 into m3.
     destruct cd as [[d12 cc2] d23].
     destruct H as [c2 [m2 [j12 [j23 [? [J [MS12 [MS23 Guars]]]]]]]]; subst.
     clear entrypoints12 entrypoints23 entrypoints13 EPC.
     split. apply (res_valid12 _ _ _ _ _ _ _ MS12).
     intros b3 ofs b1 delta R1 Comp.
     destruct (compose_meminjD_Some _ _ _ _ _ Comp) 
       as [bb [delta2 [delta3 [J1 [J2 XX]]]]].         
     subst; clear Comp.
     eapply (match_validblocks23 _ _ _ _ _ _ _ _ MS23).
 (*effects_valid*)
     clear core_diagram12 core_initial23 
       core_halted23 core_at_external23 core_after_external23 
        core_initial12  core_halted12 core_at_external12 core_after_external12
        core_diagram23 core_ord_wf23 core_ord_wf12  match_validblocks12 match_validblocks23
        (* match_mono12 *) (* match_mono23 *) res_valid12 res_valid23
        allocs_shrink12 allocs_shrink23 match_memwd12 match_memwd23.
     clear Diag12 Diag23.
      intros. 
      destruct cd as [[d12 cc2] d23]. rename c2 into c3. rename m2 into m3.
      destruct H as [c2 [m2 [j12 [j23 [? [J [MS12 [MS23 Guars]]]]]]]]; subst.
      clear entrypoints12 entrypoints23 entrypoints13 EPC.
      split. eapply (effects_valid12 _ _ _ _ _ _ _ MS12). 
                solve[eapply (effects_valid23 _ _ _ _ _ _ _ MS23)].
 (*allocs_atmost_shrink*)
    clear core_diagram12 core_initial23 
      core_halted23 core_at_external23 core_after_external23 
      core_initial12  core_halted12 core_at_external12 core_after_external12
      core_diagram23 core_ord_wf23 core_ord_wf12  match_validblocks12 match_validblocks23
      (* match_mono12 *) (* match_mono23 *) res_valid12 res_valid23
      effects_valid12 effects_valid23 match_memwd12 match_memwd23.
   clear Diag12 Diag23.
      intros. 
      destruct cd as [[d12 cc2] d23]. rename st2 into st3. rename m2 into m3.
      destruct H as [c2 [m2 [j12 [j23 [? [J [MS12 [MS23 Guars]]]]]]]]; subst.
      clear entrypoints12 entrypoints23 entrypoints13 EPC.
      destruct (compose_meminjD_Some _ _ _ _ _ H1) 
       as [bb [delta2 [delta3 [J1 [J2 XX]]]]].          
      subst; clear H1.
      specialize (allocs_shrink23 _ _ _ _ _ _ _ MS23 _ _ H0 _ _ J2). 
      specialize (allocs_shrink12 _ _ _ _ _ _ _ MS12 _ _ allocs_shrink23 _ _ J1). 
      assert (Arith: ofs2 - delta3 - delta2 = ofs2 - (delta2 + delta3)) by omega.
      rewrite Arith in allocs_shrink12; assumption.
 (*monotonicity
    clear core_diagram12 core_initial23 
      core_halted23 core_at_external23 core_after_external23 
      core_initial12  core_halted12 core_at_external12 core_after_external12
      core_diagram23 core_ord_wf23 core_ord_wf12 
      allocs_shrink12 allocs_shrink23 res_valid12 res_valid23
      effects_valid12 effects_valid23 match_memwd12 match_memwd23.
     clear Diag12 Diag23.
      intros.
      destruct d as [[d12 cc2] d23]. rename st2 into st3. rename m2 into m3.
      destruct H as [c2 [m2 [j12 [j23 [? [J [MS12 [MS23 [Guar1 [Guar2 Guar3]]]]]]]]]]; subst.
      clear entrypoints12 entrypoints23 entrypoints13 EPC.
      exists c2, m2, j12, j23.
      repeat (split; try trivial).
      (*1/5*) eapply (* match_mono12 *); try eassumption.
        intros b ofs; intros. eapply match_validblocks12; eassumption.
      (*2/5*) eapply (* match_mono23 *); try eassumption.
        intros b2 ofs; intros. 
        rewrite inject_reserve_AX. rewrite inject_reserve_AX in H. 
        destruct H as [b1 [delta [J1 R]]].
        apply H0 in R.
        exists b1, delta; eauto.

        intros b ofs; intros.
        rewrite inject_reserve_AX in H.
        destruct H as [b1 [delta [J1 R]]].
        eapply match_validblocks12; try eassumption.

        intros b; intros.
        eapply match_validblocks23; try eassumption.
      (*3/5*) intros b; intros.
              admit. (*need to modify match_mono slightly*)
      xx
eapply match_validblocks12; eassumption. 
 eapply match_validblocks12; eassumption.
  admit. monotonicity*)
 (*valid_blocks*)
    clear core_diagram12 core_initial23 
      core_halted23 core_at_external23 core_after_external23 
      core_initial12  core_halted12 core_at_external12 core_after_external12
      core_diagram23 core_ord_wf23 core_ord_wf12  (* match_mono12 *) (* match_mono23 *)
      allocs_shrink12 allocs_shrink23 res_valid12 res_valid23
      effects_valid12 effects_valid23 match_memwd12 match_memwd23.
    clear Diag12 Diag23.
    intros. rename H0 into Jb1.
    rename c2 into st3. rename m2 into m3. rename b2 into b3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [j12 [j23 [? [J [MS12 [MS23 Guars]]]]]]]]; subst.
    clear entrypoints12 entrypoints23 entrypoints13 EPC.
    destruct (compose_meminjD_Some _ _ _ _ _ Jb1)
        as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]]. subst; clear Jb1.
    split.
    solve[apply (match_validblocks12 _ _ _ _ _ _ _ MS12 _ _ _ J1)].
    solve[apply (match_validblocks23 _ _ _ _ _ _ _ MS23 _ _ _ J2)].  

 (*core_diagram*)
  clear core_initial23  core_halted23 core_at_external23 core_after_external23 
     core_initial12  core_halted12 core_at_external12 core_after_external12
     core_ord_wf23 core_ord_wf12 match_memwd12 match_memwd23.
  intros. rename st2 into st3.
  rename m2 into m3. rename H into CS.
  destruct cd as [[d12 cc2] d23].
  rename H0 into Guar1'.
  destruct H1 as [c2 [m2 [j12 [j23 [? [J 
    [MS12 [MS23 [Guar1 [Guar2 Guar3]]]]]]]]]]; subst.
  clear entrypoints12 entrypoints23 entrypoints13 EPC.
  clear Diag12.
  specialize (core_diagram12 _ _ _ _ CS _ _ _ _ _ Guar1' MS12).
  destruct core_diagram12 as [st2' [m2' [cd12' [r' [j12'
      [Inc12 [Sep12 [Rinc12 [Rsep12 [Z12 X12]]]]]]]]]]. (*[Guar2' [MS12' X12]]]]]]]]]]]. *)
  destruct X12 as [X12 | [X12 ORD12]]; destruct X12 as [n X12].
  (*Case 1*)
     clear core_diagram23.
     assert (Guar2': guarantee Sem2 (inject_reserve_ j12 r) st2' m2').
         destruct (Z12 r') as [GG2' MS12'].
           assumption.
           apply reserve_incr_refl. 
           unfold guarantee' in GG2'.
           rewrite inject_reserve_AX.
           solve[eapply guarantee_decr2; eassumption].
    specialize (Diag23 _ _ _ _ _ X12 _  _ _ _ _ Guar2' MS23).
    destruct Diag23 as [st3' [m3' [cd23' [r23' [j23'
      [Inc23 [Sep23 [Rinc23 [Rsep23 [Z23 X23]]]]]]]]]].
     exists st3'. exists m3'. exists ((cd12', Some st2'), cd23').
      assert (rEX: exists (rr:reserve), forall b ofs,
              rr b ofs <->  
              (r' b ofs \/ (exists b2, exists delta2, 
                          j12' b = Some(b2,delta2) /\ r23' b2 (ofs + delta2)))).
        admit. 
      destruct rEX as [rr Hrr].
      exists rr.  (*IF WE USE r WE HAVE TO USE ANTIMONOTONICOITY*)
      exists (compose_meminj j12' j23').
      split. eapply compose_meminj_inject_incr; eassumption.
      split. eapply compose_meminj_inject_separated.
                      eassumption. eassumption. eassumption. eassumption.
                      apply (match_validblocks12 _ _ _ _ _ _ _ MS12).
                      apply (match_validblocks23 _ _ _ _ _ _ _ MS23).
      split. intros b; intros.
           rewrite Hrr. clear Hrr. left.
           eapply Rinc12; eassumption.
      split. intros b; intros. rewrite Hrr in H0. 
             destruct H0; clear Hrr. 
              destruct (Rsep12 _ _ H H0). 
              split; trivial. 
              intros delta b3 Comp.
              destruct (compose_meminjD_Some _ _ _ _ _ Comp)
                as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]].
              subst; clear Comp.
              apply H2 in J1.
              case_eq (j23 b2).     
                 intros [? ?] ?. 
                 rewrite (Inc23 _ _ _ H3) in J2. inv J2.
                 exfalso. apply J1.
                 solve[eapply (match_validblocks23 _ _ _ _ _ _ _ MS23); eassumption].
              intros. apply (Sep23 _ _ _ H3 J2).
            destruct H0 as [b2 [delta2 [J12 R23']]].
              case_eq (j12 b).     
                 intros [? ?] ?. 
                 rewrite (Inc12 _ _ _ H0) in J12. inv J12.
                 exfalso. 
                 destruct (Rsep23 b2 (ofs + delta2)).
                    intros N.
                 solve[eapply (match_validblocks23 _ _ _ _ _ _ _ MS23); eassumption].
              intros. apply (Sep23 _ _ _ H3 J2).
              
            destruct (Rsep23 b2 (ofs + delta2)).
               intros N. rewrite inject_reserve_AX in N.
               destruct N as [b1 [delta [J R]]].

            eapply (Z23 r23').  pply reserve_separated_same. 
      split.
        intros r'' rsep'' rinc''.
        split. 
          (*goal is: guarantee' Sem3 (compose_meminj j12' j23') r'' st3' m3'*)
          unfold guarantee'.
          assert (STEPN: exists n, corestepN Sem3 G3 n st3 m3 st3' m3').
           destruct X23.
           unfold corestep_plus in H.
           destruct H as [m STEPM].
           exists (S m); auto.
           destruct H as [H _].
           unfold corestep_star in H.
           solve[auto].
          destruct STEPN as [m STEPM].
          eapply guarantee_incr_allocN' 
            with (mleft := m1) 
               (j := compose_meminj j12 j23); eauto.
            solve[eapply compose_meminj_inject_incr; eassumption].
            solve[eapply compose_meminj_inject_separated; eauto].
          intros b3 ofs; intros.
            destruct H0 as [b1 [delta [Comp R]]].
            destruct (compose_meminjD_Some _ _ _ _ _ Comp)
              as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]].
            subst; clear Comp.
            eapply (Z23 r23').
               assumption.
               apply reserve_incr_refl.
               assumption.
               exists b2, delta3.
                 split. apply (Inc23 _ _ _ J2).
                 apply Rinc23. rewrite inject_reserve_AX.
                   exists b1, delta2.
                   split; trivial.
                   assert (ofs - delta3 - delta2 = ofs - (delta2 + delta3))
                      as -> by omega.
                   clear H0.
                   destruct (reserve_dec r b1 (ofs - (delta2 + delta3))).
                     trivial.
                     destruct (Rsep12 _ _ n0 R).
                     exfalso. apply H0; clear H0 H2 n0.
                     solve[eapply (match_validblocks12 _ _ _ _ _ _ _ MS12); eassumption].
                assumption.
            intros b; intros.
             destruct (reserve_dec r b ofs).
               apply Rinc12 in s. contradiction.
             solve[eapply rsep''; eassumption]. 
        exists st2', m2', j12', j23'.
          repeat split; try solve[reflexivity].
          apply Z12.
            intros b; intros.
              destruct (reserve_dec r' b ofs).
                solve[eapply Rsep12; eassumption].
              destruct (rsep'' _ _ H H0).
                split; trivial; intros.
                case_eq (j12 b).
                  intros [? ?] ?. 
                  exfalso. apply H1; clear H1 H2 H3.
                  solve [eapply (match_validblocks12 _ _ _ _ _ _ _ MS12); eassumption].
                intros. apply (Sep12 _ _ _ H4 H3).
           assumption.
          apply Z23.
            intros b; intros.
              rewrite inject_reserve_AX in H0, H.
              destruct H0 as [b1 [delta2 [J12' R'']]].
              destruct (reserve_dec r b1 (ofs - delta2)).
                case_eq (j12 b1).
                  intros [? ?] ?. 
                  rewrite (Inc12 _ _ _ H0) in J12'. inv J12'.
                  exfalso. apply H; clear H. 
                  exists b1, delta2. split; trivial.
                intros. destruct (Sep12 _ _ _ H0 J12').
                  apply (res_valid12 _ _ _ _ _ _ _ MS12) in s.
                  contradiction.
              destruct (rsep'' _ _ n0 R'').  
                case_eq (j12 b1).
                  intros [? ?] ?. 
                  rewrite (Inc12 _ _ _ H2) in J12'. inv J12'.
                  exfalso. apply H0; clear H0.
                  solve [eapply (match_validblocks12 _ _ _ _ _ _ _ MS12); eassumption].
                intros. destruct (Sep12 _ _ _ H2 J12').
                  split; trivial; intros. 
                case_eq (j23 b).
                  intros [? ?] ?. 
                  rewrite (Inc23 _ _ _ H6) in H5. inv H5.
                  exfalso. apply H4; clear H4.
                  solve [eapply (match_validblocks23 _ _ _ _ _ _ _ MS23); eassumption].
                intros. apply (Sep23 _ _ _ H6 H5).
                  split; trivial; intros.   H2. contradiction.
                  exfalso. apply H0; clear H. 
                  exists b1, delta2. split; trivial.
                intros. destruct (Sep12 _ _ _ H0 J12').
                  apply (res_valid12 _ _ _ _ _ _ _ MS12) in s.
                  contradiction.
                  eapply (H b1); clear H. H2 H3.
                  solve [e; eassumption].
                intros. apply (Sep12 _ _ _ H4 H3).
                
                destruct (rsep'' _ _ s R'').
                solve[eapply Rsep12; eassumption].
              destruct (rsep'' _ _ H H0).
                split; trivial; intros.
                case_eq (j12 b).
                  intros [? ?] ?. 
                  exfalso. apply H1; clear H1 H2 H3.
                  solve [eapply (match_validblocks12 _ _ _ _ _ _ _ MS12); eassumption].
                intros. apply (Sep12 _ _ _ H4 H3).
           assumption.
 assumption.
      exists r'. (*IF WE USE r WE HAVE TO USE ANTIMONOTONICOITY*)
      exists (compose_meminj j12' j23').
      split. eapply compose_meminj_inject_incr; eassumption.
      split. eapply compose_meminj_inject_separated.
                      eassumption. eassumption. eassumption. eassumption.
                      apply (match_validblocks12 _ _ _ _ _ _ _ MS12).
                      apply (match_validblocks23 _ _ _ _ _ _ _ MS23).
      split. auto. (*apply reserve_incr_refl.*)
      split. 
        intros b ofs; intros.
        split; auto.
        solve[eapply Rsep12; eauto].
        intros delta b3; intros H1.
        apply compose_meminjD_Some in H1.
        destruct H1 as [b2 [delta1 [delta2 [J12' [J23' X]]]]]; subst.
        case_eq (j23 b2).
        intros [? ?] J23.
        generalize J23 as J23''; intro.
        apply Inc23 in J23.
        rewrite J23 in J23'; inv J23'.
        destruct (Rsep12 _ _ H H0).
        elimtype False.
        apply (H2 _ _ J12').
        exploit match_validblocks23; eauto.
        solve[intros [? ?]; auto].
        (*j23 b2 = None*)
        solve[intros; eapply Sep23; eauto].
      split.
        intros r'' rsep'' rinc''.
        split. unfold guarantee'.
          assert (STEPN: exists n, corestepN Sem3 G3 n st3 m3 st3' m3').
           destruct X23.
           unfold corestep_plus in H.
           destruct H as [m STEPM].
           exists (S m); auto.
           destruct H as [H _].
           unfold corestep_star in H.
           solve[auto].
          destruct STEPN as [m STEPM].
          eapply guarantee_incr_allocN' 
            with (mleft := m1) 
               (j := compose_meminj j12 j23); eauto.
            solve[eapply compose_meminj_inject_incr; eassumption].
            solve[eapply compose_meminj_inject_separated; eauto].
          intros b3 ofs; intros.
            destruct H0 as [b1 [delta [Comp R]]].
            destruct (compose_meminjD_Some _ _ _ _ _ Comp)
              as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]].
            subst; clear Comp.
            eapply (Z23 r23').
               assumption.
               apply reserve_incr_refl.
               assumption.
               exists b2, delta3.
                 split. apply (Inc23 _ _ _ J2).
                 apply Rinc23. rewrite inject_reserve_AX.
                   exists b1, delta2.
                   split; trivial.
                   assert (ofs - delta3 - delta2 = ofs - (delta2 + delta3))
                      as -> by omega.
                   clear H0.
                   destruct (reserve_dec r b1 (ofs - (delta2 + delta3))).
                     trivial.
                     destruct (Rsep12 _ _ n0 R).
                     exfalso. apply H0; clear H0 H2 n0.
                     solve[eapply (match_validblocks12 _ _ _ _ _ _ _ MS12); eassumption].
                assumption.
            intros b; intros.
             destruct (reserve_dec r b ofs).
               apply Rinc12 in s. contradiction.
             solve[eapply rsep''; eassumption]. 
        exists st2', m2', j12', j23'.
          repeat split; try solve[reflexivity].
          apply Z12.
            intros b; intros.
              destruct (reserve_dec r' b ofs).
                solve[eapply Rsep12; eassumption].
              destruct (rsep'' _ _ H H0).
                split; trivial; intros.
                case_eq (j12 b).
                  intros [? ?] ?. 
                  exfalso. apply H1; clear H1 H2 H3.
                  solve [eapply (match_validblocks12 _ _ _ _ _ _ _ MS12); eassumption].
                intros. apply (Sep12 _ _ _ H4 H3).
           assumption.
          apply Z23.
            intros b; intros.
              rewrite inject_reserve_AX in H0, H.
              destruct H0 as [b1 [delta2 [J12' R'']]].
              destruct (reserve_dec r b1 (ofs - delta2)).
                case_eq (j12 b1).
                  intros [? ?] ?. 
                  rewrite (Inc12 _ _ _ H0) in J12'. inv J12'.
                  exfalso. apply H; clear H. 
                  exists b1, delta2. split; trivial.
                intros. destruct (Sep12 _ _ _ H0 J12').
                  apply (res_valid12 _ _ _ _ _ _ _ MS12) in s.
                  contradiction.
              destruct (rsep'' _ _ n0 R'').  
                case_eq (j12 b1).
                  intros [? ?] ?. 
                  rewrite (Inc12 _ _ _ H2) in J12'. inv J12'.
                  exfalso. apply H0; clear H0.
                  solve [eapply (match_validblocks12 _ _ _ _ _ _ _ MS12); eassumption].
                intros. destruct (Sep12 _ _ _ H2 J12').
                  split; trivial; intros. 
                case_eq (j23 b).
                  intros [? ?] ?. 
                  rewrite (Inc23 _ _ _ H6) in H5. inv H5.
                  exfalso. apply H4; clear H4.
                  solve [eapply (match_validblocks23 _ _ _ _ _ _ _ MS23); eassumption].
                intros. apply (Sep23 _ _ _ H6 H5).
                  split; trivial; intros.   H2. contradiction.
                  exfalso. apply H0; clear H. 
                  exists b1, delta2. split; trivial.
                intros. destruct (Sep12 _ _ _ H0 J12').
                  apply (res_valid12 _ _ _ _ _ _ _ MS12) in s.
                  contradiction.
                  eapply (H b1); clear H. H2 H3.
                  solve [e; eassumption].
                intros. apply (Sep12 _ _ _ H4 H3).
                
                destruct (rsep'' _ _ s R'').
                solve[eapply Rsep12; eassumption].
              destruct (rsep'' _ _ H H0).
                split; trivial; intros.
                case_eq (j12 b).
                  intros [? ?] ?. 
                  exfalso. apply H1; clear H1 H2 H3.
                  solve [eapply (match_validblocks12 _ _ _ _ _ _ _ MS12); eassumption].
                intros. apply (Sep12 _ _ _ H4 H3).
           assumption.
 assumption.
               apply reserve_separated_same.
            eapply Guar3'; try eassumption.
            exists b2, delta3. apply Inc23 in J2. 
            split; trivial.
            apply Rinc23.
            rewrite inject_reserve_AX.
            exists b1, delta2.
            split; trivial.
            assert (ofs - delta3 - delta2 = ofs - (delta2 + delta3))
              as -> by omega.
            assumption.
           intros b ofs; intros.
            destruct (Rsep12 _ _ H H0).
          split; trivial.
          intros delta b3 Comp.
          destruct (compose_meminjD_Some _ _ _ _ _ Comp)
            as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]].
          subst; clear Comp.
          case_eq (j23 b2).
            intros [bb d] J23.
              rewrite (Inc23 _ _ _ J23) in J2. inv J2.
              destruct (match_validblocks23 _ _ _ _ _ _ _ MS23 _ _ _ J23).
               exfalso. apply (H2 _ _ J1 H3).
            intros. apply (Sep23 _ _ _ H3 J2).
    split.
      exists st2'. exists m2'. exists j12'. exists j23'.
      split; auto.
      split; auto.
      split; auto.
      split; auto.
      eapply guarantee_incr_alloc1; eauto.
      eapply res_valid12 with (m1:=m1'); eauto.
      intros b1 ofs1 ? ?.
        exploit Rsep12; eauto.
        solve[intros [? ?]; auto].

      intros. (*HAVE MS23' : matchstate23 cd23' r23' j23' st2' m2' st3' m3'*)
      assert (EQ: forall b ofs, Mem.valid_block m2' b -> 
          (r23' b ofs -> r2 b ofs)).
       intros. 
       split; intros.
         destruct (reserve_dec (inject_reserve_ j12 r) b ofs).
           apply Rinc23; assumption.
         destruct (reserve_dec (inject_reserve_ j12' r') b ofs).
           rewrite inject_reserve_AX in s.
           destruct s as [b1 [delta [J1' R']]].
           case_eq (j12 b1).
              intros [? ?] ?.
              rewrite (Inc12 _ _ _ H3) in J1'. inv J1'. exfalso.
              apply n0. rewrite inject_reserve_AX.
              exists b1, delta. split; trivial. 
              destruct (reserve_dec r b1 (ofs - delta)); trivial. 
              exfalso. destruct (Rsep12 _ _ n1 R'). 
              apply H4. exploit match_validblocks12; eauto.
               intros. destruct H6. trivial.
           intros.  destruct (Sep12 _ _ _ H3 J1').  assumption. eauto.
           apply Rinc23; assumption.
       destruct 
      
      admit. (*reserve_sep in match*)
      destruct X23 as [X23 | [X23 ORD23]].
      left. assumption.
      right. split. assumption.             
      solve[eapply sem_compose_ord2; apply ORD23].
Qed.



  (*Case 1*)
    assert (GUAR2: guarantee Sem2 (inject_reserve_ j12 r) st2' m2').
       clear Diag23 core_diagram23.
       unfold guarantee' in Guar2'.
       rewrite inject_reserve_AX. eapply guarantee_decr2. apply Guar2'. 
       auto. auto.
    clear Guar2'. rename GUAR2 into Guar2'.

    specialize (Diag23 _ _ _ _ _ X12 _  _ _ _ _ Guar2' MS23).
    destruct Diag23 as [st3' [m3' [cd23' [r23' [j23'
      [Inc23 [Sep23 [Rinc23 [Rsep23 [Guar3' [MS23' X23]]]]]]]]]]].
     exists st3'. exists m3'. exists ((cd12', Some st2'), cd23'). 
      exists r. (*TRICK: DO NOT USE r12' HERE*)
      exists (compose_meminj j12 j23).
      split. apply inject_incr_refl. (* eapply compose_meminj_inject_incr; eassumption.*)
      split. admit.
(*      split. eapply compose_meminj_inject_separated.
                      eassumption. eassumption. eassumption. eassumption.
                      apply (match_validblocks12 _ _ _ _ _ _ _ MS12).
                      apply (match_validblocks23 _ _ _ _ _ _ _ MS23).*)
      split. apply reserve_incr_refl.
      split. admit. (* 
        intros b ofs; intros.
        split; auto.
        solve[eapply Rsep12; eauto].
        intros delta b3; intros H1.
        apply compose_meminjD_Some in H1.
        destruct H1 as [b2 [delta1 [delta2 [J12' [J23' X]]]]]; subst.
        case_eq (j23 b2).
        intros [? ?] J23.
        generalize J23 as J23''; intro.
        apply Inc23 in J23.
        rewrite J23 in J23'; inv J23'.
        destruct (Rsep12 _ _ H H0).
        elimtype False.
        apply (H2 _ _ J12').
        exploit match_validblocks23; eauto.
        solve[intros [? ?]; auto].
        (*j23 b2 = None*)
        solve[intros; eapply Sep23; eauto].*)
      split.
        unfold guarantee'.
        assert (STEPN: exists n, corestepN Sem3 G3 n st3 m3 st3' m3').
         destruct X23.
         unfold corestep_plus in H.
         destruct H as [m STEPM].
         exists (S m); auto.
         destruct H as [H _].
         unfold corestep_star in H.
         solve[auto].
        destruct STEPN as [m STEPM].
        eapply guarantee_incr_allocN' 
          with (mleft := m1) 
             (j := compose_meminj j12 j23); eauto.
          admit. (*solve[eapply compose_meminj_inject_incr; eassumption].*)
(*          solve[eapply compose_meminj_inject_separated; eauto].*)
        intros b3 ofs; intros.
          destruct H0 as [b1 [delta [Comp R]]].
          destruct (compose_meminjD_Some _ _ _ _ _ Comp)
            as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]].
          subst; clear Comp.
          eapply Guar3'; try eassumption.
          exists b2, delta3. apply Inc23 in J2. 
          split; trivial.
          apply Rinc23.
          rewrite inject_reserve_AX.
          exists b1, delta2.
          split; trivial.
          assert (ofs - delta3 - delta2 = ofs - (delta2 + delta3))
            as -> by omega.
          eauto.
         apply reserve_incr_refl. (*intros b ofs; intros.
          destruct (Rsep12 _ _ H H0).
          split; trivial.
          intros delta b3 Comp.
          destruct (compose_meminjD_Some _ _ _ _ _ Comp)
            as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]].
          subst; clear Comp.
          case_eq (j23 b2).
            intros [bb d] J23.
              rewrite (Inc23 _ _ _ J23) in J2. inv J2.
              destruct (match_validblocks23 _ _ _ _ _ _ _ MS23 _ _ _ J23).
               exfalso. apply (H2 _ _ J1 H3).
            intros. apply (Sep23 _ _ _ H3 J2).*)
         admit.
    split.
      exists st2'. exists m2'. exists j12. exists j23.
      split; auto.
      split; auto.
      split; auto.
      split; auto.
      eapply guarantee_incr_alloc1; eauto.
      eapply res_valid12 with (m1:=m1'); eauto.
      intros b1 ofs1 ? ?.
        exploit Rsep12; eauto.
        solve[intros [? ?]; auto].

      intros.
      
      admit. (*reserve_sep in match*)
      destruct X23 as [X23 | [X23 ORD23]].
      left. assumption.
      right. split. assumption.             
      solve[eapply sem_compose_ord2; apply ORD23].
Qed.
  (*Case2*)
     destruct n.
     (*case n = 0*)
         simpl in X12.
         inv X12.
         exists st3. exists m3. exists ((cd12', Some st2'), d23).
         exists r. (*TRICK: DO NOT USE r12' HERE.*)
         exists (compose_meminj j12 j2).
         split. eapply compose_meminj_inject_incr. eassumption. apply inject_incr_refl.
         split. eapply compose_meminj_inject_separated.
                      eassumption. 
                      apply inject_separated_same_meminj. 
                       assumption. apply inject_incr_refl.
                       apply (match_validblocks12 _ _ _ _ _ _ _ MS12).
                       apply (match_validblocks23 _ _ _ _ _ _ _ MS23).
         split. apply reserve_incr_refl.
         split. apply reserve_separated_same.
         split. intros b3; intros. destruct H1 as [b1 [delta [Comp HR]]].
                destruct (compose_meminjD_Some _ _ _ _ _ Comp)
                    as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]]. subst; clear Comp.
                clear Diag23.
                eapply Guar3. apply H.
                      exists b2. exists delta3. split; trivial.
                         rewrite inject_reserve_AX.
                         exists b1. exists delta2. split; trivial.
                        remember (j1 b1) as q; destruct q; apply eq_sym in Heqq.
                            destruct p. rewrite (Inc12 _ _ _ Heqq) in J1. apply J1.
                        exfalso. destruct (Sep12 _ _ _ Heqq J1) as [NV1 _].
                                       apply NV1; clear NV1.
                                       destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 _].
                                       apply (VAL1 _ _ HR). 
                            assert (Arith: ofs - (delta2 + delta3) = ofs - delta3 - delta2) by omega.
                            rewrite Arith in HR; assumption.
                 apply H2.
         split. exists st2'. exists m2'. exists j12. exists j2.
               exists (inject_reserve_ j12 r).         
(*               destruct (inject_reserve_exists j12 r) as [rrr Hrrr]. exists rrr.*)
                 split; trivial.
                 split; trivial.
                 split. trivial.
                 split. apply ((* match_mono12 *) _ _ _ _ _ _ _ _ MS12'). assumption. 
                 split. apply ((* match_mono23 *) _ _ _ _ _ _ _ _ MS23). 
                    destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [RV _].
                    clear - Inc12 Sep12 RV. rewrite inject_reserve_AX.
                    intros b; intros. rewrite inject_reserve_AX.
                    destruct H as [b1 [delta [HJ HR]]].
                    exists b1. exists delta. split; trivial. 
                    remember (j1 b1) as q.
                    destruct q; apply eq_sym in Heqq. 
                            destruct p. rewrite (Inc12 _ _ _ Heqq) in HJ. apply HJ.
                    exfalso. specialize (RV _ _ HR). 
                                 destruct (Sep12 _ _ _ Heqq HJ). apply (H RV).
                 split. assumption.
                 split. intros b2; intros. apply Guar2; try eassumption.
                       rewrite inject_reserve_AX. rewrite inject_reserve_AX in H1.
                      destruct H1 as [b1 [delta2 [J RR]]]. 
                      assert (J1: j1 b1 = Some (b2,delta2)).        
                            remember (j1 b1) as q; destruct q; apply eq_sym in Heqq.
                                destruct p. rewrite (Inc12 _ _ _ Heqq) in J. apply J.
                            exfalso. destruct (Sep12 _ _ _ Heqq J) as [NV1 _].
                                           apply NV1; clear NV1.
                                            destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 _].
                                            apply (VAL1 _ _ RR). 
                      exists b1. exists delta2. split; trivial. 
                  intros b3; intros. apply Guar3; try eassumption.
                      destruct H1 as [b2 [delta3 [J2 R2]]].
                      exists b2. exists delta3. split; trivial.
                      rewrite  inject_reserve_AX. rewrite inject_reserve_AX in R2.
                      destruct R2 as [b1 [delta2 [J1 R1]]].
                      exists b1. exists delta2. split; trivial.
                      remember (j1 b1) as q; destruct q; apply eq_sym in Heqq.
                                destruct p. rewrite (Inc12 _ _ _ Heqq) in J1. apply J1.
                      exfalso. destruct (Sep12 _ _ _ Heqq J1) as [NV1 _].
                                           apply NV1; clear NV1.
                                            destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 _].
                                            apply (VAL1 _ _ R1). 
       right. split. exists O. simpl. reflexivity.
              eapply sem_compose_ord1. apply ORD12.
    (*case n = S(n') - proof is exactly the one from Case 1*)
    assert (GUAR2: guarantee Sem2 (inject_reserve_ j1 r) st2' m2').
       clear Diag23 core_diagram23.
       unfold guarantee' in Guar2'.
       rewrite inject_reserve_AX. eapply guarantee_decr2. apply Guar2'. assumption. assumption.
(*   clear Guar2'. rename GUAR2 into Guar2'.*)
(*    destruct (inject_reserve_exists j1 r) as [rrr Hrrr].*)
 (*   assert (GUAR2: guarantee Sem2 rrr st2' m2').
          clear - Guar2' rrr Hrrr. rewrite Hrrr. apply Guar2'.
   clear Guar2'. rename GUAR2 into Guar2'.*)
(*    remember  (inject_reserve j1 r) as rrr. 
    assert (rrr_dec: forall b ofs, {rrr b ofs}+{~rrr b ofs}).
        intros; subst. unfold inject_reserve. at.
   assert (GUAR2: guarantee Sem2 (Build_reserve' rrr rrr_dec) st2' m2').
          clear - Guar2' rrr. apply Guar2'.*)
   clear Guar2'. rename GUAR2 into Guar2'.

    specialize (Diag23 _ _ _ _ _ X12 _  _ _ _ _ Guar2' MS23).
    destruct Diag23 as [st3' [m3' [cd23' [r23' [j23
      [Inc23 [Sep23 [Rinc23 [Rsep23 [Guar3' [MS23' X23]]]]]]]]]]].
     exists st3'. exists m3'. exists ((cd12', Some st2'), cd23'). 
      exists r. (*TRICK: DO NOT USE r12' HERE*)
      exists (compose_meminj j12 j23).
      split. eapply compose_meminj_inject_incr; eassumption.
      split. eapply compose_meminj_inject_separated.
                      eassumption. eassumption. eassumption. eassumption.
                      apply (match_validblocks12 _ _ _ _ _ _ _ MS12).
                      apply (match_validblocks23 _ _ _ _ _ _ _ MS23).
      split. apply reserve_incr_refl.
      split. apply reserve_separated_same.
      split. intros b3; intros. destruct H1 as [b1 [delta [Comp HR]]].
                destruct (compose_meminjD_Some _ _ _ _ _ Comp)
                    as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]].
                subst; clear Comp.
                eapply Guar3'. apply H.
                      exists b2. exists delta3. split; trivial. simpl.
                      apply Rinc23.
                         rewrite inject_reserve_AX.
                         exists b1. exists delta2.
                         split.
                            remember (j1 b1) as d.
                            destruct d; apply eq_sym in Heqd.
                              destruct p. rewrite (Inc12 _ _ _ Heqd) in J1; assumption.
                            destruct (Sep12 _ _ _ Heqd J1) as [NV _].
                              exfalso. apply NV.
                              destruct (res_valid12 _ _ _ _ _ _ _ MS12).
                              eapply H1. apply HR.
                         assert (Arith: ofs - (delta2 + delta3) = ofs - delta3 - delta2) by omega.
                            rewrite Arith in HR; assumption.
                 apply H2.
                
     split. exists st2'. exists m2'. exists j12. exists j23.
        exists (inject_reserve_ j12 r).
(*            destruct (inject_reserve_exists j12 r) as [rrr Hrrr].*)
 (*   assert (GUAR2: guarantee Sem2 rrr st2' m2').
          clear - Guar2' rrr Hrrr. rewrite Hrrr. apply Guar2'.
   clear Guar2'. rename GUAR2 into Guar2'.*)
(*             exists  (inject_reserve j12 r).*)
(*             exists  rrr.*)
             split; trivial.
             split; trivial.
             split. trivial.
             split. apply ((* match_mono12 *) _ _ _ _ _ _ _ _ MS12'). assumption. 
             split. apply ((* match_mono23 *) _ _ _ _ _ _ _ _ MS23').
                  simpl in *. subst. 
                  destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [RV _].
                  clear -  Rinc23 Inc12 Sep12 RV. 
                  rewrite inject_reserve_AX.
                  intros b; intros. 
                     eapply Rinc23. rewrite inject_reserve_AX.
                     eapply (reserve_incr_mono _ _ Inc12 _ _ Sep12 _ RV).
                        intros bb. trivial.
                        (* intros. eapply Rinc23. rewrite R. apply H0. *)
                        apply H.
             split. apply H0.
             split; subst; simpl in *. intros b2; intros. 
                        rewrite inject_reserve_AX in H1. destruct H1 as [b1 [delta2 [J RR]]].
                        apply Guar2'; trivial. rewrite inject_reserve_AX.                         
                        exists b1. exists delta2. split; trivial.
                        remember (j1 b1) as q; destruct q; apply eq_sym in Heqq.
                            destruct p. rewrite (Inc12 _ _ _ Heqq) in J. apply J.
                        exfalso. destruct (Sep12 _ _ _ Heqq J) as [NV1 _].
                                       apply NV1; clear NV1.
                                       destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 _].
                                       apply (VAL1 _ _ RR). 
              intros b3; intros. destruct H1 as [b2 [delta3 [J2 R2]]].
                        assert (IR: inject_reserve j1 r b2 (ofs - delta3)).
                                       rewrite inject_reserve_AX in R2.
                                       destruct R2 as [b1 [delta2 [J1 RR]]].
                                       exists b1. exists delta2.
                                       split; trivial.
                                       remember (j1 b1) as w; destruct w; apply eq_sym in Heqw. 
                                                      destruct p. rewrite (Inc12 _ _ _ Heqw) in J1. apply J1.
                                             exfalso. destruct (Sep12 _ _ _ Heqw J1) as [NV1 _].
                                                apply NV1; clear NV1.
                                                destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 VAL2].
                                                apply (VAL1 _ _ RR).
                        apply Guar3'; trivial.
                        exists b2. exists delta3. split; trivial. 
                          apply Rinc23. rewrite inject_reserve_AX. apply IR.
(*                        remember (j2 b2) as q; destruct q; apply eq_sym in Heqq.
                            destruct p. rewrite (Inc23 _ _ _ Heqq) in J2. inv J2.
                            apply Rinc23. apply J2.
                        exfalso. destruct (Sep23 _ _ _ Heqq J2) as [NV2 _].
                                       apply NV2; clear NV2.
                                       destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 VAL2].
                                       destruct IR as [b1 [delta2 [J1 R1]]].
                                       eapply (VAL2 b2  (ofs - delta3)). apply R1. apply J1.
                          rewrite R. apply IR.*)
      (*split. assumption.
      split. eapply guarantee_right_trans_TwoSem; try eassumption.
                intros. apply Guar.
                 exists b0. exists delta. 
                  assert (Arith: ofs0 + delta - delta = ofs0) by omega. 
                  rewrite Arith. split; trivial.*)
       destruct X23 as [X23 | [X23 ORD23]].
          left. assumption.
          right. split. assumption.             
              eapply sem_compose_ord2. apply ORD23.

 (*initial_core*) 
  clear core_diagram23  core_halted23 core_at_external23 core_after_external23 
    core_diagram12  core_halted12 core_at_external12 core_after_external12 
    res_valid12 res_valid23 res_valid12  res_valid23
    (* match_mono12 *) Diag12 Diag23.
  intros. rename m2 into m3. rename v2 into v3. rename vals2 into vals3. 
  rename H2 into WD1. rename H3 into WD3.
  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). 
  eapply forall_valinject_hastype; eassumption.
  destruct (mem_wd_inject_splitL _ _ _ H1 WD1) as [Flat1 XX]; rewrite XX.
  assert (ValInjFlat1 := forall_val_inject_flat _ _ _ H1 _ _ H4).
(*  assert (PUB1:forall b : block, k1 b -> exists b' : block, exists ofs : Z,
                   Mem.flat_inj (Mem.nextblock m1) b = Some (b', ofs)).
       intros. destruct (H5 _ H) as [b2 [ofs2 J]]. 
         eexists. eexists. apply flatinj_I. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ J H1).*)
  assert (RMapValID: reserve_valid' r (Mem.flat_inj (Mem.nextblock m1)) m1).
       intros b1; intros. (*destruct H as [b [delta [J R]]]. *)
            apply flatinj_E in H2. apply H2.
  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ _ H0 Flat1 WD1 WD1 
       ValInjFlat1 HT H6 RMapValID)
    as [d12 [c2 [Ini2 MC12]]].

  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _ _ Ini2 H1 WD1 WD3 H4 H5 H6 H7)
    as [d23 [c3 [Ini3 MC23]]].
  exists (d12,Some c2,d23). exists c3. 
  split; trivial. 
  exists c2. exists m1. exists  (Mem.flat_inj (Mem.nextblock m1)). exists j.
  exists (inject_reserve_ (Mem.flat_inj (Mem.nextblock m1)) r).
  (*exists rrr. exists (inject_reserve (Mem.flat_inj (Mem.nextblock m1)) r).*)
  split; trivial.
  split; trivial.
  split. trivial.
  split; trivial.
  split. apply ((* match_mono23 *) _ _ _ _ _ _ _ _ MC23).
        intros b; intros. rewrite inject_reserve_AX in H.  destruct H as [b1 [delta [J X]]].
              destruct (flatinj_E _ _ _ _ J) as [? [? ?]]. clear XX. subst.
              rewrite Zminus_0_r in X. apply X. 
  split. eapply guarantee_initial; eassumption.
  split; eapply guarantee_initial; eassumption.
 (*safely_halted*)
  clear core_diagram23  core_initial23 core_at_external23 core_after_external23 
    core_diagram12  core_initial12 core_at_external12 core_after_external12.
  intros. rename c2 into c3. rename m2 into m3.  
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [c2 [m2 [j12 [j23 [rr [X [Y [R [MC12 [MC23 [Guar1 [Guar2 Guar3]]]]]]]]]]]]; subst. 
  destruct (core_halted12 _ _ _ _ _ _ _ _ _ MC12 H0 H1)
     as [v2 [vinj12 [SH2 [rty2 Inj12]]]].
  clear core_halted12.
  destruct (core_halted23 _ _ _ _ _ _ _ _ _ MC23 SH2 rty2)
     as [v3 [vinj23 [SH3 [rty3 Inj23]]]].
  clear core_halted23.
  exists v3.
  split. apply (val_inject_compose _ _ _ _ _ vinj12 vinj23).
  split. trivial.
  split. assumption. 
  eapply Mem.inject_compose; eassumption.
(*atexternal*)
  clear core_diagram23  core_initial23 core_halted23 core_after_external23 
    core_diagram12  core_initial12 core_halted12 core_after_external12 Diag12 Diag23.
  intros. rename st2 into st3. rename m2 into m3.  rename H1 into ValsValid1.
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [st2 [m2 [j1 [j2 [r2 [Y [J [R [MC12 [MC23 [Guar1 [Guar2 Guar3]]]]]]]]]]]]. subst.
  apply (core_at_external12 _ _ _ _ _ _ _ _ _ _ MC12) in H0; try assumption. 
  destruct H0 as [MInj12 [PGj1 [vals2 [ValsInj12 [HTVals2 [AtExt2 ValsValid2]]]]]].
  apply (core_at_external23 _ _ _ _ _ _ _ _ _ _ MC23) in AtExt2; try assumption. 
  destruct AtExt2 as [MInj23 [PGj2 [vals3 [ValsInj23 [HTVals3 [AtExt3 ValsValid3]]]]]].
  split. eapply Mem.inject_compose; eassumption.
  split.
  admit. (*TODO: need to prove meminj_preserves_globals G1
            (compose_meminj j1 j2) 
            from meminj_preserves_globals G1 j1
            and meminj_preserves_globals G2 j2*)
  exists vals3. 
  split.  eapply forall_val_inject_compose; eassumption.
  split. assumption.
  split; assumption.
 (*after_external*) clear core_diagram12 core_initial12 core_halted12 
  core_diagram23 core_initial23 core_halted23 Diag12 Diag23. 
  intros cd r r' j j' st1 st3 m1 e vals1 ret1 m1' m3 m3' ret3 sig H
             AtExt1 ValsValid1 PG Inc Sep Rinc Rsep MInj13'
             WD1'  WD3' val_inj_ret13 Fwd1 Fwd3
             Rely1 Rely3 HTret1 HTret3. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [st2 [m2 [j1 [j2 [r2 [Y [J [R [MC12 [MC23 [Guar1 [Guar2 Guar3]]]]]]]]]]]]. subst.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ _ MC12 AtExt1 ValsValid1) 
   as [MInj12 [PGj1 [vals2 [ValsInj12 [HTVals2 [AtExt2 ValsValid2]]]]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ _ MC23 AtExt2 ValsValid2) 
   as [MInj23 [PGj2 [vals3 [ValsInj23 [HTVals3 [AtExt3 ValsValid3]]]]]].
  clear core_at_external12 core_at_external23.
  assert (HTVals1:  Forall2 Val.has_type vals1 (sig_args (ef_sig e))).   
      eapply forall_valinject_hastype; eassumption.
  (*Val.has_type ret1 (proj_sig_res (ef_sig e))). 
            eapply valinject_hastype; eassumption.*)
  destruct (match_memwd12 _ _ _ _ _ _ _ MC12) as [WD1 WD2].
  destruct (match_memwd23 _ _ _ _ _ _ _ MC23) as [_ WD3].
destruct (res_valid12 _ _ _ _ _ _ _ MC12) as [RV1 RVR2].
destruct (res_valid23 _ _ _ _ _ _ _ MC23) as [RV2 RVR3].
assert (Core_after12: forall (cd : cd12) (r : reserve)
                          (j: meminj) (st1 : C1) (st2 : C2) (m1 m2 : mem),
                         matchstate12 cd r j st1 m1 st2 m2 ->
                         meminj_preserves_globals G1 j ->
                  forall (e : external_function) (sig : signature) (vals1 : list val),
                        at_external Sem1 st1 = Some (e, sig, vals1) ->
                        (forall v1 : val, In v1 vals1 -> val_valid v1 m1) ->
                  forall  (m1' : mem) ret1,
                        mem_forward m1 m1' ->
                        rely Sem1 r st1 m1 m1' -> 
                (*        mem_unchanged_on (rely_left Sem1 r st1) m1 m1' ->*)
                        val_has_type_opt' ret1 (proj_sig_res (ef_sig e)) ->
                   forall j' ret2,
                        inject_incr j j' ->
                        inject_separated j j' m1 m2 ->
                        val_has_type_opt' ret2 (proj_sig_res (ef_sig e)) ->
                   forall m2',
                        Mem.inject j' m1' m2' ->
                        mem_forward m2 m2' ->
                        mem_wd m1' -> mem_wd m2' ->
(*                        mem_unchanged_on (rely_right Sem1 j r st1) m2 m2' ->*)
                        rely Sem2 (inject_reserve j r) st2 m2 m2' -> 
                        val_inject_opt j' ret1 ret2 ->
                   forall (r':reserve),
                        reserve_incr r r' ->
                        reserve_separated r r' j' m1 m2 -> (*
                        (forall (b : block) (ofs : Z),
                         ~ r b ofs -> r' b ofs -> ~ owned Sem1 st1 b ofs) ->*)
                        exists (cd' : cd12) (st1' : C1) (st2' : C2),
                          after_external Sem1 ret1 st1 = Some st1' /\
                          after_external Sem2 ret2 st2 = Some st2' /\
                          matchstate12 cd' r' j' st1' m1' st2' m2' (*/\
                          owned Sem1 st1' = owned Sem1 st1 /\
                          owned Sem2 st2' = owned Sem2 st2*)).
     clear - core_after_external12.
    intros. apply (core_after_external12  cd r r' j j' st1 st2 m1 e vals1 ret1 m1' m2 m2' ret2 sig);
                    assumption.
    clear core_after_external12.
    specialize (Core_after12 _ _ _ _ _ _  _ MC12 PGj1).
    specialize (Core_after12 _ _ _ AtExt1 ValsValid1 _ _ Fwd1 Rely1 HTret1).
assert (Core_after23: forall (cd : cd23) (r : reserve)
                          (j: meminj) (st2 : C2) (st3 : C3) (m2 m3 : mem),
                         matchstate23 cd r j st2 m2 st3 m3 ->
                         meminj_preserves_globals G2 j ->
                  forall (e : external_function) (sig : signature) (vals2 : list val),
                        at_external Sem2 st2 = Some (e, sig, vals2) ->
                        (forall v2 : val, In v2 vals2 -> val_valid v2 m2) ->
                  forall  (m2' : mem) ret2,
                        mem_forward m2 m2' ->
                        rely Sem2 r st2 m2 m2' -> 
                (*  mem_unchanged_on (rely_left Sem2 r st2) m2 m2' ->*)
                        val_has_type_opt' ret2 (proj_sig_res (ef_sig e)) ->
                   forall j' ret3,
                        inject_incr j j' ->
                        inject_separated j j' m2 m3 ->
                        val_has_type_opt' ret3 (proj_sig_res (ef_sig e)) ->
                   forall m3',
                        Mem.inject j' m2' m3' ->
                        mem_wd m2' -> mem_wd m3' ->
                        mem_forward m3 m3' ->
(*                        mem_unchanged_on (rely_right Sem2 j r st2) m3 m3' ->*)
                        rely Sem3 (inject_reserve j r) st3 m3 m3' -> 
                        val_inject_opt j' ret2 ret3 ->
                   forall (r': reserve),
                        reserve_incr r r' ->
                        reserve_separated r r' j' m2 m3 ->
(*                        (forall (b : block) (ofs : Z),
                         ~ r b ofs -> r' b ofs -> ~ owned Sem2 st2 b ofs) ->*)
                        exists (cd' : cd23) (st2' : C2) (st3' : C3),
                          after_external Sem2 ret2 st2 = Some st2' /\
                          after_external Sem3 ret3 st3 = Some st3' /\
                          matchstate23 cd' r' j' st2' m2' st3' m3' (* /\
                          owned Sem2 st2' = owned Sem2 st2 /\
                          owned Sem3 st3' = owned Sem3 st3*) ).
     clear - core_after_external23.
    intros. apply (core_after_external23 cd r r' j j' st2 st3 m2 e vals2 ret2 m2' m3 m3' ret3 sig);
                   assumption.
    clear core_after_external23.
(*
  assert (myMC23 : matchstate23 d23 (Build_reserve' (inject_reserve j1 r) Dec1) j2 st2 m2 st3 m3).
                   simpl. apply MC23.
  clear MC23. rename myMC23 into MC23.
*)
    specialize (Core_after23 _ _ _ _ _ _ _ MC23 PGj2).
    specialize (Core_after23 _ _ _ AtExt2 ValsValid2).
  specialize  (RGMEMAX.interpolate_II Sem1 Sem2 _ _ _
             MInj12 _ Fwd1 _ _ MInj23 _ Fwd3 _ MInj13' Inc
             Sep WD1 WD1' WD2 WD3 WD3'); intros IP.

  assert (Rely1_dec: forall (b : block) (ofs : Z),
      {(fun (b0 : block) (ofs0 : Z) =>
        r b0 ofs0 /\ effects Sem1 st1 AllocEffect b0 ofs0) b ofs} +
      {~
       (fun (b0 : block) (ofs0 : Z) =>
        r b0 ofs0 /\ effects Sem1 st1 AllocEffect b0 ofs0) b ofs}).
     clear IP Core_after23 Core_after12. intros.
     destruct (reserve_dec r b ofs).
       destruct (effects_dec Sem1 st1 AllocEffect b ofs).
         left. split; assumption.
       right. intros N. apply n. apply N.
       right. intros N. apply n. apply N.

  assert (Uniform1: uniform
       (fun (b0 : block) (ofs0 : Z) =>
        r b0 ofs0 /\ effects Sem1 st1 AllocEffect b0 ofs0) j1).
     clear IP Core_after23 Core_after12.
     intros b; intros. admit. (*TODO*)

  specialize (IP _ _  Rinc Rsep _ Rely1_dec Uniform1 Rely1 _ Rely3).
(*unfold rely', rely in Rely3.
               (fun (b : block) (ofs : Z) => r b ofs /\
               effects Sem1 st1 AllocEffect b ofs)). _ Rely1 _ Rely3). rely Sem1 r st1 m1 m1'*)
  destruct IP as [m2' [j12' [j23' [J' [Inc12 [Inc23 [MInj12' [Fwd2 
                   [MInj23' [Sep12 [Sep23 [WD2' [RSEP12' [r23 [R23
                   [Rely2 [HRely12 UnchR2]]]]]]]]]]]]]]]]]. (*[Rely33 UnchR33]]]]]]]]]]]]]]]]]]].*)
  subst.
  assert (exists ret2, val_inject_opt j12' ret1 ret2 /\ val_inject_opt j23' ret2 ret3 /\
              val_has_type_opt' ret2 (proj_sig_res (ef_sig e))).
      subst. apply val_inject_opt_split in val_inj_ret13.
                 destruct val_inj_ret13 as [ret2 [injRet12 injRet23]].
      exists ret2. split; trivial. split; trivial.  
         eapply val_inject_opt_hastype; eassumption.
  destruct H as [ret2 [injRet12 [injRet23 HTret2]]]. 
  specialize (WD2' WD2). 
  assert (Unch2: rely Sem2 (inject_reserve j1 r) st2 m2 m2').
       destruct UnchR2 as [UnchR2a UnchR2b].
       split; intros b ofs; intros.
            eapply UnchR2a; try eassumption.
            destruct H as [[b1 [delta2 [J1 RR1]]] Eff2].
            specialize (allocs_shrink12  _ _ _ _ _ _ _ MC12 _ _ Eff2 _ _ J1).
            specialize (HRely12 _ (ofs - delta2) _ _ J1).
             assert (Arith: ofs - delta2 + delta2 = ofs) by omega.
             rewrite Arith in HRely12. apply HRely12.
             split; assumption.
        eapply UnchR2b; try eassumption.
            intros. destruct (H _ H1) as [[b1 [delta2 [J1 RR1]]] Eff2].
            specialize (allocs_shrink12  _ _ _ _ _ _ _ MC12 _ _ Eff2 _ _ J1).
            specialize (HRely12 _ (i - delta2) _ _ J1).
             assert (Arith: i - delta2 + delta2 = i) by omega.
             rewrite Arith in HRely12. apply HRely12.
             split; assumption.
  specialize (Core_after12 _ _ Inc12 Sep12 HTret2 _ MInj12' Fwd2
                       WD1' WD2' Unch2 injRet12).
  rewrite inject_reserve_AX in Core_after23.
  assert (UnchR3: rely Sem3 (inject_reserve j2 (inject_reserve j1 r)) st3 m3 m3' ).
            destruct Rely3 as [Rely3a Rely3b].
            split; intros b3 ofs; intros.
                eapply Rely3a; try eassumption.
                destruct H as [[b2 [delta3 [J2 RR]]] Eff3].
                split; trivial.
                destruct RR as [b1 [delta2 [J1 RR1]]].
                exists b1. unfold compose_meminj. rewrite J1. rewrite J2.
                exists (delta2 + delta3).
                assert (Arith: ofs - (delta2 + delta3) = ofs - delta2 - delta3) by omega.
                rewrite Arith.
                split; trivial.
                assert (Arith1: ofs - delta2 - delta3 = ofs - delta3 - delta2) by omega.
                rewrite Arith1. apply RR1.
            eapply Rely3b; try eassumption. intros.
                destruct (H _ H1) as [[b2 [delta3 [J2 RR]]] Eff3].
                split; trivial.
                destruct RR as [b1 [delta2 [J1 RR1]]].
                exists b1. unfold compose_meminj. rewrite J1. rewrite J2.
                exists (delta2 + delta3).
                assert (Arith: i - (delta2 + delta3) = i - delta2 - delta3) by omega.
                rewrite Arith.
                split; trivial.
                assert (Arith1: i - delta2 - delta3 = i - delta3 - delta2) by omega.
                rewrite Arith1. apply RR1.
  specialize (Core_after23 _ _ Fwd2 Unch2 HTret2 _ _ Inc23 
                      Sep23 HTret3 _ MInj23' WD2' WD3' Fwd3 UnchR3 injRet23).

  (*need to specialize coreafter12 to r' so that we get matchstate12' for r'*)
  specialize (Core_after12 r' Rinc RSEP12'). 
  destruct Core_after12 as [cd12' [st1' [st22' [AFT1 [Aft2 MS12]]]]]. (* [OWN1 OWN2]]]]]]].*)

(*  destruct (inject_reserve_exists j12' r') as [r12' Hr12'].*)
  (*specialize (Core_after23 (inject_reserve j12' r')).*)

  assert (Rinc2: reserve_incr (inject_reserve_ j1 r) (inject_reserve_ j12' r')). 
          subst. intros b2; intros. rewrite inject_reserve_AX.
                  rewrite inject_reserve_AX in H.
                  destruct H as [b1 [delta [HJ HR]]].
                  exists b1. exists delta. 
                  split. apply Inc12. assumption.    
                  apply Rinc. assumption.
  assert (Rsep23:  reserve_separated (inject_reserve_ j1 r) (inject_reserve_ j12' r') j23' m2 m3).
                  intros b2; intros. rewrite inject_reserve_AX in H0.
                  rewrite inject_reserve_AX in H.
                  destruct H0 as [b1 [delta [HJ HR]]].
                  remember (j1 b1) as q.
                  destruct q; apply eq_sym in Heqq. 
                          destruct p. rewrite (Inc12 _ _ _ Heqq) in HJ. inv HJ.
                      exfalso. apply H. exists b1. exists delta. split; trivial.
                      destruct (reserve_dec r b1 (ofs - delta)); trivial.
                      destruct (RSEP12' _ _ n HR).
                      exfalso. apply H0. 
                           apply (match_validblocks12 _ _ _ _ _ _ _ MC12 _ _ _ Heqq).
                  destruct (Sep12 _ _ _ Heqq HJ).
                      split; trivial.
                      intros delta3 b3 J2'. 
                      remember (j2 b2) as w.
                      destruct w; apply eq_sym in Heqw. 
                          destruct p. rewrite (Inc23 _ _ _ Heqw) in J2'. inv J2'.
                          exfalso. apply H1. 
                           apply (match_validblocks23 _ _ _ _ _ _ _ MC23 _ _ _ Heqw).
                      destruct (Sep23 _ _ _ Heqw J2'). apply H3.
  assert (RINC12: reserve_incr (inject_reserve j1 r) (inject_reserve_ j12' r')).
    rewrite inject_reserve_AX. intros b; intros.
         destruct H as [b1 [delta [JJ RR]]].
         apply Inc12 in JJ. apply Rinc in RR.
         exists b1. exists delta; auto.
  assert (RESP: reserve_separated (inject_reserve j1 r) (inject_reserve_ j12' r') j23' m2 m3).
     intros b; intros. rewrite inject_reserve_AX in H0.
     destruct H0 as [b1 [delta [JJ RR]]]. 
     remember (j1 b1) as d.
     destruct d; apply eq_sym in Heqd. 
        exfalso. destruct p.
        apply H; clear H. exists b1. exists delta. 
        rewrite (Inc12 _ _ _ Heqd) in JJ. inv JJ.
        split. trivial.
        destruct (reserve_dec r b1 (ofs - delta)); trivial.
        destruct (RSEP12' _ _ n RR).
        exfalso. apply H.
          apply (match_validblocks12 _ _ _ _ _ _ _ MC12 _ _ _ Heqd).
      destruct (Sep12 _ _ _ Heqd JJ). split; trivial.
        intros. 
        remember (j2 b) as w.
        destruct w; apply eq_sym in Heqw.  
          exfalso. destruct p. apply H1. 
            apply (match_validblocks23 _ _ _ _ _ _ _ MC23 _ _ _ Heqw).
          apply (Sep23 _ _ _ Heqw H2).
  specialize (Core_after23 _ RINC12 RESP).
  destruct Core_after23 as [cd23' [st2' [st3' [Aft22 [Aft33 MS23]]]]]. (* [OWN22 OWN3]]]]]]].*)
(*
    intros. intros N. destruct H1 as [b1 [delta [J' R']]].
           apply (own_valid23 _ _ _ _ _ _ _ MC23) in N.
                  remember (j1 b1) as q.
                  destruct q; apply eq_sym in Heqq. 
                          destruct p. rewrite (Inc12 _ _ _ Heqq) in J'. inv J'.
                          destruct (reserve_map_dec r b1 (ofs - delta)).
                            exfalso. apply H0. exists b1. exists delta. split; assumption.
                          destruct (RSEP12' _ _ n R').
                            apply Inc12 in Heqq. apply (H2 _ _ Heqq N).
                  destruct (Sep12 _ _ _ Heqq J').
                      apply (H2 N).*)
  rewrite Aft2 in Aft22. inv Aft22.
  exists (cd12', Some st2', cd23'). exists st1'. exists st3'.
  split. assumption.
  split. assumption.
  (*split.*) exists st2'. exists m2'. exists j12'. exists j23'.
     exists (inject_reserve_ j12' r'). rewrite inject_reserve_AX.
     split; trivial. 
     split; trivial. 
     split; trivial.
     split; trivial.
     split; trivial.
     split. 
              destruct (effects_valid12 _ _ _ _ _ _ _ MC12) as [EVal1 _].
              clear - AtExt1 AFT1 Guar1 Rinc RSEP12' EVal1.
               assert (HS1: reserve_separated1 r r' m1). 
                      unfold reserve_separated1. apply RSEP12'.
              specialize (guarantee_incr _ _ _ _ _ Guar1 Rinc HS1).
              intros GI b; intros.
              destruct (effects_external _ b ofs _ _ AllocEffect _ _ _ _ AtExt1 AFT1) as [Alloc _].
              destruct (effects_external _ b ofs _ _ ModifyEffect _ _ _ _ AtExt1 AFT1) as [_ Modify'].
              specialize (Modify' H1).
              specialize (EVal1 _ _ _ Modify').
              apply Alloc.
              apply GI; trivial.
     split. 
              destruct (effects_valid12 _ _ _ _ _ _ _ MC12) as [_ EVal2].
               assert (Rsep2: reserve_separated1 (inject_reserve_ j1 r) (inject_reserve_ j12' r') m2). 
                      unfold reserve_separated1. apply Rsep23. 
              clear - AtExt2 Aft2 Guar2 Rinc2 Rsep2 EVal2.
              specialize (guarantee_incr _ _ _ _ _ Guar2 Rinc2 Rsep2).
              intros GI b; intros.
              destruct (effects_external _ b ofs _ _ AllocEffect _ _ _ _ AtExt2 Aft2) as [Alloc _].
              destruct (effects_external _ b ofs _ _ ModifyEffect _ _ _ _ AtExt2 Aft2) as [_ Modify'].
              specialize (Modify' H1).
              specialize (EVal2 _ _ _ Modify').
              apply Alloc.
              apply GI; trivial.
              rewrite inject_reserve_AX. assumption.

         destruct (effects_valid23 _ _ _ _ _ _ _ MC23) as [_ EVal3].
(*              destruct (inject_reserve_exists j2 r2) as [j2r2 Hj2r2].
              destruct (inject_reserve_exists j23' r12') as [j23r12' Hj23r12'].*)

              assert (GUAR3: guarantee Sem3 (inject_reserve_ j2 (inject_reserve_ j1 r)) st3 m3).
                  intros b3 ofs. rewrite inject_reserve_AX.
                     intros. eapply (Guar3 b3 ofs); trivial.
(*                     rewrite inject_reserve_AX in H0. apply H0.*)
              clear Guar3.
             intros b; intros.
              destruct (effects_external _ b ofs _ _ AllocEffect _ _ _ _ AtExt3 Aft33) as [Alloc _].
              destruct (effects_external _ b ofs _ _ ModifyEffect _ _ _ _ AtExt3 Aft33) as [_ Modify'].
              specialize (Modify' H1).
              specialize (EVal3 _ _ _ Modify').
              apply Alloc.
              clear - GUAR3 Inc12 Sep12 Rsep23 Inc23 Sep23 Rinc2 Rsep RV1 EVal3 H0 Modify'.
              assert (Rinc3: reserve_incr (inject_reserve_ j2 (inject_reserve_ j1 r))
                               (inject_reserve_ j23' (inject_reserve_ j12' r'))).
                   intros b3 delta IR. repeat rewrite inject_reserve_AX in *.
                   destruct IR as [b2 [delta3 [J2 RR]]].   
                   apply Inc23 in J2. apply Rinc2 in RR. 
                   exists b2. exists delta3.
                   split; assumption.
               assert (Rsep3: reserve_separated1 (inject_reserve_ j2 (inject_reserve_ j1 r))
                               (inject_reserve_ j23' (inject_reserve_ j12' r')) m3).
                      unfold reserve_separated1. repeat rewrite inject_reserve_AX in *. 
                      intros b3 z NIR IR. intros N.  
                      destruct IR as [b2 [delta3 [J2 RR2]]].
                      remember (j2 b2) as q; destruct q; apply eq_sym in Heqq.
                      Focus 2. destruct (Sep23 _ _ _ Heqq J2).
                               apply (H1 N).
                      destruct p. rewrite (Inc23 _ _ _ Heqq) in J2. inv J2.
                      destruct RR2 as [b1 [delta2 [J1 RR1]]].
                      apply NIR; clear NIR.
                      exists b2. exists delta3. split. assumption.
                      exists b1. exists delta2.
                      destruct (reserve_dec r b1 (z - delta3 - delta2)).
                         specialize (RV1 _ _ s).
                         remember (j1 b1) as w.
                         destruct w; apply eq_sym in Heqw.
                           destruct p. rewrite (Inc12 _ _ _ Heqw) in J1. inv J1.
                           auto.
                         destruct (Sep12 _ _ _ Heqw J1). exfalso. apply (H RV1).
                       destruct (Rsep _ _ n RR1).
                       exfalso. apply (H1 (delta2 + delta3) b3); trivial.
                          unfold compose_meminj. rewrite J1.
                          rewrite (Inc23 _ _ _ Heqq). trivial.
              eapply (guarantee_incr _ _ _ _ _ GUAR3 Rinc3 Rsep3).
                apply EVal3. 
                repeat rewrite inject_reserve_AX. apply H0.
                assumption. 
Qed.
End RGSIM_TRANS.

(*
Section RGSIM_TRANS_EQ.
Context  (F1 C1 V1 F2 C2 V2 F3 C3 V3:Type)
               (Sem1 : RelyGuaranteeSemantics (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
               (Sem2 : RelyGuaranteeSemantics (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
               (Sem3 : RelyGuaranteeSemantics (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
               (entrypoints12 : list (val * val * signature))
               (entrypoints23 : list (val * val * signature))
               (entrypoints13 : list (val * val * signature))
               (EPC : entrypoints_compose entrypoints12  entrypoints23 entrypoints13)
               (G1 : Genv.t F1 V1) (G2 : Genv.t F2 V2) (G3 : Genv.t F3 V3)
               (SimEq12 : Forward_simulation_eq.Forward_simulation_equals mem
                      (list (ident * globdef F1 V1)) (list (ident * globdef F2 V2)) Sem1 Sem2
                      G1 G2 entrypoints12).

Lemma eqeq: 
    forall (SimEq23 : Forward_simulation_eq.Forward_simulation_equals mem
                      (list (ident * globdef F2 V2)) (list (ident * globdef F3 V3)) Sem2 Sem3
                      G2 G3 entrypoints23),
    Forward_simulation_eq.Forward_simulation_equals
          mem (list (ident * globdef F1 V1))  (list (ident * globdef F3 V3))
          Sem1 Sem3 G1 G3 entrypoints13.
Proof. intros.
  destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 
    core_initial12 core_halted12 core_at_external12 core_after_external12].  
  destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 
    core_initial23 core_halted23 core_at_external23 core_after_external23].
  eapply Forward_simulation_eq.Build_Forward_simulation_equals with
    (core_data:= prod (prod core_data12 (option C2)) core_data23) 
    (match_core := fun d c1 c3 => match d with (d1,X,d2) => 
      exists c2, X=Some c2 /\ match_core12 d1 c1 c2 /\ match_core23 d2 c2 c3 end)
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)).
(*wellfounded*) 
   eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
(*core_diagram*) 
   clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  
     core_halted12 core_at_external12 core_after_external12.
   clear core_ord_wf12 core_ord_wf23. 
   intros. destruct d as [[d12 cc2] d23]. destruct H0 as [c2 [X [? ?]]]; subst.
  eapply (diagram_eqeq _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 
    core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ _ _ core_diagram23); eassumption. 
(*initial_core*)
  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  destruct (core_initial12 _ _ _ EP12 _ H0) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
  destruct (core_initial23 _ _ _ EP23 _ H0) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
  rewrite Ini22 in Ini2. inv Ini2.
  exists (d12,Some c2,d23). exists c1. exists c3. split; trivial. split; trivial. 
    exists c2. split; trivial. split; trivial.
(*safely_halted*)
  intros. rename c2 into c3. destruct cd as [[d12 cc2] d23]. 
    destruct H as [c2 [X [MC12 MC23]]]. subst.
  apply (core_halted12 _ _ _ _ MC12) in H0.
  apply (core_halted23 _ _ _ _ MC23) in H0. assumption.
(*atexternal*)
  intros. rename st2 into st3. destruct d as [[d12cc2]  d23]. 
    destruct H as [st2 [X [MC12 MC23]]]; subst.
  apply (core_at_external12 _ _ _ _ _ _ MC12) in H0. destruct H0.
  apply (core_at_external23 _ _ _ _ _ _ MC23) in H. assumption.  
(*after_external*)
  intros. rename st2 into st3. destruct d as [[d12 cc2] d23]. 
    destruct H as [st2 [X [MC12 MC23]]]; subst.
  destruct (core_at_external12 _ _ _ _ _ _ MC12 H0)  as [AtExt2 _].
  destruct (core_after_external12 _ _ _ _ _ _ _ MC12 H0 AtExt2 H2 H3) 
    as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
  destruct (core_after_external23 _ _ _ _ _ _ _ MC23 AtExt2 H1 H2 H3) 
    as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists c1'. exists c3'. exists (d12',Some c2',d23'). split; trivial. 
    split; trivial. exists c2'. split; trivial. split; trivial. 
Qed.

Lemma eqext: 
    forall (SimExt23 : Coop_forward_simulation_ext.Forward_simulation_extends
                      (list (ident * globdef F2 V2)) (list (ident * globdef F3 V3)) Sem2 Sem3
                      G2 G3 entrypoints23),
   Coop_forward_simulation_ext.Forward_simulation_extends
      (list (ident * globdef F1 V1)) (list (ident * globdef F3 V3))
      Sem1 Sem3 G1 G3 entrypoints13.
Proof. intros.
  destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12 
    core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
  destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23 match_memwd23 match_validblocks23
    core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
  eapply Coop_forward_simulation_ext.Build_Forward_simulation_extends with
    (match_state := fun d c1 m1 c3 m3 => match d with (d1,X,d2) => 
       exists c2, X = Some c2 /\ match_core12 d1 c1 c2 /\ match_core23 d2 c2 m1 c3 m3 end)
    (core_data:= prod (prod core_data12 (option C2)) core_data23)
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)). 
(*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
(*match_wd*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
  destruct H as [c2 [X [MC12 MC23]]]; subst.
  apply (match_memwd23 _ _ _ _ _ MC23).
(*match_validblocks*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
  destruct H as [c2 [X [MC12 MC23]]]; subst.
  eapply (match_validblocks23 _ _ _ _ _ MC23); try eassumption.
(*core_diagram*) 
  clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12
    core_ord_wf23 core_ord_wf12.
  intros. rename st2 into st3.
  destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [X [? ?]]]; subst. rename m2 into m3.
  eapply (diagram_eqext _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); eassumption. 
(*initial_core*)
  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  assert (HT: Forall2 Val.has_type vals (sig_args sig)). eapply forall_lessdef_hastype; eauto.
  destruct (core_initial12 _ _ _ EP12 _ HT) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
  destruct (core_initial23 _ _ _ EP23 _ _ _ _ H0 H1 H2 H3 H4) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
  rewrite Ini22 in Ini2. inv Ini2.
  exists (d12,Some c2,d23). exists c1. exists c3. 
  split; trivial. split; trivial. exists c2. split; trivial. split; trivial.
(*safely_halted*)
  intros. rename st2 into c3. destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
  apply (core_halted12 _ _ _ _ MC12) in H0.
  apply (core_halted23 _ _ _ _ _ _ MC23) in H0. assumption. assumption.
(*atexternal*)
  intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H as [st2 [X [MC12 MC23]]].
  apply (core_at_external12 _ _ _ _ _ _ MC12) in H0. destruct H0.
  apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in H. assumption. assumption.
(*after_external*)
  intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H as [st2 [X [MC12 MC23]]].
  destruct (core_at_external12 _ _ _ _ _ _ MC12 H0)  as [AtExt2 _].
  assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). eapply forall_lessdef_hastype; eauto.
  assert (HRet1:   Val.has_type ret1 (proj_sig_res ef_sig)). eapply lessdef_hastype; eauto.
  destruct (core_after_external12 _ _ _ _ _ _ _ MC12 H0 AtExt2 HVals1 HRet1) 
    as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
  destruct (core_after_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ MC23 AtExt2 H1 H2 H3 H4 H5 H6 H7 H8 H9 
    H10 H11 H12 H13 H14) as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists c1'. exists c3'. exists (d12',Some c2',d23'). 
  split; trivial. split; trivial. exists c2'. split; trivial. split; trivial.
Qed.

Lemma eqinj: 
    forall (SimInj23 : Coop_forward_simulation_inj.Forward_simulation_inject
                      (list (ident * globdef F2 V2)) (list (ident * globdef F3 V3)) Sem2 Sem3
                      G2 G3 entrypoints23),
    Coop_forward_simulation_inj.Forward_simulation_inject 
             (list (ident * globdef F1 V1)) (list (ident * globdef F3 V3))
             Sem1 Sem3 G1 G3 entrypoints13.
Proof. intros.
          destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
         destruct SimInj23 as [core_data23 match_core23 core_ord23 core_ord_wf23 match_memwd23
              match_validblock23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
          eapply Coop_forward_simulation_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, X=Some c2 /\ match_core12 d1 c1 c2 /\ match_core23 d2 j c2 m1 c3 m3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*match_wd*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
                         destruct H as [c2 [X [MC12 MC23]]]; subst.
                         apply (match_memwd23 _ _ _ _ _ _ MC23).
            (*match_validblocks*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
                         destruct H as [c2 [X [MC12 MC23]]]; subst.
                         eapply (match_validblock23 _ _ _ _ _ _ MC23); try eassumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12.                          
                 intros. rename st2 into st3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [X [? ?]]]; subst. rename m2 into m3.
                 eapply (diagram_eqinj _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); try eassumption.
            (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). eapply forall_valinject_hastype; eauto.
                  destruct (core_initial12 _ _ _ EP12 _ HT) as [d12 [c11 [c2 [Ini1 [Ini2 MC12]]]]]. rewrite Ini1 in H0. inv H0.
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2 H3 H4 H5) as [d23 [c3 [Ini3 MC23]]].
                  exists (d12,Some c2,d23). exists c3. split; trivial. exists c2. auto.
             (*safely_halted*)
                    intros. rename c2 into c3. destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                    apply (core_halted12 _ _ _ _ MC12) in H0; try assumption.
                    apply (core_halted23 _ _ _ _ _ _ _ MC23) in H0; try assumption.
             (*atexternal*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. 
                    destruct H as [c2 [X [MC12 MC23]]]; subst. 
                    apply (core_at_external12 _ _ _ _ _ _ MC12) in H0. destruct H0.
                    apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in H; try assumption. 
                    destruct H as [MInj12 [PG2 X]].
                    assert (PG1: meminj_preserves_globals G1 j). admit. (*have meminj_preserves_globals G2 j*)  
                    split. trivial. 
                    split; assumption.
             (*after_external*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. 
                    destruct H0 as [c2 [X [MC12 MC23]]]; subst.
                    destruct (core_at_external12 _ _ _ _ _ _ MC12 H1)  as [AtExt2 HVals1]; try assumption.
                    assert (HRet1:   Val.has_type ret1 (proj_sig_res ef_sig)). eapply valinject_hastype; eassumption.
                    destruct (core_after_external12 _ _ _ _ _ _ _ MC12 H1 AtExt2 HVals1 HRet1) as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    assert (PG2: meminj_preserves_globals G2 j).  at. (*have meminj_preserves_globals G1 j*)
                    destruct (core_after_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H MC23 AtExt2 H2 PG2 H4
                       H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16) as [d23' [c22' [c3' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',Some c2',d23'). exists c1'. exists c3'. split; trivial. split; trivial. exists c2'. auto.
Qed.

Lemma CaseEq: forall
              (SIM23 : sim F2 C2 V2 F3 C3 V3 Sem2 Sem3 G2 G3 entrypoints23),
              sim F1 C1 V1 F3 C3 V3 Sem1 Sem3 G1 G3 entrypoints13.
Proof. intros.
induction SIM23; intros; subst.
 (*equality pass Sem2 -> Sem3*)  
       apply simeq. apply (eqeq R). 
 (*extension pass Sem2 -> Sem3*) 
       apply simext. apply (eqext R). 
 (*injection pass Sem2 -> Sem3*) 
       apply siminj. apply (eqinj R). 
Qed.
End MINISIM_TRANS_EQ.

Section MINISIM_TRANS_EXT.
Context  (F1 C1 V1 F2 C2 V2 F3 C3 V3:Type)
               (Sem1 : RelyGuaranteeSemantics (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
               (Sem2 : RelyGuaranteeSemantics (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
               (Sem3 : RelyGuaranteeSemantics (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
               (entrypoints12 : list (val * val * signature))
               (entrypoints23 : list (val * val * signature))
               (entrypoints13 : list (val * val * signature))
               (EPC : entrypoints_compose entrypoints12  entrypoints23 entrypoints13)
               (G1 : Genv.t F1 V1) (G2 : Genv.t F2 V2) (G3 : Genv.t F3 V3)
               (SimExt12 : Coop_forward_simulation_ext.Forward_simulation_extends
                      (list (ident * globdef F1 V1)) (list (ident * globdef F2 V2)) Sem1 Sem2
                      G1 G2 entrypoints12).

Lemma exteq: 
    forall (SimEq23 : Forward_simulation_eq.Forward_simulation_equals mem
                   (list (ident * globdef F2 V2)) (list (ident * globdef F3 V3)) Sem2 Sem3
                   G2 G3 entrypoints23),
    Coop_forward_simulation_ext.Forward_simulation_extends
               (list (ident * globdef F1 V1)) (list (ident * globdef F3 V3))
               Sem1 Sem3 G1 G3 entrypoints13. 
Proof. intros.
      destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12 match_memwd12 match_validblocks12
                 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
      destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23
                           core_initial23 core_halted23 core_at_external23 core_after_external23].
  eapply Coop_forward_simulation_ext.Build_Forward_simulation_extends with 
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, X=Some c2 /\ match_core12 d1 c1 m1 c2 m3 /\ match_core23 d2 c2 c3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*match_wd*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
                         destruct H as [c2 [X [MC12 MC23]]]; subst.
                         apply (match_memwd12 _ _ _ _ _ MC12).
            (*match_validblocks*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
                         destruct H as [c2 [X [MC12 MC23]]]; subst.
                         eapply (match_validblocks12 _ _ _ _ _ MC12); try eassumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12
                          core_ord_wf23 core_ord_wf12.
                 intros. rename st2 into st3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [X [? ?]]]; subst. rename m2 into m3.
                 eapply (diagram_exteq _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); try eassumption.
            (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ H0 H1 H2 H3 H4) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
                  destruct (core_initial23 _ _ _ EP23 _ H1) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2, d23). exists c1. exists c3. 
                  split; trivial. split; trivial. exists c2. split; trivial. split; trivial.
             (*safely_halted*)
                    intros. rename st2 into c3.  destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst. 
                    apply (core_halted12 _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [LD [SH2 Ext]]].
                    apply (core_halted23 _ _ _ _ MC23) in SH2. exists v2. split; trivial. split; trivial. assumption.
             (*atexternal*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0. 
                      destruct H0 as [vals2 [Ext [LD [HT2 [AtExt2 VV2]]]]].
                      destruct (core_at_external23 _ _ _ _ _ _ MC23 AtExt2). 
                      exists vals2. split; trivial. split; trivial. split; trivial. split; assumption.  
                    assumption.
             (*after_external*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                     rename vals2 into vals3. rename ret2 into ret3.
                    assert (X:=core_at_external12 _ _ _ _ _ _ _ _ MC12 H0 H1). destruct X as [vals2 [Ext [LD [HT2 [AtExt2 VV2]]]]]. 
                    assert (X:=core_at_external23 _ _ _ _ _ _ MC23 AtExt2). 
                    destruct X as [AtExt3 HTargs2]. rewrite AtExt3 in H2. inv H2.
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ _ MC12 H0 H1 AtExt2
                         LD HT2 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14) as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    destruct (core_after_external23 _ _ _ _ _ _ _ MC23 AtExt2 AtExt3 HT2 H10) 
                         as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists c1'. exists c3'. exists (d12',Some c2', d23'). 
                    split; trivial. split; trivial. exists c2'. split; trivial. split; trivial.
Qed.
       
Lemma extext: 
   forall (SimExt23 : Coop_forward_simulation_ext.Forward_simulation_extends
                            (list (ident * globdef F2 V2)) (list (ident * globdef F3 V3))
                           Sem2 Sem3 G2 G3 entrypoints23),
   Coop_forward_simulation_ext.Forward_simulation_extends
              (list (ident * globdef F1 V1)) (list (ident * globdef F3 V3))
              Sem1 Sem3 G1 G3 entrypoints13. 
Proof. intros.
  destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12
                        match_wd12 match_vb12 core_diagram12 core_initial12
                        core_halted12 core_at_external12 
                        core_after_external12].  
  destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23 match_wd23 match_vb23
    core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
  eapply Coop_forward_simulation_ext.Build_Forward_simulation_extends with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, exists m2, X=Some c2 /\
     match_core12 d1 c1 m1 c2 m2 /\ match_core23 d2 c2 m2 c3 m3 end).
(*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
(*match_wd*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
  destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
  split. apply (match_wd12 _ _ _ _ _ MC12).
  apply (match_wd23 _ _ _ _ _ MC23).
(*match_validblocks*) 
  intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
  destruct H as [c2 [m [X [MC12 MC23]]]]; subst.
  split; intros. eapply (match_vb23 _ _ _ _ _ MC23). 
  eapply (match_vb12 _ _ _ _ _ MC12). apply H.
  eapply (match_vb12 _ _ _ _ _ MC12). 
  eapply (match_vb23 _ _ _ _ _ MC23). apply H. 
(*core_diagram*)
  clear core_initial23 core_halted23 core_at_external23 core_after_external23 
             core_initial12  core_halted12 core_at_external12 core_after_external12
            core_ord_wf23 core_ord_wf12.
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [X [? ?]]]]; subst.
  eapply (diagram_extext _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 
    core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); try eassumption.
 (*initial_core*)
  intros. rename m2 into m3. rename vals' into args3. rename vals into args1. rename v2 into v3.
  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  assert (HT: Forall2 Val.has_type args1 (sig_args sig)). eapply forall_lessdef_hastype; eassumption.
  destruct (core_initial12 _ _ _ EP12 _ _ m1 _ (forall_lessdef_refl args1) HT (extends_refl _)) 
    as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]]; try assumption.
  destruct (core_initial23 _ _ _ EP23 _ _ _ _ H0 H1 H2) 
    as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]]; try assumption.
  rewrite Ini22 in Ini2. inv Ini2.
  exists (d12,Some c2, d23). exists c1. exists c3. split; trivial. split; trivial.
  exists c2. exists m1. split; trivial. split; trivial.
 (*safely_halted*)
  intros. rename st2 into c3. rename m2 into m3.  destruct cd as [[d12 cc2] d23]. 
  destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
  apply (core_halted12 _ _ _ _ _ _ MC12) in H0; try assumption. 
  destruct H0 as [v2 [V12 [SH2 [Ext12 VV2]]]].
  apply (core_halted23 _ _ _ _ _ _ MC23) in SH2; try assumption. 
  destruct SH2 as [v3 [V23 [SH3 [Ext23 VV3]]]].
  exists v3. split. eapply Val.lessdef_trans; eassumption.
  split; trivial. 
  split. eapply extends_trans; eassumption.
  assumption.
 (*atexternal*)
  intros. rename st2 into st3. rename m2 into m3. destruct cd as [[d12 cc2] d23]. 
  destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
  apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0; try assumption. 
  destruct H0 as [vals2 [Ext12 [LD12 [HT2 [AtExt2 VV2]]]]].
  apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in AtExt2; try assumption. 
  destruct AtExt2 as [vals3 [Ext23 [LS23 [HT3 [AtExt3 VV3]]]]]. 
  exists vals3. split. eapply extends_trans; eassumption.
  split. eapply forall_lessdef_trans; eassumption.
  split. assumption.
  split; assumption.
 (*after_external*)
  intros. rename st2 into st3. rename m2 into m3. rename m2' into m3'.  
  rename vals2 into vals3. rename ret2 into ret3. 
  destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 H0) 
    as [vals2 [Ext12 [ValsLD12 [HTVals2 [AtExt2 VV2]]]]]; try assumption.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2) 
    as [vals33 [Ext23 [ValsLD23 [HTVals3 [AtExt3 VV3]]]]]; try assumption.
  rewrite AtExt3 in H2. inv H2.
  assert (HTR1: Val.has_type ret1 (proj_sig_res ef_sig)). eapply lessdef_hastype; eassumption.
  assert (UnchOn3 :  my_mem_unchanged_on (loc_out_of_bounds m2) m3 m3').
  split; intros; eapply H7; trivial.
  eapply extends_loc_out_of_bounds; eassumption.
  intros. apply H in H15. eapply extends_loc_out_of_bounds; eassumption.
  destruct (MEMAX.interpolate_EE _ _ Ext12 _ H5 _ Ext23 _ H6 H9 H7 H12) 
    as [m2' [Fwd2 [Ext12' [Ext23' [UnchOn2 WD2]]]]].
  assert (WD2': mem_wd m2'). apply (extends_memwd _ _ Ext23' H12).
  assert (ValV2': val_valid ret1 m2'). eapply (extends_valvalid _ _ Ext12'). apply H13.
  destruct (core_after_external12 _ _ _ _ _ _ _ _ ret1 ret1 _ _ _ MC12 H0 H1 AtExt2 ValsLD12
    HTVals2 H5 Fwd2 UnchOn2 (Val.lessdef_refl _) Ext12' HTR1 H11 WD2' H13 ValV2') 
  as [c1' [c2' [d12' [AftExt1 [AftExt2 MC12']]]]].
  destruct (core_after_external23 _ _ _ _ _ _ _ _ ret1 ret3 _ _ _ MC23 AtExt2 VV2 AtExt3
    ValsLD23 HTVals3 Fwd2 H6 UnchOn3 H8 Ext23' H10 WD2' H12 ValV2' H14)
  as [cc2' [c3' [d23' [AftExt22 [AftExt3 MC23']]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists c1'. exists c3'. exists (d12',Some c2', d23'). split; trivial. split; trivial.
  exists c2'. exists m2'. split; trivial. split; trivial.
Qed.

Lemma extinj:
    forall (SimInj23 : Coop_forward_simulation_inj.Forward_simulation_inject
                   (list (ident * globdef F2 V2)) (list (ident * globdef F3 V3)) 
                   Sem2 Sem3 G2 G3 entrypoints23),
    Coop_forward_simulation_inj.Forward_simulation_inject
               (list (ident * globdef F1 V1)) (list (ident * globdef F3 V3))
               Sem1 Sem3 G1 G3 entrypoints13.
Proof. intros.
         destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12 match_memwd12 match_validblocks12
                      core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
         destruct SimInj23 as [core_data23 match_core23 core_ord23 core_ord_wf23 match_memwd23 match_validblocks23
                      core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
          eapply Coop_forward_simulation_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, exists m2, X=Some c2 /\ 
                                                  match_core12 d1 c1 m1 c2 m2 /\ match_core23 d2 j c2 m2 c3 m3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*match_wd*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
                         destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                         split. apply (match_memwd12 _ _ _ _ _ MC12).
                         apply (match_memwd23 _ _ _ _ _ _ MC23).
            (*match_validblocks*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
                         destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                         destruct (match_validblocks23 _ _ _ _ _ _ MC23 _ _ _ H0). 
                         split; trivial. 
                         eapply (match_validblocks12 _ _ _ _ _ MC12); try eassumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12
                         core_ord_wf23 core_ord_wf12.
                 intros. rename st2 into st3. rename m2 into m3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [X [? ?]]]]; subst.
                 eapply (diagram_extinj _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 
                     match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); try eassumption.
                       intros. eapply (match_validblocks12 _ _ _ _ _ H2). apply H3.
            (*initial_core*)
                  intros. rename v2 into v3. rename vals2 into vals3. rename m2 into m3.
                  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). eapply forall_valinject_hastype; eassumption.
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ ( forall_lessdef_refl _) HT (Mem.extends_refl m1) H2 H2)
                      as [d12 [c11 [c2 [Ini1 [Ini2 MC12]]]]]. rewrite Ini1 in H0. inv H0.
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2 H3 H4 H5) as [d23 [c3 [Ini3 MC23]]].
                  exists (d12,Some c2, d23). exists c3. 
                  split; trivial. exists c2. exists m1. split; trivial. split; trivial.
             (*safely_halted*)
                    intros. rename c2 into c3. rename m2 into m3.
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    apply (core_halted12 _ _ _ _ _ _ MC12) in H0; try assumption. 
                    destruct H0 as [v2 [LD12 [SH2 [Ext12 VV2]]]].
                    apply (core_halted23 _ _ _ _ _ _ _ MC23) in SH2; try assumption. 
                    destruct SH2 as [v3 [InjV23 [SH3 [InjM23 VV3]]]].
                    exists v3. split. eapply val_lessdef_inject_compose; eassumption.
                          split. trivial. 
                          split; trivial. 
                          eapply extends_inject_compose; eassumption.
             (*atexternal*)
                    intros. rename st2 into st3. rename m2 into m3.
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0; try assumption. 
                    destruct H0 as [vals2 [Ext12 [LD12 [HTVals2 [AtExt2 VV2]]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2; try assumption. 
                    destruct AtExt2 as [Inj23 [PG2 [vals3 [InjVals23 [HTVals3 [AtExt3 VV3]]]]]]. 
                    assert (PG1: meminj_preserves_globals G1 j). admit. (*have meminj_preserves_globals G2 j*) 
                    split. eapply extends_inject_compose; eassumption.
                    split. assumption.
                    exists vals3. 
                    split. eapply forall_val_lessdef_inject_compose; eassumption. 
                    split. assumption.
                    split; assumption.
             (*after_external*) 
                    clear core_diagram12 core_diagram23 core_initial12 core_initial23
                          core_halted12 core_halted23.
                    intros. rename st2 into st3. rename m2 into m3. rename ret2 into ret3. rename m2' into m3'. 
                    destruct cd as [[d12 cc2] d23]. destruct H0 as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 H1)  as 
                       [vals2 [Ext12 [LDVals12 [HTVals2 [AtExt2 VV2]]]]]; try assumption; clear core_at_external12.
                    destruct (core_at_external23 _ _ _ _ _ _ _ _ _  MC23 AtExt2)  as 
                       [Inj23 [PG2 [vals3 [InjVals23 [HTVals3 [AtExt3 VV3]]]]]]; try assumption; clear core_at_external23.
                    assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). 
                        eapply forall_lessdef_hastype; eassumption.
                    assert (HRet1:   Val.has_type ret1 (proj_sig_res ef_sig)). 
                        eapply valinject_hastype; eassumption.
                    assert (UnchOn3 :  my_mem_unchanged_on (loc_out_of_reach j m2) m3 m3').
                        split; intros; eapply H11; trivial.
                                 eapply extends_loc_out_of_reach; eassumption.
                                 intros. apply H0 in H18. eapply extends_loc_out_of_reach; eassumption.
                    assert (Sep23: inject_separated j j' m2 m3).
                         intros b. intros. destruct (H5 _ _ _ H0 H17). split; trivial. 
                         intros N. apply H18.  inv Ext12. unfold Mem.valid_block. rewrite mext_next. apply N.
                    assert (WD2: mem_wd m2). eapply match_memwd12. apply MC12. 
                    destruct (MEMAX.interpolate_EI _ _ _ Ext12 H8 _ _ Inj23 _ H10 _ H6 H11 H4 H5 H9 H13 WD2 H14)
                       as [m2' [Fwd2' [Ext12' [Inj23' [UnchOn2 [UnchOn2j WD22']]]]]].
                    assert (WD2': mem_wd m2'). apply WD22'. apply WD2. 
                    assert (ValV2': val_valid ret1 m2'). eapply (extends_valvalid _ _ Ext12'). apply H15. 
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ ret1 ret1 _ _ _ MC12 H1 H2 AtExt2 
                              LDVals12 HTVals2 H8 Fwd2' UnchOn2 (Val.lessdef_refl _) Ext12' HRet1) 
                         as [c1' [c2' [d12' [AftExt1 [AftExt2 MC12']]]]]; try assumption; clear core_after_external12.
                    destruct (core_after_external23 _ j j' _ _ _ _ vals2 ret1 _ _ _ ret3 _ Inj23 
                              MC23 AtExt2 VV2 PG2 H4 Sep23 Inj23' H7 Fwd2' UnchOn2j H10 UnchOn3 H12)
                         as [d23' [cc2' [c3' [AftExt22 [AftExt3 MC23']]]]]; try assumption; clear core_after_external23.
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',Some c2', d23'). exists c1'. exists c3'. split; trivial. split; trivial.
                    exists c2'. exists m2'. split; trivial. split; trivial.
Qed.

Lemma CaseExt: forall
              (SIM23 : sim F2 C2 V2 F3 C3 V3 Sem2 Sem3 G2 G3 entrypoints23),
              sim F1 C1 V1 F3 C3 V3 Sem1 Sem3 G1 G3 entrypoints13.
Proof. intros.
induction SIM23; intros; subst.
 (*equality pass Sem2 -> Sem3*)  
       apply simext. apply (exteq R). 
 (*extension pass Sem2 -> Sem3*) 
       apply simext. apply (extext R). 
 (*injection pass Sem2 -> Sem3*) 
       apply siminj. apply (extinj R). 
Qed.
End MINISIM_TRANS_EXT.

Section MINISIM_TRANS_INJ.
Context  (F1 C1 V1 F2 C2 V2 F3 C3 V3:Type)
               (Sem1 : RelyGuaranteeSemantics (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
               (Sem2 : RelyGuaranteeSemantics (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
               (Sem3 : RelyGuaranteeSemantics (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
               (entrypoints12 : list (val * val * signature))
               (entrypoints23 : list (val * val * signature))
               (entrypoints13 : list (val * val * signature))
               (EPC : entrypoints_compose entrypoints12  entrypoints23 entrypoints13)
               (G1 : Genv.t F1 V1) (G2 : Genv.t F2 V2) (G3 : Genv.t F3 V3)
               (SimInj12 : Coop_forward_simulation_inj.Forward_simulation_inject
                          (list (ident * globdef F1 V1)) (list (ident * globdef F2 V2))
                         Sem1 Sem2 G1 G2 entrypoints12).

Lemma injeq: 
    forall (SimEq23 : Forward_simulation_eq.Forward_simulation_equals mem
                   (list (ident * globdef F2 V2)) (list (ident * globdef F3 V3)) Sem2 Sem3
                   G2 G3 entrypoints23),
    Coop_forward_simulation_inj.Forward_simulation_inject
               (list (ident * globdef F1 V1)) (list (ident * globdef F3 V3))
               Sem1 Sem3 G1 G3 entrypoints13. 
Proof. intros.
  destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12 match_memwd12 match_vb12
            core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
   destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
    eapply Coop_forward_simulation_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, X=Some c2 /\
                                                  match_core12 d1 j c1 m1 c2 m3 /\ match_core23 d2 c2 c3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*match_wd*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
                         destruct H as [c2 [X [MC12 MC23]]]; subst.
                         apply (match_memwd12 _ _ _ _ _ _ MC12).
            (*match_validblocks*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
                         destruct H as [c2 [X [MC12 MC23]]]; subst.
                         eapply (match_vb12 _ _ _ _ _ _ MC12); try eassumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12
                         core_ord_wf23 core_ord_wf12.
                 intros. rename st2 into st3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [X [? ?]]]; subst.
                 eapply (diagram_injeq _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); try eassumption.
             (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 H1 H2 H3 H4 H5) as [d12 [c2 [Ini2 MC12]]].
                  destruct (core_initial23 _ _ _ EP23 _ H5) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2,d23). exists c3. split; trivial.
                  exists c2. split; trivial. split; trivial.
             (*safely_halted*)
                    intros. rename c2 into c3.
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                    apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0; try assumption. 
                    destruct H0 as [v2 [VInj12 [SH2 [MInj12 VV2]]]].
                    apply (core_halted23 _ _ _ _ MC23) in SH2; try assumption.
                    exists v2. split; trivial. split; trivial. split; trivial.
             (*atexternal*)
                    intros. rename st2 into st3.
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0; try assumption. 
                    destruct H0 as [Minj12 [PG1j [vals2 [VInj12 [HT2 [AtExt2 VV2]]]]]].
                    destruct (core_at_external23 _ _ _ _ _ _ MC23 AtExt2); try assumption.
                    split; trivial.
                    split; trivial.
                    exists vals2. split; trivial. split; trivial. split; trivial.
             (*after_external*)
                    intros. rename st2 into st3.
                    destruct cd as [[d12 cc2] d23]. destruct H0 as [c2 [X [MC12 MC23]]]; subst.
                    destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 H1) as 
                       [MInj12 [PG1j [vals2 [VInj12 [HT2 [AtExt2 VV2]]]]]]; try assumption.
                    destruct (core_at_external23 _ _ _ _ _ _ MC23 AtExt2) as [AtExt3 HTargs2]; try assumption. 
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ MInj12 MC12 H1 
                               H2 PG1j H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16)
                             as [d12' [c1' [c2' [AftExt1 [AftExt2 MS12']]]]].
                    destruct (core_after_external23 _ _ _ _ _ _ _ MC23 AtExt2 AtExt3 HT2 H12) 
                        as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',Some c2',d23'). exists c1'. exists c3'.
                    split; trivial. split; trivial.
                    exists c2'. split; trivial. split; trivial.
Qed.

Lemma injext:
   forall (SimExt23 : Coop_forward_simulation_ext.Forward_simulation_extends
                            (list (ident * globdef F2 V2)) (list (ident * globdef F3 V3))
                           Sem2 Sem3 G2 G3 entrypoints23),
   Coop_forward_simulation_inj.Forward_simulation_inject
                             (list (ident * globdef F1 V1))  (list (ident * globdef F3 V3))
                            Sem1 Sem3 G1 G3 entrypoints13.
Proof. intros.
    destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12 match_memwd12 match_vb12
            core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
    destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23 match_memwd23 match_vb23
            core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
    eapply Coop_forward_simulation_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, exists m2, X = Some c2 /\
                                              match_core12 d1 j c1 m1 c2 m2 /\ match_core23 d2 c2 m2 c3 m3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*match_wd*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
                         destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                         split. apply (match_memwd12 _ _ _ _ _ _ MC12). 
                             apply (match_memwd23 _ _ _ _ _ MC23).
            (*match_validblocks*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
                         destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                         destruct (match_vb12 _ _ _ _ _ _ MC12 _ _ _ H0).
                         split; try eassumption.
                         eapply (match_vb23 _ _ _ _ _ MC23); try eassumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12
                          core_ord_wf23 core_ord_wf12.
                 intros. rename st2 into st3. rename m2 into m3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [X [? ?]]]]; subst.
                 eapply (diagram_injext _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); try eassumption.
           (*initial_core*)
                  intros. rename m2 into m3. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 H1 H2 H3 H4 H5) as [d12 [c2 [Ini2 MC12]]].
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ (forall_lessdef_refl _) H5 (extends_refl m3) H3 H3) 
                         as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2,d23). exists c3. split; trivial.
                  exists c2. exists m3. split; trivial. split; assumption.
           (*safely_halted*)
                    intros. rename c2 into c3. rename m2 into m3.
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0; try assumption. 
                    destruct H0 as [v2 [V12 [SH2 [MInj12 VV2]]]].
                    apply (core_halted23 _ _ _ _ _ _ MC23) in SH2; try assumption. 
                    destruct SH2 as [v3 [V23 [SH3 [Ext23 VV3]]]].
                    exists v3. split. eapply valinject_lessdef; eassumption. 
                       split; trivial. 
                       split. eapply inject_extends_compose; eassumption.
                       assumption.
             (*atexternal*)
                    intros. rename st2 into st3. rename m2 into m3. 
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0; try assumption.
                    destruct H0 as [Minj12 [PG1j [vals2 [VInj12 [HT2 [AtExt2 VV2]]]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in AtExt2; try assumption. 
                    destruct AtExt2 as [vals3 [Mext23 [LD23 [HT3 [AtExt3 VV3]]]]].
                    split. eapply inject_extends_compose; eassumption.
                    split; trivial. 
                    exists vals3.  split. eapply forall_valinject_lessdef; eassumption.
                        split. assumption.
                        split; assumption.
             (*after_external*)
                    clear core_diagram12 core_diagram23 core_initial12 core_initial23
                          core_halted12 core_halted23.
                    intros. rename st2 into st3. rename m2 into m3. rename m2' into m3'. rename ret2 into ret3. 
                    destruct cd as [[d12 cc2] d23]. destruct H0 as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 H1) 
                         as [Minj12 [PG1j [vals2 [ValsLD12 [HTVals2 [AtExt2 VV2]]]]]]; try assumption; clear core_at_external12.
                    destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)
                         as [vals3 [MExt23 [ValsLD23 [HTVals3 [AtExt3 VV3]]]]]; try assumption; clear core_at_external23.
                    assert (Sep12: inject_separated j j' m1 m2).
                         intros b; intros. destruct (H5 _ _ _ H0 H17). split; trivial.
                            intros N. apply H19. inv MExt23. unfold Mem.valid_block. rewrite <- mext_next. apply N.
                    assert (UnchLOOB23_3': my_mem_unchanged_on (loc_out_of_bounds m2) m3 m3'). 
                         eapply inject_LOOR_LOOB; eassumption.
                    assert (WD2: mem_wd m2). apply match_memwd23 in MC23. apply MC23. 
                    destruct (MEMAX.interpolate_IE _ _ _ _ Minj12 H8 _ H4 Sep12 H9 _ _ MExt23 H10 H11 H6 UnchLOOB23_3' WD2 H13 H14)
                          as [m2' [Fwd2' [MExt23' [Minj12' [UnchLOORj1_2 WD22']]]]].
                    assert (mem_wd m2'). apply WD22'. apply WD2. 
                    assert (val_valid ret3 m2'). eapply (extends_valvalid _ _ MExt23'). apply H16.
                    destruct (core_after_external12 _ j j' _ _ _ _ _ ret1 m1' _ m2' ret3 _ Minj12 MC12 H1 H2 PG1j H4 
                                         Sep12 Minj12' H7 H8 H9 Fwd2' UnchLOORj1_2 H12 H13 H0 H15 H17)
                            as  [d12' [c1' [c2' [AftExt1 [AftExt2 MC12']]]]]; clear core_after_external12.
                    destruct (core_after_external23 _ _ _ _ _ _ _ _ ret3 ret3 _ _ _ MC23 AtExt2 VV2 AtExt3 ValsLD23
                                    HTVals3 Fwd2'  H10 UnchLOOB23_3' (Val.lessdef_refl _) MExt23' H12 H0 H14 H17 H16)
                            as [cc2' [c3' [d23' [AftExt22 [AftExt3 MC23']]]]]; clear core_after_external23.
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',Some c2', d23'). exists c1'. exists c3'. split; trivial. split; trivial.
                    exists c2'. exists m2'.  split; trivial. split; assumption.
Qed.

Lemma injinj:
   forall (SimInj23 : Coop_forward_simulation_inj.Forward_simulation_inject
                       (list (ident * globdef F2 V2)) (list (ident * globdef F3 V3))
                       Sem2 Sem3 G2 G3 entrypoints23), 
   Coop_forward_simulation_inj.Forward_simulation_inject 
              (list (ident * globdef F1 V1)) (list (ident * globdef F3 V3))
              Sem1 Sem3 G1 G3 entrypoints13.
Proof. intros.
  destruct SimInj12 
    as [core_data12 match_core12 core_ord12 core_ord_wf12 match_memwd12 
      match_validblock12 core_diagram12 
      core_initial12 core_halted12 core_at_external12 core_after_external12].  
  destruct SimInj23 
    as [core_data23 match_core23 core_ord23 core_ord_wf23  match_memwd23 
      match_validblock23 core_diagram23 
      core_initial23 core_halted23 core_at_external23 core_after_external23].
  eapply Coop_forward_simulation_inj.Build_Forward_simulation_inject with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d j c1 m1 c3 m3 => 
      match d with (d1,X,d2) => 
        exists c2, exists m2, exists j1, exists j2, 
          X=Some c2 /\ j = compose_meminj j1 j2 /\
          match_core12 d1 j1 c1 m1 c2 m2 /\ match_core23 d2 j2 c2 m2 c3 m3 
      end).
 (*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
 (*match_wd*) intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
  destruct H as [c2 [m2 [j12 [j23 [X [J [MC12 MC23]]]]]]]; subst.
  split. apply (match_memwd12 _ _ _ _ _ _ MC12).
  apply (match_memwd23 _ _ _ _ _ _ MC23).
 (*match_validblocks*) 
  intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23]. 
  destruct H as [c2 [m2 [j12 [j23 [X [J [MC12 MC23]]]]]]]; subst.
  apply compose_meminjD_Some in H0. 
  destruct H0 as [b11 [ofs11 [ofs12 [Hb [Hb1 Hdelta]]]]]. 
  split. eapply (match_validblock12 _ _ _ _ _ _ MC12); try eassumption.
  eapply (match_validblock23 _ _ _ _ _ _ MC23); try eassumption.
 (*core_diagram*)
  clear core_initial23  core_halted23 core_at_external23 core_after_external23 
    core_initial12  core_halted12 core_at_external12 core_after_external12
    core_ord_wf23 core_ord_wf12.
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [j12 [j23 [X [? [MC12 MC23]]]]]]]; subst.
  eapply (diagram_injinj _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ 
    core_diagram12 _ _ _ _ core_diagram23 
    match_validblock12 match_validblock23); try eassumption.
 (*initial_core*)
  clear core_diagram23  core_halted23 core_at_external23 core_after_external23 
    core_diagram12  core_halted12 core_at_external12 core_after_external12.
  intros. rename m2 into m3. rename v2 into v3. rename vals2 into vals3. 
  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). 
  eapply forall_valinject_hastype; eassumption.
  destruct (mem_wd_inject_splitL _ _ _ H1 H2) as [Flat1 XX]; rewrite XX.
  assert (ValInjFlat1 := forall_val_inject_flat _ _ _ H1 _ _ H4).
  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 Flat1 H2 H2 ValInjFlat1 HT) 
    as [d12 [c2 [Ini2 MC12]]].
  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2 H3 H4 H5) 
    as [d23 [c3 [Ini3 MC23]]].
  exists (d12,Some c2,d23). exists c3. 
  split; trivial. 
  exists c2. exists m1. exists  (Mem.flat_inj (Mem.nextblock m1)). exists j. 
  split; trivial. split; trivial. split; assumption.
 (*safely_halted*)
  intros. rename c2 into c3. rename m2 into m3.  
  destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [j12 [j23 [X [Y [MC12 MC23]]]]]]]; subst. 
  apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0; try assumption. 
  destruct H0 as [v2 [ValsInj12 [SH2 [Minj12 VV2]]]].
  apply (core_halted23 _ _ _ _ _ _ _ MC23) in SH2; try assumption. 
  destruct SH2 as [v3 [ValsInj23 [SH3 [MInj23 VV3]]]].
  exists v3. split. apply (val_inject_compose _ _ _ _ _ ValsInj12 ValsInj23).
  split. trivial. 
  split. eapply Mem.inject_compose; eassumption.
  assumption.
(*atexternal*)
  intros. rename st2 into st3. rename m2 into m3. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H as [st2 [m2 [j1 [j2 [Y [J [MC12 MC23]]]]]]]. subst.
  apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0; try assumption. 
  destruct H0 as [MInj12 [PGj1 [vals2 [ValsInj12 [HTVals2 [AtExt2 VV2]]]]]].
  apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2; try assumption. 
  destruct AtExt2 as [MInj23 [PGj2 [vals3 [ValsInj23 [HTVals3 [AtExt3 VV3]]]]]].
  split. eapply Mem.inject_compose; eassumption.
  split.
  admit. (*TODO: need to prove meminj_preserves_globals G1
            (compose_meminj j1 j2) 
            from meminj_preserves_globals G1 j1
            and meminj_preserves_globals G2 j2*)
  exists vals3. 
  split.  eapply forall_val_inject_compose; eassumption.
  split; try assumption.
  split; try assumption.
 (*after_external*) clear core_diagram12 core_initial12 core_halted12 
  core_diagram23 core_initial23 core_halted23. 
  intros. rename st2 into st3. rename m2 into m3. rename ret2 into ret3. rename m2' into m3'. 
  destruct cd as [[d12 cc2] d23]. 
  destruct H0 as [st2 [m2 [j1 [j2 [Y [J [MC12 MC23]]]]]]]. subst.
  rename H1 into AtExt1. rename H2 into VV1.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExt1 VV1) 
   as [MInj12 [PGj1 [vals2 [ValsInj12 [HTVals2 [AtExt2 VV2]]]]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2 VV2) 
   as [MInj23 [PGj2 [vals3 [ValsInj23 [HTVals3 [AtExt3 V3V]]]]]].
  clear core_at_external12 core_at_external23.
  assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). 
  eapply forall_valinject_hastype; eassumption.
  assert (HRet1: Val.has_type ret1 (proj_sig_res ef_sig)). 
  eapply valinject_hastype; eassumption.
  assert (mem_wd m1 /\ mem_wd m2). apply (match_memwd12 _ _ _ _ _ _ MC12). destruct H0 as [WD1 WD2].
  assert (WD3: mem_wd m3). apply (match_memwd23 _ _ _ _ _ _ MC23).
  destruct (MEMAX.interpolate_II _ _ _ MInj12 _ H8 _ _ MInj23 _ H10 _ H6 H4 H5 H9 H11 WD1 H13 WD2 WD3 H14)
    as [m2' [j12' [j23' [X [Incr12 [Incr23 [MInj12' [Fwd2 
      [MInj23' [Unch22 [Sep12 [Sep23 [Unch222' [Unch2233' WD22']]]]]]]]]]]]]]. 
  subst.
  assert (WD2': mem_wd m2'). apply WD22'. apply WD2. 
  assert (exists ret2, val_inject j12' ret1 ret2 /\ val_inject j23' ret2 ret3 /\
    Val.has_type ret2 (proj_sig_res ef_sig) /\ val_valid ret2 m2'). 
  apply val_inject_split in H7. destruct H7 as [ret2 [injRet12 injRet23]]. 
  exists ret2. split; trivial. split; trivial. 
  split. eapply valinject_hastype; eassumption.
  eapply inject_valvalid; eassumption. 
  destruct H0 as [ret2 [injRet12 [injRet23 [HasTp2 ValV2]]]].
  assert (Unch111': my_mem_unchanged_on (loc_unmapped j1) m1 m1').
  split; intros; apply H9; unfold compose_meminj, loc_unmapped in *. 
  rewrite H0. trivial. trivial. 
  intros. specialize (H0 _ H2). rewrite H0. trivial. trivial.
  specialize (core_after_external12 _ _ j12' _ _ _ _ _ ret1 m1' m2 m2' ret2 _ MInj12 MC12 AtExt1
    VV1 PGj1 Incr12 Sep12 MInj12' injRet12 H8 Unch111' Fwd2 Unch22 HasTp2 H13 WD2' H15 ValV2).
  destruct core_after_external12 as [d12' [c1' [c2' [AftExt1 [AftExt2 MC12']]]]].

  specialize (core_after_external23 _ _ j23' _ _ _ _ vals2 ret2 m2' _ m3' ret3 _ MInj23 MC23 
    AtExt2 VV2 PGj2 Incr23 Sep23 MInj23' injRet23 Fwd2 Unch222' H10 Unch2233' H12 WD2'
    H14 ValV2 H16).
  destruct core_after_external23 as [d23' [cc2' [c3' [AftExt22 [AftExt3 MC23']]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists (d12', Some c2', d23'). exists c1'. exists c3'.
  split. assumption.
  split. assumption.
  exists c2'. exists m2'. exists j12'. exists j23'. auto.
Qed.

Lemma CaseInj: forall
              (SIM23 : sim F2 C2 V2 F3 C3 V3 Sem2 Sem3 G2 G3 entrypoints23),
              sim F1 C1 V1 F3 C3 V3 Sem1 Sem3 G1 G3 entrypoints13.
Proof. intros.
induction SIM23; intros; subst.
 (*equality pass Sem2 -> Sem3*)  
       apply siminj. apply (injeq R). 
 (*extension pass Sem2 -> Sem3*) 
       apply siminj. apply (injext R). 
 (*injection pass Sem2 -> Sem3*) 
       apply siminj. apply (injinj R). 
Qed.
End MINISIM_TRANS_INJ.

Section MINISIM_TRANS.
Context  (F1 C1 V1 F2 C2 V2 F3 C3 V3:Type)
               (Sem1 : RelyGuaranteeSemantics (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
               (Sem2 : RelyGuaranteeSemantics (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
               (Sem3 : RelyGuaranteeSemantics (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
               (entrypoints12 : list (val * val * signature))
               (entrypoints23 : list (val * val * signature))
               (entrypoints13 : list (val * val * signature))
               (EPC : entrypoints_compose entrypoints12  entrypoints23 entrypoints13)
               (G1 : Genv.t F1 V1) (G2 : Genv.t F2 V2) (G3 : Genv.t F3 V3).

Lemma sim_trans: forall 
        (SIM12: sim F1 C1 V1 F2 C2 V2 Sem1 Sem2 G1 G2 entrypoints12)
        (SIM23: sim  F2 C2 V2 F3 C3 V3 Sem2 Sem3 G2 G3 entrypoints23),
        sim  F1 C1 V1 F3 C3 V3 Sem1 Sem3 G1 G3 entrypoints13.
Proof. intros.
  induction SIM12.
    eapply CaseEq; try eassumption.
    eapply CaseExt; try eassumption.
    eapply CaseInj; try eassumption.
Qed.
End MINISIM_TRANS.
*)