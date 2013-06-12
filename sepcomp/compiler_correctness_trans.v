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

Require Import Wellfounded.
Require Import Relations.

Declare Module MEMAX : MemoryInterpolationAxioms.

Lemma corestepN_fwd: forall {G C D} (Sem: CoopCoreSem G C D)
  g N c m c' m' (CS:corestepN Sem g N c m c' m'), 
  mem_forward m m'.
Proof. 
  intros G C D Sem g N.
  induction N; simpl; intros.
  inv CS. apply mem_forward_refl. 
  destruct CS as [c2 [m2 [CS1 CS2]]].
  apply corestep_fwd in CS1. apply IHN in CS2. 
  eapply mem_forward_trans; eassumption.
Qed. 

Lemma corestep_star_fwd: forall {G C D} (Sem: CoopCoreSem G C D)
  g c m c' m' (CS:corestep_star Sem g c m c' m'), 
  mem_forward m m'.
Proof. intros. destruct CS.  eapply  corestepN_fwd. apply H. Qed.

Lemma corestep_plus_fwd: forall {G C D} (Sem: CoopCoreSem G C D)
  g c m c' m' (CS:corestep_plus Sem g c m c' m'), 
  mem_forward m m'.
Proof. intros. destruct CS.  eapply  corestepN_fwd. apply H. Qed.

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
  spec H1. auto. 
  apply H1. 
Qed.

Section EXTEXT.
Lemma  diagram_extext: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoreSemantics G2 C2 mem D2)
(Sem3 : CoreSemantics G3 C3 mem D3)
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(Genv2 : G2)
(Genv1 : G1)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 Genv1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (m2 : mem),
                 match_core12 cd st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       match_core12 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem2 Genv2 st2 m2 st2'
                          m2' \/
                        corestep_star Sem2 Genv2 st2 m2 st2'
                          m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(Genv3 : G3)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 Genv2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (m2 : mem),
                 match_core23 cd st1 m1 st2 m2 ->
                 exists st2' : C3,
                   exists m2' : mem,
                     exists cd' : core_data23,
                       match_core23 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem3 Genv3 st2 m2 st2'
                          m2' \/
                        corestep_star Sem3 Genv3 st2 m2 st2'
                          m2' /\ core_ord23 cd' cd))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 Genv1 st1 m1 st1' m1')
(d12 : core_data12)
(d23 : core_data23)
(st3 : C3)
(m3 : mem)
(st2 : C2)
(m2 : mem)
(MC12 : match_core12 d12 st1 m1 st2 m2)
(MC23 : match_core23 d23 st2 m2 st3 m3),
exists st3' : C3,
  exists m3' : mem,
    exists cd' : core_data12 * option C2 * core_data23,
      (let (y, d2) := cd' in
       let (d1, X) := y in
       exists c2 : C2,
         exists m2 : mem,
           X = Some c2 /\
           match_core12 d1 st1' m1' c2 m2 /\ match_core23 d2 c2 m2 st3' m3') /\
      (corestep_plus Sem3 Genv3 st3 m3 st3' m3' \/
       corestep_star Sem3 Genv3 st3 m3 st3' m3' /\
       clos_trans (core_data12 * option C2 * core_data23)
         (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
         (d12, Some st2, d23)).
Proof. 
  intros.
  destruct (core_diagram12 _ _ _ _ CS1 _ _ _ MC12) 
           as [st2' [m2' [d12' [MC12' Y]]]]. 
  clear core_diagram12.
  assert (ZZ: corestep_plus Sem2 Genv2 st2 m2 st2' m2' \/  
               (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
    destruct Y. auto.
    destruct H.
    destruct H. destruct x.
    right. split; auto.
       left. exists x; auto.
    clear Y. destruct ZZ as [CS2 | CS2 ord12'].
    (*case1*) 
    destruct CS2.
    clear MC12 CS1.
    revert d23 st2 st2' m2' m2 st3 m3 MC23 MC12' H.
    induction x; intros. 
    (*base case*) simpl in H.
      destruct H as [c2 [m2'' [? ?]]].
      inv H0.
      destruct (core_diagram23 _ _ _ _ H _ _ _ MC23)
           as [st3' [m3' [d23' [? ?]]]].
      exists st3'. exists m3'. exists (d12',Some st2',d23').
      split. exists st2'. exists m2'. split. trivial. split; assumption. 
      destruct H1. left; assumption.
      destruct H1. right. split; trivial.
      apply t_step. constructor 2. apply H2.
    (*inductive case*)
      remember (S x) as x'. simpl in H.
      destruct H as [st2'' [m2'' [? ?]]]. subst x'.
      destruct (core_diagram23 _ _ _ _  H _ _ _ MC23)
           as [c3' [m3' [d'' [? ?]]]].
      specialize (IHx _ _ _ _ _ _ _ H1 MC12' H0).
      destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']  
        [[c2'' [m2'''' [X [MC12'' MC23'']]]] ?]]]]; subst.
      exists c3''. exists m3''. exists (d12''', Some c2'',d23'').
      split. exists c2''. exists m2''''. auto.
      destruct H2; destruct H3.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
              eapply t_trans; eauto.
          (*4/4*)
              apply t_step.
              constructor 2. apply H4.
  (*case 2*)
    destruct CS2. inv H.
    exists st3. exists m3. exists (d12',Some st2',d23).
    split. exists st2'. exists m2'. split. trivial. split; assumption.
    right. split. exists O. simpl; auto.
    apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3:Type}
  (I : forall F C V : Type, 
        CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> 
        AST.program F V -> Prop)
  (Sem1 : CoopCoreSem (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
  (Sem2 : CoopCoreSem (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
  (Sem3 : CoopCoreSem (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
  ExternIdents epts12  epts23 entrypoints13
  (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3) 
  (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
  (e12 : prog_main P1 = prog_main P2)
  (g12: CompilerCorrectness.GenvHyp P1 P2)       
  (EPC: entrypoints_compose epts12 epts23 entrypoints13)
  (EXT1: In (prog_main P1, CompilerCorrectness.extern_func main_sig)
              ExternIdents)
  (EXT2: In (prog_main P2, CompilerCorrectness.extern_func main_sig)
            ExternIdents)
  (i1: I F1 C1 V1 Sem1 P1)
  (Ext_init12: forall m1, Genv.init_mem P1 = Some m1 -> 
               exists m2, Genv.init_mem P2 = Some m2 /\ Mem.extends m1 m2)
(*  (Ext_init12 : forall m1 : mem,
             initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
             exists m2 : mem,
               initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
               Mem.extends m1 m2)*)
  (SimExt12 : Coop_forward_simulation_ext.Forward_simulation_extends
               (list (ident * globdef F1 V1))
               (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
               (Genv.globalenv P2) epts12)
  (SimExt23 : Coop_forward_simulation_ext.Forward_simulation_extends
             (list (ident * globdef F2 V2))
             (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
             (Genv.globalenv P3) epts23).

Lemma extext: Coop_forward_simulation_ext.Forward_simulation_extends
  (list (ident * globdef F1 V1))
  (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
  (Genv.globalenv P3) entrypoints13. 
Proof. 
  intros.
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
             i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12 
             epts23 entrypoints13 Ext_init12 SimExt12 SimExt23.
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
  assert (UnchOn3 :  Mem.unchanged_on (loc_out_of_bounds m2) m3 m3').
  split; intros; eapply H7; trivial.
  eapply extends_loc_out_of_bounds; eassumption.
  eapply extends_loc_out_of_bounds; eassumption. 
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

End EXTEXT.

Section INJINJ.
Lemma diagram_injinj: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoopCoreSem G2 C2 D2)
(Sem3 : CoopCoreSem G3 C3 D3)
(core_data12 : Type)
(match_core12 : core_data12 -> meminj -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(Genv2 : G2)
(Genv1 : G1)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 Genv1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (j : meminj) (m2 : mem),
                 match_core12 cd j st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       exists j' : meminj,
                         inject_incr j j' /\
                         inject_separated j j' m1 m2 /\
                         match_core12 cd' j' st1' m1' st2' m2' /\
                         (corestep_plus Sem2 Genv2 st2 m2 st2' m2' \/
                          corestep_star Sem2 Genv2 st2 m2 st2' m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> meminj -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(Genv3 : G3)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                   corestep Sem2 Genv2 st1 m1 st1' m1' ->
                   forall (cd : core_data23) (st2 : C3) 
                     (j : meminj) (m2 : mem),
                   match_core23 cd j st1 m1 st2 m2 ->
                   exists st2' : C3,
                     exists m2' : mem,
                       exists cd' : core_data23,
                         exists j' : meminj,
                           inject_incr j j' /\
                           inject_separated j j' m1 m2 /\
                           match_core23 cd' j' st1' m1' st2' m2' /\
                           (corestep_plus Sem3 Genv3 st2 m2
                              st2' m2' \/
                            corestep_star Sem3 Genv3 st2 m2
                              st2' m2' /\ core_ord23 cd' cd))
 (MatchHyp12: forall d12 j12 c1 m1 c2 m2,  match_core12 d12 j12 c1 m1 c2 m2 ->  
                    forall b1 b2 ofs, j12 b1 = Some (b2,ofs) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
 (MatchHyp23: forall d23 j23 c2 m2 c3 m3,  match_core23 d23 j23 c2 m2 c3 m3 ->  
                    forall b1 b2 ofs, j23 b1 = Some (b2,ofs) -> Mem.valid_block m2 b1 /\ Mem.valid_block m3 b2)
 (st1 : C1)
  (m1 : mem)
  (st1' : C1)
  (m1' : mem)
  (CS1 : corestep Sem1 Genv1 st1 m1 st1' m1')
  (d12 : core_data12)
  (d23 : core_data23)
  (st3 : C3)
  (m3 : mem)
  (st2 : C2)
  (m2 : mem)
  (j12 : meminj)
  (j23 : meminj)
  (MC12 : match_core12 d12 j12 st1 m1 st2 m2)
  (MC23 : match_core23 d23 j23 st2 m2 st3 m3),
   exists st3' : C3,
     exists m3' : mem,
       exists cd' : core_data12 * option C2 * core_data23,
         exists j' : meminj,
           inject_incr (compose_meminj j12 j23) j' /\
           inject_separated (compose_meminj j12 j23) j' m1 m3 /\
           (let (y, d2) := cd' in
            let (d1, X) := y in
            exists st2' : C2,
              exists m2' : mem,
                exists j12' : meminj,
                  exists j23' : meminj,
                    X = Some st2' /\
                    j' = compose_meminj j12' j23' /\
                    match_core12 d1 j12' st1' m1' st2' m2' /\
                    match_core23 d2 j23' st2' m2' st3' m3') /\
           (corestep_plus Sem3 Genv3 st3 m3 st3' m3' \/
            corestep_star Sem3 Genv3 st3 m3 st3' m3' /\
            clos_trans (core_data12 * option C2 * core_data23)
              (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
              (d12, Some st2, d23)).
Proof. 
  intros. 
  destruct (core_diagram12 _ _ _ _ CS1 _ _ _ _ MC12)
    as [st2' [m2' [d12' [j12' [InjIncr12 [InjSep12 [MC12' Y]]]]]]]; clear core_diagram12.
  assert (ZZ: corestep_plus Sem2 Genv2 st2 m2 st2' m2' \/
    (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
  destruct Y. auto.
  destruct H.
  destruct H. destruct x.
  right. split; auto.
  left. exists x; auto.
  clear Y. destruct ZZ as [CS2 | [CS2 ord12']].
 (*case1*) 
  destruct CS2.
  clear CS1. 
  cut (exists st3' : C3,  exists m3' : mem, exists d23':core_data23, exists j23' : meminj, 
    inject_incr j23 j23' /\ inject_separated j23 j23' m2 m3 /\
    match_core23 d23' j23' st2' m2' st3' m3' /\
    (corestep_plus Sem3 Genv3 st3 m3 st3' m3' \/
      (corestep_star Sem3 Genv3 st3 m3 st3' m3' /\
        clos_trans (core_data12 * option C2 * core_data23)
        (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) (d12', Some st2', d23')
        (d12, Some st2, d23)))).
  intros XX; destruct XX as [st3' [m3' [d23' [j23' [InjIncr23 [InjSep23 [MC23' ZZ]]]]]]].
  exists st3'. exists m3'. exists (d12', Some st2', d23'). exists (compose_meminj j12' j23').
  split. eapply compose_meminj_inject_incr. apply InjIncr12. apply InjIncr23. 
  split. eapply compose_meminj_inject_separated. apply InjSep12. apply InjSep23. 
  assumption. assumption.
    eapply (MatchHyp12 _ _ _ _ _ _ MC12).
    eapply (MatchHyp23 _ _ _ _ _ _ MC23).
    split. exists st2'. exists m2'. exists j12'. exists j23'. auto.
    apply ZZ.
  clear MC12 InjIncr12 InjSep12 MC12' MatchHyp12. 
  clear st1 m1 st1' m1' j12 j12'. 
  clear G1 C1 D1 Sem1 match_core12 Genv1.
  revert j23 d23 st2 m2 st3 m3 H MC23. 
  induction x; intros. 
   (*base case*) simpl in H.
    destruct H as [c2 [m2'' [? ?]]].
    inv H0.
    destruct (core_diagram23 _ _ _ _ H _ _ _ _ MC23) 
      as [st3' [m3' [d23' [j23' [InjInc23 [InjSep23 [? ?]]]]]]].
    exists st3'. exists m3'. exists d23'. exists j23'. 
    split; trivial.
    split; trivial.
    split; trivial.
    destruct H1. left; assumption.
    destruct H1. right. split; trivial.
    apply t_step. constructor 2. apply H2.
   (*inductive case*)
    remember (S x) as x'. simpl in H.
    destruct H as [st2'' [m2'' [? ?]]]. subst x'.
    destruct (core_diagram23 _ _ _ _  H _ _ _ _ MC23) 
      as [c3' [m3' [d23' [j23' [InjInc23 [InjSep23 [? ?]]]]]]]. clear core_diagram23.
    specialize (IHx j23' d23' _ _ c3' m3' H0 H1).
    destruct IHx as [c3'' [m3'' [d23'' [j23'' [InjIncr' [InjSep' [MC' XX]]]]]]].
    exists c3''. exists m3''. exists d23''. exists j23''.
    split. eapply inject_incr_trans. apply InjInc23. apply InjIncr'.
    split. clear MC' H1. intros b; intros.
    remember (j23' b).
    destruct o; apply eq_sym in Heqo. 
    destruct p. specialize (InjIncr' _ _ _ Heqo). rewrite InjIncr' in H3. inv H3.
    destruct (InjSep23 _ _ _ H1 Heqo). split; trivial.
    destruct (InjSep' _ _ _ Heqo H3).
    split; intros N.
    apply H4. apply corestep_fwd in H. apply H. apply N.
    apply H5. destruct H2 as [H2 | [H2 _]].
    apply corestep_plus_fwd in H2. apply H2. apply N.
    apply corestep_star_fwd in H2. apply H2. apply N.                      
    split. apply MC'.
    destruct H2; destruct XX.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
              eapply t_trans; eauto.
          (*4/4*)
              apply t_step.
              constructor 2. apply H4.
  (*case 2*)
   inv CS2.
   exists st3. exists m3. exists (d12',Some st2',d23). exists  (compose_meminj j12' j23). 
   split. eapply compose_meminj_inject_incr.  assumption. apply inject_incr_refl.
   split. eapply compose_meminj_inject_separated. eassumption.
   apply inject_separated_same_meminj. 
   assumption. apply inject_incr_refl.
   eapply (MatchHyp12 _ _ _ _ _ _ MC12).
   eapply (MatchHyp23 _ _ _ _ _ _ MC23).
   split. exists st2'. exists m2'. exists j12'. exists j23. auto.
   right. split. exists O. simpl; auto.
   apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
  (I :forall F C V : Type, 
    CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> 
    AST.program F V -> Prop)
  (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globdef F1 V1)))
  (Sem2 : CoopCoreSem (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
  (Sem3 : CoopCoreSem (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
  ExternIdents epts12  epts23 entrypoints13
  (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3) 
  (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
  (e12 : prog_main P1 = prog_main P2)
  (g12: CompilerCorrectness.GenvHyp P1 P2)       
  (EPC: entrypoints_compose epts12 epts23 entrypoints13)
  (EXT1: In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents)
  (EXT2: In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents)
  (i1: I F1 C1 V1 Sem1 P1)
  (SimInj12 : Coop_forward_simulation_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
    (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) epts12)
  (SimInj23 : Coop_forward_simulation_inj.Forward_simulation_inject (list (ident * globdef F2 V2))
    (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2) (Genv.globalenv P3) epts23).

Lemma injinj: Coop_forward_simulation_inj.Forward_simulation_inject 
  (list (ident * globdef F1 V1))
  (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
  (Genv.globalenv P3) entrypoints13.
Proof.
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
    i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12 
    epts23 entrypoints13 (*Inj_init12*) SimInj12 SimInj23.
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
  admit. (*TODO: need to prove meminj_preserves_globals (Genv.globalenv P1)
            (compose_meminj j1 j2)meminj_preserves_globals (Genv.globalenv P1) j1
            and meminj_preserves_globals (Genv.globalenv P2) j2*)
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
  assert (Unch111': Mem.unchanged_on (loc_unmapped j1) m1 m1').
  split; intros; apply H9; unfold compose_meminj, loc_unmapped in *. 
  rewrite H0. trivial. trivial. 
  intros. rewrite H0. trivial. trivial.
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
End INJINJ.

Section EQEQ.
Lemma diagram_eqeq: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoreSemantics G2 C2 mem D2)
(Sem3 : CoreSemantics G3 C3 mem D3)
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> C2 -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(Genv2 : G2)
(Genv1 : G1)
(core_diagram12 : forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem),
                 corestep Sem1 Genv1 st1 m st1' m' ->
                 forall (d : core_data12) (st2 : C2),
                 match_core12 d st1 st2 ->
                 exists st2' : C2,
                   exists d' : core_data12,
                     match_core12 d' st1' st2' /\
                     (corestep_plus Sem2 Genv2 st2 m st2' m' \/
                      corestep_star Sem2 Genv2 st2 m st2' m' /\
                      core_ord12 d' d))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> C3 -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(Genv3 : G3)
(core_diagram23 : forall (st1 : C2) (m : mem) (st1' : C2) (m' : mem),
                 corestep Sem2 Genv2 st1 m st1' m' ->
                 forall (d : core_data23) (st2 : C3),
                 match_core23 d st1 st2 ->
                 exists st2' : C3,
                   exists d' : core_data23,
                     match_core23 d' st1' st2' /\
                     (corestep_plus Sem3 Genv3 st2 m st2' m' \/
                      corestep_star Sem3 Genv3 st2 m st2' m' /\
                      core_ord23 d' d))
(c1 : C1)
(m1 : mem)
(c1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 Genv1 c1 m1 c1' m1')
(d12 : core_data12)
(d23 : core_data23)
(c3 : C3)
(c2 : C2)
(MC12 : match_core12 d12 c1 c2)
(MC23 : match_core23 d23 c2 c3),
exists st2' : C3,
  exists d' : core_data12 * option C2 * core_data23,
    (let (y, d2) := d' in
     let (d1, X) := y in
     exists c0 : C2,
       X = Some c0 /\ match_core12 d1 c1' c0 /\ match_core23 d2 c0 st2') /\
    (corestep_plus Sem3 Genv3 c3 m1 st2' m1' \/
     corestep_star Sem3 Genv3 c3 m1 st2' m1' /\
     clos_trans (core_data12 * option C2 * core_data23)
       (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) d'
       (d12, Some c2, d23)).
Proof. 
  intros.   
  destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' Y]]].
  assert (ZZ: corestep_plus Sem2 Genv2 c2 m1 c2' m1' \/  (c2,m1) = (c2',m1') /\ core_ord12 d12' d12).
       destruct Y. auto.
       destruct H.
       destruct H. destruct x.
       right. split; auto.
       left. exists x; auto.
     clear Y. destruct ZZ as [CS2 | CS2 ord12'].
     (*case1*)
    destruct CS2.
    clear MC12 CS1.
    revert d23 c2 m1 c2' m1' c3 MC23 MC12' H.
    induction x; intros. 
      (*base case*) simpl in H.
          destruct H as [c3' [m3' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ MC23) as [c3' [d23' [? ?]]].
          exists c3'. exists (d12',Some c2',d23').
          split. exists c2'. split. trivial. split; assumption. 
          destruct H1. left; assumption.
          destruct H1. right. split; trivial.
          apply t_step. constructor 2. apply H2.
     (*inductive case*)
           remember (S x) as x'. simpl in H.
           destruct H as [c2'' [m2'' [? ?]]]. subst x'.
           destruct (core_diagram23 c2 m1 c2'' m2'' H _ _ MC23) as [c3' [d'' [? ?]]].
           specialize (IHx _ _ _ _ _ _ H1 MC12' H0).
           destruct IHx as [c3'' [d''' [? ?]]].
           exists c3''. exists d'''.
           split; auto.
           (*inv H8. constructor. auto.
           split. auto.*)
           destruct H2; destruct H4.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H4 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H4.
               left. destruct H2 as [n1 ?]. destruct H4 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H4 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               right. destruct H2. destruct H4.
               split. destruct H2 as [n1 ?]. destruct H4 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
              eapply t_trans; eauto.
          (*4/4*)
              apply t_step.
              constructor 2. apply H5.
  (*case 2*)
    destruct CS2. inv H.
    exists c3. exists (d12',Some c2',d23).
    split. exists c2'.  split. trivial. split; assumption.
    right. split. exists O. simpl; auto.
    apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
  (I :forall F C V : Type, 
    CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> 
    AST.program F V -> Prop)
  (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globdef F1 V1)))
  (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globdef F2 V2)))
  (Sem3 : CoreSemantics (Genv.t F3 V3) C3 mem (list (ident * globdef F3 V3)))
  ExternIdents epts12  epts23 entrypoints13
  (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3) 
  (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
  (e12 : prog_main P1 = prog_main P2)
  (g12: CompilerCorrectness.GenvHyp P1 P2)       
  (EPC: entrypoints_compose epts12 epts23 entrypoints13)
  (EXT1: In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents)
  (EXT2: In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents)
  (i1: I F1 C1 V1 Sem1 P1)
  (Eq_init12 : forall m1 : mem,
    Genv.init_mem P1 = Some m1 -> Genv.init_mem P2 = Some m1)
(*  (Eq_init12 : forall m1 : mem,
    initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
    exists m2 : mem, initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\ m1 = m2)
*)
  (SimEq12 : Forward_simulation_eq.Forward_simulation_equals mem (list (ident * globdef F1 V1))
    (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
    (Genv.globalenv P2) epts12) 
  (SimEq23 : Forward_simulation_eq.Forward_simulation_equals mem (list (ident * globdef F2 V2))
    (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
    (Genv.globalenv P3) epts23).

Lemma eqeq: Forward_simulation_eq.Forward_simulation_equals mem (list (ident * globdef F1 V1))
  (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
  (Genv.globalenv P3) entrypoints13.
Proof.
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
    core_halted12 core_at_external12 core_after_external12 Eq_init12 SimEq12 SimEq23
    i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13.
  intros. destruct d as [[d12 cc2] d23]. destruct H0 as [c2 [X [? ?]]]; subst.
  eapply (diagram_eqeq _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 
    core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); eassumption. 
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

End EQEQ.

Section EQEXT.
Lemma diagram_eqext: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoreSemantics G2 C2 mem D2)
(Sem3 : CoreSemantics G3 C3 mem D3)
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> C2 -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(Genv2 : G2)
(Genv1 : G1)
(core_diagram12 : forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem),
                 corestep Sem1 Genv1 st1 m st1' m' ->
                 forall (d : core_data12) (st2 : C2),
                 match_core12 d st1 st2 ->
                 exists st2' : C2,
                   exists d' : core_data12,
                     match_core12 d' st1' st2' /\
                     (corestep_plus Sem2 Genv2 st2 m st2' m' \/
                      corestep_star Sem2 Genv2 st2 m st2' m' /\
                      core_ord12 d' d))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(Genv3 : G3)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 Genv2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (m2 : mem),
                 match_core23 cd st1 m1 st2 m2 ->
                 exists st2' : C3,
                   exists m2' : mem,
                     exists cd' : core_data23,
                       match_core23 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem3 Genv3 st2 m2 st2' m2' \/
                        corestep_star Sem3 Genv3 st2 m2 st2' m2' /\ core_ord23 cd' cd))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 Genv1 st1 m1 st1' m1')
(d12 : core_data12)
(d23 : core_data23)
(st3 : C3)
(m3 : mem)
(st2 : C2)
(MC12: match_core12 d12 st1 st2)
(MC23: match_core23 d23 st2 m1 st3 m3),
exists st2' : C3,
  exists m2' : mem,
    exists cd' : core_data12 * option C2 * core_data23,
      (let (y, d2) := cd' in
       let (d1, X) := y in
       exists c2 : C2,
         X = Some c2 /\
         match_core12 d1 st1' c2 /\ match_core23 d2 c2 m1' st2' m2') /\
      (corestep_plus Sem3 Genv3 st3 m3 st2' m2' \/
       corestep_star Sem3 Genv3 st3 m3 st2' m2' /\
       clos_trans (core_data12 * option C2 * core_data23)
         (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
         (d12, Some st2, d23)).
Proof. intros.   destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [st2' [d12' [MC12' Y]]].
    assert (ZZ: corestep_plus Sem2 Genv2 st2 m1 st2' m1' \/  (st2,m1) = (st2',m1') /\ core_ord12 d12' d12).
       destruct Y. auto.
       destruct H.
       destruct H. destruct x.
       right. split; auto.
       left. exists x; auto.
    clear Y. destruct ZZ as [CS2 | CS2 ord12'].
     (*case1*)
    destruct CS2.
    clear MC12 CS1.
    revert d23 st2 m1 st2' m1' st3 m3 MC23 MC12' H.
    induction x; intros. 
      (*base case*) simpl in H.
          destruct H as [st3' [m3' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ _ MC23) as [st3' [m3' [d23' [? ?]]]].
          exists st3'. exists m3'. exists (d12',Some st2',d23').
          split. exists st2'. split. trivial. split; assumption. 
          destruct H1. left; assumption.
          destruct H1. right. split; trivial.
          apply t_step. constructor 2. apply H2.
     (*inductive case*)
           remember (S x) as x'. simpl in H.
           destruct H as [st2'' [m2'' [? ?]]]. subst x'.
           destruct (core_diagram23 st2 m1 st2'' m2'' H _ _ _ MC23) as [c3' [m3' [d'' [? ?]]]].
           specialize (IHx _ _ _ _ _ _ _ H1 MC12' H0).
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']  [[c2'' [X [MC12'' MC23'']]] ?]]]]. subst.
           exists c3''. exists m3''. exists (d12''', Some c2'',d23'').
           split. exists c2''. auto.
           (*inv H8. constructor. auto.
           split. auto.*)
           destruct H2; destruct H3.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
              eapply t_trans; eauto.
          (*4/4*)
              apply t_step.
              constructor 2. apply H4.
  (*case 2*)
    destruct CS2. inv H.
    exists st3. exists m3. exists (d12',Some st2',d23).
    split. exists st2'.  split. trivial. split; assumption.
    right. split. exists O. simpl; auto.
    apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
       (Sem1 : CoopCoreSem (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
       (Sem2 : CoopCoreSem (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
       (Sem3 : CoopCoreSem (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
       ExternIdents epts12  epts23 entrypoints13
       (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3) 
       (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
       (e12 : prog_main P1 = prog_main P2)
       (g12: CompilerCorrectness.GenvHyp P1 P2)       
       (EPC: entrypoints_compose epts12 epts23 entrypoints13)
       (EXT1: In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (EXT2: In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (i1: I F1 C1 V1 Sem1 P1)
       (Eq_init12 : forall m1 : mem,
            Genv.init_mem P1 = Some m1 -> Genv.init_mem P2 = Some m1)
(*       (Eq_init12 : forall m1 : mem,
            initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
            exists m2 : mem, initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\ m1 = m2)
*)
       (SimEq12 : Forward_simulation_eq.Forward_simulation_equals mem (list (ident * globdef F1 V1))
                                          (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                                          (Genv.globalenv P2) epts12) 
       (SimExt23 : Coop_forward_simulation_ext.Forward_simulation_extends (list (ident * globdef F2 V2))
                            (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
                            (Genv.globalenv P3) epts23).

Lemma eqext: Coop_forward_simulation_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
                                           (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                           (Genv.globalenv P3) entrypoints13.
Proof.
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
    i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13 Eq_init12 SimEq12 SimExt23.
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

End EQEXT.

Section EQINJ.
Lemma diagram_eqinj: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoopCoreSem G2 C2 D2)
(Sem3 : CoopCoreSem G3 C3 D3)
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> C2 -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(Genv2 : G2)
(Genv1 : G1)
(core_diagram12 : forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem),
                 corestep Sem1 Genv1 st1 m st1' m' ->
                 forall (d : core_data12) (st2 : C2),
                 match_core12 d st1 st2 ->
                 exists st2' : C2,
                   exists d' : core_data12,
                     match_core12 d' st1' st2' /\
                     (corestep_plus Sem2 Genv2 st2 m st2' m' \/
                      corestep_star Sem2 Genv2 st2 m st2' m' /\
                      core_ord12 d' d))
(core_data23 : Type)
(match_core23 : core_data23 -> meminj -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(Genv3 : G3) 
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 Genv2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (j : meminj) (m2 : mem),
                 match_core23 cd j st1 m1 st2 m2 ->
                 exists st2' : C3,
                   exists m2' : mem,
                     exists cd' : core_data23,
                       exists j' : meminj,
                         inject_incr j j' /\
                         inject_separated j j' m1 m2 /\
                         match_core23 cd' j' st1' m1' st2' m2' /\
                         (corestep_plus Sem3 Genv3 st2 m2 st2'
                            m2' \/
                          corestep_star Sem3 Genv3 st2 m2 st2'
                            m2' /\ core_ord23 cd' cd))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 Genv1 st1 m1 st1' m1')
(d12 : core_data12)
(d23 : core_data23)
(st3 : C3)
(j : meminj)
(m3 : mem)
(st2 : C2)
(MC12: match_core12 d12 st1 st2)
(MC23: match_core23 d23 j st2 m1 st3 m3),
exists st2' : C3,
  exists m2' : mem,
    exists cd' : core_data12 * option C2 * core_data23,
      exists j' : meminj,
        inject_incr j j' /\
        inject_separated j j' m1 m3 /\
        (let (y, d2) := cd' in
         let (d1, X) := y in
         exists c2 : C2,
           X = Some c2 /\
           match_core12 d1 st1' c2 /\ match_core23 d2 j' c2 m1' st2' m2') /\
        (corestep_plus Sem3 Genv3 st3 m3 st2' m2' \/
         corestep_star Sem3 Genv3 st3 m3 st2' m2' /\
         clos_trans (core_data12 * option C2 * core_data23)
           (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
           (d12, Some st2, d23)).
Proof. intros.
    destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [st2' [d12' [MC12' Y]]]. clear core_diagram12.
    assert (ZZ: corestep_plus Sem2 Genv2 st2 m1 st2' m1' \/  (st2,m1) = (st2',m1') /\ core_ord12 d12' d12).
       destruct Y. auto.
       destruct H.
       destruct H. destruct x.
       right. split; auto.
       left. exists x; auto.
    clear Y. destruct ZZ as [CS2 | CS2 ord12'].
     (*case1*) rename m1 into m2. rename m1' into m2'.
    destruct CS2.
    clear MC12 CS1.
    revert j d23 st2 m2 st2' m2' st3 m3 MC23 MC12' H.
    induction x; intros. 
      (*base case*) simpl in H.
          destruct H as [st3' [m3' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ _ _ MC23) as [st3' [m3' [d23' [j' [InjInc [InjSep [? ?]]]]]]].
          exists st3'. exists m3'. exists (d12',Some st2',d23'). exists j'.
          split; trivial.
          split; trivial.
          split. exists st2'. split. trivial. split; assumption. 
          destruct H1. left; assumption.
          destruct H1. right. split; trivial.
          apply t_step. constructor 2. apply H2.
     (*inductive case*)
           remember (S x) as x'. simpl in H.
           destruct H as [st2'' [m2'' [? ?]]]. subst x'.
           destruct (core_diagram23 st2 m2 st2'' m2'' H _ _ _ _ MC23) as [c3' [m3' [d'' [j' [InjInc [InjSep [? ?]]]]]]].
           specialize (IHx _ _ _ _ _ _ _ _ H1 MC12' H0).
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']  [j'' [IncIncr' [InSep' [[c2'' [X [MC12'' MC23'']]] ?]]]]]]]. subst.
           exists c3''. exists m3''. exists (d12''', Some c2'',d23''). exists j''.
           split. eapply inject_incr_trans; eassumption.
           split. apply corestep_fwd in H.
                 intros b; intros.
                 remember (j' b).
                 destruct o; apply eq_sym in Heqo.
                      destruct p. destruct (InjSep _ _ _ H4 Heqo). apply (IncIncr') in Heqo. rewrite Heqo in H5.  inv H5.  split; trivial.
                 destruct (InSep' _ _ _ Heqo H5). split.
                    intros N. apply H6. apply H. apply N.
                    intros N. apply H7. 
                        assert (FWD: mem_forward m3 m3').
                           destruct H2 as [X | [X _]]. eapply corestep_plus_fwd; eassumption.  eapply corestep_star_fwd; eassumption.
                        apply FWD. apply N.
           split. exists c2''. auto.
           (*inv H8. constructor. auto.
           split. auto.*)
           destruct H2; destruct H3.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
              eapply t_trans; eauto.
          (*4/4*)
              apply t_step.
              constructor 2. apply H4.
  (*case 2*)
    destruct CS2. inv H.
    exists st3. exists m3. exists (d12',Some st2',d23). exists j.
    split. apply inject_incr_refl.
    split. apply inject_separated_same_meminj. 
    split. exists st2'.  split. trivial. split; assumption.
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
       (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globdef F1 V1)))
       (Sem2 : CoopCoreSem (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
       (Sem3 : CoopCoreSem (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
       ExternIdents epts12  epts23 entrypoints13
       (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3) 
       (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
       (e12 : prog_main P1 = prog_main P2)
       (g12: CompilerCorrectness.GenvHyp P1 P2)       
       (EPC: entrypoints_compose epts12 epts23 entrypoints13)
       (EXT1: In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (EXT2: In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (i1: I F1 C1 V1 Sem1 P1)
       (Eq_init12 : forall m1 : mem,
            Genv.init_mem P1 = Some m1 -> Genv.init_mem P2 = Some m1)
(*       (Eq_init12 : forall m1 : mem,
            initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
            exists m2 : mem, initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\ m1 = m2)
*)
       (SimEq12 : Forward_simulation_eq.Forward_simulation_equals mem (list (ident * globdef F1 V1))
                                          (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                                          (Genv.globalenv P2) epts12) 
       (SimInj23 : Coop_forward_simulation_inj.Forward_simulation_inject (list (ident * globdef F2 V2))
             (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
             (Genv.globalenv P3) epts23).

Lemma eqinj: Coop_forward_simulation_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                        (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                        (Genv.globalenv P3) entrypoints13.
Proof.
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
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12
                          i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13 Eq_init12 SimEq12 SimInj23.
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
                    split. trivial. 
                    split; try assumption. 
                    admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) j  from meminj_preserves_globals (Genv.globalenv P2) j for any j*)
             (*after_external*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. 
                    destruct H0 as [c2 [X [MC12 MC23]]]; subst.
                    destruct (core_at_external12 _ _ _ _ _ _ MC12 H1)  as [AtExt2 HVals1]; try assumption.
                    assert (HRet1:   Val.has_type ret1 (proj_sig_res ef_sig)). eapply valinject_hastype; eassumption.
                    destruct (core_after_external12 _ _ _ _ _ _ _ MC12 H1 AtExt2 HVals1 HRet1) as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    assert (PG2: meminj_preserves_globals (Genv.globalenv P2) j). admit. (*meminjpreservesglobals*)
                    destruct (core_after_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H MC23 AtExt2 H2 PG2 H4
                       H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16) as [d23' [c22' [c3' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',Some c2',d23'). exists c1'. exists c3'. split; trivial. split; trivial. exists c2'. auto.
Qed.
End EQINJ.

Lemma cc_trans_CaseEq: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : RelyGuaranteeSemantics (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
     (Sem2 : RelyGuaranteeSemantics (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
     (Sem3 : RelyGuaranteeSemantics (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
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
    (SimEq12 : Forward_simulation_eq.Forward_simulation_equals mem (list (ident * globdef F1 V1))
                                (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
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
           eapply eqeq; try eassumption.
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
           eapply eqext; try eassumption.
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
           eapply eqinj; try eassumption.
       (*prog_main*)
             rewrite e12; assumption.
       (*GenvHyp*) 
             destruct g23 as [Hyp2A Hyp2B].
             split; intros. rewrite Hyp2A. apply g12. 
                                   rewrite Hyp2B. apply g12.
       (*externvars*) intros b; intros. admit. (*preservation of externvars by equality phases even if V1->V2 etc*)
Qed.

Section EXTEQ. 
Lemma  diagram_exteq: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoreSemantics G2 C2 mem D2)
(Sem3 : CoreSemantics G3 C3 mem D3)
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(Genv2 : G2)
(Genv1 : G1)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 Genv1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (m2 : mem),
                 match_core12 cd st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       match_core12 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem2 Genv2 st2 m2 st2'
                          m2' \/
                        corestep_star Sem2 Genv2 st2 m2 st2'
                          m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> C3 -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(Genv3 : G3)
(core_diagram23 : forall (st1 : C2) (m : mem) (st1' : C2) (m' : mem),
                 corestep Sem2 Genv2 st1 m st1' m' ->
                 forall (d : core_data23) (st2 : C3),
                 match_core23 d st1 st2 ->
                 exists st2' : C3,
                   exists d' : core_data23,
                     match_core23 d' st1' st2' /\
                     (corestep_plus Sem3 Genv3 st2 m st2' m' \/
                      corestep_star Sem3 Genv3 st2 m st2' m' /\
                      core_ord23 d' d))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 Genv1 st1 m1 st1' m1')
(d12 : core_data12)
(d23 : core_data23)
(st3 : C3)
(m3 : mem)
(st2 : C2)
(MC12 : match_core12 d12 st1 m1 st2 m3)
(MC23: match_core23 d23 st2 st3),
exists st3' : C3,
  exists m3' : mem,
    exists cd' : core_data12 * option C2 * core_data23,
      (let (y, d2) := cd' in
       let (d1, X) := y in
       exists c2 : C2,
         X = Some c2 /\
         match_core12 d1 st1' m1' c2 m3' /\ match_core23 d2 c2 st3') /\
      (corestep_plus Sem3 Genv3 st3 m3 st3' m3' \/
       corestep_star Sem3 Genv3 st3 m3 st3' m3' /\
       clos_trans (core_data12 * option C2 * core_data23)
         (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
         (d12, Some st2, d23)).
Proof. intros.
    destruct (core_diagram12 _ _ _ _ CS1 _ _ _ MC12) as [st2' [m3' [d12' [MC12' Y]]]]. clear core_diagram12.
    assert (ZZ: corestep_plus Sem2 Genv2 st2 m3 st2' m3' \/  (st2,m3) = (st2',m3') /\ core_ord12 d12' d12).
       destruct Y. auto.
       destruct H.
       destruct H. destruct x.
       right. split; auto.
       left. exists x; auto.
    clear Y. destruct ZZ as [CS2 | CS2 ord12'].
     (*case1*) 
    destruct CS2.
    clear MC12 CS1.
    revert d23 st2 st2' m3' st3 m3 MC23 MC12' H.
    induction x; intros. 
      (*base case*) simpl in H.
          destruct H as [c2 [m2 [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _  MC23) as [st3' [d23' [? ?]]].
          exists st3'. exists m3'. exists (d12',Some st2',d23').
          split. exists st2'. split. trivial. split; assumption. 
          destruct H1. left; assumption.
          destruct H1. right. split; trivial.
          apply t_step. constructor 2. apply H2.
     (*inductive case*)
           remember (S x) as x'. simpl in H.
           destruct H as [st2'' [m2'' [? ?]]]. subst x'.
           destruct (core_diagram23 _ _ _ _  H _ _ MC23) as [c3' [d'' [? ?]]].
           specialize (IHx _ _ _ _ _ _ H1 MC12' H0).
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']   [[c2'' [X [MC12'' MC23'']]] ?]]]]; subst.
           exists c3''. exists m3''. exists (d12''', Some c2'',d23'').
           split. exists c2''. auto.
           (*inv H8. constructor. auto.
           split. auto.*)
           destruct H2; destruct H3.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
              eapply t_trans; eauto.
          (*4/4*)
              apply t_step.
              constructor 2. apply H4.
  (*case 2*)
    destruct CS2. inv H.
    exists st3. exists m3'. exists (d12',Some st2',d23).
    split. exists st2'.  split. trivial. split; assumption.
(*    apply extends_refl.
    inv H4.*)
(*    split. constructor; auto.*)
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3:Type}
(I : forall F C V : Type,  CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
(Sem1 : CoopCoreSem (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
(Sem2 : CoopCoreSem (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
(Sem3 : CoopCoreSem (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
       ExternIdents epts12  epts23 entrypoints13
       (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3) 
       (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
       (e12 : prog_main P1 = prog_main P2)
       (g12: CompilerCorrectness.GenvHyp P1 P2)       
       (EPC: entrypoints_compose epts12 epts23 entrypoints13)
       (EXT1: In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (EXT2: In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (i1: I F1 C1 V1 Sem1 P1)
(Ext_init12 : forall m1 : mem,
             Genv.init_mem P1 = Some m1 ->
             exists m2 : mem,
               Genv.init_mem P2 = Some m2 /\ Mem.extends m1 m2)
(SimExt12 : Coop_forward_simulation_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
             (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
             (Genv.globalenv P2) epts12)
(SimEq23 : Forward_simulation_eq.Forward_simulation_equals mem (list (ident * globdef F2 V2))
            (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
            (Genv.globalenv P3) epts23).

Lemma exteq: Coop_forward_simulation_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
                                        (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                       (Genv.globalenv P3) entrypoints13. 
Proof.
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
                          i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13 Ext_init12 SimExt12 SimEq23.
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
End EXTEQ.

Section EXTINJ.
Lemma  diagram_extinj: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoopCoreSem G2 C2 D2)
(Sem3 : CoopCoreSem G3 C3 D3)
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(Genv2 : G2)
(Genv1 : G1)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 Genv1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (m2 : mem),
                 match_core12 cd st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       match_core12 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem2 Genv2 st2 m2 st2'
                          m2' \/
                        corestep_star Sem2 Genv2 st2 m2 st2'
                          m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> meminj -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(Genv3 : G3)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 Genv2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (j : meminj) (m2 : mem),
                 match_core23 cd j st1 m1 st2 m2 ->
                 exists st2' : C3,
                   exists m2' : mem,
                     exists cd' : core_data23,
                       exists j' : meminj,
                         inject_incr j j' /\
                         inject_separated j j' m1 m2 /\
                         match_core23 cd' j' st1' m1' st2' m2' /\
                         (corestep_plus Sem3 Genv3 st2 m2 st2'
                            m2' \/
                          corestep_star Sem3 Genv3 st2 m2 st2'
                            m2' /\ core_ord23 cd' cd))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 Genv1 st1 m1 st1' m1')
(d12 : core_data12)
(d23 : core_data23)
(st3 : C3)
(j : meminj)
(m3 : mem)
(st2 : C2)
(m2 : mem)
(MC12 : match_core12 d12 st1 m1 st2 m2)
(MC23 : match_core23 d23 j st2 m2 st3 m3)
(match_validblocks12: forall cd st1 m1 st2 m2, 
   match_core12 cd st1 m1 st2 m2 -> (forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b)),
exists st3' : C3,
  exists m3' : mem,
    exists cd' : core_data12 * option C2 * core_data23,
      exists j' : meminj,
        inject_incr j j' /\
        inject_separated j j' m1 m3 /\
        (let (y, d2) := cd' in
         let (d1, X) := y in
         exists c2 : C2,
           exists m2' : mem,
             X = Some c2 /\
             match_core12 d1 st1' m1' c2 m2' /\
             match_core23 d2 j' c2 m2' st3' m3') /\
        (corestep_plus Sem3 Genv3 st3 m3 st3' m3' \/
         corestep_star Sem3 Genv3 st3 m3 st3' m3' /\
         clos_trans (core_data12 * option C2 * core_data23)
           (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
           (d12, Some st2, d23)).
Proof. intros.
    destruct (core_diagram12 _ _ _ _ CS1 _ _ _ MC12) as [st2' [m2' [d12' [MC12' Y]]]]. clear core_diagram12.
    assert (ZZ: corestep_plus Sem2 Genv2 st2 m2 st2' m2' \/  (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
       destruct Y. auto.
       destruct H.
       destruct H. destruct x.
       right. split; auto.
       left. exists x; auto.
    clear Y. destruct ZZ as [CS2 | CS2 ord12'].
     (*case1*) 
    destruct CS2.
    clear CS1. rename j into j23.
    cut (exists st3' : C3,  exists m3' : mem, exists d23':core_data23, exists j23' : meminj, 
                  inject_incr j23 j23' /\ inject_separated j23 j23' m2 m3 /\
                   match_core23 d23' j23' st2' m2' st3' m3' /\
                   (corestep_plus Sem3 Genv3 st3 m3 st3' m3' \/
                      (corestep_star Sem3 Genv3 st3 m3 st3' m3' /\
                        clos_trans (core_data12 * option C2 * core_data23)
                           (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) (d12', Some st2', d23')
                          (d12, Some st2, d23)))).
           intros XX; destruct XX as [st3' [m3' [d23' [j23' [InjIncr23 [InjSep23 [MC23' ZZ]]]]]]].
           exists st3'. exists m3'. exists (d12', Some st2', d23'). exists j23'. 
           split; trivial. 
           split; trivial. intros b; intros. destruct (InjSep23 _ _ _ H0 H1). 
                 split; try assumption. 
                 intros N. apply H2. eapply match_validblocks12. eassumption. apply N. 
           split. exists st2'. exists m2'. auto.
          apply ZZ.         

    clear MC12 MC12' match_validblocks12. (*InjIncr12 InjSep12 MC12' MatchHyp12.*)
          clear st1 m1 st1' m1'. clear G1 C1 D1 Sem1 match_core12 Genv1.

    revert j23 d23 st2 m2 st3 m3 H MC23. 
    induction x; intros.  
      (*base case*) simpl in H.
          destruct H as [c2 [m2'' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ _ _ MC23) as [st3' [m3' [d23' [j' [InjInc [InjSep [? ?]]]]]]].
          exists st3'. exists m3'. exists d23'. exists j'. 
          split; trivial.
          split; trivial. 
          split; trivial. 
          destruct H1. left; assumption.
          destruct H1. right. split; trivial.
          apply t_step. constructor 2. apply H2.
     (*inductive case*)
           remember (S x) as x'. simpl in H.
           destruct H as [st2'' [m2'' [? ?]]]. subst x'.
           destruct (core_diagram23 _ _ _ _  H _ _ _ _ MC23) as [c3' [m3' [d'' [j' [InjInc [InjSep [? ?]]]]]]].
           (*assert (YY:  forall b : block, Mem.valid_block m1 b -> Mem.valid_block m2'' b) .
              intros. clear IHx. apply corestep_fwd in H. eapply H. eapply match_validblocks12. apply MC12. assumption. 
     *)      specialize (IHx _ _ _ _ _ _ H0 H1).
           destruct IHx as [c3'' [m3'' [d23'' [j'' [InjIncr' [InjSep' [MC23'' ?]]]]]]]. subst.
           exists c3''. exists m3''. exists d23''. exists j''.
           split. eapply inject_incr_trans; eassumption.
           split. intros b. intros.
                     remember (j' b) as jb.
                     destruct jb; apply eq_sym in Heqjb.
                          destruct p. rewrite (InjIncr' _ _ _ Heqjb) in H5. inv H5. 
                                   destruct (InjSep _ _ _ H4 Heqjb).
                                   split; trivial. 
                     destruct (InjSep' _ _ _ Heqjb H5).
                                   split; intros N.
                                     apply corestep_fwd in H. apply H6. apply H. assumption.
                                   apply H7. 
                                      destruct H2 as [HH | [HH _]].
                                        eapply corestep_plus_fwd. apply HH. assumption.  
                                        eapply corestep_star_fwd. apply HH. assumption.
           split. assumption.  
           destruct H2; destruct H3.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
              eapply t_trans; eauto.
          (*4/4*)
              apply t_step.
              constructor 2. apply H4.
  (*case 2*)
    destruct CS2. inv H.
    exists st3. exists m3. exists (d12',Some st2',d23). exists j.
    split. apply inject_incr_refl.
    split. apply inject_separated_same_meminj.
    split. exists st2'. exists m2'. split. trivial. split; assumption.
(*    apply extends_refl.
    inv H4.*)
(*    split. constructor; auto.*)
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
       (Sem1 : CoopCoreSem (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
       (Sem2 : CoopCoreSem (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
       (Sem3 : CoopCoreSem (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
       ExternIdents epts12  epts23 entrypoints13
       (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3) 
       (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
       (e12 : prog_main P1 = prog_main P2)
       (g12: CompilerCorrectness.GenvHyp P1 P2)       
       (EPC: entrypoints_compose epts12 epts23 entrypoints13)
       (EXT1: In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (EXT2: In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (i1: I F1 C1 V1 Sem1 P1)
       (Ext_init12 : forall m1 : mem,
             Genv.init_mem P1 = Some m1 ->
             exists m2 : mem,
               Genv.init_mem P2 = Some m2 /\ Mem.extends m1 m2)
       (*(Ext_init12 : forall m1 : mem,
             initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
             exists m2 : mem,
               initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
               Mem.extends m1 m2)*)
     (SimExt12 : Coop_forward_simulation_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
             (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) epts12)
     (SimInj23 : Coop_forward_simulation_inj.Forward_simulation_inject (list (ident * globdef F2 V2))
             (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2) (Genv.globalenv P3) epts23).

Lemma extinj: Coop_forward_simulation_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                         (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                        (Genv.globalenv P3) entrypoints13.
Proof.
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
                          i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13 Ext_init12 SimExt12 SimInj23.
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
                    split. eapply extends_inject_compose; eassumption.
                    split. admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) j  from meminj_preserves_globals (Genv.globalenv P2) j for any j*)  
                    exists vals3. 
                    split. eapply forall_val_lessdef_inject_compose; eassumption. 
                    split. assumption.
                    split; assumption.
             (*after_external*) 
                    clear core_diagram12 core_diagram23 core_initial12 core_initial23
                          core_halted12 core_halted23 Ext_init12.
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
                    assert (UnchOn3 : Mem.unchanged_on (loc_out_of_reach j m2) m3 m3').
                        split; intros; eapply H11; trivial.
                                 eapply extends_loc_out_of_reach; eassumption.
                                 intros.  eapply extends_loc_out_of_reach; eassumption.
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

(*
                    destruct (PUSHOUTS.pushout_EI _ _ _ Ext12 H7) as [m2' [Fwd2' [Ext12' [UnchOn2 X]]]].
                    destruct (X _ H8) as [UnchOn2j Ext23']; clear X.
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ ret1 ret1 _ _ _ MC12 H1 AtExt2 
                              LDVals12 HTVals2 H7 Fwd2' UnchOn2 (Val.lessdef_refl _) Ext12' HRet1) 
                         as [c1' [c2' [d12' [AftExt1 [AftExt2 MC12']]]]]; clear core_after_external12.
                    specialize (Ext23' _ Inj23 _ H9 H10 _ H3 H4 H5).
                    destruct (core_after_external23 _ j j' _ _ _ _ vals2 ret1 _ _ _ ret3 _ Inj23 
                              MC23 AtExt2 PG2 H3 Sep23 Ext23' H6 Fwd2' UnchOn2j H9 UnchOn3 H11)
                         as [d23' [cc2' [c3' [AftExt22 [AftExt3 MC23']]]]]; clear core_after_external23.
*)

                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',Some c2', d23'). exists c1'. exists c3'. split; trivial. split; trivial.
                    exists c2'. exists m2'. split; trivial. split; trivial.
Qed.
End EXTINJ.

Lemma cc_trans_CaseExtends: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : RelyGuaranteeSemantics (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
     (Sem2 : RelyGuaranteeSemantics (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
     (Sem3 : RelyGuaranteeSemantics (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
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
     (SimExt12 :  Coop_forward_simulation_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
                                (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
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
           eapply exteq; try eassumption.
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
           eapply extext; try eassumption.
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
                    eapply  extends_inject_compose; eassumption.
       (*entrypoints_ok*)
           eapply ePts_compose2; eassumption.
       (*meminj_preserves_globals*)
           admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) jInit  from meminj_preserves_globals (Genv.globalenv P2) jInit*)
       (*sim_extinj*) 
           eapply extinj; try eassumption.
       (*prog_main*)
             rewrite e12; assumption.
       (*GenvHyp*) 
             destruct g23 as [Hyp2A Hyp2B].
             split; intros. rewrite Hyp2A. apply g12. 
                                  rewrite Hyp2B. apply g12.
       (*externvars*) admit. (*preservation of externvars by extension phases even if V1->V2 etc*)
Qed.

Section INJEQ.
Lemma  diagram_injeq: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoopCoreSem G2 C2 D2)
(Sem3 : CoreSemantics G3 C3 mem D3)
(core_data12 : Type)
(match_core12 : core_data12 -> meminj -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(Genv2 : G2)
(Genv1 : G1)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 Genv1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (j : meminj) (m2 : mem),
                 match_core12 cd j st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       exists j' : meminj,
                         inject_incr j j' /\
                         inject_separated j j' m1 m2 /\
                         match_core12 cd' j' st1' m1' st2' m2' /\
                         (corestep_plus Sem2 Genv2 st2 m2 st2' m2' \/
                          corestep_star Sem2 Genv2 st2 m2 st2' m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> C3 -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(Genv3 : G3)
(core_diagram23 : forall (st1 : C2) (m : mem) (st1' : C2) (m' : mem),
                 corestep Sem2 Genv2 st1 m st1' m' ->
                 forall (d : core_data23) (st2 : C3),
                 match_core23 d st1 st2 ->
                 exists st2' : C3,
                   exists d' : core_data23,
                     match_core23 d' st1' st2' /\
                     (corestep_plus Sem3 Genv3 st2 m st2' m' \/
                      corestep_star Sem3 Genv3 st2 m st2' m' /\
                      core_ord23 d' d))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 Genv1 st1 m1 st1' m1')
(d12 : core_data12)
(d23 : core_data23)
(st3 : C3)
(j : meminj)
(m2 : mem)
(st2 : C2)
(MC12 : match_core12 d12 j st1 m1 st2 m2)
(MC23 : match_core23 d23 st2 st3),
exists st3' : C3,
  exists m2' : mem,
    exists cd' : core_data12 * option C2 * core_data23,
      exists j' : meminj,
        inject_incr j j' /\
        inject_separated j j' m1 m2 /\
        (let (y, d2) := cd' in
         let (d1, X) := y in
         exists c2 : C2,
           X = Some c2 /\
           match_core12 d1 j' st1' m1' c2 m2' /\ match_core23 d2 c2 st3') /\
        (corestep_plus Sem3 Genv3 st3 m2 st3' m2' \/
         corestep_star Sem3 Genv3 st3 m2 st3' m2' /\
         clos_trans (core_data12 * option C2 * core_data23)
           (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
           (d12, Some st2, d23)).
Proof. intros.
    destruct (core_diagram12 _ _ _ _ CS1 _ _ _ _ MC12) as [st2' [m2' [d12' [j' [InjIncr [InjSep [MC12' Y]]]]]]]; clear core_diagram12.
    assert (ZZ: corestep_plus Sem2 Genv2 st2 m2 st2' m2' \/  (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
       destruct Y. auto.
       destruct H.
       destruct H. destruct x.
       right. split; auto.
       left. exists x; auto.
    clear Y. destruct ZZ as [CS2 | CS2 ord12'].
     (*case1*) 
    destruct CS2.
    clear MC12 CS1.
     revert j j' d23 st2 st2' m2 st3 m1' MC23 MC12' H InjIncr InjSep.
    induction x; intros. 
      (*base case*) simpl in H.
          destruct H as [c2 [m2'' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ MC23) as [st3' [d23' [? ?]]].
          exists st3'. exists m2'. exists (d12',Some st2',d23'). exists j'. 
          split; trivial.
          split; trivial.
          split. exists st2'. split. trivial. split. apply MC12'. apply H0.
          destruct H1. left; assumption.
          destruct H1. right. split; trivial.
          apply t_step. constructor 2. apply H2.
     (*inductive case*)
           remember (S x) as x'. simpl in H.
           destruct H as [st2'' [m2'' [? ?]]]. subst x'.
           destruct (core_diagram23 _ _ _ _  H _ _ MC23) as [c3' [d'' [? ?]]].
           specialize (IHx j' _ _ _ _ _ _ _ H1 MC12' H0).
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']  [j'' [InjIncr' [InjSep'' [[c2'' [X [MC12'' MC23'']]] ?]]]]]]]. intros b; intros. trivial. apply inject_separated_same_meminj. subst.
           exists c3''. exists m3''. exists (d12''', Some c2'',d23''). exists j''.
           split. eapply inject_incr_trans; eassumption. 
           split. eapply (inject_separated_incr_fwd _ _ _ _ _ _  InjSep InjSep'' InjIncr'). 
                    apply (corestep_fwd _ _ _ _ _ _ H). 
           split. exists c2''. split. trivial. split. apply MC12''. apply MC23''.
           (*inv H8. constructor. auto.
           split. auto.*)
           destruct H2; destruct H3.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
              eapply t_trans; eauto.
          (*4/4*)
              apply t_step.
              constructor 2. apply H4.
  (*case 2*)
    destruct CS2. inv H.
    exists st3. exists m2'. exists (d12',Some st2',d23). exists j'.
    split. assumption.
    split. assumption.
    split. exists st2'. split. trivial. split. apply MC12'. apply MC23.
(*    apply extends_refl.
    inv H4.*)
(*    split. constructor; auto.*)
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
       (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globdef F1 V1)))
       (Sem2 : CoopCoreSem (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
       (Sem3 : CoreSemantics (Genv.t F3 V3) C3 mem (list (ident * globdef F3 V3)))
       ExternIdents epts12  epts23 entrypoints13
       (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3) 
       j12
       (ePts12_ok : CompilerCorrectness.entryPts_inject_ok P1 P2 j12 ExternIdents epts12)
       (e12 : prog_main P1 = prog_main P2)
       (g12: CompilerCorrectness.GenvHyp P1 P2)       
       (EPC: entrypoints_compose epts12 epts23 entrypoints13)
       (EXT1: In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (EXT2: In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (i1: I F1 C1 V1 Sem1 P1)
       (Inj_init12 : forall m1 : mem,
             Genv.init_mem P1 = Some m1 ->
             exists m2 : mem,
               Genv.init_mem P2 = Some m2 /\ Mem.inject j12 m1 m2)
(*       (Inj_init12 : forall m1 : mem,
               initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
               exists m2 : mem,
                 initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
                 Mem.inject j12 m1 m2)
*)
      (PG1 : meminj_preserves_globals (Genv.globalenv P1) j12)
      (SimInj12 : Coop_forward_simulation_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                          (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                          (Genv.globalenv P2) epts12)
      (SimEq23 : Forward_simulation_eq.Forward_simulation_equals mem (list (ident * globdef F2 V2))
                          (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2) (Genv.globalenv P3) epts23).

Lemma injeq: Coop_forward_simulation_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                        (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                        (Genv.globalenv P3) entrypoints13.
Proof. 
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
                          i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13 Inj_init12 SimInj12 SimEq23.
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
End INJEQ.

Section INJEXT.
Lemma  diagram_injext: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoreSemantics G2 C2 mem D2)
(Sem3 : CoopCoreSem G3 C3 D3)
(core_data12 : Type)
(match_core12 : core_data12 -> meminj -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(Genv2 : G2)
(Genv1 : G1)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 Genv1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (j : meminj) (m2 : mem),
                 match_core12 cd j st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       exists j' : meminj,
                         inject_incr j j' /\
                         inject_separated j j' m1 m2 /\
                         match_core12 cd' j' st1' m1' st2' m2' /\
                         (corestep_plus Sem2 Genv2 st2 m2 st2' m2' \/
                          corestep_star Sem2 Genv2 st2 m2 st2' m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(Genv3 : G3)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 Genv2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (m2 : mem),
                 match_core23 cd st1 m1 st2 m2 ->
                 exists st2' : C3,
                   exists m2' : mem,
                     exists cd' : core_data23,
                       match_core23 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem3 Genv3 st2 m2 st2'
                          m2' \/
                        corestep_star Sem3 Genv3 st2 m2 st2'
                          m2' /\ core_ord23 cd' cd))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 Genv1 st1 m1 st1' m1')
(d12 : core_data12)
(d23 : core_data23)
(st3 : C3)
(j : meminj)
(m3 : mem)
(st2 : C2)
(m2 : mem)
(MC12: match_core12 d12 j st1 m1 st2 m2)
(MC23: match_core23 d23 st2 m2 st3 m3)
(MatchHyp12: forall d12 j12 c1 m1 c2 m2,  match_core12 d12 j12 c1 m1 c2 m2 ->  
                    forall b1 b2 ofs, j12 b1 = Some (b2,ofs) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
(MatchHyp23: forall d23 c2 m2 c3 m3,  match_core23 d23 c2 m2 c3 m3 ->  
                    forall b, Mem.valid_block m2 b <-> Mem.valid_block m3 b),
exists st2' : C3,
  exists m2' : mem,
    exists cd' : core_data12 * option C2 * core_data23,
      exists j' : meminj,
        inject_incr j j' /\
        inject_separated j j' m1 m3 /\
        (let (y, d2) := cd' in
         let (d1, X) := y in
         exists c2 : C2,
           exists m0 : mem,
             X = Some c2 /\
             match_core12 d1 j' st1' m1' c2 m0 /\
             match_core23 d2 c2 m0 st2' m2') /\
        (corestep_plus Sem3 Genv3 st3 m3 st2' m2' \/
         corestep_star Sem3 Genv3 st3 m3 st2' m2' /\
         clos_trans (core_data12 * option C2 * core_data23)
           (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
           (d12, Some st2, d23)).
Proof. intros.
    destruct (core_diagram12 _ _ _ _ CS1 _ _ _ _ MC12) as [st2' [m2' [d12' [j' [InjIncr [InjSep [MC12' Y]]]]]]]; clear core_diagram12.
    assert (ZZ: corestep_plus Sem2 Genv2 st2 m2 st2' m2' \/  (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
       destruct Y. auto.
       destruct H.
       destruct H. destruct x.
       right. split; auto.
       left. exists x; auto.
    clear Y. destruct ZZ as [CS2 | [CS2 ord12']].
     (*case1*) 
    destruct CS2.
    clear CS1. rename j into j23.
    cut (exists st3' : C3,  exists m3' : mem, exists d23':core_data23, 
                   match_core23 d23' st2' m2' st3' m3' /\
                   (corestep_plus Sem3 Genv3 st3 m3 st3' m3' \/
                      (corestep_star Sem3 Genv3 st3 m3 st3' m3' /\
                        clos_trans (core_data12 * option C2 * core_data23)
                           (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) (d12', Some st2', d23')
                          (d12, Some st2, d23)))).
           intros XX; destruct XX as [st3' [m3' [d23' [MC23' ZZ]]]].
           exists st3'. exists m3'. exists (d12', Some st2', d23'). exists j'. 
           split; trivial. 
           split; trivial. intros b; intros. destruct (InjSep _ _ _ H0 H1). 
                 split; try assumption. 
                 intros N. apply H3. eapply MatchHyp23. eassumption. apply N. 
           split. exists st2'. exists m2'. auto.
          apply ZZ.         

    clear MC12 MC12' MatchHyp12. (*InjIncr12 InjSep12 MC12' MatchHyp12.*)
          clear InjSep InjIncr j23 j' st1 m1 st1' m1'. 
          clear G1 C1 D1 Sem1 match_core12 Genv1.

    revert d23 st2 m2 st3 m3 H MC23. 
    induction x; intros.  
      (*base case*) simpl in H.
          destruct H as [c2 [m2'' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ _ MC23) as [st3' [m3' [d23' [? ?]]]].
          exists st3'. exists m3'. exists d23'. 
          split; trivial.
          destruct H1. left; assumption.
          destruct H1. right. split; trivial.
          apply t_step. constructor 2. apply H2.
     (*inductive case*)
           remember (S x) as x'. simpl in H.
           destruct H as [st2'' [m2'' [? ?]]]. subst x'.
           destruct (core_diagram23 _ _ _ _  H _ _ _ MC23) as [c3' [m3' [d'' [? ?]]]].
           specialize (IHx _ _ _ _ _ H0 H1).
           destruct IHx as [c3'' [m3'' [d23'' [ MC23'' ?]]]].
           exists c3''. exists m3''. exists d23''. 
           split. eassumption. 
           destruct H2; destruct H3.
           (*1/4*)
              left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H3.
               left. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H2.
                       destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               right. destruct H2. destruct H3.
               split. destruct H2 as [n1 ?]. destruct H3 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
              eapply t_trans; eauto.
          (*4/4*)
              apply t_step.
              constructor 2. apply H4.
  (*case 2*)
    inv CS2. 
    exists st3. exists m3. exists (d12',Some st2',d23). exists j'.
    split. assumption.
    split. intros b; intros.
                    destruct (InjSep _ _ _ H H0).
                     split; trivial.
                     intros N. apply H2. 
                     eapply MatchHyp23. apply MC23. apply N. 
    split. exists st2'. exists m2'. split. trivial. split. apply MC12'. apply MC23.
(*    apply extends_refl.
    inv H4.*)
(*    split. constructor; auto.*)
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
       (Sem1 : CoopCoreSem (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
       (Sem2 : CoopCoreSem (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
       (Sem3 : CoopCoreSem (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
       ExternIdents epts12  epts23 entrypoints13
       (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3) 
       j12
       (ePts12_ok : CompilerCorrectness.entryPts_inject_ok P1 P2 j12 ExternIdents epts12)
       (e12 : prog_main P1 = prog_main P2)
       (g12: CompilerCorrectness.GenvHyp P1 P2)       
       (EPC: entrypoints_compose epts12 epts23 entrypoints13)
       (EXT1: In (prog_main P1, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (EXT2: In (prog_main P2, CompilerCorrectness.extern_func main_sig) ExternIdents)
       (i1: I F1 C1 V1 Sem1 P1)
(*       (Inj_init12 : forall m1 : mem,
               initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
               exists m2 : mem,
                 initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
                 Mem.inject j12 m1 m2)*)
      (PG1 : meminj_preserves_globals (Genv.globalenv P1) j12)
      (SimInj12 : Coop_forward_simulation_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                          (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                          (Genv.globalenv P2) epts12)
      (SimExt23 : Coop_forward_simulation_ext.Forward_simulation_extends (list (ident * globdef F2 V2))
                           (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
                           (Genv.globalenv P3) epts23).

Lemma injext: Coop_forward_simulation_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                               (Genv.globalenv P3) entrypoints13.
Proof.
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
                          i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13 (*Inj_init12 *) SimInj12 SimExt23.
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
                    assert (UnchLOOB23_3': Mem.unchanged_on (loc_out_of_bounds m2) m3 m3'). 
                         eapply inject_LOOR_LOOB; eassumption.
                    assert (WD2: mem_wd m2). apply match_memwd23 in MC23. apply MC23. 
                    destruct (MEMAX.interpolate_IE _ _ _ _ Minj12 H8 _ H4 Sep12 H9 _ _ MExt23 H10 H11 H6 UnchLOOB23_3' WD2 H13 H14)
                          as [m2' [Fwd2' [MExt23' [Minj12' [UnchLOORj1_2 WD22']]]]].

 (*                   destruct (PUSHOUTS.pushout_IE _ _ _ _ Minj12  H7 _ H3 Sep12 H8)
                           as [m2' [Minj12' [Fwd2' [UnchLOORj1_2 MExt23']]]].
                    specialize (MExt23' _ _ MExt23 H9 H10).*)
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
End INJEXT.

Lemma cc_trans_CaseInject: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : RelyGuaranteeSemantics (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
     (Sem2 : RelyGuaranteeSemantics (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
     (Sem3 : RelyGuaranteeSemantics (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
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
     (SimInj12: Coop_forward_simulation_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                 (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
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
            eapply injeq; try eassumption.
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
           eapply inject_extends_compose; eassumption.
       (*entrypoints_ok*)
           eapply ePts_compose3; eassumption.
       (*sim_injext*) 
            eapply injext; try eassumption.
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
           eapply injinj; try eassumption.
       (*prog_main*)
             rewrite e12; assumption.
       (*GenvHyp*) 
             destruct g23 as [Hyp2A Hyp2B].
             split; intros. rewrite Hyp2A. apply g12. 
                                  rewrite Hyp2B. apply g12.
Qed.     

Theorem cc_trans:
     forall ExternIdents entrypoints12 I F1 C1 V1 F2 C2 V2
        (Sem1: RelyGuaranteeSemantics (Genv.t F1 V1) C1 (list (ident * globdef F1 V1)))
        (Sem2: RelyGuaranteeSemantics (Genv.t F2 V2) C2 (list (ident * globdef F2 V2)))
        P1 P2 
        (SIM12: CompilerCorrectness.cc_sim I ExternIdents entrypoints12 F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2)
        F3 V3 C3
        (Sem3: RelyGuaranteeSemantics (Genv.t F3 V3) C3 (list (ident * globdef F3 V3)))
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
