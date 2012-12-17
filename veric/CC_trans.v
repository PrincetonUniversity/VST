Load loadpath.
Require Import veric.base.
Require Import Events.
Require Import veric.sim.
Require Import veric.MemoryPushouts.
Require Import Wellfounded.

(*It seems we need the following property to be satisfied by at least Sem2 and Sem3.
  Probably we should add it as an axiom to CoreSemantics in sim.v.
  The fact that this property is required should not be too surprising: it corresponds to
  the axiom ec_valid_blockin Events.v*)
Definition corestep_fwd {G C D} (Sem: CoreSemantics G C mem D) :=
forall g c m c' m' (CS: corestep Sem g c m c' m'), mem_forward m m'.

Lemma corestepN_fwd: forall {G C D} (Sem: CoreSemantics G C mem D)
              (CSF: corestep_fwd Sem) g N c m c' m' (CS:corestepN Sem g N c m c' m'), 
               mem_forward m m'.
Proof. intros G C D Sem CSF g N.
  induction N; simpl; intros.
       inv CS. apply mem_forward_refl. 
       destruct CS as [c2 [m2 [CS1 CS2]]].
           apply CSF in CS1. apply IHN in CS2. eapply mem_forward_trans; eassumption.
Qed. 

Lemma corestep_star_fwd: forall {G C D} (Sem: CoreSemantics G C mem D)
              (CSF: corestep_fwd Sem) g c m c' m' (CS:corestep_star Sem g c m c' m'), 
               mem_forward m m'.
Proof. intros. destruct CS.  eapply  corestepN_fwd. apply CSF. apply H. Qed.

Lemma corestep_plus_fwd: forall {G C D} (Sem: CoreSemantics G C mem D)
              (CSF: corestep_fwd Sem) g c m c' m' (CS:corestep_plus Sem g c m c' m'), 
               mem_forward m m'.
Proof. intros. destruct CS.  eapply  corestepN_fwd. apply CSF. apply H. Qed.

Definition main_sig : signature := 
       mksignature (nil) (Some AST.Tint).

Definition entrypoints_compose (ep12 ep23 ep13 : list (val * val * signature)): Prop :=
   forall v1 v3 sig, In (v1,v3,sig) ep13 = exists v2, In (v1,v2,sig) ep12 /\ In (v2,v3,sig) ep23.

Lemma ePts_compose1: forall {F1 V1 F2 V2 F3 V3} 
     (Prg1 : AST.program F1 V1) (Prg2 : AST.program F2 V2)  (Prg3 : AST.program F3 V3)
     Epts12 Epts23 ExternIdents entrypoints13 
    (EPC : entrypoints_compose Epts12 Epts23 entrypoints13)
    (ePts12_ok : @CompilerCorrectness.entryPts_ok F1 V1 F2 V2 Prg1 Prg2 ExternIdents Epts12)
    (ePts23_ok : @CompilerCorrectness.entryPts_ok F2 V2 F3 V3 Prg2 Prg3 ExternIdents Epts23),
CompilerCorrectness.entryPts_ok Prg1 Prg3 ExternIdents entrypoints13.
Proof. intros.
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
Qed.

Lemma ePts_compose2: forall {F1 V1 F2 V2 F3 V3} 
     (P1 : AST.program F1 V1) (P2 : AST.program F2 V2)  (P3 : AST.program F3 V3)
     Epts12 Epts23 ExternIdents entrypoints13 jInit
    (EPC : entrypoints_compose Epts12 Epts23 entrypoints13)
    (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents Epts12)
    (ePts23_ok : CompilerCorrectness.entryPts_inject_ok P2 P3 jInit ExternIdents Epts23),
    CompilerCorrectness.entryPts_inject_ok P1 P3 jInit ExternIdents entrypoints13.
Proof. intros.
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
Qed.

Lemma ePts_compose3: forall {F1 V1 F2 V2 F3 V3} 
     (Prg1 : AST.program F1 V1) (Prg2 : AST.program F2 V2)  (Prg3 : AST.program F3 V3)
     Epts12 Epts23 ExternIdents entrypoints13 j12
    (EPC : entrypoints_compose Epts12 Epts23 entrypoints13)
    (ePts12_ok : @CompilerCorrectness.entryPts_inject_ok F1 V1 F2 V2 Prg1 Prg2 j12 ExternIdents Epts12)
    (ePts23_ok : @CompilerCorrectness.entryPts_ok F2 V2 F3 V3 Prg2 Prg3 ExternIdents Epts23),
CompilerCorrectness.entryPts_inject_ok Prg1 Prg3 j12 ExternIdents entrypoints13.
Proof. intros.
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
Qed.

Lemma ePts_compose4: forall {F1 V1 F2 V2 F3 V3} 
     (Prg1 : AST.program F1 V1) (Prg2 : AST.program F2 V2)  (Prg3 : AST.program F3 V3)
     Epts12 Epts23 ExternIdents entrypoints13 j12 j23
    (EPC : entrypoints_compose Epts12 Epts23 entrypoints13)
    (ePts12_ok : @CompilerCorrectness.entryPts_inject_ok F1 V1 F2 V2 Prg1 Prg2 j12 ExternIdents Epts12)
    (ePts23_ok : @CompilerCorrectness.entryPts_inject_ok F2 V2 F3 V3 Prg2 Prg3 j23 ExternIdents Epts23),
CompilerCorrectness.entryPts_inject_ok Prg1 Prg3 (compose_meminj j12 j23) ExternIdents entrypoints13.
Proof. intros.
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
Qed.

Inductive sem_compose_ord_eq_eq {D12 D23:Type} (ord12: D12 -> D12 -> Prop) (ord23: D23 -> D23 -> Prop) 
         (C2:Type):
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
(*    set (q := (d23,c)).
    change d23 with (fst q). change c with (snd q). clearbody q.
    clear d23.*)
   revert c. 
    induction d23 using (well_founded_induction WF23).
    intros.
(*    set (q' := (d12,c)).
    change d12 with (fst q'). change c with (snd q').
    clearbody q'. clear d12 c.*)
    induction d12 using (well_founded_induction WF12).
    constructor; intros. inv H1.
    generalize (H0 d0). simpl. intros.
    apply H1. auto. (* destruct q'; auto.*) 
    generalize (H d1). 
    intros. 
    spec H1. auto. (* destruct q; auto.*)
    apply H1. 
  Qed.

Lemma compose_meminjD_None: forall j jj b, 
       (compose_meminj j jj) b = None -> 
       j b = None \/ 
       (exists b', exists ofs, j b = Some(b',ofs) /\ jj b' = None). 
Proof. unfold compose_meminj; intros.
       destruct (j b).
         destruct p. right.
         remember (jj b0) as zz; destruct zz. destruct p. inv H.
         exists b0. exists z. rewrite <- Heqzz. auto.
       left; trivial.
Qed.

Lemma compose_meminjD_Some: forall j jj b b2 ofs2, 
       (compose_meminj j jj) b = Some(b2,ofs2) -> 
       exists b1, exists ofs1, exists ofs,
       j b = Some(b1,ofs1) /\ jj b1 = Some(b2,ofs) /\ ofs2=ofs1+ofs. 
Proof. unfold compose_meminj; intros.
       remember (j b) as z; destruct z; apply eq_sym in Heqz.
         destruct p. exists b0. exists z. 
         remember (jj b0) as zz. 
         destruct zz; apply eq_sym in Heqzz. 
           destruct p. inv H. exists z0. auto.
           inv H.
         inv H.
Qed. 

Lemma compose_meminj_inject_incr: forall j12 j12' j23 j23'
  (InjIncr12: inject_incr j12 j12') (InjIncr23: inject_incr j23 j23'),
  inject_incr (compose_meminj j12 j23) (compose_meminj j12' j23').
Proof.
  intros. intros b; intros. 
  apply compose_meminjD_Some in H. 
  destruct H as [b1 [ofs1 [ofs [Hb [Hb1 Hdelta]]]]]. 
  unfold compose_meminj.
  rewrite (InjIncr12 _ _ _ Hb).
  rewrite (InjIncr23 _ _ _ Hb1). subst. trivial.
Qed.

Lemma compose_meminj_inject_separated: forall j12 j12' j23 j23' m1 m2 m3
   (InjSep12 : inject_separated j12 j12' m1 m2)
   (InjSep23 : inject_separated j23 j23' m2 m3)
   (InjIncr12: inject_incr j12 j12') (InjIncr23: inject_incr j23 j23')
   (BV12: forall b1 b2 ofs, j12 b1 = Some (b2,ofs) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
   (BV23: forall b1 b2 ofs, j23 b1 = Some (b2,ofs) -> Mem.valid_block m2 b1 /\ Mem.valid_block m3 b2),
   inject_separated (compose_meminj j12 j23) (compose_meminj j12' j23') m1 m3.
Proof. intros.
  unfold compose_meminj; intros b; intros.
  remember (j12 b) as j12b.
  destruct j12b; inv H; apply eq_sym in Heqj12b. destruct p.
    rewrite (InjIncr12 _ _ _ Heqj12b) in H0.
    remember (j23 b0) as j23b0.
    destruct j23b0; inv H2; apply eq_sym in Heqj23b0. destruct p. inv H1.
    remember (j23' b0) as j23'b0.
    destruct j23'b0; inv H0; apply eq_sym in Heqj23'b0. destruct p. inv H1.
    destruct (InjSep23 _ _ _ Heqj23b0 Heqj23'b0).    
    split; trivial. exfalso. apply H. eapply BV12. apply Heqj12b.
  remember (j12' b) as j12'b.
  destruct j12'b; inv H0; apply eq_sym in Heqj12'b. destruct p.
    destruct (InjSep12 _ _ _ Heqj12b Heqj12'b). split; trivial.
    remember (j23' b0) as j23'b0.
    destruct j23'b0; inv H1; apply eq_sym in Heqj23'b0. destruct p. inv H3.
    remember (j23 b0) as j23b0.
    destruct j23b0; apply eq_sym in Heqj23b0. destruct p. rewrite (InjIncr23 _ _ _ Heqj23b0) in Heqj23'b0. inv Heqj23'b0.      
      exfalso. apply H0. eapply BV23. apply Heqj23b0.
    destruct (InjSep23 _ _ _ Heqj23b0 Heqj23'b0). assumption.    
Qed.

Lemma compose_meminj_inject_separated': forall j12 j12' j23 j23' m1 m2 m3
   (InjSep12 : inject_separated j12 j12' m1 m2)
   (InjSep23 : inject_separated j23 j23' m2 m3)
   (InjIncr12: inject_incr j12 j12') (InjIncr23: inject_incr j23 j23')
   (MInj12: Mem.inject j12 m1 m2)
   (MInj23: Mem.inject j23 m2 m3),
   inject_separated (compose_meminj j12 j23) (compose_meminj j12' j23') m1 m3.
Proof. intros.
  eapply compose_meminj_inject_separated; try eassumption.
  intros; split. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj12). apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj12).
  intros; split. apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H MInj23). apply (Mem.valid_block_inject_2 _ _ _ _ _ _ H MInj23).
Qed.

Section INJINJ.

Lemma diagram_injinj: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoreSemantics G2 C2 mem D2)
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
(MatchHyp12: forall d12 j12 c1 m1 c2 m2,  match_core12 d12 j12 c1 m1 c2 m2 ->  
                                   forall b1 b2 ofs, j12 b1 = Some (b2,ofs) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
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
  (MC23 : match_core23 d23 j23 st2 m2 st3 m3)
  (CSF2 : corestep_fwd Sem2)
  (CSF3 : corestep_fwd Sem3),
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
Proof. intros. 
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
           split. eapply compose_meminj_inject_separated. apply InjSep12. apply InjSep23. assumption. assumption.
                                 eapply (MatchHyp12 _ _ _ _ _ _ MC12).
                                 eapply (MatchHyp23 _ _ _ _ _ _ MC23).
           split. exists st2'. exists m2'. exists j12'. exists j23'. auto.
          apply ZZ.
   clear MC12 InjIncr12 InjSep12 MC12' MatchHyp12. clear st1 m1 st1' m1' j12 j12'. clear G1 C1 D1 Sem1 match_core12 Genv1.

    revert j23 d23 st2 m2 st3 m3 H MC23. 
    induction x; intros. 
      (*base case*) simpl in H.
          destruct H as [c2 [m2'' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ _ _ MC23) as [st3' [m3' [d23' [j23' [InjInc23 [InjSep23 [? ?]]]]]]].
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
           destruct (core_diagram23 _ _ _ _  H _ _ _ _ MC23) as [c3' [m3' [d23' [j23' [InjInc23 [InjSep23 [? ?]]]]]]]. clear core_diagram23.
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
                             apply H4. apply CSF2 in H. apply H. apply N.
                             apply H5. destruct H2 as [H2 | [H2 _]].
                                                   apply (corestep_plus_fwd _ CSF3) in H2. apply H2. apply N.
                                                   apply (corestep_star_fwd _ CSF3) in H2. apply H2. apply N.                      
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
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
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
(*       (Inj_init12 : forall m1 : mem,
               initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
               exists m2 : mem,
                 initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
                 Mem.inject j12 m1 m2)*)
     (SimInj12 : Sim_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
             (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) epts12)
     (SimInj23 : Sim_inj.Forward_simulation_inject (list (ident * globdef F2 V2))
             (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2) (Genv.globalenv P3) epts23)
     (CSF2: corestep_fwd Sem2) (CSF3: corestep_fwd Sem3).

Lemma val_inject_compose_split: forall j1 j2 v1 v3 (Vinj:val_inject (compose_meminj j1 j2) v1 v3),
  exists v2, val_inject j1 v1 v2 /\ val_inject j2 v2 v3.
Proof. intros.
   inv Vinj.
   exists (Vint i). split; constructor.
   exists (Vfloat f). split; constructor.
   rename b2 into b3. apply compose_meminjD_Some in H. 
        destruct H as [b2 [ofs11 [ofs22 [H1 [H2 X]]]]]; subst.
        exists (Vptr b2 (Int.add ofs1 (Int.repr ofs11))).
         split. econstructor. apply H1. trivial.
                   econstructor. apply H2. rewrite Int.add_assoc. admit. (*overflow stuff - may not hold!*)
  exists Vundef. split; econstructor.
Qed.
                 

Axiom PO_II: 
forall  m1 m2 m1' j1 (Minj12 : Mem.inject j1 m1 m2) (Fwd1: mem_forward m1 m1') j2
                          j' (InjInc: inject_incr (compose_meminj j1 j2) j')  
                          (UnchLUj:  mem_unchanged_on (loc_unmapped (compose_meminj j1 j2)) m1 m1'),
exists m2', exists j1', exists j2',  Mem.inject j1' m1' m2' /\ mem_forward m2 m2' /\ j' = compose_meminj j1' j2'.

Lemma injinj: Sim_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                         (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                        (Genv.globalenv P3) entrypoints13.
Proof.
  destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 
                        core_initial12 core_halted12 core_at_external12 core_after_external12].  
  destruct SimInj23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 
                        core_initial23 core_halted23 core_at_external23 core_after_external23].
  assert (MatchHyp12: forall d12 j12 c1 m1 c2 m2,  match_core12 d12 j12 c1 m1 c2 m2 ->  
                                   forall b1 b2 ofs, j12 b1 = Some (b2,ofs) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2). admit.
  assert (MatchHyp23: forall d23 j23 c2 m2 c3 m3,  match_core23 d23 j23 c2 m2 c3 m3 ->  
                                   forall b1 b2 ofs, j23 b1 = Some (b2,ofs) -> Mem.valid_block m2 b1 /\ Mem.valid_block m3 b2). admit.
  eapply Sim_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 => 
                    match d with (d1,X,d2) => 
                        exists c2, exists m2, exists j1, exists j2, 
                           X=Some c2 /\ j = compose_meminj j1 j2 /\
                           match_core12 d1 j1 c1 m1 c2 m2 /\ match_core23 d2 j2 c2 m2 c3 m3 
                                                                                     
                    end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 
                       core_initial12  core_halted12 core_at_external12 core_after_external12
                       i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12 
                       epts23 entrypoints13 (*Inj_init12*) SimInj12 SimInj23.
                 intros. rename st2 into st3. rename m2 into m3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [j12 [j23 [X [? [MC12 MC23]]]]]]]; subst.
                 eapply (diagram_injinj _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ 
                                        core_diagram12 _ _ _ _ _ core_diagram23); try eassumption.
           (*initial_core*)
                  intros. rename m2 into m3. rename v2 into v3. rename vals2 into vals3. 
                  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  clear core_at_external12 core_halted12 core_diagram12 core_after_external12
                        core_at_external23 core_halted23 core_diagram23 core_after_external23. 
                  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). eapply forall_valinject_hastype; eassumption.
(*assert (WD1: MEM_WD.mem_wd m1). admit.*)
                  assert (X: Mem.inject (Mem.flat_inj (Mem.nextblock m1)) m1 m1 /\ 
                             j = compose_meminj (Mem.flat_inj (Mem.nextblock m1)) j ).
                      split. apply MEM_WD.mem_wd_E.  admit. (*need  MEM_WD.mem_wd m1*) 
                             eapply (MEM_WD.meminj_split_flatinjL _ _ _ H1).  admit. (*need  MEM_WD.mem_wd m1*) 
                  destruct X as [Flat1 XX]. rewrite XX.
                  assert (ValInjFlat1 := forall_val_inject_flat _ _ _ H1 _ _ H2).
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 Flat1 ValInjFlat1 HT) as [d12 [c2 [Ini2 MC12]]].
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2 H3) as [d23 [c3 [Ini3 MC23]]].
                  exists (d12,Some c2,d23). exists c3. 
                  split; trivial. 
                  exists c2. exists m1. exists  (Mem.flat_inj (Mem.nextblock m1)). exists j. 
                  split; trivial. split; trivial. split; assumption.
             (*safely_halted*)
                    intros. rename c2 into c3. rename m2 into m3.  
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [j12 [j23 [X [Y [MC12 MC23]]]]]]]; subst. 
                    apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [ValsInj12 [SH2 Minj12]]].
                    apply (core_halted23 _ _ _ _ _ _ _ MC23) in SH2. destruct SH2 as [v3 [ValsInj23 [SH3 MInj23]]].
                    exists v3. split. apply (val_inject_compose _ _ _ _ _ ValsInj12 ValsInj23).
                          split. trivial. eapply Mem.inject_compose; eassumption.
             (*atexternal*)
                    intros. rename st2 into st3. rename m2 into m3. 
                    destruct cd as [[d12 cc2] d23]. 
                    destruct H as [st2 [m2 [j1 [j2 [Y [J [MC12 MC23]]]]]]]. subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0. 
                      destruct H0 as [MInj12 [PGj1 [vals2 [ValsInj12 [HTVals2 AtExt2]]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2. 
                      destruct AtExt2 as [MInj23 [PGj2 [vals3 [ValsInj23 [HTVals3 AtExt3]]]]].
                    split. eapply Mem.inject_compose; eassumption.
                    split. admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) (compose_meminj j1 j2)meminj_preserves_globals (Genv.globalenv P1) j1  and meminj_preserves_globals (Genv.globalenv P2) j2*)  
                    exists vals3. 
                    split.  eapply forall_val_inject_compose; eassumption.
                    split; assumption.
             (*after_external*) clear core_diagram12 core_initial12 core_halted12 core_diagram23 core_initial23 core_halted23. 
                    intros. rename st2 into st3. rename m2 into m3. rename ret2 into ret3. rename m2' into m3'. 
                    destruct cd as [[d12 cc2] d23]. 
                    destruct H0 as [st2 [m2 [j1 [j2 [Y [J [MC12 MC23]]]]]]]. subst.
                    rename H1 into AtExt1.
                    destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExt1) 
                               as [MInj12 [PGj1 [vals2 [ValsInj12 [HTVals2 AtExt2]]]]].
                    destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2) 
                              as [MInj23 [PGj2 [vals3 [ValsInj23 [HTVals3 AtExt3]]]]].
                    clear core_at_external12 core_at_external23.
                    assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). eapply forall_valinject_hastype; eassumption.
                    assert (HRet1: Val.has_type ret1 (proj_sig_res ef_sig)). eapply valinject_hastype; eassumption.
                    destruct (PO_II _ _ _ _ MInj12 H7 _ _ H3 H8) as [m2' [j1' [j2' [Minj12' [Fwd2' ZZZ]]]]]. subst.
                    specialize (core_after_external12 d12 j1 j1' st1 st2 m1 e vals1 ret1 m1' m2 m2').
                    apply val_inject_compose_split in H6. destruct H6 as [ret2 [RetJ12 RetJ23]].
                    assert (MPG1:meminj_preserves_globals (Genv.globalenv P1) j1). admit. (*meminj_preserves_globals*)
                    specialize  (core_after_external12 ret2 _ MInj12 MC12 AtExt1). 
admit. (*continue here .
xx
specialize (core_after_external12 d12 j1 _ st1 st2 m1 e vals1 ret1 m1' m2).
                    destruct (inj_incr_compose_split _ _ _ H3) as [j1' [j2' [Jinc1 [Jinc2 J']]]]. subst. 
specialize (core_after_external12 cd12 j1 j1' st1 st2 m1 e vals1 ret1 m1' m2 m2').
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
                    exists c1'. exists c3'. exists (d12',d23'). split; trivial. split; trivial. exists c2'. exists m2'.  split; trivial.*)
Admitted.
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
Proof. intros.   destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' Y]]].
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
(*    apply extends_refl.
    inv H4.*)
(*    split. constructor; auto.*)
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
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
            initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
            exists m2 : mem, initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\ m1 = m2)
       (SimEq12 : Sim_eq.Forward_simulation_equals mem (list (ident * globdef F1 V1))
                                          (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                                          (Genv.globalenv P2) epts12) 
       (SimEq23 : Sim_eq.Forward_simulation_equals mem (list (ident * globdef F2 V2))
                                         (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
                                         (Genv.globalenv P3) epts23) .
(*
Let D12:Type:= Sim_eq.core_data SimEq12.
Let D23:Type:= Sim_eq.core_data SimEq23.

  Let data13 := (Sim_eq.core_data SimEq12 * (option C2) * Sim_eq.core_data SimEq23)%type.

  Inductive sem_compose_ord 
      : (*data13 -> data13 -> Prop :=*)
 (prod (prod (Sim_eq.core_data SimEq12) (option C2)) (Sim_eq.core_data SimEq23)) ->
 (prod (prod (Sim_eq.core_data SimEq12) (option C2)) (Sim_eq.core_data SimEq23)) -> Prop :=

    | sem_compose_ord1 :
        forall (d12 d12':Sim_eq.core_data SimEq12) (c2:C2) (d23:Sim_eq.core_data SimEq23),
           Sim_eq.core_ord SimEq12  d12 d12' ->
           sem_compose_ord (d12,Some c2,d23) (d12',Some c2,d23)
    | sem_compose_ord2 :
        forall (d12 d12':Sim_eq.core_data SimEq12) (c2 c2':C2) (d23 d23':Sim_eq.core_data SimEq23),
           Sim_eq.core_ord  SimEq23 d23 d23' ->
           sem_compose_ord (d12,Some c2,d23) (d12',Some c2',d23').
 
  Lemma well_founded_sem_compose_ord: well_founded sem_compose_ord. 
  Proof. 
    intro. destruct a as [[d12 c2] d23].
    revert d12. 
    destruct c2. 
    2: constructor; intros. 2: inv H.
(*    set (q := (d23,c)).
    change d23 with (fst q). change c with (snd q). clearbody q.
    clear d23.*)
   revert c. 
    induction d23 using (well_founded_induction (Sim_eq.core_ord_wf SimEq23)).
    intros.
(*    set (q' := (d12,c)).
    change d12 with (fst q'). change c with (snd q').
    clearbody q'. clear d12 c.*)
    induction d12 using (well_founded_induction (Sim_eq.core_ord_wf SimEq12)).
    constructor; intros. inv H1.
    generalize (H0 d0). simpl. intros.
    apply H1. auto. (* destruct q'; auto.*) 
    generalize (H d1). 
    intros. 
    spec H1. auto. (* destruct q; auto.*)
    apply H1. 
  Qed.
*)
(*
  Lemma well_founded_sem_compose_ord_withmem : well_founded sem_compose_ord.
  Proof.
    intro. destruct a as [[d12 [c2 m]] d23].
    revert d12 m.
    destruct c2.
    2: constructor; intros. 2: inv H.
(*    set (q := (d23,c)).
    change d23 with (fst q). change c with (snd q). clearbody q.
    clear d23 c.*)
   revert c.
    induction d23 using (well_founded_induction (Sim_eq.core_ord_wf SimEq23)).
    intros.
(*    set (q' := (d12,c)).
    change d12 with (fst q'). change c with (snd q').
    clearbody q'. clear d12 c.*)
    induction d12 using (well_founded_induction (Sim_eq.core_ord_wf SimEq12)).
    constructor; intros. inv H1.
    generalize (H0 d12). simpl. intros.
    apply H1. auto. (* destruct q'; auto.*)
    generalize (H d23).
    intros.
    spec H1. auto. (* destruct q; auto.*)
    apply H1.
  Qed.
*)

Lemma eqeq: Sim_eq.Forward_simulation_equals mem (list (ident * globdef F1 V1))
                                       (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                       (Genv.globalenv P3) entrypoints13.
Proof.
         destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
         destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
          eapply Sim_eq.Build_Forward_simulation_equals with
                 (core_data:= prod (prod core_data12 (option C2)) core_data23) 
                 (match_core := fun d c1 c3 => match d with (d1,X,d2) => exists c2, X=Some c2 /\ match_core12 d1 c1 c2 /\ match_core23 d2 c2 c3 end)
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)).
           (*wellfounded*) 
                eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
           (*core_diagram*) 
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12 Eq_init12 SimEq12 SimEq23
                          i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13.
                 intros. destruct d as [[d12 cc2] d23]. destruct H0 as [c2 [X [? ?]]]; subst.
                 eapply (diagram_eqeq _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); eassumption. 
           (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ H0) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
                  destruct (core_initial23 _ _ _ EP23 _ H0) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2,d23). exists c1. exists c3. split; trivial. split; trivial. exists c2. split; trivial. split; trivial.
           (*safely_halted*)
                    intros. rename c2 into c3. destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]. subst.
                    apply (core_halted12 _ _ _ _ MC12) in H0.
                    apply (core_halted23 _ _ _ _ MC23) in H0. assumption.
           (*atexternal*)
                    intros. rename st2 into st3. destruct d as [[d12cc2]  d23]. destruct H as [st2 [X [MC12 MC23]]]; subst.
                    apply (core_at_external12 _ _ _ _ _ _ MC12) in H0. destruct H0.
                    apply (core_at_external23 _ _ _ _ _ _ MC23) in H. assumption.  
          (*after_external*)
                    intros. rename st2 into st3. destruct d as [[d12 cc2] d23]. destruct H as [st2 [X [MC12 MC23]]]; subst.
                    destruct (core_at_external12 _ _ _ _ _ _ MC12 H0)  as [AtExt2 _].
                    destruct (core_after_external12 _ _ _ _ _ _ _ MC12 H0 AtExt2 H2 H3) as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    destruct (core_after_external23 _ _ _ _ _ _ _ MC23 AtExt2 H1 H2 H3) as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists c1'. exists c3'. exists (d12',Some c2',d23'). split; trivial. split; trivial. exists c2'. split; trivial. split; trivial. 
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
(*    apply extends_refl.
    inv H4.*)
(*    split. constructor; auto.*)
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
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
            initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
            exists m2 : mem, initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\ m1 = m2)
       (SimEq12 : Sim_eq.Forward_simulation_equals mem (list (ident * globdef F1 V1))
                                          (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                                          (Genv.globalenv P2) epts12) 
       (SimExt23 : Sim_ext.Forward_simulation_extends (list (ident * globdef F2 V2))
                            (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
                            (Genv.globalenv P3) epts23).

Lemma eqext: Sim_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
                                           (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                           (Genv.globalenv P3) entrypoints13.
Proof.
         destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
         destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
           eapply Sim_ext.Build_Forward_simulation_extends with
                 (match_state := fun d c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, X = Some c2 /\ match_core12 d1 c1 c2 /\ match_core23 d2 c2 m1 c3 m3 end)
                 (core_data:= prod (prod core_data12 (option C2)) core_data23)
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)). 
           (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
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
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ H0 H1 H2) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2,d23). exists c1. exists c3. split; trivial. split; trivial. exists c2. split; trivial. split; trivial.
           (*safely_halted*)
                    intros. rename st2 into c3. destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                    apply (core_halted12 _ _ _ _ MC12) in H0.
                    apply (core_halted23 _ _ _ _ _ _ MC23) in H0. assumption.
           (*atexternal*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H as [st2 [X [MC12 MC23]]].
                    apply (core_at_external12 _ _ _ _ _ _ MC12) in H0. destruct H0.
                    apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in H. assumption.  
           (*after_external*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H as [st2 [X [MC12 MC23]]].
                    destruct (core_at_external12 _ _ _ _ _ _ MC12 H0)  as [AtExt2 _].
                    assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). eapply forall_lessdef_hastype; eauto.
                    assert (HRet1:   Val.has_type ret1 (proj_sig_res ef_sig)). eapply lessdef_hastype; eauto.
                    destruct (core_after_external12 _ _ _ _ _ _ _ MC12 H0 AtExt2 HVals1 HRet1) as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    destruct (core_after_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ MC23 AtExt2 H1 H2 H3 H4 H5 H6 H7 H8 H9) as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists c1'. exists c3'. exists (d12',Some c2',d23'). split; trivial. split; trivial. exists c2'. split; trivial. split; trivial.
Qed.
End EQEXT.

Section EQINJ.
Lemma diagram_eqinj: forall
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
(MC23: match_core23 d23 j st2 m1 st3 m3)
(CSF2: corestep_fwd Sem2)
(CSF3: corestep_fwd Sem3),
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
           split. apply CSF2 in H.
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
(*    apply extends_refl.
    inv H4.*)
(*    split. constructor; auto.*)
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
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
            initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
            exists m2 : mem, initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\ m1 = m2)
       (SimEq12 : Sim_eq.Forward_simulation_equals mem (list (ident * globdef F1 V1))
                                          (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                                          (Genv.globalenv P2) epts12)  (SimInj23 : Sim_inj.Forward_simulation_inject (list (ident * globdef F2 V2))
             (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
             (Genv.globalenv P3) epts23)
       (CSF2: corestep_fwd Sem2) (CSF3: corestep_fwd Sem3).

Lemma eqinj: Sim_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                        (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                        (Genv.globalenv P3) entrypoints13.
Proof.
          destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
         destruct SimInj23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
          eapply Sim_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, X=Some c2 /\ match_core12 d1 c1 c2 /\ match_core23 d2 j c2 m1 c3 m3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
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
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2 H3) as [d23 [c3 [Ini3 MC23]]].
                  exists (d12,Some c2,d23). exists c3. split; trivial. exists c2. auto.
             (*safely_halted*)
                    intros. rename c2 into c3. destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                    apply (core_halted12 _ _ _ _ MC12) in H0.
                    apply (core_halted23 _ _ _ _ _ _ _ MC23) in H0. assumption.
             (*atexternal*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst. 
                    apply (core_at_external12 _ _ _ _ _ _ MC12) in H0. destruct H0.
                    apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in H. 
                    destruct H as [MInj12 [PG2 X]]. 
                    split. trivial. 
                    split; try assumption. 
                    admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) j  from meminj_preserves_globals (Genv.globalenv P2) j for any j*)  
             (*after_external*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H0 as [c2 [X [MC12 MC23]]]; subst.
                    destruct (core_at_external12 _ _ _ _ _ _ MC12 H1)  as [AtExt2 HVals1].
                    assert (HRet1:   Val.has_type ret1 (proj_sig_res ef_sig)). eapply valinject_hastype; eassumption.
                    destruct (core_after_external12 _ _ _ _ _ _ _ MC12 H1 AtExt2 HVals1 HRet1) as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    assert (PG2: meminj_preserves_globals (Genv.globalenv P2) j). admit.
                    destruct (core_after_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ _ H MC23 AtExt2 PG2 H3 H4 H5 H6 H7 H8 H9 H10 H11) as [d23' [c22' [c3' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',Some c2',d23'). exists c1'. exists c3'. split; trivial. split; trivial. exists c2'. auto.
Qed.
End EQINJ.

Lemma cc_trans_CaseEq: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globdef F1 V1)))
     (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globdef F2 V2)))
     (Sem3 : CoreSemantics (Genv.t F3 V3) C3 mem (list (ident * globdef F3 V3)))
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3)
     (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
     (e12 : prog_main P1 = prog_main P2)
     (g12: CompilerCorrectness.GenvHyp P1 P2)
     (Eq_init12 : forall m1 : mem,
          initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
          exists m2 : mem,
            initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\ m1 = m2)
     (SimEq12 : Sim_eq.Forward_simulation_equals mem (list (ident * globdef F1 V1))
                                (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                               (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_sim I ExternIdents epts23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
     (i1: I F1 C1 V1 Sem1 P1)
     (CSF2: corestep_fwd Sem2) (CSF3: corestep_fwd Sem3),
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
         intros m1 Ini1.
           destruct (Eq_init12 _ Ini1) as [m2 [Ini2 XX]]. subst.
           apply (Eq_init23 _ Ini2). 
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
        rename Extends_init into Ext_init23. rename e into e23. rename g into g23. rename R into SimExt23.
                               rename H0 into Extern1. rename H1 into Extern2. rename ePts_ok into ePts23_ok.
                               rename H into EPC. rename i into i2. rename i0 into i3.
       apply CompilerCorrectness.ccs_ext with (entrypoints:=entrypoints13); try assumption.
       (*init_mem*)
         intros m1 Ini1.
           destruct (Eq_init12 _ Ini1) as [m2 [Ini2 XX]]. subst.
           apply (Ext_init23 _ Ini2).
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
         intros m Ini1.
           destruct (Eq_init12 _ Ini1) as [m2 [Ini2 XX]]. subst.
           apply (Inj_init23 _ Ini2).
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
(Ext_init12 : forall m1 : mem,
             initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
             exists m2 : mem,
               initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
               Mem.extends m1 m2)
(SimExt12 : Sim_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
             (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
             (Genv.globalenv P2) epts12)
(SimEq23 : Sim_eq.Forward_simulation_equals mem (list (ident * globdef F2 V2))
            (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
            (Genv.globalenv P3) epts23).

Lemma exteq: Sim_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
                                        (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                       (Genv.globalenv P3) entrypoints13. 
Proof.
      destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
      destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
  eapply Sim_ext.Build_Forward_simulation_extends with 
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, X=Some c2 /\ match_core12 d1 c1 m1 c2 m3 /\ match_core23 d2 c2 c3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12
                          i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13 Ext_init12 SimExt12 SimEq23.
                 intros. rename st2 into st3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [X [? ?]]]; subst. rename m2 into m3.
                 eapply (diagram_exteq _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); try eassumption.
            (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ H0 H1 H2) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
                  destruct (core_initial23 _ _ _ EP23 _ H1) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2, d23). exists c1. exists c3. split; trivial. split; trivial. exists c2. split; trivial. split; trivial.
             (*safely_halted*)
                    intros. rename st2 into c3.  destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst. 
                    apply (core_halted12 _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [LD [SH2 Ext]]].
                    apply (core_halted23 _ _ _ _ MC23) in SH2. exists v2. split; trivial. split; trivial.
             (*atexternal*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [vals2 [Ext [LD [HT2 AtExt2]]]].
                    destruct (core_at_external23 _ _ _ _ _ _ MC23 AtExt2). exists vals2. split; trivial. split; trivial. split; assumption.  
             (*after_external*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                     rename vals2 into vals3. rename ret2 into ret3.
                    assert (X:=core_at_external12 _ _ _ _ _ _ _ _ MC12 H0). destruct X as [vals2 [Ext [LD [HT2 AtExt2]]]].
                    assert (X:=core_at_external23 _ _ _ _ _ _ MC23 AtExt2). destruct X as [AtExt3 HTargs2]. rewrite AtExt3 in H1. inv H1.
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ _ MC12 H0 AtExt2 LD HT2 H4 H5 H6 H7 H8 H9) as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    destruct (core_after_external23 _ _ _ _ _ _ _ MC23 AtExt2 AtExt3 HT2 H9) as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists c1'. exists c3'. exists (d12',Some c2', d23'). split; trivial. split; trivial. exists c2'. split; trivial. split; trivial.
Qed.       
End EXTEQ.

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
    clear MC12 CS1.
    revert d23 st2 st2' m2' m2 st3 m3 MC23 MC12' H.
    induction x; intros. 
      (*base case*) simpl in H.
          destruct H as [c2 [m2'' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ _ MC23) as [st3' [m3' [d23' [? ?]]]].
          exists st3'. exists m3'. exists (d12',Some st2',d23').
          split. exists st2'. exists m2'. split. trivial. split; assumption. 
          destruct H1. left; assumption.
          destruct H1. right. split; trivial.
          apply t_step. constructor 2. apply H2.
     (*inductive case*)
           remember (S x) as x'. simpl in H.
           destruct H as [st2'' [m2'' [? ?]]]. subst x'.
           destruct (core_diagram23 _ _ _ _  H _ _ _ MC23) as [c3' [m3' [d'' [? ?]]]].
           specialize (IHx _ _ _ _ _ _ _ H1 MC12' H0).
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']   [[c2'' [m2'''' [X [MC12'' MC23'']]]] ?]]]]; subst.
           exists c3''. exists m3''. exists (d12''', Some c2'',d23'').
           split. exists c2''. exists m2''''. auto.
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
    split. exists st2'. exists m2'. split. trivial. split; assumption.
(*    apply extends_refl.
    inv H4.*)
(*    split. constructor; auto.*)
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3:Type}
(I : forall F C V : Type,  CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
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
(Ext_init12 : forall m1 : mem,
             initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
             exists m2 : mem,
               initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
               Mem.extends m1 m2)
(SimExt12 : Sim_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
             (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
             (Genv.globalenv P2) epts12)
(SimExt23 : Sim_ext.Forward_simulation_extends (list (ident * globdef F2 V2))
             (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
             (Genv.globalenv P3) epts23).

Lemma extext: Sim_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
                                        (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                       (Genv.globalenv P3) entrypoints13. 
Proof. intros.
      destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
      destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
       eapply Sim_ext.Build_Forward_simulation_extends with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, exists m2, X=Some c2 /\ 
                                                  match_core12 d1 c1 m1 c2 m2 /\ match_core23 d2 c2 m2 c3 m3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12
                          i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13 Ext_init12 SimExt12 SimExt23.
                 intros. rename st2 into st3. rename m2 into m3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [X [? ?]]]]; subst.
                 eapply (diagram_extext _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); try eassumption.
             (*initial_core*)
                  intros. rename m2 into m3. rename vals' into args3. rename vals into args1. rename v2 into v3.
                  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  assert (HT: Forall2 Val.has_type args1 (sig_args sig)). eapply forall_lessdef_hastype; eassumption.
                  destruct (core_initial12 _ _ _ EP12 _ _ m1 _ (forall_lessdef_refl args1) HT (extends_refl _)) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ H0 H1 H2) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2, d23). exists c1. exists c3. split; trivial. split; trivial.
                  exists c2. exists m1. split; trivial. split; trivial.
             (*safely_halted*)
                    intros. rename st2 into c3. rename m2 into m3.  destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    apply (core_halted12 _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [V12 [SH2 Ext12]]].
                    apply (core_halted23 _ _ _ _ _ _ MC23) in SH2. destruct SH2 as [v3 [V23 [SH3 Ext23]]].
                    exists v3. split. eapply Val.lessdef_trans; eassumption.
                       split; trivial. eapply extends_trans; eassumption.
             (*atexternal*)
                    intros. rename st2 into st3. rename m2 into m3. destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [vals2 [Ext12 [LD12 [HT2 AtExt2]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in AtExt2. destruct AtExt2 as [vals3 [Ext23 [LS23 [HT3 AtExt3]]]]. 
                    exists vals3. split.  eapply extends_trans; eassumption.
                       split. eapply forall_lessdef_trans; eassumption.
                        split; assumption.
             (*after_external*)
                    intros. rename st2 into st3. rename m2 into m3. rename m2' into m3'.  rename vals2 into vals3. rename ret2 into ret3. 
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
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
                    exists c1'. exists c3'. exists (d12',Some c2', d23'). split; trivial. split; trivial.
                    exists c2'. exists m2'.  split; trivial. split; trivial.
Qed.
End EXTEXT.

Section EXTINJ.
Lemma  diagram_extinj: forall
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
(BV12: forall b, Mem.valid_block m1 b -> Mem.valid_block m2 b)
(MC12 : match_core12 d12 st1 m1 st2 m2)
(MC23 : match_core23 d23 j st2 m2 st3 m3)
(CSF2: corestep_fwd Sem2)
(CSF3: corestep_fwd Sem3),
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
    clear MC12 CS1.
    revert j d23 st2 st2' m2' m2 st3 m3 MC23 MC12' H BV12.
    induction x; intros. 
      (*base case*) simpl in H.
          destruct H as [c2 [m2'' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ _ _ MC23) as [st3' [m3' [d23' [j' [InjInc [InjSep [? ?]]]]]]].
          exists st3'. exists m3'. exists (d12',Some st2',d23'). exists j'. 
          split; trivial.
          split. intros b. intros. destruct (InjSep _ _ _ H2 H3). split; trivial.
                       intros N. apply H4. eapply BV12; eassumption. (* inv Ext12.  unfold Mem.valid_block.  rewrite <- mext_next.  apply N.*)
          split. exists st2'. exists m2'. split. trivial. split; assumption. 
          destruct H1. left; assumption.
          destruct H1. right. split; trivial.
          apply t_step. constructor 2. apply H2.
     (*inductive case*)
           remember (S x) as x'. simpl in H.
           destruct H as [st2'' [m2'' [? ?]]]. subst x'.
           destruct (core_diagram23 _ _ _ _  H _ _ _ _ MC23) as [c3' [m3' [d'' [j' [InjInc [InjSep [? ?]]]]]]].
           assert (YY:  forall b : block, Mem.valid_block m1 b -> Mem.valid_block m2'' b) .
              intros. clear IHx. apply BV12 in H3. apply CSF2 in H. eapply H. apply H3.
           specialize (IHx _ _ _ _ _ _ _ _ H1 MC12' H0 YY).
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']  [j'' [InjIncr' [InjSep' [[c2'' [m2''' [X [MC12'' MC23'']]]] ?]]]]]]]. subst.
           exists c3''. exists m3''. exists (d12''', Some c2'',d23''). exists j''.
           split. eapply inject_incr_trans; eassumption.
           split. intros b. intros.
                     remember (j' b) as jb.
                     destruct jb; apply eq_sym in Heqjb.
                          destruct p. rewrite (InjIncr' _ _ _ Heqjb) in H5. inv H5. 
                                   destruct (InjSep _ _ _ H4 Heqjb).
                                   split; trivial.
                                   intros N. apply H5. eapply BV12; eassumption. 
                     destruct (InjSep' _ _ _ Heqjb H5).
                                   split; trivial.
                                   intros N. apply H7. 
                                   destruct H2 as [HH | [HH _]].
                                      eapply corestep_plus_fwd. apply CSF3. apply HH. assumption.  
                                      eapply corestep_star_fwd. apply CSF3. apply HH. assumption.  
           split. exists c2''. exists m2'''. auto.
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
    split. exists st2'. exists m2'. split. trivial. split; assumption.
(*    apply extends_refl.
    inv H4.*)
(*    split. constructor; auto.*)
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
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
       (Ext_init12 : forall m1 : mem,
             initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
             exists m2 : mem,
               initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
               Mem.extends m1 m2)
     (SimExt12 : Sim_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
             (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) epts12)
     (SimInj23 : Sim_inj.Forward_simulation_inject (list (ident * globdef F2 V2))
             (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2) (Genv.globalenv P3) epts23)
     (CSF2: corestep_fwd Sem2) (CSF3: corestep_fwd Sem3).

Lemma extinj: Sim_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                         (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                        (Genv.globalenv P3) entrypoints13.
Proof.
         destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
         destruct SimInj23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
          eapply Sim_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, exists m2, X=Some c2 /\ 
                                                  match_core12 d1 c1 m1 c2 m2 /\ match_core23 d2 j c2 m2 c3 m3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12
                          i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13 Ext_init12 SimExt12 SimInj23.
                 intros. rename st2 into st3. rename m2 into m3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [X [? ?]]]]; subst.
                 eapply (diagram_extinj _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); try eassumption.
                     admit. (*need to show orall b : block, Mem.valid_block m1 b -> Mem.valid_block m2 b but have eg match_core12 d12 st1 m1 st2 m2*)
            (*initial_core*)
                  intros. rename v2 into v3. rename vals2 into vals3. rename m2 into m3.
                  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). eapply forall_valinject_hastype; eassumption.
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ ( forall_lessdef_refl _) HT (Mem.extends_refl m1)) as [d12 [c11 [c2 [Ini1 [Ini2 MC12]]]]]. rewrite Ini1 in H0. inv H0.
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2 H3) as [d23 [c3 [Ini3 MC23]]].
                  exists (d12,Some c2, d23). exists c3. split; trivial. exists c2. exists m1. split; trivial. split; trivial.
             (*safely_halted*)
                    intros. rename c2 into c3. rename m2 into m3.
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    apply (core_halted12 _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [LD12 [SH2 Ext12]]].
                    apply (core_halted23 _ _ _ _ _ _ _ MC23) in SH2. destruct SH2 as [v3 [InjV23 [SH3 InjM23]]].
                    exists v3. split. eapply   val_lessdef_inject_compose; eassumption.
                          split. trivial. eapply extends_inject_compose; eassumption.
             (*atexternal*)
                    intros. rename st2 into st3. rename m2 into m3.
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [vals2 [Ext12 [LD12 [HTVals2 AtExt2]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2. destruct AtExt2 as [Inj23 [PG2 [vals3 [InjVals23 [HTVals3 AtExt3]]]]].
                    split. eapply extends_inject_compose; eassumption.
                    split. admit. (*need to prove  meminj_preserves_globals (Genv.globalenv P1) j  from meminj_preserves_globals (Genv.globalenv P2) j for any j*)  
                    exists vals3. 
                    split. eapply forall_val_lessdef_inject_compose; eassumption. 
                    split; assumption.
             (*after_external*)
                    intros. rename st2 into st3. rename m2 into m3. rename ret2 into ret3. rename m2' into m3'. 
                    destruct cd as [[d12 cc2] d23]. destruct H0 as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 H1)  as [vals2 [Ext12 [LDVals12 [HTVals2 AtExt2]]]].
                    destruct (core_at_external23 _ _ _ _ _ _ _ _ _  MC23 AtExt2)  as [Inj23 [PG2 [vals3 [InjVals23 [HTVals3 AtExt3]]]]].
                    assert (HVals1:  Forall2 Val.has_type vals1 (sig_args ef_sig)). eapply forall_lessdef_hastype; eassumption.
                    assert (HRet1:   Val.has_type ret1 (proj_sig_res ef_sig)). eapply valinject_hastype; eassumption.
                    destruct (PUSHOUTS.pushout_EI _ _ _ Ext12 H7) as [m2' [Fwd2' [Ext12' [UnchOn2 X]]]].
                    destruct (X _ H8) as [UnchOn2j Ext23']; clear X.
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ ret1 ret1 _ _ _ MC12 H1 AtExt2 
                            LDVals12 HTVals2 H7 Fwd2' UnchOn2 (Val.lessdef_refl _) Ext12' HRet1) as [c1' [c2' [d12' [AftExt1 [AftExt2 MC12']]]]].
                    assert (UnchOn3 :  mem_unchanged_on (loc_out_of_reach j m2) m3 m3').
                        split; intros; eapply H10; trivial.
                                 eapply extends_loc_out_of_reach; eassumption.
                                 intros. apply H0 in H13. eapply extends_loc_out_of_reach; eassumption.
                    specialize (Ext23' _ Inj23 _ H9 H10 _ H3 H4 H5).
                    assert (Sep23: inject_separated j j' m2 m3).
                         intros b. intros. destruct (H4 _ _ _ H0 H12). split; trivial. intros N. apply H13.  inv Ext12. unfold Mem.valid_block. rewrite mext_next. apply N.
                    destruct (core_after_external23 _ j j' _ _ _ _ vals2 ret1 _ _ _ ret3 _ Inj23 MC23 AtExt2 PG2 H3 Sep23 Ext23' H6 Fwd2'
                             UnchOn2j H9 UnchOn3 H11)  as [d23' [cc2' [c3' [AftExt22 [AftExt3 MC23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',Some c2', d23'). exists c1'. exists c3'. split; trivial. split; trivial.
                    exists c2'. exists m2'.  split; trivial. split; trivial.
Qed.
End EXTINJ.

Lemma cc_trans_CaseExtends: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globdef F1 V1)))
     (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globdef F2 V2)))
     (Sem3 : CoreSemantics (Genv.t F3 V3) C3 mem (list (ident * globdef F3 V3)))
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3)
     (ePts12_ok : CompilerCorrectness.entryPts_ok P1 P2 ExternIdents epts12)
     (e12 : prog_main P1 = prog_main P2)
     (g12: CompilerCorrectness.GenvHyp P1 P2)
     (Ext_init12 : forall m1 : mem,
               initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
               exists m2 : mem,
                 initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
                 Mem.extends m1 m2)
     (SimExt12 :  Sim_ext.Forward_simulation_extends (list (ident * globdef F1 V1))
                                (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                              (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_sim I ExternIdents epts23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
     (i1: I F1 C1 V1 Sem1 P1)
     (CSF2: corestep_fwd Sem2) (CSF3: corestep_fwd Sem3),
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
           apply Eq_init23 in Ini2. destruct Ini2 as [m3 [Ini3 Y]]; subst. exists m3; split; assumption.
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
        rename Extends_init into Ext_init23. rename e into e23. rename g into g23. rename R into SimExt23.
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

(*
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
(*I think in order to ensure that the addresses are good we have to require that function return values
never return pointers that are not in the domain of the returned memory.
Then we can pull in Mem.inject j1' m1' m2' and use mi_representable*)
Admitted. 

Axioms inj_incr_compose_split: forall j1 j2 j',
             inject_incr (compose_meminj j1 j2) j' ->
             exists j1', exists j2',  inject_incr j1 j1' /\ inject_incr j2 j2' /\ j'=compose_meminj j1' j2'.
(*Probably wrong - maybe we can enforce it together with pushout_II? (unlikely...)*)
*)

Section INJEQ.
Lemma  diagram_injeq: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoreSemantics G2 C2 mem D2)
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
(MC23 : match_core23 d23 st2 st3)
(CSF2: corestep_fwd Sem2),
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
           split. eapply (inject_separated_incr_fwd _ _ _ _ _ _  InjSep InjSep'' InjIncr'). apply (CSF2 _ _ _ _ _ H).
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
       (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globdef F2 V2)))
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
               initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
               exists m2 : mem,
                 initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
                 Mem.inject j12 m1 m2)
      (PG1 : meminj_preserves_globals (Genv.globalenv P1) j12)
      (SimInj12 : Sim_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                          (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                          (Genv.globalenv P2) epts12)
      (SimEq23 : Sim_eq.Forward_simulation_equals mem (list (ident * globdef F2 V2))
                          (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2) (Genv.globalenv P3) epts23)
     (CSF2: corestep_fwd Sem2).

Lemma injeq: Sim_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                        (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                        (Genv.globalenv P3) entrypoints13.
Proof. 
  destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
   destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
    eapply Sim_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, X=Some c2 /\
                                                  match_core12 d1 j c1 m1 c2 m3 /\ match_core23 d2 c2 c3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12
                          i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13 Inj_init12 SimInj12 SimEq23.
                 intros. rename st2 into st3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [X [? ?]]]; subst.
                 eapply (diagram_injeq _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); try eassumption.
             (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 H1 H2 H3) as [d12 [c2 [Ini2 MC12]]].
                  destruct (core_initial23 _ _ _ EP23 _ H3) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2,d23). exists c3. split; trivial.
                  exists c2. split; trivial. split; trivial.
             (*safely_halted*)
                    intros. rename c2 into c3.
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                    apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [VInj12 [SH2 MInj12]]].
                    apply (core_halted23 _ _ _ _ MC23) in SH2.
                    exists v2. split; trivial. split; trivial.
             (*atexternal*)
                    intros. rename st2 into st3.
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [Minj12 [PG1j [vals2 [VInj12 [HT2 AtExt2]]]]].
                    destruct (core_at_external23 _ _ _ _ _ _ MC23 AtExt2).
                    split; trivial.
                    split; trivial.
                    exists vals2. split; trivial. split; trivial.
             (*after_external*)
                    intros. rename st2 into st3.
                    destruct cd as [[d12 cc2] d23]. destruct H0 as [c2 [X [MC12 MC23]]]; subst.
                    assert (X:=core_at_external12 _ _ _ _ _ _ _ _ _ MC12 H1). destruct X as [MInj12 [PG1j [vals2 [VInj12 [HT2 AtExt2]]]]].
                    assert (X:=core_at_external23 _ _ _ _ _ _ MC23 AtExt2). destruct X as [AtExt3 HTargs2]. 
                    destruct (core_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ MInj12 MC12 H1 PG1j H3 H4 H5 H6 H7 H8 H9 H10 H11)
                                        as [d12' [c1' [c2' [AftExt1 [AftExt2 MS12']]]]].
                    destruct (core_after_external23 _ _ _ _ _ _ _ MC23 AtExt2 AtExt3 HT2 H11) as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
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
(CSF3 : corestep_fwd Sem3),
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
    clear Y. destruct ZZ as [CS2 | CS2 ord12'].
     (*case1*) 
    destruct CS2.
    clear MC12 CS1.
     revert j j' d23 st2 st2' m2 st3 m1' m3 MC23 MC12' H InjIncr InjSep.
    induction x; intros. 
      (*base case*) simpl in H.
          destruct H as [c2 [m2'' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ _ MC23) as [st3' [m3' [d23' [? ?]]]].
          exists st3'. exists m3'. exists (d12',Some st2',d23'). exists j'. 
          split; trivial.
          split. intros b; intros.
                    destruct (InjSep _ _ _ H2 H3).
                     split; trivial.
                     intros N. apply H5. 
                     assert (MEXT: Mem.extends m2 m3). admit.  (*we need that extends-simulations satisfy match c1 m1 c2 m2 -> Mem.extends m1 m2*)
                         eapply (Mem.valid_block_extends _ _ _  MEXT). apply N.
          split. exists st2'. exists m2'. split. trivial. split. apply MC12'. apply H0.
          destruct H1. left; assumption.
          destruct H1. right. split; trivial.
          apply t_step. constructor 2. apply H2.
     (*inductive case*)
           remember (S x) as x'. simpl in H.
           destruct H as [st2'' [m2'' [? ?]]]. subst x'.
           destruct (core_diagram23 _ _ _ _  H _ _ _ MC23) as [c3' [m3' [d'' [? ?]]]].
           specialize (IHx j' _ _ _ _ _ _ _ _ H1 MC12' H0).
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']  [j'' [InjIncr' [InjSep'' [[c2'' [m2''' [X [MC12'' MC23'']]]] ?]]]]]]].
                apply inject_incr_refl.
                apply inject_separated_same_meminj.
           subst.
           exists c3''. exists m3''. exists (d12''', Some c2'',d23''). exists j''.
           split. eapply inject_incr_trans; eassumption. 
           split. intros b. intros. 
                     remember (j' b) as z.
                     destruct z; apply eq_sym in Heqz.
                          destruct p. specialize (InjIncr' _ _ _ Heqz). rewrite InjIncr' in H5. inv H5.
                                 destruct (InjSep _ _ _ H4 Heqz).
                                 split; trivial.
                                 intros N. apply H6. assert (Mem.extends m2 m3). admit.  (*again we need that extends-simulations satisfy match c1 m1 c2 m2 -> Mem.extends m1 m2*)
                                           eapply (Mem.valid_block_extends _ _ _  H7). apply N.
                     destruct (InjSep'' _ _ _ Heqz H5).
                          split; trivial. intros N. apply H7.
                                   destruct H2 as [HH | [HH _]].
                                      eapply corestep_plus_fwd. apply CSF3. apply HH. assumption.  
                                      eapply corestep_star_fwd. apply CSF3. apply HH. assumption.  
           split. exists c2''. exists m2'''. split. trivial. split. apply MC12''. apply MC23''.
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
    exists st3. exists m3. exists (d12',Some st2',d23). exists j'.
    split. assumption.
    split. intros b; intros.
                    destruct (InjSep _ _ _ H H1).
                     split; trivial.
                     intros N. apply H3. 
                     assert (MEXT: Mem.extends m2' m3). admit.  (*again, we need that extends-simulations satisfy match c1 m1 c2 m2 -> Mem.extends m1 m2*)
                         eapply (Mem.valid_block_extends _ _ _  MEXT). apply N.
    split. exists st2'. exists m2'. split. trivial. split. apply MC12'. apply MC23.
(*    apply extends_refl.
    inv H4.*)
(*    split. constructor; auto.*)
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
       (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globdef F1 V1)))
       (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globdef F2 V2)))
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
(*       (Inj_init12 : forall m1 : mem,
               initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
               exists m2 : mem,
                 initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
                 Mem.inject j12 m1 m2)*)
      (PG1 : meminj_preserves_globals (Genv.globalenv P1) j12)
      (SimInj12 : Sim_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                          (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                          (Genv.globalenv P2) epts12)
      (SimExt23 : Sim_ext.Forward_simulation_extends (list (ident * globdef F2 V2))
                           (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2)
                           (Genv.globalenv P3) epts23)
      (CSF3 : corestep_fwd Sem3).

Lemma injext: Sim_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                               (Genv.globalenv P3) entrypoints13.
Proof.
    destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
    destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
    eapply Sim_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 => match d with (d1,X,d2) => exists c2, exists m2, X = Some c2 /\
                                              match_core12 d1 j c1 m1 c2 m2 /\ match_core23 d2 c2 m2 c3 m3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12  core_halted12 core_at_external12 core_after_external12
                          i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12  epts23 entrypoints13 (*Inj_init12 *) SimInj12 SimExt23.
                 intros. rename st2 into st3. rename m2 into m3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [X [? ?]]]]; subst.
                 eapply (diagram_injext _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ core_diagram12 _ _ _ _ core_diagram23); try eassumption.
           (*initial_core*)
                  intros. rename m2 into m3. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 H1 H2 H3) as [d12 [c2 [Ini2 MC12]]].
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ (forall_lessdef_refl _) H3 (extends_refl m3)) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2,d23). exists c3. split; trivial.
                  exists c2. exists m3. split; trivial. split; assumption.
           (*safely_halted*)
                    intros. rename c2 into c3. rename m2 into m3.
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [V12 [SH2 MInj12]]].
                    apply (core_halted23 _ _ _ _ _ _ MC23) in SH2. destruct SH2 as [v3 [V23 [SH3 Ext23]]].
                    exists v3. split. eapply valinject_lessdef; eassumption. 
                       split; trivial. eapply inject_extends_compose; eassumption.
             (*atexternal*)
                    intros. rename st2 into st3. rename m2 into m3. 
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [Minj12 [PG1j [vals2 [VInj12 [HT2 AtExt2]]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in AtExt2. destruct AtExt2 as [vals3 [Mext23 [LD23 [HT3 AtExt3]]]].
                    split. eapply inject_extends_compose; eassumption.
                    split; trivial. 
                    exists vals3.  split. eapply forall_valinject_lessdef; eassumption.
                        split; assumption.
             (*after_external*)
                    intros. rename st2 into st3. rename m2 into m3. rename m2' into m3'. rename ret2 into ret3. 
                    destruct cd as [[d12 cc2] d23]. destruct H0 as [c2 [m2 [X [MC12 MC23]]]]; subst.
                    destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 H1)  as [Minj12 [PG1j [vals2 [ValsLD12 [HTVals2 AtExt2]]]]].
                    destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)  as [vals3 [MExt23 [ValsLD23 [HTVals3 AtExt3]]]].
                    assert (Sep12: inject_separated j j' m1 m2).
                         intros b; intros. destruct (H4 _ _ _ H0 H12). split; trivial.
                            intros N. apply H14. inv MExt23. unfold Mem.valid_block. rewrite <- mext_next. apply N.
                    destruct (PUSHOUTS.pushout_IE _ _ _ _ Minj12  H7 _ H3 Sep12 H8) as [m2' [Minj12' [Fwd2' [UnchLOORj1_2 MExt23']]]].
                    specialize (MExt23' _ _ MExt23 H9 H10).
                    destruct (core_after_external12 _ j j' _ _ _ _ _ ret1 m1' _ m2' ret3 _ Minj12 MC12 H1 PG1j H3 
                                         Sep12 Minj12' H6 H7 H8 Fwd2' UnchLOORj1_2 H11) as  [d12' [c1' [c2' [AftExt1 [AftExt2 MC12']]]]].
                    assert (UnchLOOB23_3': mem_unchanged_on (loc_out_of_bounds m2) m3 m3'). 
                         eapply inject_LOOR_LOOB; eassumption.
                    destruct (core_after_external23 _ _ _ _ _ _ _ _ ret3 ret3 _ _ _ MC23 AtExt2 AtExt3 ValsLD23 HTVals3 Fwd2'  H9 
                                     UnchLOOB23_3' (Val.lessdef_refl _) MExt23' H11) as [cc2' [c3' [d23' [AftExt22 [AftExt3 MC23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',Some c2', d23'). exists c1'. exists c3'. split; trivial. split; trivial.
                    exists c2'. exists m2'.  split; trivial. split; assumption.
Qed.
End INJEXT.

(*
Section INJINJFULL.

Lemma diagram_injinjfull: forall
(G1 C1 D1 : Type)
(G2 C2 D2 : Type)
(G3 C3 D3 : Type)
(Sem1 : CoreSemantics G1 C1 mem D1)
(Sem2 : CoreSemantics G2 C2 mem D2)
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
  (BV12: forall b1 b2 ofs, j12 b1 = Some (b2,ofs) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
  (BV23: forall b2 b3 ofs, j23 b2 = Some (b3,ofs) -> Mem.valid_block m2 b2 /\ Mem.valid_block m3 b3)
  (MC12 : match_core12 d12 j12 st1 m1 st2 m2)
  (MC23 : match_core23 d23 j23 st2 m2 st3 m3)
  (CSF2 : corestep_fwd Sem2)
  (CSF3 : corestep_fwd Sem3),
   exists st2' : C3,
     exists m2' : mem,
       exists cd' : core_data12 * option C2 * core_data23,
         exists j' : meminj,
           inject_incr (compose_meminj j12 j23) j' /\
           inject_separated (compose_meminj j12 j23) j' m1 m3 /\
           (let (y, d2) := cd' in
            let (d1, X) := y in
            exists c2 : C2,
              exists m0 : mem,
                exists j1 : meminj,
                  exists j2 : meminj,
                    X = Some c2 /\
                    j' = compose_meminj j1 j2 /\
                    match_core12 d1 j1 st1' m1' c2 m0 /\
                    match_core23 d2 j2 c2 m0 st2' m2') /\
           (corestep_plus Sem3 Genv3 st3 m3 st2' m2' \/
            corestep_star Sem3 Genv3 st3 m3 st2' m2' /\
            clos_trans (core_data12 * option C2 * core_data23)
              (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
              (d12, Some st2, d23)).
Proof. intros. 
    destruct (core_diagram12 _ _ _ _ CS1 _ _ _ _ MC12)
          as [st2' [m2' [d12' [j12' [InjIncr12 
                    [InjSep12 [MC12' Y]]]]]]]; clear core_diagram12.
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
    assert (exists mm2, exists jj,
           corestepN Sem2 Genv2 (S x) st2 mm2 st2' m2' /\ 
                       mem_forward m2 mm2 /\
                        match_core23 d23 jj st2 mm2 st3 m3 /\
            inject_incr j23 jj /\
           forall (b2 b3 : block) (ofs : Z),
             jj b2 = Some (b3, ofs) ->
             Mem.valid_block m2 b2 /\ Mem.valid_block m3 b3).
           exists m2. exists j23. split; trivial. 
               split. apply mem_forward_refl. 
               split. trivial. split. apply inject_incr_refl.  auto.
    clear H MC23 BV23.
    destruct H0 as [mm2 [jj [H [Y2 [MC23 [JJ BV23]]]]]]. 
    revert j23 d23 st2 mm2 st3 H Y2 JJ MC23. 
    induction x; intros. 
      (*base case*) simpl in H.
          destruct H as [c2 [m2'' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ _ _ MC23) as [st3' [m3' [d23' [j23' [InjInc23 [InjSep23 [? ?]]]]]]].
          exists st3'. exists m3'. exists (d12',Some st2',d23'). 
          exists (compose_meminj j12' j23').
          split. eapply  compose_meminj_inject_incr; try eassumption.
                  eapply inject_incr_trans; eassumption.
          split. intros b; intros.
                apply compose_meminjD_Some in H3. 
                destruct H3 as [b1 [ofs1 [ofs [Hb [Hb1 DD]]]]]; subst.
                apply compose_meminjD_None in H2.
                destruct H2.
                  destruct (InjSep12 _ _ _ H2 Hb).
                  split; trivial. 
                  remember (j23 b1) as z. 
                  destruct z; apply eq_sym in Heqz.
                     destruct p. specialize (JJ _ _ _ Heqz). 
                         specialize (InjInc23 _ _ _ JJ). 
                         rewrite InjInc23 in Hb1. inv Hb1. 
                         destruct (BV23 _ _ _ Heqz).
                         exfalso. apply (H4 H5).
                  remember (jj b1) as zz.
                  destruct zz; apply eq_sym in Heqzz.
                     destruct p. specialize (InjInc23 _ _ _ Heqzz).
                       rewrite InjInc23 in Hb1. inv Hb1.
                  destruct (InjSep23 _ _ _ Heqz Hb1). apply H6.
                destruct H2 as [b22 [ofs22 [XX YY]]].
                    specialize (InjIncr12 _ _ _ XX). rewrite InjIncr12 in Hb. inv Hb.
                   destruct (InjSep23 _ _ _ YY Hb1).
                    split; trivial. 
                    destruct (BV12 _ _ _ XX).
                    apply Y in H5. exfalso. apply H2. apply H5.
          split. exists st2'. exists m2'. exists j12'. exists j23'.
            auto. 
          destruct H1. left; assumption.
          destruct H1. right. split; trivial.
          apply t_step. constructor 2. apply H2.
     (*inductive case*)
           remember (S x) as x'. simpl in H.
           destruct H as [st2'' [m2'' [? ?]]]. subst x'.
           destruct (core_diagram23 _ _ _ _  H _ _ _ _ MC23) as [c3' [m3' [d23' [j23' [InjInc23 [InjSep23 [? ?]]]]]]]. clear core_diagram23.
           specialize (IHx _ _ _ _ _ H1 MC12' H0).
           assert (BV23': forall (b2 b3 : block) (ofs : Z),
         j23' b2 = Some (b3, ofs) ->
         Mem.valid_block m2 b2 /\ Mem.valid_block m3' b3). 
                clear IHx. intros.
                remember (j23 b2) as z. 
                destruct z; apply eq_sym in Heqz. 
                   destruct p. specialize (InjInc23 _ _ _ Heqz). 
                      rewrite InjInc23 in H3.  inv H3. 
                   destruct (BV23 _ _ _ Heqz). split; trivial. admit. (*by CSF3*)
                destruct (InjSep23 _ _ _ Heqz H3). 
                  split; trivial. 
                  assert (Mem.inject j23' m2'' m3'). admit. (*From H1*)
                  apply (Mem.valid_block_inject_1 _ _ _ _ _ _ H3) in H6.                 apply Y 
                 SearchAbout Mem.inject.  Mem.inject_block_valid_1. 
                  (*by H1*)
           assert (Sep: inject_separated j12 j12' m1 m2'').
              clear IHx. intros b; intros.
              destruct (InjSep12 _ _ _ H3 H4).
              split; trivial.
              intros N. apply H6.
assert (BV12': forall (b1 b2 : block) (ofs : Z), j12' b1 = Some (b2, ofs) ->
                           Mem.valid_block m1' b1 /\ Mem.valid_block m2'' b2).
               intros. apply BV12 in H3. destruct 
               admit. (*from MC
              clear IHx. intros. 
              remember (j12 b1) as z. 
              destruct z; apply eq_sym in Heqz. 
                destruct p. rewrite (InjIncr12 _ _ _ Heqz) in H3. inv H3. destruct (BV12 _ _ _ Heqz).
                split; trivial. eapply CSF2. apply H. apply H4.
                destruct (InjSep12 _ _ _ Heqz H3).
           assert (BV23': forall (b2 b3 : block) (ofs : Z), j23' b2 = Some (b3, ofs) ->
                          Mem.valid_block m2'' b2 /\ Mem.valid_block m3' b3).
              clear IHx. intros. admit. (*From H1: match23 m2'' m3'*) 
           assert (InjSep'': inject_separated j12 j12' m1 m2'').
              clear IHx core_diagram23. intros b; intros. 
                  destruct (InjSep12 _ _ _ H3 H4). split; trivial.
                  remember (j23 b2) as z.
                  destruct z; apply eq_sym in Heqz.
                    destruct p. apply BV23 in Heqz. exfalso. apply H6. apply Heqz.   
                  remember (j23' b2) as zz.
                  destruct zz; apply eq_sym in Heqzz.
                    destruct p. destruct (BV23' _ _ _ Heqzz). apply BV23 in Heqz. exfalso. apply H6. apply Heqz.                  
                  intros N. apply H6.
SearchAbout inject_separated.xx
              remember (j23 b2) as j23b2. 
              destruct j23b2; apply eq_sym in Heqj23b2. 
              (*Some*) destruct p. assert (XX:= InjInc23 _ _ _ Heqj23b2). rewrite H3 in XX. inv XX.
                       destruct (BV23 _ _ _ Heqj23b2).
                       split. eapply CSF2. apply H. apply H4.
                       destruct H2 as [H2 | [H2 _]]. 
                         eapply (corestep_plus_fwd _ CSF3 _ _ _ _ _ H2 _ H5). 
                         eapply (corestep_star_fwd _ CSF3 _ _ _ _ _ H2 _ H5).
              (*None*)  eapply CSF3. apply H. apply H4.
              split; trivial. eapply CSF2. apply H. apply H5.
                  
           assert (YY:  forall b : block, Mem.valid_block m1 b -> Mem.valid_block m2'' b) .
              intros. clear IHx. apply BV12 in H3. apply CSF2 in H. eapply H. apply H3.
           specialize (IHx _ _ _ _ _ _ _ _ H1 MC12' H0 YY).
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']  [j'' [InjIncr' [InjSep' [[c2'' [m2''' [X [MC12'' MC23'']]]] ?]]]]]]]. subst.
           exists c3''. exists m3''. exists (d12''', Some c2'',d23''). exists j''.
           split. eapply inject_incr_trans; eassumption.
           split. intros b. intros.
                     remember (j' b) as jb.
                     destruct jb; apply eq_sym in Heqjb.
                          destruct p. rewrite (InjIncr' _ _ _ Heqjb) in H5. inv H5. 
                                   destruct (InjSep _ _ _ H4 Heqjb).
                                   split; trivial.
                                   intros N. apply H5. eapply BV12; eassumption. 
                     destruct (InjSep' _ _ _ Heqjb H5).
                                   split; trivial.
                                   intros N. apply H7. 
                                   destruct H2 as [HH | [HH _]].
                                      eapply corestep_plus_fwd. apply CSF3. apply HH. assumption.  
                                      eapply corestep_star_fwd. apply CSF3. apply HH. assumption.  
           split. exists c2''. exists m2'''. auto.
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
    split. exists st2'. exists m2'. split. trivial. split; assumption.
(*    apply extends_refl.
    inv H4.*)
(*    split. constructor; auto.*)
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
*)
Qed.

Context {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
       (I :forall F C V : Type, CoreSemantics (Genv.t F V) C mem (list (ident * globdef F V)) -> AST.program F V -> Prop)
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
(*       (Inj_init12 : forall m1 : mem,
               initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
               exists m2 : mem,
                 initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
                 Mem.inject j12 m1 m2)*)
     (SimInj12 : Sim_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
             (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1) (Genv.globalenv P2) epts12)
     (SimInj23 : Sim_inj.Forward_simulation_inject (list (ident * globdef F2 V2))
             (list (ident * globdef F3 V3)) Sem2 Sem3 (Genv.globalenv P2) (Genv.globalenv P3) epts23)
     (CSF2: corestep_fwd Sem2) (CSF3: corestep_fwd Sem3).

Lemma injinj: Sim_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                         (list (ident * globdef F3 V3)) Sem1 Sem3 (Genv.globalenv P1)
                                        (Genv.globalenv P3) entrypoints13.
Proof.
  destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 
                        core_initial12 core_halted12 core_at_external12 core_after_external12].  
  destruct SimInj23 as [core_data23 match_core23 core_ord23 core_ord_wf23 core_diagram23 
                        core_initial23 core_halted23 core_at_external23 core_after_external23].
  eapply Sim_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 => 
                    match d with (d1,X,d2) => 
                        exists c2, exists m2, exists j1, exists j2, 
                           X=Some c2 /\ j = compose_meminj j1 j2 /\
                           match_core12 d1 j1 c1 m1 c2 m2 /\ match_core23 d2 j2 c2 m2 c3 m3 
                                                                                     
                    end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23 
                       core_initial12  core_halted12 core_at_external12 core_after_external12
                       i1 I core_ord_wf23 core_ord_wf12 EXT2 EXT1 EPC e12 g12 ePts12_ok epts12 
                       epts23 entrypoints13 (*Inj_init12*) SimInj12 SimInj23.
                 intros. rename st2 into st3. rename m2 into m3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [j12 [j23 [X [? [MC12 MC23]]]]]]]; subst.
              xx   admit. (*eapply (diagram_injinj _ _ _ _ _ _ _ _ _ Sem1 Sem2 Sem3 core_data12 match_core12 _ _ _ 
                                        core_diagram12 _ _ _ _ core_diagram23); try eassumption.*)
           (*initial_core*)
                  intros. rename m2 into m3. rename v2 into v3. rename vals2 into vals3. 
                  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  clear core_at_external12 core_halted12 core_diagram12 core_after_external12
                        core_at_external23 core_halted23 core_diagram23 core_after_external23.
                  assert (HT: Forall2 Val.has_type vals1 (sig_args sig)). eapply forall_valinject_hastype; eassumption.
(*assert (WD1: MEM_WD.mem_wd m1). admit.*)
                  assert (X: Mem.inject (Mem.flat_inj (Mem.nextblock m1)) m1 m1 /\ 
                             j = compose_meminj (Mem.flat_inj (Mem.nextblock m1)) j ).
                      split. apply MEM_WD.mem_wd_E.  admit. (*need  MEM_WD.mem_wd m1*) 
                             eapply (MEM_WD.meminj_split_flatinjL _ _ _ H1).  admit. (*need  MEM_WD.mem_wd m1*) 
                  destruct X as [Flat1 XX]. rewrite XX.
                  assert (ValInjFlat1 := forall_val_inject_flat _ _ _ H1 _ _ H2).
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 Flat1 ValInjFlat1 HT) as [d12 [c2 [Ini2 MC12]]].
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2 H3) as [d23 [c3 [Ini3 MC23]]].
                  exists (d12,Some c2,d23). exists c3. 
                  split; trivial. 
                  exists c2. exists m1. exists  (Mem.flat_inj (Mem.nextblock m1)). exists j. 
                  split; trivial. split; trivial. split; assumption.
             (*safely_halted*)
                    intros. rename c2 into c3. rename m2 into m3.  
                    destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [j12 [j23 [X [Y [MC12 MC23]]]]]]]; subst. 
                    apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [ValsInj12 [SH2 Minj12]]].
                    apply (core_halted23 _ _ _ _ _ _ _ MC23) in SH2. destruct SH2 as [v3 [ValsInj23 [SH3 MInj23]]].
                    exists v3. split. apply (val_inject_compose _ _ _ _ _ ValsInj12 ValsInj23).
                          split. trivial. eapply Mem.inject_compose; eassumption.
             (*atexternal*)
                    intros. rename st2 into st3. rename m2 into m3. 
                    destruct cd as [[d12 cc2] d23]. 
                    destruct H as [st2 [m2 [j1 [j2 [Y [J [MC12 MC23]]]]]]]. subst.
                    apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0. 
                      destruct H0 as [MInj12 [PGj1 [vals2 [ValsInj12 [HTVals2 AtExt2]]]]].
                    apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2. 
                      destruct AtExt2 as [MInj23 [PGj2 [vals3 [ValsInj23 [HTVals3 AtExt3]]]]].
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
(*Continue here once other pushouts have been proven
                    destruct (inj_incr_compose_split _ _ _ H3) as [j1' [j2' [Jinc1 [Jinc2 J']]]]. subst. 
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
End INJINJ.


Lemma cc_trans_CaseInject: forall {F1 C1 V1 F2 C2 V2 F3 C3 V3} 
     (Sem1 : CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globdef F1 V1)))
     (Sem2 : CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globdef F2 V2)))
     (Sem3 : CoreSemantics (Genv.t F3 V3) C3 mem (list (ident * globdef F3 V3)))
     ExternIdents epts12 epts23 I 
     (P1 : AST.program F1 V1) (P2 : AST.program F2 V2) (P3 : AST.program F3 V3)
     (e12 : prog_main P1 = prog_main P2)
     (g12: CompilerCorrectness.GenvHyp P1 P2)
     (VarsOK1: CompilerCorrectness.externvars_ok P1 ExternIdents)
     (j12 : meminj)
     (ePts12_ok : CompilerCorrectness.entryPts_inject_ok P1 P2 j12 ExternIdents epts12)
     (Inj_init12 : forall m1 : mem,
           initial_mem Sem1 (Genv.globalenv P1) m1 (prog_defs P1) ->
           exists m2 : mem,
             initial_mem Sem2 (Genv.globalenv P2) m2 (prog_defs P2) /\
             Mem.inject j12 m1 m2)
     (PG1: meminj_preserves_globals (Genv.globalenv P1) j12)
     (SimInj12: Sim_inj.Forward_simulation_inject (list (ident * globdef F1 V1))
                                 (list (ident * globdef F2 V2)) Sem1 Sem2 (Genv.globalenv P1)
                                 (Genv.globalenv P2) epts12)
     (SIM23 : CompilerCorrectness.cc_sim I ExternIdents epts23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
     (i1: I F1 C1 V1 Sem1 P1)
     (CSF2: corestep_fwd Sem2) (CSF3: corestep_fwd Sem3),
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
           destruct (Eq_init23 _ Ini2) as [m3 [Ini3 MEq23]]; subst. exists m3; split; assumption.
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
        rename Extends_init into Ext_init23. rename e into e23. rename g into g23. rename R into SimExt23.
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
Qed.         destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12 core_diagram12 core_initial12 core_halted12 core_at_external12 core_after_external12].  
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
(*Continue here once other pushouts have been proven
                    destruct (inj_incr_compose_split _ _ _ H3) as [j1' [j2' [Jinc1 [Jinc2 J']]]]. subst. 
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
        (Sem1: CoreSemantics (Genv.t F1 V1) C1 mem (list (ident * globdef F1 V1)))
        (Sem2: CoreSemantics (Genv.t F2 V2) C2 mem (list (ident * globdef F2 V2)))
        P1 P2 
        (SIM12: CompilerCorrectness.cc_sim I ExternIdents entrypoints12 F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2)
        F3 V3 C3
        (Sem3: CoreSemantics (Genv.t F3 V3) C3 mem (list (ident * globdef F3 V3)))
        entrypoints23 P3 (SIM23:CompilerCorrectness.cc_sim I ExternIdents entrypoints23 F2 C2 V2 F3 C3 V3 Sem2 Sem3 P2 P3)
        (CSF2: corestep_fwd Sem2) (CSF3: corestep_fwd Sem3)
       entrypoints13 (EPC:entrypoints_compose entrypoints12 entrypoints23 entrypoints13),
        In (P1.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  -> 
        In (P2.(prog_main), CompilerCorrectness.extern_func main_sig) ExternIdents  ->
CompilerCorrectness.cc_sim I ExternIdents entrypoints13 F1 C1 V1 F3 C3 V3 Sem1 Sem3 P1 P3.
Proof.
  intros  ExternIdents epts12 I F1 C1 V1 F2 C2 V2 Sem1 Sem2 P1 P2 SIM12.
  induction SIM12; intros F3 V3 C3 Sem3 epts23 P3 SIM23 CSF2 CSF3.
  eapply (cc_trans_CaseEq Sem1 Sem2 Sem3); try assumption.
  eapply (cc_trans_CaseExtends Sem1 Sem2 Sem3); assumption.
  eapply (cc_trans_CaseInject Sem1 Sem2 Sem3) with (j12:=jInit); assumption.
Qed.*)
*)
