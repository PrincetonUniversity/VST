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
Require Import sepcomp.mem_lemmas. (*TODO: Is this import needed?*)
Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.
Require Import sepcomp.rg_forward_simulations.

(*Require Import sepcomp.compiler_correctness_trans. for auxiliary lemmas, like  sem_compose_ord_eq_eq etc*)
Require Import sepcomp.mem_interpolation_defs. (*For definition of my_mem_unchanged_on*)
(*Require Import sepcomp.rg_diagram.*)

Require Import sepcomp.RG_interpolants.
Declare Module RGMEMAX : RGInterpolationAxioms.

Section RGSIM.
Context  (F1 C1 V1 F2 C2 V2:Type)
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
(*
Lemma meminj_preserves_globals_ind_incr:
     forall glob f (PG: meminj_preserves_globals_ind glob f) f' (Inc: inject_incr f f'),
              meminj_preserves_globals_ind glob f'.
Proof.
intros. destruct PG as [PG1 [PG2 PG3]].
assert (G1: forall b : block, fst glob b -> f' b = Some (b, 0)).
   intros. apply Inc. apply (PG1 _ H).
split; trivial.
assert (G2: forall b : block, snd glob b -> f' b = Some (b, 0)).
  intros. apply Inc. apply (PG2 _ H).
split; trivial. intros.
  remember (f b1).
  destruct o; apply eq_sym in Heqo.
    destruct p. rewrite (Inc _ _ _ Heqo) in H0. inv H0. apply (PG3 _ _ _ H Heqo).
  assert (f' b2 = Some (b2, 0)). apply G2. apply H.
Admitted.

Lemma  meminj_preserves_globals_compose_meminj: forall {F1 V1 F2 V2}
               (G1 : Genv.t F1 V1) (G2 : Genv.t F2 V2) j1 j2,
               meminj_preserves_globals G1 j1 ->
               meminj_preserves_globals G2 j2 ->
                meminj_preserves_globals G1 (compose_meminj j1 j2).
Proof.
  intros. destruct H as [PG1 [PG2 PG3]]. destruct H0 as [QG1 [QG2 QG3]].
  split; intros.
Admitted.
  *)

Lemma val_inject_opt_split: forall (v1 v3 : option val) (j12 j23 : meminj),
       val_inject_opt (compose_meminj j12 j23) v1 v3 ->
       exists v2 : option val, val_inject_opt j12 v1 v2 /\ val_inject_opt j23 v2 v3.
Proof. intros.
  unfold val_inject_opt in *.
  destruct v1; destruct v3; try contradiction.
       destruct (val_inject_split _ _ _ _  H) as [v2 [A B]].
       exists (Some v2). split; trivial.
  exists None; split; trivial.
Qed.

Lemma val_inject_opt_hastype: forall (j : meminj) (v v' : option val),
       val_inject_opt j v v' -> 
       forall T : typ, val_has_type_opt' v' T -> val_has_type_opt' v T.
Proof. intros.
  destruct v; destruct v'; try contradiction; simpl in *.
     eapply valinject_hastype; eassumption.
  trivial.
Qed.

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
(*  spec H1. auto. 
  apply H1. *)
Qed.
(*****************************************************************)

Lemma inject_reserve_incr: forall r rr (R: reserve_incr r rr) j,
             reserve_incr (inject_reserve j r) (inject_reserve j rr).
Proof. intros. intros b; intros. 
   destruct H as [b1 [delta [J H]]].
   exists b1. exists delta. specialize (R _ _ H).
   auto.
Qed.

Lemma reserve_incr_refl: forall r, reserve_incr r r.
Proof. intros r b; auto. Qed.

Lemma reserve_separated_same: forall r j m1 m2,
    reserve_separated r r j m1 m2.
Proof. intros r j m1 m2 b; intros. contradiction. Qed.

Lemma reserve_incr_mono: forall j j'
              (Inc : inject_incr j j') m1 m2
              (Sep : inject_separated j j' m1 m2) r
              (RV : reserve_valid r m1) r'
              (Rinc : reserve_incr (inject_reserve j r) r'),
       reserve_incr (inject_reserve j' r) r'.
Proof. intros. intros b; intros. apply Rinc. 
                  destruct H as [b1 [delta [HJ HR]]].
                  exists b1. exists delta. split; trivial. 
                  remember (j b1) as q.
                  destruct q; apply eq_sym in Heqq. 
                          destruct p. rewrite (Inc _ _ _ Heqq) in HJ. apply HJ.
                  exfalso. specialize (RV _ _ HR). 
                               destruct (Sep _ _ _ Heqq HJ). apply (H RV).
Qed.
(*
Lemma guarantee_inject_reserve_mono: 
  forall {G C D}(Sem: EffectfulSemantics G C D)
              j r c m2 (Guar: guarantee Sem (inject_reserve j r) c m2)
              j'   (Inc : inject_incr j j') m1
              (Sep : inject_separated j j' m1 m2) 
              (RV : reserve_valid r m1) m2',
             guarantee Sem (inject_reserve j' r) c m2'.
Proof. intros.
  intros b; intros. 
  destruct H0 as [b1 [delta [J R]]]. 
  
apply Guar; try assumption.
  exists b1. exists delta. split; trivial.
  remember (j b1) as q; destruct q; apply eq_sym in Heqq.
     destruct p. rewrite (Inc _ _ _ Heqq) in J. apply J.
  destruct (Sep _ _ _ Heqq J). exfalso. apply (H2 H).
Qed.*)

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
(*  destruct RG as [match_state_runnable12 match_state_inj12
           match_state_preserves_globals12 rely12].*)
  rename R into R12.
(*  destruct R as [core_ord_wf12 core_diagram12 core_initial12 core_halted12
            core_at_external12 core_after_external12].*)
  induction SIM23.
  rename cd into cd23. rename matchstate into matchstate23. rename coreord into coreord23.

  rename RG into RG23.
(*  destruct RG as [match_state_runnable23 match_state_inj23 
           match_state_preserves_globals23 rely23].*)
  rename R into R23.
(*  destruct R as [core_ord_wf23 core_diagram23 core_initial23 core_halted23
            core_at_external23 core_after_external23].*)

  specialize (Forward_simulation_inj_exposed.core_diagramN R12).
  specialize (Forward_simulation_inj_exposed.core_diagramN R23).
  intros Diag23 Diag12. Locate sim_inj.
  eapply sim_inj with
    (coreord := sem_compose_ord_eq_eq coreord12 (clos_trans _ coreord23) C2)
    (matchstate := fun d r j c1 m1 c3 m3 => 
      match d with (d1,X,d2) => 
        exists c2, exists m2, exists j1, exists j2, exists r2,
          X=Some c2 /\ j = compose_meminj j1 j2 /\ 
          r2 = inject_reserve j1 r /\
          matchstate12 d1 r j1 c1 m1 c2 m2 /\ matchstate23 d2 r2 j2 c2 m2 c3 m3 /\
          (guarantee Sem1 r c1 m1 /\  guarantee Sem2 r2 c2 m2 /\  
               guarantee Sem3 (inject_reserve j2 r2) c3 m3)
      end).
    (*RG*) clear R12 R23.
         destruct RG12 as [match_state_runnable12 match_state_inj12
                                        match_state_preserves_globals12].
         destruct RG23 as [match_state_runnable23 match_state_inj23 
                                         match_state_preserves_globals23 ].
        econstructor; intros.
        (*match_state_runnable*) 
              destruct cd as [[d1 d2] d3]. rename c2 into c3. rename m2 into m3.
              destruct H as [c2 [m2 [j1 [j2 [r2 [? [J [R [MS12 [MS23 Guar12]]]]]]]]]]; subst.
              rewrite (match_state_runnable12 _ _ _ _ _ _  _ MS12).
              apply (match_state_runnable23 _ _ _ _ _ _ _ MS23).
        (*match_state_inj*) 
              destruct cd as [[d1 d2] d3]. rename c2 into c3. rename m2 into m3.
              destruct H as [c2 [m2 [j1 [j2 [r2 [? [J [R [MS12 [MS23 Guar12]]]]]]]]]]; subst.
              eapply Mem.inject_compose.
                 apply (match_state_inj12 _ _ _ _ _ _ _ MS12).
                 apply (match_state_inj23 _ _ _ _ _ _ _ MS23).
         (*match_state_preserves_globals*)
              destruct cd as [[d1 d2] d3]. rename c2 into c3. rename m2 into m3.
              destruct H as [c2 [m2 [j1 [j2 [r2 [? [J [R [MS12 [MS23 Guar12]]]]]]]]]]; subst.
              specialize (match_state_preserves_globals12 _ _ _ _ _ _ _ MS12).
              specialize (match_state_preserves_globals23 _ _ _ _ _ _ _ MS23).
              admit. (*eapply meminj_preserves_globals_compose_meminj. assumption. eassumption.*)
  destruct R12
    as [core_ord_wf12 match_memwd12 res_valid12  
           effects_valid12 allocs_shrink12 match_antimono12
           match_validblocks12 core_diagram12 core_initial12
           core_halted12 core_at_external12 core_after_external12].  
  destruct R23 
    as [core_ord_wf23 match_memwd23  res_valid23
           effects_valid23 allocs_shrink23 match_antimono23
           match_validblocks23 core_diagram23 core_initial23
           core_halted23 core_at_external23 core_after_external23].  
  constructor. (*
  eapply Coop_forward_simulation_inj.Build_Forward_simulation_inject with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d j c1 m1 c3 m3 => 
      match d with (d1,X,d2) => 
        exists c2, exists m2, exists j1, exists j2, 
          X=Some c2 /\ j = compose_meminj j1 j2 /\
          match_core12 d1 j1 c1 m1 c2 m2 /\ match_core23 d2 j2 c2 m2 c3 m3 
      end).*)
 (*well_founded*)
     eapply well_founded_sem_compose_ord_eq_eq.
         assumption.
         eapply wf_clos_trans. assumption. 
 (*match_memwd*)
    clear core_diagram12 core_initial23  core_halted23 core_at_external23 core_after_external23 
      core_initial12  core_halted12 core_at_external12 core_after_external12
      core_diagram23 core_ord_wf23 core_ord_wf12 res_valid12 res_valid23
      match_antimono12 match_antimono23 effects_valid12 effects_valid23
      allocs_shrink12 allocs_shrink23 match_validblocks12 match_validblocks23.
    clear Diag12 Diag23.
    intros. 
    destruct cd as [[d12 cc2] d23]. rename c2 into st3. rename m2 into m3.
    destruct H as [c2 [m2 [j1 [j2 [r2 [? [J [R [MS12 [MS23 Guar12]]]]]]]]]]; subst.
    clear entrypoints12 entrypoints23 entrypoints13 EPC.
    split. apply (match_memwd12 _ _ _ _ _ _ _ MS12).
    apply (match_memwd23 _ _ _ _ _ _ _ MS23).
  (*reserve_valid*) 
     clear core_diagram12 core_initial23  core_halted23 core_at_external23 core_after_external23 
       core_initial12  core_halted12 core_at_external12 core_after_external12
       core_diagram23 core_ord_wf23 core_ord_wf12  match_validblocks12 (*match_validblocks23*)
       match_antimono12 match_antimono23 effects_valid12 effects_valid23
       allocs_shrink12 allocs_shrink23 match_memwd12 match_memwd23.
     clear Diag12 Diag23.
     intros. rename c2 into c3. rename m2 into m3.
     destruct cd as [[d12 cc2] d23].
     destruct H as [c2 [m2 [j1 [j2 [r2 [? [J [R [MS12 [MS23 Guar12]]]]]]]]]]; subst.
     clear entrypoints12 entrypoints23 entrypoints13 EPC.
     split. apply (res_valid12 _ _ _ _ _ _ _ MS12).
     intros b3; intros.
     destruct H as [b1 [delta [Comp R]]].
     destruct (compose_meminjD_Some _ _ _ _ _ Comp) as [bb [delta2 [delta3 [J1 [J2 XX]]]]].         
     subst; clear Comp.
     apply (match_validblocks23 _ _ _ _ _ _ _ MS23 _ _ _ J2).
 (*effects_valid*)
     clear core_diagram12 core_initial23  core_halted23 core_at_external23 core_after_external23 
        core_initial12  core_halted12 core_at_external12 core_after_external12
        core_diagram23 core_ord_wf23 core_ord_wf12  match_validblocks12 match_validblocks23
        match_antimono12 match_antimono23 res_valid12 res_valid23
        allocs_shrink12 allocs_shrink23 match_memwd12 match_memwd23.
     clear Diag12 Diag23.
      intros. 
      destruct cd as [[d12 cc2] d23]. rename c2 into c3. rename m2 into m3.
      destruct H as [c2 [m2 [j1 [j2 [r2 [? [J [R [MS12 [MS23 Guar12]]]]]]]]]]; subst.
      clear entrypoints12 entrypoints23 entrypoints13 EPC.
      split. eapply (effects_valid12 _ _ _ _ _ _ _ MS12). 
                eapply (effects_valid23 _ _ _ _ _ _ _ MS23).
 (*allocs_atmost_shrink*)
    clear core_diagram12 core_initial23  core_halted23 core_at_external23 core_after_external23 
      core_initial12  core_halted12 core_at_external12 core_after_external12
      core_diagram23 core_ord_wf23 core_ord_wf12  match_validblocks12 match_validblocks23
      match_antimono12 match_antimono23 res_valid12 res_valid23
      effects_valid12 effects_valid23 match_memwd12 match_memwd23.
   clear Diag12 Diag23.
      intros. 
      destruct cd as [[d12 cc2] d23]. rename st2 into st3. rename m2 into m3.
      destruct H as [st2 [m2 [j1 [j2 [r2 [? [J [R [MS12 [MS23 Guar12]]]]]]]]]]; subst.
      clear entrypoints12 entrypoints23 entrypoints13 EPC.
     destruct (compose_meminjD_Some _ _ _ _ _ H1) as [bb [delta2 [delta3 [J1 [J2 XX]]]]].         
     subst; clear H1.
      specialize (allocs_shrink23 _ _ _ _ _ _ _ MS23 _ _ H0 _ _ J2). 
      specialize (allocs_shrink12 _ _ _ _ _ _ _ MS12 _ _ allocs_shrink23 _ _ J1). 
      assert (Arith: ofs2 - delta3 - delta2 = ofs2 - (delta2 + delta3)) by omega.
      rewrite Arith in allocs_shrink12; assumption.
 (*antimono*)
    clear core_diagram12 core_initial23  core_halted23 core_at_external23 core_after_external23 
       core_initial12  core_halted12 core_at_external12 core_after_external12
       core_diagram23 core_ord_wf23 core_ord_wf12  match_validblocks12 match_validblocks23
       allocs_shrink12 allocs_shrink23 (*res_valid12 res_valid23*)
       effects_valid12 effects_valid23 match_memwd12 match_memwd23.
    clear Diag12 Diag23.
    intros cd r rr. intros.
    rename m into m1. rename st into st1.
    rename m' into m3. rename st' into st3.
    destruct cd as [[d12 cc2] d23].
    destruct H as [st2 [m2 [j1 [j2 [r2 [? [J [R [MS12 [MS23 [Guar1 [Guar2 Guar3]]]]]]]]]]]]; subst.
    clear entrypoints12 entrypoints23 entrypoints13 EPC.
    exists st2. exists m2. exists j1. exists j2. exists  (inject_reserve j1 r) .
    split; trivial.
    split; trivial.
    split; trivial.
    split. apply (match_antimono12 _ _ _ _ _ _ _ _ MS12 H0).
    split. apply (match_antimono23 _ _ _ _ _ _ _ _ MS23).
              apply (inject_reserve_incr _ _ H0).
    split.  intros b1; intros. apply Guar1. apply H. apply H0. apply H1. apply H2.
    split. intros b2; intros. apply Guar2. apply H.
                              eapply reserve_incr_mono with (m1:=m1)(m2:=m2); try eassumption. 
                                   apply inject_incr_refl.
                                   apply inject_separated_same_meminj.  
                                   intros b; intros. eapply (res_valid12 _ _ _ _ _ _ _ MS12).
                                                  apply H0. apply H3. 
               intros b; intros. eapply inject_reserve_incr. apply H0. apply H3.
              assumption.
     intros b3; intros. apply Guar3; try assumption.
               subst; simpl in *. destruct H1 as [b2 [delta3 [J2 R2]]].
                         destruct R2 as [b1 [delta2 [J1 R]]].
                         exists b2. exists delta3; split; trivial.
                         exists b1. exists delta2. split; trivial. apply H0. apply R.
         
(*
 (*              eapply Guar12; try assumption. unfold guarantee in H.*)
                  destruct H2 as [b1 [delta2 [J1 HR]]].
                  apply Guar12; try assumption. clear Guar12.
                      
                 exists b1. exists delta2. apply H0 in HR. auto.
                  apply H. apply H4. 
                           assert (forall b ofs, {r b ofs}+{~r b ofs}). admit. (*TODO*) 
                           destruct (X b ofs0); trivial.
                           destruct (
 
                  destruct H2 as [b1 [delta2 [J1 HR]]]. apply H0 in HR.
                       intros bb. exists b1.
 
 assert (GR: guarantee_right Sem1 j1 r st b ofs). 
                    destruct H as [b1 [delta [J GG]]].
                    exists b1. exists delta.  split; trivial.
                    destruct GG. split; trivial. apply H0. apply H.
                 destruct H as [b1 [delta [J GL]]]. destruct GL as [R NO]. 
                        split.
                         exists b1. exists delta. split; trivial.
                      intros N. apply NO; clear NO.
                         apply (match_own12 _ _ _ _ _ _ _ MS12 _ _ N _ _  J).*)
 (*valid_blocks*)
    clear core_diagram12 core_initial23  core_halted23 core_at_external23 core_after_external23 
      core_initial12  core_halted12 core_at_external12 core_after_external12
      core_diagram23 core_ord_wf23 core_ord_wf12  match_antimono12 match_antimono23
      allocs_shrink12 allocs_shrink23 res_valid12 res_valid23
      effects_valid12 effects_valid23 match_memwd12 match_memwd23.
    clear Diag12 Diag23.
    intros. rename c2 into st3. rename m2 into m3. rename b2 into b3.
    destruct d as [[d12 cc2] d23].
    destruct H as [c2 [m2 [j1 [j2 [r2 [? [J [R [MS12 [MS23 Guar12]]]]]]]]]]; subst.
    clear entrypoints12 entrypoints23 entrypoints13 EPC.
    destruct (compose_meminjD_Some _ _ _ _ _ H0)
        as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]]. subst; clear H0.
    split. apply (match_validblocks12 _ _ _ _ _ _ _ MS12 _ _ _ J1).
    apply (match_validblocks23 _ _ _ _ _ _ _ MS23 _ _ _ J2).  
 (*core_diagram*)
  clear core_initial23  core_halted23 core_at_external23 core_after_external23 
     core_initial12  core_halted12 core_at_external12 core_after_external12
     core_ord_wf23 core_ord_wf12 match_memwd12 match_memwd23.
  intros. rename st2 into st3. rename m2 into m3. rename H into CS.
  destruct cd as [[d12 cc2] d23].
  destruct H1 as [c2 [m2 [j1 [j2 [r2 [? [J [R [MS12 [MS23 [Guar1 [Guar2 Guar3]]]]]]]]]]]]; subst.
  clear entrypoints12 entrypoints23 entrypoints13 EPC.
  clear Diag12.
  specialize (core_diagram12 _ _ _ _ CS _ _ _ _ _ H0 MS12).
  destruct core_diagram12 as [st2' [m2' [cd12' [r12' [j12
      [Inc12 [Sep12 [Rinc12 [Rsep12 [Guar2' [MS12' X12]]]]]]]]]]]. 
  destruct X12 as [X12 | [X12 ORD12]]; destruct X12 as [n X12].
  (*Case 1*)
    remember  (inject_reserve j1 r) as rrr. 
    assert (rrr_dec: forall b ofs, {rrr b ofs}+{~rrr b ofs}).
        intros; subst. unfold inject_reserve. admit.
   assert (GUAR2: guarantee Sem2 (Build_reserve' rrr rrr_dec) st2' m2').
          clear - Guar2' rrr. apply Guar2'.
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
                    as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]]. subst; clear Comp.
                eapply Guar3'. apply H.
                      exists b2. exists delta3. split; trivial. simpl.
                         exists b1. exists delta2. split; trivial.
                            assert (Arith: ofs - (delta2 + delta3) = ofs - delta3 - delta2) by omega.
                            rewrite Arith in HR; assumption.
                 apply H2.
                
     split. exists st2'. exists m2'. exists j12. exists j23.
             exists  (inject_reserve j12 r). (* r23'.*)
             split; trivial.
             split; trivial.
             split; trivial.
             split. apply (match_antimono12 _ _ _ _ _ _ _ _ MS12'). assumption. 
             split. apply (match_antimono23 _ _ _ _ _ _ _ _ MS23').
                  simpl in *. subst. 
                  destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [RV _].
                  clear - Rinc23 Inc12 Sep12 RV.
                  apply (reserve_incr_mono _ _ Inc12 _ _ Sep12 _ RV _ Rinc23). 
             split. apply H0.
             split; subst; simpl in *. intros b2; intros. destruct H1 as [b1 [delta2 [J R]]].
                        apply Guar2'; trivial.
                        exists b1. exists delta2. split; trivial.
                        remember (j1 b1) as q; destruct q; apply eq_sym in Heqq.
                            destruct p. rewrite (Inc12 _ _ _ Heqq) in J. apply J.
                        exfalso. destruct (Sep12 _ _ _ Heqq J) as [NV1 _].
                                       apply NV1; clear NV1.
                                       destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 _].
                                       apply (VAL1 _ _ R). 
              intros b3; intros. destruct H1 as [b2 [delta3 [J2 R2]]].
                        assert (IR: inject_reserve j1 r b2 (ofs - delta3)).
                                       destruct R2 as [b1 [delta2 [J1 R]]].
                                       exists b1. exists delta2.
                                       split; trivial.
                                       remember (j1 b1) as w; destruct w; apply eq_sym in Heqw. 
                                                      destruct p. rewrite (Inc12 _ _ _ Heqw) in J1. apply J1.
                                             exfalso. destruct (Sep12 _ _ _ Heqw J1) as [NV1 _].
                                                apply NV1; clear NV1.
                                                destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 VAL2].
                                                apply (VAL1 _ _ R).
                        apply Guar3'; trivial.
                        exists b2. exists delta3. split; trivial.
                        remember (j2 b2) as q; destruct q; apply eq_sym in Heqq.
                            destruct p. rewrite (Inc23 _ _ _ Heqq) in J2. apply J2.
                        exfalso. destruct (Sep23 _ _ _ Heqq J2) as [NV2 _].
                                       apply NV2; clear NV2.
                                       destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 VAL2].
                                       eapply (VAL2 _  (ofs - delta3) IR).
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
                         exists b1. exists delta2. split; trivial.
                            assert (Arith: ofs - (delta2 + delta3) = ofs - delta3 - delta2) by omega.
                            rewrite Arith in HR; assumption.
                 apply H2.
         split. exists st2'. exists m2'. exists j12. exists j2.
                 exists (inject_reserve j12 r).
                 split; trivial.
                 split; trivial.
                 split; trivial.
                 split. apply (match_antimono12 _ _ _ _ _ _ _ _ MS12'). assumption. 
                 split. apply (match_antimono23 _ _ _ _ _ _ _ _ MS23). 
                    destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [RV _].
                    clear - Inc12 Sep12 RV.
                    intros b; intros.
                    destruct H as [b1 [delta [HJ HR]]].
                    exists b1. exists delta. split; trivial. 
                    remember (j1 b1) as q.
                    destruct q; apply eq_sym in Heqq. 
                            destruct p. rewrite (Inc12 _ _ _ Heqq) in HJ. apply HJ.
                    exfalso. specialize (RV _ _ HR). 
                                 destruct (Sep12 _ _ _ Heqq HJ). apply (H RV).
                 split. assumption.
                 split. intros b2; intros. apply Guar2; try eassumption.
                      destruct H1 as [b1 [delta2 [J R]]]. 
                      assert (J1: j1 b1 = Some (b2,delta2)).        
                            remember (j1 b1) as q; destruct q; apply eq_sym in Heqq.
                                destruct p. rewrite (Inc12 _ _ _ Heqq) in J. apply J.
                            exfalso. destruct (Sep12 _ _ _ Heqq J) as [NV1 _].
                                           apply NV1; clear NV1.
                                            destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 _].
                                            apply (VAL1 _ _ R). 
                      exists b1. exists delta2. split; trivial. 
                  intros b3; intros. apply Guar3; try eassumption.
                      destruct H1 as [b2 [delta3 [J2 R2]]].
                      exists b2. exists delta3. split; trivial.
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
    remember  (inject_reserve j1 r) as rrr. 
    assert (rrr_dec: forall b ofs, {rrr b ofs}+{~rrr b ofs}).
        intros; subst. unfold inject_reserve. admit.
   assert (GUAR2: guarantee Sem2 (Build_reserve' rrr rrr_dec) st2' m2').
          clear - Guar2' rrr. apply Guar2'.
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
                    as [b2 [delta2 [delta3 [J1 [J2 ZZ]]]]]. subst; clear Comp.
                eapply Guar3'. apply H.
                      exists b2. exists delta3. split; trivial. simpl.
                         exists b1. exists delta2. split; trivial.
                            assert (Arith: ofs - (delta2 + delta3) = ofs - delta3 - delta2) by omega.
                            rewrite Arith in HR; assumption.
                 apply H2.
                
     split. exists st2'. exists m2'. exists j12. exists j23.
             exists  (inject_reserve j12 r). (* r23'.*)
             split; trivial.
             split; trivial.
             split; trivial.
             split. apply (match_antimono12 _ _ _ _ _ _ _ _ MS12'). assumption. 
             split. apply (match_antimono23 _ _ _ _ _ _ _ _ MS23').
                  simpl in *. subst. 
                  destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [RV _].
                  clear - Rinc23 Inc12 Sep12 RV.
                  apply (reserve_incr_mono _ _ Inc12 _ _ Sep12 _ RV _ Rinc23). 
             split. apply H0.
             split; subst; simpl in *. intros b2; intros. destruct H1 as [b1 [delta2 [J R]]].
                        apply Guar2'; trivial.
                        exists b1. exists delta2. split; trivial.
                        remember (j1 b1) as q; destruct q; apply eq_sym in Heqq.
                            destruct p. rewrite (Inc12 _ _ _ Heqq) in J. apply J.
                        exfalso. destruct (Sep12 _ _ _ Heqq J) as [NV1 _].
                                       apply NV1; clear NV1.
                                       destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 _].
                                       apply (VAL1 _ _ R). 
              intros b3; intros. destruct H1 as [b2 [delta3 [J2 R2]]].
                        assert (IR: inject_reserve j1 r b2 (ofs - delta3)).
                                       destruct R2 as [b1 [delta2 [J1 R]]].
                                       exists b1. exists delta2.
                                       split; trivial.
                                       remember (j1 b1) as w; destruct w; apply eq_sym in Heqw. 
                                                      destruct p. rewrite (Inc12 _ _ _ Heqw) in J1. apply J1.
                                             exfalso. destruct (Sep12 _ _ _ Heqw J1) as [NV1 _].
                                                apply NV1; clear NV1.
                                                destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 VAL2].
                                                apply (VAL1 _ _ R).
                        apply Guar3'; trivial.
                        exists b2. exists delta3. split; trivial.
                        remember (j2 b2) as q; destruct q; apply eq_sym in Heqq.
                            destruct p. rewrite (Inc23 _ _ _ Heqq) in J2. apply J2.
                        exfalso. destruct (Sep23 _ _ _ Heqq J2) as [NV2 _].
                                       apply NV2; clear NV2.
                                       destruct (res_valid12 _ _ _ _ _ _ _ MS12) as [VAL1 VAL2].
                                       eapply (VAL2 _  (ofs - delta3) IR).
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
    match_antimono12 Diag12 Diag23.
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
  assert (RMapValID: reserve_valid_right r (Mem.flat_inj (Mem.nextblock m1)) m1).
       intros b1; intros. destruct H as [b [delta [J R]]]. 
            apply flatinj_E in J. apply J.
  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ _ H0 Flat1 WD1 WD1 
       ValInjFlat1 HT H6 RMapValID)
    as [d12 [c2 [Ini2 MC12]]].

  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _ _ Ini2 H1 WD1 WD3 H4 H5 H6 H7)
    as [d23 [c3 [Ini3 MC23]]].
  exists (d12,Some c2,d23). exists c3. 
  split; trivial. 
  exists c2. exists m1. exists  (Mem.flat_inj (Mem.nextblock m1)). exists j.
  exists (inject_reserve (Mem.flat_inj (Mem.nextblock m1)) r).
  split; trivial.
  split; trivial.
  split; trivial.
  split; trivial.
  split. apply (match_antimono23 _ _ _ _ _ _ _ _ MC23).
        intros b; intros. destruct H as [b1 [delta [J X]]].
              destruct (flatinj_E _ _ _ _ J) as [? [? ?]]. clear XX. subst.
              rewrite Zminus_0_r in X. apply X. 
  split. admit. (* TODO*) 
  split. admit. (* TODO*) 
  admit. (* TODO*) 
(*  intros. destruct H as [b1 [delta [Flat [GL1 GL2]]]].
        split. 
            exists b1. exists delta. split; trivial.
        destruct (flatinj_E _ _ _ _ Flat)  as [? [? ?]]. clear XX. subst.
            intros N. apply GL2.   
            apply (match_own12 _ _ _ _ _ _ _ MC12 _ _ N _ _ Flat).*)
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
assert (Core_after12: forall (cd : cd12) (r : reserve')
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
                   forall (r':reserve'),
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
assert (Core_after23: forall (cd : cd23) (r : reserve')
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
                   forall (r': reserve'),
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
    clear core_after_external23. Locate inject_reserve. 

  assert (Dec1: forall b ofs, {inject_reserve j1 r b ofs} + {~inject_reserve j1 r b ofs}). admit.
  assert (myMC23 : matchstate23 d23 (Build_reserve' (inject_reserve j1 r) Dec1) j2 st2 m2 st3 m3).
                   simpl. apply MC23.
  clear MC23. rename myMC23 into MC23.

    specialize (Core_after23 _ _ _ _ _ _ _ MC23 PGj2).
    specialize (Core_after23 _ _ _ AtExt2 ValsValid2). 
  specialize  (RGMEMAX.interpolate_II Sem1 Sem2 _ _ _
             MInj12 _ Fwd1 _ _ MInj23 _ Fwd3 _ MInj13' Inc
             Sep WD1 WD1' WD2 WD3 WD3'); intros IP.

  specialize (IP st1 _ _ st2 Rinc Rsep Rely1). unfold rely in IP. xx Unch1 Unch3).
  destruct IP as [m2' [j12' [j23' [J' [Inc12 [Inc23 [MInj12' [Fwd2 
                   [MInj23' [Sep12 [Sep23 [WD2' [RSEP12' XXX]]]]]]]]]]]]].

  destruct XXX as [r23 [UnchR2 [UnchL2 [UnchR3 R]]]]; subst.
  
  assert (exists ret2, val_inject_opt j12' ret1 ret2 /\ val_inject_opt j23' ret2 ret3 /\
              val_has_type_opt' ret2 (proj_sig_res (ef_sig e))).
      subst. apply val_inject_opt_split in H11. destruct H11 as [ret2 [injRet12 injRet23]].
      exists ret2. split; trivial. split; trivial. 
       eapply val_inject_opt_hastype; eassumption.
  destruct H0 as [ret2 [injRet12 [injRet23 HRet2]]]. 
  specialize (WD2' WD2). 
  specialize (Core_after12 _ _ Inc12 Sep12 HRet2 _ MInj12' Fwd2
                       WD1' WD2' UnchR2 injRet12).

  specialize (Core_after23 _ _ Fwd2 UnchL2 HRet2 _ _ Inc23 
                      Sep23 HRet3 _ MInj23' WD2' WD3' Fwd3 UnchR3 injRet23).

  (*need to specialize coreafter12 to r' so that we get matchstate12' for r'*)
  specialize (Core_after12 r' RINC RSEP12' ROWN).
  destruct Core_after12 as [cd12' [st1' [st22' [AFT1 [Aft2
               [MS12 [OWN1 OWN2]]]]]]].

  specialize (Core_after23 (reserve_map_image j12' r')).
  destruct Core_after23 as [cd23' [st2' [st3' [Aft22 [Aft33
                [MS23 [OWN22 OWN3]]]]]]].
    (*reserve_map_incr (reserve_map_image j1 r) (reserve_map_image j12' r')*)
                  intros b; intros.
                  destruct H0 as [b1 [delta [HJ HR]]].
                  exists b1. exists delta. 
                  split. apply Inc12. assumption.    
                  apply RINC. assumption.
     (*reserve_map_separated (reserve_map_image j1 r)
            (reserve_map_image j12' r') j23' m2 m3*)
                  intros b; intros.
                  destruct H1 as [b1 [delta [HJ HR]]].
                  remember (j1 b1) as q.
                  destruct q; apply eq_sym in Heqq. 
                          destruct p. rewrite (Inc12 _ _ _ Heqq) in HJ. inv HJ.
                      destruct (reserve_map_dec r b1 (ofs - delta)).
                          exfalso. apply H0. exists b1. exists delta. split; assumption.
                      destruct (RSEP12' _ _ n HR).
                      exfalso. apply H1. 
                           apply (match_validblocks12 _ _ _ _ _ _ _ MC12 _ _ _ Heqq).
                  destruct (Sep12 _ _ _ Heqq HJ).
                      split; trivial.
                      intros. 
                  remember (j2 b) as w.
                  destruct w; apply eq_sym in Heqw. 
                          destruct p. rewrite (Inc23 _ _ _ Heqw) in H3. inv H3.
                          exfalso. apply H2. 
                           apply (match_validblocks23 _ _ _ _ _ _ _ MC23 _ _ _ Heqw).
                      destruct (Sep23 _ _ _ Heqw H3). apply H5.

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
                      apply (H2 N).
  rewrite Aft2 in Aft22. inv Aft22.
  exists (cd12', Some st2', cd23'). exists st1'. exists st3'.
  split. assumption.
  split. assumption.
  split. exists st2'. exists m2'. exists j12'. exists j23'.
     exists (reserve_map_image j12' r').
     split; trivial. 
     split; trivial. 
     split; trivial.
     split; trivial.
     split; trivial.
      intros. clear injRet12 injRet23 HRet2 Aft2 H11 UnchR3 UnchL2 UnchR2 Aft33 AFT1
                      WD1 WD2 WD3 WD1' WD2' WD3' AtExt3 HVals1  HTVals3 ValsInj23
                     AtExt2 HTVals2 ValsInj12 Unch3 HRet3 HRet1 Unch1 AtExt1.
             destruct H0 as [b1 [delta2 [J1 [R' NOW]]]].
                split. exists b1. exists delta2. split; trivial.
                intros N. apply NOW; clear NOW. 
                 apply (match_own12 _ _ _ _ _ _ _ MS12 _ _ N _ _ J1). 
  split; trivial.
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