Require Import Coq.Bool.Bool.

Require Import compcert.lib.Coqlib.
Require Import compcert.lib.Maps.
Require Import compcert.lib.Integers.
Require Import compcert.lib.Axioms.
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.common.Values.
Require Import compcert.common.AST.
Require Import compcert.common.Globalenvs.

Require Import VST.sepcomp.mem_lemmas.
Require Import VST.concurrency.core_semantics.
Require Import VST.sepcomp.semantics_lemmas.
Require Import VST.sepcomp.structured_injections.
Require Import VST.sepcomp.reach.
Require Import VST.sepcomp.mem_wd.

Require Import VST.sepcomp.effect_semantics. (*for specialization below*)


(*
Module Wholeprog_sim. Section Wholeprog_sim.

Context {G1 C1 M1 G2 C2 M2 : Type}

(Sem1 : @CoreSemantics G1 C1 M1)
(Sem2 : @CoreSemantics G2 C2 M2)

(ge1 : G1)
(ge2 : G2)

(main : val).

Variable ge_inv : G1 -> G2 -> Prop.

Variable init_inv : meminj -> G1 -> list val -> M1 -> G2 -> list val -> M2 -> Prop.

Variable halt_inv : (*SM_Injection*)meminj -> G1 -> val -> M1 -> G2 -> val -> M2 -> Prop.

Record Wholeprog_sim :=
{ core_data : Type
; match_state : core_data -> (*SM_Injection*)meminj -> C1 -> M1 -> C2 -> M2 -> Prop
; core_ord : core_data -> core_data -> Prop
; core_ord_wf : well_founded core_ord
; genv_inv : ge_inv ge1 ge2
; core_initial :
    forall j c1 vals1 m1 vals2 m2 n,
    initial_core Sem1 n m1 c1 main vals1 ->
    init_inv j ge1 vals1 m1 ge2 vals2 m2 ->
    exists (*mu*) cd c2,
      (*as_inj mu = j*
      /\*) initial_core Sem2 n m2 c2 main vals2
      /\ match_state cd (*mu*)j c1 m1 c2 m2
; core_diagram :
    forall st1 m1 st1' m1',
    corestep Sem1 ge1 st1 m1 st1' m1' ->
    forall cd st2 mu m2,
    match_state cd mu st1 m1 st2 m2 ->
    exists st2', exists m2', exists cd', exists mu',
    match_state cd' mu' st1' m1' st2' m2'
    /\ (corestep_plus Sem2 ge2 st2 m2 st2' m2'
        \/ (corestep_star Sem2 ge2 st2 m2 st2' m2' /\ core_ord cd' cd))
; core_halted :
    forall cd mu c1 m1 c2 m2 v1,
    match_state cd mu c1 m1 c2 m2 ->
    halted Sem1 c1 v1 ->
    exists j v2,
       halt_inv j ge1 (Vint v1) m1 ge2 (Vint v2) m2
    /\ halted Sem2 c2 v2 }.

End Wholeprog_sim.

End Wholeprog_sim.


Section CompCert_wholeprog_sim.

Context {F1 V1 C1 F2 V2 C2 : Type}

(Sem1 : @EffectSem (Genv.t F1 V1) C1)
(Sem2 : @EffectSem (Genv.t F2 V2) C2)

(ge1 : Genv.t F1 V1)
(ge2 : Genv.t F2 V2)

(main : val).

Definition cc_init_inv j (ge1 : Genv.t F1 V1) vals1 m1 (ge2 : Genv.t F2 V2) vals2 m2 :=
  Mem.inject j m1 m2 /\ Forall2 (val_inject j) vals1 vals2
  /\ meminj_preserves_globals ge1 j /\ globalfunction_ptr_inject ge1 j
  /\ mem_wd m2 /\ valid_genv ge2 m2 /\ Forall (fun v2 => val_valid v2 m2) vals2
  /\ mem_respects_readonly ge1 m1 /\ mem_respects_readonly ge2 m2.

Definition cc_halt_inv j (ge1 : Genv.t F1 V1) v1 m1 (ge2 : Genv.t F2 V2) v2 m2 :=
  meminj_preserves_globals ge1 j
  /\ val_inject j v1 v2
  /\ Mem.inject j m1 m2.

Definition CompCert_wholeprog_sim :=
  @Wholeprog_sim.Wholeprog_sim _ _ _ _ _ _
    Sem1 Sem2
    ge1 ge2
    main
    genvs_domain_eq
    cc_init_inv
    cc_halt_inv.

End CompCert_wholeprog_sim.

Require Import VST.sepcomp.internal_diagram_trans.
Require Import Relations.
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
  specialize H1. auto.
Qed.

Require Import VST.sepcomp.simulations.

Section WholeSimTrans.
Context {F1 V1 C1 F2 V2 C2 F3 V3 C3:Type}
        (Sem1 : @EffectSem (Genv.t F1 V1) C1)
        (Sem2 : @EffectSem (Genv.t F2 V2) C2)
        (Sem3 : @EffectSem (Genv.t F3 V3) C3)
        (g1 : Genv.t F1 V1)
        (g2 : Genv.t F2 V2)
        (g3 : Genv.t F3 V3).

Variable Main :val.
Variable GeInv12: (Genv.t F1 V1) -> (Genv.t F2 V2) -> Prop.
Variable InitInv12 : meminj -> (Genv.t F1 V1) -> list val -> mem -> (Genv.t F2 V2) -> list val -> mem -> Prop.
Variable HaltInv12 : (*SM_Injection*)meminj -> (Genv.t F1 V1) -> val -> mem -> (Genv.t F2 V2) -> val -> mem -> Prop.

Variable GeInv23: (Genv.t F2 V2) -> (Genv.t F3 V3) -> Prop.
Variable InitInv23 : meminj -> (Genv.t F2 V2) -> list val -> mem -> (Genv.t F3 V3) -> list val -> mem -> Prop.
Variable HaltInv23: (*SM_Injection*)meminj -> (Genv.t F2 V2) -> val -> mem -> (Genv.t F3 V3) -> val -> mem -> Prop.

Variable SIM12: Wholeprog_sim.Wholeprog_sim Sem1 Sem2 g1 g2 Main GeInv12 InitInv12 HaltInv12.
Variable SIM23: Wholeprog_sim.Wholeprog_sim Sem2 Sem3 g2 g3 Main GeInv23 InitInv23 HaltInv23.

Definition CoreData12:= Wholeprog_sim.core_data _ _ _ _ _ _ _ _  SIM12.
Definition CoreData23:= Wholeprog_sim.core_data _ _ _ _ _ _ _ _  SIM23.
Definition CoreOrd12:= Wholeprog_sim.core_ord _ _ _ _ _ _ _ _  SIM12.
Definition CoreOrd23:= Wholeprog_sim.core_ord  _ _ _ _ _ _ _ _ SIM23.
Definition MatchState12:= Wholeprog_sim.match_state _ _ _ _ _ _ _ _ SIM12.
Definition MatchState23:= Wholeprog_sim.match_state _ _ _ _ _ _ _ _ SIM23.
Definition genv_inv12 := Wholeprog_sim.genv_inv _ _ _ _ _ _ _ _ SIM12.
Definition genv_inv23 := Wholeprog_sim.genv_inv _ _ _ _ _ _ _ _ SIM23.

Definition CoreDiag12 := Wholeprog_sim.core_diagram _ _ _ _ _ _ _ _ SIM12.
Definition CoreDiag23 := Wholeprog_sim.core_diagram _ _ _ _ _ _ _ _ SIM23.
Definition Halted12:= Wholeprog_sim.core_halted _ _ _ _ _ _ _ _ SIM12.
Definition Halted23:= Wholeprog_sim.core_halted _ _ _ _ _ _ _ _ SIM23.
Definition Init12:= Wholeprog_sim.core_initial _ _ _ _ _ _ _ _ SIM12.
Definition Init23:= Wholeprog_sim.core_initial _ _ _ _ _ _ _ _ SIM23.

Definition GeInv13 (ge1:Genv.t F1 V1) (ge3: Genv.t F3 V3): Prop := exists ge2, GeInv12 ge1 ge2 /\ GeInv23 ge2 ge3.

Definition InitInv13 ge2 (j13:meminj) (ge1: Genv.t F1 V1) (vals1:list val) (m1:mem) (ge3:Genv.t F3 V3) (vals3:list val) (m3: mem): Prop :=
  exists j12 j23 vals2 m2, InitInv12 j12 ge1 vals1 m1 ge2 vals2 m2 /\
                           InitInv23 j23 ge2 vals2 m2 ge3 vals3 m3 /\
                           j13 = compose_meminj j12 j23.
Definition HaltInv13 ge2 (j13:(*SM_Injection*)meminj) (ge1: Genv.t F1 V1) (v1: val) (m1: mem)
                                                  (ge3: Genv.t F3 V3) (v3: val) (m3: mem): Prop :=
  exists j12 j23 v2 m2, HaltInv12 j12 ge1 v1 m1 ge2 v2 m2 /\
                        HaltInv23 j23 ge2 v2 m2 ge3 v3 m3 /\
                        j13 = compose_meminj j12 j23.

Definition CoreOrd:= clos_trans _ (sem_compose_ord_eq_eq CoreOrd12 CoreOrd23 C2).
Definition MatchState := fun d mu c1 m1 c3 m3 =>
      match d with (d1,X,d2) =>
        exists c2, exists m2, exists mu1, exists mu2,
          X=Some c2 /\ mu = compose_meminj mu1 mu2 /\
          MatchState12 d1 mu1 c1 m1 c2 m2 /\ MatchState23 d2 mu2 c2 m2 c3 m3
      end.

Lemma WP_corestep_trans: forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem)
      (CS1: corestep Sem1 g1 st1 m1 st1' m1'),
      forall cd (st3 : C3) (j : meminj) (m3 : mem), MatchState cd j st1 m1 st3 m3 ->
      exists (st3' : C3) (m3' : mem) cd' (j' : meminj),
          MatchState cd' j' st1' m1' st3' m3' /\
         (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
          corestep_star Sem3 g3 st3 m3 st3' m3' /\ CoreOrd cd' cd).
Proof.  intros.
destruct cd as [[cd12 X] cd23].
destruct H as [c2 [m2 [j12 [j23 [HX [Hj [MS12 MS23]]]]]]]. subst X.
destruct (CoreDiag12 _ _ _ _ CS1 _ _ _ _ MS12) as [c2' [m2' [cd12' [j12' [MS12' Step2]]]]].
assert (ZZ: corestep_plus Sem2 g2 c2 m2 c2' m2' \/
    (c2,m2) = (c2',m2') /\ CoreOrd12 cd12' cd12).
{ destruct Step2. auto.
  destruct H.
  destruct H. destruct x.
  right. split; auto.
  left. exists x; auto.
}
clear Step2. destruct ZZ as [CS2 | [CS2 ord12']].
+ (*case1*)
  destruct CS2.
  clear CS1.
  cut (exists st3' : C3,  exists m3' : mem, exists cd23', exists j23' : meminj,
    MatchState23 cd23' j23' c2' m2' st3' m3' /\
    (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
      (corestep_star Sem3 g3 st3 m3 st3' m3' /\
        clos_trans (CoreData12 * option C2 * CoreData23)
        (sem_compose_ord_eq_eq CoreOrd12 CoreOrd23 C2) (cd12', Some c2', cd23')
        (cd12, Some c2, cd23)))).
  intros XX; destruct XX as [c3' [m3' [cd23' [j23' [MC23' ZZ]]]]].
  exists c3'. exists m3'. exists (cd12', Some c2', cd23'). exists (compose_meminj j12' j23').
  split. subst. red. exists c2', m2', j12', j23'. eauto.
    apply ZZ.
  clear MS12 MS12' Hj.
  revert j23 cd23 c2 m2 st3 m3 H MS23.
  induction x; intros.
  - (*base case*)
    destruct H as [c22 [m2'' [? ?]]].
    inv H0.
    destruct (CoreDiag23 _ _ _ _ H _ _ _ _ MS23)
      as [c3' [m3' [cd23' [j23' [MS23' Step3]]]]].
    exists c3', m3', cd23', j23'.
    split; trivial.
    destruct Step3. left; assumption.
    destruct H0. right. split; trivial.
    apply t_step. constructor 2. trivial.
  - (*inductive case*)
    remember (S x) as x'.
    destruct H as [st2'' [m2'' [Step2 StepN2]]]. subst x'.
    destruct (CoreDiag23 _ _ _ _ Step2 _ _ _ _ MS23)
      as [c3' [m3' [cd23' [j23' [MS23' Step3]]]]].
    specialize (IHx j23' cd23' _ _ c3' m3' StepN2 MS23'). clear Step2 StepN2 MS23'.
    destruct IHx as [c3'' [m3'' [cd23'' [j23'' [MC' XX]]]]].
    exists c3'', m3'', cd23'', j23''.
    split. apply MC'.
    destruct Step3; destruct XX.
           (*1/4*)
              left. destruct H as [n1 ?]. destruct H0 as [n2 ?].
                      exists (n1 + S n2)%nat.
                      change (S (n1 + S n2)) with (S n1 + S n2)%nat.
                      rewrite corestepN_add. eauto.
           (*2/4*)
               destruct H0.
               left. destruct H as [n1 ?]. destruct H0 as [n2 ?].
                       exists (n1 + n2)%nat.
                       change (S (n1 + n2)) with (S n1 + n2)%nat.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               left. destruct H.
                       destruct H as [n1 ?]. destruct H0 as [n2 ?].
                       exists (n1 + n2)%nat.
                       replace (S (n1 + n2)) with (n1 + S n2)%nat by omega.
                       rewrite corestepN_add. eauto.
           (*3/4*)
               right. destruct H. destruct H0.
               split. destruct H as [n1 ?]. destruct H0 as [n2 ?].
                         exists (n1 + n2)%nat.
                         rewrite corestepN_add. eauto.
              eapply t_trans; eauto.
          (*4/4*)
              apply t_step.
              constructor 2. assumption.
+ (*case 2*)
   inv CS2.
   exists st3, m3, (cd12',Some c2', cd23), (compose_meminj j12' j23).
   split. exists c2', m2', j12', j23; auto.
   right. split. exists O. simpl; auto.
   apply t_step. constructor 1; auto.
Qed.

Definition WP_trans:
        Wholeprog_sim.Wholeprog_sim Sem1 Sem3 g1 g3 Main GeInv13 (InitInv13 g2) (HaltInv13 g2).
eapply Wholeprog_sim.Build_Wholeprog_sim with
  (core_ord:=CoreOrd)(match_state:=MatchState).
{ (*well_founded*)
  eapply Transitive_Closure.wf_clos_trans.
  eapply well_founded_sem_compose_ord_eq_eq. apply SIM12. apply SIM23. }
{ exists g2; split. apply genv_inv12. apply genv_inv23. }
{ (*Init*)
  intros j13 c1 vals1 m1 vals3 m3 n Init1 IInv13.
  destruct IInv13 as [j12 [j23 [vals2 [m2 [Initial12 [Initial23 Hj]]]]]].
  destruct (Init12 _ _ _ _ _ _ _ Init1 Initial12) as [cd12 [c2 [Init2 MS12]]].
  destruct (Init23 _ _ _ _ _ _ _ Init2 Initial23) as [cd23 [c3 [Init3 MS23]]].
  exists ((cd12, Some c2), cd23), c3. split; trivial.
  exists c2, m2, j12, j23; auto. }
{ apply WP_corestep_trans. }
{ (*Halted*)
  intros [[c12 X] c23] j c1 m1 c3 m3 v1 MS HALT1.
  destruct MS as [c2 [m2 [j12 [j23 [HX [Hj [MS12 MS23]]]]]]].
  destruct (Halted12 _ _ _ _ _ _ _ MS12 HALT1) as [j12' [v2 [MI12 HALT2]]].
  destruct (Halted23 _ _ _ _ _ _ _ MS23 HALT2) as [j23' [v3 [MI23 HALT3]]].
  exists (compose_meminj j12' j23'), v3; split; trivial.
  exists j12', j23', v2, m2; auto. }
Qed.
End WholeSimTrans.
*)