(*This file contains the proof of transitivity for
  the forward_simulations.coop_sim, ie the following theorem:

Theorem coop_sim_trans: forall
        (SIM12: coop_sim Sem1 Sem2 g1 g2 epts12)
        (SIM23: coop_sim Sem2 Sem3 g2 g3 epts23),
        coop_sim Sem1 Sem3 g1 g3 epts13.

The only holes in this file relate to the preservation and composition
of meminj_preserves_globals, an issue that is largely orthogonal to
our core focus of interest, and the definition of globalenvs may
need to evolve a bit anyway once AST.program is restructured to support
compilation units. *)

Require Import Coqlib.
Require Import Events. (*for inject_separated etc*)
Require Import compcert.common.Values.
Require Import AST.
Require Import Globalenvs.
Require Import Memory.

Require Import sepcomp.Coqlib2.

Require Import sepcomp.mem_lemmas.
Require Import sepcomp.core_semantics.
Require Import sepcomp.forward_simulations.

Require Import Wellfounded.
Require Import Relations.

Require Import sepcomp.mem_interpolants.
Declare Module MEMAX : MemoryInterpolationAxioms.

Import Forward_simulation.

Definition entrypoints_compose
  (ep12 ep23 ep13 : list (val * val * signature)): Prop :=
  forall v1 v3 sig, In (v1,v3,sig) ep13 =
    exists v2, In (v1,v2,sig) ep12 /\ In (v2,v3,sig) ep23.

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

Module Forward_simulation_trans.
Section Coop_sim_trans.
Context {F1 V1 C1 F2 V2 C2 F3 V3 C3:Type}
        (Sem1 : CoopCoreSem (Genv.t F1 V1) C1)
        (Sem2 : CoopCoreSem (Genv.t F2 V2) C2)
        (Sem3 : CoopCoreSem (Genv.t F3 V3) C3)
        (g1 : Genv.t F1 V1)
        (g2 : Genv.t F2 V2)
        (g3 : Genv.t F3 V3)
        epts12 epts23 epts13
        (EPC : entrypoints_compose epts12 epts23 epts13).

Section CaseEQ.
  Import Forward_simulation_eq.

Section EQEQ.
Lemma diagram_eqeq: forall
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> C2 -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(core_diagram12 : forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem),
                 corestep Sem1 g1 st1 m st1' m' ->
                 forall (d : core_data12) (st2 : C2),
                 match_core12 d st1 st2 ->
                 exists st2' : C2,
                   exists d' : core_data12,
                     match_core12 d' st1' st2' /\
                     (corestep_plus Sem2 g2 st2 m st2' m' \/
                      corestep_star Sem2 g2 st2 m st2' m' /\
                      core_ord12 d' d))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> C3 -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(core_diagram23 : forall (st1 : C2) (m : mem) (st1' : C2) (m' : mem),
                 corestep Sem2 g2 st1 m st1' m' ->
                 forall (d : core_data23) (st2 : C3),
                 match_core23 d st1 st2 ->
                 exists st2' : C3,
                   exists d' : core_data23,
                     match_core23 d' st1' st2' /\
                     (corestep_plus Sem3 g3 st2 m st2' m' \/
                      corestep_star Sem3 g3 st2 m st2' m' /\
                      core_ord23 d' d))
(c1 : C1)
(m1 : mem)
(c1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 g1 c1 m1 c1' m1')
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
    (corestep_plus Sem3 g3 c3 m1 st2' m1' \/
     corestep_star Sem3 g3 c3 m1 st2' m1' /\
     clos_trans (core_data12 * option C2 * core_data23)
       (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) d'
       (d12, Some c2, d23)).
Proof.
  intros.
  destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [c2' [d12' [MC12' Y]]].
  assert (ZZ: corestep_plus Sem2 g2 c2 m1 c2' m1' \/  (c2,m1) = (c2',m1') /\ core_ord12 d12' d12).
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

Lemma eqeq: forall
   (SimEq12 : Forward_simulation_equals Sem1 Sem2 g1 g2 epts12)
   (SimEq23 : Forward_simulation_equals Sem2 Sem3 g2 g3 epts23),
   Forward_simulation_equals Sem1 Sem3 g1 g3 epts13.
Proof. intros.
  destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12
     genvs_dom_eq12 core_diagram12 core_initial12 core_halted12
     core_at_external12 core_after_external12].
  destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23
     genvs_dom_eq23 core_diagram23 core_initial23 core_halted23
     core_at_external23 core_after_external23].
  eapply Forward_simulation_eq.Build_Forward_simulation_equals with
    (core_data:= prod (prod core_data12 (option C2)) core_data23)
    (match_core := fun d c1 c3 => match d with (d1,X,d2) =>
      exists c2, X=Some c2 /\ match_core12 d1 c1 c2 /\ match_core23 d2 c2 c3 end)
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)).
           (*wellfounded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
           (*genvs_dom_eq*)
             eapply genvs_domain_eq_trans; eauto.
           (*core_diagram*)
  clear core_initial23  core_halted23 core_at_external23 core_after_external23 core_initial12
    core_halted12 core_at_external12 core_after_external12  EPC epts12  epts23 epts13.
  intros. destruct d as [[d12 cc2] d23]. destruct H0 as [c2 [X [? ?]]]; subst.
  eapply (diagram_eqeq _ _ _ core_diagram12 _ _ _ core_diagram23); eassumption.
           (*initial_core*)
  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  destruct (core_initial12 _ _ _ EP12 vals) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
  destruct (core_initial23 _ _ _ EP23 vals) as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
  rewrite Ini22 in Ini2. inv Ini2.
  exists (d12,Some c2,d23). exists c1. exists c3. split; trivial. split; trivial.
    exists c2. split; trivial. split; trivial.
           (*halted*)
  intros. rename c2 into c3. destruct cd as [[d12 cc2] d23].
    destruct H as [c2 [X [MC12 MC23]]]. subst.
  apply (core_halted12 _ _ _ _ MC12) in H0.
  apply (core_halted23 _ _ _ _ MC23) in H0. assumption.
           (*atexternal*)
  intros. rename st2 into st3. destruct d as [[d12cc2]  d23].
    destruct H as [st2 [X [MC12 MC23]]]; subst.
  apply (core_at_external12 _ _ _ _ _ _ MC12) in H0.
  apply (core_at_external23 _ _ _ _ _ _ MC23) in H0. assumption.
          (*after_external*)
  intros. rename st2 into st3. destruct d as [[d12 cc2] d23].
    destruct H as [st2 [X [MC12 MC23]]]; subst.
  specialize (core_at_external12 _ _ _ _ _ _ MC12 H0).
  destruct (core_after_external12 _ _ _ ret _ _ _ MC12 H0 core_at_external12)
    as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
  destruct (core_after_external23 _ _ _ ret _ _ _ MC23 core_at_external12 H1)
    as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists c1'. exists c3'. exists (d12',Some c2',d23'). split; trivial.
    split; trivial. exists c2'. split; trivial. split; trivial.
Qed.

End EQEQ.

Section EQEXT.
  Import Forward_simulation_ext.
Lemma diagram_eqext: forall
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> C2 -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(core_diagram12 : forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem),
                 corestep Sem1 g1 st1 m st1' m' ->
                 forall (d : core_data12) (st2 : C2),
                 match_core12 d st1 st2 ->
                 exists st2' : C2,
                   exists d' : core_data12,
                     match_core12 d' st1' st2' /\
                     (corestep_plus Sem2 g2 st2 m st2' m' \/
                      corestep_star Sem2 g2 st2 m st2' m' /\
                      core_ord12 d' d))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 g2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (m2 : mem),
                 match_core23 cd st1 m1 st2 m2 ->
                 exists st2' : C3,
                   exists m2' : mem,
                     exists cd' : core_data23,
                       match_core23 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem3 g3 st2 m2 st2' m2' \/
                        corestep_star Sem3 g3 st2 m2 st2' m2' /\ core_ord23 cd' cd))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 g1 st1 m1 st1' m1')
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
      (corestep_plus Sem3 g3 st3 m3 st2' m2' \/
       corestep_star Sem3 g3 st3 m3 st2' m2' /\
       clos_trans (core_data12 * option C2 * core_data23)
         (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
         (d12, Some st2, d23)).
Proof. intros.
    destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12) as [st2' [d12' [MC12' Y]]].
    assert (ZZ: corestep_plus Sem2 g2 st2 m1 st2' m1' \/  (st2,m1) = (st2',m1')
             /\ core_ord12 d12' d12).
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
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']  [[c2'' [X [MC12'' MC23'']]] ?]]]].
             subst.
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

Lemma eqext: forall
   (SimEq12 : Forward_simulation_equals Sem1 Sem2 g1 g2 epts12)
   (SimExt23 : Forward_simulation_extends Sem2 Sem3 g2 g3 epts23),
   Forward_simulation_extends Sem1 Sem3 g1 g3 epts13.
Proof. intros.
  destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12
    genvs_dom_eq12 core_diagram12 core_initial12 core_halted12
    core_at_external12 core_after_external12].
  destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23
    genvs_dom_eq23 match_validblocks23
    core_diagram23 core_initial23 core_halted23 core_at_external23 core_after_external23].
  eapply Build_Forward_simulation_extends with
    (match_state := fun d c1 m1 c3 m3 => match d with (d1,X,d2) =>
       exists c2, X = Some c2 /\ match_core12 d1 c1 c2 /\ match_core23 d2 c2 m1 c3 m3 end)
    (core_data:= prod (prod core_data12 (option C2)) core_data23)
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2)).
           (*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
           (*genvs_dom_eq*)
             eapply genvs_domain_eq_trans; eauto.
            (*match_validblocks*)
  intros. rename c2 into c3.  rename m2 into m3.
  destruct d as [[d12 cc2] d23].
  destruct H as [c2 [X [MC12 MC23]]]; subst.
  eapply (match_validblocks23 _ _ _ _ _ MC23); try eassumption.
           (*core_diagram*)
  clear core_initial23  core_halted23 core_at_external23
    core_after_external23 core_initial12  core_halted12
    core_at_external12 core_after_external12
    core_ord_wf23 core_ord_wf12 EPC epts12  epts23 epts13.
  intros. rename st2 into st3.
  destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [X [? ?]]]; subst. rename m2 into m3.
  eapply (diagram_eqext _ _ _ core_diagram12 _ _ _ core_diagram23); eassumption.
           (*initial_core*)
  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  destruct (core_initial12 _ _ _ EP12 vals) as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
  destruct (core_initial23 _ _ _ EP23 vals vals' _ _ H0 H1)
    as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
  rewrite Ini22 in Ini2. inv Ini2.
  exists (d12,Some c2,d23). exists c1. exists c3.
  split; trivial. split; trivial. exists c2. split; trivial. split; trivial.
           (*halted*)
  intros. rename st2 into c3.
    destruct cd as [[d12 cc2] d23].
    destruct H as [c2 [X [MC12 MC23]]]; subst.
  apply (core_halted12 _ _ _ _ MC12) in H0.
  apply (core_halted23 _ _ _ _ _ _ MC23) in H0. assumption.
           (*atexternal*)
  intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H as [st2 [X [MC12 MC23]]].
  apply (core_at_external12 _ _ _ _ _ _ MC12) in H0.
  apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in H0. assumption.
           (*after_external*)
  intros. rename st2 into st3. destruct cd as [[d12 cc2] d23]. destruct H as [st2 [X [MC12 MC23]]].
  specialize (core_at_external12 _ _ _ _ _ _ MC12 H0).
  rename core_at_external12 into AtExt2.
  destruct (core_after_external12 _ _ _ ret1 _ _ _ MC12 H0 AtExt2)
    as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
  destruct (core_after_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ MC23 AtExt2
    H1 H2 H3 H4 H5 H6 H7)
    as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists c1'. exists c3'. exists (d12',Some c2',d23').
  split; trivial. split; trivial. exists c2'. split; trivial. split; trivial.
Qed.

End EQEXT.

Lemma X: forall {A B} (f g: A ->B)
      (H: (fun b => f b) = (fun b => g b)) b,
       f b = g b.
Proof. intros.
  remember ((fun b => f b) b).
     rewrite H in Heqb0. trivial.
Qed.

Section EQINJ.
  Import Forward_simulation_inj.
Lemma diagram_eqinj: forall
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> C2 -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(core_diagram12 : forall (st1 : C1) (m : mem) (st1' : C1) (m' : mem),
                 corestep Sem1 g1 st1 m st1' m' ->
                 forall (d : core_data12) (st2 : C2),
                 match_core12 d st1 st2 ->
                 exists st2' : C2,
                   exists d' : core_data12,
                     match_core12 d' st1' st2' /\
                     (corestep_plus Sem2 g2 st2 m st2' m' \/
                      corestep_star Sem2 g2 st2 m st2' m' /\
                      core_ord12 d' d))
(core_data23 : Type)
(match_core23 : core_data23 -> meminj -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 g2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (j : meminj) (m2 : mem),
                 match_core23 cd j st1 m1 st2 m2 ->
                 exists st2' : C3,
                   exists m2' : mem,
                     exists cd' : core_data23,
                       exists j' : meminj,
                         inject_incr j j' /\
                         inject_separated j j' m1 m2 /\
                         match_core23 cd' j' st1' m1' st2' m2' /\
                         (corestep_plus Sem3 g3 st2 m2 st2'
                            m2' \/
                          corestep_star Sem3 g3 st2 m2 st2'
                            m2' /\ core_ord23 cd' cd))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 g1 st1 m1 st1' m1')
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
        (corestep_plus Sem3 g3 st3 m3 st2' m2' \/
         corestep_star Sem3 g3 st3 m3 st2' m2' /\
         clos_trans (core_data12 * option C2 * core_data23)
           (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
           (d12, Some st2, d23)).
Proof. intros.
    destruct (core_diagram12 _ _ _ _ CS1 _ _ MC12)
      as [st2' [d12' [MC12' Y]]]. clear core_diagram12.
    assert (ZZ: corestep_plus Sem2 g2 st2 m1 st2' m1'
      \/  (st2,m1) = (st2',m1') /\ core_ord12 d12' d12).
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
          destruct (core_diagram23 _ _ _ _ H _ _ _ _ MC23)
            as [st3' [m3' [d23' [j' [InjInc [InjSep [? ?]]]]]]].
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
           destruct (core_diagram23 st2 m2 st2'' m2'' H _ _ _ _ MC23)
             as [c3' [m3' [d'' [j' [InjInc [InjSep [? ?]]]]]]].
           specialize (IHx _ _ _ _ _ _ _ _ H1 MC12' H0).
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']
             [j'' [IncIncr' [InSep' [[c2'' [X [MC12'' MC23'']]] ?]]]]]]]. subst.
           exists c3''. exists m3''. exists (d12''', Some c2'',d23''). exists j''.
           split. eapply inject_incr_trans; eassumption.
           split. apply corestep_fwd in H.
                 intros b; intros.
                 remember (j' b).
                 destruct o; apply eq_sym in Heqo.
                      destruct p. destruct (InjSep _ _ _ H4 Heqo).
                      apply (IncIncr') in Heqo. rewrite Heqo in H5.  inv H5.
                      split; trivial.
                 destruct (InSep' _ _ _ Heqo H5). split.
                    intros N. apply H6. apply H. apply N.
                    intros N. apply H7.
                        assert (FWD: mem_forward m3 m3').
                           destruct H2 as [X | [X _]].
                           eapply corestep_plus_fwd; eassumption.
                           eapply corestep_star_fwd; eassumption.
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

Lemma eqinj: forall
   (SimEq12 : Forward_simulation_equals Sem1 Sem2 g1 g2 epts12)
   (SimInj23 : Forward_simulation_inject Sem2 Sem3 g2 g3 epts23),
   Forward_simulation_inject Sem1 Sem3 g1 g3 epts13.
Proof. intros.
         destruct SimEq12 as [core_data12 match_core12 core_ord12 core_ord_wf12
               genvs_domain_eq12 core_diagram12 core_initial12 core_halted12
               core_at_external12 core_after_external12].
         destruct SimInj23 as [core_data23 match_core23 core_ord23 core_ord_wf23
              match_validblock23 genvs_dom_eq23 match_genv23 core_diagram23
              core_initial23 core_halted23 core_at_external23 core_after_external23].
          eapply Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 =>
                   match d with (d1,X,d2) =>
                     exists c2, X=Some c2
                       /\ match_core12 d1 c1 c2
                       /\ match_core23 d2 j c2 m1 c3 m3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*match_validblocks*) intros. rename c2 into c3.
                         rename m2 into m3. destruct d as [[d12 cc2] d23].
                         destruct H as [c2 [X [MC12 MC23]]]; subst.
                         eapply (match_validblock23 _ _ _ _ _ _ MC23); try eassumption.
           (*genvs_dom_eq*)
             eapply genvs_domain_eq_trans; eauto.
            (*match_genvs*)
                 intros.
                 clear core_initial23  core_halted23 core_at_external23
                       core_after_external23 core_initial12 core_halted12
                       core_at_external12 core_after_external12
                       core_diagram12 core_diagram23.
                 rename c2 into st3.
                 destruct d as [[d12 cc2] d23]. destruct H as [st2 [X [? ?]]]; subst.
                   rename m2 into m3.
                 apply meminj_preserves_genv2blocks.
                 rewrite (genvs_domain_eq_match_genvs _ _ genvs_domain_eq12).
                 apply meminj_preserves_genv2blocks.
                 apply (match_genv23 _ _ _ _ _ _ H0).
            (*core_diagram*)
                 clear core_initial23 core_halted23 core_at_external23
                       core_after_external23 core_initial12  core_halted12
                       core_at_external12 core_after_external12
                       EPC epts12 epts23 epts13.
                 intros. rename st2 into st3.
                 destruct cd as [[d12 cc2] d23].
                   destruct H0 as [st2 [X [? ?]]]; subst. rename m2 into m3.
                 eapply (diagram_eqinj _ _ _ core_diagram12 _ _ _ core_diagram23); try eassumption.
            (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H.
                    destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 vals1)
                    as [d12 [c11 [c2 [Ini1 [Ini2 MC12]]]]]. rewrite Ini1 in H0. inv H0.
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2)
                    as [d23 [c3 [Ini3 MC23]]].
                  apply meminj_preserves_genv2blocks.
                     apply meminj_preserves_genv2blocks in H3.
                     apply (genvs_domain_eq_preserves g1); assumption.
                  exists (d12,Some c2,d23). exists c3. split; trivial. exists c2. auto.
             (*halted*)
                    intros. rename c2 into c3. destruct cd as [[d12 cc2] d23].
                      destruct H as [c2 [X [MC12 MC23]]]; subst.
                    apply (core_halted12 _ _ _ _ MC12) in H0; try assumption.
                    apply (core_halted23 _ _ _ _ _ _ _ MC23) in H0; try assumption.
             (*atexternal*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23].
                    destruct H as [c2 [X [MC12 MC23]]]; subst.
                    apply (core_at_external12 _ _ _ _ _ _ MC12) in H0.
                    apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in H0; try assumption.
             (*after_external*)
                    intros. rename st2 into st3. destruct cd as [[d12 cc2] d23].
                    destruct H0 as [c2 [X [MC12 MC23]]]; subst.
                    specialize (core_at_external12 _ _ _ _ _ _ MC12 H1).
                    rename core_at_external12 into AtExt2.
                    destruct (core_after_external12 _ _ _ ret1 _ _ _ MC12 H1 AtExt2)
                      as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                    assert (PG2: meminj_preserves_globals g2 j).
                      solve[apply (match_genv23 _ _ _ _ _ _ MC23)].
                    destruct (core_after_external23 _ _ _ _ _ _ _ _ _ _ _ _ _ _
                        H MC23 AtExt2 PG2 H3 H4 H5 H6 H7 H8 H9 H10)
                    as [d23' [c22' [c3' [AftExt22 [AftExt3 MS23']]]]].
                    rewrite AftExt22 in AftExt2. inv AftExt2.
                    exists (d12',Some c2',d23'). exists c1'. exists c3'.
                    split; trivial. split; trivial. exists c2'. auto.
Qed.
End EQINJ.

Lemma coop_sim_trans_CaseEq: forall
     (SimEq12 : Forward_simulation_equals Sem1 Sem2 g1 g2 epts12)
     (SIM23 : coop_sim Sem2 Sem3 g2 g3 epts23),
     coop_sim Sem1 Sem3 g1 g3 epts13.
Proof. intros.
  induction SIM23; intros.
  eapply coop_sim_eq.
    apply (eqeq SimEq12 R).
  eapply coop_sim_ext.
    apply (eqext SimEq12 R).
  eapply coop_sim_inj.
    apply (eqinj SimEq12 R).
Qed.

End CaseEQ.

Section CaseEXT.
  Import Forward_simulation_ext.

Section EXTEQ.
  Import Forward_simulation_eq.
Lemma  diagram_exteq: forall
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 g1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (m2 : mem),
                 match_core12 cd st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       match_core12 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem2 g2 st2 m2 st2'
                          m2' \/
                        corestep_star Sem2 g2 st2 m2 st2'
                          m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> C3 -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(core_diagram23 : forall (st1 : C2) (m : mem) (st1' : C2) (m' : mem),
                 corestep Sem2 g2 st1 m st1' m' ->
                 forall (d : core_data23) (st2 : C3),
                 match_core23 d st1 st2 ->
                 exists st2' : C3,
                   exists d' : core_data23,
                     match_core23 d' st1' st2' /\
                     (corestep_plus Sem3 g3 st2 m st2' m' \/
                      corestep_star Sem3 g3 st2 m st2' m' /\
                      core_ord23 d' d))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 g1 st1 m1 st1' m1')
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
      (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
       corestep_star Sem3 g3 st3 m3 st3' m3' /\
       clos_trans (core_data12 * option C2 * core_data23)
         (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
         (d12, Some st2, d23)).
Proof. intros.
    destruct (core_diagram12 _ _ _ _ CS1 _ _ _ MC12)
      as [st2' [m3' [d12' [MC12' Y]]]]. clear core_diagram12.
    assert (ZZ: corestep_plus Sem2 g2 st2 m3 st2' m3' \/  (st2,m3) = (st2',m3')
             /\ core_ord12 d12' d12).
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
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']
                           [[c2'' [X [MC12'' MC23'']]] ?]]]]; subst.
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
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Lemma exteq: forall
   (SimExt12 : Forward_simulation_extends Sem1 Sem2 g1 g2 epts12)
   (SimEq23 : Forward_simulation_equals Sem2 Sem3 g2 g3 epts23),
   Forward_simulation_extends Sem1 Sem3 g1 g3 epts13.
Proof. intros.
  destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12 genvs_dom_eq12
                 match_validblocks12 core_diagram12 core_initial12 core_halted12
                 core_at_external12 core_after_external12].
  destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23
                       genvs_dom_eq23 core_diagram23 core_initial23
                       core_halted23 core_at_external23 core_after_external23].
  eapply Forward_simulation_ext.Build_Forward_simulation_extends with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d c1 m1 c3 m3 => match d with (d1,X,d2) =>
                    exists c2, X=Some c2
                      /\ match_core12 d1 c1 m1 c2 m3
                      /\ match_core23 d2 c2 c3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*genvs_dom_eq*)
                 eapply genvs_domain_eq_trans; eauto.
            (*match_validblocks*) intros. rename c2 into c3.
                 rename m2 into m3. destruct d as [[d12 cc2] d23].
                 destruct H as [c2 [X [MC12 MC23]]]; subst.
                 eapply (match_validblocks12 _ _ _ _ _ MC12); try eassumption.
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23
                       core_after_external23 core_initial12  core_halted12
                       core_at_external12 core_after_external12
                       EPC epts12  epts23 epts13.
                 intros. rename st2 into st3.
                 destruct cd as [[d12 cc2] d23].
                   destruct H0 as [st2 [X [? ?]]]; subst. rename m2 into m3.
                 eapply (diagram_exteq _ _ _ core_diagram12 _ _ _ core_diagram23); try eassumption.
            (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H.
                    destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ H0 H1)
                    as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]].
                  destruct (core_initial23 _ _ _ EP23 vals') as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2, d23). exists c1. exists c3.
                  split; trivial. split; trivial. exists c2. split; trivial. split; trivial.
             (*halted*)
                  intros. rename st2 into c3.  destruct cd as [[d12 cc2] d23].
                    destruct H as [c2 [X [MC12 MC23]]]; subst.
                  apply (core_halted12 _ _ _ _ _ _ MC12) in H0. destruct H0 as [v2 [LD [SH2 Ext]]].
                  apply (core_halted23 _ _ _ _ MC23) in SH2. exists v2.
                    split; trivial. split; trivial.
             (*atexternal*)
                  intros. rename st2 into st3.
                  destruct cd as [[d12 cc2] d23]. destruct H as [c2 [X [MC12 MC23]]]; subst.
                  apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0.
                    destruct H0 as [vals2 [Ext [LD AtExt2]]].
                    specialize (core_at_external23 _ _ _ _ _ _ MC23 AtExt2).
                    exists vals2. intuition.
             (*after_external*)
                  intros. rename st2 into st3. destruct cd as [[d12 cc2] d23].
                  destruct H as [c2 [X [MC12 MC23]]]; subst.
                  rename vals2 into vals3. rename ret2 into ret3.
                  destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 H0)
                     as [vals2 [Ext [LD AtExt2]]].
                  specialize (core_at_external23 _ _ _ _ _ _ MC23 AtExt2).
                  rename core_at_external23 into AtExt3.
                  rewrite AtExt3 in H1. inv H1.
                  destruct (core_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ _
                       MC12 H0 AtExt2 LD H3 H4 H5 H6 H7)
                    as [c1' [c2' [d12' [AftExt1 [AftExt2 MS12']]]]].
                  destruct (core_after_external23 _ _ _ ret3 _ _ _
                       MC23 AtExt2 AtExt3)
                    as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
                  rewrite AftExt22 in AftExt2. inv AftExt2.
                  exists c1'. exists c3'. exists (d12',Some c2', d23').
                  split; trivial. split; trivial. exists c2'. intuition.
Qed.
End EXTEQ.

Section EXTEXT.
Lemma  diagram_extext: forall
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 g1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (m2 : mem),
                 match_core12 cd st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       match_core12 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem2 g2 st2 m2 st2'
                          m2' \/
                        corestep_star Sem2 g2 st2 m2 st2'
                          m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 g2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (m2 : mem),
                 match_core23 cd st1 m1 st2 m2 ->
                 exists st2' : C3,
                   exists m2' : mem,
                     exists cd' : core_data23,
                       match_core23 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem3 g3 st2 m2 st2'
                          m2' \/
                        corestep_star Sem3 g3 st2 m2 st2'
                          m2' /\ core_ord23 cd' cd))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 g1 st1 m1 st1' m1')
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
      (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
       corestep_star Sem3 g3 st3 m3 st3' m3' /\
       clos_trans (core_data12 * option C2 * core_data23)
         (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
         (d12, Some st2, d23)).
Proof.
  intros.
  destruct (core_diagram12 _ _ _ _ CS1 _ _ _ MC12)
           as [st2' [m2' [d12' [MC12' Y]]]].
  clear core_diagram12.
  assert (ZZ: corestep_plus Sem2 g2 st2 m2 st2' m2' \/
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


Lemma extext: forall
  (SimExt12 : Forward_simulation_extends Sem1 Sem2 g1 g2 epts12)
  (SimExt23 : Forward_simulation_extends Sem2 Sem3 g2 g3 epts23),
   Forward_simulation_extends Sem1 Sem3 g1 g3 epts13.
Proof. intros.
  destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12
                        genvs_dom_eq12 match_vb12 core_diagram12
                        core_initial12 core_halted12 core_at_external12
                        core_after_external12].
  destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23
                        genvs_dom_eq23 match_vb23 core_diagram23
                        core_initial23 core_halted23 core_at_external23
                        core_after_external23].
  eapply Forward_simulation_ext.Build_Forward_simulation_extends with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d c1 m1 c3 m3 =>
      match d with (d1,X,d2) => exists c2, exists m2, X=Some c2
        /\ match_core12 d1 c1 m1 c2 m2 /\ match_core23 d2 c2 m2 c3 m3 end).
 (*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
 (*genvs_dom_eq*)
  eapply genvs_domain_eq_trans; eauto.
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
             EPC epts12 epts23 epts13.
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [X [? ?]]]]; subst.
  eapply (diagram_extext _ _ _ core_diagram12 _ _ _ core_diagram23); try eassumption.
 (*initial_core*)
  intros. rename m2 into m3. rename vals' into args3. rename vals into args1. rename v2 into v3.
  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  destruct (core_initial12 _ _ _ EP12 _ _ m1 _ (forall_lessdef_refl args1) (extends_refl _))
    as [d12 [c1 [c2 [Ini1 [Ini2 MC12]]]]]; try assumption.
  destruct (core_initial23 _ _ _ EP23 _ _ _ _ H0 H1)
    as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]]; try assumption.
  rewrite Ini22 in Ini2. inv Ini2.
  exists (d12,Some c2, d23). exists c1. exists c3. split; trivial. split; trivial.
  exists c2. exists m1. split; trivial. split; trivial.
 (*halted*)
  intros. rename st2 into c3. rename m2 into m3.  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
  apply (core_halted12 _ _ _ _ _ _ MC12) in H0; try assumption.
  destruct H0 as [v2 [V12 [SH2 Ext12]]].
  apply (core_halted23 _ _ _ _ _ _ MC23) in SH2; try assumption.
  destruct SH2 as [v3 [V23 [SH3 Ext23]]].
  exists v3. split. eapply Val.lessdef_trans; eassumption.
  split; trivial.
  eapply extends_trans; eassumption.
 (*atexternal*)
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
  apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0; try assumption.
  destruct H0 as [vals2 [Ext12 [LD12 AtExt2]]].
  apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in AtExt2; try assumption.
  destruct AtExt2 as [vals3 [Ext23 [LS23 AtExt3]]].
  exists vals3. split. eapply extends_trans; eassumption.
  split. eapply forall_lessdef_trans; eassumption.
  solve[intuition].
 (*after_external*)
  intros. rename st2 into st3. rename m2 into m3. rename m2' into m3'.
  rename vals2 into vals3. rename ret2 into ret3.
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 H0)
    as [vals2 [Ext12 [ValsLD12 AtExt2]]]; try assumption.
  destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)
    as [vals33 [Ext23 [ValsLD23 AtExt3]]]; try assumption.
  rewrite AtExt3 in H1. inv H1.
  assert (UnchOn3 :  Mem.unchanged_on (loc_out_of_bounds m2) m3 m3').
    split; intros; eapply H5; trivial.
    eapply extends_loc_out_of_bounds; eassumption.
    eapply extends_loc_out_of_bounds; eassumption.
  destruct (MEMAX.interpolate_EE _ _ Ext12 _ H3 _ Ext23 _ H4 H7 H5)
    as [m2' [Fwd2 [Ext12' [Ext23' UnchOn2]]]].
  destruct (core_after_external12 _ _ _ _ _ _ _ _ ret1 ret1 _ _ _ MC12 H0
      AtExt2 ValsLD12 H3 Fwd2 UnchOn2 (Val.lessdef_refl _) Ext12')
    as [c1' [c2' [d12' [AftExt1 [AftExt2 MC12']]]]].
  destruct (core_after_external23 _ _ _ _ _ _ _ _ ret1 ret3 _ _ _ MC23 AtExt2
      AtExt3 ValsLD23 Fwd2 H4 UnchOn3 H6 Ext23')
    as [cc2' [c3' [d23' [AftExt22 [AftExt3 MC23']]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists c1'. exists c3'. exists (d12',Some c2', d23'). split; trivial. split; trivial.
  exists c2'. exists m2'. intuition.
Qed.

End EXTEXT.

Section EXTINJ.
  Import Forward_simulation_inj.
Lemma  diagram_extinj: forall
(core_data12 : Type)
(match_core12 : core_data12 -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 g1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (m2 : mem),
                 match_core12 cd st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       match_core12 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem2 g2 st2 m2 st2'
                          m2' \/
                        corestep_star Sem2 g2 st2 m2 st2'
                          m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> meminj -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 g2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (j : meminj) (m2 : mem),
                 match_core23 cd j st1 m1 st2 m2 ->
                 exists st2' : C3,
                   exists m2' : mem,
                     exists cd' : core_data23,
                       exists j' : meminj,
                         inject_incr j j' /\
                         inject_separated j j' m1 m2 /\
                         match_core23 cd' j' st1' m1' st2' m2' /\
                         (corestep_plus Sem3 g3 st2 m2 st2'
                            m2' \/
                          corestep_star Sem3 g3 st2 m2 st2'
                            m2' /\ core_ord23 cd' cd))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 g1 st1 m1 st1' m1')
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
        (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
         corestep_star Sem3 g3 st3 m3 st3' m3' /\
         clos_trans (core_data12 * option C2 * core_data23)
           (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
           (d12, Some st2, d23)).
Proof. intros.
    destruct (core_diagram12 _ _ _ _ CS1 _ _ _ MC12)
      as [st2' [m2' [d12' [MC12' Y]]]]. clear core_diagram12.
    assert (ZZ: corestep_plus Sem2 g2 st2 m2 st2' m2'
      \/  (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
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
                   (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
                      (corestep_star Sem3 g3 st3 m3 st3' m3' /\
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
          clear st1 m1 st1' m1'. clear C1 Sem1 match_core12.

    revert j23 d23 st2 m2 st3 m3 H MC23.
    induction x; intros.
      (*base case*) simpl in H.
          destruct H as [c2 [m2'' [? ?]]].
          inv H0.
          destruct (core_diagram23 _ _ _ _ H _ _ _ _ MC23)
            as [st3' [m3' [d23' [j' [InjInc [InjSep [? ?]]]]]]].
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
          destruct (core_diagram23 _ _ _ _  H _ _ _ _ MC23)
            as [c3' [m3' [d'' [j' [InjInc [InjSep [? ?]]]]]]].
          specialize (IHx _ _ _ _ _ _ H0 H1).
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
    right. split. exists O. simpl; auto.
    apply t_step. constructor 1; auto.
Qed.

Lemma extinj: forall
     (SimExt12 : Forward_simulation_extends Sem1 Sem2 g1 g2 epts12)
     (SimInj23 : Forward_simulation_inject Sem2 Sem3 g2 g3 epts23),
      Forward_simulation_inject Sem1 Sem3 g1 g3 epts13.
Proof. intros.
         destruct SimExt12 as [core_data12 match_core12 core_ord12 core_ord_wf12
                               genvs_dom_eq12 match_validblocks12 core_diagram12
                               core_initial12 core_halted12 core_at_external12
                               core_after_external12].
         destruct SimInj23 as [core_data23 match_core23 core_ord23 core_ord_wf23
                      match_validblocks23 genvs_dom_eq23 match_genv23
                      core_diagram23 core_initial23
                      core_halted23 core_at_external23 core_after_external23].
         eapply Forward_simulation_inj.Build_Forward_simulation_inject with
                (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                (match_state := fun d j c1 m1 c3 m3 =>
                  match d with (d1,X,d2) => exists c2, exists m2, X=Some c2 /\
                    match_core12 d1 c1 m1 c2 m2 /\ match_core23 d2 j c2 m2 c3 m3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*match_validblocks*) intros. rename c2 into c3.  rename m2 into m3.
                 destruct d as [[d12 cc2] d23].
                 destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                 destruct (match_validblocks23 _ _ _ _ _ _ MC23 _ _ _ H0).
                 split; trivial.
                 eapply (match_validblocks12 _ _ _ _ _ MC12); try eassumption.
            (*genvs_dom_eq*)
                 eapply genvs_domain_eq_trans; eauto.
            (*match_genv*)
                 clear match_validblocks12 match_validblocks23
                       core_initial23 core_diagram23 core_halted23
                       core_at_external23 core_after_external23
                       core_initial12 core_halted12 core_diagram12
                       core_at_external12 core_after_external12.
                 intros. rename c2 into c3. rename m2 into m3.
                 destruct d as [[d12 cc2] d23].
                 destruct H as [c2 [m2 [X [? ?]]]]; subst.
                 apply meminj_preserves_genv2blocks.
                 specialize (match_genv23 _ _ _ _ _ _ H0).
                 apply meminj_preserves_genv2blocks in match_genv23.
                 eapply genvs_domain_eq_preserves; eassumption.
            (*core_diagram*)
                 clear core_initial23 core_halted23 core_at_external23
                   core_after_external23 core_initial12  core_halted12
                   core_at_external12 core_after_external12
                   EPC epts12 epts23 epts13.
                 intros. rename st2 into st3. rename m2 into m3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [X [? ?]]]]; subst.
                 eapply (diagram_extinj _ _ _ core_diagram12 _ _ _ core_diagram23); try eassumption.
                       intros. eapply (match_validblocks12 _ _ _ _ _ H2). apply H3.
            (*initial_core*)
                 intros. rename v2 into v3. rename vals2 into vals3. rename m2 into m3.
                 rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                 destruct (core_initial12 _ _ _ EP12 _ _ _ _
                            ( forall_lessdef_refl vals1) (Mem.extends_refl m1))
                   as [d12 [c11 [c2 [Ini1 [Ini2 MC12]]]]]. rewrite Ini1 in H0. inv H0.
                 destruct (core_initial23 _ _ _ EP23 _ _ _ _ _ _  Ini2 H1 H2)
                   as [d23 [c3 [Ini3 MC23]]].
                 apply meminj_preserves_genv2blocks.
                    apply meminj_preserves_genv2blocks in H3.
                    apply (genvs_domain_eq_preserves g1); assumption.
                 exists (d12,Some c2, d23). exists c3.
                 split; trivial. exists c2. exists m1. split; trivial. split; trivial.
             (*halted*)
                 intros. rename c2 into c3. rename m2 into m3.
                 destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                 apply (core_halted12 _ _ _ _ _ _ MC12) in H0; try assumption.
                 destruct H0 as [v2 [LD12 [SH2 Ext12]]].
                 apply (core_halted23 _ _ _ _ _ _ _ MC23) in SH2; try assumption.
                 destruct SH2 as [v3 [InjV23 [SH3 InjM23]]].
                 exists v3. split. eapply val_lessdef_inject_compose; eassumption.
                       split; trivial.
                       eapply Mem.extends_inject_compose; eassumption.
             (*atexternal*)
                 intros. rename st2 into st3. rename m2 into m3.
                 destruct cd as [[d12 cc2] d23].
                 destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                 apply (core_at_external12 _ _ _ _ _ _ _ _ MC12) in H0; try assumption.
                 destruct H0 as [vals2 [Ext12 [LD12 AtExt2]]].
                 apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2; try assumption.
                 destruct AtExt2 as [Inj23 [vals3 [InjVals23 AtExt3]]].
                 split. eapply Mem.extends_inject_compose; eassumption.
                 exists vals3.
                 split. eapply forall_val_lessdef_inject_compose; eassumption.
                 auto.
             (*after_external*)
                 clear core_diagram12 core_diagram23 core_initial12 core_initial23
                       core_halted12 core_halted23.
                 intros. rename st2 into st3. rename m2 into m3.
                 rename ret2 into ret3. rename m2' into m3'.
                 destruct cd as [[d12 cc2] d23].
                 destruct H0 as [c2 [m2 [X [MC12 MC23]]]]; subst.
                 destruct (core_at_external12 _ _ _ _ _ _ _ _ MC12 H1)  as
                   [vals2 [Ext12 [LDVals12 AtExt2]]]; try assumption; clear core_at_external12.
                 destruct (core_at_external23 _ _ _ _ _ _ _ _ _  MC23 AtExt2)  as
                   [Inj23 [vals3 [InjVals23 AtExt3]]]; try assumption; clear core_at_external23.
                 assert (UnchOn3 : Mem.unchanged_on (loc_out_of_reach j m2) m3 m3').
                   split; intros; eapply H10; trivial.
                   eapply extends_loc_out_of_reach; eassumption.
                   intros.  eapply extends_loc_out_of_reach; eassumption.
                 assert (Sep23: inject_separated j j' m2 m3).
                 intros b. intros. destruct (H4 _ _ _ H0 H11). split; trivial.
                 intros N. apply H12.  inv Ext12. unfold Mem.valid_block. rewrite mext_next. apply N.
                 destruct (MEMAX.interpolate_EI _ _ _ Ext12 H7 _ _ Inj23 _ H9 _ H5 H10 H3 H4 H8)
                   as [m2' [Fwd2' [Ext12' [Inj23' [UnchOn2 UnchOn2j]]]]].
                 destruct (core_after_external12 _ _ _ _ _ _ _ _ ret1 ret1 _ _ _ MC12 H1 AtExt2
                             LDVals12 H7 Fwd2' UnchOn2 (Val.lessdef_refl _) Ext12')
                   as [c1' [c2' [d12' [AftExt1 [AftExt2 MC12']]]]];
                     try assumption; clear core_after_external12.
                 assert (PG2: meminj_preserves_globals g2 j).
                 apply (match_genv23 _ _ _ _ _ _ MC23).
                 destruct (core_after_external23 _ j j' _ _ _ _ vals2 ret1 _ _ _ ret3 _ Inj23
                             MC23 AtExt2 PG2 H3 Sep23 Inj23' H6 Fwd2' UnchOn2j H9 UnchOn3)
                 as [d23' [cc2' [c3' [AftExt22 [AftExt3 MC23']]]]];
                   try assumption; clear core_after_external23.
                 rewrite AftExt22 in AftExt2. inv AftExt2.
                 exists (d12',Some c2', d23'). exists c1'. exists c3'.
                   split; trivial. split; trivial.
                 exists c2'. exists m2'. intuition.
Qed.
End EXTINJ.

Lemma coop_sim_trans_CaseExt: forall
     (SimExt12 : Forward_simulation_extends Sem1 Sem2 g1 g2 epts12)
     (SIM23 : coop_sim Sem2 Sem3 g2 g3 epts23),
     coop_sim Sem1 Sem3 g1 g3 epts13.
Proof. intros.
  induction SIM23; intros.
  eapply coop_sim_ext.
    apply (exteq SimExt12 R).
  eapply coop_sim_ext.
    apply (extext SimExt12 R).
  eapply coop_sim_inj.
    apply (extinj SimExt12 R).
Qed.

End CaseEXT.

Section CaseINJ.
  Import Forward_simulation_inj.

Section INJEQ.
  Import Forward_simulation_eq.

Lemma  diagram_injeq: forall
(core_data12 : Type)
(match_core12 : core_data12 -> meminj -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 g1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (j : meminj) (m2 : mem),
                 match_core12 cd j st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       exists j' : meminj,
                         inject_incr j j' /\
                         inject_separated j j' m1 m2 /\
                         match_core12 cd' j' st1' m1' st2' m2' /\
                         (corestep_plus Sem2 g2 st2 m2 st2' m2' \/
                          corestep_star Sem2 g2 st2 m2 st2' m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> C3 -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(core_diagram23 : forall (st1 : C2) (m : mem) (st1' : C2) (m' : mem),
                 corestep Sem2 g2 st1 m st1' m' ->
                 forall (d : core_data23) (st2 : C3),
                 match_core23 d st1 st2 ->
                 exists st2' : C3,
                   exists d' : core_data23,
                     match_core23 d' st1' st2' /\
                     (corestep_plus Sem3 g3 st2 m st2' m' \/
                      corestep_star Sem3 g3 st2 m st2' m' /\
                      core_ord23 d' d))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 g1 st1 m1 st1' m1')
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
        (corestep_plus Sem3 g3 st3 m2 st3' m2' \/
         corestep_star Sem3 g3 st3 m2 st3' m2' /\
         clos_trans (core_data12 * option C2 * core_data23)
           (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
           (d12, Some st2, d23)).
Proof. intros.
    destruct (core_diagram12 _ _ _ _ CS1 _ _ _ _ MC12)
      as [st2' [m2' [d12' [j' [InjIncr [InjSep [MC12' Y]]]]]]]; clear core_diagram12.
    assert (ZZ: corestep_plus Sem2 g2 st2 m2 st2' m2'
      \/  (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
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
           destruct IHx as [c3'' [m3'' [[[d12''' cc2''] d23'']
             [j'' [InjIncr' [InjSep'' [[c2'' [X [MC12'' MC23'']]] ?]]]]]]].
             intros b; intros. trivial. apply inject_separated_same_meminj. subst.
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
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Lemma injeq: forall
      (SimInj12 : Forward_simulation_inject Sem1 Sem2 g1 g2 epts12)
      (SimEq23 : Forward_simulation_equals Sem2 Sem3 g2 g3 epts23),
      Forward_simulation_inject Sem1 Sem3 g1 g3 epts13.
Proof. intros.
  destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12
            match_vb12 genvs_dom_eq12 match_genv12
            core_diagram12 core_initial12 core_halted12
            core_at_external12 core_after_external12].
   destruct SimEq23 as [core_data23 match_core23 core_ord23 core_ord_wf23
            genvs_dom_eq23 core_diagram23 core_initial23
            core_halted23 core_at_external23 core_after_external23].
    eapply Forward_simulation_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 =>
                   match d with (d1,X,d2) => exists c2, X=Some c2 /\
                     match_core12 d1 j c1 m1 c2 m3 /\ match_core23 d2 c2 c3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*match_validblocks*) intros. rename c2 into c3.  rename m2 into m3.
                 destruct d as [[d12 cc2] d23].
                 destruct H as [c2 [X [MC12 MC23]]]; subst.
                 eapply (match_vb12 _ _ _ _ _ _ MC12); try eassumption.
            (*genvs_dom_eq*)
              eapply genvs_domain_eq_trans; eauto.
            (*match_genv*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23
                       core_initial12  core_halted12 core_at_external12 core_after_external12
                       match_vb12 core_diagram12 core_diagram23 EPC epts12  epts23 epts13.
                 intros. rename c2 into c3.
                 destruct d as [[d12 cc2] d23]. destruct H as [c2 [X [? ?]]]; subst.
                 apply (match_genv12 _ _ _ _ _ _ H).
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23
                   core_after_external23 core_initial12  core_halted12
                   core_at_external12 core_after_external12
                   EPC epts12  epts23 epts13.
                 intros. rename st2 into st3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [X [? ?]]]; subst.
                 eapply (diagram_injeq _ _ _ core_diagram12 _ _ _ core_diagram23); try eassumption.
             (*initial_core*)
                  intros. rename v2 into v3. rewrite (EPC v1 v3 sig) in H.
                    destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 H1 H2 H3)
                    as [d12 [c2 [Ini2 MC12]]].
                  destruct (core_initial23 _ _ _ EP23 vals2)
                    as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2,d23). exists c3. split; trivial.
                  exists c2. split; trivial. split; trivial.
             (*halted*)
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
                destruct H0 as [Minj12 [vals2 [VInj12 AtExt2]]].
                specialize (core_at_external23 _ _ _ _ _ _ MC23 AtExt2).
                split; trivial.
                exists vals2. intuition.
             (*after_external*)
                intros. rename st2 into st3.
                destruct cd as [[d12 cc2] d23]. destruct H0 as [c2 [X [MC12 MC23]]]; subst.
                destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 H1) as
                  [MInj12 [vals2 [VInj12 AtExt2]]]; try assumption.
                specialize (core_at_external23 _ _ _ _ _ _ MC23 AtExt2).
                rename core_at_external23 into AtExt3.
                destruct (core_after_external12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ MInj12 MC12 H1
                  (match_genv12 _ _ _ _ _ _ MC12) H3 H4 H5 H6 H7 H8 H9 H10)
                  as [d12' [c1' [c2' [AftExt1 [AftExt2 MS12']]]]].
                destruct (core_after_external23 _ _ _ ret2 _ _ _ MC23 AtExt2 AtExt3)
                  as [c22' [c3' [d23' [AftExt22 [AftExt3 MS23']]]]].
                rewrite AftExt22 in AftExt2. inv AftExt2.
                exists (d12',Some c2',d23'). exists c1'. exists c3'.
                split; trivial. split; trivial.
                exists c2'. intuition.
Qed.
End INJEQ.

Section INJEXT.
  Import Forward_simulation_ext.
Lemma  diagram_injext: forall
(core_data12 : Type)
(match_core12 : core_data12 -> meminj -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 g1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (j : meminj) (m2 : mem),
                 match_core12 cd j st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       exists j' : meminj,
                         inject_incr j j' /\
                         inject_separated j j' m1 m2 /\
                         match_core12 cd' j' st1' m1' st2' m2' /\
                         (corestep_plus Sem2 g2 st2 m2 st2' m2' \/
                          corestep_star Sem2 g2 st2 m2 st2' m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                 corestep Sem2 g2 st1 m1 st1' m1' ->
                 forall (cd : core_data23) (st2 : C3) (m2 : mem),
                 match_core23 cd st1 m1 st2 m2 ->
                 exists st2' : C3,
                   exists m2' : mem,
                     exists cd' : core_data23,
                       match_core23 cd' st1' m1' st2' m2' /\
                       (corestep_plus Sem3 g3 st2 m2 st2'
                          m2' \/
                        corestep_star Sem3 g3 st2 m2 st2'
                          m2' /\ core_ord23 cd' cd))
(st1 : C1)
(m1 : mem)
(st1' : C1)
(m1' : mem)
(CS1 : corestep Sem1 g1 st1 m1 st1' m1')
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
        (corestep_plus Sem3 g3 st3 m3 st2' m2' \/
         corestep_star Sem3 g3 st3 m3 st2' m2' /\
         clos_trans (core_data12 * option C2 * core_data23)
           (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
           (d12, Some st2, d23)).
Proof. intros.
    destruct (core_diagram12 _ _ _ _ CS1 _ _ _ _ MC12)
      as [st2' [m2' [d12' [j' [InjIncr [InjSep [MC12' Y]]]]]]]; clear core_diagram12.
    assert (ZZ: corestep_plus Sem2 g2 st2 m2 st2' m2'
      \/  (st2,m2) = (st2',m2') /\ core_ord12 d12' d12).
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
                   (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
                      (corestep_star Sem3 g3 st3 m3 st3' m3' /\
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

    clear MC12 MC12' MatchHyp12.
          clear InjSep InjIncr j23 j' st1 m1 st1' m1'.
          clear C1 Sem1 match_core12 g1.

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
    right. split. exists O. simpl; auto.
                       apply t_step. constructor 1; auto.
Qed.

Lemma injext: forall
      (SimInj12 : Forward_simulation_inject Sem1 Sem2 g1 g2 epts12)
      (SimExt23 : Forward_simulation_extends Sem2 Sem3 g2 g3 epts23),
      Forward_simulation_inject Sem1 Sem3 g1 g3 epts13.
Proof. intros.
    destruct SimInj12 as [core_data12 match_core12 core_ord12 core_ord_wf12
                          match_vb12 genv_dom_eq12 match_genv12
                          core_diagram12 core_initial12 core_halted12
                          core_at_external12 core_after_external12].
    destruct SimExt23 as [core_data23 match_core23 core_ord23 core_ord_wf23
                          genv_dom_eq23 match_vb23 core_diagram23
                          core_initial23 core_halted23
                          core_at_external23 core_after_external23].
    eapply Forward_simulation_inj.Build_Forward_simulation_inject with
                 (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
                 (match_state := fun d j c1 m1 c3 m3 =>
                   match d with (d1,X,d2) =>
                     exists c2, exists m2, X = Some c2 /\
                       match_core12 d1 j c1 m1 c2 m2 /\ match_core23 d2 c2 m2 c3 m3 end).
            (*well_founded*)
                 eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
            (*match_validblocks*)
                 intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23].
                 destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                 destruct (match_vb12 _ _ _ _ _ _ MC12 _ _ _ H0).
                 split; try eassumption.
                 eapply (match_vb23 _ _ _ _ _ MC23); try eassumption.
            (*genvs_dom_eq*)
              eapply genvs_domain_eq_trans; eauto.
            (*match_genv*)
                 clear core_initial23  core_halted23 core_at_external23 core_after_external23
                       core_initial12  core_halted12 core_at_external12 core_after_external12
                       core_diagram12 core_diagram23  EPC epts12  epts23 epts13.
                 intros. rename c2 into c3. rename m2 into m3.
                 destruct d as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [? ?]]]]; subst.
                 apply (match_genv12 _ _ _ _ _ _ H).
            (*core_diagram*)
                 clear core_initial23  core_halted23 core_at_external23
                   core_after_external23 core_initial12  core_halted12
                   core_at_external12 core_after_external12
                   EPC epts12  epts23 epts13.
                 intros. rename st2 into st3. rename m2 into m3.
                 destruct cd as [[d12 cc2] d23]. destruct H0 as [st2 [m2 [X [? ?]]]]; subst.
                 eapply (diagram_injext _ _ _ core_diagram12 _ _ _ core_diagram23); try eassumption.
           (*initial_core*)
                  intros. rename m2 into m3. rename v2 into v3.
                    rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
                  destruct (core_initial12 _ _ _ EP12 _ _ _ _ _ _ H0 H1 H2 H3)
                    as [d12 [c2 [Ini2 MC12]]].
                  destruct (core_initial23 _ _ _ EP23 _ _ _ _
                    (forall_lessdef_refl vals2) (extends_refl m3))
                    as [d23 [c22 [c3 [Ini22 [Ini3 MC23]]]]].
                  rewrite Ini22 in Ini2. inv Ini2.
                  exists (d12,Some c2,d23). exists c3. split; trivial.
                  exists c2. exists m3. split; trivial. split; assumption.
           (*halted*)
                  intros. rename c2 into c3. rename m2 into m3.
                  destruct cd as [[d12 cc2] d23]. destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                  apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0; try assumption.
                  destruct H0 as [v2 [V12 [SH2 MInj12]]].
                  apply (core_halted23 _ _ _ _ _ _ MC23) in SH2; try assumption.
                  destruct SH2 as [v3 [V23 [SH3 Ext23]]].
                  exists v3. split. eapply valinject_lessdef; eassumption.
                    split; trivial.
                    eapply Mem.inject_extends_compose; eassumption.
             (*atexternal*)
                  intros. rename st2 into st3. rename m2 into m3.
                  destruct cd as [[d12 cc2] d23].
                  destruct H as [c2 [m2 [X [MC12 MC23]]]]; subst.
                  apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0; try assumption.
                  destruct H0 as [Minj12 [vals2 [VInj12 AtExt2]]].
                  apply (core_at_external23 _ _ _ _ _ _ _ _ MC23) in AtExt2; try assumption.
                  destruct AtExt2 as [vals3 [Mext23 [LD23 AtExt3]]].
                  split. eapply Mem.inject_extends_compose; eassumption.
                  exists vals3.
                    split. eapply forall_valinject_lessdef; eassumption.
                    auto.
             (*after_external*)
                  clear core_diagram12 core_diagram23 core_initial12 core_initial23
                    core_halted12 core_halted23.
                  intros. rename st2 into st3. rename m2 into m3.
                  rename m2' into m3'. rename ret2 into ret3.
                  destruct cd as [[d12 cc2] d23].
                  destruct H0 as [c2 [m2 [X [MC12 MC23]]]]; subst.
                  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 H1)
                    as [Minj12 [vals2 [ValsLD12 AtExt2]]]; try assumption; clear core_at_external12.
                  destruct (core_at_external23 _ _ _ _ _ _ _ _ MC23 AtExt2)
                    as [vals3 [MExt23 [ValsLD23 AtExt3]]]; try assumption; clear core_at_external23.
                  assert (Sep12: inject_separated j j' m1 m2).
                    intros b; intros. destruct (H4 _ _ _ H0 H11). split; trivial.
                    intros N. apply H13. inv MExt23. unfold Mem.valid_block.
                    rewrite <- mext_next. apply N.
                  assert (UnchLOOB23_3': Mem.unchanged_on (loc_out_of_bounds m2) m3 m3').
                    eapply inject_LOOR_LOOB; eassumption.
                  destruct (MEMAX.interpolate_IE _ _ _ _ Minj12 H7 _ H3 Sep12 H8 _ _ MExt23
                             H9 H10 H5 UnchLOOB23_3')
                    as [m2' [Fwd2' [MExt23' [Minj12' UnchLOORj1_2]]]].
                  destruct (core_after_external12 _ j j' _ _ _ _ _ ret1 m1' _ m2' ret3 _
                             Minj12 MC12 H1 (match_genv12 _ _ _ _ _ _ MC12) H3
                             Sep12 Minj12' H6 H7 H8 Fwd2' UnchLOORj1_2)
                    as  [d12' [c1' [c2' [AftExt1 [AftExt2 MC12']]]]]; clear core_after_external12.
                  destruct (core_after_external23 _ _ _ _ _ _ _ _ ret3 ret3 _ _ _
                             MC23 AtExt2 AtExt3 ValsLD23
                             Fwd2' H9 UnchLOOB23_3' (Val.lessdef_refl _) MExt23')
                    as [cc2' [c3' [d23' [AftExt22 [AftExt3 MC23']]]]]; clear core_after_external23.
                  rewrite AftExt22 in AftExt2. inv AftExt2.
                  exists (d12',Some c2', d23'). exists c1'. exists c3'.
                  split; trivial. split; trivial.
                  exists c2'. exists m2'. intuition.
Qed.
End INJEXT.

Lemma empty_inj: Mem.inject (Mem.flat_inj 1%positive) Mem.empty Mem.empty.
Proof.
  split.
    split. intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
          rewrite Zplus_0_r. assumption.
       intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
          apply Z.divide_0_r.
    intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
     intros. unfold Mem.flat_inj.
          remember (plt b 1).
          destruct s; trivial. xomega.
    intros. destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
    intros b; intros.
      destruct (flatinj_E _ _ _ _ H0) as [? [? ?]]. subst.
         exfalso. xomega.
    intros.
      destruct (flatinj_E _ _ _ _ H) as [? [? ?]]. subst.
         exfalso. xomega.
Qed.

Lemma empty_fwd: forall m, mem_forward Mem.empty m.
Proof. intros m b Vb.
   unfold Mem.valid_block in Vb. simpl in Vb. exfalso. xomega.
Qed.

Lemma inject_split: forall j m1 m3 (Inj:Mem.inject j m1 m3),
  exists m2 j1 j2, j = compose_meminj j1 j2 /\
       Mem.inject j1 m1 m2 /\ Mem.inject j2 m2 m3.
Proof. intros.
  destruct (MEMAX.interpolate_II _ _ _ empty_inj _
              (empty_fwd m1) _ _ empty_inj _ (empty_fwd m3) _ Inj)
  as [m2 [j1 [j2 [J [Inc1 [Inc2 [Inj12 [Sep12 [Inj23 Sep23]]]]]]]]].
intros b; intros.
  destruct (compose_meminjD_Some _ _ _ _ _ H) as [? [? [? [? [? ?]]]]].
    subst. destruct (flatinj_E _ _ _ _ H0) as [? [? ?]]. subst.
         exfalso. xomega.
intros b; intros.
   unfold Mem.valid_block; simpl; split; intros N; xomega.
split; intros. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
  apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0.
    simpl in H0. exfalso; xomega.
split; intros. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
  apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0.
    simpl in H0. exfalso; xomega.
subst. exists m2, j1, j2. auto.
Qed.

Lemma forall_val_inject_split: forall j1 j2 vals1 vals3
  (V: Forall2 (val_inject (compose_meminj j1 j2)) vals1 vals3),
  exists vals2, Forall2 (val_inject j1) vals1 vals2
             /\ Forall2 (val_inject j2) vals2 vals3.
Proof. intros.
  induction V; simpl.
    exists nil; simpl. split; econstructor.
  destruct IHV as [vals [Vals1 Vals2]].
    destruct (val_inject_split _ _ _ _ H) as [z [VV1 VV2]].
    exists (z::vals).
    split; econstructor; eauto.
Qed.

Lemma initial_inject_split: forall j m1 m3 (Inj:Mem.inject j m1 m3),
  exists m2 j1 j2, j = compose_meminj j1 j2 /\
       Mem.inject j1 m1 m2 /\ Mem.inject j2 m2 m3 /\
      (forall b1 b2 ofs2, j1 b1 = Some(b2,ofs2) -> (b1=b2 /\ ofs2=0)) /\
      (forall (b2 b3 : block) (ofs3 : Z),
      j2 b2 = Some (b3, ofs3) ->
      Mem.flat_inj 1%positive b2 = Some (b3, ofs3) \/
      b2 = Mem.nextblock Mem.empty /\
      compose_meminj j1 j2 (Mem.nextblock Mem.empty) = Some (b3, ofs3) \/
      (exists m : positive,
         b2 = (Mem.nextblock Mem.empty + m)%positive /\
         compose_meminj j1 j2 (Mem.nextblock Mem.empty + m)%positive =
         Some (b3, ofs3))).
Proof. intros.
  destruct (MEMAX.interpolate_II_HeqMKI _ _ _ empty_inj _
             (empty_fwd m1) _ _ empty_inj _ (empty_fwd m3) _ Inj)
    as [m2 [j1 [j2 [J [X [Y [Inc1 [Inc2 [Inj12 [_ [Inj23 [? [? [? [XX3 XX4]]]]]]]]]]]]]]].
intros b; intros.
  destruct (compose_meminjD_Some _ _ _ _ _ H) as [? [? [? [? [? ?]]]]].
    subst. destruct (flatinj_E _ _ _ _ H0) as [? [? ?]]. subst.
         exfalso. xomega.
intros b; intros.
   unfold Mem.valid_block; simpl; split; intros N; xomega.
split; intros. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
  apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
split; intros. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
  apply Mem.perm_valid_block in H0. unfold Mem.valid_block in H0. simpl in H0. exfalso; xomega.
subst. exists m2, j1, j2.
  split; trivial.
  split; trivial.
  split. trivial.
  split; trivial.
  intros. clear - H2 XX3.
    destruct (XX3 _ _ _ H2) as [AA | [AA | AA]].
    apply flatinj_E in AA. destruct AA as [? [? ?]]; subst. intuition.
    destruct AA as [? [? ?]]; subst. intuition.
    destruct AA as [mm [[? ?] ?]]; subst. intuition.
Qed.

Section INJINJ.
Lemma diagram_injinj: forall
(core_data12 : Type)
(match_core12 : core_data12 -> meminj -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 g1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (j : meminj) (m2 : mem),
                 match_core12 cd j st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       exists j' : meminj,
                         inject_incr j j' /\
                         inject_separated j j' m1 m2 /\
                         match_core12 cd' j' st1' m1' st2' m2' /\
                         (corestep_plus Sem2 g2 st2 m2 st2' m2' \/
                          corestep_star Sem2 g2 st2 m2 st2' m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> meminj -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                   corestep Sem2 g2 st1 m1 st1' m1' ->
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
                           (corestep_plus Sem3 g3 st2 m2
                              st2' m2' \/
                            corestep_star Sem3 g3 st2 m2
                              st2' m2' /\ core_ord23 cd' cd))
 (MatchHyp12: forall d12 j12 c1 m1 c2 m2,  match_core12 d12 j12 c1 m1 c2 m2 ->
                    forall b1 b2 ofs, j12 b1 = Some (b2,ofs) -> Mem.valid_block m1 b1 /\ Mem.valid_block m2 b2)
 (MatchHyp23: forall d23 j23 c2 m2 c3 m3,  match_core23 d23 j23 c2 m2 c3 m3 ->
                    forall b1 b2 ofs, j23 b1 = Some (b2,ofs) -> Mem.valid_block m2 b1 /\ Mem.valid_block m3 b2)
 (st1 : C1)
  (m1 : mem)
  (st1' : C1)
  (m1' : mem)
  (CS1 : corestep Sem1 g1 st1 m1 st1' m1')
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
           (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
            corestep_star Sem3 g3 st3 m3 st3' m3' /\
            clos_trans (core_data12 * option C2 * core_data23)
              (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
              (d12, Some st2, d23)).
Proof.
  intros.
  destruct (core_diagram12 _ _ _ _ CS1 _ _ _ _ MC12)
    as [st2' [m2' [d12' [j12' [InjIncr12 [InjSep12 [MC12' Y]]]]]]]; clear core_diagram12.
  assert (ZZ: corestep_plus Sem2 g2 st2 m2 st2' m2' \/
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
    (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
      (corestep_star Sem3 g3 st3 m3 st3' m3' /\
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
  clear C1 Sem1 match_core12 g1.
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

Lemma diagram_injinj_injsep: forall
(core_data12 : Type)
(match_core12 : core_data12 -> meminj -> C1 -> mem -> C2 -> mem -> Prop)
(core_ord12 : core_data12 -> core_data12 -> Prop)
(core_diagram12 : forall (st1 : C1) (m1 : mem) (st1' : C1) (m1' : mem),
                 corestep Sem1 g1 st1 m1 st1' m1' ->
                 forall (cd : core_data12) (st2 : C2) (j : meminj) (m2 : mem),
                 match_core12 cd j st1 m1 st2 m2 ->
                 exists st2' : C2,
                   exists m2' : mem,
                     exists cd' : core_data12,
                       exists j' : meminj,
                         inject_incr j j' /\
                         inject_separated j j' m1 m2 /\
                         match_core12 cd' j' st1' m1' st2' m2' /\
                         (corestep_plus Sem2 g2 st2 m2 st2' m2' \/
                          corestep_star Sem2 g2 st2 m2 st2' m2' /\ core_ord12 cd' cd))
(core_data23 : Type)
(match_core23 : core_data23 -> meminj -> C2 -> mem -> C3 -> mem -> Prop)
(core_ord23 : core_data23 -> core_data23 -> Prop)
(core_diagram23 : forall (st1 : C2) (m1 : mem) (st1' : C2) (m1' : mem),
                   corestep Sem2 g2 st1 m1 st1' m1' ->
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
                           (corestep_plus Sem3 g3 st2 m2
                              st2' m2' \/
                            corestep_star Sem3 g3 st2 m2
                              st2' m2' /\ core_ord23 cd' cd))
 (MatchHyp12: forall d12 j12 c1 m1 c2 m2,  match_core12 d12 j12 c1 m1 c2 m2 ->
              forall b1 b2 ofs, j12 b1 = Some (b2,ofs) -> Mem.valid_block m1 b1
                /\ Mem.valid_block m2 b2)
 (MatchHyp23: forall d23 j23 c2 m2 c3 m3,  match_core23 d23 j23 c2 m2 c3 m3 ->
              forall b1 b2 ofs, j23 b1 = Some (b2,ofs) -> Mem.valid_block m2 b1
                /\ Mem.valid_block m3 b2)
 (st1 : C1)
  (m1 : mem)
  (st1' : C1)
  (m1' : mem)
  (CS1 : corestep Sem1 g1 st1 m1 st1' m1')
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
                    match_core23 d2 j23' st2' m2' st3' m3' /\
                    inject_incr j12 j12' /\
                    inject_incr j23 j23' /\
                    inject_separated j12 j12' m1 m2 /\
                    inject_separated j23 j23' m2 m3) /\
           (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
            corestep_star Sem3 g3 st3 m3 st3' m3' /\
            clos_trans (core_data12 * option C2 * core_data23)
              (sem_compose_ord_eq_eq core_ord12 core_ord23 C2) cd'
              (d12, Some st2, d23)).
Proof.
  intros.
  destruct (core_diagram12 _ _ _ _ CS1 _ _ _ _ MC12)
    as [st2' [m2' [d12' [j12' [InjIncr12 [InjSep12 [MC12' Y]]]]]]]; clear core_diagram12.
  assert (ZZ: corestep_plus Sem2 g2 st2 m2 st2' m2' \/
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
    (corestep_plus Sem3 g3 st3 m3 st3' m3' \/
      (corestep_star Sem3 g3 st3 m3 st3' m3' /\
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
    split. exists st2'. exists m2'. exists j12'. exists j23'. intuition.
    apply ZZ.
  clear MC12 InjIncr12 InjSep12 MC12' MatchHyp12.
  clear st1 m1 st1' m1' j12 j12'.
  clear C1 Sem1 match_core12 g1.
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
   split. exists st2'. exists m2'. exists j12'. exists j23. intuition.
     apply inject_separated_same_meminj.
   right. split. exists O. simpl; auto.
   apply t_step. constructor 1; auto.
Qed.

Lemma injinj: forall
  (SimInj12 : Forward_simulation_inject Sem1 Sem2 g1 g2 epts12)
  (SimInj23 : Forward_simulation_inject Sem2 Sem3 g2 g3 epts23),
   Forward_simulation_inject Sem1 Sem3 g1 g3 epts13.
Proof. intros.
  destruct SimInj12
    as [core_data12 match_core12 core_ord12 core_ord_wf12
        match_validblock12 genvs_dom_eq12 match_genv12
        core_diagram12 core_initial12 core_halted12
        core_at_external12 core_after_external12].
  destruct SimInj23
    as [core_data23 match_core23 core_ord23 core_ord_wf23
        match_validblock23 genvs_dom_eq23 match_genv23
        core_diagram23 core_initial23 core_halted23
        core_at_external23 core_after_external23].
  eapply Forward_simulation_inj.Build_Forward_simulation_inject with
    (core_ord := clos_trans _ (sem_compose_ord_eq_eq core_ord12 core_ord23 C2))
    (match_state := fun d j c1 m1 c3 m3 =>
      match d with (d1,X,d2) =>
        exists c2, exists m2, exists j1, exists j2,
          X=Some c2 /\ j = compose_meminj j1 j2 /\
          meminj_preserves_globals g1 j1 /\
          meminj_preserves_globals g2 j2 /\
          match_core12 d1 j1 c1 m1 c2 m2 /\ match_core23 d2 j2 c2 m2 c3 m3
      end).
 (*well_founded*)
  eapply wf_clos_trans. eapply well_founded_sem_compose_ord_eq_eq; assumption.
 (*match_validblocks*)
  intros. rename c2 into c3.  rename m2 into m3. destruct d as [[d12 cc2] d23].
  destruct H as [c2 [m2 [j12 [j23 [X [J [PG1 [PG2 [MC12 MC23]]]]]]]]]; subst.
  apply compose_meminjD_Some in H0.
  destruct H0 as [b11 [ofs11 [ofs12 [Hb [Hb1 Hdelta]]]]].
  split. eapply (match_validblock12 _ _ _ _ _ _ MC12); try eassumption.
  eapply (match_validblock23 _ _ _ _ _ _ MC23); try eassumption.
 (*genvs_dom_eq*)
  eapply genvs_domain_eq_trans; eauto.
 (*match_genv*)
  clear core_initial23  core_halted23 core_at_external23 core_after_external23
        core_initial12  core_halted12 core_at_external12 core_after_external12
        core_diagram12 core_diagram23 match_validblock12 match_validblock23 EPC epts12 epts23 epts13.
  intros. rename c2 into c3. rename m2 into m3.
  destruct d as [[d12 cc2] d23].
  destruct H as [c2 [m2 [j12 [j23 [X [? [PG1 [PG2 [MC12 MC23]]]]]]]]]; subst.
  apply meminj_preserves_genv2blocks.
  apply meminj_preserves_genv2blocks in PG1.
  apply meminj_preserves_genv2blocks in PG2.
  eapply meminj_preserves_globals_ind_compose; try eassumption.
 (*core_diagram*)
  clear core_initial23  core_halted23 core_at_external23 core_after_external23
    core_initial12  core_halted12 core_at_external12 core_after_external12
    EPC epts12 epts23 epts13.
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [st2 [m2 [j12 [j23 [X [? [PG1 [PG2 [MC12 MC23]]]]]]]]]; subst.
  destruct (diagram_injinj_injsep _ _ _ core_diagram12 _ _ _ core_diagram23
    match_validblock12 match_validblock23 _ _ _ _ H _ _ _ _ _ _ _ _ MC12 MC23)
    as [c3' [m3' [[[d12' cc2'] d23'] [j' [INC [SEP [X CS3]]]]]]].
  exists c3', m3', ((d12', cc2'), d23'), j'.
  split; trivial.
  split; trivial.
  split; trivial.
  clear CS3.
  destruct X as [c2' [m2' [j12' [j23' [Y [J' [MC12' [MC23' [INC12 [INC23 [SEP12 SEP23]]]]]]]]]]].
  exists c2', m2', j12', j23'.
  split; trivial.
  split; trivial.
  split. solve [eapply meminj_preserves_incr_sep_vb; try eassumption; eauto].
  split. solve [eapply meminj_preserves_incr_sep_vb; try eassumption; eauto].
  split; trivial.
 (*initial_core*)
  clear core_diagram23  core_halted23 core_at_external23 core_after_external23
    core_diagram12  core_halted12 core_at_external12 core_after_external12.
  intros. rename m2 into m3. rename v2 into v3. rename vals2 into vals3.
  rewrite (EPC v1 v3 sig) in H. destruct H as [v2 [EP12 EP23]].
  destruct (initial_inject_split _ _ _ H1) as [m2 [j1 [j2 [J [Inj12 [Inj23 [XX3 XX4]]]]]]].
  subst.
  destruct (forall_val_inject_split _ _ _ _ H2) as [vals2 [ValsInj12 ValsInj23]].
  assert (PG1: meminj_preserves_globals g1 j1).
    clear - XX3 H3.
    apply meminj_preserves_genv2blocks.
     apply meminj_preserves_genv2blocks in H3.
      destruct H3 as [AA [BB CC]].
      split; intros.
         specialize (AA _ H).
         destruct (compose_meminjD_Some _ _ _ _ _ AA)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear AA.
         destruct (XX3 _ _ _ J1); subst. trivial.
      split; intros.
         specialize (BB _ H).
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         destruct (XX3 _ _ _ J1); subst. trivial.
      destruct (XX3 _ _ _ H0); subst. trivial.
  assert (PG2: meminj_preserves_globals g2 j2).
    clear - XX4 XX3 PG1 H3 genvs_dom_eq12.
    apply meminj_preserves_genv2blocks.
     apply meminj_preserves_genv2blocks in H3.
      destruct H3 as [AA [BB CC]].
     apply meminj_preserves_genv2blocks in PG1.
      destruct PG1 as [AA1 [BB1 CC1]].
      destruct genvs_dom_eq12.
      split; intros.
         apply H in H1.
         specialize (AA1 _ H1). specialize (AA _ H1).
         destruct (compose_meminjD_Some _ _ _ _ _ AA)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear AA.
         rewrite J1 in AA1. inv AA1. simpl in D. subst. trivial.
      split; intros.
         apply H0 in H1.
         specialize (BB1 _ H1). specialize (BB _ H1).
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         rewrite J1 in BB1. inv BB1. simpl in D. subst. trivial.
      apply H0 in H1.
         specialize (BB1 _ H1). specialize (BB _ H1). rename b2 into b3.
         destruct (compose_meminjD_Some _ _ _ _ _ BB)
            as [b2 [d1 [d2 [J1 [J2 D]]]]]; subst; clear BB.
         destruct (XX3 _ _ _ J1); subst. simpl in D. subst.
         clear BB1 XX3.
         destruct (XX4 _ _ _ H2) as [XX | [XX | XX]].
           apply flatinj_E in XX. destruct XX as [? [? ?]]; subst. trivial.
           destruct XX as [? ?]; subst.
             apply (CC _ _ _ H1 H4).
           destruct XX as [mm [? ?]]; subst.
             apply (CC _ _ _ H1 H4).
  destruct (core_initial12 _ _ _ EP12 _ _ _ _ vals2 _ H0 Inj12)
     as [d12 [c2 [Ini2 MC12]]]; try assumption.
  destruct (core_initial23 _ _ _ EP23 _ _ _ _ vals3 _ Ini2 Inj23)
     as [d23 [c3 [Ini3 MC23]]]; try assumption.
  exists (d12,Some c2,d23). exists c3.
  split; trivial.
  exists c2, m2, j1, j2. intuition.
 (*halted*)
  intros. rename c2 into c3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23].
  destruct H as [c2 [m2 [j12 [j23 [X [Y [PG1 [PG2 [MC12 MC23]]]]]]]]]; subst.
  apply (core_halted12 _ _ _ _ _ _ _ MC12) in H0; try assumption.
  destruct H0 as [v2 [ValsInj12 [SH2 Minj12]]].
  apply (core_halted23 _ _ _ _ _ _ _ MC23) in SH2; try assumption.
  destruct SH2 as [v3 [ValsInj23 [SH3 MInj23]]].
  exists v3. split. apply (val_inject_compose _ _ _ _ _ ValsInj12 ValsInj23).
  split. trivial.
  eapply Mem.inject_compose; eassumption.
(*atexternal*)
  intros. rename st2 into st3. rename m2 into m3.
  destruct cd as [[d12 cc2] d23].
  destruct H as [st2 [m2 [j1 [j2 [Y [J [PG1 [PG2 [MC12 MC23]]]]]]]]]. subst.
  apply (core_at_external12 _ _ _ _ _ _ _ _ _ MC12) in H0; try assumption.
  destruct H0 as [MInj12 [vals2 [ValsInj12 AtExt2]]].
  apply (core_at_external23 _ _ _ _ _ _ _ _ _ MC23) in AtExt2; try assumption.
  destruct AtExt2 as [MInj23 [vals3 [ValsInj23 AtExt3]]].
  split. eapply Mem.inject_compose; eassumption.
  exists vals3.
  split. eapply forall_val_inject_compose; eassumption.
  auto.
 (*after_external*) clear core_diagram12 core_initial12 core_halted12
  core_diagram23 core_initial23 core_halted23.
  intros. rename st2 into st3. rename m2 into m3.
  rename ret2 into ret3. rename m2' into m3'.
  destruct cd as [[d12 cc2] d23].
  destruct H0 as [st2 [m2 [j1 [j2 [Y [J [PG1 [PG2 [MC12 MC23]]]]]]]]]. subst.
  rename H1 into AtExt1.
  destruct (core_at_external12 _ _ _ _ _ _ _ _ _ MC12 AtExt1)
   as [MInj12 [vals2 [ValsInj12 AtExt2]]].
  destruct (core_at_external23 _ _ _ _ _ _ _ _ _ MC23 AtExt2)
   as [MInj23 [vals3 [ValsInj23 AtExt3]]].
  clear core_at_external12 core_at_external23.
  destruct (MEMAX.interpolate_II _ _ _ MInj12 _ H7 _ _ MInj23 _ H9 _ H5 H3 H4 H8 H10)
    as [m2' [j12' [j23' [X [Incr12 [Incr23 [MInj12' [Fwd2
      [MInj23' [Unch22 [Sep12 [Sep23 [Unch222' Unch2233']]]]]]]]]]]]].
  subst.
  assert (exists ret2, val_inject j12' ret1 ret2 /\ val_inject j23' ret2 ret3).
    apply val_inject_split in H6. destruct H6 as [ret2 [injRet12 injRet23]].
    exists ret2. split; trivial.
  destruct H0 as [ret2 [injRet12 injRet23]].
  assert (Unch111': Mem.unchanged_on (loc_unmapped j1) m1 m1').
    split; intros; apply H8; unfold compose_meminj, loc_unmapped in *.
    rewrite H0. trivial. trivial.
    intros. rewrite H0. trivial. trivial.
  specialize (core_after_external12 _ _ j12' _ _ _ _ _ ret1 m1' m2 m2' ret2 _
     MInj12 MC12 AtExt1 (match_genv12 _ _ _ _ _ _ MC12)
     Incr12 Sep12 MInj12' injRet12 H7 Unch111' Fwd2 Unch22).
  destruct core_after_external12 as [d12' [c1' [c2' [AftExt1 [AftExt2 MC12']]]]].

  specialize (core_after_external23 _ _ j23' _ _ _ _ vals2 ret2 m2' _ m3' ret3 _
     MInj23 MC23 AtExt2 (match_genv23 _ _ _ _ _ _ MC23)
     Incr23 Sep23 MInj23' injRet23 Fwd2 Unch222' H9 Unch2233').
  destruct core_after_external23 as [d23' [cc2' [c3' [AftExt22 [AftExt3 MC23']]]]].
  rewrite AftExt22 in AftExt2. inv AftExt2.
  exists (d12', Some c2', d23'). exists c1'. exists c3'.
  split. assumption.
  split. assumption.
  exists c2'. exists m2'. exists j12'. exists j23'. intuition.
    eapply (meminj_preserves_incr_sep _ j1); try eassumption.
    eapply (meminj_preserves_incr_sep _ j2); try eassumption.
Qed.
End INJINJ.

Lemma coop_sim_trans_CaseInj: forall
     (SimInj12 : Forward_simulation_inject Sem1 Sem2 g1 g2 epts12)
     (SIM23 : coop_sim Sem2 Sem3 g2 g3 epts23),
     coop_sim Sem1 Sem3 g1 g3 epts13.
Proof. intros.
  induction SIM23; intros.
  eapply coop_sim_inj.
    apply (injeq SimInj12 R).
  eapply coop_sim_inj.
    apply (injext SimInj12 R).
  eapply coop_sim_inj.
    apply (injinj SimInj12 R).
Qed.

End CaseINJ.

Theorem coop_sim_trans: forall
        (SIM12: coop_sim Sem1 Sem2 g1 g2 epts12)
        (SIM23: coop_sim Sem2 Sem3 g2 g3 epts23),
        coop_sim Sem1 Sem3 g1 g3 epts13.
Proof.
  intros SIM12.
  induction SIM12. intros SIM23.
    apply coop_sim_trans_CaseEq; assumption.
    apply coop_sim_trans_CaseExt; assumption.
    apply coop_sim_trans_CaseInj; assumption.
Qed.

End Coop_sim_trans. (*End of Section*)
End Forward_simulation_trans. (*End of Module*)
