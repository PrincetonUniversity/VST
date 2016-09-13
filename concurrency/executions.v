(** ** Definitions and properties of machine executions *)
Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Memory.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.dry_context.
Require Import Coqlib.
Require Import msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module Executions (SEM: Semantics)
       (Machines: MachinesSig with Module SEM := SEM)
       (AsmContext: AsmContext SEM Machines).
  Import Machines DryMachine ThreadPool AsmContext.
  Import event_semantics.
  Import Events.

  (** A number of steps of the FineConc machine*)
  Inductive multi_fstep :
    FineConc.MachState -> mem -> FineConc.MachState -> mem -> Prop :=
  | fine_refl : forall ms (m : mem),
      multi_fstep ms m ms m
  | fine_trans : forall i U U'
                        (tp tp' tp'': FineConc.machine_state)
                        (tr tr' tr'': FineConc.event_trace)
                        (m m' m'' : mem),
      FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr ++ tr', tp') m' ->
      multi_fstep (U, tr ++ tr', tp') m' (U', tr ++ tr' ++ tr'', tp'') m'' ->
      multi_fstep (i :: U,tr,tp) m (U',tr ++ tr' ++ tr'',tp'') m''.

  (** Complete executions (until the schedule is empty) of the FineConc machine*)
  Inductive fine_execution :
    FineConc.MachState -> mem -> FineConc.MachState -> mem -> Prop :=
  | fine_completed : forall ms (m : mem),
      FineConc.halted ms ->
      fine_execution ms m ms m
  | fine_exec : forall i U U'
                        (tp tp' tp'': FineConc.machine_state)
                        (tr tr' tr'': FineConc.event_trace)
                        (m m' m'' : mem),
      FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr ++ tr', tp') m' ->
      fine_execution (U, tr ++ tr', tp') m' (U', tr ++ tr' ++ tr'', tp'') m'' ->
      fine_execution (i :: U,tr,tp) m (U',tr ++ tr' ++ tr'',tp'') m''.
  
  (** Complete executions of the SC machine *)
  Inductive sc_execution :
    SC.MachState -> mem -> SC.MachState -> mem -> Prop :=
  | sc_completed : forall ms (m : mem),
      SC.halted ms ->
      sc_execution ms m ms m
  | sc_exec : forall i U U'
                      (tp tp' tp'': SC.machine_state)
                      (tr tr' tr'': SC.event_trace)
                      (m m' m'' : mem),
      SC.MachStep the_ge (i :: U, tr, tp) m (U, tr', tp') m' ->
      sc_execution (U, tr', tp') m' (U', tr'', tp'') m'' ->
      sc_execution (i :: U,tr,tp) m (U',tr'',tp'') m''.


  (*TODO: move to threads_lemmas*)
  Lemma app_eq_nil:
    forall {A:Type} (xs ys : list A),
      xs = xs ++ ys ->
      ys = nil.
  Proof.
    intros.
    erewrite <- app_nil_r in H at 1.
    apply app_inv_head in H; auto.
  Qed.

  (** ** Properties of executions and steps *)
  
  (** A property of steps is that any sequence of events added by
    one external step is a singleton *)
  Lemma fstep_ext_trace:
    forall (a : tid) U
      (i : nat) (tr tr' : SC.event_trace) (tp tp' : thread_pool) 
      (m m' : mem) (ev : machine_event),
      is_external ev ->
      nth_error tr' i = Some ev ->
      FineConc.MachStep the_ge ((a :: U)%SEQ, tr, tp) m 
                        (U, tr ++ tr', tp') m' ->
      tr' = [:: ev].
  Proof.
    intros.
    inversion H1; subst;
    simpl in *;
    try match goal with
        | [H: ?X = app ?X ?Y |- _] =>
          rewrite <- app_nil_r in H at 1;
            apply app_inv_head in H
        end; subst;
    try match goal with
        | [H: nth_error [::] _ = _ |- _] =>
          rewrite nth_error_nil in H;
            discriminate
        end.
    apply app_inv_head in H8.
    subst.
    rewrite list_map_nth in H0.
    destruct (nth_error ev0 i); simpl in H0; try discriminate.
    inv H0.
    simpl in H. by exfalso.
    apply app_inv_head in H8. subst.
    apply nth_error_In in H0. inversion H0; subst; auto.
    simpl in H2. by exfalso.
  Qed.
  
  (** Decomposing steps based on an external event*)
  Lemma multi_fstep_inv_ext:
    forall U U' i tr tr' tp m tp' m' ev
      (Hext: is_external ev)
      (Hi: nth_error tr' i = Some ev)
      (Hexec: multi_fstep (U, tr, tp) m (U', tr ++ tr', tp') m'),
    exists U'' U''' tp'' m'' tr'' tp''' m''',
      multi_fstep (U, tr, tp) m (U'', tr ++ tr'', tp'') m'' /\
      FineConc.MachStep the_ge (U'', tr ++ tr'', tp'') m''
                        (U''', tr ++ tr'' ++ [:: ev], tp''') m''' /\
      multi_fstep (U''', tr ++ tr'' ++ [:: ev], tp''') m'''
                     (U', tr ++ tr', tp') m' /\
      length tr'' = i.
  Proof.
    intros U.
    induction U; intros.
    - inversion Hexec. simpl in *.
      apply app_eq_nil in H3. subst.
      destruct i; simpl in Hi; discriminate.
    - inversion Hexec.
      + rewrite <- app_nil_r in H3 at 1.
        apply app_inv_head in H3; subst.
        rewrite nth_error_nil in Hi. discriminate.
      + subst.
        apply app_inv_head in H6. subst.
        (* need a case analysis on whether it belongs on the first list or not*)
        destruct (i < length tr'0) eqn:Hlt.
        * erewrite nth_error_app1 in Hi by ssromega.
          exists (a :: U), U, tp, m, [::], tp'0, m'0.
          assert (tr'0 = [:: ev]) by (eapply fstep_ext_trace; eauto).
          subst.
          split. rewrite app_nil_r.
          econstructor.
          split. rewrite app_nil_r.
          simpl. eauto.
          split; simpl; eauto.
          destruct i; simpl in *; auto;
          ssromega.
        * erewrite nth_error_app2 in Hi by ssromega.
          specialize (IHU U' _ (tr ++ tr'0) tr'' tp'0 m'0 tp' m' _ Hext Hi).
          rewrite <- app_assoc in IHU.
          specialize (IHU H9).
          destruct IHU as (U'' & U''' & tp'' & m'' & tr''0 & tp''' & m'''
                           & Hexec0' & Hstep & Hexec''' & Hnth).
          exists U'', U''', tp'', m'', (tr'0 ++ tr''0), tp''', m'''.
          split.
          rewrite <- app_assoc in Hexec0'.
          econstructor; eauto.
          split.
          rewrite <- app_assoc.
          repeat rewrite <- app_assoc in Hstep.
          eauto.
          rewrite <- app_assoc.
          rewrite <- app_assoc in Hexec'''.
          split. eauto.
          rewrite app_length.
          rewrite Hnth.
          ssromega.
  Qed.

  (** Decomposing steps on any kind of event. This
    theorem is stronger than the previous one *)
  Lemma multi_fstep_inv:
    forall U U' i tr tr' tp m tp' m' ev
      (Hi: nth_error tr' i = Some ev)
      (Hexec: multi_fstep (U, tr, tp) m (U', tr ++ tr', tp') m'),
    exists U'' U''' tp'' m'' tr'' pre_ev post_ev  tp''' m''',
      multi_fstep (U, tr, tp) m (U'', tr ++ tr'', tp'') m'' /\
      FineConc.MachStep the_ge (U'', tr ++ tr'', tp'') m''
                        (U''', tr ++ tr'' ++ pre_ev ++ [:: ev] ++ post_ev, tp''') m''' /\
      multi_fstep (U''', tr ++ tr'' ++ pre_ev ++ [:: ev] ++ post_ev , tp''') m'''
                     (U', tr ++ tr', tp') m' /\
      length (tr'' ++ pre_ev) = i.
  Proof.
    intros U.
    induction U; intros.
    - inversion Hexec. simpl in *.
      apply app_eq_nil in H3. subst.
      destruct i; simpl in Hi; discriminate.
    - inversion Hexec.
      + rewrite <- app_nil_r in H3 at 1.
        apply app_inv_head in H3; subst.
        rewrite nth_error_nil in Hi. discriminate.
      + subst.
        apply app_inv_head in H6. subst.
        (* need a case analysis on whether it belongs on the first list or not*)
        destruct (i < length tr'0) eqn:Hlt.
        * erewrite nth_error_app1 in Hi by ssromega.
          eapply nth_error_split in Hi.
          destruct Hi as (l1 & l2 & Htr'0 & Hl1).
          exists (a :: U), U, tp, m, [::], l1, l2, tp'0, m'0.
          subst.
          split. rewrite app_nil_r.
          econstructor.
          split. rewrite app_nil_r.
          simpl. eauto.
          split; simpl; eauto.
        * erewrite nth_error_app2 in Hi by ssromega.
          specialize (IHU U' _ (tr ++ tr'0) tr'' tp'0 m'0 tp' m' _ Hi).
          rewrite <- app_assoc in IHU.
          specialize (IHU H9).
          destruct IHU as (U'' & U''' & tp'' & m'' & tr''0 & pre_ev & post_ev
                           & tp''' & m''' & Hexec0' & Hstep & Hexec''' & Hnth).
          exists U'', U''', tp'', m'', (tr'0 ++ tr''0), pre_ev, post_ev, tp''', m'''.
          split.
          rewrite <- app_assoc in Hexec0'.
          econstructor; eauto.
          split.
          rewrite <- app_assoc.
          repeat rewrite <- app_assoc in Hstep.
          eauto.
          rewrite <- app_assoc.
          rewrite <- app_assoc in Hexec'''.
          split. eauto.
          do 2 rewrite app_length.
          rewrite <- plus_assoc.
          rewrite app_length in Hnth.
          rewrite Hnth.
          ssromega.
  Qed.

  (** The trace is irrelevant to further execution of the
  machine. It's just a history of the memory operations *)
  Lemma fstep_trace_irr:
    forall U i tp m tp' m' tr tr'
      (Hstep: FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr', tp') m'),
    forall tr'', exists ev,
        FineConc.MachStep the_ge (i :: U, tr'', tp) m (U, tr'' ++ ev, tp') m'.
  Proof.
    intros.
    inversion Hstep; subst; simpl in *; subst; inv HschedN; pf_cleanup.
    - exists [::]; erewrite cats0; econstructor; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 2; simpl; eauto.
    - exists (map [eta Events.internal tid] ev); econstructor 3; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 4; simpl; eauto.
    - exists [:: Events.external tid ev]; econstructor 5; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 6; simpl; eauto.
    - exists [::]; erewrite cats0; econstructor 7; simpl; eauto.
  Qed.

End Executions.