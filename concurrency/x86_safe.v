(** ** Erasure to X86SC Machine*)

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
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.SC_erasure.
Require Import concurrency.x86_context.
Require Import ccc26x86.Asm ccc26x86.Asm_coop.
Require Import Coqlib.
Require Import msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module X86CoreErasure <: CoreErasure X86SEM.
  Import X86SEM ValErasure event_semantics.
  
  Definition erased_reg (r:PregEq.t) (rs rs' : regset) : Prop :=
    erased_val (Pregmap.get r rs) (Pregmap.get r rs').
  
  Definition erased_regs rs rs' : Prop :=
    forall r, erased_reg r rs rs'.

  Definition erased_loader (l l' : load_frame) : Prop :=
    l = l'.

  Definition erasedCores c c' :=
    match c, c' with
    | State rs loader, State rs' loader' =>
      erased_regs rs rs' /\ erased_loader loader loader'
    | Asm_CallstateIn vf args tys retty, Asm_CallstateIn vf' args' tys' retty' =>
      vf = vf' /\ erased_val_list args args' /\
      tys = tys' /\ retty = retty'
    | Asm_CallstateOut ef vals rs loader, Asm_CallstateOut ef' vals' rs' loader' =>
      ef = ef' /\ erased_val_list vals vals'
      /\ erased_regs rs rs' /\ erased_loader loader loader'
    | _, _ => False
    end.
 
  Lemma erased_regs_refl:
    forall rs, erased_regs rs rs.
  Proof with eauto with erased.
    intros rs r;
    unfold erased_reg...
  Qed.

  Lemma erased_loader_refl:
    forall loader, erased_loader loader loader.
  Proof.
    unfold erased_loader; auto.
  Qed.
  
  Hint Immediate erased_regs_refl erased_loader_refl
       erased_val_list_refl : erased.

  Lemma erasedCores_refl:
    forall c, erasedCores c c.
  Proof with eauto with erased.
    destruct c; simpl;
    repeat split...
  Qed.

  Hint Immediate erasedCores_refl: erased.
  
  Lemma erased_regs_set:
    forall rs rs' v v' r
      (Hrs_ren: erased_regs rs rs')
      (Hval: erased_val v v'),
      erased_regs (rs # r <- v) (rs' # r <- v').
  Proof.
    intros.
    intros r'.
    unfold erased_reg.
    do 2 rewrite Pregmap.gsspec.
    destruct (Pregmap.elt_eq r' r); auto.
    eapply Hrs_ren.
  Qed.

  (*NOTE THIS IS DUPLICATED WITH X86_INJ*)
  Lemma set_regs_empty_1:
    forall regs rs,
      set_regs regs [::] rs = rs.
  Proof.
    intros;
    induction regs; by reflexivity.
  Qed.
  
  Hint Resolve erased_regs_set : erased.

  (** ** Result about at_external, after_external and initial_core *)
  Lemma at_external_erase:
    forall c c' (Herase: erasedCores c c'),
      match at_external Sem c, at_external Sem c' with
      | Some (ef, sig, vs), Some (ef', sig', vs') =>
        ef = ef' /\ sig = sig' /\ erased_val_list vs vs'
      | None, None => True
      | _, _ => False
      end.
  Proof.
    intros.
    unfold erasedCores in *.
    destruct c, c'; try (by exfalso);
    repeat match goal with
    | [H: _ /\ _ |- _] => destruct H
           end; subst;
    unfold at_external; simpl; auto.
    destruct (BuiltinEffects.observableEF_dec f0); auto.
    split; auto.
    split; auto.
    eapply erased_val_list_decode; eauto.
  Qed.

  Lemma after_external_erase :
    forall v v' c c' c2
      (HeraseCores: erasedCores c c')
      (HeraseVal: erased_val v v')
      (Hafter_external: after_external X86SEM.Sem (Some v) c = Some c2),
    exists (c2' : state),
      after_external X86SEM.Sem (Some v') c' = Some c2' /\
      erasedCores c2 c2'.
  Proof.
    intros.
    unfold after_external in *.
    simpl in *.
    unfold Asm_after_external in *.
    destruct c; try discriminate.
    inv Hafter_external.
    unfold erasedCores in HeraseCores.
    destruct c'; try by exfalso.
    destruct HeraseCores as (? & ? & ? &?); subst.
    unfold erased_loader in H2; subst.
    eexists; split; eauto.
    simpl.
    split; [|unfold erased_loader; auto].      
    destruct (loc_external_result (ef_sig f0)) as [|r' regs];
      simpl.
    eapply erased_regs_set; eauto.
    eapply H1.
    destruct (sig_res (ef_sig f0)) as [ty|];
      try destruct ty;
      simpl;
      try do 2 rewrite set_regs_empty_1;
      repeat apply erased_regs_set; eauto;
      try apply H1.
    destruct regs as [|r'' regs'']; simpl;
    eauto with erased.
    do 2 rewrite set_regs_empty_1;
      eauto with erased.
  Qed.

  Lemma erasure_initial_core:
    forall ge v arg v' arg' c
      (Hv: erased_val v v')
      (Harg: erased_val arg arg')
      (Hinit: initial_core Sem ge v [:: arg] = Some c),
      initial_core Sem ge v' [:: arg'] = Some c.
  Proof.
    intros.
    unfold initial_core in *; simpl in *.
    unfold  Asm_initial_core in *.
    destruct v; try discriminate.
    inversion Hv; subst.
    destruct (Int.eq_dec i Int.zero); try discriminate.
    destruct (Genv.find_funct_ptr ge b); try discriminate.
    destruct f; try discriminate.
    match goal with
    | [H: match ?Expr with _ => _ end = _ |- _] =>
      destruct Expr eqn:?
    end; try discriminate.
    apply andb_true_iff in Heqb0.
    destruct Heqb0.
    apply andb_true_iff in H.
    destruct H.
    unfold val_casted.vals_defined in *.
    destruct arg; (try discriminate);
    inv Harg; rewrite H0 H; simpl;
    auto.
  Qed.

End X86CoreErasure.

Module X86Erasure <: SCErasure X86SEM X86Machines X86Context X86CoreErasure.

  Module ThreadPoolErasure := ThreadPoolErasure X86SEM X86Machines X86CoreErasure.

  Import ThreadPoolErasure MemErasure ValErasure X86CoreErasure
         X86Machines DryMachine ThreadPool.
  
  

  Lemma evstep_erase:
    forall ge c1 c1' c2 ev m1 m1' m2
      (HeraseCores: erasedCores c1 c1')
      (HerasedMem: erasedMem m1 m1')
      (Hstep: ev_step SEM.Sem ge c1 m1 ev c2 m2),
    exists c2' m2',
      ev_step ErasedMachine.ThreadPool.SEM.Sem ge c1' m1' ev c2' m2' /\
      erasedCores c2 c2' /\ erasedMem m2 (erasePerm m2').
  Proof.
  Admitted.

  Ltac pf_cleanup :=
    repeat match goal with
           | [H1: invariant ?X, H2: invariant ?X |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
               subst H2
           | [H1: mem_compatible ?TP ?M, H2: mem_compatible ?TP ?M |- _] =>
             assert (H1 = H2) by (by eapply proof_irr);
             subst H2
           | [H1: is_true (leq ?X ?Y), H2: is_true (leq ?X ?Y) |- _] =>
             assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: containsThread ?TP ?M, H2: containsThread ?TP ?M |- _] =>
           assert (H1 = H2) by (by eapply proof_irr); subst H2
           | [H1: containsThread ?TP ?M,
                  H2: containsThread (@updThreadC _ ?TP _ _) ?M |- _] =>
             apply cntUpdateC' in H2;
             assert (H1 = H2) by (by eapply cnt_irr); subst H2
           | [H1: containsThread ?TP ?M,
                  H2: containsThread (@updThread _ ?TP _ _ _) ?M |- _] =>
             apply cntUpdate' in H2;
               assert (H1 = H2) by (by eapply cnt_irr); subst H2
         end.

  Lemma threadStep_erase:
    forall ge tp1 tp1' m1 m1' tp2 m2 i ev
      (HerasePool: erased_threadPool tp1 tp1')
      (cnti: containsThread tp1 i)
      (cnti': ErasedMachine.ThreadPool.containsThread tp1' i)
      (HerasedMem: erasedMem m1 m1')
      (Hcomp1: mem_compatible tp1 m1)
      (Hcomp1': ErasedMachine.mem_compatible tp1' m1')
      (Hstep: threadStep ge cnti Hcomp1 tp2 m2 ev),
    exists tp2' m2',
      ErasedMachine.threadStep ge cnti' Hcomp1' tp2' m2' ev /\
      erased_threadPool tp2 tp2' /\ erasedMem m2 (erasePerm m2').
  Proof.
    intros.
    inversion HerasePool as [Hnum Hthreads].
    specialize (Hthreads _ cnti cnti').
    inversion Hstep; subst.
    pf_cleanup;
      match goal with
        [H: erasedCtl ?Expr1 ?Expr2, H1: ?Expr1 = _ |- _] =>
        rewrite H1 in H; simpl in H;
        destruct Expr2 eqn:?
      end; try (by exfalso).
    eapply erasedMem_restr with (Hlt := Hcomp1 i cnti) in HerasedMem.
    eapply evstep_erase in Hcorestep; eauto.
    destruct Hcorestep as (c2' & m2' & Hevstep' & HerasedCores' & HerasedMem').
    exists (ErasedMachine.ThreadPool.updThreadC cnti' (Krun c2')), m2'.
    split; eauto.
    econstructor; eauto.
    split; eauto.
    constructor; eauto.
    intros j cntj cntj'.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
    + subst.
      rewrite gssThreadCode.
      rewrite ErasedMachine.ThreadPool.gssThreadCC.
      simpl; eauto.
    +
      assert (cntj0' := ErasedMachine.ThreadPool.cntUpdateC' _ _ cntj').
      assert (cntj0 := cntUpdate' _ _ _ cntj).
      erewrite  @gsoThreadCode with (cntj :=  cntj0) by eauto.
      erewrite <- @ErasedMachine.ThreadPool.gsoThreadCC with (cntj := cntj0')
        by eauto.
      inversion HerasePool; eauto.
  Qed.

  Notation fstep := (corestep fine_semantics).
  Notation scstep := (corestep x86_sc_semantics).
  
  Lemma sc_erasure:
    forall ge tp1 tp1' i U tr tr' m1 m1' tp2 m2
      (HerasePool: erased_threadPool tp1 tp1')
      (HerasedMem: erasedMem m1 m1')
      (Hfstep: fstep ge (i :: U, tr, tp1) m1 (U, tr', tp2) m2),
    exists tp2' m2',
      scstep ge (i :: U, tr, tp1') m1' (U, tr', tp2') m2' /\
      erased_threadPool tp2 tp2' /\ erasedMem m2 m2'.
  Proof.
    intros.
    inversion Hfstep; simpl in *; subst;
    inv HschedN;
    try match goal with
        | [H: containsThread _ ?I |- _ ] =>
          assert (ErasedMachine.ThreadPool.containsThread tp1' I)
            by (eapply erasedPool_contains; eauto)
        end;
    assert (Hcomp1' : ErasedMachine.mem_compatible tp1' m1')
      by (unfold ErasedMachine.mem_compatible; auto).
    - assert (Hstep' := startStep_erasure HerasePool H Htstep).
      destruct Hstep' as [tp2' [Hstart' HerasePool']].
      exists tp2', m1'.
      split. econstructor 1; simpl; eauto.
      split; eauto.
    - assert (Hstep' := resumeStep_erasure HerasePool H Htstep).
      destruct Hstep' as [tp2' [Hstart' HerasePool']].
      exists tp2', m1'.
      split. econstructor 2; simpl; eauto.
      split; eauto.
    - assert (Htstep' := threadStep_erase HerasePool H HerasedMem Hcomp1' Htstep).
      destruct Htstep' as [tp2' [m2' [Htstep' [HerasePool' HerasedMem']]]].
      exists tp2', (erasePerm m2').
      split.
      eapply X86SC.thread_step; eauto.
      split; eauto.
      eapply erasedMem_dilute_1; eauto.
    - assert (Hstep' := suspendStep_erasure HerasePool H Htstep).
      destruct Hstep' as [tp2' [Hstart' HerasePool']].
      exists tp2', m1'.
      split. econstructor 4; simpl; eauto.
      split; eauto.
    - assert (Hstep' := syncStep_erase HerasePool H HerasedMem Hcomp1' Htstep).
      destruct Hstep' as [tp2' [m2' [Hstep' [HerasePool' HerasedMem']]]].
      exists tp2', m2'.
      split.
      eapply X86SC.sync_step; eauto.
      split; eauto.
    - eapply haltStep_erasure with (cnti' := H) in Hhalted; eauto.
      exists tp1', m1';
        split; eauto.
      econstructor 6; simpl; eauto.
    - assert (~ ErasedMachine.ThreadPool.containsThread tp1' tid).
      { intros Hcontra.
        destruct HerasePool as [Hnum _].
        unfold containsThread, ErasedMachine.ThreadPool.containsThread in *.
        rewrite <- Hnum in Hcontra.
        auto.
      }
      exists tp1', m1'.
      split.
      econstructor 7; simpl; eauto.
      split; eauto.
  Qed.
        
End X86Erasure.

(** ** Safety for X86-SC semantics *)
Module X86Safe.
  Import Asm Asm_coop event_semantics FineConcSafe Events X86Erasure.

  Definition sc_init f arg := initial_core x86_sc_semantics the_ge f arg.
  
  Notation sc_safe := (X86SC.fsafe the_ge).
  Notation fsafe := (FineConc.fsafe the_ge).
    

  Inductive sc_execution :
      X86SC.MachState -> mem -> X86SC.MachState -> mem -> Prop :=
  | refl_sc_exec : forall ms (m : mem),
      X86SC.halted ms ->
      sc_execution ms m ms m
  | step_sc_trans : forall (i : tid) U U'
                   (tp tp' tp'': X86SC.machine_state)
                   (tr tr' tr'': X86SC.event_trace)
                   (m m' m'' : mem),
      X86SC.MachStep the_ge (i :: U, tr, tp) m (U, tr', tp') m' ->
      sc_execution (U, tr', tp') m' (U', tr'', tp'') m'' ->
      sc_execution (i :: U,tr,tp) m (U',tr'',tp'') m''.

  Inductive fine_execution :
    FineConc.MachState -> mem -> FineConc.MachState -> mem -> Prop :=
  | refl_fine_exec : forall ms (m : mem),
      FineConc.halted ms ->
      fine_execution ms m ms m
  | step_fine_trans : forall (i : tid) U U'
                   (tp tp' tp'': FineConc.machine_state)
                   (tr tr' tr'': FineConc.event_trace)
                   (m m' m'' : mem),
      FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr ++ tr', tp') m' ->
      fine_execution (U, tr ++ tr', tp') m' (U', tr ++ tr' ++ tr'', tp'') m'' ->
      fine_execution (i :: U,tr,tp) m (U',tr ++ tr' ++ tr'',tp'') m''.

    
  (** The initial state of X86SC is an erasure of the initial state of
  the FineConc machine *)
  Lemma init_erasure:
    forall f arg U tpsc tpf
      (HinitSC: sc_init f arg = Some (U, [::], tpsc))
      (HinitF: tpf_init f arg = Some (U, [::], tpf)),
      erased_threadPool tpf tpsc.
  Proof.
    intros.
    unfold sc_init, tpf_init in *.
    simpl in *. unfold X86SC.init_machine, FineConc.init_machine in *.
    unfold init_mach, ErasedMachine.init_mach in *.
    simpl in *.
    destruct (Asm_initial_core the_ge f arg); try discriminate.
    destruct init_perm; try discriminate.
    inv HinitSC. inv HinitF.
    unfold initial_machine, ErasedMachine.initial_machine.
    simpl.
    econstructor. simpl; eauto.
    intros. 
    simpl.
    apply erasedCores_refl; auto.
  Qed.

    (** Any execution of the FineConc machine resulting in some trace
    tr' can be matched by an execution of the X86-SC machine with the
    same trace*)
  Lemma execution_sim:
    forall U U' tpf tpf' mf mf' tpsc msc tr tr' 
      (Hexec: fine_execution (U, tr, tpf) mf (U', tr', tpf') mf')
      (HerasedPool: erased_threadPool tpf tpsc)
      (HerasedMem: erasedMem mf msc),
    exists tpsc' msc',
      sc_execution (U, tr, tpsc) msc (U', tr', tpsc') msc' /\
      erased_threadPool tpf' tpsc' /\ erasedMem mf' msc'.
  Proof.
    intros U.
    induction U.
    - intros.
      inversion Hexec; subst.
      exists tpsc, msc.
      split.
      econstructor 1. simpl; auto.
      split; auto.
    - intros.
      inversion Hexec; subst.
      + simpl in H5; by exfalso.
      + eapply sc_erasure in H8; eauto.
        destruct H8 as (tpsc0 & msc0 & Hstep0 & HerasedPool0 & HerasedMem0).
        specialize (IHU _ _ _ _ _ _ _ _ _ H9 HerasedPool0 HerasedMem0).
        destruct IHU as (tpsc2' & msc2' & Hsexec & HerasedPool' & HerasedMem').
        exists tpsc2', msc2'.
        split; eauto.
        econstructor; eauto.
  Qed.

  (** Safety of the X86SC machine*)
  Lemma x86sc_safe:
    forall sched tpsc tpf mf msc
      (Hsafe: fsafe tpf mf sched (size sched).+1)
      (HerasedPool: erased_threadPool tpf tpsc)
      (HerasedMem: erasedMem mf msc),
      sc_safe tpsc msc sched (size sched).+1.
  Proof.
    intro sched.
    induction sched as [|i sched]; intros.
    - simpl in *. inversion Hsafe;
        eapply X86SC.HaltedSafe with (tr := tr);
        simpl; auto.
    - simpl in Hsafe.
      inversion Hsafe; subst.
      simpl in H; by exfalso.
      simpl in *.
      eapply sc_erasure in H0; eauto.
      destruct H0 as (tpsc2' & msc2' & Hstep & HerasedPool' & HerasedMem').
      econstructor 3; eauto.
  Qed.

  (** Erasure from FineConc to X86-SC.*)
  Theorem x86sc_erasure:
    forall sched f arg U tpsc tpf m
      (Hmem: init_mem = Some m)
      (HinitSC: sc_init f arg = Some (U, [::], tpsc))
      (HinitF: tpf_init f arg = Some (U, [::], tpf))
      (HsafeF: fsafe tpf (diluteMem m) sched (size sched).+1),
      sc_safe tpsc (ErasedMachine.diluteMem m) sched (size sched).+1 /\
      (forall tpf' mf' tr,
          fine_execution (sched, [::], tpf) (diluteMem m) ([::], tr, tpf') mf' ->
          exists tpsc' msc',
            sc_execution (sched, [::], tpsc) (ErasedMachine.diluteMem m)
                         ([::], tr, tpsc') msc' /\
            erased_threadPool tpf' tpsc' /\ erasedMem mf' msc').
  Proof.
    intros.
    assert (HpoolErase := init_erasure _ _ HinitSC HinitF).
    assert (HmemErase : erasedMem (diluteMem m) (ErasedMachine.diluteMem m)).
    { econstructor; eauto.
      intros.
      assert (Hvalid: Mem.valid_block m b)
        by (unfold Mem.valid_block, ErasedMachine.diluteMem, erasePerm in *;
             simpl in *; auto).
      assert (Hperm:= erasePerm_V ofs k Hvalid).
      unfold permission_at in Hperm; auto.
    }
    split; first by (eapply x86sc_safe; eauto).
    intros.
    eapply execution_sim; eauto.
  Qed.
    
  (** Competing Events *)

  Definition sameLocation ev1 ev2 :=
    match location ev1, location ev2 with
    | Some (b1, ofs1, size1), Some (b2, ofs2, size2) =>
      b1 = b2 /\ exists ofs, Intv.In ofs (ofs1, (ofs1 + Z.of_nat size1)%Z) /\
                       Intv.In ofs (ofs2, (ofs2 + Z.of_nat size2)%Z)
    | _,_ => False
    end.
  
  Definition competes (ev1 ev2 : machine_event) : Prop :=
    thread_id ev1 <> thread_id ev2 /\
    sameLocation ev1 ev2 /\
    (is_internal ev1 ->
     is_internal ev2 ->
     action ev1 = Some Write \/ action ev2 = Some Write) /\
    (is_external ev1 \/ is_external ev2 ->
     action ev1 = Some Mklock \/ action ev1 = Some Freelock
     \/ action ev2 = Some Mklock \/ action ev2 = Some Freelock).

  (** Spinlock well synchronized*)
  Definition spinlock_synchronized (tr : X86SC.event_trace) :=
    forall i j ev1 ev2,
      i < j ->
      List.nth_error tr i = Some ev1 ->
      List.nth_error tr j = Some ev2 ->
      competes ev1 ev2 ->
      exists u v eu ev,
        i < u < v < j /\
        List.nth_error tr u = Some eu /\
        List.nth_error tr v = Some ev /\
        action eu = Some Release /\ action ev = Some Acquire /\
        location eu = location ev.

  (** Spinlock clean *)
  Definition spinlock_clean (tr : X86SC.event_trace) :=
    forall i j evi evj,
      i < j ->
      List.nth_error tr i = Some evi ->
      List.nth_error tr j = Some evj ->
      action evi = Some Mklock ->
      (~ exists u evu, i < u < j /\ List.nth_error tr u = Some evu /\
                  action evu = Some Freelock /\ location evu = location evi) ->
      sameLocation evj evi ->
      action evj <> Some Write /\ action evj <> Some Read.
  
End X86Safe.

  
  



