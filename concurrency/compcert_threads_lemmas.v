Require Import compcert.lib.Axioms.

Add LoadPath "../concurrency" as concurrency.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import concurrency.addressFiniteMap.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Notation EXIT := 
  (EF_external 1%positive (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG := (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint)).
Notation CREATE := (EF_external 2%positive CREATE_SIG).

Notation READ := 
  (EF_external 3%positive 
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).
Notation WRITE := 
  (EF_external 4%positive 
               (mksignature (AST.Tint::AST.Tint::AST.Tint::nil) (Some AST.Tint))).

Notation MKLOCK := 
  (EF_external 5%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).
Notation FREE_LOCK := 
  (EF_external 6%positive (mksignature (AST.Tint::nil) (Some AST.Tint))).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation LOCK := (EF_external 7%positive LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint)).
Notation UNLOCK := (EF_external 8%positive UNLOCK_SIG).

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.scheduler.
Require Import concurrency.concurrent_machine.
Require Import concurrency.dry_machine_lemmas concurrency.dry_context.
Require Import concurrency.mem_obs_eq.

(* TODO: - Injectivity - done

         - Well-defined memories

         - Remove admits - Almost done.

         - More comments explaining proofs, especially simulations.

         - More automation (hint databases, type classes for internal
           execution, etc.
         
         - The offset in renamings is annoying, consider if we want to keep it
 *)

Module InternalSteps.
  Import dry_context mySchedule DryMachine DryMachine.ThreadPool SEM.
  Import CoreLanguage.

  Section InternalSteps.
    
    Notation threadStep := (threadStep the_ge).
    Notation Sch := schedule.
    Context {cSpec : corestepSpec}.
    
    (** Internal steps are just thread coresteps or resume steps or
  start steps, they mimic fine-grained internal steps *)
    Definition internal_step {tid} {tp} m (cnt: containsThread tp tid)
               (Hcomp: mem_compatible tp m) tp' m' :=
      threadStep cnt Hcomp tp' m' \/
      (myCoarseSemantics.resume_thread cnt tp' /\ m = m') \/
      (myCoarseSemantics.start_thread the_ge cnt tp' /\ m = m').

    Inductive internal_execution : Sch -> thread_pool -> mem ->
                                   thread_pool -> mem -> Prop :=
    | refl_exec : forall tp m,
        internal_execution empty tp m tp m
    | step_trans : forall tid U U' tp m tp' m' tp'' m''
                     (cnt: containsThread tp tid)
                     (HschedN: schedPeek U = Some tid)
                     (HschedS: schedSkip U = U')
                     (Hcomp: mem_compatible tp m)
                     (Hstep: internal_step cnt Hcomp tp' m')
                     (Htrans: internal_execution U' tp' m' tp'' m''),
        internal_execution U tp m tp'' m''.

    (** Lemmas about internal steps and internal executions *)
    Lemma internal_execution_trans :
      forall i U tp tp' tp'' m m' m'' (pf': containsThread tp' i)
        (Hcomp: mem_compatible tp' m')
        (Hstep: internal_step pf' Hcomp tp'' m'')
        (Hexec: internal_execution U tp m tp' m'),
        internal_execution (U ++ [:: i]) tp m tp'' m''.
    Proof.
      intros i U. induction U; intros.
      simpl in *.
      inversion Hexec; subst.
      econstructor; simpl; eauto. constructor.
      simpl in HschedN. discriminate.
      inversion Hexec. subst. simpl in *.
      econstructor; simpl; eauto.
    Qed.

    Lemma internal_step_det :
      forall tp tp' tp'' m m' m'' i
        (Hcnt: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step Hcnt Hcomp tp' m')
        (Hstep': internal_step Hcnt Hcomp tp'' m''),
        tp' = tp'' /\ m' = m''.
    Proof.
      intros.
      destruct Hstep as [Htstep | [[Htstep ?] | [Htstep ?]]],
                        Hstep' as [Htstep' | [[Htstep' ?] | [Htstep' ?]]]; subst;
      inversion Htstep; inversion Htstep'; subst; pf_cleanup;
      rewrite Hcode in Hcode0; inversion Hcode0; subst.
      assert (Heq: c' = c'0 /\ m' = m'')
        by (eapply corestep_det; eauto).
      destruct Heq; subst;
        by auto.
      rewrite Hafter_external in Hafter_external0;
        by inversion Hafter_external0.
      rewrite Hinitial in Hinitial0;
        by inversion Hinitial0.
    Qed.

    Ltac exec_induction base_case :=
      intros;
      match goal with
      | [xs : list _, i : nat, Hexec: internal_execution _ ?Tp ?M _ _ |- _] =>
        generalize dependent Tp; generalize dependent M;
        induction xs as [| x xs' IHxs]; intros;
        [ match goal with
          | [Hexec: internal_execution _ _ _ _ _ |- _] =>
            try (inversion Hexec; subst;
                   by pf_cleanup)
          end
        | match goal with
          | [Hexec: internal_execution _ _ _ _ _ |- _] =>
            simpl in Hexec;
              destruct (x == i) eqn:Heq;
              move/eqP:Heq=>Heq;
              try eauto;
              subst;
              try (inversion Hexec as [|? ? ? ? ? ? ? ? ? ? HschedN HschedS Hcomp ? Htrans]; subst;
                   simpl in Htrans;
                   simpl in HschedN; inversion HschedN; subst;
                   pf_cleanup;
                   specialize (IHxs _ _  Htrans);
                   rewrite <- IHxs;
                   erewrite base_case; eauto)
          end
        ]
      end. 

    Lemma containsThread_internal_step :
      forall tp m tp' m' tid0 tid
        (Hcnt0: containsThread tp tid0)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step Hcnt0 Hcomp tp' m') 
        (Hcnt: containsThread tp tid),
        containsThread tp' tid.
    Proof.
      intros. inversion Hstep as [Htstep | [[Htstep _] | [Htstep _]]];
        inversion Htstep; subst;
        [ eapply corestep_containsThread; by eauto
        | by eapply cntUpdateC | by eapply cntUpdateC].
    Qed.
    
    Lemma containsThread_internal_execution :
      forall U tp m tp' m' i
        (Hexec: internal_execution U tp m tp' m'),
        containsThread tp i -> containsThread tp' i.
    Proof.
      intros U. induction U. intros.
      inversion Hexec; subst; simpl in *; auto; try discriminate.
      intros.
      inversion Hexec as [|tid0 U0 U0' ? ? tp0' m0' ? ?];
        subst. eapply containsThread_internal_step in Hstep; eauto.
    Qed.

    Lemma containsThread_internal_step' :
      forall tp m tp' m' i j
        (Hcnt0: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step Hcnt0 Hcomp tp' m') 
        (Hcnt: containsThread tp' i),
        containsThread tp i.
    Proof.
      intros. inversion Hstep as [Htstep | [[Htstep _] | [Htstep _]]];
        inversion Htstep; subst;
        [eapply corestep_containsThread'; eauto
        |  by eapply cntUpdateC'; eauto
        |  by eapply cntUpdateC'; eauto].
      
    Qed.

    Lemma containsThread_internal_execution' :
      forall U tp m tp' m' i
        (Hexec: internal_execution U tp m tp' m')
        (Hcnt: containsThread tp' i),
        containsThread tp i.
    Proof.
      intros U. induction U. intros.
      inversion Hexec; subst; simpl in *; auto; try discriminate.
      intros.
      inversion Hexec as [|tid0 U0 U0' ? ? tp0' m0' ? ?];
        subst. eapply containsThread_internal_step' in Hstep; eauto.
    Qed.

    Lemma dry_step_compatible :
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hdry: dry_step the_ge pf Hcompatible tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros.
      inversion Hdry; subst; eapply corestep_compatible;
        by eauto.
    Qed.

    Corollary coarseResume_compatible :
      forall (tp tp' : thread_pool) m (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hresume: myCoarseSemantics.resume_thread pf tp'),
        mem_compatible tp' m.
    Proof.
      intros.
      inversion Hresume; subst;
      eapply StepLemmas.updThreadC_compatible;
        by eauto.
    Qed.

    Corollary coarseStart_compatible :
      forall (tp tp' : thread_pool) m (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstart: myCoarseSemantics.start_thread the_ge pf tp'),
        mem_compatible tp' m.
    Proof.
      intros.
      inversion Hstart; subst;
      eapply StepLemmas.updThreadC_compatible;
        by eauto.
    Qed.
    
    Corollary internal_step_compatible :
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_step pf Hcompatible tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros.
      destruct Hstep as [Hdry | [[Hresume ?] | [Hstart ?]]];
        subst;
        [eapply dry_step_compatible
        | eapply coarseResume_compatible
        | eapply coarseStart_compatible]; 
          by eauto.
    Qed.
    
    Lemma internal_step_invariant:
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_step pf Hcompatible tp' m'),
        invariant tp'.
    Proof.
      intros.
      destruct Hstep as [Hdry | Hsr].
      - inversion Hdry as [tp'0 c m1 m1' c']. subst m' tp'0 tp'.
        eapply corestep_invariant; eauto.
      - destruct Hsr as [H1 | H1];
        destruct H1 as [H2 ?]; subst;
        inversion H2; subst;
          by apply StepLemmas.updThreadC_invariant.
    Qed.

    Lemma internal_execution_compatible :
      forall (tp tp' : thread_pool) m m' xs
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_execution xs tp m tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros. induction Hstep. auto. subst.
      eapply IHHstep; eauto.
      eapply internal_step_compatible; eauto.
    Qed.

    Lemma internal_execution_invariant :
      forall (tp tp' : thread_pool) m m' xs
        (Hcompatible: mem_compatible tp m)
        (Hinv: invariant tp)
        (Hstep: internal_execution xs tp m tp' m'),
        invariant tp'.
    Proof.
      intros. induction Hstep. auto. subst.
      eapply IHHstep; eauto.
      eapply internal_step_compatible; eauto.
      eapply internal_step_invariant; eauto.
    Qed.
    
    Lemma gsoThreadC_step:
      forall tp tp' m m' i j (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m')
        (Hneq: i <> j),
        getThreadC pfj = getThreadC pfj'.
    Proof.
      intros. destruct Hstep as [Hstep | [[Hstep Heq] | [Hstep Heq]]];
        inversion Hstep; subst;
        [erewrite <- gsoThreadCode with (cntj' := pfj')
          by eauto
        |
        erewrite gsoThreadCC with (cntj' := pfj')
          by eauto
        |
        erewrite gsoThreadCC with (cntj' := pfj')
          by eauto];
        reflexivity.
    Qed.

    Lemma gsoThreadC_exec:
      forall tp m tp' m' i j xs
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m')
        (Hneq: i <> j),
        getThreadC pfj = getThreadC pfj'.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hstep. inversion Hstep; subst. by pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst a. inversion Hstep; subst.
          simpl in Htrans.
          assert (pfj'0: containsThread tp'0 j)
            by (eapply containsThread_internal_step; eauto).
          specialize (IHxs _ _  pfj'0 Htrans).
          rewrite <- IHxs.
          erewrite gsoThreadC_step; eauto.
          simpl in HschedN. inversion HschedN; subst.
          assumption.
        + eauto.
    Qed.

    Lemma gsoThreadR_step:
      forall tp tp' m m' i j (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m')
        (Hneq: i <> j),
        getThreadR pfj = getThreadR pfj'.
    Proof.
      intros. destruct Hstep as [Hstep | [[Hstep Heq] | [Hstep Heq]]];
        inversion Hstep; subst;
        [erewrite <- @gsoThreadRes with (cntj' := pfj') |
         erewrite <- @gThreadCR with (cntj' := pfj')
         | erewrite <- @gThreadCR with (cntj' := pfj')];
          by eauto.
    Qed.
    
    Corollary permission_at_step:
      forall tp tp' m m' i j
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs,
        permission_at (restrPermMap (Hcomp _ pfj)) b ofs Cur =
        permission_at (restrPermMap (Hcomp' _ pfj')) b ofs Cur.
    Proof.
      intros.
      do 2 rewrite restrPermMap_Cur.
      erewrite @gsoThreadR_step;
        by eauto.
    Qed.

    Lemma gsoThreadR_execution:
      forall tp m tp' m' i j xs
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hneq: i <> j)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m'),
        getThreadR pfj = getThreadR pfj'.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hstep. inversion Hstep; subst. by pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst a. inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN; inversion HschedN; subst tid.
          pf_cleanup.
          assert (pfj'0: containsThread tp'0 j)
            by (eapply containsThread_internal_step; eauto).
          specialize (IHxs _ _  pfj'0 Htrans).
          rewrite <- IHxs.
          erewrite gsoThreadR_step; eauto.
        + eauto.
    Qed.

    Lemma gsoLockSet_step:
      forall tp tp' m m' i (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m'),
        lockSet tp = lockSet tp'.
    Proof.
      intros;
      destruct Hstep as [Htstep | [[Htstep ?] | [Htstep ?]]];
      inversion Htstep;
      subst;
      [erewrite gsoThreadLock |
       erewrite gsoThreadCLock |
       erewrite gsoThreadCLock];
        by reflexivity.
    Qed.

    Lemma gsoLockSet_execution:
      forall tp m tp' m' i xs
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m'),
        lockSet tp = lockSet tp'.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hstep. inversion Hstep; subst. by pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq; try eauto.
        subst a. inversion Hstep; subst.
        simpl in Htrans.
        simpl in HschedN; inversion HschedN; subst tid.
        pf_cleanup.
        specialize (IHxs _ _  Htrans).
        rewrite <- IHxs.
        erewrite gsoLockSet_step; eauto.
    Qed.
      
    Lemma gsoLockPool_step:
      forall tp tp' m m' i (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step pfi Hcomp tp' m') addr,
        lockRes tp addr = lockRes tp' addr.
    Proof.
      intros;
      destruct Hstep as [Htstep | [[Htstep ?] | [Htstep ?]]];
      inversion Htstep;
      subst;
      [erewrite gsoThreadLPool |
       erewrite gsoThreadCLPool |
       erewrite gsoThreadCLPool];
        by reflexivity.
    Qed.

    Lemma gsoLockPool_execution :
      forall (tp : thread_pool) (m : mem) (tp' : thread_pool) 
        (m' : mem) (i : nat) (xs : seq nat_eqType)
        (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m')
        addr,
        lockRes tp addr = lockRes tp' addr.
    Proof.
      intros. generalize dependent tp. generalize dependent m.
      induction xs; intros.
      - simpl in Hexec. inversion Hexec; subst. by pf_cleanup.
        simpl in HschedN. by discriminate.
      - simpl in Hexec.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq; try eauto.
        subst a. inversion Hexec; subst.
        simpl in Htrans.
        simpl in HschedN; inversion HschedN; subst tid.
        pf_cleanup.
        specialize (IHxs _ _  Htrans).
        rewrite <- IHxs.
        erewrite gsoLockPool_step; eauto.
    Qed.

      
    Lemma permission_at_execution:
      forall tp m tp' m' i j xs
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (Hneq: i <> j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m'),
      forall b ofs,
        permission_at (restrPermMap (Hcomp _ pfj)) b ofs Cur =
        permission_at (restrPermMap (Hcomp' _ pfj')) b ofs Cur.
    Proof.
      intros.
      do 2 rewrite restrPermMap_Cur.
      erewrite gsoThreadR_execution; eauto.
    Qed.
    
    Lemma internal_step_disjoint_val :
      forall tp tp' m m' i j
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs
        (Hreadable: 
           Mem.perm (restrPermMap (Hcomp _ pfj)) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      inversion Hstep as [Htstep | [[Htstep Heq] | [Htstep Heq]]]; subst; auto.
      inversion Htstep; subst; eapply corestep_disjoint_val;
        by eauto.
    Qed.
    
    Lemma internal_exec_disjoint_val :
      forall tp tp' m m' i j xs
        (Hneq: i <> j)
        (pfi: containsThread tp i)
        (pfj: containsThread tp j)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m') b ofs
        (Hreadable: 
           Mem.perm (restrPermMap (Hcomp _ pfj)) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      generalize dependent tp.  generalize dependent m.
      induction xs as [|x xs]; intros.
      - simpl in Hstep; inversion Hstep; subst.
        reflexivity.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (x == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst x.
          inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN.
          inversion HschedN; subst tid.
          pf_cleanup.
          assert (pfj0': containsThread tp'0 j) by
              (eapply containsThread_internal_step; eauto).
          assert (pfi0': containsThread tp'0 i) by
              (eapply containsThread_internal_step; eauto).
          assert(Hcomp0': mem_compatible tp'0 m'0) by
              (eapply internal_step_compatible; eauto).
          assert (Hreadable0':
                    Mem.perm (restrPermMap (Hcomp0' j pfj0')) b ofs Cur Readable).
          { clear IHxs Htrans HschedN Hstep.
            assert (Hperm_eq :=
                      permission_at_step Hneq  pfj pfj0' Hcomp0' Hstep0 b ofs).
            do 2 rewrite restrPermMap_Cur in Hperm_eq.
            unfold Mem.perm in *.
            assert (H1:= restrPermMap_Cur (Hcomp0' j pfj0') b ofs).
            unfold permission_at in H1.
            rewrite H1. rewrite <- Hperm_eq.
            assert (H2:= restrPermMap_Cur (Hcomp j pfj) b ofs).
            unfold permission_at in H2.
            rewrite H2 in Hreadable. assumption.
          }
          specialize (IHxs _ _  pfi0' pfj0' Hcomp0' Htrans Hreadable0').
          rewrite <- IHxs.
          eapply internal_step_disjoint_val; eauto.
        + by eauto.
    Qed.

    Lemma internal_step_disjoint_val_lock :
      forall tp tp' m m' i
        (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step pfi Hcomp tp' m') b ofs
        (Hreadable: 
           Mem.perm (restrPermMap (compat_ls Hcomp)) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      inversion Hstep as [Hcstep | [[Hrstep Heq] | [Hsstep Heq]]]; subst; auto.
      inversion Hcstep; subst; eapply corestep_disjoint_val_lockset;
        by eauto.
    Qed.
    
    Lemma internal_exec_disjoint_val_lock :
      forall tp tp' m m' i xs
        (pfi: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_execution [seq x <- xs | x == i] tp m tp' m') b ofs
        (Hreadable: 
           Mem.perm (restrPermMap (compat_ls Hcomp)) b ofs Cur Readable),
        Maps.ZMap.get ofs (Mem.mem_contents m) # b =
        Maps.ZMap.get ofs (Mem.mem_contents m') # b.
    Proof.
      intros.
      generalize dependent tp.  generalize dependent m.
      induction xs as [|x xs]; intros.
      - simpl in Hstep; inversion Hstep; subst.
        reflexivity.
        simpl in HschedN. by discriminate.
      - simpl in Hstep.
        destruct (x == i) eqn:Heq; move/eqP:Heq=>Heq.
        + subst x.
          inversion Hstep; subst.
          simpl in Htrans.
          simpl in HschedN.
          inversion HschedN; subst tid.
          pf_cleanup.
          assert (pfi0': containsThread tp'0 i) by
              (eapply containsThread_internal_step; eauto).
          assert(Hcomp0': mem_compatible tp'0 m'0) by
              (eapply internal_step_compatible; eauto).
          assert (Hreadable0':
                    Mem.perm (restrPermMap (compat_ls Hcomp0')) b ofs Cur Readable).
          { clear IHxs Htrans HschedN Hstep.
            assert (Hperm_eq :=
                      gsoLockSet_step Hstep0).
            unfold Mem.perm in *.
            assert (H1:= restrPermMap_Cur (compat_ls Hcomp0') b ofs).
            unfold permission_at in H1.
            rewrite H1.
            rewrite <- Hperm_eq.
            assert (H2:= restrPermMap_Cur (compat_ls Hcomp) b ofs).
            unfold permission_at in H2.
              by rewrite H2 in Hreadable.
          }
          specialize (IHxs _ _  pfi0' Hcomp0' Htrans Hreadable0').
          rewrite <- IHxs.
          eapply internal_step_disjoint_val_lock; eauto.
        + by eauto.
    Qed.
    
    Lemma internal_step_decay:
      forall tp m tp' m' i (cnt: containsThread tp i)
        (cnt': containsThread tp' i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hstep: internal_step cnt Hcomp tp' m'),
        decay (restrPermMap (Hcomp _ cnt))
              (restrPermMap (Hcomp' _ cnt')).
    Proof.
      intros. unfold decay. intros b ofs.
      assert (Hperm: permission_at
                       (restrPermMap (Hcomp' _ cnt')) b ofs Cur =
                     (getThreadR cnt') # b ofs)
        by (eapply restrPermMap_Cur; eauto).
      unfold permission_at in Hperm.
      destruct Hstep as [Hcstep | [[Hresume ?] | [Hstart ?]]]; subst.
      - inversion Hcstep. subst.
        eapply corestep_decay in Hcorestep.
        unfold decay in *. intros.
        specialize (Hcorestep b ofs).
        assert (Hpmap: getThreadR cnt' = getCurPerm m')
          by (by rewrite gssThreadRes).
        unfold Mem.perm in *. 
        repeat rewrite Hperm.
        repeat rewrite Hpmap.
        rewrite getCurPerm_correct.
        unfold permission_at.
          by assumption. 
      - inversion Hresume; subst.
        assert (Hpmap: getThreadR cnt' = getThreadR cnt)
          by (apply gThreadCR).
        assert (Hperm0: permission_at
                          (restrPermMap (Hcomp _ cnt)) b ofs Cur =
                        (getThreadR cnt) # b ofs)
          by (eapply restrPermMap_Cur; eauto).
        unfold Mem.perm, permission_at in *.
        rewrite Hperm Hperm0. rewrite Hpmap. auto.
        split; auto.
        intros Hinvalid p Hlt.
        apply Mem.nextblock_noaccess with (ofs := ofs)
                                            (k := Cur) in Hinvalid.
        rewrite Hinvalid in Hperm0. rewrite <- Hperm0 in Hlt.
        simpl in Hlt. by exfalso.
      - inversion Hstart; subst.
        assert (Hpmap: getThreadR cnt' = getThreadR cnt)
          by (apply gThreadCR).
        assert (Hperm0: permission_at
                          (restrPermMap (Hcomp _ cnt)) b ofs Cur =
                        (getThreadR cnt) # b ofs)
          by (eapply restrPermMap_Cur; eauto).
        unfold Mem.perm, permission_at in *.
        rewrite Hperm Hperm0. rewrite Hpmap. auto.
        split; auto.
        intros Hinvalid p Hlt.
        apply Mem.nextblock_noaccess with (ofs := ofs)
                                            (k := Cur) in Hinvalid.
        rewrite Hinvalid in Hperm0. rewrite <- Hperm0 in Hlt.
        simpl in Hlt. by exfalso.
    Qed.

    Lemma decay_trans :
      forall m m' m'',
        decay m m' ->
        decay m' m'' ->
        decay m m''.
    Admitted. (* Lennart has proved that*)

    (* This lemma is probably not useful anymore...*)
    Lemma internal_execution_decay:
      forall tp m tp' m' xs i (cnt: containsThread tp i)
        (cnt': containsThread tp' i)
        (Hcomp: mem_compatible tp m)
        (Hcomp': mem_compatible tp' m')
        (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m'),
        decay (restrPermMap (Hcomp _ cnt))
              (restrPermMap (Hcomp' _ cnt')).
    Proof.
      intros tp m tp' m' xs.
      generalize dependent tp. generalize dependent m.
      induction xs.
      - intros. simpl in Hexec. inversion Hexec; subst.
        pf_cleanup. admit. (*decay is refl *)
        simpl in HschedN. discriminate.
      - intros.
        destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq; subst.
        + simpl in Hexec.
          erewrite if_true in Hexec by (apply eq_refl).
          inversion Hexec; subst; simpl in *.
          inversion HschedN; subst tid.
          assert (Hcomp'0: mem_compatible tp'0 m'0)
            by (eapply internal_step_compatible; eauto).
          assert (cnt0': containsThread tp'0 i)
            by (eapply containsThread_internal_step; eauto).
          pf_cleanup.
          eapply IHxs with
          (Hcomp := Hcomp'0) (Hcomp' := Hcomp')
                             (cnt := cnt0') (cnt' := cnt') in Htrans.
          assert (Hdecay:
                    decay (restrPermMap (Hcomp _ cnt))
                          (restrPermMap (Hcomp'0 _ cnt0')))
            by (eapply internal_step_decay; eauto).
          eapply decay_trans; eauto.
        + simpl in Hexec.
          erewrite if_false in Hexec
            by (apply/eqP; assumption).
          auto.
    Admitted.

    Lemma internal_step_valid:
      forall tp m tp' m' i (cnt: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step cnt Hcomp tp' m') b
        (Hvalid: Mem.valid_block m b),
        Mem.valid_block m' b.
    Proof.
      intros.
      destruct Hstep as [Htstep | [[_ ?] | [_ ?]]];
        [inversion Htstep; subst;
         eapply corestep_nextblock;
           by eauto | by subst | by subst].
    Qed.

    Lemma internal_execution_valid :
      forall tp m tp' m' xs
        (Hexec: internal_execution xs tp m tp' m') b
        (Hvalid: Mem.valid_block m b),
        Mem.valid_block m' b.
    Proof.
      intros.
      generalize dependent tp. generalize dependent m.
      induction xs as [|x xs]; intros.
      inversion Hexec; subst; first by assumption.
      simpl in HschedN;
        by discriminate.
      inversion Hexec; subst.
      simpl in HschedN. inversion HschedN; subst.
      simpl in Htrans.
      assert (Hvalid0: Mem.valid_block m'0 b)
        by (eapply internal_step_valid; eauto).
        by eauto.
    Qed.
    
    
  End InternalSteps.
End InternalSteps.

Module SimDefs.

  Import mySchedule CoreLanguage InternalSteps.
  Require Import sepcomp.closed_safety.
  Import dry_context mySchedule DryMachine DryMachine.ThreadPool SEM.
  Import MemObsEq ValObsEq MemoryLemmas CoreInjections MemoryWD.
  
  Notation threadStep := (threadStep the_ge).
  Notation Sch := schedule.
  Notation cmachine_step := ((corestep coarse_semantics) the_ge).
  Notation fmachine_step := ((corestep fine_semantics) the_ge).
  Notation CoarseSem := coarse_semantics.
  Hint Unfold myCoarseSemantics.MachStep myFineSemantics.MachStep.

  (** Injections on programs *)
  Context {ci : CodeInj}.
  (*not clear what should happen with vf. Normally it should be in the
genv and hence should be mapped to itself, but let's not expose this
here*)
  Definition ctl_inj f cc cf : Prop :=
    match cc, cf with
    | Kinit vf arg, Kinit vf' arg' =>
      vf = vf' /\ val_obs f arg arg'
    | Krun c, Krun c' => core_inj f c c'
    | Kblocked c, Kblocked c' => core_inj f c c'
    | Kresume c arg, Kresume c' arg' => core_inj f c c' /\ val_obs f arg arg'
    | _, _  => False
    end.

  (*Again we do not require that the first argument to Kinit is valid
  as we never map it, although maybe we should*)
  Definition ctl_wd f t : Prop :=
    match t with
    | Krun c => core_wd f c
    | Kblocked c => core_wd f c
    | Kresume c v => core_wd f c /\ valid_val f v
    | Kinit _ v => valid_val f v
    end.

  Lemma ctl_wd_incr : forall f f' c,
      ctl_wd f c ->
      ren_domain_incr f f' ->
      ctl_wd f' c.
  Proof.
    intros f f' c Hwd Hincr.
    destruct c; simpl in *;
    repeat match goal with
        | [H: _ /\ _ |- _] =>
          destruct H
        | [ |- _] => split
        end;     
    try (eapply core_wd_incr; eauto);
    try (eapply valid_val_incr; eauto).
  Qed.
  
  Lemma ctl_inj_trans:
    forall c c' c'' (f f' f'' : memren)
      (Hcore_inj: ctl_inj f c c'')
      (Hcore_inj': ctl_inj f' c c')
      (Hf: forall b b' b'',
          f b = Some b'' ->
          f' b = Some b' ->
          f'' b' = Some b''),
      ctl_inj f'' c' c''.
  Proof.
    intros.
    destruct c, c', c''; simpl in *; try (by exfalso);
    try (destruct Hcore_inj, Hcore_inj'; split);
    try (eapply core_inj_trans; eauto).
    eapply val_obs_trans;
      by eauto.
      by subst.
      eapply val_obs_trans;
        by eauto.
  Qed.

  Definition tp_wd (f: memren) (tp : thread_pool) : Prop :=
    forall i (cnti: containsThread tp i),
      ctl_wd f (getThreadC cnti).

  Lemma tp_wd_incr : forall f f' tp,
      tp_wd f tp ->
      ren_domain_incr f f' ->
      tp_wd f' tp.
  Proof.
    intros.
    intros i cnti.
    specialize (H i cnti).
    eapply ctl_wd_incr;
      by eauto.
  Qed.

  Lemma ctl_wd_domain:
    forall f f' m (c : ctl),
      ctl_wd f c ->
      domain_memren f m ->
      domain_memren f' m ->
      ctl_wd f' c.
  Proof.
    intros f f' m c Hwd Hf Hf'.
    destruct c; simpl in *;
    repeat match goal with
           | [H: _ /\ _ |- _] => destruct H
           | [|- _ /\ _] => split
           | [|- core_wd _ _] => eapply core_wd_domain; eauto
           | [|- valid_val _ _] => eapply valid_val_domain; eauto
           end.
  Qed.

  Lemma tp_wd_domain:
    forall f f' m (tp : thread_pool),
      tp_wd f tp ->
      domain_memren f m ->
      domain_memren f' m ->
      tp_wd f' tp.
  Proof.
    intros.
    intros i cnti.
    specialize (H i cnti).
    destruct (getThreadC cnti); simpl in *;
    repeat match goal with
           | [H: _ /\ _ |- _] => destruct H
           | [|- _ /\ _] => split
           | [|- core_wd _ _] => eapply core_wd_domain; eauto
           | [|- valid_val _ _] => eapply valid_val_domain; eauto
           end.
  Qed.

  (** Simulations between individual threads. *)
  
  (* Consider hiding thread_pool completely *)
  (* The weak simulation is required to prove the correctness of
  concurrent calls. In particular, suppose that a thread executes an
  external call, this thread will be "synchronized" meaning that its
  permissions will be equal between the two machines. When the angel
  provides a new permission map for this thread we still need to show
  that it is compatible with the other threads, hence we need to know
  something about those threads as well. The fact that the permissions
  of the coarse grained machine are above the ones on the fine is
  enough to establish non-interference for the fine grained machine *)
  Definition weak_tsim {tpc tpf : thread_pool} (mc mf : Mem.mem)
             {i} (f: memren) (pfc : containsThread tpc i)
             (pff : containsThread tpf i) (compc: mem_compatible tpc mc)
             (compf: mem_compatible tpf mf) : Prop :=
    weak_mem_obs_eq f (restrPermMap  (compc i pfc))
                    (restrPermMap (compf i pff)).
  
  Record strong_tsim {tpc tpf : thread_pool} (mc mf : Mem.mem) {i}
         (f: memren) (pfc : containsThread tpc i)
         (pff : containsThread tpf i) (compc: mem_compatible tpc mc)
         (compf: mem_compatible tpf mf) : Prop :=
    { code_eq: ctl_inj f (getThreadC pfc) (getThreadC pff);
      obs_eq: mem_obs_eq f (restrPermMap (compc i pfc))
                         (restrPermMap (compf i pff))
    }.
  
  (** Simulation relation between a "coarse-grain" 
     state and a "fine-grain" state *)

  (* simStrong now maintains the extra invariant that any new blocks
      from the internal execution are owned by thread tid. This is
     needed for the suspend_sim proof. Note that it's not possible
     to prove it just by the fact that only thread tid executes because
     1. some location may be allocated and then freed in this multistep
      execution and 2. our relation only strongly relates the final state
      of the execution not in-between states. *)

  Definition fpool tpc : Type :=
    forall i (cnti: containsThread tpc i), memren.

  Definition max_inv mf := forall b ofs, Mem.valid_block mf b ->
                                    permission_at mf b ofs Max = Some Freeable.
  
  Record sim tpc mc tpf mf (xs : Sch) (f : memren) (fp: fpool tpc) : Prop :=
    { numThreads : forall i, containsThread tpc i <-> containsThread tpf i;
      mem_compc: mem_compatible tpc mc;
      mem_compf: mem_compatible tpf mf;
      safeCoarse: forall sched n, safeN coarse_semantics the_ge n (sched, tpc) mc;
      simWeak:
        forall tid
          (pfc: containsThread tpc tid)
          (pff: containsThread tpf tid),
          weak_tsim f pfc pff mem_compc mem_compf;
      fpSeperate: forall i j
                    (cnti: containsThread tpc i)
                    (cntj: containsThread tpc j)
                    (Hij: i <> j) b b' b2 b2'
                    (Hfb: f b = None)
                    (Hfb': f b' = None)
                    (Hfib: (fp _ cnti) b = Some b2)
                    (Hfjb': (fp _ cntj) b' = Some b2'),
          b2 <> b2';
      simStrong:
        forall tid (pfc: containsThread tpc tid) (pff: containsThread tpf tid),
        exists tpc' mc', ren_incr f (fp _ pfc) /\
                    ([seq x <- xs | x == tid] = nil -> f = (fp _ pfc)) /\
                    internal_execution ([seq x <- xs | x == tid])
                                       tpc mc tpc' mc' /\
                    (forall (pfc': containsThread tpc' tid)
                       (mem_compc': mem_compatible tpc' mc'),
                        strong_tsim (fp _ pfc) pfc' pff mem_compc' mem_compf) /\
                    (forall tid2 (pff2: containsThread tpf tid2)
                       (Hneq: tid <> tid2) b1 b2 ofs,
                        (fp _ pfc) b1 = Some b2 ->
                        f b1 = None ->
                        (getThreadR pff2) # b2 ofs = None) /\
                    (forall b1 b2 ofs,
                        (fp _ pfc) b1 = Some b2 ->
                        f b1 = None ->
                        (lockSet tpf) # b2 ofs = None) /\
                    (forall bl ofsl rmap b1 b2 ofs,
                        (fp _ pfc) b1 = Some b2 ->
                        f b1 = None ->
                        lockRes tpf (bl,ofsl) = Some rmap -> 
                        rmap # b2 ofs = None);
      simLocks: strong_mem_obs_eq f (restrPermMap (compat_ls mem_compc))
                                  (restrPermMap (compat_ls mem_compf));
      simLockRes: forall bl1 bl2 ofs rmap1 rmap2
                    (Hf: f bl1 = Some bl2)
                    (Hl1: lockRes tpc (bl1,ofs) = Some rmap1)
                    (Hl2: lockRes tpf (bl2,ofs) = Some rmap2),
          strong_mem_obs_eq f (restrPermMap ((compat_lp mem_compc) _ _ Hl1))
                            (restrPermMap ((compat_lp mem_compf) _ _ Hl2));
          
      invF: invariant tpf;
      maxF: max_inv mf;
      memc_wd: valid_mem mc;
      tpc_wd: tp_wd f tpc;
      thege_wd: ge_wd f the_ge;
    }.

  Arguments sim : clear implicits.

  (** Distinguishing the various step types of the concurrent machine *)

  Inductive StepType : Type :=
    Internal | Concurrent | Halted | Suspend.

  Definition ctlType (code : ctl) : StepType :=
    match code with
    | Kinit _ _ => Internal
    | Krun c =>
      match at_external Sem c with
      | None => 
        match halted Sem c with
        | Some _ => Halted
        | None => Internal
        end
      | Some _ => Suspend
      end
    | Kblocked c => Concurrent
    | Kresume c _ => Internal
    end.
  
  Definition getStepType {i tp} (cnt : containsThread tp i) : StepType :=
    ctlType (getThreadC cnt).

  Lemma ctlType_inj :
    forall c c' (f: memren)
      (Hinj: ctl_inj f c c'),
      ctlType c = ctlType c'.
  Proof.
    intros. unfold ctl_inj in Hinj.
    destruct c; destruct c'; try (by exfalso);
    unfold ctlType in *;
    try assert (Hat_ext := core_inj_ext _ _ _ Hinj);
    try assert (Hhalted := core_inj_halted _ _ _ Hinj); auto.
    destruct (at_external Sem c) as [[[? ?] ?]|]; simpl in *;
    destruct (at_external Sem c0) as [[[? ?] ?]|]; simpl in *; auto;
    try (by exfalso).
    destruct (halted Sem c), (halted Sem c0); by tauto.
  Qed.

  Lemma stepType_inj:
    forall tpc tpf i (pffi:containsThread tpf i) (pfci: containsThread tpc i) f,
      ctl_inj f (getThreadC pfci) (getThreadC pffi) ->
      getStepType pfci = getStepType pffi.
  Proof.
    intros.
    eapply ctlType_inj;
      by eauto.
  Qed.

  Lemma internal_step_type :
    forall i tp tp' m m' (cnt : containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hstep_internal: internal_step cnt Hcomp tp' m'),
      getStepType cnt = Internal.
  Proof.
    intros.
    unfold getStepType, ctlType.
    destruct Hstep_internal as [Hcstep | [[Hresume Heq] | [Hstart Heq]]].
    inversion Hcstep. subst. rewrite Hcode.
    assert (H1:= corestep_not_at_external Sem _ _ _ _ _ Hcorestep).
    rewrite H1.
    assert (H2:= corestep_not_halted Sem _ _ _ _ _ Hcorestep);
      by rewrite H2.
    inversion Hresume; subst.
    pf_cleanup;
      by rewrite Hcode.
    inversion Hstart; subst.
    pf_cleanup;
      by rewrite Hcode.
    
  Qed.

  Notation "cnt '@'  'I'" := (getStepType cnt = Internal) (at level 80).
  Notation "cnt '@'  'E'" := (getStepType cnt = Concurrent) (at level 80).
  Notation "cnt '@'  'S'" := (getStepType cnt = Suspend) (at level 80).
  Notation "cnt '@'  'H'" := (getStepType cnt = Halted) (at level 80).

  (** Simulations Diagrams *)
  Definition sim_internal_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem)
      (xs : Sch) (f : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hinternal: pff @ I)
      (Hsim: sim tpc mc tpf mf xs f fp),
    exists tpf' mf' fp',
      (forall U, fmachine_step (i :: U, tpf) mf (U, tpf') mf') /\
      sim tpc mc tpf' mf' (i :: xs) f fp'.

  Definition sim_external_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem)
      (xs : Sch) (f : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hexternal: pff @ E)
      (Hsynced: ~ List.In i xs)
      (Hsim: sim tpc mc tpf mf xs f fp),
    exists tpc' mc' tpf' mf' f' fp',
      (forall U, fmachine_step (i :: U, tpf) mf (U, tpf') mf') /\
      sim tpc' mc' tpf' mf' xs f' fp'.

  (** When we reach a suspend step, we can ``synchronize'' the two
  machines by executing on the coarse machine the internal steps of
  the thread that reached the suspend step. The injection of this
  thread will now serve as the new injection. *)

  Definition sim_suspend_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem)
      (xs : Sch) (f : memren) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hexternal: pff @ S)
      (Hsim: sim tpc mc tpf mf xs f fp),
    exists tpc' mc' tpf' mf' f' fp',
      (forall U, fmachine_step (i :: U, tpf) mf (U, tpf') mf') /\
      sim tpc' mc' tpf' mf' [seq x <- xs | x != i] f' fp'.

End SimDefs.

(** ** Proofs *)
Module SimProofs.

  Import mySchedule CoreLanguage InternalSteps.
  Require Import sepcomp.closed_safety.
  Import dry_context mySchedule DryMachine DryMachine.ThreadPool SEM.
  Import ThreadPoolWF StepLemmas.
  Import MemoryWD MemObsEq ValObsEq MemoryLemmas CoreInjections.
  
  Import SimDefs.
  
  (** Solves absurd cases from fine-grained internal steps *)
  Ltac absurd_internal Hstep :=
    inversion Hstep; try inversion Htstep; subst; simpl in *;
    try match goal with
        | [H: Some _ = Some _ |- _] => inversion H; subst
        end; pf_cleanup;
    repeat match goal with
           | [H: getThreadC ?Pf = _, Hint: ?Pf @ I |- _] =>
             unfold getStepType in Hint;
               rewrite H in Hint; simpl in Hint
           | [H1: match ?Expr with _ => _ end = _,
                  H2: ?Expr = _ |- _] => rewrite H2 in H1
           | [H: threadHalted _ |- _] =>
             inversion H; clear H; subst; pf_cleanup
           | [H1: is_true (isSome (halted ?Sem ?C)),
                  H2: match at_external _ _ with _ => _ end = _ |- _] =>
             destruct (at_external_halted_excl Sem C) as [Hext | Hcontra];
               [rewrite Hext in H2;
                 destruct (halted Sem C); discriminate |
                rewrite Hcontra in H1; exfalso; by auto]
           end; try discriminate; try (exfalso; by auto).

  (** Assumptions on threadwise semantics*)
  Context {cSpec : corestepSpec}.
  Hypothesis corestep_obs_eq:
    forall cc cf cc' mc mf mc' f
      (Hobs_eq: mem_obs_eq f mc mf)
      (Hcode_eq: core_inj f cc cf)
      (Hstep: corestep Sem the_ge cc mc cc' mc'),
    exists cf' mf' f',
      corestep Sem the_ge cf mf cf' mf'
      /\ core_inj f' cc' cf'
      /\ mem_obs_eq f' mc' mf'
      /\ ren_incr f f'
      /\ ren_separated f f' mc mf
      /\ (forall b1 b1' b2,
            f b1 = None ->
            f b1' = None ->
            f' b1 = Some b2 ->
            f' b1' = Some b2 ->
            b1 = b1')
      /\ ((exists p, ((Mem.nextblock mc' = Mem.nextblock mc + p)%positive /\
                (Mem.nextblock mf' = Mem.nextblock mf + p)%positive))
         \/ ((Mem.nextblock mc' = Mem.nextblock mc) /\
            (Mem.nextblock mf' = Mem.nextblock mf)))
      /\ (forall b,
            Mem.valid_block mf' b ->
            ~ Mem.valid_block mf b ->
            let bz := ((Zpos b) - ((Zpos (Mem.nextblock mf)) -
                                   (Zpos (Mem.nextblock mc))))%Z in
            f' (Z.to_pos bz) = Some b /\
            f (Z.to_pos bz) = None)
      /\ (Mem.nextblock mc = Mem.nextblock mf ->
         (forall b1 b2, f b1 = Some b2 -> b1 = b2) ->
         forall b1 b2, f' b1 = Some b2 -> b1 = b2).

  (* Starting from a wd state -- maybe it also requires the_ge to be
     wd, we get a new valid memory and the fact that there exists some
     renaming whose domain is the same as the new memory and
     additionally that the new core is well defined with respect to
     all renamings withe same domain.  Note that we cannot say
     anything about the codomain, i.e. that f' is an extension of f,
     because our definitions are not strong enough.*) 
  Hypothesis corestep_wd:
    forall c m c' m' f
      (Hwd: core_wd f c)
      (Hmem_wd: valid_mem m)
      (Hdomain: domain_memren f m)
      (Hcorestep: corestep Sem the_ge c m c' m'),
      valid_mem m' /\
      (exists f', ren_domain_incr f f' /\ domain_memren f' m') /\
      forall f', domain_memren f' m' ->
            core_wd f' c'.
  
  (** Proofs about [internal_execution] and [internal_step] *)
  
  Lemma internal_step_cmachine_step :
    forall (i : NatTID.tid) (tp tp' : thread_pool) (m m' : mem)
      (U : list NatTID.tid)
      (Hcnt: containsThread tp i)
      (Hcomp: mem_compatible tp m) 
      (Hstep_internal: internal_step Hcnt Hcomp tp' m'),
      cmachine_step ((buildSched (i :: U)), tp) m
                    ((buildSched (i :: U)), tp') m' /\
      (forall tp'' m'' U',
          cmachine_step ((buildSched (i :: U)), tp) m
                        ((buildSched U'), tp'') m'' ->
          tp' = tp'' /\ m' = m'' /\ i :: U = U').
  Proof.
    intros. split.
    destruct Hstep_internal as [Hcore | [[Hresume ?] | [Hstart ?]]]; subst;
    autounfold.
    econstructor; simpl; eauto.
    econstructor 2; simpl; eauto.
    econstructor 1; simpl; eauto.
    intros tp'' m'' U' Hstep.
    assert (Hstep_internal': internal_step Hcnt Hcomp tp'' m'' /\ i :: U = U').
    { inversion Hstep; subst; clear Hstep;
      simpl in *; inversion HschedN; subst; pf_cleanup;
      unfold internal_step; try (by auto);
      apply internal_step_type in Hstep_internal; exfalso;
      unfold getStepType, ctlType in Hstep_internal;
      try inversion Htstep; 
      try (inversion Hhalted); subst;
      unfold getThreadC in *; pf_cleanup;
      repeat match goal with
             | [H1: context[match ?Expr with | _ => _ end],
                    H2: ?Expr = _ |- _] =>
               rewrite H2 in H1
             end; try discriminate.
      destruct (at_external_halted_excl Sem c) as [Hnot_ext | Hcontra].
      rewrite Hnot_ext in Hstep_internal; try discriminate.
      destruct (halted Sem c) eqn:Hhalted'; try by exfalso.
      rewrite Hcontra in Hcant.
        by auto.
    }
    destruct Hstep_internal' as [Hstep_internal' Heq]; subst.
    destruct (internal_step_det Hstep_internal Hstep_internal'); subst.
    auto. 
  Qed.
  
  
  Lemma safeN_corestepN_internal:
    forall xs i U tpc mc tpc' mc' n
      (Hsafe : safeN coarse_semantics the_ge
                     ((size [seq x <- xs | x == i]) + n)
                     (buildSched (i :: U), tpc) mc)
      (Hexec : internal_execution [seq x <- xs | x == i] tpc mc tpc' mc'),
      corestepN CoarseSem the_ge (size [seq x <- xs | x == i])
                (buildSched (i :: U), tpc) mc (buildSched (i :: U), tpc') mc'
      /\ safeN coarse_semantics the_ge n (buildSched (i :: U), tpc') mc'.
  Proof.
    intros xs. induction xs as [ | x xs]; intros.
    { simpl in *. inversion Hexec; subst.
      auto.
      simpl in HschedN. discriminate.
    }
    { simpl in *.
      destruct (x == i) eqn:Hx; move/eqP:Hx=>Hx; subst.
      - simpl in Hsafe.
        destruct Hsafe as [[st' [m' Hmach_step]] Hsafe].
        destruct st' as [stU' tp'].
        specialize (Hsafe _ _ Hmach_step).
        inversion Hexec; subst; simpl in *; clear Hexec;
        inversion HschedN; subst i.
        assert (Hmach_step_det :=
                  internal_step_cmachine_step U Hstep).
        destruct Hmach_step_det as [Hmach_step' Hmach_det].
        specialize (Hmach_det _ _ _ Hmach_step).
        destruct Hmach_det as [? [? ?]]; subst.
        destruct (IHxs _ _ _ _ _ _ _ Hsafe Htrans) as [HcorestepN Hsafe'].
        eauto.
      - eapply IHxs; eauto.
    }
  Qed.
  
  Lemma at_internal_cmachine_step :
    forall i U U' tp tp' m m' (cnt: containsThread tp i)
      (isInternal: cnt @ I)
      (Hstep: cmachine_step (buildSched (i :: U), tp) m (U', tp') m'),
    exists (Hcomp : mem_compatible tp m),
      internal_step cnt Hcomp tp' m' /\ U' = buildSched (i :: U).
  Proof.
    intros.
    absurd_internal Hstep.
    exists Hcmpt. split; auto.
    do 2 right;
      by auto.
    exists Hcmpt. split; auto.
    right; left;
      by auto.
    exists Hcmpt. split; auto.
    left; auto.
  Qed.

  
  (** Starting from a well-defined state, an internal execution
  retains the well-definedeness for any injection that corresponds to
  the domain of the new memory. *)
  
  Lemma internal_step_wd:
    forall tp m tp' m' i (cnti: containsThread tp i) f
      (Hcomp: mem_compatible tp m)
      (Hmem_wd: valid_mem m)
      (Hdomain: domain_memren f m)
      (Htp_wd: tp_wd f tp)
      (Hge_wd: ge_wd f the_ge)
      (Hstep: internal_step cnti Hcomp tp' m'),
      valid_mem m' /\
      (exists f' : memren, ren_domain_incr f f' /\ domain_memren f' m') /\
      (forall f' : memren, domain_memren f' m' -> tp_wd f' tp').
  Proof.
    intros.
    inversion Hstep as [Htstep | [[Htstep ?] | [Htstep ?]]].
    - inversion Htstep; subst.
      erewrite restrPermMap_mem_valid with (Hlt := Hcomp i cnti) in Hmem_wd.
      apply corestep_wd with (f := f) in Hcorestep; eauto.
      destruct Hcorestep as [Hmem_wd' [Hf' Hcore_wd']].
      destruct Hf' as [f' [Hincr Hdomain']].
      assert (Hcore_wd_f':= Hcore_wd' _ Hdomain').
      split; auto.
      split; first by (eexists; eauto).
      intros f'' Hdomain''.
      intros j cntj.
      specialize (Hcore_wd' f'' Hdomain'').
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
      rewrite gssThreadCode.
      simpl;
        by auto.
      assert (cntj' := containsThread_internal_step' Hstep cntj).
      erewrite @gsoThreadCode with (cntj := cntj') by eauto.
      specialize (Htp_wd _ cntj').
      assert (Hincr': ren_domain_incr f f'').
        by (eapply domain_memren_incr with (f' := f'); eauto).
      eapply ctl_wd_incr;
        by eauto.
      specialize (Htp_wd _ cnti).
      rewrite Hcode in Htp_wd;
        by simpl in Htp_wd.
    - subst. split; auto.
      inversion Htstep; subst.
      split.
      exists f.
      split; unfold ren_domain_incr;
        by auto.
      intros f'' Hdomain''.
      intros j cntj'.
      assert (cntj: containsThread tp j)
        by (eapply cntUpdateC'; eauto).
      assert (Hincr: ren_domain_incr f f'')
        by (eapply domain_memren_incr with (f' := f) (f'' := f''); eauto;
            apply ren_domain_incr_refl).
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
      rewrite gssThreadCC.
      pf_cleanup.
      specialize (Htp_wd _ cntj).
      rewrite Hcode in Htp_wd.
      destruct X as [[? ?] ?].
      simpl in *.
      destruct Htp_wd as [Hcore_wd _].
      assert (Hargs:= at_external_wd _ _ Hcore_wd Hat_external).
      eapply after_external_wd; eauto.
      eapply core_wd_incr; eauto.
      eapply valid_val_list_incr;
        by eauto.
      erewrite <- @gsoThreadCC with (cntj := cntj); eauto.
      specialize (Htp_wd _ cntj).
      eapply ctl_wd_incr;
        by eauto.
    - subst; split; auto.
      inversion Htstep; subst.
      split.
      exists f.
      split; unfold ren_domain_incr;
        by auto.
      intros f'' Hdomain''.
      intros j cntj'.
      assert (cntj: containsThread tp j)
        by (eapply cntUpdateC'; eauto).
      assert (Hincr: ren_domain_incr f f'')
        by (eapply domain_memren_incr with (f' := f) (f'' := f''); eauto;
            apply ren_domain_incr_refl).
      destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
      rewrite gssThreadCC.
      pf_cleanup.
      simpl.
      eapply initial_core_wd; eauto.
      specialize (Htp_wd _ cntj).
      rewrite Hcode in Htp_wd.
      simpl in Htp_wd.
      eapply valid_val_incr;
        by eauto.
      eapply ge_wd_incr;
        by eauto.
      erewrite <- @gsoThreadCC with (cntj := cntj); eauto.
      specialize (Htp_wd _ cntj).
      eapply ctl_wd_incr;
        by eauto.
  Qed.

  Lemma internal_execution_wd:
    forall tp m tp' m' i xs f
      (Hdomain: domain_memren f m)
      (Hmem_wd: valid_mem m)
      (Htp_wd: tp_wd f tp)
      (Hge_wd: ge_wd f the_ge)
      (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m'),
      valid_mem m' /\
      (exists f' : memren, ren_domain_incr f f' /\ domain_memren f' m') /\
      (forall f' : memren, domain_memren f' m' -> tp_wd f' tp').
  Proof.
    intros.
    generalize dependent m.
    generalize dependent f.
    generalize dependent tp.
    induction xs; intros.
    simpl in Hexec; inversion Hexec; subst;
    [idtac| simpl in HschedN; by discriminate];
    split; auto;
    split; [exists f; split; unfold ren_domain_incr; auto | eauto].
    intros.
    eapply tp_wd_domain;
      by eauto.
    simpl in Hexec.
    destruct (a == i) eqn:Heq; move/eqP:Heq=>Heq; try eauto.
    subst a. inversion Hexec; subst.
    simpl in Htrans.
    simpl in HschedN; inversion HschedN; subst tid.
    assert (H := internal_step_wd Hmem_wd Hdomain Htp_wd Hge_wd Hstep).
    destruct H as [Hmem_wd0' [[f' [Hincr Hdomain0']] Htp_wd0']].
    specialize (Htp_wd0' f' Hdomain0').
    assert (Hge_wd0': ge_wd f' the_ge)
      by (eapply ge_wd_incr; eauto).
    destruct (IHxs _ f' Htp_wd0' Hge_wd0' m'0 Hdomain0' Hmem_wd0' Htrans)
      as (Hwd_mem' & Hf'' & Htp_wd').
    destruct Hf'' as [f'' [Hincr'' Hdomain'']].
    specialize (Htp_wd' _ Hdomain'').
    assert (ren_domain_incr f f'')
      by (eapply ren_domain_incr_trans; eauto).
    repeat match goal with
           | [|- _ /\ _] => split; eauto
           | [|- exists _, _] => eexists; eauto
           | [|- forall _, _] => intros
           end.
    eapply tp_wd_domain;
      by eauto.
  Qed.

  Lemma suspend_tp_wd:
    forall tpc tpc' (f : memren) i (pfc : containsThread tpc i)
      (Hsuspend: myCoarseSemantics.suspend_thread pfc tpc')
      (Htp_wd: tp_wd f tpc),
      tp_wd f tpc'.
  Proof.
    intros.
    inversion Hsuspend; subst.
    intros j cntj.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
    rewrite gssThreadCC.
    simpl. specialize (Htp_wd _ ctn).
    rewrite Hcode in Htp_wd.
    simpl in Htp_wd;
      by assumption.
    assert (ctnj0: containsThread tpc j)
      by (eapply cntUpdateC'; eauto).
    specialize (Htp_wd _ ctnj0).
    erewrite <- @gsoThreadCC with (cntj := ctnj0);
      by auto.
  Qed.
  
  (** Proofs about [fmachine_step]*)
  Lemma fstep_containsThread :
    forall tp tp' m m' i j U
      (cntj: containsThread tp j)
      (Hstep: fmachine_step (i :: U, tp) m (U, tp') m'),
      containsThread tp' j.
  Proof.
    intros.
    inversion Hstep; subst; try inversion Htstep;
    simpl in *; try inversion HschedN;
    subst; auto;
    repeat match goal with
           | [ |- containsThread (updThreadC _ _) _] =>
             apply cntUpdateC; auto
           | [ |- containsThread (updThread _ _ _) _] =>
             apply cntUpdate; auto
           | [ |- containsThread (updThreadR _ _) _] =>
             apply cntUpdateR; auto
           | [ |- containsThread (addThread _ _ _ _) _] =>
             apply cntAdd; auto
           end.
  Qed.

  Lemma fstep_containsThread' :
    forall tp tp' m m' i j U
      (cnti: containsThread tp i)
      (cntj: containsThread tp' j)
      (Hinternal: cnti @ I)
      (Hstep: fmachine_step (i :: U, tp) m (U, tp') m'),
      containsThread tp j.
  Proof.
    intros.
    absurd_internal Hstep;
      by eauto.
  Qed.
  
  Lemma fmachine_step_invariant:
    forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i) U
      (Hcompatible: mem_compatible tp m)
      (Hinternal: pf @ I)
      (Hstep: fmachine_step (i :: U, tp) m (U, tp') m'),
      invariant tp'.
  Proof.
    intros.
    absurd_internal Hstep;
      destruct Hinv as [Hno_race Hlock_pool].
    - constructor;
      try rewrite gsoThreadCLock;
      try rewrite gsoThreadCLPool.
      intros i j cnti' cntj' Hneq.
      assert (cnti := @cntUpdateC' tid i tp (Krun c_new) Htid cnti').
      assert (cntj := @cntUpdateC' tid j tp (Krun c_new) Htid cntj').
      erewrite @gThreadCR with (cntj := cntj).
      erewrite @gThreadCR with (cntj := cnti);
        by auto.
      intros i cnti'.
      assert (cnti := @cntUpdateC' tid i tp (Krun c_new) Htid cnti');
        by erewrite gThreadCR with (cntj := cnti).
      intros.
      assert (cnt0 := @cntUpdateC' tid i tp (Krun c_new) Htid cnt).
      rewrite gThreadCR;
        by eauto.
      intros.
      rewrite gsoThreadCLPool in H;
        by eauto.
    - constructor.
      intros i j cnti' cntj' Hneq.
      assert (cnti := @cntUpdateC' tid i tp (Krun c) Htid cnti').
      assert (cntj := @cntUpdateC' tid j tp (Krun c) Htid cntj').
      erewrite @gThreadCR with (cntj := cntj).
      erewrite @gThreadCR with (cntj := cnti);
        by auto.
      intros i cnti'.
      assert (cnti := @cntUpdateC' tid i tp (Krun c) Htid cnti').
      erewrite gsoThreadCLock;
        by erewrite gThreadCR with (cntj := cnti).
      intros.
      assert (cnt0 := @cntUpdateC' tid i tp (Krun c) Htid cnt).
      rewrite gThreadCR.
      rewrite gsoThreadCLPool in H;
        by eauto.
      intros.
      rewrite gsoThreadCLPool in H.
      rewrite gsoThreadCLock;
        by eauto.
      eapply corestep_invariant;
        by eauto.
  Qed.
  
  Lemma mem_compatible_setMaxPerm :
    forall tp m
      (Hcomp: mem_compatible tp m),
      mem_compatible tp (setMaxPerm m).
  Proof.
    intros tp m Hcomp.
    constructor;
      [intros i cnti b ofs | intros l pmap Hres b ofs |
       intros b ofs];
      rewrite getMaxPerm_correct;
      destruct (valid_block_dec m b) as [Hvalid | Hinvalid];
      try (
          erewrite setMaxPerm_MaxV by assumption; simpl;
          match goal with
          | [ |- match ?Expr with _ => _ end] =>
            destruct Expr
          end; constructor);
      try (
          erewrite setMaxPerm_MaxI by assumption;
          apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid;
          destruct Hcomp as [Hltth Hlrp Hltls]);
      [specialize (Hltth _ cnti b ofs) | specialize ((Hlrp _ _ Hres) b ofs) 
      | specialize (Hltls b ofs)];
      rewrite getMaxPerm_correct in Hltth Hlrp Hltls;
      unfold permission_at in *;
      rewrite Hinvalid in Hltth Hlrp Hltls; simpl in *;
        by auto.
  Qed.
  
  Lemma fmachine_step_compatible:
    forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i) U
      (Hcompatible: mem_compatible tp m)
      (Hinternal: pf @ I)
      (Hstep: fmachine_step (i :: U, tp) m (U, tp') m'),
      mem_compatible tp' m'.
  Proof.
    intros.
    absurd_internal Hstep;
      try (eapply updThreadC_compatible;
             by eauto).
    eapply mem_compatible_setMaxPerm. 
    eapply corestep_compatible;
      by eauto.
    (* this holds trivially, we don't need to use corestep_compatible*)
  Qed.

  Lemma gsoThreadR_fstep:
    forall tp tp' m m' i j U
      (Hneq: i <> j)
      (pfi: containsThread tp i)
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (Hinternal: pfi @ I)
      (Hstep: fmachine_step (i :: U, tp) m (U, tp') m'),
      getThreadR pfj = getThreadR pfj'.
  Proof.
    intros.
    absurd_internal Hstep;
      try (by rewrite <- gThreadCR with (cntj' := pfj'));
      erewrite <- @gsoThreadRes with (cntj' := pfj');
        by eauto.
  Qed.

  Lemma permission_at_fstep:
    forall tp tp' m m' i j U
      (Hneq: i <> j)
      (pfi: containsThread tp i)
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (Hcomp: mem_compatible tp m)
      (Hcomp': mem_compatible tp' m')
      (Hinv: pfi @ I)
      (Hstep: fmachine_step (i :: U, tp) m (U,tp') m') b ofs,
      permission_at (restrPermMap (Hcomp _ pfj)) b ofs Cur =
      permission_at (restrPermMap (Hcomp' _ pfj')) b ofs Cur.
  Proof.
    intros.
    do 2 rewrite restrPermMap_Cur;
      erewrite gsoThreadR_fstep;
        by eauto.
  Qed.

  Lemma gsoThreadC_fstepI:
    forall tp tp' m m' i j U
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (pfi: containsThread tp i)
      (Hinternal: pfi @ I)
      (Hstep: fmachine_step (i :: U, tp) m (U, tp') m')
      (Hneq: i <> j),
      getThreadC pfj = getThreadC pfj'.
  Proof.
    intros.
    absurd_internal Hstep;
      try (erewrite gsoThreadCC with (cntj' := pfj');
             by eauto);
      erewrite gsoThreadCode with (cntj' := pfj');
        by eauto.
  Qed.

  Lemma gsoLockSet_fstepI:
    forall tp tp' m m' i U
      (pfi: containsThread tp i)
      (Hinternal: pfi @ I)
      (Hstep: fmachine_step (i :: U, tp) m (U, tp') m'),
      lockSet tp = lockSet tp'.
  Proof.
    intros.
    absurd_internal Hstep;
      try (erewrite gsoThreadCLock;
             by eauto);
      erewrite gsoThreadLock;
        by eauto.
  Qed.

  Lemma gsoLockRes_fstepI :
    forall (tp tp' : thread_pool) (m m' : mem) (i : tid) 
      (U : seq tid) (pfi : containsThread tp i)
      (Hinternal: pfi @ I)
      (Hstep: fmachine_step (i :: U, tp) m (U, tp') m') addr,
      lockRes tp' addr = lockRes tp addr.
  Proof.
    intros.
    absurd_internal Hstep;
      try (by rewrite gsoThreadCLPool);
      try (by rewrite gsoThreadLPool).
  Qed.
  
  Hint Resolve fmachine_step_compatible fmachine_step_invariant
       fstep_containsThread fstep_containsThread' gsoLockSet_fstepI : fstep.

  Hint Rewrite gsoThreadR_fstep permission_at_fstep : fstep.
  
  Lemma fmachine_step_disjoint_val :
    forall tp tp' m m' i j U
      (Hneq: i <> j)
      (pfi: containsThread tp i)
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (Hcomp: mem_compatible tp m)
      (Hcomp': mem_compatible tp' m')
      (Hinv: pfi @ I)
      (Hstep: fmachine_step (i :: U, tp) m (U,tp') m') b ofs
      (Hreadable: 
         Mem.perm (restrPermMap (Hcomp _ pfj)) b ofs Cur Readable),
      Maps.ZMap.get ofs (Mem.mem_contents m) # b =
      Maps.ZMap.get ofs (Mem.mem_contents m') # b.
  Proof.
    intros.
    absurd_internal Hstep;
      try reflexivity;
      eapply corestep_disjoint_val;
        by eauto.
  Qed.

  Lemma diluteMem_decay :
    forall m m'
      (Hdecay: decay m m'),
      decay m (diluteMem m').
  Proof.
    intros.
    unfold decay in *.
    unfold Mem.perm in *. intros b ofs.
    assert (Hperm:= setMaxPerm_Cur m' b ofs).
    unfold permission_at in Hperm.
    rewrite Hperm.
      by auto.
  Qed.

  (** Profs about [mem_obs_eq] and [weak_mem_obs_eq] *)
  
  Lemma weak_obs_eq_restr :
    forall (m m' : Mem.mem) (f : memren)
      (weakObsEq: weak_mem_obs_eq f m m')
      (pf: permMapLt (getCurPerm m) (getMaxPerm m))
      (pf': permMapLt (getCurPerm m') (getMaxPerm (setMaxPerm m'))),
      weak_mem_obs_eq f (restrPermMap pf) (restrPermMap pf').
  Proof.
    intros. inversion weakObsEq.
    constructor; auto.
    intros.
    assert (Hrestr := restrPermMap_correct pf b1 ofs).
    destruct Hrestr as [_ Hcur].
    assert (Hrestr' :=
              restrPermMap_correct pf' b2 ofs).
    destruct Hrestr' as [_ Hcur'].
    rewrite Hcur; rewrite Hcur';
    do 2 rewrite getCurPerm_correct; eauto.
  Qed.

  Lemma mem_obs_eq_restr :
    forall (m m' : Mem.mem) (f : memren)
      (memObsEq: mem_obs_eq f m m')
      (pf: permMapLt (getCurPerm m) (getMaxPerm m))
      (pf': permMapLt (getCurPerm m') (getMaxPerm (setMaxPerm m'))),
      mem_obs_eq f (restrPermMap pf) (restrPermMap pf').
  Proof.
    intros.
    destruct memObsEq as [HweakObs HstrongObs].
    destruct HstrongObs as [Hperm_eq Hval].
    assert (Hrestr := restrPermMap_correct pf).
    assert (Hrestr' :=
              restrPermMap_correct pf').
    constructor;
      first by (eapply weak_obs_eq_restr; eauto).
    constructor;
      first by
        (intros;
          destruct (Hrestr b1 ofs) as [_ Hcur];
          destruct (Hrestr' b2 ofs) as [_ Hcur'];
          rewrite Hcur Hcur';
          do 2 rewrite getCurPerm_correct; auto).
    intros b1 b2 ofs Hf Hperm. unfold restrPermMap; simpl.
    eapply Hval; eauto.
    unfold Mem.perm in *.
    destruct (Hrestr b1 ofs) as [_ Hcur].
    unfold permission_at in *.
    rewrite Hcur in Hperm.
    rewrite getCurPerm_correct in Hperm.
      by assumption.
  Qed.

  Lemma weak_obs_eq_setMax:
    forall (f : memren) (m m' : mem),
      weak_mem_obs_eq f m m' <-> weak_mem_obs_eq f m (setMaxPerm m').
  Proof.
    intros. split; intros Hweak_obs;
            inversion Hweak_obs;
            constructor; auto;
            intros.
    rewrite setMaxPerm_Cur;
      by auto.
    specialize (perm_obs_weak0 _ _ ofs Hrenaming).
    rewrite setMaxPerm_Cur in perm_obs_weak0.
      by auto.
  Qed.
  
  (** ** Proofs of internal step safety and simulation*)

  Lemma tsim_fstep_safe:
    forall tpc tpc' tpf mc mc' mf i fi
      (pfc: containsThread tpc i) (pff: containsThread tpf i)
      (Hcompc: mem_compatible tpc mc)
      (Hcompf: mem_compatible tpf mf)
      (HmaxF: max_inv mf)
      (HinvF: invariant tpf)
      (Hstrong_sim: strong_tsim fi pfc pff Hcompc Hcompf)
      (Hstep_internal: internal_step pfc Hcompc tpc' mc'),
    exists tpf' mf' fi',
      (forall U, fmachine_step (i :: U, tpf) mf (U, tpf') mf') /\
      max_inv mf' /\
      ren_incr fi fi' /\
      ren_separated fi fi' mc mf /\
      (forall (pfc': containsThread tpc' i) (pff': containsThread tpf' i)
         (Hcompc': mem_compatible tpc' mc') (Hcompf': mem_compatible tpf' mf'),
          strong_tsim fi' pfc' pff' Hcompc' Hcompf') /\
      (forall j
         (pffj : containsThread tpf j),
          i <> j ->
          forall (b1 b2 : block),
            fi' b1 = Some b2 ->
            fi b1 = None ->
            forall ofs, (getThreadR pffj) # b2 ofs = None) /\
      (forall (b1 b2 : block) (ofs : Z),
          fi' b1 = Some b2 ->
          fi b1 = None -> (lockSet tpf) # b2 ofs = None) /\
      (forall (bl : block) (ofsl : Z)
                     (rmap : dry_machine.LocksAndResources.lock_info)
                     (b1 b2 : block) (ofs : Z),
                   fi' b1 = Some b2 ->
                   fi b1 = None ->
                   lockRes tpf (bl, ofsl) = Some rmap -> rmap # b2 ofs = None).
  Proof.
    intros.
    assert (HinvC': invariant tpc')
      by (eapply internal_step_invariant; eauto).
    destruct Hstep_internal as [Hcstep | [Hresume | Hstart]].
    { inversion Hcstep; subst; clear Hcstep.
      destruct Hstrong_sim as [Hcode_eq memObsEq].
      rewrite Hcode in Hcode_eq.
      (* getThreadC pff returns a Krun*)
      simpl in Hcode_eq. destruct (getThreadC pff) as [cf| ? | ? | ?] eqn:Hcodef;
        try (by exfalso).
      assert (H' := Hcorestep).
      eapply corestep_obs_eq in Hcorestep; eauto.
      destruct Hcorestep as
          (cf' & mf' & fi' & HcorestepF & Hcode_eq'
           & Hobs_eq' & Hincr & Hseparated & Hinjective
           & Hblocks & _ & _).
      remember (restrPermMap (Hcompf _ pff)) as mf1 eqn:Hrestrict.
      symmetry in Hrestrict.
      remember (updThread pff (Krun cf') (getCurPerm mf'))
        as tpf' eqn:Hupd.
      exists tpf', (setMaxPerm mf'), fi'.
      split.
      { (* fine machine steps *)
        intros U. eapply myFineSemantics.thread_step; simpl; eauto.
        econstructor; eauto.
      }
      {
        split.
        unfold max_inv.
        intros b ofs Hvalid.
        rewrite setMaxPerm_MaxV;
          by auto.
        split; first by assumption.
        split.
        (* Proof of seperation*)
        clear - Hupd Hseparated Hrestrict HmaxF.
        subst mf1.
        unfold ren_separated in *.
        intros b1 b2 Hfi Hfi'.
        specialize (Hseparated _ _ Hfi Hfi').
        do 2 erewrite restrPermMap_valid in Hseparated;
          by assumption.
        split.
        (* Proof of strong simulation*)
        intros. econstructor;
          first by (subst tpf'; by do 2 erewrite gssThreadCode).
        assert (Hlt_mc' : permMapLt (getCurPerm mc')
                                    (getMaxPerm mc'))
          by (unfold permMapLt; intros;
              rewrite getCurPerm_correct; rewrite getMaxPerm_correct;
              apply Mem.access_max).
        erewrite restrPermMap_irr with (Hlt' := Hlt_mc')
          by (by rewrite gssThreadRes).
        assert (Hlt_mf': permMapLt (getCurPerm mf')
                                   (getMaxPerm (setMaxPerm mf'))).
        { unfold permMapLt. intros.
          rewrite getCurPerm_correct. rewrite getMaxPerm_correct.
          destruct (valid_block_dec mf' b) as [Hvalid | Hinvalid].
          erewrite setMaxPerm_MaxV by assumption. simpl.
          destruct (permission_at mf' b ofs Cur); constructor.
          erewrite setMaxPerm_MaxI by assumption. simpl.
          apply Mem.nextblock_noaccess with (ofs := ofs) (k := Cur) in Hinvalid.
          unfold permission_at. rewrite Hinvalid. constructor.
        }
        erewrite restrPermMap_irr with (Hlt' := Hlt_mf')
          by (subst tpf'; rewrite gssThreadRes; eauto);
          by eapply mem_obs_eq_restr.
        (* block ownership*)
        (*sketch: the invariant is maintanted by coresteps hence it
           will hold for tpf'. Moreover we know that the new blocks in
           mc'|i will be mapped to new blocks in mf' by inject separated,
           where the permissions are empty for other threads. *)
        split.
        intros j pffj Hij b1 b2 Hfi' Hfi ofs.
        specialize (Hseparated _ _ Hfi Hfi').
        destruct Hseparated as [Hinvalidmc1 Hinvalidmf1].
        apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs) in Hinvalidmf1.
        assert (Hlt := Hcompf _ pffj b2 ofs).
        rewrite getMaxPerm_correct in Hlt.
        assert (Hperm_b2: permission_at mf b2 ofs Max = None).
        { subst mf1.
          assert (H:= restrPermMap_Max (Hcompf i pff) b2 ofs).
          unfold permission_at in H. rewrite Hinvalidmf1 in H.
          rewrite getMaxPerm_correct in H. by auto.
        }
        rewrite Hperm_b2 in Hlt.
        simpl in Hlt.
        destruct ((getThreadR pffj) # b2 ofs);
          by tauto.
        split.
        intros b1 b2 ofs Hfi' Hfi.
        specialize (Hseparated _ _ Hfi Hfi').
        destruct Hseparated as [Hinvalidmc1 Hinvalidmf1].
        apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs) in Hinvalidmf1.
        assert (Hlt := (compat_ls Hcompf) b2 ofs).
        rewrite getMaxPerm_correct in Hlt.
        assert (Hperm_b2: permission_at mf b2 ofs Max = None).
        { subst mf1.
          assert (H:= restrPermMap_Max (Hcompf i pff) b2 ofs).
          unfold permission_at in H. rewrite Hinvalidmf1 in H.
          rewrite getMaxPerm_correct in H. by auto.
        }
        rewrite Hperm_b2 in Hlt.
        simpl in Hlt.
        destruct ((lockSet tpf) # b2 ofs);
          by tauto.
        intros bl ofsl rmap b1 b2 ofs Hfi' Hfi Hres.
        specialize (Hseparated _ _ Hfi Hfi').
        destruct Hseparated as [Hinvalidmc1 Hinvalidmf1].
        apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs) in Hinvalidmf1.
        assert (Hlt := (compat_lp Hcompf _ Hres) b2 ofs).
        rewrite getMaxPerm_correct in Hlt.
        assert (Hperm_b2: permission_at mf b2 ofs Max = None).
        { subst mf1.
          assert (H:= restrPermMap_Max (Hcompf i pff) b2 ofs).
          unfold permission_at in H. rewrite Hinvalidmf1 in H.
          rewrite getMaxPerm_correct in H. by auto.
        }
        rewrite Hperm_b2 in Hlt.
        simpl in Hlt.
        destruct (rmap # b2 ofs);
          by tauto.
      }
    }
    { destruct Hresume as [Hresume Heq]; subst.
      inversion Hresume; subst; clear Hresume; pf_cleanup.
      destruct Hstrong_sim as [Hcode_eq memObsEq].
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pff) as [?|?|cf |? ] eqn:HcodeF;
        try (by exfalso).
      destruct Hcode_eq as [Hcode_eq Hval_eq].
      inversion Hval_eq; subst.
      (* After external for cf*)
      assert (Hafter_externalF := core_inj_after_ext _ _ _ _ Hcode_eq Hafter_external).
      destruct Hafter_externalF as [ov2 [cf' [Hafter_externalF [Hcode_eq' Hval_obs]]]].
      destruct ov2 as [v2 |]; try by exfalso.
      inversion Hval_obs; subst.
      (* cf is at external*)
      assert (Hat_externalF_spec := core_inj_ext _ _ _ Hcode_eq).
      rewrite Hat_external in Hat_externalF_spec.
      simpl in Hat_externalF_spec.
      destruct X as [[ef sig] val].
      destruct (at_external Sem cf) as [[[ef' sig'] val']|] eqn:Hat_externalF;
        try by exfalso.
      destruct Hat_externalF_spec as [? [? Harg_obs]]; subst.                         
      remember (updThreadC pff (Krun cf')) as tpf' eqn:Hupd.
      exists tpf', mf, fi.
      split.
      { (* The fine-grained machine steps *)
        intros. eapply myFineSemantics.resume_step with (Htid := pff); simpl; eauto.
        eapply myFineSemantics.ResumeThread with (c := cf);
          by eauto.
      }
      { split; first by auto.
        split; first by auto.
        split; first by congruence.
        split.
        intros.
        constructor;
          first by (subst tpf';
                     do 2 rewrite gssThreadCC; by simpl).
        erewrite restrPermMap_irr with
        (Hlt' := Hcompf _ pff) by (subst; by erewrite @gThreadCR with (cntj := pff)).
        erewrite restrPermMap_irr; eauto;
          by rewrite gThreadCR.
        split; [ | split]; intros; by congruence.
      }
    }
    { destruct Hstart as [Hstart Heq]; subst.
      inversion Hstart; subst; clear Hstart; pf_cleanup.
      destruct Hstrong_sim as [Hcode_eq memObsEq].
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pff) as [?|?|? |vf' arg'] eqn:HcodeF;
        try (by exfalso).
      destruct Hcode_eq as [? Harg_obs]; subst vf'.
      assert (Harg_obs_list: val_obs_list fi [:: arg] [:: arg'])
        by (constructor; auto; constructor).
      assert (HinitF := core_inj_init _ Harg_obs_list Hinitial).
      destruct HinitF as [c_newF [HinitialF Hcode_eq]].
      remember (updThreadC pff (Krun c_newF)) as tpf' eqn:Hupd.
      exists tpf', mf, fi.
      split.
      { (* The fine-grained machine steps *)
        intros. eapply myFineSemantics.start_step with (Htid := pff); simpl; eauto.
        eapply myFineSemantics.StartThread with (c_new := c_newF);
          by eauto.
      }
      { split; first by auto.
        split; first by auto.
        split; first by congruence.
        split.
        intros.
        constructor;
          first by (subst tpf';
                     do 2 rewrite gssThreadCC; by simpl).
        erewrite restrPermMap_irr with
        (Hlt' := Hcompf _ pff) by (subst; by erewrite @gThreadCR with (cntj := pff)).
        erewrite restrPermMap_irr; eauto;
          by rewrite gThreadCR.
        split; [|split]; intros; by congruence.
      }
    }
  Qed.

  Lemma diluteMem_valid :
    forall b m,
      Mem.valid_block m b <-> Mem.valid_block (diluteMem m) b.
  Proof.
    intros.
    split; auto.
  Qed.
  
  Lemma weak_tsim_fstep:
    forall tpc tpf tpf' mc mf mf' i j f U
      (pffi: containsThread tpf i)
      (pfcj: containsThread tpc j) (pffj: containsThread tpf j)
      (pffj': containsThread tpf' j)
      (Hcompc: mem_compatible tpc mc)
      (Hcompf: mem_compatible tpf mf)
      (Hcompf': mem_compatible tpf' mf')
      (HinvF: invariant tpf)
      (Hinternal: pffi @ I)
      (Hstep: fmachine_step (i :: U, tpf) mf (U, tpf') mf')
      (HweakSim: weak_tsim f pfcj pffj Hcompc Hcompf),
      weak_tsim f pfcj pffj' Hcompc Hcompf'.
  Proof.
    intros.
    Opaque containsThread.
    absurd_internal Hstep;
      destruct HweakSim
      as [Hdomain_invalid Hdomain_valid Hcodomain_valid Hinjective Hperm_obs_weak];
      constructor; auto.
    (* Case of start step*)
    intros b1 b2 ofs Hf.
    specialize (Hperm_obs_weak b1 b2 ofs Hf).
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite restrPermMap_Cur in Hperm_obs_weak.
    erewrite gThreadCR with (cntj := pffj);
      by assumption.
    (* Case of resume step*)
    intros b1 b2 ofs Hf.
    specialize (Hperm_obs_weak b1 b2 ofs Hf).
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite restrPermMap_Cur in Hperm_obs_weak.
    erewrite gThreadCR with (cntj := pffj);
      by assumption.
    (*Case of corestep*)
    intros b1 b2 Hf.
    erewrite restrPermMap_valid.
    erewrite <- diluteMem_valid.
    specialize (Hcodomain_valid b1 b2 Hf).
    erewrite restrPermMap_valid in Hcodomain_valid.
    eapply corestep_nextblock;
      by eauto.
    intros b1 b2 ofs Hf.
    specialize (Hperm_obs_weak _ _ ofs Hf).
    clear - Hcorestep Hf Hcodomain_valid Hperm_obs_weak.
    destruct (j == tid) eqn:Hjtid; move/eqP:Hjtid=>Hjtid.
    - subst.
      eapply corestep_decay in Hcorestep.
      apply decay_decay' in Hcorestep.
      specialize (Hcorestep b2 ofs).
      destruct Hcorestep as [_ Hold].
      apply Hcodomain_valid in Hf.
      specialize (Hold Hf).
      unfold permission_at in Hperm_obs_weak.
      do 2 erewrite restrPermMap_Cur.
      rewrite gssThreadRes.
      rewrite getCurPerm_correct.
      unfold permission_at.
      destruct Hold as [Hfree | Heq].
      + destruct Hfree as [Hfreeable Hempty].
        rewrite Hempty.
        destruct ((getThreadR pfcj) # b1 ofs); simpl;
          by constructor.
      + rewrite <- Heq.
        rewrite <- restrPermMap_Cur with (Hlt := Hcompc tid pfcj).
        unfold permission_at.
        pf_cleanup.
          by assumption.
    - do 2 rewrite restrPermMap_Cur.
      erewrite gsoThreadRes with (cntj := pffj); eauto.
      do 2 rewrite restrPermMap_Cur in Hperm_obs_weak.
        by assumption.
  Qed.
  
  Lemma cmachine_step_invariant:
    forall tpc mc tpc' mc' tpc'' mc'' U U' U'' n
      (HstepN: corestepN CoarseSem the_ge n
                         (U, tpc) mc (U', tpc') mc')
      (Hstep: cmachine_step (U', tpc') mc' (U'', tpc'') mc''),
      invariant tpc.
  Proof.
    intros. destruct n; simpl in HstepN. inversion HstepN; subst.
    inversion Hstep; subst; try inversion Htstep; auto.
    inversion Hhalted; simpl in *; subst; auto.
    simpl in *; subst; auto.
    destruct HstepN as [tpc''' [mc''' [Hstep0 _]]].
    clear Hstep.
    inversion Hstep0; subst; try inversion Htstep; auto.
    inversion Hhalted; simpl in *; subst; auto.
    simpl in *; subst; auto.
  Qed.

  Definition updateFP {tpc i} (cnti: containsThread tpc i)
             (fp: fpool tpc) (f' : memren) :=
    fun j cntj => if i == j then f' else fp j cntj.

  Lemma gssFP :
    forall tpc i f' (fp : fpool tpc) (cnti: containsThread tpc i),
      (updateFP cnti fp f') i cnti = f'.
  Proof.
    intros. unfold updateFP.
    rewrite if_true; auto.
  Qed.

  Lemma gsoFP :
    forall tpc i j f' (fp : fpool tpc) (cnti: containsThread tpc i)
      (cntj: containsThread tpc j) (Hneq: i <> j),
      (updateFP cnti fp f') j cntj = fp j cntj.
  Proof.
    intros. unfold updateFP.
    erewrite if_false; auto.
    apply/eqP; auto.
  Qed.
  
  Lemma sim_internal : sim_internal_def.
  Proof.
    unfold sim_internal_def.
    intros.
    inversion Hsim as
        [HnumThreads HmemCompC HmemCompF HsafeC
                     HsimWeak Hfpsep HsimStrong HsimLocks
                     HsimRes HinvF HmaxF Hmemc_wd Htpc_wd Hge_wd].
    assert (pfc: containsThread tpc i)
      by (eapply HnumThreads; eauto).
    (* Strong simulation for thread i*)
    destruct (HsimStrong i pfc pff)
      as [tpc' [mc' [Hincr [Hsynced [Hexec [Htsim [Hownedi [Hownedi_ls Hownedi_lp]]]]]]]];
      clear HsimStrong.
    assert (pfc': containsThread tpc' i)
      by (clear - Hexec pfc;
           eapply containsThread_internal_execution in pfc; eauto).
    specialize (Htsim pfc').
    (* It's safe to step the coarse grained machine for one more step on i*)
    specialize (HsafeC (mySchedule.buildSched (i :: nil))
                       ((size ([seq x <- xs | x == i])).+1)).
    rewrite <- addn1 in HsafeC.
    assert (HcoreN := safeN_corestepN_internal xs _ _ 1 HsafeC Hexec).
    destruct HcoreN as [HcorestepN HsafeN].
    unfold safeN in HsafeN; simpl in *.
    destruct HsafeN as [[[U tpc''] [mc'' Hstep']] _].
    assert (HinvC: invariant tpc)
      by (eapply cmachine_step_invariant; eauto).
    assert (memCompC' := internal_execution_compatible HmemCompC Hexec).
    specialize (Htsim memCompC').
    assert (Hinternal_pfc': pfc' @ I)
      by (by erewrite (stepType_inj _ _ _ (code_eq Htsim))).
    apply at_internal_cmachine_step with (cnt := pfc') in Hstep'; eauto.
    destruct Hstep' as [Hcomp [Hstep' Heq]]. subst U; pf_cleanup.
    (* And from this we derive safety for 1 step for fine-grained*)
    destruct (tsim_fstep_safe HmaxF HinvF Htsim Hstep')
      as [tpf' [mf' [fi' [HstepF [HmaxF' [Hincr' [Hsepi [Htsim' [Howned' [Hownedls' Hownedlp']]]]]]]]]].
    assert (HstepF_empty := HstepF empty).
    assert (pfc'': containsThread tpc'' i)
      by (eapply containsThread_internal_step; eauto).
    assert (pff': containsThread tpf' i)
      by (eapply (fstep_containsThread pff); eauto).
    assert (memCompC'': mem_compatible tpc'' mc'').
    eapply internal_step_compatible with (Hcompatible := memCompC'); eauto.
    assert (memCompF': mem_compatible tpf' mf')
      by (eapply fmachine_step_compatible with (pf := pff); eauto).
    exists tpf', mf', (updateFP pfc fp fi').
    split.
    (** Proof that the fine-grained execution steps *)
    assumption.
    (** Proof that the simulation is preserved*)
    clear HsafeC HcorestepN.
    eapply Build_sim with (mem_compc := HmemCompC) (mem_compf := memCompF').
    - intros k;
      split;
      intro pfk;
      [apply HnumThreads in pfk | apply HnumThreads];
        by eauto with fstep.
    - apply (safeCoarse Hsim).
    - (** Proof of weak simulation between threads *)
      intros j pfcj pffj'.
      assert (pffj: containsThread tpf j)
        by (eauto with fstep).
      eapply weak_tsim_fstep with (pffi := pff); eauto.
    - (** Proof of seperation of injection pool*)
      (*TODO: comment this proof*)
      intros k j cntk cntj Hkj.
      destruct (i == k) eqn:Hik;
        move/eqP:Hik=>Hik;
        try subst k;
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
      + by exfalso.
      + pf_cleanup.
        rewrite gssFP. rewrite gsoFP; auto.
        intros b b' b2 b2' Hf Hf' Hfi' Hfj.
        destruct (fp i pfc b) as [b2''|] eqn:Hfi.
        assert (Heq:b2 = b2'')
          by (apply Hincr' in Hfi; rewrite Hfi in Hfi';
                by inversion Hfi'); subst b2''.
        eapply Hfpsep with (i := i) (j := j) (b := b); eauto.
        unfold ren_separated in Hsepi.
        specialize (Hsepi _ _ Hfi Hfi').
        destruct Hsepi as [HinvalidC' HinvalidF'].
        assert (pfj: containsThread tpf j)
          by (eapply HnumThreads; eauto).
        assert (Hsimj := (simStrong Hsim) j cntj pfj).
        destruct Hsimj as [tpcj' [mc'j [_ [_ [Hexecj [Htsimj _]]]]]].
        assert (pfj': containsThread tpcj' j)
          by (eapply containsThread_internal_execution; eauto).
        assert (HmemCompCj': mem_compatible tpcj' mc'j)
          by (eapply internal_execution_compatible with (tp := tpc); eauto).
        specialize (Htsimj pfj' HmemCompCj').
        assert (Hcodomain := codomain_valid (weak_obs_eq (obs_eq Htsimj))).
        specialize (Hcodomain _ _ Hfj).
        erewrite restrPermMap_valid in Hcodomain.
        intros Hcontra. subst.
          by auto.
      + pf_cleanup.
        rewrite gssFP.
        rewrite gsoFP; auto.
        intros b b' b2 b2' Hf Hf' Hfk' Hfj'.
        destruct (fp j cntj b') as [b2''|] eqn:Hfj.
        assert (Heq:b2' = b2'')
          by (apply Hincr' in Hfj; rewrite Hfj in Hfj';
                by inversion Hfj'); subst b2''.
        intros Hcontra.
        eapply Hfpsep with (i := j) (j := k) (b := b') (b' := b) (b2 := b2');
          by eauto.
        unfold ren_separated in Hsepi.
        specialize (Hsepi _ _ Hfj Hfj').
        destruct Hsepi as [HinvalidC' HinvalidF'].
        assert (pffk: containsThread tpf k)
          by (by eapply HnumThreads).
        assert (Hsimk := (simStrong Hsim) k cntk pffk).
        destruct Hsimk as [tpck' [mck' [_ [_ [Hexeck [Htsimk _]]]]]].
        assert (pfck': containsThread tpck' k)
          by (eapply containsThread_internal_execution; eauto).
        assert (HmemCompCk': mem_compatible tpck' mck')
          by (eapply internal_execution_compatible with (tp := tpc); eauto).
        specialize (Htsimk pfck' HmemCompCk').
        assert (Hcodomain := codomain_valid (weak_obs_eq (obs_eq Htsimk))).
        specialize (Hcodomain _ _ Hfk').
        erewrite restrPermMap_valid in Hcodomain.
        intros Hcontra. subst. by auto.
      + rewrite gsoFP; auto.
        rewrite gsoFP; eauto.  
    - (** Proof of strong simulation between threads*)
      intros j pfcj pffj'.
      destruct (i == j) eqn:Heq; move/eqP:Heq=>Heq.
      { subst j. exists tpc'', mc''.
        pf_cleanup. rewrite gssFP.
        split;
          first by (eapply ren_incr_trans; eauto).
        split.
        intros Hnostep.
        simpl in Hnostep.
        erewrite if_true in Hnostep by (apply eq_refl);
          by discriminate.
        split.
        simpl. erewrite if_true by (apply eq_refl).
        assert (Heq: i :: [seq x <- xs | x == i] =
                     [seq x <- xs | x == i] ++ [:: i]).
        { clear. induction xs. reflexivity.
          simpl. destruct (a==i) eqn:Heq; move/eqP:Heq=>Heq.
          subst. simpl. rewrite IHxs. reflexivity.
          auto.
        }
        rewrite Heq.
        eapply internal_execution_trans;
          by eauto.
        split;
          first by (intros; eapply Htsim').
        split.
        intros k pffk' Hik b1 b2 ofs Hfi' Hf.
        assert (pffk: containsThread tpf k)
          by (eauto with fstep).
        erewrite <- gsoThreadR_fstep with (pfj := pffk); eauto.
        destruct (valid_block_dec mc' b1) as [Hvalidmc'b1 | Hinvalidmc'b1].
        assert (Hfb1 := (domain_valid (weak_obs_eq (obs_eq Htsim))) b1).
        erewrite restrPermMap_valid in Hfb1.
        destruct (Hfb1 Hvalidmc'b1) as [b2' Hfi].
        assert (b2' = b2)
          by (apply Hincr' in Hfi; rewrite Hfi in Hfi';
              inversion Hfi'; by subst); subst;
          by eauto.
        assert (Hfb1 := (domain_invalid
                           (weak_obs_eq (obs_eq Htsim))) b1).
        erewrite restrPermMap_valid in Hfb1.
        specialize (Hfb1 Hinvalidmc'b1);
          by eauto.
        split.
        intros b1 b2 ofs Hfi' Hf.
        erewrite <- gsoLockSet_fstepI with (tp := tpf); eauto.
        destruct (valid_block_dec mc' b1) as [Hvalidmc'b1 | Hinvalidmc'b1].
        assert (Hfb1 := (domain_valid (weak_obs_eq (obs_eq Htsim))) b1).
        erewrite restrPermMap_valid in Hfb1.
        destruct (Hfb1 Hvalidmc'b1) as [b2' Hfi].
        assert (b2' = b2)
          by (apply Hincr' in Hfi; rewrite Hfi in Hfi';
              inversion Hfi'; by subst); subst;
          by eauto.
        assert (Hfb1 := (domain_invalid
                           (weak_obs_eq (obs_eq Htsim))) b1).
        erewrite restrPermMap_valid in Hfb1.
        specialize (Hfb1 Hinvalidmc'b1);
          by eauto.
        intros bl ofsl rmap b1 b2 ofs Hfi' Hf Hres.
        erewrite gsoLockRes_fstepI with (tp := tpf) in Hres; eauto.
        destruct (valid_block_dec mc' b1) as [Hvalidmc'b1 | Hinvalidmc'b1].
        assert (Hfb1 := (domain_valid (weak_obs_eq (obs_eq Htsim))) b1).
        erewrite restrPermMap_valid in Hfb1.
        destruct (Hfb1 Hvalidmc'b1) as [b2' Hfi].
        assert (b2' = b2)
          by (apply Hincr' in Hfi; rewrite Hfi in Hfi';
              inversion Hfi'; by subst); subst;
          by eauto.
        assert (Hfb1 := (domain_invalid
                           (weak_obs_eq (obs_eq Htsim))) b1).
        erewrite restrPermMap_valid in Hfb1.
        specialize (Hfb1 Hinvalidmc'b1).
          by eauto.
      }
      { simpl.
        rewrite gsoFP; auto.
        erewrite if_false by (apply/eqP; intros Hcontra; auto).
        clear HsimWeak Htsim Hincr Hincr'.
        assert (HsimStrong := simStrong Hsim).
        assert (pffj: containsThread tpf j)
          by eauto with fstep.
        destruct (HsimStrong j pfcj pffj)
          as [tpcj' [mcj' [Hincrj [Hsyncedj [Hexecj [Htsimj [Hownedj [Hownedj_ls Hownedj_lp]]]]]]]].
        exists tpcj', mcj'. split; auto. split; [ by auto | split; auto].
        split.
        (* difficult part: simulation between tpf' and tpcj' *)
        intros pfcj' memCompCj'.
        specialize (Htsimj pfcj' memCompCj').
        inversion Htsimj as [code_eqjj memObsEqj].
        constructor;
          first by (erewrite <- gsoThreadC_fstepI
                    with (pfj' := pffj') (pfj := pffj); by eauto).
        constructor. (*mem_obs_eq proof*)
        { constructor.
          - apply (domain_invalid (weak_obs_eq memObsEqj)).
          - apply (domain_valid (weak_obs_eq memObsEqj)).
          - assert (Hcodomain := (codomain_valid (weak_obs_eq memObsEqj))).
            intros b1 b2 Hfj.
            specialize (Hcodomain b1 b2 Hfj).
            admit. (*lift valid block for fmachine_step*)
          - by apply (injective (weak_obs_eq (obs_eq Htsimj))).
          - intros b1 b2 ofs.
            rewrite <- permission_at_fstep with
            (Hcomp := (mem_compf Hsim)) (U := empty) (i := i) (pfi := pff)
                                        (pfj := pffj)
                                        (Hcomp' := memCompF'); auto.
              by apply (perm_obs_weak (weak_obs_eq memObsEqj)).
        }
        constructor. (*strong_obs_eq proof *)
        { intros b1 b2 ofs.
          rewrite <- permission_at_fstep with
          (Hcomp := (mem_compf Hsim)) (i := i) (U := empty) (pfi := pff)
                                      (pfj := pffj) (Hcomp' := memCompF'); auto.
            by apply (perm_obs_strong (strong_obs_eq memObsEqj)).
        }
        { intros b1 b2 ofs Hfj Hperm. unfold restrPermMap. simpl.
          assert (Hval := val_obs_eq (strong_obs_eq memObsEqj)).
          specialize (Hval b1 b2 ofs Hfj Hperm).
          unfold restrPermMap in Hval. simpl in Hval.
          assert (Hpermf: Mem.perm (restrPermMap (HmemCompF _ pffj))
                                   b2 ofs Cur Readable).
          { specialize (HstepF empty).
            assert (Hperm_eqf :=
                      permission_at_fstep Heq pff pffj pffj' HmemCompF memCompF'
                                          Hinternal HstepF b2 ofs).
            unfold permission_at in Hperm_eqf.
            assert (Hperm_weak := (perm_obs_weak (weak_obs_eq memObsEqj) b1
                                                 ofs Hfj)).
            assert (Hperm_strong := (perm_obs_strong (strong_obs_eq memObsEqj))
                                      b1 b2 ofs Hfj).
            clear - Hperm Hperm_eqf Hperm_strong Hperm_weak.
            unfold permission_at in *.
            unfold Mem.perm. rewrite Hperm_strong.
              by auto.
          }
          specialize (HstepF empty).
          erewrite <- fmachine_step_disjoint_val with
          (tp := tpf) (i := i) (j := j) (m' := mf')
                      (m := mf) (tp' := tpf') (U := empty);
            by eauto. 
        }
        (* block ownership *)
        split.
        intros k pffk' Hjk b1 b2 ofs Hfj Hf.
        assert (pffk: containsThread tpf k)
          by (eapply fstep_containsThread'; eauto).
        specialize (Hownedj _ pffk Hjk b1 b2 ofs Hfj Hf).
        destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
        subst k.
        assert (pfcj': containsThread tpcj' j)
          by (eapply containsThread_internal_execution; eauto).
        assert (Hcompcj': mem_compatible tpcj' mcj')
          by (eapply internal_execution_compatible with (tp := tpc) (m := mc);
               eauto).
        specialize (Htsimj pfcj' Hcompcj').
        assert (Hcodomain := (codomain_valid (weak_obs_eq
                                                (obs_eq Htsimj)))).
        specialize (Hcodomain _ _ Hfj).
        erewrite restrPermMap_valid in Hcodomain.
        clear - Hownedj Hcodomain Hjk HstepF_empty Hinternal HmemCompF.
        absurd_internal HstepF_empty;
          try by erewrite gThreadCR with (cntj := Htid).
        apply corestep_decay in Hcorestep.
        apply decay_decay' in Hcorestep.
        destruct (Hcorestep b2 ofs) as [_ Hdecay_valid].
        assert (Hp := restrPermMap_Cur (HmemCompF _ Htid ) b2 ofs).
        unfold permission_at in Hp.
        destruct (Hdecay_valid Hcodomain) as [[Hcontra _]| Hstable].
        rewrite Hp in Hcontra;
          by congruence.
        rewrite Hp in Hstable.
        rewrite Hownedj in Hstable.
        erewrite gssThreadRes.
        rewrite getCurPerm_correct. auto.
        erewrite <- gsoThreadR_fstep with (pfi := pff) (pfj := pffk);
          by eauto.
        split.
        intros b1 b2 ofs Hfj Hf.
        specialize (Hownedj_ls b1 b2 ofs Hfj Hf).
        erewrite <- gsoLockSet_fstepI with (tp := tpf);
          by eauto.
        intros bl ofsl rmap b1 b2 ofs Hfj Hf Hres.
        erewrite gsoLockRes_fstepI with (tp := tpf) in Hres;
          by eauto.
      }
      { (*lockset sim *)
        clear - HsimLocks HstepF_empty Hinternal.
        destruct HsimLocks as [HLocksPerm HLocksVal].
        constructor. 
        intros b1 b2 ofs Hf.
        do 2 rewrite restrPermMap_Cur.
        erewrite <- gsoLockSet_fstepI with (tp := tpf) (tp' := tpf'); eauto.
        specialize (HLocksPerm _ _ ofs Hf);
          by do 2 rewrite restrPermMap_Cur in HLocksPerm.
        intros b1 b2 ofs Hf Hperm.
        simpl in *. 
        specialize (HLocksVal _ _ _ Hf Hperm).
        absurd_internal HstepF_empty; auto.
        assert (HpermF: Mem.perm (restrPermMap (compat_ls HmemCompF))
                                 b2 ofs Cur Readable).
        { unfold Mem.perm in *.
          specialize (HLocksPerm _ _ ofs Hf).
          unfold permission_at in HLocksPerm.
          rewrite HLocksPerm;
            by auto.
        } 
        erewrite <- corestep_disjoint_val_lockset with (m := mf) (m' := m');
          by eauto.
      }
      { (*resources sim*)
        intros.
        assert (Hl2' := gsoLockRes_fstepI pff Hinternal HstepF_empty (bl2,ofs)).
        rewrite Hl2 in Hl2'. symmetry in Hl2'.
        specialize (HsimRes _ _ _ _ _ Hf Hl1 Hl2').
        destruct HsimRes as [HpermRes HvalRes].
        constructor.
        intros b1 b2 ofs0 Hf1.
        do 2 rewrite restrPermMap_Cur.
        specialize (HpermRes _ _ ofs0 Hf1);
          by do 2 rewrite restrPermMap_Cur in HpermRes.
        intros b1 b2 ofs0 Hf1 Hperm.
        simpl in *.
        specialize (HvalRes _ _ ofs0 Hf1 Hperm).

        assert (HpermF: Mem.perm (restrPermMap (compat_lp HmemCompF (bl2,ofs) Hl2'))
                                 b2 ofs0 Cur Readable).
        { unfold Mem.perm in *.
          specialize (HpermRes _ _ ofs0 Hf1).
          unfold permission_at in HpermRes.
            by rewrite HpermRes.
        }
        absurd_internal HstepF_empty; auto.
        erewrite <- corestep_disjoint_val_lockpool with (m := mf) (m' := m');
          by eauto.
      }
      { (*invariant tpf' *)
        eapply fmachine_step_invariant with (tp := tpf); eauto.
      }
      { assumption.  }
      { assumption. }
      { assumption. }
      { assumption. }
  Admitted.
  
  (** ** Proof of simulation for stop steps *)

  Lemma filter_neq_eq :
    forall {A :eqType} (xs : seq A) i j (Hneq: i <> j),
      [seq x <- [seq x <- xs | x != i] | x == j] = [seq x <- xs | x == j].
  Proof.
    intros. induction xs.
    - reflexivity.
    - simpl. destruct (a != i) eqn:Hai; move/eqP:Hai=>Hai.
      simpl.
      destruct (a ==j) eqn:Haj; move/eqP:Haj=>Haj;
        [by apply f_equal | assumption].
      subst. erewrite if_false by (apply/eqP; auto).
      assumption.
  Qed.
  
  Lemma suspend_step_inverse:
    forall i U U' tpc tpc' mc mc'
      (cnt: containsThread tpc i)
      (Hsuspend: cnt @ S)
      (Hstep: cmachine_step (i :: U, tpc) mc (U', tpc') mc'),
      U = U' /\ mc = mc' /\ mem_compatible tpc mc /\
      myCoarseSemantics.suspend_thread cnt tpc'.
  Proof.
    intros.
    inversion Hstep; simpl in *; subst; inversion HschedN; subst;
    try (inversion Htstep || inversion Hhalted); subst; pf_cleanup;
    unfold getStepType in Hsuspend;
    try rewrite Hcode in Hsuspend; simpl in Hsuspend;
    try match goal with
        | [H: match ?Expr with _ => _ end = _, H2: ?Expr = _ |- _] =>
          rewrite H2 in H
        end; try discriminate;
    try match goal with
        | [H: ~ containsThread _ _, H2: containsThread _ _ |- _] =>
          exfalso; by auto
        | [H: is_true (isSome (@halted _ _ _ _ _))  |- _] => 
          destruct (at_external_halted_excl Sem c) as [Hnot_ext | Hcontra];
            [rewrite Hnot_ext in Hsuspend;
              destruct (halted Sem c); discriminate |
             rewrite Hcontra in Hcant; by auto]
        end.
    destruct (at_external Sem c) eqn:Hat_external.
    apply corestep_not_at_external in Hcorestep.
      by congruence.
      destruct (halted Sem c); by discriminate.
      split; by auto.
  Qed.

  Lemma strong_tsim_step:
    forall tp1 tp2 tp1' m1 m2 m1' j f
      (pf1j: containsThread tp1 j)
      (pf1j': containsThread tp1' j)
      (Hcomp1: mem_compatible tp1 m1)
      (Hcomp1': mem_compatible tp1' m1')
      (Hinv: invariant tp1')
      (Hsim: strong_tsim f pf1j pf1j' Hcomp1 Hcomp1')
      (Hstep: internal_step pf1j Hcomp1 tp2 m2),
    exists tp2' m2' f',
      internal_step pf1j' Hcomp1' tp2' m2' /\
      ren_incr f f' /\
      ren_separated f f' m1 m1' /\
      (forall b1 b1' b2,
          f b1 = None ->
          f b1' = None ->
          f' b1 = Some b2 ->
          f' b1' = Some b2 ->
          b1 = b1') /\
      ((exists p, ((Mem.nextblock m2 = Mem.nextblock m1 + p)%positive /\
              (Mem.nextblock m2' = Mem.nextblock m1' + p)%positive))
       \/ ((Mem.nextblock m2 = Mem.nextblock m1) /\
          (Mem.nextblock m2' = Mem.nextblock m1'))) /\
      (forall b,
          Mem.valid_block m2' b ->
          ~ Mem.valid_block m1' b ->
          let bz := ((Zpos b) - ((Zpos (Mem.nextblock m1')) -
                                 (Zpos (Mem.nextblock m1))))%Z in
          f' (Z.to_pos bz) = Some b /\
          f (Z.to_pos bz) = None) /\
      (exists (pf2j: containsThread tp2 j)
         (pf2j': containsThread tp2' j)
         (Hcomp2: mem_compatible tp2 m2)
         (Hcomp2': mem_compatible tp2' m2'),
          strong_tsim f' pf2j pf2j' Hcomp2 Hcomp2') /\
      (Mem.nextblock m1 = Mem.nextblock m1' ->
       (forall b1 b2 : block, f b1 = Some b2 -> b1 = b2) ->
       forall b1 b2 : block, f' b1 = Some b2 -> b1 = b2).
  Proof.
    intros.
    inversion Hstep as [Hcstep | [[Hresume ?] | [Hstart ?]]].
    - inversion Hcstep; subst.
      inversion Hsim as [Hcode_eq Hmem_obs_eq].
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [c1' | | |] eqn:Hcodej'; try by exfalso.
      assert (H := corestep_obs_eq c c1' c' m2 Hmem_obs_eq Hcode_eq Hcorestep).
      destruct H
        as [c2' [m2' [f' [Hcorestep' [Hcode_eq'
                                        [Hobs_eq [Hincr [Hseparated
                                                           [Hinjective
                                                              [Hnextblock [Hinverse Hid]]]]]]]]]]].
      exists (updThread pf1j' (Krun c2') (getCurPerm m2')), m2', f'.
      assert (Hinternal':
                internal_step pf1j' Hcomp1'
                              (updThread pf1j' (Krun c2') (getCurPerm m2')) m2')
        by (left; econstructor; eauto).
      split; first by assumption.
      split; first by assumption.
      split; first by assumption.
      split; first by assumption.
      split; first by assumption.
      split; first by auto.
      split.
      { assert (pf2j := containsThread_internal_step Hstep pf1j).
        assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
        assert (Hcomp2 := internal_step_compatible Hstep).
        assert (Hcomp2' := internal_step_compatible Hinternal').
        exists pf2j, pf2j', Hcomp2, Hcomp2'.
        constructor; first by do 2 rewrite gssThreadCode.
        destruct Hobs_eq as [[Hinvalid' Hvalid' ? ? Hweak_perm] [Hstrong_perm Hval]].
        constructor.
        + (*weak_mem_obs_eq proof*)
          constructor.
          * intros b Hinvalid;
            erewrite restrPermMap_valid in Hinvalid;
              by eauto. 
          * intros b Hvalid;
            erewrite restrPermMap_valid in Hvalid;
              by eauto.
          * eauto.
          * eauto. 
          * intros b1 b2 ofs Hf';
            do 2 rewrite restrPermMap_Cur;
            do 2 rewrite gssThreadRes;
          do 2 rewrite getCurPerm_correct;
            by eauto.
        +(* strong_perm proof *)
          constructor.
          * intros b1 b2 ofs Hf'.
            do 2 rewrite restrPermMap_Cur;
              do 2 rewrite gssThreadRes;
              do 2 rewrite getCurPerm_correct;
                by eauto.
          * (* val proof *)
            intros b1 b2 ofs Hf' Hreadable.
            simpl.
            eapply Hval; eauto.
            unfold Mem.perm in *.
            assert (H:= restrPermMap_Cur (Hcomp2 j pf2j) b1 ofs).
            unfold permission_at in H.
            rewrite H in Hreadable.
            rewrite gssThreadRes in Hreadable;
              rewrite getCurPerm_correct in Hreadable.
              by assumption. }
      do 2 erewrite restrPermMap_nextblock in Hid;
        by eauto.
    - (* Case internal step is a resume or start step*)
      subst m2.
      inversion Hsim as [Hcode_eq Hmem_obs_eq].
      inversion Hresume; subst.
      pf_cleanup.
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [ | |c1'|] eqn:Hcode'; try by exfalso.
      destruct Hcode_eq as [Hcode_eq Hval_eq].
      inversion Hval_eq; subst.
      assert (Hat_external_spec := core_inj_ext _ _ _ Hcode_eq).
      rewrite Hat_external in Hat_external_spec.
      destruct X as [[? ?] vs].
      destruct (at_external Sem c1') as [[[? ?] ?] | ] eqn:Hat_external';
        try by exfalso.
      destruct Hat_external_spec as [? [? ?]]; subst.
      assert (Hafter_external' := core_inj_after_ext _ _ _ _
                                                     Hcode_eq Hafter_external).
      destruct Hafter_external' as [ov2 [c2' [Hafter_external'
                                                [Hcore_inj' Hval_obs]]]].
      destruct ov2 as [? |]; try by exfalso.
      inversion Hval_obs; subst.
      exists (updThreadC pf1j' (Krun c2')), m1', f.
      assert (Hinternal':
                internal_step pf1j' Hcomp1' (updThreadC pf1j' (Krun c2')) m1')
        by ( clear - Hat_external' Hafter_external' Hcode' Hinv;
             right; left; split; econstructor; eauto).
      split;
        first by assumption.
      split; first by auto.
      split; first by congruence.
      split; first by congruence.
      split; first by auto.
      split; first by
          (intros; by exfalso).
      split; try by eauto.
      assert (pf2j := containsThread_internal_step Hstep pf1j).
      assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
      assert (Hcomp2 := internal_step_compatible Hstep).
      assert (Hcomp2' := internal_step_compatible Hinternal').
      exists pf2j, pf2j', Hcomp2, Hcomp2'.
      constructor; first by do 2 rewrite gssThreadCC.
      destruct Hmem_obs_eq
        as [[Hinvalid' Hvalid' Hcodomain Hinjective Hweak_perm]
              [Hstrong_perm Hval]].
      constructor.
      + (*weak_mem_obs_eq proof*)
        constructor.
        * intros b Hinvalid;
          erewrite restrPermMap_valid in Hinvalid;
            by eauto. 
        * intros b Hvalid;
          erewrite restrPermMap_valid in Hvalid;
            by eauto.
        * by eauto.
        * by eauto.
        * intros b1 b2 ofs Hf'. 
          do 2 rewrite restrPermMap_Cur;
            do 2 rewrite gThreadCR.
          specialize (Hweak_perm _ _ ofs Hf').
          do 2 rewrite restrPermMap_Cur in Hweak_perm.
            by assumption.
      + (* strong_perm proof *)
        constructor.
        intros b1 b2 ofs Hf'.
        do 2 rewrite restrPermMap_Cur;
          do 2 rewrite gThreadCR;
          specialize (Hstrong_perm _ _ ofs Hf');
          do 2 rewrite restrPermMap_Cur in Hstrong_perm;
            by assumption.
      + (* val proof *)
        intros b1 b2 ofs Hf' Hreadable.
        simpl.
        eapply Hval; eauto.
        unfold Mem.perm in *.
        assert (Hp2:= restrPermMap_Cur (Hcomp2 j pf2j) b1 ofs).
        assert (Hp1:= restrPermMap_Cur (Hcomp1 j pf1j) b1 ofs).
        unfold permission_at in *.
        rewrite Hp2 in Hreadable.
        rewrite Hp1.
          by rewrite gThreadCR in Hreadable.
    - (*case it's a start step*)      
      subst m2.
      inversion Hsim as [Hcode_eq Hmem_obs_eq].
      inversion Hstart; subst.
      pf_cleanup.
      rewrite Hcode in Hcode_eq.
      simpl in Hcode_eq.
      destruct (getThreadC pf1j') as [| | |vf' arg'] eqn:Hcode'; try by exfalso.
      destruct Hcode_eq as [Hvf Harg_obs]; subst vf'.
      assert (Harg_obs_list: val_obs_list f [:: arg] [:: arg'])
        by (constructor; auto; constructor).
      assert (HinitF := core_inj_init _ Harg_obs_list Hinitial).
      destruct HinitF as [c_newF [HinitialF Hcode_eq]].
      exists (updThreadC pf1j' (Krun c_newF)), m1', f.
      assert (Hinternal':
                internal_step pf1j' Hcomp1' (updThreadC pf1j' (Krun c_newF)) m1')
        by ( clear - Hcode' Hinv HinitialF;
             right; right; split; econstructor; eauto).
      split;
        first by assumption.
      split; first by auto.
      split; first by congruence.
      split; first by congruence.
      split; first by auto.
      split; first by
          (intros; by exfalso).
      split; try by eauto.
      assert (pf2j := containsThread_internal_step Hstep pf1j).
      assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
      assert (Hcomp2 := internal_step_compatible Hstep).
      assert (Hcomp2' := internal_step_compatible Hinternal').
      exists pf2j, pf2j', Hcomp2, Hcomp2'.
      constructor; first by do 2 rewrite gssThreadCC.
      destruct Hmem_obs_eq
        as [[Hinvalid' Hvalid' Hcodomain Hinjective Hweak_perm]
              [Hstrong_perm Hval]].
      constructor.
      + (*weak_mem_obs_eq proof*)
        constructor.
        * intros b Hinvalid;
          erewrite restrPermMap_valid in Hinvalid;
            by eauto. 
        * intros b Hvalid;
          erewrite restrPermMap_valid in Hvalid;
            by eauto.
        * by eauto.
        * by eauto.
        * intros b1 b2 ofs Hf'. 
          do 2 rewrite restrPermMap_Cur;
            do 2 rewrite gThreadCR.
          specialize (Hweak_perm _ _ ofs Hf').
          do 2 rewrite restrPermMap_Cur in Hweak_perm.
            by assumption.
      + (* strong_perm proof *)
        constructor.
        intros b1 b2 ofs Hf'.
        do 2 rewrite restrPermMap_Cur;
          do 2 rewrite gThreadCR;
          specialize (Hstrong_perm _ _ ofs Hf');
          do 2 rewrite restrPermMap_Cur in Hstrong_perm;
            by assumption.
      + (* val proof *)
        intros b1 b2 ofs Hf' Hreadable.
        simpl.
        eapply Hval; eauto.
        unfold Mem.perm in *.
        assert (Hp2:= restrPermMap_Cur (Hcomp2 j pf2j) b1 ofs).
        assert (Hp1:= restrPermMap_Cur (Hcomp1 j pf1j) b1 ofs).
        unfold permission_at in *.
        rewrite Hp2 in Hreadable.
        rewrite Hp1.
          by rewrite gThreadCR in Hreadable.
  Qed.

  Lemma strong_tsim_execution:
    forall tp1 tp2 tp1' m1 m2 m1' j xs f
      (pf1j: containsThread tp1 j)
      (pf1j': containsThread tp1' j)
      (Hcomp1: mem_compatible tp1 m1)
      (Hcomp1': mem_compatible tp1' m1')
      (Hinv: invariant tp1')
      (Hsim: strong_tsim f pf1j pf1j' Hcomp1 Hcomp1')
      (Hexec: internal_execution [seq x <- xs | x == j] tp1 m1 tp2 m2),
    exists tp2' m2' f',
      internal_execution [seq x <- xs | x == j] tp1' m1' tp2' m2' /\
      ren_incr f f' /\
      ren_separated f f' m1 m1' /\
      (forall b1 b1' b2,
          f b1 = None ->
          f b1' = None ->
          f' b1 = Some b2 ->
          f' b1' = Some b2 ->
          b1 = b1') /\
      ((exists p, ((Mem.nextblock m2 = Mem.nextblock m1 + p)%positive /\
              (Mem.nextblock m2' = Mem.nextblock m1' + p)%positive))
       \/ ((Mem.nextblock m2 = Mem.nextblock m1) /\
          (Mem.nextblock m2' = Mem.nextblock m1'))) /\
      (forall b,
          Mem.valid_block m2' b ->
          ~ Mem.valid_block m1' b ->
          let bz := ((Zpos b) - ((Zpos (Mem.nextblock m1')) -
                                 (Zpos (Mem.nextblock m1))))%Z in
          f' (Z.to_pos bz) = Some b /\
          f (Z.to_pos bz) = None) /\
      (exists (pf2j: containsThread tp2 j)
         (pf2j': containsThread tp2' j)
         (Hcomp2: mem_compatible tp2 m2)
         (Hcomp2': mem_compatible tp2' m2'),
          strong_tsim f' pf2j pf2j' Hcomp2 Hcomp2') /\
      (Mem.nextblock m1 = Mem.nextblock m1' ->
       (forall b1 b2 : block, f b1 = Some b2 -> b1 = b2) ->
       forall b1 b2 : block, f' b1 = Some b2 -> b1 = b2).
  Proof.
    intros.
    generalize dependent tp1.
    generalize dependent m1.
    generalize dependent f.
    generalize dependent tp1'. generalize dependent m1'.
    induction xs as [|x xs]; simpl; intros.
    - inversion Hexec; subst.
      exists tp1', m1', f.
      split; first by constructor.
      split; first by auto.
      split; first by congruence.
      split; first by congruence.
      split; first by auto.
      split; first by (intros; by exfalso).
      split; by eauto.
      simpl in HschedN;
        by inversion HschedN.
    - destruct (x == j) eqn:Hxj; move/eqP:Hxj=>Hxj.
      + subst x. inversion Hexec as [|tid U U' tp1a m1a tp0 m0].
        subst U U' tp1a m1a tp'' m''.
        simpl in Htrans. simpl in HschedN;
          inversion HschedN; subst tid; clear HschedN Hexec.
        pf_cleanup.
        assert (Htsim := strong_tsim_step Hinv Hsim Hstep).
        destruct Htsim as
            (tp0' & m0' & f0 & Hstep0' & Hincr0' & Hsep0' & Hinjective0'
             & Hnextblock0' & Hinverse0' & Htsim0' & Hid0').
        destruct Htsim0' as [pfj' [pfj0' [Hcomp' [Hcomp0' Htsim0]]]].
        pf_cleanup.
        assert (Hinv0': invariant tp0')
          by (eapply internal_step_invariant; eauto).
        destruct (IHxs _ _ _ _ Hinv0' _ _ _ _ _ Htsim0 Htrans)
          as (tp2' & m2' & f2' & Hexec & Hincr2 & Hsep2 & Hinjective2
             & Hnextblock2 & Hinverse2 & Hsim2 & Hid2);
          exists tp2', m2', f2'.
        destruct Hsim2 as [pf2j [pf2j' [Hcomp2 [Hcomp2' Htsim2]]]].
        split; first by (econstructor; simpl; eauto).
        split; first by (eapply ren_incr_trans; eauto).
        split.
        { (*injection separated *)
          intros b1 b2 Hf Hf2'.
          unfold ren_separated in *.
          destruct (valid_block_dec m0 b1) as [Hvalidm0 | Hinvalidm0].
          * apply (domain_valid (weak_obs_eq (obs_eq Htsim0))) in Hvalidm0.
            destruct Hvalidm0 as [x Hf0].
            assert (b2 = x).
            {  assert (Hf2'' : f2' b1 = Some x)
                by (eapply Hincr2; eauto).
               rewrite Hf2' in Hf2''. inversion Hf2''; by subst. }
            subst x.
            eapply Hsep0';
              by eauto.
          * apply (domain_invalid (weak_obs_eq (obs_eq Htsim0))) in Hinvalidm0.
            destruct (Hsep2 _ _ Hinvalidm0 Hf2') as [Hinvalid Hinvalidm0'].
            split;
              intros Hcontra;
              eapply internal_step_valid in Hcontra; eauto.
        }
        split.
        { (* injectivity for new blocks *)
          intros b1 b1' b2 Hf Hf' Hf2 Hf2'.
          destruct (valid_block_dec m0 b1) as [Hvalidm0 | Hinvalidm0];
            destruct (valid_block_dec m0 b1') as [Hvalidm0' | Hinvalidm0'].
          - apply (domain_valid (weak_obs_eq (obs_eq Htsim0))) in Hvalidm0.
            destruct Hvalidm0 as [b2' Hf0].
            apply (domain_valid (weak_obs_eq (obs_eq Htsim0))) in Hvalidm0'.
            destruct Hvalidm0' as [b2'' Hf0'].
            assert (Heq: b2 = b2' /\ b2' = b2'').
            { apply Hincr2 in Hf0'.
              apply Hincr2 in Hf0. rewrite Hf0 in Hf2.
              rewrite Hf0' in Hf2'. inversion Hf2; inversion Hf2'; by subst. }
            destruct Heq; subst b2' b2''.
            eapply Hinjective0'; eauto.
          - (* Proof: b1 is valid in m0. By codomain_valid b2 must
                 be valid in m0'. b1' is invalid in m0 and valid in
                 m2.  by seperation any block that it maps is invalid
                 in m0' and valid only in m2'.  Hence we derive a
                 contradiction on Mem.valid_block m2' b2 *)
            
            apply (domain_valid (weak_obs_eq (obs_eq Htsim0))) in Hvalidm0.
            destruct Hvalidm0 as [b2' Hf0].
            apply (domain_invalid (weak_obs_eq (obs_eq Htsim0))) in Hinvalidm0'.
            unfold inject_separated in Hsep2.
            specialize (Hsep2 _ _ Hinvalidm0' Hf2').
            destruct Hsep2 as [? Hinvalidb2].
            assert (b2 = b2')
              by (eapply Hincr2 in Hf0; rewrite Hf0 in Hf2; inversion Hf2; by subst);
              subst b2'.
            apply (codomain_valid (weak_obs_eq (obs_eq Htsim0))) in Hf0.
            erewrite restrPermMap_valid in Hf0.
              by exfalso.
          - (* Proof: same as above with the roles of b1 and b1' exchanged *)
            apply (domain_valid (weak_obs_eq (obs_eq Htsim0))) in Hvalidm0'.
            destruct Hvalidm0' as [b2' Hf0].
            apply (domain_invalid (weak_obs_eq (obs_eq Htsim0))) in Hinvalidm0.
            unfold inject_separated in Hsep2.
            specialize (Hsep2 _ _ Hinvalidm0 Hf2).
            destruct Hsep2 as [? Hinvalidb2].
            assert (b2 = b2')
              by (eapply Hincr2 in Hf0; rewrite Hf0 in Hf2'; inversion Hf2';
                    by subst);
              subst b2'.
            apply (codomain_valid (weak_obs_eq (obs_eq Htsim0))) in Hf0.
            erewrite restrPermMap_valid in Hf0.
              by exfalso.
          - (* Proof: both b1 and b1' are not valid in m0, hence they are only
                  valid in m2, for which we have injectivity by induction hypothesis *)
            apply (domain_invalid (weak_obs_eq (obs_eq Htsim0))) in Hinvalidm0.
            apply (domain_invalid (weak_obs_eq (obs_eq Htsim0))) in Hinvalidm0'.
              by eauto.
        } split.
        { (*Nextblock*)
          destruct Hnextblock0' as [[p0 [Hnextblock0 Hnextblock0']]
                                   | [Hnextblock0 Hnextblock0']];
          destruct Hnextblock2 as [[p2 [Hnextblock2 Hnextblock2']]
                                  | [Hnextblock2 Hnextblock2']];
          clear - Hnextblock0 Hnextblock0' Hnextblock2 Hnextblock2';
          rewrite Hnextblock2 Hnextblock2';
          rewrite Hnextblock0 Hnextblock0'.
          - left. exists (p0+p2)%positive.
            split; by rewrite Pos.add_assoc.
          - left;
            exists p0; by split.
          - left; exists p2;
              by split.
          - right; by split.
        } split.
        { (*inverse, TODO: sketch proof *)
          clear - Hinverse2 Hinverse0' Hincr2 Hincr0' Hnextblock0' Hnextblock2.
          intros b Hvalidm2' Hinvalidm1'.
          destruct (valid_block_dec m0' b) as [Hvalidm0' | Hinvalidm0'].
          - specialize (Hinverse0' _ Hvalidm0' Hinvalidm1').
            simpl in Hinverse0'.
            destruct Hinverse0' as [Hf0 Hf].
            apply Hincr2 in Hf0. by split.
          - specialize (Hinverse2 _ Hvalidm2' Hinvalidm0').
            simpl in Hinverse2.
            destruct Hinverse2 as [Hf2' Hf0].
            (* NOTE: axiom on nextblock is used for the difference here*)
            assert (Heq: ((Z.pos (Mem.nextblock m1') - Z.pos (Mem.nextblock m1)) =
                          Z.pos (Mem.nextblock m0') - Z.pos(Mem.nextblock m0))%Z).
            { clear - Hnextblock0'.
              destruct Hnextblock0' as [[p0 [Hnextblock0 Hnextblock0']]
                                       | [Hnextblock0 Hnextblock0']];
                rewrite Hnextblock0 Hnextblock0';
                [do 2 rewrite Pos2Z.inj_add;
                  rewrite Zminus_plus_simpl_r;
                    by reflexivity | by reflexivity].
            }
            simpl in *.
            rewrite <- Heq in Hf2', Hf0.
            split; first by assumption.
            match goal with
            | [|- ?Expr = None] =>
              destruct Expr as [?|] eqn:Hf
            end;
              [apply Hincr0' in Hf; by congruence | trivial].
        }
        split; first by eauto.
        intros Hnb1 Hf.
        specialize (Hid0' Hnb1 Hf).
        assert (Hnb0: Mem.nextblock m0 = Mem.nextblock m0')
          by (destruct Hnextblock0' as [[p [Hnb0 Hnb0']] | [Hnb0 Hnb0']];
                by rewrite Hnb0 Hnb0' Hnb1).
        specialize (Hid2 Hnb0 Hid0').
          by assumption.
    - destruct (IHxs _ _ _ _ Hinv _ _ _ _ _ Hsim Hexec)
        as
          [tp2' [m2' [f2' [Hexec2
                             [Hincr2
                                [Hsep2 [Hinjective2
                                          [Hnextblock2 [Hinverse2 [Hsim2 Hid2]]]]]]]]]];
      exists tp2', m2', f2'.
      repeat (split; auto).
  Qed.
  
  Lemma strong_tsim_stop:
    forall tpc tpc' tpf mc mc' mf i fi
      (pfc: containsThread tpc i) (pff: containsThread tpf i)
      (Hcompc: mem_compatible tpc mc) (Hcompf: mem_compatible tpf mf)
      (HinvF: invariant tpf)
      (Hstrong_sim: strong_tsim fi pfc pff Hcompc Hcompf)
      (Hstep: cmachine_step (buildSched [:: i], tpc) mc (empty, tpc') mc')
      (Hsuspend: pfc @ S),
    exists tpf',
      myFineSemantics.suspend_thread pff tpf' /\
      forall (Hcompc': mem_compatible tpc' mc') (Hcompf' : mem_compatible tpf' mf)
        (pfc': containsThread tpc' i) (pff': containsThread tpf' i),
        strong_tsim fi pfc' pff' Hcompc' Hcompf'.
  Proof.
    intros.
    inversion Hstep; simpl in *; subst; inversion HschedN; subst;
    try (inversion Htstep || inversion Hhalted); subst; pf_cleanup;
    unfold getStepType in Hsuspend;
    try rewrite Hcode in Hsuspend; simpl in Hsuspend;
    try match goal with
        | [H: match ?Expr with _ => _ end = _, H2: ?Expr = _ |- _] =>
          rewrite H2 in H
        end; try discriminate;
    try match goal with
        | [H: ~ containsThread _ _, H2: containsThread _ _ |- _] =>
          exfalso; by auto
        | [H: is_true (isSome (@halted _ _ _ _ _))  |- _] => 
          destruct (at_external_halted_excl Sem c) as [Hnot_ext | Hcontra];
            [rewrite Hnot_ext in Hsuspend;
              destruct (halted Sem c); discriminate |
             rewrite Hcontra in Hcant; by auto]
        end.
    destruct Hstrong_sim as [Hcode_eq memObsEq].
    rewrite Hcode in Hcode_eq.
    simpl in Hcode_eq.
    destruct (getThreadC pff) as [c'| | |] eqn:Hcode';
      try by exfalso.
    assert (Hat_external_spec := core_inj_ext _ _ _ Hcode_eq).
    rewrite Hat_external in Hat_external_spec.
    destruct X as [[? ?] ?].
    destruct (at_external Sem c') as [[[? ?] ?]|] eqn:Hat_external';
      try by exfalso.
    destruct Hat_external_spec as [? [? ?]]; subst.
    exists (updThreadC pff (Kblocked c')).
    split; first by (econstructor; eauto).
    intros.
    constructor;
      first by do 2 rewrite gssThreadCC.
    erewrite restrPermMap_irr with
    (Hlt := Hcompc' tid pfc') (Hlt' := Hcmpt tid Htid)
      by (erewrite gThreadCR with (cntj := Htid); reflexivity).
    erewrite restrPermMap_irr with
    (Hlt := Hcompf' tid pff') (Hlt' := Hcompf tid pff)
      by (erewrite gThreadCR with (cntj := pff); reflexivity).
    assumption.
  Qed.

  (** ** Results about id injections*)
  Definition id_ren m :=
    fun b => if is_left (valid_block_dec m b) then Some b else None.

  Hint Unfold id_ren.

  Lemma id_ren_correct:
    forall m (b1 b2 : block), (id_ren m) b1 = Some b2 -> b1 = b2.
  Proof.
    intros. unfold id_ren in *.
    destruct (valid_block_dec m b1); simpl in *;
      by inversion H.
  Qed.

  Lemma id_ren_domain:
    forall m, domain_memren (id_ren m) m.
  Proof.
    unfold id_ren, domain_memren.
    intros.
    destruct (valid_block_dec m b); simpl;
    split; intuition.
  Qed.

  Lemma id_ren_validblock:
    forall m b
      (Hvalid: Mem.valid_block m b),
      id_ren m b = Some b.
  Proof.
    intros.
    eapply id_ren_domain in Hvalid.
    destruct (id_ren m b) eqn:Hid.
    apply id_ren_correct in Hid;
      by subst.
      by exfalso.
  Qed.

  Lemma id_ren_invalidblock:
    forall m b
      (Hinvalid: ~ Mem.valid_block m b),
      id_ren m b = None.
  Proof.
    intros.
    assert (Hnot:= iffLRn (id_ren_domain m b) Hinvalid).
    destruct (id_ren m b) eqn:Hid;
      first by exfalso.
      by reflexivity.
  Qed.

  Lemma is_id_ren :
    forall f m
      (Hdomain: domain_memren f m)
      (Hf_id: forall b1 b2, f b1 = Some b2 -> b1 = b2),
      f = id_ren m.
  Proof.
    intros. extensionality b.
    assert (Hdomain_id := id_ren_domain m).
    destruct (f b) eqn:Hf, (id_ren m b) eqn:Hid;
      try (assert (H:= id_ren_correct _ _ Hid));
      try (specialize (Hf_id b _ Hf));
      subst; auto.
    assert (Hid': ~ id_ren m b0)
      by (rewrite Hid; auto).
    assert (Hf': f b0)
      by (rewrite Hf; auto).
    apply (proj2 (Hdomain b0)) in Hf'.
    apply (iffRLn (Hdomain_id b0)) in Hid';
      by exfalso.
    assert (Hid': id_ren m b0)
      by (rewrite Hid; auto).
    assert (Hf': ~ f b0)
      by (rewrite Hf; auto).
    apply (proj2 (Hdomain_id b0)) in Hid'.
    apply (iffRLn (Hdomain b0)) in Hf';
      by exfalso.
  Qed.
  
  Lemma ctl_inj_id:
    forall f c,
      ctl_wd f c ->
      (forall b1 b2, f b1 = Some b2 -> b1 = b2) ->
      ctl_inj f c c.
  Proof.
    intros.
    destruct c; simpl in *;
    repeat match goal with
           |[H: _ /\ _ |- _] =>
            destruct H
           |[|- _ /\ _] => split; auto
           |[|- core_inj _ _ _] =>
            eapply core_inj_id; eauto
           |[|- val_obs _ _ _] =>
            eapply val_obs_id; eauto
           end.
  Qed.
  
  (** Stepping on thread i with internal steps and then a suspend step
  retains a strong simulation with the id injeciton on all other
  threads*)
  Lemma strong_tsim_id :
    forall tp tp' tp'' m m' i j xs f
      (Hij: i <> j)
      (pfj: containsThread tp j)
      (pfj': containsThread tp' j)
      (pfj'': containsThread tp'' j)
      (pfi': containsThread tp' i)
      (Hmem_wd: valid_mem m)
      (Hdomain: domain_memren f m)
      (Htp_wd: tp_wd f tp)
      (Hge_wd: ge_wd f the_ge)
      (Hcomp: mem_compatible tp m)
      (Hcomp'': mem_compatible tp'' m')
      (Hsuspend: myCoarseSemantics.suspend_thread pfi' tp'')
      (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m'),
      strong_tsim (id_ren m)
                  pfj pfj'' Hcomp Hcomp''.
  Proof.
    intros.
    assert (Hdomain_id: domain_memren (id_ren m) m)
      by (apply id_ren_domain).
    assert (Htp_wd_id: tp_wd (id_ren m) tp)
      by (eapply tp_wd_domain; eauto).
    assert (Hid := id_ren_correct m).
    constructor.
    - (* cores are related*)
      assert (Hcore := gsoThreadC_suspendC pfj' pfj'' Hij Hsuspend).
      rewrite <- Hcore.
      erewrite <- gsoThreadC_exec with (pfj := pfj) (pfj' := pfj'); eauto.
      specialize (Htp_wd_id _ pfj).
      eapply ctl_inj_id;
        by eauto.
    - (* mem_obs_eq *)
      constructor.
      + (*weak_mem_obs_eq*)
        constructor.
        * (*invalid domain of fid*)
          intros b Hinvalid.
          erewrite restrPermMap_valid in Hinvalid.
          specialize (Hdomain_id b).
          apply iffLRn in Hdomain_id; auto.
          destruct (id_ren m b);
            [by exfalso | by reflexivity].
        * (*valid domain of fid*)
          intros b Hvalid.
          erewrite restrPermMap_valid in Hvalid.
          apply Hdomain_id in Hvalid.
          destruct (id_ren m b);
            [eexists; eauto | by exfalso].
        * (*codomain of fid *)
          intros b1 b2 Hfid.
          assert (Hfid0: id_ren m b1)
            by (by rewrite Hfid).
          apply Hdomain_id in Hfid0.
          erewrite restrPermMap_valid.
          apply id_ren_correct in Hfid; subst.
          eapply internal_execution_valid;
            by eauto.
        * (*fid is injective*)
          intros b1 b1' b2 Hfb1 Hfb1'.
          apply id_ren_correct in Hfb1.
          apply id_ren_correct in Hfb1';
            by subst.
        * (* Permissions of memc are higher than memc''*)
          intros b1 b2 ofs Hfid.
          apply id_ren_correct in Hfid; subst b2.
          do 2 rewrite restrPermMap_Cur.
          erewrite <- gsoThreadR_suspendC with
          (cntj' := pfj'') (cntj := pfj') by eauto.
          erewrite <- gsoThreadR_execution with (pfj' := pfj')
                                                 (pfj := pfj); eauto.
          destruct ((getThreadR pfj) # b1 ofs); simpl;
            by constructor.
      + constructor.
        (* Permissions of memc'' are higher than mc*)
        intros b1 b2 ofs Hfid.
        apply id_ren_correct in Hfid; subst b2.
        do 2 rewrite restrPermMap_Cur.
        erewrite <- gsoThreadR_suspendC with
        (cntj' := pfj'') (cntj := pfj') by eauto.
        erewrite <- gsoThreadR_execution with (pfj' := pfj')
                                               (pfj := pfj); eauto.
        (* j-Values of mc and mc'' are equal up to injection*)
        intros b1 b2 ofs Hfid Hreadable.
        assert (Hvalid: Mem.valid_block m b1)
          by (eapply Hdomain_id; by rewrite Hfid).
        apply id_ren_correct in Hfid; subst b2.
        simpl.
        erewrite <- internal_exec_disjoint_val
        with (tp := tp) (xs := xs) (tp' := tp') (m' := m'); eauto.
        destruct (Maps.ZMap.get ofs (Mem.mem_contents m) # b1) eqn:Hget;
          constructor.
        specialize (Hmem_wd _ Hvalid _ _ Hget).
        simpl in Hmem_wd.
        eapply val_obs_id; eauto.
        eapply wd_val_valid;
          by eauto.
          by eapply containsThread_internal_execution'; eauto.
  Qed.
  
  Lemma sim_suspend : sim_suspend_def.
  Proof.
    unfold sim_suspend_def.
    intros.
    inversion Hsim as
        [HnumThreads HmemCompC HmemCompF HsafeC HsimWeak Hfpsep
                     HsimStrong HsimLocks HsimRes HinvF HmaxF Hwd_mem Htp_wd Hge_wd].
    assert (pfc: containsThread tpc i)
      by (eapply HnumThreads; eauto).
    destruct (HsimStrong i pfc pff)
      as (tpc' & mc' & Hincr & Hsynced & Hexec & Htsim & Hownedi
          & Hownedi_ls & Hownedi_lp);
      clear HsimStrong.
    assert (pfc': containsThread tpc' i)
      by (clear - Hexec pfc; eapply containsThread_internal_execution in pfc;
          eauto).
    specialize (Htsim pfc').
    specialize (HsafeC (mySchedule.buildSched (i ::  nil))
                       ((size ([seq x <- xs | x == i])).+1)).
    rewrite <- addn1 in HsafeC.
    assert (HcoreN := safeN_corestepN_internal xs _ nil 1 HsafeC Hexec).
    destruct HcoreN as [HcorestepN HsafeN].
    unfold safeN in HsafeN; simpl in *.
    destruct HsafeN as [[[U tpc''] [mc'' Hstep']] _].
    assert (HinvC: invariant tpc)
      by (eapply cmachine_step_invariant; eauto).
    assert (memCompC' := internal_execution_compatible HmemCompC Hexec).
    specialize (Htsim memCompC').
    assert (Hstop_pfc': pfc' @ S)
      by (by erewrite (stepType_inj _ _ _ (code_eq Htsim))).
    (* A suspend step pops the schedule and does not touch the memory *)
    assert (Heq : empty = U /\ mc' = mc'' /\ mem_compatible tpc' mc' /\
                  myCoarseSemantics.suspend_thread pfc' tpc'')
      by (eapply suspend_step_inverse; eauto).
    destruct Heq as [? [? [Hcomp' HsuspendC]]]; subst mc' U.
    assert (memCompC'': mem_compatible tpc'' mc'')
      by (eapply suspendC_compatible; eauto).
    assert (HstepF := strong_tsim_stop HinvF Htsim Hstep' Hstop_pfc').
    destruct HstepF as [tpf' [HstepF Htsim']].
    assert (memCompF': mem_compatible tpf' mf)
      by (eapply suspendF_compatible; eauto).
    exists tpc'', mc'', tpf', mf.
    (* since thread i commits, the new global renaming will be fi *)
    exists (fp i pfc).
    assert (pfci': containsThread tpc' i)
      by (eapply containsThread_internal_execution; eauto).
    assert (pfci'': containsThread tpc'' i)
      by (eapply suspendC_containsThread with (tp := tpc'); eauto).
    (* and we need to shift all other mappings..*)
    exists (fun j (cntj'': containsThread tpc'' j) =>
         let cntj := (containsThread_internal_execution'
                        Hexec ((proj2 (suspendC_containsThread j HsuspendC)) cntj'')) in
         if i == j then
           fp i pfc else
           fun b1 =>
             match valid_block_dec mc b1 with
             | in_left => f b1
             | in_right =>
               match valid_block_dec mc'' b1 with
               | in_left => (fp i pfc) b1
               | in_right =>
                 let bz :=
                     (Z.pos b1 - (Z.pos (Mem.nextblock mc'') -
                                  Z.pos (Mem.nextblock mc)))%Z in
                 (fp j cntj) (Z.to_pos bz)
               end
             end).
    split.
    { (* the fine-grained machine takes a suspend step *)
      intros U; eapply myFineSemantics.suspend_step; simpl; eauto.
    }
    { (* The simulation between tpc'' and tpf' is retained. *)
      (* We prove first that well-definedeness of the components of
      the state is also preserved. We only prove it here to avoid
      duplicated work when we re-establish these invariants *)
      assert (Hdomainf: domain_memren f mc)
        by (specialize (HsimWeak _ pfc pff);
             eapply weak_obs_eq_domain_ren in HsimWeak; eauto).
      assert (Hwd := internal_execution_wd _ _ Hdomainf Hwd_mem Htp_wd Hge_wd Hexec).
      destruct Hwd as [Hwd_mem' [[f' [Hincrf' Hdomainf']] Htp_wd']].
      assert (pffi': containsThread tpf' i)
        by (eapply suspendF_containsThread with (cnti := pff); eauto).
      specialize (Htsim' memCompC'' memCompF' pfci'' pffi').
      assert (Hdomain_fi: domain_memren (fp i pfc) mc'')
        by (eapply (mem_obs_eq_domain_ren (obs_eq Htsim')); eauto).
      specialize (Htp_wd' _ Hdomain_fi).
      eapply Build_sim with (mem_compc := memCompC'') (mem_compf := memCompF').
      { (* number of threads *)
        clear - HnumThreads Hexec HsuspendC HstepF.
        intros j. assert (Hpffj := suspendF_containsThread j HstepF).
        assert (Hpfcj' := suspendC_containsThread j HsuspendC).
        split; intros;
        [apply Hpffj; apply HnumThreads;
         destruct Hpfcj'; eapply containsThread_internal_execution'; eauto
        |  apply Hpfcj';
          destruct Hpffj;
          eapply containsThread_internal_execution; eauto;
          destruct (HnumThreads j); by auto].            
      }
      { (* safety of coarse state *)
        intros U n.
        assert (Hsafe_tpc := safeCoarse Hsim).
        specialize (Hsafe_tpc (buildSched (i :: U))
                              (size [seq x <- xs | x == i] + (1 + n))).
        assert (HcoreN := safeN_corestepN_internal xs _ U _ Hsafe_tpc Hexec).
        destruct HcoreN as [HcorestepN_tpc HsafeN_tpc'].
        simpl in HsafeN_tpc'.
        destruct HsafeN_tpc' as [[[U' tpc''0] [mc''0 Hstep'0]] Hsafe].

        destruct (suspend_step_inverse pfc' Hstop_pfc' Hstep'0)
          as [? [? [_ Hsuspend]]]; subst U' mc''0.
        assert (tpc''0 = tpc'')
          by (eapply suspendC_step_det; eauto);
          subst tpc''0.
          by eauto.
      }
      { (* Proof of weak simulation between the threadpools and memories *)
        clear HsafeC. pf_cleanup.
        intros j pfcj'' pffj'.
        constructor.
        { (* Outside the domain of fi *)
          apply (domain_invalid (weak_obs_eq (obs_eq Htsim))).
        }
        { (* Inside the domain of fi *)
          apply (domain_valid (weak_obs_eq (obs_eq Htsim))).
        }
        { (* Valid codomain*)
          apply (codomain_valid (weak_obs_eq (obs_eq Htsim))).
        }
        { (* Injective fi*)
          apply (injective (weak_obs_eq (obs_eq Htsim))).
        }
        { (* Permissions of the coarse-state are higher than the fine-state *)
          (* Proof idea: for thread i, we have a strong simulation
            on internal steps and then a suspend step so it should be
            straightforward. For thread j: For blocks before
            (nextblock mc) from weak-sim and for blocks after
            (nextblock mc) this should be freeable on i and thus empty
            on j. Correction: This doesn't hold, because the new
            blocks may have been freed by some internal step. Hence we
            need some other way to capture that they belong to thread
            i and the other threads should have empty permission (a
            new invariant). In fact, this invariant should talk about
            the permissions at the fine-grained level as we no longer
            can use the non-interference invariant because the
            permissions of thread i are not necessary freeable.

            Deprecated and wrong: Morever, we have a strong simulation
            on thread i and a non-interference invariant, hence we can
            infer that the new locations will have empty permission on
            the fine-grained machine.  *)
          intros b1 b2 ofs Hfi.
          (* The permissions will be same as before taking the suspend step*)
          assert (pffj: containsThread tpf j)
            by (eapply suspendF_containsThread; eauto).
          assert (Hperm_eqF: permission_at (restrPermMap (memCompF' _ pffj'))
                                           b2 ofs Cur =
                             permission_at (restrPermMap (HmemCompF _ pffj))
                                           b2 ofs Cur)
            by (do 2 rewrite restrPermMap_Cur;
                 erewrite <- gsoThreadR_suspendF with (cntj := pffj); eauto).
          rewrite Hperm_eqF.

          (* Likewise for the coarse-grained machine*)
          assert (pfcj': containsThread tpc' j)
            by (eapply suspendC_containsThread; eauto).
          assert (Hperm_eqC: permission_at (restrPermMap (memCompC'' _ pfcj''))
                                           b1 ofs Cur =
                             permission_at (restrPermMap (memCompC' _ pfcj'))
                                           b1 ofs Cur)
            by (do 2 rewrite restrPermMap_Cur;
                 erewrite <- gsoThreadR_suspendC with (cntj := pfcj'); eauto).
          rewrite Hperm_eqC.
          clear Hperm_eqF Hperm_eqC HcorestepN HstepF Hstep'.
          destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
          { (* Case j = i *)
            subst.
            clear - Htsim Hfi.
            destruct Htsim as [_ Hstrong]; destruct Hstrong as [Hweak _ _];
            destruct Hweak as [_ _ _ _ Hperm_weak].
            specialize (Hperm_weak b1 b2 ofs Hfi).
              by pf_cleanup.
          }
          { (* Case j <> i *)
            assert (pfcj: containsThread tpc j)
              by (eapply containsThread_internal_execution'; eauto).
            specialize (HsimWeak _ pfcj pffj). 
            inversion HsimWeak as [Hinvdomain Hdomain Hcodomain Hinjective Hobs_weak].
            destruct (valid_block_dec mc b1) as [Hvalid_mc | Hinvalid_mc].
            - (* b1 is a block that's valid in mc, i.e. not allocated by i *)
              assert (Hvalid: Mem.valid_block (restrPermMap (HmemCompC _ pfcj)) b1)
                by (unfold Mem.valid_block in *;
                      by rewrite restrPermMap_nextblock).
              apply Hdomain in Hvalid.
              destruct Hvalid as [b2' Hf].
              assert (b2 = b2')
                by (apply Hincr in Hf; rewrite Hf in Hfi;
                    inversion Hfi; by subst); subst b2'.
              erewrite <- permission_at_execution with (i := i) (xs := xs) (tp := tpc);
                by eauto.
            - (* b1 is a block that's not valid in mc, i.e. allocated by i *)
              (* NOTE: here is the place where we use the invariant
                about blocks owned by i. The proof became much smaller
                (but the burden was moved elsewhere)*)
              apply Hinvdomain in Hinvalid_mc.
              specialize (Hownedi j pffj Hij _ _ ofs Hfi Hinvalid_mc).
              do 2 rewrite restrPermMap_Cur. rewrite Hownedi.
              destruct ((getThreadR pfcj') # b1 ofs); simpl;
                by auto.
          }
        }
      }
      { (* Proof of seperation*)
        intros k j cntk cntj Hkj b b' b2 b2' Hfi Hfi' Hfk Hfj.
        simpl in Hfk, Hfj.
        destruct (i == k) eqn:Hik; destruct (i == j) eqn: Hij;
        move/eqP:Hik=> Hik; move/eqP:Hij => Hij.
        - subst k j. by exfalso.
        - subst k.
            by congruence.
        - subst j.
            by congruence.
        - destruct (valid_block_dec mc b) as [Hvalidb | Hinvalidb];
          first by (apply Hincr in Hfk; by congruence).
          destruct (valid_block_dec mc'' b) as [Hvalidib | Hinvalidib];
            first by congruence.
          destruct (valid_block_dec mc b') as [Hvalidb' | Hinvalidb'];
            first by (apply Hincr in Hfj; by congruence).
          destruct (valid_block_dec mc'' b') as [Hvalidib' | Hinvalidib'];
            first by congruence.
          assert (Hle: (Mem.nextblock mc <= Mem.nextblock mc'')%positive)
            by admit.
          (*TODO: need nextblock instead of valid_block axioms*)
          specialize (HsimWeak _ pfc pff).
          apply Pos.lt_eq_cases in Hle.
          destruct Hle as [Hlt | Heq].
          + apply Pos.le_nlt in Hinvalidb.
            apply Pos.le_nlt in Hinvalidib.
            assert (Hinvalid:
                      (Mem.nextblock mc <=
                       Z.to_pos (Z.pos_sub b (Mem.nextblock mc'' -
                                              Mem.nextblock mc)))%positive)
              by (eapply le_sub; eauto).
            eapply Hfpsep with (i := k) (j := j); eauto.
            apply Pos.le_nlt in Hinvalid.
            apply (domain_invalid HsimWeak) in Hinvalid.
            rewrite Z.pos_sub_gt; auto.
            apply Pos.le_nlt in Hinvalidb'.
            apply Pos.le_nlt in Hinvalidib'.
            assert (Hinvalid':
                      (Mem.nextblock mc <=
                       Z.to_pos (Z.pos_sub b' (Mem.nextblock mc'' -
                                               Mem.nextblock mc)))%positive)
              by (eapply le_sub; eauto).
            apply Pos.le_nlt in Hinvalid'.
            apply (domain_invalid HsimWeak) in Hinvalid'.
            rewrite Z.pos_sub_gt; auto.
          + eapply Hfpsep with (i := k) (j := j); eauto; 
            rewrite Heq;
            rewrite Z.pos_sub_diag; simpl;
            [ by apply (domain_invalid HsimWeak) in Hinvalidb
            | by apply (domain_invalid HsimWeak) in Hinvalidb'].
      }  
      { (* Proof of strong simulation *)
        (* If thread i = thread j then it's straightforward. 
         * If thread i <> thread j then we need to shuffle things.
         * In particular we know that for some memory mcj s.t mc -->j mcj
         * we have a strong simulation with mf and we want to establish it for
         * mcj' s.t. mc -->i mci --> mcj'. 
         * Take as fj' = | b < nb mc => id | nb mc =< b < nb mci => fi 
         *               | nb mci =< b < nb mcj' => fj (g b)) where g is the inverse of
         * the f that storngly injects mcj to mcj'.
         * Note that: mc strongly injects in mci|j with id, hence mcj strongly injects
              into mcj' with an extension of the id injection (fij). *)

        intros j pfcj'' pffj'.
        case (i == j) eqn:Hij; move/eqP:Hij=>Hij.
        { subst j. exists tpc'', mc''. simpl.
          split;
            first by (apply ren_incr_refl).
          split; auto. split.
          assert (Hempty: [seq x <- [seq x <- xs | x != i] | x == i] = nil).
          { clear. induction xs as [|x xs]; first by reflexivity.
            simpl; destruct (x == i) eqn:Heq;
            simpl; first by assumption.
            erewrite if_false
              by (apply/eqP; intro Hcontra; subst;
                    by move/eqP:Heq=>Heq).
              by assumption.
          }
          rewrite Hempty;
            by constructor.
          split; first by (intros; pf_cleanup; auto).
          split; first by congruence.
          split; by congruence.
        }
        { (*case j <> i *)
          assert (pfc'j: containsThread tpc' j)
            by (eapply suspendC_containsThread with (cnti := pfc'); eauto).
          assert (pfcj: containsThread tpc j)
            by (eapply containsThread_internal_execution'; eauto).

          specialize (HsimWeak _ pfc pff).
          (*domain of f*)
          assert (Hdomain_f: domain_memren f mc)
            by (apply (weak_obs_eq_domain_ren HsimWeak)).
          (* domain of id renaming*)
          assert (Hdomain_id: domain_memren (id_ren mc) mc)
            by (apply id_ren_domain).
          (* the thread-pool is well-defined for id renaming*)
          assert (Htp_wd_id: tp_wd (id_ren mc) tpc)
            by (eapply tp_wd_domain; eauto).
          assert (Hge_wd_id: ge_wd (id_ren mc) the_ge)
            by (eapply ge_wd_domain; eauto).
          simpl.
          erewrite proof_irr
          with (a1 := (containsThread_internal_execution'
                         Hexec (proj2 (suspendC_containsThread j HsuspendC)
                                      pfcj'')))
                 (a2 := pfcj).
          
          (* The original <tpc, mc> strongly injects into <tpc'',mc''> where
               <tpc, mc> -->i <tpc', mc'> -->iS <tpc'',mc'>  with the id map*)
          assert (Hsim_c_ci: strong_tsim (id_ren mc)
                                         pfcj pfcj'' HmemCompC memCompC'')
            by (eapply strong_tsim_id with (f := id_ren mc) (pfi' := pfc'); eauto).
          assert (pffj: containsThread tpf j)
            by (eapply suspendF_containsThread; eauto).
          assert (Htsimj := (simStrong Hsim) j pfcj pffj).
          (* executing the internal steps for thread j gives us a strong 
           * simulation between the coarse and fine-grained states. *)
          destruct Htsimj as
              (tpcj & mcj & Hincrj & Hsyncedj & Hexecj & Htsimj
               & Hownedj & Hownedj_ls & Hownedj_lp).
          (* by the strong simulation on mc and mc'' (via id) we can
              obtain a strong simulation between mcj and mcj', where
              mcj' mc -->i --> mci -->j mcj' *)
          assert (Hinv'': invariant tpc'')
            by (eapply suspendC_invariant with (tp := tpc');
                 [eapply internal_execution_invariant with (tp := tpc);
                   eauto | eauto]).
          assert (Hsimjj':= strong_tsim_execution xs Hinv'' Hsim_c_ci Hexecj).
          destruct Hsimjj'
            as (tpcj' & mcj' & fij & Hexecij
                & Hincr' & Hsep & Hinjective & Hnextblockj' & Hinverse & Hsimjj').
          destruct Hsimjj' as [[pfcjj [pfij [Hcompjj [Hcompij Hsimij]]]] Hid_case].
          pf_cleanup.
          (* notice that mcj and mcj' will be equal up to nextblock mc
           * (mcj injects to mcj' with id up to nextblock mc). Hence
           * for blocks smaller than nb mc we follow the fj injection to mf
           * for blocks between nb mc and nb mc'' we follow the fi injection
           * and for blocks after that we follow the fj one after taking
           * the inverse. (TODO: point to a diagram) *)
          (*TODO: comment deprecated*)
          specialize (Htsimj pfcjj Hcompjj).
          exists tpcj', mcj'.

          (* Notice also that the nextblock of mc will be
                smaller or equal to that of mc''*)
          assert (Hle_nextblock: (Mem.nextblock mc <= Mem.nextblock mc'')%positive)
            by admit.

          (* Moreover we prove that for all blocks b1 if the
                inverse of b1 is mapped by fpj and b1 is not valid in
                mc and mc'' then it is is valid in mcj'*)
          (* TODO: make this a separate lemma*)
          assert (Hvalidmcj':
                    forall b1 b2 (pf: containsThread tpc j),
                      ~ Mem.valid_block mc b1 ->
                      ~ Mem.valid_block mc'' b1 ->
                      fp j pf
                         (Z.to_pos ((Z.pos b1 -
                                     (Z.pos (Mem.nextblock mc'') -
                                      Z.pos (Mem.nextblock mc)))%Z)) = Some b2 ->
                      Mem.valid_block mcj' b1).
          { (*NOTE: this is a somewhat tedious proof,
                      probably because the definitions are weak in
                      some sense. It's still doable, so I'll go ahead
                      but maybe at some point we should reconsider the
                      relations*)
            (*Proof sketch: We prove that if b1 >= nb mcj'
                        then (b1 - (nb mcj' - nb mcj)) >= nb mcj
                        hence, it's invalid in mcj and we derive a
                        contradiction by the fact that it's mapped by
                        fpj. *)
            intros b1 b2 pf Hinvalidmc Hinvalidmc'' Hf'.
            destruct (valid_block_dec mcj' b1) as [? | Hinvalidmcj'];
              first by assumption.
            exfalso.
            clear - Hnextblockj' Hinvalidmc Hinvalidmc''
                                 Hf' Hinvalidmcj' Htsimj Hle_nextblock.
            pf_cleanup.
            apply Pos.le_lteq in Hle_nextblock.
            destruct Hle_nextblock as [Hlt | Hnbeq].
            - (*TODO: factor this out as a lemma*)
              assert (Hnblocks:
                        (Z.pos (Mem.nextblock mc'') + Z.neg (Mem.nextblock mc) =
                         Z.pos (Mem.nextblock mcj') + Z.neg (Mem.nextblock mcj))%Z).
              { clear -Hnextblockj'.
                destruct Hnextblockj' as [[p [Hmcj Hmcj']]|[Hmcj Hmcj']];
                  rewrite Hmcj Hmcj'; try reflexivity.
                replace (Z.neg (Mem.nextblock mc + p)) with
                (Z.opp (Z.pos (Mem.nextblock mc + p))%Z)
                  by (by rewrite Pos2Z.opp_pos).
                rewrite Z.add_opp_r.
                do 2 rewrite Pos2Z.inj_add.
                rewrite Zminus_plus_simpl_r.
                  by reflexivity.
              }
              simpl in Hf'.
              rewrite <- Pos2Z.add_pos_neg in Hf'.
              rewrite Hnblocks in Hf'. simpl in Hf'.
              assert (Hnb': (Mem.nextblock mcj < Mem.nextblock mcj')%positive).
              { simpl in Hnblocks.
                rewrite Z.pos_sub_gt in Hnblocks; auto.
                destruct (Coqlib.plt (Mem.nextblock mcj) (Mem.nextblock mcj'))
                  as [? | Hcontra];
                  first by assumption.
                unfold Coqlib.Plt in Hcontra.
                apply Pos.le_nlt in Hcontra.
                apply Pos.le_lteq in Hcontra.
                exfalso.
                destruct Hcontra as [Hcontra | Hcontra].
                rewrite Z.pos_sub_lt in Hnblocks; auto.
                  by congruence.
                  rewrite Hcontra in Hnblocks.
                  rewrite Z.pos_sub_diag in Hnblocks.
                  assert (H:= Pos2Z.is_pos (Mem.nextblock mc'' - Mem.nextblock mc)).
                  rewrite Hnblocks in H.
                    by apply Z.lt_irrefl with (x :=0%Z).
              }
              rewrite Z.pos_sub_gt in Hf'; auto.
              simpl in Hf'.        
              apply Pos.le_nlt in Hinvalidmcj'.
              assert (Hinvalid: (Mem.nextblock mcj
                                 <=
                                 Z.to_pos (Z.pos_sub b1 (Mem.nextblock mcj'
                                                         - Mem.nextblock mcj)))%positive)
                by (eapply le_sub; eauto).
              apply Pos.le_nlt in Hinvalid.
              apply (domain_invalid (weak_obs_eq (obs_eq Htsimj))) in Hinvalid.
                by congruence.
            - rewrite Hnbeq in Hf'.
              simpl in Hf'.
              rewrite Z.pos_sub_diag in Hf'.
              simpl in Hf'.
              destruct Hnextblockj' as [[p [Hmcj Hmcj']] | [Hmcj Hmcj']].
              + rewrite Hnbeq in Hmcj.
                rewrite <- Hmcj' in Hmcj.
                assert (Hcontra: ~ Mem.valid_block mcj b1)
                  by (unfold Mem.valid_block in *; rewrite Hmcj; auto).
                apply (domain_invalid (weak_obs_eq (obs_eq Htsimj))) in Hcontra.
                  by congruence.
              + assert (Hcontra: ~ Mem.valid_block mcj b1)
                  by (unfold Mem.valid_block in *; rewrite Hmcj; auto).
                apply (domain_invalid (weak_obs_eq (obs_eq Htsimj))) in Hcontra.
                  by congruence.
          }
          split.
          { (* fi is included in f' *)
            intros b1 b2 Hfi.
            destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
            - assert (Hf_val := (domain_valid HsimWeak) b1).
              specialize (Hf_val
                            ((proj2 (restrPermMap_valid
                                       (HmemCompC i pfc) b1)) Hvalidmc)).
              destruct Hf_val as [b2' Hf_val].
              assert (Heq: b2 = b2')
                by (apply Hincr in Hf_val;
                     rewrite Hf_val in Hfi; inversion Hfi; by subst);
                subst b2';
                  by assumption.
            - destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''];
              first by assumption.
              destruct (valid_block_dec mcj' b1) as [Hvalidmcj'_b1 | Hinvalidmcj'];
                assert (Hcontra := domain_invalid (weak_obs_eq (obs_eq Htsim')));
                assert (Hinvalid: ~ Mem.valid_block
                                    (restrPermMap (memCompC'' i pfci'')) b1)
                  by (intros Hcontra2;
                        by apply restrPermMap_valid in Hcontra2);
                specialize (Hcontra _ Hinvalid);
                  by congruence.
          } split.
          { (* synced *)
            intros Hsynced'.
            assert (Hlst :[seq x <- [seq x <- xs | x != i] | x == j] =
                          [seq x <- xs | x == j]) by (by eapply filter_neq_eq).
            rewrite Hlst in Hsynced'.
            rewrite Hsynced' in Hexecij.
            inversion Hexecij; subst;
            [|simpl in HschedN; inversion HschedN; subst; discriminate].
            rewrite Hsynced' in Hexecj.
            specialize (Hsyncedj Hsynced'). simpl. subst f.
            extensionality b.
            destruct (valid_block_dec mc b) as [Hvalidmc | Hinvalidmc].
            - assert (Hfb := (domain_valid HsimWeak) b Hvalidmc).
              destruct Hfb as [b' Hfb].
              rewrite Hfb. by apply Hincr in Hfb.
            - destruct (valid_block_dec mcj' b) as [? | Hinvalidmcj'];
              first by reflexivity.
              assert (Hinvdomain := domain_invalid (weak_obs_eq (obs_eq Htsim))).
              assert (Hinvalidmcji':
                        ~ Mem.valid_block (restrPermMap (memCompC' i pfc')) b)
                by (intros Hcontra; by apply restrPermMap_valid in Hcontra).
              specialize (Hinvdomain _ Hinvalidmcji'). rewrite Hinvdomain.
              assert (Heq: mc = mcj)
                by (inversion Hexecj; [subst mcj; auto |
                                       simpl in HschedN; discriminate]).
              subst mcj.
              assert (Hle: (Mem.nextblock mc <= Mem.nextblock mcj')%positive)
                by admit.
              apply Pos.lt_eq_cases in Hle.
              destruct Hle as [Hlt | Heq].
              + apply Pos.le_nlt in Hinvalidmc.
                apply Pos.le_nlt in Hinvalidmcj'.
                assert (Hinvalid:
                          (Mem.nextblock mc <=
                           Z.to_pos (Z.pos_sub b (Mem.nextblock mcj' -
                                                  Mem.nextblock mc)))%positive)
                  by (eapply le_sub; eauto).
                rewrite Z.pos_sub_gt; auto.
                simpl.
                apply Pos.le_nlt in Hinvalid.
                apply (domain_invalid HsimWeak) in Hinvalid.
                  by auto.
              + rewrite Heq. rewrite Z.pos_sub_diag. simpl.
                apply (domain_invalid HsimWeak) in Hinvalidmc;
                  by auto.
          } split.
          { (* tpc'' can step in a fine grained way for thread j *)
              by rewrite filter_neq_eq.
          } split.
          { (*strong simulation between mcj' and mf' *)
            intros pfcj' Hcompcj'. pf_cleanup.
            constructor.
            - (* code injection between thread j on tpj' and tpf'*)
              assert (Hctlij := code_eq Hsimij).
              assert (Hctljj := code_eq Htsimj).
              erewrite <- gsoThreadC_suspendF with (cntj := pffj) (cntj' := pffj');
                eauto.
              eapply ctl_inj_trans with (c:= getThreadC pfcjj); eauto.
              (* transitivity of f''*)              
              intros b b' b'' Hfpj Hfij.
              destruct (valid_block_dec mc b').
              assert (Hfid := (domain_valid (weak_obs_eq (obs_eq Hsim_c_ci))) _ v).
              destruct Hfid as [b2' Hfid].
              assert (b' = b2')
                by (apply id_ren_correct in Hfid; auto); subst b2'.
              apply Hincr' in Hfid.
              assert (b = b')
                by (eapply (injective (weak_obs_eq (obs_eq Hsimij))); eauto);
                subst.
              apply (domain_valid HsimWeak) in v.
              destruct v as [b2' Hf].
              assert (b2' = b'')
                by ( apply Hincrj in Hf;
                     rewrite Hf in Hfpj; by inversion Hfpj);
                by subst b2'.
              destruct (valid_block_dec mc'' b').
              destruct (valid_block_dec mc b) eqn:dec_mc_b.
              assert (v0' := v0).
              apply (domain_valid (weak_obs_eq (obs_eq Hsim_c_ci))) in v0'.
              destruct v0' as [b2' Hid].
              assert (b = b2')
                by (apply id_ren_correct in Hid; auto); subst b2'.
              apply Hincr' in Hid. rewrite Hfij in Hid.
              inversion Hid; subst;
                by exfalso.
              clear dec_mc_b.
              apply (domain_invalid (weak_obs_eq (obs_eq Hsim_c_ci))) in n0.
              specialize (Hsep _ _ n0 Hfij).
              destruct Hsep as [? ?];
                by exfalso.
              destruct (valid_block_dec mc b) as [Hcontra | ?].
              assert (Hfid :=
                        (domain_valid (weak_obs_eq (obs_eq Hsim_c_ci))) _ Hcontra).
              destruct Hfid as [b2' Hfid].
              assert (b = b2')
                by (apply id_ren_correct in Hfid; auto); subst b2'.
              apply Hincr' in Hfid. rewrite Hfij in Hfid.
              inversion Hfid; subst;
                by exfalso.
              assert (Hvalidb': Mem.valid_block mcj' b')
                by ( apply (codomain_valid (weak_obs_eq (obs_eq Hsimij))) in Hfij;
                       by erewrite restrPermMap_valid in Hfij).
              specialize (Hinverse _ Hvalidb' n0).
              simpl in Hinverse.
              destruct Hinverse as [Hfij' Hg].
              assert (b = Z.to_pos
                            match
                              (- Z.pos_sub (Mem.nextblock mc'')
                                           (Mem.nextblock mc))%Z
                            with
                            | 0%Z => Z.pos b'
                            | Z.pos y' => Z.pos (b' + y')
                            | Z.neg y' => Z.pos_sub b' y'
                            end)
                by (eapply Hinjective; eauto;
                    assert (Hfid_domain:= iffLRn (id_ren_domain mc b) n1);
                    destruct (id_ren mc b); [by exfalso | by tauto]);
                by subst.
            - (*mem_obs_eq between thread-j on mij=mcj' and on mff'*)
              (* Before going into the actual proof, some assertions about
                   how the permissions in the various proofs relate.
                   Again we should point at a figure somewhere. *)

              (* For a block that's valid in mc, j-permissions of mcj'
                         and mcj are equal *)
              assert (HpermC_mc_block: forall b1 ofs,
                         Mem.valid_block mc b1 ->
                         permission_at (restrPermMap (Hcompij j pfij))
                                       b1 ofs Cur =
                         permission_at (restrPermMap (Hcompjj j pfcjj))
                                       b1 ofs Cur).
              { intros b1 ofs Hvalidmc.
                specialize (Hincr' b1 b1 ltac:(eapply id_ren_validblock; eauto)).
                assert (HpermC_gt :=
                          (perm_obs_strong (strong_obs_eq (obs_eq Hsimij)))
                            b1 b1 ofs Hincr');
                  by eauto.
              }
              (* j-permissions of mcj are higher than mf*)
              assert (HpermF_mcj :=
                        perm_obs_weak (weak_obs_eq (obs_eq Htsimj))).

              (* also j-permissions of mcj are equal to mf*)
              assert (Hpermmcj_F := perm_obs_strong (strong_obs_eq
                                                       (obs_eq Htsimj))).
              
              (* The permission of j at an i-block in mci is
                   empty. We can deduce that by the fact that mc steps
                   to mc'' with i-steps hence the permissions of
                   thread-j will remain empty and then mc'' steps to
                   mcj' and the permissions will remain empty by
                   decay*)
              assert (Hpermj_mc'':
                        forall b1 ofs,
                          ~ Mem.valid_block mc b1 ->
                          Mem.valid_block mc'' b1 ->
                          permission_at (restrPermMap (memCompC'' _ pfcj''))
                                        b1 ofs Cur = None).
              { intros b1 ofs Hinvalidmc Hvalidmc''.
                (* Proof that the permission at b1 in mc|j is empty *)
                assert (Hinitp:
                          permission_at (restrPermMap (HmemCompC _ pfcj))
                                        b1 ofs Cur = None).
                { apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs)
                    in Hinvalidmc.
                  assert (Hlt := HmemCompC _ pfcj b1 ofs).
                  rewrite getMaxPerm_correct in Hlt.
                  unfold permission_at in Hlt. rewrite Hinvalidmc in Hlt.
                  simpl in Hlt.
                  rewrite restrPermMap_Cur.
                  destruct ((getThreadR pfcj) # b1 ofs); by tauto.
                }
                (* Proof that internal execution on thread i
                  preserves these empty permissions*)
                assert (pfcj': containsThread tpc' j)
                  by (eapply containsThread_internal_execution; eauto).
                assert (Hp': permission_at (restrPermMap (memCompC' _ pfcj'))
                                           b1 ofs Cur = None).
                { rewrite restrPermMap_Cur.
                  erewrite <- gsoThreadR_execution with (pfj := pfcj); eauto.
                  rewrite restrPermMap_Cur in Hinitp. by assumption.
                }
                rewrite restrPermMap_Cur.
                erewrite <- gsoThreadR_suspendC with (cntj:= pfcj'); eauto.
                rewrite restrPermMap_Cur in Hp'.
                  by assumption.
              }

              (* The permission of j at an i-block in mcij/mcj' is empty*)
              assert (Hpermj_mcj': forall b1 ofs,
                         ~ Mem.valid_block mc b1 ->
                         Mem.valid_block mc'' b1 ->
                         permission_at
                           (restrPermMap (Hcompij j pfij)) b1 ofs Cur = None).
              { (* Proof: By the fact that this block is allocated
                           by i, we know that the permission of thread
                           j on memory mc'' will be empty. Moreover by
                           the decay predicate, mcj' will have the
                           same permission as mc'' on this block
                           (since valid blocks cannot increase their
                           permissions) *)
                intros b1 ofs Hinvalidmc Hvalidmc''.
                specialize (Hpermj_mc'' b1 ofs Hinvalidmc Hvalidmc'').
                unfold permission_at in Hpermj_mc''.
                erewrite restrPermMap_Cur.
                assert (Hdecay := internal_execution_decay).
                specialize (Hdecay _ _ _ _ _ _ pfcj'' pfij memCompC'' Hcompij Hexecij).
                unfold decay in Hdecay.
                apply decay_decay' in Hdecay.
                specialize (Hdecay b1 ofs).
                destruct Hdecay as [_ Hold].
                erewrite restrPermMap_valid in Hold.
                specialize (Hold Hvalidmc'').
                destruct Hold as [[Hcontra _] | Heq]; first by congruence.
                rewrite Hpermj_mc'' in Heq.
                assert (Hperm_at := restrPermMap_Cur (Hcompij j pfij) b1 ofs).
                unfold permission_at in Hperm_at. by rewrite Hperm_at in Heq.
              }

              (* The permission of j at an i-block in mf is empty *)
              assert (Hpermj_eqF: forall b1 b2 ofs,
                         ~ Mem.valid_block mc b1 ->
                         Mem.valid_block mc'' b1 ->
                         fp i pfc b1 = Some b2 ->
                         permission_at (restrPermMap (memCompF' j pffj'))
                                       b2 ofs Cur = None).
              { (* Proof is straightforward by the blocks owned by i invariant*)
                intros b1 b2 ofs Hinvalidmc Hvalidmc'' Hfi.
                rewrite restrPermMap_Cur.
                erewrite <- gsoThreadR_suspendF with (cntj := pffj) by eauto.
                assert (Hf := (domain_invalid HsimWeak)).
                specialize (Hf b1).
                erewrite restrPermMap_valid in Hf. 
                eapply Hownedi; by eauto.
              }
              
              (* The j-permission of a j-block at mcj is equal to the 
                   permission at mcj'*)
              assert (Hpermmcj_mcj': forall b1' b1 ofs,
                         fij b1' = Some b1 ->
                         permission_at (restrPermMap (Hcompjj j pfcjj))
                                       b1' ofs Cur =
                         permission_at (restrPermMap (Hcompij j pfij))
                                       b1 ofs Cur).
              { intros b1' b1 ofs Hfij. 
                assert (Hperm_gt :=
                          (perm_obs_strong (strong_obs_eq (obs_eq Hsimij)))
                            b1' b1 ofs Hfij).
                eauto.
              }

              constructor.
              { (* weak obs eq *)
                constructor.
                - (*invalid domain of f' *)
                  intros b Hinvalid.
                  assert (Hinvalidmc'': ~ Mem.valid_block mc'' b)
                    by (intros Hcontra;
                         eapply internal_execution_valid with (m' := mcj')
                          in Hcontra;
                         eauto).
                  assert (Hinvalidmc: ~ Mem.valid_block mc b)
                    by (intros Hcontra;
                         eapply internal_execution_valid with (m' := mc'')
                          in Hcontra;
                         eauto).
                  simpl.
                  repeat match goal with
                         | [|- context[match ?Expr with _ => _ end ]] =>
                           destruct Expr; first by exfalso
                         end.
                  erewrite restrPermMap_valid in Hinvalid.
                  match goal with
                  | [|- fp _ _ ?Expr = _] =>
                    destruct (valid_block_dec mcj Expr) as [Hvalidmcj | Hinvalidmcj]
                  end.
                  + apply Pos.lt_eq_cases in Hle_nextblock.
                    destruct Hle_nextblock as [Hlt | Heq].
                    * apply Pos.le_nlt in Hinvalidmc''.
                      apply Pos.le_nlt in Hinvalidmc.
                      assert (Hinvalid':
                                (Mem.nextblock mc <=
                                 Z.to_pos (Z.pos_sub b (Mem.nextblock mc'' -
                                                        Mem.nextblock mc)))%positive)
                        by (eapply le_sub; eauto).
                      apply Pos.le_nlt in Hinvalid'.
                      apply (domain_valid (weak_obs_eq (obs_eq Hsimij))) in Hvalidmcj.
                      apply (domain_invalid (weak_obs_eq (obs_eq Hsim_c_ci ))) in Hinvalid'.
                      destruct Hvalidmcj as [b2 Hfij].
                      rewrite Z.pos_sub_gt in Hfij; auto.
                      assert (Hinvalid2 := Hsep _ _ Hinvalid' Hfij).
                      assert (Hvalidb2 :=
                                (codomain_valid (weak_obs_eq (obs_eq Hsimij))) _ _ Hfij).
                      erewrite restrPermMap_valid in Hvalidb2.
                      destruct Hinvalid2 as [_ Hinvalidb2''].
                      specialize (Hinverse _ Hvalidb2 Hinvalidb2'').
                      simpl in Hinverse.
                      destruct Hinverse as [Hcontra _].
                      assert (Heq_contra :=
                                (injective (weak_obs_eq (obs_eq Hsimij)))
                                  _ _ _ Hfij Hcontra).
                      assert (Heq : b = b2).
                      { apply Pos.le_nlt in Hinvalidb2''.
                        assert (((Mem.nextblock mc'' - Mem.nextblock mc) < b)%positive)
                          by (eapply lt_lt_sub; eauto).
                        assert (((Mem.nextblock mc'' - Mem.nextblock mc) < b2)%positive)
                          by (eapply lt_lt_sub; eauto).
                        rewrite Z.pos_sub_gt in Heq_contra; auto.
                        simpl in Heq_contra.
                        apply Z2Pos.inj_iff in Heq_contra;
                          try (rewrite Z.pos_sub_gt; auto;
                               apply Pos2Z.is_pos).
                        rewrite Z.pos_sub_gt in Heq_contra; auto.
                        rewrite Z.pos_sub_gt in Heq_contra; auto.
                        inversion Heq_contra as [Heq_contra2].
                        apply Pos.compare_eq_iff in Heq_contra2.
                        rewrite Pos.sub_compare_mono_r in Heq_contra2;
                          try (eapply lt_lt_sub; eauto).
                          by apply Pos.compare_eq_iff.
                      } subst b. by exfalso.
                    * rewrite Heq in Hvalidmcj.
                      rewrite Z.pos_sub_diag in Hvalidmcj.
                      simpl in Hvalidmcj.
                      rewrite Heq. rewrite Z.pos_sub_diag.
                      simpl.
                      apply (domain_valid (weak_obs_eq (obs_eq Hsimij))) in Hvalidmcj.
                      apply (domain_invalid (weak_obs_eq (obs_eq Hsim_c_ci ))) in Hinvalidmc.
                      destruct Hvalidmcj as [b2 Hfij].
                      assert (Hinvalid2 := Hsep _ _ Hinvalidmc Hfij).
                      assert (Hvalidb2 :=
                                (codomain_valid (weak_obs_eq (obs_eq Hsimij))) _ _ Hfij).
                      erewrite restrPermMap_valid in Hvalidb2.
                      destruct Hinvalid2 as [_ Hinvalidb2''].
                      specialize (Hinverse _ Hvalidb2 Hinvalidb2'').
                      simpl in Hinverse.
                      destruct Hinverse as [Hcontra _].
                      rewrite Heq in Hcontra.
                      rewrite Z.pos_sub_diag in Hcontra.
                      simpl in Hcontra.
                      assert (Heq_contra :=
                                (injective (weak_obs_eq (obs_eq Hsimij)))
                                  _ _ _ Hfij Hcontra).
                      subst;
                        by exfalso.
                  + apply (domain_invalid (weak_obs_eq (obs_eq Htsimj))) in Hinvalidmcj.
                      by assumption.
                - (*valid domain of f'*)
                  intros b1 Hvalid.
                  simpl.
                  erewrite restrPermMap_valid in Hvalid.
                  destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
                  + assert (Hf := (domain_valid HsimWeak) b1).
                    erewrite restrPermMap_valid in Hf.
                    destruct (Hf Hvalidmc) as [b2 Hf_val].
                    eexists; eassumption.
                  + destruct (valid_block_dec mc'' b1)
                      as [Hvalidmc'' | Hinvalidmc''].
                    * assert (Hfi := (domain_valid
                                        (weak_obs_eq (obs_eq Htsim'))) b1).
                      erewrite restrPermMap_valid in Hfi.
                      eauto.
                    * clear HpermF_mcj Hpermmcj_F Hpermj_mc'' Hpermj_mcj' Hpermj_eqF
                            Hpermmcj_mcj' HpermC_mc_block.
                      specialize (Hinverse b1 Hvalid Hinvalidmc'').
                      simpl in Hinverse.
                      destruct Hinverse as [Hfij Hf'].
                      destruct (
                          valid_block_dec mcj
                                          (Z.to_pos
                                             match
                                               (- Z.pos_sub (Mem.nextblock mc'') (Mem.nextblock mc))%Z
                                             with
                                             | 0%Z => Z.pos b1
                                             | Z.pos y' => Z.pos (b1 + y')
                                             | Z.neg y' => Z.pos_sub b1 y'
                                             end)) as [Hvalidmcj | Hinvalidmcj].
                      { apply (domain_valid (weak_obs_eq (obs_eq Htsimj))) in Hvalidmcj.
                          by assumption.
                      }
                      { apply (domain_invalid (weak_obs_eq (obs_eq Hsimij))) in Hinvalidmcj.
                          by congruence.
                      }
                - (* valid codomain of f'*)
                  intros b1 b2 Hf'.
                  assert (Hfj_codomain := codomain_valid (weak_obs_eq (obs_eq Htsimj))).
                  assert (Hfi_codomain := codomain_valid (weak_obs_eq (obs_eq Htsim))).
                  erewrite restrPermMap_valid in *.
                  simpl in Hf'.
                  repeat match goal with
                         | [H: context[match valid_block_dec ?M ?B with
                                       | _ => _ end] |- _] =>
                           destruct (valid_block_dec M B)
                         end; try discriminate.
                  specialize (Hfj_codomain b1 b2);
                    erewrite restrPermMap_valid in *.
                  eauto.
                  specialize (Hfi_codomain b1 b2);
                    erewrite restrPermMap_valid in *.
                  eauto.
                  specialize (Hfj_codomain _ _ Hf').
                    by erewrite restrPermMap_valid in *.
                - (* injectivity *)
                  intros b1 b1' b2 Hfb1 Hfb1'. simpl in Hfb1, Hfb1'.
                  destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
                  { (*case b1 is valid in mc*)
                    destruct (valid_block_dec mc b1') as [Hvalidmc' | Hinvalidmc'].
                    - (*case b1' is also valid in mc*)
                      eapply (injective HsimWeak); eauto.
                    - (*case b1' is not valid in mc *)
                      destruct (valid_block_dec mc'' b1') as [Hvalidmc''' | Hinvalidmc'''].
                      + apply Hincr in Hfb1.
                        eapply (injective (weak_obs_eq (obs_eq Htsim))); eauto.
                      + (* case b1' is in mcj' or invalid *)
                        (* we can derive a contradiction by the fact
                          that the inverse of b1' will be a block that
                          is invalid in mc, and that fpj maps it to
                          the same block as b1 which is valid in mc,
                          using injectivity of fpj*)
                        clear - Hfb1' Hfb1 Hincrj Htsimj Hvalidmc Hexec
                                      Hinvalidmc''' Hinvalidmc' Hle_nextblock.
                        apply Hincrj in Hfb1.
                        apply Pos.le_lteq in Hle_nextblock.
                        destruct Hle_nextblock as [Hlt | Hnbeq].
                        * rewrite Z.pos_sub_gt in Hfb1'; auto. simpl in Hfb1'.
                          apply Pos.le_nlt in Hinvalidmc'''.
                          assert (Hinvalid: (Mem.nextblock mc
                                             <=
                                             Z.to_pos (Z.pos_sub b1' (Mem.nextblock mc''
                                                                      - Mem.nextblock mc)))%positive)
                            by (eapply le_sub; eauto).
                          apply Pos.le_nlt in Hinvalid.
                          assert (Hcontra:= (injective
                                               (weak_obs_eq (obs_eq Htsimj)))
                                              _ _ _ Hfb1 Hfb1').
                          subst b1.
                            by exfalso.
                        * rewrite Hnbeq in Hfb1'.
                          rewrite Z.pos_sub_diag in Hfb1'.
                          simpl in Hfb1'.
                          assert (Hcontra := (injective (weak_obs_eq (obs_eq Htsimj)))
                                               _ _ _ Hfb1 Hfb1').
                          subst b1;
                            by exfalso.
                  }
                  { (* case b1 is a block that is invalid in mc *)
                    destruct (valid_block_dec mc b1') as [Hvalidmc' | Hinvalidmc'].
                    - (* case b1' is a block is that valid in mc*)
                      (*this is orthogonal to the above case, maybe factor it out?*)
                      admit.
                    - (* case b1' is invalid in mc*)
                      destruct (valid_block_dec mc'' b1) as [Hvalidmci | Hinvalidmci].
                      + destruct (valid_block_dec mc'' b1') as [Hvalidmci' | Hinvalidmci'];
                        first by (eapply (injective (weak_obs_eq (obs_eq Htsim))); eauto).
                        (* the inverse of b1' will be in invalid in
                          mc (fresh in mcj). Hence by seperation
                          between fpj and fpi it must be that b2 <>
                          b2, contradiction. *)
                        clear - Hfb1' Hfb1 Htsimj Hfpsep Hinvalidmc Hexec
                                      Hinvalidmc' Hinvalidmci' HsimWeak Hij Hle_nextblock.
                        exfalso.
                        apply (domain_invalid HsimWeak) in Hinvalidmc.
                        apply Pos.le_lteq in Hle_nextblock.
                        destruct Hle_nextblock as [Hlt | Hnbeq].
                        * rewrite Z.pos_sub_gt in Hfb1'; auto. simpl in Hfb1'.
                          apply Pos.le_nlt in Hinvalidmci'.
                          assert (Hinvalid: (Mem.nextblock mc
                                             <=
                                             Z.to_pos (Z.pos_sub b1' (Mem.nextblock mc''
                                                                      - Mem.nextblock mc)))%positive)
                            by (eapply le_sub; eauto).
                          apply Pos.le_nlt in Hinvalid.
                          apply (domain_invalid HsimWeak) in Hinvalid.
                          eapply Hfpsep with (b := b1) (i := i) (j := j); eauto.
                        * rewrite Hnbeq in Hfb1'.
                          rewrite Z.pos_sub_diag in Hfb1'.
                          simpl in Hfb1'.
                          apply (domain_invalid HsimWeak) in Hinvalidmc'.
                          eapply Hfpsep with (b := b1) (i:=i) (j:=j); eauto.
                      + (*case b1 is invalid in mc''*)
                        destruct (valid_block_dec mc'' b1') as [Hvalidmci' | Hinvalidmci'].
                        { (*again orthogonal to the above case*)
                          clear - Hfb1' Hfb1 Htsimj Hfpsep Hexec Hinvalidmc
                                        Hinvalidmc' Hinvalidmci Hvalidmci' HsimWeak Hij
                                        Hle_nextblock.
                          exfalso.
                          apply (domain_invalid HsimWeak) in Hinvalidmc'.
                          apply Pos.le_lteq in Hle_nextblock.
                          destruct Hle_nextblock as [Hlt | Hnbeq].
                          * rewrite Z.pos_sub_gt in Hfb1; auto. simpl in Hfb1.
                            apply Pos.le_nlt in Hinvalidmci.
                            assert (Hinvalid: (Mem.nextblock mc
                                               <=
                                               Z.to_pos (Z.pos_sub b1 (Mem.nextblock mc''
                                                                       - Mem.nextblock mc)))%positive)
                              by (eapply le_sub; eauto).
                            apply Pos.le_nlt in Hinvalid.
                            apply (domain_invalid HsimWeak) in Hinvalid.
                            eapply Hfpsep with (b := b1') (i := i) (j := j); eauto.
                          * rewrite Hnbeq in Hfb1.
                            rewrite Z.pos_sub_diag in Hfb1.
                            simpl in Hfb1.
                            apply (domain_invalid HsimWeak) in Hinvalidmc.
                            eapply Hfpsep with (b := b1') (b' := b1) (i:=i) (j:=j);
                              by eauto.
                        }
                        { (* case where they are both valid in mcj',
                              by injectivity of fpj for the inverses of b1 and b1'*)
                          apply (domain_invalid HsimWeak) in Hinvalidmc.
                          apply (domain_invalid HsimWeak) in Hinvalidmc'.
                          assert (Heq := (injective (weak_obs_eq (obs_eq Htsimj)))
                                           _ _ _ Hfb1 Hfb1').
                          apply Pos.le_lteq in Hle_nextblock.
                          destruct Hle_nextblock as [Hlt | Hnbeq].
                          * eapply Pos.le_nlt in Hinvalidmci.
                            eapply Pos.le_nlt in Hinvalidmci'.
                            assert (((Mem.nextblock mc'' - Mem.nextblock mc) < b1)%positive)
                              by (eapply lt_lt_sub; eauto).
                            assert (((Mem.nextblock mc'' - Mem.nextblock mc) < b1')%positive)
                              by (eapply lt_lt_sub; eauto).
                            rewrite Z.pos_sub_gt in Heq; auto.
                            simpl in Heq.
                            apply Z2Pos.inj in Heq;
                              try (rewrite Z.pos_sub_gt; auto;
                                   apply Pos2Z.is_pos). 
                            rewrite Z.pos_sub_gt in Heq; auto.
                            rewrite Z.pos_sub_gt in Heq; auto.
                            inversion Heq as [Heq2].
                            apply Pos.compare_eq_iff in Heq2.
                            rewrite Pos.sub_compare_mono_r in Heq2;
                              try (eapply lt_lt_sub; eauto).
                              by apply Pos.compare_eq_iff.
                          * rewrite Hnbeq in Heq.
                            rewrite Z.pos_sub_diag in Heq.
                            simpl in Heq;
                              by assumption.
                        }
                  }
                - (* permissions of mcj' are higher than mf *)
                  intros b1 b2 ofs Hf'.
                  simpl in Hf'.
                  destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
                  { (*case it's a block that's valid in mc*)
                    specialize (HpermC_mc_block b1 ofs Hvalidmc).
                    apply Hincrj in Hf'.
                    specialize (HpermF_mcj b1 b2 ofs Hf').
                    rewrite <- HpermC_mc_block in HpermF_mcj.
                    do 2 erewrite restrPermMap_Cur in *.
                    erewrite <- gsoThreadR_suspendF
                    with (cntj := pffj) (cntj' := pffj'); eauto.
                  }
                  { (*case it's a block that's invalid in mc*)
                    destruct (valid_block_dec mc'' b1)
                      as [Hvalidmc'' | Hinvalidmc''].
                    (*case it's a block that's valid in mc'' (an i-block)*)
                    specialize (Hpermj_eqF _ _ ofs Hinvalidmc Hvalidmc'' Hf').
                    rewrite Hpermj_eqF.
                    specialize (Hpermj_mcj' b1 ofs Hinvalidmc Hvalidmc'').
                    rewrite Hpermj_mcj'.
                    simpl;
                      by constructor.
                    (*case it's a block that's invalid in mc'' *)
                    specialize (Hvalidmcj' _ _ pfcj Hinvalidmc Hinvalidmc'' Hf').
                    specialize (Hinverse b1 Hvalidmcj' Hinvalidmc'').
                    simpl in Hinverse.
                    destruct Hinverse as [Hfij _].
                    specialize (HpermF_mcj _ _ ofs Hf').
                    specialize (Hpermmcj_F _ _ ofs Hf').
                    replace (permission_at (restrPermMap
                                              (memCompF' j pffj')) b2 ofs Cur)
                    with ((getThreadR pffj') # b2 ofs)
                      by (rewrite restrPermMap_Cur; reflexivity).
                    erewrite <- gsoThreadR_suspendF
                    with (cntj := pffj) (cntj' := pffj'); eauto.
                    replace ((getThreadR pffj) # b2 ofs)
                    with
                    (permission_at (restrPermMap
                                      (mem_compf Hsim _ pffj)) b2 ofs Cur)
                      by (rewrite restrPermMap_Cur; reflexivity).
                    specialize (Hpermmcj_mcj' _ _ ofs Hfij).
                    rewrite <- Hpermmcj_mcj'.
                      by assumption.
                  }
              } constructor.
              { (* strong_perm_obs *)
                intros b1 b2 ofs Hf'.
                (* the permissions of mf' and mf are the same,
                     suspend step does not touch the memory*)
                rewrite restrPermMap_Cur.
                erewrite <- gsoThreadR_suspendF
                with (cntj := pffj) (cntj' := pffj'); eauto.
                simpl in Hf'.
                rewrite <- restrPermMap_Cur with (Hlt := mem_compf Hsim _ pffj).
                destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
                - (* b is a valid block in mc*)
                  specialize (HpermC_mc_block _ ofs Hvalidmc).
                  apply Hincrj in Hf'.
                  specialize (Hpermmcj_F _ _ ofs Hf').
                  rewrite <- HpermC_mc_block in Hpermmcj_F.
                    by assumption.
                - destruct (valid_block_dec mc'' b1)
                    as [Hvalidmc'' | Hinvalidmc''].
                  + (* b1 is an i-block (allocated by thread i) *)
                    specialize (Hpermj_mcj' _ ofs Hinvalidmc Hvalidmc'').
                    rewrite Hpermj_mcj'.
                    rewrite restrPermMap_Cur.
                    apply (domain_invalid HsimWeak) in Hinvalidmc.
                      by eauto.
                  + specialize (Hvalidmcj' _ _ _ Hinvalidmc Hinvalidmc'' Hf').
                    specialize (Hinverse b1 Hvalidmcj' Hinvalidmc'').
                    simpl in Hinverse.
                    destruct Hinverse as [Hfij _].
                    specialize (Hpermmcj_mcj' _ _ ofs Hfij).
                    rewrite <- Hpermmcj_mcj'.
                      by eauto.
              }
              { (* val_obs_eq *)
                intros b1 b2 ofs Hf' Hreadable.
                simpl.
                assert (Hvalmcj_mcj' := val_obs_eq (strong_obs_eq (obs_eq Hsimij)));
                  simpl in Hvalmcj_mcj'.
                assert (Hvalmcj_mf := (val_obs_eq (strong_obs_eq (obs_eq Htsimj))));
                  simpl in Hvalmcj_mf. 
                destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc]
                                                      eqn:Hvalidmcdec.
                - (* Value of a block that is valid in mc *)
                  (* Idea: this block is mapped between mcj and mcj' by id
                       and from mcj to mf by fj. Hence we can reuse fj *)
                  assert (Hincr'_b1 := Hincr' b1 b1 ltac:(eapply id_ren_validblock; eauto)).
                  assert (Hvalmcj_mcj'_b1 := Hvalmcj_mcj' _ _ ofs Hincr'_b1).
                  apply Hincrj in Hf'.
                  assert (Hvalmcj_mf_b1 := Hvalmcj_mf _ _ ofs Hf').
                  unfold Mem.perm in Hreadable, Hvalmcj_mcj'_b1, Hvalmcj_mf_b1.
                  assert (Hreadable' := Hpermmcj_mcj' _ _ ofs Hincr'_b1).
                  unfold permission_at in Hreadable'.
                  rewrite <- Hreadable' in Hreadable.
                  specialize (Hvalmcj_mf_b1 Hreadable).
                  specialize (Hvalmcj_mcj'_b1 Hreadable).
                  inversion Hvalmcj_mcj'_b1 as
                      [n Hn_mcj Hn_mcj' | vj vj' q1 n Hval_obsjj' Hvj Hvj'
                       | Hundef_mcj Hmv_mcj'].
                  + rewrite <- Hn_mcj in Hvalmcj_mf_b1.
                    inversion Hvalmcj_mf_b1 as [n0 Heq Hn_mf| |];
                      first by constructor.
                  + (* Fragments case *)
                    rewrite <- Hvj in Hvalmcj_mf_b1.
                    inversion Hvalmcj_mf_b1 as [| vj0 vf q n0 Hval_obsjf Hvj0 Hvf |];
                      subst vj0 q1 n0.
                    constructor.
                    inversion Hval_obsjj' as [| | | | bpj1 bpj'2 ofsp Hfijp|]; subst;
                    inversion Hval_obsjf as [| | | | bpj0 bpf2 ofspf Hf'p|];
                    try subst bpj0; subst; try by constructor.
                    clear Hval_obsjf Hval_obsjj' Hvf Hvj.
                    constructor.
                    destruct (valid_block_dec mc bpj1) as [Hvalidmcbpj1 | Hinvalidmcbpj1]
                                                            eqn:Hdecbpj1.
                    { assert (Hincr'_bpj1 := Hincr' bpj1 bpj1 ltac:(eapply id_ren_validblock; eauto)).
                      rewrite Hincr'_bpj1 in Hfijp; inversion Hfijp; subst bpj'2.
                      rewrite Hdecbpj1.
                      clear Hfijp Hdecbpj1.
                      apply (domain_valid HsimWeak) in Hvalidmcbpj1.
                      destruct Hvalidmcbpj1 as [b2' Hf].
                      assert (b2' = bpf2)
                        by (apply Hincrj in Hf; rewrite Hf in Hf'p; by inversion Hf'p);
                        by subst.
                    }
                    { (* here it is usefulto have inject seperation for fij*)
                      unfold inject_separated in Hsep.
                      specialize (Hsep bpj1 bpj'2
                                       ltac:(eapply id_ren_invalidblock; eauto) Hfijp).
                      destruct Hsep as [_ Hinvalidmc''bpj'2].
                      assert (Hinvalidbmcpj'2: ~ Mem.valid_block mc bpj'2).
                      { intros Hcontra.
                        eapply internal_execution_valid with
                        (b := bpj'2) (m' := mc'') in Hcontra;
                          by eauto.
                      }
                      destruct (valid_block_dec mc bpj'2) as
                          [Hvalidmcbpj'2 | Hinvalidmcbpj'2];
                        first (by exfalso; auto).
                      destruct (valid_block_dec mc'' bpj'2) as [? | _];
                        first by (exfalso; auto).
                      destruct (valid_block_dec mcj' bpj'2) as [Hvalidmcj'bpj'2 | Hcontra].
                      specialize (Hinverse _ Hvalidmcj'bpj'2 Hinvalidmc''bpj'2).
                      simpl in Hinverse.
                      destruct Hinverse as [Hfij0 Hfid0].
                      clear HpermC_mc_block HpermF_mcj Hpermmcj_F Hpermj_mc'' Hreadable'
                            Hreadable   Hpermmcj_mcj'   Hpermj_eqF    Hvj'.
                      clear Hdecbpj1.
                      apply (domain_invalid (weak_obs_eq (obs_eq Hsim_c_ci)))
                        in Hinvalidmcbpj1.
                      specialize (Hinjective _ _ _ Hfid0 Hinvalidmcbpj1 Hfij0 Hfijp).
                      subst bpj1;
                        by assumption.
                      apply (codomain_valid (weak_obs_eq (obs_eq Hsimij))) in Hfijp.
                      erewrite restrPermMap_valid in Hfijp;
                        by exfalso.
                    }
                    rewrite <- Hundef_mcj in Hvalmcj_mf_b1.
                    inversion Hvalmcj_mf_b1;
                      by constructor.
                - (* Notice that this case is exactly the same as
                       above.  What changes is in which memory region
                       the pointer is in, but the proof about the
                       pointer itself is the same.  TODO: can we merge
                       the two cases? I think no, but need to check
                       again *)

                  destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''].
                  specialize (Hpermj_mcj' _ ofs Hinvalidmc Hvalidmc'').
                  unfold Mem.perm in Hreadable.
                  unfold permission_at in Hpermj_mcj'.
                  rewrite Hpermj_mcj' in Hreadable.
                  simpl in Hreadable;
                    by exfalso.
                  specialize (Hvalidmcj' _ _ _ Hinvalidmc Hinvalidmc'' Hf').
                  assert (Hinverse_b1 := Hinverse _ Hvalidmcj' Hinvalidmc'').
                  simpl in Hinverse_b1.
                  destruct Hinverse_b1 as [Hfij _].
                  assert (Hpermeq := Hpermmcj_mcj' _ _ ofs Hfij).
                  assert (Hreadable': Mem.perm (restrPermMap (Hcompjj j pfcjj))
                                               ((Z.to_pos
                                                   match
                                                     (- Z.pos_sub (Mem.nextblock mc'')
                                                                  (Mem.nextblock mc))%Z
                                                   with
                                                   | 0%Z => Z.pos b1
                                                   | Z.pos y' => Z.pos (b1 + y')
                                                   | Z.neg y' => Z.pos_sub b1 y'
                                                   end)) ofs Cur Readable)
                    by (unfold Mem.perm in *; unfold permission_at in Hpermeq;
                          by rewrite Hpermeq).
                  specialize (Hvalmcj_mcj' _ _ ofs Hfij Hreadable').
                  specialize (Hvalmcj_mf _ _ ofs Hf' Hreadable').
                  clear Hreadable Hreadable' Hpermeq Hpermmcj_mcj' Hpermj_eqF Hpermj_mcj'
                        Hpermj_mc'' Hpermmcj_F HpermF_mcj HpermC_mc_block.
                  inversion Hvalmcj_mcj' as
                      [n Hn_mcj Hn_mcj' | vj vj' q1 n Hval_obsjj' Hvj Hvj'| Hundef_mcj Hmv_mcj'].
                  + rewrite <- Hn_mcj in Hvalmcj_mf.
                    inversion Hvalmcj_mf as [n0 Heq Hn_mf| |];
                      first by constructor.
                  + (* Fragments case *)
                    rewrite <- Hvj in Hvalmcj_mf.
                    inversion Hvalmcj_mf as [| vj0 vf q n0 Hval_obsjf Hvj0 Hvf |];
                      subst vj0 q1 n0.
                    constructor.
                    inversion Hval_obsjj' as [| | | | bpj1 bpj'2 ofsp Hfijp|]; subst;
                    inversion Hval_obsjf as [| | | | bpj0 bpf2 ofspf Hf'p|];
                    try subst bpj0; subst; try by constructor.
                    clear Hval_obsjf Hval_obsjj' Hvf Hvj.
                    constructor.
                    destruct (valid_block_dec mc bpj1) as [Hvalidmcbpj1 | Hinvalidmcbpj1]
                                                            eqn:Hdecbpj1.
                    { assert (Hincr'_bpj1 := Hincr' bpj1 bpj1
                                                    ltac:(eapply id_ren_validblock; eauto)).
                      rewrite Hincr'_bpj1 in Hfijp; inversion Hfijp; subst bpj'2.
                      rewrite Hdecbpj1.
                      clear Hfijp Hdecbpj1.
                      apply (domain_valid HsimWeak) in Hvalidmcbpj1.
                      destruct Hvalidmcbpj1 as [b2' Hf].
                      assert (b2' = bpf2)
                        by (apply Hincrj in Hf; rewrite Hf in Hf'p; by inversion Hf'p);
                        by subst.
                    }
                    { (* here it is usefulto have inject seperation for fij*)
                      unfold inject_separated in Hsep.
                      specialize (Hsep bpj1 bpj'2
                                       ltac:(eapply id_ren_invalidblock; eauto) Hfijp).
                      destruct Hsep as [_ Hinvalidmc''bpj'2].
                      assert (Hinvalidbmcpj'2: ~ Mem.valid_block mc bpj'2).
                      { intros Hcontra.
                        eapply internal_execution_valid with
                        (b := bpj'2) (m' := mc'') in Hcontra;
                          by eauto.
                      }
                      destruct (valid_block_dec mc bpj'2) as
                          [Hvalidmcbpj'2 | Hinvalidmcbpj'2];
                        first (by exfalso; auto).
                      destruct (valid_block_dec mc'' bpj'2) as [? | _];
                        first by (exfalso; auto).
                      destruct (valid_block_dec mcj' bpj'2) as [Hvalidmcj'bpj'2 | Hcontra].
                      specialize (Hinverse _ Hvalidmcj'bpj'2 Hinvalidmc''bpj'2).
                      simpl in Hinverse.
                      destruct Hinverse as [Hfij0' Hfid0'].
                      (* NOTE: i need injectivity for the newly
                           (Separated) blocks. So fij bpj1 and fij
                           imply b0 = bpj1. I can have that *)
                      clear Hdecbpj1.
                      apply (domain_invalid (weak_obs_eq (obs_eq Hsim_c_ci)))
                        in Hinvalidmcbpj1.
                      specialize (Hinjective _ _ _ Hfid0' Hinvalidmcbpj1 Hfij0' Hfijp).
                      subst bpj1;
                        by assumption.
                      apply (codomain_valid (weak_obs_eq (obs_eq Hsimij))) in Hfijp.
                      erewrite restrPermMap_valid in Hfijp;
                        by exfalso.
                    }
                    rewrite <- Hundef_mcj in Hvalmcj_mf.
                    inversion Hvalmcj_mf.
                      by constructor.
              } 
          } split.
          { (* Proof that block ownership is preserved*)
            intros k pffk' Hjk b1 b2 ofs Hf' Hfi.
            destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
            - (* If b1 is valid in mc then it should be in f and
                since fi is an extension of f it should be in fi as
                well *)
              apply (domain_valid HsimWeak) in Hvalidmc.
              destruct Hvalidmc as [? Hf].
              apply Hincr in Hf. by congruence.
            - destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''];
              first by congruence.
              specialize (Hvalidmcj' _ _ _ Hinvalidmc Hinvalidmc'' Hf').
              destruct (Hinverse _ Hvalidmcj' Hinvalidmc'') as [Hfij ?].
              unfold inject_separated in Hsep.
              specialize (Hsep _ _ H Hfij).
              destruct Hsep as [Hinvalidb0 _].
              apply (domain_invalid HsimWeak) in Hinvalidb0.
              assert (pffk: containsThread tpf k)
                by (eapply suspendF_containsThread with (cnti := pff); eauto).
              specialize (Hownedj _ pffk Hjk _ _ ofs Hf' Hinvalidb0).
              erewrite <- gsoThreadR_suspendF with (cntj := pffk);
                by eauto.
          } split.
          { (*Block ownership with lockset*)
            intros b1 b2 ofs Hf' Hfi.
            destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
            - (* If b1 is valid in mc then it should be in f and
                since fi is an extension of f it should be in fi as
                well *)
              apply (domain_valid HsimWeak) in Hvalidmc.
              destruct Hvalidmc as [? Hf].
              apply Hincr in Hf. by congruence.
            - destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''];
              first by congruence.
              specialize (Hvalidmcj' _ _ _ Hinvalidmc Hinvalidmc'' Hf').
              destruct (Hinverse _ Hvalidmcj' Hinvalidmc'') as [Hfij Hfinv].
              unfold inject_separated in Hsep.
              specialize (Hsep _ _ Hfinv Hfij).
              destruct Hsep as [Hinvalidb0 _].
              apply (domain_invalid HsimWeak) in Hinvalidb0.
              specialize (Hownedj_ls _ _ ofs Hf' Hinvalidb0).
              erewrite <- suspendF_lockSet with (tp := tpf);
                by eauto.
          }
          { (*Block ownership with lock resources *)
            intros bl ofsl rmap b1 b2 ofs Hf' Hfi Hres.
            destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
            - (* If b1 is valid in mc then it should be in f and
                since fi is an extension of f it should be in fi as
                well *)
              apply (domain_valid HsimWeak) in Hvalidmc.
              destruct Hvalidmc as [? Hf].
              apply Hincr in Hf. by congruence.
            - destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''];
              first by congruence.
              specialize (Hvalidmcj' _ _ _ Hinvalidmc Hinvalidmc'' Hf').
              destruct (Hinverse _ Hvalidmcj' Hinvalidmc'') as [Hfij Hfinv].
              unfold inject_separated in Hsep.
              specialize (Hsep _ _ Hfinv Hfij).
              destruct Hsep as [Hinvalidb0 _].
              apply (domain_invalid HsimWeak) in Hinvalidb0.
              erewrite <- suspendF_lockPool with (tp := tpf) in Hres;
                by eauto.
        }
        }
        }
      { (* Proof that lockset simulation is preserved *)
        clear - HstepF Hexec HsuspendC HsimLocks Hincr Htsim HsimWeak Hownedi_ls.
        destruct HsimLocks as [HLocksPerm HLocksVal].
        simpl in *.
        assert (Hperm_eq: forall b ofs,
                   permission_at (restrPermMap (compat_ls memCompC'')) b ofs Cur =
                   permission_at (restrPermMap (compat_ls HmemCompC)) b ofs Cur).
        { intros.
          do 2 rewrite restrPermMap_Cur.
          erewrite <- suspendC_lockSet with (tp := tpc'); eauto.
          erewrite <- gsoLockSet_execution; eauto.
        }
        constructor.
        intros b1 b2 ofs Hfi.
        rewrite (Hperm_eq b1 ofs).
        do 2 rewrite restrPermMap_Cur.
        erewrite <- suspendF_lockSet with (tp' := tpf'); eauto.
        specialize (HsimWeak i pfc pff).
        destruct (valid_block_dec mc b1) as [Hvalid | Hinvalid].
        apply (domain_valid HsimWeak) in Hvalid.
        destruct Hvalid as [b2' Hf].
        assert (b2' = b2)
          by (apply Hincr in Hf; rewrite Hf in Hfi; by inversion Hfi);
          subst b2'.
        specialize (HLocksPerm _ _ ofs Hf);
          by do 2 rewrite restrPermMap_Cur in HLocksPerm.
        assert (Hempty:= Mem.nextblock_noaccess _ _ ofs Max Hinvalid).
        assert (Hlt:= (compat_ls HmemCompC) b1 ofs).
        rewrite getMaxPerm_correct in Hlt. unfold permission_at in Hlt.
        rewrite Hempty in Hlt. simpl in Hlt.
        destruct ((lockSet tpc) # b1 ofs);
          first by exfalso.
        apply (domain_invalid HsimWeak) in Hinvalid.
        erewrite Hownedi_ls;
          by eauto.
        intros b1 b2 ofs Hfi Hperm.
        simpl.
        unfold Mem.perm in *.
        unfold permission_at in Hperm_eq.
        rewrite (Hperm_eq b1 ofs) in Hperm.
        specialize (HsimWeak _ pfc pff).
        destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
        apply (domain_valid HsimWeak) in Hvalidmc.
        destruct Hvalidmc as [b2' Hf].
        assert (b2 = b2')
          by (apply Hincr in Hf; rewrite Hfi in Hf; by inversion Hf);
          subst b2'.
        erewrite <- internal_exec_disjoint_val_lock with (Hcomp := HmemCompC)
                                                          (m := mc) (tp := tpc);
          eauto.
        specialize (HLocksVal _ _ _ Hf Hperm).
        eapply memval_obs_eq_incr;
          by eauto.
        assert (Hempty:= Mem.nextblock_noaccess _ _ ofs Max Hinvalidmc).
        assert (Hlt:= (compat_ls HmemCompC) b1 ofs).
        rewrite getMaxPerm_correct in Hlt. unfold permission_at in Hlt.
        rewrite Hempty in Hlt. simpl in Hlt.
        apply (domain_invalid HsimWeak) in Hinvalidmc.
        assert (Hcontra:= restrPermMap_Cur (compat_ls HmemCompC) b1 ofs).
        unfold permission_at in Hcontra. rewrite Hcontra in Hperm.
        destruct ((lockSet tpc) # b1 ofs);
          by (simpl in Hperm; exfalso).
      }
      { (* Proof of strong simulation of resources *)
        clear - HstepF Hexec HsuspendC HsimRes Hincr Htsim
                       HsimWeak Hownedi_ls Hownedi_lp HsimLocks.
        intros bl1 bl2 ofs rmap1 rmap2 Hfl Hl1'' Hl2'.
        assert (Hl1: lockRes tpc (bl1,ofs) = Some rmap1)
          by (erewrite <- suspendC_lockPool with (pfc := pfc') in Hl1''; eauto;
              erewrite <- gsoLockPool_execution in Hl1''; eauto).

        assert (Hl2: lockRes tpf (bl2,ofs) = Some rmap2)
          by (erewrite <- suspendF_lockPool with (pff := pff) in Hl2'; eauto).

        assert (pff': containsThread tpf' i)
          by (eapply suspendF_containsThread with (cnti := pff); eauto).
        
        destruct HsimLocks.
        assert (Hperm_eq: forall b ofs,
                    permission_at (restrPermMap (compat_lp memCompC'' _ Hl1'')) b ofs Cur =
                    permission_at (restrPermMap (compat_lp HmemCompC _ Hl1)) b ofs Cur)
          by (intros; by do 2 rewrite restrPermMap_Cur).

        assert (Hvalid: Mem.valid_block mc bl1)
          by (eapply lock_valid_block; eauto).
        specialize (HsimWeak _ pfc pff).
        apply (domain_valid HsimWeak) in Hvalid.
        destruct Hvalid as [bl2' Hfl0].
        assert (bl2 = bl2')
          by (apply Hincr in Hfl0; rewrite Hfl in Hfl0; by inversion Hfl0); subst.
        specialize (HsimRes _ _ _ _ _ Hfl0 Hl1 Hl2).
        destruct HsimRes as [HpermRes HvalRes].
        constructor.
        intros b1 b2 ofs0 Hf1.
        rewrite (Hperm_eq b1 ofs0).
        do 2 rewrite restrPermMap_Cur.
        destruct (valid_block_dec mc b1) as [Hvalid | Hinvalid].
        apply (domain_valid HsimWeak) in Hvalid.
        destruct Hvalid as [b2' Hf].
        assert (b2' = b2)
          by (apply Hincr in Hf; rewrite Hf in Hf1; by inversion Hf1);
          subst b2'.
        specialize (HpermRes _ _ ofs0 Hf);
          by do 2 rewrite restrPermMap_Cur in HpermRes.
        assert (Hempty:= Mem.nextblock_noaccess _ _ ofs0 Max Hinvalid).
        assert (Hlt:= (compat_lp HmemCompC) _ _ Hl1 b1 ofs0).
        rewrite getMaxPerm_correct in Hlt. unfold permission_at in Hlt.
        rewrite Hempty in Hlt. simpl in Hlt.
        destruct (rmap1 # b1 ofs0);
          first by exfalso.
        apply (domain_invalid HsimWeak) in Hinvalid.
        eapply Hownedi_lp;
          by eauto.
        intros b1 b2 ofs0 Hfi Hperm.
        simpl.
        unfold Mem.perm in *.
        unfold permission_at in Hperm_eq.
        rewrite (Hperm_eq b1 ofs0) in Hperm.
        destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
        apply (domain_valid HsimWeak) in Hvalidmc.
        destruct Hvalidmc as [b2' Hf].
        assert (b2 = b2')
          by (apply Hincr in Hf; rewrite Hfi in Hf; by inversion Hf);
          subst b2'.

        Lemma internal_exec_disjoint_val_lockPool:
          forall (tp tp' : thread_pool) (m m' : mem) (i : tid) xs
            (cnti: containsThread tp i)
            (Hcomp : mem_compatible tp m)
            (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m')
            bl ofsl pmap
            (Hl: lockRes tp (bl,ofsl) = Some pmap)
            b ofs,
            Mem.perm (restrPermMap (compat_lp Hcomp _ Hl)) b ofs Cur Readable ->
            Maps.ZMap.get ofs (Mem.mem_contents m) # b =
            Maps.ZMap.get ofs (Mem.mem_contents m') # b.
        Proof.
          Admitted.
        
        erewrite <- internal_exec_disjoint_val_lockPool with (m := mc) (tp := tpc);
          eauto.
        specialize (HvalRes _ _ _ Hf Hperm).
        eapply memval_obs_eq_incr;
          by eauto.
        assert (Hempty:= Mem.nextblock_noaccess _ _ ofs0 Max Hinvalidmc).
        assert (Hlt:= (compat_lp HmemCompC) _ _ Hl1 b1 ofs0).
        rewrite getMaxPerm_correct in Hlt. unfold permission_at in Hlt.
        rewrite Hempty in Hlt. simpl in Hlt.
        apply (domain_invalid HsimWeak) in Hinvalidmc.
        assert (Hcontra:= restrPermMap_Cur (compat_lp HmemCompC _ Hl1) b1 ofs0).
        unfold permission_at in Hcontra. rewrite Hcontra in Hperm.
        destruct (rmap1 # b1 ofs0);
          by (simpl in Hperm; exfalso).
      }
        { (* Proof that the fine grained invariant is preserved *)
            by eapply suspendF_invariant with (pff := pff); eauto.
        }
        { (* Proof the max_inv is preserved *)
          by auto.
        }
        { by auto. }
        { eapply suspend_tp_wd;
            by eauto.
        }
        { apply ren_incr_domain_incr in Hincr.
          eapply ge_wd_incr;
            by eauto.
        }
    } 
  Admitted.

  (** ** Proofs about external steps*)

  Lemma not_in_filter :
    forall {A:eqType} (i : A) xs
      (HIn: ~ List.In i xs),
      [seq x <- xs | x == i] = [::].
  Proof.
    intros.
    induction xs as [|j xs]; first by reflexivity.
    simpl.
    destruct (j == i) eqn:Hji; move/eqP:Hji=>Hji;
      first by (subst j; simpl in *; exfalso; apply HIn; by auto).
    apply IHxs. intros Hcontra.
    apply HIn. simpl; by auto.
  Qed.

  Lemma external_step_inverse :
    forall U U' tp m tp' m' i (cnti: containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hexternal: cnti @ E)
      (Hstep: myCoarseSemantics.MachStep the_ge (i :: U,tp) m (U', tp') m'),
      U = U' /\ syncStep the_ge cnti Hcomp tp' m'.
  Proof.
    intros.
    inversion Hstep;
      try inversion Htstep; subst; simpl in *;
      try match goal with
          | [H: Some _ = Some _ |- _] => inversion H; subst
          end; pf_cleanup;

      repeat match goal with
             | [H: getThreadC ?Pf = _, Hext: ?Pf @ E |- _] =>
               unfold getStepType in Hext;
                 rewrite H in Hext; simpl in Hext
             | [H1: match ?Expr with _ => _ end = _ |- _] =>
               destruct Expr
             | [H: threadHalted _ |- _] =>
               inversion H; clear H; subst; pf_cleanup
             | [H1: is_true (isSome (halted ?Sem ?C)),
                    H2: match at_external _ _ with _ => _ end = _ |- _] =>
               destruct (at_external_halted_excl Sem C) as [Hext | Hcontra];
                 [rewrite Hext in H2;
                   destruct (halted Sem C); discriminate |
                  rewrite Hcontra in H1; exfalso; by auto]
             end; try discriminate;
      auto.
      by exfalso.
  Qed.

  (** Function that projects the angel through a memory injection to
    compute a new angel *)

  Definition projectAngel (f : memren) (deltaMap : delta_map) : delta_map :=
    Maps.PTree.fold (fun acc b bperm =>
                       match f b with
                       | Some b' =>
                         Maps.PTree.set b' bperm acc
                       | None =>
                         acc end)
                    deltaMap (Maps.PTree.empty _).

  
  Definition isProjection (f : memren) (deltaMap deltaMap' : delta_map) : Prop :=
    forall b b',
      f b = Some b' ->
      Maps.PTree.get b deltaMap = Maps.PTree.get b' deltaMap'.

  (** It's proof of correctness under the assumption that f is injective *)
  Lemma projectAngel_correct:
    forall (f:memren) deltaMap
      (Hf_injective: forall b1 b1' b2,
          f b1 = Some b2 ->
          f b1' = Some b2 ->
          b1 = b1'),
      isProjection f deltaMap (projectAngel f deltaMap).
  Proof.
    intros.
    eapply Maps.PTree_Properties.fold_rec with (P := isProjection f).
    { intros dmap dmap' a Heq Hprojection. intros b b' Hf.
      specialize (Heq b). rewrite <- Heq.
      unfold isProjection in Hprojection. eauto.
    }
    { unfold isProjection.
      intros;
        by do 2 rewrite Maps.PTree.gempty.
    }
    { intros dmap a bnew fnew Hget_dmap Hget_delta Hprojection.
      intros b b' Hf.
      destruct (Pos.eq_dec b bnew) as [Heq | Hneq].
      - subst bnew. rewrite Maps.PTree.gss.
        rewrite Hf.
          by rewrite Maps.PTree.gss.
      - rewrite Maps.PTree.gso; auto.
        unfold isProjection in Hprojection.
        destruct (f bnew) as [b'0|] eqn:Hfnew;
          try eauto.
        rewrite Maps.PTree.gso.
        eapply Hprojection; eauto.
        intros Hcontra.
        subst b'0;
          by eauto.
    }
  Qed.

  Lemma projectAngel_correct_2:
    forall (f:memren) deltaMap b'
      (Hf: ~ exists b, f b = Some b'),
      Maps.PTree.get b' (projectAngel f deltaMap) = None.
  Proof.
    intros.
    unfold projectAngel.
    eapply Maps.PTree_Properties.fold_rec. auto.
    rewrite Maps.PTree.gempty. reflexivity.
    intros.
    destruct (f k) as [b'0 |] eqn:Hf'.
    destruct (Pos.eq_dec b' b'0); subst.
    exfalso.
      by eauto.
      rewrite Maps.PTree.gso;
        by auto.
        by assumption.
  Qed.

  Lemma computeMap_projection_1:
    forall (tpc tpf : thread_pool) (mc mf : mem) f
      (i : tid) (pff : containsThread tpf i) (pfc : containsThread tpc i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf) (virtue : delta_map)
      (Hobs_eq: mem_obs_eq f (restrPermMap (HmemCompC i pfc))
                           (restrPermMap (HmemCompF i pff)))
      b1 b2
      (Hf: f b1 = Some b2),
      (computeMap (getThreadR pff) (projectAngel f virtue)) # b2 =
      (computeMap (getThreadR pfc) virtue) # b1.
  Proof.
    intros.
    extensionality ofs.
    destruct Hobs_eq as [Hweak_obs Hstrong_obs].
    destruct Hweak_obs.
    assert (Hangel := projectAngel_correct _ virtue injective0).
    specialize (Hangel _ _ Hf).
    symmetry in Hangel.
    destruct (Maps.PTree.get b1 virtue) as [df |] eqn:Hget.
    destruct (df ofs) as [p|] eqn:Hdf.
    erewrite (computeMap_1 _ _ _ _ Hget Hdf).
    erewrite (computeMap_1 _ _ _ _ Hangel Hdf);
      by reflexivity.
    erewrite (computeMap_2 _ _ _ _ Hget Hdf).
    erewrite (computeMap_2 _ _ _ _ Hangel Hdf).
    destruct Hstrong_obs.
    specialize (perm_obs_strong0 b1 b2 ofs Hf);
      by do 2 rewrite restrPermMap_Cur in perm_obs_strong0.
    erewrite (computeMap_3 _ _ _ _ Hget).
    erewrite (computeMap_3 _ _ _ _ Hangel).
    destruct Hstrong_obs.
    specialize (perm_obs_strong0 b1 b2 ofs Hf);
      by do 2 rewrite restrPermMap_Cur in perm_obs_strong0.
  Qed.

  Lemma computeMap_projection_2:
    forall (tpc tpf : thread_pool) f (i : tid)
      (pff : containsThread tpf i) (pfc : containsThread tpc i)
      (virtue : delta_map) b2
      (Hb1: ~ (exists b1 : block, f b1 = Some b2)),
      (computeMap (getThreadR pff) (projectAngel f virtue)) # b2 =
      (getThreadR pff) # b2.
  Proof.
    intros.
    assert (H := projectAngel_correct_2 _ virtue Hb1).
    extensionality ofs';
      by erewrite computeMap_3.
  Qed.
  
  Lemma sync_locks_mem_obs_eq:
    forall (tpc tpf : thread_pool) (mc mf : mem) f
      (i : tid) (pff : containsThread tpf i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf) (mc' : mem)
      (pfc : containsThread tpc i) (c : code) (b : block) 
      (ofs : int) (virtue : delta_map) (b2 : block) 
      (mf' : mem) (cf : code) v
      (HmemCompC' : mem_compatible
                      (updThread pfc (Kresume c Vundef)
                                 (computeMap (getThreadR pfc) virtue)) mc')
      (HmemCompF': mem_compatible
                     (updThread pff (Kresume cf Vundef)
                                (computeMap (getThreadR pff)
                                            (projectAngel f virtue))) mf')
      (Hinj: forall b1 b1' b2 : block,
          f b1 = Some b2 ->
          f b1' = Some b2 -> b1 = b1')
      (Hf: f b = Some b2)
      (Hmem_obs: strong_mem_obs_eq f
                                   (restrPermMap (compat_ls HmemCompC))
                                   (restrPermMap (compat_ls HmemCompF)))
      (Hstore: Mem.store Mint32 (restrPermMap (compat_ls HmemCompC)) b
                         (Int.intval ofs) (Vint v) = Some mc')
      (HstoreF: Mem.store Mint32 (restrPermMap (compat_ls HmemCompF)) b2
                          (Int.intval ofs) (Vint v) = Some mf'),
      strong_mem_obs_eq f (restrPermMap (compat_ls HmemCompC'))
                        (restrPermMap (compat_ls HmemCompF')).
  Proof.
    intros.
    destruct Hmem_obs as [Hperm_obs Hval_obs].
    constructor.
    intros b0 b3 ofs0 Hf0.
    specialize (Hperm_obs _ _ ofs0 Hf0).
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite restrPermMap_Cur in Hperm_obs.
    do 2 erewrite gsoThreadLock in *;
      by assumption.
    intros b0 b3 ofs0 Hf0 Hperm.
    simpl in *.
    assert (Hperm0: Mem.perm (restrPermMap (compat_ls HmemCompC)) b0 ofs0 Cur Readable).
    { unfold Mem.perm in *.
      assert (H1 := restrPermMap_Cur (compat_ls HmemCompC') b0 ofs0).
      assert (H2 := restrPermMap_Cur (compat_ls HmemCompC) b0 ofs0).
      unfold permission_at in *.
      rewrite H1 in Hperm.
      rewrite H2;
        by erewrite gsoThreadLock in Hperm. }
    erewrite Mem.store_mem_contents; eauto. simpl.
    erewrite Mem.store_mem_contents with (m2 := mf'); eauto. simpl.
    destruct (Pos.eq_dec b b0) as [? | Hneq].
    subst b0.
    assert (b2 = b3)
      by (rewrite Hf in Hf0; by inversion Hf0); subst b3.
    do 2 rewrite Maps.PMap.gss.
    destruct (Z_lt_le_dec ofs0 (Int.intval ofs)) as [Hlt | Hge].
    do 2erewrite Mem.setN_outside
      by (left; auto);
      by eauto.
    destruct (Z_lt_ge_dec ofs0
                          ((Int.intval ofs) +
                           Z.of_nat (length (inj_bytes (encode_int 4 (Int.unsigned v)))))) as [Hlt | Hge'].
    (*case it's the lock address*)
    unfold inj_bytes in *.
    rewrite Coqlib.list_length_map in Hlt.
    rewrite encode_int_length in Hlt.
    assert (H1 := Mem.getN_setN_same (inj_bytes (encode_int 4 (Int.unsigned v)))
                                     (Int.intval ofs) (Mem.mem_contents mc) # b).
    assert (H2 := Mem.getN_setN_same (inj_bytes (encode_int 4 (Int.unsigned v)))
                                     (Int.intval ofs) (Mem.mem_contents mf) # b2).
    unfold inj_bytes in H1, H2.
    rewrite Coqlib.list_length_map in H1, H2.
    rewrite encode_int_length in H1, H2. simpl in H1, H2.
    assert (Hofs: (ofs0 = Int.intval ofs \/ ofs0 = (Int.intval ofs) + 1
                   \/ ofs0 = (Int.intval ofs) + 1 + 1 \/
                   ofs0 = (Int.intval ofs) + 1 + 1 + 1)%Z)
      by (clear - Hlt Hge; simpl in Hlt; omega).
    
    destruct (encode_int 4 (Int.unsigned v)); first by discriminate.
    destruct l; first by discriminate.
    destruct l; first by discriminate. destruct l; first by discriminate.
    destruct l. 2: by discriminate.
    simpl in H1, H2.
    inversion H1; inversion H2. simpl in *.
    destruct Hofs as [? | [? | [? | ?]]]; subst;
    repeat (try rewrite Maps.ZMap.gss;
             try erewrite Maps.ZMap.gso
              by (intros Hcontra; clear - Hcontra;
                  destruct ofs; simpl in Hcontra;  clear intrange;
                  symmetry in Hcontra;
                  rewrite <- Z.add_0_r in Hcontra;
                  repeat rewrite <- Z.add_assoc in Hcontra;
                  simpl in Hcontra;
                  apply Z.add_reg_l in Hcontra; by omega));
      by constructor.
    erewrite Mem.setN_outside
      by (right; auto).
    erewrite Mem.setN_outside
      by (right; auto);
      by eauto.
    assert (b2 <> b3) (*by injectivity*)
      by (intros Hcontra; subst; eauto).
    erewrite Maps.PMap.gso by auto.
    erewrite Maps.PMap.gso by auto.
      by eauto.
  Qed. 

  (* NOTE: this is only needed to find out if a block is in the
    codomain of f, which is decidable *)
  Require Import Coq.Logic.ClassicalFacts.
  Hypothesis em : excluded_middle.

  (** Maintaing the invariant through projection of the angel*)

  (** This lemma is for the case we are trying to establish
    disjointness between some thread's resource map and the newly
    installed map from the angel*)
  Lemma disjoint_angel_project:
    forall (tpc tpf : thread_pool) (mc mf : mem) f
      (i j: tid) (pff : containsThread tpf i) (pfc : containsThread tpc i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf) (virtue : delta_map) 
      (c cf : ctl)
      (pffj' : containsThread
                 (updThread pff cf
                            (computeMap (getThreadR pff)
                                        (projectAngel f virtue))) j)
      (pffi' : containsThread
                 (updThread pff cf
                            (computeMap (getThreadR pff)
                                        (projectAngel f virtue))) i)
      (HnumThreads: forall k, containsThread tpc k <-> containsThread tpf k)
      (Hij: i <> j)
      (Hno_raceC: race_free (updThread pfc c (computeMap (getThreadR pfc) virtue)))
      (HsimWeak: forall (tid : tid) (pfc0 : containsThread tpc tid)
                   (pff0 : containsThread tpf tid),
          weak_tsim f pfc0 pff0 HmemCompC HmemCompF)
      (HinvF: invariant tpf)
      (Hobs_eq: mem_obs_eq f (restrPermMap (HmemCompC i pfc))
                           (restrPermMap (HmemCompF i pff))),
      permMapsDisjoint (getThreadR pffi') (getThreadR pffj').
  Proof.
    intros.
    rewrite gssThreadRes.
    assert (pffj:= cntUpdate' _ _ pff pffj').
    erewrite gsoThreadRes with (cntj := pffj) by eauto.
    assert (pfcj := (proj2 (HnumThreads _)) pffj).
    assert (pfcj' := cntUpdate c (computeMap (getThreadR pfc) virtue)
                               pfc pfcj).
    assert (pfc' := cntUpdate c (computeMap (getThreadR pfc) virtue) pfc pfc).
    specialize (Hno_raceC _ _ pfc' pfcj' Hij).
    erewrite gssThreadRes in Hno_raceC.
    unfold permMapsDisjoint.
    intros b2 ofs.
    specialize (HsimWeak _ pfcj pffj).
    destruct HsimWeak.
    assert (Hmapped: forall b1 b2,
               f b1 = Some b2 ->
               (computeMap (getThreadR pff)
                           (projectAngel f virtue)) # b2 =
               (computeMap (getThreadR pfc) virtue) # b1)
      by (eapply computeMap_projection_1; eauto).
    assert (Hunmapped: forall b2,
               (~ exists b1, f b1 = Some b2) ->
               (computeMap (getThreadR pff) (projectAngel f virtue)) # b2 =
               (getThreadR pff) # b2)
      by (eapply computeMap_projection_2; eauto).
    (*NOTE: this is actually decidable*)
    assert (Hb2: (exists b1, f b1 = Some b2) \/
                 ~ (exists b1, f b1 = Some b2))
      by eapply em.
    destruct Hb2 as [Hb2m | Hb2u].
    (*case b2 is mapped by f*)
    destruct Hb2m as [b1 Hf].
    specialize (Hmapped _ _ Hf).
    rewrite Hmapped.
    specialize (Hno_raceC b1 ofs).
    erewrite gsoThreadRes with (cntj := pfcj) in Hno_raceC by eauto.
    specialize (perm_obs_weak0 _ _ ofs Hf).
    do 2 rewrite restrPermMap_Cur in perm_obs_weak0.
    eapply perm_union_lower;
      by eauto.
    (* case b2 is not mapped by f*)
    specialize (Hunmapped _ Hb2u).
    rewrite Hunmapped.
      by apply ((no_race HinvF) _ _ pff pffj Hij b2 ofs).
  Qed.

  (** Storing on disjoint permisison maps should not affect the result*)
  Lemma gsoMem_obs_eq:
    forall (tpc tpf : thread_pool) (mc mf mc' mf' : mem) 
      (f : memren) (bl1 bl2 : block) (ofs : Z) (v : int) pmapC pmapC' pmapF
      i (pfc: containsThread tpc i) (pff: containsThread tpf i)
      (HltC: permMapLt pmapC (getMaxPerm mc))
      (HltF: permMapLt pmapF (getMaxPerm mf))
      (b1 : block) (ofs0 : Z) (b2 : block)
      (Hinj: forall b1 b1' b2 : block,
          f b1 = Some b2 ->
          f b1' = Some b2 -> b1 = b1')
      (Hval_obs_eq: memval_obs_eq f (Maps.ZMap.get ofs0 (Mem.mem_contents mc) # b1)
                                  (Maps.ZMap.get ofs0 (Mem.mem_contents mf) # b2))
      (Hf: f b1 = Some b2)
      (Hfl: f bl1 = Some bl2)
      (Hstore: Mem.store Mint32 (restrPermMap HltC)
                         bl1 ofs (Vint v) = Some mc')
      (HstoreF: Mem.store Mint32 (restrPermMap HltF)
                          bl2 ofs (Vint v) = Some mf')
      (Hreadable : Mem.perm_order' (pmapC' # b1 ofs0) Readable)
      (Hdisjoint: permMapsDisjoint pmapC pmapC'),
      memval_obs_eq f (Maps.ZMap.get ofs0 (Mem.mem_contents mc') # b1)
                    (Maps.ZMap.get ofs0 (Mem.mem_contents mf') # b2).
  Proof.
    intros.
    erewrite Mem.store_mem_contents; eauto.
    erewrite Mem.store_mem_contents with (m2 := mf'); eauto.
    simpl.
    destruct (Pos.eq_dec b1 bl1) as [? | Hneq_b1].
    - subst bl1.
      assert (b2 = bl2)
        by (rewrite Hf in Hfl; inversion Hfl; by subst).
      subst bl2.
      do 2 rewrite Maps.PMap.gss.
      destruct (Z_lt_le_dec ofs0 ofs) as [Hlt | Hge].
      do 2 erewrite Mem.setN_outside
        by (left; auto);
        by eauto.
      destruct (Z_lt_ge_dec
                  ofs0 (ofs + Z.of_nat
                                (length (inj_bytes (encode_int 4 (Int.unsigned v))))))
        as [Hlt | Hge'].
      (* case the two addresses coincide - contradiction by invariant*)
      + unfold inj_bytes in *.
        rewrite Coqlib.list_length_map in Hlt.
        rewrite encode_int_length in Hlt. simpl in Hlt.
        clear - Hreadable Hstore Hge Hlt Hdisjoint.
        apply Mem.store_valid_access_3 in Hstore.
        unfold Mem.valid_access in Hstore. simpl in Hstore.
        destruct Hstore as [Hcontra _].
        simpl in *.
        unfold Mem.range_perm in Hcontra.
        specialize (Hcontra ofs0 (conj Hge Hlt)).
        unfold Mem.perm in Hcontra.
        assert (H := restrPermMap_Cur HltC b1 ofs0).
        unfold permission_at in H.
        rewrite H in Hcontra; clear H.
        specialize (Hdisjoint b1 ofs0).
        destruct (pmapC # b1 ofs0) as [pl|],
                                              (pmapC' # b1 ofs0) as [pi|];
          try (destruct pl); try (destruct pi); simpl in *;
          destruct Hdisjoint as [? Hdisjoint]; inversion Hdisjoint; subst;
          try (by inversion Hreadable); try (by inversion Hcontra).
      + erewrite Mem.setN_outside
          by (right; auto).
        erewrite Mem.setN_outside
          by (right; auto);
          by eauto.
    - assert (b2 <> bl2) (*by injectivity*)
        by (intros Hcontra; subst; eauto).
      erewrite Maps.PMap.gso by auto.
      erewrite Maps.PMap.gso by auto.
        by eauto.
  Qed.
  
  Lemma invariant_project:
    forall (tpc tpf : thread_pool) (mc mf : mem) f 
      (i : tid) (pff : containsThread tpf i) (pfc : containsThread tpc i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf) 
      (virtue : delta_map) c cf
      (HinvF: invariant tpf)
      (HinvC': invariant (updThread pfc c (computeMap (getThreadR pfc) virtue)))
      (HsimWeak: forall (tid : tid) (pfc0 : containsThread tpc tid)
                   (pff0 : containsThread tpf tid),
          weak_tsim f pfc0 pff0 HmemCompC HmemCompF)
      (Htsim: mem_obs_eq f (restrPermMap (HmemCompC i pfc))
                         (restrPermMap (HmemCompF i pff)))
      (HsimLP: strong_mem_obs_eq f
                                 (restrPermMap (compat_ls HmemCompC))
                                 (restrPermMap (compat_ls HmemCompF)))
      (HnumThreads: forall i, containsThread tpc i <-> containsThread tpf i),
      invariant
        (updThread pff cf
                   (computeMap (getThreadR pff)
                               (projectAngel f virtue))).
  Proof.
    intros.
    constructor.
    (* no race for coarse-grained state*)
    assert (Hno_raceC:= no_race HinvC').
    intros k j pffk' pffj' Hkj.
    destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik;
      first by (subst k; eapply disjoint_angel_project;
                eauto).
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij;
      first by (apply permMapsDisjoint_comm; subst;
                eapply disjoint_angel_project; eauto).
    assert (pffj:= cntUpdate' _ _ pff pffj').
    erewrite gsoThreadRes with (cntj := pffj) by eauto.
    assert (pffk:= cntUpdate' _ _ pff pffk').
    erewrite gsoThreadRes with (cntj := pffk) by eauto;
      by apply ((no_race HinvF) _ _ pffk pffj Hkj).
    (* no race between lockset and threads*)
    intros j pffj'.
    rewrite gsoThreadLock.
    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
    subst j.
    rewrite gssThreadRes.
    assert (pfcj' := cntUpdate c (computeMap (getThreadR pfc) virtue)
                               pfc pfc).
    assert (Hno_raceC':= (lock_set_threads HinvC') _ pfcj').
    erewrite gssThreadRes in Hno_raceC'.
    rewrite gsoThreadLock in Hno_raceC'.
    unfold permMapsDisjoint.
    intros b2 ofs.
    destruct HsimLP as [HpermLP _].
    assert (Hmapped: forall b1 b2,
               f b1 = Some b2 ->
               (computeMap (getThreadR pff)
                           (projectAngel f virtue)) # b2 =
               (computeMap (getThreadR pfc) virtue) # b1)
      by (eapply computeMap_projection_1; eauto).
    assert (Hunmapped: forall b2,
               (~ exists b1, f b1 = Some b2) ->
               (computeMap (getThreadR pff) (projectAngel f virtue)) # b2 =
               (getThreadR pff) # b2)
      by (eapply computeMap_projection_2; eauto).
    (*NOTE: this is actually decidable*)
    assert (Hb2: (exists b1, f b1 = Some b2) \/
                 ~ (exists b1, f b1 = Some b2))
      by eapply em.
    destruct Hb2 as [Hb2m | Hb2u].
    (*case b2 is mapped by f*)
    destruct Hb2m as [b1 Hf].
    specialize (Hmapped _ _ Hf).
    rewrite Hmapped.
    specialize (Hno_raceC' b1 ofs).
    specialize (HpermLP _ _ ofs Hf).
    do 2 rewrite restrPermMap_Cur in HpermLP;
      by rewrite HpermLP.
    (* case b2 is not mapped by f*)
    specialize (Hunmapped _ Hb2u).
    rewrite Hunmapped;
      by apply ((lock_set_threads HinvF) _ pff b2 ofs).
    assert (pffj:= cntUpdate' _ _ pff pffj').
    erewrite gsoThreadRes with (cntj := pffj) by eauto;
      by apply ((lock_set_threads HinvF) _ pffj).
    admit.
    admit.
  Admitted.

  Lemma lockRes_eq:
    forall (tpc tpf : thread_pool) (mc mf : mem) i f
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf)
      (pfc : containsThread tpc i)
      (b1 b2 : block) ofs
      (pmap : dry_machine.LocksAndResources.lock_info)
      (HisLock : lockRes tpc (b1, ofs) = Some pmap)
      (Hf: f b1 = Some b2)
      (Hsim_ls: strong_mem_obs_eq f (restrPermMap (compat_ls HmemCompC))
                                  (restrPermMap (compat_ls HmemCompF))),
    exists pmapF : dry_machine.LocksAndResources.lock_info,
      lockRes tpf (b2, ofs) = Some pmapF.
  Proof.
    intros.
    destruct Hsim_ls as [Hperm_ls _].
    specialize (Hperm_ls _ _ ofs Hf).
    eapply lockSetGuts_1 in HisLock.
    do 2 rewrite restrPermMap_Cur in Hperm_ls.
    rewrite HisLock in Hperm_ls;
      by eapply lockSetGuts_2 in Hperm_ls.
  Qed.
  
  (** The projected angel satisfies the [angelSpec] *)
    (* TODO: generalize this for non-empty map *)
  Lemma angelSpec_project:
    forall (tpc tpf : thread_pool) (mc mf : mem) (f : memren)
      (i : tid)
      (pfc : containsThread tpc i)
      (pff : containsThread tpf i)
      (HmemCompC : mem_compatible tpc mc)
      (HmemCompF : mem_compatible tpf mf)
      (bl1 bl2 : block) ofs
      (pmap pmapF: dry_machine.LocksAndResources.lock_info)
      (virtueThread : delta_map)
      (Hres: lockRes tpc (bl1, ofs) = Some pmap)
      (HresF: lockRes tpf (bl2,ofs) = Some pmapF)
      (Hangel: angelSpec pmap (getThreadR pfc) empty_map
                         (computeMap (getThreadR pfc) virtueThread))
      (Hf: f bl1 = Some bl2)
      (HsimRes: strong_mem_obs_eq f
                                  (restrPermMap (compat_lp HmemCompC (bl1, ofs) Hres))
                                  (restrPermMap (compat_lp HmemCompF (bl2, ofs) HresF)))
      (Htsim: strong_tsim f pfc pff HmemCompC HmemCompF),
      angelSpec pmapF (getThreadR pff) empty_map
                (computeMap (getThreadR pff) (projectAngel f virtueThread)).
  Proof.
    intros.
    destruct Hangel as [HangelIncr HangelDecr].
    constructor.
    intros b2 ofs0 Hperm.
    (*NOTE: this is actually decidable*)
    assert (Hb2: (exists b1, f b1 = Some b2) \/
                 ~ (exists b1, f b1 = Some b2))
      by eapply em.
    destruct Hb2 as [[b1 Hf1] | Hunmapped].
    destruct Htsim as [? Hmem_obs_eq].
    erewrite computeMap_projection_1 in Hperm; eauto.
    specialize (HangelIncr _ _ Hperm).
    destruct HangelIncr as [Hreadable | Hreadable];
      [destruct Hmem_obs_eq as [_ [Hperm_eq _]] | destruct HsimRes as [Hperm_eq _]];
      specialize (Hperm_eq _ _ ofs0 Hf1);
      do 2 rewrite restrPermMap_Cur in Hperm_eq;
      rewrite Hperm_eq;
        by auto.
    erewrite computeMap_projection_2 in Hperm; eauto.
    intros b2 ofs0.
    replace (empty_map # b2 ofs0) with (@None permission)
      by (unfold Maps.PMap.get; rewrite Maps.PTree.gempty; by simpl).
    destruct (pmapF # b2 ofs0);
      by simpl.
  Qed.

  Lemma gss_mem_obs_eq_lock:
    forall tpc tpf mc mf mc' mf' pmap pmapF
      c cf i (f: memren)
      bl1 bl2 ofs v virtue
      (pfc: containsThread tpc i)
      (pff: containsThread tpf i)
      (pfc': containsThread (updLockSet
                               (updThread pfc (Kresume c Vundef)
                                          (computeMap (getThreadR pfc) virtue))
                               (bl1, ofs) empty_map) i)
      (pff': containsThread (updLockSet
                               (updThread pff (Kresume cf Vundef)
                                          (computeMap (getThreadR pff)
                                                      (projectAngel f virtue)))
                               (bl1, ofs) empty_map) i)
      (HmemCompC: mem_compatible tpc mc)
      (HmemCompF: mem_compatible tpf mf)
      (HmemCompC': mem_compatible
                     (updLockSet
                        (updThread pfc (Kresume c Vundef)
                                   (computeMap (getThreadR pfc) virtue))
                        (bl1, ofs) empty_map) mc')
      (HmemCompF'' : mem_compatible
                       (updLockSet
                          (updThread pff (Kresume cf Vundef)
                                     (computeMap (getThreadR pff)
                                                 (projectAngel f virtue)))
                          (bl2, ofs) empty_map) mf')
      (Hf: f bl1 = Some bl2)
      (HinvC: invariant tpc)
      (HinvF: invariant tpf)
      (HisLock : lockRes tpc (bl1, ofs) = Some pmap)
      (HisLockF : lockRes tpf (bl2, ofs) = Some pmapF)
      (Hobs_eq: mem_obs_eq f (restrPermMap (HmemCompC i pfc))
                           (restrPermMap (HmemCompF i pff)))
      (HstoreC: Mem.store Mint32 (restrPermMap (compat_ls HmemCompC)) bl1
                          ofs (Vint v) = Some mc')
      (HstoreF: Mem.store Mint32 (restrPermMap (compat_ls HmemCompF)) bl2
                          ofs (Vint v) = Some mf')
      (Hangel : angelSpec pmap (getThreadR pfc) empty_map
                          (computeMap (getThreadR pfc) virtue))
      (HangelF : angelSpec pmapF (getThreadR pff) empty_map
                           (computeMap (getThreadR pff) (projectAngel f virtue)))
      (HsimRes:
         strong_mem_obs_eq f
                           (restrPermMap (compat_lp HmemCompC (bl1, ofs) HisLock))
                           (restrPermMap (compat_lp HmemCompF (bl2, ofs) HisLockF))),
      mem_obs_eq f (restrPermMap (HmemCompC' i pfc'))
                 (restrPermMap (HmemCompF'' i pff')).
  Proof.
    intros.
    inversion Hobs_eq.
    assert (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
      by (
          intros;
          erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompC);
          split;
          [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
          eauto).
    assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
      by (intros; split; intros Hinvalid Hcontra;
            by apply Hvb in Hcontra).
    assert (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
      by (
          intros;
          erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompF);
          split;
          [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
          eauto).
    constructor.
    (*weak_obs_eq*)
    destruct weak_obs_eq0.
    constructor;
      try (intros b1; erewrite restrPermMap_valid);
      try (erewrite <- Hvb');
      try (erewrite <- Hvb);
      try by eauto.
    intros b1 b2 Hf1. erewrite restrPermMap_valid.
    erewrite <- HvbF.
    specialize (codomain_valid0 _ _ Hf1);
      by erewrite restrPermMap_valid in codomain_valid0.
    intros b1 b2 ofs0 Hf1.
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite gLockSetRes.
    do 2 rewrite gssThreadRes.
    erewrite computeMap_projection_1; eauto;
      by apply po_refl.
    constructor.
    intros b1 b2 ofs0 Hf1.
    do 2 rewrite restrPermMap_Cur.
    do 2 rewrite gLockSetRes.
    do 2 rewrite gssThreadRes.
    erewrite computeMap_projection_1; eauto;
      by apply po_refl.
    intros b1 b2 ofs0 Hf1 Hperm.
    destruct Hangel as [HangelIncr HangelDecr].
    unfold Mem.perm in *.
    assert (Hperm_eq := restrPermMap_Cur (HmemCompC' i pfc') b1 ofs0).
    unfold permission_at in Hperm_eq.
    rewrite Hperm_eq in Hperm.
    rewrite gLockSetRes in Hperm.
    rewrite gssThreadRes in Hperm.
    specialize (HangelIncr _ _ Hperm).
    destruct HangelIncr as [Hreadablei | Hreadablelp].
    (* case the address was already readable on thread i*)
    simpl.
    destruct strong_obs_eq0 as [_ Hval_obs_eq].
    unfold Mem.perm in Hval_obs_eq.
    assert (Hperm_eq_old := restrPermMap_Cur (HmemCompC i pfc) b1 ofs0).
    unfold permission_at in Hperm_eq_old.
    specialize (Hval_obs_eq _ _ ofs0 Hf1).
    rewrite Hperm_eq_old in Hval_obs_eq.
    specialize (Hval_obs_eq Hreadablei).
    simpl in Hval_obs_eq.
    destruct weak_obs_eq0.
    destruct HinvC.
    eapply gsoMem_obs_eq with (bl1 := bl1) (HltC := compat_ls HmemCompC)
                                           (HltF := compat_ls HmemCompF)
                                           (pmapC':= getThreadR pfc);
      by eauto.
    (*case the address was readable on the lockpool*)
    simpl.
    destruct HsimRes as [_ Hval_obs_eq].
    unfold Mem.perm in Hval_obs_eq.
    assert (Hperm_eq_old := restrPermMap_Cur
                              (compat_lp HmemCompC (bl1, ofs) HisLock) b1 ofs0).
    unfold permission_at in Hperm_eq_old.
    specialize (Hval_obs_eq _ _ ofs0 Hf1).
    rewrite Hperm_eq_old in Hval_obs_eq.
    specialize (Hval_obs_eq Hreadablelp).
    simpl in Hval_obs_eq.
    destruct weak_obs_eq0.
    destruct HinvC.
    specialize (lock_res_set0 _ _ HisLock).
    apply permMapsDisjoint_comm in lock_res_set0.
    eapply gsoMem_obs_eq with (bl1 := bl1) (HltC := compat_ls HmemCompC)
                                           (HltF := compat_ls HmemCompF)
                                           (pmapC':= pmap);
      by eauto.
  Qed.

  (** Performing a store on a lock, retains a strong simulation, using
  the id injection, for threads*)
  Lemma strong_tsim_store_id:
    forall tp tp' m m' i b ofs v
      (pfi: containsThread tp i)
      (pfi': containsThread tp' i)
      (Hresi: getThreadR pfi' = getThreadR pfi)
      (Hcodei: getThreadC pfi' = getThreadC pfi)
      (Hcomp: mem_compatible tp m)
      (Hcomp': mem_compatible tp' m') 
      (HinvC: invariant tp)
      (Hmem_wd: valid_mem m)
      (Htp_wd: tp_wd (id_ren m) tp)
      (Hstore: Mem.store Mint32
                         (restrPermMap (compat_ls Hcomp)) b ofs v = Some m'),
      (strong_tsim (id_ren m) pfi pfi' Hcomp Hcomp') /\
      (Mem.nextblock m = Mem.nextblock m').
  Proof.
    intros.
    split.
    constructor.
    { (* ctl_inj between threads *)
      rewrite Hcodei.
      specialize (Htp_wd _ pfi).
      destruct (getThreadC pfi); simpl in *;
      repeat match goal with
             | [|- core_inj _ _ _] =>
               apply core_inj_id; auto
             | [H: _ /\ _ |- _] => destruct H
             | [|- _ /\ _] => split
             | [|- val_obs _ _ _] =>
               apply val_obs_id; auto
             end;
      try (apply id_ren_correct).
      by reflexivity.
    }
    { (* mem_obs_eq *)
      constructor.
      constructor.
      intros b0 Hinvalid. erewrite restrPermMap_valid in Hinvalid;
        by apply id_ren_invalidblock.
      intros b1 Hvalid. erewrite restrPermMap_valid in Hvalid.
      exists b1;
        by apply id_ren_validblock.
      intros b1 b2 Hf.
      erewrite restrPermMap_valid.
      eapply Mem.store_valid_block_1; eauto.
      erewrite restrPermMap_valid.
      unfold id_ren in Hf.
      destruct (valid_block_dec m b1);
        by [simpl in Hf; inversion Hf; by subst | by exfalso].
      intros b1 b1' b2 Hf1 Hf1'.
      apply id_ren_correct in Hf1.
      apply id_ren_correct in Hf1';
        by subst.
      intros b1 b2 ofs0 Hf.
      do 2 rewrite restrPermMap_Cur.
      rewrite Hresi.
      apply id_ren_correct in Hf; subst;
        by eapply po_refl.
      constructor.
      intros b1 b2 ofs0 Hf.
      do 2 rewrite restrPermMap_Cur.
      rewrite Hresi.
      apply id_ren_correct in Hf;
        by subst.
      intros b1 b2 ofs0 Hf Hperm.
      assert (Hvalid: Mem.valid_block m b1)
        by (assert (Hdomain := id_ren_domain m);
             apply Hdomain;
             by rewrite Hf).
      apply id_ren_correct in Hf; subst.
      assert (Hstable: ~ Mem.perm (restrPermMap (compat_ls Hcomp)) b2 ofs0 Cur Writable).
      { clear - Hperm HinvC.
        destruct HinvC as [_ Hdisjoint _ _].
        intros Hcontra.
        specialize (Hdisjoint _ pfi b2 ofs0).
        unfold Mem.perm in *.
        assert (Heq1 := restrPermMap_Cur (Hcomp i pfi) b2 ofs0).
        assert (Heq2 := restrPermMap_Cur (compat_ls Hcomp) b2 ofs0).
        unfold permission_at in *.
        rewrite Heq1 in Hperm.
        rewrite Heq2 in Hcontra.
        clear Heq1 Heq2.
        destruct ((getThreadR pfi) # b2 ofs0) as [pl|],
                                                 ((lockSet tp) # b2 ofs0) as [pi|];
          try (destruct pl); try (destruct pi); simpl in *;
          destruct Hdisjoint as [? Hdisjoint]; inversion Hdisjoint; subst;
          try (by inversion Hperm); try (by inversion Hcontra).
      }
      simpl.
      replace (Mem.mem_contents m)
      with (Mem.mem_contents (restrPermMap (compat_ls Hcomp)))
        by reflexivity.
      erewrite store_contents_other with (m' := m'); eauto.
      eapply memval_obs_eq_id; try apply id_ren_correct.
      simpl.
      specialize (Hmem_wd b2 Hvalid ofs0 _ (Logic.eq_refl _)).
      destruct (Maps.ZMap.get ofs0 (Mem.mem_contents m) # b2);
        auto.
      unfold mem_wd.val_valid in Hmem_wd.
      unfold valid_memval, valid_val.
      destruct v0; auto.
      apply ((id_ren_domain m) b0) in Hmem_wd.
      destruct (id_ren m b0);
        [eexists; reflexivity | by exfalso].
    }
    erewrite Mem.nextblock_store with
    (m1 := (restrPermMap (compat_ls Hcomp))) (m2 := m');
      by eauto.
  Qed.

  Lemma strong_tsim_id_trans:
    forall (tp1 tp1' tp2 : thread_pool) (m1 m1' m2 : mem)
      (f fid: memren) (i : tid)
      (pf1 : containsThread tp1 i)
      (pf1' : containsThread tp1' i)
      (pf2 : containsThread tp2 i)
      (Hcomp1 : mem_compatible tp1 m1)
      (Hcomp1' : mem_compatible tp1' m1')
      (Hcomp2 : mem_compatible tp2 m2)
      (Hvalid: forall b, Mem.valid_block m1 b <-> Mem.valid_block m1' b)
      (Htsim_id: strong_tsim (id_ren m1) pf1 pf1' Hcomp1 Hcomp1')
      (Htsim: strong_tsim f pf1 pf2 Hcomp1 Hcomp2),
      strong_tsim f pf1' pf2 Hcomp1' Hcomp2.
  Proof.
    intros.
    destruct Htsim_id as [code_eq_id obs_eq_id].
    destruct Htsim as [code_eq obs_eq].
    constructor.
    - destruct (getThreadC pf1'), (getThreadC pf1); simpl in *;
      try (by exfalso);
      destruct (getThreadC pf2); simpl in *; try (by exfalso);
      repeat match goal with
             | [H: _ /\ _ |- _] =>
               destruct H
             | [|- _ /\ _] => split
             | [|- core_inj _ _ _] =>
               eapply core_inj_trans; eauto
             | [|- val_obs _ _ _] =>
               eapply val_obs_trans; eauto
             | [|- forall _, _] =>
               intros b b' b'' Hf Hfid;
                 apply id_ren_correct in Hfid;
               subst
             end; subst; auto.
    - destruct obs_eq. destruct weak_obs_eq0.
      destruct obs_eq_id as [weak_obs_eq_id strong_obs_eq_id].
      destruct strong_obs_eq_id as [Hperm_id Hval_id].
      destruct weak_obs_eq_id.
      assert (Hinvalid: forall b, ~ Mem.valid_block m1 b <-> ~Mem.valid_block m1' b)
        by (intros b; specialize (Hvalid b); destruct Hvalid;
            split; intros; intro Hcontra; eauto).
      constructor.
      + constructor; eauto.
        intros b Hb.
        erewrite restrPermMap_valid in Hb.
        apply Hinvalid in Hb;
          by auto.
        intros b Hb.
        erewrite restrPermMap_valid in Hb.
        apply Hvalid in Hb;
          by auto.
        intros b1 b2 ofs Hf.
        specialize (perm_obs_weak0 _ _ ofs Hf).
        assert (Hb1: Mem.valid_block m1 b1)
          by (destruct (valid_block_dec m1 b1) as [? | Hcontra]; auto;
              apply domain_invalid0 in Hcontra;
                by congruence).
        apply domain_valid1 in Hb1.
        destruct Hb1 as [b2' Hfid].
        assert (b1 = b2')
          by (apply id_ren_correct in Hfid; by subst);
          subst b2'.
        specialize (Hperm_id _ _ ofs Hfid).
        rewrite Hperm_id;
          by auto.
      + destruct strong_obs_eq0.
        constructor.
        intros b1 b2 ofs Hf.
        specialize (perm_obs_strong0 _ _ ofs Hf).
        assert (Hb1: Mem.valid_block m1 b1)
          by (destruct (valid_block_dec m1 b1) as [? | Hcontra]; auto;
              apply domain_invalid0 in Hcontra;
                by congruence).
        apply domain_valid1 in Hb1.
        destruct Hb1 as [b2' Hfid].
        assert (b1 = b2')
          by (apply id_ren_correct in Hfid; by subst);
          subst b2'.
        specialize (Hperm_id _ _ ofs Hfid).
        rewrite Hperm_id;
          by auto.
      + intros b1 b2 ofs Hf Hperm.
        clear - Hperm Hf val_obs_eq0 domain_invalid0 Hval_id
                      Hperm_id domain_valid1.
        assert (Hb1: Mem.valid_block m1 b1)
          by (destruct (valid_block_dec m1 b1) as [? | Hcontra]; auto;
              apply domain_invalid0 in Hcontra;
                by congruence).
        apply domain_valid1 in Hb1.
        destruct Hb1 as [b2' Hfid].
        assert (b1 = b2')
          by (apply id_ren_correct in Hfid; by subst);
          subst b2'.
        specialize (Hperm_id _ _ ofs Hfid).
        unfold permission_at in Hperm_id.
        unfold Mem.perm in *.
        rewrite Hperm_id in Hperm.
        specialize (val_obs_eq0 _ _ _ Hf Hperm).
        specialize (Hval_id _ _ _ Hfid Hperm).
        eapply memval_obs_trans; eauto.
        intros b b' b'' Hf' Hfid'.
        apply id_ren_correct in Hfid';
          by subst.
  Qed.
  
  Lemma sim_external: sim_external_def.
  Proof.
    unfold sim_external_def.
    intros.
    inversion Hsim as
        [HnumThreads HmemCompC HmemCompF HsafeC HsimWeak HfpSep HsimStrong
                     HsimLocks HsimRes HinvF HmaxF Hmemc_wd Htpc_wd Hge_wd].
    (* Thread i is in the coarse-grained machine*)
    assert (pfc: containsThread tpc i)
      by (eapply HnumThreads; eauto).
    (* Since thread i is synced, the coarse machine doesn't need to take any steps*)
    apply @not_in_filter with (xs := xs) in Hsynced.
    destruct (HsimStrong i pfc pff)
      as [tpc' [mc' [Hincr [Hsyncf [Hexec [Htsim [Hownedi Hownedi_ls]]]]]]];
      clear HsimStrong.
    (* Hence tpc = tpc' and mc = mc' *)
    rewrite Hsynced in Hexec.
    assert (Heq: tpc = tpc' /\ mc = mc')
      by (clear -Hexec; inversion Hexec; subst; auto; simpl in HschedN; discriminate).
    destruct Heq; subst tpc' mc'; clear Hexec.
    (* And also f won't change, i.e. f = fi *)
    specialize (Hsyncf Hsynced); subst f.
    clear Hincr.
    (* By safety, the coarse-grained machine can step for all schedules *)
    specialize (HsafeC (mySchedule.buildSched (i :: nil)) 1).
    simpl in HsafeC. destruct HsafeC as [[[U tpc'] [mc' HstepC]] _].
    (* We know there is a strong simulation for thread i*)
    specialize (Htsim pfc HmemCompC).
    (*TODO: coarse machine step implies the invariant*)
    assert (HinvC: invariant tpc)
      by admit.
    (* Since the fine grained machine is at an external step so is
      the coarse-grained machine*)
    assert (HexternalC: pfc @ E)
      by (by erewrite (stepType_inj _ _ _ (code_eq Htsim))).
    (* An external step pops the schedule and executes a concurrent call *)
    assert (Heq : empty = U /\ syncStep the_ge pfc HmemCompC tpc' mc')
      by (eapply external_step_inverse; eauto).
    destruct Heq as [? HconcC]; subst U.
    assert (HmemCompC': mem_compatible tpc' mc')
      by admit.
    (*TODO: we must deduce that fact from safety of coarse-grained machine*)
    exists tpc', mc'.
    (* We proceed by case analysis on the concurrent call *)
    inversion HconcC; try subst tp' tp''; try subst m'.
    { (* Lock Acquire *)
        (* In order to construct the new memory we have to perform the
        load and store of the lock, after setting the correct permissions*)
        (*We prove that b is valid in m1 (and mc)*)
        assert (Hvalidb: Mem.valid_block m1 b)
          by (eapply load_valid_block; eauto).
        rewrite <- Hrestrict_pmap in Hvalidb.
        (*  and compute the corresponding block in mf *)
        destruct ((domain_valid (weak_obs_eq (obs_eq Htsim))) _ Hvalidb)
          as [b2 Hfb].
        assert (Hvalidb2 := (codomain_valid (weak_obs_eq (obs_eq Htsim))) _ _ Hfb).
        erewrite restrPermMap_valid in Hvalidb2.
        remember (restrPermMap (compat_ls HmemCompF)) as mf1 eqn:Hrestrict_pmapF.
        subst m1.
        (* and prove that loading from that block in mf gives us the
        same value as in mc, i.e. unlocked*)
        assert (HloadF: Mem.load Mint32 mf1 b2 (Int.intval ofs) = Some (Vint Int.one)).
        {
          destruct (load_val_obs _ _ _ Hload Hfb HsimLocks) as [v2 [Hloadf Hobs_eq]].
          inversion Hobs_eq; subst.
            by auto.
        }
        assert (Hval_obs: val_obs (fp i pfc) (Vint Int.zero) (Vint Int.zero))
          by constructor.
        (* and then storing gives us related memories*)
        assert (HstoreF := store_val_obs _ _ _ Hstore Hfb Hval_obs HsimLocks).
        destruct HstoreF as [mf' [HstoreF HsimLocks']].
        (* We have that the code of the fine grained execution
        is related to the one of the coarse-grained*)
        assert (Hcore_inj:= code_eq Htsim).
        rewrite Hcode in Hcore_inj.
        simpl in Hcore_inj.
        destruct (getThreadC pff) as [? | cf |? | ?] eqn:HcodeF;
          try by exfalso.
        (* And now we can prove that cf is also at external *)
        assert (Hat_external_spec := core_inj_ext _ _ _ Hcore_inj).
        rewrite Hat_external in Hat_external_spec.
        destruct (at_external Sem cf) as [[[? ?] vsf]|] eqn:Hat_externalF;
          try by exfalso.
        (* and moreover that it's the same external and their
        arguments are related by the injection*)
        destruct Hat_external_spec as [? [? Harg_obs]]; subst.
        inversion Harg_obs as [|? ? lock_ptr ? Hptr_obs Hl]; subst.
        inversion Hl; subst.
        inversion Hptr_obs as [| | | |b1 bf ofs0 Hf|];
          subst b1 ofs0 lock_ptr.
        assert (bf = b2)
          by (rewrite Hf in Hfb; by inversion Hfb);
          subst bf.
        (* To compute the new fine grained state, we apply the
        renaming to the resources the angel provided us*)
        remember (projectAngel (fp i pfc) virtueThread) as virtueF eqn:HvirtueF.
        remember (updThread pff (Kresume cf Vundef)
                            (computeMap (getThreadR pff) virtueF))
          as tpf' eqn:Htpf'.
        (* We prove that the mapped block is a lock*)
        assert (HisLockF: exists pmapF, lockRes tpf (b2, Int.intval ofs) = Some pmapF)
          by (eapply lockRes_eq; eauto).
        destruct HisLockF as [pmapF HisLockF].
        (* and then prove that the projected angel satisfies the angelSpec*)
        assert (HangelF: angelSpec pmapF (getThreadR pff) empty_map
                                   (computeMap (getThreadR pff) virtueF))
          by (subst; eapply angelSpec_project; eauto).
        (* and finally build the final fine-grained state*)
        remember (updLockSet tpf' (b2, Int.intval ofs) empty_map) as tpf'' eqn:Htpf'';
          symmetry in Htpf''.
        exists tpf'', mf', (fp i pfc), fp.
        split.
        (* proof that the fine grained machine can step*)
        intros U.
        assert (HsyncStepF: syncStep the_ge pff HmemCompF tpf'' mf')
          by (eapply step_acquire with (b:=b2); eauto).
        econstructor; simpl;
          by eauto.
        (* Proof that the new coarse and fine state are in simulation*)
        (* The safety of the new coarse grained state will be useful
        to establish the machine invariant and the fact that the new
        memory and threadpool are compatible hence we prove it here*)
        assert (HsafeC': forall sched n,
                   safeN CoarseSem the_ge n
                         (sched,
                          (updLockSet
                             (updThread pfc (Kresume c Vundef)
                                        (computeMap (getThreadR pfc) virtueThread))) 
                             (b, Int.intval ofs) empty_map) mc').
        { clear - Hsim HstepC.
          assert (Hsafe := safeCoarse Hsim).
          intros U n.
          specialize (Hsafe (i :: U) (n.+1)).
          simpl in Hsafe.
          destruct Hsafe as [_ Hsafe'].
          assert (HstepC':
                    myCoarseSemantics.MachStep
                      the_ge (i :: U, tpc) mc
                      (U,
                       (updLockSet
                          (updThread pfc (Kresume c Vundef)
                                     (computeMap (getThreadR pfc) virtueThread)) 
                          (b, Int.intval ofs) empty_map))
                      mc') by admit.
          specialize (Hsafe' _ _ HstepC');
            by assumption.
        }
        (*TODO: make this into a lemma: safety ==> invariant*)
        assert (HinvC': invariant (updLockSet
                                     (updThread pfc (Kresume c Vundef)
                                                (computeMap (getThreadR pfc) virtueThread)) 
                                     (b, Int.intval ofs) empty_map)).
        { specialize (HsafeC' [:: i] 1).
          simpl in HsafeC'.
          destruct HsafeC' as [[? [? HstepC']] ?].
          clear - HstepC'.
          inversion HstepC'; try inversion Htstep; try inversion Hhalted; subst;
          simpl in *; by auto.
        }
        assert (HmaxF': max_inv mf').
        { intros b0 ofs0 Hvalid0.
          unfold permission_at.
          erewrite Mem.store_access; eauto.
          assert (H := restrPermMap_Max (compat_ls HmemCompF) b0 ofs0).
          eapply Mem.store_valid_block_2 in Hvalid0; eauto.
          erewrite restrPermMap_valid in Hvalid0.
          specialize (HmaxF b0 ofs0 Hvalid0).
          unfold permission_at in H.
          rewrite H.
          rewrite getMaxPerm_correct;
            by assumption.
        }
        assert (HmemCompF'' : mem_compatible tpf'' mf')
          by admit.
        subst.
        eapply Build_sim with (mem_compc := HmemCompC') (mem_compf := HmemCompF'').
        - (* containsThread *)
          clear - HnumThreads.
          intros j.
          split; intros cntj;
          eapply cntUpdateL;
          eapply cntUpdate;
          apply cntUpdateL' in cntj;
          apply cntUpdate' in cntj;
            by eapply HnumThreads.
        - (*safety of coarse machine*)
            by assumption.
        - (* weak simulation between the two machines*)
          (*TODO: factor this out as a lemma*)
          intros j pfcj' pffj'.
          assert (pfcj: containsThread tpc j)
            by (eapply cntUpdateC'; eauto).
          assert (pffj: containsThread tpf j)
            by (eapply cntUpdateC'; eauto).
          specialize (HsimWeak _ pfcj pffj).
          assert (Hvb: forall b, Mem.valid_block mc b <-> Mem.valid_block mc' b)
            by (
                intros;
                erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompC);
                split;
                [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
                eauto).
          assert (Hvb': forall b, ~ Mem.valid_block mc b <-> ~ Mem.valid_block mc' b)
            by (intros; split; intros Hinvalid Hcontra;
                  by apply Hvb in Hcontra).
          assert (HvbF: forall b, Mem.valid_block mf b <-> Mem.valid_block mf' b)
            by (
                intros;
                erewrite <- restrPermMap_valid with (Hlt := compat_ls HmemCompF);
                split;
                [eapply Mem.store_valid_block_1 | eapply Mem.store_valid_block_2];
                eauto).
          clear - Hvb Hvb' HvbF HstoreF Hstore HsimWeak Hsim.
          destruct HsimWeak.
          constructor; intros;
          repeat
            (match goal with
             | [H: context[Mem.valid_block (restrPermMap _) _] |- _] =>
               erewrite restrPermMap_valid in H
             | [H: ~ Mem.valid_block _ _ |- _] =>
               apply Hvb' in H; clear Hvb'
             | [H: Mem.valid_block _ _ |- _] =>
               apply Hvb in H; clear Hvb
             | [|- Mem.valid_block (restrPermMap _) _] =>
               erewrite restrPermMap_valid
             | [|- Mem.valid_block _ _] =>
               eapply HvbF; clear HvbF
             end); eauto;
          try by specialize (codomain_valid0 _ _ H).
          { (* Permissions on coarse machine are higher than permissions on fine*)
            destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij.
            - (*this is the case where the angel has replaced some permissions*)
              subst j. 
              do 2 rewrite restrPermMap_Cur.
              do 2 rewrite gLockSetRes.
              do 2 rewrite gssThreadRes.
              (*by case analysis on whether the angel changed the
              permission at this address*)
              assert (Hproject: Maps.PTree.get b0 (projectAngel (fp i pfc) virtueThread) =
                                Maps.PTree.get b1 virtueThread)
                by (symmetry; eapply projectAngel_correct; eauto).
              pf_cleanup.
              specialize (perm_obs_weak0 _ _ ofs0 Hrenaming).
              destruct (Maps.PTree.get b1 virtueThread) as [df|] eqn:Hdelta.
              + destruct (df ofs0) as [pnew |] eqn:Hdf.
                rewrite (computeMap_1 _ _ _ _ Hdelta Hdf).
                rewrite (computeMap_1 _ _ _ _ Hproject Hdf);
                  by eapply po_refl.
                rewrite (computeMap_2 _ _ _ _ Hdelta Hdf).
                rewrite (computeMap_2 _ _ _ _ Hproject Hdf);
                  by do 2 rewrite restrPermMap_Cur in perm_obs_weak0.
              + rewrite (computeMap_3 _ _ _ _ Hdelta).
                rewrite (computeMap_3 _ _ _ _ Hproject);
                  by do 2 rewrite restrPermMap_Cur in perm_obs_weak0.
            - do 2 erewrite restrPermMap_Cur.
              do 2 rewrite gLockSetRes.
              erewrite gsoThreadRes with (cntj := pfcj); eauto.
              erewrite gsoThreadRes with (cntj := pffj); eauto.
              specialize (perm_obs_weak0 _ _ ofs0 Hrenaming).
              do 2 erewrite restrPermMap_Cur in perm_obs_weak0;
                by assumption. }
          (* Proof of seperation of injections *)
          intros k j cntk' cntj' Hkj b0 b0' b3 b3' Hf0 Hf0' Hfk' Hfj'.
          assert (cntk: containsThread tpc k)
            by (eapply cntUpdateC'; eauto).
          assert (cntj: containsThread tpc j)
            by (eapply cntUpdateC'; eauto).
          erewrite cnt_irr with (cnt1 := cntk') (cnt2 := cntk) in Hfk'.
          erewrite cnt_irr with (cnt1 := cntj') (cnt2 := cntj) in Hfj'.
          eapply (HfpSep _ _ cntk cntj Hkj b0 b0');
            by eauto.
          (* Proof of strong simulations after executing some thread*)
          intros.
          destruct (tid == i) eqn:Htid; move/eqP:Htid=>Htid; subst.
          { (*case of strong simulation for the thread that took the external*)
            exists (updLockSet
                 (updThread pfc (Kresume c Vundef)
                            (computeMap (getThreadR pfc) virtueThread)) 
                 (b, Int.intval ofs) empty_map), mc'.
            assert (pfc0 = pfc)
              by (eapply cnt_irr; eauto); subst pfc0.
            rewrite Hsynced.
            repeat (split; (auto || constructor)).
            split; first by apply ren_incr_refl.
            split; first by auto.
            split; first by constructor.
            split.
            intros.
            constructor.
            do 2 rewrite gLockSetCode.
            do 2 rewrite gssThreadCode;
              by (split; [assumption | constructor]).
            destruct Htsim;
              by (eapply gss_mem_obs_eq_lock; eauto).
            repeat split;
              by congruence.
          }
          { (*strong simulation for another thread*)
            assert (Hstrong_sim := simStrong Hsim).
            assert (pfcj: containsThread tpc tid)
              by (eapply cntUpdateL' in pfc0;
                   eapply cntUpdate' in pfc0;
                   eauto).
            assert (pffj: containsThread tpf tid)
              by (eapply cntUpdateL' in pff0;
                   eapply cntUpdate' in pff0;
                   eauto).
            specialize (Hstrong_sim _ pfcj pffj).
            destruct Hstrong_sim
              as (tpcj & mcj & Hincrj & Hsyncedj & Hexecj & Htsimj
                  & Hownedj & Hownedj_ls & Hownedj_lp).
            (* first we prove that i is a valid thread after executing thread j*)
            assert (pfcij:= containsThread_internal_execution Hexecj pfc).

            (*Proof Sketch: Basically the proof we want is that
            changing some non-observable part of the state/memory
            should not affect the execution of thread j. To avoid
            giving yet another definition of equivalence of the
            observable state we re-use our strong injections. Steps:
            
            1. The original state <tpc,mc> will strongly inject with
            the id injection in the state <tpc', mc'> where we have
            updated the value of the lock and the resource maps
            according to the angel.

            2. Hence if <tpc,mc> takes internal steps to get to <tpcj,
            mcj> so will <tpc',mc'> to go to a new state
            <tpcj',mcj'>. Moreover <tpcj,mcj> will inject to
            <tpcj',mcj'> with the id injection. We had to strengthen
            our lemmas and corestep_obs_eq to obtain that last part.

            3. We use [strong_tsim_id_trans] to get that <tpcj',mcj'>
               will strongly inject in <tpf,mf> with the same
               injection as <tpcj,mcj>.

            4. Finally we prove that changing the state/memory
            in (TODO: add lemma name) non-observable parts retains the
            [strong_tsim] relation. *)

            (* Step 1*)
            assert (pfcjj: containsThread tpcj tid)
              by (eapply containsThread_internal_execution; eauto).
            assert (Hcompj: mem_compatible tpcj mcj)
              by (eapply internal_execution_compatible with (tp := tpc); eauto).
            specialize (Htsimj pfcjj Hcompj).
            (* We prove that thread tid on the original state injects
            in thread tid after updating the lockpool and storing the
            lock value*)
            assert (Htsimj_id:
                      (strong_tsim (id_ren mc) pfcj pfc0 HmemCompC HmemCompC') /\
                      (Mem.nextblock mc = Mem.nextblock mc')).
            { eapply strong_tsim_store_id; eauto.
              erewrite gLockSetRes.
              rewrite gsoThreadRes; eauto.
              erewrite gLockSetCode.
              rewrite gsoThreadCode; eauto.
              assert (domain_memren (id_ren mc) mc)
                by (apply id_ren_domain).
              assert (domain_memren (fp i pfc) mc)
                by (apply (mem_obs_eq_domain_ren (obs_eq Htsim))).
              eapply tp_wd_domain;
                by eauto.
            }
            destruct Htsimj_id as [Htsimj_id Hnextblock].
            
            (*TODO: lemma*)
            (* Step 2.*)
            assert (H := strong_tsim_execution _ HinvC' Htsimj_id Hexecj).
            destruct H as
                (tp2' & m2' & f' & Hexecj'& Hincrj' & Hsepj'
                 & Hinj' & Hnextblock' & Hinvj' & Htsimj' & Hid').
            destruct Htsimj' as (pf2j & pf2j' & Hcomp2 & Hcomp2' & Htsimj').
            specialize (Hid' Hnextblock (id_ren_correct mc)).
            assert (f' = id_ren mcj)
              by ( pose ((mem_obs_eq_domain_ren (obs_eq Htsimj')));
                   eapply is_id_ren; eauto); subst f'.
            exists tp2', m2'.
            erewrite cnt_irr with (cnt1 := pfc0) (cnt2 := pfcj).
            split; first by auto.
            split; first by auto.
            split; first by auto.
            split.
            (*strong thread simulation for j*)
            intros.
            pf_cleanup.
            (* Step 3, we use transitivity of strong_tsim *)
            assert (Htsim2j: strong_tsim (fp tid pfcj) pf2j' pffj Hcomp2'
                                         (mem_compf Hsim)).
            { eapply strong_tsim_id_trans
              with (f := fp tid pfcj) (Hcomp1 := Hcompj) (Hcomp1' := Hcomp2');
              eauto.
              destruct Hnextblock' as [[p [Hmcj Hm2']] | [Hmcj Hm2']];
              unfold Mem.valid_block;
              rewrite Hmcj Hm2' Hnextblock;
                by tauto.
            } 
            admit.
            (*TODO: lemma that says that changing the state and
            memoryin places with no access retains simulation *)
            split.
            (*thread ownership*)
            intros k pff2k Hjk b1 b0 ofs0 Hfj Hfi.
            destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
            { subst k.
              rewrite gLockSetRes.
              rewrite gssThreadRes; auto.
              assert (Hunmapped: ~ (exists b, (fp i pfc) b = Some b0)).
              { intros Hcontra.
                destruct Hcontra as [b3 Hcontra].
                assert (Hfj' := Hincrj _ _ Hcontra).
                assert (Heq := injective (weak_obs_eq (obs_eq Htsimj)) _ _ Hfj Hfj');
                  subst b3.
                  by congruence.
              }
              erewrite computeMap_projection_2;
                by eauto.
            }
            { rewrite gLockSetRes.
              rewrite gsoThreadRes; auto.
              eapply Hownedj;
                by eauto.
            }
            split.
            (* lockset ownership*)
            intros b1 b0 ofs0 Hfj Hfi.
            assert (b2 <> b0).
            { intros ?; subst b0.
              assert (Hfbj := Hincrj _ _ Hfb).
              assert (Heq := injective (weak_obs_eq (obs_eq Htsimj)) _ _ Hfj Hfbj);
                subst b.
                by congruence.
            }
            replace ((lockSet
                        (updLockSet
                           (updThread pff (Kresume cf Vundef)
                                      (computeMap (getThreadR pff)
                                                  (projectAngel (fp i pfc) virtueThread)))
                           (b2, Int.intval ofs) empty_map)) # b0 ofs0) with
            ((lockSet tpf) # b0 ofs0) by admit.
            eapply Hownedj_ls;
              by eauto.
            (* lockpool ownership*)
            intros bl ofsl rmap b1 b0 ofs0 Hfj Hfi Hres.
            destruct (EqDec_address (b2, Int.intval ofs) (bl, ofsl)) as [Heq | Hneq].
            (* case rmap is the resource map updated by the angel*)
            inversion Heq; subst.

            Lemma gssLockRes:
              forall tp addr pmap,
                lockRes (updLockSet tp addr pmap) addr = Some pmap.
            Proof.
            Admitted.

            rewrite gssLockRes in Hres. inversion Hres.
            unfold Maps.PMap.get.
            rewrite Maps.PTree.gempty. auto.
            (*case it is another resource map*)
            
            rewrite gsoLockRes in Hres; auto.
            rewrite gsoThreadLPool in Hres;
              by eauto.
            
            
            
            assert (b2 <> b0).
            { intros ?; subst b0.
              assert (Hfbj := Hincrj _ _ Hfb).
              assert (Heq := injective (weak_obs_eq (obs_eq Htsimj)) _ _ Hfj Hfbj);
                subst b.
                by congruence.
            }
            
            
                    
                  

            

           
            
            
            
              
            
            

            






            

                                          
                                          (* Proof of [strong_mem_obs_eq] for lock pool*)
            eapply sync_strong_mem_obs_eq; eauto.
               specialize (HsimWeak _ pfc pff);
                 by apply (injective HsimWeak).
               (* Proof of invariant preservation for fine-grained machine*)
               destruct Htsim.
               eapply invariant_project;
                 by eauto.
                 (* Max permission invariant*)
                 by assumption.
                 
                            
                            
                            
                            
                            

                                                Admitted.
                    
                    
                    End SimProofs.

