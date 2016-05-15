Require Import compcert.lib.Axioms.

Add LoadPath "../concurrency" as concurrency.

Require Import sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

Require Import Coq.Program.Program.
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
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
Require Import concurrency.concurrent_machine dry_machine_lemmas dry_context.


(* TODO: - Partial injectiveness (for fresh blocks) - Done

         - Well-defined memories

         - Remove admits - Almost done.

         - More comments explaining proofs, especially simulations.

         - More automation (hint databases, type classes for internal
           execution, etc.
         
         - The offset in renamings is annoying, consider if we want to keep it
 *)

Global Notation "a # b" := (Maps.PMap.get b a) (at level 1).
(** ** Injections between memories *)
Module MemObsEq.

  Import SEM. 

  (* A compcert injection would not work because it allows permissions to go up *)
  (* Moreover, we require that undefined values are matched by the target memory,
     unlike compcert injections *)
  
  (** Weak injection between memories *)
  Record weak_mem_obs_eq (f : meminj) (mc mf : M) :=
    {
      domain_invalid: forall b, ~(Mem.valid_block mc b) -> f b = None;
      domain_valid: forall b, Mem.valid_block mc b -> exists b', f b = Some (b',0%Z);
      codomain_valid: forall b1 b2, f b1 = Some (b2,0%Z) -> Mem.valid_block mf b2;
      injective: forall b1 b1' b2, f b1 = Some (b2,0%Z) ->
                              f b1' = Some(b2,0%Z) ->
                              b1 = b1';
      perm_obs_weak :
        forall b1 b2 ofs (Hrenaming: f b1 = Some (b2,0%Z)),
          Mem.perm_order''
            (permission_at mc b1 ofs Cur)
            (permission_at mf b2 ofs Cur)}.

  (** Strong injections on values *)
  Inductive val_obs (mi : meminj) : val -> val -> Prop :=
    obs_int : forall i : int, val_obs mi (Vint i) (Vint i)
  | obs_long : forall i : int64, val_obs mi (Vlong i) (Vlong i)
  | obs_float : forall f : Floats.float,
      val_obs mi (Vfloat f) (Vfloat f)
  | obs_single : forall f : Floats.float32,
      val_obs mi (Vsingle f) (Vsingle f)
  | obs_ptr : forall (b1 b2 : block) (ofs : int),
      mi b1 = Some (b2,0%Z) ->
      val_obs mi (Vptr b1 ofs) (Vptr b2 ofs)
  | obs_undef : val_obs mi Vundef Vundef.

  Inductive memval_obs_eq (f : meminj) : memval -> memval -> Prop :=
  | memval_obs_byte : forall n : byte,
      memval_obs_eq f (Byte n) (Byte n)
  | memval_obs_frag : forall (v1 v2 : val) (q : quantity) (n : nat)
                        (Hval_obs: val_obs f v1 v2),
      memval_obs_eq f (Fragment v1 q n) (Fragment v2 q n)
  | memval_obs_undef : memval_obs_eq f Undef Undef.
  
  (** Strong injection between memories *)
  Record mem_obs_eq (f : meminj) (mc mf : M) :=
    {
      weak_obs_eq : weak_mem_obs_eq f mc mf;
      perm_obs_strong :
        forall b1 b2 ofs (Hrenaming: f b1 = Some (b2,0%Z)),
          Mem.perm_order''
            (permission_at mf b2 ofs Cur)
            (permission_at mc b1 ofs Cur);
      val_obs_eq :
        forall b1 b2 ofs (Hrenaming: f b1 = Some (b2,0%Z))
          (Hperm: Mem.perm mc b1 ofs Cur Readable),
          memval_obs_eq f (Maps.ZMap.get ofs mc.(Mem.mem_contents)#b1)
                        (Maps.ZMap.get ofs mf.(Mem.mem_contents)#b2)}.
  
End MemObsEq.

Module InternalSteps.
  Import dry_context mySchedule DryMachine DryMachine.ThreadPool SEM.
  Import CoreLanguage.

  Section InternalSteps.
    
    Notation cstep := (cstep the_ge).
    Notation Sch := schedule.
    Context {cSpec : corestepSpec}.

    Variable initU: mySchedule.schedule.
    Definition coarse_semantics:=
      myCoarseSemantics.MachineSemantics initU.
    
  (** Internal steps are just thread coresteps or resume steps, they
  mimic fine-grained internal steps *)
  Definition internal_step {tid} {tp} m (cnt: containsThread tp tid)
             (Hcomp: mem_compatible tp m) tp' m' :=
    cstep cnt Hcomp tp' m' \/
    (myCoarseSemantics.resume_thread cnt tp' /\ m = m').

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
    intros. destruct Hstep as [Hcore | [Hresume ?]],
                              Hstep' as [Hcore' | [Hresume' ?]]; subst.
    - inversion Hcore; inversion Hcore'.
      unfold corestep_fun in *.
      subst. pf_cleanup.
      rewrite Hcode in Hcode0. inversion Hcode0. subst c0.
      assert (Heq: c' = c'0 /\ m' = m'').
        by (eapply corestep_det; eauto).
        destruct Heq; subst; auto.
    - inversion Hcore; inversion Hresume'; subst.
      pf_cleanup.
      rewrite Hcode in Hcode0. discriminate.
    - inversion Hresume; inversion Hcore'; subst;
      pf_cleanup. unfold getThreadC in *; rewrite Hcode in Hcode0.
      discriminate.
    - inversion Hresume; inversion Hresume'; subst.
      pf_cleanup. rewrite Hcode in Hcode0; inversion Hcode0; subst.
      rewrite Hafter_external in Hafter_external0.
        by inversion Hafter_external0.
  Qed.

  Lemma containsThread_internal_step :
      forall tp m tp' m' tid0 tid
        (Hcnt0: containsThread tp tid0)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step Hcnt0 Hcomp tp' m') 
        (Hcnt: containsThread tp tid),
        containsThread tp' tid.
    Proof.
      intros. inversion Hstep as [Htstep | [Htstep _]];
        inversion Htstep; subst;
        [ eapply corestep_containsThread; by eauto
        | by eapply cntUpdateC].
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
      intros. inversion Hstep as [Htstep | [Htstep _]];
        inversion Htstep; subst;
        [eapply corestep_containsThread'; eauto |
           by eapply cntUpdateC'; eauto].
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
    
    Corollary internal_step_compatible :
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_step pf Hcompatible tp' m'),
        mem_compatible tp' m'.
    Proof.
      intros.
      destruct Hstep as [Hdry | [Hresume ?]];
        [eapply dry_step_compatible | subst; eapply coarseResume_compatible];
        eauto.
    Qed.
    
    Lemma internal_step_invariant:
      forall (tp tp' : thread_pool) m m' (i : nat) (pf : containsThread tp i)
        (Hcompatible: mem_compatible tp m)
        (Hstep: internal_step pf Hcompatible tp' m'),
        invariant tp'.
    Proof.
      intros.
      destruct Hstep as [Hdry | Hresume].
      - inversion Hdry as [tp'0 c m1 m1' c']. subst m' tp'0 tp'.
        eapply corestep_invariant; eauto.
      - destruct Hresume as [Hresume Heq]; subst.
        inversion Hresume; subst.
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
      intros. destruct Hstep as [Hstep | [Hstep Heq]];
      inversion Hstep; subst;
      [erewrite <- gsoThreadCode with (cntj' := pfj')
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
      intros. destruct Hstep as [Hstep | [Hstep Heq]];
        inversion Hstep; subst;
        [erewrite <- @gsoThreadRes with (cntj' := pfj') |
         erewrite <- @gThreadCR with (cntj' := pfj')];
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
      inversion Hstep as [Hcstep | [Hrstep Heq]]; subst; auto.
      inversion Hcstep; subst; eapply corestep_disjoint_val;
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
      destruct Hstep as [Hcstep | [Hresume ?]]; subst.
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
    Qed.

    Lemma internal_step_valid:
      forall tp m tp' m' i (cnt: containsThread tp i)
        (Hcomp: mem_compatible tp m)
        (Hstep: internal_step cnt Hcomp tp' m') b
        (Hvalid: Mem.valid_block m b),
        Mem.valid_block m' b.
    Proof.
      intros.
      destruct Hstep as [Htstep | [_ ?]];
        [inversion Htstep; subst;
         eapply corestep_nextblock;
         by eauto | by subst].
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

  Import MemObsEq mySchedule CoreLanguage InternalSteps.
  Require Import sepcomp.closed_safety.
  Import dry_context mySchedule DryMachine DryMachine.ThreadPool SEM.
  
  Notation cstep := (cstep the_ge).
  Notation Sch := schedule.
  Notation cmachine_step := ((corestep coarse_semantics) the_ge).
  Notation fmachine_step := ((corestep fine_semantics) the_ge).
  Notation CoarseSem := coarse_semantics.
  Hint Unfold myCoarseSemantics.MachStep myFineSemantics.MachStep.
  
  (** Simulations between individual threads. *)
  
  (* Consider hiding thread_pool completely *)
  Definition weak_tsim {tpc tpf : thread_pool} (mc mf : Mem.mem)
             {i} (f: meminj) (pfc : containsThread tpc i)
             (pff : containsThread tpf i) (compc: mem_compatible tpc mc)
             (compf: mem_compatible tpf mf) : Prop :=
    weak_mem_obs_eq f (restrPermMap  (compc i pfc))
                    (restrPermMap (compf i pff)).
  
  Record strong_tsim {tpc tpf : thread_pool} (mc mf : Mem.mem) {i}
         (f: meminj) (pfc : containsThread tpc i)
         (pff : containsThread tpf i) (compc: mem_compatible tpc mc)
         (compf: mem_compatible tpf mf) : Prop :=
    { code_eq: getThreadC pfc = getThreadC pff;
      strong_obs: mem_obs_eq f (restrPermMap (compc i pfc))
                             (restrPermMap (compf i pff))
    }.

  
  (** Simulation relation between a "coarse-grain" 
     state and a "fine-grain" state *)
  
  Definition max_inv mf := forall b ofs, Mem.valid_block mf b ->
                                    permission_at mf b ofs Max = Some Freeable.

  (* simStrong now maintains the extra invariant that any new blocks
      from the internal execution are owned by thread tid. This is
     needed for the suspend_sim proof. Note that it's not possible
     to prove it just by the fact that only thread tid executes because
     1. some location may be allocated and then freed in this multistep
      execution and 2. our relation only strongly relates the final state
      of the execution not in-between states. *)

  Definition fpool tpc : Type :=
    forall i (cnti: containsThread tpc i), meminj.
      
  Record sim tpc mc tpf mf (xs : Sch) (f : meminj) (fp: fpool tpc) : Prop :=
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
                    (Hfib: (fp _ cnti) b = Some (b2,0%Z))
                    (Hfjb': (fp _ cntj) b' = Some (b2',0%Z)),
          b2 <> b2';
      simStrong:
        forall tid (pfc: containsThread tpc tid) (pff: containsThread tpf tid),
        exists tpc' mc', inject_incr f (fp _ pfc) /\
                       ([seq x <- xs | x == tid] = nil -> f = (fp _ pfc)) /\
                       internal_execution ([seq x <- xs | x == tid])
                                          tpc mc tpc' mc' /\
                       (forall (pfc': containsThread tpc' tid)
                         (mem_compc': mem_compatible tpc' mc'),
                           strong_tsim (fp _ pfc) pfc' pff mem_compc' mem_compf) /\
                       (forall tid2 (pff2: containsThread tpf tid2)
                          (Hneq: tid <> tid2) b1 b2 ofs,
                           (fp _ pfc) b1 = Some (b2,0%Z) ->
                           f b1 = None ->
                           (getThreadR pff2) # b2 ofs = None);
                           
      invF: invariant tpf;
      maxF: max_inv mf
    }.

  Arguments sim : clear implicits.


  (** Distinguishing the various step types of the concurrent machine *)

  Inductive StepType : Type :=
    Internal | Concurrent | Halted | Suspend.

  Definition ctlType (code : ctl) : StepType :=
    match code with
    | Krun c =>
      match at_external Sem c with
      | None => 
        match halted Sem c with
        | Some _ => Halted
        | None => Internal
        end
      | Some _ => Suspend
      end
    | Kstop c => Concurrent
    | Kresume c => Internal
    end.
  
  Definition getStepType {i tp} (cnt : containsThread tp i) : StepType :=
    ctlType (getThreadC cnt).

  Lemma internal_step_type :
    forall i tp tp' m m' (cnt : containsThread tp i)
      (Hcomp: mem_compatible tp m)
      (Hstep_internal: internal_step cnt Hcomp tp' m'),
      getStepType cnt = Internal.
  Proof.
    intros.
    unfold getStepType, ctlType.
    destruct Hstep_internal as [Hcstep | [Hresume Heq]].
    inversion Hcstep. subst. rewrite Hcode.
    assert (H1:= corestep_not_at_external Sem _ _ _ _ _ Hcorestep).
    rewrite H1.
    assert (H2:= corestep_not_halted Sem _ _ _ _ _ Hcorestep).
      by rewrite H2.
      inversion Hresume; subst.
      pf_cleanup. by rewrite Hcode.
  Qed.

  Notation "cnt '@'  'I'" := (getStepType cnt = Internal) (at level 80).
  Notation "cnt '@'  'E'" := (getStepType cnt = Concurrent) (at level 80).
  Notation "cnt '@'  'S'" := (getStepType cnt = Suspend) (at level 80).
  Notation "cnt '@'  'H'" := (getStepType cnt = Halted) (at level 80).

  (** Simulations Diagrams *)
  Definition sim_internal_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem)
      (xs : Sch) (f : meminj) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hinternal: pff @ I)
      (Hsim: sim tpc mc tpf mf xs f fp),
    exists tpf' mf' fp',
      (forall U, fmachine_step (i :: U, tpf) mf (U, tpf') mf') /\
      sim tpc mc tpf' mf' (i :: xs) f fp'.

  Definition sim_external_def :=
    forall (tpc tpf : thread_pool) (mc mf : Mem.mem)
      (xs : Sch) (f : meminj) (fp : fpool tpc) (i : NatTID.tid)
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
      (xs : Sch) (f : meminj) (fp : fpool tpc) (i : NatTID.tid)
      (pff: containsThread tpf i)
      (Hexternal: pff @ S)
      (Hsim: sim tpc mc tpf mf xs f fp),
    exists tpc' mc' tpf' mf' f' fp',
      (forall U, fmachine_step (i :: U, tpf) mf (U, tpf') mf') /\
      sim tpc' mc' tpf' mf' [seq x <- xs | x != i] f' fp'.

End SimDefs.

(** ** Proofs *)
Module SimProofs.

  Import MemObsEq mySchedule CoreLanguage InternalSteps.
  Require Import sepcomp.closed_safety.
  Import dry_context mySchedule DryMachine DryMachine.ThreadPool SEM StepLemmas.
  
  Import SimDefs.
  
  (** Solves absurd cases from fine-grained internal steps *)
    Ltac absurd_internal Hstep :=
      inversion Hstep; try inversion Htstep; subst; simpl in *;
      try match goal with
          | [H: value _ = Some _ |- _] => inversion H; subst
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
          forall cc cc' mc mf mc' f
            (Hobs_eq: mem_obs_eq f mc mf)
            (Hstep: corestep Sem the_ge cc mc cc' mc'),
          exists mf' f',
            corestep Sem the_ge cc mf cc' mf'
            /\ mem_obs_eq f' mc' mf'
            /\ inject_incr f f'
            /\ inject_separated f f' mc mf
            /\ (forall b1 b1' b2,
                  f b1 = None ->
                  f b1' = None ->
                  f' b1 = Some (b2,0%Z) ->
                  f' b1' = Some (b2,0%Z) ->
                  b1 = b1')
            /\ ((exists p, ((Mem.nextblock mc' = Mem.nextblock mc + p)%positive /\
                    (Mem.nextblock mf' = Mem.nextblock mf + p)%positive))
               \/ ((Mem.nextblock mc' = Mem.nextblock mc) /\
                  (Mem.nextblock mf' = Mem.nextblock mf))) (* NOTE: can this be just the difference?*)
            /\ (forall b,
                  Mem.valid_block mf' b ->
                  ~ Mem.valid_block mf b ->
                   let bz := ((Zpos b) - ((Zpos (Mem.nextblock mf)) -
                                          (Zpos (Mem.nextblock mc))))%Z in
                   f' (Z.to_pos bz) = Some (b,0%Z) /\
                   f (Z.to_pos bz) = None).

    (* /\ (exists g, forall b2, Mem.valid_block mf' b2 -> *)
            (*               ~ Mem.valid_block mf b2 -> *)
            (*               exists b1, g b2 = Some (b1,0%Z) *)
            (*                     /\ f' b1 = Some (b2,0%Z) *)
            (*                     /\ f b1 = None). *)

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
      destruct Hstep_internal as [Hcore | [Hresume Hmem]]; subst;
      autounfold;
      econstructor(simpl; eauto).
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
        rewrite Hnot_ext in Hstep_internal.
        destruct (halted Sem c); discriminate.
        rewrite Hcontra in Hcant. auto.
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
      unfold getStepType in isInternal.
      inversion Hstep; subst; try inversion Htstep; subst; simpl in *;
      try match goal with
          | [H: value _ = Some _ |- _] => inversion H; subst
          end; pf_cleanup;
      repeat match goal with
             | [H: getThreadC _ = _ |- _] =>
               rewrite H in isInternal; simpl in isInternal
             | [H1: match ?Expr with _ => _ end = _,
                    H2: ?Expr = _ |- _] => rewrite H2 in H1
             | [H: threadHalted _ |- _] =>
               inversion H; clear H; subst; pf_cleanup
             end; try discriminate; try (exfalso; by auto).
      exists Hcmpt. split; auto.
      right; auto.
      exists Hcmpt. split; auto.
      left; auto.
      destruct (at_external_halted_excl Sem c) as [Hext | Hcontra];
      [rewrite Hext in isInternal;
      destruct (halted Sem c); discriminate |
       rewrite Hcontra in Hcant; exfalso; by auto].
    Qed.

    (** Proofs about [fmachine_step]*)
    Lemma fstep_containsThread :
      forall tp tp' m m' i j
        (cntj: containsThread tp j)
        (Hstep: forall U, fmachine_step (i :: U, tp) m (U, tp') m'),
        containsThread tp' j.
    Proof.
      intros. specialize (Hstep empty).
      inversion Hstep; subst; try inversion Htstep;
      simpl in *; try inversion HschedN;
      subst; auto;
      (* the tactic below seems highly redundant but maybe it won't be
         if we make the modules opaque *)
      repeat match goal with
             | [ |- containsThread (updThreadC _ _) _] =>
               apply cntUpdateC; auto
             | [ |- containsThread (updThread _ _ _) _] =>
               apply cntUpdate; auto
             | [ |- containsThread (updThreadR _ _) _] =>
               apply cntUpdateR; auto
             | [ |- containsThread (addThread _ _ _) _] =>
               apply cntAdd; auto
             end.
    Qed.

    Lemma fstep_containsThread' :
      forall tp tp' m m' i j
        (cnti: containsThread tp i)
        (cntj: containsThread tp' j)
        (Hinternal: cnti @ I)
        (Hstep: forall U, fmachine_step (i :: U, tp) m (U, tp') m'),
        containsThread tp j.
    Proof.
      intros.
      specialize (Hstep empty).
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
      - constructor.
        intros i j cnti' cntj' Hneq.
        assert (cnti := @cntUpdateC' tid i tp (Krun c) Htid cnti').
        assert (cntj := @cntUpdateC' tid j tp (Krun c) Htid cntj').
        erewrite @gThreadCR with (cntj := cntj).
        erewrite @gThreadCR with (cntj := cnti);
          by auto.
        intros i cnti'.
        assert (cnti := @cntUpdateC' tid i tp (Krun c) Htid cnti').
        erewrite gsoThreadCLock.
          by erewrite gThreadCR with (cntj := cnti).
      - by eapply corestep_invariant; eauto.
    Qed.
    
    Lemma mem_compatible_setMaxPerm :
      forall tp m
        (Hcomp: mem_compatible tp m),
        mem_compatible tp (setMaxPerm m).
    Proof.
      intros tp m Hcomp.
      constructor;
        [intros i cnti b ofs | intros b ofs];
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
          destruct Hcomp as [Hltth Hltls]);
          [specialize (Hltth _ cnti b ofs)
          | specialize (Hltls b ofs)];
          rewrite getMaxPerm_correct in Hltth Hltls;
          unfold permission_at in *;
          rewrite Hinvalid in Hltth Hltls; simpl in *;
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
      absurd_internal Hstep.
      eapply updThreadC_compatible;
        by eauto.
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
        [by rewrite <- gThreadCR with (cntj' := pfj') |].
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
      absurd_internal Hstep.
      erewrite gsoThreadCC with (cntj' := pfj');
        by eauto.
      erewrite gsoThreadCode with (cntj' := pfj'); eauto.
    Qed.
    
    Hint Resolve fmachine_step_compatible fmachine_step_invariant
         fstep_containsThread fstep_containsThread' : fstep.

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
        [reflexivity | eapply corestep_disjoint_val; by eauto].
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
      forall (m m' : Mem.mem) (f : meminj)
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
      forall (m m' : Mem.mem) (f : meminj)
        (memObsEq: mem_obs_eq f m m')
        (pf: permMapLt (getCurPerm m) (getMaxPerm m))
        (pf': permMapLt (getCurPerm m') (getMaxPerm (setMaxPerm m'))),
        mem_obs_eq f (restrPermMap pf) (restrPermMap pf').
    Proof.
      intros.
      inversion memObsEq.
      assert (Hrestr := restrPermMap_correct pf).
      assert (Hrestr' :=
                restrPermMap_correct pf').
      constructor.
      - eapply weak_obs_eq_restr; eauto.
      - intros;
        destruct (Hrestr b1 ofs) as [_ Hcur];
        destruct (Hrestr' b2 ofs) as [_ Hcur'];
        rewrite Hcur Hcur';
        do 2 rewrite getCurPerm_correct; auto.
      - intros. unfold restrPermMap; simpl.
        eapply val_obs_eq0; eauto.
        unfold Mem.perm in *.
        destruct (Hrestr b1 ofs) as [_ Hcur].
        unfold permission_at in *.
        rewrite Hcur in Hperm.
        rewrite getCurPerm_correct in Hperm. assumption.
    Qed.

    Lemma weak_obs_eq_setMax:
      forall (f : meminj) (m m' : mem),
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
        inject_incr fi fi' /\
        (forall (pfc': containsThread tpc' i) (pff': containsThread tpf' i)
          (Hcompc': mem_compatible tpc' mc') (Hcompf': mem_compatible tpf' mf'),
            strong_tsim fi' pfc' pff' Hcompc' Hcompf') /\
        (forall j
           (pffj : containsThread tpf j),
            i <> j ->
            forall (b1 b2 : block),
              fi' b1 = Some (b2, 0%Z) ->
              fi b1 = None ->
              forall ofs, (getThreadR pffj) # b2 ofs = None).
    Proof.
      intros.
      assert (HinvC': invariant tpc')
        by (eapply internal_step_invariant; eauto).
      destruct Hstep_internal as [Hcstep | Hresume].
      { inversion Hcstep; subst; clear Hcstep.
        destruct Hstrong_sim as [Hcode_eq memObsEq].
        rewrite Hcode in Hcode_eq.
        assert (H' := Hcorestep).
        eapply corestep_obs_eq in Hcorestep; eauto.
        destruct Hcorestep
          as [mf' [fi' [HcorestepF [Hobs_eq' [Hincr [Hseparated Hinverse]]]]]].
        remember (restrPermMap (Hcompf _ pff)) as mf1 eqn:Hrestrict.
        symmetry in Hrestrict.
        remember (updThread pff (Krun c') (getCurPerm mf'))
          as tpf' eqn:Hupd.
        exists tpf' (setMaxPerm mf') fi'.
        split.
        { (* fine machine steps *)
          intros U. eapply myFineSemantics.core_step; simpl; eauto.
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
         intros j pffj Hij b1 b2 Hfi' Hfi ofs.
         specialize (Hseparated _ _ _ Hfi Hfi').
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
         simpl in Hlt. destruct ((getThreadR pffj) # b2 ofs); by tauto.
        }
      }
      { destruct Hresume as [Hresume Heq]; subst.
        inversion Hresume; subst; clear Hresume; pf_cleanup.
        destruct Hstrong_sim as [Hcode_eq memObsEq].
        rewrite Hcode in Hcode_eq.
        remember (updThreadC pff (Krun c')) as tpf' eqn:Hupd.
        exists tpf' mf fi.
        split.
        { (* The fine-grained machine steps *)
          intros. eapply myFineSemantics.resume_step; simpl; eauto.
          econstructor; eauto.
        }
        { split; first by auto.
          split; first by auto.
          split.
          - intros.
            constructor;
              first by (subst tpf';
                          by do 2 rewrite gssThreadCC).
            erewrite restrPermMap_irr with
            (Hlt' := Hcompf _ pff) by (subst; by erewrite @gThreadCR with (cntj := pff)).
            erewrite restrPermMap_irr; eauto.
              by rewrite gThreadCR.
          - intros j pffj Hij b1 b2 Hfi Hfi'.
            by congruence.
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
      (* Case of resume step*)
      intros b1 b2 ofs Hf.
      specialize (Hperm_obs_weak b1 b2 ofs Hf).
      do 2 rewrite restrPermMap_Cur.
      do 2 rewrite restrPermMap_Cur in Hperm_obs_weak.
      erewrite gThreadCR with (cntj := pffj).
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
               (fp: fpool tpc) (f' : meminj) :=
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
                       HsimWeak Hfpsep HsimStrong HinvF HmaxF].
      assert (pfc: containsThread tpc i)
        by (eapply HnumThreads; eauto).
      (* Strong simulation for thread i*)
      destruct (HsimStrong i pfc pff)
        as [tpc' [mc' [Hincr [Hsynced [Hexec [Htsim Hownedi]]]]]];
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
        by (assert (Hcodes := code_eq Htsim);
             unfold getStepType; by rewrite Hcodes).
      apply at_internal_cmachine_step with (cnt := pfc') in Hstep'; eauto.
      destruct Hstep' as [Hcomp [Hstep' Heq]]. subst U; pf_cleanup.
      (* And from this we derive safety for 1 step for fine-grained*)
      destruct (tsim_fstep_safe HmaxF HinvF Htsim Hstep')
        as [tpf' [mf' [fi' [HstepF [HmaxF' [Hincr' [Htsim' Howned']]]]]]].
      assert (pfc'': containsThread tpc'' i)
        by (eapply containsThread_internal_step; eauto).
      assert (pff': containsThread tpf' i)
        by (eapply (fstep_containsThread pff); eauto).
      assert (memCompC'': mem_compatible tpc'' mc'').
      eapply internal_step_compatible with (Hcompatible := memCompC'); eauto.
      assert (memCompF': mem_compatible tpf' mf')
        by (eapply fmachine_step_compatible with (pf := pff); eauto).
      exists tpf' mf' (updateFP pfc fp fi').
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
        assert (Hsepi: inject_separated (fp i pfc) fi' mc' mf) by admit.
        (*TODO: Lift this admit*)
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
          destruct (fp i pfc b) as [[b2'' ?]|] eqn:Hfi.
          assert (Heq:b2 = b2'' /\ z = 0%Z).
          apply Hincr' in Hfi. rewrite Hfi in Hfi';
                                 by inversion Hfi'.
          destruct Heq; subst b2'' z.
          eapply Hfpsep with (i := i) (j := j) (b := b); eauto.
          unfold inject_separated in Hsepi.
          specialize (Hsepi _ _ _ Hfi Hfi').
          destruct Hsepi as [HinvalidC' HinvalidF'].
          assert (pfj: containsThread tpf j) by admit.
          assert (Hsimj := (simStrong Hsim) j cntj pfj).
          destruct Hsimj as [tpcj' [mc'j [_ [_ [Hexecj [Htsimj _]]]]]].
          assert (pfj': containsThread tpcj' j)
            by (eapply containsThread_internal_execution; eauto).
          assert (HmemCompCj': mem_compatible tpcj' mc'j)
            by (eapply internal_execution_compatible with (tp := tpc); eauto).
          specialize (Htsimj pfj' HmemCompCj').
          assert (Hcodomain := codomain_valid (weak_obs_eq (strong_obs Htsimj))).
          specialize (Hcodomain _ _ Hfj).
          erewrite restrPermMap_valid in Hcodomain.
          intros Hcontra. subst. by auto.
        + pf_cleanup.
          rewrite gssFP.
          rewrite gsoFP; auto.
          intros b b' b2 b2' Hf Hf' Hfk' Hfj'.
          destruct (fp j cntj b') as [[b2'' z]|] eqn:Hfj.
          assert (Heq:b2' = b2'' /\ z = 0%Z)
            by (apply Hincr' in Hfj; rewrite Hfj in Hfj';
                  by inversion Hfj').
          destruct Heq; subst b2'' z.
          intros Hcontra.
          eapply Hfpsep with (i := j) (j := k) (b := b') (b' := b) (b2 := b2');
            by eauto.
          unfold inject_separated in Hsepi.
          specialize (Hsepi _ _ _ Hfj Hfj').
          destruct Hsepi as [HinvalidC' HinvalidF'].
          assert (pffk: containsThread tpf k) by admit.
          assert (Hsimk := (simStrong Hsim) k cntk pffk).
          destruct Hsimk as [tpck' [mck' [_ [_ [Hexeck [Htsimk _]]]]]].
          assert (pfck': containsThread tpck' k)
            by (eapply containsThread_internal_execution; eauto).
          assert (HmemCompCk': mem_compatible tpck' mck')
            by (eapply internal_execution_compatible with (tp := tpc); eauto).
          specialize (Htsimk pfck' HmemCompCk').
          assert (Hcodomain := codomain_valid (weak_obs_eq (strong_obs Htsimk))).
          specialize (Hcodomain _ _ Hfk').
          erewrite restrPermMap_valid in Hcodomain.
          intros Hcontra. subst. by auto.
        + rewrite gsoFP; auto.
          rewrite gsoFP; eauto.  
      - (** Proof of strong simulation between threads*)
        intros j pfcj pffj'.
        destruct (i == j) eqn:Heq; move/eqP:Heq=>Heq.
        { subst j. exists tpc'' mc''.
          pf_cleanup. rewrite gssFP.
          split;
            first by (eapply inject_incr_trans; eauto).
          split.
          - intros Hnostep.
            simpl in Hnostep. rewrite if_true in Hnostep.
            discriminate. apply eq_refl.
          - split.
            simpl. rewrite if_true.
            assert (Heq: i :: [seq x <- xs | x == i] =
                         [seq x <- xs | x == i] ++ [:: i]).
            { clear. induction xs. reflexivity.
              simpl. destruct (a==i) eqn:Heq; move/eqP:Heq=>Heq.
              subst. simpl. rewrite IHxs. reflexivity.
              auto.
            }
            rewrite Heq.
            eapply internal_execution_trans; by eauto.
              by apply eq_refl.
          - split; first by (intros; eapply Htsim').
            intros k pffk' Hik b1 b2 ofs Hfi' Hf.
            assert (pffk: containsThread tpf k)
              by (eauto with fstep).
            erewrite <- gsoThreadR_fstep with (pfj := pffk); eauto.
            destruct (valid_block_dec mc' b1) as [Hvalidmc'b1 | Hinvalidmc'b1].
            - assert (Hfb1 := (domain_valid (weak_obs_eq (strong_obs Htsim))) b1).
              erewrite restrPermMap_valid in Hfb1.
              destruct (Hfb1 Hvalidmc'b1) as [b2' Hfi].
              assert (b2' = b2)
                by (apply Hincr' in Hfi; rewrite Hfi in Hfi';
                    inversion Hfi'; by subst); subst.
                by eauto.
            - assert (Hfb1 := (domain_invalid
                                 (weak_obs_eq (strong_obs Htsim))) b1).
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
            as [tpcj' [mcj' [Hincrj [Hsyncedj [Hexecj [Htsimj Hownedj]]]]]].
          exists tpcj' mcj'. split; auto. split; [ by auto | split; auto].
          split.
          (* difficult part: simulation between tpf' and tpcj' *)
          intros pfcj' memCompCj'.
          specialize (Htsimj pfcj' memCompCj').
          inversion Htsimj as [code_eqjj memObsEqj].
          constructor;
            first by
              (rewrite code_eqjj;
                 by (eapply gsoThreadC_fstepI; eauto)).
          constructor. (*mem_obs_eq proof*)
          { constructor.
            - apply (domain_invalid (weak_obs_eq memObsEqj)).
            - apply (domain_valid (weak_obs_eq memObsEqj)).
            - assert (Hcodomain := (codomain_valid (weak_obs_eq memObsEqj))).
              intros b1 b2 Hfj.
              specialize (Hcodomain b1 b2 Hfj).
              admit. (*lift valid block for fmachine_step*)
            - by apply (injective (weak_obs_eq (strong_obs Htsimj))).
            - intros b1 b2 ofs.
              rewrite <- permission_at_fstep with
              (Hcomp := (mem_compf Hsim)) (U := empty) (i := i) (pfi := pff)
                                          (pfj := pffj)
                                          (Hcomp' := memCompF'); auto.
                by apply (perm_obs_weak (weak_obs_eq memObsEqj)).
          }
          { intros b1 b2 ofs.
            rewrite <- permission_at_fstep with
            (Hcomp := (mem_compf Hsim)) (i := i) (U := empty) (pfi := pff)
                                        (pfj := pffj) (Hcomp' := memCompF'); auto.
              by apply (perm_obs_strong memObsEqj).
          }
          { intros b1 b2 ofs Hfj Hperm. unfold restrPermMap. simpl.
            assert (Hval := val_obs_eq memObsEqj).
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
              assert (Hperm_strong := (perm_obs_strong memObsEqj) b1 b2 ofs Hfj).
              clear - Hperm Hperm_eqf Hperm_strong Hperm_weak.
              destruct Hsim; simpl in Hperm_strong, Hperm_weak; pf_cleanup.
              unfold permission_at in *.
              rewrite Hperm_eqf in Hperm_strong Hperm_weak.
              unfold Mem.perm_order'' in Hperm_strong, Hperm_weak.
              unfold Mem.perm, Mem.perm_order' in *. 
              destruct ((Mem.mem_access
                           (restrPermMap (memCompF' _ pffj'))) # b2 ofs Cur) eqn:?.
              - rewrite Hperm_eqf.
                destruct ((Mem.mem_access
                             (restrPermMap (memCompCj' _ pfcj')))
                            # b1 ofs Cur) eqn:?.
                eapply perm_order_trans; eauto.
                tauto.
              - rewrite Hperm_eqf.
                destruct ((Mem.mem_access (restrPermMap
                                             (memCompCj' _ pfcj')))
                            # b1 ofs Cur); auto.
            }
            specialize (HstepF empty).
            erewrite <- fmachine_step_disjoint_val with (tp := tpf)
            (i := i) (j := j) (m' := mf') (m := mf) (tp' := tpf') (U := empty);
              by eauto. 
          }
          (* block ownership *)
          intros k pffk' Hjk b1 b2 ofs Hfj Hf.
          assert (pffk: containsThread tpf k)
            by (eapply fstep_containsThread'; eauto).
            specialize (Hownedj _ pffk Hjk b1 b2 ofs Hfj Hf).
            destruct (i == k) eqn:Hik; move/eqP:Hik=>Hik.
            - subst k.
              assert (pfcj': containsThread tpcj' j)
                by (eapply containsThread_internal_execution; eauto).
              assert (Hcompcj': mem_compatible tpcj' mcj')
                by (eapply internal_execution_compatible with (tp := tpc) (m := mc);
                     eauto).
              specialize (Htsimj pfcj' Hcompcj').
              assert (Hcodomain := (codomain_valid (weak_obs_eq
                                                      (strong_obs Htsimj)))).
              specialize (Hcodomain _ _ Hfj).
              erewrite restrPermMap_valid in Hcodomain.
              specialize (HstepF empty).
              clear - Hownedj Hcodomain Hjk HstepF Hinternal HmemCompF.
              absurd_internal HstepF;
                first by erewrite gThreadCR with (cntj := Htid).
              apply corestep_decay in Hcorestep.
              apply decay_decay' in Hcorestep.
              destruct (Hcorestep b2 ofs) as [_ Hdecay_valid].
              assert (Hp := restrPermMap_Cur (HmemCompF _ Htid ) b2 ofs).
              unfold permission_at in Hp.
              destruct (Hdecay_valid Hcodomain) as [[Hcontra _]| Hstable].
              * rewrite Hp in Hcontra;
                  by congruence.
              * rewrite Hp in Hstable.
                rewrite Hownedj in Hstable.
                erewrite gssThreadRes.
                rewrite getCurPerm_correct. auto.
            - erewrite <- gsoThreadR_fstep with (pfi := pff) (pfj := pffk); eauto.
        }
        { (*invariant tpf' *)
          eapply fmachine_step_invariant with (tp := tpf); eauto.
        }
        { assumption.  }
        Grab Existential Variables. assumption. assumption. assumption.
        auto. auto. auto. auto. (*TODO: find out where these existentials come from*)
    Qed.

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
        inject_incr f f' /\
        inject_separated f f' m1 m1' /\
        (forall b1 b1' b2,
            f b1 = None ->
            f b1' = None ->
            f' b1 = Some (b2,0%Z) ->
            f' b1' = Some (b2,0%Z) ->
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
            f' (Z.to_pos bz) = Some (b,0%Z) /\
            f (Z.to_pos bz) = None) /\
        (exists (pf2j: containsThread tp2 j)
           (pf2j': containsThread tp2' j)
           (Hcomp2: mem_compatible tp2 m2)
           (Hcomp2': mem_compatible tp2' m2'),
            strong_tsim f' pf2j pf2j' Hcomp2 Hcomp2').
    Proof.
      intros.
      inversion Hstep as [Hcstep | [Hresume ?]].
      - inversion Hcstep; subst.
        inversion Hsim as [Hcode_eq Hmem_obs_eq].
        remember (getThreadC pf1j') as c1' eqn:Hcode'.
        subst c1'.
        rewrite Hcode in Hcode_eq.
        assert (H := corestep_obs_eq c c' m2 Hmem_obs_eq Hcorestep).
        destruct H
          as [m2' [f' [Hcorestep' [Hobs_eq [Hincr [Hseparated
                                                     [Hinjective [Hnextblock Hinverse]]]]]]]].
        exists (updThread pf1j' (Krun c') (getCurPerm m2')) m2' f'.
        assert (Hinternal':
                  internal_step pf1j' Hcomp1'
                                (updThread pf1j' (Krun c') (getCurPerm m2')) m2')
          by (left; econstructor; eauto).
        split; first by assumption.
        split; first by assumption.
        split; first by assumption.
        split; first by assumption.
        split; first by assumption.
        split; first by auto.
        assert (pf2j := containsThread_internal_step Hstep pf1j).
        assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
        assert (Hcomp2 := internal_step_compatible Hstep).
        assert (Hcomp2' := internal_step_compatible Hinternal').
        exists pf2j pf2j' Hcomp2 Hcomp2'.
        constructor; first by do 2 rewrite gssThreadCode.
        destruct Hobs_eq as [[Hinvalid' Hvalid' Hweak_perm] Hstrong_perm Hval].
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
        + (* strong_perm proof *)
          intros b1 b2 ofs Hf'.
          do 2 rewrite restrPermMap_Cur;
            do 2 rewrite gssThreadRes;
            do 2 rewrite getCurPerm_correct;
              by eauto.
        + (* val proof *)
          intros b1 b2 ofs Hf' Hreadable.
          simpl.
          eapply Hval; eauto.
          unfold Mem.perm in *.
          assert (H:= restrPermMap_Cur (Hcomp2 j pf2j) b1 ofs).
          unfold permission_at in H.
          rewrite H in Hreadable.
          rewrite gssThreadRes in Hreadable;
            rewrite getCurPerm_correct in Hreadable.
            by assumption.
      - (* Case internal step is a resume step*)
        subst m2.
        inversion Hsim as [Hcode_eq Hmem_obs_eq].
        inversion Hresume; subst.
        pf_cleanup. rewrite Hcode_eq in Hcode.
        exists (updThreadC pf1j' (Krun c')) m1' f.
        assert (Hinternal':
                  internal_step pf1j' Hcomp1' (updThreadC pf1j' (Krun c')) m1')
          by (right; split; econstructor; eauto).
        split;
          first by assumption.
        split; first by auto.
        split; first by congruence.
        split; first by congruence.
        split; first by auto.
        split; first by
            (intros; by exfalso).
        assert (pf2j := containsThread_internal_step Hstep pf1j).
        assert (pf2j' := containsThread_internal_step Hinternal' pf1j').
        assert (Hcomp2 := internal_step_compatible Hstep).
        assert (Hcomp2' := internal_step_compatible Hinternal').
        exists pf2j pf2j' Hcomp2 Hcomp2'.
        constructor; first by do 2 rewrite gssThreadCC.
        destruct Hmem_obs_eq
          as [[Hinvalid' Hvalid' Hcodomain Hinjective Hweak_perm] Hstrong_perm Hval].
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
          assert (H2:= restrPermMap_Cur (Hcomp2 j pf2j) b1 ofs).
          assert (H1:= restrPermMap_Cur (Hcomp1 j pf1j) b1 ofs).
          unfold permission_at in *.
          rewrite H2 in Hreadable.
          rewrite H1.
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
        inject_incr f f' /\
        inject_separated f f' m1 m1' /\
        (forall b1 b1' b2,
            f b1 = None ->
            f b1' = None ->
            f' b1 = Some (b2,0%Z) ->
            f' b1' = Some (b2,0%Z) ->
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
             f' (Z.to_pos bz) = Some (b,0%Z) /\
             f (Z.to_pos bz) = None) /\
        (exists (pf2j: containsThread tp2 j)
           (pf2j': containsThread tp2' j)
           (Hcomp2: mem_compatible tp2 m2)
           (Hcomp2': mem_compatible tp2' m2'),
            strong_tsim f' pf2j pf2j' Hcomp2 Hcomp2').
    Proof.
     intros.
      generalize dependent tp1.
      generalize dependent m1.
      generalize dependent f.
      generalize dependent tp1'. generalize dependent m1'.
      induction xs as [|x xs]; simpl; intros.
      - inversion Hexec; subst.
        exists tp1' m1' f.
        split; first by constructor.
        split; first by auto.
        split; first by congruence.
        split; first by congruence.
        split; first by auto.
        split; first by (intros; by exfalso).
        do 4 eexists; eauto.
        simpl in HschedN; inversion HschedN.
      - destruct (x == j) eqn:Hxj; move/eqP:Hxj=>Hxj.
        + subst x. inversion Hexec as [|tid U U' tp1a m1a tp0 m0].
          subst U U' tp1a m1a tp'' m''.
          simpl in Htrans. simpl in HschedN;
            inversion HschedN; subst tid; clear HschedN Hexec.
          pf_cleanup.
          assert (Htsim := strong_tsim_step Hinv Hsim Hstep).
          destruct Htsim as
              [tp0' [m0' [f0 [Hstep0'
                                [Hincr0' [Hsep0' [Hinjective0'
                                                    [Hnextblock0' [Hinverse0' Htsim0']]]]]]]]].
          destruct Htsim0' as [pfj' [pfj0' [Hcomp' [Hcomp0' Htsim0]]]].
          pf_cleanup.
          assert (Hinv0': invariant tp0')
            by (eapply internal_step_invariant; eauto).
          destruct (IHxs _ _ _ _ Hinv0' _ _ _ _ _ Htsim0 Htrans)
            as [tp2' [m2' [f2' [Hexec2 [Hincr2 [Hsep2 [Hinjective2
                                                         [Hnextblock2 [Hinverse2 Hsim2]]]]]]]]];
          exists tp2' m2' f2'.
          destruct Hsim2 as [pf2j [pf2j' [Hcomp2 [Hcomp2' Htsim2]]]].
          split; first by (econstructor; simpl; eauto).
          split; first by (eapply inject_incr_trans; eauto).
          split.
          { (*injection separated *)
            intros b1 b2 delta Hf Hf2'.
            unfold inject_separated in *.
            destruct (valid_block_dec m0 b1) as [Hvalidm0 | Hinvalidm0].
            * apply (domain_valid (weak_obs_eq (strong_obs Htsim0))) in Hvalidm0.
              destruct Hvalidm0 as [? Hf0].
              assert (b2 = x).
              {  assert (Hf2'' : f2' b1 = Some (x,0%Z))
                by (eapply Hincr2; eauto).
                 rewrite Hf2' in Hf2''. inversion Hf2''; by subst. }
              subst x.
              eapply Hsep0';
                by eauto.
            * apply (domain_invalid (weak_obs_eq (strong_obs Htsim0))) in Hinvalidm0.
              destruct (Hsep2 _ _ _ Hinvalidm0 Hf2') as [Hinvalid Hinvalidm0'].
              split;
                intros Hcontra;
                eapply internal_step_valid in Hcontra; eauto.
          }
          split.
          { (* injectivity for new blocks *)
            intros b1 b1' b2 Hf Hf' Hf2 Hf2'.
            destruct (valid_block_dec m0 b1) as [Hvalidm0 | Hinvalidm0];
              destruct (valid_block_dec m0 b1') as [Hvalidm0' | Hinvalidm0'].
            - apply (domain_valid (weak_obs_eq (strong_obs Htsim0))) in Hvalidm0.
              destruct Hvalidm0 as [b2' Hf0].
              apply (domain_valid (weak_obs_eq (strong_obs Htsim0))) in Hvalidm0'.
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
              
              apply (domain_valid (weak_obs_eq (strong_obs Htsim0))) in Hvalidm0.
              destruct Hvalidm0 as [b2' Hf0].
              apply (domain_invalid (weak_obs_eq (strong_obs Htsim0))) in Hinvalidm0'.
              unfold inject_separated in Hsep2.
              specialize (Hsep2 _ _ _ Hinvalidm0' Hf2').
              destruct Hsep2 as [? Hinvalidb2].
              assert (b2 = b2')
                by (eapply Hincr2 in Hf0; rewrite Hf0 in Hf2; inversion Hf2; by subst);
                subst b2'.
              apply (codomain_valid (weak_obs_eq (strong_obs Htsim0))) in Hf0.
              erewrite restrPermMap_valid in Hf0.
                by exfalso.
            - (* Proof: same as above with the roles of b1 and b1' exchanged *)
              
              apply (domain_valid (weak_obs_eq (strong_obs Htsim0))) in Hvalidm0'.
              destruct Hvalidm0' as [b2' Hf0].
              apply (domain_invalid (weak_obs_eq (strong_obs Htsim0))) in Hinvalidm0.
              unfold inject_separated in Hsep2.
              specialize (Hsep2 _ _ _ Hinvalidm0 Hf2).
              destruct Hsep2 as [? Hinvalidb2].
              assert (b2 = b2')
                by (eapply Hincr2 in Hf0; rewrite Hf0 in Hf2'; inversion Hf2'; by subst);
                subst b2'.
              apply (codomain_valid (weak_obs_eq (strong_obs Htsim0))) in Hf0.
              erewrite restrPermMap_valid in Hf0.
                by exfalso.
            - (* Proof: both b1 and b1' are not valid in m0, hence they are only
                  valid in m2, for which we have injectivity by induction hypothesis *)
              apply (domain_invalid (weak_obs_eq (strong_obs Htsim0))) in Hinvalidm0.
              apply (domain_invalid (weak_obs_eq (strong_obs Htsim0))) in Hinvalidm0'.
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
                destruct Expr as [[? ?]|] eqn:Hf
              end;
                [apply Hincr0' in Hf; by congruence | trivial].
          }
          by eauto.
      - destruct (IHxs _ _ _ _ Hinv _ _ _ _ _ Hsim Hexec)
            as [tp2' [m2' [f2' [Hexec2 [Hincr2 [Hsep2 [Hinjective2
                                                         [Hnextblock2 [Hinverse2 Hsim2]]]]]]]]];
          exists tp2' m2' f2'.
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
      exists (updThreadC pff (Kstop c)).
      split.
      econstructor; eauto.
      intros.
      constructor;
        first by do 2 rewrite gssThreadCC.
      erewrite restrPermMap_irr with (Hlt := Hcompc' tid pfc') (Hlt' := Hcmpt tid Htid)
        by (erewrite gThreadCR with (cntj := Htid); reflexivity).
      erewrite restrPermMap_irr with (Hlt := Hcompf' tid pff') (Hlt' := Hcompf tid pff)
        by (erewrite gThreadCR with (cntj := pff); reflexivity).
      assumption.
    Qed.

    (** Strong simulation with the id injection*)
    Lemma strong_tsim_id :
      forall tp tp' tp'' m m' i j xs
        (Hij: i <> j)
        (pfj: containsThread tp j)
        (pfj': containsThread tp' j)
        (pfj'': containsThread tp'' j)
        (pfi': containsThread tp' i)
        (Hcomp: mem_compatible tp m)
        (Hcomp'': mem_compatible tp'' m')
        (Hsuspend: myCoarseSemantics.suspend_thread pfi' tp'')
        (Hexec: internal_execution [seq x <- xs | x == i] tp m tp' m'),
        strong_tsim (fun b => if valid_block_dec m b then Some (b,0%Z) else None)
                    pfj pfj'' Hcomp Hcomp''.
    Proof.
      constructor.
      - (* codes are equal*)
        assert (Hcode := gsoThreadC_suspendC pfj' pfj'' Hij Hsuspend).
        rewrite <- Hcode.
          by erewrite gsoThreadC_exec with (pfj' := pfj'); eauto.
      - (* mem_obs_eq *)
        constructor.
        + (*weak_mem_obs_eq*)
          constructor.
          * (*invalid domain of fid*)
            intros b Hinvalid.
            destruct (valid_block_dec m b) as [Hcontra | ?];
              [unfold Mem.valid_block in *;
                rewrite restrPermMap_nextblock in Hinvalid;
                  by exfalso | by reflexivity].
          * (*valid domain of fid*)
            intros b Hvalid.
              by destruct (valid_block_dec m b);
              [exists b; by reflexivity | unfold Mem.valid_block in *;
                   rewrite restrPermMap_nextblock in Hvalid; by exfalso].
          * (*codomain of fid *)
            intros b1 b2 Hfid.
            destruct (valid_block_dec m b1); simpl in Hfid;
            try discriminate.
            inversion Hfid; subst.
            erewrite restrPermMap_valid.
            eapply internal_execution_valid; by eauto.
          * (*fid is injective*)
            intros b1 b1' b2 Hfb1 Hfb1'.
            destruct (valid_block_dec m b1), (valid_block_dec m b1');
              simpl in Hfb1, Hfb1';
              [rewrite <- Hfb1 in Hfb1'; inversion Hfb1'; auto| | |];
                by discriminate.
          * (* Permissions of memc are higher than memc''*)
            intros b1 b2 ofs Hfid.
            destruct (valid_block_dec m b1); simpl in Hfid;
            try discriminate.
            inversion Hfid; subst.
            do 2 rewrite restrPermMap_Cur.
            erewrite <- gsoThreadR_suspendC with
            (cntj' := pfj'') (cntj := pfj') by eauto.
            erewrite <- gsoThreadR_execution with (pfj' := pfj')
                                                   (pfj := pfj); eauto.
            destruct ((getThreadR pfj) # b2 ofs); simpl;
              by constructor.
        + (* Permissions of memc'' are higher than mc*)
          intros b1 b2 ofs Hfid.
          destruct (valid_block_dec m b1); simpl in Hfid;
          try discriminate.
          inversion Hfid; subst.
          do 2 rewrite restrPermMap_Cur.
          erewrite <- gsoThreadR_suspendC with
          (cntj' := pfj'') (cntj := pfj') by eauto.
          erewrite <- gsoThreadR_execution with (pfj' := pfj')
                                                 (pfj := pfj); eauto.
          destruct ((getThreadR pfj) # b2 ofs); simpl;
            by constructor.
        + (* j-Values of mc and mc'' are equal up to injection*)
          intros b1 b2 ofs Hfid Hreadable.
          destruct (valid_block_dec m b1); simpl in Hfid;
          try discriminate.
          inversion Hfid; subst.
          simpl.
          erewrite <- internal_exec_disjoint_val
          with (tp := tp) (xs := xs) (tp' := tp') (m' := m'); eauto.
          destruct (Maps.ZMap.get ofs (Mem.mem_contents m) # b2);
            constructor.
          destruct v0; try constructor.
          admit. (* need the mem_wd invariant to show this*)
            by eapply containsThread_internal_execution'; eauto.
    Qed.
    
    Lemma le_sub:
      forall x y z,
        (x < z)%positive ->
        (z <= y)%positive ->
        (x <= Z.to_pos (Z.pos_sub y (z - x)))%positive.
    Admitted.
    
    Lemma sim_suspend : sim_suspend_def.
    Proof.
      unfold sim_suspend_def.
      intros.
      inversion Hsim as
          [HnumThreads HmemCompC HmemCompF HsafeC HsimWeak Hfpsep HsimStrong HinvF HmaxF].
      assert (pfc: containsThread tpc i)
        by (eapply HnumThreads; eauto).
      destruct (HsimStrong i pfc pff)
        as [tpc' [mc' [Hincr [Hsynced [Hexec [Htsim Hownedi]]]]]];
        clear HsimStrong.
      assert (pfc': containsThread tpc' i)
        by (clear - Hexec pfc; eapply containsThread_internal_execution in pfc; eauto).
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
        by (assert (Hcodes := code_eq Htsim);
             unfold getStepType; by rewrite Hcodes).
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
      exists tpc'' mc'' tpf' mf.
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
                       (Z.pos b1 - (Z.pos (Mem.nextblock mc'') - Z.pos (Mem.nextblock mc)))%Z in
                   (fp j cntj) (Z.to_pos bz)
                 end
               end).
      split.
      { (* the fine-grained machine takes a suspend step *)
        intros U; eapply myFineSemantics.suspend_step; simpl; eauto.
      }
      { (* The simulation between tpc'' and tpf' is retained. *)
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
            apply (domain_invalid (weak_obs_eq (strong_obs Htsim))).
          }
          { (* Inside the domain of fi *)
            apply (domain_valid (weak_obs_eq (strong_obs Htsim))).
          }
          { (* Valid codomain*)
            apply (codomain_valid (weak_obs_eq (strong_obs Htsim))).
          }
          { (* Injective fi*)
            apply (injective (weak_obs_eq (strong_obs Htsim))).
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
                erewrite <- permission_at_execution with (xs := xs) (tp := tpc);
                  eauto.
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
          { subst j. exists tpc'' mc''.
            split; auto. split; auto. split; auto.
            assert (Hempty: [seq x <- [seq x <- xs | x != i] | x == i] = nil).
            { clear. induction xs as [|x xs]; first by reflexivity.
              simpl; destruct (x == i) eqn:Heq;
              simpl; first by assumption.
              erewrite if_false
                by (apply/eqP; intro Hcontra; subst;
                      by move/eqP:Heq=>Heq).
                by assumption.
            }
            rewrite Hempty. by constructor.
            split; first by auto.
              by congruence.
          }
          { (*case j <> i *)
            assert (pffi': containsThread tpf' i)
              by (eapply suspendF_containsThread with (cnti := pff); eauto).
            specialize (Htsim' memCompC'' memCompF' pfci'' pffi').
            assert (pfc'j: containsThread tpc' j)
              by (eapply suspendC_containsThread with (cnti := pfc'); eauto).
            assert (pfcj: containsThread tpc j)
              by (eapply containsThread_internal_execution'; eauto).
            
            (* The original <tpc, mc> strongly injects into <tpc'',mc''> where
               <tpc, mc> -->i <tpc', mc'> -->iS <tpc'',mc'>  with the id map*)
            assert (Hsim_c_ci: strong_tsim (fun b => if valid_block_dec mc b then
                                                    Some (b,0%Z) else None)
                                           pfcj pfcj'' HmemCompC memCompC'')
              by (eapply strong_tsim_id with (pfi' := pfc'); eauto).
            
            assert (pffj: containsThread tpf j)
              by (eapply suspendF_containsThread; eauto).
            assert (Htsimj := (simStrong Hsim) j pfcj pffj).
            (* executing the internal steps for thread j gives us a strong 
             * simulation between the coarse and fine-grained states. *)
            destruct Htsimj as
                [tpcj [mcj [Hincrj [Hsyncedj [Hexecj [Htsimj Hownedj]]]]]].
            (* by the strong simulation on mc and mc'' (via id) we can
              obtain a strong simulation between mcj and mcj', where
              mcj' mc -->i --> mci -->j mcj' *)
            assert (Hinv'': invariant tpc'')
              by (eapply suspendC_invariant with (tp := tpc');
                   [eapply internal_execution_invariant with (tp := tpc); eauto | eauto]).
            assert (Hsimjj':= strong_tsim_execution xs Hinv'' Hsim_c_ci Hexecj).
            destruct Hsimjj'
              as [tpcj' [mcj' [fij [Hexecij
                                      [Hincr' [Hsep [Hinjective
                                                         [Hnextblockj' [Hinverse Hsimjj']]]]]]]]].
            destruct Hsimjj' as [pfcjj [pfij [Hcompjj [Hcompij Hsimij]]]].
            pf_cleanup.
            (* notice that mcj and mcj' will be equal up to nextblock mc
             * (mcj injects to mcj' with id up to nextblock mc). Hence
             * for blocks smaller than nb mc we follow the fj injection to mf
             * for blocks between nb mc and nb mc'' we follow the fi injection
             * and for blocks after that we follow the fj one after taking
             * the inverse. (TODO: point to a diagram) *)
            (*TODO: comment deprecated*)
            specialize (Htsimj pfcjj Hcompjj).
            specialize (HsimWeak _ pfc pff).
            exists tpcj' mcj'.
            split.
            { (* fi is included in f' *)
              intros b1 b2 delta Hfi.
              destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
              - assert (Hf_val := (domain_valid HsimWeak) b1).
                specialize (Hf_val
                              ((proj2 (restrPermMap_valid
                                         (HmemCompC i pfc) b1)) Hvalidmc)).
                destruct Hf_val as [b2' Hf_val].
                assert (Heq: b2 = b2' /\ delta = 0%Z)
                  by (apply Hincr in Hf_val;
                       rewrite Hf_val in Hfi; inversion Hfi; by subst);
                  destruct Heq;
                  subst b2' delta.
                  by assumption.
              - destruct (valid_block_dec mc'' b1) as [Hvalidmc'' | Hinvalidmc''];
                first by assumption.
                destruct (valid_block_dec mcj' b1) as [Hvalidmcj' | Hinvalidmcj'];
                  assert (Hcontra := domain_invalid (weak_obs_eq (strong_obs Htsim')));
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
              - destruct (valid_block_dec mcj' b) as [Hvalidmcj' | Hinvalidmcj'];
                first by reflexivity.
                assert (Hinvdomain := domain_invalid (weak_obs_eq (strong_obs Htsim))).
                assert (Hinvalidmcji': ~ Mem.valid_block (restrPermMap (memCompC' i pfc')) b)
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
                  erewrite proof_irr with (a1 := (containsThread_internal_execution'
                                                    Hexec
                                                    (proj2 (suspendC_containsThread j HsuspendC) pfcj'')))
                                          (a2 := pfcj).
                    by auto.
                + rewrite Heq. rewrite Z.pos_sub_diag. simpl.
                  apply (domain_invalid HsimWeak) in Hinvalidmc.
                  erewrite proof_irr with (a1 := (containsThread_internal_execution'
                                                    Hexec
                                                    (proj2 (suspendC_containsThread j HsuspendC) pfcj'')))
                                            (a2 := pfcj);
                    by auto.
            } split.
            { (* tpc'' can step in a fine grained way for thread j *)
                by rewrite filter_neq_eq.
            } split.
            { (*strong simulation between mcj' and mf' *)
              intros pfcj' Hcompcj'. pf_cleanup.
              constructor.
              - assert (Hctlij := code_eq Hsimij).
                assert (Hctljj := code_eq Htsimj).
                subst.
                rewrite Hctlij in Hctljj.
                erewrite <- gsoThreadC_suspendF with (cntj := pffj) (cntj' := pffj');
                  by eauto.
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
                  unfold inject_incr in Hincr'.
                  specialize (Hincr' b1 b1 0%Z).
                  destruct (valid_block_dec mc b1); try by exfalso.
                  simpl in Hincr'.
                  specialize (Hincr' (Logic.eq_refl _)).
                  assert (HpermC_lt :=
                            (perm_obs_weak (weak_obs_eq (strong_obs Hsimij)))
                              b1 b1 ofs Hincr').
                  assert (HpermC_gt :=
                            (perm_obs_strong (strong_obs Hsimij))
                              b1 b1 ofs Hincr').
                  eapply perm_order_antisym; eauto.
                }
                (* j-permissions of mcj are higher than mf*)
                assert (HpermF_mcj :=
                          perm_obs_weak (weak_obs_eq (strong_obs Htsimj))).

                (* also j-permissions of mcj are lower than mf*)
                assert (Hpermmcj_F := perm_obs_strong (strong_obs Htsimj)).
                
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
                            permission_at (restrPermMap (HmemCompC _ pfcj)) b1 ofs Cur = None).
                  { apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs) in Hinvalidmc.
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
                           fp i pfc b1 = Some (b2, 0%Z) ->
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
                           fij b1' = Some (b1, 0%Z) ->
                           permission_at (restrPermMap (Hcompjj j pfcjj))
                                         b1' ofs Cur =
                           permission_at (restrPermMap (Hcompij j pfij))
                                         b1 ofs Cur).
                { intros b1' b1 ofs Hfij. 
                  assert (Hperm_lt :=
                            (perm_obs_weak (weak_obs_eq (strong_obs Hsimij)))
                              b1' b1 ofs Hfij).
                  assert (Hperm_gt :=
                            (perm_obs_strong ((strong_obs Hsimij)))
                              b1' b1 ofs Hfij).
                  eapply perm_order_antisym; eauto.
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
                    + assert (Hle: (Mem.nextblock mc <= Mem.nextblock mc'')%positive)
                        by admit.
                      apply Pos.lt_eq_cases in Hle.
                      destruct Hle as [Hlt | Heq].
                      * apply Pos.le_nlt in Hinvalidmc''. apply Pos.le_nlt in Hinvalidmc.
                        assert (Hinvalid':
                                  (Mem.nextblock mc <=
                                   Z.to_pos (Z.pos_sub b (Mem.nextblock mc'' -
                                                          Mem.nextblock mc)))%positive)
                          by (eapply le_sub; eauto).
                        apply Pos.le_nlt in Hinvalid'.
                        apply (domain_valid (weak_obs_eq (strong_obs Hsimij))) in Hvalidmcj.
                        apply (domain_invalid (weak_obs_eq (strong_obs Hsim_c_ci ))) in Hinvalid'.
                        destruct Hvalidmcj as [b2 Hfij].
                        rewrite Z.pos_sub_gt in Hfij; auto.
                        assert (Hinvalid2 := Hsep _ _ _ Hinvalid' Hfij).
                        assert (Hvalidb2 :=
                                  (codomain_valid (weak_obs_eq (strong_obs Hsimij))) _ _ Hfij).
                        erewrite restrPermMap_valid in Hvalidb2.
                        destruct Hinvalid2 as [_ Hinvalidb2''].
                        specialize (Hinverse _ Hvalidb2 Hinvalidb2'').
                        simpl in Hinverse.
                        destruct Hinverse as [Hcontra _].
                        assert (Heq_contra :=
                                  (injective (weak_obs_eq (strong_obs Hsimij)))
                                    _ _ _ Hfij Hcontra).
                        assert (Heq : b = b2).
                        { rewrite Z.pos_sub_gt in Heq_contra.
                          simpl in Heq_contra.
                          apply Z2Pos.inj_iff in Heq_contra.
                          rewrite Z.pos_sub_gt in Heq_contra.
                          rewrite Z.pos_sub_gt in Heq_contra.
                          inversion Heq_contra as [Heq_contra2].
                          apply Pos.compare_eq_iff in Heq_contra2.
                          rewrite Pos.sub_compare_mono_r in Heq_contra2.
                            by apply Pos.compare_eq_iff.
                            admit.
                            admit.
                            admit. admit.
                            rewrite Z.pos_sub_gt; auto.
                            apply Pos2Z.is_pos.
                            admit.
                            rewrite Z.pos_sub_gt; auto.
                            apply Pos2Z.is_pos.
                            admit.
                            auto.
                        } subst b. by exfalso.
                      * rewrite Heq in Hvalidmcj.
                        rewrite Z.pos_sub_diag in Hvalidmcj.
                        simpl in Hvalidmcj.
                        rewrite Heq. rewrite Z.pos_sub_diag.
                        simpl.
                        apply (domain_valid (weak_obs_eq (strong_obs Hsimij))) in Hvalidmcj.
                        apply (domain_invalid (weak_obs_eq (strong_obs Hsim_c_ci ))) in Hinvalidmc.
                        destruct Hvalidmcj as [b2 Hfij].
                        assert (Hinvalid2 := Hsep _ _ _ Hinvalidmc Hfij).
                        assert (Hvalidb2 :=
                                  (codomain_valid (weak_obs_eq (strong_obs Hsimij))) _ _ Hfij).
                        erewrite restrPermMap_valid in Hvalidb2.
                        destruct Hinvalid2 as [_ Hinvalidb2''].
                        specialize (Hinverse _ Hvalidb2 Hinvalidb2'').
                        simpl in Hinverse.
                        destruct Hinverse as [Hcontra _].
                        rewrite Heq in Hcontra.
                        rewrite Z.pos_sub_diag in Hcontra.
                        simpl in Hcontra.
                        assert (Heq_contra :=
                                  (injective (weak_obs_eq (strong_obs Hsimij)))
                                    _ _ _ Hfij Hcontra).
                        subst. by exfalso.
                    + apply (domain_invalid (weak_obs_eq (strong_obs Htsimj))) in Hinvalidmcj.
                      erewrite proof_irr with
                      (a1 := (containsThread_internal_execution'
                                Hexec (proj2 (suspendC_containsThread j HsuspendC) pfcj'')))
                        (a2 := pfcj).
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
                                          (weak_obs_eq (strong_obs Htsim'))) b1).
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
                        { apply (domain_valid (weak_obs_eq (strong_obs Htsimj))) in Hvalidmcj.
                          erewrite proof_irr with
                          (a1 := containsThread_internal_execution'
                                   Hexec (proj2 (suspendC_containsThread j HsuspendC) pfcj''))
                            (a2 := pfcj).
                            by assumption.
                        }
                        { apply (domain_invalid (weak_obs_eq (strong_obs Hsimij))) in Hinvalidmcj.
                          by congruence.
                        }
                  - (* valid codomain of f'*)
                    intros b1 b2 Hf'.
                    assert (Hfj_codomain := codomain_valid (weak_obs_eq (strong_obs Htsimj))).
                    assert (Hfi_codomain := codomain_valid (weak_obs_eq (strong_obs Htsim))).
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
                    erewrite proof_irr with 
                    (a1 := (containsThread_internal_execution'
                              Hexec (proj2 (suspendC_containsThread j HsuspendC) pfcj'')))
                      (a2 := pfcj) in Hf'.
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
                          eapply (injective (weak_obs_eq (strong_obs Htsim))); eauto.
                        + (* case b1' is in mcj' or invalid *)
                          (* we can derive a contradiction by the fact
                          that the inverse of b1' will be a block that
                          is invalid in mc, and that fpj maps it to
                          the same block as b1 which is valid in mc,
                          using injectivity of fpj*)
                          clear - Hfb1' Hfb1 Hincrj Htsimj Hvalidmc Hexec
                                        Hinvalidmc''' Hinvalidmc'.
                          erewrite proof_irr
                          with (a1 := (containsThread_internal_execution'
                                         Hexec (proj2 (suspendC_containsThread j HsuspendC) pfcj'')))
                                 (a2 := pfcj) in Hfb1'.
                          apply Hincrj in Hfb1.
                          assert (Hnb: (Mem.nextblock mc <= Mem.nextblock mc'')%positive)
                            by admit.
                          apply Pos.le_lteq in Hnb.
                          destruct Hnb as [Hlt | Hnbeq].
                          * rewrite Z.pos_sub_gt in Hfb1'; auto. simpl in Hfb1'.
                            apply Pos.le_nlt in Hinvalidmc'''.
                            assert (Hinvalid: (Mem.nextblock mc
                                               <=
                                               Z.to_pos (Z.pos_sub b1' (Mem.nextblock mc''
                                                                        - Mem.nextblock mc)))%positive)
                              by (eapply le_sub; eauto).
                            apply Pos.le_nlt in Hinvalid.
                            assert (Hcontra:= (injective
                                                 (weak_obs_eq (strong_obs Htsimj)))
                                                _ _ _ Hfb1 Hfb1').
                            subst b1.
                              by exfalso.
                          * rewrite Hnbeq in Hfb1'.
                            rewrite Z.pos_sub_diag in Hfb1'.
                            simpl in Hfb1'.
                            assert (Hcontra := (injective (weak_obs_eq (strong_obs Htsimj)))
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
                          first by (eapply (injective (weak_obs_eq (strong_obs Htsim))); eauto).
                          (* the inverse of b1' will be in invalid in
                          mc (fresh in mcj). Hence by seperation
                          between fpj and fpi it must be that b2 <>
                          b2, contradiction. *)
                          clear - Hfb1' Hfb1 Htsimj Hfpsep Hinvalidmc Hexec
                                        Hinvalidmc' Hinvalidmci' HsimWeak Hij.
                          exfalso.
                          apply (domain_invalid HsimWeak) in Hinvalidmc.
                          erewrite proof_irr
                          with (a1 := (containsThread_internal_execution'
                                         Hexec (proj2 (suspendC_containsThread j HsuspendC)
                                                      pfcj'')))
                                 (a2 := pfcj) in Hfb1'.
                          assert (Hnb: (Mem.nextblock mc <= Mem.nextblock mc'')%positive)
                            by admit.
                          apply Pos.le_lteq in Hnb.
                          destruct Hnb as [Hlt | Hnbeq].
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
                                          Hinvalidmc' Hinvalidmci Hvalidmci' HsimWeak Hij.
                            exfalso.
                            apply (domain_invalid HsimWeak) in Hinvalidmc'.
                            erewrite proof_irr
                            with (a1 := (containsThread_internal_execution'
                                           Hexec (proj2 (suspendC_containsThread j HsuspendC)
                                                        pfcj'')))
                                   (a2 := pfcj) in Hfb1.
                            assert (Hnb: (Mem.nextblock mc <= Mem.nextblock mc'')%positive)
                              by admit.
                            apply Pos.le_lteq in Hnb.
                            destruct Hnb as [Hlt | Hnbeq].
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
                            erewrite proof_irr
                            with (a1 := (containsThread_internal_execution'
                                           Hexec (proj2 (suspendC_containsThread j HsuspendC)
                                                        pfcj'')))
                                   (a2 := pfcj) in Hfb1, Hfb1'.
                            assert (Heq := (injective (weak_obs_eq (strong_obs Htsimj)))
                                               _ _ _ Hfb1 Hfb1').
                            assert (Hnb: (Mem.nextblock mc <= Mem.nextblock mc'')%positive)
                              by admit.
                            apply Pos.le_lteq in Hnb.
                            destruct Hnb as [Hlt | Hnbeq].
                            * rewrite Z.pos_sub_gt in Heq; auto.
                              simpl in Heq.
                              apply Z2Pos.inj in Heq.
                              rewrite Z.pos_sub_gt in Heq.
                              rewrite Z.pos_sub_gt in Heq.
                              inversion Heq as [Heq2].
                              apply Pos.compare_eq_iff in Heq2.
                              rewrite Pos.sub_compare_mono_r in Heq2.
                            by apply Pos.compare_eq_iff.
                            admit.
                            admit.
                            admit. admit.
                            rewrite Z.pos_sub_gt; auto.
                            apply Pos2Z.is_pos.
                            admit.
                            rewrite Z.pos_sub_gt; auto.
                            apply Pos2Z.is_pos.
                            admit.
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
                      simpl; by constructor.
                      (*case it's a block that's invalid in mc'' *)
                      destruct (valid_block_dec mcj')
                        as [Hvalidmcj' | Hinvalidmcj']; try discriminate.
                      specialize (Hinverse b1 Hvalidmcj' Hinvalidmc'').
                      destruct Hinverse as [b1' [Hg [Hfij Hfid]]].
                      rewrite Hg in Hf'.
                      specialize (HpermF_mcj b1' b2 ofs Hf').
                      specialize (Hpermmcj_F b1' b2 ofs Hf').
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
                }
                { (* strong_perm_obs *)
                  intros b1 b2 ofs Hf'.
                  (* the permissions of mf' and mf are the same,
                     suspend step does not touch the memory*)
                  rewrite restrPermMap_Cur.
                    erewrite <- gsoThreadR_suspendF
                  with (cntj := pffj) (cntj' := pffj'); eauto.
                  rewrite <- restrPermMap_Cur with (Hlt := mem_compf Hsim _ pffj).
                  destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc].
                  - (* b is a valid block in mc*)
                    specialize (HpermC_mc_block _ ofs Hvalidmc).
                    specialize (Hpermmcj_F _ _ ofs Hf').
                    rewrite <- HpermC_mc_block in Hpermmcj_F.
                      by assumption.
                  - destruct (valid_block_dec mc'' b1)
                      as [Hvalidmc'' | Hinvalidmc''].
                    + (* b1 is an i-block (allocated by thread i) *)
                      specialize (Hpermj_mcj' _ ofs Hinvalidmc Hvalidmc'').
                      rewrite Hpermj_mcj'.
                      match goal with
                      | [|- Mem.perm_order'' ?Expr _] =>
                        destruct Expr
                      end; simpl; auto.
                    + destruct (valid_block_dec mcj' b1) as [Hvalidmcj'|?];
                      try discriminate.
                      specialize (Hinverse b1 Hvalidmcj' Hinvalidmc'').
                      destruct Hinverse as [b1' [Hg [Hfij _]]].
                      rewrite Hg in Hf'.
                      specialize (Hpermmcj_mcj' _ _ ofs Hfij).
                      rewrite <- Hpermmcj_mcj'.
                        by eauto.
                }
                { (* val_obs_eq *)
                  intros b1 b2 ofs Hf' Hreadable.
                  simpl.
                  assert (Hvalmcj_mcj' := val_obs_eq (strong_obs Hsimij));
                    simpl in Hvalmcj_mcj'.
                  assert (Hvalmcj_mf := (val_obs_eq (strong_obs Htsimj)));
                    simpl in Hvalmcj_mf. 
                  destruct (valid_block_dec mc b1) as [Hvalidmc | Hinvalidmc]
                                                        eqn:Hvalidmcdec.
                  - (* Value of a block that is valid in mc *)
                    (* Idea: this block is mapped between mcj and mcj' by id
                       and from mcj to mf by fj. Hence we can reuse fj *)
                    assert (Hincr'_b1 := Hincr' b1 b1 0%Z).
                    rewrite Hvalidmcdec in Hincr'_b1. simpl in Hincr'_b1.
                    specialize (Hincr'_b1 (Logic.eq_refl _)).
                    assert (Hvalmcj_mcj'_b1 := Hvalmcj_mcj' _ _ ofs Hincr'_b1).
                    assert (Hvalmcj_mf_b1 := Hvalmcj_mf _ _ ofs Hf').
                    unfold Mem.perm in Hreadable, Hvalmcj_mcj'_b1, Hvalmcj_mf_b1.
                    assert (Hreadable' := Hpermmcj_mcj' _ _ ofs Hincr'_b1).
                    unfold permission_at in Hreadable'.
                    rewrite <- Hreadable' in Hreadable.
                    specialize (Hvalmcj_mf_b1 Hreadable).
                    specialize (Hvalmcj_mcj'_b1 Hreadable).
                    inversion Hvalmcj_mcj'_b1 as
                        [n Hn_mcj Hn_mcj' | vj vj' q1 n Hval_obsjj' Hvj Hvj'| Hundef_mcj Hmv_mcj'].
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
                      { assert (Hincr'_bpj1 := Hincr' bpj1 bpj1 0%Z).
                        rewrite Hdecbpj1 in Hincr'_bpj1. simpl in Hincr'_bpj1.
                        specialize (Hincr'_bpj1 (Logic.eq_refl _)).
                        rewrite Hincr'_bpj1 in Hfijp; inversion Hfijp; subst bpj'2.
                        clear Hfijp.
                        rewrite Hdecbpj1. by assumption.
                      }
                      { (* here it is usefulto have inject seperation for fij*)
                        unfold inject_separated in Hsep.
                        specialize (Hsep bpj1 bpj'2 0%Z).
                        rewrite Hdecbpj1 in Hsep.
                        simpl in Hsep. specialize (Hsep (Logic.eq_refl _) Hfijp).
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
                        destruct Hinverse as [b0 [Hg [Hfij0 Hfid0]]].
                        rewrite Hg.
                        clear HpermC_mc_block HpermF_mcj Hpermmcj_F Hpermj_mc'' Hreadable'
                              Hreadable   Hpermmcj_mcj'   Hpermj_eqF    Hvj'.
                        (* NOTE: i need injectivity for the newly
                           (Separated) blocks. So fij bpj1 =  fij b0
                           imply b0 = bpj1. This is possible *)
                        clear Hdecbpj1.
                        apply (domain_invalid (weak_obs_eq (strong_obs Hsim_c_ci)))
                          in Hinvalidmcbpj1.
                        specialize (Hinjective _ _ _ Hfid0 Hinvalidmcbpj1 Hfij0 Hfijp).
                        subst b0. by assumption.
                        apply (codomain_valid (weak_obs_eq (strong_obs Hsimij))) in Hfijp.
                        erewrite restrPermMap_valid in Hfijp. by exfalso.
                      }
                      rewrite <- Hundef_mcj in Hvalmcj_mf_b1.
                      inversion Hvalmcj_mf_b1.
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
                    destruct (valid_block_dec mcj' b1) as [Hvalidmcj' | ?];
                      try discriminate.
                    destruct (Hinverse _ Hvalidmcj' Hinvalidmc'') as [b0 [Hg [Hfij _]]].
                    rewrite Hg in Hf'.
                    assert (Hpermeq := Hpermmcj_mcj' _ _ ofs Hfij).
                    assert (Hreadable': Mem.perm (restrPermMap (Hcompjj j pfcjj))
                                                 b0 ofs Cur Readable)
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
                      { assert (Hincr'_bpj1 := Hincr' bpj1 bpj1 0%Z).
                        rewrite Hdecbpj1 in Hincr'_bpj1. simpl in Hincr'_bpj1.
                        specialize (Hincr'_bpj1 (Logic.eq_refl _)).
                        rewrite Hincr'_bpj1 in Hfijp; inversion Hfijp; subst bpj'2.
                        clear Hfijp.
                        rewrite Hdecbpj1. by assumption.
                      }
                      { (* here it is usefulto have inject seperation for fij*)
                        unfold inject_separated in Hsep.
                        specialize (Hsep bpj1 bpj'2 0%Z).
                        rewrite Hdecbpj1 in Hsep.
                        simpl in Hsep. specialize (Hsep (Logic.eq_refl _) Hfijp).
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
                        destruct Hinverse as [b0' [Hg' [Hfij0' Hfid0']]].
                        rewrite Hg'.
                        (* NOTE: i need injectivity for the newly
                           (Separated) blocks. So fij bpj1 and fij
                           imply b0 = bpj1. I can have that *)
                        clear Hdecbpj1.
                        apply (domain_invalid (weak_obs_eq (strong_obs Hsim_c_ci)))
                          in Hinvalidmcbpj1.
                        specialize (Hinjective _ _ _ Hfid0' Hinvalidmcbpj1 Hfij0' Hfijp).
                        subst b0'. by assumption.
                        apply (codomain_valid (weak_obs_eq (strong_obs Hsimij))) in Hfijp.
                        erewrite restrPermMap_valid in Hfijp. by exfalso.
                      }
                      rewrite <- Hundef_mcj in Hvalmcj_mf.
                      inversion Hvalmcj_mf.
                        by constructor.
                } 
            }
            { (* Proof that block ownership is preserved*)
              subst f'.
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
                destruct (valid_block_dec mcj' b1) as [Hvalidmcj' | Hinvalidmcj'].
                destruct (Hinverse _ Hvalidmcj' Hinvalidmc'') as [b0 [Hg [Hfij ?]]].
                rewrite Hg in Hf'.
                unfold inject_separated in Hsep.
                specialize (Hsep _ _ _ H Hfij).
                destruct Hsep as [Hinvalidb0 _].
                apply (domain_invalid HsimWeak) in Hinvalidb0.
                assert (pffk: containsThread tpf k)
                  by (eapply suspendF_containsThread with (cnti := pff); eauto).
                specialize (Hownedj _ pffk Hjk _ _ ofs Hf' Hinvalidb0).
              erewrite <- gsoThreadR_suspendF with (cntj := pffk); eauto.
              by discriminate.
            }
          }
          }
        { (* Proof that the fine grained invariant is preserved *)
            by eapply suspendF_invariant with (pff := pff); eauto.
        }
        { (* Proof the max_inv is preserved *)
            by auto.
        }
      }
    Qed.

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
        U = U' /\ conc_call the_ge cnti Hcomp tp' m'.
    Proof.
      intros.
      inversion Hstep;
        try inversion Htstep; subst; simpl in *;
        try match goal with
            | [H: value _ = Some _ |- _] => inversion H; subst
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
    Definition projectAngelStrong (f : meminj)
               (deltaMap : delta_map) (init : delta_map): delta_map :=
      Maps.PTree.fold (fun acc b bperm =>
                         match f b with
                         | Some (b',_) =>
                           Maps.PTree.set b' bperm acc
                         | None =>
                           acc end)
                      deltaMap init.

    Definition projectAngel (f : meminj) (deltaMap : delta_map) : delta_map :=
      projectAngelStrong f deltaMap (Maps.PTree.empty _).

    Definition isProjection (f : meminj) (deltaMap deltaMap' : delta_map) : Prop :=
      forall b b' ofs,
        f b = Some (b', ofs) ->
        Maps.PTree.get b deltaMap = Maps.PTree.get b' deltaMap'.

    Definition isProjectionStrong (init : delta_map) (f : meminj) (deltaMap deltaMap' : delta_map) : Prop :=
      forall b b' ofs fd,
        f b = Some (b', ofs) ->
        (Maps.PTree.get b deltaMap = Some fd ->
        Maps.PTree.get b' deltaMap' = Some fd) /\
        (Maps.PTree.get b deltaMap = None ->
        Maps.PTree.get b' deltaMap' = Maps.PTree.get b' init).

    Lemma projectAngel_correct:
      forall f deltaMap,
        isProjection f deltaMap (projectAngel f deltaMap).
    Proof.
      intros.
      eapply Maps.PTree_Properties.fold_rec with (P := isProjection f).
      { intros dmap dmap' a Heq Hprojection. intros b b' ofs Hf.
        specialize (Heq b). rewrite <- Heq.
        unfold isProjection in Hprojection. eauto.
      }
      { unfold isProjection.
        intros;
          by do 2 rewrite Maps.PTree.gempty.
      }
      { intros dmap a bnew fnew Hget_dmap Hget_delta Hprojection.
        intros b b' ofs Hf.
        
        destruct (Pos.eq_dec b bnew) as [Heq | Hneq].
        - subst bnew. rewrite Maps.PTree.gss.
          rewrite Hf.
            by rewrite Maps.PTree.gss.
        - rewrite Maps.PTree.gso; auto.
          unfold isProjection in Hprojection.
          destruct (f bnew) eqn:Hfnew.
          destruct p.
          
          Focus 2.
          eauto.
          destruct (Pos.eq_dec b' b0).
          subst b0. rewrite Maps.PTree.gss.
          specialize (
      
    Lemma projectAngelStrong_correct:
      forall f deltaMap deltaMap' init
        (Hproject: projectAngelStrong f deltaMap init = deltaMap'),
        isProjectionStrong init f deltaMap deltaMap'.
    Proof.
      intros.
      rewrite <- Hproject. clear Hproject.
      eapply Maps.PTree_Properties.fold_rec with (P := isProjectionStrong init f).
      { intros. intros b b' ofs fd Hf.
        specialize (H0 b b' ofs fd Hf). destruct H0.
        split. rewrite <- H. eauto.
        rewrite <- H; auto. }
      { intros b b' ofs fd Hf.
        split. rewrite Maps.PTree.gempty. by discriminate.
        auto.
      }
      { intros dmap dmap' b1 fd1 Hget_dmap Hget_deltaMap Hproject_dmap.
        rewrite Hget_deltaMap.
        intros b b' ofs fd Hf. split.
        - intros Hget_dmap'.
          destruct (Pos.eq_dec b b1) as [Heq | Hneq].
          + subst b1. rewrite Maps.PTree.gss in Hget_dmap'. inversion Hget_dmap'; subst.
            rewrite Hf. by rewrite Maps.PTree.gss.
          + rewrite Maps.PTree.gso in Hget_dmap'; auto.
            destruct (f b1) as [[b1' ofs']|] eqn:Hfb1.
            
            destruct (Hproject_dmap b1 b1' ofs' fd1 Hfb1) as [_ IH].
            specialize (IH Hget_dmap).
            rewrite Hget_deltaMap.
            destruct (f b1). destruct p.
            
            
      unfold projectAngelStrong in Hproject.
      rewrite  Maps.PTree.fold_spec in Hproject.
      unfold Maps.PTree.elements in Hproject.    
      generalize dependent deltaMap'.
      generalize dependent init.
      induction deltaMap as [|deltaMap1 IH1 o deltaMap2 IH2]; intros.
      - rewrite <- Hproject.
        intros b b' ofs Hf. split.
        intros Hcontra.
        rewrite Maps.PTree.gleaf in Hcontra;
          by discriminate.
        auto.
      - rewrite Maps.PTree.xelements_node in Hproject. 
        do 2 rewrite List.fold_left_app in Hproject.
        
        
    
    Lemma sim_external: sim_external_def.
    Proof.
      unfold sim_external_def.
      intros.
      inversion Hsim as
          [HnumThreads HmemCompC HmemCompF HsafeC HsimWeak HsimStrong HinvF HmaxF].
      (* Thread i is in the coarse-grained machine*)
      assert (pfc: containsThread tpc i)
        by (eapply HnumThreads; eauto).
      (* Since thread i is synced, the coarse machine doesn't need to take any steps*)
      apply @not_in_filter with (xs := xs) in Hsynced.
      destruct (HsimStrong i pfc pff)
        as [fi [tpc' [mc' [Hincr [Hsyncf [Hexec [Htsim Hownedi]]]]]]];
        clear HsimStrong.
      (* Hence tpc = tpc' and mc = mc' *)
      rewrite Hsynced in Hexec.
      assert (Heq: tpc = tpc' /\ mc = mc')
        by (inversion Hexec; subst; auto; simpl in HschedN; discriminate).
      destruct Heq; subst tpc' mc'; clear Hexec.
      (* And also f won't change, i.e. f = fi *)
      specialize (Hsyncf Hsynced); subst fi.
      clear Hincr.
      (* By safety, the coarse-grained machine can step for all schedules *)
      specialize (HsafeC (mySchedule.buildSched (i :: nil)) 1).
      simpl in HsafeC. destruct HsafeC as [[[U tpc'] [mc' HstepC]] _].
      (* We know there is a strong simulation for thread i*)
      specialize (Htsim pfc HmemCompC).
      assert (HinvC: invariant tpc)
             by admit.
      assert (HexternalC: pfc @ E)
        by (assert (Hcodes := code_eq Htsim);
             unfold getStepType; by rewrite Hcodes).
       
      (* An external step pops the schedule and executes a concurrent call *)
      assert (Heq : empty = U /\ conc_call the_ge pfc HmemCompC tpc' mc')
        by (eapply external_step_inverse; eauto).
      destruct Heq as [? HconcC]; subst U; clear HstepC.
      exists tpc' mc'.
      (* We proceed by case analysis on the concurrent call *)
      destruct HconcC.
      { (* Lock Acquire *)

      assert (memCompC'': mem_compatible tpc'' mc'')
        by (eapply suspendC_compatible; eauto).
      assert (HstepF := strong_tsim_stop HinvF Htsim Hstep' Hstop_pfc').
      destruct HstepF as [tpf' [HstepF Htsim']].
      assert (memCompF': mem_compatible tpf' mf)
        by (eapply suspendF_compatible; eauto).
      exists tpc'' mc'' tpf' mf.
      (* since thread i commits, the new global renaming will be fi *)
      exists fi.
      split.
      { (* the fine-grained machine takes a suspend step *)
        intros U; eapply myFineSemantics.suspend_step; simpl; eauto.
      }
      { (* The simulation between tpc'' and tpf' is retained. *)
        eapply Build_sim with (mem_compc := memCompC'') (mem_compf := memCompF').
        { (* number of threads *)
          clear - HnumThreads Hexec HsuspendC HstepF.
          intros j. assert (Hpffj := suspendF_containsThread j HstepF).
          assert (Hpfcj' := suspendC_containsThread j HsuspendC).
 
            
End SimProofs.

