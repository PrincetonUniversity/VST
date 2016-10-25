(** * Spinlock well synchronized and spinlock clean*)
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
Require Import compcert.common.Events.
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.permjoin_def.
Require Import concurrency.concurrent_machine.
Require Import concurrency.memory_lemmas.
Require Import concurrency.dry_context.
Require Import concurrency.fineConc_safe.
Require Import concurrency.executions.
Require Import Coqlib.
Require Import msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module SpinLocks (SEM: Semantics)
       (Machines: MachinesSig with Module SEM := SEM)
       (AsmContext: AsmContext SEM Machines).
  Import Machines DryMachine ThreadPool AsmContext.
  Import event_semantics.
  Import Events.
  Module Executions := Executions SEM Machines AsmContext.
  Import Executions.

  Section Spinlocks.

    Hypothesis EM: ClassicalFacts.excluded_middle.

    (** True if two events access at least one common byte*)
    Definition sameLocation ev1 ev2 :=
      match Events.location ev1, Events.location ev2 with
      | Some (b1, ofs1, size1), Some (b2, ofs2, size2) =>
        b1 = b2 /\ exists ofs, Intv.In ofs (ofs1, (ofs1 + Z.of_nat size1)%Z) /\
                         Intv.In ofs (ofs2, (ofs2 + Z.of_nat size2)%Z)
      | _,_ => False
      end.

    (** Competing Events *)

    (** Actions that may compete*)
    Definition caction (ev : Events.machine_event) :=
      match ev with
      | internal _ (event_semantics.Write _ _ _) => Some Write
      | internal _ (event_semantics.Read _ _ _ _) => Some Read
      | internal _ (event_semantics.Alloc _ _ _) => None
      | internal _ (event_semantics.Free _) => None
      | external _ (release _ _ _) => Some Release
      | external _ (acquire _ _ _) => Some Acquire
      | external _ (mklock _) => Some Mklock
      | external _ (freelock _) => Some Freelock
      | external _ (spawn _ _ _) => None
      | external _ (failacq _) => Some Failacq
      end.

    (** Two events compete if they access the same location, from a
    different thread. *)

    (*this definition allows reads and writes to compete with release/acq - wrong*)
    (*Definition competes (ev1 ev2 : Events.machine_event) : Prop :=
      thread_id ev1 <> thread_id ev2 /\
      sameLocation ev1 ev2 /\
      caction ev1 /\ caction ev2 /\
      (caction ev1 = Some Write \/
       caction ev2 = Some Write \/
       caction ev1 = Some Mklock \/
       caction ev2 = Some Mklock \/
       caction ev1 = Some Freelock \/
       caction ev2 = Some Freelock). *)

    (* this definition allows makelock/freelock to compete with
    freelock/makelock, that's probably desired*)
    Definition competes (ev1 ev2 : Events.machine_event) : Prop :=
      thread_id ev1 <> thread_id ev2 /\ (* different threads*)
      sameLocation ev1 ev2 /\ (* same location *)
      caction ev1 /\ (* both are competing type*)
      caction ev2 /\ 
      (is_internal ev1 ->
       is_internal ev2 ->
       (** if they are both internal, at least one of them is a Write*)
       action ev1 = Write \/ action ev2 =  Write) /\
      (is_external ev1 \/ is_external ev2 ->
       (** if one of them is external, then at least one of them is a Mklock or
       freelock*)
       action ev1 = Mklock \/ action ev1 = Freelock
       \/ action ev2 = Mklock \/ action ev2 = Freelock).
    
    (** Spinlock well synchronized*)
    Definition spinlock_synchronized (tr : SC.event_trace) :=
      forall i j ev1 ev2,
        i < j ->
        List.nth_error tr i = Some ev1 ->
        List.nth_error tr j = Some ev2 ->
        competes ev1 ev2 ->
        (exists u v eu ev,
          i < u < v < j /\
          List.nth_error tr u = Some eu /\
          List.nth_error tr v = Some ev /\
          action eu = Release /\ action ev = Acquire /\
          location eu = location ev) \/
        (** we also consider spawn operations to be synchronizing*)
        (exists u eu,
            i < u < j /\
            List.nth_error tr u = Some eu /\
            action eu = Spawn).
    
    (** Spinlock clean*)
    Definition spinlock_clean (tr : FineConc.event_trace) :=
      forall i j evi evj
        (Hij: i < j)
        (Hi: List.nth_error tr i = Some evi)
        (Hj: List.nth_error tr j = Some evj)
        (Hmklock: action evi = Mklock)
        (Hfreelock: forall u evu, i < u < j ->
                             List.nth_error tr u = Some evu ->
                             action evu <> Freelock \/
                             location evu <> location evi)
        (Hlocation: sameLocation evj evi),
        action evj <> Write /\ action evj <> Read.

    (** After a step that generates a [mklock] event at [address] addr, addr
  will be in the [lockRes] and thread i will have lock permission on addr*)
    Lemma Mklock_lockRes:
      forall i U tr tp m tp' m' addr
        (Hstep: FineConc.MachStep
                  the_ge (i :: U, tr, tp) m
                  (U, tr ++ [:: external i (Events.mklock addr)], tp') m'),
        lockRes tp' addr /\
        forall (cnti': containsThread tp' i),
          ((getThreadR cnti').2 !! (addr.1)) addr.2 = Some Writable.
    Proof.
      intros.
      inv Hstep; simpl in *;
      try (apply app_eq_nil in H4; discriminate).
      apply app_inv_head in H5.
      destruct ev; simpl in *; discriminate.
      apply app_inv_head in H5;
        inv H5.
      (** case it's an external step that generates a mklock event*)
      inv Htstep.
      rewrite gsslockResUpdLock; split; auto.
      intros cnti'.
      rewrite gLockSetRes gssThreadRes.
      rewrite <- Hlock_perm.
      erewrite setPermBlock_same by (simpl; omega).
      reflexivity.
    Qed.

    (** [True] whenever some resource in [tp] has above [Readable] lock-permission on [laddr]*)
    Definition isLock tp laddr :=
      (exists i (cnti: containsThread tp i),
          Mem.perm_order'' ((getThreadR cnti).2 !! (laddr.1) laddr.2) (Some Readable)) \/
      (exists laddr' rmap, lockRes tp laddr' = Some rmap /\
                      Mem.perm_order'' (rmap.2 !! (laddr.1) laddr.2) (Some Readable)).


    (** If no freelock event is generated by a step, locks are
    preserved*)
    Lemma remLockRes_Freelock:
      forall i U tr tr' tp m tp' m' addr
        (Hlock: lockRes tp addr)
        (HisLock: isLock tp addr)
        (Hstep: FineConc.MachStep
                  the_ge (i :: U, tr, tp) m
                  (U, tr ++ tr', tp') m')
        (Hev: forall u ev, nth_error tr' u = Some ev ->
                      action ev <> Freelock \/
                      location ev <> Some (addr, lksize.LKSIZE_nat)),
        lockRes tp' addr /\
        isLock tp' addr.
    Proof.
      intros.
      inv Hstep; simpl in *;
      try (inversion Htstep;
            subst tp');
      try (rewrite gsoThreadCLPool; auto);
      try (rewrite gsoThreadLPool; auto);
      try subst tp'0; try subst tp''.
      - (** [threadStep] case*)
        split; auto.
        unfold isLock in *.
        inv HschedN.
        destruct HisLock as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + left.
          pose proof (cntUpdate (Krun c') (getCurPerm m'0, (getThreadR Htid).2) Htid cntj) as cntj'.
          exists j, cntj'.
          destruct (tid == j) eqn:Hij;
            move/eqP:Hij=>Hij;
                           subst;
                           [rewrite gssThreadRes | erewrite @gsoThreadRes with (cntj := cntj) by eauto];
                           simpl; pf_cleanup; auto.
        + right.
          exists laddr', rmap'.
          rewrite gsoThreadLPool.
          split; eauto.
      - unfold isLock in *.
        inv HschedN.
        destruct HisLock as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + specialize (Hangel2 b (Int.intval ofs)).
          pose proof (cntUpdate (Kresume c Vundef) newThreadPerm Htid
                                (cntUpdateL (b, Int.intval ofs) (empty_map, empty_map) cntj)) as cntj'.
          destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij.
          * subst. pf_cleanup.
            apply permjoin_order in Hangel2.
            destruct Hangel2.
            destruct (EqDec_address (b, Int.intval ofs) addr); subst.
            rewrite gssLockRes; split; auto.
            (*TODO: return here*)
            
          erewrite gsoLockRes by eauto.
          rewrite gsoThreadLPool; auto.
      - destruct (EqDec_address (b, Int.intval ofs) addr); subst.
        rewrite gssLockRes; auto.
        erewrite gsoLockRes by eauto.
        rewrite gsoThreadLPool; auto.
      - rewrite gsoAddLPool; subst tp_upd.
        rewrite gsoThreadLPool; auto.
      - destruct (EqDec_address (b, Int.intval ofs) addr); subst.
        rewrite gssLockRes; auto.
        erewrite gsoLockRes by eauto.
        rewrite gsoThreadLPool; auto.
      - (** Interesting case: freelock *)
        apply app_inv_head in H5; subst.
        specialize (Hev 0 (external tid (freelock (b, Int.intval ofs)))
                        ltac:(reflexivity)).
        simpl in Hev.
        destruct Hev; first by exfalso.
        erewrite gsolockResRemLock
          by (intros Hcontra; subst; auto).
        rewrite gsoThreadLPool; auto.
      - assumption.
      - subst tp'; auto.
      - subst tp'; auto.
    Qed.
    
    (*TODO: Move to some library *)
    Lemma nth_error_app:
      forall {A:Type} i (ys xs : list A),
        nth_error xs i = nth_error (ys ++ xs) (length ys + i).
    Proof.
      intros A i ys.
      generalize dependent i.
      induction ys; intros.
      - simpl. rewrite add0n.
        reflexivity.
      - simpl.
        eauto.
    Qed.

    (** If some address is a lock and there is no event of type
  Freelock at this address in some trace tr then the address is still
  a lock at the resulting state *)
    Lemma remLockRes_Freelock_execution:
      forall U U' tr tr' tp m tp' m' addr
        (Hlock: lockRes tp addr)
        (Hstep: fine_execution (U, tr, tp) m
                               (U', tr ++ tr', tp') m')
        (Hfreelock: forall (u : nat) (evu : machine_event),
            nth_error tr' u = Some evu ->
            action evu <> Freelock \/
            location evu <> Some (addr, lksize.LKSIZE_nat)),
        lockRes tp' addr.
    Proof.
      induction U; intros.
      - inversion Hstep.
        rewrite <- app_nil_r in H3 at 1.
        apply app_inv_head in H3; subst.
        assumption.
      - inversion Hstep.
        + rewrite <- app_nil_r in H3 at 1.
          apply app_inv_head in H3; subst;
          assumption.
        + subst.
          apply app_inv_head in H6. subst.
          eapply remLockRes_Freelock in H8; eauto.
          specialize (IHU U' (tr ++ tr'0) tr'' tp'0 m'0 tp' m' addr H8).
          rewrite <- app_assoc in IHU.
          specialize (IHU H9).
          eapply IHU.
          intros u evu Hnth''.
          erewrite nth_error_app with (ys := tr'0) in Hnth''.
          eauto.
          intros.
          erewrite <- nth_error_app1 with (l' := tr'') in H.
          eauto.
          eapply nth_error_Some.
          intros Hcontra; congruence.
    Qed.

    (** Permissions of addresses that are valid and not freeable do
    not change by internal steps*)
    Lemma ev_elim_nonempty_stable:
      forall m m' b ofs es
        (Hvalid: Mem.valid_block m b)
        (Hperm: Mem.perm_order'' (Some Nonempty)
                                 (permission_at m b ofs Cur))
        (Helim: ev_elim m es m'),
        permission_at m b ofs Cur = permission_at m' b ofs Cur.
    Proof.
      intros.
      generalize dependent m.
      induction es as [|ev es]; intros.
      - inversion Helim; subst; auto.
      - simpl in Helim.
        destruct ev;
          try (destruct Helim as [m'' [Haction Helim']]).
        + pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Haction b ofs) as Heq.
          do 2 rewrite getCurPerm_correct in Heq.
          rewrite Heq.
          rewrite Heq in Hperm.
          eapply IHes; eauto.
          eapply Mem.storebytes_valid_block_1; eauto.
        + destruct Helim; eauto.
        + pose proof (MemoryLemmas.permission_at_alloc_1
                        _ _ _ _ _ _ ofs Haction Hvalid Cur) as Heq.
          rewrite Heq. rewrite Heq in Hperm.
          eapply IHes; eauto.
          eapply Mem.valid_block_alloc; eauto.
        + assert (Hlt: ~ Mem.perm m b ofs Cur Freeable).
          { intros Hcontra.
            unfold Mem.perm in Hcontra.
            simpl in Hperm. unfold permission_at in *.
            destruct ((Mem.mem_access m) !! b ofs Cur); inv Hperm;
            simpl in Hcontra; inversion Hcontra.
          }
          pose proof (MemoryLemmas.permission_at_free_list_1 _ _ _ _ _
                                                             Haction Hlt Cur) as Heq.
          rewrite Heq. rewrite Heq in Hperm.
          eapply IHes; eauto.
          pose proof (freelist_forward _ _ _ Haction) as Hfwd.
          destruct (Hfwd _ Hvalid); auto.
    Qed.

    (** Spinlock clean for a single step*)
    Lemma fstep_clean:
      forall U U' tp m addr tr pre ev post tp' m' tidi
        (Hlock: lockRes tp addr)
        (Hlocation: sameLocation ev (external tidi (mklock addr)))
        (Hstep: FineConc.MachStep the_ge (U, tr, tp) m
                                  (U', tr ++ pre ++ [:: ev] ++ post, tp') m'),
        action ev <> Write /\ action ev <> Read.
    Proof.
      intros.
      inversion Hstep; simpl in *;
      try match goal with
          | [H: ?X = app ?X ?Y |- _] =>
            rewrite <- app_nil_r in H at 1;
              apply app_inv_head in H
          end; subst;
      try match goal with
          | [H: nth_error [::] _ = _ |- _] =>
            rewrite nth_error_nil in H;
              discriminate
          end;
      try match goal with
          | [H: [::] = ?X ++ (_ :: _) |- _] =>
            destruct X; simpl in H; congruence
          end.
      { (** Case of internal step *)
        (*NOTE: Should spinlock clean also mention free and alloc?*)
        inversion Htstep; subst.
        apply app_inv_head in H5.
        apply ev_step_elim in Hcorestep.
        destruct Hcorestep as [Helim _].
        apply list_append_map_inv in H5.
        destruct H5 as (mpre & mpost & Hpre & Hevpost & Hev0).
        destruct mpost as [|mev mpost];
          simpl in Hevpost; first by discriminate.
        inv Hevpost.
        apply ev_elim_split in Helim.
        destruct Helim as (m2 & ? & Helim_ev).
        unfold sameLocation in Hlocation.
        destruct (location (internal tid mev))
          as [[[b1 ofs1] size1]|] eqn:Haccessed_loc; try by exfalso.
        (** Case location function is defined, i.e. for writes and reads*)
        simpl in Hlocation.
        destruct addr as [bl ofsl].
        destruct Hlocation as [Hb [ofs' [Hintv Hintvl]]].
        (** [ofs'] is the exact offset which both events access*)
        subst.
        (** hence the lockpool will have [Writable] permission on
          [address] (bl, ofs') *)
        eapply lockSet_spec_2 with (ofs' := ofs') in Hlock; eauto.
        (** and thus all threads will have at most [Nonempty]
          permission on this [address]*)
        assert (Hperm:
                  Mem.perm_order'' (Some Nonempty)
                                   ((getThreadR Htid) !! bl ofs')).
        { destruct Hinv as [_ Hinv _ _].
          specialize (Hinv tid Htid bl ofs').
          destruct Hinv as [pu Hpu].
          rewrite Hlock in Hpu.
          destruct ((getThreadR Htid) !! bl ofs'); simpl in *; auto.
          destruct p; inv Hpu. constructor.
        }
        assert (Hvalid: Mem.valid_block m bl).
        { pose proof (compat_ls Hcmpt bl ofs') as Hlt.
          rewrite Hlock in Hlt.
          destruct (valid_block_dec m bl); auto.
          apply Mem.nextblock_noaccess with (k := Max) (ofs := ofs') in n.
          rewrite getMaxPerm_correct in Hlt.
          unfold permission_at in Hlt.
          rewrite n in Hlt. simpl in Hlt. by exfalso.
        }
        (** ev_elim steps cannot change the permission of the lock
          on the memory *)
        rewrite <- restrPermMap_Cur with (Hlt := Hcmpt tid Htid) in Hperm.
        apply (proj2 (restrPermMap_valid (Hcmpt tid Htid) bl)) in Hvalid.
        pose proof (ev_elim_nonempty_stable _ _ _ Hvalid Hperm H) as Heq.
        simpl in Helim_ev.
        split; intros Haction; simpl in Haction;
        destruct mev; try discriminate;
        simpl in Haccessed_loc; inv Haccessed_loc.
        + (** Case the event is a Write *)
          destruct Helim_ev as [m'' [Hstore Helim']].
          clear - Hstore Heq Hperm Hintv.
          apply Mem.storebytes_range_perm in Hstore.
          specialize (Hstore ofs' Hintv).
          unfold Mem.perm in Hstore.
          unfold permission_at in *.
          destruct (((Mem.mem_access m2) !! bl ofs' Cur)) as [p|]; try destruct p;
          simpl in Hstore; inv Hstore; rewrite Heq in Hperm; simpl in Hperm;
          inv Hperm.
        + (** Case the event is a Read *)
          destruct Helim_ev as [Hload Helim'].
          clear - Hload Heq Hperm Hintv.
          assert (Hlength := Mem.loadbytes_length _ _ _ _ _ Hload).
          apply Mem.loadbytes_range_perm in Hload.
          assert (Heq_size: length bytes = size bytes)
            by (clear; induction bytes; simpl; auto).
          rewrite Heq_size in Hlength. rewrite Hlength in Hintv.
          unfold Mem.range_perm in Hload.
          rewrite nat_of_Z_max in Hintv.
          destruct (Z.max_dec n 0) as [Hmax | Hmax];
            rewrite Hmax in Hintv. 
          * specialize (Hload ofs' Hintv).
            unfold Mem.perm in Hload.
            unfold permission_at in *.
            rewrite Heq in Hperm.
            destruct (((Mem.mem_access m2) !! bl ofs' Cur)) as [p|]; try destruct p;
            simpl in Hperm; inversion Hperm;
            simpl in Hload; inversion Hload.
          * rewrite Z.add_0_r in Hintv.
            destruct Hintv; simpl in *. omega.
      }
      { (** Case it's an external step*)
        apply app_inv_head in H5.
        destruct pre; simpl in H5;
        inv H5.
        simpl; destruct ev0; split; intro Hcontra; by discriminate.
        destruct pre; simpl in H1; inv H1.
      }
    Qed.

    (*TODO: move to module about executions*)
    Lemma fstep_event_sched:
      forall U tr tp m U' ev tp' m'
        (Hstep: FineConc.MachStep the_ge (U, tr, tp) m
                                  (U', tr ++ [:: ev], tp') m'),
        U = (thread_id ev) :: U'.
    Proof.
      intros.
      inv Hstep; simpl in *;
      try (apply app_eq_nil in H4; discriminate);
      subst;
      unfold dry_machine.Concur.mySchedule.schedPeek in HschedN;
      unfold dry_machine.Concur.mySchedule.schedSkip;
      destruct U; simpl in *; try discriminate;
      inv HschedN.
      apply app_inv_head in H5;
        destruct ev0; simpl in *; try discriminate.
      destruct ev0; simpl in *; try discriminate.
      inv H5. reflexivity.
      apply app_inv_head in H5.
      inv H5. reflexivity.
    Qed.

    (*TODO: same*)
    Lemma fstep_trace_monotone:
      forall U tp m tr U' tp' m' tr'
        (Hstep: FineConc.MachStep the_ge (U, tr, tp) m
                                  (U', tr', tp') m'),
      exists tr'',
        tr' = tr ++ tr''.
    Proof.
      intros.
      inv Hstep; simpl in *; subst;
      try (exists [::]; rewrite app_nil_r; reflexivity);
      eexists; reflexivity.
    Qed.

    (*TODO: same*)
    Lemma fine_execution_trace_monotone:
      forall U tr tp m U' tr' tp' m'
        (Hexec: fine_execution (U, tr, tp) m (U', tr', tp') m'),
      exists tr'',
        tr' = tr ++ tr''.
    Proof.
      induction U; intros.
      - inv Hexec. exists [::]. rewrite app_nil_r. reflexivity.
      - inv Hexec. exists [::]. rewrite app_nil_r. reflexivity.
        eapply fstep_trace_monotone in H8.
        destruct H8 as [tr''0 H8].
        apply app_inv_head in H8; subst.
        eapply IHU in H9.
        now eauto.
    Qed.
    
    (** FineConc is spinlock clean*)
    Theorem fineConc_clean:
      forall U tr tp m tp' m'
        (Hexec: fine_execution (U, [::], tp) m ([::], tr, tp') m'),
        spinlock_clean tr.
    Proof.
      unfold spinlock_clean.
      intros.
      replace tr with ([::] ++ tr) in Hexec by reflexivity.
      apply fine_execution_inv_ext with (i := i) (ev := evi) in Hexec; auto.
      destruct Hexec as (U' & U'' & tp'' & m'' & tr'' & tp''' & m'''
                         & Hexec & Hstep & Hexec' & Hsize).
      destruct evi as [|tidi evi'];
        simpl in Hmklock. destruct m0; discriminate.
      destruct evi'; try discriminate.
      simpl in *.    
      assert (Hsched: U' = tidi :: U'')
        by (eapply fstep_event_sched in Hstep; simpl in Hstep; assumption).
      rewrite Hsched in Hstep.
      apply Mklock_lockRes in Hstep.      
      assert (exists trj, tr = tr'' ++ [:: external tidi (mklock a)] ++ trj)
        by (eapply fine_execution_trace_monotone in Hexec';
             destruct Hexec' as [? Hexec'];
             rewrite <- app_assoc in Hexec';
             eexists; eauto).
      destruct H as [trj H].
      subst.
      rewrite app_assoc in Hexec'.
      assert (Hj_trj:
                nth_error trj (j - length (tr'' ++ [:: external tidi (mklock a)])) =
                Some evj).
      { rewrite <- nth_error_app2.
        rewrite <- app_assoc. assumption.
        rewrite app_length. simpl. ssromega.
      }
      eapply fine_execution_inv with (ev := evj) in Hexec'; eauto.
      destruct Hexec' as (Uj' & Uj'' & tpj'' & mj'' & trj'' & pre_j & post_j &
                          tpj''' & mj''' & Hexecj' & Hstepj & Hexecj'' & Hsizej).
      erewrite nth_error_app2 in Hj by ssromega.
      assert (Hlock: lockRes tpj'' a).
      { eapply remLockRes_Freelock_execution with
        (tr := tr'' ++ [:: external tidi (mklock a)]) (tr' := trj''); eauto.
        intros u evu Hnth.
        assert (exists trj''', trj = trj'' ++ pre_j ++ [:: evj] ++ post_j ++ trj''').
        { eapply fine_execution_trace_monotone in Hexecj''.
          destruct Hexecj'' as [? Hexecj'']. 
          do 3 rewrite <- app_assoc in Hexecj''.
          apply app_inv_head in Hexecj''.
          apply app_inv_head in Hexecj''.
          subst. do 3 rewrite <- app_assoc.
          eexists;
            by eauto.
        }
        destruct H as [trj''' H].
        subst.
        do 2 rewrite app_length in Hsizej.
        simpl in Hsizej.
        eapply (Hfreelock (length (tr'' ++ [:: external tidi (mklock a)]) + u)).
        apply/andP. split.
        rewrite app_length. simpl.
        ssromega.
        rewrite app_length.
        simpl.
        (* u is smaller than length of trj''*)
        assert (Hu: (u < length trj'')%coq_nat)
          by (erewrite <- nth_error_Some; intros Hcontra; congruence).
        rewrite <- ltn_subRL.
        rewrite <- Hsizej. ssromega.
        replace ((tr'' ++
                       [:: external tidi (mklock a)] ++
                       trj'' ++ pre_j ++ [:: evj] ++ post_j ++ trj''')) with
        ((tr'' ++ [:: external tidi (mklock a)]) ++
                                                trj'' ++ pre_j ++ [:: evj] ++
                                                post_j ++ trj''')
          by (rewrite <- app_assoc; reflexivity).
        erewrite <- nth_error_app with (ys := tr'' ++
                                                  [:: external tidi (mklock a)]).
        rewrite nth_error_app1. eauto.
        erewrite <- nth_error_Some. intro Hcontra; congruence.
      }
      rewrite app_assoc in Hstepj.
      eapply fstep_clean with (tr := (tr'' ++ [:: external tidi (mklock a)]) ++ trj'');
        by eauto.
      destruct evi; simpl in *; auto. destruct m0; discriminate.
    Qed.
    
    (** A location that the machine has no access to (i.e. the
  permission is empty in all its resources) *) 
    Inductive deadLocation tp b ofs : Prop :=
    | Dead: forall
        (Hthreads: forall i (cnti: containsThread tp i),
            (getThreadR cnti) !! b ofs = None)
        (Hlocks: (lockSet tp) !! b ofs = None)
        (Hresources: forall l pmap,
            lockRes tp l = Some pmap ->
            pmap !! b ofs = None),
        deadLocation tp b ofs.

    (** Permission decrease: A permission decrease is caused either by a
  free event or a release event. *)
    Lemma permission_decrease_execution:
      forall U tr tpi mi U' tr' tpj mj
        b ofs tidn ev
        (cnti: containsThread tpi tidn)
        (cntj: containsThread tpj tidn)
        (Hexec: fine_execution (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hreadable: Mem.perm_order' ((getThreadR cnti) !! b ofs) Readable)
        (Hperm: Mem.perm_order'' ((getThreadR cnti) !! b ofs)
                                 ((getThreadR cntj) !! b ofs))
        (Hperm': (getThreadR cnti) !! b ofs <> (getThreadR cntj) !! b ofs),
        
      exists tr_pre evu U'' U''' tp_pre m_pre tp_dec m_dec,
        fine_execution (U, tr, tpi) mi (U', tr ++ tr_pre, tp_pre) m_pre /\
        FineConc.MachStep the_ge (U', tr ++ tr_pre, tp_pre) m_pre
                          (U'', tr ++ tr_pre ++ [:: ev], tp_dec) m_dec /\
        fine_execution (U'', tr ++ tr_pre ++ [:: ev], tp_dec) m_dec
                       (U''', tr ++ tr',tpj) mj /\
        ((action evu = Free /\ deadLocation tpj b ofs) \/
         (action evu = Release /\
          (forall k evk, nth_error tr_pre k = Some evk ->
                    action evk <> Release \/ location evk <> location evu) /\
          forall tp_dec' m_dec',
            fine_execution (U, tr, tpi) mi
                           (U'', tr ++ tr_pre ++ [:: ev], tp_dec') m_dec' ->
            exists rmap,
              match location evu with
              | Some (laddr, _) =>
                lockRes tp_dec' laddr = Some rmap /\
                Mem.perm_order' (rmap !! b ofs) Readable
              | None => False
              end)).
    Proof.
      induction U as [|tid' U]; intros.
      - inversion Hexec. apply app_eq_nil in H3; subst.
        pf_cleanup. by congruence.
      - inversion Hexec.
        + apply app_eq_nil in H3; subst.
          pf_cleanup;
            by congruence.
        + apply app_inv_head in H6; subst.
          

          Definition in_free_list (b : block) ofs xs :=
            exists x, List.In x xs /\
                 let '(b', lo, hi) := x in
                 b = b' /\
                 (lo <= ofs < hi)%Z.

          Fixpoint in_free_list_trace (b : block) ofs es :=
            match es with
            | event_semantics.Free l :: es =>
              in_free_list b ofs l \/ in_free_list_trace b ofs es
            | _ :: es =>
              in_free_list_trace b ofs es
            | [:: ] =>
              False
            end.

          (** If (b, ofs) is in the list of freed addresses then the
          permission was Freeable and became None. The
          [Mem.valid_block] premise ensures that the location was not
          allocated by some event in ev, simplifying the statement and
          proof. *)
          Lemma ev_elim_free_1:
            forall m ev m' b ofs,
              Mem.valid_block m b ->
              ev_elim m ev m' ->
              in_free_list_trace b ofs ev ->
              permission_at m b ofs Cur = Some Freeable /\
              permission_at m' b ofs Cur = None /\
              exists e, List.In e ev /\
                   match e with
                   | event_semantics.Free _ => True
                   | _ => False
                   end.
          Proof.
          Admitted.

          (** If (b, ofs) is not in the list of freed locations and b
          is a valid block then the permissions remains the same
          (cannot be freed or allocated)*)
          Lemma ev_elim_free_2:
            forall m ev m' b ofs,
              Mem.valid_block m b ->
              ev_elim m ev m' ->
              ~ in_free_list_trace b ofs ev ->
              permission_at m b ofs Cur = permission_at m' b ofs Cur.
          Proof.
          Admitted.
          
          Lemma fstep_decay_inv: 
            forall i j U tr tp m tr' tp' m'
              (cnt: containsThread tp j)
              (cnt': containsThread tp' j)
              (Hstep: FineConc.MachStep the_ge (i :: U, tr, tp) m
                                        (U, tr ++ tr', tp') m'),
            forall b ofs
              (Hvalid: Mem.valid_block m b)
              (Hreadable: Mem.perm_order' ((getThreadR cnt) !! b ofs) Readable),
              (* the permission at this address remains the same or is increased*)
              (Mem.perm_order'' ((getThreadR cnt') !! b ofs)
                                ((getThreadR cnt) !! b ofs)) \/
              exists ev,
                ((List.In ev tr' /\ action ev = Free /\ deadLocation tp' b ofs) \/
                 (tr' = [:: ev] /\
                  action ev = Release /\
                  (* for any possible resulting state under the same
                  trace. This is strengthening is need to deal with
                  the non-determinism of the machine. Moreover
                  including footprints in release/acquire events was
                  used to control this non-determinism as required by
                  this proof. *)
                  forall tp' m',
                    FineConc.MachStep the_ge (i :: U, tr, tp) m
                                      (U, tr ++ tr', tp') m' ->
                    exists rmap,
                      match location ev with
                      | Some (laddr, _) =>
                        lockRes tp' laddr = Some rmap /\
                         Mem.perm_order' (rmap !! b ofs) Readable
                      | None => False
                      end)).
          Proof.
            intros.
            inv Hstep; simpl in *;
            try apply app_eq_nil in H4;
            try inv Htstep;
            inv HschedN; pf_cleanup;
            try (left; rewrite gThreadCR; apply po_refl).
            - (* internal step case *)
              apply app_inv_head in H5; subst.
              apply ev_step_elim in Hcorestep.
              destruct Hcorestep as [Helim _].
              destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
              + rewrite gssThreadRes.
                (* NOTE: this is decidable*)
                destruct (EM (in_free_list_trace b ofs ev)) as [Hdead | Hlive].
                { (* case this address was freed*)
                  eapply ev_elim_free_1 with (m := (restrPermMap (Hcmpt j Htid)))
                                               (m' := m'0) in Hdead; eauto.
                  destruct Hdead as [Hfreeable [Hempty [evf [Hin Hfree]]]].
                  destruct evf; try by exfalso.
                  right.
                  exists (internal j (event_semantics.Free l)).
                  simpl. left.
                  rewrite restrPermMap_Cur in Hfreeable.
                  repeat split; auto.
                  apply in_map with (f := fun ev => internal j ev) in Hin.
                  assumption.
                  - (* no thread has permission on (b, ofs)*)
                    intros i cnti.
                    destruct (i == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
                    + rewrite gssThreadRes.
                      rewrite getCurPerm_correct.
                      assumption.
                    + (* case i is a different thread than the one that stepped*)
                      (* by the invariant*) 
                      assert (cnti' := cntUpdate' _ _ _ cnti).
                      erewrite gsoThreadRes with (cntj := cnti')
                        by (intro Hcontra; subst; auto).
                      destruct Hinv.
                      specialize (no_race0 _ _ cnti' Htid Hij b ofs).
                      rewrite Hfreeable in no_race0.
                      rewrite perm_union_comm in no_race0.
                      apply no_race_racy in no_race0.
                      inversion no_race0. reflexivity.
                      constructor.
                  - (* lockset permissions*)
                    rewrite gsoThreadLock.
                    destruct Hinv.
                    specialize (lock_set_threads0 _ Htid b ofs).
                    rewrite Hfreeable in lock_set_threads0.
                    rewrite perm_union_comm in lock_set_threads0.
                    apply no_race_racy in lock_set_threads0.
                    inversion lock_set_threads0. reflexivity.
                    constructor.
                  - (* lock resources permissions*)
                    intros laddr rmap Hres.
                    rewrite gsoThreadLPool in Hres.
                    destruct Hinv.
                    specialize (lock_res_threads0 _ _ _ Htid Hres b ofs).
                    rewrite Hfreeable in lock_res_threads0.
                    rewrite perm_union_comm in lock_res_threads0.
                    apply no_race_racy in lock_res_threads0.
                    inversion lock_res_threads0. reflexivity.
                    constructor.
                }
                { (* case the address was not freed *)
                  left.
                  erewrite <- restrPermMap_valid with (Hlt := Hcmpt j Htid)
                    in Hvalid.
                  eapply ev_elim_free_2 in Hlive; eauto.
                  rewrite restrPermMap_Cur in Hlive.
                  rewrite getCurPerm_correct.
                  rewrite <- Hlive.
                  pf_cleanup.
                  apply po_refl.
                }
              + (* case it was another thread that stepped *)
                left.
                erewrite gsoThreadRes with (cntj := cnt)
                  by assumption.
                apply po_refl.
            - (* lock acquire*)
              left.
              rewrite gLockSetRes.
              destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
              + rewrite gssThreadRes.
                destruct Hangel.
                admit. (* need to add to acq angel spec that
                thread permissions only increase*)
              + erewrite gsoThreadRes by eassumption.
                apply po_refl.
            - (* lock release *)
              rewrite gLockSetRes.
              destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
              + rewrite gssThreadRes.
                (* need stronger angel spec. We need to able to
                establish that the permission on the thread either
                stays the same or the lp is increased. Replacing relAngelIncr0:*)
                assert (Htransfer:
                          forall (b : positive) (ofs : Z),
                            Mem.perm_order' ((getThreadR Htid) !! b ofs) Readable <->
                            Mem.perm_order' (virtueLP !! b ofs) Readable \/
                            ((computeMap (getThreadR Htid) virtueThread) !! b ofs) =
                            (getThreadR Htid) !! b ofs) by admit.
                pf_cleanup.
                eapply Htransfer in Hreadable.
                destruct Hreadable as [HreadableRes | Hstable].
                * (* case the lockres was increased *)
                  right.
                  apply app_inv_head in H5; subst.
                  eexists. right.
                  split. reflexivity.
                  split. reflexivity.
                  intros tp'0 m'0.
                  clear - HreadableRes.
                  intros Hstep'0.
                  inv Hstep'0;
                    simpl in *; try apply app_eq_nil in H4; try discriminate.
                  apply app_inv_head in H5.
                  destruct ev; simpl; discriminate.
                  apply app_inv_head in H5.
                  inv H5.
                  (*external step case*)
                  inv Htstep.
                  exists virtueLP.
                  rewrite gsslockResUpdLock.
                  split; auto.
                * (* case lockres was not increased *)
                  left. rewrite Hstable.
                  now apply po_refl.
              + (* case a different thread stepped - easy*)
                left. erewrite gsoThreadRes by eauto.
                now apply po_refl.
            - (* need to strengthen angel for spawn as well*)
              assert (Hstable: forall b ofs,
                        Mem.perm_order' ((getThreadR Htid) !! b ofs) Readable ->
                        (getThreadR Htid) !! b ofs =
                        ((computeMap (getThreadR Htid) virtue1) !! b ofs))
                by admit.
              destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
              + pf_cleanup.      
                specialize (Hstable b ofs Hreadable).
                left.
                rewrite gsoAddRes gssThreadRes.
                rewrite Hstable.
                apply po_refl.
              + left. rewrite gsoAddRes gsoThreadRes; eauto.
                apply po_refl.
            - (* MkLock *)
              left.
              rewrite gLockSetRes.
              destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij; subst.
              + pf_cleanup.
                rewrite gssThreadRes.
                
                
                specialize (Hstable b ofs Hreadable).
                left.
                rewrite gsoAddRes gssThreadRes.
                rewrite Hstable.
                apply po_refl.
              + left. rewrite gsoAddRes gsoThreadRes; eauto.
                apply po_refl.
              
                
                  
                  
              + erewrite gsoThreadRes by eassumption.
                apply po_refl.
              apply app_inv_head in H5. subst.
              destruct Hangel.
              
              right.
              eexists. right.
              split; eauto.
              simpl. split; first by reflexivity.
              intros tp'0 m'0 Hstep'0.
              
              
                                                

                Lemma permission_decrease_execution:
                               forall U tr tpi mi U' tr' tpj mj
                                 b ofs tidn tidm
                                 (cntin: containsThread tpi tidn)
                                 (cntjn: containsThread tpj tidn)
                                 (cntim: containsThread tpi tidm)
                                 (cntjm: containsThread tpj tidm)
                                 (Hexec: fine_execution (U, tr, tpi) mi
                                                        (U', tr ++ tr', tpj) mj)
                                 (Hreadablein: Mem.perm_order' ((getThreadR cntin) !! b ofs) Readable)
                                 (Hreadablejm: Mem.perm_order' ((getThreadR cntjm) !! b ofs) Readable)
                                 (Hwritable: Mem.perm_order' ((getThreadR cntin) !! b ofs) Writable \/
                                             Mem.perm_order' ((getThreadR cntjm) !! b ofs) Writable),
                               exists tr_pre evu tr_post U'' tp_pre m_pre tp_dec m_dec tp_post m_post,
                                 fine_execution (U, tr, tpi) mi (U', tr ++ tr_pre, tp_pre) m_pre /\
                                 FineConc.MachStep the_ge (U', tr ++ tr_pre, tp_pre) m_pre
                                                   (U'', tr ++ tr_pre ++ [:: ev], tp_dec) m_dec /\
                                 fine_execution (U'', tr ++ tr_pre ++ [:: ev], tp_dec) m_dec
                                                (U''', tr ++ tr_pre ++ [:: ev] ++ tr_post,tp_post) m_post /\
                                 FineConc.MachStep the_ge (U''', tr ++ tr_pre ++ [:: ev] ++ tr_post, tp_post) m_post
                                                   (U'''', tr ++ tr_pre ++ [
                                                                
                                                                
                                                                nth_error tr' u = Some evu /\
                                                                ((action evu = Free /\ deadLocation tpj b ofs) \/
                                                                 (action evu = Release /\
                                                                  resource
                                                                    (forall k evk, k < u ->
                                                                              nth_error tr' k = Some evk ->
                                                                              action evk <> Release \/ location evk <> location evu))).
                                                                Proof.
                                                                  induction U as [|tid' U]; intros.
                                                                  - inversion Hexec. apply app_eq_nil in H3; subst.
                                                                    pf_cleanup. by congruence.
                                                                  - inversion Hexec.
                                                                    + apply app_eq_nil in H3; subst. pf_cleanup.
                                                                        by congruence.
                                                                    + apply app_inv_head in H6; subst.
                                                                      
                                                                      

                                                                      
                                                                      specialize (IHU (tr ++ tr'0) tp' 
                                                                                      
                                                                                      
                                                                                      
                                                                                      
                                                                                      
                                                                                      (** FineConc is spinlock well-synchronized and clean*)
                                                                                      Theorem fineConc_spinlock:
                                                                                    forall U tr tp m tp' m'
                                                                                      (Hexec: fine_execution (U, [::], tp) m ([::], tr, tp') m'),
                                                                                      spinlock_synchronized tr.
                                                                                  Proof.
                                                                                    intros.
                                                                                    unfold spinlock_synchronized; intros i j evi evj Hij Hi Hj Hcompetes.
                                                                                    replace tr with ([::] ++ tr ) in Hexec by reflexivity.
                                                                                    (* We can decompose the execution in three parts, around the event i *)
                                                                                    assert (Hexec' := fine_execution_inv _ _ Hi Hexec).
                                                                                    destruct (is_external evi || is_external evj) eqn:Hexternal;
                                                                                      move/orP:Hexternal => Hexternal.
                                                                                    - (* Case evi or evj are externals *)
                                                                                      admit.
                                                                                    - (* Case evi and evj are internal (memory) events *)
                                                                                      destruct Hexec' as (Ui' & Ui'' & tpi & mi & tr' & pre_i & post_i &
                                                                                                          tpi' & mi' & Hexec' & Hstepi & Hexeci'' & Hsizei).
                                                                                      
                                                                                      
                                                                                      

                                                                                      