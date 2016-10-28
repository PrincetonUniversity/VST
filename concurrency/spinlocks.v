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
        forall (cnti': containsThread tp' i) ofs,
          Intv.In ofs (addr.2, addr.2 + lksize.LKSIZE)%Z ->
          ((getThreadR cnti').2 !! (addr.1)) ofs = Some Writable.
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
      intros.
      erewrite setPermBlock_same by eauto.
      reflexivity.
    Qed.

    (** [True] whenever some resource in [tp] has above [Readable] lock-permission on [laddr]*)
    (* I could not prove the stronger version, where quantification happens inside each case*)
    Definition isLock tp laddr :=
      forall ofs, Intv.In ofs (laddr.2, laddr.2 + lksize.LKSIZE)%Z ->
      (exists i (cnti: containsThread tp i),
          Mem.perm_order'' ((getThreadR cnti).2 !! (laddr.1) ofs) (Some Readable)) \/
      (exists laddr' rmap, lockRes tp laddr' = Some rmap /\
                      Mem.perm_order'' (rmap.2 !! (laddr.1) ofs) (Some Readable)).

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
        intros ofs0 Hintv.
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
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
        split.
        destruct (EqDec_address (b, Int.intval ofs) addr); subst.
        rewrite gssLockRes; auto.
        erewrite gsoLockRes by eauto.
        rewrite gsoThreadLPool; auto.
        intros ofs0 Hintv.
        specialize (Hangel2 (addr.1) ofs0).
        apply permjoin_order in Hangel2.
        destruct Hangel2 as [Hlt1 Hlt2].
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + pose proof (cntUpdate (Kresume c Vundef) newThreadPerm Htid
                                (cntUpdateL (b, Int.intval ofs) (empty_map, empty_map) cntj)) as cntj'.
          destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij.
          * subst.
            left.
            exists j, cntj'.
            rewrite gLockSetRes gssThreadRes.
            pf_cleanup.        
            now eauto using po_trans.
          * left.
            exists j, cntj'.
            rewrite gLockSetRes.
            erewrite @gsoThreadRes with (cntj := cntj) by eauto.
            now eauto using po_trans.
        + destruct (EqDec_address (b, Int.intval ofs) laddr').
          * subst.
            left.
            pose proof (cntUpdate (Kresume c Vundef) newThreadPerm Htid
                                  (cntUpdateL (b, Int.intval ofs) (empty_map, empty_map) Htid)) as cnti'.
            exists tid, cnti'.
            rewrite gLockSetRes gssThreadRes.
            rewrite HisLock0 in Hres; inv Hres.
            eauto using po_trans.
          * right.
            exists laddr', rmap'.
            erewrite gsoLockRes by eauto.
            rewrite gsoThreadLPool.
            split; now eauto.
      - unfold isLock in *.
        inv HschedN.        split.
        destruct (EqDec_address (b, Int.intval ofs) addr); subst.
        rewrite gssLockRes; auto.
        erewrite gsoLockRes by eauto.
        rewrite gsoThreadLPool; auto.
        intros ofs0 Hintv.
        specialize (Hangel2 (addr.1) ofs0).
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij.
          * subst.
            pf_cleanup.
            apply permjoin_readable_iff in Hangel2.
            destruct (Hangel2.1 Hperm) as [Hperm' | Hperm'].
            left.
            exists j, cntj.
            rewrite gLockSetRes gssThreadRes.
            now eauto.
            right.
            exists (b, Int.intval ofs), virtueLP.
            rewrite gssLockRes.
            split;
              now eauto.
          * left.
            exists j, cntj.
            rewrite gLockSetRes.
            erewrite @gsoThreadRes with (cntj := cntj) by eauto.
            now eauto.
        + destruct (EqDec_address (b, Int.intval ofs) laddr').
          * subst.
            rewrite HisLock0 in Hres; inv Hres.
            destruct (Hrmap addr.1 ofs0) as [_ Hrmap2].
            rewrite Hrmap2 in Hperm.
            exfalso. simpl in Hperm.
            now assumption.
          * right.
            exists laddr', rmap'.
            erewrite gsoLockRes by eauto.
            rewrite gsoThreadLPool.
            split; now eauto.
      - unfold isLock in *.
        inv HschedN.
        split;
          first by (rewrite gsoAddLPool gsoThreadLPool;
                    assumption).
        intros ofs0 Hintv.
        specialize (Hangel2 (addr.1) ofs0).
        apply permjoin_readable_iff in Hangel2.
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij.
          * subst.
            pf_cleanup.
            destruct (Hangel2.1 Hperm) as [Hperm' | Hperm'].
            left.
            exists (latestThread tp), (contains_add_latest (updThread cntj (Kresume c Vundef) threadPerm') (Vptr b ofs) arg newThreadPerm).
            erewrite gssAddRes by reflexivity.
            assumption.
            left.
            exists j, (cntAdd (Vptr b ofs) arg newThreadPerm cntj).
            rewrite @gsoAddRes gssThreadRes.
            assumption.
          * left.
            exists j, (cntAdd (Vptr b ofs) arg newThreadPerm cntj).
            rewrite @gsoAddRes.
            erewrite @gsoThreadRes with (cntj := cntj) by eauto.
            now eauto.
        + right.
          exists laddr', rmap'.
          rewrite gsoAddLPool gsoThreadLPool.
          split;
            now auto.
      - (** Makelock case*)
        inv HschedN.
        split.
        destruct (EqDec_address (b, Int.intval ofs) addr); subst.
        rewrite gssLockRes; auto.
        erewrite gsoLockRes by eauto.
        rewrite gsoThreadLPool;
          now auto.
        intros ofs0 Hintv.
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + left. exists j, cntj.
          rewrite gLockSetRes.
          destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij.
          * subst.
            pf_cleanup.
            rewrite gssThreadRes.
            rewrite <- Hlock_perm.
            destruct (setPermBlock_or (Some Writable) b (Int.intval ofs) (lksize.LKSIZE_nat) (getThreadR cntj).2 addr.1 ofs0)
              as [Heq | Heq];
              rewrite Heq; simpl; auto using perm_order.
          * rewrite gsoThreadRes;
              now auto.
        + assert ((b, Int.intval ofs) <> laddr')
            by (intros Hcontra; subst; congruence).
          right.
          exists laddr', rmap'.
          erewrite gsoLockRes by eauto.
          rewrite gsoThreadLPool.
          split; auto.
      - (** Interesting case: freelock *)
        unfold isLock in *.
        apply app_inv_head in H5; subst.
        specialize (Hev 0 (external tid (freelock (b, Int.intval ofs)))
                        ltac:(reflexivity)).
        simpl in Hev.
        destruct Hev; first by exfalso.
        erewrite gsolockResRemLock
          by (intros Hcontra; subst; auto).
        rewrite gsoThreadLPool.
        split; auto.
        intros ofs0 Hintv.
        destruct (HisLock ofs0 Hintv) as [[j [cntj Hperm]] | [laddr' [rmap' [Hres Hperm]]]].
        + left.
          exists j, cntj.
          rewrite gRemLockSetRes.
          destruct (tid == j) eqn:Hij; move/eqP:Hij=>Hij.
          * subst.
            pf_cleanup.
            rewrite gssThreadRes.
            rewrite <- Hlock_perm.
            assert (Hneq: b <> addr.1 \/ (b = addr.1) /\ ((ofs0 < (Int.intval ofs))%Z \/ (ofs0 >= (Int.intval ofs) + lksize.LKSIZE)%Z)).
            { destruct (Pos.eq_dec b (addr.1)); subst; auto.
              destruct addr as [b' ofs']; simpl;
                right; split; auto.
              simpl in His_lock, Hintv.
              assert (Hofs': (ofs' + lksize.LKSIZE <= Int.intval ofs \/ ofs' >= Int.intval ofs + lksize.LKSIZE)%Z).
              { destruct (zle (ofs' + lksize.LKSIZE)%Z (Int.intval ofs)).
                - left; auto.
                - destruct (zlt ofs' (Int.intval ofs + lksize.LKSIZE)%Z); eauto.
                  destruct (zlt ofs' (Int.intval ofs)).
                  + exfalso.
                    pose proof (lockRes_valid Hinv b' ofs') as Hvalid.
                    destruct (lockRes tp (b', ofs')) eqn:Hlock'; auto.
                    specialize (Hvalid (Int.intval ofs)).
                    erewrite Hvalid in His_lock.
                    congruence.
                    omega.
                  + exfalso.
                    pose proof (lockRes_valid Hinv b' (Int.intval ofs)) as Hvalid.
                    rewrite His_lock in Hvalid.
                    specialize (Hvalid ofs').
                    erewrite Hvalid in Hlock.
                    now eauto.
                    assert (Hneq: Int.intval ofs <> ofs')
                      by (intros Hcontra; subst; apply H; auto).
                    clear - g l g0 Hneq.
                    omega.
              }
              unfold Intv.In in Hintv.
              simpl in Hintv.
              destruct Hofs'; omega.
            }
            destruct Hneq as [? | [? ?]]; subst;
              [rewrite setPermBlock_other_2 | rewrite setPermBlock_other_1];
              auto.
          * rewrite gsoThreadRes;
              now auto.
        + destruct (EqDec_address (b, Int.intval ofs) laddr').
          * subst.
            rewrite Hres in His_lock; inv His_lock.
            exfalso.
            destruct (Hrmap addr.1 ofs0) as [_ Hrmap2].
            rewrite Hrmap2 in Hperm.
            simpl in Hperm.
            now assumption.
          * right.
            exists laddr', rmap'.
            erewrite gsolockResRemLock;
              now auto.
      - split; assumption.
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

    (** If some address is a lock and there is no event of type Freelock at this
  address in some trace tr then the address is still a lock at the resulting
  state *)
    Lemma remLockRes_Freelock_execution:
      forall U U' tr tr' tp m tp' m' addr
        (Hlock: lockRes tp addr)
        (HisLock: isLock tp addr)
        (Hstep: multi_fstep (U, tr, tp) m
                               (U', tr ++ tr', tp') m')
        (Hfreelock: forall (u : nat) (evu : machine_event),
            nth_error tr' u = Some evu ->
            action evu <> Freelock \/
            location evu <> Some (addr, lksize.LKSIZE_nat)),
        lockRes tp' addr /\
        isLock tp' addr.
    Proof.
      induction U; intros.
      - inversion Hstep.
        rewrite <- app_nil_r in H3 at 1.
        apply app_inv_head in H3; subst.
        split; assumption.
      - inversion Hstep.
        + rewrite <- app_nil_r in H3 at 1.
          apply app_inv_head in H3; subst;
          split; assumption.
        + subst.
          apply app_inv_head in H6. subst.
          eapply remLockRes_Freelock in H8; eauto.
          destruct H8 as [Hres0 HisLock0].
          specialize (IHU U' (tr ++ tr'0) tr'' tp'0 m'0 tp' m' addr Hres0 HisLock0).
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

    (**TODO: move to dry_machine_lemmas? make a new file with core lemmas?*)
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
        (HisLock: isLock tp addr)
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
        (** hence there will be some lock permission that is above [Readable] on
          [address] (bl, ofs') by [isLock] *)
        specialize (HisLock ofs' Hintvl).
        (** and thus all threads will have at most [Nonempty]
          data permission on this [address] by [perm_coh]*)
        assert (Hperm:
                  Mem.perm_order'' (Some Nonempty)
                                   ((getThreadR Htid).1 !! bl ofs')).
        { destruct HisLock as [[j [cntj Hperm]] | [laddr [rmap [Hres Hperm]]]].
          - pose proof ((thread_data_lock_coh Hinv cntj).1 _ Htid bl ofs') as Hcoh.
            clear - Hcoh Hperm.
            simpl in Hperm.
            destruct ((getThreadR Htid).1 !! bl ofs') as [p|]; simpl; auto;
              destruct ((getThreadR cntj).2 !! bl ofs') as [p0|]; simpl in Hperm;
                inversion Hperm; subst;
                  simpl in Hcoh; destruct p;
                    try (by exfalso); eauto using perm_order.
          - pose proof ((locks_data_lock_coh Hinv _ Hres).1 _ Htid bl ofs') as Hcoh.
            clear - Hcoh Hperm.
            simpl in Hperm.
            destruct ((getThreadR Htid).1 !! bl ofs') as [p|]; simpl; auto;
              destruct (rmap.2 !! bl ofs') as [p0|]; simpl in Hperm;
                inversion Hperm; subst;
                  simpl in Hcoh; destruct p;
                    try (by exfalso); eauto using perm_order.
        }

        (** [bl] must be a [Mem.valid_block]*)
        assert (Hvalid: Mem.valid_block m bl)
          by (destruct (lockRes tp (bl, ofsl)) as [rmap|] eqn:Hres; try (by exfalso);
              pose proof (lockRes_blocks Hcmpt (bl, ofsl) Hres);
              eauto).

        (** ev_elim steps cannot change the permission of the lock
          on the memory *)
        rewrite <- restrPermMap_Cur with (Hlt := (Hcmpt tid Htid).1) in Hperm.
        apply (proj2 (restrPermMap_valid (Hcmpt tid Htid).1 bl)) in Hvalid.
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
    
    (** FineConc is spinlock clean*)
    Theorem fineConc_clean:
      forall U tr tp m tp' m'
        (Hexec: multi_fstep (U, [::], tp) m ([::], tr, tp') m'),
        spinlock_clean tr.
    Proof.
      unfold spinlock_clean.
      intros.
      replace tr with ([::] ++ tr) in Hexec by reflexivity.
      (** break up the trace in the parts of interest*)
      apply multi_fstep_inv_ext with (i := i) (ev := evi) in Hexec; auto.
      destruct Hexec as (U' & U'' & tp'' & m'' & tr'' & tp''' & m'''
                         & Hexec & Hstep & Hexec' & Hsize).
      destruct evi as [|tidi evi'];
        simpl in Hmklock. destruct m0; discriminate.
      destruct evi'; try discriminate.
      simpl in *.    
      assert (Hsched: U' = tidi :: U'')
        by (eapply fstep_event_sched in Hstep; simpl in Hstep; assumption).
      rewrite Hsched in Hstep.
      (** The thread that executed the [mklock] operation must be in the threadpool*)
      destruct (fstep_ev_contains _ Hstep) as [cnti cnti'].
      (** since there was a [mklock] event, [a] will be in [lockRes] and the
      thread will have lock-permission on it*)
      apply Mklock_lockRes in Hstep.
      destruct Hstep as [HlockRes''' Hperm'''].
      assert (exists trj, tr = tr'' ++ [:: external tidi (mklock a)] ++ trj)
        by (eapply multi_fstep_trace_monotone in Hexec';
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
      eapply multi_fstep_inv with (ev := evj) in Hexec'; eauto.
      destruct Hexec' as (Uj' & Uj'' & tpj'' & mj'' & trj'' & pre_j & post_j &
                          tpj''' & mj''' & Hexecj' & Hstepj & Hexecj'' & Hsizej).
      erewrite nth_error_app2 in Hj by ssromega.
      assert (Hlock: lockRes tpj'' a /\ isLock tpj'' a).
      { eapply remLockRes_Freelock_execution with
        (tr := tr'' ++ [:: external tidi (mklock a)]) (tr' := trj''); eauto.
        left.
        exists tidi, cnti'.
        erewrite Hperm''' by eauto.
        simpl; now constructor.
        intros u evu Hnth.
        assert (exists trj''', trj = trj'' ++ pre_j ++ [:: evj] ++ post_j ++ trj''').
        { eapply multi_fstep_trace_monotone in Hexecj''.
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
        (** u is smaller than length of trj''*)
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
      destruct Hlock as [HlockResj HisLockj].
      rewrite app_assoc in Hstepj.
      eapply fstep_clean; eauto.
      destruct evi; simpl in *; auto. destruct m0; discriminate.
    Qed.
    
    (** A location that the machine has no access to (i.e. the permission is
  empty in all its resources) *) 
    Inductive deadLocation tp b ofs : Prop :=
    | Dead: forall
        (Hthreads: forall i (cnti: containsThread tp i),
            (getThreadR cnti).1 !! b ofs = None /\ (getThreadR cnti).2 !! b ofs = None)
        (Hlocks: (lockSet tp) !! b ofs = None)
        (Hresources: forall l pmap,
            lockRes tp l = Some pmap ->
            pmap.1 !! b ofs = None /\ pmap.2 !! b ofs = None),
        deadLocation tp b ofs.

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
    

    (** Permission decrease: A thread can decrease its data permissions by:
- Freeing memory.
- Spawning a thread
- A makelock operation, turning data into lock
- Releasing a lock *)
    Lemma data_permission_decrease_step:
      forall U tr tp m U' tp' m' tr_pre ev tr_post tidn b ofs
        (cnt: containsThread tp tidn)
        (cnt': containsThread tp' tidn)
        (Hstep: FineConc.MachStep the_ge (U, tr, tp) m (U', tr ++ tr_pre ++ [:: ev] ++ tr_post, tp') m')
        (Hperm: Mem.perm_order'' ((getThreadR cnt).1 !! b ofs) ((getThreadR cnt').1 !! b ofs))
        (Hperm': (getThreadR cnt).1 !! b ofs <> (getThreadR cnt').1 !! b ofs),
        (action ev = Free /\ deadLocation tp' b ofs) \/
        (action ev = Spawn) \/
        (action ev = Mklock /\
         match location ev with
         | Some (addr, sz) =>
           b = addr.1 /\
           Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
         | None =>
           False
         end) \/
        (action ev = Release).
    Proof.
      Admitted.
      (*intros.
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
          intros tp'0 m'0 Hstep'0. *)

    Lemma data_permission_decrease_execution:
      forall U tr tpi mi U' tr' tpj mj
        b ofs tidn
        (cnti: containsThread tpi tidn)
        (cntj: containsThread tpj tidn)
        (Hexec: fine_execution (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hreadable: Mem.perm_order' ((getThreadR cnti).1 !! b ofs) Readable)
        (Hperm: Mem.perm_order'' ((getThreadR cnti).1 !! b ofs)
                                 ((getThreadR cntj).1 !! b ofs))
        (Hperm': (getThreadR cnti).1 !! b ofs <> (getThreadR cntj).1 !! b ofs),
        
      exists tr_pre evu U'' U''' tp_pre m_pre tp_dec m_dec,
        fine_execution (U, tr, tpi) mi (U', tr ++ tr_pre, tp_pre) m_pre /\
        FineConc.MachStep the_ge (U', tr ++ tr_pre, tp_pre) m_pre
                          (U'', tr ++ tr_pre ++ [:: evu], tp_dec) m_dec /\
        fine_execution (U'', tr ++ tr_pre ++ [:: evu], tp_dec) m_dec
                       (U''', tr ++ tr',tpj) mj /\
        ((action evu = Free /\ deadLocation tpj b ofs) \/
         (action evu = Spawn) \/
         (action evu = Mklock /\
          match location evu with
          | Some (addr, sz) =>
            b = addr.1 /\
            Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
          | None => False
          end) \/
         (action evu = Release /\
          (** and this is the first release to drop the permissions of [(b,ofs)]*)
          (forall (cntu: containsThread tp_pre tidn),
              (getThreadR cntu).1 !! b ofs = (getThreadR cnti).1 !! b ofs))).
    Proof.
      Admitted.
      (*induction U as [|tid' U]; intros.
      - inversion Hexec. apply app_eq_nil in H3; subst.
        pf_cleanup. by congruence.
      - inversion Hexec.
        + apply app_eq_nil in H3; subst.
          pf_cleanup;
            by congruence.
        + apply app_inv_head in H6; subst. *)

    (** Permission increase: A thread can increase its data permissions by:
- Allocating memory.
- If it is spawned
- A freelock operation, turning a lock into data.
- Acquiring a lock *)
    Lemma data_permission_increase_step:
      forall U tr tp m U' tp' m' tr_pre ev tr_post tidn b ofs
        (cnt: containsThread tp tidn)
        (cnt': containsThread tp' tidn)
        (Hstep: FineConc.MachStep the_ge (U, tr, tp) m (U', tr ++ tr_pre ++ [:: ev] ++ tr_post, tp') m')
        (Hperm: Mem.perm_order'' ((getThreadR cnt').1 !! b ofs) ((getThreadR cnt).1 !! b ofs))
        (Hperm': (getThreadR cnt).1 !! b ofs <> (getThreadR cnt').1 !! b ofs),
        (match ev with
         | internal _ (event_semantics.Alloc b' lo hi) =>
           (** we can strengthen that but no need to*)
           b = b'
         | _ => False
         end) \/
        (action ev = Spawn) \/
        (action ev = Freelock /\
         match location ev with
         | Some (addr, sz) =>
           b = addr.1 /\
           Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
         | None =>
           False
         end) \/
        (action ev = Acquire).
    Proof.
    Admitted.
    
    Lemma data_permission_increase_execution:
      forall U tr tpi mi U' tr' tpj mj
        b ofs tidn
        (cnti: containsThread tpi tidn)
        (cntj: containsThread tpj tidn)
        (Hexec: fine_execution (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hperm: Mem.perm_order'' ((getThreadR cnti).1 !! b ofs)
                                 ((getThreadR cntj).1 !! b ofs))
        (Hperm': (getThreadR cnti).1 !! b ofs <> (getThreadR cntj).1 !! b ofs),
        
      exists tr_pre evu U'' U''' tp_pre m_pre tp_dec m_dec,
        fine_execution (U, tr, tpi) mi (U', tr ++ tr_pre, tp_pre) m_pre /\
        FineConc.MachStep the_ge (U', tr ++ tr_pre, tp_pre) m_pre
                          (U'', tr ++ tr_pre ++ [:: evu], tp_dec) m_dec /\
        fine_execution (U'', tr ++ tr_pre ++ [:: evu], tp_dec) m_dec
                       (U''', tr ++ tr',tpj) mj /\
        ((match evu with
          | internal _ (event_semantics.Alloc b' lo hi) =>
            (** we can strengthen that but no need to*)
            b = b'
          | _ => False
          end) \/
         (action evu = Spawn) \/
         (action evu = Freelock /\
          match location evu with
          | Some (addr, sz) =>
            b = addr.1 /\
            Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
          | None =>
            False
          end) \/
         (action evu = Acquire)).
    Proof.
    Admitted.

    Lemma maximal_competing:
      forall i j tr evi evj
        (Hij: i < j)
        (Hi: nth_error tr i = Some evi)
        (Hj: nth_error tr j = Some evj)
        (Hcompetes: competes evi evj),
      exists k evk, i <= k < j /\
               nth_error tr k = Some evk /\
               competes evk evj /\
               (forall k' evk', k < k' < j ->
                           nth_error tr k' = Some evk' ->
                           ~ competes evk' evj).
    Proof.
      intros i j tr.
      generalize dependent j.
      generalize dependent i.
      induction tr; intros.
      - rewrite nth_error_nil in Hi.
        discriminate.              
      -
        (** Is there any competing with [evj] event in [tr]?*)
        assert (Hcompeting: (exists k' evk',
                                i < k' < j /\
                                nth_error (a :: tr) k' = Some evk' /\
                                competes evk' evj) \/
                            ~ (exists k' evk',
                                  i < k' < j /\
                                  nth_error (a :: tr) k' = Some evk' /\
                                  competes evk' evj))
          by (eapply EM).
        destruct Hcompeting as [[k' [evk' [Horder [Hk' Hcompete']]]] |
                                Hno_race].
        + (** If yes, then use this to instantiate the IH*)
          destruct k'; first by (exfalso; ssromega).
          destruct j; first by (exfalso; ssromega).
          simpl in *.
          destruct (IHtr k' j evk' evj ltac:(ssromega) Hk' Hj Hcompete')
            as (k & evk & Horder' & Hk & Hcompetekj & Hmaximal).
          exists (S k), evk.
          repeat (split; simpl; eauto).
          ssromega.
          intros k'0 evk'0 Horder'0 Hk'0.
          destruct k'0; first by (exfalso; ssromega).
          simpl in Hk'0.
          eapply Hmaximal; eauto.
        + (** Otherwise [evi] is the first event to compete with [evj] and hence maximal*)
          exists i, evi.
          repeat (split; eauto).
          ssromega.
          intros k' evk' Horder' Hk' Hcompetes'.
          (** but by [Hno_race] there is no event at k' [i < k'] s.t. it competes with evj*)
          eapply Hno_race.
          exists k', evk'.
          split; eauto.
    Qed.
    
    
    Lemma fineConc_step_synchronized:
      forall U0 U U' tr0 tr tp0 m0 tp m tp' m' tr'
        (Hexec: multi_fstep (U0, tr0, tp0) m0 (U, tr0 ++ tr, tp) m)
        (Hstep: FineConc.MachStep the_ge (U, tr0 ++ tr, tp) m (U', tr0 ++ tr ++ tr', tp') m')
        (Hsynchronized: spinlock_synchronized (tr0 ++ tr)),
        spinlock_synchronized (tr0 ++ tr ++ tr').
    Proof.
      intros.
      (** Consider two competing events evi and evj*)
      intros i j evi evj Hneq Hi Hj Hcompetes.
      destruct (lt_dec j (length (tr0 ++ tr))) as [Hj_in_tr | Hj_not_in_tr].
      - (** If [evj] is in [tr] then so is [evi], by [i < j] and the goal is
        trivial by [Hsynchronized]*)
        assert (Hi_in_tr: (i < length (tr0 ++ tr))%coq_nat) by ssromega.
        eapply nth_error_app1 with (l' := tr') in Hj_in_tr.
        eapply nth_error_app1 with (l' := tr') in Hi_in_tr.
        rewrite catA in Hi, Hj.
        rewrite Hi_in_tr in Hi.
        rewrite Hj_in_tr in Hj.
        destruct (Hsynchronized i j evi evj Hneq Hi Hj Hcompetes) as
            [[u [v [eu [ev [Horder [Hevu [Hevv [Hactu [Hactv Hloc]]]]]]]]] |
             [u [eu [Horder [Hu Hactu]]]]].
        + left.
          exists u, v, eu, ev.
          Lemma nth_error_app_inv:
            forall (A : Type) (i : nat) (v: A) (ys xs : seq.seq A), nth_error xs i = Some v ->
                                                             nth_error (xs ++ ys) i = Some v.
          Admitted.

          repeat (split; eauto);
          rewrite catA;
          now eapply nth_error_app_inv.
        + right.
          exists u, eu.
          repeat (split; eauto).
          rewrite catA;
            now eapply nth_error_app_inv.
      - (** Hence [evj] is in [tr'] *)

        (** By [maximal_competing] there must exist some maximal event [ek] s.t. it competes with [evj]*)
        destruct (maximal_competing _ _ _ Hneq Hi Hj Hcompetes)
          as (k & evk & Horder & Hk & Hcompetes_kj & Hmaximal).
        (** By case analysis on the type of the competing events [evk] and [evj]*)
        destruct (is_internal evk && is_internal evj) eqn:Hevk_evj.
        { (** If [evk] and [evj] are [internal] events *)
          move/andP:Hevk_evj=>[Hinternal_k Hinternal_j].
          destruct Hcompetes_kj as (Hthreads_neq & Hsame_loc & Hcactionk & Hactionj & His_write & _).
          specialize (His_write Hinternal_k Hinternal_j).
          admit.
        }
    Admitted.
        
        
              
Lemma multi_fstep_snoc:
            forall U U' U'' tr tr' tr'' tp m tp' m' tp'' m''
              (Hexec: multi_fstep (U, tr, tp) m (U', tr ++ tr', tp') m')
              (Hstep: FineConc.MachStep the_ge (U', tr ++ tr', tp') m' (U'', tr ++ tr' ++ tr'', tp'') m''),
              multi_fstep (U, tr, tp) m (U'', tr ++ tr' ++ tr'', tp'') m''.
          Proof.
            induction U; intros.
            - inversion Hexec.
              rewrite <- app_nil_r in H3 at 1.
              apply app_inv_head in H3. subst.
              simpl in *. erewrite app_nil_r in *.
              inversion Hstep; simpl in *;
                try discriminate.
            - inversion Hexec.
              + rewrite <- app_nil_r in H3 at 1.
                apply app_inv_head in H3. subst.
                erewrite app_nil_r in *.
                simpl in *.
                Lemma fstep_sched_inv:
                  forall i U tp m tr U' tp' m' tr'
                    (Hstep: FineConc.MachStep the_ge (i :: U, tr, tp) m
                                              (U', tr', tp') m'),
                    U' = U.
                Admitted.
                assert (U = U'')
                  by (erewrite fstep_sched_inv by eauto; reflexivity); subst.
                replace (tr ++ tr'') with (tr ++ tr'' ++ [::])
                  by (rewrite app_nil_r; auto).
                econstructor; eauto.
                rewrite app_nil_r.
                now econstructor.
              + subst.
                apply app_inv_head in H6. subst.
                clear Hexec.
                rewrite <- app_assoc.
                econstructor.
                eauto.
                specialize (IHU U' U'' (tr ++ tr'0) tr''0 tr'' tp'0 m'0 tp' m' tp'' m'').
                rewrite app_assoc.
                eapply IHU.
                rewrite <- app_assoc.
                now eassumption.
                rewrite! app_assoc in Hstep.
                rewrite! app_assoc.
                assumption.
          Qed.
          Lemma app_assoc_l:
            forall (A : Type) (l m n : seq.seq A),
              l ++ m ++ n = l ++ (m ++ n).
          Admitted.
                                                                                       
    (** FineConc is spinlock well-synchronized, strengthened version of the theorem*)
    Theorem fineConc_spinlock_strong:
      forall U U0 U' tr tr0 tr' tp m tp0 m0 tp' m'
        (Hsynced: spinlock_synchronized (tr0 ++ tr))
        (Hexec0: multi_fstep (U0, tr0, tp0) m0 (U, tr0 ++ tr, tp) m)
        (Hexec: multi_fstep (U, tr0 ++ tr, tp) m (U', tr0 ++ tr ++ tr', tp') m'),
        spinlock_synchronized (tr0 ++ tr ++ tr').
    Proof.
      intro.
      induction U; intros.
      - inversion Hexec. subst.
        apply app_inv_head in H3.
        rewrite <- app_nil_r in H3 at 1;
          apply app_inv_head in H3;
          subst.
        rewrite catA cats0.
        assumption.
      - inversion Hexec.
        + apply app_inv_head in H3.
          rewrite <- app_nil_r in H3 at 1;
            apply app_inv_head in H3;
            subst.
          rewrite catA cats0.
          assumption.
        + subst.
          replace (tr0 ++ tr ++ tr') with
          ((tr0 ++ tr) ++ tr') in H6 by (rewrite app_assoc; auto). 
          apply app_inv_head in H6. subst.
          rewrite <- app_assoc in H8.
          pose proof H8 as Hfstep.
          eapply fineConc_step_synchronized in H8; eauto.
          specialize (IHU U0 U' (tr ++ tr'0) tr0 tr'').
          assert (Heq: cat tr0 (cat tr (app tr'0 tr'')) = tr0 ++ (tr ++ tr'0)%list ++ tr'')
            by (rewrite <- app_assoc_l;
                rewrite! app_assoc;
                reflexivity).
          rewrite Heq.
          eapply IHU with (tp0 := tp0) (tp := tp'0) (m0 := m0) (m := m'0).
          rewrite <- app_assoc_l.
          assumption.
          eapply multi_fstep_snoc; eauto.
          rewrite! app_assoc.
          rewrite! app_assoc in H9.
          eassumption.
    Qed.

    (** FineConc is spinlock well-synchronized*)
    Corollary fineConc_spinlock:
      forall U tr tp m tp' m'
        (Hexec: multi_fstep (U, [::], tp) m ([::], tr, tp') m'),
        spinlock_synchronized tr.
    Proof.
      intros.
      do 2 rewrite <- app_nil_l.
      eapply fineConc_spinlock_strong with (U0 := U) (tp0 := tp) (m0 := m);
        eauto.
      simpl.
      intros ? ? ? ? ? Hcontra.
      rewrite nth_error_nil in Hcontra. discriminate.
      simpl.
      now econstructor.
    Qed.
                                                                                      

                                                                                      