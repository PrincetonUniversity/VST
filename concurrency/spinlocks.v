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
Require Import concurrency.dry_machine_lemmas.
Require Import concurrency.executions.
Require Import Coqlib.
Require Import msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module SpinLocks (SEM: Semantics)
       (SemAxioms: SemanticsAxioms SEM)
       (Machines: MachinesSig with Module SEM := SEM)
       (AsmContext: AsmContext SEM Machines).
  Import Machines DryMachine ThreadPool AsmContext.
  Import event_semantics.
  Import Events.

  Module ThreadPoolWF := ThreadPoolWF SEM Machines.
  Module CoreLanguage := CoreLanguage SEM SemAxioms.
  Module CoreLanguageDry := CoreLanguageDry SEM SemAxioms DryMachine.
  Module StepLemmas := StepLemmas SEM Machines.          
  Module Executions := Executions SEM Machines AsmContext.

  Import Executions CoreLanguage CoreLanguageDry ThreadPoolWF StepLemmas.

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
    Lemma ev_elim_stable:
      forall m m' b ofs es
        (Hvalid: Mem.valid_block m b)
        (Hperm: Mem.perm_order'' (Some Writable)
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
        assert (Hperm': Mem.perm_order'' (Some Writable) (permission_at (restrPermMap (Hcmpt tid Htid).1) bl ofs' Cur))
          by (eapply po_trans; eauto; simpl; eauto using perm_order).
        apply (proj2 (restrPermMap_valid (Hcmpt tid Htid).1 bl)) in Hvalid.
        pose proof (ev_elim_stable _ _ _ Hvalid Hperm' H) as Heq.
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
          rewrite Hlength in Hintv.
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
        (action ev = Free /\ deadLocation tp' m' b ofs) \/
        (action ev = Spawn) \/
        (action ev = Mklock /\
         thread_id ev = tidn /\
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
        (Hexec: multi_fstep (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
        (Hreadable: Mem.perm_order' ((getThreadR cnti).1 !! b ofs) Readable)
        (Hperm: Mem.perm_order'' ((getThreadR cnti).1 !! b ofs)
                                 ((getThreadR cntj).1 !! b ofs))
        (Hperm': (getThreadR cnti).1 !! b ofs <> (getThreadR cntj).1 !! b ofs),
        
      exists tr_pre tru U'' U''' tp_pre m_pre tp_dec m_dec,
        multi_fstep (U, tr, tpi) mi (U', tr ++ tr_pre, tp_pre) m_pre /\
        FineConc.MachStep the_ge (U', tr ++ tr_pre, tp_pre) m_pre
                          (U'', tr ++ tr_pre ++ tru, tp_dec) m_dec /\
        multi_fstep (U'', tr ++ tr_pre ++ tru, tp_dec) m_dec
                       (U''', tr ++ tr',tpj) mj /\
        ( exists evu,
          (List.In evu tru /\ action evu = Free /\ deadLocation tpj mj b ofs) \/
         (tru = [:: evu] /\ action evu = Spawn) \/
         (tru = [:: evu] /\ action evu = Mklock /\ thread_id evu = tidn /\
          match location evu with
          | Some (addr, sz) =>
            b = addr.1 /\
            Intv.In ofs (addr.2, addr.2 + (Z.of_nat sz))%Z
          | None => False
          end) \/
         (tru = [:: evu] /\ action evu = Release /\
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
        (Hexec: multi_fstep (U, tr, tpi) mi (U', tr ++ tr', tpj) mj)
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
    
    Lemma nth_error_app_inv:
      forall (A : Type) (i : nat) (v: A) (ys xs : seq.seq A), nth_error xs i = Some v ->
                                                       nth_error (xs ++ ys) i = Some v.
    Admitted.

    Lemma app_assoc_l:
      forall (A : Type) (l m n : seq.seq A),
        l ++ m ++ n = l ++ (m ++ n).
    Admitted.

    Lemma free_list_cases:
      forall l m m' b ofs
        (Hfree: Mem.free_list m l = Some m'),
        (permission_at m b ofs Cur = Some Freeable /\
         permission_at m' b ofs Cur = None) \/
        (permission_at m b ofs Cur = permission_at m' b ofs Cur).
    Proof.
    Admitted.

    Lemma elim_perm_valid_block:
      forall m T m' b ofs ofs' bytes
        (Hintv: Intv.In ofs' (ofs, (ofs + Z.of_nat (length bytes))%Z))
        (Helim: ev_elim m T m')
        (Hvalid: Mem.valid_block m b),
        (** Either the location was freed*)
        (permission_at m b ofs' Cur = Some Freeable /\ permission_at m' b ofs' Cur = None) \/
        (** or it wasn't and the operation denoted by the event implies the permission*)
        ((List.In (event_semantics.Write b ofs bytes) T ->
          Mem.perm_order'' (permission_at m b ofs' Cur) (Some Writable) /\
          Mem.perm_order'' (permission_at m' b ofs' Cur) (Some Writable)) /\
         (forall n,
             List.In (event_semantics.Read b ofs n bytes) T ->
             Mem.perm_order'' (permission_at m b ofs' Cur) (Some Readable) /\
             Mem.perm_order'' (permission_at m' b ofs' Cur) (Some Readable))).
    Proof.
      intros.
      generalize dependent m'.
      generalize dependent m.
      induction T as [| ev]; intros.
      - inversion Helim; subst.
        right; split; intros; simpl in H; by exfalso.
      - simpl in Helim.
        destruct ev.
        + destruct Helim as [m'' [Hstore Helim']].
          eapply Mem.storebytes_valid_block_1 in Hvalid; eauto.
          destruct (IHT _ Hvalid _ Helim') as [? | [Hwrite Hread]].
          * pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Hstore b ofs') as Heq.
            rewrite! getCurPerm_correct in Heq.
            rewrite Heq.
            left; assumption.
          * assert (in_free_list_trace b ofs' T \/ ~ in_free_list_trace b ofs' T) as Hfree
                by (apply EM).
            destruct Hfree as [Hfree | HnotFree].
            { (** If (b, ofs') was freed in the trace T*)
              eapply ev_elim_free_1 in Hfree; eauto.
              destruct Hfree as [? [? ?]].
              left.
              pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Hstore b ofs') as Heq.
              rewrite! getCurPerm_correct in Heq.
              rewrite Heq. now eauto.
            }
            { (** If [(b,ofs')] waas not freed in [T]*)
              right.
              eapply ev_elim_free_2 in HnotFree; eauto.
              rewrite <- HnotFree.
              pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Hstore b ofs') as Heq.
              rewrite! getCurPerm_correct in Heq.
              rewrite <- Heq.
              clear Heq.
              split.
              - intros Hin.
                simpl in Hin.
                destruct Hin as [Heq | Hin].
                + inv Heq.
                  apply Mem.storebytes_range_perm in Hstore.
                  specialize (Hstore _ Hintv).
                  unfold Mem.perm, permission_at in *.
                  rewrite <- po_oo.
                  split;
                    now assumption.
                + specialize (Hwrite Hin).
                  pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Hstore b ofs') as Heq.
                  rewrite! getCurPerm_correct in Heq.
                  rewrite Heq.
                  destruct Hwrite;
                    split;
                    now assumption.
              - intros n Hin.
                simpl in Hin.
                destruct Hin as [Heq | Hin].
                discriminate.
                specialize (Hread _ Hin).
                pose proof (MemoryLemmas.mem_storebytes_cur _ _ _ _ _ Hstore b ofs') as Heq.
                rewrite! getCurPerm_correct in Heq.
                rewrite Heq.
                destruct Hread; split;
                  now assumption.
            }
        + (** Case the new operation is a read*)
          destruct Helim as [Hload Helim'].
          destruct (IHT _ Hvalid _ Helim') as [? | [Hwrite Hread]].
          * left; assumption.
          * assert (in_free_list_trace b ofs' T \/ ~ in_free_list_trace b ofs' T) as Hfree
                by (apply EM).
            destruct Hfree as [Hfree | HnotFree].
            { (** If (b, ofs') was freed in the trace T*)
              eapply ev_elim_free_1 in Hfree; eauto.
              destruct Hfree as [? [? ?]].
              left.
              now eauto.
            }
            { (** If [(b,ofs')] waas not freed in [T]*)
              right.
              eapply ev_elim_free_2 in HnotFree; eauto.
              rewrite <- HnotFree.
              split.
              - intros Hin.
                simpl in Hin.
                destruct Hin as [Heq | Hin];
                  first by discriminate.
                destruct (Hwrite Hin).
                split;
                  now assumption.
              - intros n0 Hin.
                simpl in Hin.
                destruct Hin as [Heq | Hin].
                + inv Heq.
                  pose proof (Mem.loadbytes_length _ _ _ _ _ Hload) as Hlength.
                  destruct (zle n0 0).
                  * exfalso.
                    eapply Mem.loadbytes_empty with (m := m) (b := b) (ofs := ofs) in l.
                    rewrite Hload in l. inv l.
                    unfold Intv.In in Hintv. simpl in Hintv.
                    rewrite Z.add_0_r in Hintv.
                    ssromega.
                  * rewrite Hlength in Hintv.
                    erewrite nat_of_Z_eq in Hintv by omega.
                    apply Mem.loadbytes_range_perm in Hload.
                    specialize (Hload _ Hintv).
                    unfold Mem.perm, permission_at in *.
                    split;
                      now assumption.
                + split; eapply Hread;
                    now eauto.
            }
        + (** Case thew new operation allocated memory*)
          destruct Helim as [m'' [Halloc Helim']].
          pose proof (Mem.valid_block_alloc _ _ _ _ _ Halloc _ Hvalid) as Hvalid'.
          destruct (IHT _ Hvalid' _ Helim') as [Heq | [Hwrite Hread]].
          * erewrite <- MemoryLemmas.permission_at_alloc_1 in Heq by eauto.
            left; eauto.
          * assert (in_free_list_trace b ofs' T \/ ~ in_free_list_trace b ofs' T) as Hfree
                by (apply EM).
            destruct Hfree as [Hfree | HnotFree].
            { (** If (b, ofs') was freed in the trace T*)
              eapply ev_elim_free_1 in Hfree; eauto.
              destruct Hfree as [? [? ?]].
              left.
              erewrite MemoryLemmas.permission_at_alloc_1 by eauto.
              now eauto.
            }
            { (** If [(b,ofs')] waas not freed in [T]*)
              right.
              eapply ev_elim_free_2 in HnotFree; eauto.
              rewrite <- HnotFree.
              split; intros; simpl in H;
              destruct H; try (discriminate);
                erewrite MemoryLemmas.permission_at_alloc_1 by eauto;
                [split; eapply Hwrite | split; eapply Hread];
                now eauto.
            }
        + (** Case the new operation freed memory*)
          destruct Helim as [m'' [Hfree Helim']].
          assert (Hvalid': Mem.valid_block m'' b)
            by (unfold Mem.valid_block in *; erewrite nextblock_freelist by eauto; eauto).
          destruct (IHT _ Hvalid' _ Helim') as [Heq | [Hwrite Hread]].
          * assert (Hperm: Mem.perm m'' b ofs' Cur Freeable)
              by (unfold Mem.perm; unfold permission_at in Heq;
                  rewrite Heq.1; simpl; auto using perm_order).
            pose proof (perm_freelist _ _ _ _ _ Cur Freeable Hfree Hperm) as Hperm'.
            unfold Mem.perm in Hperm'.
            destruct Heq.
            left; split; auto.
            unfold permission_at.
            destruct ((Mem.mem_access m) !! b ofs' Cur) as [p|]; simpl in Hperm';
              inv Hperm'; reflexivity.
          * eapply free_list_cases with (b := b) (ofs := ofs') in Hfree.
            destruct Hfree as [[Heq1 Heq2] | Heq].
            left. split; auto.
            erewrite <- ev_elim_stable; eauto.
            rewrite Heq2.
            now apply po_None.
            rewrite Heq.
            right; split; intros; simpl in H;
              destruct H; try (discriminate);
                eauto.
    Qed.

    Lemma elim_perm_invalid_block:
      forall m T m' b ofs ofs' bytes
        (Hintv: Intv.In ofs' (ofs, (ofs + Z.of_nat (length bytes))%Z))
        (Helim: ev_elim m T m')
        (Hvalid: ~ Mem.valid_block m b),
        (** or it wasn't and the operation denoted by the event implies the permission*)
        (List.In (event_semantics.Write b ofs bytes) T ->
         (permission_at m' b ofs' Cur = Some Freeable \/ permission_at m' b ofs' Cur = None)
         /\ Mem.valid_block m' b) /\
         (forall n,
             List.In (event_semantics.Read b ofs n bytes) T ->
             (permission_at m' b ofs' Cur = Some Freeable \/ permission_at m' b ofs' Cur =  None) /\ Mem.valid_block m' b).
    Proof.
    Admitted.

    Lemma fstep_ev_perm:
      forall U tr tp m U' tr_pre tr_post tp' m' ev
        (Hstep: FineConc.MachStep the_ge (U, tr, tp) m (U', tr ++ tr_pre ++ [:: ev] ++ tr_post , tp') m'),
        (action ev = Write ->
         forall (cnt: containsThread tp (thread_id ev)) (cnt': containsThread tp' (thread_id ev)),
           match location ev with
           | Some (b, ofs, sz) =>
             forall ofs', Intv.In ofs' (ofs, ofs + Z.of_nat sz)%Z ->
                     (Mem.valid_block m b ->
                      Mem.perm_order'' ((getThreadR cnt).1 !! b ofs') (Some Writable)) /\
                     (Mem.perm_order'' ((getThreadR cnt').1 !! b ofs') (Some Writable) \/
                      deadLocation tp' m' b ofs')
           | None => False
           end) /\
        (action ev = Read ->
         forall (cnt: containsThread tp (thread_id ev)) (cnt': containsThread tp' (thread_id ev)),
           match location ev with
           | Some (b, ofs, sz) =>
             forall ofs', Intv.In ofs' (ofs, ofs + Z.of_nat sz)%Z ->
                     (Mem.valid_block m b ->
                      Mem.perm_order'' ((getThreadR cnt).1 !! b ofs') (Some Readable)) /\
                     (Mem.perm_order'' ((getThreadR cnt').1 !! b ofs') (Some Readable) \/
                      deadLocation tp' m' b ofs')
           | None => False
           end).
    Proof.
      intros.
      inversion Hstep; simpl in *;
        try (apply app_eq_nil in H4;
             subst; destruct tr_pre;
             simpl in H4; discriminate).
      - (** case of internal steps*)
        apply app_inv_head in H5; subst.
        (** proof that the [thread_id] of the event and the head of the schedule match*)
        assert (Hin: List.In ev (map [eta internal tid] ev0))
          by (rewrite H5; apply in_app; right; simpl; auto).
        apply in_map_iff in Hin.
        destruct Hin as [mev [? Hin]].
        subst.
        simpl in *.
        inversion Htstep; subst.
        split; intros Haction Hcnt Hcnt';
          destruct mev; try discriminate;
            pf_cleanup.
        + (** Write case*)
          intros ofs' Hintv.
          pose proof (ev_step_elim _ _ _ _ _ _ _ Hcorestep) as Helim.
          destruct Helim as [Helim _].
          (** By case analysis on whether [b] was a valid block or not*)
          destruct (valid_block_dec m b).
          { (** case [b] is a valid block in [m]*)
            eapply elim_perm_valid_block in Helim; eauto.
            destruct Helim as [[Hfreeable Hempty] | [Hwrite Hread]].
            - (** case the block was freed by the internal step. This implies that
            [(b, ofs)] is now a [deadLocation]*)
              split.
              + intros. rewrite restrPermMap_Cur in Hfreeable.
                rewrite Hfreeable. simpl; now constructor.
              + right.
                constructor; eauto.
                eapply ev_step_validblock with (b := b) in Hcorestep.
                now eauto.
                now eauto.
                intros i cnti.
                rewrite restrPermMap_Cur in Hfreeable.
                pose proof (cntUpdate' _ _ _ cnti) as cnti0.
                eapply invariant_freeable_empty_threads with (j := i) (cntj := cnti0) in Hfreeable;
                  eauto.
                destruct Hfreeable.
                destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
                subst. pf_cleanup.
                rewrite! gssThreadRes.
                simpl.
                rewrite getCurPerm_correct.
                split;
                  now auto.
                rewrite! gsoThreadRes;
                  now auto.
                intros.
                rewrite gsoThreadLPool in H.
                rewrite restrPermMap_Cur in Hfreeable.
                apply invariant_freeable_empty_locks with (laddr := l) (rmap := pmap) in Hfreeable;
                  now eauto.
            - (** case the block was not freed*)
              split.
              + intros. 
                rewrite! restrPermMap_Cur in Hwrite.
                eapply Hwrite;
                  now eauto.
              + rewrite gssThreadRes.
                simpl.
                rewrite getCurPerm_correct.
                left; eapply Hwrite;
                  now eauto.
          }
          { (** case [b] is an invalid block in [m]*)
            eapply elim_perm_invalid_block in Helim; eauto.
            split;
              first by (intros; exfalso; eauto).
            destruct Helim as [Hwrite _].
            rewrite gssThreadRes. simpl.
            destruct (Hwrite Hin) as [[Hallocated | Hfreed] Hvalid'].
            - left.
              rewrite getCurPerm_correct.
              rewrite Hallocated.
              simpl; now constructor.
            - right.
              econstructor; eauto.
              + intros.
                pose proof (cntUpdate' _ _ _ cnti) as cnti0.              
                destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
                * subst. pf_cleanup.
                  rewrite gssThreadRes.
                  simpl. rewrite getCurPerm_correct.
                  split; auto.
                  now eapply (mem_compatible_invalid_block _ Hcmpt n).1.
                * rewrite gsoThreadRes; auto.
                  now eapply (mem_compatible_invalid_block _ Hcmpt n).1.
              + intros.
                rewrite gsoThreadLPool in H.
                split;
                  eapply (mem_compatible_invalid_block _ Hcmpt n).2;
                  now eauto.
          }
        + (** Read case*)
          intros ofs' Hintv.
          pose proof (ev_step_elim _ _ _ _ _ _ _ Hcorestep) as Helim.
          destruct Helim as [Helim _].
          (** By case analysis on whether [b] was a valid block or not*)
          destruct (valid_block_dec m b).
          { (** case [b] is a valid block in [m]*)
            eapply elim_perm_valid_block in Helim; eauto.
            destruct Helim as [[Hfreeable Hempty] | [Hwrite Hread]].
            - (** case the block was freed by the internal step. This implies that
            [(b, ofs)] is now a [deadLocation]*)
              split.
              + intros. rewrite restrPermMap_Cur in Hfreeable.
                rewrite Hfreeable. simpl; now constructor.
              + right.
                constructor; eauto.
                eapply ev_step_validblock with (b := b) in Hcorestep.
                now eauto.
                now eauto.
                intros i cnti.
                rewrite restrPermMap_Cur in Hfreeable.
                pose proof (cntUpdate' _ _ _ cnti) as cnti0.
                eapply invariant_freeable_empty_threads with (j := i) (cntj := cnti0) in Hfreeable;
                  eauto.
                destruct Hfreeable.
                destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
                subst. pf_cleanup.
                rewrite! gssThreadRes.
                simpl.
                rewrite getCurPerm_correct.
                split;
                  now auto.
                rewrite! gsoThreadRes;
                  now auto.
                intros.
                rewrite gsoThreadLPool in H.
                rewrite restrPermMap_Cur in Hfreeable.
                apply invariant_freeable_empty_locks with (laddr := l) (rmap := pmap) in Hfreeable;
                  now eauto.
            - (** case the block was not freed*)
              split.
              + intros. 
                rewrite! restrPermMap_Cur in Hread.
                eapply Hread;
                  now eauto.
              + rewrite gssThreadRes.
                simpl.
                rewrite getCurPerm_correct.
                left; eapply Hread;
                  now eauto.
          }
          { (** case [b] is an invalid block in [m]*)
            eapply elim_perm_invalid_block in Helim; eauto.
            split;
              first by (intros; exfalso; eauto).
            destruct Helim as [_ Hread].
            rewrite gssThreadRes. simpl.
            destruct (Hread _ Hin) as [[Hallocated | Hfreed] Hvalid'].
            - left.
              rewrite getCurPerm_correct.
              rewrite Hallocated.
              simpl; now constructor.
            - right.
              econstructor; eauto.
              + intros.
                pose proof (cntUpdate' _ _ _ cnti) as cnti0.              
                destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
                * subst. pf_cleanup.
                  rewrite gssThreadRes.
                  simpl. rewrite getCurPerm_correct.
                  split; auto.
                  now eapply (mem_compatible_invalid_block _ Hcmpt n0).1.
                * rewrite gsoThreadRes; auto.
                  now eapply (mem_compatible_invalid_block _ Hcmpt n0).1.
              + intros.
                rewrite gsoThreadLPool in H.
                split;
                  eapply (mem_compatible_invalid_block _ Hcmpt n0).2;
                  now eauto.
          }
      - (** case of external steps *)
        apply app_inv_head in H5.
        destruct (tr_pre); simpl;
          inv H5.
        simpl; destruct ev0; split; intros;
          discriminate.
        destruct l; now inv H9.
    Qed.

    Lemma multi_fstep_mem_compatible :
      forall U tr tp m U' tr' tp' m'
        (Hexec: multi_fstep (U, tr, tp) m (U', tr', tp') m'),
        mem_compatible tp m \/ tp = tp' /\ m = m' /\ U = U' /\ tr = tr'.
    Proof.
      intros.
      inversion Hexec; subst.
      right; auto.
      eapply fstep_mem_compatible in H7.
      left; auto.
    Qed.

    Lemma multi_fstep_invariant :
      forall U tr tp m U' tr' tp' m'
        (Hexec: multi_fstep (U, tr, tp) m (U', tr', tp') m'),
        invariant tp \/ tp = tp' /\ m = m' /\ U = U' /\ tr = tr'.
    Proof.
      intros.
      inversion Hexec; subst.
      right; auto.
      eapply fstep_invariant in H7.
      left; auto.
    Qed.

    Lemma multi_fstep_valid_block:
      forall U tr tp m U' tr' tp' m' b
        (Hexec: multi_fstep (U, tr, tp) m (U', tr', tp') m')
        (Hvalid: Mem.valid_block m b),
        Mem.valid_block m' b.
    Proof.
      intros.
      induction Hexec.
      assumption.
    Admitted.

    Lemma perm_order_incompatible:
      forall p p'
        (Hreadable: Mem.perm_order'' p (Some Readable))
        (Hwritable: Mem.perm_order'' p' (Some Writable)),
        perm_union p p' = None.
    Proof.
      intros.
      destruct p as [p0|], p' as [p0'|];
        try destruct p0;
        try destruct p0';
        simpl in *; try (reflexivity);
          try (by inversion Hwritable);
          try (by inversion Hreadable).
    Qed.

    (** [FineConc.MachStep] preserves [spinlock_synchronized]*)
    Lemma fineConc_step_synchronized:
      forall U0 U U'  tr tp0 m0 tp m tp' m' tr'
        (Hexec: multi_fstep (U0, [::], tp0) m0 (U, tr, tp) m)
        (Hstep: FineConc.MachStep the_ge (U, tr, tp) m (U', tr ++ tr', tp') m')
        (Hsynchronized: spinlock_synchronized tr),
        spinlock_synchronized (tr ++ tr').
    Proof.
      intros.
      (** Consider two competing events evi and evj*)
      intros i j evi evj Hneq Hi Hj Hcompetes.
      destruct (lt_dec j (length tr)) as [Hj_in_tr | Hj_not_in_tr].
      - (** If [evj] is in [tr] then so is [evi], by [i < j] and the goal is
        trivial by [Hsynchronized]*)
        assert (Hi_in_tr: (i < length tr)%coq_nat) by ssromega.
        eapply nth_error_app1 with (l' := tr') in Hj_in_tr.
        eapply nth_error_app1 with (l' := tr') in Hi_in_tr.
        rewrite Hi_in_tr in Hi.
        rewrite Hj_in_tr in Hj.
        destruct (Hsynchronized i j evi evj Hneq Hi Hj Hcompetes) as
            [[u [v [eu [ev [Horder [Hevu [Hevv [Hactu [Hactv Hloc]]]]]]]]] |
             [u [eu [Horder [Hu Hactu]]]]].
        + left.
          exists u, v, eu, ev.
          repeat (split; eauto using nth_error_app_inv).
        + right.
          exists u, eu.
          repeat (split; eauto using nth_error_app_inv).
      - (** Hence [evj] is in [tr'] *)
        (** By [maximal_competing] there must exist some maximal event [ek] s.t. it competes with [evj]*)
        destruct (maximal_competing _ _ _ Hneq Hi Hj Hcompetes)
          as (k & evk & Horder & Hk & Hcompetes_kj & Hmaximal).
        (** [evk] cannot be in [tr'] because this would imply that it is from
        the same thread as [j] and hence not competing*)
        assert (Hk_not_in_tr': (k < length tr)%coq_nat)
          by admit.
        erewrite nth_error_app1 in Hk by assumption.
        (** By case analysis on the type of the competing events [evk] and [evj]*)
        destruct (is_internal evk && is_internal evj) eqn:Hevk_evj.
        { (** If [evk] and [evj] are [internal] events *)
          move/andP:Hevk_evj=>[Hinternal_k Hinternal_j].
          destruct Hcompetes_kj as (Hthreads_neq & Hsame_loc & Hcactionk & Hcactionj & His_write & _).
          specialize (His_write Hinternal_k Hinternal_j).
          (** To find the state that corresponds to [evk] we break the execution
          in [multi_fstep] chunks and the [FineConc.Machstep] that produces [evk]*)
          destruct (multi_fstep_inv _ _ Hk Hexec)
            as (Uk & Uk' & tp_k & m_k & tr0 & pre_k & post_k & tp_k'
                & m_k' & Hexeck & Hstepk & Hexec' & Hk_index).
          erewrite! app_nil_l in *.

          (** *** Useful Results*)
          (** tr' will be of the form tr'_pre ++ evj ++ tr'_post*)
          assert (Htr': exists tr'_pre tr'_post, tr' = tr'_pre ++ [:: evj] ++ tr'_post).
          { erewrite nth_error_app2 in Hj by ssromega.
            apply nth_error_split in Hj.
            destruct Hj as (tr'_pre & tr'_post & ? & ?).
            subst.
            exists tr'_pre, tr'_post.
            reflexivity.
          }
          destruct Htr' as (tr'_pre & tr'_post & Heq). subst.

          (** The threads that generated [evk] and [evj] are
          valid threads in the respective thread pools*)
          assert (cntk: containsThread tp_k (thread_id evk))
            by admit.
          assert (cntk': containsThread tp_k' (thread_id evk))
            by admit.

          assert (cntj: containsThread tp (thread_id evj))
            by admit.
          assert (cntj': containsThread tp' (thread_id evj))
            by admit.

          (** [evk] and [evj] are Read/Write events*)
          (** evk is either a [Write] or [Read] event*)
          assert (Hactionk: action evk = Write \/ action evk = Read).
          { destruct evk as [tidk evk|?]; simpl in Hinternal_k; try by exfalso.
            destruct evk; simpl in Hcactionk; try (by exfalso);
              simpl; now auto.
          }
          (** evj is either a [Write] or [Read] event*)
          assert (Hactionj: action evj = Write \/ action evj = Read).
          { destruct evj as [tidj evj|?]; simpl in Hinternal_j; try by exfalso.
            destruct evj; simpl in Hcactionj; try (by exfalso);
              simpl; now auto.
          }

          (** [location] is defined for [evk] as it is a [Read] or [Write] event*)
          assert (Hloc_k: exists bk ofsk szk, location evk = Some (bk, ofsk, szk)).
          { destruct Hactionk; destruct evk as [? evk | ? evk];
              destruct evk; try (discriminate);
                simpl;
                eexists; eauto.
          }
          (** [location] is defined for [evj] as it is a [Read] or [Write] event*)
          assert (Hloc_j: exists bj ofsj szj, location evj = Some (bj, ofsj, szj)).
          { destruct Hactionj; destruct evj as [? evj | ? evj];
              destruct evj; try (discriminate);
                simpl;
                eexists; eauto.
          }
          destruct Hloc_k as (b & ofsk & szk & Hloc_k).
          destruct Hloc_j as (b' & ofsj & szj & Hloc_j).
          (** Find the competing byte*)
          unfold sameLocation in Hsame_loc.
          rewrite Hloc_k Hloc_j in Hsame_loc.
          destruct Hsame_loc as [? [ofs [Hintvk Hintvj]]]; subst b'.

          pose proof (multi_fstep_trace_monotone Hexec') as Heq.
          subst.
          destruct Heq as [tr'' Heq]; subst.

          (** *** Proving that the permissions required for [evk] and [evj]
              are above [Readable] and incompatible*)

          assert (Hpermissions: Mem.perm_order'' ((getThreadR cntk').1 !! b ofs) (Some Readable) /\
                                Mem.perm_order'' ((getThreadR cntj).1 !! b ofs) (Some Readable) /\
                                (Mem.perm_order'' ((getThreadR cntk').1 !! b ofs) (Some Writable) \/
                                 Mem.perm_order'' ((getThreadR cntj).1 !! b ofs) (Some Writable))
                 ).
          { destruct(fstep_ev_perm _ _ _ Hstepk) as [Hwritek Hreadk].
            destruct(fstep_ev_perm _ _ _ Hstep) as [Hwritej Hreadj].
            rewrite Hloc_j in Hwritej Hreadj.
            rewrite Hloc_k in Hwritek, Hreadk.
            (** First we prove that [(b, ofs)] cannot be a [deadLocation] *)
            assert (Hnotdead: ~ deadLocation tp_k' m_k' b ofs).
            { (** Suppose that it was. [deadLocation] is preserved by
            [multi_fstep] and hence [evj] would not have sufficient permissions
            to perform a [Read] or [Write]*)

              intros Hdead.
              (** [(b,ofs)] is [deadLocation] at [tp], [m]*)
              eapply multi_fstep_deadLocation with (tp' := tp) (m' := m) in Hdead; eauto.
              (** Hence [b] is a valid block in [m]*)
              inversion Hdead.
              (** Moreover permissions of the machine on [(b, ofs)] are None*)
              destruct (Hthreads _ cntj) as [Hperm1 _].
              (** The permissions of the thread [thread_id evj] must be above
              [Readable] by the fact that [evj] is a [Read] or [Write] event,
              which leads to a contradiction*)
              destruct Hactionj as [Hactionj | Hactionj];
                [destruct (Hwritej Hactionj cntj cntj' ofs Hintvj) as [Hperm _] |
                 destruct (Hreadj Hactionj cntj cntj' ofs Hintvj) as [Hperm _]];
                specialize (Hperm Hvalid);
                rewrite Hperm1 in Hperm; simpl in Hperm;
                  now auto.
            }

            assert (Hvalid: forall p, Mem.perm_order'' ((getThreadR cntk').1 !! b ofs) (Some p) ->
                            Mem.valid_block m b).
            { intros.
              eapply multi_fstep_valid_block; eauto.
              eapply perm_order_valid_block; eauto.
              destruct (multi_fstep_mem_compatible Hexec') as [Hcompk' | Heq].
              - destruct Hcompk'.
                now eapply (compat_th0 _ cntk').1.
              - destruct Heq as [? [? _]]; subst.
                eapply fstep_mem_compatible in Hstep.
                now eapply Hstep.
            }

            destruct Hactionk as [Hactionk | Hactionk];
              [destruct (Hwritek Hactionk cntk cntk' ofs Hintvk) as [_ [Hpermk | Hcontra]] |
               destruct (Hreadk Hactionk cntk cntk' ofs Hintvk) as [_ [Hpermk | Hcontra]]];
              try (by exfalso); split;
                try (eapply po_trans; eauto;
                     now constructor);
                destruct Hactionj as [Hactionj | Hactionj];
              try (destruct (Hwritej Hactionj cntj cntj' ofs Hintvj) as [Hpermj _]);
              try (destruct (Hreadj Hactionj cntj cntj' ofs Hintvj) as [Hpermj _]);
              specialize (Hpermj (Hvalid _ Hpermk));
              repeat match goal with
                     | [H1: action _ = Read, H2: action _ = Read |- _] =>
                       rewrite H1 H2 in His_write; destruct His_write; discriminate
                     | [ |- _ /\ _] =>
                       split
                     | [H: Mem.perm_order'' ?X ?Y |- Mem.perm_order'' ?X ?Y] =>
                       assumption
                     | [ |- Mem.perm_order'' _ _] =>
                       eapply po_trans; eauto; simpl; now constructor
                     end;
              eauto.
          }
          destruct Hpermissions as (Hperm_k & Hperm_j & Hwritable_kj).
          (** Moreover by the [invariant] permissions of [thread_id evk] and
          [thread_id evj] will have compatible permissions at [tpk'] *)
          assert (Hinvk': invariant tp_k').
          { destruct (multi_fstep_invariant Hexec') as [Hinvk' | [? _]].
              - now eapply Hinvk'.
              - subst.
                eapply fstep_invariant in Hstep.
                now eapply Hstep.
          }

          assert (cntk'_j: containsThread tp (thread_id evk))
            by admit.
          (** By the [invariant] permissions of [thread_id evk] and
          [thread_id evj] will have compatible permissions at [tp] *)
          assert (Hinv: invariant tp)
                 by (eapply fstep_invariant; eauto).
          assert (Hcompatible_j: perm_union ((getThreadR cntk'_j).1 !! b ofs) ((getThreadR cntj).1 !! b ofs))
            by (destruct ((no_race_thr Hinv cntk'_j cntj Hthreads_neq).1 b ofs) as [pu Hcompatiblek'j];
                rewrite Hcompatiblek'j; auto).
          (** This implies that permission of thread [thread_id evk] on that location has dropped*)
          assert (Hdropped: Mem.perm_order'' ((getThreadR cntk').1 !! b ofs) ((getThreadR cntk'_j).1 !! b ofs) /\
                  (getThreadR cntk').1 !! b ofs <> (getThreadR cntk'_j).1 !! b ofs). 
          { clear - Hcompatible_j Hperm_k Hperm_j Hwritable_kj.
            destruct (((getThreadR cntk')#1) # b ofs) as [pk' | ];
              simpl in Hperm_k; inversion Hperm_k; subst;
                destruct (((getThreadR cntj)#1) # b ofs);
                simpl in Hperm_j; inversion Hperm_j; subst;
                  simpl in Hwritable_kj;
                  destruct Hwritable_kj as [H1 | H2]; try (by inversion H1);
                    try (by inversion H2);
                    destruct (((getThreadR cntk'_j)#1) # b ofs) as [pk'_j|]; simpl in Hcompatible_j;
                      try (destruct pk'_j);
                      try (by exfalso);
                      simpl; split; eauto using perm_order;
                        intros Hcontra; discriminate.
          }
          (** Hence by [data_permission_decrease_execution] we have four cases for how the permissions of [thread_id evk] dropped*)
          destruct (data_permission_decrease_execution _ b ofs cntk' cntk'_j Hexec' Hperm_k Hdropped.1 Hdropped.2)
            as (tre_pre_u & tru & ? & ? & tp_pre_u & m_pre_u &
                tp_dec & m_dec & Hexec_pre_u & Hstepu & Hexec_post_u & evu & Hspec_u).
          destruct Hspec_u as [Hfreed | [Hspawned | [Hmklock | Hrelease]]].
          { (** Case permissions dropped by a [Free] event. This leads to a
          contradiction because it would be a [deadLocation]*)
            destruct Hfreed as (HIn & HFree & Hdead).
            inversion Hdead.
            specialize (Hthreads _ cntj).
            rewrite Hthreads.1 in Hperm_j.
            simpl in Hperm_j;
              by exfalso.
          }
          { (** Case permissions were dropped by a spawn event - we are done*)
            destruct Hspawned as (? & Hactionu).
            subst.
            right.
            remember (tr0 ++ pre_k ++ [:: evk] ++ post_k) as tr00.
            apply multi_fstep_trace_monotone in Hexec_post_u.
            destruct Hexec_post_u as [? Heq].
            rewrite <- app_assoc in Heq.
            apply app_inv_head in Heq. subst.
            exists (length ((((tr0 ++ pre_k) ++ [:: evk]) ++ post_k) ++ tre_pre_u)%list), evu.
            split. simpl.
            - apply/andP.
              split.
              + rewrite! app_length.
                clear - Horder. simpl.
                move/andP:Horder => [Hle ?].
                rewrite app_length in Hle.
                now ssromega.
              + clear - Hj_not_in_tr.
                erewrite! app_length in *.
                simpl in *.
                ssromega.
            - split.
              rewrite! app_assoc.
              rewrite <- app_assoc.
              rewrite <- app_assoc.
              rewrite <- addn0.
              rewrite <- nth_error_app.
              reflexivity.
              assumption.
          }
          { (** Case permissions were dropped by a Mklock event - this leads to
          a contradiction by the fact that [evu] will compete with [evj], while
          [evk] is the maximal competing event *)
            destruct Hmklock as [Htru [Hactionu [Hthreadu Hlocu]]].
            subst.
            exfalso.
            remember (tr0 ++ pre_k ++ [:: evk] ++ post_k) as tr00.
            apply multi_fstep_trace_monotone in Hexec_post_u.
            destruct Hexec_post_u as [? Heq].
            rewrite <- app_assoc in Heq.
            apply app_inv_head in Heq. subst.
            eapply (Hmaximal (length (tr0 ++ pre_k ++ [:: evk] ++ post_k ++ tre_pre_u)%list) evu).
            - rewrite! app_length.
              apply/andP.
              split.
              + simpl. ssromega.
              + clear - Hj_not_in_tr.
                rewrite! app_length in Hj_not_in_tr.
                simpl in *.
                ssromega.
            - rewrite! app_assoc.
              rewrite <- addn0.
              do 2 rewrite <- app_assoc.
              rewrite <- nth_error_app.
              reflexivity.
            - repeat split.
              + intros Hcontra.
                rewrite Hthreadu in Hcontra.
                now auto.
              + destruct (location evu) as [[[bu ofsu] szu]|] eqn:Hloc_u;
                  try (by exfalso).
                unfold sameLocation.
                rewrite Hloc_u Hloc_j.
                simpl in Hlocu.
                destruct Hlocu as [? Hintvu]; subst.
                split; auto.
                exists ofs; split; now auto.
              + destruct evu as [? evu | ? evu];
                  destruct evu; try discriminate.
                simpl. now auto.
              + destruct evu as [? evu | ? evu];
                  destruct evu; try discriminate.
                simpl. now auto.
              + intros.
                destruct evu as [? evu | ? evu];
                  destruct evu; try discriminate.
              + intros.
                left.
                assumption.
          }


    Abort.        
        
   
    
    (** FineConc is spinlock well-synchronized, strengthened version of the theorem*)
     Theorem fineConc_spinlock_strong:
      forall U U0 U' tr tr' tp m tp0 m0 tp' m'
        (Hsynced: spinlock_synchronized tr)
        (Hexec0: multi_fstep (U0, [::], tp0) m0 (U, tr, tp) m)
        (Hexec: multi_fstep (U, tr, tp) m (U', tr ++ tr', tp') m'),
        spinlock_synchronized (tr ++ tr').
    Proof.
      intro.
      induction U; intros.
      - inversion Hexec. 
        rewrite <- app_nil_r in H3 at 1;
          apply app_inv_head in H3;
          subst.
        rewrite <- catA.
        rewrite! cats0.
        assumption.
      - inversion Hexec.
        + rewrite <- app_nil_r in H3 at 1;
            apply app_inv_head in H3;
            subst.
          rewrite <- catA.
          rewrite! cats0.
          assumption.
        + subst.
          apply app_inv_head in H6; subst.
          pose proof H8 as Hfstep.
          eapply fineConc_step_synchronized in H8; eauto.
          specialize (IHU U0 U' (tr ++ tr'0) tr'').
          do 2 rewrite <- app_assoc in IHU.
          rewrite <- app_assoc_l.
          eapply IHU with (tp0 := tp0) (tp := tp'0) (m0 := m0) (m := m'0).
          eassumption.
          rewrite <- app_nil_l with (l := tr ++ tr'0).
          eapply multi_fstep_snoc; eauto.
          eauto.
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
                                                                                      

                                                                                      