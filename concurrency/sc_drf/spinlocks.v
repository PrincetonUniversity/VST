(** * Spinlock well synchronized and spinlock clean*)
Require Import compcert.lib.Axioms.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.common.sepcomp. Import SepComp.
Require Import VST.sepcomp.semantics_lemmas.

Require Import VST.concurrency.common.pos.

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

Require Import VST.concurrency.common.threadPool.
Require Import VST.concurrency.common.threads_lemmas.
Require Import VST.concurrency.common.tactics.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.common.permjoin_def.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.memory_lemmas.
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.dry_machine_step_lemmas.
Require Import VST.concurrency.sc_drf.executions.
Require Import VST.msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module SpinLocks.
  Import HybridMachine HybridMachineSig ThreadPool ThreadPoolWF
         CoreLanguage CoreLanguageDry AsmContext StepLemmas Executions.
  Import event_semantics.
  Import Events.
  
  Section SpinLocks.
    Context {Sem : Semantics}
            {SemAxioms: SemAxioms}
            {initU: seq nat}.
    Variable EM: ClassicalFacts.excluded_middle.

    Existing Instance OrdinalPool.OrdinalThreadPool.
    Existing Instance DryHybridMachine.DryHybridMachineSig.
    Existing Instance dryFineMach.
    Existing Instance bareMach.

    Existing Instance FineDilMem.
    Open Scope nat.
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
      | external _ (release _ _) => Some Release
      | external _ (acquire _ _) => Some Acquire
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
    Definition spinlock_synchronized (tr : event_trace) :=
      forall (i j : nat) ev1 ev2,
        i < j ->
        List.nth_error tr i = Some ev1 ->
        List.nth_error tr j = Some ev2 ->
        competes ev1 ev2 ->
        (exists u v eu ev,
          i <= u < v /\ v < j /\
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
    Definition spinlock_clean (tr : event_trace) :=
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

    Notation fstep := ((corestep (AsmContext.fine_semantics initU))).

    Opaque containsThread getThreadR getThreadC t lockRes.
    (** Spinlock clean for a single step*)
    Lemma fstep_clean:
      forall U U' tp m addr tr pre ev post tp' m' tidi
        (Hlock: lockRes tp addr)
        (HisLock: isLock tp addr)
        (Hlocation: sameLocation ev (external tidi (mklock addr)))
        (Hstep: fstep (U, tr, tp) m
                                  (U', tr ++ pre ++ [:: ev] ++ post, tp') m'),
        action ev <> Write /\ action ev <> Read.
    Proof.
      intros.
      inversion Hstep; simpl in *;
      try match goal with
          | [H: ?X = cat ?X ?Y |- _] =>
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
        (*destruct Hcorestep as [Helim _].*)rename Hcorestep into Helim.
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
          - pose proof ((thread_data_lock_coh _ Hinv _ cntj).1 _ Htid bl ofs') as Hcoh.
            clear - Hcoh Hperm.
            simpl in Hperm.
            destruct ((getThreadR Htid).1 !! bl ofs') as [p|]; simpl; auto;
              destruct ((getThreadR cntj).2 !! bl ofs') as [p0|]; simpl in Hperm;
                inversion Hperm; subst;
                  simpl in Hcoh; destruct p;
                    try (by exfalso); eauto using perm_order.
          - pose proof ((locks_data_lock_coh _ Hinv _ _ Hres).1 _ Htid bl ofs') as Hcoh.
            clear - Hcoh Hperm.
            simpl in Hperm.
            destruct ((getThreadR Htid).1 !! bl ofs') as [p|]; simpl; auto;
              destruct (rmap.2 !! bl ofs') as [p0|]; simpl in Hperm;
                inversion Hperm; subst;
                  simpl in Hcoh; destruct p;
                    try (by exfalso); eauto using perm_order.
        }

        (** [bl] must be a [Mem.valid_block]*)
        assert (Hvalid: Mem.valid_block m bl).
        
          by (destruct (lockRes tp (bl, ofsl)) as [rmap|] eqn:Hres; try (by exfalso);
              pose proof (lockRes_blocks _ _ Hcmpt (bl, ofsl) _ Hres);
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

    Notation multi_fstep := (@multi_step Sem FineDilMem _ DryHybridMachine.DryHybridMachineSig).
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
      apply @multi_step_inv_ext with (i := i) (ev := evi) in Hexec; auto.
      destruct Hexec as (U' & U'' & tp'' & m'' & tr'' & tp''' & m'''
                         & Hexec & Hstep & Hexec' & Hsize).
      destruct evi as [|tidi evi'];
        simpl in Hmklock. destruct m0; discriminate.
      destruct evi'; try discriminate.
      simpl in *.
      rewrite <- app_nil_r with (l := [:: external tidi (mklock a)]) in Hstep;
        rewrite <- app_nil_l with (l := [:: external tidi (mklock a)]) in Hstep;
        rewrite <- app_assoc in Hstep;
      assert (Hsched: U' = tidi :: U'')
        by (eapply step_event_sched in Hstep;
            simpl in Hstep; assumption).
      rewrite Hsched in Hstep.
      (** The thread that executed the [mklock] operation must be in the threadpool*)
      destruct (step_ev_contains _ _ _ Hstep) as [cnti cnti'].
      (** since there was a [mklock] event, [a] will be in [lockRes] and the
      thread will have lock-permission on it*)
      apply Mklock_lockRes in Hstep.
      destruct Hstep as [HlockRes''' Hperm'''].
      assert (exists trj, tr = tr'' ++ [:: external tidi (mklock a)] ++ trj)
        by (eapply multi_step_trace_monotone in Hexec';
             destruct Hexec' as [? Hexec'];
             rewrite <- app_assoc in Hexec';
             eexists; eauto).
      destruct H as [trj H].
      subst.
      rewrite catA in Hexec'.
      assert (Hj_trj:
                nth_error trj (j - length (tr'' ++ [:: external tidi (mklock a)])) =
                Some evj).
      { rewrite <- nth_error_app2.
        rewrite <- app_assoc. assumption.
        rewrite app_length. simpl. ssromega.
      }
      eapply multi_step_inv with (ev := evj) in Hexec'; eauto.
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
        { eapply multi_step_trace_monotone in Hexecj''.
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
      - (** Is there any competing with [evj] event in [tr]?*)
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

    (** Actions that require a [Readable] permission*)
    Inductive raction ev : Prop :=
    | read: action ev = Read ->
            raction ev
    | acq: action ev = Acquire ->
           raction ev
    | rel: action ev = Release ->
           raction ev
    | facq: action ev = Failacq ->
            raction ev.

    (** Actions that require a [Writable] permission*)
    Inductive waction ev : Prop:=
    | write: action ev = Write ->
             waction ev
    | mk: action ev = Mklock ->
          waction ev
    | fl: action ev = Freelock ->
          waction ev.

    Lemma compete_cases:
      forall evi evj
        (Hcompetes: competes evi evj),
        (raction evi /\ waction evj) \/
        (waction evi /\ caction evj).
    Proof.
      intros.
      destruct Hcompetes as (? & ? & Hact1 & Hact2 & Hint & Hext).
      unfold caction.
      destruct evi as [? evi | ? evi], evj as [? evj | ? evj];
        destruct evi, evj; auto 10 using raction, waction;
        simpl in *;
        try (by exfalso);
        try (destruct (Hint ltac:(auto 1) ltac:(auto 1)); discriminate);
        try (destruct (Hext ltac:(auto 2)) as [? | [? | [? | ?]]]; discriminate).
    Qed.

    Lemma fstep_ev_perm:
      forall U tr tp m U' tr_pre tr_post tp' m' ev
        (Hstep: fstep (U, tr, tp) m (U', tr ++ tr_pre ++ [:: ev] ++ tr_post , tp') m'),
        (waction ev ->
         forall (cnt: containsThread tp (thread_id ev)) (cnt': containsThread tp' (thread_id ev)),
           match location ev with
           | Some (b, ofs, sz) =>
             forall ofs', Intv.In ofs' (ofs, ofs + Z.of_nat sz)%Z ->
                     (Mem.valid_block m b ->
                      Mem.perm_order'' ((getThreadR cnt).1 !! b ofs') (Some Writable) \/
                      Mem.perm_order'' ((getThreadR cnt).2 !! b ofs') (Some Writable)) /\
                     ((Mem.perm_order'' ((getThreadR cnt').1 !! b ofs') (Some Writable) \/
                       Mem.perm_order'' ((getThreadR cnt').2 !! b ofs') (Some Writable)) \/
                      deadLocation tp' m' b ofs')
           | None => False
           end) /\
        (caction ev ->
         forall (cnt: containsThread tp (thread_id ev)) (cnt': containsThread tp' (thread_id ev)),
           match location ev with
           | Some (b, ofs, sz) =>
             forall ofs', Intv.In ofs' (ofs, ofs + Z.of_nat sz)%Z ->
                     (Mem.valid_block m b ->
                      Mem.perm_order'' ((getThreadR cnt).1 !! b ofs') (Some Readable) \/
                      Mem.perm_order'' ((getThreadR cnt).2 !! b ofs') (Some Readable)) /\
                     ((Mem.perm_order'' ((getThreadR cnt').1 !! b ofs') (Some Readable) \/
                       Mem.perm_order'' ((getThreadR cnt').2 !! b ofs') (Some Readable)) \/
                      (tr_pre = [::] /\ tr_post = [::] /\ action ev = Release /\
                       (exists rmap, sz = lksize.LKSIZE_nat /\
                                lockRes tp' (b, ofs) = Some rmap /\
                                (Mem.perm_order'' (rmap.1 !! b ofs') (Some Readable) \/
                                 Mem.perm_order'' (rmap.2 !! b ofs') (Some Readable)))) \/
                      deadLocation tp' m' b ofs')
           | None => False
           end).
    Proof.
      intros.
      inversion Hstep; simpl in *;
        try match goal with
            | [H: ?X = cat ?X ?Y |- _] =>
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
      - (** case of internal steps*)
        apply app_inv_head in H5; subst.
        (** proof that the [thread_id] of the event and the head of the schedule match*)
        assert (Hin: List.In ev (List.map [eta internal tid] ev0))
          by (rewrite H5; apply in_app; right; simpl; auto).
        apply in_map_iff in Hin.
        destruct Hin as [mev [? Hin]].
        subst.
        assert (Hwritable:
                  (waction (internal tid mev) ->
                   forall (cnt : containsThread tp (thread_id (internal tid mev)))
                     (cnt' : containsThread tp' (thread_id (internal tid mev))),
                     match location (internal tid mev) with
                     | Some (b, ofs, sz) =>
                       forall ofs' : Z,
                         Intv.In ofs' (ofs, (ofs + Z.of_nat sz)%Z) ->
                         (Mem.valid_block m b ->
                          Mem.perm_order'' (((getThreadR cnt)#1) # b ofs') (Some Writable) \/
                          Mem.perm_order'' (((getThreadR cnt)#2) # b ofs') (Some Writable)) /\
                         ((Mem.perm_order'' (((getThreadR cnt')#1) # b ofs') (Some Writable) \/
                           Mem.perm_order'' (((getThreadR cnt')#2) # b ofs') (Some Writable)) \/
                          deadLocation tp' (diluteMem m'0) b ofs')
                     | None => False
                     end) ).
        { simpl in *; inversion Htstep; subst.
          intros Haction Hcnt Hcnt';
            destruct mev;
            try (inv Haction; simpl in *; discriminate);
            Tactics.pf_cleanup.
          (** Write case*)
          intros ofs' Hintv.
          pose proof (ev_step_elim _ _ _ _ _ _ Hcorestep) as Helim.
          (*destruct Helim as [Helim _].*)
          (** By case analysis on whether [b] was a valid block or not*)
          destruct (valid_block_dec m b).
          { (** case [b] is a valid block in [m]*)
            eapply elim_perm_valid_block in Helim; eauto.
            destruct Helim as [[Hfreeable Hempty] | [Hwrite Hread]].
            - (** case the block was freed by the internal step. This implies that
            [(b, ofs)] is now a [deadLocation]*)
              split.
              + intros. rewrite restrPermMap_Cur in Hfreeable.
                rewrite Hfreeable. simpl; left; now constructor.
              + right.
                constructor; eauto.
                eapply ev_step_validblock with (b := b) in Hcorestep.
                now eauto.
                now eauto.
                intros i cnti.
                rewrite restrPermMap_Cur in Hfreeable.
                pose proof (cntUpdate' _ _  Htid cnti) as cnti0.
                eapply invariant_freeable_empty_threads with (j := i) (cntj := cnti0)
                  in Hfreeable;
                  eauto.
                destruct Hfreeable.
                destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
                subst. Tactics.pf_cleanup.
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
                apply invariant_freeable_empty_locks with (laddr := l) (rmap := pmap)
                  in Hfreeable;
                  now eauto.
            - (** case the block was not freed*)
              split.
              + intros.
                left.
                rewrite! restrPermMap_Cur in Hwrite.
                eapply Hwrite;
                  now eauto.
              + rewrite gssThreadRes.
                simpl.
                rewrite getCurPerm_correct.
                do 2 left; eapply Hwrite;
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
              simpl; left; now constructor.
            - right.
              econstructor; eauto.
              + intros.
                pose proof (cntUpdate' _ _ Htid cnti) as cnti0.
                destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
                * subst. Tactics.pf_cleanup.
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
        }
        simpl in *.
        inversion Htstep; subst.
        split; intros Haction Hcnt Hcnt';
        destruct mev;
        try (inv Haction; simpl in *; discriminate);
            Tactics.pf_cleanup; eauto.
        + (** Write case*)
          intros ofs' Hintv.
          destruct (Hwritable ltac:(constructor; auto) Htid Hcnt' ofs' Hintv)
            as [Hperm Hperm'].
          split.
          intros Hvalid.
          destruct (Hperm Hvalid); [left | right];
          eapply po_trans; eauto; simpl; eauto using perm_order.
          destruct Hperm' as [Hperm' | Hdead]; eauto.
          left.
          destruct Hperm'; [left | right];
          eapply po_trans; eauto; simpl; eauto using perm_order.
        + (** Read case*)
          intros ofs' Hintv.
          pose proof (ev_step_elim _ _ _ _ _ _ Hcorestep) as Helim.
          (*destruct Helim as [Helim _].*)
          (** By case analysis on whether [b] was a valid block or not*)
          destruct (valid_block_dec m b).
          { (** case [b] is a valid block in [m]*)
            eapply elim_perm_valid_block in Helim; eauto.
            destruct Helim as [[Hfreeable Hempty] | [Hwrite Hread]].
            - (** case the block was freed by the internal step. This implies that
            [(b, ofs)] is now a [deadLocation]*)
              split.
              + intros. rewrite restrPermMap_Cur in Hfreeable.
                rewrite Hfreeable. simpl; left; now constructor.
              + right. right.
                constructor; eauto.
                eapply ev_step_validblock with (b := b) in Hcorestep.
                now eauto.
                now eauto.
                intros i cnti.
                rewrite restrPermMap_Cur in Hfreeable.
                pose proof (cntUpdate' _ _ Htid cnti) as cnti0.
                eapply invariant_freeable_empty_threads with (j := i) (cntj := cnti0) in Hfreeable;
                  eauto.
                destruct Hfreeable.
                destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
                subst. Tactics.pf_cleanup.
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
                left.
                eapply Hread;
                  now eauto.
              + rewrite gssThreadRes.
                simpl.
                rewrite getCurPerm_correct.
                do 2 left; eapply Hread;
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
              simpl; left; now constructor.
            - do 2 right.
              econstructor; eauto.
              + intros.
                pose proof (cntUpdate' _ _ Htid cnti) as cnti0.
                destruct (i == tid) eqn:Heq; move/eqP:Heq=>Heq.
                * subst. Tactics.pf_cleanup.
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
        assert (Hwritable:
                  (waction (external tid ev0) ->
                   forall (cnt : containsThread tp (thread_id (external tid ev0)))
                     (cnt' : containsThread tp' (thread_id (external tid ev0))),
                     match location (external tid ev0) with
                     | Some (b, ofs, sz) =>
                       forall ofs' : Z,
                         Intv.In ofs' (ofs, (ofs + Z.of_nat sz)%Z) ->
                         (Mem.valid_block m b ->
                          Mem.perm_order'' (((getThreadR cnt)#1) # b ofs') (Some Writable) \/
                          Mem.perm_order'' (((getThreadR cnt)#2) # b ofs') (Some Writable)) /\
                         ((Mem.perm_order'' (((getThreadR cnt')#1) # b ofs') (Some Writable) \/
                           Mem.perm_order'' (((getThreadR cnt')#2) # b ofs') (Some Writable)) \/
                          deadLocation tp' m' b ofs')
                     | None => False
                     end)).
        { intros.
          destruct ev0; inv H; simpl in H0; try (discriminate);
          inv Htstep.
          - intros ofs' Hintv.
            Tactics.pf_cleanup.
            split.
            intros Hvalid.
            specialize (Hfreeable _ Hintv).
            unfold Mem.perm in Hfreeable.
            erewrite <- restrPermMap_Cur with (Hlt := (Hcmpt tid Htid)#1) by eauto.
            unfold permission_at. now eauto.
            left. rewrite gLockSetRes gssThreadRes.
            rewrite <- Hlock_perm.
            rewrite setPermBlock_same. right; simpl; auto using perm_order.
            eauto.
          - intros ofs' Hintv.
            Tactics.pf_cleanup.
            split.
            intros Hvalid.
            specialize (Hfreeable _ Hintv).
            unfold Mem.perm in Hfreeable.
            erewrite <- restrPermMap_Cur with (Hlt := (Hcmpt tid Htid)#2) by eauto.
            unfold permission_at.
            now eauto.
            left. rewrite gRemLockSetRes gssThreadRes.
            rewrite <- Hdata_perm.
            erewrite setPermBlock_var_same by eauto.
            left; simpl; auto using perm_order.
            specialize (Hneq_perms (nat_of_Z (ofs' - Ptrofs.intval ofs))).
            destruct Hintv. unfold lksize.LKSIZE_nat, lksize.LKSIZE in *.
            erewrite nat_of_Z_eq in Hneq_perms
              by (simpl in *; now ssromega).
            assert ((0 <= ofs' - Ptrofs.intval ofs < lksize.LKSIZE)%Z)
              by (unfold LKSIZE;
                  unfold Mptr in *;
                  destruct Archi.ptr64; simpl in *;
                  ssromega).
            replace ((nat_of_Z (ofs' - Ptrofs.intval ofs)).+1) with
            (nat_of_Z (ofs' - Ptrofs.intval ofs +1)) in Hneq_perms
              by (zify;
                  erewrite! nat_of_Z_eq
                    by (unfold lksize.LKSIZE in *; simpl in *; ssromega);
                  omega).
            now eauto.
        }
        split; auto.
        intros Haction cnt cnt'.
        destruct ev0; inv Htstep.
        + intros ofs' Hintv.
          Tactics.pf_cleanup.
          split. intros. 
          specialize (Haccess _ Hintv).
          rewrite <- restrPermMap_Cur with (Hlt := (Hcmpt tid Htid).2).
          unfold permission_at, Mem.perm in *; now auto.
          rewrite gLockSetRes gssThreadRes.
          clear Hwritable Hstep.
          specialize (Haccess ofs' Hintv).
          unfold Mem.perm in Haccess.
          pose proof (restrPermMap_Cur (Hcmpt _ Htid).2 b ofs') as Heq.
          unfold permission_at in Heq.
          rewrite Heq in Haccess.
          specialize (Hangel2 b ofs').
          eapply permjoin_readable_iff in Hangel2.
          pose proof (Hangel2.1 Haccess) as Hperm.
          destruct Hperm as [Hperm | Hperm].
          simpl in Hperm.
          left. now auto.
          right. simpl in Hperm.
          left.
          repeat split; auto.
          exists virtueLP. split; auto.
          rewrite gssLockRes. repeat split; auto.
        + intros ofs' Hintv.
          Tactics.pf_cleanup.
          split. intros.
          specialize (Haccess _ Hintv).
          rewrite <- restrPermMap_Cur with (Hlt := (Hcmpt tid Htid).2).
          unfold permission_at, Mem.perm in *; now auto.
          rewrite gLockSetRes gssThreadRes.
          clear Hwritable Hstep.
          specialize (Haccess ofs' Hintv).
          unfold Mem.perm in Haccess.
          pose proof (restrPermMap_Cur (Hcmpt _ Htid).2 b ofs') as Heq.
          unfold permission_at in Heq.
          rewrite Heq in Haccess.
          specialize (Hangel2 b ofs').
          eapply permjoin_readable_iff in Hangel2.
          pose proof (Hangel2.2 (or_intror Haccess)) as Hperm.
          left; now auto.
        + intros ofs' Hintv.
          Tactics.pf_cleanup.
          specialize (Hfreeable _ Hintv).
          pose proof (restrPermMap_Cur (Hcmpt _ Htid).1 b ofs') as Heq.
          unfold permission_at in Heq.
          unfold Mem.perm in Hfreeable.
          rewrite po_oo in Hfreeable.
          rewrite Heq in Hfreeable.
          split.
          intros.
          left.
          eapply po_trans; eauto; simpl; now constructor.
          left.
          rewrite gLockSetRes gssThreadRes.
          rewrite <- Hlock_perm. right.
          rewrite setPermBlock_same; simpl. now constructor.
          eauto.
        + intros ofs' Hintv.
          specialize (Hfreeable _ Hintv).
          pose proof (restrPermMap_Cur (Hcmpt _ Htid).2 b ofs') as Heq.
          unfold permission_at in Heq.
          unfold Mem.perm in Hfreeable.
          rewrite po_oo in Hfreeable.
          rewrite Heq in Hfreeable.
          Tactics.pf_cleanup.
          split.
          intros.
          right.
          eapply po_trans; eauto; simpl; now constructor.
          left.
          rewrite gRemLockSetRes gssThreadRes.
          rewrite <- Hdata_perm.
          left.
          erewrite setPermBlock_var_same by eauto.
          specialize (Hneq_perms (nat_of_Z (ofs' - Ptrofs.intval ofs))).
          destruct Hintv. unfold lksize.LKSIZE_nat, lksize.LKSIZE in *.
          erewrite nat_of_Z_eq in Hneq_perms
            by (simpl in *; now ssromega).
          assert ((0 <= ofs' - Ptrofs.intval ofs < lksize.LKSIZE)%Z)
            by (unfold LKSIZE;
                unfold Mptr in *;
                destruct Archi.ptr64; simpl in *;
                ssromega).
          replace ((nat_of_Z (ofs' - Ptrofs.intval ofs)).+1) with
          (nat_of_Z (ofs' - Ptrofs.intval ofs +1)) in Hneq_perms
            by (zify;
                erewrite! nat_of_Z_eq
                  by (unfold lksize.LKSIZE in *; simpl in *; ssromega);
                omega).
          eapply po_trans; eauto; simpl;
          eauto using perm_order.
        + simpl in Haction.
            by exfalso.
        + intros ofs' Hintv.
          Tactics.pf_cleanup.
          specialize (Haccess _ Hintv).
          rewrite <- restrPermMap_Cur with (Hlt := (Hcmpt tid Htid).2).
          unfold permission_at, Mem.perm in *; now auto.
        + destruct l; simpl in H1;
            now inv H1.
    Qed.

    Lemma waction_caction:
      forall ev,
        waction ev -> caction ev.
    Proof.
      intros; destruct ev as [? ev | ? ev]; destruct ev;
      inversion H; (auto || discriminate).
    Qed.

    Lemma raction_caction:
      forall ev,
        raction ev -> caction ev.
    Proof.
      intros; destruct ev as [? ev | ? ev]; destruct ev;
      inversion H; (auto || discriminate).
    Qed.

    Lemma raction_waction:
      forall ev,
        raction ev -> ~ waction ev.
    Proof.
      intros.
      intro Hcontra.
      inversion H; inv Hcontra; congruence.
    Qed.

    Lemma waction_raction:
      forall ev,
        waction ev -> ~ raction ev.
    Proof.
      intros.
      intro Hcontra.
      inversion H; inv Hcontra; congruence.
    Qed.

    Lemma caction_location:
      forall ev,
        caction ev ->
        exists b ofs sz, location ev = Some (b, ofs, sz).
    Proof.
      intros.
      destruct ev as [? ev | ? ev];
        destruct ev; simpl in *; try (by exfalso);
          try (destruct a);
          do 3 eexists; reflexivity.
    Qed.


    Opaque containsThread.
    (** [FineConc.MachStep] preserves [spinlock_synchronized]*)
    Lemma fineConc_step_synchronized:
      forall U0 U U'  tr tp0 m0 tp m tp' m' tr'
        (Hexec: multi_fstep (U0, [::], tp0) m0 (U, tr, tp) m)
        (Hstep: fstep (U, tr, tp) m (U', tr ++ tr', tp') m')
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
        (** By [maximal_competing] there must exist some maximal event [ek] s.t.
        it competes with [evj]*)
        destruct (maximal_competing _ _ _ Hneq Hi Hj Hcompetes)
          as (k & evk & Horder & Hk & Hcompetes_kj & Hmaximal).
        (** [evk] cannot be in [tr'] because this would imply that it is from
        the same thread as [j] and hence not competing*)
        assert (Hk_not_in_tr': (k < length tr)%coq_nat).
        { destruct (lt_dec k (length tr)); auto.
          erewrite nth_error_app2 in Hk by omega.
          destruct Hcompetes_kj.
          apply nth_error_In in Hk.
          erewrite nth_error_app2 in Hj by omega.
          apply nth_error_In in Hj.
          eapply step_event_tid with (ev := evk) (ev' := evj) in Hstep; eauto.
          exfalso; auto.
        }
        erewrite nth_error_app1 in Hk by assumption.

        (** To find the state that corresponds to [evk] we break the execution
          in [multi_fstep] chunks and the [FineConc.Machstep] that produces [evk]*)
        destruct (multi_step_inv _ _ Hk Hexec)
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
          by (eapply step_ev_contains in Hstepk;
              eapply Hstepk.1).
        assert (cntk': containsThread tp_k' (thread_id evk))
          by (eapply step_ev_contains in Hstepk;
              eapply Hstepk.2).
        assert (cntj: containsThread tp (thread_id evj))
          by (eapply step_ev_contains in Hstep;
              eapply Hstep.1).
        assert (cntj': containsThread tp' (thread_id evj))
          by (eapply step_ev_contains in Hstep;
              eapply Hstep.2).

        inversion Hcompetes_kj as (Hthreads_neq & Hsame_loc & Hcactionk & Hcactionj & _ & _).
        (** [location] is defined for [evk] as it is a competing event*)
        assert (Hloc_k: exists bk ofsk szk, location evk = Some (bk, ofsk, szk))
          by (eapply caction_location; eauto).
        (** [location] is defined for [evj] as it is a competing event*)
        assert (Hloc_j: exists bj ofsj szj, location evj = Some (bj, ofsj, szj))
          by (eapply caction_location; eauto).

        destruct Hloc_k as (b & ofsk & szk & Hloc_k).
        destruct Hloc_j as (b' & ofsj & szj & Hloc_j).
        (** Find the competing byte*)
        unfold sameLocation in Hsame_loc.
        rewrite Hloc_k Hloc_j in Hsame_loc.
        destruct Hsame_loc as [? [ofs [Hintvk Hintvj]]]; subst b'.

        pose proof (multi_step_trace_monotone Hexec') as Heq.
        subst.
        destruct Heq as [tr'' Heq]; subst.


        (** The states of the machine satisfy the [invariant]*)
        assert (Hinv: invariant tp)
          by (eapply step_invariant; eapply Hstep).
        assert (Hinvk': invariant tp_k').
        { destruct (multi_step_invariant Hexec') as [Hinvk' | [? _]].
          - now eapply Hinvk'.
          - subst.
            eapply step_invariant in Hstep.
            now eapply Hstep.
        }

        assert (cntk'_j: containsThread tp (thread_id evk))
          by (eapply step_ev_contains in Hstepk;
              destruct Hstepk;
              eapply multi_step_containsThread; eauto).

        (** [b] is valid if someone has permission on it*)
        assert (Hvalid_mk': forall p, Mem.perm_order'' ((getThreadR cntk').1 !! b ofs) (Some p) \/
                                 Mem.perm_order'' ((getThreadR cntk').2 !! b ofs) (Some p) ->
                                 Mem.valid_block m_k' b).
        { intros.
          assert (Hlt: permMapLt ((getThreadR cntk').1) (getMaxPerm m_k') /\
                  permMapLt ((getThreadR cntk').2) (getMaxPerm m_k')).
          { destruct (multi_step_mem_compatible Hexec') as [Hcompk' | Heq].
            - destruct Hcompk'.
              now eapply (compat_th0 _ cntk').
            - destruct Heq as [? [? _]]; subst.
              eapply step_mem_compatible in Hstep.
              now eapply Hstep.
          }
          destruct Hlt.
          destruct H;
            eapply perm_order_valid_block;
            now eauto.
        }

        assert (Hvalid_m: forall p, Mem.perm_order'' ((getThreadR cntk').1 !! b ofs) (Some p) \/
                               Mem.perm_order'' ((getThreadR cntk').2 !! b ofs) (Some p) ->
                               Mem.valid_block m b).
        { intros.
          eapply multi_step_valid_block; eauto.
        }

        assert (Hvalid_mk'2: pre_k = [::] /\
                             post_k = [::] /\
                             action evk = Release /\
                             (exists rmap,
                                 szk = lksize.LKSIZE_nat /\
                                 lockRes tp_k' (b, ofsk) = Some rmap /\
                                 (Mem.perm_order'' ((rmap#1) # b ofs) (Some Readable) \/
                                  Mem.perm_order'' ((rmap#2) # b ofs) (Some Readable))) ->
                             Mem.valid_block m_k' b).
        { intros.
          destruct H as [? [? [? [rmap [? [Hres Hperm]]]]]].
          destruct (multi_step_mem_compatible Hexec') as [Hcompk' | Heq].
          - destruct Hcompk'.
            now eapply (lockRes_blocks0 _ _ Hres).
          - destruct Heq as [? [? _]]; subst.
            eapply step_mem_compatible in Hstep.
            now eapply (lockRes_blocks _ _ Hstep _  _ Hres).
        }

        assert (Hvalid_m2: pre_k = [::] /\
                             post_k = [::] /\
                             action evk = Release /\
                             (exists rmap,
                                 szk = lksize.LKSIZE_nat /\
                                 lockRes tp_k' (b, ofsk) = Some rmap /\
                                 (Mem.perm_order'' ((rmap#1) # b ofs) (Some Readable) \/
                                  Mem.perm_order'' ((rmap#2) # b ofs) (Some Readable))) ->
                               Mem.valid_block m b).
        { intros.
          eapply multi_step_valid_block; eauto.
        }

        (** *** The Proof*)

        (** We proceed by a case analysis on whether [thread_id evj] was in
            the threadpool at index k. If not then there must have been a
            spawn event between u and j and we are done *)
        destruct (containsThread_dec_ (thread_id evj) tp_k')
          as [cntj_k' | Hnot_contained].
        { (** Case [thread_id evj] is in the threadpool*)
          (** by [compete_cases] there are two main cases:
- evk is of type [Read], [Acquire], [AcquireFail], [Release] and [evj] is of type [Write], [Mklock], [Freelock] or
- evk is of type [Write], [Mklock], [Freelock] and [evj] is of any type that competes*)
          pose proof (compete_cases Hcompetes_kj) as Hcases.

          (** *** Proving that the permissions required for [evk] and [evj]
              are above [Readable] and incompatible*)

          assert (Hpermissions: ((Mem.perm_order'' ((getThreadR cntk').1 !! b ofs) (Some Readable) \/
                                  Mem.perm_order'' ((getThreadR cntk').2 !! b ofs) (Some Readable)) \/
                                 (pre_k = [::] /\
                                  post_k = [::] /\
                                  action evk = Release /\
                                  (exists rmap,
                                      szk = lksize.LKSIZE_nat /\
                                      lockRes tp_k' (b, ofsk) = Some rmap /\
                                      (Mem.perm_order'' ((rmap#1) # b ofs) (Some Readable) \/
                                      Mem.perm_order'' ((rmap#2) # b ofs) (Some Readable))))) /\
                                (Mem.perm_order'' ((getThreadR cntj).1 !! b ofs) (Some Readable) \/
                                 Mem.perm_order'' ((getThreadR cntj).2 !! b ofs) (Some Readable)) /\
                                (waction evk ->
                                 Mem.perm_order'' ((getThreadR cntk').1 !! b ofs) (Some Writable) \/
                                 Mem.perm_order'' ((getThreadR cntk').2 !! b ofs) (Some Writable)) /\
                                (waction evj ->
                                 Mem.perm_order'' ((getThreadR cntj).1 !! b ofs) (Some Writable) \/
                                 Mem.perm_order'' ((getThreadR cntj).2 !! b ofs) (Some Writable))).
          { destruct(fstep_ev_perm _ _ _ Hstepk) as [Hwritek Hreadk].
            destruct(fstep_ev_perm _ _ _ Hstep) as [Hwritej Hreadj].
            rewrite Hloc_j in Hwritej Hreadj.
            rewrite Hloc_k in Hwritek, Hreadk.
            (** First we prove that [(b, ofs)] cannot be a [deadLocation] *)
            assert (Hnotdead: ~ deadLocation tp_k' m_k' b ofs).
            { (** Suppose that it was. [deadLocation] is preserved by
                      [multi_fstep] and hence [evj] would not have sufficient permissions
                      to perform a [caction]*)
              intros Hdead.
              (** [(b,ofs)] is [deadLocation] at [tp], [m]*)
              eapply @multi_step_deadLocation with (tp' := tp) (m' := m) in Hdead; eauto.
              (** Hence [b] is a valid block in [m]*)
              inversion Hdead.
              (** Moreover permissions of the machine on [(b, ofs)] are None*)
              destruct (Hthreads _ cntj) as [Hperm1 Hperm2].
              (** The permissions of the thread [thread_id evj] must be above
                      [Readable] by the fact that [evj] is a [caction] event,
                      which leads to a contradiction*)
              pose proof ((Hreadj Hcactionj cntj cntj' ofs Hintvj).1 Hvalid) as Hperm.
              rewrite Hperm1 Hperm2 in Hperm.
              simpl in Hperm.
              destruct Hperm;
                now auto.
            }
            destruct Hcases as [[Hractionk Hwactionj] | [Hwactionk Hwractionj]];
              [ destruct (Hreadk (raction_caction Hractionk) cntk cntk' ofs Hintvk)
                as [_ [Hpermk | [Hrelease | Hcontra]]]
              | destruct (Hwritek Hwactionk cntk cntk' ofs Hintvk) as [_ [Hpermk | Hcontra]]];
              try (by exfalso); split;
                try (eapply po_trans; eauto;
                     now constructor);
                try (specialize (Hvalid_m _ Hpermk));
                try (specialize (Hvalid_m2 Hrelease));
                repeat match goal with
                       | [H: waction evj |- _] =>
                         destruct (Hwritej H cntj cntj' ofs Hintvj) as [Hpermj _];
                           try (specialize (Hpermj Hvalid_m));
                           try (specialize (Hpermj Hvalid_m2));
                           clear Hwritej
                       | [H: is_true (isSome (caction evj)) |- _] =>
                         destruct (Hreadj H cntj cntj' ofs Hintvj) as [Hpermj _];
                           try (specialize (Hpermj Hvalid_m));
                           try (specialize (Hpermj Hvalid_m2));
                           clear Hreadj
                       | [H: waction evk |- _] =>
                         destruct (Hwritek H cntk cntk' ofs Hintvk) as [_ [Hpermk | Hcontra]];
                           clear Hwritek
                       | [H: is_true (isSome (caction evk)) |- _] =>
                         destruct (Hreadk H cntk cntk' ofs Hintvk) as [_ [Hpermk| [Hrelease | Hcontra]]];
                           clear Hreadk
                       | [ |- _ /\ _] =>
                         split
                       | [H: Mem.perm_order'' ?X ?Y |- Mem.perm_order'' ?X ?Y] =>
                         assumption
                       | [ |- Mem.perm_order'' _ _] =>
                         eapply po_trans; eauto; simpl; now constructor
                       | [H: Mem.perm_order'' _ _ \/ Mem.perm_order'' _ _ |- _] =>
                         destruct H
                       | [H: Mem.perm_order'' ?X ?Y  |- Mem.perm_order'' ?X ?Y \/ _] =>
                         left
                       | [H: Mem.perm_order'' ?X ?Y  |- _ \/ Mem.perm_order'' ?X ?Y] =>
                           right
                       | [ |- _ -> _] => intros
                       | [H: waction ?X, H2: raction ?X |- Mem.perm_order'' _ _] =>
                         exfalso; eapply waction_raction
                       | [H: deadLocation _ _ _ _, H2: ~ deadLocation _ _ _ _ |- _ ] =>
                         exfalso; eauto
                       end;
                eauto.
          }
          destruct Hpermissions as (Hperm_k & Hperm_j & Hwritablek & Hwritablej).

          (** By the [invariant] permissions of [thread_id evk] and
          [thread_id evj] will have compatible permissions at [tp] *)
          assert (Hcompatible11_j: perm_union ((getThreadR cntk'_j).1 !! b ofs)
                                              ((getThreadR cntj).1 !! b ofs))
            by (destruct ((no_race_thr _ Hinv _ _ cntk'_j cntj Hthreads_neq).1 b ofs) as [pu Hcompatiblek'j];
                 rewrite Hcompatiblek'j; auto).

          assert (Hcompatible12_j: perm_coh ((getThreadR cntk'_j).1 !! b ofs)
                                            ((getThreadR cntj).2 !! b ofs))
            by (pose proof ((thread_data_lock_coh _ Hinv _ cntj).1 _ cntk'_j b ofs);
                 auto).

          assert (Hcompatible21_j: perm_coh ((getThreadR cntj).1 !! b ofs)
                                              ((getThreadR cntk'_j).2 !! b ofs))
            by (pose proof ((thread_data_lock_coh _ Hinv _ cntk'_j).1 _ cntj b ofs);
                 auto).

          assert (Hcompatible22_j: perm_union ((getThreadR cntk'_j).2 !! b ofs)
                                              ((getThreadR cntj).2 !! b ofs))
            by (destruct ((no_race_thr _ Hinv _ _ cntk'_j cntj Hthreads_neq).2 b ofs) as [pu Hcompatiblek'j];
                 rewrite Hcompatiblek'j; auto).

          (** There are two main cases: 1. evk is a [raction], 2. evk is a [waction]*)
          destruct Hcases as [[Hractionk Hwactionj] | [Hwactionk _]].
          { (** Case [evk] is an [raction] and [evj] is an [waction]*)
            specialize (Hwritablej Hwactionj).
            assert (Hpermk'_j: ~ Mem.perm_order'' ((getThreadR cntk'_j).1 !! b ofs) (Some Readable)
                               /\ ~ Mem.perm_order'' ((getThreadR cntk'_j).2 !! b ofs) (Some Readable)).
            { clear - Hcompatible11_j Hcompatible12_j Hcompatible21_j
                                      Hcompatible22_j Hwritablej Hthreads_neq.
              destruct Hwritablej as [Hwritablej | Hwritablej];
                [destruct ((getThreadR cntj).1 !! b ofs) as [p1 | ] |
                  destruct ((getThreadR cntj).2 !! b ofs) as [p1 | ]]; simpl in Hwritablej;
              inv Hwritablej;
              destruct ((getThreadR cntk'_j).1 !! b ofs);
              destruct ((getThreadR cntk'_j).2 !! b ofs);
              simpl; split; intros Hcontra;
              inv Hcontra; simpl in *;
              now auto.
            }
            destruct Hperm_k as [Hperm_k | Hrelease_k]. (*TODO: second case*)
            { (** Case permissions were not dropped by the step at k*)
              assert (Hperm_k_drop:
                      (Mem.perm_order'' (((getThreadR cntk')#1) # b ofs)
                                        (Some Readable) /\
                       ~ Mem.perm_order'' (((getThreadR cntk'_j)#1) # b ofs)
                         (Some Readable)) \/
                      (Mem.perm_order'' (((getThreadR cntk')#2) # b ofs)
                                        (Some Readable) /\
                       ~ Mem.perm_order'' (((getThreadR cntk'_j)#2) # b ofs)
                         (Some Readable)))
              by (destruct Hperm_k; [left | right]; split; destruct Hpermk'_j;
                  now auto).
            (** Hence by [permission_decrease_execution] we have four cases
            for how the permissions of [thread_id evk] dropped*)
            destruct (permission_decrease_execution _ b ofs cntk' cntk'_j Hexec' Hperm_k_drop)
              as (tr_pre_u & tru & ? & ? & tp_pre_u & m_pre_u &
                  tp_dec & m_dec & Hexec_pre_u & Hstepu & Hexec_post_u & evu & Hspec_u).
            destruct Hspec_u as [Hfreed | [Hspawned | [Hfreelock | [Hmklock | Hrelease]]]].
              { (** Case permissions dropped by a [Free] event. This leads to a
                  contradiction because it would be a [deadLocation] *)
                destruct Hfreed as (HIn & HFree & Hdead).
                inversion Hdead.
                specialize (Hthreads _ cntj).
                rewrite Hthreads.1 Hthreads.2 in Hperm_j.
                simpl in Hperm_j;
                  destruct Hperm_j;
                    by exfalso.
            }
            { (** Case permissions were dropped by a spawn event - we are done*)
              destruct Hspawned as (? & Hactionu).
              subst.
              right.
              remember (tr0 ++ pre_k ++ [:: evk] ++ post_k) as tr00.
              apply multi_step_trace_monotone in Hexec_post_u.
              destruct Hexec_post_u as [? Heq].
              replace (((tr0 ++ pre_k ++ [:: evk] ++ post_k) ++ tr_pre_u ++ [:: evu]) ++ x1)%list with
                  (((tr0 ++ pre_k ++ [:: evk] ++ post_k) ++ (tr_pre_u ++ [:: evu]) ++ x1)) in Heq
                by (repeat rewrite <- app_assoc; reflexivity).
              apply app_inv_head in Heq. subst.
              exists (length ((((tr0 ++ pre_k) ++ [:: evk]) ++ post_k) ++ tr_pre_u)%list), evu.
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
             { (** Case permissions were dropped by a [Freelock] event - this leads to
                  a contradiction by the fact that [evu] will compete with [evj], while
                  [evk] is the maximal competing event *)
              destruct Hfreelock as [Htru [Hactionu [Hthreadu Hlocu]]].
              subst.
              exfalso.
              remember (tr0 ++ pre_k ++ [:: evk] ++ post_k) as tr00.
              apply multi_step_trace_monotone in Hexec_post_u.
              destruct Hexec_post_u as [? Heq].
              replace (((tr0 ++ pre_k ++ [:: evk] ++ post_k) ++ tr_pre_u ++ [:: evu]) ++ x1)%list with
                  (((tr0 ++ pre_k ++ [:: evk] ++ post_k) ++ (tr_pre_u ++ [:: evu]) ++ x1)) in Heq
                by (repeat rewrite <- app_assoc; reflexivity).
              apply app_inv_head in Heq. subst.
              eapply (Hmaximal (length (tr0 ++ pre_k ++ [:: evk] ++ post_k ++ tr_pre_u)%list) evu).
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
                  right; left.
                  assumption.
            }
            { (** Case permissions were dropped by a [Mklock] event - this leads to
                  a contradiction by the fact that [evu] will compete with [evj], while
                  [evk] is the maximal competing event *)
              destruct Hmklock as [Htru [Hactionu [Hthreadu Hlocu]]].
              subst.
              exfalso.
              remember (tr0 ++ pre_k ++ [:: evk] ++ post_k) as tr00.
              apply multi_step_trace_monotone in Hexec_post_u.
              destruct Hexec_post_u as [? Heq].
              replace (((tr0 ++ pre_k ++ [:: evk] ++ post_k) ++ tr_pre_u ++ [:: evu]) ++ x1)%list with
                  (((tr0 ++ pre_k ++ [:: evk] ++ post_k) ++ (tr_pre_u ++ [:: evu]) ++ x1)) in Heq
                by (repeat rewrite <- app_assoc; reflexivity).
              apply app_inv_head in Heq. subst.
              eapply (Hmaximal (length (tr0 ++ pre_k ++ [:: evk] ++ post_k ++ tr_pre_u)%list) evu).
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
            { (** Case permissions were dropped by a [Release] event.*)
              destruct Hrelease as [? [Hrelease [Hthread_eq Hrmap]]];
                subst.
              destruct Hrmap as [rmap Hspec].
              destruct (location evu) as [[[bu ofsu] szu]|] eqn:Hlocu;
                try (by exfalso).
              destruct Hspec as [? [Hresu Hperm_rmap]].
              subst.
              (** There are two cases: either [(bu,ofsu)] is a lock at [tp] or it is not*)
              destruct (lockRes tp (bu,ofsu)) as [rmap'|] eqn:Hres.
              - (** Case [(bu, ofsu)] is still a lock at [tp]*)
                (** By the [invariant] its permissions must have dropped because
                [thread_id evj] has a Writable permission at that location*)
                assert (Hperm_res: ~ Mem.perm_order'' (rmap'.1 !! b ofs) (Some Readable) /\
                                   ~ Mem.perm_order'' (rmap'.2 !! b ofs) (Some Readable)).
                { clear - Hinv Hres Hwritablej.
                  destruct ((no_race _ Hinv _ _ cntj _ Hres).1 b ofs) as [pu Hcomp].
                  destruct ((no_race _ Hinv _ _ cntj _ Hres).2 b ofs) as [pu2 Hcomp2].
                  pose proof ((thread_data_lock_coh _ Hinv _ cntj).2 _ _ Hres b ofs) as Hcoh.
                  pose proof ((locks_data_lock_coh _ Hinv _ _ Hres).1 _ cntj b ofs) as Hcoh2.
                  split; intros Hcontra; destruct Hwritablej;
                  repeat match goal with
                         | [H: Mem.perm_order'' ?X _ |- _] =>
                           destruct X; simpl in H; inv H; simpl in *
                         | [H: match ?X with _ => _ end = _ |- _] =>
                           destruct X
                         end; simpl in *;
                  try (discriminate || by exfalso).
                }
                pose proof (multi_step_trace_monotone Hexec_post_u) as [tr''0 Heq].
                rewrite! app_assoc_reverse in Heq.
                do 4 apply app_inv_head in Heq; subst.
                rewrite! app_assoc in Hexec_post_u.

                assert (Hperm_res_drop:
                          (Mem.perm_order'' ((rmap#1) # b ofs) (Some Readable) /\
                           ~ Mem.perm_order'' ((rmap'#1) # b ofs) (Some Readable)) \/
                          (Mem.perm_order'' ((rmap#2) # b ofs) (Some Readable) /\
                           ~ Mem.perm_order'' ((rmap'.2) # b ofs) (Some Readable)))
                  by (destruct Hperm_res; destruct Hperm_rmap; [left | right];
                      now auto).
                (** Hence by [lockRes_permission_decrease_execution] there must
                have been some [Acquire] event on that lock*)
                destruct (lockRes_permission_decrease_execution _ _ _ _ Hresu Hres
                                                                Hexec_post_u Hperm_res_drop)
                  as (v & evv & Hev & Hactionv & Hlocv).
                left.
                exists (length ((tr0 ++ pre_k ++ [:: evk] ++ post_k) ++ tr_pre_u)%list),
                (length ((tr0 ++ pre_k ++ [:: evk] ++ post_k) ++ tr_pre_u ++ [:: evu])%list + v),
                evu, evv.
                repeat split; auto.
                + clear - Horder.
                  erewrite! app_assoc.
                  erewrite! app_length in *.
                  now ssromega.
                + clear - Hj_not_in_tr Hev.
                  erewrite! app_assoc in *.
                  erewrite! app_length in *.
                  erewrite <- Nat.le_ngt in Hj_not_in_tr.
                  pose proof ((nth_error_Some tr''0 v).1 ltac:(intros Hcontra; congruence)).
                  simpl in *.
                  now ssromega.
                + rewrite! app_assoc.
                  do 2 rewrite <- app_assoc.
                  rewrite <- addn0.
                  rewrite <- nth_error_app.
                  reflexivity.
                + rewrite! app_assoc.
                  rewrite <- app_assoc.
                  rewrite <- nth_error_app.
                  apply nth_error_app_inv;
                    now eauto.
                + rewrite Hlocv Hlocu.
                  reflexivity.
              - (** Case [(bu, ofsu)] is no longer a lock*)
                pose proof (multi_step_trace_monotone Hexec_post_u) as [tr_fl Heq].
                rewrite! app_assoc_reverse in Heq.
                do 4 apply app_inv_head in Heq; subst.
                rewrite! app_assoc in Hexec_post_u.
                destruct (lockRes_freelock_execution _ _ Hresu Hres Hexec_post_u)
                  as (tr_pre_fl & evfl & ? & ? & tp_pre_fl &
                      m_pre_fl & tp_fl & m_fl & Hexec_pre_fl & Hstep_fl &
                      Hexec_post_fl & Haction_fl & Hloc_fl & rmap_fl & Hres_fl & Hres_fl_empty).
                (** Hence, at some point in the trace, the permissions at [(bu,
                ofsu)] dropped. This can only be done by an [Acquire] step*)
                assert (Hperm_rmap_empty: ~ Mem.perm_order'' ((empty_map, empty_map).1 !! b ofs)
                                           (Some Readable) /\
                                         ~ Mem.perm_order'' ((empty_map, empty_map).2 !! b ofs)
                                           (Some Readable))
                  by (rewrite empty_map_spec; now auto).

                assert (Hperm_rmap_drop:
                          (Mem.perm_order'' ((rmap#1) # b ofs) (Some Readable) /\
                           ~ Mem.perm_order'' (rmap_fl.1 # b ofs) (Some Readable)) \/
                          (Mem.perm_order'' ((rmap#2) # b ofs) (Some Readable) /\
                           ~ Mem.perm_order'' (rmap_fl.2 # b ofs) (Some Readable)))
                  by (destruct Hperm_rmap_empty; destruct Hperm_rmap;
                      erewrite (Hres_fl_empty b ofs).1;
                      erewrite (Hres_fl_empty b ofs).2;
                      [left | right];
                      now auto).


                destruct (lockRes_permission_decrease_execution _ _ _ _ Hresu Hres_fl
                                                                Hexec_pre_fl Hperm_rmap_drop)
                  as (v & evv & Hv & Haction_v & Hloc_v).
                left.
                pose proof (multi_step_trace_monotone Hexec_post_fl) as [tr_fl' Heq].
                rewrite! app_assoc_reverse in Heq.
                do 6 apply app_inv_head in Heq; subst.
                exists (length ((tr0 ++ pre_k ++ [:: evk] ++ post_k) ++ tr_pre_u)%list),
                (length (((((tr0 ++ pre_k) ++ [:: evk]) ++ post_k) ++ tr_pre_u) ++ [:: evu])%list + v),
                evu, evv.
                repeat split; auto.
                * clear - Horder.
                  erewrite! app_assoc.
                  erewrite! app_length in *.
                  now ssromega.
                * clear - Hj_not_in_tr Hv.
                  erewrite! app_assoc in *.
                  erewrite! app_length in *.
                  erewrite <- Nat.le_ngt in Hj_not_in_tr.
                  pose proof ((nth_error_Some tr_pre_fl v).1 ltac:(intros Hcontra; congruence)).
                  simpl in *.
                  now ssromega.
                * rewrite! app_assoc.
                  do 4 rewrite <- app_assoc.
                  rewrite <- addn0.
                  rewrite <- nth_error_app.
                  reflexivity.
                * rewrite! app_assoc.
                  do 3 rewrite <- app_assoc.
                  rewrite <- nth_error_app.
                  apply nth_error_app_inv;
                    now eauto.
                * rewrite Hloc_v Hlocu.
                  reflexivity.
            }
            }
            { (** Case [evk] was a [Release] and it released the lock location itself*)
              destruct Hrelease_k as [? [? [Hrelease [rmap [? [Hresk' Hperm_rmap]]]]]];
                subst.
              (** There are two cases: either [(b,ofs)] is a lock at [tp] or it is not*)
              destruct (lockRes tp (b,ofsk)) as [rmap'|] eqn:Hres.
              - (** Case [(b, ofs)] is still a lock at [tp]*)
                (** By the [invariant] its permissions must have dropped because
                [thread_id evj] has a Writable permission at that location*)
                assert (Hperm_res: ~ Mem.perm_order'' (rmap'.1 !! b ofs) (Some Readable) /\
                                   ~ Mem.perm_order'' (rmap'.2 !! b ofs) (Some Readable)).
                { clear - Hinv Hres Hwritablej.
                  destruct ((no_race _ Hinv _ _ cntj _ Hres).1 b ofs) as [pu Hcomp].
                  destruct ((no_race _ Hinv _ _ cntj _ Hres).2 b ofs) as [pu2 Hcomp2].
                  pose proof ((thread_data_lock_coh _ Hinv _ cntj).2 _ _ Hres b ofs) as Hcoh.
                  pose proof ((locks_data_lock_coh _ Hinv _ _ Hres).1 _ cntj b ofs) as Hcoh2.
                  split; intros Hcontra; destruct Hwritablej;
                  repeat match goal with
                         | [H: Mem.perm_order'' ?X _ |- _] =>
                           destruct X; simpl in H; inv H; simpl in *
                         | [H: match ?X with _ => _ end = _ |- _] =>
                           destruct X
                         end; simpl in *;
                  try (discriminate || by exfalso).
                }

                assert (Hperm_res_drop:
                          (Mem.perm_order'' ((rmap#1) # b ofs) (Some Readable) /\
                           ~ Mem.perm_order'' ((rmap'#1) # b ofs) (Some Readable)) \/
                          (Mem.perm_order'' ((rmap#2) # b ofs) (Some Readable) /\
                           ~ Mem.perm_order'' ((rmap'.2) # b ofs) (Some Readable)))
                  by (destruct Hperm_res; destruct Hperm_rmap; [left | right];
                      now auto).
                (** Hence by [lockRes_permission_decrease_execution] there must
                have been some [Acquire] event on that lock*)
                simpl in Hexec'.
                destruct (lockRes_permission_decrease_execution _ _ _ _ Hresk' Hres
                                                                Hexec' Hperm_res_drop)
                  as (v & evv & Hev & Hactionv & Hlocv).
                left.
                simpl.
                exists (length tr0),
                (length ((tr0 ++ [:: evk]))%list + v),
                evk, evv.
                repeat split; auto.
                + clear - Horder Hev Hj_not_in_tr.
                  erewrite! app_assoc in *.
                  erewrite! app_length in *.
                  erewrite <- Nat.le_ngt in Hj_not_in_tr.
                  pose proof ((nth_error_Some tr'' v).1 ltac:(intros Hcontra; congruence)).
                  simpl in *. now ssromega.
                + clear - Hj_not_in_tr Hev.
                  erewrite! app_assoc in *.
                  erewrite! app_length in *.
                  erewrite <- Nat.le_ngt in Hj_not_in_tr.
                  pose proof ((nth_error_Some tr'' v).1 ltac:(intros Hcontra; congruence)).
                  simpl in *.
                  now ssromega.
                + do 2 rewrite <- app_assoc.
                  rewrite <- addn0.
                  rewrite <- nth_error_app.
                  reflexivity.
                + rewrite <- app_assoc.
                  rewrite <- nth_error_app.
                  apply nth_error_app_inv;
                    now eauto.
                + rewrite Hloc_k Hlocv.
                  reflexivity.
              - (** Case [(b, ofsk)] is no longer a lock*)
                destruct (lockRes_freelock_execution _ _ Hresk' Hres Hexec')
                  as (tr_pre_fl & evfl & ? & ? & tp_pre_fl &
                      m_pre_fl & tp_fl & m_fl & Hexec_pre_fl & Hstep_fl &
                      Hexec_post_fl & Haction_fl & Hloc_fl & rmap_fl & Hres_fl & Hres_fl_empty).
                (** Hence, at some point in the trace, the permissions at [(b,
                ofsk)] dropped. This can only be done by an [Acquire] step*)
                assert (Hperm_rmap_empty: ~ Mem.perm_order'' ((empty_map, empty_map).1 !! b ofs)
                                           (Some Readable) /\
                                         ~ Mem.perm_order'' ((empty_map, empty_map).2 !! b ofs)
                                           (Some Readable))
                  by (rewrite empty_map_spec; now auto).

                assert (Hperm_rmap_drop:
                          (Mem.perm_order'' ((rmap#1) # b ofs) (Some Readable) /\
                           ~ Mem.perm_order'' (rmap_fl.1 # b ofs) (Some Readable)) \/
                          (Mem.perm_order'' ((rmap#2) # b ofs) (Some Readable) /\
                           ~ Mem.perm_order'' (rmap_fl.2 # b ofs) (Some Readable)))
                  by (destruct Hperm_rmap_empty; destruct Hperm_rmap;
                      erewrite (Hres_fl_empty b ofs).1;
                      erewrite (Hres_fl_empty b ofs).2;
                      [left | right];
                      now auto).


                destruct (lockRes_permission_decrease_execution _ _ _ _ Hresk' Hres_fl
                                                                Hexec_pre_fl Hperm_rmap_drop)
                  as (v & evv & Hv & Haction_v & Hloc_v).
                left.
                pose proof (multi_step_trace_monotone Hexec_post_fl) as [tr_fl' Heq].
                rewrite! app_assoc_reverse in Heq.
                simpl in Heq.
                apply app_inv_head in Heq; subst.
                inv Heq.
                simpl.
                exists (length tr0),
                (length ((tr0 ++ [::evk])%list) + v),
                evk, evv.
                repeat split; auto.
                * clear - Horder Hj_not_in_tr Hv.
                  rewrite cats0 in Horder.
                  erewrite! app_assoc in *.
                  erewrite! app_length in *.
                  erewrite <- Nat.le_ngt in Hj_not_in_tr.
                  pose proof ((nth_error_Some tr_pre_fl v).1 ltac:(intros Hcontra; congruence)).
                  simpl in *.
                  now ssromega.
                * clear - Hj_not_in_tr Hv.
                  erewrite! app_assoc in *.
                  erewrite! app_length in *.
                  erewrite <- Nat.le_ngt in Hj_not_in_tr.
                  pose proof ((nth_error_Some tr_pre_fl v).1 ltac:(intros Hcontra; congruence)).
                  simpl in *.
                  now ssromega.
                * rewrite! app_assoc_reverse.
                  rewrite <- addn0.
                  rewrite <- app_assoc.
                  rewrite <- nth_error_app.
                  reflexivity.
                * rewrite! app_assoc.
                  do 2 rewrite <- app_assoc.
                  rewrite <- nth_error_app.
                  apply nth_error_app_inv;
                    now eauto.
                * rewrite Hloc_v Hloc_k.
                  reflexivity.
            }
             }
          { (** Case [evk] is a [waction] *)
            specialize (Hwritablek Hwactionk).
            (** [thread_id evj] must have permissions that are below [Readable]*)
            assert (Hpermj_k': ~ Mem.perm_order'' ((getThreadR cntj_k').1 !! b ofs) (Some Readable) /\
                               ~ Mem.perm_order'' ((getThreadR cntj_k').2 !! b ofs) (Some Readable)).
              { clear - Hperm_k Hinvk' Hwritablek Hthreads_neq.
                pose proof ((no_race_thr _ Hinvk' _ _ cntk' cntj_k' Hthreads_neq).1 b ofs) as Hcomp.
                assert (Hcompatible12_j: perm_coh ((getThreadR cntk').1 !! b ofs)
                                                  ((getThreadR cntj_k').2 !! b ofs))
                  by (pose proof ((thread_data_lock_coh _ Hinvk' _ cntj_k').1 _ cntk' b ofs);
                       auto).

                assert (Hcompatible21_j: perm_coh ((getThreadR cntj_k').1 !! b ofs)
                                                  ((getThreadR cntk').2 !! b ofs))
                  by (pose proof ((thread_data_lock_coh _ Hinvk' _ cntk').1 _ cntj_k' b ofs);
                       auto).

                pose proof ((no_race_thr _ Hinvk' _ _ cntk' cntj_k' Hthreads_neq).2 b ofs) as Hcomp2.
                destruct Hwritablek as [Hwritablek | Hwritablek];
                  [destruct ((getThreadR cntk').1 !! b ofs) as [p1 | ] |
                   destruct ((getThreadR cntk').2 !! b ofs) as [p1 | ]]; simpl in Hwritablek;
                  inv Hwritablek;
                  destruct ((getThreadR cntj_k').1 !! b ofs);
                  destruct ((getThreadR cntj_k').2 !! b ofs);
                  simpl; split; intros Hcontra;
                  inv Hcontra; simpl in *;
                  try (destruct Hcomp);
                  try (destruct Hcomp2);
                  try (auto || discriminate).
              }

              assert (Hperm_incr:
                        (Mem.perm_order'' (((getThreadR cntj)#1) # b ofs) (Some Readable) /\
                         ~ Mem.perm_order'' (((getThreadR cntj_k')#1) # b ofs) (Some Readable)) \/
                        (Mem.perm_order'' (((getThreadR cntj)#2) # b ofs) (Some Readable) /\
                         ~ Mem.perm_order'' (((getThreadR cntj_k')#2) # b ofs) (Some Readable)))
              by (destruct Hpermj_k'; destruct Hperm_j; now auto).
              (** By [permission_increase_execution] we have four cases as
              to how the permissions increased*)
              destruct (@permission_increase_execution _ initU _ _ _ _ _ _ _ _ _ _ ofs _ cntj_k' cntj Hexec' Hperm_incr)
                as (tr_pre_v & evv & ? & ? & tp_pre_v & m_pre_v &
                    tp_inc & m_inc & Hexec_pre_v & Hstepv & Hexec_post_v & Hspec_v); eauto.
              (** Proof of equality of traces*)
              pose proof (multi_step_trace_monotone Hexec_post_v) as Heq_trace.
              destruct Heq_trace as [tr''0 Heq_trace].
              erewrite! app_assoc_reverse in Heq_trace.
              do 4 apply app_inv_head in Heq_trace. subst.
              rewrite! app_assoc.
              destruct Hspec_v as [Hactionv | [[Hactionv [Hthreadv Hloc_v]] |
                                               [[Hactionv [Hthreadv Hloc_v]] |
                                                [Hactionv [Hthreadv Hrmap]]]]].
              - (** Case permissions were increased by a [Spawn] event*)
                right.
                exists (length (((((tr0 ++ pre_k) ++ [:: evk]) ++ post_k) ++ tr_pre_v)%list)), evv.
                repeat split.
                + clear - Hj_not_in_tr Horder.
                  erewrite! app_assoc in *.
                  erewrite! app_length in *.
                  simpl.
                  apply/andP.
                  split.
                  now ssromega.
                  erewrite <- Nat.le_ngt in Hj_not_in_tr.
                  simpl in *.
                  now ssromega.
                + rewrite <- addn0.
                  do 2 rewrite <- app_assoc.
                  rewrite <- nth_error_app.
                  now reflexivity.
                + assumption.
              - (** Case permissions were increased by a [Freelock] event*)
                (** In this case, [evv] competes with [evk] and by the premise
                that [tr] is [spinlock_synchronized] there will be a [Spawn] or
                [Release]-[Acquire] pair between them and hence between [evk]
                and [evj] as well *)
                assert (Hcompeteskj: competes evk evv).
                { repeat split; eauto.
                  - rewrite Hthreadv.
                    now auto.
                  - unfold sameLocation.
                    destruct (location evv) as [[[bv ofsv] szv]|]; try (by exfalso).
                    destruct Hloc_v as [Heqb Hintvv].
                    simpl in Heqb. subst.
                    rewrite Hloc_k.
                    split; auto.
                    exists ofs.
                    split; now auto.
                  - destruct evv as [? evv | ? evv];
                      destruct evv; simpl in Hactionv; simpl;
                        try (by exfalso);
                        now auto.
                  - intros.
                    exfalso.
                    destruct evv as [? evv | ? evv];
                      simpl in Hactionv;
                      destruct evv; try (discriminate);
                        try (by exfalso).
                }
                rewrite! app_assoc in Hsynchronized.
                specialize (Hsynchronized (length ((tr0 ++ pre_k)%list))
                                          (length ((((tr0 ++ pre_k) ++ [:: evk]) ++ post_k) ++ tr_pre_v)%list)
                                          evk evv).
                simpl in Hsynchronized.
                destruct (Hsynchronized ltac:(clear; erewrite! app_length in *; ssromega)
                                               ltac:(clear; do 4 rewrite <- app_assoc;
                                                     rewrite <- addn0;
                                                     rewrite <- nth_error_app; reflexivity)
                                                      ltac:(clear;
                                                            rewrite <- addn0;
                                                            rewrite <- app_assoc;
                                                            rewrite <- nth_error_app; reflexivity) Hcompeteskj)
                  as [[r [a [er [ea [Horderra [Horderra' [Hevr [Heva [Hactr [Hacta Hloc_ra]]]]]]]]]] |
                      [s [es [Horders [Hs Hacts]]]]].
                + (** Case there is a [Release]-[Acquire] pair between k and v*)
                  left.
                  exists r, a, er, ea.
                  repeat split; auto.
                  * clear - Horderra Horderra' Horder.
                    rewrite! app_assoc_reverse in Horderra'.
                    erewrite! app_length in *.
                    apply/andP.
                    split; now ssromega.
                  * clear - Horderra Horderra' Horder Hj_not_in_tr.
                    rewrite! app_assoc_reverse in Horderra'.
                    erewrite! app_length in *.
                    ssromega.
                  * eapply nth_error_app_inv;
                      eassumption.
                  * eapply nth_error_app_inv;
                      eassumption.
                + (** Case there is a [Spawn] event between k and v*)
                  right.
                  exists s, es.
                  repeat split; auto.
                  * clear - Horders Horder Hj_not_in_tr.
                    erewrite! app_assoc_reverse in *.
                    erewrite! app_length in *.
                    ssromega.
                  * eapply nth_error_app_inv;
                    now eauto.
              - (** Case permissions were increased by a [Mklock] event*)
                (** In this case, [evv] competes with [evk] and by the premise
                that [tr] is [spinlock_synchronized] there will be a [Spawn] or
                [Release]-[Acquire] pair between them and hence between [evk]
                and [evj] as well *)
                assert (Hcompeteskj: competes evk evv).
                { repeat split; eauto.
                  - rewrite Hthreadv.
                    now auto.
                  - unfold sameLocation.
                    destruct (location evv) as [[[bv ofsv] szv]|]; try (by exfalso).
                    destruct Hloc_v as [Heqb Hintvv].
                    simpl in Heqb. subst.
                    rewrite Hloc_k.
                    split; auto.
                    exists ofs.
                    split; now auto.
                  - destruct evv as [? evv | ? evv];
                    destruct evv; simpl in Hactionv; simpl;
                    try (by exfalso);
                    now auto.
                  - intros.
                    exfalso.
                    destruct evv as [? evv | ? evv];
                      simpl in Hactionv;
                      destruct evv; try (discriminate);
                      try (by exfalso).
                }
                rewrite! app_assoc in Hsynchronized.
                specialize (Hsynchronized (length ((tr0 ++ pre_k)%list))
                                          (length ((((tr0 ++ pre_k) ++ [:: evk]) ++ post_k) ++ tr_pre_v)%list)
                                          evk evv).
                simpl in Hsynchronized.
                destruct (Hsynchronized ltac:(clear; erewrite! app_length in *; ssromega)
                                               ltac:(clear; do 4 rewrite <- app_assoc;
                                                     rewrite <- addn0;
                                                     rewrite <- nth_error_app; reflexivity)
                                                      ltac:(clear;
                                                             rewrite <- addn0;
                                                             rewrite <- app_assoc;
                                                             rewrite <- nth_error_app; reflexivity) Hcompeteskj)
                  as [[r [a [er [ea [Horderra [Horderra' [Hevr [Heva [Hactr [Hacta Hloc_ra]]]]]]]]]] |
                      [s [es [Horders [Hs Hacts]]]]].
                + (** Case there is a [Release]-[Acquire] pair between k and v*)
                  left.
                  exists r, a, er, ea.
                  repeat split; auto.
                  * clear - Horderra Horderra' Horder.
                    rewrite! app_assoc_reverse in Horderra'.
                    erewrite! app_length in *.
                    apply/andP.
                    split; now ssromega.
                  * clear - Horderra Horderra' Horder Hj_not_in_tr.
                    rewrite! app_assoc_reverse in Horderra'.
                    erewrite! app_length in *.
                    ssromega.
                  * eapply nth_error_app_inv;
                    eassumption.
                  * eapply nth_error_app_inv;
                    eassumption.
                + (** Case there is a [Spawn] event between k and v*)
                  right.
                  exists s, es.
                  repeat split; auto.
                  * clear - Horders Horder Hj_not_in_tr.
                    erewrite! app_assoc_reverse in *.
                    erewrite! app_length in *.
                    ssromega.
                  * eapply nth_error_app_inv;
                    now eauto.
              - (** Case permissions were increased by an [Acquire] event*)
                destruct Hrmap as [rmap Hlocv].
                destruct (location evv) as [[laddr sz]|] eqn: Hloc_v; try (by exfalso).
                destruct Hlocv as [Hsz [HlockRes_v Hperm_res]]; subst.
                (** [rmap] at [tp_k'] will either not exist or if it exists will be below [Readable]*)
                destruct (lockRes tp_k' laddr) as [rmap_k|] eqn:Hres_k.
                + (** By [invariant] at [tp_k'] [rmap_k !! b ofs] will be below [Readable]*)
                  assert (Hperm_rmap_k: ~ Mem.perm_order'' (rmap_k.1 !! b ofs) (Some Readable) /\
                                        ~ Mem.perm_order'' (rmap_k.2 !! b ofs) (Some Readable)).
                  { clear - Hres_k Hinvk' Hwritablek.
                    pose proof ((no_race _ Hinvk' _ _ cntk' _ Hres_k).1 b ofs) as [? Hcomp].
                    pose proof ((no_race _ Hinvk' _ _ cntk' _ Hres_k).2 b ofs) as [? Hcomp2].
                    pose proof ((thread_data_lock_coh _ Hinvk' _ cntk').2 _ _ Hres_k b ofs) as Hcoh.
                    pose proof ((locks_data_lock_coh _ Hinvk' _ _ Hres_k).1 _ cntk' b ofs) as Hcoh2.
                    destruct Hwritablek;
                    split; intros Hcontra;
                    repeat match goal with
                           | [H: Mem.perm_order'' ?X _ |- _] =>
                             destruct X; simpl in H; inv H; simpl in *
                           | [H: match ?X with _ => _ end = _ |- _] =>
                             destruct X
                           end; simpl in *;
                    try (discriminate || by exfalso).
                  }

                  assert (Hperm_incr':
                            (~ Mem.perm_order'' ((rmap_k#1) # b ofs) (Some Readable) /\
                              Mem.perm_order'' ((rmap#1) # b ofs) (Some Readable)) \/
                            (~ Mem.perm_order'' ((rmap_k#2) # b ofs) (Some Readable) /\
                              Mem.perm_order'' ((rmap#2) # b ofs) (Some Readable)))
                    by (destruct Hperm_rmap_k; destruct Hperm_res; now auto).
                  (** Then there must have soome [Release] event on that lock to
                  increase its permissions*)
                  destruct (lockRes_permission_increase_execution _ _ _ _ Hres_k HlockRes_v
                                                                  Hexec_pre_v Hperm_incr')
                    as (u & evu & Hu & Hactionu & Hlocu).
                  left.
                  exists ((length (((tr0 ++ pre_k) ++ [:: evk]) ++ post_k)%list) + u),
                  (length ((((tr0 ++ pre_k) ++ [:: evk]) ++ post_k) ++ tr_pre_v)%list), evu, evv.
                  repeat split.
                  * clear - Hu Hj_not_in_tr Horder.
                    erewrite! app_assoc in *.
                    erewrite! app_length in *.
                    simpl in *.
                    apply/andP.
                    move/andP:Horder=>[? ?].
                    split. now ssromega.
                    pose proof ((nth_error_Some tr_pre_v u).1 ltac:(intros Hcontra; congruence)).
                    simpl.
                    now ssromega.
                  * clear - Hj_not_in_tr.
                    erewrite! app_assoc in *;
                      erewrite! app_length in *.
                    erewrite <- Nat.le_ngt in Hj_not_in_tr.
                    simpl in *. now ssromega.
                  * do 3 rewrite <- app_assoc.
                    rewrite <- nth_error_app.
                    eapply nth_error_app_inv;
                      now eauto.
                  * do 2 rewrite <- app_assoc.
                    rewrite <- addn0.
                    rewrite <- nth_error_app.
                    reflexivity.
                  * assumption.
                  * assumption.
                  * rewrite Hloc_v Hlocu.
                    reflexivity.
                + (** Case the lock was not created at index k*)
                  (** Since the lock exists at v someone must have created it*)
                  destruct (lockRes_mklock_execution _ _ Hres_k HlockRes_v Hexec_pre_v)
                    as (tr_prew & evw & ? & ? & tp_prew & m_prew & tp_mk & m_mk
                        & Hexec_prew & Hstep_mk & Hexec_postw & Hactionw & Hlocw & Hlock_mk).
                  (** At that point it's resources would be empty. But later the
                  lock has a [Readable] permission in it, hence there must be a
                  [Release] on that lock*)
                  assert (Hperm_mk:
                            ~ Mem.perm_order'' ((empty_map, empty_map).1 !! b ofs) (Some Readable) /\
                            ~ Mem.perm_order'' ((empty_map, empty_map).2 !! b ofs) (Some Readable))
                    by (rewrite empty_map_spec; simpl; now auto).
                  destruct (multi_step_trace_monotone Hexec_postw) as [tr_post_mk Heq_tr].
                  rewrite! app_assoc_reverse in Heq_tr.
                  do 4 apply app_inv_head in Heq_tr; subst.
                  rewrite! app_assoc in Hexec_postw.
                  assert (Hperm_res_incr':
                            (~ Mem.perm_order'' (((empty_map, empty_map)#1) # b ofs)
                              (Some Readable) /\
                              Mem.perm_order'' ((rmap#1) # b ofs) (Some Readable)) \/
                            (~ Mem.perm_order'' (((empty_map, empty_map)#2) # b ofs)
                               (Some Readable) /\
                              Mem.perm_order'' ((rmap#2) # b ofs) (Some Readable)))
                    by (destruct Hperm_mk; destruct Hperm_res; now auto).
                  destruct (lockRes_permission_increase_execution _ _ _ _ Hlock_mk HlockRes_v
                                                                  Hexec_postw Hperm_res_incr')
                    as (u & evu & Hu & Hactionu & Hlocu).
                  left.
                  exists (length (((((tr0 ++ pre_k) ++ [:: evk]) ++ post_k) ++ tr_prew ++ [:: evw])%list) + u),
                  (length ((((tr0 ++ pre_k) ++ [:: evk]) ++ post_k) ++ tr_prew ++ [:: evw] ++
                                                                    tr_post_mk) %list), evu, evv.
                  repeat split.
                  * clear - Hu Hj_not_in_tr Horder.
                    erewrite! app_assoc in *.
                    erewrite! app_length in *.
                    simpl in *.
                    apply/andP.
                    move/andP:Horder=>[? ?].
                    split. now ssromega.
                    pose proof ((nth_error_Some tr_post_mk u).1 ltac:(intros Hcontra; congruence)).
                    simpl.
                    now ssromega.
                  * clear - Hj_not_in_tr.
                    erewrite! app_assoc in *;
                      erewrite! app_length in *.
                    erewrite <- Nat.le_ngt in Hj_not_in_tr.
                    simpl in *. now ssromega.
                  * rewrite! app_assoc.
                    do 3 rewrite <- app_assoc.
                    rewrite <- nth_error_app.
                    eapply nth_error_app_inv;
                      now eauto.
                  * do 2 rewrite <- app_assoc.
                    rewrite <- addn0.
                    rewrite <- nth_error_app.
                    reflexivity.
                  * assumption.
                  * assumption.
                  * rewrite Hloc_v Hlocu.
                    reflexivity.
            }
          }

        { (** Case [thread_id evj] was not in the threadpool*)
          destruct (thread_spawn_execution _ Hnot_contained cntj Hexec')
            as (tr_pre_spawn & evv & ? & ? & tp_pre_spawn & m_pre_spawn &
                tp_spanwed & m_spanwed & Hexec_pre_spawn & Hstep_spawn &
                Hexec_post_spawn & Hactionv).
          right.
          destruct (multi_step_trace_monotone Hexec_post_spawn) as [tr''0 Heq].
          rewrite! app_assoc_reverse in Heq.
          do 4 apply app_inv_head in Heq; subst.
          rewrite! app_assoc.
          exists (length ((((tr0 ++ pre_k) ++ [:: evk]) ++ post_k) ++ tr_pre_spawn)%list), evv.
          repeat split.
          + clear - Hj_not_in_tr Horder.
            erewrite! app_assoc in *.
            erewrite! app_length in *.
            simpl.
            apply/andP.
            split.
            now ssromega.
            erewrite <- Nat.le_ngt in Hj_not_in_tr.
            simpl in *.
            now ssromega.
          + rewrite <- addn0.
            do 2 rewrite <- app_assoc.
            rewrite <- nth_error_app.
            now reflexivity.
          + assumption.
        }
        Unshelve.
        all:auto.
    Qed.

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
          rewrite <- app_assoc in IHU.
          eapply IHU with (tp0 := tp0) (tp := tp'0) (m0 := m0) (m := m'0).
          eassumption.
          rewrite <- app_nil_l with (l := tr ++ tr'0).
          eapply multi_step_snoc; eauto.
          now eauto.
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

  End SpinLocks.
End SpinLocks.
