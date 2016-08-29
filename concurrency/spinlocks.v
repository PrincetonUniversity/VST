(** ** Spinlock well synchronized*)
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
Require Import concurrency.concurrent_machine.
Require Import concurrency.memory_lemmas.
Require Import concurrency.dry_context.
Require Import concurrency.fineConc_safe.
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

  (*  Inductive fine_execution :
    FineConc.MachState -> mem -> FineConc.MachState -> mem -> Prop :=
  | refl_fine_exec : forall ms (m : mem),
      FineConc.halted ms ->
      fine_execution ms m ms m
  | step_fine_trans : forall i U U'
                             (tp tp' tp'': FineConc.machine_state)
                             (tr tr' tr'': FineConc.event_trace)
                             (m m' m'' : mem),
      FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr ++ tr', tp') m' ->
      fine_execution (U, tr ++ tr', tp') m' (U', tr ++ tr' ++ tr'', tp'') m'' ->
      fine_execution (i :: U,tr,tp) m (U',tr ++ tr' ++ tr'',tp'') m''. *)

  Inductive fine_execution :
    FineConc.MachState -> mem -> FineConc.MachState -> mem -> Prop :=
  | refl_fine_exec : forall ms (m : mem),
      fine_execution ms m ms m
  | step_fine_trans : forall i U U'
                             (tp tp' tp'': FineConc.machine_state)
                             (tr tr' tr'': FineConc.event_trace)
                             (m m' m'' : mem),
      FineConc.MachStep the_ge (i :: U, tr, tp) m (U, tr ++ tr', tp') m' ->
      fine_execution (U, tr ++ tr', tp') m' (U', tr ++ tr' ++ tr'', tp'') m'' ->
      fine_execution (i :: U,tr,tp) m (U',tr ++ tr' ++ tr'',tp'') m''.

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

  Lemma step_ext_trace:
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
  
  
  Lemma fine_execution_inv_ext:
    forall U U' i tr tr' tp m tp' m' ev
           (Hext: is_external ev)
           (Hi: nth_error tr' i = Some ev)
           (Hexec: fine_execution (U, tr, tp) m (U', tr ++ tr', tp') m'),
    exists U'' U''' tp'' m'' tr'' tp''' m''',
      fine_execution (U, tr, tp) m (U'', tr ++ tr'', tp'') m'' /\
      FineConc.MachStep the_ge (U'', tr ++ tr'', tp'') m''
                        (U''', tr ++ tr'' ++ [:: ev], tp''') m''' /\
      fine_execution (U''', tr ++ tr'' ++ [:: ev], tp''') m'''
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
          assert (tr'0 = [:: ev]) by (eapply step_ext_trace; eauto).
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

  Lemma fine_execution_inv:
    forall U U' i tr tr' tp m tp' m' ev
           (Hi: nth_error tr' i = Some ev)
           (Hexec: fine_execution (U, tr, tp) m (U', tr ++ tr', tp') m'),
    exists U'' U''' tp'' m'' tr'' pre_ev post_ev  tp''' m''',
      fine_execution (U, tr, tp) m (U'', tr ++ tr'', tp'') m'' /\
      FineConc.MachStep the_ge (U'', tr ++ tr'', tp'') m''
                        (U''', tr ++ tr'' ++ pre_ev ++ [:: ev] ++ post_ev, tp''') m''' /\
      fine_execution (U''', tr ++ tr'' ++ pre_ev ++ [:: ev] ++ post_ev , tp''') m'''
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
      | internal _ (Alloc _ _ _) => None
      | internal _ (Free _) => None
      | external _ (release _) => Some Release
      | external _ (acquire _) => Some Acquire
      | external _ (mklock _) => Some Mklock
      | external _ (freelock _) => Some Freelock
      | external _ (spawn _) => None
      | external _ (failacq _) => Some Failacq
      end.
  
  Definition competes (ev1 ev2 : Events.machine_event) : Prop :=
    thread_id ev1 <> thread_id ev2 /\
    sameLocation ev1 ev2 /\
    (is_internal ev1 ->
     is_internal ev2 ->
     caction ev1 ->
     caction ev2 ->
     action ev1 = Some Write \/ action ev2 = Some Write) /\
    (is_external ev1 \/ is_external ev2 ->
     action ev1 = Some Mklock \/ action ev1 = Some Freelock
     \/ action ev2 = Some Mklock \/ action ev2 = Some Freelock).

  (** Spinlock well synchronized*)
  Definition spinlock_synchronized (tr : SC.event_trace) :=
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

  Definition spinlock_synchronized' (tr : SC.event_trace) :=
    forall ev1 ev2 tr1 tr2 tr3
           (Htr: tr = tr1 ++ [:: ev1] ++ tr2 ++ [:: ev2] ++ tr3)
           (Hcompete: competes ev1 ev2),
    exists evl evu tr2' tr2'' tr2''',
      tr2 = tr2' ++ [:: evu] ++ tr2'' ++ [:: evl] ++ tr2'''/\
      action evu = Some Release /\ action evl = Some Acquire /\
      location evu = location evl.
  
  (** Spinlock clean *)
  Definition spinlock_clean (tr : FineConc.event_trace) :=
    forall i j evi evj
      (Hij: i < j)
      (Hi: List.nth_error tr i = Some evi)
      (Hj: List.nth_error tr j = Some evj)
      (Hmklock: action evi = Some Mklock)
      (Hfreelock: forall u evu, i < u < j ->
                                List.nth_error tr u = Some evu ->
                                action evu <> Some Freelock \/
                                location evu <> location evi)
      (Hlocation: sameLocation evj evi),
      action evj <> Some Write /\ action evj <> Some Read.

  (** After a step that generates a [mklock] event at [address] addr,
  addr will be in the lockSet *)
  Lemma Mklock_lockRes:
    forall i U tr tp m tp' m' addr
           (Hstep: FineConc.MachStep
                     the_ge (i :: U, tr, tp) m
                     (U, tr ++ [:: external i (Events.mklock addr)], tp') m'),
      lockRes tp' addr.
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
    rewrite gsslockResUpdLock. auto.
  Qed.

  Lemma remLockRes_Freelock:
    forall i U tr tr' tp m tp' m' addr
           (Hlock: lockRes tp addr)
           (Hstep: FineConc.MachStep
                     the_ge (i :: U, tr, tp) m
                     (U, tr ++ tr', tp') m')
           (Hev: forall u ev, nth_error tr' u = Some ev ->
                              action ev <> Some Freelock \/
                              location ev <> Some (addr, lksize.LKSIZE_nat)),
      lockRes tp' addr.
  Proof.
    intros.
    inv Hstep; simpl in *;
    try (inversion Htstep;
          subst tp');
    try (rewrite gsoThreadCLPool; auto);
    try (rewrite gsoThreadLPool; auto);
    try subst tp'0 tp''.
    - destruct (EqDec_address (b, Int.intval ofs) addr); subst.
      rewrite gssLockRes; auto.
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
  
  Lemma remLockRes_Freelock_execution:
    forall U U' tr tr' tp m tp' m' addr
           (Hlock: lockRes tp addr)
           (Hstep: fine_execution (U, tr, tp) m
                                  (U', tr ++ tr', tp') m')
           (Hfreelock: forall (u : nat) (evu : machine_event),
               nth_error tr' u = Some evu ->
               action evu <> Some Freelock \/
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
        destruct Helim'; auto.
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

  Lemma fstep_clean:
    forall U U' tp m addr tr pre ev post tp' m' tidi
           (Hlock: lockRes tp addr)
           (Hlocation: sameLocation ev (external tidi (mklock addr)))
           (Hstep: FineConc.MachStep the_ge (U, tr, tp) m
                                     (U', tr ++ pre ++ [:: ev] ++ post, tp') m'),
      action ev <> Some Write /\ action ev <> Some Read.
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
        destruct Helim_ev as [m'' [Hstore [Helim' Hbytes]]].
        clear - Hstore Heq Hperm Hbytes Hintv.
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
    
    assert (Hsched: U' = tidi :: U'')
      by (eapply fstep_event_sched in Hstep; simpl in Hstep; assumption).
    rewrite Hsched in Hstep.
    apply Mklock_lockRes in Hstep.

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
  
  (** A location that has been freed and the machine can no longer
  access (i.e. the permission is empty in all its resources) *) 
  Inductive freedLocation tp b ofs : Prop :=
  | Freed: forall
      (Hthreads: forall i (cnti: containsThread tp i),
          (getThreadR cnti) !! b ofs = None)
      (Hlocks: (lockSet tp) !! b ofs = None)
      (Hresources: forall l pmap,
          lockRes tp l = Some pmap ->
          pmap !! b ofs = None),
      freedLocation tp b ofs.

  (** Permission decrease: A permission decrease is caused either by a
  free event or a release event. *)
  Lemma permission_decrease_execution:
    forall U tr tp m U' tpi mi pre_i post_i U'' tr' tp' m'
           U''' pre_j post_j tpj mj
           i j evi evj b ofs tidn
           (cnt: containsThread tp tidn)
           (cnt': containsThread tp' tidn)
           (Hstepi: FineConc.MachStep
                      the_ge (U, tr, tp) m
                      (U', tr ++ pre_i ++ [:: evi] ++ post_i, tpi) mi)
           (Hexec: fine_execution
                     (U', tr ++ pre_i ++ [:: evi] ++ post_i, tpi) mi
                     (U'', tr ++ pre_i ++ [:: evi] ++ post_i ++ tr', tp') m')
           (Hstepj: FineConc.MachStep
                      the_ge (U'', tr ++ pre_i ++ [:: evi] ++
                                      post_i ++ tr', tp') m'
                      (U''', tr ++ pre_i ++ [:: evi] ++
                                post_i ++ tr' ++
                                pre_j ++ [:: evj] ++ post_j, tpj) mj)
           (Hperm: Mem.perm_order'' ((getThreadR cnt) !! b ofs)
                                    ((getThreadR cnt') !! b ofs))
           (Hperm': (getThreadR cnt) !! b ofs <> (getThreadR cnt') !! b ofs),
    exists u evu,
      nth_error tr' u = Some evu /\
      ((action evu = Free /\ freedLocation b ofs) \/
       (action evu = Release /\
        (forall k, k < u ->
                   action k <> Release \/ location k <> location u))).
       
  
                    
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
      
    
           

     