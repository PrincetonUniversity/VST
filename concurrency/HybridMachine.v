From mathcomp.ssreflect Require Import ssreflect seq ssrbool ssrfun.
Require Import compcert.common.Memory.
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs.
Require Import compcert.lib.Integers.

Require Import msl.Axioms.
Require Import Coq.ZArith.ZArith.
Require Import sepcomp.semantics.
Require Import sepcomp.event_semantics.
Require Export concurrency.semantics.
Require Export concurrency.lksize.
Require Import concurrency.threadPool. Export threadPool.

Require Import concurrency.machine_semantics.
Require Import concurrency.permissions.
Require Import concurrency.bounded_maps.
Require Import concurrency.addressFiniteMap.

Require Import concurrency.scheduler.
Require Import Coq.Program.Program.

Require Import concurrency.safety.

Require Import concurrency.coinductive_safety.


Require Import concurrency.concurrent_machine_rec.

Require Import veric.res_predicates.
Require Import veric.Clight_new.
Require Import veric.Clightnew_coop.

Require Import concurrency.HybridMachineSig.

Require Import concurrency.CoreSemantics_sum.



Section HybridMachine.
  
  Definition Resources: Resources_rec:=
    Build_Resources_rec (access_map * access_map) (access_map * access_map).
  Notation res:= (recres Resources).
  Notation lock_info:= (reclock_info Resources).

  Definition take_the_first (ress: res): access_map:= ress.1.
  
  (*Semantics *)
  Parameter CLN_evsem : (@EvSem genv corestate).
  Parameter CLN_msem :
    msem CLN_evsem = CLN_memsem.


  (** *The Hybrid Semantics Build*)
  Variables hb: option nat.
  Variables Sems Semt: Semantics_rec.
  
  Definition Sem: Semantics_rec:= CoreSem_Sum hb Sems Semt.
  (* Definition Sem: Semantics_rec.
    apply (@Build_Semantics_rec (*fundef type*) genv corestate CLN_evsem (*fun g => genv_genv g*)).
  Defined.*)

  Notation C:= (semC Sem).
  Notation G:= (semG Sem).
  Notation semSem:= (semSem Sem).
  
  Definition ThreadPool :=  OrdinalThreadPool_rec Resources Sem.
  (** Memories*)
  Definition richMem: Type:= mem.
  Definition dryMem: richMem -> mem:= id.
  Definition diluteMem: mem -> mem := setMaxPerm.

  Notation thread_pool := (t_ ThreadPool).
  Notation containsThread := (@containsThread_ _ _ ThreadPool).
  Notation getThreadC:= (@getThreadC_ _ _ ThreadPool).
  Notation getThreadR:= (getThreadR_ ThreadPool).
  Notation lockGuts:= (lockGuts_ ThreadPool).
  Notation lockSet:= (lockSet_ ThreadPool).
  Notation lockRes:= (lockRes_ ThreadPool).
  Notation addThread:= (addThread_ ThreadPool).
  Notation updThreadC:= (@updThreadC_ _ _ ThreadPool).
  Notation updThreadR:= (updThreadR_ ThreadPool).
  Notation updThread:= (updThread_ ThreadPool).
  Notation updLockSet:= (updLockSet_ ThreadPool).
  Notation remLockSet:= (remLockSet_ ThreadPool).
  Notation latestThread:= (latestThread_ ThreadPool).
  Notation lr_valid:= (lr_valid_ ThreadPool).
  Notation find_thread:= (find_thread_ ThreadPool).
  Notation cntUpdate:= (cntUpdate_ ThreadPool).
  Notation cntUpdate':= (cntUpdate'_ ThreadPool).
  Notation gssThreadCode:= (gssThreadCode_ ThreadPool).
  Notation gsoThreadCode:= (gsoThreadCode_ ThreadPool).
  Notation gLockSetCode:= (gLockSetCode_ ThreadPool).
  Notation gsoAddCode:= (gsoAddCode_ ThreadPool).
  Notation gRemLockSetCode:= (gRemLockSetCode_ ThreadPool).
  Notation gssAddCode:= (gssAddCode_ ThreadPool).
  Notation gsoThreadCC:= (gsoThreadCC_ ThreadPool).

  

  
  (** The state respects the memory*)

     Record mem_compatible' (tp: thread_pool ) m : Prop :=
       { compat_th :> forall {tid} (cnt: containsThread_ _ tp tid),
             permMapLt (getThreadR_ _ cnt).1 (getMaxPerm m) /\
             permMapLt (getThreadR_ _ cnt).2 (getMaxPerm m);
         compat_lp : forall l pmaps, lockRes tp l = Some pmaps ->
                                permMapLt pmaps.1 (getMaxPerm m) /\
                                permMapLt pmaps.2 (getMaxPerm m);
         lockRes_blocks: forall l rmap, lockRes tp l = Some rmap ->
                                   Mem.valid_block m l.1}.

     Definition mem_compatible tp m : Prop := mem_compatible' tp m.


     (* should there be something that says that if something is a lock then
     someone has at least readable permission on it?*)
     Record invariant' (tp: thread_pool ) :=
       { no_race_thr :
           forall i j (cnti: containsThread_ _ tp i) (cntj: containsThread_ _ tp j)
             (Hneq: i <> j),
             permMapsDisjoint2 (getThreadR_ _ cnti)
                              (getThreadR cntj); (*thread's resources are disjoint *)
         no_race_lr:
           forall laddr1 laddr2 rmap1 rmap2
             (Hneq: laddr1 <> laddr2)
             (Hres1: lockRes tp laddr1 = Some rmap1)
             (Hres2: lockRes tp laddr2 = Some rmap2),
             permMapsDisjoint2 rmap1 rmap2; (*lock's resources are disjoint *)
         no_race:
           forall i laddr (cnti: containsThread tp i) rmap
             (Hres: lockRes tp laddr = Some rmap),
             permMapsDisjoint2 (getThreadR cnti) rmap; (*resources are disjoint
             between threads and locks*)
         (* an address is in the lockres if there is at least one >= Readable
         lock permission - I am writing the weak version where this is required
         only for permissions of threads*)
         (* lock_res_perm: *)
         (*   forall b ofs, *)
         (*     (exists i (cnti: containsThread tp i), *)
         (*         Mem.perm_order' ((getThreadR cnti).2 !! b ofs) Readable) ->  *)
         (*     lockRes tp (b, ofs); *)

         (* if an address is a lock then there can be no data
             permission above non-empty for this address*)
         thread_data_lock_coh:
           forall i (cnti: containsThread tp i),
             (forall j (cntj: containsThread tp j),
                permMapCoherence (getThreadR cntj).1 (getThreadR cnti).2) /\
             (forall laddr rmap,
                 lockRes tp laddr = Some rmap ->
                 permMapCoherence rmap.1 (getThreadR cnti).2);
         locks_data_lock_coh:
           forall laddr rmap
             (Hres: lockRes tp laddr = Some rmap),
             (forall j (cntj: containsThread tp j),
                 permMapCoherence (getThreadR cntj).1 rmap.2) /\
             (forall laddr' rmap',
                 lockRes tp laddr' = Some rmap' ->
                 permMapCoherence rmap'.1 rmap.2);
         lockRes_valid: lr_valid (lockRes_ _ tp) (*well-formed locks*)
       }.
     Definition invariant := invariant'.

     (** Steps*)
     Inductive dry_step genv {tid0 tp m} (cnt: containsThread tp tid0)
               (Hcompatible: mem_compatible tp m) :
       thread_pool -> mem -> seq.seq mem_event -> Prop :=
     | step_dry :
         forall (tp':thread_pool) c m1 m' (c' : C) ev
           (** Instal the permission's of the thread on non-lock locations*)
           (Hrestrict_pmap: restrPermMap (Hcompatible tid0 cnt).1 = m1)
           (Hinv: invariant tp)
           (Hcode: getThreadC cnt = Krun c)
           (Hcorestep: ev_step semSem genv c m1 ev c' m')
           (** the new data resources of the thread are the ones on the
           memory, the lock ones are unchanged by internal steps*)
           (Htp': tp' = updThread cnt (Krun c') (getCurPerm m', (getThreadR cnt).2)),
           dry_step genv cnt Hcompatible tp' m' ev.

     Definition option_function {A B} (opt_f: option (A -> B)) (x:A): option B:=
       match opt_f with
         Some f => Some (f x)
       | None => None
       end.
     Infix "??" := option_function (at level 80, right associativity).

     Inductive ext_step {isCoarse:bool} (genv:G) {tid0 tp m}
               (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
       thread_pool -> mem -> sync_event -> Prop :=
     | step_acquire :
         forall (tp' tp'':thread_pool) m0 m1 c m' b ofs
           (pmap : lock_info)
           (pmap_tid' : access_map)
           (virtueThread : delta_map * delta_map)
           (Hbounded: if isCoarse then
                        ( sub_map virtueThread.1 (getMaxPerm m).2 /\
                          sub_map virtueThread.2 (getMaxPerm m).2)
                      else
                        True ),
           let newThreadPerm := (computeMap (getThreadR cnt0).1 virtueThread.1,
                                  computeMap (getThreadR cnt0).2 virtueThread.2) in
           forall
             (Hinv : invariant tp)
             (Hcode: getThreadC cnt0 = Kblocked c)
             (Hat_external: semantics.at_external semSem c = Some (LOCK, Vptr b ofs::nil))
             (** install the thread's permissions on lock locations*)
             (Hrestrict_pmap0: restrPermMap (Hcompat tid0 cnt0).2 = m0)
             (** To acquire the lock the thread must have [Readable] permission on it*)
             (Haccess: Mem.range_perm m0 b (Int.intval ofs) ((Int.intval ofs) + LKSIZE) Cur Readable)
             (** check if the lock is free*)
             (Hload: Mem.load Mint32 m0 b (Int.intval ofs) = Some (Vint Int.one))
             (** set the permissions on the lock location equal to the max permissions on the memory*)
             (Hset_perm: setPermBlock (Some Writable)
                                       b (Int.intval ofs) ((getThreadR cnt0).2) LKSIZE_nat = pmap_tid')
             (Hlt': permMapLt pmap_tid' (getMaxPerm m))
             (Hrestrict_pmap: restrPermMap Hlt' = m1)
             (** acquire the lock*)
             (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
             (HisLock: lockRes tp (b, Int.intval ofs) = Some pmap)
             (Hangel1: permMapJoin pmap.1 (getThreadR cnt0).1 newThreadPerm.1)
             (Hangel2: permMapJoin pmap.2 (getThreadR cnt0).2 newThreadPerm.2)
             (Htp': tp' = updThread cnt0 (Kresume c Vundef) newThreadPerm)
             (** acquiring the lock leaves empty permissions at the resource pool*)
             (Htp'': tp'' = updLockSet tp' (b, Int.intval ofs) (empty_map, empty_map)),
             ext_step genv cnt0 Hcompat tp'' m'
                      (acquire (b, Int.intval ofs)
                               (Some virtueThread))

     | step_release :
         forall (tp' tp'':thread_pool) m0 m1 c m' b ofs virtueThread virtueLP pmap_tid' rmap
           (Hbounded: if isCoarse then
                        ( sub_map virtueThread.1 (getMaxPerm m).2 /\
                          sub_map virtueThread.2 (getMaxPerm m).2)
                      else
                        True )
           (HboundedLP: if isCoarse then
                        ( map_empty_def virtueLP.1 /\
                          map_empty_def virtueLP.2 /\
                          sub_map virtueLP.1.2 (getMaxPerm m).2 /\
                          sub_map virtueLP.2.2 (getMaxPerm m).2)
                      else
                        True ),
           let newThreadPerm := (computeMap (getThreadR cnt0).1 virtueThread.1,
                                 computeMap (getThreadR cnt0).2 virtueThread.2) in
           forall
             (Hinv : invariant tp)
             (Hcode: getThreadC cnt0 = Kblocked c)
             (Hat_external: semantics.at_external semSem c =
                            Some (UNLOCK, Vptr b ofs::nil))
             (** install the thread's permissions on lock locations *)
             (Hrestrict_pmap0: restrPermMap (Hcompat tid0 cnt0).2 = m0)
             (** To acquire the lock the thread must have [Readable] permission on it*)
             (Haccess: Mem.range_perm m0 b (Int.intval ofs) ((Int.intval ofs) + LKSIZE) Cur Readable)
             (Hload: Mem.load Mint32 m0 b (Int.intval ofs) = Some (Vint Int.zero))
             (** set the permissions on the lock location equal to the max permissions on the memory*)
             (Hset_perm: setPermBlock (Some Writable)
                                      b (Int.intval ofs) ((getThreadR cnt0).2) LKSIZE_nat = pmap_tid')
             (Hlt': permMapLt pmap_tid' (getMaxPerm m))
             (Hrestrict_pmap: restrPermMap Hlt' = m1)
             (** release the lock *)
             (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.one) = Some m')
             (HisLock: lockRes tp (b, Int.intval ofs) = Some rmap)
             (** And the lock is taken*)
             (Hrmap: forall b ofs, rmap.1 !! b ofs = None /\ rmap.2 !! b ofs = None)
             (Hangel1: permMapJoin newThreadPerm.1 virtueLP.1 (getThreadR cnt0).1)
             (Hangel2: permMapJoin newThreadPerm.2 virtueLP.2 (getThreadR cnt0).2)
             (Htp': tp' = updThread cnt0 (Kresume c Vundef)
                                    (computeMap (getThreadR cnt0).1 virtueThread.1,
                                     computeMap (getThreadR cnt0).2 virtueThread.2))
             (Htp'': tp'' = updLockSet tp' (b, Int.intval ofs) virtueLP),
             ext_step genv cnt0 Hcompat tp'' m'
                      (release (b, Int.intval ofs)
                               (Some virtueLP))
     | step_create :
         forall (tp_upd tp':thread_pool) c b ofs arg virtue1 virtue2
           (Hbounded: if isCoarse then
                        ( sub_map virtue1.1 (getMaxPerm m).2 /\
                          sub_map virtue1.2 (getMaxPerm m).2)
                      else
                        True )
             (Hbounded_new: if isCoarse then
                        ( sub_map virtue2.1 (getMaxPerm m).2 /\
                          sub_map virtue2.2 (getMaxPerm m).2)
                      else
                        True ),
           let threadPerm' := (computeMap (getThreadR cnt0).1 virtue1.1,
                               computeMap (getThreadR cnt0).2 virtue1.2) in
           let newThreadPerm := (computeMap empty_map virtue2.1,
                                 computeMap empty_map virtue2.2) in
           forall
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: semantics.at_external semSem c = Some (CREATE, Vptr b ofs::arg::nil))
           (** we do not need to enforce the almost empty predicate on thread
           spawn as long as it's considered a synchronizing operation *)
           (Hangel1: permMapJoin newThreadPerm.1 threadPerm'.1 (getThreadR cnt0).1)
           (Hangel2: permMapJoin newThreadPerm.2 threadPerm'.2 (getThreadR cnt0).2)
           (Htp_upd: tp_upd = updThread cnt0 (Kresume c Vundef) threadPerm')
           (Htp': tp' = addThread tp_upd (Vptr b ofs) arg newThreadPerm),
             ext_step genv cnt0 Hcompat tp' m
                      (spawn (b, Int.intval ofs)
                             (Some (getThreadR cnt0, virtue1)) (Some virtue2))


     | step_mklock :
         forall  (tp' tp'': thread_pool) m1 c m' b ofs pmap_tid',
           let: pmap_tid := getThreadR cnt0 in
           forall
             (Hinv : invariant tp)
             (Hcode: getThreadC cnt0 = Kblocked c)
             (Hat_external: semantics.at_external semSem c = Some (MKLOCK, Vptr b ofs::nil))
             (** install the thread's data permissions*)
             (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m1)
             (** To create the lock the thread must have [Writable] permission on it*)
             (Hfreeable: Mem.range_perm m1 b (Int.intval ofs) ((Int.intval ofs) + LKSIZE) Cur Writable)
             (** lock is created in acquired state*)
             (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
             (** The thread's data permissions are set to Nonempty*)
             (Hdata_perm: setPermBlock
                            (Some Nonempty)
                            b
                            (Int.intval ofs)
                            pmap_tid.1
                            LKSIZE_nat = pmap_tid'.1)
             (** thread lock permission is increased *)
             (Hlock_perm: setPermBlock
                            (Some Writable)
                            b
                            (Int.intval ofs)
                            pmap_tid.2
                            LKSIZE_nat = pmap_tid'.2)
             (** Require that [(b, Int.intval ofs)] was not a lock*)
             (HlockRes: lockRes tp (b, Int.intval ofs) = None)
             (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
             (** the lock has no resources initially *)
             (Htp'': tp'' = updLockSet tp' (b, Int.intval ofs) (empty_map, empty_map)),
             ext_step genv cnt0 Hcompat tp'' m' (mklock (b, Int.intval ofs))

     | step_freelock :
         forall  (tp' tp'': thread_pool) c b ofs pmap_tid' m1 pdata rmap
           (Hbounded: if isCoarse then
                        ( bounded_maps.bounded_nat_func' pdata LKSIZE_nat)
                      else
                        True ),
             let: pmap_tid := getThreadR cnt0 in
           forall
           (Hinv: invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: semantics.at_external semSem c = Some (FREE_LOCK, Vptr b ofs::nil))
           (** If this address is a lock*)
           (His_lock: lockRes tp (b, (Int.intval ofs)) = Some rmap)
           (** And the lock is taken *)
           (Hrmap: forall b ofs, rmap.1 !! b ofs = None /\ rmap.2 !! b ofs = None)
           (** Install the thread's lock permissions*)
           (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).2 = m1)
           (** To free the lock the thread must have at least Writable on it*)
           (Hfreeable: Mem.range_perm m1 b (Int.intval ofs) ((Int.intval ofs) + LKSIZE) Cur Writable)
           (** lock permissions of the thread are dropped to empty *)
           (Hlock_perm: setPermBlock
                          None
                          b
                          (Int.intval ofs)
                          pmap_tid.2
                          LKSIZE_nat = pmap_tid'.2)
           (** data permissions are computed in a non-deterministic way *)
           (Hneq_perms: forall i,
                 (0 <= Z.of_nat i < LKSIZE)%Z ->
                 Mem.perm_order'' (pdata (S i)) (Some Writable)
           )
           (*Hpdata: perm_order pdata Writable*)
           (Hdata_perm: setPermBlock_var (*=setPermBlockfunc*)
                          pdata
                          b
                          (Int.intval ofs)
                          pmap_tid.1
                          LKSIZE_nat = pmap_tid'.1)
           (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
           (Htp'': tp'' = remLockSet tp' (b, Int.intval ofs)),
           ext_step genv cnt0 Hcompat  tp'' m (freelock (b, Int.intval ofs))
     | step_acqfail :
         forall  c b ofs m1
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: semantics.at_external semSem c = Some (LOCK, Vptr b ofs::nil))
           (** Install the thread's lock permissions*)
           (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).2 = m1)
           (** To acquire the lock the thread must have [Readable] permission on it*)
           (Haccess: Mem.range_perm m1 b (Int.intval ofs) ((Int.intval ofs) + LKSIZE) Cur Readable)
           (** Lock is already acquired.*)
           (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero)),
           ext_step genv cnt0 Hcompat tp m (failacq (b, Int.intval ofs)).

     Definition threadStep (genv : G): forall {tid0 ms m},
         containsThread ms tid0 -> mem_compatible ms m ->
         thread_pool -> mem -> seq.seq mem_event -> Prop:=
       @dry_step genv.

     Lemma threadStep_equal_run:
    forall g i tp m cnt cmpt tp' m' tr,
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q').
    Proof.
      intros. split.
      - intros [cntj [ q running]].
        inversion H; subst.
        assert (cntj':=cntj).
        eapply (cntUpdate (Krun c') (getCurPerm m', (getThreadR cnt)#2) cntj) in cntj'.
        exists cntj'.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c'.
          rewrite gssThreadCode; reflexivity.
        + exists q.
          rewrite gsoThreadCode; auto.
      - intros [cntj' [ q' running]].
        inversion H; subst.
        assert (cntj:=cntj').
        eapply cntUpdate' with(c0:=Krun c')(p:=(getCurPerm m', (getThreadR cnt)#2)) in cntj; eauto.
        exists cntj.
        destruct (NatTID.eq_tid_dec i j).
        + subst j; exists c.
          rewrite <- Hcode.
          f_equal.
          apply cnt_irr.
        + exists q'.
          rewrite gsoThreadCode in running; auto.
    Qed.

     Definition syncStep (isCoarse:bool) (genv :G) :
       forall {tid0 ms m},
         containsThread ms tid0 -> mem_compatible ms m ->
         thread_pool -> mem -> sync_event -> Prop:=
       @ext_step isCoarse genv.




  Lemma syncstep_equal_run:
    forall b g i tp m cnt cmpt tp' m' tr,
      @syncStep b g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q').
  Proof.
    intros b g i tp m cnt cmpt tp' m' tr H j; split.
    - intros [cntj [ q running]].
      destruct (NatTID.eq_tid_dec i j).
      + subst j. generalize running; clear running.
        inversion H; subst;
          match goal with
          | [ H: getThreadC ?cnt = Kblocked ?c |- _ ] =>
            replace cnt with cntj in H by apply cnt_irr;
              intros HH; rewrite HH in H; inversion H
          end.
      + (*this should be easy to automate or shorten*)
        inversion H; subst.
        * exists (cntUpdateL _ _
                        (cntUpdate (Kresume c Vundef)
                                   newThreadPerm
                                   _ cntj)), q.
          rewrite gLockSetCode.
          rewrite gsoThreadCode; assumption.
        * exists ( (cntUpdateL _ _
                          (cntUpdate (Kresume c Vundef)
                                     (computeMap (getThreadR cnt)#1 virtueThread#1,
                                      computeMap (getThreadR cnt)#2 virtueThread#2)
                                     _ cntj))), q.
          rewrite gLockSetCode.
          rewrite gsoThreadCode; assumption.
        * exists (cntAdd _ _ _
                    (cntUpdate (Kresume c Vundef)
                               threadPerm'
                               _ cntj)), q.
          erewrite gsoAddCode . (*i? *)
          rewrite gsoThreadCode; assumption.
          eapply cntUpdate. eauto.
        * exists ( (cntUpdateL _ _
                          (cntUpdate (Kresume c Vundef)
                                     pmap_tid'
                                     _ cntj))), q.
          rewrite gLockSetCode.
          rewrite gsoThreadCode; assumption.
        * exists ( (cntRemoveL _
                          (cntUpdate (Kresume c Vundef)
                                     pmap_tid'
                                     _ cntj))), q.
          rewrite gRemLockSetCode.
          rewrite gsoThreadCode; assumption.
        * exists cntj, q; assumption.
    - intros [cntj [ q running]].
      destruct (NatTID.eq_tid_dec i j).
      + subst j. generalize running; clear running.
        inversion H; subst;
          try rewrite gLockSetCode;
          try rewrite gRemLockSetCode;
          try rewrite gssThreadCode;
          try solve[intros HH; inversion HH].
        { (*addthread*)
          assert (cntj':=cntj).
          eapply cntAdd' in cntj'; destruct cntj' as [ [HH HHH] | HH].
          * erewrite gsoAddCode; eauto.
            subst; rewrite gssThreadCode; intros AA; inversion AA.
          * erewrite gssAddCode . intros AA; inversion AA.
            assumption. }
          { (*AQCUIRE*)
            replace cntj with cnt by apply cnt_irr.
            rewrite Hcode; intros HH; inversion HH. }
      + generalize running; clear running.
        inversion H; subst;
        try erewrite <- age_getThreadCode;
          try rewrite gLockSetCode;
          try rewrite gRemLockSetCode;
          try (rewrite gsoThreadCode; [|auto]);
        try (intros HH;
        match goal with
        | [ H: getThreadC ?cnt = Krun ?c |- _ ] =>
          exists cntj, c; exact H
        end).
      (*Add thread case*)
        assert (cntj':=cntj).
        eapply cntAdd' in cntj'; destruct cntj' as [ [HH HHH] | HH].
        * erewrite gsoAddCode; eauto.
          destruct (NatTID.eq_tid_dec i j);
            [subst; rewrite gssThreadCode; intros AA; inversion AA|].
          rewrite gsoThreadCode; auto.
          exists HH, q; assumption.
        * erewrite gssAddCode . intros AA; inversion AA.
          assumption.



          Grab Existential Variables.
          eauto. eauto. eauto.
  Qed.


  Lemma syncstep_not_running:
    forall b g i tp m cnt cmpt tp' m' tr,
      @syncStep b g i tp m cnt cmpt tp' m' tr ->
      forall cntj q, ~ @getThreadC i tp cntj = Krun q.
  Proof.
    intros.
    inversion H;
      match goal with
      | [ H: getThreadC ?cnt = _ |- _ ] =>
        erewrite (cnt_irr _ cnt);
          rewrite H; intros AA; inversion AA
      end.
  Qed.



     Inductive threadHalted': forall {tid0 ms},
         containsThread ms tid0 -> Prop:=
     | thread_halted':
         forall tp c tid0
           (cnt: containsThread tp tid0)
           (*Hinv: invariant tp*)
           (Hcode: getThreadC cnt = Krun c)
           (Hcant: semantics.halted semSem c),
           threadHalted' cnt.

    Definition threadHalted: forall {tid0 ms},
         containsThread ms tid0 -> Prop:= @threadHalted'.


   (* Lemma updCinvariant': forall {tid} ds c (cnt: containsThread ds tid),
         invariant (updThreadC cnt c) <-> invariant ds.
           split.
           { intros INV; inversion INV.
             constructor.
             - generalize no_race; unfold race_free.
               simpl. intros.
               apply no_race0; auto.
             - simpl; assumption.
             - simpl; assumption.
             - simpl; assumption.
             - simpl; assumption. }

           { intros INV; inversion INV.
             constructor.
             - generalize no_race; unfold race_free.
               simpl. intros.
               apply no_race0; auto.
             - simpl; assumption.
             - simpl; assumption.
             - simpl; assumption.
             - simpl; assumption. }
     Qed. *)


  Lemma threadHalt_update:
    forall i j, i <> j ->
      forall tp cnt cnti c' cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j (@updThreadC i tp cnti c') cnt') .
  Proof.
    intros; split; intros HH; inversion HH; subst;
    econstructor; eauto.
    erewrite <- (gsoThreadCC H); exact Hcode.
    erewrite (gsoThreadCC H); exact Hcode.
  Qed.


     Definition one_pos : pos.pos := pos.mkPos NPeano.Nat.lt_0_1.

     Definition initial_machine ge c :=
       threadPool.mk
         Resources
         Sem
         one_pos
         (fun _ =>  Krun c)
         (fun _ => (pmap, empty_map)) (*initially there are no locks*)
         empty_lset.


     Definition init_mach (pmap : option res) (genv:G)
                (v:val)(args:list val):option thread_pool :=
       match semantics.initial_core semSem 0 genv v args with
       | Some c =>
         match pmap with
         | Some pmap => Some (initial_machine pmap.1 c)
         | None => None
         end
       | None => None
       end.

     Section HybDryMachineLemmas.


       (*TODO: This lemma should probably be moved. *)
       Lemma threads_canonical:
         forall ds m i (cnt:containsThread ds i),
           mem_compatible ds m ->
           isCanonical (getThreadR cnt).1 /\
           isCanonical (getThreadR cnt).2.
             intros.
             destruct (compat_th _ _ H cnt);
               eauto using canonical_lt.
       Qed.
       (** most of these lemmas are in DryMachinLemmas*)

       (** *Invariant Lemmas*)

       (** ** Updating the machine state**)
        (* Manny invaraint lemmas were removed from here. *)
     End HybDryMachineLemmas.



    (** *More Properties of halted thread*)
      Lemma threadStep_not_unhalts:
    forall g i tp m cnt cmpt tp' m' tr,
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) ->
        (@threadHalted j tp' cnt') .
  Proof.
    intros.
    inversion H; inversion H0; subst.
    destruct (NatTID.eq_tid_dec i j).
    - subst j.
      eapply ev_step_ax1 in Hcorestep.
      eapply corestep_not_halted in Hcorestep.
      replace cnt1 with cnt in Hcode0 by apply cnt_irr.
      rewrite Hcode0 in Hcode; inversion Hcode;
      subst c0.
      rewrite Hcorestep in Hcant; inversion Hcant.
    - econstructor; eauto.
      rewrite gsoThreadCode; auto;
      erewrite <- age_getThreadCode; eauto.
  Qed.


  Lemma syncstep_equal_halted:
    forall b g i tp m cnti cmpt tp' m' tr,
      @syncStep b g i tp m cnti cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j tp' cnt').
  Proof.
    intros; split; intros HH; inversion HH; subst;
    econstructor; subst; eauto.
    - destruct (NatTID.eq_tid_dec i j).
      + subst j.
        inversion H;
          match goal with
          | [ H: getThreadC ?cnt = Krun ?c,
                 H': getThreadC ?cnt' = Kblocked ?c' |- _ ] =>
            replace cnt with cnt' in H by apply cnt_irr;
              rewrite H' in H; inversion H
          end.
      + inversion H; subst;
        try erewrite <- age_getThreadCode;
          try rewrite gLockSetCode;
          try rewrite gRemLockSetCode;
          try erewrite gsoAddCode; eauto;
            try rewrite gsoThreadCode; try eassumption.
        * apply threadPool.cntUpdate; eauto. eapply cnt.
        * { (*AQCUIRE*)
            replace cnt' with cnt0 by apply cnt_irr;
            exact Hcode. }
        
    - destruct (NatTID.eq_tid_dec i j).
      + subst j.
        inversion H; subst;
        match goal with
          | [ H: getThreadC ?cnt = Krun ?c,
                 H': getThreadC ?cnt' = Kblocked ?c' |- _ ] =>
            try erewrite <- age_getThreadCode in H;
              try rewrite gLockSetCode in H;
              try rewrite gRemLockSetCode in H;
              try erewrite gsoAddCode in H; eauto;
              try rewrite gssThreadCode in H;
              try solve[inversion H]
        end.
        * apply threadPool.cntUpdate; eauto. apply cnt.
        * { (*AQCUIRE*)
            replace cnt with cnt0 by apply cnt_irr;
            exact Hcode. }
      +
        inversion H; subst;
        match goal with
          | [ H: getThreadC ?cnt = Krun ?c,
                 H': getThreadC ?cnt' = Kblocked ?c' |- _ ] =>
            try erewrite <- age_getThreadCode in H;
              try rewrite gLockSetCode in H;
              try rewrite gRemLockSetCode in H;
              try erewrite gsoAddCode in H; eauto;
              try rewrite gsoThreadCode in H;
              try solve[inversion H]; eauto
        end.
        * apply threadPool.cntUpdate; eauto. apply cnt.
        { (*AQCUIRE*)
            replace cnt with cnt0 by apply cnt_irr;
          exact Hcode. }

        Grab Existential Variables.
        eauto. eauto. eauto.
  Qed.

  Definition HybMachineSig: MachineSig_rec Resources Sem ThreadPool:=
    (@Build_MachineSig_rec Resources Sem ThreadPool
              richMem
              dryMem
              diluteMem
              mem_compatible
              invariant
              threadStep
              threadStep_equal_run
              syncStep
              syncstep_equal_run
              syncstep_not_running
              (@threadHalted)
              threadHalt_update
              syncstep_equal_halted
              threadStep_not_unhalts
              init_mach
           ).
    

(** *Building the hybrid machine*)
  
    (*Record HybridMachine_rec:=
      {
        MachineSemantics: schedule -> option res ->
                          CoreSemantics G MachState mem
        ; initial_schedule: forall genv main vals U U' p c tr n,
            initial_core (MachineSemantics U p) n genv main vals = Some (U',tr,c) ->
          U' = U /\ tr = nil
    }. *)

(* Module CoarseMachine (SCH:Scheduler)(SIG : ConcurrentMachineSig with Module ThreadPool.TID:=SCH.TID with Module Events.TID :=SCH.TID) <: ConcurrentMachine with Module SCH:= SCH with Module TP:= SIG.ThreadPool  with Module SIG:= SIG. *)

  (*Schedule*)

  Notation Sch:=(seq.seq nat).
  Notation event_trace := (seq.seq machine_event).
  Definition schedPeek sch: option nat:=
    match sch with
      nil => None
    | cons hd tl => Some hd
    end.
  
  Definition schedSkip sch: (seq.seq nat):= List.tl sch.
  Notation machine_state := thread_pool.

  (** Resume and Suspend: threads running must be preceded by a Resume
     and followed by Suspend.  This functions wrap the state to
     indicate it's ready to take a syncronisation step or resume
     running. (This keeps the invariant that at most one thread is not
     at_external) *)

  Inductive start_thread' genv: forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | StartThread: forall tid0 ms ms' c_new vf arg
                    (ctn: containsThread ms tid0)
                    (Hcode: getThreadC ctn = Kinit vf arg)
                    (Hinitial: semantics.initial_core semSem tid0
                                            genv vf (arg::nil) = Some c_new)
                    (Hinv: invariant ms)
                    (Hms': updThreadC ctn (Krun c_new)  = ms'),
      start_thread' genv ctn ms'.
  Definition start_thread genv: forall {tid0 ms}, 
      containsThread ms tid0 -> machine_state -> Prop:=
    @start_thread' genv.
  Inductive resume_thread': forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | ResumeThread: forall tid0 ms ms' c c' X
                    (ctn: containsThread ms tid0)
                    (Hat_external: semantics.at_external semSem c = Some X)
                    (Hafter_external: semantics.after_external semSem None c = Some c')
                    (Hcode: getThreadC ctn = Kresume c Vundef)
                    (Hinv: invariant ms)
                    (Hms': updThreadC ctn (Krun c')  = ms'),
      resume_thread' ctn ms'.
  Definition resume_thread: forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @resume_thread'.

  Inductive suspend_thread': forall {tid0} {ms:machine_state},
      containsThread ms tid0 -> machine_state -> Prop:=
  | SuspendThread: forall tid0 ms ms' c X
                     (ctn: containsThread ms tid0)
                     (Hcode: getThreadC ctn = Krun c)
                     (Hat_external: semantics.at_external semSem c = Some X)
                     (Hinv: invariant ms)
                     (Hms': updThreadC ctn (Kblocked c) = ms'),
      suspend_thread' ctn ms'.
  Definition suspend_thread : forall {tid0 ms},
      containsThread ms tid0 -> machine_state -> Prop:=
    @suspend_thread'.

  Inductive machine_step {genv:G}:
    Sch -> event_trace -> machine_state -> mem -> Sch ->
    event_trace -> machine_state -> mem -> Prop :=
  | start_step:
      forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: start_thread genv Htid ms'),
        machine_step U [::] ms m U [::] ms' m
  | resume_step:
      forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: resume_thread Htid ms'),
        machine_step U [::] ms m U [::] ms' m
  | thread_step:
      forall tid U ms ms' m m' ev
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: threadStep genv Htid Hcmpt ms' m' ev),
        machine_step U [::] ms m U [::] ms' m'
  | suspend_step:
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep:suspend_thread Htid ms'),
        machine_step U [::] ms m U' [::] ms' m
  | sync_step:
      forall tid U U' ms ms' m m' ev
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: syncStep true genv Htid Hcmpt ms' m' ev),
        machine_step U [::] ms m  U' [::] ms' m'
  | halted_step:
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hinv: invariant ms)
        (Hhalted: threadHalted Htid),
        machine_step U [::] ms m  U' [::] ms m
  | schedfail :
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (Htid: ~ containsThread ms tid)
        (Hinv: invariant ms)
        (HschedS: schedSkip U = U'),        (*Schedule Forward*)
        machine_step U [::] ms m U' [::] ms m.

  (*Lemma to deal with the trivial trace*)
  Lemma trace_nil: forall ge U tr st m U' tr' st' m',
      @machine_step ge U tr st m U' tr' st' m' ->
  tr = nil /\ tr' = nil.
  Proof. move=> ge U tr st m U' tr' st' m' ms; inversion ms; intuition. Qed.

  (*The new semantics bellow makes internal (thread) and external (machine) steps explicit*)
  Inductive internal_step {genv:G}:
    Sch -> machine_state -> mem -> machine_state -> mem -> Prop :=
  | thread_step':
      forall tid U ms ms' m m' ev
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: threadStep genv Htid Hcmpt ms' m' ev),
        internal_step U ms m ms' m'.

  Inductive external_step  {genv:G}:
    Sch -> event_trace -> machine_state -> mem -> Sch ->
    event_trace -> machine_state -> mem -> Prop :=
  | start_state': forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: start_thread genv Htid ms'),
        external_step U [::] ms m U [::] ms' m
  | resume_step':
      forall tid U ms ms' m
        (HschedN: schedPeek U = Some tid)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: resume_thread Htid ms'),
        external_step U [::] ms m U [::] ms' m
  | suspend_step':
      forall tid U U' ms ms' m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep:suspend_thread Htid ms'),
        external_step U [::] ms m U' [::] ms' m
  | sync_step':
      forall tid U U' ms ms' m m' ev
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Htstep: syncStep true genv Htid Hcmpt ms' m' ev),
        external_step U [::] ms m  U' [::] ms' m'
  | halted_step':
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (HschedS: schedSkip U = U')        (*Schedule Forward*)
        (Htid: containsThread ms tid)
        (Hcmpt: mem_compatible ms m)
        (Hinv: invariant ms)
        (Hhalted: threadHalted Htid),
        external_step U [::] ms m  U' [::] ms m
  | schedfail':
      forall tid U U' ms m
        (HschedN: schedPeek U = Some tid)
        (Htid: ~ containsThread ms tid)
        (Hinv: invariant ms)
        (HschedS: schedSkip U = U'),        (*Schedule Forward*)
        external_step U [::] ms m U' [::] ms m.
  (*Symmetry*)
  (* These steps are basically the same: *)
  Lemma step_equivalence1: forall ge U tr st m U' tr' st' m',
    @machine_step ge U tr st m U' tr' st' m' ->
    (U=U' /\ tr = tr' /\  @internal_step ge U st m st' m') \/
    @external_step ge U tr st m U' nil st' m'.
  Proof.
    move=> ge U tr st m U' tr' st' m' ms.
    inversion ms;
      first[ solve [ left; repeat split=>//; econstructor; eauto] |
             solve[right; econstructor; eauto]].
  Qed.
  Lemma step_equivalence2: forall ge U st m st' m',
      @internal_step ge U st m st' m' ->
      @machine_step ge U nil st m U nil st' m'.
  Proof. move=>  ge U st m st' m' istp.
         by inversion istp; econstructor; eauto.
  Qed.
   Lemma step_equivalence3: forall ge U tr st m U' tr' st' m',
      @external_step ge U tr st m U' tr' st' m' ->
      @machine_step ge U tr st m U' tr' st' m'.
   Proof. move=>  ge U tr st m U' nil st' m' estp.
          inversion estp;
          [
              solve[econstructor 1 ; eauto]|
              solve[econstructor 2 ; eauto]|
              solve[econstructor 4 ; eauto]|
              solve[econstructor 5 ; eauto]|
              solve[econstructor 6 ; eauto]|
              solve[econstructor 7 ; eauto]].
   Qed.

  Notation MachState:= (@MachState _ _ ThreadPool).

  Definition MachStep G (c:MachState) (m:mem)
             (c' :MachState) (m':mem) :=
    @machine_step G (fst (fst c)) (snd (fst c)) (snd c)  m
                  (fst (fst c')) (snd (fst c')) (snd c')  m'.

  Definition at_external (st : MachState)
    : option (external_function * list val) := None.

  Definition after_external (ov : option val) (st : MachState) :
    option (MachState) := None.

  (*not clear what the value of halted should be*)
  (*Nick: IMO, the machine should be halted when the schedule is empty.
            The value is probably unimportant? *)
  (*Santiago: I belive empty schedule should "diverge". After all that's *)
  Definition halted (st : MachState) : option val :=
    match schedPeek (fst (fst st)) with
    | Some _ => None
    | _ => Some Vundef
    end.

  (*Lemma halted_al_schedules: forall st,
      halted st ->*)


  Definition init_machine (U:Sch) (r : option res) the_ge
             (f : val) (args : list val)
    : option MachState :=
    match init_mach r the_ge f args with
    | None => None
    | Some c => Some (U, [::], c)
    end.

  Program Definition MachineCoreSemantics (U:Sch) (r : option res):
    CoreSemantics G MachState mem.
  intros.
  apply (@Build_CoreSemantics _ MachState _
                              (fun n => init_machine U r)
                              at_external
                              after_external
                              halted
                              MachStep
        );
    unfold at_external, halted; try reflexivity.
  intros. inversion H; subst; rewrite HschedN; reflexivity.
  auto.
  Defined.

  Definition init_machine' (r : option res) the_ge
             (f : val) (args : list val)
    : option (machine_state) :=
    match init_mach r the_ge f args with
    | None => None
    | Some c => Some (c)
    end.

  (*This is not used anymore:
   * find_thread
   * running_thread *)
  Definition find_runnin (c:@ctl C): bool :=
    match c with
    | Krun _ => true
    | _ => false
    end.
  Definition running_thread: machine_state -> option nat:=
    fun st => find_thread st find_runnin.

    Definition unique_Krun tp i :=
     forall j cnti q,
       @getThreadC j tp cnti = Krun q ->
       ~ @threadHalted j tp cnti  ->
       eq_nat_dec i j.


  Program Definition new_MachineSemantics (U:Sch) (r : option res):
    @ConcurSemantics G nat Sch event_trace machine_state mem.
  apply (@Build_ConcurSemantics _ nat Sch event_trace  machine_state _
                              (init_machine' r)
                              (fun U st => halted (U, nil, st))
                              (fun ge U st m st' m' =>
                                 @internal_step ge U st m
                                                st' m'
                              )
                              (fun ge U (tr:event_trace) st m U' tr' st' m' =>
                                 @external_step ge U tr st m
                                                U' tr' st' m'
                              )
                              unique_Krun
                              (*fun A => running_thread A*))
         ;
    unfold at_external, halted; try reflexivity.
  - intros. inversion H; subst; rewrite HschedN; reflexivity.
  - intros. inversion H; subst; rewrite HschedN; reflexivity.
  Defined.

(*
  Definition MachineSemantics := MachineSemantics'.*)
  Lemma hybrid_initial_schedule: forall genv main vals U U' p c tr n,
      initial_core (MachineCoreSemantics U p) n genv main vals = Some (U',tr,c) ->
      U' = U /\ tr = nil.
        simpl. unfold init_machine. intros.
        destruct (init_mach p genv main vals); try solve[inversion H].
        inversion H; subst; split; auto.
  Qed.

  Lemma corestep_empty_trace: forall genv U tr tr' c m c' m' U',
      MachStep genv (U,tr,c) m (U', tr', c') m' ->
      tr = nil /\ tr' = nil.
  Proof.
    intros.
    inversion H; subst; simpl in *; auto.
  Qed.

  (** Schedule safety of the coarse-grained machine*)
  Inductive csafe (ge : G) (st : MachState) (m : mem) : nat -> Prop :=
  | Safe_0: csafe ge st m 0
  | HaltedSafe: forall n, halted st -> csafe ge st m n
  | CoreSafe : forall tp' m' n
                 (Hstep: MachStep ge st m (fst (fst st),[::],tp') m')
                 (Hsafe: csafe ge (fst (fst st),[::],tp') m' n),
      csafe ge st m (S n)
  | AngelSafe: forall tp' m' n
                 (Hstep: MachStep ge st m (schedSkip (fst (fst st)),[::],tp') m')
                 (Hsafe: forall U'', csafe ge (U'',[::],tp') m' n),
      csafe ge st m (S n).


  (* MachineSemantics
   * initial_schedule 
   *)
  Definition HybridMachine: HybridMachine_rec Resources Sem ThreadPool:=
     (Build_HybridMachine_rec _ _ _ MachineCoreSemantics new_MachineSemantics hybrid_initial_schedule).
    
End HybridMachine.
