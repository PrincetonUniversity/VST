Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.
Require Import concurrency.scheduler.
Require Import concurrency.concurrent_machine.
Require Import concurrency.addressFiniteMap. (*The finite maps*)
Require Import concurrency.pos.
Require Import concurrency.lksize.
Require Import concurrency.permjoin_def.
Require Import Coq.Program.Program.
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.
Require Import concurrency.threads_lemmas.
Require Import concurrency.semantics.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.permissions.
Require Import concurrency.threadPool.

Module LocksAndResources.
  (** Dry resources are a permission map for non-lock locations and one for lock
  locations*)
  Definition res := (access_map * access_map)%type.
  Definition lock_info := (access_map * access_map)%type.  
End LocksAndResources.


Module ThreadPool (SEM:Semantics)  <: ThreadPoolSig
    with Module TID:= NatTID with Module SEM:=SEM
    with Module RES := LocksAndResources.

    Include (OrdinalPool SEM LocksAndResources).
    
End ThreadPool.

Module Concur.
  
  Module mySchedule := ListScheduler NatTID.

  (** The type of dry machines. This is basically the same as
  [ConcurrentMachineSig] but resources are instantiated with dry
  resources*)
  Module Type DryMachineSig  (SEM: Semantics) <: ConcurrentMachineSig
      with Module ThreadPool.RES:= LocksAndResources
      with Module ThreadPool.TID:=mySchedule.TID.
                                     
     Declare Module Events : EventSig.
     Module ThreadPool := ThreadPool SEM.
     Import ThreadPool SEM.
     Import event_semantics Events.
     
     (** Memories*)
     Definition richMem: Type:= mem.
     Definition dryMem: richMem -> mem:= id.
     Definition diluteMem: mem -> mem := setMaxPerm.
     
     Notation thread_pool := (ThreadPool.t).

     (** The state respects the memory*)
     Record mem_compatible' tp m : Prop :=
       { compat_th :> forall {tid} (cnt: containsThread tp tid),
             permMapLt (getThreadR cnt).1 (getMaxPerm m) /\
             permMapLt (getThreadR cnt).2 (getMaxPerm m);
         compat_lp : forall l pmaps, lockRes tp l = Some pmaps ->
                                permMapLt pmaps.1 (getMaxPerm m) /\
                                permMapLt pmaps.2 (getMaxPerm m);
         lockRes_blocks: forall l rmap, lockRes tp l = Some rmap ->
                                   Mem.valid_block m l.1}.
     
     Definition mem_compatible tp m : Prop := mem_compatible' tp m.

     Record invariant' tp :=
       { no_race_thr :
           forall i j (cnti: containsThread tp i) (cntj: containsThread tp j)
             (Hneq: i <> j),
             permMapsDisjoint2 (getThreadR cnti)
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
         lockRes_valid: lr_valid (lockRes tp) (*well-formed locks*)
       }.

     Definition invariant := invariant'.
     Parameter threadStep :
       G ->
       forall tid0 (ms : t) (m : mem),
         containsThread ms tid0 ->
         mem_compatible ms m -> t -> mem -> seq mem_event -> Prop.
     
     Axiom threadStep_equal_run:
    forall g i tp m cnt cmpt tp' m' tr, 
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q').
     Parameter syncStep :
       G ->
       forall tid0 (ms : t) (m : mem),
         containsThread ms tid0 ->
         mem_compatible ms m -> t -> mem -> sync_event -> Prop.
     
  Axiom syncstep_equal_run:
    forall g i tp m cnt cmpt tp' m' tr, 
      @syncStep g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q').
  
  Axiom syncstep_not_running:
    forall g i tp m cnt cmpt tp' m' tr, 
      @syncStep g i tp m cnt cmpt tp' m' tr ->
      forall cntj q, ~ @getThreadC i tp cntj = Krun q.

     
     Parameter threadHalted :
       forall tid0 (ms : t), containsThread ms tid0 -> Prop.
     Parameter init_mach : option RES.res -> G -> val -> seq val -> option t.

     

  Axiom threadHalt_update:
    forall i j, i <> j ->
      forall tp cnt cnti c' cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j (@updThreadC i tp cnti c') cnt') .
  
  Axiom syncstep_equal_halted:
    forall g i tp m cnti cmpt tp' m' tr, 
      @syncStep g i tp m cnti cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j tp' cnt').
  
  Axiom threadStep_not_unhalts:
    forall g i tp m cnt cmpt tp' m' tr, 
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) ->
        (@threadHalted j tp' cnt') .
  
  End DryMachineSig.
  
  Module DryMachineShell (SEM:Semantics)  <: DryMachineSig SEM.
                                                           
     Module Events := Events.
     Module ThreadPool := ThreadPool SEM.
     Import ThreadPool.
     Import ThreadPool.SEM ThreadPool.RES.
     Import event_semantics Events.

     Notation tid := NatTID.tid.

     (** Memories*)
     Definition richMem: Type:= mem.
     Definition dryMem: richMem -> mem:= id.
     Definition diluteMem: mem -> mem := setMaxPerm.
     
     Notation thread_pool := (ThreadPool.t).
     
     (** The state respects the memory*)

     Record mem_compatible' tp m : Prop :=
       { compat_th :> forall {tid} (cnt: containsThread tp tid),
             permMapLt (getThreadR cnt).1 (getMaxPerm m) /\
             permMapLt (getThreadR cnt).2 (getMaxPerm m);
         compat_lp : forall l pmaps, lockRes tp l = Some pmaps ->
                                permMapLt pmaps.1 (getMaxPerm m) /\
                                permMapLt pmaps.2 (getMaxPerm m);
         lockRes_blocks: forall l rmap, lockRes tp l = Some rmap ->
                                   Mem.valid_block m l.1}.
     
     Definition mem_compatible tp m : Prop := mem_compatible' tp m.

     
     (* should there be something that says that if something is a lock then
     someone has at least readable permission on it?*)
     Record invariant' tp :=
       { no_race_thr :
           forall i j (cnti: containsThread tp i) (cntj: containsThread tp j)
             (Hneq: i <> j),
             permMapsDisjoint2 (getThreadR cnti)
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
         lockRes_valid: lr_valid (lockRes tp) (*well-formed locks*)
       }.
     Definition invariant := invariant'.
     
     (** Steps*)
     Inductive dry_step genv {tid0 tp m} (cnt: containsThread tp tid0)
               (Hcompatible: mem_compatible tp m) :
       thread_pool -> mem -> seq mem_event -> Prop :=
     | step_dry :
         forall (tp':thread_pool) c m1 m' (c' : code) ev
           (** Instal the permission's of the thread on non-lock locations*)
           (Hrestrict_pmap: restrPermMap (Hcompatible tid0 cnt).1 = m1)
           (Hinv: invariant tp)
           (Hcode: getThreadC cnt = Krun c)
           (Hcorestep: ev_step Sem genv c m1 ev c' m')
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

     Inductive ext_step (genv:G) {tid0 tp m}
               (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
       thread_pool -> mem -> sync_event -> Prop :=
     | step_acquire :
         forall (tp' tp'':thread_pool) m0 m1 c m' b ofs
           (pmap : LocksAndResources.lock_info)
           (pmap_tid' : access_map)
           (virtueThread : delta_map * delta_map),
           let newThreadPerm := (computeMap (getThreadR cnt0).1 virtueThread.1,
                                  computeMap (getThreadR cnt0).2 virtueThread.2) in
           forall
             (Hinv : invariant tp)
             (Hcode: getThreadC cnt0 = Kblocked c)
             (Hat_external: at_external Sem c = Some (LOCK, Vptr b ofs::nil))
             (** install the thread's permissions on lock locations*)
             (Hrestrict_pmap0: restrPermMap (Hcompat tid0 cnt0).2 = m0)
             (** check if the thread has permission to acquire the lock and the lock is free*)
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
         forall (tp' tp'':thread_pool) m0 m1 c m' b ofs virtueThread virtueLP pmap_tid' rmap,
           let newThreadPerm := (computeMap (getThreadR cnt0).1 virtueThread.1,
                                 computeMap (getThreadR cnt0).2 virtueThread.2) in
           forall
             (Hinv : invariant tp)
             (Hcode: getThreadC cnt0 = Kblocked c)
             (Hat_external: at_external Sem c =
                            Some (UNLOCK, Vptr b ofs::nil))
             (** install the thread's permissions on lock locations *) 
             (Hrestrict_pmap0: restrPermMap (Hcompat tid0 cnt0).2 = m0)
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
         forall (tp_upd tp':thread_pool) c b ofs arg virtue1 virtue2,
           let threadPerm' := (computeMap (getThreadR cnt0).1 virtue1.1,
                               computeMap (getThreadR cnt0).2 virtue1.2) in
           let newThreadPerm := (computeMap empty_map virtue2.1,
                                 computeMap empty_map virtue2.2) in
           forall
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c = Some (CREATE, Vptr b ofs::arg::nil))
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
             (Hat_external: at_external Sem c = Some (MKLOCK, Vptr b ofs::nil))
             (** install the thread's data permissions*)
             (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).1 = m1)
             (** lock is created in acquired state*)
             (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
             (** The thread's data permissions are set to Nonempty*)
             (Hdata_perm: setPermBlock (Some Nonempty) b (Int.intval ofs) pmap_tid.1 LKSIZE_nat = pmap_tid'.1)
             (** thread lock permission is increased *)
             (Hlock_perm: setPermBlock (Some Writable) b
                                       (Int.intval ofs) pmap_tid.2 LKSIZE_nat = pmap_tid'.2)
             (** Require that [(b, Int.intval ofs)] was not a lock*)
             (HlockRes: lockRes tp (b, Int.intval ofs) = None)
             (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
             (** the lock has no resources initially *)
             (Htp'': tp'' = updLockSet tp' (b, Int.intval ofs) (empty_map, empty_map)),
             ext_step genv cnt0 Hcompat tp'' m' (mklock (b, Int.intval ofs))
                      
     | step_freelock :
         forall  (tp' tp'': thread_pool) c b ofs pmap_tid' m1 pdata rmap,
           let: pmap_tid := getThreadR cnt0 in
           forall 
           (Hinv: invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c = Some (FREE_LOCK, Vptr b ofs::nil))
           (** If this address is a lock*)
           (His_lock: lockRes tp (b, (Int.intval ofs)) = Some rmap)
           (** And the lock is taken *)
           (Hrmap: forall b ofs, rmap.1 !! b ofs = None /\ rmap.2 !! b ofs = None)
           (** Install the thread's lock permissions*)
           (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).2 = m1)
           (** To free the lock the thread must have at least Writable on it*)
           (Hfreeable: Mem.range_perm m1 b (Int.intval ofs) ((Int.intval ofs) + LKSIZE) Cur Writable)
           (** lock permissions of the thread are dropped to empty *)
           (Hlock_perm: setPermBlock None b (Int.intval ofs) pmap_tid.2 LKSIZE_nat = pmap_tid'.2)
           (** data permissions are computed in a non-deterministic way *)
           (Hpdata: perm_order pdata Writable)
           (Hdata_perm: setPermBlock (Some pdata) b
                                     (Int.intval ofs) pmap_tid.1 LKSIZE_nat = pmap_tid'.1)
           (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
           (Htp'': tp'' = remLockSet tp' (b, Int.intval ofs)),
           ext_step genv cnt0 Hcompat  tp'' m (freelock (b, Int.intval ofs))
     | step_acqfail :
         forall  c b ofs m1
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c = Some (LOCK, Vptr b ofs::nil))
           (** Install the thread's lock permissions*)
           (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0).2 = m1)
           (** Lock is already acquired.*)
           (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero)),
           ext_step genv cnt0 Hcompat tp m (failacq (b, Int.intval ofs)).
     
     Definition threadStep (genv : G): forall {tid0 ms m},
         containsThread ms tid0 -> mem_compatible ms m ->
         thread_pool -> mem -> seq mem_event -> Prop:=
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
     
     Definition syncStep (genv :G) :
       forall {tid0 ms m},
         containsThread ms tid0 -> mem_compatible ms m ->
         thread_pool -> mem -> sync_event -> Prop:=
       @ext_step genv.


     
    
  Lemma syncstep_equal_run:
    forall g i tp m cnt cmpt tp' m' tr, 
      @syncStep g i tp m cnt cmpt tp' m' tr ->
      forall j,
        (exists cntj q, @getThreadC j tp cntj = Krun q) <->
        (exists cntj' q', @getThreadC j tp' cntj' = Krun q').
  Proof.
    intros g i tp m cnt cmpt tp' m' tr H j; split.
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
    forall g i tp m cnt cmpt tp' m' tr, 
      @syncStep g i tp m cnt cmpt tp' m' tr ->
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
           (Hinv: invariant tp)
           (Hcode: getThreadC cnt = Krun c)
           (Hcant: halted Sem c),
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
    admit.
(*    eapply updCinvariant'; assumption. *)
    erewrite <- (gsoThreadCC H); exact Hcode.
    admit.
      (* eapply updCinvariant'; eassumption. *) 
    erewrite (gsoThreadCC H); exact Hcode.
  Admitted.
  
  
     Definition one_pos : pos := mkPos NPeano.Nat.lt_0_1.
     
     Definition initial_machine pmap c :=
       ThreadPool.mk
         one_pos
         (fun _ =>  Krun c)
         (fun _ => (pmap, empty_map)) (*initially there are no locks*)
         empty_lset.

           
     Definition init_mach (pmap : option RES.res) (genv:G)
                (v:val)(args:list val):option thread_pool :=
       match initial_core Sem genv v args with
       | Some c =>      
         match pmap with
         | Some pmap => Some (initial_machine pmap.1 c)
         | None => None
         end
       | None => None
       end.

     Module DryMachineLemmas.
       
       (* Lemma updLock_raceFree: forall ds a pmap, *)
       (*   race_free ds -> *)
       (*   race_free (updLockSet ds a pmap). *)
       (* Proof. *)
       (*   unfold race_free; intros. *)
       (*   rewrite gLockSetRes. rewrite gLockSetRes. *)
       (*   apply H; assumption. *)
       (* Qed. *)

       (* Lemma remLock_raceFree: forall ds a, *)
       (*     race_free ds -> *)
       (*     race_free (remLockSet ds a). *)
       (* Proof. *)
       (*   unfold race_free; intros. *)
       (*   assert (cnti':=cntRemoveL' cnti). *)
       (*   assert (cntj':=cntRemoveL' cntj). *)
       (*   rewrite (gRemLockSetRes cnti' ). *)
       (*   erewrite (gRemLockSetRes cntj'). *)
       (*   apply H; assumption. *)
       (* Qed. *)

       (*TODO: This lemma should probably be moved. *)
       Lemma threads_canonical:
         forall ds m i (cnt:ThreadPool.containsThread ds i),
           mem_compatible ds m ->  
           isCanonical (ThreadPool.getThreadR cnt).1 /\
           isCanonical (ThreadPool.getThreadR cnt).2.
             intros.
             destruct (compat_th H cnt);
               eauto using canonical_lt.
       Qed.
       (** most of these lemmas are in DryMachinLemmas*)

       (** *Invariant Lemmas*)
      
     (*
       (** ** Updating the machine state**)
       (*Lemma updCinvariant: forall {tid} ds c (cnt: containsThread ds tid),
           invariant ds ->
           invariant (updThreadC cnt c).
             intros ? ? ? ? INV; inversion INV.
             constructor; auto.
       Qed.

       Lemma updThread_inv: forall ds i (cnt: containsThread ds i) c pmap,
           invariant ds ->
           (forall j (cnt: containsThread ds j),
               i<>j -> permMapsDisjoint pmap.1 (getThreadR cnt).1 /\
                     permMapsDisjoint pmap.2 (getThreadR cnt).2)->
           (forall l pmap0, lockRes ds l = Some pmap0 ->
                       permMapsDisjoint pmap0.1 pmap.1 /\
                       permMapsDisjoint pmap0.2 pmap.2) ->
           invariant (updThread cnt c pmap).
       Proof.
         intros ds x cnt c pmap INV A B.
         constructor.
         - intros.
           destruct (scheduler.NatTID.eq_tid_dec x i); [|destruct (scheduler.NatTID.eq_tid_dec x j)].
           + subst i.
             rewrite gssThreadRes.
             rewrite gsoThreadRes; try solve[assumption].
             assert (cntj':=cntj).
             apply cntUpdate' in cntj'.
             eapply (A); assumption.
           + subst j.
             apply permMapsDisjoint2_comm.
             rewrite gssThreadRes.
             rewrite gsoThreadRes; try solve[assumption].
             apply A; assumption.
           + rewrite gsoThreadRes; try solve[assumption].
             rewrite gsoThreadRes; try solve[assumption].
             inversion INV. apply no_race_thr0; assumption.
         -  intros.
           rewrite gsoThreadLPool in Hres1.
           rewrite gsoThreadLPool in Hres2.
           inversion INV. eapply no_race_lr0; eauto.
         - intros i laddr cnti rmap.
           rewrite gsoThreadLPool; intros Hres.
           destruct (scheduler.NatTID.eq_tid_dec x i).
           + subst x. rewrite gssThreadRes.
             apply permMapsDisjoint2_comm.
             eapply B; eassumption.
           + rewrite gsoThreadRes; auto.
             inversion INV. eapply no_race0; eassumption.
         - intros i cnti.
           destruct (scheduler.NatTID.eq_tid_dec x i).
           + subst x. rewrite gssThreadRes.

             
           + rewrite gsoThreadRes; auto.
             
           
         - intros. rewrite gsoThreadLock.
           destruct (scheduler.NatTID.eq_tid_dec x i).
           + subst x. rewrite gssThreadRes. apply B.
           + rewrite gsoThreadRes; try solve[assumption].
             inversion INV. apply lock_set_threads0.
         - intros. rewrite gsoThreadLPool in H.
           destruct (scheduler.NatTID.eq_tid_dec x i).
           + subst x. rewrite gssThreadRes. 
             apply (C _ _ H).
           + rewrite gsoThreadRes; try solve[assumption].
             inversion INV. eapply lock_res_threads; eassumption.
         - intros. rewrite gsoThreadLPool in H.
           rewrite gsoThreadLock.
           inversion INV. eapply lock_res_set0. eassumption.
         - intros.
           intros b ofs. rewrite gsoThreadLPool.
           inversion INV. eapply lockRes_valid0.
       Qed. *)

       (*
       Lemma updLock_inv: forall ds a pmap,
           invariant ds ->
           (forall i (cnt: containsThread ds i) ofs0,
               Intv.In ofs0 (snd a, ((snd a) + LKSIZE)%Z) ->
               permDisjoint (Some Writable) ((getThreadR cnt) !! (fst a) ofs0) ) ->
           (forall i (cnt : containsThread ds i),
               permMapsDisjoint pmap (getThreadR cnt)) ->
           (permMapsDisjoint (lockSet ds) pmap) ->
           (forall ofs0,
               Intv.In ofs0 (snd a, ((snd a) + LKSIZE)%Z) ->
               permDisjoint (Some Writable) (pmap !! (fst a) ofs0)) ->
           (forall l pmap0, lockRes ds l = Some pmap0 ->
                       forall ofs0,
                         Intv.In ofs0 (snd a, ((snd a) + LKSIZE)%Z) ->
                       permDisjoint (Some Writable) (pmap0 !! (fst a) ofs0))->
           (forall ofs0,
               (snd a < ofs0 < (snd a) + LKSIZE)%Z -> lockRes ds (fst a, ofs0) = None) ->
           (forall ofs : Z,
               (ofs < (snd a) < ofs + LKSIZE)%Z -> lockRes ds (fst a, ofs) = None ) ->
           invariant (updLockSet ds a pmap).
       Proof.
         intros ? ? ? INV A B C D E F G. constructor.
         - apply updLock_raceFree. inversion INV; assumption.
         - intros. rewrite gLockSetRes.
           apply permDisjoint_permMapsDisjoint; intros b0 ofs0.
           destruct a as [b ofs].
           destruct (ident_eq b b0).
           subst b0; destruct (Intv.In_dec ofs0 (ofs, ofs + LKSIZE)%Z).
           + rewrite gssLockSet; auto.
           + rewrite gsoLockSet_1; auto.
             apply permMapsDisjoint_permDisjoint.
             inversion INV; auto.
             apply Intv.range_notin in n.
             unfold LKSIZE in n; simpl in n; simpl; assumption.
             unfold LKSIZE; simpl; omega.
           + rewrite gsoLockSet_2; auto.
             apply permMapsDisjoint_permDisjoint.
             inversion INV; auto.
         - intros.
           destruct (addressFiniteMap.AMap.E.eq_dec a l).
           + subst.
             rewrite gssLockRes in H; inversion H; subst.
             rewrite gLockSetRes. apply B.
           + rewrite gsoLockRes in H; try solve[assumption].
             inversion INV. eapply lock_res_threads0. apply H.
         - intros.
           destruct (addressFiniteMap.AMap.E.eq_dec a l); destruct a as [b ofs].
           + subst.
             rewrite gsslockResUpdLock in H; inversion H. subst pmap0.
             apply permDisjoint_permMapsDisjoint; intros b0 ofs0.
             { destruct (ident_eq b b0).
               subst b; destruct (Intv.In_dec ofs0 (ofs, ofs + LKSIZE)%Z).
               + apply permDisjoint_comm; rewrite gssLockSet; auto.
               + rewrite gsoLockSet_1.
                 apply permDisjoint_comm; apply permMapsDisjoint_permDisjoint; auto.
                 eapply Intv.range_notin in n; unfold LKSIZE in n. auto.
                 simpl. unfold LKSIZE; simpl; omega.
               + rewrite gsoLockSet_2; auto.
                 apply permDisjoint_comm; apply permMapsDisjoint_permDisjoint; auto.
             }
             
           + rewrite gsolockResUpdLock in H; auto.
             apply permDisjoint_permMapsDisjoint; intros b0 ofs0.
             { destruct (ident_eq b b0).
               subst b; destruct (Intv.In_dec ofs0 (ofs, ofs + LKSIZE)%Z).
               + apply permDisjoint_comm; rewrite gssLockSet; auto.
                 eapply E; eassumption.
               + rewrite gsoLockSet_1.
                 apply permMapsDisjoint_permDisjoint; auto.
                 inversion INV. eapply lock_res_set0. eassumption. 
                 eapply Intv.range_notin in n0; unfold LKSIZE in n0; auto.
                 simpl. unfold LKSIZE; simpl; omega.
               + rewrite gsoLockSet_2; auto.
                 apply permMapsDisjoint_permDisjoint; auto.
                 inversion INV. eapply lock_res_set0. eassumption. 
             }
         - intros b ofs.
           destruct (AMap.E.eq_dec a (b,ofs)).
           + subst a. rewrite gsslockResUpdLock.
             intros ofs0 HH. rewrite gsolockResUpdLock.
             apply F0 || apply F; auto.
             intros AA. inversion AA. rewrite H0 in HH.
             destruct HH as [H1 H2]; clear - H1.
             omega.
           + rewrite gsolockResUpdLock; auto.
             inversion INV. clear - lockRes_valid0 n G.
             specialize (lockRes_valid0 b ofs).
             destruct (lockRes ds (b, ofs)) eqn:MAP; auto.
             intros ofs0 ineq.
             destruct (AMap.E.eq_dec a (b,ofs0)).
             * subst a. apply G0 in ineq || apply G in ineq.
                   rewrite ineq in MAP; inversion MAP.
             * rewrite gsolockResUpdLock; auto.
       Qed.

       (*This probaly needs more hypothesis. 
        *  *)
       Lemma remLock_inv: forall ds a,
           invariant ds ->
           invariant (remLockSet ds a).
       Proof.
         intros ? ? INV.
         constructor.
         - apply remLock_raceFree. inversion INV; assumption.
         - intros.
           apply permDisjoint_permMapsDisjoint.
           intros b ofs.
           (*
           destruct a as [a1 a2].
           destruct (ident_eq a1 b).
           (*destruct (addressFiniteMap.AMap.E.eq_dec a (b, ofs)).*)
           + subst. rewrite gsslockSet_rem.
             exists  ((getThreadR cnt) !! b ofs); reflexivity.
           + destruct a; rewrite (gsolockSet_rem _ ); try assumption.
             inversion INV. apply lock_set_threads0.
         - intros.
           destruct (addressFiniteMap.AMap.E.eq_dec a l).
           + subst a. rewrite gsslockResRemLock in H; inversion H.
           + rewrite gsolockResRemLock in H. inversion INV.
             eapply lock_res_threads0.
             eassumption. exact n.
         - intros.
           destruct (addressFiniteMap.AMap.E.eq_dec a l).
           + subst a. rewrite gsslockResRemLock in H; inversion H.
           + rewrite gsolockResRemLock in H.
             2: exact n.
             inversion INV.
             unfold permMapsDisjoint. intros b ofs.
             destruct (addressFiniteMap.AMap.E.eq_dec a (b, ofs)).
             * subst a; rewrite gsslockSet_rem;
               exists (pmap !! b ofs).
               apply perm_union_comm; reflexivity.
             * destruct a; rewrite gsolockSet_rem.
               eapply lock_res_set0. eassumption.
               assumption.*)
       Admitted.

       Lemma addThrd_inv: forall ds vf arg new_perm,
           invariant ds ->
           (forall i (Hi: containsThread ds i), permMapsDisjoint (getThreadR Hi) new_perm) ->
           (permMapsDisjoint (lockSet ds) new_perm) ->
           (forall l lmap,
               lockRes ds l = Some lmap -> permMapsDisjoint lmap new_perm) ->
           invariant (addThread ds vf arg new_perm).
       Proof.
         intros ? ? ? ? dinv AA BB CC.
         constructor.
         - intros i j cnti cntj ineq.
           assert (cnti':=cnti); assert (cntj':=cntj).
           eapply cntAdd' in cnti'.
           eapply cntAdd' in cntj'.
           destruct cnti' as [[cnti0 difi]| eqi]; destruct cntj' as [[cntj0 difj]| eqj].
           + erewrite gsoAddRes with (cntj1:= cnti0); try eassumption.
             erewrite gsoAddRes with (cntj1:= cntj0); try eassumption.
             apply no_race; assumption. 
           + subst j. erewrite gsoAddRes with (cntj0:= cnti0); try eassumption.
             erewrite gssAddRes. apply AA.
             reflexivity.
           + subst i. erewrite gsoAddRes with (cntj1:= cntj0); try eassumption.
             erewrite gssAddRes.
             apply permMapsDisjoint_comm; apply AA.
             reflexivity.
           + subst. contradict ineq; reflexivity.
         - intros.
           assert (cnt':=cnt).
           eapply cntAdd' in cnt'.
           destruct cnt' as [[cnt0 dif]| eq].
           + erewrite gsoAddRes with (cntj:= cnt0); try eassumption.
             rewrite gsoAddLock.
             apply lock_set_threads; assumption.
           + erewrite gssAddRes; try eassumption.
         - intros.
           assert (cnt':=cnt).
           eapply cntAdd' in cnt'.
           destruct cnt' as [[cnt0 dif]| eq].
           + erewrite gsoAddRes with (cntj:= cnt0); try eassumption.
             inversion dinv. eapply lock_res_threads; eassumption.
           + erewrite gssAddRes; try eassumption.
             eapply CC; eassumption.
         - intros. rewrite gsoAddLock.
           inversion dinv. eapply lock_res_set; eassumption.
         - intros b ofs; rewrite gsoAddLPool.
           inversion dinv. apply lockRes_valid0.
       Qed.

       (** *Invariant after corestep*)
       Lemma decay_disjoint:
      forall m m' p
        (Hdecay: decay m m')
        (Hlt: permMapLt p (getMaxPerm m))
        (Hdisjoint: permMapsDisjoint (getCurPerm m) p),
        permMapsDisjoint (getCurPerm m') p.
    Proof.
      intros.
      unfold permMapsDisjoint in *.
      intros.
      destruct (Hdecay b ofs) as [_ Hold].
      clear Hdecay.
      specialize (Hdisjoint b ofs).
      destruct (valid_block_dec m b) as [Hvalid | Hinvalid].
      - destruct (Hold Hvalid) as [Hfree | Heq].
        + destruct (Hfree Cur) as [_ Hm']. rewrite getCurPerm_correct.
          assert (not_racy (permission_at m' b ofs Cur))
            by (unfold permission_at; rewrite Hm'; constructor).
            by eapply not_racy_union.
        + rewrite getCurPerm_correct. unfold permission_at.
          rewrite <- Heq. rewrite getCurPerm_correct in Hdisjoint.
          unfold permission_at in Hdisjoint. assumption.
      - assert (Hnone: (p !! b ofs) = None).
        { apply Mem.nextblock_noaccess with (ofs := ofs) (k := Max) in Hinvalid.
          unfold permMapLt in Hlt.
          specialize (Hlt b ofs).
          rewrite getMaxPerm_correct in Hlt.
          unfold permission_at in Hlt.
          rewrite Hinvalid in Hlt. simpl in Hlt.
          destruct (p !! b ofs); tauto.
        }
        rewrite Hnone.
        rewrite perm_union_comm.
        eapply not_racy_union;
          by constructor.
    Qed.
       
       Opaque getThreadR.
    Lemma step_decay_invariant:
      forall (tp : thread_pool) (m : mem) (i : nat)
        (pf : containsThread tp i) c m1 m1' c'
        (Hinv: invariant tp)
        (Hcompatible: mem_compatible tp m)
        (Hrestrict_pmap :restrPermMap (Hcompatible i pf) = m1)
        (Hdecay: decay m1 m1')
        (Hcode: getThreadC pf = Krun c),
        invariant (updThread pf (Krun c') (getCurPerm m1')).
    Proof.
      intros.
      destruct Hinv as [Hrace Hlp].
      constructor.
      { (* non-interference in threads *)
        unfold race_free in *.
        intros j k.
        destruct (i == j) eqn:Heqj, (i == k) eqn:Heqk; move/eqP:Heqj=>Heqj;
          move/eqP:Heqk=>Heqk; simpl in *; intros cntj' cntk' Hneq;
                        assert (cntk: containsThread tp k)
                          by (eapply cntUpdate'; eauto);
                        assert (cntj: containsThread tp j)
                          by (eapply cntUpdate'; eauto).
        - subst j k; exfalso; auto.
        - subst j.
          erewrite gssThreadRes.
          erewrite @gsoThreadRes with (cntj := cntk); eauto.
          specialize (Hrace _ _ pf cntk Hneq).
          assert (Hlt := compat_th Hcompatible cntk).
          subst m1.
          eapply decay_disjoint; eauto.
          unfold permMapLt in *.
          intros b ofs.
          rewrite getMaxPerm_correct;
            by rewrite restrPermMap_Max.
          intros b ofs.
          rewrite getCurPerm_correct;
            by rewrite restrPermMap_Cur.
        - subst k.
          erewrite @gsoThreadRes with (cntj := cntj); auto.
          erewrite gssThreadRes.
          specialize (Hrace _ _ pf cntj Heqj).
          assert (Hlt := compat_th Hcompatible cntj).
          subst m1.
          eapply permMapsDisjoint_comm.
          eapply decay_disjoint; eauto.
          unfold permMapLt in *.
          intros b ofs.
          rewrite getMaxPerm_correct;
            by rewrite restrPermMap_Max.
          intros b ofs.
          rewrite getCurPerm_correct;
            by rewrite restrPermMap_Cur.
        - erewrite @gsoThreadRes with (cntj := cntj); auto.
          erewrite @gsoThreadRes with (cntj := cntk); auto.
      }
      { (* non-interference with lockpool*)
        intros j cntj.
        rewrite gsoThreadLock.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hik; subst.
        - erewrite gssThreadRes. apply permMapsDisjoint_comm.
          assert (Hlt := compat_ls Hcompatible).
          eapply decay_disjoint; eauto.
          intros b ofs.
          rewrite getMaxPerm_correct;
            by rewrite restrPermMap_Max.
          intros b ofs. rewrite perm_union_comm.
          rewrite getCurPerm_correct.
          rewrite restrPermMap_Cur.
            by eapply Hlp.
        - erewrite @gsoThreadRes with (cntj := cntUpdate' cntj);
            by eauto.
      }
      { intros l pmap j cntj Hres.
        rewrite gsoThreadLPool in Hres.
        destruct (i == j) eqn:Hij; move/eqP:Hij=>Hik; subst.
        - erewrite gssThreadRes. apply permMapsDisjoint_comm.
          assert (Hlt := compat_lp Hcompatible _ Hres).
          eapply decay_disjoint; eauto.
          intros b ofs.
          rewrite getMaxPerm_correct;
            by rewrite restrPermMap_Max.
          intros b ofs. rewrite perm_union_comm.
          rewrite getCurPerm_correct.
          rewrite restrPermMap_Cur;
            by (eapply lock_res_threads0; eauto).
        - erewrite @gsoThreadRes with (cntj := cntUpdate' cntj);
            by eauto.
      }
      { intros l pmap Hres.
        rewrite gsoThreadLock.
        rewrite gsoThreadLPool in Hres;
          by eauto.
      }
      { clear - lockRes_valid0.
        intros b ofs. rewrite gsoThreadLPool.
        specialize (lockRes_valid0 b ofs).
        destruct (lockRes tp (b, ofs)); try constructor.
        intros ofs0 ineq.
        rewrite gsoThreadLPool; auto.
        }
    Qed. *)
     *)    
     End DryMachineLemmas.



    (** *More Properties of halted thread*)
      Lemma threadStep_not_unhalts:
    forall g i tp m cnt cmpt tp' m' tr, 
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) ->
        (@threadHalted j tp' cnt') .
  Proof.
    intros; inversion H; inversion H0; subst.
    destruct (NatTID.eq_tid_dec i j).
    - subst j. simpl in Hcorestep.
      eapply ev_step_ax1 in Hcorestep.
      eapply corestep_not_halted in Hcorestep.
      replace cnt1 with cnt in Hcode0 by apply cnt_irr.
      rewrite Hcode0 in Hcode; inversion Hcode;
      subst c0.
      rewrite Hcorestep in Hcant; inversion Hcant.
    - econstructor; eauto.
      + admit. (* Invariant *)
      
      + rewrite gsoThreadCode; auto;
        erewrite <- age_getThreadCode; eauto.
  Admitted.

  
  Lemma syncstep_equal_halted:
    forall g i tp m cnti cmpt tp' m' tr, 
      @syncStep g i tp m cnti cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j tp' cnt').
  Proof.
    intros; split; intros HH; inversion HH; subst;
    econstructor; subst; eauto.
    - admit. (* Invariant *)
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
        { (*AQCUIRE*)
            replace cnt' with cnt0 by apply cnt_irr;
          exact Hcode. }
    - admit. (* invariant *)
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
        { (*AQCUIRE*)
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
        { (*AQCUIRE*)
            replace cnt with cnt0 by apply cnt_irr;
          exact Hcode. }
        

          
          Grab Existential Variables.
          eauto. eauto. eauto. eauto. eauto. eauto.
          eauto. eauto. eauto. eauto. eauto. eauto.
          eauto. eauto. eauto.
  Admitted.

  End DryMachineShell.
  
End Concur.
