Require Import compcert.lib.Axioms.

Add LoadPath "../concurrency" as concurrency.

Require Import sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.
Require Import concurrency.concurrent_machine.
Require Import concurrency.threads_lemmas.
Require Import Coq.Program.Program.
Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

(*From msl get the juice! *)
Require Import msl.rmaps.
Require Import veric.compcert_rmaps.
Require Import veric.juicy_mem.
Require Import veric.juicy_extspec.
Require Import veric.jstep.

(*The finite maps*)
Require Import addressFiniteMap.


(**)
Require Import veric.res_predicates. (*For the precondition of lock make and free*)

Notation EXIT := 
  (EF_external "EXIT" (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG :=
  (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default).
Notation CREATE := (EF_external "CREATE" CREATE_SIG).

Notation READ := 
  (EF_external "READ" (mksignature (AST.Tint::AST.Tint::AST.Tint::nil)
                                   (Some AST.Tint) cc_default)).
Notation WRITE := 
  (EF_external "WRITE" (mksignature (AST.Tint::AST.Tint::AST.Tint::nil)
                                    (Some AST.Tint) cc_default)).

Notation MKLOCK := 
  (EF_external "MKLOCK" (mksignature (AST.Tint::nil)
                                     (Some AST.Tint) cc_default)).
Notation FREE_LOCK := 
  (EF_external "FREE_LOCK" (mksignature (AST.Tint::nil)
                                        (Some AST.Tint) cc_default)).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation LOCK := (EF_external "LOCK" LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation UNLOCK := (EF_external "UNLOCK" UNLOCK_SIG).

Definition LKCHUNK:= Mint32.
Definition LKSIZE:= align_chunk LKCHUNK.

Require Import (*compcert_linking*) concurrency.permissions concurrency.threadPool.

(* There are some overlaping definition conflicting. 
   Here we fix that. But this is obviously ugly and
   the conflicts should be removed by renaming!     *)
Notation "x <= y" := (x <= y)%nat. 
Notation "x < y" := (x < y)%nat.


Module LockPool.
  (* The lock set is a Finite Map:
     Address -> option option rmap
     Where the first option stands for the address being a lock
     and the second for the lock being locked/unlocked *)
  Definition LockPool:= address -> option (option rmap).
  Notation SSome x:= (Some (Some x)).
  Notation SNone:= (Some None).
End LockPool.
Export LockPool.

Module Res.
  Definition res := rmap.
  Definition LockPool := AMap.t (option rmap).
End Res.

Module ThreadPool (SEM:Semantics) <: ThreadPoolSig
    with Module TID:= NatTID with Module SEM:=SEM
    with Module RES:= Res.
  Include (OrdinalPool SEM Res).
  
  (** The Lock Resources Set *)
  
  Definition lock_set t: LockPool:= (AMap.find (elt:=option rmap))^~ (lockSet t).

  Definition is_lock t:= fun loc => AMap.mem loc (lset t).

  (*Add/Update lock: Notice that adding and updating are the same, depending wether then
    lock was already there. *)
  Definition addLock tp loc (res: option Res.res):=
  mk (num_threads tp)
     (pool tp)
     (perm_maps tp)
     (AMap.add loc res (lset tp)).
  (*Remove Lock*)
  Definition remLock tp loc:=
  mk (num_threads tp)
     (pool tp)
     (perm_maps tp)
     (AMap.remove loc (lset tp)).
   
End ThreadPool.

Module JMem.
  
  Parameter get_fun_spec: juicy_mem -> address -> val -> option (pred rmap * pred rmap).
  Parameter get_lock_inv: juicy_mem -> address -> option (pred rmap).
  
End JMem.

Module Concur.

  
  Module mySchedule := ListScheduler NatTID.
  
  (** Semantics of the coarse-grained juicy concurrent machine*)
  Module JuicyMachineShell (SEM:Semantics)  <: ConcurrentMachineSig
      with Module ThreadPool.TID:=mySchedule.TID
      with Module ThreadPool.SEM:= SEM
      with Module ThreadPool.RES := Res.

    Module ThreadPool := ThreadPool SEM.
    Import ThreadPool.
    Import ThreadPool.SEM.
    Notation tid := NatTID.tid.                  

    (** Memories*)
    Parameter level: nat.
    Definition richMem: Type:= juicy_mem.
    Definition dryMem: richMem -> mem:= m_dry.
    Definition diluteMem: mem -> mem := fun x => x.
    
    (** Environment and Threadwise semantics *)
    (* This all comes from the SEM. *)
    (*Parameter G : Type.
    Parameter Sem : CoreSemantics G code mem.*)
    Notation the_sem := Sem.
    
    (*thread pool*)
    Import ThreadPool.  
    Notation thread_pool := (ThreadPool.t).  
    
    (** Machine Variables*)
    Definition lp_id : tid:= (0)%nat. (*lock pool thread id*)
    
    (** Invariants*)
    (** The state respects the memory*)
    Definition access_cohere' m phi:= forall loc,
      Mem.perm_order'' (max_access_at m loc) (perm_of_res (phi @ loc)).
    Record mem_cohere' m phi :=
      { cont_coh: contents_cohere m phi;
        (*acc_coh: access_cohere m phi;*)
        acc_coh: access_cohere' m phi;
        max_coh: max_access_cohere m phi;
        all_coh: alloc_cohere m phi
      }.
    Definition mem_thcohere tp m :=
      forall {tid} (cnt: containsThread tp tid), mem_cohere' m (getThreadR cnt). 
    Definition mem_lock_cohere (ls:LockPool) m:=
      forall loc rm, ls loc = SSome rm -> mem_cohere' m rm.

    (*Join juice from all threads *)
    Definition getThreadsR tp:=
      map (perm_maps tp) (enum ('I_(num_threads tp))).
    Fixpoint join_list (ls: seq.seq Res.res) r:=
      if ls is phi::ls' then exists r', join phi r' r /\ join_list ls' r' else
        app_pred emp r.  (*Or is is just [amp r]?*)
    Definition join_threads tp r:= join_list (getThreadsR tp) r.

    (*Join juice from all locks*)
    Fixpoint join_list' (ls: seq.seq (option Res.res)) (r:option Res.res):=
      if ls is phi::ls' then exists (r':option Res.res),
          @join _ (@Join_lower Res.res _) phi r' r /\ join_list' ls' r' else r=None.
    Definition join_locks tp r:= join_list' (map snd (AMap.elements (lset tp))) r.

    (*Join all the juices*)
    Inductive join_all: t -> Res.res -> Prop:=
      AllJuice tp r0 r1 r:
        join_threads tp r0 ->
        join_locks tp r1 ->
        join (Some r0) r1 (Some r) ->
        join_all tp r.

    Definition locks_correct (lset : Res.LockPool) (juice: rmap):=
      forall loc sh psh P z, juice @ loc = YES sh psh (LK z) P  ->  AMap.find loc lset. 
    
    Record mem_compatible' tp m: Prop :=
      {   all_juice  : Res.res
        ; juice_join : join_all tp all_juice
        ; all_cohere : mem_cohere' m all_juice
        ; loc_set_ok : locks_correct (lockSet tp) all_juice
      }.

    Definition mem_compatible: thread_pool -> mem -> Prop:=
      mem_compatible'.

    Lemma thread_mem_compatible: forall tp m,
        mem_compatible tp m ->
        mem_thcohere tp m.
    Admitted.

    Lemma lock_mem_compatible: forall tp m,
        mem_compatible tp m ->
        mem_lock_cohere (lock_set tp) m.
    Admitted.
    (** There is no inteference in the thread pool *)
    (* Per-thread disjointness definition*)
    Definition disjoint_threads tp :=
      forall i j (cnti : containsThread tp i)
        (cntj: containsThread tp j) (Hneq: i <> j),
        joins (getThreadR cnti)
              (getThreadR cntj).
    (* Per-lock disjointness definition*)
    Definition disjoint_locks tp :=
      forall loc1 loc2 r1 r2,
        lock_set tp loc1 = SSome r1 ->
        lock_set tp loc2 = SSome r2 ->
        joins r1 r2.
    (* lock-thread disjointness definition*)
    Definition disjoint_lock_thread tp :=
      forall i loc r (cnti : containsThread tp i),
        lock_set tp loc = SSome r ->
        joins (getThreadR cnti)r.
    
    Record invariant' (tp:t) := True. (* The invariant has been absorbed my mem_compat*)
     (* { no_race : disjoint_threads tp
      }.*)

    Definition invariant := invariant'.

    (*Lemmas to retrive the ex-invariant properties from the mem-compat*)
    Lemma disjoint_threads_compat': forall tp all_juice,
        join_all tp all_juice ->
        disjoint_threads tp.
    Admitted.
    Lemma disjoint_threads_compat: forall tp m
        (mc: mem_compatible tp m),
        disjoint_threads tp.
    Proof. intros ? ? mc ; inversion mc.
           eapply disjoint_threads_compat'; eassumption.
    Qed.
    Lemma disjoint_locks_compat:  forall tp m
        (mc: mem_compatible tp m),
        disjoint_locks tp.
    Admitted.
    Lemma disjoint_locks_t_hread_compat:  forall tp m
        (mc: mem_compatible tp m),
        disjoint_lock_thread tp.
    Admitted.
    
    (** Steps*)

    (* What follows is the lemmas needed to construct a "personal" memory
       That is a memory with the juice and Cur of a particular thread. *)
    
    Definition mapmap {A B} (def:B) (f:positive -> A -> B) (m:PMap.t A): PMap.t B:=
      (def, PTree.map f m#2).
    (* You need the memory, to make a finite tree. *)
    Definition juice2Perm (phi:rmap)(m:mem): access_map:=
      mapmap (fun _ => None) (fun block _ => fun ofs => perm_of_res (phi @ (block, ofs)) ) (getCurPerm m).
    Lemma juice2Perm_canon: forall phi m, isCanonical (juice2Perm phi m).
          Proof. unfold isCanonical; reflexivity. Qed.
    Lemma juice2Perm_nogrow: forall phi m b ofs,
        Mem.perm_order'' (perm_of_res (phi @ (b, ofs)))
                         ((juice2Perm phi m) !! b ofs).
    Proof.
      intros. unfold juice2Perm, mapmap, PMap.get.
      rewrite PTree.gmap.
      destruct (((getCurPerm m)#2) ! b) eqn: inBounds; simpl.
      - destruct ((perm_of_res (phi @ (b, ofs)))) eqn:AA; rewrite AA; simpl; try reflexivity.
        apply perm_refl.
      - unfold Mem.perm_order''.
        destruct (perm_of_res (phi @ (b, ofs))); trivial.
    Qed.
    Lemma juice2Perm_cohere: forall phi m,
        access_cohere' m phi ->
        permMapLt (juice2Perm phi m) (getMaxPerm m).
    Proof.
      unfold permMapLt; intros.
      rewrite getMaxPerm_correct; unfold permission_at.
      eapply (po_trans _ (perm_of_res (phi @ (b, ofs))) _) .
      - specialize (H (b, ofs)); simpl in H. apply H. unfold max_access_at in H.
      - apply juice2Perm_nogrow.
    Qed.
    
    Definition juicyRestrict {phi:rmap}{m:Mem.mem}(coh:access_cohere' m phi): Mem.mem:=
      restrPermMap (juice2Perm_cohere coh).
    Lemma juicyRestrictContents: forall phi m (coh:access_cohere' m phi),
        forall loc, contents_at m loc = contents_at (juicyRestrict coh) loc.
    Proof. unfold juicyRestrict; intros. rewrite restrPermMap_contents; reflexivity. Qed.
    Lemma juicyRestrictMax: forall phi m (coh:access_cohere' m phi),
        forall loc, max_access_at m loc = max_access_at (juicyRestrict coh) loc.
    Proof. unfold juicyRestrict; intros. rewrite restrPermMap_max; reflexivity. Qed.
    Lemma juicyRestrictNextblock: forall phi m (coh:access_cohere' m phi),
        Mem.nextblock m = Mem.nextblock (juicyRestrict coh).
    Proof. unfold juicyRestrict; intros. rewrite restrPermMap_nextblock; reflexivity. Qed.
    Lemma juicyRestrictContentCoh: forall phi m (coh:access_cohere' m phi) (ccoh:contents_cohere m phi),
        contents_cohere (juicyRestrict coh) phi.
    Proof.
      unfold contents_cohere; intros. rewrite <- juicyRestrictContents.
      eapply ccoh; eauto.
    Qed.
    Lemma juicyRestrictMaxCoh: forall phi m (coh:access_cohere' m phi) (ccoh:max_access_cohere m phi),
        max_access_cohere (juicyRestrict coh) phi.
    Proof.
      unfold max_access_cohere; intros.
      repeat rewrite <- juicyRestrictMax.
      repeat rewrite <- juicyRestrictNextblock.
      apply ccoh.
    Qed.
    Lemma juicyRestrictAllocCoh: forall phi m (coh:access_cohere' m phi) (ccoh:alloc_cohere m phi),
        alloc_cohere (juicyRestrict coh) phi.
    Proof.
      unfold alloc_cohere; intros.
      rewrite <- juicyRestrictNextblock in H.
      apply ccoh; assumption.
    Qed.

    Lemma restrPermMap_correct :
    forall p' m (Hlt: permMapLt p' (getMaxPerm m))
      b ofs,
      permission_at (restrPermMap Hlt) b ofs Max =
      Maps.PMap.get b (getMaxPerm m) ofs /\
      permission_at (restrPermMap Hlt) b ofs Cur =
      Maps.PMap.get b p' ofs.
    Proof. admit. Qed.

    Lemma juicyRestrictCurEq:
      forall (phi : rmap) (m : mem) (coh : access_cohere' m phi)
     (loc : Address.address),
        (access_at (juicyRestrict coh) loc) = (perm_of_res (phi @ loc)).
    Proof.
      intros. unfold juicyRestrict.
      unfold access_at.
      destruct (restrPermMap_correct (juice2Perm_cohere coh) loc#1 loc#2) as [MAX CUR].
      unfold permission_at in *.
      rewrite CUR.
      unfold juice2Perm.
      unfold mapmap. 
      unfold PMap.get.
      rewrite PTree.gmap; simpl.
      destruct ((PTree.map1
             (fun f : Z -> perm_kind -> option permission => f^~ Cur)
             (Mem.mem_access m)#2) ! (loc#1)) as [VALUE|]  eqn:THING.
      - destruct loc; simpl.
        destruct ((perm_of_res (phi @ (b, z)))) eqn:HH; rewrite HH; reflexivity. 
      - simpl. rewrite PTree.gmap1 in THING.
        destruct (((Mem.mem_access m)#2) ! (loc#1)) eqn:HHH; simpl in THING; try solve[inversion THING].
        unfold access_cohere' in coh.
        unfold max_access_at in coh. unfold PMap.get in coh.
        generalize (coh loc).
        rewrite HHH; simpl.
        Lemma Mem_canonical_useful: forall m loc k, (Mem.mem_access m)#1 loc k = None.
        Admitted.
        rewrite Mem_canonical_useful.
        destruct (perm_of_res (phi @ loc)); auto.
        intro H; inversion H.
    Qed.
    
    Lemma juicyRestrictAccCoh: forall phi m (coh:access_cohere' m phi),
        access_cohere (juicyRestrict coh) phi.
    Proof.
      unfold access_cohere; intros.
      rewrite juicyRestrictCurEq.
      destruct ((perm_of_res (phi @ loc))) eqn:HH; try rewrite HH; simpl; [apply perm_refl | trivial].
    Qed.

    (* PERSONAL MEM: Is the contents of the global memory, 
       with the juice of a single thread and the Cur that corresponds to that juice.*)
    Definition personal_mem' {phi m}
               (acoh: access_cohere' m phi)
               (ccoh:contents_cohere m phi)
               (macoh: max_access_cohere m phi)
               (alcoh: alloc_cohere m phi) : juicy_mem :=
      mkJuicyMem _ _ (juicyRestrictContentCoh acoh ccoh)
                   (juicyRestrictAccCoh acoh) 
                   (juicyRestrictMaxCoh acoh macoh)
                   (juicyRestrictAllocCoh acoh alcoh).

    Definition personal_mem {tid js m}(cnt: containsThread js tid)(Hcompatible: mem_compatible js m): juicy_mem:=
      let cohere:= (thread_mem_compatible Hcompatible cnt) in
      personal_mem' (acc_coh cohere) (cont_coh cohere) (max_coh cohere) (all_coh cohere).
    
    Definition juicy_sem := (FSem.F _ _ JuicyFSem.t) _ _ the_sem.
    (* Definition juicy_step := (FSem.step _ _ JuicyFSem.t) _ _ the_sem. *)
    
    Inductive juicy_step genv {tid0 tp m} (cnt: containsThread tp tid0)
      (Hcompatible: mem_compatible tp m) : thread_pool -> mem  -> Prop :=
    | step_juicy :
        forall (tp':thread_pool) c jm jm' m' (c' : code),
          forall (Hpersonal_perm:
               personal_mem cnt Hcompatible = jm)
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt = Krun c)
            (Hcorestep: corestep juicy_sem genv c jm c' jm')
            (Htp': tp' = updThread cnt (Krun c') (m_phi jm'))
            (Hm': m_dry jm' = m'),
            juicy_step genv cnt Hcompatible tp' m'.

    Definition pack_res_inv R:= SomeP ([unit:Type])  (fun _ => R) .

    Notation Kstop := (concurrent_machine.Kstop).
    Inductive syncStep' genv {tid0 tp m}
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> Prop :=
    | step_acquire :
        forall (tp' tp'':thread_pool) jm c m1 jm' b ofs d_phi psh phi,
          (*let: phi := m_phi jm in*)
          let: phi' := m_phi jm' in
          let: m' := m_dry jm' in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (*Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm*)
            (Hpersonal_juice: getThreadR cnt0 = phi)
            (sh:Share.t)(R:pred rmap)
            (HJcanwrite: phi@(b, Int.intval ofs) = YES sh psh (LK LKSIZE) (pack_res_inv R))
            (Hrestrict_pmap:
               makeCurMax m = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.one))
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
            (His_unlocked:lock_set tp (b, Int.intval ofs) = SSome d_phi )
            (Hadd_lock_res: join (m_phi jm) d_phi  phi')  
            (Htp': tp' = updThread cnt0 (Kresume c) phi')
            (Htp'': tp'' = addLock tp' (b, Int.intval ofs) None),
            syncStep' genv cnt0 Hcompat tp'' m'                 
    | step_release :
        forall  (tp' tp'':thread_pool) jm c m1 jm' b ofs psh (d_phi phi':rmap) (R: pred rmap) ,
          let: phi := m_phi jm in
          let: phi' := m_phi jm' in
          let: m' := m_dry jm' in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (UNLOCK, ef_sig UNLOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (sh:Share.t)(R:pred rmap)
            (HJcanwrite: phi@(b, Int.intval ofs) = YES sh psh (LK LKSIZE) (pack_res_inv R))
            (Hrestrict_pmap:
               makeCurMax m = m1)
            (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero))
            (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.one) = Some m')
            (* what does the return value denote?*)
            (Hget_lock_inv: JMem.get_lock_inv jm (b, Int.intval ofs) = Some R)
            (Hsat_lock_inv: R d_phi)
            (Hrem_lock_res: join d_phi phi' (m_phi jm))
            (Htp': tp' = updThread cnt0 (Kresume c) phi')
            (Htp'': tp'' = addLock tp' (b, Int.intval ofs) (Some d_phi) ),
            syncStep' genv cnt0 Hcompat tp'' m'          
    | step_create :
        (* HAVE TO REVIEW THIS STEP LOOKING INTO THE ORACULAR SEMANTICS*)
        forall  (tp_upd tp':thread_pool) c c_new vf arg jm (d_phi phi': rmap) b ofs P Q,
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (CREATE, ef_sig CREATE, vf::arg::nil))
            (Hinitial: initial_core the_sem genv vf (arg::nil) = Some c_new)
            (Hfun_sepc: vf = Vptr b ofs)
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (Hget_fun_spec: JMem.get_fun_spec jm (b, Int.intval ofs) arg = Some (P,Q))
            (Hsat_fun_spec: P d_phi)
            (Hrem_fun_res: join d_phi phi' (m_phi jm))
            (Htp': tp_upd = updThread cnt0 (Kresume c) phi')
            (Htp'': tp' = addThread tp_upd c_new d_phi),
            syncStep' genv cnt0 Hcompat tp' m
                     
    | step_mklock :
        forall  (tp' tp'': thread_pool) jm jm' c b ofs R ,
          let: phi := m_phi jm in
          let: phi' := m_phi jm' in
          let: m' := m_dry jm' in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (MKLOCK, ef_sig MKLOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (*This the first share of the lock, 
              can/should this be different for each location? *)
            (sh:Share.t)
            (*Check I have the right permission to mklock and the riht value (i.e. 0) *)
            (Haccess: address_mapsto LKCHUNK (Vint Int.zero) sh Share.top (b, Int.intval ofs) phi)
            (*Check the new memory has the lock*)
            (Hlock: phi'@ (b, Int.intval ofs) = YES sh pfullshare (LK LKSIZE) (pack_res_inv R))
            (*Check the new memory has the right continuations THIS IS REDUNDANT! *)
            (*Hcont: forall i, 0<i<LKSIZE ->   phi'@ (b, Int.intval ofs + i) = YES sh pfullshare (CT i) NoneP*)
            (*Check the two memories coincide in everything else *)
            (Hj_forward: forall loc, loc#1 <> b \/ ~0<loc#2-(Int.size ofs)<LKSIZE  -> phi@loc = phi'@loc)
            (*Check the memories are equal!*)
            (Hm_forward: m = m')
            (Htp': tp' = updThread cnt0 (Kresume c) phi')
            (Htp'': tp'' = addLock tp' (b, Int.intval ofs) None),
            syncStep' genv cnt0 Hcompat tp'' m' 
    | step_freelock :
        forall  (tp' tp'': thread_pool) c b ofs jm jm' m1 R,
          let: phi := m_phi jm in
          let: phi' := m_phi jm' in
          let: m' := m_dry jm' in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (FREE_LOCK, ef_sig FREE_LOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (*This the first share of the lock, 
              can/should this be different for each location? *)
            (sh:Share.t)
            (*Check the new memoryI have has the right permission to mklock and the riht value (i.e. 0) *)
            (Haccess: address_mapsto LKCHUNK (Vint Int.zero) sh Share.top (b, Int.intval ofs) phi')
            (*Check the old memory has the lock*)
            (Hlock: phi@ (b, Int.intval ofs) = YES sh pfullshare (LK LKSIZE) (pack_res_inv R))
            (*Check the old memory has the right continuations  THIS IS REDUNDANT!*)
            (*Hcont: forall i, 0<i<LKSIZE ->   phi@ (b, Int.intval ofs + i) = YES sh pfullshare (CT i) NoneP *)
            (*Check the two memories coincide in everything else *)
            (Hj_forward: forall loc, loc#1 <> b \/ ~0<loc#2-(Int.size ofs)<LKSIZE  -> phi@loc = phi'@loc)
            (*Check the memories are equal!*)
            (Hm_forward:
               makeCurMax m = m1)
            (Htp': tp' = updThread cnt0 (Kresume c) (m_phi jm'))
            (Htp': tp'' = remLock tp' (b, Int.intval ofs)),
            syncStep' genv cnt0 Hcompat  tp'' (m_dry jm')  (* m_dry jm' = m_dry jm = m *)
                     
    | step_acqfail :
        forall  c b ofs jm psh,
          let: phi := m_phi jm in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (sh:Share.t)(R:pred rmap)
            (HJcanwrite: phi@(b, Int.intval ofs) = YES sh psh (LK LKSIZE) (pack_res_inv R))
            (Hload: Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.zero)),
            syncStep' genv cnt0 Hcompat tp m.
    
    Definition threadStep (genv:G): forall {tid0 ms m},
                                 containsThread ms tid0 -> mem_compatible ms m ->
                                 thread_pool -> mem -> Prop:=
      @juicy_step genv.
    
    
    Definition syncStep (genv:G):
      forall {tid0 ms m}, containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> Prop:=
      @syncStep' genv.
    
    Inductive threadHalted': forall {tid0 ms},
                               containsThread ms tid0 -> Prop:=
    | thread_halted':
        forall tp c tid0
          (cnt: containsThread tp tid0),
          forall
            (Hthread: getThreadC cnt = Krun c)
            (Hcant: halted the_sem c),
            threadHalted' cnt. 
    Definition threadHalted: forall {tid0 ms},
                               containsThread ms tid0 -> Prop:= @threadHalted'.


    (* The initial machine has to be redefined.
       Right now its build by default with empty maps,
       but it should be built with the correct juice,
       corresponding to global variables, arguments
       and function specs. *)

    Lemma onePos: (0<1)%coq_nat. auto. Qed.
    Definition initial_machine c:=
      mk (mkPos onePos) (fun _ => (Kresume c)) (fun _ => empty_rmap level) (AMap.empty (option Res.res)).
    
    Definition init_mach (genv:G)(v:val)(args:list val) : option thread_pool:=
      match initial_core the_sem genv v args with
      | Some c => Some (initial_machine  c)
      | None => None
      end.
      
  End JuicyMachineShell.
  
  (*
This is how you would instantiate a module (though it might be out of date

Declare Module SEM:Semantics.
  Module JuicyMachine:= JuicyMachineShell SEM.
  Module myCoarseSemantics :=
    CoarseMachine mySchedule JuicyMachine.
  Definition coarse_semantics:=
    myCoarseSemantics.MachineSemantics.*)
  
End Concur.
