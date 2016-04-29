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

Require Import (*compcert_linking*) concurrency.permissions.

(* There are some overlaping definition conflicting. 
   Here we fix that. But this is obviously ugly and
   the conflicts should be removed by renaming!     *)
Notation "x <= y" := (x <= y)%nat. 
Notation "x < y" := (x < y)%nat.


Module LockPool.
  Definition LockPool:= address -> option rmap.
End LockPool.
Export LockPool.

Module ThreadPool (SEM:Semantics) <: ThreadPoolSig
                                        with Module TID:= NatTID with Module SEM:=SEM.
  Module TID:=NatTID.
  Module SEM:=SEM.
  Import TID SEM.
  
  Notation code:=C.
  Definition res := rmap.
  
  Definition LockPool := LockPool.
  
  Record t' := mk
                 { num_threads : pos
                   ; pool :> 'I_num_threads -> @ctl code
                   ; perm_maps : 'I_num_threads -> res
                   ; lpool : LockPool
                 }.
  
  Definition t := t'.
  
  Definition containsThread (tp : t) (i : NatTID.tid) : Prop:=
    i < num_threads tp.

  Definition getThreadC {i tp} (cnt: containsThread tp i) : ctl :=
    tp (Ordinal cnt).
  
  Definition getThreadR {i tp} (cnt: containsThread tp i) : res :=
    (perm_maps tp) (Ordinal cnt).

  Definition addThread (tp : t) (c : code) (pmap : res) : t :=
    let: new_num_threads := pos_incr (num_threads tp) in
    let: new_tid := ordinal_pos_incr (num_threads tp) in
    mk new_num_threads
        (fun (n : 'I_new_num_threads) => 
           match unlift new_tid n with
           | None => Kresume c (*Could be a new state Kinit?? *)
           | Some n' => tp n'
           end)
        (fun (n : 'I_new_num_threads) => 
           match unlift new_tid n with
           | None => pmap
           | Some n' => (perm_maps tp) n'
           end)
        ((lpool tp)).
  
  Definition updThreadC {tid tp} (cnt: containsThread tp tid) (c' : ctl) : t :=
    mk (num_threads tp)
       (fun n => if n == (Ordinal cnt) then c' else (pool tp)  n)
       (perm_maps tp) (lpool tp).

  Definition updThreadR {tid tp} (cnt: containsThread tp tid)
             (pmap' : res) : t :=
    mk (num_threads tp) (pool tp)
       (fun n =>
          if n == (Ordinal cnt) then pmap' else (perm_maps tp) n) (lpool tp).

  Definition updThread {tid tp} (cnt: containsThread tp tid) (c' : ctl)
             (pmap : res) : t :=
    mk (num_threads tp)
       (fun n =>
          if n == (Ordinal cnt) then c' else tp n)
       (fun n =>
          if n == (Ordinal cnt) then pmap else (perm_maps tp) n) (lpool tp).

  Lemma gssThreadCode {tid tp} (cnt: containsThread tp tid) c' p'
        (cnt': containsThread (updThread cnt c' p') tid) :
    getThreadC cnt' = c'.
  Proof.
    simpl.
    rewrite threads_lemmas.if_true; auto.
    unfold updThread, containsThread in *. simpl in *.
    apply/eqP. apply f_equal.
    apply proof_irr.
  Qed.

  Lemma gssThreadRes {tid tp} (cnt: containsThread tp tid) c' p'
        (cnt': containsThread (updThread cnt c' p') tid) :
    getThreadR cnt' = p'.
  Proof.
    simpl. rewrite threads_lemmas.if_true; auto.
    unfold updThread, containsThread in *. simpl in *.
    apply/eqP. apply f_equal.
    apply proof_irr.
  Qed.

  Lemma gssThreadCC {tid tp} (cnt: containsThread tp tid) c'
        (cnt': containsThread (updThreadC cnt c') tid) :
    getThreadC cnt' = c'.
  Proof.
    simpl. rewrite threads_lemmas.if_true; auto.
    unfold updThreadC, containsThread in *. simpl in *.
    apply/eqP. apply f_equal.
    apply proof_irr.
  Qed.

  Lemma gssThreadCR {tid tp} (cnt: containsThread tp tid) c'
        (cnt': containsThread (updThreadC cnt c') tid) :
    getThreadR cnt = getThreadR cnt'.
  Proof.
    simpl.
    unfold getThreadR. 
    unfold updThreadC, containsThread in *. simpl in *.
    do 2 apply f_equal.
    apply proof_irr.
  Qed.
  
End ThreadPool.


Module JMem.
  
  Parameter get_fun_spec: juicy_mem -> address -> val -> option (pred rmap * pred rmap).
  Parameter get_lock_inv: juicy_mem -> address -> option (pred rmap).
  
End JMem.

Module Concur.

  
  Module mySchedule := ListScheduler NatTID.
  
  (** Semantics of the coarse-grained juicy concurrent machine*)
  Module JuicyMachineSig  <: ConcurrentMachineSig with Module ThreadPool.TID:=mySchedule.TID.

    Declare Module SEM:Semantics.
    Module ThreadPool := ThreadPool SEM.
    Import ThreadPool.
    Import ThreadPool.SEM.
    Notation tid := NatTID.tid.                  

    (** Memories*)
    Parameter level: nat.
    Definition richMem: Type:= juicy_mem.
    Definition dryMem: richMem -> mem:= m_dry.
    
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
    Definition mem_cohere tp m :=
      forall {tid} (cnt: containsThread tp tid), mem_cohere' m (getThreadR cnt). 
    
    Record mem_compatible' tp m :=
      { perm_comp: mem_cohere tp m
                              (* ; mem_canonical: isCanonical (getMaxPerm m) *)
      }.
    
    Definition mem_compatible: thread_pool -> mem -> Prop:=
      mem_compatible'.

    (** There is no inteference in the thread pool *)
    (* Per-thread disjointness definition*)
    Definition race_free tp :=
      forall i j (cnti : containsThread tp i)
        (cntj: containsThread tp j) (Hneq: i <> j),
        joins (getThreadR cnti)
              (getThreadR cntj).

    Record invariant' tp :=
      { (*canonical : forall tid, isCanonical (juice tp tid);*)
        no_race : race_free tp;
        lock_pool : forall (cnt : containsThread tp 0%nat), exists c,
              getThreadC cnt  = Krun c /\ halted the_sem c
      }.

    Definition invariant := invariant'.
    
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
      let cohere:= (perm_comp Hcompatible cnt) in
      personal_mem' (acc_coh cohere) (cont_coh cohere) (max_coh cohere) (all_coh cohere).
    
    Definition juicy_sem := (FSem.F _ _ JuicyFSem.t) _ _ the_sem.
    (* Definition juicy_step := (FSem.step _ _ JuicyFSem.t) _ _ the_sem. *)
    
    Inductive juicy_step genv {tid0 tp m} (cnt: containsThread tp tid0)
      (Hcompatible: mem_compatible tp m) : thread_pool -> mem  -> Prop :=
    | step_juicy :
        forall (tp':thread_pool) c jm jm' m' (c' : code),
          let: lp := lpool tp in
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
    Inductive conc_step genv {tid0 tp m}
              (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
      thread_pool -> mem -> Prop :=
    | step_lock :
        forall (tp':thread_pool) jm c c' jm' b ofs d_phi,
          let: phi := m_phi jm in
          let: phi' := m_phi jm' in
          let: m' := m_dry jm' in
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (sh:Share.t)(R:pred rmap)
            (HJcanwrite: phi@(b, Int.intval ofs) = YES sh pfullshare (LK LKSIZE) (pack_res_inv R))
            (Hload: Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.one))
            (Hstore: Mem.store Mint32 m b (Int.intval ofs) (Vint Int.zero) = Some m')
            (Hat_external: after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (His_unlocked:lpool tp (b, Int.intval ofs) = Some d_phi )
            (Hadd_lock_res: join (m_phi jm) d_phi  phi')  
            (Htp': tp' = updThread cnt0 (Kresume c') phi'),
            conc_step genv cnt0 Hcompat tp' m'                 
    | step_unlock :
        forall  (tp':thread_pool) jm c c' jm' b ofs (d_phi phi':rmap) (R: pred rmap) ,
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
            (HJcanwrite: phi@(b, Int.intval ofs) = YES sh pfullshare (LK LKSIZE) (pack_res_inv R))
            (Hload: Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.zero))
            (Hstore: Mem.store Mint32 m b (Int.intval ofs) (Vint Int.one) = Some m')
            (* what does the return value denote?*)
            (Hat_external: after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (Hget_lock_inv: JMem.get_lock_inv jm (b, Int.intval ofs) = Some R)
            (Hsat_lock_inv: R d_phi)
            (Hrem_lock_res: join d_phi phi' (m_phi jm))
            (Htp': tp' = updThread cnt0 (Kresume c') phi'),
            conc_step genv cnt0 Hcompat tp' m'          
    | step_create :
        (* HAVE TO REVIEW THIS STEP LOOKING INTO THE ORACULAR SEMANTICS*)
        forall  (tp_upd tp':thread_pool) c c' c_new vf arg jm (d_phi phi': rmap) b ofs P Q,
          forall
            (Hinv : invariant tp)
            (Hthread: getThreadC cnt0 = Kstop c)
            (Hat_external: at_external the_sem c =
                           Some (CREATE, ef_sig CREATE, vf::arg::nil))
            (Hinitial: initial_core the_sem genv vf (arg::nil) = Some c_new)
            (Hfun_sepc: vf = Vptr b ofs)
            (Hafter_external: after_external the_sem
                                             (Some (Vint Int.zero)) c = Some c')
            (Hcompatible: mem_compatible tp m)
            (Hpersonal_perm: 
               personal_mem cnt0 Hcompatible = jm)
            (Hget_fun_spec: JMem.get_fun_spec jm (b, Int.intval ofs) arg = Some (P,Q))
            (Hsat_fun_spec: P d_phi)
            (Hrem_fun_res: join d_phi phi' (m_phi jm))
            (Htp': tp_upd = updThread cnt0 (Kresume c') phi')
            (Htp': tp' = addThread tp_upd c_new d_phi),
            conc_step genv cnt0 Hcompat tp' m
                     
    | step_mklock :
        forall  (tp' tp'': thread_pool) jm jm' c c' b ofs R ,
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
            (Hat_external: after_external
                             the_sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = updThread cnt0 (Kresume c') phi'),
            conc_step genv cnt0 Hcompat tp'' m' 
    | step_freelock :
        forall  (tp' tp'': thread_pool) c c' b ofs jm jm' R,
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
            (Hm_forward: m = m')
            (Hat_external: after_external the_sem (Some (Vint Int.zero)) c = Some c')
            (Htp': tp' = updThread cnt0 (Kresume c') (m_phi jm')),
            conc_step genv cnt0 Hcompat  tp'' (m_dry jm')  (* m_dry jm' = m_dry jm = m *)
                     
    | step_lockfail :
        forall  c b ofs jm,
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
            (HJcanwrite: phi@(b, Int.intval ofs) = YES sh pfullshare (LK LKSIZE) (pack_res_inv R))
            (Hload: Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.zero)),
            conc_step genv cnt0 Hcompat tp m.
    
    Definition cstep (genv:G): forall {tid0 ms m},
                                 containsThread ms tid0 -> mem_compatible ms m ->
                                 thread_pool -> mem -> Prop:=
      @juicy_step genv.
    
    
    Definition conc_call (genv:G):
      forall {tid0 ms m}, containsThread ms tid0 -> mem_compatible ms m ->
        thread_pool -> mem -> Prop:=
      @conc_step genv.
    
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
      mk (mkPos onePos) (fun _ => c) (fun _ => empty_rmap level) (fun _ => None).
    
    Definition init_mach (genv:G)(v:val)(args:list val) : option thread_pool:=
      match initial_core the_sem genv v args with
      | Some c => Some (initial_machine (Kresume c))
      | None => None
      end.
      
End JuicyMachineSig.

  Module myCoarseSemantics :=
    CoarseMachine mySchedule JuicyMachineSig.
  Definition coarse_semantics:=
    myCoarseSemantics.MachineSemantics.
  
End Concur.
