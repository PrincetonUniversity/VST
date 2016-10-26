Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.
Require Import concurrency.pos.
Require Import concurrency.scheduler.
Require Import concurrency.concurrent_machine.
Require Import concurrency.addressFiniteMap. (*The finite maps*)
Require Import concurrency.pos.
Require Import concurrency.lksize.
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

Require Import Coq.ZArith.ZArith.

Notation EXIT := 
  (EF_external "EXIT" (mksignature (AST.Tint::nil) None)). 

Notation CREATE_SIG :=
  (mksignature (AST.Tint::AST.Tint::nil) (Some AST.Tint) cc_default).
Notation CREATE := (EF_external "spawn" CREATE_SIG).

Notation READ := 
  (EF_external "READ" (mksignature (AST.Tint::AST.Tint::AST.Tint::nil)
                                   (Some AST.Tint) cc_default)).
Notation WRITE := 
  (EF_external "WRITE" (mksignature (AST.Tint::AST.Tint::AST.Tint::nil)
                                    (Some AST.Tint) cc_default)).

Notation MKLOCK := 
  (EF_external "makelock" (mksignature (AST.Tint::nil)
                                     (Some AST.Tint) cc_default)).
Notation FREE_LOCK := 
  (EF_external "freelock" (mksignature (AST.Tint::nil)
                                        (Some AST.Tint) cc_default)).

Notation LOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation LOCK := (EF_external "acquire" LOCK_SIG).
Notation UNLOCK_SIG := (mksignature (AST.Tint::nil) (Some AST.Tint) cc_default).
Notation UNLOCK := (EF_external "release" UNLOCK_SIG).

Require Import concurrency.permissions.
Require Import concurrency.threadPool.

Module LocksAndResources.
  Definition res : Type := unit.
  Definition lock_info : Type := unit.
End LocksAndResources.

Module ThreadPool (SEM:Semantics)  <: ThreadPoolSig
    with Module TID:= NatTID with Module SEM:=SEM
    with Module RES := LocksAndResources.
    Include (OrdinalPool SEM LocksAndResources).
End ThreadPool.


Module mySchedule := ListScheduler NatTID.

Module ErasedMachineShell (SEM:Semantics)  <: ConcurrentMachineSig
    with Module ThreadPool.TID:=mySchedule.TID
    with Module ThreadPool.SEM:= SEM
    with Module ThreadPool.RES:= LocksAndResources
    with Module Events.TID := mySchedule.TID.

   Module Events := Events.
   Module ThreadPool := ThreadPool SEM.
   Import ThreadPool.
   Import ThreadPool.SEM ThreadPool.RES.
   Import event_semantics Events.
   
   Notation tid := NatTID.tid.

   (** Memories*)
   Definition richMem: Type:= mem.
   Definition dryMem: richMem -> mem:= id.
   Definition diluteMem: mem -> mem := erasePerm.
   
   Notation thread_pool := (ThreadPool.t).
   Notation perm_map := ThreadPool.RES.res.
   
   (** The state respects the memory*)
   Definition mem_compatible (tp : thread_pool) (m : mem) : Prop := True.

   Definition invariant (tp : thread_pool) := True.
   
   (** Steps*)
   Inductive dry_step genv {tid0 tp m} (cnt: containsThread tp tid0)
             (Hcompatible: mem_compatible tp m) :
     thread_pool -> mem -> seq mem_event -> Prop :=
   | step_dry :
       forall (tp':thread_pool) c m' (c' : code) ev
         (Hcode: getThreadC cnt = Krun c)
         (Hcorestep: ev_step Sem genv c m ev c' m')
         (Htp': tp' = updThreadC cnt (Krun c')),
     dry_step genv cnt Hcompatible tp' m' ev.

   Inductive ext_step (genv:G) {tid0 tp m} (*Can we remove genv from here?*)
             (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
     thread_pool -> mem -> sync_event -> Prop :=
   | step_acquire :
       forall (tp' : thread_pool) c m' b ofs
         (Hcode: getThreadC cnt0 = Kblocked c)
         (Hat_external: at_external Sem c =
                        Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
         (Hload: Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.one))
         (Hstore: Mem.store Mint32 m b (Int.intval ofs) (Vint Int.zero) = Some m')
         (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
         ext_step genv cnt0 Hcompat tp' m' (acquire (b, Int.intval ofs) None)
                  
   | step_release :
       forall (tp':thread_pool) c m' b ofs
         (Hcode: getThreadC cnt0 = Kblocked c)
         (Hat_external: at_external Sem c =
                        Some (UNLOCK, ef_sig UNLOCK, Vptr b ofs::nil))
         (Hstore: Mem.store Mint32 m b (Int.intval ofs) (Vint Int.one) = Some m')
         (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
         ext_step genv cnt0 Hcompat tp' m' (release (b, Int.intval ofs) None)
                  
   | step_create :
       forall (tp_upd tp':thread_pool) c b ofs arg
         (Hcode: getThreadC cnt0 = Kblocked c)
         (Hat_external: at_external Sem c =
                        Some (CREATE, ef_sig CREATE, Vptr b ofs::arg::nil))
         (Htp_upd: tp_upd = updThreadC cnt0 (Kresume c Vundef))
         (Htp': tp' = addThread tp_upd (Vptr b ofs) arg tt),
         ext_step genv cnt0 Hcompat tp' m (spawn (b, Int.intval ofs))
                  
   | step_mklock :
       forall  (tp': thread_pool) c m' b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external Sem c =
                         Some (MKLOCK, ef_sig MKLOCK, Vptr b ofs::nil))
          (Hstore: Mem.store Mint32 m b (Int.intval ofs) (Vint Int.zero) = Some m')
          (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
         ext_step genv cnt0 Hcompat tp' m' (mklock (b, Int.intval ofs))
                  
   | step_freelock :
       forall (tp' tp'': thread_pool) c b ofs
         (Hcode: getThreadC cnt0 = Kblocked c)
         (Hat_external: at_external Sem c =
                        Some (FREE_LOCK, ef_sig FREE_LOCK, Vptr b ofs::nil))
         (Htp': tp' = updThreadC cnt0 (Kresume c Vundef)),
         ext_step genv cnt0 Hcompat  tp' m (freelock (b,Int.intval ofs))
                  
   | step_acqfail :
       forall  c b ofs
          (Hcode: getThreadC cnt0 = Kblocked c)
          (Hat_external: at_external Sem c =
                         Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
          (Hload: Mem.load Mint32 m b (Int.intval ofs) = Some (Vint Int.zero)),
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
   Admitted.
   
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
   Admitted.
  
  Lemma syncstep_not_running:
    forall g i tp m cnt cmpt tp' m' tr, 
      @syncStep g i tp m cnt cmpt tp' m' tr ->
      forall cntj q, ~ @getThreadC i tp cntj = Krun q.
   Admitted.
  

   
   Inductive threadHalted': forall {tid0 ms},
       containsThread ms tid0 -> Prop:=
   | thread_halted':
       forall tp c tid0
         (cnt: containsThread tp tid0)
         (Hcode: getThreadC cnt = Krun c)
         (Hcant: halted Sem c),
         threadHalted' cnt.
   
   Definition threadHalted: forall {tid0 ms},
       containsThread ms tid0 -> Prop:= @threadHalted'.

   
  Lemma threadHalt_update:
    forall i j, i <> j ->
      forall tp cnt cnti c' cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j (@updThreadC i tp cnti c') cnt') .
   Admitted.
  
  Lemma syncstep_equal_halted:
    forall g i tp m cnti cmpt tp' m' tr, 
      @syncStep g i tp m cnti cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) <->
        (@threadHalted j tp' cnt').
   Admitted.
  
  Lemma threadStep_not_unhalts:
    forall g i tp m cnt cmpt tp' m' tr, 
      @threadStep g i tp m cnt cmpt tp' m' tr ->
      forall j cnt cnt',
        (@threadHalted j tp cnt) ->
        (@threadHalted j tp' cnt') .
   Admitted.
   
   Definition one_pos : pos := mkPos NPeano.Nat.lt_0_1.
   
   Definition initial_machine c :=
     ThreadPool.mk
       one_pos
       (fun _ =>  Krun c)
       (fun _ => tt)
       empty_lset.

   Definition init_mach (_ : option unit) (genv:G)
              (v:val)(args:list val):option thread_pool :=
     match initial_core Sem genv v args with
     | Some c =>      
       Some (initial_machine c)
     | None => None
     end.
     
End ErasedMachineShell.

