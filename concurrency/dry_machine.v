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
  Definition res := access_map.
  Definition lock_info := access_map.
End LocksAndResources.


Module ThreadPool (SEM:Semantics)  <: ThreadPoolSig
    with Module TID:= NatTID with Module SEM:=SEM
    with Module RES := LocksAndResources.
                        Include (OrdinalPool SEM LocksAndResources).
End ThreadPool.


Module Concur.
  
  Module mySchedule := ListScheduler NatTID.

  Module DryMachineShell (SEM:Semantics)  <: ConcurrentMachineSig
      with Module ThreadPool.TID:=mySchedule.TID
      with Module ThreadPool.SEM:= SEM
      with Module ThreadPool.RES:= LocksAndResources.
                                    
     Module ThreadPool := ThreadPool SEM.
     Import ThreadPool.
     Import ThreadPool.SEM ThreadPool.RES.
     
     Notation tid := NatTID.tid.
     
     (** Memories*)
     Definition richMem: Type:= mem.
     Definition dryMem: richMem -> mem:= id.
     Definition diluteMem: mem -> mem := setMaxPerm.
     
     Notation thread_pool := (ThreadPool.t).
     Notation perm_map := ThreadPool.RES.res.
     
     (** The state respects the memory*)
     Record mem_compatible' tp m : Prop :=
       { compat_th :> forall {tid} (cnt: containsThread tp tid),
             permMapLt (getThreadR cnt) (getMaxPerm m);
         compat_lp : forall l pmap, lockRes tp l = Some pmap ->
                               permMapLt pmap (getMaxPerm m);
         compat_ls : permMapLt (lockSet tp) (getMaxPerm m)}.
     
     Definition mem_compatible tp m : Prop := mem_compatible' tp m.

     (** Per-thread disjointness definition*)
     Definition race_free (tp : thread_pool) :=
       forall i j (cnti : containsThread tp i)
         (cntj : containsThread tp j) (Hneq: i <> j),
         permMapsDisjoint (getThreadR cnti)
                          (getThreadR cntj).
     
     (*argh this invariant is such a pain, tried collecting everything
    first, still a pain *)
     Record invariant' tp :=
       { no_race : race_free tp;
         lock_set_threads : forall i (cnt : containsThread tp i),
             permMapsDisjoint (lockSet tp) (getThreadR cnt);
         lock_res_threads : forall l pmap i (cnt : containsThread tp i),
             lockRes tp l = Some pmap ->
             permMapsDisjoint pmap (getThreadR cnt);
         lock_res_set : forall l pmap,
             lockRes tp l = Some pmap ->
             permMapsDisjoint pmap (lockSet tp)
       }.

     Definition invariant := invariant'.

     Record relAngelSpec (src tgt src' tgt' : access_map) : Prop :=
       { relAngelIncr: forall b ofs,
           Mem.perm_order' (Maps.PMap.get b src ofs) Readable <->
           Mem.perm_order' (Maps.PMap.get b tgt' ofs) Readable \/
           Mem.perm_order' (Maps.PMap.get b src' ofs) Readable;
         relAngelDecr: forall b ofs,
             Mem.perm_order'' (Maps.PMap.get b src ofs)
                              (Maps.PMap.get b src' ofs)}.

     Record acqAngelSpec (src tgt src' tgt' : access_map) : Prop :=
       { acqAngelIncr: forall b ofs,
           Mem.perm_order' (Maps.PMap.get b tgt' ofs) Readable ->
           Mem.perm_order' (Maps.PMap.get b tgt ofs) Readable \/
           Mem.perm_order' (Maps.PMap.get b src ofs) Readable;
         acqAngelDecr: forall b ofs,
             Mem.perm_order'' (Maps.PMap.get b src ofs)
                              (Maps.PMap.get b src' ofs)}.

     (*Lets see if the other cases should change.*)
     Record angelSpec (src tgt src' tgt' : access_map) : Prop :=
       { angelIncr: forall b ofs,
           Mem.perm_order' (Maps.PMap.get b tgt' ofs) Readable ->
           Mem.perm_order' (Maps.PMap.get b tgt ofs) Readable \/
           Mem.perm_order' (Maps.PMap.get b src ofs) Readable;
         angelDecr: forall b ofs,
             Mem.perm_order'' (Maps.PMap.get b src ofs)
                              (Maps.PMap.get b src' ofs)}.
     
     (** Steps*)
     Inductive dry_step genv {tid0 tp m} (cnt: containsThread tp tid0)
               (Hcompatible: mem_compatible tp m) : thread_pool -> mem  -> Prop :=
     | step_dry :
         forall (tp':thread_pool) c m1 m' (c' : code),
         forall (Hrestrict_pmap:
              restrPermMap (Hcompatible tid0 cnt) = m1)
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt = Krun c)
           (Hcorestep: corestep Sem genv c m1 c' m')
           (Htp': tp' = updThread cnt (Krun c') (getCurPerm m')),
           dry_step genv cnt Hcompatible tp' m'.

     Definition option_function {A B} (opt_f: option (A -> B)) (x:A): option B:=
       match opt_f with
         Some f => Some (f x)
       | None => None
       end.
     Infix "??" := option_function (at level 80, right associativity).
     
     (*missing lock-ranges*)
     Inductive ext_step (genv:G) {tid0 tp m} (*Can we remove genv from here?*)
               (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
       thread_pool -> mem -> Prop :=
     | step_acquire :
         forall (tp' tp'':thread_pool) m1 c m' b ofs pmap virtueThread
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c =
                          Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
           (Hcompatible: mem_compatible tp m)
           (Hrestrict_pmap: restrPermMap (compat_ls Hcompat) = m1)
           (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.one))
           (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
           (HisLock: lockRes tp (b, Int.intval ofs) = Some pmap)
           (Hangel: acqAngelSpec pmap (getThreadR cnt0)
                              empty_map
                              (computeMap (getThreadR cnt0) virtueThread))
           (Htp': tp' = updThread cnt0 (Kresume c Vundef)
                                  (computeMap (getThreadR cnt0) virtueThread))
           (Htp'': tp'' = updLockSet tp' (b, Int.intval ofs) empty_map),
           ext_step genv cnt0 Hcompat tp'' m' 
                    
     | step_release :
         forall (tp' tp'':thread_pool) m1 c m' b ofs pmap virtueThread virtueLP
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (*His_empty: pmap = empty_map *) (*Maybe we need this? *)
           (Hat_external: at_external Sem c =
                          Some (UNLOCK, ef_sig UNLOCK, Vptr b ofs::nil))
           (Hrestrict_pmap: restrPermMap (compat_ls Hcompat) = m1)
           (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero))
           (Hstore: Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.one) = Some m')
           (HisLock: lockRes tp (b, Int.intval ofs) = Some pmap)
           (Hangel: relAngelSpec (getThreadR cnt0) pmap
                              (computeMap (getThreadR cnt0) virtueThread)
                              virtueLP)
           (Htp': tp' = updThread cnt0 (Kresume c Vundef)
                                  (computeMap (getThreadR cnt0) virtueThread))
           (Htp'': tp'' = updLockSet tp' (b, Int.intval ofs) virtueLP),
           ext_step genv cnt0 Hcompat tp'' m' 
                    
     | step_create :
         forall  (tp_upd tp':thread_pool) c vf arg virtue1 virtue2,
         forall
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c =
                          Some (CREATE, ef_sig CREATE, vf::arg::nil))
           (HangelDecr: forall b ofs, Mem.perm_order''
                                   (Maps.PMap.get b (getThreadR cnt0) ofs)
                                   (Maps.PMap.get b (computeMap
                                                       (getThreadR cnt0) virtue1) ofs))
           (HangelIncr: forall b ofs,
               Mem.perm_order'' (Some Nonempty)
                                (Maps.PMap.get b (computeMap empty_map virtue2)
                                               ofs))
           (Htp_upd: tp_upd = updThread cnt0 (Kresume c Vundef)
                                        (computeMap (getThreadR cnt0) virtue1))
           (Htp': tp' = addThread tp_upd vf arg
                                  (computeMap empty_map virtue2)),
           ext_step genv cnt0 Hcompat tp' m
                    
     | step_mklock :
         forall  (tp' tp'': thread_pool) m1 c m' b ofs pmap_tid',
           let: pmap_tid := getThreadR cnt0 in
           forall
             (Hinv : invariant tp)
             (Hcode: getThreadC cnt0 = Kblocked c)
             (Hat_external: at_external Sem c =
                            Some (MKLOCK, ef_sig MKLOCK, Vptr b ofs::nil))
             (Hrestrict_pmap: restrPermMap (Hcompat tid0 cnt0) = m1)
             (Hstore:
                Mem.store Mint32 m1 b (Int.intval ofs) (Vint Int.zero) = Some m')
             (Hdrop_perm:
                setPermBlock (Some Nonempty) b (Int.intval ofs) pmap_tid LKSIZE_nat = pmap_tid')
             (*Hlp_perm: setPerm (Some Writable)
                               b (Int.intval ofs) (lockSet tp) = pmap_lp*)
             (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
             (Htp'': tp'' = updLockSet tp' (b,(Int.intval ofs)) empty_map),
             ext_step genv cnt0 Hcompat tp'' m' 
                      
     | step_freelock :
         forall  (tp' tp'': thread_pool) c b ofs virtue pmap' m',
         forall
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c =
                          Some (FREE_LOCK, ef_sig FREE_LOCK, Vptr b ofs::nil))
           (*(Hangel_spec1: forall b0, b0 <> b -> virtue ! b0 = None) 
           (Hangel_spec2: forall ofs0, ~ Intv.In (ofs0 - Int.intval ofs) (0%Z, LKSIZE) ->
                                  ((virtue ! b) ?? ofs0) = None)
           (Hangel_spec3: forall ofs0, Intv.In (ofs0 - Int.intval ofs) (0%Z, LKSIZE) ->
                                  ((virtue ! b) ?? ofs0) = Some (Some (Some Writable)) \/
                                  (virtue ! b ?? ofs0) = Some (Some (Some Freeable)))*)
           (Hangel: angelSpec (lockSet tp) (getThreadR cnt0)
                              (lockSet (remLockSet tp (b, Int.intval ofs)))
                              (computeMap (getThreadR cnt0) virtue ))
           (Hset_perm: (computeMap (getThreadR cnt0) virtue) = pmap')
           (*Hset_perm: setPermBlock virtue b (Int.intval ofs) 
            (getThreadR cnt0) LKSIZE_nat = pmap') (* This should be computemap + specs*) *)
           
           (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap')
           (Htp'': tp'' = remLockSet tp' (b,(Int.intval ofs)))
           (Hmem_no_change: m = m'),
           ext_step genv cnt0 Hcompat  tp'' m'
                    
     | step_acqfail :
         forall  c b ofs m1,
         forall
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c =
                          Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
           (*His_lock: (Maps.PMap.get b (lockSet tp)) (Int.intval ofs)*)
           (Hrestrict_pmap: restrPermMap (compat_ls Hcompat) = m1)
           (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero)),
           ext_step genv cnt0 Hcompat tp m.
     
     Definition threadStep (genv : G): forall {tid0 ms m},
         containsThread ms tid0 -> mem_compatible ms m ->
         thread_pool -> mem -> Prop:=
       @dry_step genv.
     
     Definition syncStep (genv :G) :
       forall {tid0 ms m},
         containsThread ms tid0 -> mem_compatible ms m ->
         thread_pool -> mem -> Prop:=
       @ext_step genv.

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
     
     Definition one_pos : pos := mkPos NPeano.Nat.lt_0_1.

     Definition compute_init_perm : G -> access_map :=
       fun _ => empty_map.
     
     Definition initial_machine genv c :=
       ThreadPool.mk
         one_pos
         (fun _ =>  Kresume c Vundef)
         (fun _ => compute_init_perm genv)
         empty_lset.
           
     Definition init_mach (genv:G)(v:val)(args:list val):option thread_pool :=
       match initial_core Sem genv v args with
       | Some c =>      
         Some (initial_machine genv c)
       | None => None
       end.

     Module DryMachineLemmas.
       
       
       Lemma updLock_raceFree: forall ds a pmap,
         race_free ds ->
         race_free (updLockSet ds a pmap).
       Proof.
         unfold race_free; intros.
         rewrite gLockSetRes. rewrite gLockSetRes.
         apply H; assumption.
       Qed.

       Lemma remLock_raceFree: forall ds a,
           race_free ds ->
           race_free (remLockSet ds a).
       Proof.
         unfold race_free; intros.
         assert (cnti':=cntRemoveL' cnti).
         assert (cntj':=cntRemoveL' cntj).
         rewrite (gRemLockSetRes cnti' ).
         erewrite (gRemLockSetRes cntj').
         apply H; assumption.
       Qed.

       (*TODO: This lemma should probably be moved. *)
       Lemma threads_canonical:
         forall ds m i (cnt:ThreadPool.containsThread ds i),
           mem_compatible ds m ->  
           isCanonical (ThreadPool.getThreadR cnt).
             intros.
             pose (HH:= compat_th H cnt); apply canonical_lt in HH.
             assumption.
       Qed.

       (** *Invariant Lemmas*)
       Lemma initial_invariant: forall genv c,
           invariant (initial_machine genv c).
             unfold  invariant.
             constructor.
             - unfold race_free, initial_machine; simpl.
               unfold containsThread; simpl.
               intros.
               apply empty_disjoint.
             - intros.
               unfold initial_machine; simpl.
               unfold permMapsDisjoint; intros.
               exists ((compute_init_perm genv) !! b ofs).
               unfold empty_map.
               unfold PMap.get at 1; simpl. rewrite PTree.gempty.
               reflexivity.
             - unfold initial_machine, lockRes, containsThread ; simpl.
               intros. rewrite threadPool.find_empty in H; inversion H.
             - unfold initial_machine, lockRes, containsThread ; simpl.
               intros. rewrite threadPool.find_empty in H; inversion H.
       Qed.

       (** ** Updating the machine state**)
       Lemma updCinvariant: forall {tid} ds c (cnt: containsThread ds tid),
           invariant ds ->
           invariant (updThreadC cnt c).
             intros ? ? ? ? INV; inversion INV.
             constructor.
             - generalize no_race; unfold race_free.
               simpl. intros.
               apply no_race0; auto.
             - simpl; assumption.
             - simpl; assumption.
             - simpl; assumption.
       Qed.

       

       Lemma updThread_inv: forall ds i (cnt: containsThread ds i) c pmap,
           invariant ds ->
           (forall j (cnt: containsThread ds j),
               i<>j -> permMapsDisjoint pmap (getThreadR cnt))->
           (permMapsDisjoint (lockSet ds) pmap) ->
           (forall l pmap0, lockRes ds l = Some pmap0 -> permMapsDisjoint pmap0 pmap) ->
           invariant (updThread cnt c pmap).
       Proof.
         intros ? x ? ? ? INV A B C.
         constructor.
         - unfold race_free; intros.
           destruct (scheduler.NatTID.eq_tid_dec x i); [|destruct (scheduler.NatTID.eq_tid_dec x j)].
           + subst i.
             rewrite gssThreadRes.
             rewrite gsoThreadRes; try solve[assumption].
             assert (cntj':=cntj).
             apply cntUpdate' in cntj'.
             eapply (A); assumption.
           + subst j.
             apply permMapsDisjoint_comm.
             rewrite gssThreadRes.
             rewrite gsoThreadRes; try solve[assumption].
             apply A; assumption.
           + rewrite gsoThreadRes; try solve[assumption].
             rewrite gsoThreadRes; try solve[assumption].
             inversion INV. apply no_race; assumption.
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
       Qed.
       
       Lemma updLock_inv: forall ds a pmap,
           invariant ds ->
           (forall i (cnt: containsThread ds i),
               permDisjoint (Some Writable) ((getThreadR cnt) !! (fst a) (snd a)) ) ->
           (forall i (cnt : containsThread ds i),
               permMapsDisjoint pmap (getThreadR cnt)) ->
           (permMapsDisjoint (lockSet ds) pmap) ->
           (permDisjoint (Some Writable) (pmap !! (fst a) (snd a))) ->
           (forall l pmap0, lockRes ds l = Some pmap0 ->
                       permDisjoint (Some Writable) (pmap0 !! (fst a) (snd a)))->
           invariant (updLockSet ds a pmap).
       Proof.
         intros ? ? ? INV A B C D E. constructor.
         - apply updLock_raceFree. inversion INV; assumption.
         - intros. rewrite gLockSetRes.
           destruct a as [b ofs]; rewrite lockSet_upd.
           apply disjoint_add.
           inversion INV; apply lock_set_threads0.
           apply A.
         - intros.
           destruct (addressFiniteMap.AMap.E.eq_dec a l).
           + subst.
             rewrite gssLockRes in H; inversion H; subst.
             rewrite gLockSetRes. apply B.
           + rewrite gsoLockRes in H; try solve[assumption].
             inversion INV. eapply lock_res_threads0. apply H.
         - intros.
           destruct (addressFiniteMap.AMap.E.eq_dec a l); destruct a.
           + subst.
             rewrite gssLockRes in H; inversion H; subst.
             rewrite lockSet_upd.
             apply permMapsDisjoint_comm; apply disjoint_add.
             apply C0.
             apply D.
           + rewrite lockSet_upd.
             apply permMapsDisjoint_comm.
             apply disjoint_add.
             * inversion INV. apply permMapsDisjoint_comm. eapply lock_res_set0.
               rewrite <- H. symmetry.
               apply gsoLockRes; assumption.
             * eapply E. rewrite <- H.
               rewrite gsoLockRes. reflexivity.
               assumption.
       Qed.

       Lemma remLock_inv: forall ds a,
           invariant ds ->
           (forall i (cnt: containsThread ds i),
               permDisjoint (Some Writable) ((getThreadR cnt) !! (fst a) (snd a)) ) ->
           invariant (remLockSet ds a).
       Proof.
         intros ? ? INV A.
         constructor.
         - apply remLock_raceFree. inversion INV; assumption.
         - intros.
           
           unfold permMapsDisjoint. intros.
           destruct (addressFiniteMap.AMap.E.eq_dec a (b, ofs)).
           + subst a. rewrite gsslockSet_rem.
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
               assumption.
       Qed.

     End DryMachineLemmas.
     
  End DryMachineShell.

  (* Here I make the core semantics*)
(*Declare Module SEM:Semantics.
  Module DryMachine:= DryMachineShell SEM.
  Module myCoarseSemantics :=
    CoarseMachine mySchedule DryMachine.
  Module myFineSemantics :=
    FineMachine mySchedule  DryMachine.

  Definition coarse_semantics:=
    myCoarseSemantics.MachineSemantics.
  Definition fine_semantics:=
    myFineSemantics.MachineSemantics.*)
  
End Concur.



(* After this there needs to be some cleaning. *)










(* Section InitialCore. *)

(*   Context {cT G : Type} {the_sem : CoreSemantics G cT Mem.mem}. *)
(*   Import ThreadPool. *)

  
(*   Notation thread_pool := (t cT). *)
(*   Notation perm_map := access_map. *)
  
(*   Definition at_external (st : (list nat) * thread_pool) *)
(*   : option (external_function * signature * seq val) := None. *)

(*   Definition after_external (ov : option val) (st : list nat * thread_pool) : *)
(*     option (list nat * thread_pool) := None. *)

(*   Definition two_pos : pos := mkPos NPeano.Nat.lt_0_2. *)
  
(*   Definition ord1 := Ordinal (n := two_pos) (m := 1) (leqnn two_pos). *)

(*   (*not clear what the value of halted should be*) *)
(*   Definition halted (st : list nat * thread_pool) : option val := None. *)

(*   Variable compute_init_perm : G -> access_map. *)
(*   Variable lp_code : cT. *)
(*   Variable sched : list nat. *)

(*   Definition initial_core the_ge (f : val) (args : list val) : option (list nat * thread_pool) := *)
(*     match initial_core the_sem the_ge f args with *)
(*       | None => None *)
(*       | Some c => *)
(*         Some (sched, ThreadPool.mk *)
(*                        two_pos *)
(*                        (fun tid => if tid == ord0 then lp_code *)
(*                                 else if tid == ord1 then c *)
(*                                      else c (*bogus value; can't occur*)) *)
(*                        (fun tid => if tid == ord0 then empty_map else *)
(*                                   if tid == ord1 then compute_init_perm the_ge *)
(*                                   else empty_map) *)
(*                        0) *)
(*     end. *)

(*   Variable aggelos : nat -> access_map. *)

(*   Definition cstep (the_ge : G) (st : list nat * thread_pool) m *)
(*              (st' : list nat * thread_pool) m' := *)
(*     @step cT G the_sem the_ge aggelos (@coarse_step cT G the_sem the_ge) *)
(*           (fst st) (snd st) m (fst st') (snd st') m'. *)

(*   Definition fstep (the_ge : G) (st : list nat * thread_pool) m *)
(*              (st' : list nat * thread_pool) m' := *)
(*     @step cT G the_sem the_ge aggelos (@fine_step cT G the_sem the_ge) *)
(*           (fst st) (snd st) m (fst st') (snd st') m'. *)
  
(*   Program Definition coarse_semantics : *)
(*     CoreSemantics G (list nat * thread_pool) mem := *)
(*     Build_CoreSemantics _ _ _ *)
(*                         initial_core *)
(*                         at_external *)
(*                         after_external *)
(*                         halted *)
(*                         cstep *)
(*                         _ _ _. *)

(*   Program Definition fine_semantics : *)
(*     CoreSemantics G (list nat * thread_pool) mem := *)
(*     Build_CoreSemantics _ _ _ *)
(*                         initial_core *)
(*                         at_external *)                                          
(*                         after_external *)
(*                         halted *)
(*                         fstep *)
(*                         _ _ _. *)

(* End InitialCore. *)
(* End Concur. *)