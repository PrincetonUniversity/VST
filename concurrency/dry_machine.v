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

  (** The type of dry machines. This is basically the same as
  [ConcurrentMachineSig] but resources are instantiated with dry
  resources*)
  Module Type DryMachineSig  (SEM: Semantics) <: ConcurrentMachineSig
      with Module ThreadPool.RES:= LocksAndResources
      with Module ThreadPool.TID:=mySchedule.TID.
                                     
     Declare Module Events : EventSig.
     Module ThreadPool := OrdinalPool SEM LocksAndResources.
     Import ThreadPool SEM.
     Import event_semantics Events.
     
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
     
     Record invariant' tp :=
       { no_race : race_free tp;
         lock_set_threads : forall i (cnt : containsThread tp i),
             permMapsDisjoint (lockSet tp) (getThreadR cnt);
         lock_res_threads : forall l pmap i (cnt : containsThread tp i),
             lockRes tp l = Some pmap ->
             permMapsDisjoint pmap (getThreadR cnt);
         lock_res_set : forall l pmap,
             lockRes tp l = Some pmap ->
             permMapsDisjoint pmap (lockSet tp);
         lockRes_valid: lr_valid (lockRes tp)
       }.

     Definition invariant := invariant'.
     Parameter threadStep :
       G ->
       forall tid0 (ms : t) (m : mem),
         containsThread ms tid0 ->
         mem_compatible ms m -> t -> mem -> seq mem_event -> Prop.
     Parameter syncStep :
       G ->
       forall tid0 (ms : t) (m : mem),
         containsThread ms tid0 ->
         mem_compatible ms m -> t -> mem -> sync_event -> Prop.
     Parameter threadHalted :
       forall tid0 (ms : t), containsThread ms tid0 -> Prop.
     Parameter init_mach : option RES.res -> G -> val -> seq val -> option t.
  
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
     
     Record invariant' tp :=
       { no_race : race_free tp;
         lock_set_threads : forall i (cnt : containsThread tp i),
             permMapsDisjoint (lockSet tp) (getThreadR cnt);
         lock_res_threads : forall l pmap i (cnt : containsThread tp i),
             lockRes tp l = Some pmap ->
             permMapsDisjoint pmap (getThreadR cnt);
         lock_res_set : forall l pmap,
             lockRes tp l = Some pmap ->
             permMapsDisjoint pmap (lockSet tp);
         lockRes_valid: lr_valid (lockRes tp)
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
     
     (** Steps*)
     Inductive dry_step genv {tid0 tp m} (cnt: containsThread tp tid0)
               (Hcompatible: mem_compatible tp m) :
       thread_pool -> mem -> seq mem_event -> Prop :=
     | step_dry :
         forall (tp':thread_pool) c m1 m' (c' : code) ev,
         forall (Hrestrict_pmap:
              restrPermMap (Hcompatible tid0 cnt) = m1)
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt = Krun c)
           (Hcorestep: ev_step Sem genv c m1 ev c' m')
           (Htp': tp' = updThread cnt (Krun c') (getCurPerm m')),
           dry_step genv cnt Hcompatible tp' m' ev.

     Definition option_function {A B} (opt_f: option (A -> B)) (x:A): option B:=
       match opt_f with
         Some f => Some (f x)
       | None => None
       end.
     Infix "??" := option_function (at level 80, right associativity).
     
     Inductive ext_step (genv:G) {tid0 tp m} (*Can we remove genv from here?*)
               (cnt0:containsThread tp tid0)(Hcompat:mem_compatible tp m):
       thread_pool -> mem -> sync_event -> Prop :=
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
           ext_step genv cnt0 Hcompat tp'' m' (acquire (b, Int.intval ofs))
                    
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
           ext_step genv cnt0 Hcompat tp'' m' (release (b, Int.intval ofs))
                    
     | step_create :
         forall  (tp_upd tp':thread_pool) c b ofs arg virtue1 virtue2,
         forall
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c =
                          Some (CREATE, ef_sig CREATE, Vptr b ofs::arg::nil))
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
           (Htp': tp' = addThread tp_upd (Vptr b ofs) arg
                                  (computeMap empty_map virtue2)),
           ext_step genv cnt0 Hcompat tp' m (spawn (b, Int.intval ofs))
                    
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
             (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap_tid')
             (Htp'': tp'' = updLockSet tp' (b,(Int.intval ofs)) empty_map),
             ext_step genv cnt0 Hcompat tp'' m' (mklock (b, Int.intval ofs))
                      
     | step_freelock :
         forall  (tp' tp'': thread_pool) c b ofs virtue pmap' m',
         forall
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c =
                          Some (FREE_LOCK, ef_sig FREE_LOCK, Vptr b ofs::nil))
           (His_lock: lockRes tp (b, (Int.intval ofs)))
           (Hset_perm: computeMap (getThreadR cnt0) virtue = pmap')
           (Hchanged: forall ofs',
               Intv.In ofs' (Int.intval ofs,
                                 (Int.intval ofs) + Z.of_nat (LKSIZE_nat))%Z ->
               Mem.perm_order' (pmap' !! b ofs') Writable)
           (Hunchanged: forall b' ofs',
               (b = b' /\ (~ Intv.In ofs' (Int.intval ofs,
                                              (Int.intval ofs) +
                                               Z.of_nat (LKSIZE_nat)))%Z
                \/ b <> b') -> 
               pmap' !! b' ofs' = (getThreadR cnt0) !! b' ofs')
           (Htp': tp' = updThread cnt0 (Kresume c Vundef) pmap')
           (Htp'': tp'' = remLockSet tp' (b,(Int.intval ofs)))
           (Hmem_no_change: m = m'),
           ext_step genv cnt0 Hcompat  tp'' m' (freelock (b,Int.intval ofs))
                    
     | step_acqfail :
         forall  c b ofs m1,
         forall
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c =
                          Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
           (Hrestrict_pmap: restrPermMap (compat_ls Hcompat) = m1)
           (Hload: Mem.load Mint32 m1 b (Int.intval ofs) = Some (Vint Int.zero)),
           ext_step genv cnt0 Hcompat tp m (failacq (b, Int.intval ofs)).
     
     Definition threadStep (genv : G): forall {tid0 ms m},
         containsThread ms tid0 -> mem_compatible ms m ->
         thread_pool -> mem -> seq mem_event -> Prop:=
       @dry_step genv.
     
     Definition syncStep (genv :G) :
       forall {tid0 ms m},
         containsThread ms tid0 -> mem_compatible ms m ->
         thread_pool -> mem -> sync_event -> Prop:=
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
     
     Definition initial_machine pmap c :=
       ThreadPool.mk
         one_pos
         (fun _ =>  Krun c)
         (fun _ => pmap)
         empty_lset.

           
     Definition init_mach (pmap : option access_map) (genv:G)
                (v:val)(args:list val):option thread_pool :=
       match initial_core Sem genv v args with
       | Some c =>      
         match pmap with
         | Some pmap => Some (initial_machine pmap c)
         | None => None
         end
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
       Lemma initial_invariant: forall pmap c,
           invariant (initial_machine pmap c).
             unfold  invariant.
             constructor.
             - unfold race_free, initial_machine; simpl.
               unfold containsThread; simpl.
               intros.
               exfalso.
               apply Hneq.
               destruct i,j; simpl in *; auto;
               ssromega.
             - intros.
               unfold initial_machine; simpl.
               unfold permMapsDisjoint; intros. 
               exists (pmap !! b ofs).
               unfold empty_map.
               unfold lockSet. simpl.
               unfold A2PMap. simpl.
               rewrite PMap.gi; reflexivity.
             - unfold initial_machine, lockRes, containsThread ; simpl.
               intros. rewrite threadPool.find_empty in H; inversion H.
             - unfold initial_machine, lockRes, containsThread ; simpl.
               intros. rewrite threadPool.find_empty in H; inversion H.
             - unfold initial_machine, lockRes, empty_lset. simpl.
               intros b ofs; unfold AMap.empty; simpl. constructor.
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
         - intros.
           intros b ofs. rewrite gsoThreadLPool.
           inversion INV. eapply lockRes_valid0.
       Qed.
       
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
    Qed.
    
     End DryMachineLemmas.
     
  End DryMachineShell.
  
End Concur.
