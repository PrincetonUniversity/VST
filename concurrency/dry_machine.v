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
           ext_step genv cnt0 Hcompat  tp'' m'
                    
     | step_acqfail :
         forall  c b ofs m1,
         forall
           (Hinv : invariant tp)
           (Hcode: getThreadC cnt0 = Kblocked c)
           (Hat_external: at_external Sem c =
                          Some (LOCK, ef_sig LOCK, Vptr b ofs::nil))
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
     
     Definition initial_machine pmap c :=
       ThreadPool.mk
         one_pos
         (fun _ =>  Kresume c Vundef)
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
       Qed.

       (** Similar states are the ones that are identical for
       everything but permissions. *)
       Inductive similar_mem m m' :=
       | SimilarMem : Mem.mem_contents m = Mem.mem_contents m' ->
                      Mem.nextblock m = Mem.nextblock m' ->
                      similar_mem m m'.

       Inductive similar_threadPool tp tp' :=
       | SimilarPool :
           num_threads tp = num_threads tp' ->
           (forall i (cnti: containsThread tp i) (cnti': containsThread tp' i),
               getThreadC cnti = getThreadC cnti') ->
           similar_threadPool tp tp'.

       Lemma similar_updLockSet:
         forall tp tp' addr addr' rmap rmap',
           similar_threadPool tp tp' ->
           similar_threadPool (updLockSet tp addr rmap)
                              (updLockSet tp' addr' rmap').
       Proof.
         intros.
         inversion H.
         constructor; auto.
       Qed.
       
       Lemma similar_updThread:
         forall tp tp' i (cnti: containsThread tp i)
           (cnti': containsThread tp' i) c pmap pmap',
           similar_threadPool tp tp' ->
           similar_threadPool (updThread cnti c pmap) (updThread cnti' c pmap').
       Proof.
         intros.
         inversion H.
         constructor; auto.
         intros.
         destruct (i0 == i) eqn:Heq; move/eqP:Heq=>Heq.
         subst. do 2 rewrite gssThreadCode; auto.
         rewrite gsoThreadCode; auto.
         rewrite gsoThreadCode; auto.
       Qed.

       Lemma similar_addThread:
         forall tp tp' i (cnti: containsThread tp i)
           (cnti': containsThread tp' i) v arg pmap pmap',
           similar_threadPool tp tp' ->
           similar_threadPool (addThread tp v arg pmap) (addThread tp' v arg pmap').
       Proof.
         intros.
         inversion H.
         constructor.
         unfold addThread; simpl. rewrite H0; auto.
         intros.
         assert (cnti00 := cntAdd' cnti0).
         assert (cnti0'0 := cntAdd' cnti'0).
         destruct cnti00 as [[cnti00 ?] | Heq];
           destruct cnti0'0 as [[cnti0'0 ?] | ?].
         - erewrite gsoAddCode with (cntj := cnti00) by eauto.
           erewrite gsoAddCode with (cntj := cnti0'0) by eauto.
           eauto.
         - exfalso; subst; apply H2.
           destruct (num_threads tp), (num_threads tp'); simpl; inversion H0; auto.
         - exfalso; subst; apply H2.
           destruct (num_threads tp), (num_threads tp'); simpl; inversion H0; auto.
         - subst. erewrite gssAddCode by eauto.
           erewrite gssAddCode; eauto.
       Qed.
       
       Lemma similar_remLockSet:
         forall tp tp' addr addr',
           similar_threadPool tp tp' ->
           similar_threadPool (remLockSet tp addr)
                              (remLockSet tp' addr').
       Proof.
         intros.
         inversion H.
         constructor; auto.
       Qed.

       Lemma mem_load_similar:
         forall chunk m m' b ofs pmap pmap' v v'
           (Hlt: permMapLt pmap (getMaxPerm m))
           (Hlt': permMapLt pmap' (getMaxPerm m'))
           (Hload: Mem.load chunk (restrPermMap Hlt) b ofs = Some v)
           (Hload': Mem.load chunk (restrPermMap Hlt') b ofs = Some v')
           (Hsimilar: similar_mem m m'),
           v = v'.
       Proof.
         intros.
         inversion Hsimilar.
         apply Mem.load_result in Hload.
         apply Mem.load_result in Hload'.
         simpl in *.
         rewrite H in Hload. subst; auto.
       Qed.

       Lemma mem_store_similar:
         forall chunk m m' b ofs pmap pmap' v m2 m2'
           (Hlt: permMapLt pmap (getMaxPerm m))
           (Hlt': permMapLt pmap' (getMaxPerm m'))
           (Hstore: Mem.store chunk (restrPermMap Hlt) b ofs v = Some m2)
           (Hstore': Mem.store chunk (restrPermMap Hlt') b ofs v = Some m2')
           (Hsimilar: similar_mem m m'),
           similar_mem m2 m2'.
       Proof.
         intros.
         inversion Hsimilar.
         constructor.
         erewrite Mem.store_mem_contents by eauto.
         erewrite Mem.store_mem_contents with (m2 := m2') by eauto.
         simpl. rewrite H; auto.
         apply Mem.nextblock_store in Hstore.
         apply Mem.nextblock_store in Hstore'.
         simpl in *.
         rewrite Hstore Hstore' H0; auto.
       Qed.
       
       Hint Resolve similar_updLockSet similar_updThread
            similar_addThread similar_remLockSet mem_store_similar: similar.

       (** Synchronization steps from similar states reach similar states*)
       Lemma syncStep_value_det:
         forall ge tp1 tp1' m1 m1' tp2 m2 tp2' m2' i
           (cnti: containsThread tp1 i)
           (cnti': containsThread tp1' i)
           (HsimilarPool: similar_threadPool tp1 tp1')
           (HsimilarMem: similar_mem m1 m1')
           (Hcomp1: mem_compatible tp1 m1)
           (Hcomp1': mem_compatible tp1' m1')
           (Hstep1: syncStep ge cnti Hcomp1 tp2 m2)
           (Hstep1': syncStep ge cnti' Hcomp1' tp2' m2'),
           similar_threadPool tp2 tp2' /\ similar_mem m2 m2'.
       Proof with eauto with similar.
         intros.
         inversion HsimilarPool.
         inversion Hstep1; subst;
         inversion Hstep1'; subst;
         specialize (H0 _ cnti cnti');
         rewrite H0 in Hcode;
         rewrite Hcode in Hcode0;
         inversion Hcode0; subst;
         rewrite Hat_external in Hat_external0;
         inversion Hat_external0; subst; split;
         try match goal with
             | [H1: Mem.load _ _ _ _ = Some ?V1,
                    H2: Mem.load _ _ _ _ = Some ?V2 |- _] =>
               assert (Heq := mem_load_similar _ _ _ _ _ H1 H2 HsimilarMem)
             end; try discriminate;
         eauto with similar.
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
