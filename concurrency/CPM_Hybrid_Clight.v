(*Require Import Coqlib.*)
Require Import VST.concurrency.DryMachineSourceCore.
Require Import VST.concurrency.x86_context.

Require Import VST.concurrency.CoreSemantics_sum.
Require Import VST.concurrency.HybridMachine.

Require Import VST.concurrency.machine_semantics.
Set Bullet Behavior "Strict Subproofs".

(*Import the dry CPM for Clight_core*)
Import DMS.
Import DryMachine.

(*Build the hybrid context*)
Notation hb:=(Some 0).
Definition Hybrid_resources:=
  Build_Resources_rec
    dry_machine.LocksAndResources.res
    dry_machine.LocksAndResources.lock_info.
Definition Sems:= Build_Semantics_rec SEM.G SEM.C SEM.CLC_evsem.
Definition Semt:= X86SEM_rec. (*Need both for hybrid*)
Definition Hybrid_Sem:= CoreSem_Sum hb Sems Semt.
Definition Hybrid_MachineSem U r := new_MachineSemantics hb Sems Semt U r.
Definition Hybrid_new_machine U r:=
(HybridMachineSig.ConcurMachineSemantics _ _ _ (HybridMachine hb Sems Semt) U r).
Definition Hybrid_Thread_pool_context:=
  OrdinalThreadPool_rec Hybrid_resources Hybrid_Sem.

(* Hybrid ThreadPool *)
Definition make_hybrid_thread_pool (tp:thread_pool): t_ Hybrid_Thread_pool_context.
  destruct tp.
  econstructor; eauto.
  intros.
  eapply pool in X; destruct X;
    [eapply Krun|eapply Kblocked| eapply Kresume | eapply (Kinit v v0)] ; auto;
  apply SState; auto.
Defined.

(* Hybrid trace*)
Definition make_hybrid_event (ev:ErasedMachine.Events.machine_event): 
  HybridMachineSig.machine_event.
  destruct ev.
  - constructor ; eauto.
  - constructor 2; eauto.
    inversion s;
      [eapply HybridMachineSig.release|
       eapply HybridMachineSig.acquire|
       eapply HybridMachineSig.mklock|
       eapply HybridMachineSig.freelock|
       eapply HybridMachineSig.spawn|
       eapply HybridMachineSig.failacq]; eauto.
Qed.
  
Fixpoint make_hybrid_trace (tr: SC.event_trace): list HybridMachineSig.machine_event.
  induction tr.
  - exact nil.
  - apply cons; auto.
    exact (make_hybrid_event a).
Defined.

Require Import Coqlib.
Require Import msl.Axioms.

Lemma containsthread_preserved tid st (T:containsThread (make_hybrid_thread_pool st) tid):
    ThreadPool.containsThread st tid.
Proof. destruct st; simpl in *; apply T. Defined. 

Lemma containsthread_preserved_inv tid st (T:ThreadPool.containsThread st tid):
      containsThread (make_hybrid_thread_pool st) tid.   
Proof. destruct st; simpl in *; apply T. Defined. 

Lemma lockRes_preserved st l pmaps (L:lockRes (make_hybrid_thread_pool st) l = Some pmaps): 
      ThreadPool.lockRes st l = Some pmaps.
Proof. destruct st; simpl in *. apply L. Qed.

Lemma lockRes_preserved_inv st l pmaps (L: ThreadPool.lockRes st l = Some pmaps):
      lockRes (make_hybrid_thread_pool st) l = Some pmaps. 
Proof. destruct st; simpl in *. apply L. Qed.

Lemma lockRes_preserved_eq st l:
   ThreadPool.lockRes st l = lockRes (make_hybrid_thread_pool st) l. 
Proof. destruct st; simpl in *; reflexivity.  Qed.

Lemma mem_compatible_preserved st m (Hcmpt : mem_compatible st m):
      HybridMachine.mem_compatible hb Sems Semt (make_hybrid_thread_pool st) m.
Proof. inv Hcmpt. econstructor; intros.
    + destruct (compat_th0 _ (containsthread_preserved _ _ cnt)).
      clear compat_th0; simpl in *. destruct st; simpl in *. split; assumption.
    + apply (compat_lp0 l pmaps (lockRes_preserved _ _ _ H)). 
    + apply (lockRes_blocks0 _ _ (lockRes_preserved _ _ _ H)).
Defined. 

Lemma containsThread_eq tid st1 Htid:
     containsthread_preserved tid st1
            (containsthread_preserved_inv tid st1 Htid) = Htid.
Proof. destruct st1. reflexivity. Qed.

Lemma invariant_preserved st (Hinv : invariant st):
      HybridMachine.invariant hb Sems Semt (make_hybrid_thread_pool st).
Proof. inv Hinv.
  constructor.
  - clear - no_race_thr0; intros. specialize (no_race_thr0 i j (containsthread_preserved _ _ cnti)  (containsthread_preserved _ _ cntj) Hneq). 
    destruct st; simpl in *. apply no_race_thr0.
  - clear - no_race_lr0; intros. 
    specialize (no_race_lr0 laddr1 laddr2).
    rewrite (lockRes_preserved _ _ _ Hres1) in no_race_lr0.
    rewrite (lockRes_preserved _ _ _ Hres2) in no_race_lr0. 
    eapply (no_race_lr0 _ _ Hneq); trivial. 
  - clear - no_race0; intros.  unfold lockRes_, ThreadPool in *; simpl in *.
    specialize (no_race0 i laddr (containsthread_preserved _ _ cnti)).
    rewrite (lockRes_preserved _ _ _ Hres) in no_race0.
    specialize (no_race0 _ (eq_refl _)). destruct st; simpl in *. apply no_race0.
  - clear - thread_data_lock_coh0; intros. 
    destruct (thread_data_lock_coh0 _ (containsthread_preserved _ _ cnti)) as [A B]; clear thread_data_lock_coh0.
    split; [ clear B | clear A]; intros.
    * specialize (A _  (containsthread_preserved _ _ cntj)). destruct st; apply A.
    * specialize (B laddr).
      rewrite (lockRes_preserved _ _ _ H) in B.
      specialize (B _ (eq_refl _)). destruct st; apply B.
  - clear - locks_data_lock_coh0; intros. 
    specialize (locks_data_lock_coh0 laddr).
    rewrite (lockRes_preserved _ _ _ Hres) in locks_data_lock_coh0.
    destruct (locks_data_lock_coh0 _ (eq_refl _)) as [A B]; clear locks_data_lock_coh0.
    split; [ clear B | clear A]; intros.
    * specialize (A _  (containsthread_preserved _ _ cntj)). destruct st; apply A.
    * specialize (B laddr').
      rewrite (lockRes_preserved _ _ _ H) in B.
      specialize (B _ (eq_refl _)). destruct st; apply B.
  - clear - lockRes_valid0. unfold lr_valid_ in *. destruct st; simpl in *. assumption.
  - clear. intros. destruct X. eexists; try reflexivity. destruct st; simpl in *. 
    remember (pool (fintype.Ordinal (n:=pos.n num_threads) (m:=i) cnti)) as q.
    destruct q; inv H.
  - clear. intros. destruct X. 2: eexists; reflexivity.
    admit. (*mixup between languages?*)
Admitted.  

Lemma hybridtrace_nil: make_hybrid_trace nil = @nil HybridMachineSig.machine_event.
Proof. reflexivity. Qed. 

(* Initial simulation *)
(*This lemma is under construction*)
(*Lemma Hcore_initial :
    forall j c1 vals1 m1 m1' vals2 m2 m2' main,
    initial_machine Sem1 ge1 m1 main vals1 = Some (c1, m1') ->
    exists cd c2,
      HybridMachine.initial_machine hb Hybrid_Sems Hybrid_Semt main vals2 = Some (c2, m2')
      /\ MSmatch_states cd j c1 (option_proj m1 m1') c2 (option_proj m2 m2').*)


(* Thread step 1to1 simulation*)
Lemma thread_step_diagram:
    forall U0 gs gt st1 m st1' m' U r,
    thread_step (new_DMachineSem U0 r) gs U st1 m st1' m' ->
    thread_step (Hybrid_new_machine U0 r) (gs,gt) U
                                  ( make_hybrid_thread_pool st1) m
                                  (make_hybrid_thread_pool st1') m'.
Proof.
  unfold new_DMachineSem, Hybrid_new_machine; simpl. intros. inv H.
  specialize (mem_compatible_preserved _ _ Hcmpt). intros [PermFst PermSnd]. simpl in *.
  eapply thread_step' with (tid:=tid)(ev:=ev)
     (Htid:=containsthread_preserved_inv _ _ Htid)(Hcmpt:=mem_compatible_preserved _ _ Hcmpt).
     apply HschedN.
  inv Htstep. econstructor; simpl in *; try reflexivity.
+ (*invariant*) clear - Hinv. apply invariant_preserved; trivial. 
+ destruct st1; simpl in *. rewrite Hcode. reflexivity.
+ apply SEvstep. simpl. unfold ThreadPool.SEM.Sem in Hcorestep.
  assert (permissions.restrPermMap (proj1 (Hcmpt tid Htid)) =
         permissions.restrPermMap
     (proj1
        ((mem_compatible_preserved st1 m Hcmpt) tid
           (containsthread_preserved_inv tid st1 Htid)))). 
  { destruct Hcmpt; simpl in *.
    remember (compat_th0 tid
         (containsthread_preserved tid st1
            (containsthread_preserved_inv tid st1 Htid))) as q.
    destruct q. 
    remember (compat_th0 tid Htid) as w; destruct w.
    destruct st1. simpl in *. rewrite Heqw, Heqq. trivial. }
  rewrite H in Hcorestep. apply Hcorestep.
+ unfold updThread;  destruct st1; simpl. f_equal. extensionality a.
  remember (@eqtype.eq_op (fintype.ordinal_eqType (pos.n num_threads)) a
      (@fintype.Ordinal (pos.n num_threads) tid Htid)) as q.
  destruct q; try reflexivity.
Qed.

(* Machine step 1to1 simulation*)
(* Note the traces should be nil...*)
Lemma machine_step_diagram:
    forall U0 gs gt st1 m st1' tr tr' m' U U' r,
    machine_step (new_DMachineSem U0 r) gs U tr st1 m U' tr' st1' m' ->
    machine_step (Hybrid_new_machine U0 r) (gs,gt) U (make_hybrid_trace tr)
                                  ( make_hybrid_thread_pool st1) m U' (make_hybrid_trace tr')
                                  (make_hybrid_thread_pool st1') m'.
Proof. intros.  unfold machine_step. unfold Hybrid_new_machine. simpl. inv H; simpl. 
+ inv Htstep; simpl in *. 
  eapply start_state' with (tid:=tid)(Htid:=containsthread_preserved_inv _ _ (*Htid*)ctn).
  - apply HschedN.
  - apply mem_compatible_preserved; trivial.
  - red; simpl. apply (StartThread  hb Sems Semt (gs, gt) m tid) with (c_new:=SState _ _ c_new)(vf:=vf)(arg:=arg); simpl.
    * unfold getThreadC. destruct st1; simpl in *. rewrite Hcode. trivial. 
    * unfold initial_core_sum; simpl. unfold state_sum_optionmt. 
      unfold semantics.initial_core in Hinitial. simpl in *. destruct (semantics.csem (event_semantics.msem ThreadPool.SEM.Sem)). simpl in *. admit. (* simpl in *. apply Hinitial. why do we seem to be in Asm?*)
    * apply invariant_preserved; trivial.
    * unfold updThreadC; simpl. destruct st1; simpl in *. f_equal. extensionality n.
      remember (@eqtype.eq_op (fintype.ordinal_eqType (pos.n num_threads)) n (fintype.Ordinal (n:=pos.n num_threads) (m:=tid) ctn)) as q.
      destruct q; reflexivity.
+ inv Htstep; simpl in *.
  apply resume_step' with (tid:=tid)(Htid:=containsthread_preserved_inv _ _ (*Htid*)ctn).
  - apply HschedN.
  - apply mem_compatible_preserved; trivial.
  - red; simpl. apply ResumeThread with (c:=SState _ _ c)(c':=SState _ _ c')(X:=X). 
    * simpl. unfold at_external_sum; simpl. eassumption.
    * simpl. unfold state_sum_options. unfold ThreadPool.SEM.Sem in Hafter_external. rewrite Hafter_external; trivial.
    * simpl. destruct st1; simpl in *. rewrite Hcode; trivial.
    * apply invariant_preserved; trivial.
    * destruct st1; simpl. unfold updThreadC; simpl. f_equal. extensionality n.
      remember (@eqtype.eq_op (fintype.ordinal_eqType (pos.n num_threads)) n (fintype.Ordinal (n:=pos.n num_threads) (m:=tid) ctn)) as q.
      destruct q; reflexivity.
+ inv Htstep; simpl in *.
  apply suspend_step' with (tid:=tid)(Htid:=containsthread_preserved_inv _ _ (*Htid*)ctn).
  - apply HschedN.
  - reflexivity. (*double goal seems odd*)
  -  apply mem_compatible_preserved; trivial.
  - red; simpl. apply SuspendThread with (c:=SState _ _ c)(X:=X). 
    * unfold ThreadPool.getThreadC in Hcode. destruct st1; simpl in *. rewrite Hcode; trivial.
    * unfold at_external_sum; simpl. eassumption.
    * apply invariant_preserved; trivial.
    * destruct st1; simpl. unfold updThreadC; simpl. f_equal. extensionality n.
      remember (@eqtype.eq_op (fintype.ordinal_eqType (pos.n num_threads)) n (fintype.Ordinal (n:=pos.n num_threads) (m:=tid) ctn)) as q.
      destruct q; reflexivity.
+ inv Htstep; simpl in *.
  { (*acquire*)
    eapply sync_step' with (tid:=tid)(Htid:=containsthread_preserved_inv _ _ Htid)(Hcmpt:=mem_compatible_preserved _ _ Hcmpt).
    - apply HschedN.
    - reflexivity. (*double goal seems odd*)
    - red; simpl. eapply (@HybridMachine.step_acquire hb Sems Semt true (gs,gt))with (c:=SState _ _ c)(Hlt':=Hlt'); simpl.
      * apply Hbounded.
      * apply invariant_preserved; trivial.
      * unfold ThreadPool.getThreadC in Hcode. destruct st1; simpl in *. rewrite Hcode; trivial.
      * apply Hat_external.
      * instantiate (1:=(permissions.restrPermMap (proj2 (Hcmpt tid Htid)))). destruct st1; simpl. f_equal. f_equal. f_equal. simpl. 
        unfold mem_compatible_preserved; simpl. destruct Hcmpt; simpl. remember (compat_th0 tid Htid) as q. destruct q; trivial.
      * apply Haccess.
      * apply Hload.
      * destruct st1. reflexivity.
      * reflexivity.
      * apply Hstore.
      * apply lockRes_preserved_inv. apply HisLock.
      * destruct st1; simpl in *; apply Hangel1.
      * destruct st1; simpl in *; apply Hangel2.
      * reflexivity.
      * unfold updLockSet, updThread. destruct st1; simpl in *. f_equal.
        extensionality n.
        remember (@eqtype.eq_op (fintype.ordinal_eqType (pos.n num_threads)) n (fintype.Ordinal (n:=pos.n num_threads) (m:=tid) Htid)) as q.
        destruct q; reflexivity. }
  { (*release*) 
    eapply sync_step' with (tid:=tid)(Htid:=containsthread_preserved_inv _ _ Htid)(Hcmpt:=mem_compatible_preserved _ _ Hcmpt).
    - apply HschedN.
    - reflexivity. (*double goal seems odd*)
    - red; simpl. eapply (@HybridMachine.step_release hb Sems Semt true (gs,gt))with (c:=SState _ _ c)(Hlt':=Hlt'); simpl.
    * apply Hbounded.
    * apply HboundedLP. 
    * apply invariant_preserved; trivial.
    * unfold ThreadPool.getThreadC in Hcode. destruct st1; simpl in *. rewrite Hcode; trivial.
    * apply Hat_external.
    * instantiate (1:=(permissions.restrPermMap (proj2 (Hcmpt tid Htid)))). destruct st1; simpl. f_equal. f_equal. f_equal. simpl. 
      unfold mem_compatible_preserved; simpl. destruct Hcmpt; simpl. remember (compat_th0 tid Htid) as q. destruct q; trivial.
    * apply Haccess.
    * apply Hload.
    * destruct st1. reflexivity.
    * reflexivity.
    * apply Hstore.
    * apply lockRes_preserved_inv. apply HisLock.
    * apply Hrmap.
    * destruct st1; simpl in *; apply Hangel1.
    * destruct st1; simpl in *; apply Hangel2.
    * reflexivity.
    * unfold updLockSet, updThread. destruct st1; simpl in *. f_equal.
      extensionality n.
      remember (@eqtype.eq_op (fintype.ordinal_eqType (pos.n num_threads)) n (fintype.Ordinal (n:=pos.n num_threads) (m:=tid) Htid)) as q.
      destruct q; reflexivity. }
  { (*spawn*) 
    eapply sync_step' with (tid:=tid)(Htid:=containsthread_preserved_inv _ _ Htid)(Hcmpt:=mem_compatible_preserved _ _ Hcmpt).
    - apply HschedN.
    - reflexivity. (*double goal seems odd*)
    - red; simpl. eapply (@HybridMachine.step_create hb Sems Semt true (gs,gt))with (c:=SState _ _ c); simpl.
    * apply Hbounded.
    * apply Hbounded_new. 
    * apply invariant_preserved; trivial.
    * unfold ThreadPool.getThreadC in Hcode. destruct st1; simpl in *. rewrite Hcode; trivial.
    * apply Hat_external.
    * destruct st1; simpl in *; apply Hangel1.
    * destruct st1; simpl in *; apply Hangel2.
    * reflexivity.
    * unfold addThread, updThread. destruct st1; simpl in *. f_equal.
      extensionality n.
      remember (@fintype.unlift (S (pos.n num_threads)) (pos.ordinal_pos_incr num_threads) n) as w.
      destruct w. 
      ++ destruct (@eqtype.eq_op (fintype.ordinal_eqType (pos.n num_threads)) o
            (@fintype.Ordinal (pos.n num_threads) tid Htid)); try reflexivity.
      ++ trivial. }
  { (*makelock*) 
    eapply sync_step' with (tid:=tid)(Htid:=containsthread_preserved_inv _ _ Htid)(Hcmpt:=mem_compatible_preserved _ _ Hcmpt).
    - apply HschedN.
    - reflexivity. (*double goal seems odd*)
    - red; simpl. eapply (@HybridMachine.step_mklock hb Sems Semt true (gs,gt))with (c:=SState _ _ c)(pmap_tid':=pmap_tid'); simpl.
    * apply invariant_preserved; trivial.
    * unfold ThreadPool.getThreadC in Hcode. destruct st1; simpl in *. rewrite Hcode; trivial.
    * apply Hat_external.
    * instantiate (1:=(permissions.restrPermMap (proj1 (Hcmpt tid Htid)))). destruct st1; simpl. f_equal. f_equal. f_equal. simpl. 
      unfold mem_compatible_preserved; simpl. destruct Hcmpt; simpl. remember (compat_th0 tid Htid) as q. destruct q; trivial.
    * apply Hfreeable.
    * apply Hstore.
    * rewrite <- Hdata_perm. destruct st1; simpl; trivial.
    * rewrite <- Hlock_perm. destruct st1; simpl; trivial.
    * rewrite <- lockRes_preserved_eq; trivial.
    * reflexivity.
    * unfold updLockSet, updThread. destruct st1; simpl in *. f_equal.
      extensionality n.
      remember (@eqtype.eq_op (fintype.ordinal_eqType (pos.n num_threads)) n (fintype.Ordinal (n:=pos.n num_threads) (m:=tid) Htid)) as q.
      destruct q; reflexivity. }
  { (*freelock*) 
    eapply sync_step' with (tid:=tid)(Htid:=containsthread_preserved_inv _ _ Htid)(Hcmpt:=mem_compatible_preserved _ _ Hcmpt).
    - apply HschedN.
    - reflexivity. (*double goal seems odd*)
    - red; simpl. eapply (@HybridMachine.step_freelock hb Sems Semt true (gs,gt))with (c:=SState _ _ c)(pmap_tid':=pmap_tid')(rmap:=rmap); simpl.
    * apply Hbounded.
    * apply invariant_preserved; trivial.
    * unfold ThreadPool.getThreadC in Hcode. destruct st1; simpl in *. rewrite Hcode; trivial.
    * apply Hat_external.
    * rewrite <- lockRes_preserved_eq; trivial.
    * apply Hrmap.
    * instantiate (1:=(permissions.restrPermMap (proj2 (Hcmpt tid Htid)))). destruct st1; simpl. f_equal. f_equal. f_equal. simpl. 
      unfold mem_compatible_preserved; simpl. destruct Hcmpt; simpl. remember (compat_th0 tid Htid) as q. destruct q; trivial. 
    * apply Hfreeable.
    * rewrite <- Hlock_perm. destruct st1; simpl; trivial.
    * apply Hneq_perms.
    * rewrite <- Hdata_perm. destruct st1; simpl; trivial.
    * reflexivity.
    * unfold remLockSet, updThread. destruct st1; simpl in *. f_equal.
      extensionality n.
      remember (@eqtype.eq_op (fintype.ordinal_eqType (pos.n num_threads)) n (fintype.Ordinal (n:=pos.n num_threads) (m:=tid) Htid)) as q.
      destruct q; reflexivity. }
  { (*acquire_fail*) 
    eapply sync_step' with (tid:=tid)(Htid:=containsthread_preserved_inv _ _ Htid)(Hcmpt:=mem_compatible_preserved _ _ Hcmpt).
    - apply HschedN.
    - reflexivity. (*double goal seems odd*)
    - red; simpl. eapply (@HybridMachine.step_acqfail hb Sems Semt true (gs,gt))with (c:=SState _ _ c); simpl.
    * apply invariant_preserved; trivial.
    * unfold ThreadPool.getThreadC in Hcode. destruct st1'; simpl in *. rewrite Hcode; trivial.
    * apply Hat_external.
    * instantiate (1:=(permissions.restrPermMap (proj2 (Hcmpt tid Htid)))). destruct st1'; simpl. f_equal. f_equal. f_equal. simpl. 
      unfold mem_compatible_preserved; simpl. destruct Hcmpt; simpl. remember (compat_th0 tid Htid) as q. destruct q; trivial. 
    * apply Haccess. 
    * apply Hload. }
+ (*halted*)
  inv Hhalted; simpl in *.
  apply halted_step' with (tid:=tid)(Htid:=containsthread_preserved_inv _ _ cnt).
  - apply HschedN.
  - reflexivity. (*double goal seems odd*)
  - apply mem_compatible_preserved; trivial.
  - apply invariant_preserved; trivial.
  - red; simpl. apply (@HybridMachine.thread_halted' hb Sems Semt) with (c:=SState _ _ c); simpl. 
    * unfold ThreadPool.getThreadC in Hcode. destruct st1'; simpl in *. rewrite Hcode; trivial.
    * apply Hcant.
+ (* schedfail *) 
  simpl in *.
  apply schedfail' with (tid:=tid). (*(Htid:=containsthread_preserved_inv _ _ tid).*)
  - apply HschedN.
  - intros N. elim Htid; clear Htid. apply containsthread_preserved. apply N.
  - apply invariant_preserved; trivial.
  - reflexivity. 
Admitted.

(* Same halted states *) 
Lemma same_halted U0 U c1 v1 r:
    conc_halted (new_DMachineSem U0 r) U c1 = Some v1 <->
    conc_halted (Hybrid_new_machine U0 r) U ( make_hybrid_thread_pool c1) = Some v1.
Proof. 
  unfold new_DMachineSem, Hybrid_new_machine; simpl.
  unfold DryConc.halted, halted; simpl.
  remember (SCH.schedPeek U) as q. remember (schedPeek U) as w.
  assert (q=w); subst. reflexivity. split; intros; trivial.
Qed.

Lemma getThread_preserved c j q (cnti : containsThread (make_hybrid_thread_pool c) j)
     (G: getThreadC cnti = Krun q):
     exists qq, ThreadPool.getThreadC (containsthread_preserved j c cnti) = Krun qq.
Proof. unfold containsThread in cnti. unfold getThreadC in G. unfold ThreadPool.getThreadC; simpl in *.
  destruct c; simpl in *.
  remember (pool (fintype.Ordinal (n:=pos.n num_threads) (m:=j) cnti)) as w.
  destruct w; try discriminate. inv G. exists c; trivial.
Qed. 

Lemma getThread_preserved_inv c j q (cnti : containsThread (make_hybrid_thread_pool c) j)
     (G: ThreadPool.getThreadC (containsthread_preserved j c cnti) = Krun q):
     exists qq, getThreadC cnti = Krun qq.
Proof. unfold containsThread in cnti. unfold  ThreadPool.getThreadC in G. unfold getThreadC; simpl in *.
  destruct c; simpl in *.
  remember (pool (fintype.Ordinal (n:=pos.n num_threads) (m:=j) cnti)) as w.
  destruct w; try discriminate. inv G. eexists; reflexivity. 
Qed. 

Require Import Nat.
Lemma ThreadHalted c j (cnti : @containsThread Resources (Sem hb Sems Semt) (make_hybrid_thread_pool c) j)
      (N : @threadHalted j c (containsthread_preserved j c cnti)):
@HybridMachine.threadHalted hb Sems Semt j (make_hybrid_thread_pool c) cnti.
Proof. inv N.
econstructor.
+ unfold getThreadC_; simpl. clear Hcant. 
  unfold getThreadC. unfold ThreadPool.getThreadC in Hcode. simpl in *.
  destruct c; simpl in *. unfold containsThread in cnti. simpl in *.
  unfold ThreadPool.containsThread in cnt. simpl in *.
  assert (P: pool (@fintype.Ordinal (pos.n num_threads) j cnti) = pool (@fintype.Ordinal (pos.n num_threads) j cnt)).
     clear. replace cnt with cnti. trivial. apply proof_irr. 
  rewrite P, Hcode. reflexivity.
+ apply Hcant.
Qed.

Lemma ThreadHalted_inv c j (cnti : @containsThread Resources (Sem hb Sems Semt) (make_hybrid_thread_pool c) j)
      (N :@HybridMachine.threadHalted hb Sems Semt j (make_hybrid_thread_pool c) cnti):
  @threadHalted j c (containsthread_preserved j c cnti).
Proof. inv N.
 unfold getThreadC_ in *; simpl. destruct c; simpl in *. 
 remember (pool (fintype.Ordinal (n:=pos.n num_threads) (m:=j) cnt)) as w.
 destruct w; try discriminate. inv Hcode.
econstructor.
+ unfold ThreadPool.getThreadC. simpl in *.
  assert (P: pool (@fintype.Ordinal (pos.n num_threads) j cnti) = pool (@fintype.Ordinal (pos.n num_threads) j cnt)).
     clear. replace cnt with cnti. trivial. apply proof_irr. 
  rewrite P,  <- Heqw. reflexivity. 
+ apply Hcant.
Qed.

Lemma same_thread_running U r c i:
      runing_thread (new_DMachineSem U r) c i <->
      runing_thread (Hybrid_new_machine U r) (make_hybrid_thread_pool c) i.
Proof. 
  unfold new_DMachineSem, Hybrid_new_machine; simpl.
  unfold DryConc.unique_Krun, unique_Krun; simpl.
  split; intros.
+ specialize (ThreadHalted _ _ cnti); intros.
  destruct c; simpl in *. unfold containsThread in cnti; simpl in cnti. unfold ThreadPool.containsThread in H; simpl in H. 
  remember (pool (fintype.Ordinal (n:=pos.n num_threads) (m:=j) cnti) ) as w.
  destruct w; inv H0; symmetry in Heqw. exploit (H j cnti c Heqw); clear H.
  - eauto. 
  - destruct (SCH.TID.eq_tid_dec i j); subst.
    destruct (Nat.eq_dec j j); trivial; try omega. destruct (Nat.eq_dec i j); trivial; try omega.
+ destruct (SCH.TID.eq_tid_dec i j); subst; simpl. reflexivity. admit. (*BUG ?*) 
Admitted.
