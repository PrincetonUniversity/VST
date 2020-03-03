
Require Import Omega.

Require Import Coq.Classes.Morphisms.
Require Import Relation_Definitions.

Require Import compcert.common.Globalenvs.
Require Import compcert.common.ExposedSimulations.
Require Import compcert.common.Values.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.

Require Import VST.concurrency.lib.tactics.
Require Import VST.concurrency.common.Compcert_lemmas.
Require Import VST.concurrency.common.permissions. Import permissions.
Require Import VST.concurrency.common.semantics. 
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.advanced_permissions.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.
Require Import VST.concurrency.compiler.synchronisation_steps_semantics.


Require Import VST.concurrency.lib.Coqlib3.

Require Import VST.concurrency.memsem_lemmas.
Import BinNums.

Import BinInt.
Import List.
Import Integers.
Import Ptrofs.
Import Basics.
Import FunctionalExtensionality.

Require Import VST.concurrency.compiler.Clight_self_simulation.
Require Import VST.concurrency.compiler.C_lemmas.
Require Import VST.concurrency.compiler.Asm_self_simulation.
Require Import VST.concurrency.compiler.Asm_lemmas.
Require Import VST.concurrency.compiler.diagrams.
Require Import VST.concurrency.common.mem_equiv.
Require Import VST.concurrency.lib.pair.
Require Import VST.concurrency.compiler.inject_virtue.
Require Import VST.concurrency.compiler.concur_match.
Require Import VST.concurrency.lib.Coqlib3.

Set Nested Proofs Allowed.
Set Bullet Behavior "Strict Subproofs".

(*Clight Machine *)
Require Import VST.concurrency.common.ClightMachine.
(*Asm Machine*)
Require Import VST.concurrency.common.x86_context.
Import bounded_maps.

Import ThreadPool.
Import OrdinalPool.

Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.

(** *Things to move*)

Fixpoint list_f {A} (f: Z -> A) (n:nat) ofs:=
  match n with
  | S n' => f ofs :: list_f f n' (ofs + 1)
  | _ => nil
  end.
Lemma forall_range:
  forall n {A} P (f: Z -> A) ofs,
    Forall P (list_f f n ofs) ->
    forall ofs0,
      Intv.In ofs0 (ofs, ofs + (Z.of_nat n)) ->
      P (f ofs0).
Proof.
  induction n; intros.
  - simpl in H0.
    replace (ofs + 0) with ofs in H0 by omega.
    exfalso; eapply Intv.empty_notin; eauto.
    unfold Intv.empty; simpl; omega.
  - destruct (Z.eq_dec ofs ofs0).
    + subst; inv H; auto.
    + assert (Intv.In ofs0 (ofs + 1, (ofs + 1) + Z.of_nat n)).
      { unfold Intv.In in *.
        simpl in *.
        destruct H0; split.
        * omega.
        * clear - H1.
          replace (ofs + 1 + Z.of_nat n)
            with (ofs + Z.pos (Pos.of_succ_nat n)); auto.
          clear.
          rewrite <- Z.add_assoc, Zpos_P_of_succ_nat.
          omega. }
      clear H0.
      eapply IHn; eauto.
      inv H; auto.
Qed.
Lemma fun_range:
  forall n {A} (f f': Z -> A) ofs,
    list_f f n ofs =
    list_f f' n ofs  ->
    forall ofs0,
      Intv.In ofs0 (ofs, ofs + (Z.of_nat n)) ->
      f ofs0 = f' ofs0.
Proof.
  induction n; intros.
  - simpl in H0.
    replace (ofs + 0) with ofs in H0 by omega.
    exfalso; eapply Intv.empty_notin; eauto.
    unfold Intv.empty; simpl; omega.
  - destruct (Z.eq_dec ofs ofs0).
    + subst; inv H; auto.
    + assert (Intv.In ofs0 (ofs + 1, (ofs + 1) + Z.of_nat n)).
      { unfold Intv.In in *.
        simpl in *.
        destruct H0; split.
        * omega.
        * clear - H1.
          replace (ofs + 1 + Z.of_nat n)
            with (ofs + Z.pos (Pos.of_succ_nat n)); auto.
          clear.
          rewrite <- Z.add_assoc, Zpos_P_of_succ_nat.
          omega. }
      clear H0.
      eapply IHn; eauto.
      inv H; auto.
Qed.
Lemma fun_range4:
  forall {A} (f f': Z -> A) ofs,
    f ofs :: f (ofs + 1)
      :: f (ofs + 1 + 1)
      :: f (ofs + 1 + 1 + 1):: nil = 
    f' ofs :: f' (ofs + 1)
       :: f' (ofs + 1 + 1)
       :: f' (ofs + 1 + 1 + 1):: nil ->
    forall ofs0,
      Intv.In ofs0 (ofs, ofs + 4) ->
      f ofs0 = f' ofs0.
Proof.
  intros.
  eapply (fun_range 4); simpl; eauto.
Qed.

Lemma perm_image_injects_map:
  (* should probably replace perm_image 
                     with full_inject_map*)
  forall mu mp, perm_image mu mp <-> injects_map mu mp.
Proof.
  split; intros ** ? **.
  - exploit H. eapply at_least_Some_trivial; eauto.
    intros (?&?&?); econstructor; eauto.
  - hnf in H0. match_case in H0.
    exploit H; eauto. intros HH; inv HH.
    repeat econstructor; eauto.
Qed.
Lemma map_valid_Lt:
  forall m p1 p2,
    permMapLt p1 p2 ->
    map_valid m p2 ->
    map_valid m p1.
Proof.
  intros ** ? **. 
  specialize (H b ofs).
  rewrite H1 in H.
  simpl in H; hnf in H.
  match_case in H; eauto.
Qed.
Lemma map_valid_proper:
  Proper (mem_equiv ==> access_map_equiv ==> iff)
         map_valid.
Proof.
  setoid_help.proper_iff.
  setoid_help.proper_intros.
  intros ? **.
  hnf. inv H. rewrite <- nextblock_eqv.
  eapply H1.
  rewrite H0; eauto.
Qed.


Lemma Lt_valid_map:
  forall m d,
    permMapLt_pair d (getMaxPerm m) ->
    map_valid_pair m d.
Proof.
  intros ?. solve_pair.
  intros. intros ? **.
  destruct (valid_block_dec m b); try assumption.
  eapply Mem.nextblock_noaccess in n.
  specialize (H b ofs).
  rewrite H0 in H; hnf in H.
  rewrite getMaxPerm_correct in H. simpl in H.
  unfold permission_at in *.
  rewrite n in H; tauto.
Qed.

(* This should go in mem_equiv*)
Instance permMapJoin_equivalent:
  Proper (access_map_equiv
            ==> access_map_equiv
            ==> access_map_equiv ==> iff) permMapJoin.
Proof.
  setoid_help.proper_iff; setoid_help.proper_intros; subst.
  intros ??. rewrite <- H, <- H0, <- H1. auto.
Qed.
Lemma Lt_option_impl:
  forall b a,
    permMapLt_pair a b  ->
    pair21_prop full_map_option_implication a b.
Proof.
  intros ?. solve_pair.
  intros ** ??; hnf.
  repeat match_case; eauto.
  specialize (H b0 ofs).
  rewrite Heqo, Heqo0 in H.
  inv H.
Qed.
Lemma Lt_inject_map_pair:
  forall mu b a, 
    injects_map mu b ->
    permMapLt_pair a b ->
    injects_map_pair mu a.
Proof.
  intros ??. solve_pair.
  intros ** ? **.
  exploit H0; rewrite H1.
  intros HH; hnf in HH; match_case in HH.
  eapply H; eauto.
Qed.

Lemma map_lt_implication: forall b a,
    permMapLt_pair a b ->
    pair21_prop full_map_option_implication a b.
Proof.
  intros b. solve_pair.
  intros ** ? **.
  specialize (H b0 ofs).
  red; repeat match_case; auto.
Qed.


Lemma max_map_valid:
  forall m, map_valid m (getMaxPerm m).
Proof.
  intros ???? HH.
  destruct (valid_block_dec m b); auto.
  eapply Mem.nextblock_noaccess in n.
  rewrite getMaxPerm_correct in HH. unfold permission_at in *.
  rewrite HH in n; congruence.
Qed.
Lemma disjoint_lt:
  forall A A' B,
    permMapLt A' A ->
    permMapsDisjoint A B ->
    permMapsDisjoint A' B.
Proof.
  intros ** ??. specialize (H b ofs).
  dup H as HH.
  specialize (H0 b ofs) as [C H0].
  unfold Mem.perm_order'',perm_union in *.
  (* We do all the cases *)
  repeat match_case in H;
    repeat match_case in H0;
    inv H0; inv H; try econstructor; eauto.
Qed.
Hint Unfold permMapsDisjoint2: pair.

Lemma disjoint_lt_pair:
  forall a a' b,
    permMapLt_pair2 a' a ->
    permMapsDisjoint2 a b ->
    permMapsDisjoint2 a' b.
Proof.
  solve_pair. apply disjoint_lt.
Qed.

Lemma join_disjoint:
  forall A B C,
    permMapJoin A B C ->
    permMapsDisjoint A B.
Proof.
  intros ** b ofs. specialize (H b ofs).
  inv H; econstructor; simpl; eauto.
  unfold perm_union; match_case; eauto.
Qed.

Instance permMapLt_refl:
  Reflexive permMapLt.
intros ? ? ?. hnf. match_case; constructor. Qed.
Lemma disjoint_join:
  forall a b c,
    permMapJoin a b c ->
    permMapsDisjoint a b.
  intros ** ??. specialize (H b0 ofs).
  unfold perm_union; match_case.
  + inv H; eexists; simpl; eauto.
  + inv H; eexists; simpl; eauto.
Qed.
Lemma permMapCoherence_Lt:
  forall p1 p2 p1' p2',
    permMapCoherence p1 p2 ->
    permMapLt p1' p1 ->
    permMapLt p2' p2 ->
    permMapCoherence p1' p2'.
Proof.
  intros ** b ofs.
  eapply perm_coh_lower; eauto.
Qed.
Lemma join_disjoint_pair:
  forall A B C,
    permMapJoin_pair A B C ->
    permMapsDisjoint2 A B.
Proof.
  solve_pair.
  apply disjoint_join.
Qed.


(** * mem_compatible *)
Lemma mem_compatible_updLock:
  forall Sem Tp m st st' l lock_info,
    permMapLt_pair lock_info (getMaxPerm m) ->
    Mem.valid_block m (fst l) ->
    st' = ThreadPool.updLockSet(resources:=dryResources) st l lock_info ->
    @mem_compatible Sem Tp st m ->
    @mem_compatible Sem Tp st' m.
Proof.
  intros * Hlt Hvalid HH Hcmpt.
  subst st'; constructor; intros.
  - erewrite ThreadPool.gLockSetRes. apply Hcmpt.
  - (*Two cases, one of which goes by Hlt*)
    destruct (addressFiniteMap.AMap.E.eq_dec l l0).
    + subst. rewrite ThreadPool.gsslockResUpdLock in H.
      inv H; auto.
    + subst. rewrite ThreadPool.gsolockResUpdLock in H; auto.
      eapply Hcmpt; eauto. 
  - (*Two cases, one of which goes by Hvalid*)
    destruct (addressFiniteMap.AMap.E.eq_dec l l0); subst; eauto.
    eapply Hcmpt.
    subst. rewrite ThreadPool.gsolockResUpdLock in H; eauto.

    Unshelve.
    eapply ThreadPool.cntUpdateL'; eauto.
Qed.
Lemma mem_compatible_updthread:
  forall Sem Tp m st st' i (cnt:ThreadPool.containsThread st i) c res,
    permMapLt_pair res (getMaxPerm m) ->
    st' = ThreadPool.updThread(resources:=dryResources) cnt c res ->
    @mem_compatible Sem Tp st m ->
    @mem_compatible Sem Tp st' m.
Proof.
  intros * Hlt HH Hcmpt.
  subst st'; constructor; intros.
  - (*Two cases, one of which goes by Hlt*)
    destruct (Nat.eq_dec i tid).
    + subst. rewrite ThreadPool.gssThreadRes; auto.
    + subst. unshelve erewrite ThreadPool.gsoThreadRes; auto.
      eapply ThreadPool.cntUpdate'; eauto.
      eapply Hcmpt.
  - rewrite ThreadPool.gsoThreadLPool in H.
    eapply Hcmpt; eassumption.
  -  rewrite ThreadPool.gsoThreadLPool in H.
     eapply Hcmpt; eassumption.
Qed.
Lemma mem_compatible_addThread:
  forall Sem Tp m st st' f_ptr arg res,
    permMapLt_pair res (getMaxPerm m) ->
    st' = ThreadPool.addThread(resources:=dryResources) st f_ptr arg res ->
    @mem_compatible Sem Tp st m ->
    @mem_compatible Sem Tp st' m.
Proof.
  intros * Hlt HH Hcmpt.
  subst st'; constructor; intros.
  - (*Two cases, one of which goes by Hlt*)
    exploit @ThreadPool.cntAdd'; eauto; intros [[? ?]| ?].
    + subst. unshelve erewrite ThreadPool.gsoAddRes; auto.
      eapply Hcmpt.
    + rewrite ThreadPool.gssAddRes; auto.
  - rewrite ThreadPool.gsoAddLPool in H.
    eapply Hcmpt; eassumption.
  -  rewrite ThreadPool.gsoAddLPool in H.
     eapply Hcmpt; eassumption.
Qed.

(** * Lemmas about invariant*)

Ltac rewrite_getupd:=
  repeat match goal with
         | _ => erewrite ThreadPool.gLockSetRes
         | _ => rewrite ThreadPool.gsoThreadLPool
         | _ => rewrite ThreadPool.gssThreadRes
         | _ => erewrite ThreadPool.gssLockRes
         | _ => erewrite ThreadPool.gsoThreadRes by eauto
         | _ => erewrite ThreadPool.gsoLockRes by eauto 
         end.
Lemma invariant_update:
  forall Sem (st st': @ThreadPool.t dryResources Sem OrdinalPool.OrdinalThreadPool) h laddr c lock_perm th_perm
    (Hcnt:ThreadPool.containsThread st h),
    st' =
    ThreadPool.updLockSet (ThreadPool.updThread Hcnt c th_perm) laddr lock_perm ->
    invariant st ->
    forall (no_race_thr0: forall j (cntj : ThreadPool.containsThread st j),
          (j <> h) ->
          permMapsDisjoint2 th_perm (ThreadPool.getThreadR cntj))
      (no_race_lr: forall (laddr': address) (rmap : lock_info),
          laddr' <> laddr ->
          ThreadPool.lockRes st laddr' = Some rmap -> permMapsDisjoint2 lock_perm rmap)
      (no_race1: permMapsDisjoint2 th_perm lock_perm)
      (no_race2: forall laddr0 rmap,
          laddr0 <> laddr -> ThreadPool.lockRes st laddr0 = Some rmap ->
          permMapsDisjoint2 th_perm rmap)
      (no_race3: forall i (cnti : ThreadPool.containsThread st i),
          i <> h ->
          permMapsDisjoint2 (ThreadPool.getThreadR cnti) lock_perm)
      (thread_date_lock_coh1: permMapCoherence (fst th_perm) (snd th_perm))
      (thread_date_lock_coh2: permMapCoherence (fst lock_perm) (snd th_perm))
      (thread_date_lock_coh3: permMapCoherence (fst th_perm) (snd lock_perm))
      (thread_date_lock_coh4: forall i (cnti : ThreadPool.containsThread st i),
          i <> h ->
          permMapCoherence (fst th_perm) (snd (ThreadPool.getThreadR cnti)) /\
          permMapCoherence (fst (ThreadPool.getThreadR cnti)) (snd th_perm))
      (thread_date_lock_coh5: forall i (cnti : ThreadPool.containsThread st i),
          i <> h ->
          permMapCoherence (fst (ThreadPool.getThreadR cnti)) (snd lock_perm) /\
          permMapCoherence (fst lock_perm) (snd (ThreadPool.getThreadR cnti)))
      (thread_date_lock_coh6: forall laddr0 rmap,
          laddr0 <> laddr -> ThreadPool.lockRes st laddr0 = Some rmap ->
          permMapCoherence (fst rmap) (snd th_perm) /\
          permMapCoherence (fst th_perm) (snd rmap))
      (locks_data_lock_coh1: permMapCoherence (fst lock_perm) (snd lock_perm))
      (locks_data_lock_coh2: forall laddr0 rmap,
          laddr0 <> laddr -> ThreadPool.lockRes st laddr0 = Some rmap ->
          permMapCoherence (fst rmap) (snd lock_perm) /\
          permMapCoherence (fst lock_perm) (snd rmap))
      (lockRes_valid: coqlib4.isSome (ThreadPool.lockRes st laddr)),
      invariant st'.
Proof.
  intros * ? Hinv **. constructor.
  - intros * ?.
    destruct (Nat.eq_dec i h);
      destruct (Nat.eq_dec j h); subst; rewrite_getupd.
    + contradict Hneq; reflexivity.
    + rewrite_getupd. auto.
    + apply permMapsDisjoint2_comm; auto.
    + eapply no_race_thr; eauto.
  - intros * ?.
    destruct (addressFiniteMap.AMap.E.eq_dec laddr1 laddr);
      destruct (addressFiniteMap.AMap.E.eq_dec laddr2 laddr); subst;
        rewrite_getupd; intros.
    + contradict Hneq; auto.
    + inv Hres1. eapply no_race_lr0; eauto.
    + inv Hres2. eapply permMapsDisjoint2_comm, no_race_lr0; eauto.
    + eapply no_race_lr; try eapply Hneq; eauto.
  - intros *.
    destruct (Nat.eq_dec i h);
      destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
      subst; rewrite_getupd; intros.
    + inv Hres; assumption.
    + eauto.
    + inv Hres. eauto.
    + eapply no_race; eauto.
  - intros *; split; intros *.
    + destruct (Nat.eq_dec i h);
        destruct (Nat.eq_dec j h); subst; intros; rewrite_getupd.
      * assumption.
      * apply thread_date_lock_coh4; auto.
      * apply thread_date_lock_coh4; auto.
      * exploit @thread_data_lock_coh; eauto. intros [HH ?].
        apply HH.
    + destruct (Nat.eq_dec i h);
        destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
        subst; rewrite_getupd; intros.
      * inv H; assumption.
      * eapply thread_date_lock_coh6; eauto.
      * symmetry in H; inv H. apply thread_date_lock_coh5; auto.
      * eapply Hinv; eauto.
  - intros *; split; intros *; revert Hres.
    + destruct (Nat.eq_dec j h);
        destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
        subst; rewrite_getupd; intros.
      * inv Hres; eauto.
      * eapply thread_date_lock_coh6; eauto.
      * inv Hres. eapply thread_date_lock_coh5; auto.
      * exploit @locks_data_lock_coh; eauto. intros [HH ?].
        apply HH.
    + destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
        destruct (addressFiniteMap.AMap.E.eq_dec laddr' laddr);
        subst; rewrite_getupd; intros.
      * inv Hres; inv H; eauto.
      * inv Hres; eapply locks_data_lock_coh2; eauto.
      * inv H; eapply locks_data_lock_coh2; eauto.
      * pose proof (locks_data_lock_coh _ Hinv _ _ Hres).
        destruct H0. specialize (H1 _ _ H). auto.
  - intros ??.
    destruct (addressFiniteMap.AMap.E.eq_dec (b,ofs) laddr); subst.
    + rewrite ThreadPool.gsslockResUpdLock; intros.
      assert (ofs <> ofs0) by omega.
      rewrite ThreadPool.gsolockResUpdLock, ThreadPool.gsoThreadLPool.
      2: { intros HH; apply H0; inv HH; reflexivity. }
      exploit @lockRes_valid; eauto.
      assert (coqlib4.isSome (ThreadPool.lockRes st (b, ofs))) by assumption.
      (* instantiate(2:=ofs); instantiate(2:=b). *)
      unfold ThreadPool.lr_valid; simpl.
      unfold OrdinalPool.lr_valid; simpl.
      instantiate(1:=b); instantiate(1:=ofs).
      simpl in *; match_case; try inv H1; eauto.
    + rewrite ThreadPool.gsolockResUpdLock,
      ThreadPool.gsoThreadLPool; auto; intros.
      match_case; auto; intros.
      exploit @lockRes_valid; eauto.
      rewrite Heqo.
      intros HH; apply HH in H.
      assert ((b, ofs0) <> laddr). {
        destruct (addressFiniteMap.AMap.E.eq_dec (b,ofs0) laddr); auto.
        subst. rewrite H in lockRes_valid0; inv lockRes_valid0. }
      rewrite ThreadPool.gsolockResUpdLock, ThreadPool.gsoThreadLPool; auto.

      Unshelve.
      all: auto.
Qed.

Lemma invariant_update_thread:
  forall Sem (st st': @ThreadPool.t dryResources Sem OrdinalPool.OrdinalThreadPool) h c th_perm
    (Hcnt:ThreadPool.containsThread st h),
    st' = ThreadPool.updThread Hcnt c th_perm ->
    invariant st ->
    forall (no_race_thr0: forall j (cntj : ThreadPool.containsThread st j),
          (j <> h) ->
          permMapsDisjoint2 th_perm (ThreadPool.getThreadR cntj))
      (no_race2: forall laddr0 rmap,
          ThreadPool.lockRes st laddr0 = Some rmap ->
          permMapsDisjoint2 th_perm rmap)
      (thread_date_lock_coh1: permMapCoherence (fst th_perm) (snd th_perm))
      (thread_date_lock_coh4: forall i (cnti : ThreadPool.containsThread st i),
          i <> h ->
          permMapCoherence (fst th_perm) (snd (ThreadPool.getThreadR cnti)) /\
          permMapCoherence (fst (ThreadPool.getThreadR cnti)) (snd th_perm))
      (thread_date_lock_coh6: forall laddr0 rmap,
          ThreadPool.lockRes st laddr0 = Some rmap ->
          permMapCoherence (fst rmap) (snd th_perm) /\
          permMapCoherence (fst th_perm) (snd rmap)),
      invariant st'.
Proof.
  intros * ? Hinv **. constructor.
  - intros * ?.
    destruct (Nat.eq_dec i h);
      destruct (Nat.eq_dec j h); subst; rewrite_getupd.
    + contradict Hneq; reflexivity.
    + rewrite_getupd. auto.
    + apply permMapsDisjoint2_comm; auto.
    + eapply no_race_thr; eauto.
  - intros * ?. subst st'. repeat rewrite ThreadPool.gsoThreadLPool.
    apply Hinv; assumption.
  - intros *.  subst st'. repeat rewrite ThreadPool.gsoThreadLPool. 
    destruct (Nat.eq_dec i h);
      subst; rewrite_getupd; intros.
    + eauto.
    + eapply no_race; eauto.
  - intros *; split; intros *.
    + destruct (Nat.eq_dec i h);
        destruct (Nat.eq_dec j h); subst; intros; rewrite_getupd.
      * assumption.
      * apply thread_date_lock_coh4; auto.
      * apply thread_date_lock_coh4; auto.
      * exploit @thread_data_lock_coh; eauto. intros [HH ?].
        apply HH.
    + subst st'. repeat rewrite ThreadPool.gsoThreadLPool.
      destruct (Nat.eq_dec i h);
        subst; rewrite_getupd; intros.
      * eapply thread_date_lock_coh6; eauto.
      * eapply Hinv; eauto.
  - intros *; split; intros *; revert Hres.
    + destruct (Nat.eq_dec j h); subst; rewrite_getupd; intros.
      * eapply thread_date_lock_coh6; eauto.
      * exploit @locks_data_lock_coh; eauto. intros [HH ?].
        apply HH.
    + subst; rewrite_getupd; intros.
      eapply Hinv; eauto.
  - hnf; intros; subst; rewrite_getupd.
    eapply Hinv.
    
    Unshelve.
    all: auto.
Qed.

Lemma invariant_updateLock:
  forall Sem (st st': @ThreadPool.t dryResources Sem OrdinalThreadPool)
         laddr lock_perm,
    st' =
    ThreadPool.updLockSet st laddr lock_perm ->
    invariant st ->
    forall (no_race_lr: forall (laddr': address) (rmap : lock_info),
               laddr' <> laddr ->
               ThreadPool.lockRes st laddr' = Some rmap -> permMapsDisjoint2 lock_perm rmap)
           (no_race3: forall i (cnti : ThreadPool.containsThread st i),
               permMapsDisjoint2 (ThreadPool.getThreadR cnti) lock_perm)
           (thread_date_lock_coh5: forall i (cnti : ThreadPool.containsThread st i),
               permMapCoherence (fst (ThreadPool.getThreadR cnti)) (snd lock_perm) /\
               permMapCoherence (fst lock_perm) (snd (ThreadPool.getThreadR cnti)))
           (locks_data_lock_coh1: permMapCoherence (fst lock_perm) (snd lock_perm))
           (locks_data_lock_coh2: forall laddr0 rmap,
               laddr0 <> laddr -> ThreadPool.lockRes st laddr0 = Some rmap ->
               permMapCoherence (fst rmap) (snd lock_perm) /\
               permMapCoherence (fst lock_perm) (snd rmap))
           (lockRes_valid: forall ofs0 : Z, snd laddr < ofs0 < (snd laddr) + LKSIZE ->
                                            lockRes st (fst laddr, ofs0) = None)
           (lockRes_valid2: forall ofs0 : Z, ofs0 < snd laddr < ofs0 + LKSIZE ->
                                             lockRes st (fst laddr, ofs0) = None),
      invariant st'.
Proof.
  intros * ? Hinv **. constructor.
  - intros * ?. subst; rewrite_getupd.
    eapply Hinv; eauto.
  - intros * ?.
    destruct (addressFiniteMap.AMap.E.eq_dec laddr1 laddr);
      destruct (addressFiniteMap.AMap.E.eq_dec laddr2 laddr); subst;
        rewrite_getupd; intros.
    + contradict Hneq; auto.
    + inv Hres1. eapply no_race_lr0; eauto.
    + inv Hres2. eapply permMapsDisjoint2_comm, no_race_lr0; eauto.
    + eapply no_race_lr; try eapply Hneq; eauto.
  - intros *.
    destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
      subst; rewrite_getupd; intros.
    + inv Hres; eauto.
    + eapply no_race in Hres; eauto.
  - intros *; split; intros *.
    + subst; intros; rewrite_getupd.
      eapply thread_data_lock_coh in Hinv as [Hinv _]; eauto.
    + destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
        subst; rewrite_getupd; intros.
      * inv H; eapply thread_date_lock_coh5.
      * eapply thread_data_lock_coh in Hinv as [_ Hinv]; eauto.
  - intros *; split; intros *; revert Hres.
    + destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
        subst; rewrite_getupd; intros.
      * inv Hres. eapply thread_date_lock_coh5. 
      * eapply locks_data_lock_coh in Hinv as [Hinv _]; eauto.
    + destruct (addressFiniteMap.AMap.E.eq_dec laddr0 laddr);
        destruct (addressFiniteMap.AMap.E.eq_dec laddr' laddr);
        subst; rewrite_getupd; intros.
      * inv Hres; inv H; eauto.
      * inv Hres; eapply locks_data_lock_coh2; eauto.
      * inv H; eapply locks_data_lock_coh2; eauto.
      * pose proof (locks_data_lock_coh _ Hinv _ _ Hres).
        destruct H0. specialize (H1 _ _ H). auto.
  - intros ??. 
    destruct (addressFiniteMap.AMap.E.eq_dec (b,ofs) laddr); subst.
    + match_case; simpl in *; eauto.
      intros.
      rewrite gsolockResUpdLock; auto.
      intros HH; inv HH; omega.
    + rewrite ThreadPool.gsolockResUpdLock; auto; intros.
      match_case; auto; intros.
      
      exploit (@lockRes_valid _ _ _ Hinv b ofs) ; eauto.
      rewrite Heqo.
      dup H as H'.
      intros HH; apply HH in H.
      destruct (addressFiniteMap.AMap.E.eq_dec (b,ofs0) laddr);
        swap 1 2.
      * rewrite ThreadPool.gsolockResUpdLock; auto.
      * subst.
        eapply neq_prod in n.
        2: exact Classical_Prop.classic.
        destruct n; try congruence.
        destruct H0 as [_ H0].
        rewrite ThreadPool.gsolockResUpdLock; auto.
        exploit lockRes_valid2; eauto; simpl.
        simpl in *; intros HH'; rewrite HH' in Heqo;
          congruence.
        

        
        Unshelve.
        all: auto.
Qed.



Section SimulationTactics.
  Context {CC_correct: CompCert_correctness}
          {Args: ThreadSimulationArguments}.
  
  (*Module MyConcurMatch := ConcurMatch CC_correct Args.
  Export MyConcurMatch. *)
  
  (* Export MyThreadSimulationDefinitions. *)
  Import HybridMachineSig.
  Import DryHybridMachine.
  Import self_simulation.
  Import OrdinalPool.
  
  Existing Instance OrdinalPool.OrdinalThreadPool.
  Existing Instance HybridMachineSig.HybridCoarseMachine.DilMem.
  
  Notation thread_perms st i cnt:= (fst (@getThreadR _ _ st i cnt)).
  Notation lock_perms st i cnt:= (snd (@getThreadR  _ _ st i cnt)).
  
  (*+ tactics to push 
         mem_compat
         forward (in diagrams) *)
  
  Lemma mem_compatible_fullThreadUpdate:
    forall Sem Tp m st st' st'' l lock_info
      i (cnt:ThreadPool.containsThread st i) c res,
      @mem_compatible Sem Tp st m ->
      permMapLt_pair res (getMaxPerm m) ->
      permMapLt_pair lock_info (getMaxPerm m) ->
      Mem.valid_block m (fst l) ->
      st'' = ThreadPool.updLockSet st' l lock_info ->
      st' = ThreadPool.updThread cnt c res ->
      @mem_compatible Sem Tp st'' m.
  Proof.
    intros.
    eapply mem_compatible_updLock; eauto. clear H1 H2 H3.
    eapply mem_compatible_updthread; eauto.
  Qed.
  Lemma mem_compatible_fullAddThread:
    forall Sem Tp m st st' st'' c arg f_ptr
      i (cnt:ThreadPool.containsThread st i) new_th_res res,
      @mem_compatible Sem Tp st m ->
      permMapLt_pair res (getMaxPerm m) ->
      permMapLt_pair new_th_res (getMaxPerm m) ->
      st'' = ThreadPool.addThread st' f_ptr arg new_th_res ->
      st' = ThreadPool.updThread cnt c res ->
      @mem_compatible Sem Tp st'' m.
  Proof.
    intros.
    eapply mem_compatible_addThread; eauto. clear H1 H2.
    eapply mem_compatible_updthread; eauto.
  Qed.
  Lemma mem_compatible_fullThreadUpdate_join1:
    forall {Sem Tp} st c m st' st'' b ofs th_perm lock_perm
      i (cnt:ThreadPool.containsThread st i) ,
      @mem_compatible Sem Tp st m ->
      permMapJoin_pair th_perm lock_perm (ThreadPool.getThreadR cnt) ->
      Mem.valid_block m b ->
      st'' = ThreadPool.updLockSet st' (b, ofs) lock_perm ->
      st' = ThreadPool.updThread cnt c th_perm ->
      @mem_compatible Sem Tp st'' m.
  Proof.
    intros. eapply mem_compatible_fullThreadUpdate; simpl; eauto.
    - apply (permMapLt_pair_trans211 _ (ThreadPool.getThreadR cnt)).
      * eapply permMapJoin_lt_pair1; eassumption.
      * eapply H.
    - apply (permMapLt_pair_trans211 _ (ThreadPool.getThreadR cnt)).
      * eapply permMapJoin_lt_pair2; eassumption.
      * eapply H.
    - simpl; auto.
  Qed.
  
  Definition fullThreadUpdate {sem} st i cnt th_st new_perms adr  :=
    (updLockSet
       (@updThread dryResources sem i st cnt th_st (fst new_perms)) adr (snd new_perms)).
  Definition fullThUpd_comp {sem} st i cnt th_st (angel: virtue) adr  :=
    @fullThreadUpdate
      sem st i cnt th_st
      (computeMap_pair (getThreadR cnt) (virtueThread angel), virtueLP angel) adr.
  
  Lemma store_cmpt:
    forall Sem Tp st chunk b ofs v m m' p Hlt ,
      Mem.store chunk (@restrPermMap p m Hlt ) b ofs v = Some m' ->
      @mem_compatible Sem Tp st m -> 
      @mem_compatible Sem Tp st m'.
  Proof.
    intros. 
    eapply mem_compat_Max in H0;
      try (symmetry; etransitivity).
    - eassumption.
    - symmetry; eapply store_max_equiv; eassumption.
    - apply restr_Max_equiv.
    - eapply Mem.nextblock_store; eassumption.
    - reflexivity.
  Qed.


  (*Invariant lemmas*)
  

  (* Move this one where the other perm_coh + Freeable lemma is*)
  Lemma perm_coh_None_not_Free:
    forall b, b <> Some Freeable -> perm_coh None b.
  Proof. intros. hnf; repeat (match_case; eauto). Qed.


  Lemma invariant_empty_updLockSet:
    forall hb (st:@ThreadPool (Some hb)) b ofs st',
      invariant st ->
      (forall ofs0 : Z, ofs < ofs0 < ofs + LKSIZE ->
                        ThreadPool.lockRes st (b, ofs0) = None) ->
      (forall ofs0 : Z, ofs0 < ofs < ofs0 + LKSIZE ->
                        ThreadPool.lockRes st (b, ofs0) = None) ->
      st' = ThreadPool.updLockSet st (b, ofs) (pair0 empty_map) ->
      (*coqlib4.isSome (ThreadPool.lockRes st (b, ofs)) ->*)
      invariant st'.
  Proof.
    intros * Hinv ???. eapply invariant_updateLock; simpl in *; eauto.
    - split; eapply empty_disjoint'.
    - intros; eapply permMapsDisjoint2_comm.
      split; eapply empty_disjoint'.
    - simpl. split; try eapply permCoh_empty'.
      + intros ??.
        rewrite empty_is_empty; simpl.
        eapply perm_coh_None_not_Free.
        eapply perm_coh_not_freeable.
        eapply thread_data_lock_coh in Hinv as
            [HH _]; eauto. eapply HH. 
    - eapply permCoh_empty'.
    - simpl. split; try eapply permCoh_empty'.
      intros ??. rewrite empty_is_empty; simpl.
      eapply perm_coh_None_not_Free.
      eapply perm_coh_not_freeable.
      eapply locks_data_lock_coh in Hinv as
          [_ HH]; eauto. eapply HH; eauto.

      Unshelve.
      all: eauto.
  Qed.
  
  Lemma invariant_empty_updLockSet_upd:
    forall hb (st:ThreadPool (Some hb)) b ofs st',
      invariant st ->
      st' = ThreadPool.updLockSet st (b, ofs) (pair0 empty_map) ->
      coqlib4.isSome (ThreadPool.lockRes st (b, ofs)) ->
      invariant st'.
  Proof.
    intros * Hinv ??.
    eapply invariant_empty_updLockSet; eauto.
    - simpl. eapply lockRes_valid in Hinv.
      specialize (Hinv b ofs); simpl in *.
      match_case in Hinv; try now inv H0.
    - simpl. eapply lockRes_valid in Hinv.
      intros. 
      specialize (Hinv b ofs0); simpl in *.
      destruct_lhs; auto.
      rewrite Hinv in H0; eauto. inv H0.
      
      Unshelve.
      all: eauto.
  Qed.
  
  Lemma invariant_update_join_rel:
    forall Sem (st st': @ThreadPool.t dryResources Sem OrdinalThreadPool)
           h laddr c lock_perm th_perm
           (Hcnt:ThreadPool.containsThread st h),
      coqlib4.isSome (ThreadPool.lockRes st laddr) ->
      st' =
      ThreadPool.updLockSet (ThreadPool.updThread Hcnt c th_perm) laddr lock_perm ->
      invariant st ->
      permMapJoin_pair th_perm lock_perm (getThreadR Hcnt) ->
      invariant st'.
  Proof.
    intros * ? ? Hinv Hjoin; eapply invariant_update; eauto.
    - intros ; eapply disjoint_lt_pair.
      eapply permMapJoin_lt_pair1; eauto.
      eapply Hinv; auto.
    - intros. eapply disjoint_lt_pair.
      eapply permMapJoin_lt_pair2; eauto.
      exploit no_race; eauto; intros HH; apply HH.
    - eapply join_disjoint_pair; eauto.
    - intros ; eapply disjoint_lt_pair.
      intros; eapply permMapJoin_lt_pair1; eauto.
      exploit no_race; eauto; intros HH; apply HH.
    - intros; eapply permMapsDisjoint2_comm,
              disjoint_lt_pair; eauto. 
      eapply permMapJoin_lt_pair2; eauto.
      eapply Hinv; auto.
    - eapply permMapCoherence_Lt.
      + exploit thread_data_lock_coh; eauto.
        intros [HH ?]. eapply HH.
      + eapply permMapJoin_lt.
        eapply Hjoin.
      + eapply permMapJoin_lt.
        eapply Hjoin.
    - eapply permMapCoherence_Lt.
      + exploit thread_data_lock_coh; eauto.
        intros [HH ?]. eapply HH.
      + eapply permMapJoin_lt.
        eapply permMapJoin_comm, Hjoin.
      + eapply permMapJoin_lt; eapply Hjoin.
    - eapply permMapCoherence_Lt.
      + exploit thread_data_lock_coh; eauto.
        intros [HH ?]. eapply HH.
      + eapply permMapJoin_lt, Hjoin.
      + eapply permMapJoin_lt; eapply permMapJoin_comm, Hjoin.
    - split; eapply permMapCoherence_Lt.
      3,5: reflexivity.
      1,3: exploit thread_data_lock_coh; try apply Hinv;
        intros [HH ?]; eapply HH.
      all: eapply permMapJoin_lt, Hjoin.
    - split; eapply permMapCoherence_Lt.
      2,6: reflexivity.
      1,3: exploit thread_data_lock_coh; try apply Hinv;
        intros [HH ?]; eapply HH.
      all: eapply permMapJoin_lt,permMapJoin_comm, Hjoin.
    - split; eapply permMapCoherence_Lt.
      2,6: reflexivity.
      1: exploit thread_data_lock_coh; eauto; intros [? HH];
        eapply HH; eauto.
      2: exploit locks_data_lock_coh; try eassumption;
        intros [HH ?]; eapply HH.
      all: eapply permMapJoin_lt, Hjoin.
    - eapply permMapCoherence_Lt.
      2,3: eapply permMapJoin_lt, permMapJoin_comm, Hjoin.
      exploit thread_data_lock_coh; eauto; intros [HH ?]; auto.
      eapply HH.
    - intros; split; eapply permMapCoherence_Lt.
      2,6: reflexivity.
      2,4: eapply permMapJoin_lt, permMapJoin_comm, Hjoin.
      2:{  exploit locks_data_lock_coh; eauto.
           intros [HH ?]; eapply HH. }
      {  exploit thread_data_lock_coh; eauto.
         intros [? HH]. eapply HH; eauto. }
  Qed.
  
  Lemma invariant_update_join_acq:
    forall Sem (st st': @ThreadPool.t dryResources Sem OrdinalThreadPool)
           h laddr c lock_perm th_perm
           (Hcnt:ThreadPool.containsThread st h),
      ThreadPool.lockRes st laddr = Some lock_perm ->
      st' =
      ThreadPool.updLockSet (ThreadPool.updThread Hcnt c th_perm) laddr
                            (empty_map, empty_map) ->
      invariant st ->
      permMapJoin_pair lock_perm (getThreadR Hcnt) th_perm ->
      invariant st'.
  Proof.
    intros * ? ? Hinv Hjoin; eapply invariant_update; eauto.
    - intros.
  (* This is almost right: 
           IF Nonempty + Writable = Freeable
           we know: 
              disjoin Nonempty Nonempty    
              disjoin Writable Nonempty
           but it's not true that:
              disjoin Freeable Nonempty *)
  (** * SOLUTION add the invariant of st1'
               to the lemmas statement.     
               with  an extra safety step, we know the second 
           state satisfies the invariant.
           Then to establish invariant for the target, 
           use the Mem.inject of each thread to move it 
           back to the source, then use the relations 
           in the source!
   *)
  Admitted.
  
        Lemma contains_addThread_neq:
          forall res Sem st st' f_ptr arg th_perm i,
            st' = addThread st f_ptr arg th_perm ->
            @containsThread res Sem st' i ->
            i <> latestThread st ->
            containsThread st i.
        Proof.
          unfold containsThread.
          intros; subst st'.
          simpl in H0. simpl.
          unfold latestThread in H1.
          remember ( pos.n (num_threads st))  as K.
          clear - H0 H1. 
          pose proof (@ssrnat.leP (S i) (S K)) ; eauto.
          rewrite H0 in H.
          pose proof (@ssrnat.leP (S i) (K)) ; eauto.
          destruct H2; eauto.
          exfalso; apply n. inv H. omega.
        Qed.          
        Lemma contains_addThread_disj:
          forall res Sem st f_ptr arg th_perm i,
            @containsThread res Sem (addThread st f_ptr arg th_perm) i ->
            containsThread st i \/ i = latestThread st.
        Proof.
          intros.
          destruct (Nat.eq_dec i (latestThread st)); eauto.
          exploit contains_addThread_neq; eauto.
        Qed.
      Lemma invariant_add_thread_only:
        forall Sem (st st': @ThreadPool.t dryResources Sem OrdinalPool.OrdinalThreadPool) th_perm
          f_ptr arg,
          st' = ThreadPool.addThread st f_ptr arg th_perm ->
          invariant st ->
          forall (no_race_thr0: forall j (cntj : ThreadPool.containsThread st j),
                permMapsDisjoint2 th_perm (ThreadPool.getThreadR cntj))
            (no_race2: forall laddr0 rmap,
                ThreadPool.lockRes st laddr0 = Some rmap ->
                permMapsDisjoint2 th_perm rmap)
            (thread_date_lock_coh1: permMapCoherence (fst th_perm) (snd th_perm))
            (thread_date_lock_coh4: forall i (cnti : ThreadPool.containsThread st i),
                permMapCoherence (fst th_perm) (snd (ThreadPool.getThreadR cnti)) /\
                permMapCoherence (fst (ThreadPool.getThreadR cnti)) (snd th_perm))
            (thread_date_lock_coh6: forall laddr0 rmap,
                ThreadPool.lockRes st laddr0 = Some rmap ->
                permMapCoherence (fst rmap) (snd th_perm) /\
                permMapCoherence (fst th_perm) (snd rmap)),
            invariant st'.
      Proof.
        simpl; intros * Hst Hinv **.
        
        econstructor; simpl; subst st'.

        
        Ltac addThread_rewrite_getR cnti:=
          let cnti0:= fresh "cnti0" in
          let His_last:= fresh "His_last"  in
          eapply contains_addThread_disj in cnti as cnti0;
          destruct cnti0 as [cnti0 | His_last];
          [ repeat rewrite (gsoAddRes cnti0 cnti) in * |
            repeat rewrite gssAddRes in * by assumption ].
        - intros. addThread_rewrite_getR cnti;
            addThread_rewrite_getR cntj; eauto.
          + eapply Hinv; auto.
          + apply permMapsDisjoint2_comm; eauto.
          + subst; contradict Hneq; reflexivity.
        - intros *; do 2 rewrite gsoAddLPool; eapply Hinv.
        - intros *; rewrite gsoAddLPool.
          addThread_rewrite_getR cnti; eauto.
          + intros; exploit no_race; simpl; eauto.
        - split.
          + intros *. addThread_rewrite_getR cnti;
                        addThread_rewrite_getR cntj; eauto.
            * exploit thread_data_lock_coh; eauto; intros [HH _].
              eapply HH.
            * eapply thread_date_lock_coh4.
            * erewrite gssAddRes by assumption. eapply thread_date_lock_coh4.
          + intros *. rewrite gsoAddLPool. addThread_rewrite_getR cnti.
            * eapply Hinv.
            * intros; eapply thread_date_lock_coh6; eauto.
        - intros *; rewrite gsoAddLPool; split.
          + intros *. addThread_rewrite_getR cntj; eauto.
            * exploit locks_data_lock_coh; eauto; intros [HH _].
              eapply HH.
            * eapply thread_date_lock_coh6; eauto.
          + intros *. rewrite gsoAddLPool. eapply Hinv; simpl; eauto.
        - intros ? ?; match_case; auto.
          intros. rewrite gsoAddLPool in *.
          exploit lockRes_valid; try eapply Hinv; simpl.
          rewrite Heqo. eauto.
      Qed.
    Lemma invariant_add_thread:
            forall Sem (st st': @ThreadPool.t dryResources Sem OrdinalThreadPool)
              h c old_th_perm  new_th_perm f_ptr arg
              (Hcnt:ThreadPool.containsThread st h),
      st' = ThreadPool.addThread
              (ThreadPool.updThread Hcnt c old_th_perm)
              f_ptr arg new_th_perm ->
      invariant st ->
      permMapJoin_pair new_th_perm old_th_perm  (getThreadR Hcnt) ->
      invariant st'.
    Proof.
      intros * Hst1' Hinv Hjoin.
      assert (Hinv':invariant (ThreadPool.updThread Hcnt c old_th_perm)).
      { simpl. eapply invariant_update_thread; eauto. 
        - simpl; eauto.
        - simpl; intros. eapply disjoint_lt_pair.
          + eapply permMapJoin_lt_pair2; eassumption.
          + eapply Hinv; auto.
        - intros. eapply disjoint_lt_pair.
          + eapply permMapJoin_lt_pair2; eassumption.
          + eapply no_race in H; simpl in *; eauto.
        - eapply permMapCoherence_Lt.
          + exploit thread_data_lock_coh; eauto.
            intros [HH ?]. eapply HH.
          + eapply permMapJoin_lt, permMapJoin_comm, Hjoin.
          + eapply permMapJoin_lt, permMapJoin_comm, Hjoin.
        - intros; split.
          + eapply permMapCoherence_Lt.
            * exploit thread_data_lock_coh; eauto.
              intros [HH ?]. eapply HH.
            * eapply permMapJoin_lt, permMapJoin_comm, Hjoin.
            * reflexivity.
          + eapply permMapCoherence_Lt.
            * exploit thread_data_lock_coh; eauto.
              intros [HH ?]. eapply HH.
            * reflexivity.
            * eapply permMapJoin_lt, permMapJoin_comm, Hjoin.
        - intros; split.
          + eapply permMapCoherence_Lt.
            2:{ reflexivity. }
            * exploit thread_data_lock_coh; eauto.
              intros [HH ?]. eapply H0; eauto.
            * eapply permMapJoin_lt, permMapJoin_comm, Hjoin.
          + eapply permMapCoherence_Lt.
            3:{ reflexivity. }
            * exploit locks_data_lock_coh; eauto.
              intros [HH ?]. eapply HH.
            * eapply permMapJoin_lt, permMapJoin_comm, Hjoin. }
      eapply invariant_add_thread_only; try eexact Hinv'.
      - subst st'; simpl; reflexivity.
      - intros. destruct (Nat.eq_dec h j).
        + subst. rewrite ThreadPool.gssThreadRes.
          eapply join_disjoint_pair; eauto.
        + subst. unshelve erewrite ThreadPool.gsoThreadRes; eauto.
          simpl; intros. eapply disjoint_lt_pair.
          * eapply permMapJoin_lt_pair1; eassumption.
          * eapply Hinv; auto.
      - intros *. rewrite ThreadPool.gsoThreadLPool; intros.
        eapply disjoint_lt_pair.
          + eapply permMapJoin_lt_pair1; eassumption.
          + eapply no_race in H; simpl in *; eauto.
      - eapply permMapCoherence_Lt.
        * exploit thread_data_lock_coh; try eapply Hinv.
          intros [HH ?]. eapply HH.
        * eapply permMapJoin_lt, Hjoin.
        * eapply permMapJoin_lt, Hjoin.
      - intros i ?. destruct (Nat.eq_dec h i).
        + subst. rewrite ThreadPool.gssThreadRes.
          split; eapply permMapCoherence_Lt;
            try now eapply permMapJoin_lt, Hjoin.
          2,4: try now eapply permMapJoin_lt, permMapJoin_comm, Hjoin.
          * exploit thread_data_lock_coh; try eapply Hinv.
            intros [HH ?]. eapply HH.
          * exploit thread_data_lock_coh; try eapply Hinv.
            intros [HH ?]. eapply HH.
        + subst. unshelve erewrite ThreadPool.gsoThreadRes; eauto.
          split; eapply permMapCoherence_Lt;
            try now eapply permMapJoin_lt, Hjoin.
          2,4: reflexivity.
          * exploit thread_data_lock_coh; try eapply Hinv.
            intros [HH ?]. eapply HH.
          * exploit thread_data_lock_coh; try eapply Hinv.
            intros [HH ?]. eapply HH.
      - intros *. rewrite ThreadPool.gsoThreadLPool; intros.
        split; eapply permMapCoherence_Lt;
          try now eapply permMapJoin_lt, Hjoin.
          2,4: reflexivity.
          * exploit thread_data_lock_coh; try eapply Hinv.
            intros [? HH]. eapply HH; eauto.
          * exploit locks_data_lock_coh; try eapply Hinv; eauto.
            intros [HH ?]. eapply HH.
    Qed.
    
  
    Lemma tree_map_inject_over_mem_structure:
            forall {A} m1 m2 mu virt ,
            (getMaxPerm m1) = (getMaxPerm m2) ->
            tree_map_inject_over_mem(A:=A) m1 mu virt =
            tree_map_inject_over_mem m2 mu virt.
          Proof.
            unfold tree_map_inject_over_mem.
            intros * ->; auto.
          Qed.
          
    Lemma permMapJoin_pair_inject_spawn_simpl:
      forall mu m1 m2
        virtue1 virtue_new1 th_perms1 th_perms2,
        sub_map virtue1 (snd (getMaxPerm m1)) ->
        sub_map virtue_new1 (snd (getMaxPerm m1)) ->
        let ThreadPerm1 := computeMap th_perms1 virtue1 in
        let newThreadPerm1 := computeMap empty_map virtue_new1 in
        permMapJoin newThreadPerm1 ThreadPerm1 th_perms1 ->
        forall 
          (Hlt_th1 : permMapLt (th_perms1) (getMaxPerm m1))
          (Hlt_th2 : permMapLt (th_perms2) (getMaxPerm m2)),
          Mem.inject mu (restrPermMap Hlt_th1) (restrPermMap Hlt_th2) ->
          injects_dmap mu virtue1   ->
          injects_dmap mu virtue_new1   ->
          let virtue2 := (tree_map_inject_over_mem m2 mu) virtue1 in
          let virtue_new2 := (tree_map_inject_over_mem m2 mu) virtue_new1 in
          let ThreadPerm2 :=  computeMap th_perms2 virtue2 in
          let newThreadPerm2 := computeMap (empty_map) virtue_new2 in
          permMapJoin newThreadPerm2 ThreadPerm2 th_perms2.
    Proof.
      intros. subst_set.
      assert (Hmax2: getMaxPerm m2 = getMaxPerm (restrPermMap Hlt_th2)).
      { symmetry; apply getMax_restr_eq. }
      assert (Hmax1: getMaxPerm m1 = getMaxPerm (restrPermMap Hlt_th1)).
      { symmetry; apply getMax_restr_eq. }
      
      apply permMapJoin_comm, compute_map_join_fwd.
      eapply delta_map_join_inject.
      4: erewrite tree_map_inject_over_mem_structure;
          try eapply inject_perm_perfect_image_dmap; eauto. 
      - eapply H2.
      - apply sub_map_filtered.
        erewrite getMax_restr_eq; eassumption.
      - erewrite getMax_restr_eq; apply Hlt_th1.
      - eapply sub_map_implication_dmap.
        rewrite <- Hmax1; auto.
      - eapply perm_perfect_image_computeMap.
        + intros ? **. rewrite empty_is_empty in *. inv H8.
        + apply perm_perfect_imageempty_map. 
        + erewrite tree_map_inject_over_mem_structure;
            try eapply inject_perm_perfect_image_dmap; eauto.
          eapply sub_map_implication_dmap.
        rewrite <- Hmax1; auto.
          
      - eapply inject_almost_perfect in H2.
        eapply almost_perfect_image_proper; try eassumption;
        eauto; try reflexivity.
        1,2: symmetry; eapply getCur_restr.
      - eapply compute_map_join_bkw, permMapJoin_comm; eauto.
    Qed.
    Lemma permMapJoin_pair_inject_spawn:
      forall mu m1 m2
        virtue1 virtue_new1 th_perms1 th_perms2,
        sub_map_pair virtue1 (snd (getMaxPerm m1)) ->
        sub_map_pair virtue_new1 (snd (getMaxPerm m1)) ->
        let ThreadPerm1 := computeMap_pair th_perms1 virtue1 in
        let newThreadPerm1 := computeMap_pair (pair0 empty_map) virtue_new1 in
        permMapJoin_pair newThreadPerm1 ThreadPerm1 th_perms1 ->
        forall 
          (Hlt_th1 : permMapLt (fst th_perms1) (getMaxPerm m1))
          (Hlt_th2 : permMapLt (fst th_perms2) (getMaxPerm m2))
          (Hlt_lk1 : permMapLt (snd th_perms1) (getMaxPerm m1))
          (Hlt_lk2 : permMapLt (snd th_perms2) (getMaxPerm m2)),
          Mem.inject mu (restrPermMap Hlt_th1) (restrPermMap Hlt_th2) ->
          Mem.inject mu (restrPermMap Hlt_lk1) (restrPermMap Hlt_lk2) ->
          injects_dmap_pair mu virtue1   ->
          injects_dmap_pair mu virtue_new1   ->
          let virtue2 := virtueThread_inject m2 mu virtue1 in
          let virtue_new2 := virtueThread_inject m2 mu virtue_new1 in
          let ThreadPerm2 :=  computeMap_pair th_perms2 virtue2 in
          let newThreadPerm2 := computeMap_pair (pair0 empty_map) virtue_new2 in
          permMapJoin_pair newThreadPerm2 ThreadPerm2 th_perms2.
    Proof.
      simpl; intros; split; simpl.
      - eapply permMapJoin_pair_inject_spawn_simpl; eauto.
        + eapply H.
        + eapply H0.
        + eapply H1.
        + eapply H4.
        + eapply H5.
      - eapply permMapJoin_pair_inject_spawn_simpl; eauto.
        + eapply H.
        + eapply H0.
        + eapply H1.
        + eapply H4.
        + eapply H5.
    Qed.
  
      Lemma permMapsDisjoint_setPermBlock:
        forall b ofs p P1 size P2,
          0 < size ->
        permMapsDisjoint P1 P2 ->
        (forall ofs0 : Z,
            ofs <= ofs0 < ofs + size ->
            exists pu, perm_union p 
                         (P2 !! b ofs0) = Some pu) ->
        permMapsDisjoint
        (setPermBlock p b ofs P1 ((Z.to_nat size))) P2.
      Proof.
        intros ** b ofs0.
        assert (Hnneg: 0 <= size0) by omega.        
        destruct (peq b0 b).
        - subst.
          destruct (Intv.In_dec ofs0 (ofs, ofs + size0)).
          + rewrite setPermBlock_same; eauto.
            rewrite Z2Nat.id; eauto.
          + rewrite setPermBlock_other_1; eauto.
            rewrite Z2Nat.id; eauto.
            apply Intv.range_notin in n; simpl in n; eauto.
            simpl. omega.
        - rewrite setPermBlock_other_2; eauto.
      Qed.
      Lemma permMapsDisjoint_setPermBlock_pair:
        forall b ofs p P1 size P2,
          0 < size ->
        permMapsDisjoint2 P1 P2 ->
        (forall ofs0 : Z,
            ofs <= ofs0 < ofs + size ->
            exists pu, perm_union (fst p)
                         ((fst P2) !! b ofs0) = Some pu) ->
        (forall ofs0 : Z,
            ofs <= ofs0 < ofs + size ->
            exists pu, perm_union (snd p)
                         ((snd P2) !! b ofs0) = Some pu) ->
        permMapsDisjoint2
        (setPermBlock_pair b ofs p P1 (pair0 (Z.to_nat size))) P2.
      Proof.
        intros; split; simpl; eapply permMapsDisjoint_setPermBlock;
          try eapply H0; eauto.
      Qed.
      Lemma permMapCoherence_setPermBlock1:
        forall p1 b ofs P1 P2 size,
          0 < size ->
        (forall ofs0 : Z,
            ofs <= ofs0 < ofs + size ->
            Mem.perm_order'' (P1 !! b ofs0) p1) -> 
        permMapCoherence P1 P2 ->
        permMapCoherence
          (setPermBlock p1 b ofs P1 (Z.to_nat size)) P2.
      Proof.
        intros ** b' ofs0.
        assert (Hnneg: 0 <= size0) by omega.        
        destruct (peq b b').
        - subst; destruct (Intv.In_dec ofs0 (ofs, ofs + (size0))).
          + rewrite setPermBlock_same; eauto.
            2: erewrite Z2Nat.id; eauto.
            eapply perm_coh_lower; try eapply H1; eauto.
            apply po_refl.
          + apply Intv.range_notin in n; simpl in n.
            * repeat rewrite setPermBlock_other_1; eauto.
              erewrite Z2Nat.id; eauto.
            * simpl; omega.
        - repeat rewrite setPermBlock_other_2; eauto.
      Qed.
      Lemma permMapCoherence_setPermBlock2:
        forall p2 b ofs P1 P2 size,
          0 < size ->
        (forall ofs0 : Z,
            ofs <= ofs0 < ofs + size ->
             perm_coh (P1 !! b ofs0) p2) -> 
        permMapCoherence P1 P2 ->
        permMapCoherence P1
          (setPermBlock p2 b ofs P2 (Z.to_nat size)).
      Proof.
        intros ** b' ofs0.
        assert (Hnneg: 0 <= size0) by omega.        
        destruct (peq b b').
        - subst; destruct (Intv.In_dec ofs0 (ofs, ofs + (size0))).
          + rewrite setPermBlock_same; eauto.
            erewrite Z2Nat.id; eauto.
          + apply Intv.range_notin in n; simpl in n.
            * repeat rewrite setPermBlock_other_1; eauto.
              erewrite Z2Nat.id; eauto.
            * simpl; omega.
        - repeat rewrite setPermBlock_other_2; eauto.
      Qed.
      Lemma permMapCoherence_setPermBlock_double:
        forall p1 p2 b ofs P1 P2 size,
          0 <  (size) ->
        permMapCoherence P1 P2 ->
        perm_coh p1 p2 ->
        permMapCoherence
          (setPermBlock p1 b ofs P1 (Z.to_nat size))
          (setPermBlock p2 b ofs P2 (Z.to_nat size)).
      Proof.
        intros ** b' ofs0.
        assert (Hnneg: 0 <= size0) by omega.        
        destruct (peq b b').
        - subst; destruct (Intv.In_dec ofs0 (ofs, ofs + (size0))).
          + repeat rewrite setPermBlock_same; eauto.
            1,2: erewrite Z2Nat.id; eauto.
          + apply Intv.range_notin in n; simpl in n.
            * repeat rewrite setPermBlock_other_1; eauto.
              1,2: erewrite Z2Nat.id; eauto.
            * simpl; omega.
        - repeat rewrite setPermBlock_other_2; eauto.
      Qed.
      Lemma invariant_makelock:
    forall (hb1 hb2:nat) c st1 b1 ofs cnt perms,
      @invariant _ (TP (Some hb2)) st1 ->
      set_new_mems b1 ofs (@getThreadR _ _ hb1 st1 cnt) LKSIZE_nat perms ->
      (forall ofs0 : Z, ofs <= ofs0 < ofs + LKSIZE ->
                        Mem.perm_order' ((thread_perms hb1 st1 cnt) !! b1 ofs0) Writable) ->
      @invariant _ (TP (Some hb2)) (@updThread _ (HybridSem (Some hb2))
                                               hb1 st1 cnt c perms).
      Proof.
        pose proof (LKSIZE_pos) as Hpos.
    intros * Hinv Hset Hrange. inv Hset.
    eapply invariant_update_thread; simpl; eauto; simpl.
    - intros **.
      eapply permMapsDisjoint_setPermBlock_pair; auto.
      + eapply Hinv; auto.
      + simpl; intros.
        exploit Hrange; eauto; intros.
        unshelve exploit @no_race_thr; simpl; try apply H; eauto.
        intros [HH1 _]. specialize (HH1 b1 ofs0).
        do 2 (match_case; eauto); simpl in *.
        match_case in HH1. inv H1.
      + simpl; intros.
        exploit Hrange; eauto; intros.
        unshelve exploit @thread_data_lock_coh; simpl; try apply H; eauto.
        intros [HH1 _]. specialize (HH1 _ cnt b1 ofs0).
        do 2 (match_case; eauto); simpl in *.
        1,2,3: hnf in HH1; repeat match_case in HH1; try inv H1.
    - intros **.
      eapply permMapsDisjoint_setPermBlock_pair;auto.
      + exploit @no_race; simpl; eauto.
      + simpl; intros.
        exploit Hrange; eauto; intros.
        unshelve exploit @no_race; simpl; try apply H; eauto.
        intros [HH1 _]. specialize (HH1 b1 ofs0).
        do 2 (match_case; eauto); simpl in *.
        unfold perm_union in HH1.
        repeat match_case in HH1; try inv H1.
      + simpl; intros.
        exploit Hrange; eauto; intros.
        unshelve exploit @locks_data_lock_coh; simpl; try apply H; eauto.
        intros [HH1 _]. specialize (HH1 _ cnt b1 ofs0).
        do 2 (match_case; eauto).
        1,2,3: hnf in HH1; repeat match_case in HH1; try inv H1.
    - eapply permMapCoherence_setPermBlock_double; eauto.
      + exploit @thread_data_lock_coh; eauto.
        intros [HH _]; eapply HH.
      + constructor.
    - intros; split.
      + eapply permMapCoherence_setPermBlock1; auto.
        * intros. eapply perm_order''_trans.  
          -- rewrite <- po_oo; eauto.
          -- constructor.
        * exploit @thread_data_lock_coh; simpl; try apply H; eauto.
          intros [HH1 _]. eapply HH1.
      + eapply permMapCoherence_setPermBlock2; auto.
        * intros; exploit Hrange; eauto.
          intros HH.
          unshelve exploit @no_race_thr; try eapply H; simpl; eauto.
          intros [Hjoin _]; specialize (Hjoin b1 ofs0).
          normal_hyp.
          hnf; repeat (match_case; eauto); simpl in H2.
          all: repeat (match_case in H2; try now inv HH).
        * exploit @thread_data_lock_coh; eauto.
          simpl; intros [HH _]; eauto.
    - intros; split.
      + eapply permMapCoherence_setPermBlock2; auto.
        * Lemma perm_coh_union_writable:
            forall x z,
            Mem.perm_order'' z (Some Writable) ->
            (exists pu,
              perm_union x z = Some pu) ->
            perm_coh x (Some Writable).
          Proof.
            intros * H1 [pu H2].
            unfold Mem.perm_order'', perm_union, perm_coh in *.
            repeat (match_case in H2; try now inv H1).
          Qed.
          intros; eapply perm_coh_union_writable; eauto.
          -- rewrite <- po_oo; eauto.
          -- eapply permMapsDisjoint_comm.
             exploit @no_race; simpl; eauto.
             intros [HH _]; simpl in HH; eauto.
        * exploit @thread_data_lock_coh; eauto; intros  [_ HH]; eauto.
          specialize (HH _ _ H). simpl in HH; eauto.
      + eapply permMapCoherence_setPermBlock1; auto.
        * intros. eapply perm_order''_trans.  
          -- rewrite <- po_oo; eauto.
          -- constructor.
        * exploit @locks_data_lock_coh; simpl; try apply H; eauto.
          intros [HH1 _]. eapply HH1.
      Qed.   
  
  (* END of invariant lemmas*)


  Lemma atx_injection Sem: 
    let CoreSem := sem_coresem Sem in
    forall (SelfSim: (self_simulation semC CoreSem))
           mu b1 b2 delt th_state1 th_state2 m1 m2 FUN ofs,
      mu b1 = Some (b2, delt) ->
      match_self (code_inject semC CoreSem SelfSim) mu th_state1 m1 th_state2 m2 ->
      semantics.at_external CoreSem th_state1 m1 =
      Some (FUN, (Vptr b1 ofs) :: nil) ->
      semantics.at_external CoreSem th_state2 m2 =
      Some (FUN, Vptr b2 (add ofs (repr delt)) :: nil).
  Proof.
    intros * Hinj Hmatch_self Hat_external.
    eapply ssim_preserves_atx in Hat_external as
        (args' & Hatx2 & Hval_inj); eauto.
    - (* unify arg's *)
      inv Hval_inj. inv H3. inv H1.
      rewrite Hinj in H2; inv H2.
      eauto.
  Qed.

  
  Lemma lock_update_mem_strict_load_inject:
    forall f b b' ofs delt perms1 perms2 m1 m2 m1' vl vs,
    forall (Hinj_b : f b = Some (b', delt))
           Hlt1 Hlt2
           (Hinj_lock: Mem.inject f (@restrPermMap perms1 m1 Hlt1)
                                  (@restrPermMap perms2 m2 Hlt2)),
      lock_update_mem_strict_load b ofs perms1 m1 m1' (Vint vl) (Vint vs) ->
      inject_lock' LKSIZE f b ofs m1 m2 ->
      exists m2',
        lock_update_mem_strict_load b' (ofs+ delt) perms2 m2 m2' (Vint vl) (Vint vs) /\
        Mem.inject f m1' m2'.
  Proof.
    intros. inv H.

    Print Instances Proper.
    rewrite <- (restr_proof_irr_equiv _ _ lock_mem_lt),
    (restr_proof_irr_equiv _ _ Hlt2)
      in Hinj_lock.
    assert (writable_lock b' (ofs + delt) perms2 m2).
    { eapply writable_lock_inject_restr; eauto. }

    
    eapply Mem.store_mapped_inject in Hstore; eauto.
    - destruct Hstore as (m2'&Hstore2&Hinj2).
      exists m2'; split; auto.
      unshelve econstructor; eauto.
      + match goal with
          |- context[?a + ?b + ?c]=>
          replace (a + b + c) with ((a + c) + b) by omega   
        end.
        eapply Mem.range_perm_inject; eauto.
      + eapply Mem.load_inject in Hload; eauto.
        * destruct Hload as (v2 & ? & HH).
          inv HH; eauto.
    - simpl.
      eapply mem_inject_equiv; 
        try (eapply setPermBlock_mem_inject; try eapply Hinj_lock);
        eauto.
      { subst m_writable_lock_1 lock_mem.
        etransitivity; [|eapply restrPermMap_idempotent].
        apply restrPermMap_equiv; try reflexivity.
        eapply setPermBlock_access_map_equiv; eauto.
        rewrite getCur_restr. reflexivity.
        econstructor; auto.  }
      { etransitivity; [|eapply restrPermMap_idempotent].
        apply restrPermMap_equiv; try reflexivity.
        eapply setPermBlock_access_map_equiv; eauto.
        simpl; rewrite getCur_restr. reflexivity.
        econstructor; auto. }
      
      Unshelve.
      all: unfold writable_lock in *;
        try rewrite getCur_restr;
        try rewrite getMax_restr;
        try assumption.
  Qed.

  
  Definition compat_restr {Sem tpool m} perms {st} Hlt Hcmpt:=
    @mem_compat_restrPermMap Sem tpool m perms st Hlt Hcmpt.
  (* Move to mem_equiv? *)
  Instance build_delta_content_equiv:
    Proper (Logic.eq ==> content_equiv ==>
                     Logic.eq) build_delta_content.
  Proof.
    intros ??? ???; subst.
    unfold build_delta_content; simpl.
    f_equal.
    extensionality b.
    extensionality dm_f.
    extensionality ofs.
    do 3 match_case.
  Qed.
  Lemma syncStep_restr:
    forall Sem tpool i st cnt m Hcmpt st' m' ev, 
      @syncStep Sem tpool true i st m cnt Hcmpt st' m' ev ->
      forall p Hlt, let Hcmpt_new:= compat_restr p Hlt Hcmpt in
                    exists p' Hlt',
                      syncStep true cnt Hcmpt_new st' (@restrPermMap p' m' Hlt') ev.
  Proof.
    intros.
    inv H; simpl in *; do 2 eexists;
      match goal with
        |- syncStep _ _ _ _ ?rm ?ev =>
        remember rm as M
      end; assert (Hcequiv:content_equiv M m') by
          (subst; eapply restr_content_equiv);
      symmetry in Hcequiv;
      repeat rewrite Hcequiv.
    - (*acquire*)
      econstructor 1; eauto;
        repeat rewrite restr_Max_eq; eauto;
          try (erewrite <- restrPermMap_idempotent_eq;
               eauto).
      erewrite Hstore.
      f_equal. rewrite (mem_is_restr_eq m').
      subst M; reflexivity.
    - (*release*)
      econstructor; eauto;
        repeat rewrite restr_Max_eq; eauto;
          try (erewrite <- restrPermMap_idempotent_eq;
               eauto).
      erewrite Hstore.
      f_equal. rewrite (mem_is_restr_eq m').
      subst M; reflexivity.
    - (*create*)
      replace (build_delta_content (fst virtue1) m') with
          (build_delta_content (fst virtue1) M) by
          (rewrite Hcequiv; reflexivity).
      replace (build_delta_content (fst virtue2) m') with
          (build_delta_content (fst virtue2) M) by
          (rewrite Hcequiv; reflexivity).
      subst M.
      econstructor 3; eauto;
        repeat rewrite restr_Max_eq; eauto;
          try (erewrite <- restrPermMap_idempotent_eq;
               eauto).
      rewrite restr_Max_equiv; eauto.
    - (*mklock*)
      econstructor; eauto;
        repeat rewrite restr_Max_eq; eauto;
          try (erewrite <- restrPermMap_idempotent_eq;
               eauto).
      erewrite Hstore.
      f_equal. rewrite (mem_is_restr_eq m').
      subst M; reflexivity.
    - (* freelock*)
      subst M;
        econstructor 5; eauto;
          repeat rewrite restr_Max_eq; eauto;
            try (erewrite <- restrPermMap_idempotent_eq;
                 eauto).
    - (* acqfail *)
      subst M;
        econstructor 6; eauto;
          repeat rewrite restr_Max_eq; eauto;
            try (erewrite <- restrPermMap_idempotent_eq;
                 eauto).

      Unshelve.
      all: rewrite getMax_restr; eauto.
  Qed.


  Lemma mi_perm_perm_threads:
    forall hb i cd mu m1 m2 (st1: @t dryResources (HybridSem (@Some nat hb))) st2 Hcnt1 Hcnt2,
      concur_match hb cd mu st1 m1 st2 m2 ->
      mi_perm_perm mu (thread_perms i st1 Hcnt1) (thread_perms i st2 Hcnt2).
  Proof.
    intros * CMatch.
    match goal with
      |- mi_perm_perm _ ?a ?b =>
      rewrite <- (getCur_restr a);
        rewrite <- (getCur_restr b)
    end.
    eapply mi_inj_mi_perm_perm_Cur, CMatch.
    Unshelve.  all: eapply CMatch.
  Qed.

  Lemma INJ_lock_permissions_None
    : forall (hb : nat) (ocd : option compiler_index) (j : meminj)
             (cstate1 : ThreadPool (Some hb)) (m1 : mem)
             (cstate2 : ThreadPool (Some (S hb))) (m2 : mem) ,
      concur_match hb ocd j cstate1 m1 cstate2 m2 ->
      Mem.meminj_no_overlap j m1 ->
      forall (b b' : block) (delt : Z) (rmap : lock_info) ofs
             (Haccess: Mem.perm m1 b ofs Cur Readable),
        j b = Some (b', delt) ->
        lockRes cstate1 (b, ofs) = None ->
        lockRes cstate2 (b', ofs + delt) = None.
  Proof.
    intros.
    match goal with
      |- ?X = _ => destruct X eqn:HH
    end; eauto.

    eapply INJ_lock_permissions_preimage in HH; eauto;
      destruct HH as (?&?&?&?&?&?&?&?).
    exfalso; destruct (peq x0 b).
    - subst. unify_injection.
      replace x1 with (ofs) in H4. rewrite H2 in H4; congruence.
      omega.
    - exploit H0; try eapply n; eauto.
      -- eapply Mem.perm_implies.
         eapply writable_locks; eauto. constructor.
      -- instantiate(1:= ofs).
         eapply Mem.perm_implies. eapply Mem.perm_cur_max.
         eauto.
         constructor.
      -- intros [HH|HH]; auto.
  Qed.
  
  
  Lemma lock_update_mem_strict_load_mem_update_restr:
    forall (b : block) (ofs : Z) (p : access_map) (m m' : mem) (vload vstore : val),
      lock_update_mem_strict_load b ofs p m m' vload vstore ->
      forall (Hlt: @permMapLt (getCurPerm m) (getMaxPerm m')),  
        lock_update_mem m (b, ofs) (encode_val AST.Mint32 vstore) (restrPermMap Hlt).
  Proof.
    intros.
    unshelve eapply lock_update_mem_restr'; swap 5 1; swap 6 2.
    eapply lock_update_mem_strict_load_mem_update.
    * eapply lock_update_mem_strict_load_restr.
      erewrite <- restrPermMap_idempotent_eq.
      erewrite <- (mem_is_restr_eq).
      eapply H.
    * red. eapply getCur_restr.
    * symmetry; eapply getCur_restr.
    * rewrite getCur_restr.
      eapply lock_update_mem_strict_load_Max_equiv in H.
      unfold Max_equiv in *.
      rewrite H.
      apply mem_cur_lt_max.
    * rewrite getMax_restr.
      apply mem_cur_lt_max.
  Qed.
  Lemma INJ_lock_content':
    forall hb ocd j cstate1 m1 cstate2 m2,
      concur_match hb ocd j cstate1 m1 cstate2 m2 ->
      forall (b : block) (ofs : Z) (rmap : lock_info),
        lockRes cstate1 (b, ofs) = Some rmap ->
        mi_memval_perm j
                       (fst rmap) (*LOCKED DATA*)
                       (Mem.mem_contents m1)
                       (Mem.mem_contents m2).
  Proof.
    intros. 
    (* Seems like I need to add this to the concur_match*)
  Admitted.
  Lemma INJ_lock_content'':
    forall hb ocd j cstate1 m1 cstate2 m2,
      concur_match hb ocd j cstate1 m1 cstate2 m2 ->
      forall (b : block) (ofs : Z) (rmap : lock_info),
        lockRes cstate1 (b, ofs) = Some rmap ->
        mi_memval_perm j
                       (snd rmap)
                       (Mem.mem_contents m1)
                       (Mem.mem_contents m2).
  Proof.
    (* Seems like I need to add this to the concur_match*)
  Admitted.
  
  Lemma lockSet_is_not_readable:
    forall hb ocd j cstate1 m1 cstate2 m2,
      concur_match hb ocd j cstate1 m1 cstate2 m2 ->
      forall b (ofs : Z) (rec : lock_info),
        lockRes cstate1 (b, ofs) = Some rec ->
        (forall i (cnt:containsThread cstate1 i),
            forall ofs0, ofs <= ofs0 < ofs + LKSIZE -> 
                         ((thread_perms i cstate1 cnt) !! b ofs0) = Some Nonempty) /\
        (forall b' ofs' rec',
            lockRes cstate1 (b', ofs') = Some rec' ->
            forall ofs0, ofs <= ofs0 < ofs + LKSIZE ->
                         ((fst rec') !! b ofs0)  = Some Nonempty ).
  Proof.
    (*This has to be added to concur_match*)
  Admitted.

  
  Lemma writable_is_not_lock:
    forall hb ocd j cstate1 m1 cstate2 m2,
      concur_match hb ocd j cstate1 m1 cstate2 m2 ->
      forall b ofs i (cnt:containsThread cstate1 i),
        Mem.perm_order' ((thread_perms i cstate1 cnt) !! b ofs) Readable ->
        lockRes cstate1 (b, ofs) = None.
  Proof.
    intros. destruct_lhs; eauto.
    eapply lockSet_is_not_readable in Heqo as (?&?); eauto.
    rewrite H1 in H0; eauto. inv H0.
    pose proof LKSIZE_pos; omega.
  Qed.


  
  
  Inductive coerce_state_type  {a b T}: forall t, @state_sum a b -> t -> T -> T -> T ->  Prop:=
  | SourceCoerce_T: forall t1 t2 c, coerce_state_type a (@SState _ _ c) c t1 t2 t1
  | TargetCoerce_T: forall t1 t2 c, coerce_state_type b (@TState _ _ c) c t1 t2 t2.
  Definition mach_state n:= ThreadPool (Some n).

  Lemma coerse_state_atx:
    forall shb Sem SemC sum_state (th_state:@semC Sem) m,
      coerce_state_type
        semC sum_state th_state
        (CSem, Clight.state)
        (AsmSem, Asm.state) (Sem, SemC) ->
      semantics.at_external (sem_coresem Sem) th_state m =
      semantics.at_external (sem_coresem (HybridSem shb)) sum_state m.
  Proof.
    intros * Hcoerce. inv Hcoerce; simpl.
    all: replace th_state with c; try reflexivity.
    all: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
  Qed.


  (*This should be parameters of the result.*)
  Definition atx_only_visible {s} (Sem:semantics.CoreSemantics s mem):=
    forall c m m' f_and_args,
      same_visible m m' ->
      semantics.at_external Sem c m = Some f_and_args ->
      semantics.at_external Sem c m' = Some f_and_args.
  Lemma atx_only_visible_Clight:
    atx_only_visible (Clightcore_coop.cl_core_sem Clight_g).
  Proof.
    intros ?* . simpl. unfold Clight.at_external.
    destruct c; simpl; intros; congruence.
  Qed.
  Lemma atx_only_visible_Asm:
    atx_only_visible (Asm_core.Asm_core_sem Asm_g).
  Proof.
    intros ?* . simpl. unfold Asm.at_external; simpl.
    destruct c; simpl.
    intros. repeat match_case in H0. inv H0.
    rewrite <- H, Heqo0; auto.
  Qed.
  
  (** *TODO: Move the following to diagrams.c*)

  
  Definition remLockfFullUpdate {sem} st i cnt th_st new_perms adr  :=
    (remLockSet
       (@updThread dryResources sem i st cnt th_st (new_perms)) adr).
  

  
  Inductive strict_evolution_diagram cd mu code1 m1 m1' code2 m2':=
  | build_stric_diagram:
      forall lev1 lev2 j m2
             (Hcomp_match : compiler_match cd j code1 m1 code2 m2)
             (Hstrict_evolution : strict_injection_evolution j mu lev1 lev2)
             (Hinterference1 : mem_interference m1 lev1 m1')
             (Hinterference2 : mem_interference m2 lev2 m2'),
        strict_evolution_diagram cd mu code1 m1 m1' code2 m2'.
  
  Inductive interference_diagram_atx i code1 code2 m1 f' m1' m2':Prop :=
  | build_inter_diagram_atx:
      forall f FUN m2 args1 args2  lev1 lev2
             (Hinj: Mem.inject f m1 m2)
             (Hinj': Mem.inject f' m1' m2')
             (Hstrict_evolution: strict_injection_evolution f f' lev1 lev2)
             (Hmatch_states: compiler_match i f code1 m1 code2 m2)
             (*Hmatch_states': compiler_match i f' code1 m1' code2 m2'*)
             (* Probably can also add this, but seems like I don't need it*)
             (Hinterference1 : mem_interference m1 lev1 m1')
             (Hinterference2 : mem_interference m2 lev2 m2')
             (Hat_external1: Clight.at_external (Clight.set_mem code1 m1) =
                             Some (FUN, args1))
             (Hat_external1': Clight.at_external (Clight.set_mem code1 m1') =
                              Some (FUN, args1))
             (Hat_external2: Asm.at_external Asm_g (Asm.set_mem code2 m2) =
                             Some (FUN, args2))
             (Hat_external2': Asm.at_external Asm_g (Asm.set_mem code2 m2') =
                              Some (FUN, args2))
             (Hinj_args: Val.inject_list f args1 args2)
      , interference_diagram_atx i code1 code2 m1 f' m1' m2'.

  Lemma retroactive_int_diagram_atx:
    forall  i code1 code2 m1 f' m1' m2' FUN 
            (Hstrict: strict_evolution_diagram i f' code1 m1 m1' code2 m2')
            (Hinj': Mem.inject f' m1' m2')
            args1
            (Hat_external1': Clight.at_external (Clight.set_mem code1 m1') =
                             Some (FUN, args1)),
      interference_diagram_atx i code1 code2 m1 f' m1' m2'.
  Proof.
    intros.
    inversion Hstrict.
    pose proof (atx_only_visible_Clight) as Hsame1.
    pose proof (atx_only_visible_Asm) as Hsame2.
    eapply Hsame1 in Hat_external1' as Hat_external1.
    2: { symmetry. eapply interference_same_visible. eassumption. }
    eapply (Injsim_atxX compiler_sim) in Hat_external1 as HH; eauto.

    destruct HH as (args' & Hat_external2 & Hinj_args).
    rename args' into args2.
    
    eapply Hsame2 in Hat_external2 as Hat_external2'.
    2: { eapply interference_same_visible; eassumption. }
    econstructor; eauto.
    - !goal (Mem.inject j m1 m2).
      eapply (Injfsim_match_meminjX compiler_sim)
        in Hcomp_match.
      destruct code1, code2; eapply Hcomp_match.
  Qed.

  
  
  Inductive same_cnt {hb1 hb2} i (st1: ThreadPool hb1) (st2: ThreadPool hb2):
    containsThread st1 i ->
    containsThread st2 i -> Prop :=
  | Build_same_cnt:
      forall (cnt1: containsThread(Sem:=HybridSem hb1) st1 i)
             (cnt2: containsThread(Sem:=HybridSem hb2) st2 i),
        same_cnt i st1 st2 cnt1 cnt2.


  (*Definition sem_coresem Sem:=(@csem _ (@event_semantics.msem _ (@semSem Sem))).*)
  Instance Sum_at_external_proper shb (c_gen: Clight.genv):
    Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
           (semantics.at_external (sem_coresem (HybridSem shb))).
  Proof.
    intros ??? ???; subst; simpl.
    unfold at_external_sum, sum_func.
    destruct y.
    - eapply C_at_external_proper; auto.
    - eapply Asm_at_external_proper; auto.
      Unshelve.
      eassumption.
  Qed.
  Instance Sum_at_external_proper':
    forall hb,
      Proper (Logic.eq ==> mem_equiv ==> Logic.eq)
             (semantics.at_external (sem_coresem (HybridSem (Some hb)))).
  Proof.
    intros ??? ???; subst; simpl.
    unfold at_external_sum, sum_func.
    destruct y.
    - eapply C_at_external_proper; auto.
    - eapply Asm_at_external_proper; auto.

      Unshelve.
      exact Clight_g.
  Qed.
  

  (* Large diagram:
         Diagram of steps over external calls. Called "Large"
         because in a thread-local view, it steps all interactions in one step. 
   *)
  Lemma large_external_diagram:
    forall cd f mu j'' code1 code2 cge age args1 rel_trace m1 m1'''
           args2 rel_trace2 FUN
           m2 m2' m2'' m2''' lev1 lev1' lev2 lev2' s1'
           p Hlt dpm1 dpm2 name signature
           (Hfun: FUN = AST.EF_external name signature)
           (Hconsec: consecutive_sem name signature)
           (Hun_dsnt_ret: doesnt_return FUN)
           (Hun_dsnt_ret_sig: AST.sig_res signature = None)
           (Hinj_delts: EventsAux.inject_delta_map mu dpm1 dpm2)
           (Heqrel_trace1 : rel_trace = Events.Event_acq_rel lev1 dpm1 lev1' :: nil)
           (Heqrel_trace : rel_trace2 = Events.Event_acq_rel lev2 dpm2 lev2' :: nil)
           (HAge: age =  (Genv.globalenv Asm_program))
           (HCge: cge = (Clight.globalenv C_program) )
           (Hext_rel1 : Events.external_call
                          FUN (Clight.genv_genv cge) 
                          args1 m1 rel_trace Vundef m1''')
           (Hext_rel2 : Events.external_call
                          FUN age 
                          args2 m2 rel_trace2 Vundef m2''')
           (Hnb_eq : Mem.nextblock m2'' = Mem.nextblock m2')
           (Hstrict_evolution : strict_injection_evolution f mu lev1 lev2)
           (Hstrict_evolution' : strict_injection_evolution mu j'' lev1' lev2')
           (Hafter_ext : Clight.after_external None code1 m1''' = Some s1')
           (Hmatch_states : compiler_match cd f code1 m1 code2 m2)
           (Hat_external1 : Clight.at_external (Clight.set_mem code1 m1) =
                            Some (FUN, args1))
           (Hat_external2 : Asm.at_external Asm_g (Asm.set_mem code2 m2) =
                            Some (FUN, args2))
           (Hinterference2' : mem_interference (@restrPermMap p m2'' Hlt) lev2' m2''')
           (Hconsecutive : consecutive_until (Mem.nextblock m2) lev2 (Mem.nextblock m2'))
           (Hconsecutive' : consecutive_until (Mem.nextblock m2'') lev2' (Mem.nextblock m2''')),
    exists (cd' : compiler_index) (j''' : meminj) (s2' : Asm.state),
      Asm.after_external Asm_g None code2 m2''' = Some s2' /\
      inject_incr mu j''' /\ compiler_match cd' j''' s1' m1''' s2' m2'''.
  Proof.
    intros; subst FUN.
    
    (* remove this comment *)
    (** *1. Prove that this is a CompCert step (en external step).
     *)
    exploit C_large_step_as_compcert_step; eauto.
    replace Values.Vundef with Vundef; eauto; simpl.
    intros Hstep.
    
    
    (** *2. Apply the simulation
                To construct the step in Asm
     *)
    subst cge;
      eapply (Injsim_simulation_atxX compiler_sim) in Hstep; eauto.
    specialize (Hstep _ _ _ Hmatch_states).
    destruct Hstep as (j2'&Hincr&Hstep_str&Hstep).
    clear Hat_external1 Hafter_ext.

    (* Notice that memories before and after stroe have same next_block*)
    
    (** *3. Following steps we prove each of the things we need. *)

    move Hstep_str at bottom.
    destruct Hstep_str as
        (i2_str & s2_str & t_str &
         Hstep_str & Hmatch_str & Hinj_trace_str).
    
    assert (Hincr_j'': inject_incr j'' j2').
    { (*
                    ( ) ---- lev1 + lev1' ---> ( )
                     |                          |  \
                     f     regular diagram      j'' \
                     |                          |    \
                    ( ) ---- lev2 + lev2' ---> ( )    \
                      \                                \
                      =eq=  strong/principled diagram  j2'
                        \                                \
                        ( )---- lev2_str + lev2_str --->( )
       *)
      eapply principled_diagram_correct'.
      - (** *Full strong diagram *)
        rewrite Hnb_eq in Hconsecutive'.
        eapply principled_diagram_exists'.
        + exploit (strict_inj_evolution_cat f mu j''); eauto.
        + exploit (consecutive_until_cat lev2 lev2');
            try eassumption.
          eapply consecutive_until_consecutive.
      - subst rel_trace.
        inv Hinj_trace_str. clear H3; inv H1.
        do 2 econstructor; auto. 
        + eapply list_inject_mem_effect_cat; 
            eapply list_inject_weaken;
            eassumption.
        + unfold Asm.at_external in Hat_external2.
          repeat match_case in Hat_external2.
          inv Hstep_str.
          * (*Can't be a builtin, it's at_ext*) exfalso.
            inv H.
            rewrite Heqs in H9; inv H9.
            rewrite Heqv in H0; inv H0.
            unfold Asm_g,the_ge, X86Context.the_ge in *.
            rewrite Heqo in H1. congruence.
          * simpl in *.
            rewrite Heqs in H; inv H.
            rewrite Heqv in H0; inv H0.
            unfold Asm_g,the_ge,X86Context.the_ge in *.
            rewrite Heqo in H1. inv H1.
            inv Hat_external2.
            replace m2 with m.
            2:{ destruct code2; inv Heqs; auto. }
            eapply Hconsec; try reflexivity; eauto.
    }

    
    assert (Hincr_mu : inject_incr mu j2').
    { eapply inject_incr_trans.
      eapply (evolution_inject_incr).
      all: eassumption. }

    assert (Hinj_trace: Events.inject_trace j2' rel_trace rel_trace2).
    { subst rel_trace rel_trace2.
      econstructor; try solve[constructor].
      econstructor.
      - emonotonicity; eauto.
        emonotonicity; eauto.
        eapply evolution_list_inject_mem; eauto.
      - emonotonicity; eauto.
      - emonotonicity; try apply Hincr_j''.
        eapply evolution_list_inject_mem in Hstrict_evolution'; assumption.
    }
    clear Hstrict_evolution'.

    subst rel_trace.
    destruct  (Hstep _ Hinj_trace)
      as (cd' & s2' & step & comp_match).

    (* Assert the after_external we know:
               Given from 
               Hat_external2: Asm.at_externalge (c2, m2) = Blah
               step: (c2, m2) --> s2' *)
    exploit asm_after_external_when_external_step;
      subst rel_trace2; simpl in *; eauto; try reflexivity.
    intros Hafter_x.

    (* Now change the mem to the one we need *)
    replace (Asm.get_mem s2') with m2''' in Hafter_x.
    2:{ !goal (m2''' = _).
        clear - Hun_dsnt_ret_sig HAge step Hat_external2 Hafter_x Hext_rel2.
        replace m2''' with (Asm.get_mem (Asm.set_mem s2' m2'''))
          by (destruct s2'; auto); f_equal. 
        eapply asm_step_determ; try eassumption.
        eapply thread_step_from_external; simpl; eauto.
        - simpl; eauto.
        - subst age; eauto.  }
    
    do 3 eexists; repeat (split; eauto).
    unfold compiler_match; simpl.
    eapply after_x_mem in Hafter_x.
    rewrite <- Hafter_x, asm_set_mem_get_mem.
    eassumption.
  Qed.

  
  Lemma at_external_sum_sem:
    forall hb Sem,
      let CoreSem := sem_coresem Sem in
      forall th_state2 sum_state2 m1 m2
             (st1:mach_state hb)
             (st2:mach_state (S hb)) tid cnt1 cnt2 args'
             (HState2 : coerce_state_type semC sum_state2 th_state2 
                                          (CSem, Clight.state) (AsmSem, Asm.state) 
                                          (Sem, semC))
             (Hthread_mem1 : access_map_equiv (thread_perms tid st1 cnt1) (getCurPerm m1))
             (Hthread_mem2 : access_map_equiv (thread_perms tid st2 cnt2) (getCurPerm m2))
             (thread_compat2 : thread_compat st2 tid cnt2 m2)
             (abs_proof : permMapLt (fst (getThreadR cnt2)) (getMaxPerm m2)) F
             (Hat_external2 : at_external CoreSem th_state2 m2 = Some (F, args')), 
        at_external
          (sem_coresem (HybridSem (Some (S hb))))
          sum_state2 (restrPermMap abs_proof) = Some (F, args').
  Proof.
    intros.
    simpl; unfold at_external_sum, sum_func.
    rewrite <- (restr_proof_irr (th_comp thread_compat2)).
    rewrite <- Hat_external2; simpl.
    inversion HState2; subst.
    - !goal ( Clight.at_external _ = _ _ m2).
      replace c with th_state2; auto.
      2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
      eapply C_at_external_proper; auto.
      eapply cur_equiv_restr_mem_equiv; auto.
    - !goal ( Asm.at_external _ _ = _ _ m2).
      replace c with th_state2; auto.
      2: eapply (Extensionality.EqdepTh.inj_pair2 Type (fun x => x)); auto.
      simpl.
      (* why can't I rewrite?*)
      eapply Asm_at_external_proper; auto.
      eapply cur_equiv_restr_mem_equiv; auto.
  Qed.
  
End SimulationTactics.


Lemma permMapJoin_pair_inject_rel:
  forall angel m1
         m2 mu  th_perms1 th_perms2,
    sub_map_virtue angel (getMaxPerm m1) ->
    let newThreadPerm1 := computeMap_pair (th_perms1) (virtueThread angel) in
    permMapJoin_pair newThreadPerm1 (virtueLP angel) (th_perms1) ->
    forall 
      (Hlt_th1 : permMapLt (fst th_perms1) (getMaxPerm m1))
      (Hlt_th2 : permMapLt (fst th_perms2) (getMaxPerm m2))
      (Hlt_lk1 : permMapLt (snd th_perms1) (getMaxPerm m1))
      (Hlt_lk2 : permMapLt (snd th_perms2) (getMaxPerm m2)),
      Mem.inject mu (restrPermMap Hlt_th1) (restrPermMap Hlt_th2) ->
      Mem.inject mu (restrPermMap Hlt_lk1) (restrPermMap Hlt_lk2) ->
      injects_angel mu angel   ->
      let angel2 := inject_virtue m2 mu angel in
      let newThreadPerm2 := computeMap_pair (th_perms2)
                                            (virtueThread angel2) in
      permMapJoin_pair newThreadPerm2 (virtueLP angel2) (th_perms2).
Proof.
  intros. subst newThreadPerm2.
  eapply compute_map_join_fwd_pair.
  eapply delta_map_join_inject_pair';
    try match goal with
          |- delta_map_join_pair _ _ _ =>
          eapply compute_map_join_bkw_pair; eassumption
        end; eauto. 
  - !goal (perm_perfect_virtue mu angel angel2).
    subst angel2.
    replace (inject_virtue m2 mu angel) with
        (inject_virtue (restrPermMap Hlt_th2) mu angel).
    eapply inject_virtue_perm_perfect; eauto.
    { eapply map_lt_implication.
      eapply permMapLt_pair_trans211; swap 1 2.
      - rewrite getMax_restr_eq; split; simpl; eauto.
      - eapply permMapJoin_lt_pair2; eauto.
    }
    rewrite getMax_restr_eq.
    pose proof (virtueThread_sub_map _ _ H) as HH.
    clear -HH.
    apply sub_map_implication_dmap_pair; eauto.
    apply inject_virtue_max_eq; eauto.
    rewrite getMax_restr_eq; auto.              
  - !goal(Mem.meminj_no_overlap _ m1).
    rewrite <- (restr_Max_equiv Hlt_th1); eapply H1.
  - !goal (dmap_vis_filtered_pair (virtueThread angel) m1).
    eapply sub_map_filtered_pair, virtueThread_sub_map, H.
  - split; eauto.
  - !goal (almost_perfect_image_pair _ _ _ _).
    eapply inject_almost_perfect_pair; eauto.
Qed.





Lemma delta_map_join_inject_pair2
  : forall (m : mem) (f : meminj) 
           (A1 A2 B1 B2 : Pair access_map)
           (C1 C2 : Pair delta_map),
    Mem.meminj_no_overlap f m ->
    dmap_vis_filtered_pair C1 m ->
    permMapLt_pair A1 (getMaxPerm m) ->
    perm_perfect_image_dmap_pair f C1 C2 ->
    perm_perfect_image_pair f A1 A2 ->
    almost_perfect_image_pair f (getMaxPerm m) B1 B2 ->
    delta_map_join2_pair A1 B1 C1 -> delta_map_join2_pair A2 B2 C2.
Proof.
  intros ? ?. unfold delta_map_join2_pair. solve_pair.
  apply delta_map_join2_inject.
Qed.

Lemma permMapJoin_pair_inject_acq:
  forall m1 lock_perm
         (* (st1:  mach_state hb)
              (st2:  mach_state (S hb)) *)
         m2 mu  th_perms1 th_perms2 virtueThread
         (Hangel_bound:
            pair21_prop sub_map virtueThread (snd (getMaxPerm m1))),
    let newThreadPerm1 := computeMap_pair th_perms1 virtueThread in
    permMapJoin_pair lock_perm th_perms1 newThreadPerm1 ->
    forall
      (Hlt_locks: permMapLt_pair lock_perm (getMaxPerm m1))
      (Hlt_th1 : permMapLt (fst th_perms1) (getMaxPerm m1))
      (Hlt_th2 : permMapLt (fst th_perms2) (getMaxPerm m2))
      (Hlt_lk1 : permMapLt (snd th_perms1) (getMaxPerm m1))
      (Hlt_lk2 : permMapLt (snd th_perms2) (getMaxPerm m2)),
      Mem.inject mu (restrPermMap Hlt_th1) (restrPermMap Hlt_th2) ->
      Mem.inject mu (restrPermMap Hlt_lk1) (restrPermMap Hlt_lk2) ->
      injects_angel mu (Build_virtue virtueThread lock_perm) ->
      let virtueThread2 := virtueThread_inject m2 mu virtueThread in
      let newThreadPerm2 := computeMap_pair (th_perms2) virtueThread2 in
      permMapJoin_pair (virtueLP_inject m2 mu lock_perm) th_perms2 newThreadPerm2.
Proof.
  intros. subst newThreadPerm2. inv H2.

  apply compute_map_join_fwd_pair2;
    apply compute_map_join_bkw_pair2 in H.
  eapply delta_map_join_inject_pair2; eauto.
  - !goal(Mem.meminj_no_overlap _ m1).
    rewrite <- (restr_Max_equiv Hlt_th1); eapply H0.
  - !goal (dmap_vis_filtered_pair _ m1).
    eapply sub_map_filtered_pair; eassumption.
  - !goal(perm_perfect_image_dmap_pair _ _ _).
    subst virtueThread2.
    replace (virtueThread_inject m2 mu virtueThread) with
        (virtueThread_inject (restrPermMap Hlt_th2) mu virtueThread).
    eapply inject_virtue_perm_perfect_image_dmap; eauto.
    { rewrite getMax_restr_eq; eauto. }
    
    unfold virtueThread_inject, tree_map_inject_over_mem.
    rewrite getMax_restr_eq; reflexivity.
  - !goal (perm_perfect_image_pair _ _ _).
    erewrite virtueLP_inject_max_eq_exteny.
    
    { eapply inject_virtue_perm_perfect_image; eauto.
      + move Hangel_bound at bottom.
        apply Lt_option_impl; auto.
        rewrite getMax_restr; auto. }
    symmetry; apply getMax_restr_eq.
  - !goal (almost_perfect_image_pair _ _ _ _).
    eapply inject_almost_perfect_pair; eauto.
Qed.





Definition mi_memval_perm_dmap f dm cont1 cont2:=
  forall (b1 b2 : block) (delta ofs : Z),
    f b1 = Some (b2, delta) ->
    opt_rel Mem.perm_order'' (dmap_get dm b1 ofs) (Some (Some Readable)) ->
    memval_inject f (ZMap.get ofs cont1 !! b1)
                  (ZMap.get (ofs + delta) cont2 !! b2).
Lemma mi_inv_option_implication:
  forall m1 m2 f b1 b2 delta,
    Mem.mem_inj f m1 m2 ->
    f b1 = Some(b2,delta) ->
    forall ofs p, (getMaxPerm m1) !! b1 ofs = Some p ->
                  option_implication (snd (getMaxPerm m1)) ! b1 (snd (getMaxPerm m2)) ! b2.
Proof.
  intros; hnf. do 2 (match_case; auto).
  exploit Mem.mi_perm; eauto.
  - instantiate(2:=Max). 
    hnf. rewrite_getPerm; unfold "!!"; rewrite Heqo; simpl.
    unfold "!!" in H1. rewrite Heqo in H1. rewrite H1. constructor.
  - unfold Mem.perm; rewrite_getPerm; unfold "!!". rewrite Heqo0.
    rewrite Max_isCanonical.
    intros HH; inv HH.
Qed.
Lemma mi_memval_perm_computeMap:
  forall mu x y cont1 cont2,
    mi_memval_perm mu x cont1 cont2 ->
    mi_memval_perm_dmap mu y cont1 cont2 ->
    mi_memval_perm mu (computeMap x y) cont1 cont2.
Proof.
  intros. hnf in *; intros.
  rewrite computeMap_get in H2.
  match_case in H2.
  eapply H0; auto.
  rewrite Heqo. constructor; auto.
Qed.


Lemma mi_memval_perm_almosequal:
  forall mu m1 m1' m2 m2' adr1 adr2 p_store p delta
         (Hreadable: forall ofs, Intv.In ofs (snd adr1, snd adr1 + 4) ->
                                 Mem.perm_order' (p_store !! (fst adr1) ofs) Readable)
         (Hno_over: maps_no_overlap mu p p_store),
    content_almost_same m1 m1' adr1 ->
    content_almost_same m2 m2' adr2 ->
    mu (fst adr1) = Some (fst adr2, delta) ->
    snd adr2 = snd adr1 + delta ->
    (forall ofs : Z,
        Intv.In ofs (snd adr1, snd adr1 +  4) ->
        memval_inject mu
                      (ZMap.get ofs (Mem.mem_contents m1') !! (fst adr1))
                      (ZMap.get (ofs + delta) (Mem.mem_contents m2') !! (fst adr2)) ) ->
    mi_memval_perm mu p 
                   (Mem.mem_contents m1) (Mem.mem_contents m2) ->
    mi_memval_perm mu p
                   (Mem.mem_contents m1') (Mem.mem_contents m2').
Proof.
  intros ** ? **.
  eapply perms_no_over_point_to_range in Hno_over.
  pose proof (Classical_Prop.classic (b1 <> fst adr1 \/ ~ Intv.In ofs (snd adr1, snd adr1 +  4))).
  destruct H7.
  destruct (base.block_eq_dec b1 (fst adr1)) eqn:HH; subst.
  destruct H7 as [HH1 |HH1]; try congruence.
  
  
  - (* ~ Intv.In ofs (snd adr1, snd adr1 + LKSIZE) *)
    unify_injection.
    rewrite H,H0; auto.
    rewrite H2; auto.
    right. hnf; simpl. intros.
    unfold Intv.In in *; simpl in *.
    eapply HH1. clear - H7. omega.
  - (* b1 <> fst adr1 *)
    exploit Hno_over; try eassumption.
    + !goal(_<_). instantiate(1:= 4). omega.
    + !goal(Mem.perm_order' _ Nonempty).
      eapply perm_order_trans101; eauto. constructor.
    + intros. instantiate(1:=snd adr1).
      eapply perm_order_trans101; eauto.
      eapply Hreadable. hnf; simpl; omega.
      constructor.
    + intros.
      rewrite H,H0; auto.
      rewrite H2; auto.
  - eapply Classical_Prop.not_or_and in H7; normal.
    apply Classical_Prop.NNPP in H7;
      apply Classical_Prop.NNPP in H8.
    subst b1.
    rewrite H1 in H5; inv H5.
    auto.
Qed.
Lemma mi_memval_perm_store:
  forall (b1 b2 : block) v
         (m1 m1' m2 m2' lock_mem : mem)
         (perm1 perm1' perm2' : access_map)
         (delta ofs : Z)
         (mu : meminj) 
         (Hinj_b' : mu b1 = Some (b2, delta))
         (Hlt_th1 : permMapLt perm1 (getMaxPerm m1))
         (Hinj' : Mem.inject mu m1 m2)
         (Hmax_eq: Max_equiv lock_mem m1)
         (Haccess : Mem.range_perm lock_mem b1 ofs (ofs + LKSIZE) Cur Readable)
         (Hwritable_lock1 : permMapLt
                              (setPermBlock (Some Writable) b1 ofs perm1' LKSIZE_nat)
                              (getMaxPerm m1))
         (Hwritable_lock0 : permMapLt
                              (setPermBlock (Some Writable) b2 
                                            (ofs + delta) perm2' LKSIZE_nat) 
                              (getMaxPerm m2)),
    let m_writable_lock_1 := restrPermMap Hwritable_lock1 : mem in
    let m_writable_lock_0 := restrPermMap Hwritable_lock0 : mem in
    forall (Hstore : Mem.store AST.Mint32 m_writable_lock_1 b1 ofs (Vint v) = Some m1')
           (Hstore0 : Mem.store AST.Mint32 m_writable_lock_0 b2 (ofs + delta) (Vint v) =
                      Some m2'),
      mi_memval_perm mu perm1 (Mem.mem_contents m1) (Mem.mem_contents m2)
      ->
      mi_memval_perm mu perm1 (Mem.mem_contents m1') (Mem.mem_contents m2').
Proof.
  intros; subst_set.
  eapply (mi_memval_perm_almosequal) with
      (adr1:= (b1,ofs))(adr2:= (b2,ofs+delta)); eauto.
  
  ++ simpl; intros.
     unfold Mem.range_perm in Haccess.
     rewrite getCur_restr.
     rewrite setPermBlock_same.
     instantiate(1:=Some Writable). constructor.
     assert (4< Z.of_nat LKSIZE_nat).
     { unfold LKSIZE_nat, LKSIZE in *.
       rewrite size_chunk_Mptr.
       clear - H0. red in H0; simpl in H0. match_case; simpl; omega. }
     !goal (ofs <= ofs0 < ofs + Z.of_nat LKSIZE_nat)%Z.
     clear - H0 H1. hnf in H0; simpl in H0.
     omega. 
  ++ !goal(maps_no_overlap _ _ _).
     eapply maps_no_overlap_under_mem; eauto. (* *)
     apply Hinj'. 
     rewrite getCur_restr. apply Hwritable_lock1.
  ++ !goal(content_almost_same _ m1' _).
     pose proof (@restr_content_equiv _  _ Hwritable_lock1) as H0; symmetry in H0.
     eapply content_almost_same_proper; try eassumption; try reflexivity.
     eapply store_almost_same; eassumption.
  ++ !goal(content_almost_same _ m2' (b2, (ofs + delta))).
     pose proof (@restr_content_equiv _  _ Hwritable_lock0) as H0; symmetry in H0.
     eapply content_almost_same_proper; try eassumption; try reflexivity.
     eapply store_almost_same; eassumption.
  ++ simpl; intros.
     {   clear - H0 Hstore Hstore0.
         move Hstore at bottom.
         eapply Mem.loadbytes_store_same,loadbytes_D in Hstore.
         destruct Hstore as [? Hstore].
         eapply Mem.loadbytes_store_same,loadbytes_D in Hstore0.
         destruct Hstore0 as [? HH].
         rewrite Hstore in HH.
         simpl in HH.
         assert (Heq_range: forall ofs0,
                    Intv.In ofs0 (ofs, ofs + 4) -> 
                    ZMap.get ofs0 (Mem.mem_contents m1') !! b1 =
                    ZMap.get (ofs0+delta) (Mem.mem_contents m2') !! b2
                ).
         { eapply fun_range4; eauto.
           repeat match goal with
                  | |- context [ ?x + delta ] =>
                    replace (x + delta) with (delta + x) in * by omega
                  end;
             repeat rewrite Z.add_assoc; auto. }
         clear HH.
         rewrite <- Heq_range; auto.
         assert (Heq_range_bytes: forall ofs0,
                    Intv.In ofs0 (ofs, ofs + 4) -> 
                    exists bl,
                      ZMap.get ofs0 (Mem.mem_contents m1') !! b1 =
                      Byte bl
                ).
         { eapply (forall_range 4 (fun (X:memval) => exists bl:byte, X = Byte bl)).
           simpl in *. rewrite <- Hstore.
           repeat econstructor. }
         exploit Heq_range_bytes; eauto;
           intros (bl& -> ).
         econstructor.
         
     }
     Unshelve.
     eauto.
     unfold Max_equiv in *; rewrite Hmax_eq; auto.
Qed.

       Lemma range_mem_permMapLt_max:
            forall b lo hi p m,
              Mem.range_perm m b lo hi Max p ->
              permMapLt_range (getMaxPerm m) b lo hi (Some p).
          Proof.
            unfold Mem.range_perm, Mem.perm.
            intros ** ??.
            exploit H; eauto.
            rewrite_getPerm.
            eauto.
          Qed.
          Lemma range_perm_cur_max:
            forall (m : mem) (b : block) (ofs ofs2 : Z) (p : permission),
              Mem.range_perm m b ofs ofs2 Cur p ->
              Mem.range_perm m b ofs ofs2 Max p.
          Proof.
            intros ** ? **. eapply H in H0.
            eapply Mem.perm_cur_max; auto.
          Qed.
          Lemma set_new_mems_LT1:
          forall b ofs m perms new_perms n_z
            (Hpos: 0 <= n_z),
            permMapLt (fst perms) (getMaxPerm m) ->
            set_new_mems b ofs perms (Z.to_nat n_z) new_perms ->
            Mem.range_perm m b ofs (ofs + n_z) Cur Writable ->
            permMapLt (fst new_perms) (getMaxPerm m). 
        Proof.
          intros. inv H0; simpl.
          eapply permMapLt_setPermBlock; eauto.
          rewrite Z2Nat.id; eauto.
          apply range_mem_permMapLt_max; eauto.
          eapply range_perm_cur_max; eauto.
          eapply Mem.range_perm_implies; eauto. constructor.
        Qed.
        Lemma set_new_mems_LT2:
          forall b ofs m perms new_perms n_z
            (Hpos: 0 <= n_z),
            permMapLt (snd perms) (getMaxPerm m) ->
            set_new_mems b ofs perms (Z.to_nat n_z) new_perms ->
            Mem.range_perm m b ofs (ofs + n_z) Cur Writable ->
            permMapLt (snd new_perms) (getMaxPerm m). 
        Proof.
          intros. inv H0; simpl.
          eapply permMapLt_setPermBlock; eauto.
          rewrite Z2Nat.id; eauto.
          apply range_mem_permMapLt_max; eauto.
          eapply range_perm_cur_max; eauto.
        Qed.
Lemma mi_memval_perm_store':
  forall (b1 b2 : block) v
         (m1 m1' m2 m2' lock_mem : mem)
         (perm1 : access_map)
         (delta ofs : Z)
         (mu : meminj) 
         (Hinj_b' : mu b1 = Some (b2, delta))
         (Hlt_th1 : permMapLt perm1 (getMaxPerm m1))
         (Hinj' : Mem.inject mu m1 m2)
         (Hmax_eq: Max_equiv lock_mem m1)
         pp1 pp2
         (Haccess : Mem.range_perm lock_mem b1 ofs (ofs + LKSIZE) Cur Writable)
         (Hwritable_lock1 : permMapLt
                              pp1
                              (getMaxPerm m1))
         (Hwritable_lock0 : permMapLt
                              pp2
                              (getMaxPerm m2)),
    let m_writable_lock_1 := restrPermMap Hwritable_lock1 : mem in
    let m_writable_lock_0 := restrPermMap Hwritable_lock0 : mem in
    forall (Hstore : Mem.store AST.Mint32 m_writable_lock_1 b1 ofs (Vint v) = Some m1')
           (Hstore0 : Mem.store AST.Mint32 m_writable_lock_0 b2 (ofs + delta) (Vint v) =
                      Some m2'),
      mi_memval_perm mu perm1 (Mem.mem_contents m1) (Mem.mem_contents m2)
      ->
      mi_memval_perm mu perm1 (Mem.mem_contents m1') (Mem.mem_contents m2').
Proof.
  intros; subst_set.
  eapply (mi_memval_perm_almosequal) with
      (adr1:= (b1,ofs))(adr2:= (b2,ofs+delta)); eauto.
  
  ++ simpl; intros.
     unfold Mem.range_perm in Haccess.
     rewrite getCur_restr.
     rewrite setPermBlock_same.
     instantiate(1:=Some Writable). constructor.
     assert (4< Z.of_nat LKSIZE_nat).
     { unfold LKSIZE_nat, LKSIZE in *.
       rewrite size_chunk_Mptr.
       clear - H0. red in H0; simpl in H0. match_case; simpl; omega. }
     !goal (ofs <= ofs0 < ofs + Z.of_nat LKSIZE_nat)%Z.
     clear - H0 H1. hnf in H0; simpl in H0.
     omega. 
  ++ !goal(maps_no_overlap _ _ _).
     eapply maps_no_overlap_under_mem; eauto.
     apply Hinj'. 
     rewrite getCur_restr.
     eapply permMapLt_setPermBlock; eauto.
     eapply range_mem_permMapLt_max.
     rewrite <- Hmax_eq; eauto.
     replace (Z.of_nat LKSIZE_nat) with LKSIZE; eauto.
     apply range_perm_cur_max; eauto.
  ++ !goal(content_almost_same _ m1' _).
     pose proof (@restr_content_equiv _  _ Hwritable_lock1) as H0; symmetry in H0.
     eapply content_almost_same_proper; try eassumption; try reflexivity.
     eapply store_almost_same; eassumption.
  ++ !goal(content_almost_same _ m2' (b2, (ofs + delta))).
     pose proof (@restr_content_equiv _  _ Hwritable_lock0) as H0; symmetry in H0.
     eapply content_almost_same_proper; try eassumption; try reflexivity.
     eapply store_almost_same; eassumption.
  ++ simpl; intros.
     {   clear - H0 Hstore Hstore0.
         move Hstore at bottom.
         eapply Mem.loadbytes_store_same,loadbytes_D in Hstore.
         destruct Hstore as [? Hstore].
         eapply Mem.loadbytes_store_same,loadbytes_D in Hstore0.
         destruct Hstore0 as [? HH].
         rewrite Hstore in HH.
         simpl in HH.
         assert (Heq_range: forall ofs0,
                    Intv.In ofs0 (ofs, ofs + 4) -> 
                    ZMap.get ofs0 (Mem.mem_contents m1') !! b1 =
                    ZMap.get (ofs0+delta) (Mem.mem_contents m2') !! b2
                ).
         { eapply fun_range4; eauto.
           repeat match goal with
                  | |- context [ ?x + delta ] =>
                    replace (x + delta) with (delta + x) in * by omega
                  end;
             repeat rewrite Z.add_assoc; auto. }
         clear HH.
         rewrite <- Heq_range; auto.
         assert (Heq_range_bytes: forall ofs0,
                    Intv.In ofs0 (ofs, ofs + 4) -> 
                    exists bl,
                      ZMap.get ofs0 (Mem.mem_contents m1') !! b1 =
                      Byte bl
                ).
         { eapply (forall_range 4 (fun (X:memval) => exists bl:byte, X = Byte bl)).
           simpl in *. rewrite <- Hstore.
           repeat econstructor. }
         exploit Heq_range_bytes; eauto;
           intros (bl& -> ).
         econstructor.
         
     }
     Unshelve.
     eauto.
     { eapply permMapLt_setPermBlock; eauto.
       - eapply range_mem_permMapLt_max.
         replace (Z.of_nat LKSIZE_nat) with LKSIZE; eauto.
         apply range_perm_cur_max; eauto.
       - unfold Max_equiv in *; rewrite Hmax_eq; auto.
     }
     
Qed.

Lemma sub_map_implictaion':
  forall (A B : Type) (x : PMap.t (Z -> option A)) (y : PMap.t (Z -> option B)),
    fst x = (fun _ : Z => None) ->
    sub_map (snd x) (snd y) -> forall b : positive,
        forall ofs, option_implication (x !! b ofs) (y !! b ofs).
Proof.
  intros. eapply sub_map_sub_map' in H0.
  hnf. repeat match_case; eauto.
  unfold "!!" in *.
  rewrite H in Heqo.
  match_case in Heqo. 
  eapply H0 in Heqo1. normal_hyp.
  rewrite H1 in Heqo0.
  hnf in H2. specialize (H2 ofs).
  rewrite Heqo, Heqo0 in H2.
  exploit H2. econstructor.
  intros HH; inv HH.
Qed.
Lemma mem_inj_Max_implication:
  forall mu m1 m2,
    Mem.mem_inj mu m1 m2 ->
    forall b1 b2 delta ofs,
      mu b1 = Some (b2, delta) ->
      option_implication ((getMaxPerm m1) !! b1 ofs)
                         ((getMaxPerm m2) !! b2 (ofs + delta)).
Proof.
  intros.
  hnf; match_case; eauto.
  exploit Mem.mi_perm; try eapply Hinj'; eauto.
  instantiate(1:=Nonempty).
  instantiate(1:=Max).
  instantiate(1:=ofs).
  hnf.
  rewrite_getPerm. rewrite Heqo.
  apply perm_any_N.
  unfold Mem.perm. rewrite_getPerm.
  intros HH; match_case; eauto.
Qed.
Lemma mi_perm_inv_perm_compute:
  forall v
         (mu : meminj)
         (m1 m1' m2 : mem)
         (perm1 perm2 : access_map)
         (Hthread_mem1 : access_map_equiv perm1 (getCurPerm m1))
         (Hthread_mem2 : access_map_equiv perm2 (getCurPerm m2))
         (Hangel_bound : sub_map v (snd (getMaxPerm m1)))
         (Hinj' : Mem.inject mu m1 m2)
         (Hmax_eq0 : Max_equiv m1 m1'),
    mi_perm_inv_perm mu (computeMap perm1 v)
                     (computeMap perm2 (tree_map_inject_over_mem m2 mu v)) m1'.
Proof.
  intros; hnf; intros.
  destruct (Classical_Prop.classic (Mem.perm m1' b1 ofs Max Nonempty))
    as [HH|HH]; eauto.
  unfold Mem.perm in HH.
  
  (*Lem ma about computeMap? *)
  
  
  clear - Hthread_mem1 Hthread_mem2 m1' H Hangel_bound Hmax_eq0 HH Hinj'
                       Hangel_bound m2 H H0.

  rewrite computeMap_get; rewrite computeMap_get in H0.
  (*Maybe best to start destructing the virtue1 and then destruct virtue2*)
  match_case; [|match_case in H0].
  -- (*dmap1 = Some *)
    clear - Hangel_bound m2 H H0 Heqo Hinj'.
    exploit tree_map_inject_over_mem_correct_forward; eauto.
    { instantiate(1:=m2).
      intros ofs0.
      eapply option_implication_trans.
      ++ instantiate(1:=((getMaxPerm m1) !! b1 ofs0)).        
         eapply sub_map_implictaion'; eauto.
      ++ eapply mem_inj_Max_implication; eauto.
         apply Hinj'. }
    { eapply no_overla_dmap_mem.
      intros; eapply sub_map_implication_dmap.
      eapply Hangel_bound.
      eapply Hinj'. }
    { unfold delta_map in *. intros HH'; rewrite HH' in H0. 
      auto. }

  -- (*dmap1 = None | dmap2 = Some *)
    exploit dmap_inject_correct_backwards; eauto.
    intros (?&?&?&?&?&?).
    destruct (base.block_eq_dec b1 x).
    ++ (*b0 = x*)
      subst. repeat unify_injection. assert (ofs=x1) by omega; subst x1.
      unfold delta_map in *. 
      rewrite Heqo in H3; congruence.
    ++           (*b0 <> x*)      
      assert (HHx : Mem.perm_order' ((Mem.mem_access m1) !! x x1 Max) Nonempty).
      { exploit sub_map_implication_dmap.
        eapply Hangel_bound.
        intros HH1; simpl in *.
        unfold option_implication_dmap_access in *.
        unfold delta_map in *; rewrite H3 in HH1.
        simpl in HH1.
        rewrite getMaxPerm_correct in HH1. unfold permission_at in HH1.
        match_case in HH1.
        constructor. }
      assert (HHb1 : Mem.perm_order' ((Mem.mem_access m1) !! b1 ofs Max) Nonempty).
      { revert HH; do 2 rewrite_getPerm. rewrite Hmax_eq0; auto. }
      exploit Mem.mi_no_overlap; try eapply Hinj'; eauto.
      intros [HHH| HHH]; contradict HHH; auto.
  -- (*dmap1 = None | dmap2 = None *)
    rewrite Hthread_mem1.
    rewrite Hthread_mem2 in H0.
    eapply inject_mi_perm_inv_perm_Cur in H0; eauto.
    rewrite <- Hmax_eq0. eassumption.
    
Qed.



Lemma tree_map_inject_restr:
  forall A p m mu perm Hlt,
    @tree_map_inject_over_mem A m mu perm =
    tree_map_inject_over_mem (@restrPermMap p m Hlt) mu perm.
Proof.
  intros. unfold tree_map_inject_over_mem.
  rewrite restr_Max_eq; reflexivity.
Qed.

Lemma mem_eq:
  forall m1 m2,
    Mem.mem_contents m1 = Mem.mem_contents m2 ->
    Mem.mem_access m1 = Mem.mem_access m2 ->
    Mem.nextblock m1 = Mem.nextblock m2 ->
    m1 = m2.
Proof.
  intros. destruct m1, m2; simpl in *.
  dependent_rewrite H.
  dependent_rewrite H0.
  dependent_rewrite H1.
  f_equal; try apply Axioms.proof_irr.
Qed.
Lemma restrPermMap_access_equiv:
  forall p p' m Hlt Hlt',
    access_map_equiv p p'->
    @restrPermMap p m Hlt =
    @restrPermMap p' m Hlt'.
Proof.
  intros.
  unfold restrPermMap.
  
  eapply mem_eq; try solve[simpl; eauto].
  simpl; do 2 f_equal.
  extensionality b;
    extensionality f;
    extensionality ofs.
  extensionality k. match_case; eauto.
  rewrite H. eauto.
Qed.
Lemma virtue_inject:
  forall mu virt m2',
    injects_dmap mu virt ->
    map_no_overlap mu (fun _ => None, virt) ->
    ( forall b1 b2 ofs0 delta,
        mu b1 = Some (b2, delta) ->
        option_implication (dmap_get virt b1 ofs0)
                           ((getMaxPerm m2') !! b2 (ofs0 + delta))) ->
    EventsAux.inject_delta_map mu virt
                               (tree_map_inject_over_mem m2' mu virt).
Proof.
  intros. econstructor.
  - intros; exploit H; eauto.
    intros HH; inv HH.
    exploit H2; eauto; intros HH.
    do 2 eexists; split; eauto.
    eapply tree_map_inject_over_mem_correct_forward; eauto.
  - intros. eapply dmap_inject_correct_backwards in H2.
    normal_hyp. subst.
    do 3 eexists. repeat weak_split; eauto.
Qed.
(*move to inject_virtue *)
Lemma virtue_inject_bounded:
  forall mu virt m2 m1,
    Mem.mem_inj mu m1 m2 ->
    injects_dmap mu virt ->
    sub_map virt (snd (getMaxPerm m1)) ->
    Mem.meminj_no_overlap mu m1 ->
    (forall b1 b2 delta, mu b1 = Some (b2, delta) ->
                         Mem.valid_block m2 b2) -> 
    EventsAux.inject_delta_map mu virt (tree_map_inject_over_mem m2 mu virt).
Proof.
  intros; eapply virtue_inject; eauto.
  - eapply no_overla_perm_mem; eauto.
    eapply sub_map_implication_dmap; eauto.
  - intros. eapply option_implication_trans.
    + eapply sub_map_implictaion'; eauto.
    + eapply mem_inj_Max_implication; eauto.
Qed.

Lemma lock_update_mem_strict_load_Max_eq:
  forall b ofs p m m' v1 v2,
    lock_update_mem_strict_load b ofs p m m' v1 v2 ->
    getMaxPerm m = getMaxPerm m'.
Proof.
  intros; inv H.
  erewrite <- getMax_restr_eq.
  eapply store_max_eq; eauto.
Qed.



Lemma LKSIZE_nat_pos': (0 < LKSIZE_nat)%nat.
Proof.
  replace 0%nat with (Z.to_nat 0)%Z by reflexivity.
  unfold LKSIZE_nat, LKSIZE.
  rewrite size_chunk_Mptr.
  destruct Archi.ptr64;
    eapply Z2Nat.inj_lt; eauto; try omega.
Qed.
Hint Resolve LKSIZE_nat_pos': core.


(* MOVE this within the file. Probably add a section for update lemmas? *)

Ltac unfold_state_forward:=
  match goal with
  | H:?st' = fullThUpd_comp ?st _ _ _ _ (?b, ?ofs)
    |- _ => unfold fullThUpd_comp, fullThreadUpdate in H
  | H:= fullThUpd_comp ?st _ _ _ _ (?b, ?ofs)
        |- _ => unfold fullThUpd_comp, fullThreadUpdate in H
      | H:?st' = fullThreadUpdate ?st _ _ _ _ (?b, ?ofs)
        |- _ => unfold fullThreadUpdate in H
      | H:= fullThreadUpdate ?st _ _ _ _ (?b, ?ofs)
            |- _ => unfold fullThreadUpdate in H
  end.

Ltac apply_permMapLt_compute_inject_pair:=
  match goal with
  | |- permMapLt_pair (computeMap_pair _ _) _ =>
    eapply permMapLt_compute_inject_pair_useful; eauto
  | |- permMapLt_pair (computeMap _ _ , computeMap _ _) _ =>
    eapply permMapLt_compute_inject_pair_useful; eauto
  end.


(** *solve_permMapLt_easy
          for all those permMapLt_pair that can be solved "directly"
 *)
Ltac solve_permMapLt_lock_update_mem:=
  first [eapply lock_update_mem_permMapLt_range_Cur; eassumption
        |eapply lock_update_mem_permMapLt_range_Max; eassumption].
Ltac solve_permMapLt_cmpt:=
  match goal with
    [Hcmpt: mem_compatible ?st ?m
     |- permMapLt_pair (@getThreadR _ _ _ ?st _) (getMaxPerm ?m)] =>
    eapply Hcmpt
  |[Hcmpt: mem_compatible ?st ?m,
           Hlock_perm: ThreadPool.lockRes ?st _ = Some ?pmaps
    |- permMapLt_pair ?pmaps (getMaxPerm ?m)] =>
   eapply Hcmpt
  end.

Ltac solve_permMapLt_join:=
  match goal with
  | H:permMapJoin_pair ?b _ _ |- permMapLt_pair2 ?b _ =>
    now apply (permMapJoin_lt_pair1 _ _ _ H)
  | H:permMapJoin_pair _ ?b _ |- permMapLt_pair2 ?b _ =>
    now apply (permMapJoin_lt_pair2 _ _ _ H)
  end.
Ltac solve_permMapLt_empty_pair:=
  match goal with
  | |- permMapLt_pair (pair0 empty_map) _ =>
    eapply permMapLt_empty_pair
  | |- permMapLt_pair (empty_map,empty_map) _ =>
    eapply permMapLt_empty_pair
  end.
Ltac solve_permMapLt_easy:=
  (* for those goals that can be solved directly*)
  first
    [ eassumption
    | solve_permMapLt_empty_pair
    | solve_permMapLt_lock_update_mem
    | solve_permMapLt_join
    (* slower :*)
    | solve_permMapLt_cmpt ].
Ltac solve_permMapLt_set_new_perms:=
  match goal with
    [Hnp: set_new_mems _ _ _ _ ?new_perms
     |- permMapLt_pair ?new_perms (getMaxPerm _)] =>
    inv Hnp; eapply permMapLt_setPermBlock_pair;
    [ permMapLt_range_pair_simpl|];
    solve_permMapLt_easy
  end.
Ltac solve_permMapLt_pair:=
  try eassumption;
  try (split; eassumption);
  subst_set; try subst;
  first
    [ solve_permMapLt_easy
    | eapply permMapLt_pair_trans211;
      [solve_permMapLt_easy  
      |solve_permMapLt_cmpt]
    | solve_permMapLt_set_new_perms
    (* inject one sometimes gets stuck. *)
    | solve[apply_permMapLt_compute_inject_pair] (*HERE!*)
    | idtac "permMapLt_pair cant be solved:"; print_goal].
(*We can use the previous to solve regular permMapLt *)
Ltac solve_permMapLt:=
  let H:= fresh in
  match goal with
  | [ |- permMapLt (fst ?a) ?b] =>
    assert (H:permMapLt_pair a b) by solve_permMapLt_pair
  | [|- permMapLt (snd ?a) ?b] =>
    assert (H:permMapLt_pair a b) by solve_permMapLt_pair
  end; apply H.
Ltac solve_valid_block:=
  subst_set; subst;
  match goal with
  |  |- Mem.valid_block ?m ?b =>
     solve[simpl; eapply Mem.valid_block_inject_1; eauto]
  (* destruct (mem_l emmas.valid_block_dec m b) as [n|n]; eauto;
            eapply Mem.mi_freeblocks in n; eauto;
            unify_injection *)
  | |- Mem.valid_block ?m ?b =>
    solve[simpl; eapply Mem.valid_block_inject_2; eauto]
  end.
Ltac forward_cmpt' H:=
  let Hcmpt_update_state:= fresh "Hcmpt_update" in
  eapply (@mem_compatible_fullThreadUpdate _ (TP _)) in H
    as Hcmpt_update_state; try reflexivity; simpl;
  [ idtac
  | eassumption
  | solve_permMapLt_pair 
  | solve_permMapLt_pair
  | solve_valid_block ];
  idtac.



Ltac forward_cmpt_add_th H:=
  let Hcmpt_update_state:= fresh "Hcmpt_update" in
  eapply (@mem_compatible_fullAddThread _ (TP _)) in H
    as Hcmpt_update_state; try reflexivity; simpl;
  [ idtac
  | eassumption
  | solve_permMapLt_pair 
  | solve_permMapLt_pair ];
  idtac.
Ltac forward_state_cmpt_all :=
  repeat unfold_state_forward;
  match goal with
  | H:?st' = updLockSet (updThread _ _ _) _ _
    |- _ =>
    let M := fresh in
    mark M st'; forward_cmpt' H;
    try forward_state_cmpt_all; clear M
  | st':=updLockSet (updThread ?a ?b ?c) ?d ?e:_
         |- _ => 
         let M := fresh in
         mark M st';
         (let H := fresh in
          assert (H : st' = updLockSet (updThread a b c) d e) by reflexivity;
          forward_cmpt' H; try forward_state_cmpt_all; clear M H)
           
       | st' := updThread ?cnt ?c ?res : _,
                                         st'' := addThread ?st' ?f_ptr ?arg ?new_res : _
                                                 |- _ => 
                                                 let M := fresh in
                                                 (mark M st'';
                                                  (let H := fresh in
                                                   assert (H : st'' =
                                                               addThread (updThread cnt c res) f_ptr arg new_res)
                                                     by reflexivity;
                                                   forward_cmpt_add_th H; try forward_state_cmpt_all; clear M H))
  end.
(*Ltac forward_state_cmpt_all :=
  repeat unfold_state_forward;
  match goal with
  | H:?st' = updLockSet (updThread _ _ _) _ _
    |- _ =>
    let M := fresh in
    mark M st'; forward_cmpt' H;
    try forward_state_cmpt_all; clear M
  | st':=updLockSet (updThread ?a ?b ?c) ?d ?e:_
         |- _ => 
         let M := fresh in
         mark M st';
         (let H := fresh in
          assert (H : st' = updLockSet (updThread a b c) d e) by reflexivity;
          forward_cmpt' H; try forward_state_cmpt_all; clear M H)
  end.*)
(* TODO move this to the highest place possible (there the lmmas are defined?)*)
Ltac solve_max_equiv:=
  (* solves the following cases:
               - reflexivity
               - just a restriction.
               - after a Mem.store.
               - a compbination of two of the previous ones. *)
  solve[ etransitivity;
         (* try Mem.store; *)
         first [(eapply store_max_equiv; eassumption)|
                (symmetry; eapply store_max_equiv; eassumption)|
                idtac];
         (*try straight restrictions*)
         first [(eapply restr_Max_equiv)|
                (symmetry; eapply restr_Max_equiv)|
                idtac];
         (*try restrictions of another hypothesis*)
         first [(eapply Max_equiv_restr; eassumption)|
                (symmetry; eapply Max_equiv_restr; eassumption)|
                idtac];
         (*finally, if there are goals left, reflexivity*)
         try reflexivity].
Ltac solve_nextblock_eq:=
  (* solves the following cases:
               - reflexivity
               - just a restriction.
               - after a Mem.store.
               - a compbination of two of the previous ones. *)
  solve[ etransitivity;
         (* try Mem.store; *)
         first [(eapply Mem.nextblock_store; eassumption)|
                (symmetry; eapply Mem.nextblock_store; eassumption)|
                idtac];
         (*finally, if there are goals left, reflexivity*)
         try reflexivity].
Ltac pose_max_equiv:=
  match goal with
    [H:lock_update_mem_strict_load _ _ _ ?m ?m' _ _ |- _] =>
    try match goal with [Hmax_eq: Max_equiv m m'|- _]=> fail 2 end;
    let Hmax_eq:= fresh "Hmax_eq" in
    let Hnb_eq:= fresh "Hnb_eq" in
    assert (Hmax_eq: Max_equiv m m') by (inv H; solve_max_equiv);
    assert (Hnb_eq: Mem.nextblock m = Mem.nextblock m')
      by (inv H; solve_nextblock_eq)
  | [H:lock_update_mem_strict _ _ ?m ?m' _ |- _] =>
    try match goal with [Hmax_eq: Max_equiv m m'|- _]=> fail 2 end;
    let Hmax_eq:= fresh "Hmax_eq" in
    let Hnb_eq:= fresh "Hnb_eq" in
    assert (Hmax_eq: Max_equiv m m') by (inv H; solve_max_equiv);
    assert (Hnb_eq: Mem.nextblock m = Mem.nextblock m')
      by (inv H; solve_nextblock_eq)
  end.
Ltac forward_mem_cmpt_all :=
  match goal with
  |[ Hmax_equiv: Max_equiv ?m ?m',
                 Hnb_eq:  Mem.nextblock ?m =  Mem.nextblock ?m',
                          Hcmpt: mem_compatible ?st ?m |- _ ] =>
   try match goal with [H: mem_compatible st m' |- _ ] => fail 2 end;
   let Hcmpt_mem_fwd:= fresh "Hcmpt_mem_fwd" in 
   try eapply mem_compat_Max in Hcmpt as Hcmpt_mem_fwd;
   [| eassumption| eassumption]
  end.
Ltac forward_cmpt_all:=
  forward_state_cmpt_all;
  repeat forward_mem_cmpt_all.

(*+ End forward CMPT*)








(** *More useful tactics 
        Add comments?
 *)

Ltac unify_at_ext:=
  repeat match goal with
           [H: semantics.at_external _ _ _ = Some _ |- _] =>
           simpl in H
         end;
  match goal with
    [H1: Clight.at_external ?X = _,
         H2: Clight.at_external ?X = _ |- _] =>
    rewrite H1 in H2; invert H2
  end.
Ltac inj_args_inv_followup f:=
  match goal with
  | [H:Val.inject f (Vptr ?b1 ?ofs) _ |- _]  =>
    invert H; try clear H;
    match goal with
    | [Hinj_b_badname: f b1 = Some _ |- _ ] =>
      let Hinj_b:= fresh "Hinj_b" in
      rename Hinj_b_badname into Hinj_b;
      try (let Hinj_b':= fresh "Hinj_b'" in
           eapply evolution_inject_incr in Hinj_b as Hinj_b';
           eauto; [idtac] (*check only one goal left.*) )
    end
  | [H:Val.inject f _ ?arg2 |- _] =>
    let arg_name:= fresh "arg2" in rename arg2 into arg_name
  end.
Ltac inj_args_inv:=
  repeat match goal with
         | [Hinj_args: Val.inject_list ?f _ _  |- _ ]=>
           let Hinj_args1:= fresh "Hinj_args" in
           let Hinj_args2:= fresh "Hinj_args" in
           invert Hinj_args; try clear Hinj_args; 
           try (inj_args_inv_followup f)
         end.
Ltac inj_args_inv_old:=
  match goal with
    [Hinj_args: Val.inject_list ?f (Vptr ?b1 ?ofs :: nil) _  |- _ ]=>
    invert Hinj_args;
    match goal with
    | [ Hinj_ptr: Val.inject _ (Vptr b1 ofs) _,
                  Hinj_nil: Val.inject_list _ nil _ |- _ ] =>
      invert Hinj_ptr; invert Hinj_nil;
      match goal with
      | [Hinj_b_badname: f b1 = Some _ |- _ ] =>
        let Hinj_b:= fresh "Hinj_b" in rename Hinj_b_badname into Hinj_b;
                                       try (let Hinj_b':= fresh "Hinj_b'" in
                                            eapply evolution_inject_incr in Hinj_b as Hinj_b';
                                            eauto; [idtac] (*check only one goal left.*) )
      end
    end
  end.
Ltac inject_lock_update_mem_strict_load:=
  lazymatch goal with
    [CMatch: concur_match _ _ ?mu ?st1 ?m1' ?st2 ?m2',
             Hlock: lock_update_mem_strict_load _ _ _ _ _ _ _ |- _ ] =>
    let Hlock_update_mem_strict_load1:= fresh "Hlock_update_mem_strict_load1" in
    dup Hlock as Hlock_update_mem_strict_load1;
    let m2'':=fresh "m2''" in 
    let Hlock_update_mem_strict_load2:=fresh "Hlock_update_mem_strict_load2" in 
    let Hinj2:=fresh "Hinj2" in 
    eapply lock_update_mem_strict_load_inject in Hlock
      as (m2''&Hlock_update_mem_strict_load2&Hinj2);
    eauto; try (eapply CMatch; eauto); [idtac]
  end.
Ltac get_injection_thread_mem:=
  match goal with
    [CMatch: concur_match _ _ ?mu ?st1 ?m1' ?st2 ?m2' |- _ ] =>
    let Hinj':= fresh "Hinj'" in
    assert (Hinj': Mem.inject mu m1' m2') by
        (rewrite <- (cur_equiv_restr_mem_equiv m1') by eassumption;
         rewrite <- (cur_equiv_restr_mem_equiv m2') by eassumption;
         eapply INJ_threads; eauto)
  end.
Ltac use_retroactive_int_diagram_atx:=
  match goal with
    [Hstrict: strict_evolution_diagram _ _ _ _ _ _ _  |- _] =>
    eapply retroactive_int_diagram_atx in Hstrict;
    eauto; [idtac]; (* This checks there is only one goal left! *)
    inversion Hstrict; unify_at_ext      
  end.

Ltac inject_lock_update_mem_strict:=
  lazymatch goal with
    [CMatch: concur_match _ _ ?mu ?st1 ?m1' ?st2 ?m2',
             Hlock: lock_update_mem_strict _ _ _ _ _ |- _ ] =>
    let Hlock_update_mem_strict1:= fresh "Hlock_update_mem_strict1" in
    dup Hlock as Hlock_update_mem_strict1;
    let m2'':=fresh "m2''" in 
    let Hlock_update_mem_strict2:=fresh "Hlock_update_mem_strict2" in 
    let Hinj2:=fresh "Hinj2" in 
    eapply lock_update_mem_strict_inject in Hlock
      as (m2''&Hlock_update_mem_strict2&Hinj2);
    eauto; try (eapply CMatch; eauto); [ ]
  end.
Ltac left_diagram:=
  (* 1. Set up the injection*)
  get_injection_thread_mem;
  (* 2. Now we expand the diagram backwards *)
  use_retroactive_int_diagram_atx;
  inj_args_inv;
  (* There are different types of left diagram.
`            each case is a different type. *)
  first 
    [inject_lock_update_mem_strict_load
    | inject_lock_update_mem_strict| idtac].




(** *Solve Unsigned: for goals of the shape: *)
(** *solve_unsigned *)
(*   unsigned (add ofs (repr delta) = unsigned ofs + delta)
 *)
Ltac solve_unsigned1:=
  (*check the goal *)
  try replace intval with unsigned by reflexivity;
  match goal with
  | [|- unsigned (add ?ofs (repr ?delta)) = unsigned ?ofs + ?delta ] => idtac
  | [|- unsigned ?ofs + ?delta = unsigned (add ?ofs (repr ?delta)) ] => symmetry
  | _ => fail "Not the right goal"
  end.
Ltac solve_unsigned2:=
  (* find the "Mem.load" *)
  match goal with
  | [ H: lock_update_mem_strict_load _ ?uofs _ _ _ _ _ |- _ = ?uofs + _ ] =>
    inv H
  | [ H: lock_update_mem_strict _ ?uofs _ _ _ |- _ = ?uofs + _ ] =>
    inv H
  | _ => idtac 
  end.
Ltac solve_solve_unsigned3 H:=
  eapply Mem.valid_access_implies with
    (p2:=Nonempty) in H; try constructor;
  (* Apply the main lemma Mem.address_inject'*)
  eapply Mem.address_inject'; try eapply H.
Ltac solve_unsigned3:=
  (* convert "Mem.load" into "Mem.access" and apply the main lemma *)
  match goal with
  | [ H: Mem.load _ ?m _ ?uofs = _ |- _ = ?uofs + _ ] =>
    eapply Mem.load_valid_access in H; solve_solve_unsigned3 H
  | H:Mem.store _ ?m _ ?uofs _ = _
    |- _ = ?uofs + _ =>
    eapply Mem.store_valid_access_3 in H; solve_solve_unsigned3 H
  end.
Ltac solve_unsigned4:= idtac;
                       (* Two goals left: 
                      Mem.inject mu lock_ mem lock_mem 2 
                      mu b1 = Some (b2, delta)   *)
                       try (subst_set;
                            eapply @INJ_locks;
                            first[
                                now eapply concur_match_perm_restrict'; eauto|
                                eassumption]);
                       (* second goal by assumption *)
                       try eassumption.
Ltac solve_unsigned:=
  solve_unsigned1; solve_unsigned2;
  solve_unsigned3; solve_unsigned4.


(* end of solve_unsigned*)


Lemma mi_perm_perm_setPermBlock:
  forall mu p b1 b2 ofs delt P1 P2 n Pmax,
    (0 < n)%nat ->
    (* bounded by a non overlapping map *)
    map_no_overlap mu Pmax ->
    permMapLt P1 Pmax ->
    permMapLt_range Pmax b1 ofs (ofs + Z.of_nat n) (Some Nonempty) ->
    mi_perm_perm mu P1 P2 ->
    mu b1 = Some (b2, delt) ->
    mi_perm_perm mu (setPermBlock p b1 ofs P1 n)
                 (setPermBlock p b2 (ofs + delt) P2 n).
Proof.
  intros ** ? * Hinj.

  assert (0 < Z.of_nat n) by omega.
  
  destruct (peq b0 b1).
  - subst. unify_injection.
    subst; destruct (Intv.In_dec ofs0 (ofs, ofs + (Z.of_nat n))).
    + repeat rewrite setPermBlock_same; eauto. 
      unfold Intv.In in i; simpl in *; omega.
    + apply Intv.range_notin in n0; simpl in n0; simpl.
      2: omega.
      repeat rewrite setPermBlock_other_1; eauto. 
      omega.
  - rewrite setPermBlock_other_2; eauto. 
    intros. eapply perms_no_over_point_to_range in H0.
    exploit H0; try eassumption.
    + eapply perm_order_trans101. 
      eapply perm_order_trans211. apply H1.
      eauto. constructor.
    + intros; eapply H2. instantiate(1:= ofs). omega.
    + intros [? | ?].
      * rewrite setPermBlock_other_2; auto. eapply H3; eauto.
      * destruct (peq b2 b3).
        -- subst. rewrite setPermBlock_other_1; auto. eapply H3; eauto.
           apply Intv.range_notin in H7; simpl in H7; simpl; auto.
           omega.
        -- rewrite setPermBlock_other_2; auto. eapply H3; eauto.
Qed.
Lemma set_new_mems_inject1:
  forall mu m1 m2 n ofs delt b1 b2
    (new_perms1 new_perms2: Pair access_map)
         (new_perms11' new_perms12' new_perms21' new_perms22':access_map),
  forall Hlt11  Hlt21 ,
    (forall ofs0 : Z,
            ofs <= ofs0 < ofs + (Z.of_nat n) ->
            memval_inject mu (ZMap.get ofs0 (Mem.mem_contents m1) !! b1)
                          (ZMap.get (ofs0 + delt)
                                    (Mem.mem_contents m2) !! b2)) ->
    Mem.inject mu (@restrPermMap (fst new_perms1) m1 Hlt11)
               (@restrPermMap (fst new_perms2) m2 Hlt21) ->
    mu b1 = Some (b2, delt) ->
    set_new_mems b1 ofs (new_perms1) n
                 (new_perms11', new_perms12') ->
    set_new_mems b2 (ofs + delt) 
                 (new_perms2) n
                 (new_perms21', new_perms22') ->
    forall Hlt11' Hlt21',
      Mem.inject mu (@restrPermMap new_perms11' m1 Hlt11')
                 (@restrPermMap new_perms21' m2 Hlt21').
Proof.
  intros.
  inv H2; inv Hset_block.
  inv H3; inv Hset_block.
    
  destruct n.
  { clean_proofs; eauto. }
  assert (0 < S n)%nat by omega.
  remember (S n) as m. clear Heqm n.
  
  unfold setPermBlock_pair in *; simpl in *.
  clean_proofs_goal. 
  erewrite (restrPermMap_idempotent_eq _ Hlt11').
  erewrite (restrPermMap_idempotent_eq _ Hlt21').
  eapply inject_restr; eauto.
  - eapply setPermBlock_range_perm in Hlt11' as Hrange1.
    
    eapply mi_perm_perm_setPermBlock; eauto.
    + eapply no_overlap_mem_perm. 
      erewrite <- restr_Max_equiv. eapply H0.
    + apply range_mem_permMapLt_max; auto.
    + rewrite <- (getCur_restr (fst new_perms1)).
      rewrite <- (getCur_restr (fst new_perms2)).
      eapply mi_inj_mi_perm_perm_Cur. apply H0.
  - intros ? * Hinj . destruct (peq b1 b0).
    + subst; unify_injection.
      destruct (Intv.In_dec ofs0 (ofs, ofs + (Z.of_nat m))).
      * intros; eauto.  
      * rewrite setPermBlock_other_1; intros.
        simpl. eapply H0; eauto. 
        hnf. rewrite_getPerm.
        rewrite (getCur_restr (fst new_perms1)).
        eauto.
        apply Intv.range_notin in n; simpl in n; eauto.
        simpl; omega.
    + rewrite setPermBlock_other_2; intros; eauto.
        simpl. eapply H0; eauto. 
        hnf. rewrite_getPerm.
        rewrite (getCur_restr (fst new_perms1)).
        eauto.
  - repeat rewrite setPermBlock_setPermBlock_var'.
    rewrite restr_Max_equiv.
    erewrite <- restr_Max_equiv.
    rewrite <- (getCur_restr (fst new_perms1)).
    rewrite <- (getCur_restr (fst new_perms2)).
    eapply mi_perm_inv_perm_setPermBlock_var; eauto;
      try now eapply H0.
    2:{ eapply inject_mi_perm_inv_perm_Cur; eauto. }
    eapply setPermBlock_range_perm; eauto.
    rewrite getMax_restr; eauto.

    Unshelve.
    all: rewrite getMax_restr; eauto.
Qed.

Lemma set_new_mems_inject2:
  forall mu m1 m2 n ofs delt b1 b2
         (new_perms1 new_perms2: Pair access_map)
         (new_perms11' new_perms12' new_perms21' new_perms22':access_map),
  forall Hlt12 Hlt22,
    (forall ofs0 : Z,
            ofs <= ofs0 < ofs + (Z.of_nat n) ->
            memval_inject mu (ZMap.get ofs0 (Mem.mem_contents m1) !! b1)
                          (ZMap.get (ofs0 + delt)
                                    (Mem.mem_contents m2) !! b2)) ->
    Mem.inject mu (@restrPermMap (snd new_perms1) m1 Hlt12)
               (@restrPermMap (snd new_perms2) m2 Hlt22) ->
    mu b1 = Some (b2, delt) ->
    set_new_mems b1 ofs (new_perms1) n
                 (new_perms11', new_perms12') ->
    set_new_mems b2 (ofs + delt) 
                 (new_perms2) n
                 (new_perms21', new_perms22') ->
    forall Hlt12' Hlt22',
      Mem.inject mu (@restrPermMap new_perms12' m1 Hlt12')
                 (@restrPermMap new_perms22' m2 Hlt22').
Proof.
  intros.
  inv H2; inv Hset_block.
  inv H3; inv Hset_block.
    
  destruct n.
  { clean_proofs; eauto. }
  assert (0 < S n)%nat by omega.
  remember (S n) as m. clear Heqm n.

  unfold setPermBlock_pair in *; simpl in *.
  clean_proofs_goal. 

  erewrite (restrPermMap_idempotent_eq _ Hlt12').
  erewrite (restrPermMap_idempotent_eq _ Hlt22').
  eapply inject_restr; eauto.
  - eapply setPermBlock_range_perm in Hlt12' as Hrange1.
     
    eapply mi_perm_perm_setPermBlock; eauto.
    + eapply no_overlap_mem_perm. 
      erewrite <- restr_Max_equiv. eapply H0.
    + apply range_mem_permMapLt_max; eauto.
      eapply Mem.range_perm_implies; eauto. constructor.
    + rewrite <- (getCur_restr (snd new_perms1)).
      rewrite <- (getCur_restr (snd new_perms2)).
      eapply mi_inj_mi_perm_perm_Cur. apply H0.
  - intros ? * Hinj . destruct (peq b1 b0).
    + subst; unify_injection.
      destruct (Intv.In_dec ofs0 (ofs, ofs + (Z.of_nat m))).
      * intros; eauto.  
      * rewrite setPermBlock_other_1; intros.
        simpl. eapply H0; eauto. 
        hnf. rewrite_getPerm.
        rewrite (getCur_restr (snd new_perms1)).
        eauto.
        apply Intv.range_notin in n; simpl in n; eauto.
        simpl; omega.
    + rewrite setPermBlock_other_2; intros; eauto.
        simpl. eapply H0; eauto. 
        hnf. rewrite_getPerm.
        rewrite (getCur_restr (snd new_perms1)).
        eauto.
  - repeat rewrite setPermBlock_setPermBlock_var'.
    rewrite restr_Max_equiv.
    erewrite <- restr_Max_equiv.
    rewrite <- (getCur_restr (snd new_perms1)).
    rewrite <- (getCur_restr (snd new_perms2)).
    eapply mi_perm_inv_perm_setPermBlock_var; eauto;
      try now eapply H0.
    2:{ eapply inject_mi_perm_inv_perm_Cur; eauto. }
    eapply Mem.range_perm_implies.
    eapply setPermBlock_range_perm; eauto.
    rewrite getMax_restr; eauto. constructor.
    

    Unshelve.
    all: try rewrite getMax_restr; eauto.
Qed.
    


Lemma set_new_mems_inject:
  forall mu m1 m2 n ofs delt b1 b2
         (new_perms1 new_perms2: Pair access_map)
         (new_perms11' new_perms12' new_perms21' new_perms22':access_map),
  forall Hlt11 Hlt12 Hlt21 Hlt22,
    (forall ofs0 : Z,
            ofs <= ofs0 < ofs + (Z.of_nat n) ->
            memval_inject mu (ZMap.get ofs0 (Mem.mem_contents m1) !! b1)
                          (ZMap.get (ofs0 + delt)
                                    (Mem.mem_contents m2) !! b2)) ->
    Mem.inject mu (@restrPermMap (fst new_perms1) m1 Hlt11)
               (@restrPermMap (fst new_perms2) m2 Hlt21) ->
    Mem.inject mu (@restrPermMap (snd new_perms1) m1 Hlt12)
               (@restrPermMap (snd new_perms2) m2 Hlt22) ->
    mu b1 = Some (b2, delt) ->
    set_new_mems b1 ofs (new_perms1) n
                 (new_perms11', new_perms12') ->
    set_new_mems b2 (ofs + delt) 
                 (new_perms2) n
                 (new_perms21', new_perms22') ->
    forall Hlt11' Hlt12' Hlt21' Hlt22',
      Mem.inject mu (@restrPermMap new_perms11' m1 Hlt11')
                 (@restrPermMap new_perms21' m2 Hlt21') /\
      Mem.inject mu (@restrPermMap new_perms12' m1 Hlt12')
                 (@restrPermMap new_perms22' m2 Hlt22').
Proof.
  intros; split.
  - eapply set_new_mems_inject1; eauto.
  - eapply set_new_mems_inject2; eauto.
Qed.

Lemma store_inj_other_perm:
  forall mu m1 m2 b1 ofs1 b2 delt p1 p2 Hlto1 Hlto2 v
    (Hno_over:Mem.meminj_no_overlap mu m1), 
    Mem.mem_inj mu (@restrPermMap p1 m1 Hlto1) (@restrPermMap p2 m2 Hlto2) ->
    mu b1 = Some (b2, delt) ->
    forall ch op1 op2 Hlt1' Hlt2' m1' m2',
      Mem.store ch (@restrPermMap op1 m1 Hlt1') b1 ofs1 (Vint v) = Some m1' ->
      Mem.store ch (@restrPermMap op2 m2 Hlt2') b2 (ofs1 + delt) (Vint v) =
      Some m2' ->
      forall Hlt1' Hlt2',
        Mem.mem_inj mu (@restrPermMap p1 m1' Hlt1') (@restrPermMap p2 m2' Hlt2').
Proof.
  intros.

  assert (Hcur1:Cur_equiv (restrPermMap Hlto1) (restrPermMap Hlt1'0)).
  { eapply Cur_equiv_restr; reflexivity. }
  assert (Hcur2:Cur_equiv (restrPermMap Hlto2) (restrPermMap Hlt2'0)).
  { eapply Cur_equiv_restr; reflexivity. }

  assert (Hmax1:Max_equiv (restrPermMap Hlto1) (restrPermMap Hlt1'0)).
  { repeat rewrite restr_Max_equiv.
    eapply store_max_equiv in H1; rewrite <- H1.
    rewrite restr_Max_equiv; reflexivity. }
  assert (Hmax2:Max_equiv (restrPermMap Hlto2) (restrPermMap Hlt2'0)).
  { repeat rewrite restr_Max_equiv.
    eapply store_max_equiv in H2; rewrite <- H2.
    rewrite restr_Max_equiv; reflexivity. }

  econstructor.
  - intros *. destruct k.
    + rewrite <- Hmax1, <- Hmax2. eapply H.
    + rewrite <- Hcur1, <- Hcur2. eapply H.
  - intros *. rewrite <- Hmax1. eapply H.
  - intros *; simpl; rewrite <- Hcur1; intros.
    eapply Mem.store_mem_contents in H1 as HH1. rewrite HH1.
    eapply Mem.store_mem_contents in H2 as HH2. rewrite HH2.
    
    destruct (peq b0 b1).
    + subst; unify_injection.
      do 2 rewrite PMap.gss.
      destruct (Intv.In_dec ofs
                            (ofs1, ofs1 + Z.of_nat (Datatypes.length (encode_val ch (Vint v))))).
      * do 2 (rewrite memory_lemmas.MemoryLemmas.setN_inside; eauto).
        replace (ofs + delta - (ofs1 + delta)) with (ofs - (ofs1))
          by omega.
        assert (forall x b mu, x = Byte b ->
                          memval_inject mu x x).
        { intros; subst; constructor. }
        -- Lemma forall1_nth:
             forall {A B} l1 l2 n (f: A -> B -> Prop) def1 def2,
               (f def1 def2) ->
               list_forall2 f l1 l2 ->
               f (nth n l1 def1) (nth n l2 def2).
           Proof.
             induction l1; intros.
             - inv H0; simpl; auto.
               destruct n; eauto.
             - inv H0. simpl. match_case.
               eapply IHl1; auto.
           Qed.
           eapply forall1_nth.
           ++ econstructor.
           ++ apply encode_val_inject. constructor.
        -- unfold Intv.In in *; simpl in *.
           omega.
      * repeat rewrite Mem.setN_outside.
        eapply H; eauto.
        -- rewrite encode_val_length, <- size_chunk_conv in *.
           apply Intv.range_notin in n; simpl in n; eauto.
           simpl. omega. simpl. pose proof (size_chunk_pos ch); omega.
        -- rewrite encode_val_length, <- size_chunk_conv in *.
           apply Intv.range_notin in n; simpl in n; eauto.
           simpl. pose proof (size_chunk_pos ch); omega.
    + (* need no overlap! *)
      rewrite PMap.gso; eauto.
      destruct (peq b2 b3); swap 1 2.
      * rewrite PMap.gso; eauto.
        eapply H; eauto.
      * subst.
        dup H4 as HH4.
        eapply Mem.perm_cur_max in H4.
        apply Mem.store_valid_access_3 in H1.
        destruct H1 as [Hrange _].
        eapply range_perm_cur_max in Hrange.
        move Hrange at bottom.
        move H4 at bottom.
        eapply meminj_no_overlap_maps_no_overlap in Hno_over.
        eapply perm_no_over_point_to_range in Hno_over.
        exploit Hno_over;
          try eapply n; eauto.
        -- pose proof (size_chunk_pos ch).
           instantiate(1:=size_chunk ch); omega.
        -- hnf in H4. rewrite_getPerm.
           rewrite getMax_restr in H4.
           eapply perm_order_trans101; eauto. constructor.
        -- intros.
           exploit Hrange; swap 1 2.
           intros HH; hnf in HH. rewrite_getPerm.
           rewrite getMax_restr in HH.
           eapply perm_order_trans101; eauto. constructor.
           instantiate(1:=ofs1). 
           omega.
        -- intros [ ? | ?]. contradict H1; reflexivity.
           rewrite PMap.gss.
           rewrite Mem.setN_outside.
           eapply H; eauto.
           apply Intv.range_notin in H1; simpl in H1; eauto.
           rewrite encode_val_length, <- size_chunk_conv.
           eauto.
           simpl. pose proof (size_chunk_pos ch); omega.

           
Qed.
Lemma store_inject_other_perm:
  forall mu m1 m2 b1 ofs1 b2 delt p1 p2 Hlto1 Hlto2 v, 
    Mem.inject mu (@restrPermMap p1 m1 Hlto1) (@restrPermMap p2 m2 Hlto2) ->
    mu b1 = Some (b2, delt) ->
    forall ch op1 op2 Hlt1' Hlt2' m1' m2',
      Mem.store ch (@restrPermMap op1 m1 Hlt1') b1 ofs1 (Vint v) = Some m1' ->
      Mem.store ch (@restrPermMap op2 m2 Hlt2') b2 (ofs1 + delt) (Vint v) =
      Some m2' ->
      forall Hlt1' Hlt2',
        Mem.inject mu (@restrPermMap p1 m1' Hlt1') (@restrPermMap p2 m2' Hlt2').
Proof.
  intros.

  assert (Hcur1:Cur_equiv (restrPermMap Hlto1) (restrPermMap Hlt1'0)).
  { eapply Cur_equiv_restr; reflexivity. }
  assert (Hcur2:Cur_equiv (restrPermMap Hlto2) (restrPermMap Hlt2'0)).
  { eapply Cur_equiv_restr; reflexivity. }

  assert (Hmax1:Max_equiv (restrPermMap Hlto1) (restrPermMap Hlt1'0)).
  { repeat rewrite restr_Max_equiv.
    eapply store_max_equiv in H1; rewrite <- H1.
    rewrite restr_Max_equiv; reflexivity. }
  assert (Hmax2:Max_equiv (restrPermMap Hlto2) (restrPermMap Hlt2'0)).
  { repeat rewrite restr_Max_equiv.
    eapply store_max_equiv in H2; rewrite <- H2.
    rewrite restr_Max_equiv; reflexivity. }
  
  econstructor.
  - eapply store_inj_other_perm; eauto.
    2: eapply H. erewrite <- restr_Max_equiv. eapply H.
  - intros **.
    eapply Mem.mi_freeblocks; eauto.
    intros HH; apply H3.
    eapply restrPermMap_valid. 
    eapply restrPermMap_valid in HH.
    eapply Mem.store_valid_block_1; eauto.
  - intros **.
    eapply restrPermMap_valid.
    eapply Mem.store_valid_block_1; eauto.
    eapply restrPermMap_valid.
    eapply Mem.mi_mappedblocks in H3 as HH; try eapply H.
    eauto.
  - rewrite restr_Max_equiv, <- store_max_equiv; eauto.
    erewrite restr_Max_equiv, <- restr_Max_equiv.
    eapply H.
  - intros * Hinj.
    rewrite restr_Max_equiv, <- store_max_equiv; eauto.
    erewrite restr_Max_equiv, <- restr_Max_equiv.
    eapply H; eauto.

    
  - intros * Hinj.
    destruct k.
    + rewrite <- Hmax1, <- Hmax2.
      eapply H; auto.
    + rewrite <- Hcur2.
      intros HH; eapply Mem.mi_perm_inv in HH;
        try apply H; eauto.
      destruct HH as [? | ?]; [left| right].
      * rewrite <- Hcur1; auto.
      * rewrite <- Hmax1; auto.

        Unshelve.
        2: rewrite getMax_restr; eauto.
    
Qed.

Lemma invariant_update_mk:
  forall (Sem : Semantics) (st st' : ThreadPool.t)
         (h : nat) (laddr : address) new_perms
         (c : ctl) tid
         (cnt1: ThreadPool.containsThread st tid)
         b ofs (Hcnt : ThreadPool.containsThread st h),
    ThreadPool.lockRes st laddr = None ->
    set_new_mems b ofs (ThreadPool.getThreadR cnt1) LKSIZE_nat new_perms ->
    st' = ThreadPool.updLockSet (ThreadPool.updThread Hcnt c  new_perms) laddr
                                (pair0 empty_map) ->
    invariant st -> invariant st'.
Admitted.
Lemma perm_surj_setPermBlock_Nonempty:
  forall mu perm1 perm2,
    perm_surj mu perm1 perm2 -> 
    forall b1 b2 delt,
      mu b1 = Some (b2, delt) ->
      forall ofs n,
        (0 < n)%nat ->
        perm_surj mu
                  (setPermBlock (Some Nonempty) b1 ofs perm1 n)
                  (setPermBlock (Some Nonempty) b2 (ofs+delt) perm2 n).
Proof.
Admitted.


    Lemma val_inject_mem_inject:
      forall mu m1 m2 arg1 arg2,
        val_inject (Mem.flat_inj (Mem.nextblock m1)) arg1 arg1 ->
        arg1 <> Vundef ->
        Mem.inject mu m1 m2 ->
        val_inject mu arg1 arg2 ->
        val_inject (Mem.flat_inj (Mem.nextblock m2)) arg2 arg2.
    Proof.
      intros. inv H; inv H2; try solve[econstructor]; swap 1 2.
      - contradict H0; eauto.
      - intros; econstructor. 
        + unfold Mem.flat_inj. match_case.
          * reflexivity.
          * clear Heqs.
            contradict n. eapply Mem.mi_mappedblocks; eauto.
        + rewrite add_zero; auto.
    Qed.
      
    Lemma mi_perm_inv_perm_compute_pair:
      forall mu m1 m2 perm1 perm2 v Hlt11 Hlt12 Hlt21 Hlt22,
        Mem.inject mu (@restrPermMap (fst perm1) m1 Hlt11)
                   (@restrPermMap (fst perm2) m2 Hlt21) ->
        Mem.inject mu (@restrPermMap (snd perm1) m1 Hlt12)
                   (@restrPermMap (snd perm2) m2 Hlt22) ->
        sub_map_pair v (snd (getMaxPerm m1)) ->
        mi_perm_inv_perm_pair
          mu
          (computeMap_pair perm1 v)
          (computeMap_pair perm2
                           (pair1 (tree_map_inject_over_mem m2 mu) v)) m1.
    Proof.
      intros. split.
      - simpl; erewrite tree_map_inject_restr.
        eapply (mi_perm_inv_perm_compute);
          try (symmetry; apply getCur_restr);
          eauto.
        + rewrite restr_Max_eq; apply H1.
        + eapply restr_Max_equiv.
      - simpl; erewrite tree_map_inject_restr.
        eapply (mi_perm_inv_perm_compute);
          try (symmetry; apply getCur_restr);
          eauto.
        + rewrite restr_Max_eq; apply H1.
        + eapply restr_Max_equiv.
    Qed.

    
    Lemma mem_compat_remLockSet:
      forall Sem m st adr,
        mem_compatible(Sem:=Sem)(tpool:=OrdinalThreadPool) st m ->
        mem_compatible(tpool:=OrdinalThreadPool) (ThreadPool.remLockSet st adr) m.
    Proof.
      intros. inv H.
      econstructor.
      - intros *. erewrite ThreadPool.gRemLockSetRes; eauto.
      - intros * HH.
        destruct (addressFiniteMap.AMap.E.eq_dec adr l).
        + subst; rewrite ThreadPool.gsslockResRemLock in HH; congruence.
        + subst; rewrite ThreadPool.gsolockResRemLock in HH; eauto.
      - intros * HH.
        destruct (addressFiniteMap.AMap.E.eq_dec adr l).
        + subst; rewrite ThreadPool.gsslockResRemLock in HH; congruence.
        + subst; rewrite ThreadPool.gsolockResRemLock in HH; eauto.
          Unshelve.
          eapply cnt.
    Qed.
    
    Lemma invariant_update_free:
      forall (Sem : Semantics) (st st' : ThreadPool.t)
        (c : ctl) 
        (tid : nat) (cnt1 : ThreadPool.containsThread st tid) 
        (b : block) (ofs : Z) (Hcnt : containsThread st tid)
        pdata perms,
        ThreadPool.lockRes st (b, ofs) = Some perms ->
        permMapLt_range (lock_perms st tid Hcnt) b ofs
                        (ofs + Z.of_nat LKSIZE_nat) (Some Writable) ->
        let new_perms := setPermBlock_var_pair
                           b ofs LKSIZE_nat (pdata, fun _ : nat => None)
                           (getThreadR Hcnt) in
        st' = remLockfFullUpdate st tid Hcnt c new_perms (b, ofs) ->
        invariant st ->
        invariant st'.
    Admitted.

        
Lemma concur_match_free_lock:
  forall (CC_correct: CompCert_correctness)
    (Args: ThreadSimulationArguments)
    ocd hb f st1 m1 st2 m2,
    concur_match.concur_match hb ocd f st1 m1 st2 m2 ->
    forall st1' m1' st2' m2' b_lock1 b_lock2 ofs_lock delta
      th_perms1 th_perms2 c1 c2 tid,
    forall (Hlt1 : permMapLt th_perms1 (getMaxPerm m1'))
      (Hlt2 : permMapLt th_perms2 (getMaxPerm m2')),
      Mem.inject f (restrPermMap Hlt1) (restrPermMap Hlt2) ->
      invariant(tpool:=OrdinalThreadPool) st1' ->
      invariant(tpool:=OrdinalThreadPool) st2' ->
      mem_compatible(Sem:=HybridSem (Some hb)) st1' m1 ->
      mem_compatible(Sem:=HybridSem (Some (S hb))) st2' m2 ->
      forall (th_lock_perms1 th_lock_perms2 : access_map)
        (Hlt_lock1 : permMapLt th_lock_perms1 (getMaxPerm m1'))
        (Hlt_lock2 : permMapLt th_lock_perms2 (getMaxPerm m2'))
        cnt1 cnt2,
        Mem.inject f (restrPermMap Hlt_lock1) (restrPermMap Hlt_lock2) ->
        perm_surj f th_lock_perms1 th_lock_perms2 ->
        let st1':=
            (remLockfFullUpdate
               st1 tid cnt1 c1 (th_perms1, th_lock_perms1)
               (b_lock1, ofs_lock)) in
        let st2':=
            (remLockfFullUpdate
               st2 tid cnt2 c2 (th_perms2, th_lock_perms2)
               (b_lock2, ofs_lock + delta)) in
        f b_lock1 = Some (b_lock2, delta) ->
        one_thread_match hb hb tid ocd f c1 (restrPermMap Hlt1) c2
                         (restrPermMap Hlt2) ->
        concur_match.concur_match hb ocd f st1' m1' st2' m2'.
Proof.
  
Admitted.