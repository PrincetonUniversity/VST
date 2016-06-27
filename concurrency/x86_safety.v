Require Import compcert.lib.Axioms.

Require Import concurrency.sepcomp. Import SepComp.
Require Import sepcomp.semantics_lemmas.

Require Import concurrency.pos.

(*
From mathcomp.ssreflect Require Import ssreflect ssrbool ssrnat ssrfun eqtype seq fintype finfun.
Set Implicit Arguments.
*)

(*NOTE: because of redefinition of [val], these imports must appear 
  after Ssreflect eqtype.*)
Require Import compcert.common.AST.     (*for typ*)
Require Import compcert.common.Values. (*for val*)
Require Import compcert.common.Globalenvs. 
Require Import compcert.common.Memory.
Require Import compcert.common.Events.
Require Import compcert.lib.Integers.

Require Import Coq.ZArith.ZArith.

Require Import concurrency.threads_lemmas.
Require Import concurrency.permissions.
Require Import concurrency.concurrent_machine.
Require Import concurrency.mem_obs_eq.
Require Import concurrency.x86_inj.
Require Import concurrency.compcert_threads_lemmas.
Require Import concurrency.dry_context.
Require Import sepcomp.closed_safety.

Import dry_context SEM mySchedule DryMachine DryMachine.ThreadPool.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

(** ** Safety for X86 interleaving semantics *)
Module X86Safe.

  Module SimDefs := SimDefs X86Inj.
  Module SimProofs := SimProofs X86Inj.
  Import SimDefs SimProofs X86Inj dry_machine_lemmas.
  Import Renamings MemObsEq ValObsEq.

Section CSPEC.
  Context {cspec: CoreLanguage.corestepSpec}.

  Definition csafe (tp : thread_pool) m sched :=
    forall n, safeN coarse_semantics the_ge n (sched,tp) m.

  Definition fsafe (tp : thread_pool) m sched :=
    forall n, safeN fine_semantics the_ge n (sched,tp) m.

  Import Asm Asm_coop.

Require Import Coqlib.
Require Import msl.Coqlib2.

Lemma x86_corestep_fun:  corestep_fun Sem.
Proof.
  hnf; intros.
  inv H; inv H0;
  repeat 
    match goal with
    | H: ?A = _, H':?A=_ |- _ => inversion2 H H' 
    | H: ?A, H': ?A |- _ => clear H'
    end;
  try congruence; try now (split; auto).
  pose proof (extcall_arguments_determ _ _ _ _ _ H3 H10).
  subst args0; auto.
Qed.

Lemma mem_step_nextblock:
  forall m m',
     mem_step m m' ->
   (Mem.nextblock m <= Mem.nextblock m')%positive.
Proof.
 induction 1.
 apply Mem.nextblock_storebytes in H; 
   rewrite H; apply Pos.le_refl.
 apply Mem.nextblock_alloc in H.
 rewrite H. clear.
 apply Pos.lt_eq_cases. left. apply Pos.lt_succ_r. apply Pos.le_refl.
 apply effect_properties.nextblock_freelist in H.
   rewrite H; apply Pos.le_refl.
 eapply Pos.le_trans; eassumption.
Qed.

Lemma mem_step_decay:
  forall m m',
     mem_step m m' ->
    decay m m'.
Proof.
 induction 1.
*
 split; intros.
 contradiction H0; clear H0.
 eapply Mem.storebytes_valid_block_2; eauto.
 right. intros.
 apply Mem.storebytes_access in H.
 rewrite H; auto.
*
 split; intros.
+
 assert (b=b').
 pose proof (Mem.nextblock_alloc _ _ _ _ _ H).
 apply Mem.alloc_result in H. subst.
 unfold Mem.valid_block in *.
 rewrite H2 in *; clear H2.
 apply Plt_succ_inv in H1. destruct H1; auto.
 contradiction. subst b'. clear - H.
 Transparent Mem.alloc. unfold Mem.alloc in H. Opaque Mem.alloc.
  inv H. simpl.
 destruct (base.range_dec lo ofs hi); [left | right]; intros.
 rewrite PMap.gss. destruct (zle lo ofs); try omega. destruct (zlt ofs hi); try omega.
 reflexivity.
 rewrite PMap.gss.
 destruct (zle lo ofs), (zlt ofs hi); try reflexivity.
 omega.
 +
 assert (b<>b').
 intro. subst b'. apply Mem.alloc_result in H. subst b.
 unfold Mem.valid_block in H0. apply Plt_ne in H0.
 contradiction H0; auto.
 right. intro.
 Transparent Mem.alloc. unfold Mem.alloc in H. Opaque Mem.alloc.
  inv H. simpl.
  rewrite PMap.gso by auto. auto.
*
 revert m H; induction l; intros. inv H. apply decay_refl.
 simpl in H. destruct a. destruct p. 
 destruct (Mem.free m b z0 z) eqn:?H; inv H.
 apply decay_trans with m0; [ | | eapply IHl; eauto].
 eapply Mem.valid_block_free_1; eauto.
 clear  - H0. rename m0 into m'. rename z0 into lo. rename z into hi.
 Transparent Mem.free. unfold Mem.free in H0. Opaque Mem.free.
 if_tac in H0; inv H0.
 unfold Mem.unchecked_free; hnf; unfold Mem.valid_block; simpl.
 split; intros; simpl. contradiction.
 destruct (adr_range_dec (b,lo) (hi-lo) (b0,ofs)).
 destruct a. subst b0. rewrite !PMap.gss. specialize (H ofs).
 left; intro.
 destruct (zle lo ofs); try omega. destruct (zlt ofs hi); try omega.
 split; simpl; auto. spec H; [omega |].
 hnf in H. match type of H with match ?A with _ => _ end => destruct A eqn:?H end; try contradiction.
 assert (p=Freeable). inv H; auto. subst p. clear H.
 destruct k; auto.
 pose proof (Mem.access_max m b ofs).
 rewrite H1 in H.
 match goal with |- ?A = _ => destruct A; inv H end; auto.
 clear H.
 right. intros.
 destruct (peq b b0); auto. subst b0. rewrite PMap.gss.
 unfold adr_range in n.
 assert (~ (lo <= ofs < hi)) by (contradict n; split; auto; omega).
 destruct (zle lo ofs); try reflexivity.
 destruct (zlt ofs hi); try reflexivity. omega.
 rewrite PMap.gso by auto. auto.
*
 apply decay_trans with m''; auto.
 apply mem_step_nextblock in H.
 unfold Mem.valid_block; intros.
 eapply Plt_Ple_trans; try apply H1. apply H.
Qed.

Lemma exec_load_same_mem:
  forall ge ch m a rs rd rs' m',
   exec_load ge ch m a rs rd = Next rs' m' ->
   m=m'.
Proof.
intros.
unfold exec_load in H.
destruct (Mem.loadv ch m (eval_addrmode ge a rs)) eqn:?; inv H.
reflexivity.
Qed.

Lemma exec_store_obeys_cur_write:
  forall ge ch m a rs rs0 d rs' m',
   exec_store ge ch m a rs rs0 d = Next rs' m' ->
   forall b ofs, 
     Mem.valid_block m b ->
     ~ Mem.perm m b ofs Cur Writable ->
  ZMap.get ofs (PMap.get b (Mem.mem_contents m)) =
  ZMap.get ofs (PMap.get b (Mem.mem_contents m')).
Proof.
intros.
 unfold exec_store in H.
 destruct (Mem.storev ch m (eval_addrmode ge a rs) (rs rs0)) eqn:?; inv H.
 unfold Mem.storev in Heqo.
 destruct (eval_addrmode ge a rs); inv Heqo.
 symmetry;
 eapply MemoryLemmas.store_contents_other; eauto.
Qed.

Lemma alloc_contents:
 forall m lo hi m' b' b ofs,
    Mem.valid_block m b ->
    Mem.alloc m lo hi = (m',b') ->
  ZMap.get ofs (PMap.get b (Mem.mem_contents m)) =
  ZMap.get ofs (PMap.get b (Mem.mem_contents m')).
Proof.
 intros.
Transparent Mem.alloc. unfold Mem.alloc in H0. Opaque Mem.alloc.
inv H0. simpl.
unfold Mem.valid_block in H.
rewrite PMap.gso; auto.
intro; subst. apply Plt_strict in H; auto.
Qed.

Lemma free_contents:
 forall m b lo hi m' b' ofs,
    Mem.free m b lo hi = Some m' ->
     ~adr_range (b,lo) (hi-lo) (b',ofs) ->
  ZMap.get ofs (PMap.get b' (Mem.mem_contents m)) =
  ZMap.get ofs (PMap.get b' (Mem.mem_contents m')).
Proof.
intros.
Transparent Mem.free.
unfold Mem.free in H.
Opaque Mem.free.
destruct (Mem.range_perm_dec m b lo hi Cur Freeable); inv H.
unfold Mem.unchecked_free.
simpl.
reflexivity.
Qed.

Lemma mem_step_obeys_cur_write:
  forall m b ofs m',
    Mem.valid_block m b ->
   ~ Mem.perm m b ofs Cur Writable ->
   mem_step m m' ->
 ZMap.get ofs (PMap.get b (Mem.mem_contents m)) =
 ZMap.get ofs (PMap.get b (Mem.mem_contents m')).
Proof.
 intros.
 induction H1.
*
  revert m ofs0 H H0 H1; induction bytes; intros.
 Transparent Mem.storebytes.
 unfold Mem.storebytes in H1.
 destruct (Mem.range_perm_dec m b0 ofs0
         (ofs0 + Z.of_nat (length nil)) Cur Writable);
  inv H1; simpl.
 destruct (peq b b0). subst b0.
 rewrite PMap.gss. auto.
 rewrite PMap.gso; auto.
 change (a::bytes) with ((a::nil)++bytes) in H1.
 apply Mem.storebytes_split in H1.
 destruct H1 as [m1 [? ?]].
 etransitivity.
 2: eapply IHbytes; try apply H2.
 clear H2 IHbytes.
 unfold Mem.storebytes in H1. 
Opaque Mem.storebytes.
 destruct (Mem.range_perm_dec m b0 ofs0
         (ofs0 + Z.of_nat (length (a :: nil))) Cur Writable);
 inv H1; simpl.
 destruct (peq b b0). subst b0.
 rewrite PMap.gss.
 destruct (zeq ofs0 ofs). subst.
 contradiction H0. apply r. simpl. omega.
 rewrite ZMap.gso; auto. 
 rewrite PMap.gso; auto.
 clear - H H1.
 eapply Mem.storebytes_valid_block_1; eauto.
 contradict H0. clear - H1 H0.
 eapply Mem.perm_storebytes_2; eauto.
*
 apply effect_properties.AllocContentsOther with (b':=b) in H1.
 rewrite H1. auto. intro; subst.
 apply Mem.alloc_result in H1; unfold Mem.valid_block in H.
 subst. apply Plt_strict in H; auto.
*
 revert m H H0 H1; induction l; simpl; intros.
 inv H1; auto.
 destruct a. destruct p.
 destruct (Mem.free m b0 z0 z) eqn:?; inv H1.
 rewrite <- (IHl m0); auto.
 eapply free_contents; eauto.
 intros [? ?]. subst b0. apply H0.
 apply Mem.free_range_perm in Heqo.
   specialize (Heqo ofs).
   spec Heqo; [omega | ].
   eapply Mem.perm_implies; eauto. constructor.
 clear - H Heqo.
 unfold Mem.valid_block in *.
 apply Mem.nextblock_free in Heqo. rewrite Heqo.
 auto.
 clear - H0 Heqo.
 contradict H0.
 eapply Mem.perm_free_3; eauto.
*
 assert (Mem.valid_block m'' b). {
   apply mem_step_nextblock in H1_.
   unfold Mem.valid_block in *.
   eapply Plt_le_trans; eauto.
 }
 rewrite IHmem_step1 by auto. apply IHmem_step2; auto.
 contradict H0.
 clear - H H1_ H0.
 revert H H0; induction H1_; intros.
 eapply Mem.perm_storebytes_2; eauto.
 pose proof (Mem.perm_alloc_inv _ _ _ _ _ H _ _ _ _ H1).
 if_tac in H2; auto. subst b'.
 pose proof (Mem.alloc_result _ _ _ _ _ H).
 subst. apply Plt_strict in H0. contradiction.
 eapply Mem.perm_free_list in H; try apply H1.
 destruct H; auto.
 eapply IHH1_1; auto. eapply IHH1_2; eauto.
 apply mem_step_nextblock in H1_1.
 unfold Mem.valid_block in *.
 eapply Plt_le_trans; eauto.
Qed.

Instance x86Spec : CoreLanguage.corestepSpec.
  Proof.
    split.
    intros m m' m'' ge c c' c'' Hstep Hstep'.
    *
      eapply x86_corestep_fun; eauto.
    * 
      intros.
      hnf in Hstep. 
      apply asm_mem_step in Hstep.
      eapply mem_step_obeys_cur_write; auto.
    * 
      intros.
      apply mem_step_decay.
      apply asm_mem_step in H; auto.
    *
      intros.
      apply mem_step_nextblock.
      apply asm_mem_step in H; auto.
  Qed.

End CSPEC.

Parameter init_tp : thread_pool.
Parameter init_mem : mem.



End X86Safe.

  
  


  