(** ** Instantiating the dry and erased machine for X86*)

Require Import concurrency.dry_machine.
Require Import concurrency.erased_machine.
Require Import concurrency.concurrent_machine.
Require Import concurrency.permissions.
Require Import concurrency.memory_lemmas.
Require Import concurrency.dry_context.
Require Import concurrency.dry_machine_lemmas.
Require Import ccc26x86.Asm_coop.
Require Import ccc26x86.Asm_event.
Require Import compcert.common.Globalenvs.
Require Import Coqlib.
Require Import msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Import Concur.

Module X86SEM <: Semantics.
  Definition F := Asm.fundef.            
  Definition V := unit.
  Definition G := Asm.genv.
  Definition C := state.
  Definition Sem := Asm_EvSem.
  Definition getEnv (g: G) := g.
End X86SEM.

(** The DryConc, FineConc and SC machines instantiated for X86*)
Module X86Machines <: (MachinesSig with Module SEM := X86SEM).

  Module SEM := X86SEM.
  Module DryMachine := DryMachineShell X86SEM.
  Module ErasedMachine := ErasedMachineShell X86SEM.

  Module DryConc := CoarseMachine mySchedule DryMachine.
  Module FineConc := FineMachine mySchedule DryMachine.
  Module SC := FineMachine mySchedule ErasedMachine.

End X86Machines.

Module X86Context <: AsmContext X86SEM X86Machines.

  Import X86Machines.
  Parameter initU: mySchedule.schedule.
  Parameter the_program: Asm.program.
  
  Definition init_mem := Genv.init_mem the_program.
  Definition init_perm : option access_map :=
    match init_mem with
    | Some m => Some (getCurPerm m)
    | None => None
    end.
  
  Definition the_ge := Globalenvs.Genv.globalenv the_program.
  
  Definition coarse_semantics:=
    DryConc.MachineSemantics initU init_perm.
  
  Definition fine_semantics:=
    FineConc.MachineSemantics initU init_perm.
  
  Definition sc_semantics :=
    SC.MachineSemantics initU None.

  Definition tpc_init f arg := initial_core coarse_semantics the_ge f arg.
  Definition tpf_init f arg := initial_core fine_semantics the_ge f arg.
  Definition sc_init f arg := initial_core sc_semantics the_ge f arg.

End X86Context.

Module X86SEMAxioms <: SemanticsAxioms X86SEM.
    
  Import Asm Asm_coop event_semantics semantics_lemmas
         X86SEM Memory.
                        
  Lemma corestep_det: corestep_fun Sem.
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

  Lemma mem_step_decay:
    forall m m',
      mem_step m m' ->
      decay m m'.
  Proof.
    induction 1.
    *
      split; intros.
      contradiction H0; clear H0.
      eapply Memory.Mem.storebytes_valid_block_2; eauto.
      right. intros.
      apply Memory.Mem.storebytes_access in H.
      rewrite H; auto.
    *
      split; intros.
    +
      assert (b=b').
      pose proof (Memory.Mem.nextblock_alloc _ _ _ _ _ H).
      apply Memory.Mem.alloc_result in H. subst.
      unfold Memory.Mem.valid_block in *.
      rewrite H2 in H1; clear H2.
      apply Plt_succ_inv in H1. destruct H1; auto.
      contradiction. subst b'. clear - H.
      Transparent Memory.Mem.alloc. unfold Memory.Mem.alloc in H. Opaque Memory.Mem.alloc.
      inv H. simpl.
      destruct (veric.Memory.range_dec lo ofs hi); [left | right]; intros.
      rewrite PMap.gss. destruct (zle lo ofs); try omega. destruct (zlt ofs hi); try omega.
      reflexivity.
      rewrite PMap.gss.
      destruct (zle lo ofs), (zlt ofs hi); try reflexivity.
      omega.
    +
      assert (b<>b').
      intro. subst b'. apply Memory.Mem.alloc_result in H. subst b.
      unfold Memory.Mem.valid_block in H0. apply Plt_ne in H0.
      contradiction H0; auto.
      right. intro.
      Transparent Memory.Mem.alloc. unfold Memory.Mem.alloc in H. Opaque Memory.Mem.alloc.
      inv H. simpl.
      erewrite PMap.gso by auto. auto.
      *
        revert m H; induction l; intros. inv H. apply decay_refl.
        simpl in H. destruct a. destruct p. 
        destruct (Memory.Mem.free m b z0 z) eqn:?H; inv H.
        apply decay_trans with m0; [ | | eapply IHl; eauto].
        eapply Memory.Mem.valid_block_free_1; eauto.
        clear  - H0. rename m0 into m'. rename z0 into lo. rename z into hi.
        Transparent Memory.Mem.free. unfold Memory.Mem.free in H0. Opaque Memory.Mem.free.
        if_tac in H0; inv H0.
        unfold Memory.Mem.unchecked_free; hnf; unfold Memory.Mem.valid_block; simpl.
        split; intros; simpl. contradiction.
        destruct (adr_range_dec (b,lo) (hi-lo) (b0,ofs)).
        destruct a. subst b0. rewrite !PMap.gss. specialize (H ofs).
        left; intro.
        destruct (zle lo ofs); try omega. destruct (zlt ofs hi); try omega.
        split; simpl; auto. spec H; [omega |].
        hnf in H. match type of H with match ?A with _ => _ end => destruct A eqn:?H end; try contradiction.
        assert (p= Memtype.Freeable). inv H; auto. subst p. clear H.
        destruct k; auto.
        pose proof (Memory.Mem.access_max m b ofs).
        rewrite H1 in H.
        match goal with |- ?A = _ => destruct A; inv H end; auto.
        clear H.
        right. intros.
        destruct (peq b b0); auto. subst b0. rewrite PMap.gss.
        unfold adr_range in n.
        assert (~ (lo <= ofs < hi)%Z) by (contradict n; split; auto; omega).
        destruct (zle lo ofs); try reflexivity.
        destruct (zlt ofs hi); try reflexivity. omega.
        erewrite PMap.gso by auto. auto.
      *
        apply decay_trans with m''; auto.
        apply mem_step_nextblock in H.
        unfold Memory.Mem.valid_block; intros.
        eapply Plt_Ple_trans; try apply H1. apply H.
  Qed.

    Lemma exec_load_same_mem:
      forall ge ch m a rs rd rs' m',
        exec_load ge ch m a rs rd = Next rs' m' ->
        m=m'.
    Proof.
      intros.
      unfold exec_load in H.
      destruct (Memory.Mem.loadv ch m (eval_addrmode ge a rs)) eqn:?; inv H.
      reflexivity.
    Qed.

    Lemma exec_store_obeys_cur_write:
      forall ge ch m a rs rs0 d rs' m',
        exec_store ge ch m a rs rs0 d = Next rs' m' ->
        forall b ofs, 
          Memory.Mem.valid_block m b ->
          ~ Memory.Mem.perm m b ofs Memtype.Cur Memtype.Writable ->
          ZMap.get ofs (PMap.get b (Memory.Mem.mem_contents m)) =
          ZMap.get ofs (PMap.get b (Memory.Mem.mem_contents m')).
    Proof.
      intros.
      unfold exec_store in H.
      destruct (Memory.Mem.storev ch m (eval_addrmode ge a rs) (rs rs0)) eqn:?; inv H.
      unfold Memory.Mem.storev in Heqo.
      destruct (eval_addrmode ge a rs); inv Heqo.
      symmetry;
        eapply MemoryLemmas.store_contents_other; eauto.
    Qed.

    Lemma mem_step_obeys_cur_write:
      forall m b ofs m',
        Memory.Mem.valid_block m b ->
        ~ Memory.Mem.perm m b ofs Memtype.Cur Memtype.Writable ->
        mem_step m m' ->
        ZMap.get ofs (PMap.get b (Memory.Mem.mem_contents m)) =
        ZMap.get ofs (PMap.get b (Memory.Mem.mem_contents m')).
    Proof.
      intros.
      induction H1.
      *
        revert m ofs0 H H0 H1; induction bytes; intros.
        Transparent Memory.Mem.storebytes.
        unfold Memory.Mem.storebytes in H1.
        destruct (Memory.Mem.range_perm_dec m b0 ofs0
                                     (ofs0 + Z.of_nat (length nil)) Memtype.Cur Memtype.Writable);
          inv H1; simpl.
        destruct (peq b b0). subst b0.
        rewrite PMap.gss. auto.
        rewrite PMap.gso; auto.
        change (a::bytes) with ((a::nil)++bytes) in H1.
        apply Memory.Mem.storebytes_split in H1.
        destruct H1 as [m1 [? ?]].
        etransitivity.
        2: eapply IHbytes; try apply H2.
        clear H2 IHbytes.
        unfold Memory.Mem.storebytes in H1. 
        Opaque Memory.Mem.storebytes.
        destruct (Memory.Mem.range_perm_dec m b0 ofs0
                                     (ofs0 + Z.of_nat (length (a :: nil))) Memtype.Cur Memtype.Writable);
          inv H1; simpl.
        destruct (peq b b0). subst b0.
        rewrite PMap.gss.
        destruct (zeq ofs0 ofs). subst.
        contradiction H0. apply r. simpl. omega.
        rewrite ZMap.gso; auto. 
        rewrite PMap.gso; auto.
        clear - H H1.
        eapply Memory.Mem.storebytes_valid_block_1; eauto.
        contradict H0. clear - H1 H0.
        eapply Memory.Mem.perm_storebytes_2; eauto.
      *
        apply AllocContentsOther with (b':=b) in H1.
        rewrite H1. auto. intro; subst.
        apply Memory.Mem.alloc_result in H1; unfold Memory.Mem.valid_block in H.
        subst. apply Plt_strict in H; auto.
      *
        revert m H H0 H1; induction l; simpl; intros.
        inv H1; auto.
        destruct a. destruct p.
        destruct (Memory.Mem.free m b0 z0 z) eqn:?; inv H1.
        rewrite <- (IHl m0); auto.
        eapply free_contents; eauto.
        intros [? ?]. subst b0. apply H0.
        apply Memory.Mem.free_range_perm in Heqo.
        specialize (Heqo ofs).
        spec Heqo; [omega | ].
        eapply Memory.Mem.perm_implies; eauto. constructor.
        clear - H Heqo.
        unfold Memory.Mem.valid_block in *.
        apply Memory.Mem.nextblock_free in Heqo. rewrite Heqo.
        auto.
        clear - H0 Heqo.
        contradict H0.
        eapply Memory.Mem.perm_free_3; eauto.
      *
        assert (Memory.Mem.valid_block m'' b). {
          apply mem_step_nextblock in H1_.
          unfold Memory.Mem.valid_block in *.
          eapply Plt_le_trans; eauto.
        }
        erewrite IHmem_step1 by auto. apply IHmem_step2; auto.
        contradict H0.
        clear - H H1_ H0.
        revert H H0; induction H1_; intros.
        eapply Memory.Mem.perm_storebytes_2; eauto.
        pose proof (Memory.Mem.perm_alloc_inv _ _ _ _ _ H _ _ _ _ H1).
        if_tac in H2; auto. subst b'.
        pose proof (Memory.Mem.alloc_result _ _ _ _ _ H).
        subst. apply Plt_strict in H0. contradiction.
        eapply Memory.Mem.perm_free_list in H; try apply H1.
        destruct H; auto.
        eapply IHH1_1; auto. eapply IHH1_2; eauto.
        apply mem_step_nextblock in H1_1.
        unfold Memory.Mem.valid_block in *.
        eapply Plt_le_trans; eauto.
    Qed.

    Lemma corestep_unchanged_on:
      forall the_ge c m
        c' m' (b : block) (ofs : Z),
        corestep X86SEM.Sem the_ge c m c' m' ->
        Memory.Mem.valid_block m b ->
        ~ Memory.Mem.perm m b ofs Memtype.Cur Memtype.Writable ->
        ZMap.get ofs (Memory.Mem.mem_contents m) !! b =
        ZMap.get ofs (Memory.Mem.mem_contents m') !! b.
    Proof.
      intros.
      hnf in H. 
      apply asm_mem_step in H.
      eapply mem_step_obeys_cur_write; auto.
    Qed.

    Lemma corestep_decay:
      forall ge c c' m m',
        corestep X86SEM.Sem ge c m c' m' -> decay m m'.
    Proof.
      intros.
      apply mem_step_decay.
      apply asm_mem_step in H; auto.
    Qed.

    Lemma corestep_nextblock :
      forall ge c m c' m',
        corestep X86SEM.Sem ge c m c' m' ->
        (Memory.Mem.nextblock m <= Memory.Mem.nextblock m')%positive.
    Proof.
      intros.
      apply mem_step_nextblock.
      apply asm_mem_step in H; auto.
    Qed.
End X86SEMAxioms.
