(** * Instantiating the dry and bare machine for X86*)

Require Import VST.concurrency.HybridMachine.
Require Import VST.concurrency.erased_machine.
Require Import VST.concurrency.HybridMachineSig.
Require Import VST.concurrency.permissions.
Require Import VST.concurrency.memory_lemmas.
Require Import VST.concurrency.dry_context.
(* Require Import VST.concurrency.HybridMachine_lemmas. *)
Require Import VST.concurrency.Asm_core.
Require Import VST.concurrency.Asm_event.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import Coqlib.
Require Import VST.msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module X86Context.
  Import AsmContext.
  
  Section X86Context.

    Variable initU: seq.seq nat.
    Variable the_program: Asm.program.

    Definition the_ge := Globalenvs.Genv.globalenv the_program.
    Hypothesis Hsafe : safe_genv the_ge.

    Instance X86Sem: Semantics:=
      { semG:= Asm.genv;
         semC:= Asm.state;
         semSem:= Asm_EvSem the_ge Hsafe;
         the_ge := the_ge
      }.

    Definition coarse_semantics:=
      coarse_semantics initU (Genv.init_mem the_program).
    Definition fine_semantics:=
      fine_semantics initU (Genv.init_mem the_program).
    Definition bare_semantics :=
      bare_semantics initU.

  End X86Context.
End X86Context.

  Module X86SEMAxioms.

    Import Asm Asm_core event_semantics semantics_lemmas
           X86Context Memory.

    Section X86Context.

    Variable initU: seq.seq nat.
    Variable the_program: Asm.program.

    Definition the_ge := Globalenvs.Genv.globalenv the_program.
    Hypothesis Hsafe : safe_genv the_ge.

    Instance X86Sem: Semantics := X86Sem the_program Hsafe.

(*    Lemma corestep_det: forall m m' m'' c c' c'' m1 m1' m1'',
      corestep semSem (State c m1) m (State c' m1') m' ->
      corestep semSem (State c m1) m (State c'' m1'') m'' ->
      c' = c'' /\ m' = m''.
    Proof.
      hnf; intros.
      inv H; inv H0; simpl in *.
      inv H; inv H1;
        repeat
          match goal with
          | H: ?A = _, H':?A=_ |- _ => inversion2 H H'
          | H: ?A, H': ?A |- _ => clear H'
          end;
        try congruence; try now (split; auto).
      assert (vargs0=vargs) by (eapply Events.eval_builtin_args_determ; eauto).
      subst vargs0.
      exploit Hsafe; eauto.
      assert (t0=t) by (eapply builtin_event_determ; eauto). subst t0.
      destruct (Events.external_call_determ _ _ _ _ _ _ _ _ _ _ H12 H16).
      specialize (H0 (eq_refl _)). destruct H0; subst m'' vres0.
      auto.
    Qed.*)

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
      forall c m
        c' m' b (ofs : Z),
        corestep semSem c m c' m' ->
        Memory.Mem.valid_block m b ->
        ~ Memory.Mem.perm m b ofs Memtype.Cur Memtype.Writable ->
        ZMap.get ofs (Memory.Mem.mem_contents m) !! b =
        ZMap.get ofs (Memory.Mem.mem_contents m') !! b.
    Proof.
      intros.
      hnf in H.
      apply asm_mem_step in H; auto.
      eapply mem_step_obeys_cur_write; auto.
    Qed.

    Lemma corestep_decay:
      forall c c' m m',
        corestep semSem c m c' m' -> decay m m'.
    Proof.
      intros.
      apply mem_step_decay.
      simpl in H.
      apply asm_mem_step in H; auto.
    Qed.

    Lemma corestep_nextblock :
      forall c m c' m',
        corestep semSem c m c' m' ->
        (Memory.Mem.nextblock m <= Memory.Mem.nextblock m')%positive.
    Proof.
      intros.
      apply mem_step_nextblock.
      simpl in H.
      apply asm_mem_step in H; auto.
    Qed.
  End X86Context.
  End X86SEMAxioms.
