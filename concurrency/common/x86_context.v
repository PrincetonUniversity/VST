(** * Instantiating the dry and bare machine for X86*)

Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.common.erased_machine.
Require Import VST.concurrency.common.HybridMachineSig.
Require Import VST.concurrency.common.permissions.
Require Import VST.concurrency.memory_lemmas.
Require Import VST.concurrency.common.dry_machine_lemmas.
Require Import VST.concurrency.common.dry_context.
Require Import VST.concurrency.common.Asm_core.
Require Import VST.concurrency.common.Asm_event.
Require Import VST.concurrency.common.dry_context.
Require Import compcert.common.Globalenvs.
Require Import compcert.common.Memory.
Require Import compcert.lib.Coqlib.
Require Import VST.msl.Coqlib2.

Set Bullet Behavior "None".
Set Bullet Behavior "Strict Subproofs".

Module X86Context.
  Import AsmContext.
  
  Section X86Context.

    Context {the_program: Asm.program}.

    Definition the_ge := Globalenvs.Genv.globalenv the_program.
    Context {Hsafe : safe_genv the_ge}.

    Instance X86Sem: Semantics:=
      { semG:= Asm.genv;
         semC:= Asm.state;
         semSem:= Asm_EvSem the_ge Hsafe;
         the_ge := the_ge
      }.

    (*Import the Asm Hybrid Machine*)
    (** *Coarse Asm Machine*)
  Import AsmContext.
  Definition AsmHybridMachine    := @dryCoarseMach X86Sem.
  Definition AsmConcurSem    := HybridMachineSig.HybridMachineSig.ConcurMachineSemantics
                                  (HybridMachine:= AsmHybridMachine).

  (** *Fine Asm Machine*)
  
  Import AsmContext.
  Definition AsmFineHybridMachine    := @dryFineMach X86Sem.
  Definition AsmFineConcurSem    := HybridMachineSig.HybridMachineSig.ConcurMachineSemantics
                                  (HybridMachine:= AsmFineHybridMachine).

  (** The initial state 
      There are three, but all should be equivalent. *)
  Definition Asm_initial_state := tpc_init(asmSem:=X86Sem).
  Definition Asm_initial_state_fine := tpf_init(asmSem:=X86Sem).
  Definition Asm_initial_state_bare := bare_init(asmSem:=X86Sem).
  
  End X86Context.
End X86Context.

Module X86SEMAxioms.

  Import Asm Asm_core event_semantics semantics_lemmas
           X86Context Memory.

  Section X86Context.

    Context {initU: seq.seq nat}
            {the_program: Asm.program}.
    Notation the_ge := (@the_ge the_program).
    Context {Hsafe : safe_genv the_ge}.


    Instance X86Sem: Semantics := @X86Sem the_program Hsafe.

    Lemma corestep_det: corestep_fun semSem.
    Proof.
      simpl.                  
      intros m m' m'' c c' c'' Hstep1 Hstep2.
      simpl in Hstep1, Hstep2.
      inv Hstep1;
        inv Hstep2.
      simpl in *.
      inv H; inv H1; subst;
        try (congruence);
        unfold set_mem in *; destruct c;
          try (repeat match goal with
                 |[H: State _ _ = State _ _ |- _] =>
                  inv H
                 |[H: ?Expr = ?V1, H2: ?Expr = ?V2 |- _]=>
                  rewrite H in H2; inv H2
                 end;
               eauto);
          try (unfold exec_instr in *; discriminate).
      simpl.
      pose proof (Events.eval_builtin_args_determ H7 H12); subst.
      assert (t = t0).
      { destruct ef0; simpl in *;
        unfold safe_genv in Hsafe;
        specialize (Hsafe _ _ _ _ _ _ _ _ _ _ _ _ H5 H6 H7 H13);
        simpl in *;
        try (destruct Hsafe as [_ [_ Hcontra]]; now exfalso).
        inversion H13. inversion H8; subst.
        reflexivity.
        inversion H13; inversion H8; subst.
        reflexivity.
        inversion H13; inversion H8; subst.
        reflexivity.
      }
      subst.
      destruct (Events.external_call_deterministic _ _ _ _ _ _ _ _ _ H8 H13);
        subst.
      now auto.
      unfold at_external in H0.
      rewrite H4 in H0.
      erewrite if_true in H0 by reflexivity.
      rewrite H5 in H0.
      destruct (get_extcall_arguments r m (Conventions1.loc_arguments (AST.ef_sig ef0)))
               eqn:Hget;
      [discriminate | eapply get_extcall_arguments_spec in H10; congruence].
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
      forall ch m a rs rd rs' m',
        exec_load the_ge ch m a rs rd = Next rs' m' ->
        m=m'.
    Proof.
      intros.
      unfold exec_load in H.
      destruct (Memory.Mem.loadv ch m (eval_addrmode the_ge a rs)) eqn:?; inv H.
      reflexivity.
    Qed.

    Lemma exec_store_obeys_cur_write:
      forall ch m a rs rs0 d rs' m',
        exec_store the_ge ch m a rs rs0 d = Next rs' m' ->
        forall b ofs,
          Memory.Mem.valid_block m b ->
          ~ Memory.Mem.perm m b ofs Memtype.Cur Memtype.Writable ->
          ZMap.get ofs (PMap.get b (Memory.Mem.mem_contents m)) =
          ZMap.get ofs (PMap.get b (Memory.Mem.mem_contents m')).
    Proof.
      intros.
      unfold exec_store in H.
      destruct (Memory.Mem.storev ch m (eval_addrmode the_ge a rs) (rs rs0)) eqn:?; inv H.
      unfold Memory.Mem.storev in Heqo.
      destruct (eval_addrmode the_ge a rs); inv Heqo.
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
          eapply Pos.lt_le_trans; eauto.
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
        unfold Memory.Mem.valid_block, Plt in *.
        zify; omega.
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

    Lemma at_external_halted_excl:
      forall q m, semantics.at_external (@semSem X86Sem) q m = None \/ forall i, ~ halted semSem q i.
    Proof.
      intros.
      simpl.
      unfold at_external.
      repeat match goal with
             | [|-match ?Expr with _ => _ end = _ \/ _] =>
               destruct Expr eqn:?; auto
             end.
      unfold set_mem in Heqs.
      destruct q; inversion Heqs; subst.
      right.
      intros i0 Hcontra.
      inversion Hcontra; subst.
      rewrite H1 in Heqv.
      discriminate.
    Qed.

    Lemma initial_core_det:
      forall i m v args c c' m' m'',
        initial_core semSem i m c m' v args ->
        initial_core semSem i m c' m'' v args ->
        c = c' /\ m' = m''.
    Proof.
      intros.
      simpl in H, H0.
      destruct H, H0.
      pose proof (Smallstep.sd_initial_determ
                    (Asm.semantics_determinate the_program)).
      simpl in H1.
      specialize (H3 _ _ _ _ _ H H0).
      subst.
      auto.
    Qed.
      
    Lemma make_arg_unchanged_on:
      forall rs m l arg rs' m'
        (Hmake_args: make_arg rs m l arg = Some (rs', m')),
        (forall b ofs, ~ Mem.perm m b ofs Cur Writable -> ZMap.get ofs (Mem.mem_contents m) !! b = ZMap.get ofs (Mem.mem_contents m') !! b) /\
        (forall b ofs k, permission_at m b ofs k = permission_at m' b ofs k) /\
        (forall b, Mem.valid_block m' b <-> Mem.valid_block m b).
    Proof.
      intros.
      unfold make_arg in *.
      destruct l.
      inv Hmake_args.
      repeat split; intros; auto.
      destruct (Mem.storev (AST.chunk_of_type ty) m (Values.Val.offset_ptr (rs RSP) (Integers.Ptrofs.repr (Stacklayout.fe_ofs_arg + 4 * pos))) arg) eqn:Hstorev;
        try discriminate.
      inv Hmake_args.
      eapply MemoryLemmas.mem_storev_store in Hstorev.
      destruct Hstorev as [b' [ofs' [? Hstore]]].
      split.
      - intros.
        symmetry.
          eapply MemoryLemmas.store_contents_other;
            now eauto.
      - split.
        + intros.
          unfold permission_at.
          erewrite <- Mem.store_access;
            now eauto.
        + split;
            [eapply Mem.store_valid_block_2 |
             eapply Mem.store_valid_block_1 ];
              now eauto.
    Qed.

    Lemma make_arguments_unchanged_on:
      forall rs m args ls rs' m'
        (Hmake_args: make_arguments rs m ls args = Some (rs', m')),
        (forall b ofs, ~ Mem.perm m b ofs Cur Writable -> ZMap.get ofs (Mem.mem_contents m) !! b = ZMap.get ofs (Mem.mem_contents m') !! b) /\
        (forall b ofs k, permission_at m b ofs k = permission_at m' b ofs k) /\
        (forall b, Mem.valid_block m' b <-> Mem.valid_block m b).
    Proof.
      induction args as [|arg args]; intros.
      - destruct ls; simpl in Hmake_args; inv Hmake_args.
        split;
          [split; reflexivity| split; auto].
        tauto.
      - destruct ls; simpl in Hmake_args; [inv Hmake_args|].
        destruct (make_arguments rs m ls args) eqn:Hmake_args0; try discriminate.
        destruct p as [rs0 m0].
        destruct (IHargs _ _ _ Hmake_args0) as [Hvaleq [Hpermeq Hblock_eq]].
        destruct r.
        + eapply make_arg_unchanged_on in Hmake_args.
          destruct Hmake_args as [Hvaleq0 [Hpermeq0 Hblockeq0]].
          split.
          * intros.
            specialize (Hvaleq b ofs ltac:(eauto)).
            specialize (Hpermeq b ofs).
            specialize (Hvaleq0 b ofs).
            specialize (Hpermeq0 b ofs).
            erewrite Hvaleq by assumption.
            erewrite Hvaleq0.
            split; auto.
            intros.
            unfold Mem.perm, permission_at in *.
            erewrite <- Hpermeq; eauto.
          * split. 
            intros.
            erewrite <- Hpermeq0.
            erewrite <- Hpermeq.
            auto.
            split;
            intros Hvalid'.
            eapply Hblock_eq; eapply Hblockeq0;
              now eauto.
            erewrite Hblockeq0; erewrite Hblock_eq;
              now eauto.
        + destruct (make_arg rs0 m0 rhi (Values.Val.hiword arg)) eqn:Hmake_arg; try discriminate.
          destruct p as [rs1 m1].
          eapply make_arg_unchanged_on in Hmake_arg; eauto.
          eapply make_arg_unchanged_on in Hmake_args; eauto.
          destruct Hmake_arg as [Hvaleq0 [Hpermeq0 Hblockeq0]].
          destruct Hmake_args as [Hvaleq1 [Hpermeq1 Hblockeq1]].
          split.
          * intros.
            specialize (Hvaleq b ofs ltac:(eauto)).
            specialize (Hpermeq b ofs).
            specialize (Hvaleq0 b ofs).
            specialize (Hpermeq0 b ofs).
            specialize (Hvaleq1 b ofs).
            specialize (Hpermeq1 b ofs).
            erewrite Hvaleq by assumption.
            erewrite Hvaleq0
              by (unfold Mem.perm, permission_at in *; erewrite <- Hpermeq; eauto).
            erewrite Hvaleq1.
            reflexivity.
            unfold Mem.perm, permission_at in *.
            erewrite <- Hpermeq0, <- Hpermeq.
            eauto.
          * unfold Mem.perm, permission_at in *.
            split.
            intros b ofs k.
            erewrite Hpermeq;
                 erewrite Hpermeq0.
            now eauto.
            intros b.
            split; intros;
              [erewrite <- Hblock_eq, <- Hblockeq0, <- Hblockeq1 |
               erewrite Hblockeq1, Hblockeq0, Hblock_eq];
            now eauto.
    Qed.

    Lemma initial_core_unchanged_on :
      forall (i : nat) (v : Values.val) (args : list Values.val) (c : semC) (m m' : mem) (b : Values.block) (ofs : Z),
        initial_core semSem i m c m' v args ->
        Mem.valid_block m b -> ~ Mem.perm m b ofs Cur Writable -> ZMap.get ofs (Mem.mem_contents m) !! b = ZMap.get ofs (Mem.mem_contents m') !! b /\
                                                                forall k, permission_at m b ofs k = permission_at m' b ofs k.
    Proof.
      intros.
      unfold initial_core in H. simpl in H.
      destruct H.
      inv H.
      simpl.
      eapply MemoryLemmas.mem_storev_store in H6.
      destruct H6 as [? [? [? Hstore6]]].
      eapply MemoryLemmas.mem_storev_store in H5.
      destruct H5 as [? [? [? Hstore5]]].
      assert ( ~ Mem.perm m1 b ofs Cur Writable).
      { intros Hcontra.
        eapply H1.
        eapply Mem.perm_alloc_4; eauto.
        apply Mem.fresh_block_alloc in H4.
        intros ?; subst;
          now auto.
      }
      assert ( ~ Mem.perm m2 b ofs Cur Writable).
      { unfold Mem.perm in *.
        erewrite Mem.store_access with (m2:= m2) (m1 := m1) by eauto.
        assumption.
      }
      assert ( ~ Mem.perm m3 b ofs Cur Writable).
      { unfold Mem.perm in *.
        erewrite Mem.store_access with (m2:= m3) (m1 := m2) by eauto.
        assumption.
      } 
      eapply make_arguments_unchanged_on in H7; eauto.
      destruct H7 as [Hvaleq34 [Hpermeq34 _]].
      specialize (Hvaleq34 b ofs ltac:(eauto)).
      specialize (Hpermeq34 b ofs).
      erewrite <- Hvaleq34.
      erewrite MemoryLemmas.store_contents_other with (m' := m3); eauto. 
      erewrite MemoryLemmas.store_contents_other with (m' := m2); eauto.
      erewrite MemoryLemmas.val_at_alloc_1; eauto.
      split; [reflexivity|].
      intros k.
      erewrite MemoryLemmas.permission_at_alloc_1 with (m' := m1) by eauto.
      erewrite <- Hpermeq34.
      unfold permission_at in *.
      erewrite Mem.store_access with (m2:= m3) (m1 := m2) by eauto.
      erewrite Mem.store_access with (m2:= m2) (m1 := m1) by eauto.
      reflexivity.
    Qed.

    Corollary initial_core_unchanged_on' :
      forall (i : nat) (v : Values.val) (args : list Values.val) (c : semC) (m m' : mem) (b : Values.block) (ofs : Z),
        initial_core semSem i m c m' v args ->
        Mem.valid_block m b -> ~ Mem.perm m b ofs Cur Writable -> ZMap.get ofs (Mem.mem_contents m) !! b = ZMap.get ofs (Mem.mem_contents m') !! b.
    Proof.
      intros.
      eapply initial_core_unchanged_on;
        eauto.
    Qed.
    
    Lemma initial_core_decay :
      forall (i : nat) (v : Values.val) (args : list Values.val) (c : semC) (m m' : mem),
        initial_core semSem i m c m' v args ->
        strong_decay m m'.
    Proof.
      intros.
      simpl in H.
      destruct H as [Hinit ?].
      subst.
      inv Hinit.
      simpl.
      split.
      - intros.
        eapply make_arguments_unchanged_on in H3; eauto.
        destruct H3 as [Hval3 [Hperm3 Hblock3]].
        unfold permission_at in Hperm3.
        eapply MemoryLemmas.mem_storev_store in H1.
        destruct H1 as [? [? [? Hstore1]]].
        eapply MemoryLemmas.mem_storev_store in H2.
        destruct H2 as [? [? [? Hstore2]]].
        assert (b0 = stk).
          { eapply Hblock3 in H5.
            eapply Mem.store_valid_block_2 in H5; eauto.
            eapply Mem.store_valid_block_2 in H5; eauto.
            eapply Mem.valid_block_alloc_inv in H0; eauto.
            destruct H0; [assumption | exfalso; now auto].
          }
          subst.
          destruct (Intv.In_dec ofs (0%Z,(3*size_chunk AST.Mptr))).
        + left.
          intros k.
          erewrite <- Hperm3.
          erewrite Mem.store_access with (m2 := m3) by eauto.
          erewrite Mem.store_access with (m2 := m2) by eauto.
          eapply MemoryLemmas.permission_at_alloc_2 in H0;
            now eauto.
        + right.
          intros k.
          erewrite <- Hperm3.
          erewrite Mem.store_access with (m2 := m3) by eauto.
          erewrite Mem.store_access with (m2 := m2) by eauto.
          eapply MemoryLemmas.permission_at_alloc_3 in H0;
            eauto.
          eapply Intv.range_notin in n; eauto.
          simpl.
          unfold AST.Mptr. destruct Archi.ptr64; simpl; omega.
      - intros Hvalid.
        eapply make_arguments_unchanged_on in H3; eauto.
        destruct H3 as [_ [Hperm3 Hblock3]].
        unfold permission_at in Hperm3.
        eapply MemoryLemmas.mem_storev_store in H1.
        destruct H1 as [? [? [? Hstore1]]].
        eapply MemoryLemmas.mem_storev_store in H2.
        destruct H2 as [? [? [? Hstore2]]].
        intros k.
        erewrite <- Hperm3.
        erewrite Mem.store_access with (m2 := m3) by eauto.
        erewrite Mem.store_access with (m2 := m2) by eauto.
        pose proof (MemoryLemmas.permission_at_alloc_1 _ _ _ _ _ _ ofs H0 Hvalid k) as Heq_perm.
        unfold permission_at in Heq_perm.
        assumption.
    Qed.

    Lemma initial_core_nextblock :
      forall (i : nat) (v : Values.val) (args : list Values.val) (c : semC) (m m' : mem),
        initial_core semSem i m c m' v args ->
        (Mem.nextblock m <= Mem.nextblock m')%positive.
    Proof.
      intros.
      inv H.
      simpl.
      inv H0.
      simpl.
      eapply make_arguments_unchanged_on in H4.
      destruct H4 as [_ [_ Hvalid4]].
      unfold Mem.valid_block, Plt in Hvalid4.
      eapply Mem.nextblock_alloc in H1.
      eapply Mem.nextblock_store in H2.
      eapply Mem.nextblock_store in H3.
      assert ((Mem.nextblock m4 = Mem.nextblock m3)%positive).
      { destruct (Pos.lt_total (Mem.nextblock m4) (Mem.nextblock m3)); auto.
        exfalso.
        pose proof (proj2 (Hvalid4 (Mem.nextblock m4)) H0).
        zify; omega.
        destruct H0; auto.
        exfalso.
        pose proof (proj1 (Hvalid4 (Mem.nextblock m3)) H0).
        zify; omega.
      }
      clear - H1 H2 H3 H0.
      rewrite H0, H3, H2, H1.
      clear.
      zify; omega.
    Qed.

    Instance X86Axioms : CoreLanguage.SemAxioms :=
      { corestep_unchanged_on := corestep_unchanged_on;
        corestep_decay := corestep_decay;
        corestep_nextblock := corestep_nextblock;
        at_external_halted_excl := at_external_halted_excl;
        initial_core_unchanged_on := initial_core_unchanged_on';
        initial_core_decay := initial_core_decay;
        initial_core_nextblock := initial_core_nextblock
      }.

    Instance X86Det : CoreLanguage.SemDet :=
      { corestep_det := corestep_det;
        initial_core_det := initial_core_det
      }.

  End X86Context.
End X86SEMAxioms.
