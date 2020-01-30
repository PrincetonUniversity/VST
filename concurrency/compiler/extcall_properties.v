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
Require Import VST.concurrency.compiler.concurrent_compiler_simulation.
Require Import VST.concurrency.compiler.sequential_compiler_correct.
Require Import VST.concurrency.compiler.advanced_permissions.
Require Import VST.concurrency.compiler.CoreSemantics_sum.
Require Import VST.concurrency.common.HybridMachine.
Require Import VST.concurrency.compiler.HybridMachine_simulation.


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
Require Import VST.concurrency.compiler.Asm_self_simulation.
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
Require Import VST.concurrency.compiler.concurrent_compiler_simulation_definitions.
Require Import VST.concurrency.compiler.synchronisation_steps_semantics.
Import bounded_maps.

Import HybridMachineSig.
Include common.Events.

Notation vone:= (Vint Int.one).
Notation vzero:= (Vint Int.zero).

Ltac trans_n n:=
  match n with
  | O => idtac
  | S ?n' =>
    etransitivity;
    [|trans_n n']
  end.
Lemma mem_equalitiy:
  forall m1 m2,
    Mem.mem_contents m1 = Mem.mem_contents m2 ->
    Mem.mem_access m1 = Mem.mem_access m2 ->
    Mem.nextblock m1 = Mem.nextblock m2 ->
    m1 = m2.
Proof.
  intros.
  destruct m1; destruct m2; simpl in *.
  dependent_rewrite H.
  dependent_rewrite H0.
  dependent_rewrite H1.
  f_equal; apply Axioms.proof_irr.
Qed.
Instance loc_not_writable_proper:
  Proper (Max_equiv ==> Logic.eq ==> Logic.eq ==> iff) Events.loc_not_writable.
Proof.
  intros ??? ??? ???; subst.
  split; intros HH HH'; eapply HH; eauto.
  rewrite H; auto.
  rewrite <- H; auto.
Qed.


(*Useful Generic lemmas, worst case, move to diagrams.v, 
maybe advanced_permissions.v? *) 
Lemma nextblock_eq_valid:
  forall m1 m2,
    (forall b, Mem.valid_block m1 b <->
          Mem.valid_block m2 b) <->
    (Mem.nextblock m1 = Mem.nextblock m2).
Proof.
  intros; split.
  - unfold Mem.valid_block in *.
    remember (Mem.nextblock m1) as a eqn:HH; clear HH.
    remember (Mem.nextblock m2) as b eqn:HH; clear HH.
    intros.
    destruct (Dcompare_inf (a ?= b)%positive) as [[? | ?] | ?].
    + apply Pos.compare_eq; eauto.
    + eapply H in e. apply Plt_strict in e. contradict e.
    + eapply Pos.compare_gt_iff in e. 
      eapply H in e. apply Plt_strict in e. contradict e.
  - unfold Mem.valid_block. intros ->. reflexivity.
Qed.
Lemma nextblock_leq_valid:
  forall m1 m2,
    (forall b, Mem.valid_block m1 b ->
          Mem.valid_block m2 b) <->
    (Ple (Mem.nextblock m1) ( Mem.nextblock m2)).
Proof.
  intros; split.
  - unfold Mem.valid_block in *.
    remember (Mem.nextblock m1) as a eqn:HH; clear HH.
    remember (Mem.nextblock m2) as b eqn:HH; clear HH.
    intros ** ?.
    unfold Plt in H.
    eapply Pos.compare_gt_iff,H in H0.
    eapply Plt_strict; eassumption.
  - unfold Mem.valid_block.
    intros. eapply Plt_Ple_trans; eauto.
Qed.

Lemma Max_equiv_perm:
  forall m1 m2,
    Max_equiv m1 m2 <->
    (forall b ofs p, Mem.perm m2 b ofs Max p <-> Mem.perm m1 b ofs Max p).
Proof.
  intros; split; intros.
  - rewrite H; reflexivity.
  - intros ?; extensionality ofs.
    unfold Mem.perm in *.
    specialize (H b ofs). repeat rewrite_getPerm.
    apply self_simulation.all_order_eq in H; eauto.
Qed.

(*Move te following to diagrms.v:*)
Lemma nextblock_event_ple:
  forall le nb1 nb2, nextblock_event nb1 le nb2 -> Ple nb1 nb2.
Proof.
  intros. inv H; try now reflexivity.
  apply Ple_succ.
Qed.


Lemma consecutive_until_plt:
  forall le nb1 nb2, consecutive_until nb1 le nb2 -> Ple nb1 nb2.
Proof.
  induction le.
  + intros. inv H; reflexivity.
  + intros. inv H.
    etransitivity.
    
    eapply nextblock_event_ple; eauto.
    eauto.
Qed.
Lemma mem_interference_nextblock:
  forall m1 e m2,
    mem_interference m1 e m2 ->
    Ple (Mem.nextblock m1) (Mem.nextblock m2).
Proof.
  intros ??? H. eapply interference_consecutive_until in H.
  eapply consecutive_until_plt; eauto.
Qed.
Lemma mem_effect_interf_max_perm:
  forall ev m1 m2, 
    mem_effect_interf m1 ev m2 ->
    forall b ofs p, Mem.valid_block m1 b ->
               Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Proof.
  intros; inv H.
  - unfold Mem.perm in *.
    eapply Mem.storebytes_access in H3.
    repeat rewrite_getPerm.
    rewrite restr_Max_eq in *.
    rewrite getMaxPerm_correct in *;
      unfold permission_at in *.
    rewrite H3 in H1.
    repeat rewrite_getPerm.
    rewrite restr_Max_eq in *; auto.
  - eapply Mem.perm_alloc_4; eauto.
    + rewrite restr_Max_equiv in H1; eauto.
    + intros HH; subst.
      eapply Mem.alloc_result in H2; subst.
      clear - H0. eapply Plt_strict; eauto.
  - eapply (perm_freelist _ _ _ b ofs Max p) in H3; eauto;
      unfold Mem.perm in *; repeat rewrite_getPerm.
    + rewrite restr_Max_equiv in H3; eauto.
    + rewrite restr_Max_equiv in H1; eauto.
Qed.
Lemma mem_interference_max_perm:
  forall lev m1 m2, 
    mem_interference m1 lev m2 ->
    forall b ofs p, Mem.valid_block m1 b ->
               Mem.perm m2 b ofs Max p -> Mem.perm m1 b ofs Max p.
Proof.
  induction lev.
  - intros. inv H; auto.
  - intros. inv H.
    eapply  mem_effect_interf_max_perm; eauto.
    eapply IHlev; eauto.
    apply mem_effect_interf_consecutive in H5.
    eapply Plt_Ple_trans.
    + apply H0.
    + eapply nextblock_event_ple; eauto.
Qed.

Lemma mem_interference_valid:
  forall lev m1 m2, 
    mem_interference m1 lev m2 ->
    forall b, Mem.valid_block m1 b ->
               Mem.valid_block m2 b.
Proof.
  induction lev.
  - intros. inv H; auto.
  - intros. inv H.
    eapply IHlev; eauto.
    apply mem_effect_interf_consecutive in H4.
    eapply Plt_Ple_trans.
    + apply H0.
    + eapply nextblock_event_ple; eauto.
Qed.  
Lemma mem_effect_interf_Cur:
  forall m1 ev m2, mem_effect_interf m1 ev m2 ->
              Cur_equiv m1 m2.
Proof.
  intros. rewrite (mem_is_restr_eq m1).
  inv H; symmetry;
    eapply Cur_equiv_restr; reflexivity.
Qed.
Lemma mem_interference_Cur:
  forall ev m1 m2, mem_interference m1 ev m2 ->
              Cur_equiv m1 m2.
Proof.
  induction ev.
  - intros. inv H; auto. reflexivity.
  - intros. inv H.
    etransitivity.
    + eapply mem_effect_interf_Cur; eauto.
    + eapply IHev; eauto.
Qed.
Lemma mem_effect_interf_preserves_nowriables:
  forall m1 e m2,
    mem_effect_interf  m1 e m2 ->
    forall p b ofs, Events.loc_not_writable m1 b ofs->
             Mem.perm m1 b ofs Max p -> 
             ZMap.get ofs (Mem.mem_contents m1) !! b =
             ZMap.get ofs (Mem.mem_contents m2) !! b.
Proof.
  intros; symmetry; inv H; simpl.
  + erewrite Mem.storebytes_mem_contents; eauto; simpl.
      destruct (peq b0 b).
      * subst. rewrite PMap.gss.
        rewrite Mem.setN_outside; eauto.
        assert (Hwrit:Events.loc_not_writable m' b ofs).
        { intros HH; eapply H0. eapply Mem.perm_storebytes_2 in H3; eauto.
          rewrite restr_Max_equiv in H3; eauto. } 
        eapply Mem.storebytes_range_perm in H3.
        destruct (Intv.In_dec ofs (ofs0, ofs0+  Z.of_nat (Datatypes.length mvs))).
        2:{ eapply Intv.range_notin in n; simpl in *; eauto.
            assert (0 < Z.of_nat (Datatypes.length mvs)).
            { destruct mvs; try now exfalso; eauto. simpl.
              rewrite Zpos_P_of_succ_nat; omega. }
            omega. }
        exfalso; apply H0.
        hnf in H3. 
        hnf in i; simpl in *. eapply H3 in i.
        apply Mem.perm_cur_max in i.
        erewrite restr_Max_equiv in i. 
        assumption.
      * rewrite PMap.gso; eauto.
    + erewrite AllocContentsOther; eauto.
      intros HH; subst.
      eapply Mem.alloc_result in H2; subst.
      eapply Plt_strict. eapply Mem.perm_valid_block; eauto.
    + eapply free_list_contents_eq in H3; eauto.
      simpl in *. rewrite H3; reflexivity.
Qed.

    Lemma mem_effect_interf_max_perm12:
      forall (lev : Events.mem_effect) (m1 m2 : mem),
        mem_effect_interf m1 lev m2 ->
        forall (b : block) (ofs : Z) (k : perm_kind) (p : permission),
          Events.loc_not_writable m1 b ofs ->
          Mem.valid_block m1 b -> Mem.perm m1 b ofs k p <-> Mem.perm m2 b ofs k p.
    Proof.
      intros lev m1 m2 H.
      intros b ofs k; revert b ofs.
    destruct k; swap 1 2.
    { intros.
      !goal(Mem.perm _ _ _ Cur _ <-> _).
      unfold Mem.perm. repeat rewrite_getPerm.
      inv H; rewrite getCur_restr; reflexivity. }
    inv H.
    + intros.
      eapply semantics_lemmas.storebytes_unch_loc_unwritable in H1.
      rewrite restr_Max_equiv.
      inv H1. exploit unchanged_on_perm; eauto.
      intros HH; eapply H; eauto.
      erewrite <- restr_Max_equiv; eauto.
      intros. rewrite <- H1. 
      erewrite restr_Max_equiv; reflexivity.
    + intros; split.
      * rewrite restr_Max_equiv.
        eapply Mem.perm_alloc_1; eauto.
      * rewrite restr_Max_equiv; intros.
        eapply Mem.perm_alloc_4; eauto.
        intros ?; subst.
        eapply Mem.alloc_result in H0; subst.
        eapply Plt_strict. eapply H1.
    + intros; rewrite restr_Max_equiv; split; intros.
      * eapply semantics_lemmas.freelist_perm_inv in H1; eauto.
        -- destruct H1; eauto. exfalso; eapply H.
           rewrite restr_Max_equiv in H1.
           eapply Mem.perm_implies; eauto; constructor.
        -- rewrite restr_Max_equiv; eauto.
      * eapply perm_freelist in H1; eauto.
        rewrite restr_Max_equiv in H1; eauto.
    Qed.
Lemma interference_preserves_nowriables:
  forall e m1 m2,
    mem_interference m1 e m2 ->
    forall p b ofs, Events.loc_not_writable m1 b ofs->
             Mem.perm m1 b ofs Max p -> 
             ZMap.get ofs (Mem.mem_contents m1) !! b =
             ZMap.get ofs (Mem.mem_contents m2) !! b.
Proof.
  induction e.
  - intros. inv H; auto.
  - intros. inv H.
    etransitivity.
    eapply mem_effect_interf_preserves_nowriables; eauto.
    eapply IHe; eauto.
    + intros HH; eapply H0.
      eapply mem_effect_interf_max_perm; eauto.
      eapply Mem.perm_valid_block; eauto.
    + eapply mem_effect_interf_max_perm12 in H5; eauto.
      eapply H5; eauto.
      eapply Mem.perm_valid_block; eauto.
Qed.
    
Lemma mem_effect_interf_readonly:
  forall lev (m1 : mem) (m2 : mem),
    mem_effect_interf m1 lev m2 ->
    Mem.unchanged_on (Events.loc_not_writable m1) m1 m2.
Proof.
  intros. econstructor.
  - inv H. 
    + apply Mem.nextblock_storebytes in H1; simpl in *.
      rewrite H1; reflexivity.
    + apply Mem.nextblock_alloc in H0; simpl in *.
      rewrite H0. apply Ple_succ.
    + apply nextblock_freelist in H1;  simpl in *.
      rewrite H1; reflexivity.
  - eapply mem_effect_interf_max_perm12; eassumption.
  - intros; symmetry; eapply mem_effect_interf_preserves_nowriables; eauto.
    eapply Mem.perm_cur_max; eassumption.
Qed.
Lemma mem_effect_interf_nextblock:
  forall (ev : Events.mem_effect) (m m' : mem),
    mem_effect_interf m ev m' ->
    Ple (Mem.nextblock m) (Mem.nextblock m').
Proof.
  intros. eapply mem_effect_interf_consecutive in H.
  eapply nextblock_event_ple; eauto.
Qed.
  
Lemma mem_interference_readonly:
  forall lev (m1 : mem) (m2 : mem),
  mem_interference m1 lev m2 -> Mem.unchanged_on (Events.loc_not_writable m1) m1 m2.
Proof.
  induction lev.
  - intros. inv H; auto.
    econstructor; intros; try reflexivity.
  - intros. inv H.
    econstructor; intros.
    + etransitivity.
      eapply mem_effect_interf_readonly; eauto.
      eapply IHlev; auto.
    + etransitivity.
      eapply mem_effect_interf_readonly; eauto.
      assert (Mem.valid_block m' b).
      { eapply nextblock_leq_valid; eauto.
        eapply mem_effect_interf_nextblock; eauto. }
      eapply IHlev; auto.
      intros HH. eapply H.
      eapply mem_effect_interf_max_perm; eauto.
    + etransitivity; swap 1 2.
      eapply mem_effect_interf_readonly; eauto.
      assert (Mem.valid_block m1 b).
      { eapply Mem.perm_valid_block; eauto. }
      eapply IHlev; eauto.
      * intros HH. eapply H.
        eapply mem_effect_interf_max_perm; eauto.
      * rewrite <- mem_effect_interf_Cur; eauto. 
Qed.

      Inductive In_list_free: block -> Z -> list (block*Z*Z) -> Prop:=
      | In_head_free: forall b ofs lo hi tl,
          lo <= ofs < hi ->
          In_list_free b ofs ((b, lo, hi)::tl)
      | In_tail_free: forall b ofs hd tl,
          In_list_free b ofs tl ->
          In_list_free b ofs (hd::tl).
      
      Inductive in_mem_effect: block -> Z -> mem_effect -> Prop :=
      | In_Write: forall b ofs mvs,
          in_mem_effect b ofs (Write b ofs mvs)
      | In_Alloc: forall b ofs lo hi,
          lo <= ofs < hi ->
          in_mem_effect b ofs (Alloc b lo hi)
      | In_Freelist: forall b ofs ls,
          In_list_free b ofs ls ->
          in_mem_effect b ofs (Free ls).
      Inductive In_list_events: block -> Z -> list mem_effect -> Prop:=
      | In_head: forall b ofs ev tl,
          in_mem_effect b ofs ev ->
          In_list_events b ofs (ev::tl)
      | In_tail: forall b ofs hd tl,
          In_list_events b ofs tl ->
          In_list_events b ofs (hd::tl).
      Definition not_In_list_events ls b ofs:=
        ~ In_list_events b ofs ls.
      
      Lemma mem_interference_mem_extends:
        forall (m1 : mem) e (m2 m1' : mem),
          mem_interference m1 e m2 ->
          Mem.extends m1 m1' ->
          exists (m2' : mem),
            mem_interference m1' e m2' /\
            Mem.extends m2 m2' /\ Mem.unchanged_on (not_In_list_events e) m1' m2'.
      Proof.
      Admitted.

(* STOP moving to diagrams.v *)


(*Move the following to synchronisation_steps_semantics.v*)

Lemma release_preserves_nextblock:
  forall ptr m1 dpm m2,
    release ptr m1 dpm m2 ->
    (Mem.nextblock m1) = (Mem.nextblock m2).
Proof.
  intros. inv H.
  eapply Mem.nextblock_store in H0; simpl in *; auto.
Qed.

Lemma release_preserves_max_equiv:
  forall ptr m1 dpm m2,
    release ptr m1 dpm m2 -> Max_equiv m1 m2.
Proof.
  intros. inv H.
  eapply store_max_equiv in H0.
  rewrite restr_Max_equiv.
  rewrite restr_Max_equiv in H0; auto.
Qed.
Lemma release_valid_block:
      forall ge vargs m1 t vres m2,
        extcall_release ge vargs m1 t vres m2 ->
        Ple (Mem.nextblock m1) (Mem.nextblock m2).
(* Mem.valid_block m1 b -> Mem.valid_block m2 b. *)
    Proof.
      intros. inv H.
      etransitivity.
      - eapply mem_interference_nextblock; eauto.
      - etransitivity.
        + erewrite release_preserves_nextblock; try apply H1.
          reflexivity.
        + eapply mem_interference_nextblock; eauto.
    Qed.

    Lemma extcall_release_readonly:
      forall (ge : Senv.t) (vargs : list val) (m1 : mem) (t : Events.trace)
        (vres : val) (m2 : mem),
        extcall_release ge vargs m1 t vres m2 ->
        Mem.unchanged_on (Events.loc_not_writable m1) m1 m2.
    Proof.
      intros. econstructor.
      + eapply release_valid_block; eassumption.
      + unfold Events.loc_not_writable; intros.
        inv H.  
        eapply mem_interference_readonly in H2;
          eapply mem_interference_readonly in H4.
        (*Move this to my tactics*)
        trans_n 2%nat; swap 2 3. 
        * eapply H2; eauto. 
        * eapply H4; eauto.
          -- intros HH; eapply H0; eapply H2; eauto.
             rewrite release_preserves_max_equiv; eauto.
          -- eapply nextblock_eq_valid.
             symmetry; eapply release_preserves_nextblock; eauto.
             eapply nextblock_leq_valid; eauto.
             eapply H2.
        * destruct k.
          -- rewrite release_preserves_max_equiv; eauto; reflexivity.
          -- admit. (* This is not true right now
                     need to wait for Xavier to see if this condition can be removed...
                     OR add it to release.
                     *)
      + intros. inv H.
        symmetry; trans_n 2%nat; swap 2 3.
        * eapply mem_interference_readonly in H2.
          symmetry; eapply H2; eauto.
        * eapply interference_preserves_nowriables; eauto.
          -- erewrite <- release_preserves_max_equiv; try eapply H3.
             intros HH; eapply H0.
             eapply mem_interference_max_perm; eauto.
             eapply Mem.perm_valid_block; eauto.
          --  rewrite <- release_preserves_max_equiv; eauto.
              eapply  mem_interference_Cur in H2.
              rewrite H2 in H1.
              eapply Mem.perm_cur_max; eauto.
        * inv H3.
          assert (Hwrit: forall ofs, b = b0 ->
                    unsigned ofs0 <= ofs < unsigned ofs0 + size_chunk AST.Mint32 ->
                    Mem.perm m1 b ofs Max Writable).
          {  eapply Mem.store_valid_access_3 in H6. inv H6.
            intros; subst. hnf in H. exploit H; eauto.
            intros HH. 
            apply Mem.perm_cur_max in HH; eauto.
            rewrite restr_Max_equiv in HH.
            eapply mem_interference_max_perm; eauto.
            eapply Mem.perm_valid_block; eauto. }
            
          eapply Mem.store_mem_contents in H6; simpl in *.
          rewrite H6.
          destruct (peq b b0).
          -- subst; rewrite PMap.gss.
             rewrite Mem.setN_outside; eauto.
             simpl.
             replace (Datatypes.length (inj_bytes (encode_int 4 (Int.unsigned Int.one))))
               with 4%nat; swap 1 2.
             { unfold inj_bytes.
               rewrite map_length, encode_int_length. reflexivity. }
             destruct (Intv.In_dec ofs (unsigned ofs0, unsigned ofs0 +  Z.of_nat 4)).
             2:{ eapply Intv.range_notin in n; simpl in *; eauto.
                 omega. }
             exfalso; apply H0.
             eapply Hwrit; eauto.
          -- rewrite PMap.gso; eauto.
    Admitted.
    
      Lemma release_determ:
        forall ptr m1 dpm m2 m2' ,
          release ptr m1 dpm m2 ->
          release ptr m1 dpm m2' -> m2 = m2'.
      Proof.
        intros. inv H; inv H0.
        eapply mem_equalitiy.
        - simpl.
          eapply Mem.store_mem_contents in H1; rewrite H1.
          eapply Mem.store_mem_contents in H3; rewrite H3.
          reflexivity.
        - simpl.
          eapply Mem.store_access in H1; rewrite H1;
            eapply Mem.store_access in H3; rewrite H3; simpl.
          f_equal.
          unfold PTree.map.
          do 2 rewrite xmap_compose.
          f_equal.
        - simpl.
          eapply Mem.nextblock_store in H1; rewrite H1;
            eapply Mem.nextblock_store in H3; eauto.
      Qed.

      Notation delta_map:= (PTree.t (Z -> option (option permission))).
      
      Definition not_In_deltamap (dpm:delta_map) b_ofs b ofs:=
        dmap_get dpm b ofs = None /\ (b,ofs) <> b_ofs.
      Definition not_In_acq_rel e b_ofs dpm e' b ofs:=
        not_In_list_events e b ofs /\
        not_In_deltamap dpm b_ofs b ofs /\
        not_In_list_events e' b ofs.
      
      Lemma unchanged_on_implies_strong:
        forall (P Q : block -> Z -> Prop) (m m' : mem),
          Mem.unchanged_on P m m' ->
          (forall (b : block) (ofs : Z), Q b ofs -> P b ofs) ->
          Mem.unchanged_on Q m m'.
      Proof. intros. eapply Mem.unchanged_on_implies; intros; eauto. Qed.
             
      Lemma release_mem_extends:
        forall (m1 : mem) (m2 m1' : mem) dmp b0 ofs0,
          release (Vptr b0 ofs0) m1 dmp m2 ->
          Mem.extends m1 m1' ->
          exists  (m2' : mem),
          release (Vptr b0 ofs0) m1' dmp m2' /\
          Mem.extends m2 m2' /\ Mem.unchanged_on (not_In_deltamap dmp (b0,unsigned ofs0)) m1' m2'.
      Proof.
      Admitted.
      Lemma interference_release_not_in_event:
        forall m1 m2 m3 m4 b0 ofs0 e dpm e',
          mem_interference m1 e m2 ->
          release (Vptr b0 ofs0) m2 dpm m3 ->
          mem_interference m3 e' m4 ->
          forall b ofs, Events.loc_out_of_bounds m1 b ofs ->
                   not_In_acq_rel e (b0,unsigned ofs0) dpm e' b ofs.     
      Proof.
      Admitted.
      Lemma extcall_release_mem_extends:
      forall (ge : Senv.t) (vargs : list val) (m1 : mem) (t : Events.trace)
        (vres : val) (m2 m1' : mem) (vargs' : list val),
        extcall_release ge vargs m1 t vres m2 ->
        Mem.extends m1 m1' ->
        Val.lessdef_list vargs vargs' ->
        exists (vres' : val) (m2' : mem),
          extcall_release ge vargs' m1' t vres' m2' /\
          Val.lessdef vres vres' /\
          Mem.extends m2 m2' /\ Mem.unchanged_on (Events.loc_out_of_bounds m1) m1' m2'.
    Proof.
      intros. inv H. inv H1. inv H8. inv H6.
      rename m2 into m4;
        rename m' into m2;
        rename m'' into m3.
      pose proof (interference_release_not_in_event _ _ _ _ _ _ _ _ _
                                                    H2 H3 H4) as HH.
      eapply mem_interference_mem_extends in H2; eauto. normal_hyp.
      eapply release_mem_extends in H3; eauto; normal_hyp.
      eapply mem_interference_mem_extends in H4; eauto. normal_hyp.
      rename x1 into m4';
        rename x into m2';
        rename x0 into m3'.
      do 2 econstructor; split.
      - econstructor; eauto.
      - split; constructor; eauto.
        eapply (unchanged_on_implies_strong
                  _ (not_In_acq_rel e (b,unsigned ofs) dpm e')) in H8.
        eapply unchanged_on_implies_strong in H6.
        eapply unchanged_on_implies_strong in H2.
        eapply Mem.unchanged_on_trans in H8; eauto.
        eapply Mem.unchanged_on_trans in H8; eauto.
        eapply unchanged_on_implies_strong; eauto.
        intros * AA; eapply AA.
        intros * AA; eapply AA.
        intros * AA; eapply AA.
    Qed.


(*STOP moving to synchronisation_steps_semantics.v*)





(** *TODO: this is necessary, but nobody will use it.
          make sure every function has it... and PROVE it!
 *)
      
Lemma extcall_properties_release:
  Events.extcall_properties extcall_release UNLOCK_SIG.
Proof.
  econstructor.
  - intros. inv H; constructor.
  - intros. inv H0; econstructor; eauto.
  - unfold Mem.valid_block.
    intros. eapply Plt_Ple_trans; try eassumption.
    eapply release_valid_block; eauto.
  - intros. inv H.
    eapply mem_interference_max_perm;
      try eassumption.
    rewrite release_preserves_max_equiv; try apply H3.
    eapply mem_interference_max_perm; eauto.
    eapply mem_interference_valid in H2; eauto.
    eapply nextblock_eq_valid; try eassumption.
    symmetry;eapply release_preserves_nextblock; eassumption.
  - eapply extcall_release_readonly.
  - eapply extcall_release_mem_extends.
  -
    
      Definition injectable_mem_effect (f:meminj) m1 e:=
        forall b ofs, In_list_events b ofs e ->
                 Mem.valid_block m1 b ->
                 ~ f b = None.
      Definition injectable_dpm (f:meminj) m1 (dpm:delta_map):=
        forall b ofs, ~ dmap_get dpm b ofs = None ->
                 Mem.valid_block m1 b ->
                 ~ f b = None. 
    Inductive injectable_trace_event (f:meminj) (m:mem): event -> Prop :=
      | injable_syscall: forall str vls vls', injectable_trace_event f m (Event_syscall str vls vls')
      | injable_vload: forall a b c d, injectable_trace_event f m (Event_vload a b c d)
      | injable_vstore: forall a b c d, injectable_trace_event f m (Event_vstore a b c d)
      | injable_annot: forall a b, injectable_trace_event f m (Event_annot a b)
      | injable_acq_rel: forall lev1 dpm lev2 ,
          injectable_mem_effect f m lev1 ->
          injectable_dpm f m dpm ->
          injectable_mem_effect f m lev2 ->
          injectable_trace_event f m (Event_acq_rel lev1 dpm lev2)
      | injable_spawn: forall b dpm1 dpm2,
          injectable_dpm f m dpm1 ->
          injectable_dpm f m dpm2 ->
          injectable_trace_event
            f m (Event_spawn b dpm1 dpm2).
    Definition injectable_trace f m:= Forall (injectable_trace_event f m). 
    Lemma release_mem_inject:
        forall (m1 : mem) dpm (m2 m1' : mem) f b0 ofs0 b0' ofs0',
          release (Vptr b0 ofs0) m1 dpm m2 ->
          Mem.inject f m1 m1' ->
          val_inject f (Vptr b0 ofs0) (Vptr b0' ofs0') ->
          injectable_dpm f m1 dpm  -> 
          exists dpm' (m2' : mem),
            release (Vptr b0' ofs0') m1' dpm' m2' /\
            Mem.inject f m2 m2' /\ 
            Mem.unchanged_on (not_In_deltamap dpm' (b0', unsigned ofs0') ) m1' m2' /\
            Mem.unchanged_on (not_In_deltamap dpm (b0, unsigned ofs0) ) m1 m2 /\
            EventsAux.inject_delta_map f dpm dpm'.
    Proof.
      
    Admitted.
    
    Lemma mem_interference_mem_inject:
      forall (m1 : mem) e (m2 m1' : mem) f,
        mem_interference m1 e m2 ->
        Mem.inject f m1 m1' ->
        injectable_mem_effect f m1 e -> 
        exists f' e' (m2' : mem),
          mem_interference m1' e' m2' /\
          Mem.inject f' m2 m2' /\ inject_incr f f' /\
          Events.inject_separated f f' m1 m1' /\
          Mem.unchanged_on (not_In_list_events e) m1 m2 /\
          Mem.unchanged_on (not_In_list_events e') m1' m2' /\
          Events.list_inject_mem_effect_strong f' e e' /\
          (Events.injection_full f m1 -> Events.injection_full f' m2).
    Proof.
    Admitted.
      Lemma injectable_trace_not_in_trace:
            forall f m1 e1 b ofs dpm e2,
              f b <> None ->
              injectable_trace_event f m1 (Event_acq_rel e1 dpm e2) ->
            forall (b0 : block) (ofs0 : Z),
              Events.loc_unmapped f b0 ofs0 ->
              Mem.valid_block m1 b0 ->
              not_In_acq_rel e1 (b, ofs) dpm e2 b0 ofs0.
          Proof.
            unfold not_In_acq_rel; intros. inv H0. 
            hnf in H; repeat weak_split.
            - intros HH. eapply H6; eauto.
            - split.
              + destruct (dmap_get dpm b0 ofs0) eqn:HH; eauto.
                exfalso; eapply H7; eauto.
                rewrite HH; intros; discriminate.
              + intros HH; inv HH. apply H; apply H1.
            - intros HH. eapply H8; eauto.
          Qed.
    Lemma extcall_release_mem_inject:
      forall (ge1 ge2 : Senv.t) (vargs : list val) (m1 : mem) (t : Events.trace) 
        (vres : val) (m2 : mem) (f : block -> option (block * Z)) (m1' : mem) 
        (vargs' : list val),
        Events.symbols_inject f ge1 ge2 ->
        extcall_release ge1 vargs m1 t vres m2 ->
        Mem.inject f m1 m1' ->
        Val.inject_list f vargs vargs' ->
        injectable_trace f m1 t ->
        exists (f' : meminj) (vres' : val) (m2' : mem) (t' : Events.trace),
          extcall_release ge2 vargs' m1' t' vres' m2' /\
          val_inject f' vres vres' /\
          Mem.inject f' m2 m2' /\
          Mem.unchanged_on (Events.loc_unmapped f) m1 m2 /\
          Mem.unchanged_on (Events.loc_out_of_reach f m1) m1' m2' /\
          inject_incr f f' /\
          Events.inject_separated f f' m1 m1' /\
          Events.inject_trace_strong f' t t' /\
          (Events.injection_full f m1 -> Events.injection_full f' m2).
    Proof.
      intros. inv H0. inv H2. inv H8. inv H10.
      (*inv H3; inv H8; inv H9. *)
      rename m2 into m4;
        rename m' into m2;
        rename m'' into m3.
      rename e into e1; rename e' into e2.
      
      eapply mem_interference_mem_inject in H4; eauto. normal_hyp.
      eapply release_mem_inject in H5; eauto. normal_hyp.
      eapply mem_interference_mem_inject in H6; eauto. normal_hyp.
      rename x1 into m2';
      rename x3 into m3';
      rename x6 into m4'.
      rename x into f1;
        rename x4 into f3.
      rename x0 into e1';
        rename x5 into e2';
        rename x2 into dpm'.
      exists f3, Vundef, m4'. eexists.
      repeat weak_split; try solve[constructor]; eauto.
      - econstructor; eauto.
      - eapply Mem.unchanged_on_implies.
        instantiate (1:= (not_In_acq_rel e1 (b,unsigned ofs) dpm e2)).
        + eapply Mem.unchanged_on_trans; [|eapply Mem.unchanged_on_trans].
          * eapply unchanged_on_implies_strong; eauto.
            intros * AA; apply AA.
          * eapply unchanged_on_implies_strong. try eassumption.
            intros * AA; apply AA.
          * eapply unchanged_on_implies_strong. try eassumption.
            intros * AA; apply AA.
        + eapply injectable_trace_not_in_trace; eauto.
          * rewrite H7; intros; congruence.
          * inv H3; eauto.
      - eapply Mem.unchanged_on_implies.
        instantiate (1:= (not_In_acq_rel e1'
                                         (b2,(unsigned (add ofs (repr delta)))) dpm' e2')).
        + eapply Mem.unchanged_on_trans; [|eapply Mem.unchanged_on_trans].
          * eapply unchanged_on_implies_strong; eauto.
            intros * AA; apply AA.
          * eapply unchanged_on_implies_strong. try eassumption.
            intros * AA; apply AA.
          * eapply unchanged_on_implies_strong. try eassumption.
            intros * AA; eapply AA.
        + intros.
          Lemma event_valid_locations_nonempty:
            forall (b0:block) ofs0 m1 e m2,
              In_list_events b0 ofs0 e ->
              Mem.valid_block m1 b0 ->
              mem_interference m1 e m2 ->
              Mem.perm m1 b0 ofs0 Max Nonempty. 
          Proof.
          Admitted.
          Lemma interf_no_incr_Max:
            forall m1 e m2,
              mem_interference m1 e m2 ->
              forall b0 ofs0 p,
              Mem.perm m2 b0 ofs0 Max p ->
              Mem.perm m1 b0 ofs0 Max p.
          Proof.
          Admitted.
          Definition max_incr m m':=
            forall b ofs p,
              Mem.perm m b ofs Max p ->
              Mem.perm m' b ofs Max p.
            
            
          Definition strict_incr: meminj -> meminj ->
                                  block -> block -> Prop.
            intros. eapply True.
          Qed.
          Definition strict_incr_mem: meminj -> meminj ->
                                      mem -> mem -> Prop:=
            fun f f' m m' =>
              strict_incr f f' (Mem.nextblock m)
                          (Mem.nextblock m').
          Lemma out_of_reach_incr:
            forall f f' m m',
              strict_incr_mem f f' m m' ->
              max_incr m' m ->
            forall b ofs,
            Events.loc_out_of_reach f m b ofs ->
              Mem.valid_block m b ->
              Events.loc_out_of_reach f' m' b ofs.
          Proof.
            intros ** b ofs HH1 HH2.
            eapply H1; swap 1 2.
            - eapply H0; eauto. 
            - admit. (*because it's valid. *)
          Admitted.

          cut (exists b delt, f b = Some (b0, delt) /\ Mem.perm m1 b (ofs0 - delt) Max Nonempty).
          { intros; normal_hyp; eapply H24; eauto. }
          admit. (* Todo prove the mapping implies not in the trace*)
          * admit.
          
      - repeat (eapply inject_incr_trans; eauto).
      - admit. (* Events.inject_separated "Transitivity" *)
      - do 2 econstructor; eauto.
        eapply Events.list_inject_mem_effect_strong_incr; eauto.
        repeat (eapply inject_incr_trans; eauto).
        eapply EventsAux.inj_delta_map_mono; eauto.
      - inv H3. intros; eauto.
        eapply H23.
        hnf. intros. eapply H12; eauto.
        eapply nextblock_eq_valid; try eapply H24; eauto.
        symmetry; eapply release_preserves_nextblock; eauto.
        admit.
        
        Lemma injectable_mem_effect_incr:
          forall f f' m e,
            inject_incr f f' ->
            injectable_mem_effect f m e ->
            injectable_mem_effect f' m e.
        Proof.
          intros.
          intros ? ? ? ? ?.
          eapply H0; eauto.
          destruct (f b) eqn:HH; eauto. destruct p.
          eapply H in HH; rewrite HH in H3; congruence.
        Qed.    
      - !goal (injectable_mem_effect x m3 e2). admit.
      - !goal (injectable_dpm x m2 dpm). admit.
      - !goal(injectable_mem_effect f m1 e1). admit.
    Admitted.
    intros; exploit extcall_release_mem_inject; eauto.
    admit. (* ADD to extcall_properties. *)
    intros. normal_hyp; repeat (econstructor; eauto).
  - intros; exploit extcall_release_mem_inject; eauto.
    admit. (* ADD to extcall_properties. *)
    intros. normal_hyp; repeat (econstructor; eauto).
  - (* trace length *)
    intros. inv H. simpl; omega.
  - intros; inv H; inv H0.
  - intros. inv H; inv H0.
    split; swap 1 2.
    + intros H; inv H. split; eauto.
      exploit mem_interference_determ;
        [eapply H1| eapply H5| intros ?].
      rewrite H in *.
      eapply release_determ in H7; try eapply H2. subst.
      eapply mem_interference_determ; eauto.
    +  (*need to add reflexive match for traces *)
Admitted.  
      
    
           
          
        
        assert (HH : forall b0 : block, Ple b0 a <-> Ple b0 b).
        { intros; split; intros.

          
Lemma extcall_properties_acquire:
  Events.extcall_properties extcall_acquire LOCK_SIG.
Proof.
(* this is given axiomatically in compcert, 
                     but we must prove it*)
Admitted.